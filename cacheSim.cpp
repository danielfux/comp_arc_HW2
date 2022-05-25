/* 046267 Computer Architecture - Spring 2022 - HW #2 */
/* -------------------------------------------------- include files ----------------------------------------------- */
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>
// additional include files
#include <cmath>
#include <vector>
/* --------------------------------------------------- standards -------------------------------------------------- */
using std::FILE;
using std::string;
using std::cout;
using std::endl;
using std::cerr;
using std::ifstream;
using std::stringstream;
// additional standards
using std::vector;
/* -------------------------------------------------- static constants -------------------------------------------- */
static const int fail = -1;
static const int command_size = 32;
static const int notFound = -1;
/* -------------------------------------------------- global variables -------------------------------------------- */
static unsigned int times_to_access_data = 0;
static unsigned int tot_time_to_access_data = 0;
static unsigned int times_to_access_mem = 0;
static unsigned int tot_time_to_access_mem = 0;
static unsigned int block_size;  // [bytes]
static unsigned int bits_for_offset;
static unsigned int write_allocate;
static unsigned int mem_cyc_;
// for return values from function find_parallel_tag_and_set
static unsigned int parallel_tag_to_l1 = 0;
static unsigned int parallel_set_to_l1 = 0;
static unsigned int lru_address_l1 = 0;

static unsigned int parallel_tag_to_l2 = 0;
static unsigned int parallel_set_to_l2 = 0;
static unsigned int lru_address_l2 = 0;
static unsigned int data_counter = 0;

/* -------------------------------------------------- Block Class ------------------------------------------------- */
class Block {
public:
    unsigned int tag_;
    bool valid_;
    bool dirty_; // regarding the level below
    unsigned int count_;
    unsigned int address_;
};

/* --------------------------------------------------- Set Class -------------------------------------------------- */
class Set {
public:
    vector<Block *> blocks_vec_in_set; // parallel to vector of apartments in each floor
    unsigned int tot_blocks_in_set; // equals to ways number
    unsigned int tag_idx_in_set = 0;
    unsigned int lru_idx = 0;
    unsigned int set_idx;

    // constructor with params
    Set(unsigned int ways_num, unsigned int set_i) : tot_blocks_in_set(ways_num),
                                                     set_idx(set_i) { // initiates tot_blocks_in_set with ways_num

        for (unsigned int i = 0; i < tot_blocks_in_set; ++i) {
            blocks_vec_in_set.push_back(new Block());
            // TODO: throw exception if allocation failed
            blocks_vec_in_set[i]->count_ = i; // initial state for lru
            blocks_vec_in_set[i]->tag_ = 0;
            blocks_vec_in_set[i]->valid_ = false;
            blocks_vec_in_set[i]->dirty_ = false;
            blocks_vec_in_set[i]->address_ =0;
        }
    }

    /* ______________________________________  lru_init __________________________________________________ */
    void lru_init(unsigned int way_idx) {
        for (unsigned int i = 0; i < tot_blocks_in_set; ++i){
            if (blocks_vec_in_set[i]->count_ == 0) {
                way_idx = i;
            }
        }
    }
    /* ______________________________________  lru_update __________________________________________________ */
    void lru_update(unsigned int way_idx) {
        int x = blocks_vec_in_set[way_idx]->count_;
        blocks_vec_in_set[way_idx]->count_ = tot_blocks_in_set - 1;
        for (unsigned int j = 0; j < tot_blocks_in_set; ++j) {
            if (j != way_idx && blocks_vec_in_set[j]->count_ > x) {
                blocks_vec_in_set[j]->count_--;
            }
        }
        //check if there is a free block in the set and update the lru index to be the free index
        for (unsigned int i = 0; i < tot_blocks_in_set; ++i) {
            if (!blocks_vec_in_set[i]->valid_) {
                this->lru_idx = i;
                return;
            }
        }
        // if there isn't a free block we will take the updated lru index
        for (unsigned int i = 0; i < tot_blocks_in_set; ++i) {
            if (blocks_vec_in_set[i]->count_ == 0) {
                this->lru_idx = i;
            }
        }
    }
    /* ______________________________________  isBlockFree ____________________________________________ */
    bool isBlockFree(){
        for (unsigned int i = 0; i < tot_blocks_in_set; ++i) {
            if (!blocks_vec_in_set[i]->valid_) {
                return true;
            }
        }
        return false;
    }
    /* ______________________________________  addBlockToSet ____________________________________________ */
    void addBlockToSet(unsigned tag,unsigned int address) {
        blocks_vec_in_set[lru_idx]->tag_ = tag;
        blocks_vec_in_set[lru_idx]->valid_ = true;
        blocks_vec_in_set[lru_idx]->address_=address;
        lru_update(lru_idx);
    }
    /* _______________________________________ addDirtyBlockToSet ________________________________________ */
    void addDirtyBlockToSet(unsigned int tag,unsigned int address) {
        blocks_vec_in_set[lru_idx]->tag_ = tag;
        blocks_vec_in_set[lru_idx]->valid_ = true;
        blocks_vec_in_set[lru_idx]->dirty_ = true;
        blocks_vec_in_set[lru_idx]->address_= address;
        lru_update(lru_idx);
    }
    /* ______________________________________  idxOfTagInSet __________________________________________________ */
    int idxOfTagInSet(unsigned int tag) {
        for (unsigned int i = 0; i < tot_blocks_in_set; ++i) {
            if (blocks_vec_in_set[i]->tag_ == tag && blocks_vec_in_set[i]->valid_) {
                this->tag_idx_in_set = i;
                return i;
            }
        }
        this->tag_idx_in_set = notFound;
        return notFound;
    }
    /* ______________________________________ return_lru_idx __________________________________________________ */
    unsigned int return_lru_idx() {
        return this->lru_idx;
    }
    /* ______________________________________ return_lru_tag __________________________________________________ */
    unsigned int return_lru_tag() {
        return blocks_vec_in_set[lru_idx]->tag_;
    }

    /* ______________________________________ isLruDirty __________________________________________________ */
    bool isLruDirty() {
        return blocks_vec_in_set[lru_idx]->dirty_;
    }
};

/* --------------------------------------------------- Cache Class ----------------------------------------------- */
class Cache {
    // cash includes serial of sets and each set includes serial of blocks

public:
    vector<Set *> sets_vec; // parallel to pointers to floors
    unsigned int num_of_sets_in_a_cache_; // [...]
    unsigned int bits_for_set_;
    unsigned int set_idx_; // [...]
    unsigned int num_of_blocks_in_a_set_; // (ways) parallels to apartments in each floor
    unsigned int bits_for_tag_;
    unsigned int cache_size_;
    unsigned int cache_assoc_;  // [...]
    unsigned int cache_cyc_;    // [cycles]
    unsigned int cache_misses_; // [...]
    unsigned int times_to_access_cache_; // [...] (l1_access_cnt/block_size)

    // constructor without params
    Cache() {};
    // Constructor with params
    //Cache() {}
    // copy-constructor
    //Cache(Cache const&) {}
    // operator =
    //void operator=(Cache const&) {}
    // destructor
    //~Cache() {};
    /* ______________________________________  getSetIdx __________________________________________________ */
    /*
     * assume pc: dddddddd cccccccc bbbbbbbb sssooooo
     * num_of_sets = 8
     * block_size = 32 Bytes
     * bits_for_offset = Bsize = (log2(block_size) = log2(32)=5
     * bits_for_sets = log2(num_of_sets) = log2(8) = 3
     * tmp = command_size -bi_for_sets = 32- 3 = 29
     * pc << (tmp -bits_for_offset) = 29 - 5  = 24 :
     *  sssooooo 00000000 00000000 00000000 >> shift_factor
     * 00000000 00000000 00000000 00000sss
     */
    unsigned int idxOfSetInCache(unsigned int address,unsigned int num_of_sets) {
        if (num_of_sets == 0) {
            return fail;
            // TODO: throw an exception}
        }
        unsigned int bits_for_sets = log2(num_of_sets);
        unsigned int tmp = command_size - bits_for_sets;
        unsigned int extracted_set = (address << (tmp - bits_for_offset)) >> tmp;
        this->set_idx_ = extracted_set;
        return extracted_set;
    }
    /* ______________________________________ get_tag __________________________________________________ */
    unsigned int get_tag(unsigned int address,unsigned int bits_for_set) {
       return address >> (bits_for_set + bits_for_offset);
    }
    /* ______________________________________ find_parallel_tag_and_set __________________________________________________ */
    void find_parallel_tag_and_set(Cache *L1, Cache *L2, unsigned int l1_set, unsigned int l2_set) {
        unsigned int lru_idx_l1 = L1->sets_vec[l1_set]->return_lru_idx();
        lru_address_l1 = L1->sets_vec[l1_set]->blocks_vec_in_set[lru_idx_l1]->address_;
        // finds tag and set in L2, that are parallel to L1:
        parallel_set_to_l1 = L2->idxOfSetInCache(lru_address_l1, L2->num_of_sets_in_a_cache_);
        parallel_tag_to_l1 = L2->get_tag(lru_address_l1, L2->bits_for_set_);

        unsigned int lru_idx_l2 = L2->sets_vec[l2_set]->return_lru_idx();
        lru_address_l2 = L2->sets_vec[l2_set]->blocks_vec_in_set[lru_idx_l2]->address_;
        // finds tag and set in L1, that are parallel to L2:
        parallel_set_to_l2 = L1->idxOfSetInCache(lru_address_l2, L1->num_of_sets_in_a_cache_);
        parallel_tag_to_l2 = L1->get_tag(lru_address_l2, L1->bits_for_set_);
    }
    /* ______________________________________ invalidate_block __________________________________________________ */
    // evicts block with index block_num of set with index set_i
    void invalidate_block(unsigned int block_num, unsigned int set_i) {///
        sets_vec[set_i]->blocks_vec_in_set[block_num]->valid_ = false;///
        //sets_vec[set_i]->lru_update(block_num); ///
    }
    /* ______________________________________ make_block_dirty __________________________________________________ */
    // makes block with index block_num of set with index set_i dirty
    void make_block_dirty(unsigned int way, unsigned int set_i) { ///
        sets_vec[set_i]->blocks_vec_in_set[way]->dirty_ = true;///
        sets_vec[set_i]->lru_update(way);

    }
    /* ______________________________________ make_block_not_dirty __________________________________________________ */
    // makes block with index block_num of set with index set_i not dirty
    void make_block_not_dirty(unsigned int way, unsigned int set_i) { ///
        sets_vec[set_i]->blocks_vec_in_set[way]->dirty_ = false;///
        //sets_vec[set_i]->lru_update(way); ///
    }
};
/* --------------------------------------------------- External Functions ----------------------------------------- */
/* ####################################### cache_and_globals_init ############################################ */
int cache_and_globals_init(unsigned int MemCyc, unsigned int BSize, unsigned int L1Size, unsigned int L2Size,
                           unsigned int L1Assoc, unsigned int L2Assoc, unsigned int L1Cyc, unsigned int L2Cyc,
                           unsigned int WrAlloc, Cache *L1, Cache *L2) {
    //init global params
    block_size = (unsigned int) pow(2, BSize);  // [Bytes]
    if (block_size == 0) {
        return fail;
        //TODO: throw an exception
    }
    write_allocate = WrAlloc;
    bits_for_offset = BSize;
    // init mem params
    mem_cyc_ = MemCyc;
    // init L1 params
    L1->cache_size_  = (unsigned int) pow(2, L1Size);  // [Bytes]
    L1->cache_assoc_ = (unsigned int) pow(2, L1Assoc); // [Bytes]
    L1->cache_cyc_ = L1Cyc; // number of cycles to access L1
    L1->num_of_blocks_in_a_set_ = L1->cache_size_ / block_size;
    L1->num_of_sets_in_a_cache_ = L1->num_of_blocks_in_a_set_ / L1->cache_assoc_;
    if(L1->num_of_sets_in_a_cache_ <= 0){
        return fail;
        //TODO: throw an exception
    }
    L1->bits_for_set_ = log2(L1->num_of_sets_in_a_cache_);
    L1->bits_for_tag_ = command_size - L1->bits_for_set_ - bits_for_offset;
    L1->cache_misses_ = 0;
    L1->times_to_access_cache_ = 0;
    // for L1: create sets with blocks according to number of sets needed and association level
    for (unsigned int i = 0; i < L1->num_of_sets_in_a_cache_; ++i) {
        L1->sets_vec.push_back(new Set(L1->cache_assoc_, i)); // cache_assoc is ways_num
        // TODO: take care if alloc fails
    }

    // init L2 params
    L2->cache_size_ = (unsigned int) pow(2, L2Size);  // [Bytes]
    L2->cache_assoc_ = (unsigned int) pow(2, L2Assoc);
    L2->cache_cyc_ = L2Cyc; // number of cycles to access L2
    L2->num_of_blocks_in_a_set_ = L2->cache_size_ / block_size;
    if(L2->num_of_sets_in_a_cache_ <= 0){
        return fail;
        //TODO: throw an exception
    }
    L2->num_of_sets_in_a_cache_ = L2->num_of_blocks_in_a_set_ / L2->cache_assoc_;
    L2->bits_for_set_ = log2(L2->num_of_sets_in_a_cache_);
    L2->bits_for_tag_ = command_size - L2->bits_for_set_ - bits_for_offset;
    L2->cache_misses_ = 0;
    L2->times_to_access_cache_ = 0;
    // for L2: create sets with blocks according to number of sets needed and association level
    for (unsigned int i = 0; i < L2->num_of_sets_in_a_cache_; ++i) {
        L2->sets_vec.push_back(new Set(L2->cache_assoc_, i)); // cache_assoc is ways_num
        // TODO: take care if alloc fails
    }
    return 0;
}

/* ############################################ updateL2IfL1Dirty ############################################ */
void updateL2IfL1Dirty(Cache *L1, Cache *L2, unsigned int l1_tag,unsigned int l2_set, unsigned int lru_tag) {
    unsigned int l1_normalized_to_l2 = lru_tag >> (L1->bits_for_tag_ - L2->bits_for_tag_);
    L2->sets_vec[l2_set]->idxOfTagInSet(l1_normalized_to_l2);
    L2->sets_vec[l2_set]->lru_update(L2->sets_vec[l2_set]->idxOfTagInSet(l1_normalized_to_l2));
    //L2->sets_vec[l2_set]->lru_update(L2->sets_vec[l2_set]->return_lru_idx());///
}

/* ############################################ evict_l2 ############################################ */
void evict_l2(Cache *L1, unsigned int l1_tag,Cache *L2, unsigned int l2_set, unsigned int lru_tag) {
    unsigned int l1_normalized_to_l2 = lru_tag >> (L1->bits_for_tag_ - L2->bits_for_tag_);
    L2->invalidate_block(L2->sets_vec[l2_set]->idxOfTagInSet(l1_normalized_to_l2),l2_set); ///
    //L2->sets_vec[l2_set]->blocks_vec_in_set[l1_normalized_to_l2]->valid_ = false;
}

/* ############################################ readFromCache ############################################ */
void readFromCache(Cache *L1, unsigned int l1_set, unsigned int l1_tag,
                   Cache *L2, unsigned int l2_set, unsigned int l2_tag,unsigned int address) {

    // l1_hit/l2_hits return 0 if index for particular tag *has not been not found*
    // or it *has been found but the block is not valid*
    // if it returns 1 it means that index with such tag exists.
    int l1_hit = (L1->sets_vec[l1_set]->idxOfTagInSet(l1_tag) != notFound ? 1 : 0);
    int l2_hit = (L2->sets_vec[l2_set]->idxOfTagInSet(l2_tag) != notFound ? 1 : 0);
    int state = l1_hit * 2 + 1 * l2_hit;
    L1->find_parallel_tag_and_set(L1,L2,l1_set,l2_set);
    data_counter++;

    switch (state) {
        case 0: { // miss in L1 and miss in L2
            L1->cache_misses_++;
            L1->times_to_access_cache_++;
            L2->cache_misses_++;
            L2->times_to_access_cache_++;
            times_to_access_mem++;
            tot_time_to_access_mem += mem_cyc_;
            bool doesBlockExistInL1 = (L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2) != notFound ? true : false);
            if(!L2->sets_vec[l2_set]->isBlockFree()){
                if(doesBlockExistInL1){ //block exists
                    unsigned int idx_of_parallel_tag_to_l2 = L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2);
                    if (L1->sets_vec[l1_set]->blocks_vec_in_set[idx_of_parallel_tag_to_l2]->dirty_) {
                        unsigned dirty_l1_way = L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2);
                        L1->sets_vec[parallel_set_to_l2]->blocks_vec_in_set[dirty_l1_way]->valid_=false;
                        unsigned l2_lru_way = L2->sets_vec[l2_set]->return_lru_idx();
                        L2->sets_vec[l2_set]->blocks_vec_in_set[l2_lru_way]->valid_=false;
                    }
                    else{
                        unsigned dirty_l1_way = L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2);
                        L1->sets_vec[parallel_set_to_l2]->blocks_vec_in_set[dirty_l1_way]->valid_=false;
                    }
                    L2->sets_vec[l2_set]->addBlockToSet(l2_tag,address);
                    if(L1->sets_vec[l1_set]->isLruDirty()){
                        unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                        L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                    }
                    L1->sets_vec[l1_set]->addBlockToSet(l1_tag,address);
                }

                else{ //block doesn't exist in L1
                    if (L2->sets_vec[l2_set]->isLruDirty()) {
                        unsigned int lru_tag = L2->sets_vec[l2_set]->return_lru_tag();
                        L2->make_block_not_dirty(lru_tag,l2_set); // updates memory by making the lru not dirty
                    }
                    L2->sets_vec[l2_set]->addBlockToSet(l2_tag,address);
                    // repeat begin
                    L2->find_parallel_tag_and_set(L1,L2,l1_set,l2_set);
                    if(L1->sets_vec[l1_set]->isLruDirty()) {
                        unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                        L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                    }
                    L1->sets_vec[l1_set]->addBlockToSet(l1_tag,address);
                    // repeat end
                }
            }

            else{ // there is a free block in the set
                L2->sets_vec[l2_set]->addBlockToSet(l2_tag,address);
                L2->find_parallel_tag_and_set(L1,L2,l1_set,l2_set);
                if(L1->sets_vec[l1_set]->isLruDirty()) {
                    unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                    L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                }
                L1->sets_vec[l1_set]->addBlockToSet(l1_tag,address);
            }


            break;
        }

        case 1: { // miss in L1 and hit in L2
            L1->cache_misses_++;
            L1->times_to_access_cache_++;
            L2->times_to_access_cache_++;
            int idx =L2->sets_vec[l2_set]->idxOfTagInSet(l2_tag);
            L2->sets_vec[l2_set]->lru_update(idx);
            if(L1->sets_vec[l1_set]->isLruDirty()) {
                unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
            }
            L1->sets_vec[l1_set]->addBlockToSet(l1_tag,address);
            break;
        }

        default: { // reading from L1 got hit
            L1->times_to_access_cache_++;
            if (L1->sets_vec[l1_set]->idxOfTagInSet(l1_tag) != notFound) { ///
                L1->sets_vec[l1_set]->lru_update(L1->sets_vec[l1_set]->idxOfTagInSet(l1_tag));
            }
            break;
        }
    }
}

/* ############################################ writeToCache ############################################ */
void writeToCache(Cache *L1, unsigned int l1_set, unsigned int l1_tag,
                  Cache *L2, unsigned int l2_set, unsigned int l2_tag,unsigned int address) {
    // l1_hit/l2_hits return 0 if index for particular tag *has not been not found*
    // or it *has been found but the block is not valid*
    // if it returns 1 it means that index with such tag exists.
    data_counter++;
    int l1_hit = (L1->sets_vec[l1_set]->idxOfTagInSet(l1_tag) != notFound ? 1 : 0);
    int l2_hit = (L1->sets_vec[l1_set]->idxOfTagInSet(l2_tag) != notFound ? 1 : 0);
    int state = l1_hit * 2 + 1 * l2_hit;
    L1->find_parallel_tag_and_set(L1,L2,l1_set,l2_set);
    switch (state) {
        case 0: { // miss in L1 and miss in L2
            L1->cache_misses_++;
            L2->cache_misses_++;
            L1->times_to_access_cache_++;
            L2->times_to_access_cache_++;
            times_to_access_mem++;
            tot_time_to_access_mem += mem_cyc_;
            bool doesBlockExistInL1 = (L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2) != notFound ? true : false);
            if (write_allocate == 1) {
                if(!L2->sets_vec[l2_set]->isBlockFree()){
                    if(doesBlockExistInL1){ //block exists
                        unsigned int idx_of_parallel_tag_to_l2 = L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2);
                        if (L1->sets_vec[l1_set]->blocks_vec_in_set[idx_of_parallel_tag_to_l2]->dirty_) {
                            unsigned dirty_l1_way = L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2);
                            L1->sets_vec[parallel_set_to_l2]->blocks_vec_in_set[dirty_l1_way]->valid_=false;
                            unsigned l2_lru_way = L2->sets_vec[l2_set]->return_lru_idx();
                            L2->sets_vec[l2_set]->blocks_vec_in_set[l2_lru_way]->valid_=false;
                        }

                        else{
                            unsigned dirty_l1_way = L1->sets_vec[parallel_set_to_l2]->idxOfTagInSet(parallel_tag_to_l2);
                            L1->sets_vec[parallel_set_to_l2]->blocks_vec_in_set[dirty_l1_way]->valid_=false;
                        }
                        L2->sets_vec[l2_set]->addBlockToSet(l2_tag,address);
                        if(L1->sets_vec[l1_set]->isLruDirty()){
                            unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                            L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                        }
                            L1->sets_vec[l1_set]->addDirtyBlockToSet(l1_tag,address);
                    }

                    else{ //block doesn't exist in L1
                        if (L2->sets_vec[l2_set]->isLruDirty()) {
                            unsigned int lru_tag = L2->sets_vec[l2_set]->return_lru_tag();
                            L2->make_block_not_dirty(lru_tag,l2_set); // updates memory by making the lru not dirty
                        }
                        L2->sets_vec[l2_set]->addBlockToSet(l2_tag,address);
                        // repeat begin
                        L2->find_parallel_tag_and_set(L1,L2,l1_set,l2_set);
                        if(L1->sets_vec[l1_set]->isLruDirty()) {
                            unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                            L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                        }
                        L1->sets_vec[l1_set]->addDirtyBlockToSet(l1_tag,address);
                        // repeat end
                    }
                }

                else{ // there is a free block in the set
                    L2->sets_vec[l2_set]->addBlockToSet(l2_tag,address);
                    L2->find_parallel_tag_and_set(L1,L2,l1_set,l2_set);
                    if(L1->sets_vec[l1_set]->isLruDirty()) {
                        unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                        L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                    }
                    L1->sets_vec[l1_set]->addDirtyBlockToSet(l1_tag,address);
                }
            }

            else{
                /// writes to mem
            }
            break;
        }

        case 1: { // miss in L1 and hit in L2
            L1->cache_misses_++;
            L1->times_to_access_cache_++;
            L2->times_to_access_cache_++;
            if (write_allocate == 1) {
                if (L1->sets_vec[l1_set]->isLruDirty()) {
                    L1->find_parallel_tag_and_set(L1,L2, l1_set, l2_set); // here we use only parallel set/tag_to_l1 (for l2)
                    unsigned dirty_l2_way = L2->sets_vec[parallel_set_to_l1]->idxOfTagInSet(parallel_tag_to_l1);
                    L2->make_block_dirty(dirty_l2_way,parallel_set_to_l1);
                }
                L1->sets_vec[l1_set]->addDirtyBlockToSet(l1_tag,address);
                unsigned int l2_way = L2->sets_vec[l2_set]->idxOfTagInSet(l2_tag);
                L2->sets_vec[l2_set]->lru_update(l2_way);
            }
            else {
                unsigned int l2_way = L2->sets_vec[l2_set]->idxOfTagInSet(l2_tag);
                L2->make_block_dirty(l2_way,l2_tag);
            }
            break;
        }

        default: { // writing to L1 got hit
            L1->times_to_access_cache_++;
            unsigned dirty_idx = L1->sets_vec[l1_set]->idxOfTagInSet(l1_tag);
            L1->make_block_dirty(dirty_idx,l1_set);
            break;
        }
    }


}

/* ############################################ executeOperation ############################################ */
void executeOperation(char operation, unsigned int address, Cache *L1, Cache *L2) {
    // extract the set from the address given
    /* Let address be : tttttttt tttttttt tttaaaaa aaaooooo
     * assume:
     * offset_bits = 5
     * sets_bits = 8
     * tag_bits = 32 - 8 - 5 = 19
     * address << tag_bits : aaaaaaaa ooooo000 00000000 00000000 = tmp
     * set = tmp >> tag_bits + offset_bits = 00000000 00000000 00000000 aaaaaaaa
     * */
    if (L1->bits_for_set_ != 0) {
        L1->set_idx_ = (address << L1->bits_for_tag_) >> (L1->bits_for_tag_ + bits_for_offset);
    } else {
        L1->set_idx_ = 0;
    }
    if (L2->bits_for_set_ != 0) {
        L2->set_idx_ = (address << L2->bits_for_tag_) >> (L2->bits_for_tag_ + bits_for_offset);
    } else {
        L2->set_idx_ = 0;
    }
    // extract the tag from the address given
    /* Let address be : tttttttt tttttttt tttaaaaa aaaooooo
     * assume:
     * offset_bits = 5
     * sets_bits = 8
     * tag_bits = 32 - 8 - 5 = 19
     * tag = address >> (set_bits+offset_bits) : 00000000 00000ttt tttttttt tttttttt
     * */
    unsigned int l1_tag = address >> (L1->bits_for_set_ + bits_for_offset);
    unsigned int l2_tag = address >> (L2->bits_for_set_ + bits_for_offset);

    // update statistics since executing operation requires access through L1 always

    // execute writing / reading
    switch (operation) {
        case 'w': {
            writeToCache(L1, L1->set_idx_, l1_tag, L2, L2->set_idx_, l2_tag,address);
            break;
        }
        case 'r': {
            readFromCache(L1, L1->set_idx_, l1_tag, L2, L2->set_idx_, l2_tag,address);
            break;
        }
    }
}

/* ############################################ getStats ############################################ */
void getStats(double *L1MissRate, double *L2MissRate, double *avgAccTime, Cache *L1, Cache *L2) {
    *L1MissRate = 0, *L2MissRate = 0, *avgAccTime = 0;

    if (L1->cache_misses_ != 0)
        *L1MissRate = (double) L1->cache_misses_ / L1->times_to_access_cache_;
    if (L2->cache_misses_ != 0)
        *L2MissRate = (double) L2->cache_misses_ / L2->times_to_access_cache_;

    times_to_access_data = L1->times_to_access_cache_ + L2->times_to_access_cache_ + times_to_access_mem;
    tot_time_to_access_data =
            L1->times_to_access_cache_ * L1->cache_cyc_ + L2->times_to_access_cache_ * L2->cache_cyc_ +
            times_to_access_mem * mem_cyc_;
    if (times_to_access_data != 0)
        *avgAccTime = (double) tot_time_to_access_data / data_counter;
}

/* ---------------------------------------------------- Main -------------------------------------------------- */
int main(int argc, char **argv) {

    if (argc < 19) {
        cerr << "Not enough arguments" << endl;
        return 0;
    }

    // Get input arguments

    // File
    // Assuming it is the first argument
    char *fileString = argv[1];
    ifstream file(fileString); //input file stream
    string line;
    if (!file || !file.good()) {
        // File doesn't exist or some other error
        cerr << "File not found" << endl;
        return 0;
    }

    unsigned MemCyc = 0, BSize = 0, L1Size = 0, L2Size = 0, L1Assoc = 0,
            L2Assoc = 0, L1Cyc = 0, L2Cyc = 0, WrAlloc = 0;

    for (int i = 2; i < 19; i += 2) {
        string s(argv[i]);
        if (s == "--mem-cyc") {
            MemCyc = atoi(argv[i + 1]);
        } else if (s == "--bsize") {
            BSize = atoi(argv[i + 1]);
        } else if (s == "--l1-size") {
            L1Size = atoi(argv[i + 1]);
        } else if (s == "--l2-size") {
            L2Size = atoi(argv[i + 1]);
        } else if (s == "--l1-cyc") {
            L1Cyc = atoi(argv[i + 1]);
        } else if (s == "--l2-cyc") {
            L2Cyc = atoi(argv[i + 1]);
        } else if (s == "--l1-assoc") {
            L1Assoc = atoi(argv[i + 1]);
        } else if (s == "--l2-assoc") {
            L2Assoc = atoi(argv[i + 1]);
        } else if (s == "--wr-alloc") {
            WrAlloc = atoi(argv[i + 1]);
        } else {
            cerr << "Error in arguments" << endl;
            return 0;
        }
    }
    /*------------------------------------------ addition I begin ----------------------------------------------- */
    Cache L1;
    Cache L2;
    if (cache_and_globals_init(MemCyc, BSize, L1Size, L2Size, L1Assoc, L2Assoc, L1Cyc, L2Cyc, WrAlloc, &L1, &L2) < 0) {
        return fail;
    }
    /*------------------------------------------ addition I end ------------------------------------------------- */

    while (getline(file, line)) {

        stringstream ss(line);
        string address;
        char operation = 0; // read (R) or write (W)
        if (!(ss >> operation >> address)) {
            // Operation appears in an Invalid format
            cout << "Command Format error" << endl;
            return 0;
        }

        // DEBUG - remove this line
        cout << "operation: " << operation;

        string cutAddress = address.substr(2); // Removing the "0x" part of the address

        // DEBUG - remove this line
        cout << ", address (hex)" << cutAddress;

        unsigned long int num = 0;
        num = strtoul(cutAddress.c_str(), NULL, 16);
        /*----------------------------------------- addition II begin ----------------------------------------------- */
        executeOperation(operation, num, &L1, &L2);
        /*------------------------------------------ addition II end ------------------------------------------------- */

        // DEBUG - remove this line
        cout << " (dec) " << num << endl;

    }

    double L1MissRate;
    double L2MissRate;
    double avgAccTime;
    /*------------------------------------------ addition III begin ----------------------------------------------- */
    getStats(&L1MissRate, &L2MissRate, &avgAccTime, &L1, &L2);
    /*------------------------------------------ addition III end ------------------------------------------------- */

  // cout << "L1miss=%.03f " << L1MissRate << endl;
 // cout << "L2miss=%.03f " << L2MissRate << endl;
   // cout << "AccTimeAvg=%.03f\n" << avgAccTime << endl;
   printf("L1miss=%.03f ", L1MissRate);
   printf("L2miss=%.03f ", L2MissRate);
    printf("AccTimeAvg=%.03f\n", avgAccTime);
    //cout << " fuck this shit!!!!! "  << endl;

    return 0;
}