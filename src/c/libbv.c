#include <stdint.h>

#define FULL      0xFFFFFFFFFFFFFFFF
#define EMPTY     0x0000000000000000
#define MASK8     0xFFLL
#define MASK16    0xFFFFLL
#define MASK32    0xFFFFFFFFLL
#define MASK(LEN) (FULL >> (64 - (LEN)))
#define MAX(A, B) (A > B? A : B)
#define MIN(A, B) (A < B? A : B)

uint64_t bv_test(uint8_t idx, uint8_t len, uint64_t val){
  idx = MASK(6) & idx;
  len = len <= 64 ? len : 64;
  val = MASK(len) & val;
  return (val & (1LL << idx)) > 0 ? 1LL : 0LL;
}

uint64_t bv_reverse(uint8_t len, uint64_t val){
  len = len <= 64 ? len : 64;
  val = MASK(len) & val;

  uint8_t i;
  uint64_t val_res = EMPTY;
  
  for (i = 0; i < len; i++)
    val_res += (bv_test(i, len, val) << (len-1-i));
  
  return val_res;
}

uint64_t bv_slice(uint8_t lb, uint8_t ub, \
		  uint8_t len, uint64_t val) {
  len = len <= 64 ? len : 64;
  val = MASK(len) & val;
    
  uint64_t val_res = EMPTY;
  uint8_t i;
  uint64_t msk_lb = FULL << lb;
  uint64_t msk_ub = FULL >> (64 - ub);
  uint64_t msk = msk_lb & msk_ub;
  val_res = (val & msk) >> lb;

  /* for(i = lb; i < ub; i++) */
  /*   if(bv_test(i, len, val) == 1) */
  /*     val_res += (1LL << (i-lb)); */
  
  return val_res;
}

uint64_t bv_sign_ext(uint8_t len, uint64_t val) {
  len = len <= 64 ? len : 64;

  uint64_t msk = MASK(len);
  uint64_t sign = bv_test(len-1, len, val);

  return ((sign==1) ? ((val & msk) + (FULL ^ msk)) : (val & msk));
}

uint64_t bv_zero_ext(uint8_t len, uint64_t val) {
  len = len <= 64 ? len : 64;
  return (val & MASK(len));
}

uint64_t bv_neg(uint8_t len, uint64_t val){
  len = len <= 64 ? len : 64;
  return ((~val) & MASK(len));
}

uint64_t bv_and(uint8_t len, uint64_t val_1, uint64_t val_2){
  len = len <= 64 ? len : 64;
  val_1 = val_1 & MASK(len);
  val_2 = val_2 & MASK(len);
  return val_1 & val_2;
}

uint64_t bv_or(uint8_t len, uint64_t val_1, uint64_t val_2){
  len = len <= 64 ? len : 64;
  val_1 = val_1 & MASK(len);
  val_2 = val_2 & MASK(len);
  return val_1 | val_2;
}

uint64_t bv_xor(uint8_t len, uint64_t val_1, uint64_t val_2){
  len = len <= 64 ? len : 64;
  val_1 = val_1 & MASK(len);
  val_2 = val_2 & MASK(len);
  return val_1 ^ val_2;
}

uint64_t bv_add(uint8_t len, uint64_t val_1, uint64_t val_2){
  len = len <= 63 ? len : 63;
  val_1 = val_1 & MASK(len);
  val_2 = val_2 & MASK(len);
  
  return (val_1 + val_2) & MASK(len+1);
}

uint64_t bv_complement(uint8_t len, uint64_t val) {
  len = len <= 64 ? len : 64;
  val = val & MASK(len);
  return ((~val) + 1LL) & MASK(len);
}

uint64_t bv_sub(uint8_t len, uint64_t val_1, uint64_t val_2) {
  len = len <= 64 ? len : 64;
  val_1 = val_1 & MASK(len);
  val_2 = val_2 & MASK(len);
  return bv_add(len, val_1, bv_complement(len, val_2)) & MASK(len);
}

uint64_t bv_concatenate(uint8_t len_1, uint64_t val_1, \
			uint8_t len_2, uint64_t val_2) {
  uint64_t msk_1 = MASK(len_1);
  uint64_t msk_2 = MASK(len_2);
  val_1 = val_1 & msk_1;
  val_2 = val_2 & msk_2;
  return (val_1 << len_2) + val_2;
}

uint64_t bv_srl(uint8_t len_1, uint64_t val_1, \
		uint8_t len_2, uint64_t val_2) {
  len_1 = len_1 <= 6  ? len_1 : 6;
  len_2 = len_2 <= 64 ? len_2 : 64;
  val_1 = val_1 & MASK(len_1);
  val_2 = val_2 & MASK(len_2);
  return (val_2 >> val_1) & MASK(len_2);
}

uint64_t bv_srl_2(uint8_t sht, uint8_t len, uint64_t val) {
  sht = sht <= len  ? sht : len;
  val = val & MASK(len);
  return (val >> sht) & MASK(len);
}

uint64_t bv_sra(uint8_t len_1, uint64_t val_1, \
		uint8_t len_2, uint64_t val_2) {
  len_1 = len_1 <= 6  ? len_1 : 6;
  len_2 = len_2 <= 64 ? len_2 : 64;
  val_1 = val_1 & MASK(len_1);
  val_2 = val_2 & MASK(len_2);
  uint64_t sign = bv_test(len_2-1, len_2, val_2);
  return ((val_2 >> val_1) & MASK(len_2))	\
       + ((sign == 1)				\
	  ? ((FULL << ((len_2 > val_1)		\
		       ? len_2 - val_1 : 0))	\
	     & MASK(len_2))			\
	  : EMPTY);
}

uint64_t bv_sra_2(uint8_t sht, uint8_t len, uint64_t val) {
  sht = sht <= len  ? sht : len;
  val = val & MASK(len);
  uint64_t val_shifted = (val >> sht) & MASK(len);
  uint64_t sign = bv_test(len-1, len, val);
  uint64_t signs = 0;
  
  if (sign == 1){
    signs = FULL << (len - sht);
  }

  return (signs + val_shifted) & MASK(len);
}

uint64_t bv_sll(uint8_t len_1, uint64_t val_1, \
		uint8_t len_2, uint64_t val_2) {
  len_1 = len_1 <= 6  ? len_1 : 6;
  len_2 = len_2 <= 64 ? len_2 : 64;
  val_1 = val_1 & MASK(len_1);
  val_2 = val_2 & MASK(len_2);
  return (val_2 << val_1) & MASK(len_2);
}

uint64_t bv_sll_2(uint8_t sht, uint8_t len, uint64_t val) {
  sht = sht <= len  ? sht : len;
  val = val & MASK(len);
  return (val << sht) & MASK(len);
}

uint64_t bv_lt(uint8_t len, uint64_t val_1, uint64_t val_2) {
  len = len <= 64 ? len : 64;
  
  val_1 = val_1 & MASK(len);
  val_1 = bv_sign_ext(len, val_1);
  
  val_2 = val_2 & MASK(len);
  val_2 = bv_sign_ext(len, val_2);
  
  return (((int64_t) val_1) < ((int64_t) val_2)) ? 1 : 0;
}

uint64_t bv_eq(uint8_t len, uint64_t val_1, uint64_t val_2) {
  len = len <= 64 ? len : 64;
  val_1 = val_1 & MASK(len);
  val_2 = val_2 & MASK(len);
  
  return (val_1 == val_2) ? 1 : 0;
}

uint64_t bv_ltu(uint8_t len, uint64_t val_1, uint64_t val_2) {
  len = len <= 64 ? len : 64;
  
  val_1 = val_1 & MASK(len);
  val_1 = bv_zero_ext(len, val_1);
  
  val_2 = val_2 & MASK(len);
  val_2 = bv_zero_ext(len, val_2);
  
  return (val_1 < val_2) ? 1 : 0;
}

uint64_t bv_mult18(uint64_t val_1, uint64_t val_2) {

  uint64_t res;
  
  val_1 = val_1 & MASK(18);
  val_1 = bv_sign_ext(18, val_1);
  
  val_2 = val_2 & MASK(18);
  val_2 = bv_sign_ext(18, val_2);

  res = ((int64_t) val_1) * ((int64_t) val_2);
  res = res & MASK(36);
  
  return res;
}
