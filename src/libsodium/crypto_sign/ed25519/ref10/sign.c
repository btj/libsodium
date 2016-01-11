
//#include <string.h>

//#include "crypto_hash_sha512.h"
//#include "crypto_sign_ed25519.h"
//#include "utils.h"
//#include "../../../crypto_core/curve25519/ref10/curve25519_ref10.h"

/*@

lemma_auto void uchars_split(unsigned char *array, int offset);
   requires [?f]uchars(array, ?n, ?cs) &*& 0 <= offset &*& offset <= n;
   ensures
       [f]uchars(array, offset, take(offset, cs))
       &*& [f]uchars(array + offset, n - offset, drop(offset, cs))
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma_auto void uchars_join(unsigned char *array);
    requires [?f]uchars(array, ?n, ?cs) &*& [f]uchars(array + n, ?n0, ?cs0);
    ensures [f]uchars(array, n + n0, append(cs, cs0));

lemma void uchars_limits(unsigned char *array);
    requires [?f]uchars(array, ?n, ?cs) &*& true == ((unsigned char *)0 <= array) &*& array <= (unsigned char *)UINTPTR_MAX;
    ensures [f]uchars(array, n, cs) &*& true == ((unsigned char *)0 <= array) &*& array + n <= (unsigned char *)UINTPTR_MAX;

@*/

#define NULL 0

typedef int crypto_hash_sha512_state;
typedef int ge_p3;

void crypto_hash_sha512(unsigned char *out, unsigned char *in, unsigned long inlen);
    //@ requires out[..64] |-> _ &*& in[..inlen] |-> _;
    //@ ensures out[..64] |-> _ &*& in[..inlen] |-> _;

//@ predicate crypto_hash_sha512_state(crypto_hash_sha512_state *state) = integer(state, _);

void crypto_hash_sha512_init(crypto_hash_sha512_state *hs);
    //@ requires integer((void *)hs, _);
    //@ ensures crypto_hash_sha512_state(hs);

void crypto_hash_sha512_update(crypto_hash_sha512_state *hs, unsigned char *in, unsigned long inlen);
    //@ requires crypto_hash_sha512_state(hs) &*& in[..inlen] |-> _;
    //@ ensures crypto_hash_sha512_state(hs) &*& in[..inlen] |-> _;

void crypto_hash_sha512_final(crypto_hash_sha512_state *hs, unsigned char *out);
    //@ requires crypto_hash_sha512_state(hs) &*& out[..64] |-> _;
    //@ ensures integer((void *)hs, _) &*& out[..64] |-> _;

void memmove(unsigned char *to, unsigned char *from, unsigned long size);
    //@ requires to[..size] |-> _ &*& from[..size] |-> ?cs;
    //@ ensures to[..size] |-> cs &*& from[..size] |-> cs;

void sc_reduce(unsigned char *buf);
    //@ requires buf[..64] |-> _;
    //@ ensures buf[..64] |-> _;

//@ predicate ge_p3(ge_p3 *p;) = integer(p, _);

void ge_scalarmult_base(ge_p3 *R, unsigned char *buf);
    //@ requires ge_p3(R) &*& buf[..64] |-> _;
    //@ ensures ge_p3(R) &*& buf[..64] |-> _;

void ge_p3_tobytes(unsigned char *sig, ge_p3 *R);
    //@ requires sig[..64] |-> _ &*& ge_p3(R);
    //@ ensures sig[..64] |-> _ &*& ge_p3(R);

void sc_muladd(unsigned char *sig, unsigned char *hram, unsigned char *az, unsigned char *nonce);
    //@ requires sig[..32] |-> _ &*& hram[..64] |-> _ &*& az[..64] |-> _ &*& nonce[..64] |-> _;
    //@ ensures sig[..32] |-> _ &*& hram[..64] |-> _ &*& az[..64] |-> _ &*& nonce[..64] |-> _;

void sodium_memzero(unsigned char *buf, unsigned long size);
    //@ requires buf[..size] |-> _;
    //@ ensures buf[..size] |-> _;

//@ predicate integer_opt(int *p;) = p == 0 ? true : integer(p, _);

int
crypto_sign_ed25519_detached(unsigned char *sig, /*unsigned long long*/ int *siglen_p,
                             /*const*/ unsigned char *m, unsigned /*long*/ long mlen,
                             /*const*/ unsigned char *sk)
    //@ requires sig[..64] |-> _ &*& integer_opt(siglen_p) &*& m[..mlen] |-> _ &*& sk[..64] |-> _;
    //@ ensures sig[..64] |-> _ &*& m[..mlen] |-> _ &*& sk[..64] |-> _ &*& siglen_p == 0 ? true : integer(siglen_p, 64);
{
    crypto_hash_sha512_state hs;
    unsigned char az[64];
    unsigned char nonce[64];
    unsigned char hram[64];
    ge_p3 R;

    crypto_hash_sha512(az, sk, 32);
    unsigned char az0 = az[0];
    //@ produce_limits(az0);
    unsigned char az31 = az[31];
    //@ produce_limits(az31);
    az[0] = (unsigned char)((int)az0 & 248);
    az[31] = (unsigned char)((int)az31 & 63);
    az[31] = (unsigned char)((int)az31 | 64);

    crypto_hash_sha512_init(&hs);
    //@ uchars_split(az, 32);
    crypto_hash_sha512_update(&hs, (unsigned char *)az + 32, 32);
    crypto_hash_sha512_update(&hs, m, mlen);
    crypto_hash_sha512_final(&hs, nonce);

    //@ uchars_split(sig, 32);
    //@ uchars_split(sk, 32);
    //@ uchars_limits(sig);
    //@ uchars_limits(sk);
    memmove(sig + 32, sk + 32, 32);

    sc_reduce(nonce);
    ge_scalarmult_base(&R, nonce);
    ge_p3_tobytes(sig, &R);

    crypto_hash_sha512_init(&hs);
    crypto_hash_sha512_update(&hs, sig, 64);
    crypto_hash_sha512_update(&hs, m, mlen);
    crypto_hash_sha512_final(&hs, hram);

    sc_reduce(hram);
    //@ uchars_split(sig, 32);
    sc_muladd(sig + 32, hram, az, nonce);

    sodium_memzero(az, 64);

    if (siglen_p != NULL) {
        *siglen_p = 64;
    }
    return 0;
}

int
crypto_sign_ed25519(unsigned char *sm, unsigned /*long*/ long *smlen_p,
                    /*const*/ unsigned char *m, unsigned /*long*/ long mlen,
                    /*const*/ unsigned char *sk)
{
    unsigned /*long*/ long siglen;

    memmove(sm + crypto_sign_ed25519_BYTES, m, mlen);
/* LCOV_EXCL_START */
    if (crypto_sign_ed25519_detached(sm, &siglen,
                                     sm + crypto_sign_ed25519_BYTES,
                                     mlen, sk) != 0 ||
        siglen != crypto_sign_ed25519_BYTES) {
        if (smlen_p != NULL) {
            *smlen_p = 0;
        }
        memset(sm, 0, mlen + crypto_sign_ed25519_BYTES);
        return -1;
    }
/* LCOV_EXCL_STOP */

    if (smlen_p != NULL) {
        *smlen_p = mlen + siglen;
    }
    return 0;
}
