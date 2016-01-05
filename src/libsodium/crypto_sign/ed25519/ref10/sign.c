
//#include <string.h>

//#include "crypto_hash_sha512.h"
//#include "crypto_sign_ed25519.h"
//#include "utils.h"
//#include "../../../crypto_core/curve25519/ref10/curve25519_ref10.h"

#define NULL 0

typedef int crypto_hash_sha512_state;
typedef int ge_p3;

void crypto_hash_sha512(char *az, char *sk, unsigned long length);
    //@ requires true;
    //@ ensures true;

void crypto_hash_sha512_init(crypto_hash_sha512_state *hs);
    //@ requires true;
    //@ ensures true;

void crypto_hash_sha512_update(crypto_hash_sha512_state *hs, char *az, unsigned long length);
    //@ requires true;
    //@ ensures true;

void crypto_hash_sha512_final(crypto_hash_sha512_state *hs, char *nonce);
    //@ requires true;
    //@ ensures true;

void memmove(void *to, void *from, unsigned long size);
    //@ requires true;
    //@ ensures true;

void sc_reduce(char *nonce);
    //@ requires true;
    //@ ensures true;

void ge_scalarmult_base(ge_p3 *R, char *nonce);
    //@ requires true;
    //@ ensures true;

void ge_p3_tobytes(char *sig, ge_p3 *R);
    //@ requires true;
    //@ ensures true;

void sc_muladd(char *sig, char *hram, char *az, char *nonce);
    //@ requires true;
    //@ ensures true;

void sodium_memzero(char *buf, unsigned long size);
    //@ requires true;
    //@ ensures true;

//@ predicate integer_opt(int *p;) = p == 0 ? true : integer(p, _);

int
crypto_sign_ed25519_detached(char *sig, /*unsigned long long*/ int *siglen_p,
                             /*const*/ char *m, unsigned /*long*/ long mlen,
                             /*const*/ char *sk)
    //@ requires integer_opt(siglen_p);
    //@ ensures siglen_p == 0 ? true : integer(siglen_p, 64);
{
    crypto_hash_sha512_state hs;
    char az[64];
    char nonce[64];
    char hram[64];
    ge_p3 R;

    crypto_hash_sha512(az, sk, 32);
    az[0] = (char)(az[0] & 248);
    az[31] = (char)(az[31] & 63);
    az[31] = (char)(az[31] | 64);

    crypto_hash_sha512_init(&hs);
    crypto_hash_sha512_update(&hs, (char *)az + 32, 32);
    crypto_hash_sha512_update(&hs, m, mlen);
    crypto_hash_sha512_final(&hs, nonce);

    memmove(sig + 32, sk + 32, 32);

    sc_reduce(nonce);
    ge_scalarmult_base(&R, nonce);
    ge_p3_tobytes(sig, &R);

    crypto_hash_sha512_init(&hs);
    crypto_hash_sha512_update(&hs, sig, 64);
    crypto_hash_sha512_update(&hs, m, mlen);
    crypto_hash_sha512_final(&hs, hram);

    sc_reduce(hram);
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
