#ifndef SIGN_H
#define SIGN_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"
#include "api.h"
#include "polyvec.h"
#include "poly.h"

#define challenge DILITHIUM_NAMESPACE(challenge)
void challenge(poly *c, const uint8_t seed[SEEDBYTES]);
struct strategy_1_sk_precomp {
  polyveck t0hat, s2hat;
  polyvecl mat[K], s1hat;
  uint8_t key[SEEDBYTES], tr[CRHBYTES];
};

void precompute_strategy_1_sk_parts(struct strategy_1_sk_precomp* precomp,
                                    const uint8_t* sk);

int crypto_sign_signature(uint8_t* sig,
                          size_t* siglen,
                          const uint8_t* m,
                          size_t mlen,
                          const struct strategy_1_sk_precomp* precomp);
int crypto_sign(uint8_t* sm,
                size_t* smlen,
                const uint8_t* msg,
                size_t len,
                const struct strategy_1_sk_precomp* sk_precomp
);
// #define crypto_sign_keypair DILITHIUM_NAMESPACE(crypto_sign_keypair)
// int crypto_sign_keypair(uint8_t *pk, uint8_t *sk);

// #define crypto_sign_signature DILITHIUM_NAMESPACE(signature)
// int crypto_sign_signature(uint8_t *sig, size_t *siglen,
//                           const uint8_t *m, size_t mlen,
//                           const uint8_t *sk);

// #define crypto_sign DILITHIUM_NAMESPACE(crypto_sign)
// int crypto_sign(uint8_t *sm, size_t *smlen,
//                 const uint8_t *m, size_t mlen,
//                 const uint8_t *sk);

// #define crypto_sign_verify DILITHIUM_NAMESPACE(verify)
// int crypto_sign_verify(const uint8_t *sig, size_t siglen,
//                        const uint8_t *m, size_t mlen,
//                        const uint8_t *pk);

// #define crypto_sign_open DILITHIUM_NAMESPACE(crypto_sign_open)
// int crypto_sign_open(uint8_t *m, size_t *mlen,
//                      const uint8_t *sm, size_t smlen,
//                      const uint8_t *pk);

#endif
