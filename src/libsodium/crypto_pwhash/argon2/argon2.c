/*
 * Argon2 source code package
 *
 * Written by Daniel Dinu and Dmitry Khovratovich, 2015
 *
 * This work is licensed under a Creative Commons CC0 1.0 License/Waiver.
 *
 * You should have received a copy of the CC0 Public Domain Dedication along
 * with
 * this software. If not, see
 * <http://creativecommons.org/publicdomain/zero/1.0/>.
 */

#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>


#include "utils.h"

#include "argon2.h"
#include "argon2-encoding.h"
#include "argon2-core.h"

int argon2_core(argon2_context *context, argon2_type type) {
    /* 1. Validate all inputs */
    int result = validate_inputs(context);
    uint32_t memory_blocks, segment_length;
    argon2_instance_t instance;

    if (ARGON2_OK != result) {
        return result;
    }

    if (Argon2_i != type) {
        return ARGON2_INCORRECT_TYPE;
    }

    /* 2. Align memory size */
    /* Minimum memory_blocks = 8L blocks, where L is the number of lanes */
    memory_blocks = context->m_cost;

    if (memory_blocks < 2 * ARGON2_SYNC_POINTS * context->lanes) {
        memory_blocks = 2 * ARGON2_SYNC_POINTS * context->lanes;
    }

    segment_length = memory_blocks / (context->lanes * ARGON2_SYNC_POINTS);
    /* Ensure that all segments have equal length */
    memory_blocks = segment_length * (context->lanes * ARGON2_SYNC_POINTS);

    instance.region = NULL;
    instance.passes = context->t_cost;
    instance.memory_blocks = memory_blocks;
    instance.segment_length = segment_length;
    instance.lane_length = segment_length * ARGON2_SYNC_POINTS;
    instance.lanes = context->lanes;
    instance.threads = context->threads;
    instance.type = type;

    /* 3. Initialization: Hashing inputs, allocating memory, filling first
     * blocks
     */
    result = initialize(&instance, context);

    if (ARGON2_OK != result) {
        return result;
    }

    /* 4. Filling memory */
    fill_memory_blocks(&instance);

    /* 5. Finalization */
    finalize(context, &instance);

    return ARGON2_OK;
}

int argon2_hash(const uint32_t t_cost, const uint32_t m_cost,
                const uint32_t parallelism, const void *pwd,
                const size_t pwdlen, const void *salt, const size_t saltlen,
                void *hash, const size_t hashlen, char *encoded,
                const size_t encodedlen, argon2_type type) {

    argon2_context context;
    int result;
    uint8_t *out;

    if (pwdlen > UINT32_MAX) {
        return ARGON2_PWD_TOO_LONG;
    }

    if (hashlen > UINT32_MAX) {
        return ARGON2_OUTPUT_TOO_LONG;
    }

    if (saltlen > UINT32_MAX) {
        return ARGON2_SALT_TOO_LONG;
    }

    out = (uint8_t *) malloc(hashlen);
    if (!out) {
        return ARGON2_MEMORY_ALLOCATION_ERROR;
    }

    context.out = (uint8_t *)out;
    context.outlen = (uint32_t)hashlen;
    context.pwd = (uint8_t *)pwd;
    context.pwdlen = (uint32_t)pwdlen;
    context.salt = (uint8_t *)salt;
    context.saltlen = (uint32_t)saltlen;
    context.secret = NULL;
    context.secretlen = 0;
    context.ad = NULL;
    context.adlen = 0;
    context.t_cost = t_cost;
    context.m_cost = m_cost;
    context.lanes = parallelism;
    context.threads = parallelism;
    context.flags = ARGON2_DEFAULT_FLAGS;

    result = argon2_core(&context, type);

    if (result != ARGON2_OK) {
        memset(out, 0x00, hashlen);
        free(out);
        return result;
    }

    /* if raw hash requested, write it */
    if (hash) {
        memcpy(hash, out, hashlen);
    }

    /* if encoding requested, write it */
    if (encoded && encodedlen) {
        if (!encode_string(encoded, encodedlen, &context, type)) {
            memset(out, 0x00, hashlen);
            memset(encoded, 0x00, encodedlen);
            free(out);
            return ARGON2_ENCODING_FAIL;
        }
    }

    free(out);

    return ARGON2_OK;
}

int argon2i_hash_encoded(const uint32_t t_cost, const uint32_t m_cost,
                         const uint32_t parallelism, const void *pwd,
                         const size_t pwdlen, const void *salt,
                         const size_t saltlen, const size_t hashlen,
                         char *encoded, const size_t encodedlen) {

    return argon2_hash(t_cost, m_cost, parallelism, pwd, pwdlen, salt, saltlen,
                       NULL, hashlen, encoded, encodedlen, Argon2_i);
}

int argon2i_hash_raw(const uint32_t t_cost, const uint32_t m_cost,
                     const uint32_t parallelism, const void *pwd,
                     const size_t pwdlen, const void *salt,
                     const size_t saltlen, void *hash, const size_t hashlen) {

    return argon2_hash(t_cost, m_cost, parallelism, pwd, pwdlen, salt, saltlen,
                       hash, hashlen, NULL, 0, Argon2_i);
}

int argon2_verify(const char *encoded, const void *pwd, const size_t pwdlen,
                  argon2_type type) {

    argon2_context ctx;
    uint8_t *out;
    int ret;

    /* max values, to be updated in decode_string */
    ctx.adlen = 512;
    ctx.saltlen = 512;
    ctx.outlen = 512;

    ctx.ad = (uint8_t *) malloc(ctx.adlen);
    ctx.salt = (uint8_t *) malloc(ctx.saltlen);
    ctx.out = (uint8_t *) malloc(ctx.outlen);
    if (!ctx.out || !ctx.salt || !ctx.ad) {
        free(ctx.ad);
        free(ctx.salt);
        free(ctx.out);
        return ARGON2_MEMORY_ALLOCATION_ERROR;
    }
    out = (uint8_t *) malloc(ctx.outlen);
    if (!out) {
        free(ctx.ad);
        free(ctx.salt);
        free(ctx.out);
        return ARGON2_MEMORY_ALLOCATION_ERROR;
    }

    if(decode_string(&ctx, encoded, type) != 1) {
        free(ctx.ad);
        free(ctx.salt);
        free(ctx.out);
        free(out);
        return ARGON2_DECODING_FAIL;
    }

    ret = argon2_hash(ctx.t_cost, ctx.m_cost, ctx.threads, pwd, pwdlen, ctx.salt,
                      ctx.saltlen, out, ctx.outlen, NULL, 0, type);

    free(ctx.ad);
    free(ctx.salt);

    if (ret != ARGON2_OK || sodium_memcmp(out, ctx.out, ctx.outlen) != 0) {
        free(out);
        free(ctx.out);
        return ARGON2_DECODING_FAIL;
    }
    free(out);
    free(ctx.out);

    return ARGON2_OK;
}

int argon2i_verify(const char *encoded, const void *pwd, const size_t pwdlen) {
    return argon2_verify(encoded, pwd, pwdlen, Argon2_i);
}

int argon2i(argon2_context *context) {
    return argon2_core(context, Argon2_i);
}

int verify_i(argon2_context *context, const char *hash) {
    int result;
    if (0 == context->outlen || NULL == hash) {
        return ARGON2_OUT_PTR_MISMATCH;
    }

    result = argon2_core(context, Argon2_i);

    if (ARGON2_OK != result) {
        return result;
    }

    return 0 == memcmp(hash, context->out, context->outlen);
}
