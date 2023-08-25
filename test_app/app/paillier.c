#include "paillier.h"

// LCM for BIGNUMs 最大公约数,L函数用到
static int BN_lcm(BIGNUM *r, const BIGNUM *a, const BIGNUM *b, BN_CTX *ctx)
{
    int ret = 0;
    BN_CTX_start(ctx);

    BIGNUM *tmp = BN_CTX_get(ctx);
    BIGNUM *gcd = BN_CTX_get(ctx);

    //lcm = a*b/gcd(a,b)
    if (!BN_gcd(gcd, a, b, ctx))
        goto end;
    if (!BN_div(tmp, NULL, a, gcd, ctx))
        goto end;
    if (!BN_mul(r, b, tmp, ctx))
        goto end;

    ret = 1;
end:
    if (ret != 1)
    {
       printf("error\n");
    } 

    BN_CTX_end(ctx);
    return ret;
}

static int genprime_cb(int p, int n, BN_GENCB *arg)
{
    char c = '*';

    if (p == 0)
        c = '.';
    if (p == 1)
        c = '+';
    if (p == 2)
        c = '*';
    if (p == 3)
        c = '\n';
//    putc(c, stderr);
//    fflush(stderr);
    return 1;
}

// L函数 (x-1)/n
static int L(BIGNUM *res, const BIGNUM *u, const BIGNUM *n, BN_CTX *ctx)
{
    int ret = 1;

    BIGNUM *u_cp = BN_dup(u);
    if (!BN_sub_word(u_cp, 1))
        goto end;
    if (!BN_div(res, NULL, u_cp, n, ctx))
        goto end;

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    } 

    BN_free(u_cp);
    return ret;
}

//For generate random keys
int generateRandomKeys(paillierKeys *keys, int key_len, BN_CTX *ctx)
{
//    BN_GENCB cb;
//    struct bn_gencb_st cb;
    int ret = 1;
    BIGNUM *p, *q, *tmp, *n, *n2, *g, *lamda, *mu;

    BN_CTX_start(ctx);

    // Temp BIGNUMs,会被是放掉
    p = BN_CTX_get(ctx);
    q = BN_CTX_get(ctx);
    tmp = BN_CTX_get(ctx);

    // Part of the keys BIGNUMs
    n = BN_new();
    n2 = BN_new();
    g = BN_new();
    lamda = BN_new();
    mu = BN_new();

    // Choose two large prime numbers p,q
    // This numbers have to hold gcd(pq, (p-1)(q-1)) = 1
    do
    {
       // BN_GENCB_set(&cb, genprime_cb, NULL);
        if (!BN_generate_prime_ex(p, key_len, 0, NULL, NULL, NULL))
            goto end;
        if (!BN_generate_prime_ex(q, key_len, 0, NULL, NULL, NULL))
            goto end;

        // Compute n = pq
        if (!BN_mul(n, p, q, ctx))
            goto end;

        // Test if primes are ok
        if (!BN_sub_word(p, 1))
            goto end;
        if (!BN_sub_word(q, 1))
            goto end;
        if (!BN_mul(tmp, p, q, ctx))
            goto end;
    }
    while (BN_cmp(p, q) == 0 || BN_gcd(tmp, tmp, n, ctx) != 1);

    // lamda = lcm(p-1,q-1)
    if (!BN_lcm(lamda, p, q, ctx))
        goto end;

    // calculate n的平方
    if (!BN_mul(n2, n, n, ctx))
        goto end;
    do
    {
        // Select a random integer g mod n2
        do
        {
            if (!BN_rand_range(g, n2))
                goto end;
        }
        while (BN_is_zero(g));

        // Calculate mu
        if (!BN_mod_exp(tmp, g, lamda, n2, ctx))
            goto end;
        if (L(tmp, tmp, n, ctx) != 0)
            goto end;
        BN_mod_inverse(mu, tmp, n, ctx);
    }
    while (mu == NULL);

    keys->pub.n = n;
    keys->pub.n2 = n2;
    keys->pub.g = g;

    keys->priv.n = BN_dup(n);
    keys->priv.n2 = BN_dup(n2);
    keys->priv.lamda = lamda;
    keys->priv.mu = mu;

    keys->n = BN_dup(n);
    keys->n2 = BN_dup(n2);

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);
    return ret;
}

int encrypt(BIGNUM *c, const BIGNUM *m, const pubKey *key, BN_CTX *ctx)
{
    int ret = 1;
    BN_CTX_start(ctx);

    BIGNUM *r = BN_CTX_get(ctx);
    BIGNUM *tmp1 = BN_CTX_get(ctx);
    BIGNUM *tmp2 = BN_CTX_get(ctx);

    // Let m be the message to be encrypted where m E Zn,就是m小于n
    if (BN_cmp(m, key->n) >= 0)
    {
        printf("Message not in Zn\n");
        goto end;
    }

    // Select random r where r E Zn,就是r在0到n之间
    do
    {
        if (!BN_rand(r, DEFAULT_KEY_LEN*2, 0, 0))
            goto end;
    }
    while (BN_is_zero(r));

    if (!BN_mod(r, r, key->n, ctx))
        goto end;

    // Compute ciperthext as c = g^m*r^n mod n^2
    if (!BN_mod_exp(tmp1, key->g, m, key->n2, ctx))
        goto end;
    if (!BN_mod_exp(tmp2, r, key->n, key->n2, ctx))
        goto end;

    if (!BN_mod_mul(c, tmp1, tmp2, key->n2, ctx))
        goto end;

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);

    return ret;
}

int decrypt(BIGNUM *plain, const BIGNUM *c, const privKey *key, BN_CTX *ctx)
{
    int ret = 1;
    BN_CTX_start(ctx);

    BIGNUM *tmp = BN_CTX_get(ctx);

    // Let c be the ciphertext to decrypt, where c E Zn2
    if (!BN_cmp(c, key->n2) == 1)
    {
        printf("Message provided not in Zn2");
        goto end;
    }

    // Compute the plaintext message as: m = L(c^lamda mod n2)*mu mod n
    if (!BN_mod_exp(tmp, c, key->lamda, key->n2, ctx))
        goto end;
    if (L(tmp, tmp, key->n, ctx) != 0)
        goto end;
    if (!BN_mod_mul(plain, tmp, key->mu, key->n, ctx))
        goto end;

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);
    return ret;
}

//E(m1)*E(m2)
int addTest(BIGNUM *result, const BIGNUM *enc, const BIGNUM *plain, const pubKey *key, BN_CTX *ctx)
{
    int ret = 1;
    BN_CTX_start(ctx);

    BIGNUM *plain_enc = BN_CTX_get(ctx);

    if (encrypt(plain_enc, plain, key, ctx) != 0)
        goto end;

    if (!BN_mod_mul(result, enc, plain_enc, key->n2, ctx))
        goto end;

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);
    return ret;
}

// E(m1)^n
int mulTest(BIGNUM *result, const BIGNUM *a, const BIGNUM *mul_factor, const pubKey *key, BN_CTX *ctx)
{
    int ret = 1;

    if (!BN_mod_exp(result, a, mul_factor, key->n2, ctx))
        goto end;

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    return ret;
}

//For generate random keys
int generateRandomKeys_test()
{
    // BN_GENCB cb;
    int ret = 1;
    BIGNUM *p, *q, *tmp, *n, *n2, *g, *lamda, *mu;

    int key_len = DEFAULT_KEY_LEN;

    BN_CTX * ctx = BN_CTX_new();
    BN_CTX_start(ctx);

    // Temp BIGNUMs,会被是放掉
    p = BN_CTX_get(ctx);
    q = BN_CTX_get(ctx);
    tmp = BN_CTX_get(ctx);

    // Part of the keys BIGNUMs
    n = BN_new();
    n2 = BN_new();
    g = BN_new();
    lamda = BN_new();
    mu = BN_new();

    // Choose two large prime numbers p,q
    // This numbers have to hold gcd(pq, (p-1)(q-1)) = 1
    do
    {
        // BN_GENCB_set(&cb, genprime_cb, NULL);
        if (!BN_generate_prime_ex(p, key_len, 0, NULL, NULL, NULL))
            goto end;
        if (!BN_generate_prime_ex(q, key_len, 0, NULL, NULL, NULL))
            goto end;

        // Compute n = pq
        if (!BN_mul(n, p, q, ctx))
            goto end;

        // Test if primes are ok
        if (!BN_sub_word(p, 1))
            goto end;
        if (!BN_sub_word(q, 1))
            goto end;
        if (!BN_mul(tmp, p, q, ctx))
            goto end;
    }
    while (BN_cmp(p, q) == 0 || BN_gcd(tmp, tmp, n, ctx) != 1);

    // lamda = lcm(p-1,q-1)
    if (!BN_lcm(lamda, p, q, ctx))
        goto end;

    // calculate n的平方
    if (!BN_mul(n2, n, n, ctx))
        goto end;
    do
    {
        // Select a random integer g mod n2
        do
        {
            if (!BN_rand_range(g, n2))
                goto end;
        }
        while (BN_is_zero(g));

        // Calculate mu
        if (!BN_mod_exp(tmp, g, lamda, n2, ctx))
            goto end;
        if (L(tmp, tmp, n, ctx) != 0)
            goto end;
        BN_mod_inverse(mu, tmp, n, ctx);
    }
    while (mu == NULL);

    pb.n = n;
    pb.n2 = n2;
    pb.g = g;

    pv.n = BN_dup(n);
    pv.n2 = BN_dup(n2);
    pv.lamda = lamda;
    pv.mu = mu;

    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);
    return ret;
}

int encrypt_test(char *c_char, char *m_char)
{
    int ret = 1;

    BN_CTX *ctx = BN_CTX_new();
    BN_CTX_start(ctx);

    BIGNUM *r = BN_CTX_get(ctx);
    BIGNUM *tmp1 = BN_CTX_get(ctx);
    BIGNUM *tmp2 = BN_CTX_get(ctx);
    BIGNUM *c = BN_CTX_get(ctx);
    BIGNUM *m = BN_CTX_get(ctx);

    // BN_hex2bn(&c,c_char);
    BN_hex2bn(&m,m_char);

    // Let m be the message to be encrypted where m E Zn,就是m小于n
    if (BN_cmp(m, pb.n) >= 0)
    {
        printf("Message not in Zn\n");
        goto end;
    }

    // Select random r where r E Zn,就是r在0到n之间
    do
    {
        if (!BN_rand(r, DEFAULT_KEY_LEN*2, 0, 0))
            goto end;
    }
    while (BN_is_zero(r));

    if (!BN_mod(r, r, pb.n, ctx))
        goto end;

    // Compute ciperthext as c = g^m*r^n mod n^2
    if (!BN_mod_exp(tmp1, pb.g, m, pb.n2, ctx))
        goto end;
    if (!BN_mod_exp(tmp2, r, pb.n, pb.n2, ctx))
        goto end;

    if (!BN_mod_mul(c, tmp1, tmp2, pb.n2, ctx))
        goto end;

    char *tmp = BN_bn2hex(c);
    memcpy(c_char, tmp, strlen(tmp) + 1);
    OPENSSL_free(tmp);
    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);
    BN_CTX_free(ctx);

    return ret;
}

int decrypt_test(char *plain_char, char *c_char)
{
    int ret = 1;
    BN_CTX* ctx = BN_CTX_new();
    BN_CTX_start(ctx);
    BIGNUM *tmp = BN_CTX_get(ctx);
    BIGNUM *plain = BN_CTX_get(ctx);
    BIGNUM *c = BN_CTX_get(ctx);

    BN_hex2bn(&c,c_char);

    // Let c be the ciphertext to decrypt, where c E Zn2
    if (!BN_cmp(c, pv.n2) == 1)
    {
        printf("Message provided not in Zn2");
        goto end;
    }

    // Compute the plaintext message as: m = L(c^lamda mod n2)*mu mod n
    if (!BN_mod_exp(tmp, c, pv.lamda, pv.n2, ctx))
        goto end;
    if (L(tmp, tmp, pv.n, ctx) != 0)
        goto end;
    if (!BN_mod_mul(plain, tmp, pv.mu, pv.n, ctx))
        goto end;

    char *tmpp = BN_bn2hex(plain);
    memcpy(plain_char, tmpp, strlen(tmpp) + 1);
    OPENSSL_free(tmpp);
    ret = 0;
end:
    if (ret)
    {
        printf("error\n");
    }

    BN_CTX_end(ctx);
    BN_CTX_free(ctx);
    return ret;
}
