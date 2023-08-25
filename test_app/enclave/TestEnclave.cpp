/*
 * Copyright (C) 2011-2021 Intel Corporation. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in
 *     the documentation and/or other materials provided with the
 *     distribution.
 *   * Neither the name of Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */


#define COM_LENGTH 20
#define PLAIN_SLOT 50
#define EPSILON 100
#define KEY_LENGTH 1024


#include <stdio.h>      /* vsnprintf */
#include <stdarg.h>



#include "pthread.h"


#include "TestEnclave.h"
#include "TestEnclave_t.h"  /* print_string */
#include "tSgxSSL_api.h"

#include <openssl/ec.h>
#include <openssl/bn.h>
#include <openssl/rsa.h>
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/rand.h>
#include <vector>
#include "tests/random.h"
#include "paillier.h"


using namespace std;

void* status;


/* 
 * printf: 
 *   Invokes OCALL to display the enclave buffer to the terminal.
 */
void printf(const char *fmt, ...)
{
    char buf[BUFSIZ] = {'\0'};
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, BUFSIZ, fmt, ap);
    va_end(ap);
    uprint(buf);
}

int convertToComplement(int num, int n) {
    n -= 1;
    if (num >= 0) {
        return num; // 如果是非负数，直接返回原数值
    }
    else {
        
        int complement = -num; // 先取绝对值
        int mask = (1 << n) - 1; // 获取补码的掩码
        complement = ~complement + 1; // 取反加1
        complement = complement & mask; // 保留低N位
        complement += (1 << n); // 符号位

        return complement; // 返回N位补码
    }
}

int round(float num)
{
    double frac_part = num - static_cast<int>(num);
    if(frac_part > 0.5)
        return static_cast<int>(num);
    return static_cast<int>(num)+1;
}


vector<int> expand_data_vector(vector<double> data) 
{

    int N = data.size();
    vector<int> expanded_data;


    for(int i=0;i<N;i++)
    {
        expanded_data.push_back(round(data[i]*EPSILON));
    }

    return expanded_data;

}

vector<BIGNUM*> complement_data_vector(vector<int> data) 
{

    int N = data.size();

    vector<BIGNUM*> complement_data;
    for(int i=0;i<N;i++)
    {
        int c_value = convertToComplement(data[i], COM_LENGTH);
        BIGNUM* bn = BN_new();
        BN_set_word(bn, static_cast<unsigned long>(c_value));
        complement_data.push_back(bn);
    }
    

    return complement_data;

}






vector<double> parameters = {-5.49041649, 1.47357761 , 4.34477227 ,-0.52787233 , 0.06100615 , 0.13143248 , 3.36249505, 1.55706012 , 0.74380218};
   



void enclave_ecall(void* ep_r1,  void* mpcen_data,  char* ep_r_innerproduct, char** me_d_innerproduct,  void* priv,  void* pub, void* pub2){

    vector<int> e_parameters = expand_data_vector(parameters);
    e_parameters[0] *= EPSILON;

    vector<BIGNUM*> ce_parameters = complement_data_vector(e_parameters);

    pubKey* Upk = (pubKey*) pub;
    pubKey* CSPpk = (pubKey*) pub2;
    privKey* MOsk = (privKey*) priv;


    vector<BIGNUM*>* in_ep_r1 = reinterpret_cast<vector<BIGNUM*>*>(ep_r1);
    vector<BIGNUM*>* in_mpcen_data = reinterpret_cast<vector<BIGNUM*>*>(mpcen_data);
    BIGNUM* in_ep_r_innerproduct = BN_new();
    vector<BIGNUM*> in_me_d_innerproduct;

    BN_CTX *ctx = BN_CTX_new();
    BN_CTX_start(ctx);
    int D = (*in_ep_r1).size();

    // Generate big random number r2


    BIGNUM* top = BN_new();
    BN_one(top);
    BN_lshift(top, top, 1000);

    BIGNUM* r2 = BN_new();
    BN_zero(r2);
    // BN_rand_range(r2, top);

    // Calculate random inner product
    
    BIGNUM* tmp = BN_new();
    BN_one(in_ep_r_innerproduct);

    for (int i = 0; i < D; i++)
    {
        BN_mod_exp(tmp, (*in_ep_r1)[i], ce_parameters[i+1], CSPpk->n2, ctx);
        BN_mod_mul(in_ep_r_innerproduct, in_ep_r_innerproduct, tmp, CSPpk->n2, ctx);
        BN_mod_sub(in_ep_r_innerproduct, in_ep_r_innerproduct, r2, CSPpk->n2, ctx);
    }

    char* ret = BN_bn2hex(in_ep_r_innerproduct);
    memcpy(ep_r_innerproduct,ret,strlen(ret)+1);

    // Calculate masked inner product

    // decrypt masked data and calculate masked inner product
    vector<BIGNUM*> in_mpcn_data(D);
    BIGNUM* in_pm_d_innerproduct = BN_new();
    BN_zero(in_pm_d_innerproduct);
    for (int i = 0; i < D; i++)
    {   
        in_mpcn_data[i] = BN_new();
        decrypt(in_mpcn_data[i], (*in_mpcen_data)[i], MOsk, ctx);
        BN_mul(tmp, in_mpcn_data[i], ce_parameters[i+1], ctx);
        BN_add(in_pm_d_innerproduct, in_pm_d_innerproduct, tmp);
    }
    BN_add(in_pm_d_innerproduct, in_pm_d_innerproduct, r2);


    // Unpack inner product
    vector<BIGNUM*> in_m_d_innerproduct;
    BIGNUM* BNzero = BN_new();
    BN_zero(BNzero);

    BIGNUM* BNmod = BN_new();
    BN_one(BNmod);
    BN_lshift(BNmod,BNmod,PLAIN_SLOT);

    int N = 0;


    while(BN_cmp(in_pm_d_innerproduct, BNzero) != 0)
    {
        BIGNUM* element = BN_new();
        BN_mod(element, in_pm_d_innerproduct, BNmod, ctx);
        BN_rshift(in_pm_d_innerproduct,in_pm_d_innerproduct,PLAIN_SLOT);
        N+=1;
        in_m_d_innerproduct.push_back(element);
        // printf("%s\n", BN_bn2hex(element));
    } 

    for (int i = 0; i < N; i++)
    {
        encrypt(tmp, in_m_d_innerproduct[i], Upk, ctx);
        char* ret2 = BN_bn2hex(tmp);
        memcpy(me_d_innerproduct[N-i-1], ret2, strlen(ret2)+1);
    }



   











    
}