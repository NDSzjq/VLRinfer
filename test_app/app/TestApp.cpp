/*
 * Copyright (C) 2011-2018 Intel Corporation. All rights reserved.
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


#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <bitset>

#include <unistd.h>
#include <pwd.h>
#define MAX_PATH FILENAME_MAX
#define COM_LENGTH 20
#define PLAIN_SLOT 50
#define EPSILON 100
#define KEY_LENGTH 1024


#include "sgx_urts.h"
#include "TestApp.h"
#include "TestEnclave_u.h"
#include "paillier.h"


#include <sys/time.h>
#include <random>
#include <cstdio>
#include <algorithm>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <unistd.h>
#include <thread>
#include <omp.h>
#include <unordered_map>


#include <openssl/ec.h>
#include <openssl/bn.h>
#include <openssl/rsa.h>
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/rand.h>


#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>

using namespace std;

int N;
int D;



/* Global EID shared by multiple threads */
sgx_enclave_id_t global_eid = 0;

typedef struct _sgx_errlist_t {
    sgx_status_t err;
    const char *msg;
    const char *sug; /* Suggestion */
} sgx_errlist_t;

/* Error code returned by sgx_create_enclave */
static sgx_errlist_t sgx_errlist[] = {
    {
        SGX_ERROR_UNEXPECTED,
        "Unexpected error occurred.",
        NULL
    },
    {
        SGX_ERROR_INVALID_PARAMETER,
        "Invalid parameter.",
        NULL
    },
    {
        SGX_ERROR_OUT_OF_MEMORY,
        "Out of memory.",
        NULL
    },
    {
        SGX_ERROR_ENCLAVE_LOST,
        "Power transition occurred.",
        "Please refer to the sample \"PowerTransition\" for details."
    },
    {
        SGX_ERROR_INVALID_ENCLAVE,
        "Invalid enclave image.",
        NULL
    },
    {
        SGX_ERROR_INVALID_ENCLAVE_ID,
        "Invalid enclave identification.",
        NULL
    },
    {
        SGX_ERROR_INVALID_SIGNATURE,
        "Invalid enclave signature.",
        NULL
    },
    {
        SGX_ERROR_OUT_OF_EPC,
        "Out of EPC memory.",
        NULL
    },
    {
        SGX_ERROR_NO_DEVICE,
        "Invalid SGX device.",
        "Please make sure SGX module is enabled in the BIOS, and install SGX driver afterwards."
    },
    {
        SGX_ERROR_MEMORY_MAP_CONFLICT,
        "Memory map conflicted.",
        NULL
    },
    {
        SGX_ERROR_INVALID_METADATA,
        "Invalid enclave metadata.",
        NULL
    },
    {
        SGX_ERROR_DEVICE_BUSY,
        "SGX device was busy.",
        NULL
    },
    {
        SGX_ERROR_INVALID_VERSION,
        "Enclave version was invalid.",
        NULL
    },
    {
        SGX_ERROR_INVALID_ATTRIBUTE,
        "Enclave was not authorized.",
        NULL
    },
    {
        SGX_ERROR_ENCLAVE_FILE_ACCESS,
        "Can't open enclave file.",
        NULL
    },
};

/* Check error conditions for loading enclave */
void print_error_message(sgx_status_t ret)
{
    size_t idx = 0;
    size_t ttl = sizeof sgx_errlist/sizeof sgx_errlist[0];

    for (idx = 0; idx < ttl; idx++) {
        if(ret == sgx_errlist[idx].err) {
            if(NULL != sgx_errlist[idx].sug)
                printf("Info: %s\n", sgx_errlist[idx].sug);
            printf("Error: %s\n", sgx_errlist[idx].msg);
            break;
        }
    }
    
    if (idx == ttl)
        printf("Error code is 0x%X. Please refer to the \"Intel SGX SDK Developer Reference\" for more details.\n", ret);
}

/* Initialize the enclave:
 *   Step 1: try to retrieve the launch token saved by last transaction
 *   Step 2: call sgx_create_enclave to initialize an enclave instance
 *   Step 3: save the launch token if it is updated
 */
int initialize_enclave(void)
{
    char token_path[MAX_PATH] = {'\0'};
    sgx_launch_token_t token = {0};
    sgx_status_t ret = SGX_ERROR_UNEXPECTED;
    int updated = 0;
    
    /* Step 1: try to retrieve the launch token saved by last transaction 
     *         if there is no token, then create a new one.
     */
    /* try to get the token saved in $HOME */
    const char *home_dir = getpwuid(getuid())->pw_dir;
    
    if (home_dir != NULL && 
        (strlen(home_dir)+strlen("/")+sizeof(TOKEN_FILENAME)+1) <= MAX_PATH) {
        /* compose the token path */
        strncpy(token_path, home_dir, strlen(home_dir));
        strncat(token_path, "/", strlen("/"));
        strncat(token_path, TOKEN_FILENAME, sizeof(TOKEN_FILENAME)+1);
    } else {
        /* if token path is too long or $HOME is NULL */
        strncpy(token_path, TOKEN_FILENAME, sizeof(TOKEN_FILENAME));
    }

    FILE *fp = fopen(token_path, "rb");
    if (fp == NULL && (fp = fopen(token_path, "wb")) == NULL) {
        printf("Warning: Failed to create/open the launch token file \"%s\".\n", token_path);
    }

    if (fp != NULL) {
        /* read the token from saved file */
        size_t read_num = fread(token, 1, sizeof(sgx_launch_token_t), fp);
        if (read_num != 0 && read_num != sizeof(sgx_launch_token_t)) {
            /* if token is invalid, clear the buffer */
            memset(&token, 0x0, sizeof(sgx_launch_token_t));
            printf("Warning: Invalid launch token read from \"%s\".\n", token_path);
        }
    }
    /* Step 2: call sgx_create_enclave to initialize an enclave instance */
    /* Debug Support: set 2nd parameter to 1 */
    ret = sgx_create_enclave(TESTENCLAVE_FILENAME, SGX_DEBUG_FLAG, &token, &updated, &global_eid, NULL);
    if (ret != SGX_SUCCESS) {
        print_error_message(ret);
        if (fp != NULL) fclose(fp);
        return -1;
    }

    /* Step 3: save the launch token if it is updated */
    if (updated == FALSE || fp == NULL) {
        /* if the token is not updated, or file handler is invalid, do not perform saving */
        if (fp != NULL) fclose(fp);
        return 0;
    }

    /* reopen the file with write capablity */
    fp = freopen(token_path, "wb", fp);
    if (fp == NULL) return 0;
    size_t write_num = fwrite(token, 1, sizeof(sgx_launch_token_t), fp);
    if (write_num != sizeof(sgx_launch_token_t))
        printf("Warning: Failed to save launch token to \"%s\".\n", token_path);
    fclose(fp);
    return 0;
}



/* OCall functions */
void uprint(const char *str)
{
    /* Proxy/Bridge will check the length and null-terminate 
     * the input string to prevent buffer overflow. 
     */
    printf("%s", str);
    // fflush(stdout);
}




/* Read Test data*/

vector<vector<double>> readCsvFile(string fileName) {
    ifstream file(fileName);
    vector<vector<double>> data;
    string line;

    while (getline(file, line)) {
        vector<double> row;
        stringstream ss(line);
        string cell;

        while (getline(ss, cell, ',')) {
            row.push_back(stod(cell));
        }

        data.push_back(row);
    }

    return data;
}



void printBinary(int num) {
    bitset<sizeof(int) * 8> binary(num);
    cout << binary << endl;
}

/* Encode complement*/




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


vector<vector<double>> transpose(vector<vector<double>> matrix) {
    vector<vector<double>> result(matrix[0].size(), vector<double>(matrix.size()));

    for (int i = 0; i < matrix.size(); i++) {
        for (int j = 0; j < matrix[i].size(); j++) {
            result[j][i] = matrix[i][j];
        }
    }

    return result;
}


vector<vector<double>> normalize(vector<vector<double>> data) {
    vector<vector<double>> normalized_data;
    // int N = data.size();
    int N = 10;
    int D = data[0].size()-1;

    // 对每一列进行归一化处理
    for (int j = 0; j < D; j++) {
        double max_val = data[0][j], min_val = data[0][j];
        for (int i = 0; i < N; i++) {
            if (data[i][j] > max_val) {
                max_val = data[i][j];
            }
            if (data[i][j] < min_val) {
                min_val = data[i][j];
            }
        }

        vector<double> column;
        for (int i = 0; i < N; i++) {
            double val = (data[i][j] - min_val) / (max_val - min_val);
            column.push_back(val);
        }
        normalized_data.push_back(column);
    }

    return transpose(normalized_data);
}


vector<vector<int>> expand_data_matrix(vector<vector<double>> data) 
{
    vector<vector<int>> expanded_data;

    int N = data.size();
    int D = data[0].size();


    for(int i=0;i<N;i++)
    {
        vector<int> row;
        for(int j=0;j<D;j++)
        {
            row.push_back(round(data[i][j]*EPSILON));
        }
        expanded_data.push_back(row);
    }

    return expanded_data;

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

vector<vector<int>> complement_data_matrix(vector<vector<int>> data) 
{
    vector<vector<int>> complement_data;

    int N = data.size();
    int D = data[0].size();


    for(int i=0;i<N;i++)
    {
        vector<int> row;
        for(int j=0;j<D;j++)
        {
            row.push_back(convertToComplement(data[i][j], COM_LENGTH));
        }
        complement_data.push_back(row);
    }

    return complement_data;

}


vector<int> complement_data_vector(vector<int> data) 
{

    int N = data.size();

    vector<int> complement_data;
    for(int i=0;i<N;i++)
    {
        complement_data.push_back(convertToComplement(data[i], COM_LENGTH));
    }
    

    return complement_data;

}



int pack_num = 10;

vector<BIGNUM*> pack_data_matrix(vector<vector<int>> data) 
{
    vector<BIGNUM*> packed_data;

    int N = data.size();
    int D = data[0].size();


    for(int i=0;i<D;i++)
    {
        BIGNUM* packed_value = BN_new();
        BN_zero(packed_value);
        for(int j=0;j<N;j++)
        {
            BIGNUM* tmp = BN_new();
            BN_set_word(tmp, static_cast<unsigned long>(data[j][i]));

            BN_add(packed_value, packed_value, tmp);
            BN_lshift(packed_value, packed_value, PLAIN_SLOT);
        }
        BN_rshift(packed_value, packed_value, PLAIN_SLOT);
        packed_data.push_back(packed_value);
    }

    return packed_data;

}


vector<BIGNUM*> pack_r_matrix(vector<vector<BIGNUM*>> r1) 
{
    vector<BIGNUM*> packed_r;

    int N = r1.size();
    int D = r1[0].size();


    for(int i=0;i<D;i++)
    {
        BIGNUM* packed_value = BN_new();
        BN_zero(packed_value);
        for(int j=0;j<N-1;j++)
        {
            BN_add(packed_value, packed_value, r1[j][i]);
            BN_lshift(packed_value, packed_value, PLAIN_SLOT);
        }
        BN_rshift(packed_value, packed_value, PLAIN_SLOT);
        packed_r.push_back(packed_value);
    }

    return packed_r;

}


vector<BIGNUM*> encrypt_data_vector(vector<BIGNUM*> data, pubKey *key, BN_CTX *ctx)
{
    vector<BIGNUM*> enc_data;
    int N = data.size();
    for(int j=0;j<N;j++)
    {
        BIGNUM* enc_value = BN_new();
        encrypt(enc_value, data[j], key, ctx);
        enc_data.push_back(enc_value);
    }
    return enc_data;

}


vector<vector<BIGNUM*>> random_matrix(int X, int Y) {
    BIGNUM* top = BN_new();
    BN_one(top);
    BN_lshift(top, top, COM_LENGTH);
    // 生成随机矩阵
    vector<vector<BIGNUM*>> matrix(X, vector<BIGNUM*>(Y));
    for (int i = 0; i < X; i++) {
        for (int j = 0; j < Y; j++) {
            matrix[i][j] = BN_new();
            BN_zero(matrix[i][j]);
            // BN_rand_range(matrix[i][j], top);
        }
    }

    return matrix;
}

vector<BIGNUM*>  mask_data_vector(vector<BIGNUM*> data, vector<vector<BIGNUM*>> r1){
    int N = r1.size();
    int D = data.size();
    vector<BIGNUM*> masked_data(D);
    for(int j=0;j<D;j++)
    {
        masked_data[j] = BN_new();
        BN_copy(masked_data[j],data[j]);
        for(int i=0;i<N;i++)
        {
            BIGNUM* tmp = BN_new();
            BN_lshift(tmp, r1[i][j], i*PLAIN_SLOT);
            BN_add(masked_data[j], masked_data[j], tmp);
        }
    }
    return masked_data;

}

string hex_to_binary(const string& hex_str) {
    string binary_str;
    // 定义十六进制字符和对应的二进制数之间的映射
    unordered_map<char, string> hex_to_bin_map = {
        {'0', "0000"}, {'1', "0001"}, {'2', "0010"}, {'3', "0011"},
        {'4', "0100"}, {'5', "0101"}, {'6', "0110"}, {'7', "0111"},
        {'8', "1000"}, {'9', "1001"}, {'A', "1010"}, {'B', "1011"},
        {'C', "1100"}, {'D', "1101"}, {'E', "1110"}, {'F', "1111"}
    };
    // 逐个转换十六进制字符为二进制数，并将它们组合起来
    for (char c : hex_str) {
        binary_str += hex_to_bin_map[toupper(c)];
    }
    return binary_str;
}

vector<BIGNUM*> unpack_value(BIGNUM* p_r_innerproduct, BN_CTX *ctx)
{
    vector<BIGNUM*> r_innerproduct(N);
    BIGNUM* BNzero = BN_new();
    BN_zero(BNzero);

    BIGNUM* BNmod = BN_new();
    BN_one(BNmod);
    BN_lshift(BNmod,BNmod,PLAIN_SLOT);

    for (int i = 0; i < N; i++)
    {
        r_innerproduct[N-i-1] = BN_new();
        BN_mod(r_innerproduct[N-i-1], p_r_innerproduct, BNmod, ctx);
        BN_rshift(p_r_innerproduct,p_r_innerproduct,PLAIN_SLOT);
    }
    return r_innerproduct;

}




/* Application entry */
int main(int argc, char *argv[])
{
    (void)(argc);
    (void)(argv);



    // read data
    vector<vector<double>> data = readCsvFile("diabetes_test.csv");
    // Min-Max normalization
    vector<vector<double>> n_data = normalize(data);
    N = n_data.size();
    D = n_data[0].size();
    // Expand data to integers
    vector<vector<int>> en_data = expand_data_matrix(n_data);
    // Encode data to complements
    vector<vector<int>> cen_data = complement_data_matrix(en_data);
    // Pack data
    vector<BIGNUM*> pcen_data = pack_data_matrix(cen_data);
    // Generate key pairs
    BN_CTX *ctx = BN_CTX_new();
    BN_CTX_start(ctx);
    paillierKeys MOKey;
    generateRandomKeys(&MOKey, KEY_LENGTH, ctx);
    paillierKeys UKey;
    generateRandomKeys(&UKey, KEY_LENGTH, ctx);
    paillierKeys CSPKey;
    generateRandomKeys(&CSPKey, KEY_LENGTH, ctx);
    // Encrypt data
    vector<BIGNUM*> epcen_data = encrypt_data_vector(pcen_data, &MOKey.pub, ctx);
    // Generate random matrix
    vector<vector<BIGNUM*>> r1 = random_matrix(N, D);
    // Mask data
    vector<BIGNUM*> mpcen_data = mask_data_vector(epcen_data, r1);
    // Pack R1
    vector<BIGNUM*> p_r1 = pack_r_matrix(r1);
    // Encrypt R1
    vector<BIGNUM*> ep_r1 = encrypt_data_vector(p_r1, &CSPKey.pub, ctx);


    /* Initialize the enclave */
    if (initialize_enclave() < 0){
        return 1; 
    }

    // Random inner product
    char* ep_r_innerproduct_s = (char*)malloc(KEY_LENGTH*2);

    // Mask inner product
    char** me_d_innerproduct_s = (char**)malloc(N*sizeof(char*));
    for (int i = 0; i < N; i++)
    {
        me_d_innerproduct_s[i] = (char*)malloc(KEY_LENGTH*2);
    }


    

    // printf("%s\n",BN_bn2dec(ep_r1[0]));



    // Enter enclave
    enclave_ecall(global_eid, &ep_r1, &mpcen_data, ep_r_innerproduct_s, me_d_innerproduct_s, &MOKey.priv, &UKey.pub, &CSPKey.pub);


    // Decrypt random inner product
    BIGNUM* p_r_innerproduct = BN_new();
    BIGNUM* ep_r_innerproduct = BN_new();
    BN_hex2bn(&ep_r_innerproduct, ep_r_innerproduct_s);
    decrypt(p_r_innerproduct, ep_r_innerproduct, &CSPKey.priv, ctx);

    // Unpack random inner product

    vector<BIGNUM*> r_innerproduct = unpack_value(p_r_innerproduct, ctx);



    // Calculate prediction output


    vector<BIGNUM*> e_innerproduct(N);
    vector<BIGNUM*> me_d_innerproduct(N);
    for (int i = 0; i < N; i++)
    {
        e_innerproduct[i] = BN_new();
        me_d_innerproduct[i] = BN_new();
        BN_hex2bn(&me_d_innerproduct[i], me_d_innerproduct_s[i]);
        BN_mod_exp(e_innerproduct[i], UKey.pub.g, r_innerproduct[i], UKey.pub.n2, ctx);

        BN_mod_mul(e_innerproduct[i], e_innerproduct[i], me_d_innerproduct[i],  UKey.pub.n2, ctx);
    }




    // Decrypt prediction output
    vector<int> prediction_result(N);
    BIGNUM* tmp = BN_new();

    for (int i = 0; i < N; i++)
    {

        decrypt(tmp, e_innerproduct[i], &UKey.priv, ctx);
        char* s = BN_bn2dec(tmp);
        int mask = 1 << (COM_LENGTH);
        prediction_result[i] = 1;
        if (atoi(s) & mask)
            prediction_result[i] = -1;

        cout << prediction_result[i] << endl;
    }




    
    


    // printf("%s\n", BN_bn2hex(p_r_innerproduct));


    // while(BN_cmp(p_r_innerproduct, BNzero) != 0)
    // {
    
    // } 

    


    // vector<char*> me_d_innerproduct(N);
    // BIGNUM* bn = BN_new();
    // BIGNUM* ep_r_innerproduct = BN_new();
    // BN_hex2bn(&ep_r_innerproduct, ep_r_innerproduct_s);
    // decrypt(bn, ep_r_innerproduct, &CSPKey.priv, ctx);
    // printf("%s\n", BN_bn2dec(bn));

    // for (int i = 0; i < D; i++)
    // {
    //     printf("%s\n", BN_bn2dec((ep_r1)[i]));
    // }


    // // for (const auto& row : r1) {
    //     for (const auto& cell :  p_r1) {
    //         cout << hex_to_binary(BN_bn2hex(cell)) << endl;
    //     }
    // //     cout << endl;
    // // }




    // struct timeval timeStart, timeEnd; 
    // double runTime=0; 
    // gettimeofday(&timeStart, NULL );




    // // read buckets from file
    // read_bucket();

    // // init model
    // model_init();
    // init_model_splits();

    // /*Initialize SHE keys*/
    // BN_CTX* ctx = BN_CTX_new();
    // BN_CTX_start(ctx);
    // SHE_key key;
    // generateRandomKeys_she(&key, ctx);


    // /* Initialize the enclave */
    // if (initialize_enclave() < 0){
    //     return 1; 
    // }


    // // training
    // for (int r=0; r<tree_num;++r)
    // {
    //     // calculate gradients
    //     float* gradients1 = (float*)malloc(train_data_num*sizeof(float));
    //     float* gradients2 = (float*)malloc(train_data_num*sizeof(float));
    //     gradients_calcuation(gradients1, gradients2);


    //     // expand gradients to BIGNUM integers
    //     BIGNUM** bigGradients1 = init_big_gradients();
    //     BIGNUM** bigGradients2 = init_big_gradients();
    //     gradients_expand(gradients1, bigGradients1);
    //     gradients_expand(gradients2, bigGradients2);


    //     char** sampleSpace = train_one_tree(r, bigGradients1, bigGradients2, gradients1, gradients2, key);

    //     // model updating
    //     model_weights_update(r, sampleSpace, weights, gradients1, gradients2);

    // }
    // BN_CTX_end(ctx);
    // gettimeofday(&timeEnd, NULL); 
    // runTime = (timeEnd.tv_sec - timeStart.tv_sec ) + (double)(timeEnd.tv_usec -timeStart.tv_usec)/1000000;  
    // cout << "Total running time:" << endl;
    // printf("%lfs\n", runTime);  


    // predicting
    // test_accuracy();

    
    



    
//     struct timeval timeStart, timeEnd; 
//     double runTime=0; 
     // gettimeofday(&timeStart, NULL );

//     gettimeofday(&timeEnd, NULL); 
//     runTime = (timeEnd.tv_sec - timeStart.tv_sec ) + (double)(timeEnd.tv_usec -timeStart.tv_usec)/1000000;  
//     cout << "Encryption running time:" << endl;
//     printf("%lfs\n", runTime);  

    
    return 0;
}
