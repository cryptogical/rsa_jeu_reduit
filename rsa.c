#include <stdio.h>
#include <gmp.h>
#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <math.h>

void PGCD(mpz_t result, mpz_t a, mpz_t b);
void bePrime(mpz_t p, mpz_t t);
void isPrime(mpz_t result, mpz_t n);
void computeInvert(mpz_t d , mpz_t e , mpz_t n);
void genPrime(mpz_t p, mpz_t q, int n, gmp_randstate_t rnd);
void encrypt(mpz_t encrypted, mpz_t message, mpz_t e, mpz_t n);
void decrypt(mpz_t original, mpz_t encrypted, mpz_t d, mpz_t n);
void powering(mpz_t result, mpz_t a, mpz_t b, mpz_t n);
void sig_msg_RSA(mpz_t sig, mpz_t message, mpz_t d, mpz_t n);
void verif_sig_RSA(mpz_t sig , mpz_t message, mpz_t e, mpz_t n);
void encrypt_CRT(mpz_t chiffre, mpz_t message,  mpz_t e, mpz_t n);
void decrypt_CRT(mpz_t msg,  mpz_t cipher , mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p);
void sig_msg_RCT(mpz_t sig, mpz_t msg, mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p);

void computeInvert(mpz_t d , mpz_t e , mpz_t n) { // it's EEA, nothing more nothing less
   mpz_t e0, t0, t, q, r, n0, _loc0;
   mpz_inits(e0, t0, t, q, r, n0, _loc0, NULL);

   mpz_set_ui(t, 1) ;
   mpz_set(n0, n);
   mpz_set(e0, e);
   mpz_tdiv_q(q, n0, e0);
   mpz_mod(r, n0, e0);

   do {
       mpz_mul(_loc0, q, t);
       mpz_sub(_loc0, t0, _loc0);
       if(mpz_cmp_ui(_loc0, 0) >= 0) {
           mpz_mod(_loc0, _loc0, n);
       }
       else {
           mpz_mod(_loc0, _loc0, n);
       }
       mpz_set(t0, t);
       mpz_set(t, _loc0);
       mpz_set(n0, e0);
       mpz_set(e0, r);
       mpz_tdiv_q(q, n0, e0);
       mpz_mod(r, n0, e0);

   }while(mpz_cmp_ui(r, 0) > 0);
   mpz_set(d, t);

   mpz_clears(e0, t0, t, q, r, n0, _loc0, NULL);
}
/*
void modulus(mpz_t res, mpz_t a, mpz_t b) {
    mpz_t q, t, _loc;
    mpz_inits(q, t, _loc, NULL);
    if(mpz_sgn(b) < 0) {
        mpz_neg(_loc, b); // b = - b 
    }
    else {
        mpz_set(_loc, b);
    }
    if(mpz_cmp(a, _loc) < 0) {
        mpz_set(res, a);
    }
    else {
        mpz_tdiv_q(q, a, _loc);
        mpz_mul(t, q, _loc);
        mpz_sub(res, a, t);
    }
    mpz_clears(q, t, _loc, NULL);
}

void modulus_ui(mpz_t res, mpz_t a, int b) {
    mpz_t q, t, z_b, _loc;
    mpz_inits(q, t, z_b, _loc, NULL);
    mpz_set_ui(z_b, b);
    if(mpz_sgn(z_b) < 0) {
        mpz_neg(_loc, z_b); // b = - b 
    } //Si b est négatif, on le met en positif et on change le signe de a ?
    else {
        mpz_set(_loc, z_b);
    }
    if(mpz_cmp(a, _loc) < 0) {
        mpz_set(res, a);
    }
    else {
        mpz_tdiv_q(q, a, _loc); // Essayer avec mpz_cdiv_q
        mpz_mul(t, q, _loc);
        mpz_sub(res, a, t);
    }
    mpz_clears(q, t, _loc, z_b, NULL);
}
*/
void isPrime(mpz_t result, mpz_t n) { // Based on Miller Rabin
    mpz_t _loc0, p, e, m, i, k, _loc1;
    mpz_inits(_loc0, p, e, m, i, k, _loc1, NULL);

    mpz_sub_ui(m, n, 1);
    mpz_sub_ui(e, n, 1);
    mpz_set_ui(_loc0, 10);

    mpz_set_ui(k, 0);
    mpz_mod_ui(_loc1, e, 2);

    do {
        mpz_tdiv_q_ui(e, e, 2); 
        mpz_add_ui(k, k, 1);
        mpz_mod_ui(_loc1, e, 2);
    }while(mpz_cmp_ui(_loc1, 0) == 0);

    powering(p, _loc0, e, n);

    if(mpz_cmp_ui(p, 1) == 0) { // 1...
        mpz_set_ui(result , 1);
        return;
    }

    mpz_set_ui(i, 0);

    do {
        if(mpz_cmp(p, m) == 0) {
            mpz_set_ui(result, 1);
            break;
        }
        if(mpz_cmp_ui(p, 1) == 0) {
            mpz_set_ui(result, 0);
            break;
        }
        mpz_mul(p, p, p);
        mpz_mod(p, p, n);

        mpz_add_ui(i, i, 1);
    }while(mpz_cmp(i, k) < 0);
    mpz_clears(_loc0, p, e, m, i, k, _loc1, NULL);
}

void bePrime(mpz_t p, mpz_t t) {
    mpz_t _loc0;
    mpz_init(_loc0);
    mpz_add_ui(p, t, 13);
    isPrime(_loc0, p);
    do{
        mpz_add_ui(p, p, 13); // 2 or something else
        isPrime(_loc0, p);
    }while (mpz_cmp_ui(_loc0, 0) != 1 );
    mpz_clear(_loc0);
}

void genPrime(mpz_t p, mpz_t q, int n, gmp_randstate_t state) {
    mpz_t rand, _loc0, max, min;
    mpz_inits(rand, _loc0, max, min, NULL);

    mpz_ui_pow_ui(max, 2, n+1); // Borne sup 2^n+1
    mpz_ui_pow_ui(min, 2, n); // Borne inf

    do {
        mpz_urandomm(rand, state, max); // On le génère de la bonne taille
    }while(mpz_cmp(rand, min) < 0);

    bePrime(p, rand); // On cherche un premier de taille prédefinie

    do {
        mpz_urandomm(_loc0, state, max );
    }while((mpz_cmp(_loc0, min) < 0 ));

    bePrime(q, _loc0);
    // TODO: verif si p != q
    mpz_clears(rand, _loc0, max, min, NULL);
}

void genNumber(mpz_t p, int n, gmp_randstate_t state) {
    mpz_t rand, _loc0, max, min;
    mpz_inits(rand, _loc0, max, min, NULL);

    mpz_ui_pow_ui(max, 2, n+1); // Borne sup
    mpz_ui_pow_ui(min, 2, n); // Borne inf

    do {
        mpz_urandomm(rand, state, max ); // On le génère de la bonne taille
    }while(mpz_cmp(rand, min) > 0);
    mpz_set(p, rand);
    mpz_clears(rand, _loc0, max, min, NULL);
}


void PGCD(mpz_t result, mpz_t a, mpz_t b) {
    mpz_t _loc0, _loc1, _loc2;
    mpz_inits(_loc0, _loc1, _loc2, NULL);

    mpz_set(_loc0, a);
    mpz_set(_loc1, b);

    while(mpz_cmp_ui(_loc1, 0) != 0) {
        mpz_mod(_loc2, _loc0, _loc1);
        mpz_set(_loc0, _loc1);
        mpz_set(_loc1, _loc2);
    }
    mpz_set(result, _loc0);
    mpz_clears(_loc0, _loc1, _loc2, NULL);
}

void encrypt(mpz_t encrypted, mpz_t message, mpz_t e, mpz_t n) {
    powering(encrypted, message, e, n); 
}

void decrypt(mpz_t original, mpz_t encrypted, mpz_t d, mpz_t n) {
    powering(original, encrypted, d, n);;
}

void powering(mpz_t result, mpz_t a, mpz_t b, mpz_t n) { // res = a ^ b [n]
    mpz_t _loc, t, a_bis, b_bis;
    mpz_inits(_loc, t, a_bis, b_bis, NULL);
    mpz_set(a_bis, a);
    mpz_set(b_bis, b);
    mpz_set_ui(_loc, 1);

    while (mpz_cmp_ui(b_bis, 0) > 0) {
        mpz_mod_ui(t, b_bis, 2);
        if(mpz_cmp_ui(t, 0) != 0) {
            mpz_mul(_loc, _loc, a_bis);
            mpz_mod(_loc, _loc, n);
        }
        mpz_mul(a_bis, a_bis, a_bis);
        mpz_mod (a_bis, a_bis, n);
        mpz_tdiv_q_ui(b_bis, b_bis, 2);
    }

    mpz_set(result, _loc);
    mpz_clears( _loc, t, a_bis, b_bis, NULL);
}

void sig_msg_RSA(mpz_t sig, mpz_t message, mpz_t d, mpz_t n) {
    decrypt(sig, message ,d ,n);
}

void verif_sig_RSA(mpz_t sig , mpz_t message, mpz_t e, mpz_t n) {
    mpz_t hash;
	mpz_init(hash);
    encrypt(hash, sig, e, n);
    if(mpz_cmp(message, hash) == 0) {
        printf("Signature Status : OK!\n");
    }
    else {
        printf("Signature Status : NOT OK ! Altered message.\n");
    }
    mpz_clear(hash);
}


void encrypt_CRT(mpz_t chiffre, mpz_t message,  mpz_t e, mpz_t n) {
    mpz_t cipher;

	mpz_init(cipher);
	mpz_set_si(cipher, 1);

    powering(cipher, message, e, n);
    mpz_set(chiffre, cipher);

    mpz_clear(cipher);
}

void decrypt_CRT(mpz_t msg,  mpz_t cipher , mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p) {
    mpz_t message, m_p, m_q, n, _loc0, pq, _loc1;
	mpz_inits(message, m_p, m_q, n, _loc0, pq, _loc1, NULL);

	mpz_set_ui(message, 1);
	mpz_mul(n, p, q);

    decrypt(m_p, cipher, d_p, p);
    decrypt(m_q, cipher, d_q, q);

	mpz_sub(pq, m_q, m_p);
	mpz_mul(_loc0, pq, i_p);
	mpz_mod(_loc1, _loc0, q);
	mpz_mul(message, _loc1, p);
	mpz_add(message, message, m_p);
	mpz_mod(message, message, n);

    mpz_set(msg, message);

	mpz_clears(message, m_p, m_q, n, _loc0, _loc1, pq, NULL);
}

void sig_msg_RCT(mpz_t sig, mpz_t msg, mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p) {
    decrypt_CRT(sig, msg , d_p,  p,  d_q,  q,  i_p);
}

int main(int argc, char* argv[]) {
    
    if(argv[1] == NULL) {
        printf("Il manque le nombre de bits. Fin du programme.\n");
        return 0;
    }
    // COMPUTATION
    clock_t t1, t2, t1_, t2_;
    int nbBits = atoi(argv[1]);
    gmp_randstate_t rand;
    gmp_randinit_default (rand);
    gmp_randseed_ui(rand, time(NULL));
    mpz_t n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, sig, cipher, decipher, d_p, d_q, i_p, s_p, s_q, e_p, e_q, sig_crt, msg;
    mpz_inits(n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, sig, cipher, decipher, d_p, d_q, i_p, s_p, s_q, e_p, e_q, sig_crt, msg, NULL);
    genNumber(msg, round(nbBits / 2), rand);
    gmp_printf("RSA à jeu réduit d'instructions pour n = %d, message : %Zd.\n\n\n", nbBits, msg);
    genPrime(p, q, round(nbBits / 2), rand);
    gmp_printf("p = %Zd\n", p);
    gmp_printf("q = %Zd\n", q);
    mpz_set_ui(e, 65537);
    gmp_printf("e = %Zd\n", e);
    mpz_mul(n, p, q); // n = p * q

    gmp_printf("n = p * q = %Zd\n", n);

    mpz_sub_ui(p_1, p, 1); // p - 1
    mpz_sub_ui(q_1, q, 1); // q - 1

    mpz_mul(phi, p_1, q_1); 

    gmp_printf("phi = %Zd\n", phi);
    computeInvert(d, e, phi); // d = e ^-1 [phi]
    gmp_printf("d = %Zd\n", d);

    printf("\n\n\n");

    // RSA BASIC
    printf("RSA (classic).\n");
    t1 = clock();
    encrypt(encrypted, msg, e, n);
    gmp_printf("Cipher : %Zd\n", encrypted);
    sig_msg_RSA(sig, msg, d, n);
    gmp_printf("Signature : %Zd\n", sig);
    verif_sig_RSA(sig, msg, e, n);
    
    decrypt(decrypted, encrypted, d, n);
    gmp_printf("Decipher : %Zd\n", decrypted);
    t2 = clock();
    double exec = (double) (t2 - t1) * 1000 / (double) CLOCKS_PER_SEC;
    printf("Execution time : %f ms \n", exec);

    printf("\n\n\n");

    printf("RSA using CRT.\n");
    t1_ = clock();
    mpz_sub_ui(e_p, p, 1); //e_p = p - 1
    mpz_sub_ui(e_q, q, 1); //e_q = q - 1

    computeInvert(i_p, p, q); 
    computeInvert(d_p, e, e_p);
    computeInvert(d_q, e, e_q);

    gmp_printf("d_p = %Zd, d_q = %Zd, i_p = %Zd\n", d_p, d_q, i_p);

    // On chiffre suivant le CRT
    encrypt_CRT(cipher, msg, e, n);
    gmp_printf("Cipher : %Zd\n", cipher);

    // On signe le message
    sig_msg_RCT(sig_crt, msg, d_p, p, d_q, q, i_p);
    gmp_printf("Signature CRT rev : %Zd\n", sig_crt);

    // Vérification de la signature
    verif_sig_RSA(sig_crt, msg, e, n);

    // Déchiffrement suivant le CRT
    decrypt_CRT(decipher, cipher , d_p, p, d_q, q, i_p);
    gmp_printf("Decipher : %Zd\n", decipher);
    t2_ = clock();
    mpz_clears(n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, sig, cipher, decipher, d_p, d_q, i_p, s_p, s_q, e_p, e_q, sig_crt, msg, NULL);
    gmp_randclear(rand);
    double exec_ = (double) (t2_ - t1_) * 1000 / (double) CLOCKS_PER_SEC;
    printf("Execution time : %f ms \n", exec_);
    printf("\n\n");
    double average =  (exec / exec_) * 100;
    printf("Conclusion : CRT is %.0f%% faster than classic RSA.\n", average);
    return 0;
}
