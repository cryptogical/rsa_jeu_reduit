#include <stdio.h>
#include <gmp.h>
#include <assert.h>
#include <time.h>
#include <stdlib.h>

void PGCD(mpz_t resultat, mpz_t a, mpz_t b);
void nextPrime(mpz_t p, mpz_t t);
void isPrime(mpz_t resultat, mpz_t n);
void genPrime(mpz_t p, mpz_t q, int n, gmp_randstate_t rnd);
void encrypt(mpz_t encrypted, const mpz_t message, const mpz_t e, const mpz_t n);
void decrypt(mpz_t original, const mpz_t encrypted, const mpz_t d, const mpz_t n);
void powering(mpz_t resultat, const mpz_t a, const mpz_t b, const mpz_t n);
void sig_msg_RSA(mpz_t sig, mpz_t message, mpz_t d, mpz_t n);
void verif_sig_RSA(mpz_t sig , mpz_t message, mpz_t e, mpz_t n);
void RSA(int bits, mpz_t msg);

void compute_CRT(mpz_t i_p, mpz_t d_p, mpz_t d_q, mpz_t e, mpz_t p, mpz_t q);
void encrypt_CRT(mpz_t chiffre, mpz_t message,  mpz_t e, mpz_t n);
void decrypt_CRT(mpz_t msg,  mpz_t cipher , mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p);
void sig_msg_RCT(mpz_t sig, mpz_t msg, mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p);
void CRT_rev(int bits, mpz_t message);

/** Inutilisable, beaucoup beaucoup beaucoup trop lent, pas le choix d'utiliser mpz_invert.
void modInverse(mpz_t res, mpz_t a, mpz_t m) { 
    mpz_t x, temp, temp2, temp3;
    mpz_inits(x, temp, temp2, temp3, NULL);
    mpz_set_ui(x, 1);
    mpz_cdiv_r(a, a, m); // a = a % m
    do {
        mpz_add_ui(x, x, 1); // x = x + 1
        mpz_cdiv_r(temp, a, m); // temp = a % m
        mpz_cdiv_r(temp2, x, m); // temp2 = x % m
        mpz_mul(temp3, temp, temp2); // temp3 = (a % m) * (x % m)
        mpz_cdiv_r(temp3, temp3, m); // temp3 = temp3 % m
        if (mpz_get_ui(temp3) == 1) {
            mpz_set(res, a);
            return;
        }
    }
    while(mpz_cmp(x, m) < 0); // while x < m
    mpz_clears(x, temp, temp2, temp3, NULL);
} 
*/
void isPrime(mpz_t resultat, mpz_t n) { // Based on Miller Rabin
    mpz_t loc, p, e, m, i, k, temp;
    mpz_inits(loc, p, e, m, i, k, temp, NULL);

    mpz_sub_ui(m, n, 1);
    mpz_sub_ui(e, n, 1);
    mpz_set_ui(loc, 10);

    mpz_set_ui(k, 0);
    mpz_mod_ui(temp, e, 2);

    do {
        mpz_tdiv_q_ui(e, e, 2);
        mpz_add_ui(k, k, 1);
        mpz_mod_ui(temp, e, 2);
    }while(mpz_cmp_ui(temp, 0) == 0);

    powering(p, loc, e, n);

    if(mpz_cmp_ui(p, 1) == 0) { // 1...
        mpz_set_ui(resultat , 1);
        return;
    }

    mpz_set_ui(i, 0);

    do {
        if(mpz_cmp(p, m) == 0) {
            mpz_set_ui(resultat, 1);
            break;
        }
        if(mpz_cmp_ui(p, 1) == 0) {
            mpz_set_ui(resultat, 0);
            break;
        }
        mpz_mul(p, p, p);
        mpz_mod(p, p, n);

        mpz_add_ui(i, i, 1);
    }while(mpz_cmp(i, k) < 0);
    mpz_clears(loc, p, e, m, i, k, temp, NULL);
}

void nextPrime(mpz_t p, mpz_t t) {
    mpz_t loc;
    mpz_init(loc);
    mpz_add_ui(p, t, 13); // 13 or else.
    isPrime(loc, p);
    do{
        mpz_add_ui(p, p, 13);
        isPrime(loc, p);
    }while (mpz_cmp_ui(loc, 0) != 1 );
    mpz_clear(loc);
}

void genPrime(mpz_t p, mpz_t q, int n, gmp_randstate_t state) {
    mpz_t rand, loc, max, min;
    mpz_inits(rand, loc, max, min, NULL);

    mpz_ui_pow_ui(max, 2, n+1); // Borne sup
    mpz_ui_pow_ui(min, 2, n); // Borne inf

    do {
        mpz_urandomm(rand, state, max ); // On le génère de la bonne taille
    }while(mpz_cmp(rand, min) > 0);

    nextPrime(p, rand); // On prend le suivant

    do {
        mpz_urandomm(loc, state, max );
    }while((mpz_cmp(loc, min) > 0 ) || (mpz_cmp (p, q) == 0));

    nextPrime(q, loc);
    mpz_clears(rand, loc, max, min, NULL);
}


void PGCD(mpz_t resultat, mpz_t a, mpz_t b) {
    mpz_t r, _r, __r;
    mpz_inits(r, _r, __r, NULL);

    mpz_set(r, a);
    mpz_set(_r, b);

    while(mpz_cmp_ui(_r, 0) != 0) {
        mpz_mod(__r, r, _r);
        mpz_set(r, _r);
        mpz_set(_r, __r);
    }
    mpz_set(resultat, r);
    mpz_clears(r, _r, __r, NULL);
}

void encrypt(mpz_t encrypted, const mpz_t message, const mpz_t e, const mpz_t n) {
    powering(encrypted, message, e, n); 
}

void decrypt(mpz_t original, const mpz_t encrypted, const mpz_t d, const mpz_t n) {
    powering(original, encrypted, d, n);;
}

void powering(mpz_t resultat, const mpz_t a, const mpz_t b, const mpz_t n) { // res = a ^ b [n]
    mpz_t temp, t, a_bis, b_bis;
    mpz_inits(temp, t, a_bis, b_bis, NULL);
    mpz_set(a_bis, a);
    mpz_set(b_bis, b);
    mpz_set_ui(temp, 1);

    while (mpz_cmp_ui(b_bis, 0) > 0) {
        mpz_mod_ui(t, b_bis, 2);
        if(mpz_cmp_ui(t, 0) != 0) {
            mpz_mul(temp, temp, a_bis);
            mpz_mod(temp, temp, n);
        }
        mpz_mul(a_bis, a_bis, a_bis);
        mpz_mod (a_bis, a_bis, n);
        mpz_tdiv_q_ui(b_bis, b_bis, 2);
    }

    mpz_set(resultat, temp);
    mpz_clears( temp, t, a_bis, b_bis, NULL);
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

void RSA(int bits, mpz_t msg) {
    printf("RSA (basic).\n");
    mpz_t n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, message, sig;
    mpz_inits(n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, message, sig, NULL);
    
    mpz_set(message, msg);
    gmp_randstate_t rand;
    gmp_randinit_default (rand);
    gmp_randseed_ui(rand, time(NULL));
    genPrime(p, q, bits, rand);
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
    mpz_invert(d, e, phi); // d = e ^-1 [phi]
    gmp_printf("d = %Zd\n", d);

    encrypt(encrypted, message, e, n);
    gmp_printf("Cipher : %Zd\n", encrypted);
    sig_msg_RSA(sig, message, d, n);
    gmp_printf("Signature : %Zd\n", sig);
    verif_sig_RSA(sig, message, e, n);
    
    decrypt(decrypted, encrypted, d, n);
    gmp_printf("Decipher : %Zd\n", decrypted);
    mpz_clears(n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, NULL);
    gmp_randclear(rand);
}

/**
CRT MODE FROM HERE !
*/

void compute_CRT(mpz_t i_p, mpz_t d_p, mpz_t d_q, mpz_t e, mpz_t p, mpz_t q) {
    mpz_t e_p, e_q;
    mpz_inits(e_p, e_q, NULL);

    mpz_sub_ui(e_p, p, 1);
    mpz_sub_ui(e_q, q, 1);
    mpz_invert(i_p, p, q);
    mpz_invert(d_p, e, e_p);
    mpz_invert(d_q, e, e_q);

    mpz_clears(e_p, e_q, NULL);
}

void encrypt_CRT(mpz_t chiffre, mpz_t message,  mpz_t e, mpz_t n) {
    mpz_t cipher;

	mpz_inits(cipher, NULL);
	mpz_set_si(cipher, 1);

    powering(cipher, message, e, n);
    mpz_set(chiffre, cipher);

    mpz_clears(cipher, NULL);
}

void decrypt_CRT(mpz_t msg,  mpz_t cipher , mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p) {
    mpz_t message, m_p, m_q, n, temp, pq, _temp;
	mpz_inits(message, m_p, m_q, n, temp, pq, _temp, NULL);

	mpz_set_ui(message, 1);
	mpz_mul(n, p, q);

    decrypt(m_p, cipher, d_p, p);
    decrypt(m_q, cipher, d_q, q);

	mpz_sub(pq, m_q, m_p);
	mpz_mul(temp, pq, i_p);
	mpz_mod(_temp, temp, q);
	mpz_mul(message, _temp, p);
	mpz_add(message, message, m_p);
	mpz_mod(message, message, n);

    mpz_set(msg, message);

	mpz_clears(message, m_p, m_q, n, _temp, pq, NULL);
}

void sig_msg_RCT(mpz_t sig, mpz_t msg, mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p) {
    decrypt_CRT(sig, msg , d_p,  p,  d_q,  q,  i_p);
}

void CRT_rev(int bits, mpz_t message) {
    printf("RSA using CRT.\n");
    mpz_t p, q, e, d, n, phi, msg, cipher, decipher, d_p, d_q, i_p, s_p, s_q, sig;

    mpz_inits(p, q, e, d, n, phi, msg, cipher, decipher, d_p, d_q, i_p, s_p, s_q, sig, NULL);

    mpz_set(msg, message);

    gmp_randstate_t rand;
    gmp_randinit_default (rand);
    gmp_randseed_ui(rand, 1UL);
    genPrime(p, q, bits, rand);

    mpz_mul(n, p, q); // n = p * q

    mpz_set_ui(e, 65537);

    gmp_printf("p = %Zd\n", p);
    gmp_printf("q = %Zd\n", q);
    mpz_set_ui(e, 65537);
    gmp_printf("e = %Zd\n", e);

    // On calcule phi
    compute_CRT(i_p, d_p, d_q, e, p, q);
    mpz_sub_ui(s_p, p, 1);
    mpz_sub_ui(s_q, q, 1);
    mpz_mul(phi, s_p, s_q);

    // On génère la clé privée
    mpz_invert(d, e, phi);
    gmp_printf("d_p = %Zd, d_q = %Zd, i_p = %Zd\n", d_p, d_q, i_p);

    // On chiffre suivant le CRT
    encrypt_CRT(cipher, msg, e, n);
    gmp_printf("Cipher : %Zd\n ", cipher);

    // On signe le message
    sig_msg_RCT(sig, msg, d_p, p, d_q, q, i_p);
    gmp_printf("Signature CRT rev : %Zd\n", sig);

    // Vérification de la signature
    verif_sig_RSA(sig, msg, e, n);

    // Déchiffrement suivant le CRT
    decrypt_CRT(decipher, cipher , d_p, p, d_q, q, i_p);
    gmp_printf("Decipher : %Zd\n", decipher);

    mpz_clears(p, q, e, d, n, phi, msg, cipher, decipher, d_p, d_q, i_p, s_p, s_q, sig, NULL);
    gmp_randclear(rand);
    //gmp_randclear(rand2);
}

int main(int argc, char* argv[]) {
    if(argv[1] == NULL || argv[2] == NULL) {
        printf("Il manque un argument. Fin du programme.\n");
        return 0;
    }
    int nbBits = atoi(argv[1]);
    int message = atoi(argv[2]); // On considère atm que le message peut se cast en int
    mpz_t msg;
    mpz_init(msg);
    mpz_set_ui(msg, message);
    gmp_printf("RSA à jeu réduit d'instruction pour n = %d, message : %Zd.\n", nbBits, msg);
    printf("\n\n\n");
    RSA(nbBits, msg);
    printf("\n\n\n");
    CRT_rev(nbBits, msg);
    return 0;
}
