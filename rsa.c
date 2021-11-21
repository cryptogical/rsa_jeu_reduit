#include <stdio.h>
#include <gmp.h>
#include <assert.h>
#include <time.h>

#define nbBits 1024
#define MSG 123456

void PGCD(mpz_t resultat, mpz_t a, mpz_t b);
void encrypt(mpz_t encrypted, const mpz_t message, const mpz_t e, const mpz_t n);
void decrypt(mpz_t original, const mpz_t encrypted, const mpz_t d, const mpz_t n);
void rsa_power(mpz_t resultat, const mpz_t a, const mpz_t b, const mpz_t n);
void sig_msg_RSA(mpz_t sig, mpz_t message, mpz_t d, mpz_t n);
void verif_sig_RSA(mpz_t sig , mpz_t message, mpz_t e, mpz_t n);
void RSA();
void Calcul_CRT(mpz_t i_p, mpz_t d_p, mpz_t d_q, mpz_t e, mpz_t p, mpz_t q);
void encrypt_CRT(mpz_t chiffre, mpz_t message,  mpz_t e, mpz_t n);
void decrypt_CRT(mpz_t msg,  mpz_t cipher , mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p);
void sig_msg_RCT(mpz_t sig, mpz_t msg, mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p);
void CRT_rev();

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
    rsa_power(encrypted, message, e, n); 
}

void decrypt(mpz_t original, const mpz_t encrypted, const mpz_t d, const mpz_t n) {
    rsa_power(original, encrypted, d, n);;
}

void rsa_power(mpz_t resultat, const mpz_t a, const mpz_t b, const mpz_t n) { // res = a ^ b [n]
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
        printf("Signaturee Status : NOT OK ! Altered message.");
    }
    mpz_clear(hash);
}

void RSA() {
    mpz_t n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, message, sig;
    mpz_inits(n, d, e, p, q, p_1, q_1, phi, encrypted, decrypted, message, sig, NULL);
    
    mpz_set_ui(message, msg);

    // Génération de p
    gmp_randstate_t rand;
	gmp_randinit_default (rand);
    gmp_randseed_ui(rand, time(NULL));

	mpz_urandomb(p, rand, nbBits - 1);
	mpz_add_ui(p, p, 2);

    mpz_nextprime(p, p);
    gmp_printf("p = %Zd\n", p);

    // Génération de q
    gmp_randstate_t rand2;
	gmp_randinit_default (rand2);
    gmp_randseed_ui(rand2, 0UL); // cast de int vers unsigned long int

	mpz_urandomb(q, rand2, nbBits - 1);
	mpz_add_ui(q, q, 2);

    mpz_nextprime(q, q);
    gmp_printf("q = %Zd\n", q);

    mpz_set_ui(e, 65537);
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
}

/**
CRT MODE FROM HERE !
*/

void Calcul_CRT(mpz_t i_p, mpz_t d_p, mpz_t d_q, mpz_t e, mpz_t p, mpz_t q) {
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

    rsa_power(cipher, message, e, n);
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

	mpz_clears(message, m_p, m_q, n, _temp, p_q, NULL);
}

void sig_msg_RCT(mpz_t sig, mpz_t msg, mpz_t d_p, mpz_t p, mpz_t d_q, mpz_t q, mpz_t i_p) {
    decrypt_CRT(sig, msg , d_p,  p,  d_q,  q,  i_p);
}

void CRT_rev() {
    mpz_t p, q, e, d, n, phi, msg, cipher, decipher, d_p, d_q, i_p, s_p, s_q, sig;

    mpz_inits(p, q, e, d, n, phi, msg, cipher, decipher, d_p, d_q, i_p, s_p, s_q, sig, NULL);

    mpz_set_ui(msg, MSG);

    // Génération de p
    gmp_randstate_t rand;
	gmp_randinit_default (rand);
    gmp_randseed_ui(rand, time(NULL));

	mpz_urandomb(p, rand, nbBits - 1);
	mpz_add_ui(p, p, 2);

    mpz_nextprime(p, p);
    gmp_printf("p = %Zd\n", p);

    // Génération de q
    gmp_randstate_t rand2;
	gmp_randinit_default (rand2);
    gmp_randseed_ui(rand2, 0UL); // cast de int vers unsigned long int

	mpz_urandomb(q, rand2, nbBits - 1);
	mpz_add_ui(q, q, 2);

    mpz_nextprime(q, q);
    gmp_printf("q = %Zd\n", q);

    mpz_mul(n, p, q); // n = p * q

    mpz_set_ui(e, 65537);

    // On calcule phi
    Calcul_CRT(i_p, d_p, d_q, e, p, q);
    mpz_sub_ui(s_p, p, 1);
    mpz_sub_ui(s_q, q, 1);
    mpz_mul(phi, s_p, s_q);

    // On génère la clé privée
    mpz_invert(d, e, phi);
    gmp_printf("d_p = %Zd, d_q = %Zd, i_p = %Zd\n", dp, dq, ip);

    // On chiffre suivant le CRT
    encrypt_CRT(cipher, msg, e, n);
    gmp_printf("Cipher : %Zd\n ", cipher);

    // On signe le message
    sig_msg_RCT(sig, msg, dp, p, d_q, q, i_p);
    gmp_printf("Signature CRT rev : %Zd\n", sig);

    // Déchiffrement suivant le CRT
    mpz_init_set_str(decipher, "1", 0);
    decrypt_CRT(decipher, cipher , d_p, p, d_q, q, i_p);
    gmp_printf("Decipher : %Zd\n", decipher);

    // Vérification de la signature
    verif_sig_RSA(sig, msg, e, n);

    mpz_clears(p, q, e, d, n, phi, msg, cipher, decipher, d_p, d_q, i_p, s_p, s_q, sig, NULL);

}

int main() {
    CRT_rev();
    return 0;
}