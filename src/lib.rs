use rand::Rng;

trait PowMod 
    where Self: Clone + Copy
{
    fn powmod(&self, exponent: Self, modulo: Self) -> Self;
}

impl PowMod for u128 {
    fn powmod(&self, exponent: u128, modulo: u128) -> u128 {
        match exponent {
            0 => 1,
            1 => self % modulo,
            _ => {
                let div_2_result = self.powmod(exponent / 2, modulo);
                let rest_result = self.powmod(exponent % 2,modulo);
               (div_2_result * div_2_result * &rest_result) % modulo
            }
        }
    }
}

pub struct RSAPublicKey {
    e: u128,
    n: u128,
}

impl RSAPublicKey {
    pub fn encript(&self, m: u128) -> u128 {
        m.powmod(self.e,self.n)
    }
}

pub struct RSAPrivateKey {
    d: u128,
    n: u128,
}

impl RSAPrivateKey {
    pub fn decrypt(&self, m: u128) -> u128 {
        m.powmod(self.d,self.n)
    }
}

fn is_divisible_small_prime(x: u128) -> bool { 
    static SMALL_PRIMES: [u128; 100] = [
        2,
        3,
        5,
        7,
        11,
        13,
        17,
        19,
        23,
        29,
        31,
        37,
        41,
        43,
        47,
        53,
        59,
        61,
        67,
        71,
        73,
        79,
        83,
        89,
        97,
        101,
        103,
        107,
        109,
        113,
        127,
        131,
        137,
        139,
        149,
        151,
        157,
        163,
        167,
        173,
        179,
        181,
        191,
        193,
        197,
        199,
        211,
        223,
        227,
        229,
        233,
        239,
        241,
        251,
        257,
        263,
        269,
        271,
        277,
        281,
        283,
        293,
        307,
        311,
        313,
        317,
        331,
        337,
        347,
        349,
        353,
        359,
        367,
        373,
        379,
        383,
        389,
        397,
        401,
        409,
        419,
        421,
        431,
        433,
        439,
        443,
        449,
        457,
        461,
        463,
        467,
        479,
        487,
        491,
        499,
        503,
        509,
        521,
        523,
        541,
    ];
    for p in SMALL_PRIMES {
        if x % p == 0 {
            return false;
        }
    }
    true
}

pub fn ggt(a : u128, b: u128) -> u128 {
    let mut m = if a > b {[a,b]} else {[b,a]};
    loop {
        let remainder = m[0] % m[1];
        if remainder == 0 { break; }
        m[0] = m[1];
        m[1] = remainder;
    }
    return m[1];
}

// miller rabin probabilistic prime number test 
// after 16 iterations there is a 1 in 2^64 chance the test is wrong of he says the number is prime.
// the test is allways right when it says the number is not prime.
pub fn miller_rabin(n: u128) -> bool {
    let mut k = 0;
    let mut m = n-1;
    while m % 2 == 0 {
        m /= 2;
        k += 1;
    }

    let mut rng = rand::thread_rng();

    let a:u128 = rng.gen_range(2..n-2);

    if ggt(n,a) != 1 { return false; }

    let mut b: Vec<u128> = vec![a.powmod(m, n)];

    if b[0] == 1 { 
        return true;
    }

    let mut j = 0;
    for i in 1..k+1 {
        b.push(0);
        b[i] = b[i-1].powmod(2, n);

        if b[i] == 1 {
            j = i-1;
        }
    }

    if b[k] != 1 {
        return false;
    }

    let ggt_j = ggt(n, b[j] + 1);
    if ggt_j == 1 || ggt_j == n {
        return true;
    }

    false
}

// prime number test
// uses is_divisible_small_prime for early out for most numbers and
// miller rabin(16 iterations) to make sure its really a prime
pub fn is_prime(n: u128) -> bool {
    match n {
        0..=1 => false,
        2 => true,
        _ => {
            if is_divisible_small_prime(n) { 
                return false
            };

            for _ in 0..16 {
                if !miller_rabin(n) {
                    return false;
                }
            }

            true
        }
    }
}

// generates a prime number between 2^10 and 2^20
pub fn gen_prime() -> u128 {
    let mut rng = rand::thread_rng();

    loop {
        let a: u128 = rng.gen_range(u128::pow(2,10)..u128::pow(2,20));

        if is_prime(a) { break a; }
    }
}

pub struct EEAResult {
    pub k: u128,
    pub c: u128,
    pub d: u128,
}

// expanded euclidian algorithm in Zn
pub fn eea_mod(a : u128, b: u128, n: u128) -> EEAResult {
    let mut m = if a > b {[a,b]} else {[b,a]};
    let mut c = [1,0];
    let mut d = [0,1];
    loop {
        let remainder = m[0] % m[1];
        if remainder == 0 { break; }
        let quotient = m[0] / m[1];
        let new_c = (c[0] + n - (c[1] * quotient)% n) % n;
        let new_d = (d[0] + n - (d[1] * quotient)% n) % n;

        m[0] = m[1];
        m[1] = remainder;
        c[0] = c[1];
        c[1] = new_c;       
        m[1] = remainder;
        d[0] = d[1];
        d[1] = new_d;    
    }
    return EEAResult{k:m[1],c:c[1],d:d[1]};
}

pub fn gen_rsa_keypair() -> (RSAPrivateKey, RSAPublicKey) {
    let prim_a = gen_prime();
    let prim_b = gen_prime();

    let n = prim_a * prim_b;

    let phi_n = (prim_a - 1) * (prim_b - 1);

    let mut rng = rand::thread_rng();

    let e = loop {
        let pot_e = rng.gen_range(u128::pow(2,5)..u128::pow(2,10));
        if ggt(phi_n, pot_e) == 1 {
            break pot_e;
        }
    };
    let d = eea_mod(phi_n,e, phi_n).d as u128;

    (RSAPrivateKey{d:d,n:n}, RSAPublicKey{e:e,n:n})
}

#[cfg(test)]
mod tests {

    use crate::*;

    #[test]
    fn it_works() {

        let (private_key, public_key) = gen_rsa_keypair();

        let m = 123u128;

        let c = public_key.encript(m);

        let m_1 = private_key.decrypt(c);

        assert_eq!(m,m_1);
    }
}
