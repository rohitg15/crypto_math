import sys
from typing import Optional
from Crypto import Random
import random
import math

class MyError(Exception): 
    
    # Constructor or Initializer 
    def __init__(self, value): 
        self.value = value 
    
    # __str__ is to print() the value 
    def __str__(self): 
        return(repr(self.value)) 

class Point:
    """
        Represents a point on an elliptic curve
    """
    def __init__(self, x, y):
        self.x = x
        self.y = y
    
    def equals(self, other):
        return (self.x == other.x and self.y == other.y)


class CryptoMath:

    @staticmethod
    def get_random_bytes(n :int)    ->  bytes():
        """
            returns :   bytes()  n cryptographically random bytes
        """
        return Random.get_random_bytes(n)

    @staticmethod
    def get_prng_int(x :int, y :int)  ->  int:
        """
            returns :   (int)   a such that
            x <= a <= y
            and a is the output of a non-cryptographic pseudo-random generator
        """
        return random.randint(x, y)

    @staticmethod
    def mod_exp(x :int, y :int, n :int) -> int:
        """
            returns : (int) (x ** y) % n
        """
        res = 1
        while y > 0:
            if (y & 1) == 1:
                res = (res * x) % n
            x = (x * x) % n
            y = y >> 1

        return res % n
    
    @staticmethod
    def mod_inv_p(x, p):
        if x % p == 0:
            raise('x is divisible by p. No modular inverse!')
        return pow(x, p-2, p)
    
    @staticmethod
    def gcd(x :int, y :int) -> int:
        """
            returns :   (int)   gcd(x,y) using euclid's algorithm
        """
        while y > 0:
            x, y = y, x % y

        return x

    @staticmethod
    def egcd(x :int, y :int) -> int:
        """
            returns :   (int, int, int) : (d, a, b) such that
                d   :   gcd(x,y)    =   a*x + b*y
            using extended euclidean algorithm
        """
        a0 = 1
        b0 = 0
        a1 = 0
        b1 = 1
        r0 = x
        r1 = y
        while r1 > 0:
            q = r0 // r1
            r2 = r0 - q * r1
            a2 = a0 - q * a1
            b2 = b0 - q * b1

            r0 = r1
            r1 = r2
            a0 = a1
            a1 = a2
            b0 = b1
            b1 = b2
        
        return (r0, a0, b0)

    @staticmethod
    def mod_inv(x :int, n :int, is_positive: bool = False) -> int:
        """
            returns :   (int)   :   (y) such that
            (x * y) % n = 1
        """
        (d, a, b) = CryptoMath.egcd(x, n)
        if d != 1:
            # modular inverse does not exist
            return None
        # if a < 0:
        #     return n + a

        if is_positive and a < 0:
            return n + a
        return a
    
    @staticmethod
    def mod_mul(a, b, n):
        """ returns (a * b) % n without overflowing """
        x = 0
        y = a
        while b > 0:
            if (b & 1) != 0:
                # odd number
                x = (x + y) % n
            y = (y + y) % n
            b = b >> 1
        return x % n
        
    @staticmethod
    def fermat_is_prime(p :int) ->  bool:
        """
            returns :   (bool)  True if p is a prime
                according to the Fermat's primality test.
                This can be fooled by carmichael numbers eg: 561
        """
        assert(p > 1)
        if p == 2 or p == 3:
            return True
        
        a = CryptoMath.get_prng_int(2, p - 1)
        if CryptoMath.mod_exp(a, p - 1, p) == 1:
            return True
        return False
    
    @staticmethod
    def crt(a :[int], n :[int]) ->  int:
        """
            returns :   x (mod M) such that
            x % n[i] = a[i] for each (a[i], n[i])
            M = n[0] * n[1] .... * n[num - 1]
            where num = len(n) = len(a)
            assumes that n[i] is relatively prime with n[j] for all j != i
            computes 'x' using the chinese remainder theorem
        """
        num = len(n)
        assert(num == len(a))

        M = 1
        for i in range(num):
            M *= n[i]
        
        N = []
        for i in range(num):
            N.append(M // n[i])
        
        # now, gcd(N[i], n[i]) = 1
        z = []
        for i in range(num):
            z.append(CryptoMath.mod_inv(N[i], n[i]))
        
        x = 0
        # (z[i] * N[i]) % n[i] = 1
        # (z[i] * n[i]) % n[j] = 0 when j != i
        for i in range(num):
            x = (x + ( (a[i] * z[i] * N[i]) % M )) % M

        return x

    @staticmethod
    def get_primes(n :int) -> []:
        """
            returns :   [(int)] array of primes <= n
                computed using the sieve method
        """

        primes = [True] * (n + 1)
        count = len(primes)
        res = []
        for p in range(2, count):
            if primes[p] is True:
                res.append(p)
                j = p * 2
                while j < count:
                    primes[j] = False
                    j = j + p

        return res
    
    @staticmethod
    def miller_rabin_is_prime(p :int, num_iterations : int = 5)   ->  bool:
        """
            returns :   (bool) True if p is a prime
                according to the Miller-Rabin primality test
        """
        assert(p > 1)
        if p == 2 or p == 3:
            return True
        
        q = p - 1
        s = 0
        while q > 0 and q % 2 == 0:
            s += 1
            q = q >> 1
        
        for _ in range(num_iterations):
            a = CryptoMath.get_prng_int(2, p  - 1)
            d = CryptoMath.mod_exp(a, q, p)
            if d == 1 or d == p - 1:
                # possibly prime, check next witness
                continue
            
            is_possibly_prime = False
            for i in range(1, s):
                d = pow(d, 2, p)
                if d == p - 1:
                    # possibly prime, check next witness
                    is_possibly_prime = True
                    break
            
            if is_possibly_prime is False:
                # definitely composite - a value y other than 1, p - 1 satisfied
                # pow (x, p - 1, p) = 1 such that y * y = x
                return False
        
        return True

    @staticmethod
    def phi(n : int) -> int:
        """
            returns :   (int)   euler's totient function on input n
        """
        if (n == 1):
            return 1

        i = 2
        result = n
        while i * i <= n:
            if n % i == 0:
                while n % i == 0:
                    n = n // i
                result = (result - (result // i))
            i = i + 1
        
        if n > 1:
            result = (result - (result // n))
        
        return result

    # Factorization Algorithms
    @staticmethod
    def fermat_factorization(n :int) -> int:
        """
            returns :   (int) a factor of n 
                computed using the Fermat's 2 squares method
        """
        a = math.ceil(math.sqrt(n))
        b2 = (a * a) - n
        b = int(math.sqrt(b2))
        while b2 != b * b:
            a = a + 1
            b2 = (a * a) - n
            b = int(math.sqrt(b2))

        return a - b

    @staticmethod
    def pollard_pminus1_factorization(n : int, b_max :int  = 1000000) -> int:
        """
            returns :   (int) a factor of n
                computed using the pollard's p-1 algorithm

                idea:   if n = p * q and p is a prime such that p - 1 is B-powersmooth,
                        then fermat's little theorem can be used to compute ((a ** M) - 1),
                        which has a gcd (>1) with n
        """
        b = 10
        primes = CryptoMath.get_primes(b_max)
        g = 1
        while b <= b_max and g < n:
            a = CryptoMath.get_prng_int(2, n - 1)
            g = CryptoMath.gcd(a, n)
            if (g > 1):
                return g
            
            for p in primes:
                if p >= b:
                    continue

                pe = 1
                while pe * p <= b:
                    pe = pe * p
                
                a = CryptoMath.mod_exp(a, pe, n)
                g = CryptoMath.gcd(a - 1, n)
                if g > 1 and g < n:
                    return g
            
            b = b * 2

        return 1

    @staticmethod
    def pollard_pminus1_factorization2(n :int, B :int = 1000000, iter = 100) -> int:
        """
            returns :   (int) a factor of n computed using pollard's p-1 algorithm
        """
        for _ in range(iter):
            a = CryptoMath.get_prng_int(2, n-1)
            g = CryptoMath.gcd(a, n)
            if g > 1:
                return g
            
            for i in range(2, B):
                a = CryptoMath.mod_exp(a, i, n)
                g = CryptoMath.gcd(a - 1, n)
                if g > 1 and g < n:
                    return g
        
        return 1


    @staticmethod
    def pollards_rho_factorization(n :int, rseed = 2) -> int:
        """
            returns :   (int) a factor of n
                computed using pollard's rho algorithm
        """
        def f(x :int) -> int:
            return (x * x + 1) % n
        
        g = 1
        seed = rseed
        x = seed
        y = seed
        while g == 1:
            x = f(x)
            y = f(y)
            y = f(y)

            # key idea: x = y mod p (but not mod n)
            g = CryptoMath.gcd(x - y, n)
        
        return g

    # Discrete Logarithm Algorithms

    @staticmethod
    def baby_step_giant_step_dlog(a :int, b : int, m :int) -> int:
        """
            returns :   (int)   x such that
                (a ** x) mod m = b using baby-step-giant-step algorithm
                consider x = np + q
        """
        n = int(math.sqrt(m)) + 1
        table = {}
        g = pow(a, n, m)
        for p in range(1, n + 1):
            table[g] = p
            g = (g * a) % m
        
        g = b % m
        for q in range(0, n + 1):
            exp_p  = table.get(g)
            if exp_p is not None:
                res = (n * exp_p - q)
                if res < m:
                    return res
            g = (g * a) % m
        
        return -1

    

    @staticmethod
    def pollards_rho_dlog(g :int, y :int, n: int) -> int:
        """
            returns :   (int)   x such that
                (g ** x) mod n = y using pollard's rho algorithm
                idea: find a collision in the sequence (g ** ai)(y ** bi) = (g ** aj)(y ** bj)
                n   : prime
        """
        m = n - 1
        h = (g * y) % n
        def f(x :int, g :int, y :int, n :int, a :int, b :int) -> (int, int, int):
            res = x % 3
            if res == 0:
                return ( (x * g) % n, a + 1, b )
            elif res == 1:
                return ( (x * x) % n, a + 1, b + 1)
            return ( (x * y) % n, a, b + 1 )
        
        ai = bi = aj = bj = 1
        slow = h
        fast = h
        while True:
            slow, ai, bi = f(slow, g, y, n, ai, bi)
            fast, aj, bj = f(fast, g, y, n, aj, bj)
            fast, aj, bj = f(fast, g, y, n, aj, bj)
            if slow == fast:
                a = (ai - aj) % m
                b = (bj - bi) % m
                b_inv = CryptoMath.mod_inv(b, m)
                if b_inv is None:
                    raise('Error: hit corner case in pollards rho')
                return (a * b_inv) % m
            
        return None

    @staticmethod
    def pollards_kangaroo_dlog(g: int, y: int, p: int, a: int, b: int, num_trials: int = 100) -> int:
        """
            returns :   (int) x such that pollard's kangaroo algorithm to compute discrete logarithm
        """
        
        for i in range(0, num_trials):
            print ("iteration ", i )
            k = int( math.log2( (b + i - a) // 2 ) )
            x0 =  b + i
            x1 = 0
            
            N = int (pow(2, k + 2)) // k

            # let the tame kangaroo jump N steps
            for _ in range(N):
                jump_pw = int(pow(g, x0, k))
                jump = int(pow(2, jump_pw))
                x1 = x0 + jump
                x0 = x1

            xn = x1
            yn = pow(g, xn, p)
            
            # let the wild kangaroo jump
            y0 = y
            dist = 0
            while True:
                jump_pw = int(pow(2, y0 % k))

                # NOTE: dist denotes the distance in the exponent 'x'
                dist += jump_pw

                jump = int(pow(g, jump_pw, p))
                y1 = (y0 * jump) % p

                if y1 == yn:
                    return xn - dist

                if dist > xn - a:
                    # wild kangaroo went past tame kangaroo
                    break
                
                y0 = y1
        
        raise('Could not find discrete logarithm')

    @staticmethod
    def pollards_kangaroo_dlog2(g: int, y: int, p: int, a: int, b: int, num_trials: int = 1000) -> int:
        """

        """
        def f(y: int, k: int) -> int:
            return int(pow(2, y % k))

        for i in range(num_trials):
            # k = int( math.log2( b + i - a ) ) // 2
            k = 1 + (i + 1) % 17
            # k = order // 2
            N = int (pow(2, k + 2)) // k

            print (f"#iteration({i}): k= {k}, {N}")
            
            # start a tame kangaroo
            xT = 0
            yT = pow(g, b, p)
            for _ in range(N):
                xT = xT + f(yT, k)
                yT = yT * int(pow(g, f(yT, k)))
            
            xW = 0
            yW = y
            while xW < b - a + xT:
                xW = xW + f(yW, k)
                yW = yW * int(pow(g, f(yW, k)))

                if yW == yT:
                    return xT + b - xW
        
        return None

    @staticmethod
    def Pollard_kangaroo_serial(public_key, order, generator, modulus, b=2**20):
        """ This is the Pollard rho lambda or Pollard Kangaroo algorithm,
        this version is for serial computers (no parallelization).
        it seems like I need to store the first list in a hash table
        Also we do not need to know the order of g to use it.
        """
        # initialization
        alpha = generator # to keep the same variables as in the book
        beta = public_key

        # random walk
        def f(x):
            k = order // 2
            return pow(alpha, int(x), k) % order

        # tame kangaroo
        a = 0
        if b==0:
            b = order//2

        x = pow(alpha, b, modulus)
        # x = Mod(x, modulus)
        x = (x % modulus)

        dx = 0
        i = 0

        # tame kangaroo jumping
        while i < b:
            fx = f(x)
            x = x * pow(alpha, fx, modulus)
            dx += fx
            i += 1

        # wild kangaroo
        # y = Mod(beta, modulus)
        y = (y % modulus)

        dy = 0
        i = 0

        # wild kangaroo jumping
        while i < b:
            fy = f(y)
            y = y * pow(alpha, fy, modulus)
            dy += fy

            # trap
            if x == y:
                return (b + dx - dy) % order
            if dy > b - a + dx:
                break
            i += 1

        # failure
        b = randint(2, order//2)
        return Pollard_kangaroo_serial(public_key, order, generator, modulus, b)

    @staticmethod
    def lenstra_ecm_factorization(n: int, b_max: int = 100000, num_iterations = 100) -> int:
        """
            returns :   (int) factor of n, computed using
                        Lenstra's elliptic curve factorization method

                        Considering standard weirstrass curve
                        y^2 = x^3 + Ax + B (mod N)
        """

        for _ in range(num_iterations):

            # choose point P = (a, b) and then A, B all mod n
            a = random.randint(1, n - 1)
            b = random.randint(1, n - 1)
            P = Point(a, b)

            A = random.randint(1, n - 1)
            B = (b ** 2 - (a ** 3 + A * a)) % n
            
            # choosing the point first, then A and then B ensures the 
            # point (a, b) lies on the curve

            curve = EllipticCurve(A, B, n)

            Q = P
            for j in range(2, b_max):
                try:
                    Q = curve.scale(Q, j)
                except MyError as ex:
                    e = int(ex.__str__())
                    d = CryptoMath.gcd(e, n)
                    if d > 1 and d < n:
                        return d
                    if d == n:
                        break

        return None
        



class Subgroup:
    def __init__(self, sg, sg_order):
        self.sg = sg
        self.sg_order = sg_order




class EllipticCurve:
    """
        Represents an elliptic curve
    """
    def __init__(self, a, b, p, curve_order = None):
        """
            a - curve x-coefficient of type integer
            b - curve constant of type integer
            curve_order - number of elements defined by this elliptic curve group
            p - modulus for the finite field of type integer
        """
        self.curve_order = curve_order
        self.O = Point(0, 1)
        self.p = p
        if a < 0:
            self.a = p + a
        else:
            self.a = a
        if b < 0:
            self.b = p + b
        else:
            self.b = b
        
        self.subgroups = []
        

    @staticmethod
    def get_random_point(curve, p):
        x = y = -1
        x = 2
            
        while True:
            # use CSPRNG
            # x = randint(2, p)
            ysq = ( (x * x * x) + (curve.a * x) + curve.b ) % p
            try:
                y = CryptoMath.TonelliShanksSqrt(ysq, p)
                break
            except:
                print ("x = ", x, " didnt work")
                x = x + 1
                continue
        print ("Found random point on curve: ", curve, "-> (", x, " , ", y, ")")
        if y < 0:
            y = p + y
        return Point(x, y)
    
    
    def add_subgroup(self, sg, sg_order):
        self.subgroups.append(Subgroup(sg, sg_order))
    
    def __inverse__(self, p):
        """
            returns inverse of point p on the Elliptic Curve in GF(p)
        """
        return Point(p.x, (self.p + (-1 * p.y)) % self.p)


    def valid(self, P):
        """
            Determine whether we have a valid representation of a point
            on our curve.  We assume that the x and y coordinates
            are always reduced modulo p, so that we can compare
            two points for equality with a simple ==
        """
        if P == self.O:
            return True
        else:
            return (
                (P.y**2 - (P.x**3 + self.a*P.x + self.b)) % self.p == 0 and
                0 <= P.x < self.p and 0 <= P.y < self.p)
        
    def add(self, p1, p2):
        """
            Add two points p1, p2 in GF(p)

            Arguments-
                p1  -   point on the Elliptic Curve
                p2  -   point on the Elliptoc Curve
            
            Returns-
                point obtained by adding the points p1 and p2

        """
        if p1.equals(self.O):
            return p2

        if p2.equals(self.O):
            return p1

        p2_inv = self.__inverse__(p2)
        if p1.equals(p2_inv):
            return self.O

        x1 = p1.x
        y1 = p1.y

        x2 = p2.x
        y2 = p2.y

        if p1.equals(p2):
            y1_inv = CryptoMath.mod_inv(y1 * 2, self.p, is_positive=True)
            if y1_inv is None:
                raise MyError(y1 * 2)
            m = CryptoMath.mod_mul(  (3 * x1 * x1 + self.a), y1_inv, self.p )
        else:
            x_diff = (x2 - x1)
            x_inv = CryptoMath.mod_inv(x_diff, self.p, is_positive=True)
            if x_inv is None:
                raise MyError(x_diff)
            y_diff = y2 - y1
            m = CryptoMath.mod_mul( y_diff, x_inv, self.p )

        x3 = (m**2 - x1 - x2) % self.p

        y3 = (m * (x1 - x3) - y1) % self.p
        
        # assert(self.valid(new_p))
        return Point(x3, y3)

    def scale(self, x, k):
        """
            compute scalar product x * k

            Arguments-
                x   -   point on the Elliptic Curve
                k   -   scalar integer
            
            Returns-
                Summation of x with itself k times
        """
        result = self.O
        while k > 0:
            if k & 1:
                result = self.add(result, x)
            x = self.add(x, x)
            k = k >> 1
        return result
                

if __name__ == "__main__":
    # print ("mod_exp (2, 7, 11) : ", CryptoMath.mod_exp(2, 7, 11))
    # print ("gcd (1, 0) : ", CryptoMath.gcd(1, 0))
    # print ("gcd (0, 1) : ", CryptoMath.gcd(0, 1))
    # print ("gcd (0, 0) : ", CryptoMath.gcd(0, 0))
    # print ("gcd (10, 5): ", CryptoMath.gcd(10, 5))
    # print ("gcd (12, 16): ", CryptoMath.gcd(12, 16))
    # print ("egcd (12, 16):", CryptoMath.egcd(12, 16))
    # print ("egcd (65537, 18)", CryptoMath.egcd(65537, 18) )
    # print ("mod_inv(18, 65537): ", CryptoMath.mod_inv(18, 65537))
    # print ("fermat_is_prime(2): ", CryptoMath.fermat_is_prime(2))
    # print ("fermat_is_prime(3): ", CryptoMath.fermat_is_prime(3))
    # print ("fermat_is_prime(7): ", CryptoMath.fermat_is_prime(7))
    # print ("fermat_is_prime(11): ", CryptoMath.fermat_is_prime(11))
    # print ("fermat_is_prime(13): ", CryptoMath.fermat_is_prime(13))
    # print ("fermat_is_prime(1105): ", CryptoMath.fermat_is_prime(1105))
    # print ("miller_rabin_is_prime(2): ", CryptoMath.miller_rabin_is_prime(2))
    # print ("miller_rabin_is_prime(3): ", CryptoMath.miller_rabin_is_prime(3))
    # print ("miller_rabin_is_prime(7): ", CryptoMath.miller_rabin_is_prime(7))
    # print ("miller_rabin_is_prime(11): ", CryptoMath.miller_rabin_is_prime(11))
    # print ("miller_rabin_is_prime(13): ", CryptoMath.miller_rabin_is_prime(13))
    # print ("miller_rabin_is_prime(1105): ", CryptoMath.miller_rabin_is_prime(1105))
    # print ("crt ([1, 4, 6], [3, 5, 7]): ", CryptoMath.crt([1, 4, 6], [3, 5, 7]))
    # print ("phi(1): ", CryptoMath.phi(1))
    # print ("phi(2): ", CryptoMath.phi(2))
    # print ("phi(15): ", CryptoMath.phi(15))
    # print ("fermat_factorization(15): ", CryptoMath.fermat_factorization(15))
    # print ("fermat_factorization(121): ", CryptoMath.fermat_factorization(121))
    # print ("fermat_factorization(13273)", CryptoMath.fermat_factorization(13273))
    # print ("pollard_pminus1_factorization(4817191, 1000): ", CryptoMath.pollard_pminus1_factorization2(4817191, 100000))
    # print ("pollard_pminus1_factorization(121, 100): ", CryptoMath.pollard_pminus1_factorization2(121, 100))
    # print ("pollard_pminus1_factorization(1024, 100): ", CryptoMath.pollard_pminus1_factorization2(1024, 100))
    # print ("pollard_pminus1_factorization(65537, 100000): ", CryptoMath.pollard_pminus1_factorization2(65537, 100000))
    # print ("pollard_rho_factorization(4817191): ", CryptoMath.pollards_rho_factorization(4817191))
    # print ("baby_step_giant_step_discrete_logarithm(2, 3, 5): ", CryptoMath.baby_step_giant_step_dlog(2, 3, 5))
    # print ("pollards_rho_discrete_log(2, 3, 5): ", CryptoMath.pollards_rho_dlog(2, 13699544328167240935, 16429744134624869189))
    # print ("pollards_rho_discrete_log(2, 124, 65537): ", CryptoMath.pollards_rho_dlog(2, 124, 65537))
    
    # print ("pollards_kangaroo_discrete_log(2, 124, 65537): ", CryptoMath.pollards_kangaroo_dlog2(2, 124, 65537, 0, 50000))

    A = -95051
    B = 11279326
    p = 233970423115425145524320034830162017933
    G = Point(182, 85518893674295321206118380980485522083)
    order = 29246302889428143187362802287225875743
    test_curve = EllipticCurve(A, B, p, order)   
    P = test_curve.scale(G, order)
    
    assert(P.equals(test_curve.O))

    print ("lenstra_ecm_factorization(602400691612422154516282778947806249229526581): ", CryptoMath.lenstra_ecm_factorization(456))

    
    
    
    
