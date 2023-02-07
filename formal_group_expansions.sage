r"""
Given a genus 2 curve described by an equation of the form
`y^2 = x^5 + b_1 x^4 + b_2 x^3 + b_3 x^2 + b_4 x + b_5`, this code computes:

- expansions of `X_{ij}/X_{111}`, `X_{ijk}/X_{111}`
  as power series in the formal group paramaters `T_1, T_2` of [Gra90];
- expansions for the formal group law with respect to `T_1, T_2` [Gra90];
- expansions for the formal strict logarithm (see [Bia23]);
- expansion for the naive sigma function, or any other sigma function if you
  have an explicit description of the choices of constants this corresponds to
  (see [Bia23]).

NB: In principle, the code should work for `f` defined over a commutative `\QQ`-algebra, but it currently (Sage 9.6) does not always work:
Example: if `f` is defined over a p-adic field, it returns an error.

In this case, there are ways around this issue. The most general is to compute
the expansions over R.<b1,b2,b3,b4,b5> = PolynomialRing(Rationals()) and then specialise (although this might
be slow if you are interested in many digits of precision).

EXAMPLES:: This code gives the expansion of [Bia23, Appendix C]:
    sage: R.<b1,b2,b3,b4,b5,c11,c12,c22> = PolynomialRing(Rationals())
    sage: _.<x> = PolynomialRing(R)
    sage: f = x^5 + b1*x^4+b2*x^3+b3*x^2+b4*x+b5
    sage: %time sigma_gen = sigma_function(f,9,[c11,c12,c22])
    CPU time: 5.22 s, Wall time: 5.40 s

          This computes the canonical `p`-adic sigma function for `y^2 = x^5 -1`
          for every `p` congruent to 1 modulo 10 (cf. [Bia23, 6.5])
    sage: R.<x> = PolynomialRing(Rationals())
    sage: f = x^5 -1
    sage: n = 20
    sage: %time sigma_can = sigma_function(f, n + 1)
    CPU time: 5.88 s, Wall time: 6.11 s
    sage: sigma_can
    T1 + 10/3*T1^4*T2 + 3/2*T1^3*T2^4 + 425/9*T1^7*T2^2 + 2/7*T1^2*T2^7 + 37/30*T1^11 + 329/5*T1^6*T2^5 + 23/315*T1*T2^10 + 76532/81*T1^10*T2^3 + 9439/168*T1^5*T2^8 +             6781/117*T1^14*T2 + 4935/2*T1^9*T2^6 + 6541/189*T1^4*T2^11 + 107815651/4860*T1^13*T2^4 + 5035127/1260*T1^8*T2^9 + 19891/1470*T1^3*T2^14 + 1545775/702*T1^17*T2^2 +             83618243/945*T1^12*T2^7 + 208761373/45360*T1^7*T2^12 + 122582/37485*T1^2*T2^17 + O(T1, T2)^21

REFERENCES:
- [Bia23] \F. Bianchi, "p-Adic sigma functions and heights on Jacobians of
  genus 2 curves", 2023.
- [Gra90] \D. Grant, "Formal groups in genus two", Journal für die reine und angewandte
  Mathematik 411, 1990.
"""

def X111_inv_Xij_X111_inv(f, n):
    r"""
    Return expansions of `1/X_{111}`, `X_{12}/X_{111}`,
    `X_{22}/X_{111}` in `T1,T2`, up to `O(T1,T2)^n`.
    INPUT:
    - ``f`` -- a monic polynomial of degree `5` over a
      commutative ring `R`.
    - ``n`` -- an integer.
    OUTPUT: A list of three polynomials in `R[T1,T2]`, each of total
    degree at most `n-1` that agree up to `O(T1,T2)^n` with the
    expansions of `1/X_{111}`, `X_{12}/X_{111}`, `X_{22}/X_{111}`.
    """
    [b5, b4, b3, b2, b1, b0] = f.coefficients(sparse = False)
    field_coeffs = b5.parent()
    R.<T1,T2> = PolynomialRing(field_coeffs)
    if n <= 3:
        return [R(0), R(0), R(0)]
    alphas = [[] for i in range(n)]
    betas = [[] for i in range(n)]
    gammas = [[] for i in range(n)]

    for i in range(3):
        alphas[i] = [0 for j in range(n)]
    for i in range(1):
        betas[i] = [0 for j in range(n)]
        gammas[i] = [0 for j in range(n)]

    m = 1
    X111_inverse = sum(sum(alphas[r][s]*T1^r*T2^s for r in range(m-s)) for s in range(m))
    X12_over_X111 = sum(sum(gammas[r][s]*T1^r*T2^s for r in range(m-s)) for s in range(m))
    X22_over_X111 = sum(sum(betas[r][s]*T1^r*T2^s for r in range(m-s)) for s in range(m))

    while m < n:
        #only need to consider m odd
        if m%2 == 0:
            for j in range(m+1):
                i = m - j
                if i > 2:
                    alphas[i].append(0)
                if i > 0:
                    betas[i].append(0)
                    gammas[i].append(0)
            m += 1
            continue
        X111_inverse_square = R(X111_inverse^2) #surely you don't need to recompute all this
        X111_inverse_cube = R(X111_inverse_square * X111_inverse)
        X12_over_X111_square = R(X12_over_X111)^2
        X22_over_X111_square = R(X22_over_X111)^2
        X22_over_X111_cube = R(X22_over_X111_square*X22_over_X111)

        for j in range(m + 1):
            i = m - j
            if i<=2:
                continue
            alphas[i].append(-(kronecker_delta(i,3)*kronecker_delta(j,0)
                               - b3*alphas[i-2][j]
                               + b4*sum(sum(gammas[r][s]*alphas[i-1-r][j-s] for r in range(i-3)) for s in range(j+1))
                               - 3*b5*sum(sum(betas[r][s]*alphas[i-1-r][j-s] for r in range(i-3)) for s in range(j+1))
                               - (4*b1*b5 - b2*b4)*X111_inverse_square[i-1, j]
                               - 3*b2*b5*sum(sum(gammas[r][s]*X111_inverse_square[i-r, j-s] for r in range(i-5)) for s in range(j+1))
                               + (4*b3*b5-b4^2)*sum(sum(betas[r][s]*X111_inverse_square[i-r, j-s] for r in range(i-5)) for s in range(j+1))
                               + (4*b1*b3*b5 + b4*b5 -b1*b4^2 - b2^2*b5)*X111_inverse_cube[i,j]))

            if j >= 1:
                alphas[i][j] += 2*b5*X111_inverse_square[i, j-1]

        for j in range(m+1):
            i = m - j
            if i == 0:
                continue
            betas[i].append(- X12_over_X111_square[i+1,j]
                            + b2*sum(sum(gammas[r][s]*alphas[i+1-r][j-s] for r in range(1,i-1)) for s in range(j+1))
                            - b4*X111_inverse_square[i+1, j])
            if j >=1:
                betas[i][j] += 2*alphas[i+1][j-1]

        for j in range(m+1):
            i = m - j
            if i == 0:
                continue
            gammas[i].append(-(-b1*betas[i][j]
                              -b2*(sum(sum(betas[r][s]*gammas[i+1-r][j-s] for r in range(1,i+1)) for s in range(1,j+1)) + sum(betas[r][0]*gammas[i+1-r][j] for r in range(2,i+1))) #or even from 3 in last sum
                              + b3*X22_over_X111_square[i+1, j]
                              + b4*(sum(sum(gammas[r][s]*X22_over_X111_square[i+2-r, j-s] for r in range(1,i+1)) for s in range(j)) + sum(gammas[r][j]*X22_over_X111_square[i+2-r, 0] for r in range(1,i)))
                              - b5*X22_over_X111_cube[i+2,j]
                              - (b3-b1*b2)*sum(sum(gammas[r][s]*alphas[i+1-r][j-s] for r in range(1,i-1)) for s in range(j+1))
                              - (b2^2-b1*b3)*sum(sum(betas[r][s]*alphas[i+1-r][j-s] for r in range(1,i-1)) for s in range(j+1))
                              + (b1*b4-b2*b3 -b5)*sum(sum(sum(sum(alphas[r][s]*betas[q][v]*gammas[i+2-r-q][j-s-v] for q in range(1,i+2-r)) for r in range(3,i+1)) for v in range(j+1-s)) for s in range(j+1))
                              -b1*b5*sum(sum(X22_over_X111_square[r,s]*alphas[i+2-r][j-s] for r in range(2,i)) for s in range(j+1))
                              - (b1*b4-b5)*X111_inverse_square[i+1,j]
                              + b2*(b2^2-b1*b3)*sum(sum(gammas[r][s]*X111_inverse_square[i+2-r,j-s] for r in range(1,i-3)) for s in range(j+1))
                              + (b3*b4-b2*b5)*sum(sum(betas[r][s]*X111_inverse_square[i+2-r,j-s] for r in range(1,i-3)) for s in range(j+1))
                              + (b1*b3*b4-b2^2*b4-b3*b5)*X111_inverse_cube[i+2,j]))

            if j>=1:
                gammas[i][j] += - 2*b1*alphas[i+1][j-1] -2*b2*sum(sum(gammas[r][s]*alphas[i+2-r][j-1-s] for r in range(1,i)) for s in range(j)) + 2*b3*sum(sum(alphas[r][s]*betas[i+2-r][j-1-s] for r in range(3,i+2)) for s in range(j))   + 2*(b1*b3-b2^2)*X111_inverse_square[i+2,j-1]
            if j>=2:
                gammas[i][j] += -alphas[i+2][j-2]

        X111_inverse += sum(alphas[r][m-r]*T1^r*T2^(m-r) for r in range(m+1))
        X12_over_X111 += sum(gammas[r][m-r]*T1^r*T2^(m-r) for r in range(m+1))
        X22_over_X111 += sum(betas[r][m-r]*T1^r*T2^(m-r) for r in range(m+1))

        m += 1

    return [X111_inverse, X12_over_X111, X22_over_X111]


def Xijk_X111_inv(f, n, Xij_X111 = [], also_Xij = False):
    r"""
    Return expansions of `X_{112}/X_{111}`, `X_{122}/X_{111}`,
    `X_{222}/X_{111}` in `T1,T2`, up to `O(T1,T2)^n`.
    INPUT:
    - ``f`` -- a monic polynomial of degree `5` over a
      commutative ring `R`.
    - ``n`` -- an integer.
    - ``Xij_X111`` -- list of expansions in `T1,T2` of
      `1/X_{111}`, `X_{12}/X_{111}`, `X_{22}/X_{111}`, up to
      `O(T1,T2)^n` (given as polynomials).
      If an empty list is provided, these are computed.
    - ``also_Xij`` -- True/False (default False). If `True`,
      the expansions of `1/X_{111}`, `X_{12}/X_{111}`, `X_{22}/X_{111}`
      are also returned.
    OUTPUT: If `also_Xij` is `False`:
    - A list of three polynomials in `R[T1,T2]`, each of total degree at most
    `n-1`, that agree up to `O(T1,T2)^n` with the expansions of
    `X_{112}/X_{111}`, `X_{122}/X_{111}`,`X_{222}/X_{111}`.

            If `also_Xij` is `True`: a tuple consisting of:
    - A list of three polynomials in `R[T1,T2]`, each of total degree at most
    `n-1`, that agree up to `O(T1,T2)^n` with the expansions of
    `X_{112}/X_{111}`, `X_{122}/X_{111}`,`X_{222}/X_{111}`.
    - A list of three polynomials in `R[T1,T2]`, each of total degree at most
    `n-1`, that agree up to `O(T1,T2)^n` with the expansions of
    `1/X_{111}`, `X_{12}/X_{111}`, `X_{22}/X_{111}`.
    """
    if n == 3:
        n += 1
    if Xij_X111 == []:
        Xij_X111 = X111_inv_Xij_X111_inv(f, n)
    X111_inverse = Xij_X111[0]
    X12_over_X111 = Xij_X111[1]
    X22_over_X111 = Xij_X111[2]

    X111_inverse_square = X111_inverse^2
    X22_over_X111_square = X22_over_X111^2
    X12_over_X111_times_X111_inverse = X12_over_X111*X111_inverse
    X22_over_X111_times_X111_inverse = X22_over_X111*X111_inverse
    X12_over_X111_times_X22_over_X111 = X12_over_X111*X22_over_X111

    [b5, b4, b3, b2, b1, b0] = f.coefficients(sparse = False)
    field_coeffs = b5.parent()
    R.<T1,T2> = PolynomialRing(field_coeffs)
    if n <= 2:
        if also_Xij == False:
            return [R(0),R(0),R(0)]
        else:
            return [R(0),R(0),R(0)], Xij_X111
    deltas = [[] for i in range(n)]
    epsilons = [[] for i in range(n)]
    zetas = [[] for i in range(n)]

    deltas[0].extend([0,0,-1,0]) #constant term and coefficient of T2, T2^2, T2^3
    deltas[1].extend([0,0,0]) #coefficients of T1, T1T2, T1T2^2
    deltas[2].extend([0,0]) #coefficients of T1^2, T1^2T2
    deltas[3].extend([0]) #coefficient of T1^3
    epsilons[0].extend([0,0,0,0]) #constant term and coefficients of T2, T2^2, T2^3
    epsilons[1].extend([0,1,0]) #coefficients of T1, T1T2, T1T2^2
    epsilons[2].extend([0,0]) #coefficients of T1^2, T1^2T2
    epsilons[3].extend([0]) #coefficient of T1^3
    zetas[0].extend([0,0,0,0]) #constant term and coefficient of T2, T2^2, T2^3
    zetas[1].extend([0,0,0]) #coefficients of T1, T1T2, T1T2^2
    zetas[2].extend([-1,0]) #coefficients of T1^2, T1^2T2
    zetas[3].extend([0]) #coefficient of T1^3

    m = 4
    X112_over_X111 = sum(sum(deltas[r][s]*T1^r*T2^s for r in range(m-s)) for s in range(m))
    X122_over_X111 = sum(sum(epsilons[r][s]*T1^r*T2^s for r in range(m-s)) for s in range(m))
    X222_over_X111 = sum(sum(zetas[r][s]*T1^r*T2^s for r in range(m-s)) for s in range(m))

    while m < n:
        #only need to consider m even
        if m%2 == 1:
            for j in range(m+1):
                i = m - j
                epsilons[i].append(0)
                zetas[i].append(0)
                deltas[i].append(0)
            m += 1
            continue
        X112_over_X111_square = R(X112_over_X111^2)

        for j in range(m+1):
            i = m-j

            epsilons[i].append(X112_over_X111_square[i,j] #NB: typo in f10 in [Gra90]: first term should be X_{112}^2
                               + 2*b4*X12_over_X111_times_X22_over_X111[i,j]
                               - 3*b5*X22_over_X111_square[i,j]
                               + (b1*b4 - b2*b3 -b5)*X12_over_X111_times_X111_inverse[i,j]
                               - 2*b1*b5*X22_over_X111_times_X111_inverse[i,j]
                               + (b3*b4-b2*b5)*X111_inverse_square[i,j])
            if i>=1:
                epsilons[i][j] += b3*X22_over_X111[i-1,j]
            if j>=1:
                epsilons[i][j] += -2*b3*X111_inverse[i,j-1]
        X122_over_X111 += sum(epsilons[r][m-r]*T1^r*T2^(m-r) for r in range(m+1))

        for j in range(m+1):
            i = m-j
            zetas[i].append(-(-(sum(sum(deltas[r][s]*epsilons[i-r][j-s] for r in range(i+1)) for s in range(j)) + sum(deltas[r][j]*epsilons[i-r][0] for r in range(i)))
                              - 2*b3*X12_over_X111_times_X22_over_X111[i,j]
                              + b4*X22_over_X111_square[i,j]
                              + (3*b2^2-2*b1*b3)*X12_over_X111_times_X111_inverse[i,j]
                              + (b1*b4-b5)*X22_over_X111_times_X111_inverse[i,j]
                              - 2*b2*b4*X111_inverse_square[i,j]))

            if j>=1:
                zetas[i][j] += -2*X12_over_X111[i,j-1] - 5*b2*X111_inverse[i,j-1]
            if i>=1:
                zetas[i][j] += -2*b1*X12_over_X111[i-1,j] + 3*b2*X22_over_X111[i-1,j] + b3*X111_inverse[i-1,j]

        X222_over_X111 += sum(zetas[r][m-r]*T1^r*T2^(m-r) for r in range(m+1))
        X222_over_X111_square = R(X222_over_X111^2)

        for j in range(m+1):
            i = m - j
            deltas[i].append(b1*epsilons[i][j]
                             - b2*(sum(sum(deltas[r][s]*epsilons[i-r][j-s] for r in range(i+1)) for s in range(j)) + sum(deltas[r][j]*epsilons[i-r][0] for r in range(i)))
                             + b3*(sum(sum(deltas[r][s]*zetas[i-r][j-s] for r in range(i+1)) for s in range(j)) + sum(deltas[r][j]*zetas[i-r][0] for r in range(i)))
                             - b4*(sum(sum(zetas[r][s]*epsilons[i-r][j-s] for r in range(i+1)) for s in range(j+1)))
                             + b5*X222_over_X111_square[i,j]
                             - (b5+b1*b4)*X12_over_X111_times_X22_over_X111[i,j]
                             + 2*b1*b5*X22_over_X111_square[i,j]
                             + (2*b2*b4+b1*b2*b3+b1*b5-b3^2-b1^2*b4)*X12_over_X111_times_X111_inverse[i,j]
                             + 2*b5*(b1^2-b2)*X22_over_X111_times_X111_inverse[i,j]
                             + (b1*b2*b5 - b1*b3*b4 - 2*b3*b5)*X111_inverse_square[i,j])

            if j>=1:
                deltas[i][j] +=  - b2*X12_over_X111[i,j-1] + b3*X22_over_X111[i,j-1] + 2*(b1*b3+b4)*X111_inverse[i,j-1]
            if i>=1:
                deltas[i][j] += b3*X12_over_X111[i-1,j] - b1*b3*X22_over_X111[i-1,j] + 2*b5*X111_inverse[i-1,j]

        X112_over_X111 += sum(deltas[r][m-r]*T1^r*T2^(m-r) for r in range(m+1))
        m += 1

    if also_Xij == False:
        return [X112_over_X111, X122_over_X111, X222_over_X111]
    else:
        return [X112_over_X111, X122_over_X111, X222_over_X111], Xij_X111


def F1_F2(f,n, Xij_X111 = [], Xijk_X111 = []):
    r"""
    Return expansions of the formal group law up to
    `O(T1,T2,S1,S2)^n`.
    INPUT:
    - ``f`` -- a monic polynomial of degree `5` over a
      characteristic `0` integral domain `R` where `2` is invertible.
    - ``n`` -- an integer.
    - ``Xij_X111`` -- list of expansions in `T1,T2` of
      `1/X_{111}`, `X_{12}/X_{111}`, `X_{22}/X_{111}`, up to
      `O(T1,T2)^{n+2}` (given as power series over `R`).
      If an empty list is provided, these are computed.
    - ``Xijk_X111`` -- list of expansions in `T1,T2` of
      `X_{112}/X_{111}`, `X_{122}/X_{111}`,`X_{222}/X_{111}`, up to
      `O(T1,T2)^{n+1}` (given as power series over `R`).
      If an empty list is provided, these are computed.
    OUTPUT: A tuple consisting of:
    - A list of two power series in `R[[T1,T2,S1,S2]]`
      giving the formal group law up to `O(T1,T2,S1,S2)^n`.
    - A list of three power series in `R[[T1,T2]]`
      giving the expansions of `T1^3*X_{11}`, `T1^3*X_{12}`, `T1^3*X_{22}`
      up to `O(T1,T2)^n`, `O(T1,T2)^{n+2}`, `O(T1,T2)^{n+2}`, respectively.
    """
    if n == 2:
        n += 1
    [b5, b4, b3, b2, b1, b0] = f.coefficients(sparse = False)
    field_coeffs = b5.parent()
    _.<T1,T2> = PowerSeriesRing(field_coeffs)
    if n <= 1:
        R2.<T1,T2,S1,S2> = PowerSeriesRing(field_coeffs)
        return [R2(0), R2(0)], [_(0), _(0), _(0)]
    if Xij_X111 == []:
        Xij_X111_pol = X111_inv_Xij_X111_inv(f, n+2)
        Xij_X111 = [_(Xij_X111_pol[i] + O(T1,T2)^(n+2)) for i in range(3)]
    if Xijk_X111 == []:
        Xijk_X111_pol = Xijk_X111_inv(f, n+1, Xij_X111 = Xij_X111_pol)
        Xijk_X111 = [_(Xijk_X111_pol[i] + O(T1,T2)^(n+1)) for i in range(3)]
    X111_inverse = Xij_X111[0]
    X12_over_X111 = Xij_X111[1]
    X22_over_X111 = Xij_X111[2]
    X112_over_X111 = Xijk_X111[0]
    X122_over_X111 = Xijk_X111[1]
    X222_over_X111 = Xijk_X111[2]

    X111_times_T1_cube = (X111_inverse/T1^3)^(-1)
    X11_times_T1_cube = X111_times_T1_cube*(-T1)
    X22_times_T1_cube =  X22_over_X111*X111_times_T1_cube
    X12_times_T1_cube = X12_over_X111*X111_times_T1_cube

    X122_times_T1_cube = X122_over_X111*X111_times_T1_cube
    X222_times_T1_cube = X222_over_X111*X111_times_T1_cube
    X112_times_T1_cube = X112_over_X111*X111_times_T1_cube

    R2.<T1,T2,S1,S2> = PowerSeriesRing(field_coeffs)
    X11u_times_T1_cube = R2(X11_times_T1_cube)
    X11v_times_S1_cube = X11u_times_T1_cube(S1,S2,T1,T2)

    X12u_times_T1_cube = R2(X12_times_T1_cube)
    X12v_times_S1_cube = X12u_times_T1_cube(S1,S2,T1,T2)

    X22u_times_T1_cube = R2(X22_times_T1_cube)
    X22v_times_S1_cube = X22u_times_T1_cube(S1,S2,T1,T2)

    X111u_times_T1_cube = R2(X111_times_T1_cube)
    X111v_times_S1_cube = X111u_times_T1_cube(S1,S2,T1,T2)

    X122u_times_T1_cube = R2(X122_times_T1_cube)
    X122v_times_S1_cube = X122u_times_T1_cube(S1,S2,T1,T2)

    X222u_times_T1_cube = R2(X222_times_T1_cube)
    X222v_times_S1_cube = X222u_times_T1_cube(S1,S2,T1,T2)

    X112u_times_T1_cube = R2(X112_times_T1_cube)
    X112v_times_S1_cube = X112u_times_T1_cube(S1,S2,T1,T2)

    wpu_times_T1_cube = -2*X111u_times_T1_cube*T2 - b2*X12u_times_T1_cube + b4*T1^3
    wpv_times_S1_cube = wpu_times_T1_cube(S1,S2,T1,T2)

    q_uv_times_T1S1_cube = X11u_times_T1_cube*S1^3  + X12u_times_T1_cube*X22v_times_S1_cube
    q_uv_times_T1S1_cube += -q_uv_times_T1S1_cube(S1,S2,T1,T2)

    q1_uv_times_T1S1_cube = 2*X111u_times_T1_cube*S1^3 + 2*X112u_times_T1_cube*X22v_times_S1_cube + 2*X122v_times_S1_cube*X12u_times_T1_cube
    q1_uv_times_T1S1_cube += -q1_uv_times_T1S1_cube(S1,S2,T1,T2)

    q11_uv_times_T1S1_cube = 4*b3*q_uv_times_T1S1_cube + 4*b4*(X12u_times_T1_cube*S1^3 - X12v_times_S1_cube*T1^3) + 4*(wpu_times_T1_cube*X12v_times_S1_cube - wpv_times_S1_cube*X12u_times_T1_cube) - 8*b5*(X22u_times_T1_cube*S1^3 - X22v_times_S1_cube*T1^3) + 8*(X112u_times_T1_cube*X122v_times_S1_cube - X112v_times_S1_cube*X122u_times_T1_cube)

    q111_uv_times_T1S1_pow_6  = 4*b3*q1_uv_times_T1S1_cube *T1^3*S1^3 + 8*(X111u_times_T1_cube*X22u_times_T1_cube*X12v_times_S1_cube*S1^3 - X111v_times_S1_cube*X22v_times_S1_cube*X12u_times_T1_cube*T1^3) + 2*X122v_times_S1_cube*(2*X12u_times_T1_cube*(6*X11u_times_T1_cube*S1^3 - 2*X11v_times_S1_cube*T1^3 + 4*b3*T1^3*S1^3)-4*b4*X22u_times_T1_cube*T1^3*S1^3)-2*X122u_times_T1_cube*(2*X12v_times_S1_cube*(6*X11v_times_S1_cube*T1^3 - 2*X11u_times_T1_cube*S1^3 + 4*b3*T1^3*S1^3)-4*b4*X22v_times_S1_cube*T1^3*S1^3)+ 2*X112u_times_T1_cube*(X12v_times_S1_cube*(12*X12v_times_S1_cube*T1^3-8*X12u_times_T1_cube*S1^3+4*b2*T1^3*S1^3)+4*b4*S1^6*T1^3)-2*X112v_times_S1_cube*(X12u_times_T1_cube*(12*X12u_times_T1_cube*S1^3-8*X12v_times_S1_cube*T1^3+4*b2*T1^3*S1^3)+4*b4*T1^6*S1^3)

    q_uv_times_T1S1_cube_square = q_uv_times_T1S1_cube^2
    q_uv_times_T1S1_cube_cube = q_uv_times_T1S1_cube*q_uv_times_T1S1_cube_square
    q1_uv_times_T1S1_cube_square = q1_uv_times_T1S1_cube^2
    q1_uv_times_T1S1_cube_cube = q1_uv_times_T1S1_cube*q1_uv_times_T1S1_cube_square


    X11_uv_times_T1S1_pow_9_times_q_uv_square = -(X11u_times_T1_cube*S1^3 + X11v_times_S1_cube*T1^3)*q_uv_times_T1S1_cube_square + 1/4*q1_uv_times_T1S1_cube_square*T1^3*S1^3 - 1/4*q11_uv_times_T1S1_cube*q_uv_times_T1S1_cube*T1^3*S1^3

    X111_uv_times_T1S1_pow_12_times_q_uv_cube = -1/2*(X111u_times_T1_cube*S1^3 + X111v_times_S1_cube*T1^3)*q_uv_times_T1S1_cube_cube + 3/16*q1_uv_times_T1S1_cube*q11_uv_times_T1S1_cube*q_uv_times_T1S1_cube*T1^3*S1^3 - 1/16*q111_uv_times_T1S1_pow_6*q_uv_times_T1S1_cube_square - 1/8*q1_uv_times_T1S1_cube_cube*T1^3*S1^3 + 3/4*(X11u_times_T1_cube*S1^3 + X11v_times_S1_cube*T1^3)*q1_uv_times_T1S1_cube*q_uv_times_T1S1_cube_square


    q2_uv_times_T1S1_cube = 2*(X112u_times_T1_cube*S1^3 + X122u_times_T1_cube*X22v_times_S1_cube + X222v_times_S1_cube*X12u_times_T1_cube)
    q2_uv_times_T1S1_cube += -q2_uv_times_T1S1_cube(S1,S2,T1,T2)
    q12_uv_times_T1S1_cube = 4*b3*X12u_times_T1_cube*S1^3 + 2*b2*X12u_times_T1_cube*X22v_times_S1_cube - 4*X11u_times_T1_cube*X12v_times_S1_cube + 2*wpu_times_T1_cube*X22v_times_S1_cube - 2*b4*X22u_times_T1_cube*S1^3 + 4*X222v_times_S1_cube*X112u_times_T1_cube
    q12_uv_times_T1S1_cube += -q12_uv_times_T1S1_cube(S1,S2,T1,T2)

    X12_uv_times_T1S1_pow_9_times_q_uv_square = -(X12u_times_T1_cube*S1^3 + X12v_times_S1_cube*T1^3)*q_uv_times_T1S1_cube_square + 1/4*q1_uv_times_T1S1_cube*q2_uv_times_T1S1_cube*T1^3*S1^3 -1/4*q12_uv_times_T1S1_cube*q_uv_times_T1S1_cube*T1^3*S1^3

    q22_uv_times_T1S1_cube = 8*b1*X12u_times_T1_cube*X22v_times_S1_cube + 4*b2*X12u_times_T1_cube*S1^3 - 4*wpu_times_T1_cube*S1^3 - 8*X11u_times_T1_cube*X22v_times_S1_cube + 8*X122u_times_T1_cube*X222v_times_S1_cube
    q22_uv_times_T1S1_cube += - q22_uv_times_T1S1_cube(S1,S2,T1,T2)

    q2_uv_times_T1S1_cube_square = q2_uv_times_T1S1_cube^2

    X22_uv_times_T1S1_pow_9_times_q_uv_square = -(X22u_times_T1_cube*S1^3 + X22v_times_S1_cube*T1^3)*q_uv_times_T1S1_cube_square + 1/4*q2_uv_times_T1S1_cube_square*T1^3*S1^3 - 1/4*q22_uv_times_T1S1_cube*q_uv_times_T1S1_cube*T1^3*S1^3

    wp_uv_times_T1S1_pow_18_times_q_uv_pow_4 = X11_uv_times_T1S1_pow_9_times_q_uv_square * X22_uv_times_T1S1_pow_9_times_q_uv_square - X12_uv_times_T1S1_pow_9_times_q_uv_square^2

    X_uv_times_T1S1_pow_18_times_q_uv_pow_4 = 1/2*(wp_uv_times_T1S1_pow_18_times_q_uv_pow_4 + b2*X12_uv_times_T1S1_pow_9_times_q_uv_square*q_uv_times_T1S1_cube_square*T1^3*S1^3-b4*q_uv_times_T1S1_cube*q_uv_times_T1S1_cube_cube*T1^6*S1^6)

    F1 = ((-X11_uv_times_T1S1_pow_9_times_q_uv_square*q_uv_times_T1S1_cube)/X111_uv_times_T1S1_pow_12_times_q_uv_cube)
    F2 = (-X_uv_times_T1S1_pow_18_times_q_uv_pow_4/(X111_uv_times_T1S1_pow_12_times_q_uv_cube*T1^3*S1^3*q_uv_times_T1S1_cube))

    return [F1, F2], [X11_times_T1_cube, X12_times_T1_cube, X22_times_T1_cube]


def solve_diff_eq_D1D2(D1g, D2g, mat, T1, T2):
    r"""
    Solve a system of two differential equations.
    Let `D_1`, `D_2` be the invariant derivations corresponding
    the the strict formal group exponential. Then find the power series
    `g(T1,T2)` such that `D_1(g) = D1g`, `D_2(g) = D2g` and `g(0,0) = 0`.
    (if `g` exists).
    INPUT:
    - ``D1g`` -- a power series in `T1`,`T2`.
    - ``D2g`` -- a power series in `T1`,`T2`.
    - ``mat`` -- the`2x2` matrix `(\partial F_i/\partial T_j ((0,0,T1,T2)))^{-1}`.
    - ``T1,T2`` -- variables.
    OUTPUT: a power series
    """
    dg_dTi = mat.transpose()*vector([D1g, D2g])
    dg_dT1 = dg_dTi[0]
    dg_dT2 = dg_dTi[1]
    g_minus_hT2 = dg_dT1.integral(T1)
    dh_dT2 = dg_dT2 - g_minus_hT2.derivative(T2)
    g = g_minus_hT2 + dh_dT2.integral(T2)
    assert g.derivative(T1) == dg_dT1, "No solutions."
    return g


def strict_log(f, n, Fs = False):
    r"""
    Return expansions for the strict formal group logarithm,
    the matrix `(\partial F_i/\partial T_j ((0,0,T1,T2)))^{-1}` and
    its inverse.
    The strict logarithm is returned up to `O(T1,T2)^n`, the matrices
    up to `O(T1,T2)^{n-1}`.
    NOTE: `f` should be defined over a commutative `\QQ` algebra.
    """
    field_coeffs = f.parent().base_ring()

    if Fs == False:
        Fs = F1_F2(f,n, Xij_X111 = [], Xijk_X111 = [])[0]
    F1 = Fs[0]
    F2 = Fs[1]
    T1 = F1.parent().gens()[0]
    T2 = F1.parent().gens()[1]
    FS = Matrix([[F1.derivative(T1), F1.derivative(T2)],[F2.derivative(T1), F2.derivative(T2)]])
    matinv = FS(0,0,T1,T2)
    _.<T1,T2> = PowerSeriesRing(field_coeffs)
    try:
        matinv = matinv.change_ring(_)
    except TypeError:
        #problem in coercion of power series ring for certain base rings, e.g. a polynomial ring.
        matinv_new = matrix(_,2)
        for r in range(2):
            for s in range(2):
                m = matinv[r,s].precision_absolute()
                matinv_new[r,s] = sum([sum([matinv[r,s].polynomial()[i,j,0,0]*T1^i*T2^j for i in range(m-j)]) for j in range(m)])
                matinv_new[r,s] = matinv_new[r,s] + O(T1,T2)^m
        matinv = matinv_new

    mat = matinv^(-1)
    mat = mat.change_ring(_)
    z1_T1T2 = solve_diff_eq_D1D2(1, 0, mat, T1, T2)
    z2_T1T2 = solve_diff_eq_D1D2(0, 1, mat, T1, T2)
    return [z1_T1T2, z2_T1T2], matinv, mat


def D1(h, matinv, T1, T2):
    r"""
    Return `D_1(h)`.
    INPUT:
    - ``h`` -- a power series in `T1`,`T2`.
    - ``matinv`` -- the`2x2` matrix `(\partial F_i/\partial T_j ((0,0,T1,T2)))`
    - ``T1,T2`` -- variables.
    OUTPUT: a power series.
    """
    return matinv[0,0]*h.derivative(T1) + matinv[1,0]*h.derivative(T2)


def D2(h, matinv, T1, T2):
    r"""
    Return `D_2(h)`.
    INPUT:
    - ``h`` -- a power series in `T1`,`T2`.
    - ``matinv`` -- the`2x2` matrix `(\partial F_i/\partial T_j ((0,0,T1,T2)))`
    - ``T1,T2`` -- variables.
    OUTPUT: a power series.
    """
    return matinv[0,1]*h.derivative(T1) + matinv[1,1]*h.derivative(T2)


def sigma_function(f, n, cij = [0,0,0]):
    r"""
    Return the sigma function corresponding to
    the choice of constants `cij`, up to `O(T1,T2)^n`.
    INPUT:
    - ``f`` -- a monic polynomial of degree `5` over a
      commutative `\QQ` algebra.
    - ``n`` -- an integer.
    - ``cij`` -- a list of constants.
    OUTPUT: A power series in `T1,T2`.
    """
    Xij_X111_pol = X111_inv_Xij_X111_inv(f, n + 2)
    Xijk_X111_pol = Xijk_X111_inv(f, n + 1 , Xij_X111 = Xij_X111_pol, also_Xij = False)
    _.<T1,T2> = PowerSeriesRing(f.parent().base_ring())
    if n <= 1:
        return _(0).add_bigoh(1)
    if n <= 3:
        return T1 + O(T1,T2)^3
    Xij_X111 = [_(Xij_X111_pol[i] + O(T1,T2)^(n+2)) for i in range(3)]
    Xijk_X111 = [_(Xijk_X111_pol[i] + O(T1,T2)^(n+1)) for i in range(3)]
    Fs, Xij_times_T1_cube = F1_F2(f, n, Xij_X111 = Xij_X111, Xijk_X111 = Xijk_X111)
    LOG, matinv, mat = strict_log(f, n, Fs = Fs)
    D1T1 = D1(T1, matinv, T1, T2)
    D2T1 = D2(T1, matinv, T1, T2)
    D1D1T1 = D1(D1T1, matinv, T1, T2)
    D1D2T1 = D1(D2T1, matinv, T1, T2)
    D2D2T1 = D2(D2T1, matinv, T1, T2)

    D1D1logu = (-Xij_times_T1_cube[0]-T1*(D1D1T1*T1-D1T1^2))/T1^3
    D1D2logu = (-Xij_times_T1_cube[1]-T1*(D1D2T1*T1-D1T1*D2T1))/T1^3
    D2D2logu = (-Xij_times_T1_cube[2]-T1*(D2D2T1*T1-D2T1^2))/T1^3

    D1logu = solve_diff_eq_D1D2(D1D1logu, D1D2logu, mat, T1, T2)
    D2logu = solve_diff_eq_D1D2(D1D2logu, D2D2logu, mat, T1, T2)
    logu = solve_diff_eq_D1D2(D1logu, D2logu, mat, T1, T2)
    u = logu.exp()
    sigma0 = T1*u
    if cij == [0,0,0]:
        sigma = sigma0
    else:
        sigma = sigma0*exp(1/2*cij[0]*LOG[0]^2 + cij[1]*LOG[0]*LOG[1] + 1/2*cij[2]*LOG[1]^2)
    #be careful with default precisions when we have exponentials, but doesn't seem a problem.
    if sigma.precision_absolute() == +Infinity:
        sigma = sigma.add_bigoh(n)
    return sigma
