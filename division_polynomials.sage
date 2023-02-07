r"""
This is a translation to SageMath of Magma code by de Jong--Mueller,
based on the paper [dJM14].
The code computes division values of points on Jacobians of odd degree genus 2
hyperelliptic curves, using division polynomials `phi_n (n<=5)` as computed by
Uchida and the recurrence relations of [Kan10, Theorem 9 (corrected)]
and [Uch11, Example 6.6].

The function `division_value_new` is new.
It provides a more efficient way of computing a division value:
see [Bia23, Remark 6.4].

Start date: 06/07/2020

REFERENCES:
- [Bia23] \F. Bianchi, "p-Adic sigma functions and heights on Jacobians of
  genus 2 curves", 2023.
- [dJM14] \R. de Jong and J.S. Mueller, "Canonical heights and division polynomials",
  Math. Proc. Cambridge Philos. Soc. 157, 2014.
- [Gra90] \D. Grant, "Formal groups in genus two", Journal für die reine und angewandte
  Mathematik 411, 1990.
- [Kan10] \N. Kanayama, Corrections to "Division polynomials and multiplication
  formulae in dimension 2", Math. Proc. Cambridge Philos. Soc. 149, 2010.
- [Uch11] \Y. Uchida, "Division polynomials and canonical local heights on hyperelliptic Jacobians",
  Manuscripta Mathematica 134, 2011.
"""

load("./phi345.sage")

def variable_Di(f, i, coefs, vars):
    r"""
    Given an element f of `vars = [p11,...,p222]`, an integer `i`
    and a set of coefficients specifying a genus 2 curve,
    return the derivation `D_i(f)` as in [Kan10, Theorem 9].
    """
    f4, f3, f2, f1, f0 = coefs
    if i == 1:
        return {
        vars[0]: vars[3],
        vars[1]: vars[4],
        vars[2]: vars[5],
        vars[3]: 6*vars[0]^2 + 4*f2*vars[0] + 4*f1*vars[1] - 12*f0*vars[2] - 8*f4*f0 + 2*f3*f1,
        vars[4]: 6*vars[0]*vars[1] + 4*f2*vars[1] - 2*f1*vars[2] - 4*f0,
        vars[5]: 2*vars[0]*vars[2] + 4*vars[1]^2 + 2*f3*vars[1],
        vars[6]: 6*vars[1]*vars[2] - 2*vars[0] + 4*f4*vars[1],
        }[f]
    else:
        return {
        vars[0]: vars[4],
        vars[1]: vars[5],
        vars[2]: vars[6],
        vars[3]: 6*vars[0]*vars[1] + 4*f2*vars[1] - 2*f1*vars[2] - 4*f0,
        vars[4]: 2*vars[0]*vars[2] + 4*vars[1]^2 + 2*f3*vars[1],
        vars[5]: 6*vars[1]*vars[2] - 2*vars[0] + 4*f4*vars[1],
        vars[6]: 6*vars[2]^2 + 4*vars[1] + 4*f4*vars[2] + 2*f3,
        }[f]


def monomial_Di(f, i, j, coefs, vars):
    r"""
    Given a monomial `f` in `vars = [p11,...,p222]`, an integer `i`
    and a set of coefficients specifying a genus 2 curve,
    return the derivation `D_i(f)` as in [Kan10, Theorem 9].
    """
    if f.is_one():
        return 0
    deg = f.degrees()[j-1]
    deg = ZZ(deg)
    if deg.is_zero():
        return monomial_Di(f, i, j + 1, coefs, vars)
    else:
        pj = vars[j-1]
        g = f.quo_rem(pj^deg)[0]
        return pj^deg * monomial_Di(g, i, j + 1, coefs, vars) + deg*pj^(deg - 1)*g*variable_Di(pj, i, coefs, vars)


def Di(f, i, coefs, vars):
    r"""
    Given a polynomial `f` in `vars = [p11,...,p222]`, an integer `i`
    and a set of coefficients specifying a genus 2 curve,
    return the derivation `D_i(f)` as in [Kan10, Theorem 9].
    """
    C = f.coefficients()
    M = f.monomials()
    return sum([C[j]*monomial_Di(M[j], i, 1, coefs, vars) for j in range(len(M))])


def initial_division_polynomials(coefs):
    r"""
    Compute the first 5 division polynomials associated to
    the Jacobian of the genus 2 curve specified by
    the coefficients `coefs = [f4, f3, f2, f1, f0]`.
    """
    #R = FractionField(coefs[0].parent())
    R = coefs[0].parent()
    _.<p11, p12, p22, p111, p112, p122, p222> = PolynomialRing(R)
    L = [R.one(),  p12 * p122 - p22 * p112 - p111]
    p = [p11, p12, p22, p111, p112, p122, p222]
    L.extend([phi3(p, coefs), phi4nf(p, coefs),phi5nf(p, coefs)])
    return L


def division_values(P, fs, bd):
    r"""
    Return the values of the division polynomials `phi_m`
    at `P` for all `1<=m<=bd`
    `P` is a point on a Jacobian surface, not in the support
    of the theta divisor.
    If `bd>5`, then `2P` should not be in the support of theta either.
    If `bd>8`, then `\phi_5(P) - \phi_4(P)\phi_2(P)^3 + \phi_3(P)^3`
    should be non-zero.
    """
    #FB:
    g = 2
    assert P[0].degree() == g, "P lies on the theta divisor"

    coefs = [fs[i] for i in range(len(fs)-1)]
    coefs.reverse()
    phi = initial_division_polynomials(coefs)
    PR = phi[1].parent()
    vars = [PR.gens()[i] for i in range(7)]
    pgis = [-P[0][g - i - 1] for i in range(g)]
    pggis = [2*P[1][g - i - 1 ] for i in range(g)]
    #now add p11, p111, p112
    #p11, using f_6 in [Gra90]:
    pgis.append( -pgis[0]^3 - pgis[0]*pgis[1] - fs[4]*pgis[0]^2 - fs[3]*pgis[0] - fs[2] + pggis[0]^2 / 4)
    #p112, using f_3 in [Gra90]:
    pggis.append(pgis[1]*pggis[0] - pgis[0]*pggis[1])
    #p111, using f_4 in [Gra90]:
    pggis.append(2*(pgis[0] + fs[4])*pggis[2] - (pgis[1] + fs[3])*pggis[1] - pgis[2]*pggis[0])
    #The orders are [p22, p12, p11] and [p222, p122, p112, p111].
    #But now we are going to reorder them
    pgis.reverse()
    pggis.reverse()
    ps = pgis + pggis # [p11, p12, p22, p111, p112, p122, p222]

    L = [PR(p)(ps) for p in phi]
    if bd <= 5:
        return L

    assert L[1] != 0, "2P lies on the theta divisor"

    hms = []
    for n in range(1,5):
        derivs_n1 = Di(phi[n], 1, coefs, vars)(ps)
        d_n2 = Di(phi[n], 2, coefs, vars)
        derivs_n2 = d_n2(ps)
        dderivs_n1 = Di(d_n2, 1, coefs, vars)(ps)
        dderivs_n2 = Di(d_n2, 2, coefs, vars)(ps)
        hms.append([derivs_n1*derivs_n2 - L[n]*dderivs_n1, derivs_n2^2 - L[n]*dderivs_n2])

    #phi6:
    L.append((L[1]^2 * L[2] * L[4] - L[3]^2 * L[2] * L[0] + (hms[0][0] * hms[2][1] - hms[0][1] * hms[2][0]) / 64) / L[1])
    #phi7:
    L.append(L[2]^3 * L[4] - L[3]^3 * L[1] + (hms[1][0] * hms[2][1] - hms[1][1] * hms[2][0]) / 144)
    #phi8:
    L.append((L[2]^2 * L[3] * L[5] - L[4]^2 * L[3] * L[1] + (hms[1][0] * hms[3][1] - hms[1][1] * hms[3][0]) / 225) / L[1])

    if bd <= 8:
        return L

    quotient = L[4] - L[3] * L[1]^3 + L[2]^3
    assert quotient != 0, "quotient vanishes at P"

    m = 4
    while 2*m <= bd:
        if m > 4:
            #phi_{2m}
            L.append((L[m + 3] * L[m] * L[m - 3] * L[m - 4] - L[m + 3] * L[m - 1] * L[m - 3]^2 * L[1]^2 + L[m + 3] * L[m - 2]^2 * L[m - 3] * L[2] - L[m + 2] * L[m + 1] * L[m - 2] * L[m - 5] + L[m + 2] * L[m - 1] * L[m - 2] * L[m - 3] * L[2]^2 - L[m + 2] * L[m - 2]^3 * L[3] * L[1] + L[m + 1]^2 * L[m - 1] * L[m - 5] * L[1]^2 - L[m + 1] * L[m] * L[m - 1] * L[m - 4] * L[2]^2 + L[m + 1] * L[m - 1] * L[m - 2]^2 * L[4] - L[m + 1] * L[m]^2 * L[m - 5] * L[2] + L[m]^3 * L[m - 4] * L[3] * L[1] - L[m]^2 * L[m - 1] * L[m - 3] * L[4]) / L[1] / quotient)

        if 2*m != bd:
            #phi_{2m+1}
            L.append((L[m + 3] * L[m + 1] * L[m - 3]^2 - L[m + 3] * L[m] * L[m - 2] * L[m - 3] * L[1]^2 + L[m + 3] * L[m - 1]^2 * L[m - 3] * L[2] - L[m + 2]^2 * L[m - 2] * L[m - 4] + L[m + 2] * L[m] * L[m - 2]^2 * L[2]^2 - L[m + 2] * L[m - 1]^2 * L[m - 2] * L[3] * L[1] + L[m + 2] * L[m + 1] * L[m - 1] * L[m - 4] * L[1]^2 - L[m + 1]^2 * L[m - 1] * L[m - 3] * L[2]^2 + L[m + 1] * L[m - 1]^3 * L[4] - L[m + 2] * L[m]^2 * L[m - 4] * L[2] + L[m + 1] * L[m]^2 * L[m - 3] * L[3] * L[1] - L[m]^3 * L[m - 2] * L[4]) / quotient)

        m += 1
    return L


def division_value(P, fs, bd):
    r"""
    Returns `phi_{bd}(P)`.
    For more efficient implementation, use
    `division_value_new`.
    """
    return division_values(P, fs, bd)[bd-1]


def division_value_new(P, fs, bd):
    r"""
    FB: 18/11/2020
    In order to compute the `m`-th division values `phi_m(P)`,
    no need to compute `phi_k(P)` for all `k<=m` (but only for some).
    The code for this is based on the source code for
    `_multiply_point(E, R, P, m)` in `sage.schemes.elliptic_curves.padics`
    (implemented by Harvey).

    EXAMPLES:
    Comparing time and output with `division_value`:
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^3*(x-1)^2 +1
        sage: fs = f.coefficients(sparse = False)
        sage: X = HyperellipticCurve(f)
        sage: J = Jacobian(X)
        sage: P = J(X(0,-1), X(1,-1))
        sage: %time dv = division_value(P, fs, 1000)
        CPU time: 19.92 s, Wall time: 21.29 s
        sage: %time dv_new = division_value_new(P, fs, 1000)
        CPU time: 1.81 s, Wall time: 2.96 s
        sage: dv == dv_new
        True

    It runs also over the `p`-adics or integers modulo a positive
    integer, as long as the coefficients `fs` are coerced into `\QQ` or `\ZZ`:
        sage: R.<x> = PolynomialRing(QQ)
        sage: f = x^3*(x-1)^2 +1
        sage: fs = f.coefficients(sparse = False)
        sage: X = HyperellipticCurve(f)
        sage: J = Jacobian(X)
        sage: P = J(X(0,-1), X(1,-1))
        sage: %time dv_Q = division_value_new(P, fs, 5000)
        CPU time: 31.93 s, Wall time: 38.07 s
        sage: p = 11; n = 30
        sage: K = Qp(p,n)
        sage: XK = X.change_ring(K)
        sage: JK = Jacobian(XK)
        verbose 0 (3848: multi_polynomial_ideal.py, groebner_basis) Warning: falling back to very slow toy implementation.
        verbose 0 (1081: multi_polynomial_ideal.py, dimension) Warning: falling back to very slow toy implementation.
        sage: PK = JK(P[0].change_ring(K),P[1].change_ring(K))
        sage: %time dv_K = division_value_new(PK, fs, 5000)
        CPU time: 1.04 s, Wall time: 2.18 s
        sage: Pp0 = P[0].change_ring(Integers(p^n))
        sage: Pp1 = P[1].change_ring(Integers(p^n))
        sage: fs = [ZZ(fss) for fss in fs]
        sage: %time dv_R = division_value_new((Pp0,Pp1), fs, 5000)
        CPU time: 0.85 s, Wall time: 0.88 s
        sage: dv_K - dv_Q
        O(11^30)
        sage: dv_K - dv_K.parent()(dv_R)
        O(11^30)
    """

    if bd <= 8:
        return division_values(P, fs, bd)[bd-1]

    #The following is similar to the source code for
    #`_multiply_point(E, R, P, m)` in `sage.schemes.elliptic_curves.padics`
    #make a list of disjoint intervals [a[i], b[i]) such that we need to
    #compute phi_k(P) for all a[i] <= k <= b[i] for each i
    intervals = []
    interval = (bd - 4, bd + 5)
    while interval[0] < interval[1]:
        intervals.append(interval)
        interval = max((interval[0] - 7) >> 1, 0), \
                   min((interval[1] + 9) >> 1, interval[0])

    #Compute first 8 division values
    idv = division_values(P, fs, 8)
    L = {}
    for i in range(8):
        L[i+1] = idv[i] #NB: here the indexing is shifted by 1
        #compared to the code of division_values!
        #(Agrees with magma's though)

    quotient = L[5] - L[4] * L[2]^3 + L[3]^3
    assert quotient != 0, "quotient vanishes at P"

    for i in reversed(intervals):
        k = i[0]
        while k < i[1]:
            if k > 8:
                m = k >> 1
                if k & 1:
                    L[k] = (L[m + 4] * L[m + 2] * L[m - 2]^2 - L[m + 4] * L[m + 1] * L[m - 1] * L[m - 2] * L[2]^2 + L[m + 4] * L[m]^2 * L[m - 2] * L[3] - L[m + 3]^2 * L[m - 1] * L[m - 3] + L[m + 3] * L[m + 1] * L[m - 1]^2 * L[3]^2 - L[m + 3] * L[m]^2 * L[m - 1] * L[4] * L[2] + L[m + 3] * L[m + 2] * L[m] * L[m - 3] * L[2]^2 - L[m + 2]^2 * L[m] * L[m - 2] * L[3]^2 + L[m + 2] * L[m]^3 * L[5] - L[m + 3] * L[m + 1]^2 * L[m - 3] * L[3] + L[m + 2] * L[m + 1]^2 * L[m - 2] * L[4] * L[2] - L[m + 1]^3 * L[m - 1] * L[5]) / quotient
                else:
                    L[k] = (L[m + 4] * L[m + 1] * L[m - 2] * L[m - 3] - L[m + 4] * L[m] * L[m - 2]^2 * L[2]^2 + L[m + 4] * L[m - 1]^2 * L[m - 2] * L[3] - L[m + 3] * L[m + 2] * L[m - 1] * L[m - 4] + L[m + 3] * L[m] * L[m - 1] * L[m - 2] * L[3]^2 - L[m + 3] * L[m - 1]^3 * L[4] * L[2] + L[m + 2]^2 * L[m] * L[m - 4] * L[2]^2 - L[m + 2] * L[m + 1] * L[m] * L[m - 3] * L[3]^2 + L[m + 2] * L[m] * L[m - 1]^2 * L[5] - L[m + 2] * L[m + 1]^2 * L[m - 4] * L[3] + L[m + 1]^3 * L[m - 3] * L[4] * L[2] - L[m + 1]^2 * L[m] * L[m - 2] * L[5]) / L[2] / quotient

            k = k + 1

    return L[bd]


def LocalHeightUchida(P, v, Iterations = 0, Precision = 0):
    r"""
    Computes the local height at v of a point P on the Jacobian
    of a genus 2 curve over the rationals given by a monic odd degree model,
    where v is a place. This uses [dJM14, Theorem 2.1].
    """

    C = P.parent().curve()
    if C.genus() != 2:
        return "The genus of the curve must be 2"
    f,h = C.hyperelliptic_polynomials()
    if h.is_zero() == False:
        return "The curve must be given by a simplified model"
    if f.degree() % 2 == 0:
        return "The curve must be given by a monic odd degree model."
    if C.base_ring() != QQ:
        return "The base field must be the rational field."

    if Iterations.is_zero():
        Iterations = 1000

    if Precision.is_zero():
        Precision = 50

    fs = f.coefficients(sparse = False)

    if v != 0:
        #work over Qp
        Qpprec = Qp(v, Precision)
        Pv = [g.change_ring(Qpprec) for g in [P[0],P[1]]]
        # Compute phi_n(Pv), n = Iterations.
        phi_v = division_value(Pv, fs, Iterations);
        return -(phi_v).valuation() * log(v) / Iterations^2, phi_v.valuation(), Iterations

    else:
        #work over R
        RF = RealField(Precision)
        Pv = [g.change_ring(RG) for g in [P[0], P[1]]]
        #compute phi_n(Pv), n = Iterations.
        phi_v = division_value(Pv, fs, Iterations)
        return log(abs(phi_v)) / Iterations^2
