r"""
Given a genus 2 curve described by an equation of the form
`y^2 = x^5 + b_1 x^4 + b_2 x^3 + b_3 x^2 + b_4 x + b_5`,
either over `\QQ` or `\QQ_p` for some prime `p`, and with Jacobian `J`,
this code computes:

(1) local (canonical and non-canonical) p-adic Néron functions for `J`
    w.r.t. `2*Theta`;

    main functions: `canonical_sigma_function`, `height_at_p`, `height_away_p_rat`.

(2) abelian integrals (no assumption on the reduction);

    main function: `abelian_logs`.

Here are some examples, but see also function descriptions.

EXAMPLES::

(1) The example of [Bia23, 6.6]:
    sage: R.<x> = PolynomialRing(Rationals())
    sage: f = x^3*(x - 1)^2 + 1
    sage: X = HyperellipticCurve(f)
    sage: P2 = X(0, 1)
    sage: P2m = X(0,-1)
    sage: J = Jacobian(X)
    sage: v2 = J(P2m, P2)
    sage: p = 11
    sage: n = 9
    sage: sigma_can = canonical_sigma_function(f, p, n+1)
    sage: height_at_p(v2, sigma_can, m=29) #NB: if m is not provided, a suitable m is computed internally.
    If you haven't given me the canonical sigma function, you should be careful with precision.
    2*11^3 + 6*11^4 + 10*11^5 + 10*11^6 + 9*11^7 + 10*11^8 + O(11^9)

    For the same example, we compute the `p`-adic Néron function at `2`, for
    any `p` different from `2.
    In particular, the following returns `lambda_2(v2)/log_p(2)`:
    sage: height_away_p_rat(v2, 2, m = 3)  #NB: here m should be provided (as 2 is of bad reduction)
    -2/3

(2) Comparing abelian integrals with Coleman integration algorithm:
    sage: R.<x> = PolynomialRing(Rationals())
    sage: f = x^5 + x^3 + x^2 + 1
    sage: p = 5; prec = 18
    sage: X = HyperellipticCurve(f)
    sage: J = Jacobian(X)
    sage: D = J(X(0,-1), X(1,-2))
    sage: m = 40
    sage: logs = abelian_logs(D, p, prec , m)
    sage: XK = X.change_ring(Qp(p,prec + 2))
    sage: ints = XK.coleman_integrals_on_basis(XK(1,-2),XK(0,-1))
    sage: [ints[i] - logs[i] for i in range(2)]
    [O(5^18), O(5^18)]


REFERENCES:
- [BBCF+19] \J.S. Balakrishnan, F. Bianchi, V. Cantoral-Farfán, M. Çiperiani, and A. Etropolski,
  "Chabauty–Coleman experiments for genus 3 hyperelliptic curves", In Research Directions in Number Theory,
  Springer, 2019.
- [Bia23] \F. Bianchi, "p-Adic sigma functions and heights on Jacobians of
  genus 2 curves", 2023.
- [Bla18] \C. Blakestad, "On Generalizations of p-Adic Weierstrass Sigma and Zeta Functions," Ph.D. thesis,
  University of Colorado, 2018.
"""

load("./formal_group_expansions.sage")
load("./division_polynomials.sage")
import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer

############## AUXILIARY FUNCTIONS ###############

def normalise(xs):
    r"""
    Choose right normalisation method based on ground field.
    Translation to SageMath of Stoll's Magma code for
    Kummer surface.
    INPUT:
    - ``xs`` - a list of elements in a field `F` or integral domain
      with fraction field `F`.
    OUTPUT: A list of length `len(xs)` of elements in `F`.
    This is a list of zeros if xs is a list of zeros, or projectively
    equivalent to xs otherwise.

    EXAMPLES:
        sage: K = Qp(2,10)
        sage: xs = [K(1), K(2^(-1)),K(2^(-2)),K(2^(-3))]
        sage: normalise(xs)
        [2^3 + O(2^13), 2^2 + O(2^12), 2 + O(2^11), 1 + O(2^10)]
    """
    F = xs[0].parent()
    F = FractionField(F)
    assert [xs[i] in F for i in range(len(xs))], "look back at this"
    if isinstance(F,LaurentSeriesRing) or isinstance(F,sage.rings.padics.local_generic.LocalGeneric):
        #normalise such that coordinates are integral, with one being a unit,
        #and such that the first unit is 1.
        #First step: Make minimal valuation zero.
        v = min([min(x.valuation(), x.precision_absolute()) for x in xs if x!=0])
        a = F.uniformizer()^(-v)
        xs1 = [a*x for x in xs]
        #Second step: normalise first unit.
        i = 0
        while xs1[i].valuation() > 0:
            i += 1
        return [x/xs1[i] for x in xs1]
    i = 0
    while xs[i] == 0:
        i += 1
    return [x/xs[i] for x in xs]


def T1_T2(P, fs, p, n, check_formal = False):
    r"""
    Return the parameters `T_1` and `T_2` at the point P.
    INPUT:
    - ``P`` -- point on the Jacobian (either over `\QQ` or `\QQ_p`).
    - ``fs`` -- coefficients of the monic degree `5` polynomial
      defining the curve.
    - ``p`` -- a prime.
    - ``n`` -- an integer: the desired relative `p`-adic precision
      of the output.
    - ``check_formal`` -- `True/False` (default `False`): if `True`,
      checks if the image of `P` on the Kummer surface reduces to
      `(0 : 0 : 0 : 1)` modulo `p`. If it does not, it returns an
      AssertionError.
    OUTPUT: A tuple consisting of two `p`-adic numbers.

    EXAMPLES:
    This is a point in the example of [Bia23, 6.6].
    We find (by trial and error) the smallest positive `m` for which
    `m*v1` lies in the formal group at `2`. For this `m` we also compute
    `T_1(m*v1)`:
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^3*(x - 1)^2 + 1
        sage: X = HyperellipticCurve(f)
        sage: P2m = X(0,-1)
        sage: P1 = X(1,-1)
        sage: J = Jacobian(X)
        sage: v1 = J(P2m, P1)
        sage: fs = f.coefficients(sparse = False)
        sage: p = 2
        sage: n = 10
        sage: for m in range(20):
        ....:     try:
        ....:         T1mv1, T2mv1 =T1_T2(m*v1, fs, p, n, check_formal = True)
        ....:         print("smallest m is", m)
        ....:         print("T1(mv1) is", T1mv1)
        ....:         break
        ....:     except AssertionError:
        ....:         pass
        smallest m is 12
        T1(mv1) is 2 + 2^4 + 2^5 + 2^7 + 2^10 + O(2^11)
    """
    g = 2
    b5, b4, b3, b2, b1, b0 = fs
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

    kum_norm = normalise([Qp(p,n)(1),Qp(p,n)(pgis[0]),Qp(p,n)(pgis[1]),Qp(p,n)(pgis[2])])
    if check_formal == True:
        assert [kum_norm[i] % p for i in range(3)] == [0,0,0], "Not in the formal group."

    T1 = - 2*Qp(p, n)(pgis[2]/pggis[3])
    pofP = pgis[2]*pgis[0] - pgis[1]^2
    XofP = 1/2*(pofP + b2*pgis[1] - b4)
    T2 = - Qp(p,n)(XofP/(1/2*pggis[3]))
    return T1, T2

############## ABELIAN LOGS ###############

def adjusted_prec_Log(n, p):
    r"""
    Compute sufficient `T`-adic precision so
    that the formal group logarithm returns
    currect results modulo `p^n`.
    Uses [Bia23, Proposition 2.7].
    For `n <= p^p-p`, uses proof of [Proposition 3.11, BBCF+19].
    """
    if n <= p^p -p:
        M = n
        r = n
        while r % p != 0:
            r += 1
        if r - r.valuation(p) < n:
            M = r + 1
    else:
        M = n
        while M - RR(log(M)/log(p)).floor() < n:
            M += 1
        # m-ord_p(m) >= m-(log_p(m)).floor()
        # the RHS is increasing as (log_p(m+1)).floor() <= (log_p(m)).floor() + 1
        # so suffices to find the smallest M for which M-(log_p(M)).floor() >= n.
    return M


def abelian_logs(D, p, prec, m = 0, LOG = []):
    r"""
    Return `p`-adic integrals from 0 to `D` of
    holomorphic differentials `Omega_1` and `Omega_2`.
    (notation of [Bia23]) of the Jacobian `J` of a
    genus 2 curve `y^2 = f(x)`, `f` monic of degree `5`.
    `p` need not be of good reduction, nor odd.
    INPUT:
    - ``D`` -- a point in `J(\QQ_p)` or `J(\QQ)`. If in
      `J(\QQ_p)`, `LOG` should be pre-computed.
    - ``p`` -- a prime.
    - ``prec`` -- an integer: the desired precision of the output.
    - ``m`` -- an integer such that `m*D` is in the formal group at `p`.
      If m is not provided, the code computes the order of the Jacobian
      over `\F_p`, provided that `p` is of good reduction. Else it returns an
      error message.
    - ``LOG`` -- a list of two power series in two variables,
      giving the strict formal group logarithm.
      If not provided, this is computed to suitable precision.
      If you want to use the function abelian_logs for more than
      one point on the same Jacobian, it's advisable to pre-compute `LOG`.
    OUTPUT: A tuple of two `p`-adic numbers, or a string (if `m` is not provided
    and cannot be computed).

    EXAMPLES:
    An example with `p = 2` (and where we also show how to pre-compute `LOG`).
    The curve has LMFDB label 127896.a.255792.1.
    It is bielliptic over `\QQ` and, in particular the Jacobian is isogenous to
    `E1xE2` where `E1` has rank `2` and `E2` has rank `0` over `\QQ`.
    If `D` in `J(\QQ)` is non-torsion, thus expect that `int^D Omega_1/int^D Omega_2` is
    rational and independent of `p`.
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^5 - 16*x^4 - 160*x^3 + 2880*x^2 - 12288*x + 16384
        sage: p = 2
        sage: prec = 10
        sage: H = HyperellipticCurve(f)
        sage: J = Jacobian(H)
        sage: D =J(H(0,128), H(0, -128))
        sage: m = 8
        sage: des_prec = prec + m.valuation(2)
        sage: adj_prec = adjusted_prec_Log(des_prec, 2)
        sage: LOG,_,_ = strict_log(f, adj_prec)
        sage: logs_8_D = abelian_logs(D, 2, prec, m, LOG = LOG)
        sage: logs_8_D[0]/logs_8_D[1]
        2^-3 + O(2^6)
        sage: #Let's check the same quotient when p = 5
        sage: logs_40_D_5 = abelian_logs(D, 5, prec, 40, LOG = LOG)
        sage: logs_40_D_5[0]/logs_40_D_5[1] - Qp(5,prec)(1/8)
        O(5^10)
    """
    H = D.parent().curve()
    if m == 0:
        try:
            Hp = H.change_ring(GF(p))
            m = Hp.frobenius_polynomial()(1)
        except ValueError:
            return "Cannot compute a suitable m for you, as p is not of good reduction"
    mD = m*D
    f = H.hyperelliptic_polynomials()[0]
    fs = f.coefficients(sparse = False)
    val_m = m.valuation(p)
    des_prec = prec + m.valuation(p)
    adj_prec = adjusted_prec_Log(des_prec, p)
    T1_mD, T2_mD = T1_T2(mD, fs, p, des_prec)
    #prec + n- ord(n) >= prec iff n - ord(n) >= 0. Always.
    assert T1_mD.valuation() > 0, "Not in the formal group"
    assert T2_mD.valuation() > 0, "Not in the formal group"
    if LOG == []:
        LOG,_,_ = strict_log(f, adj_prec)
    else:
        assert adj_prec <= min(LOG[0].precision_absolute(), LOG[1].precision_absolute()) , "Input power series precision is too low."

    LOG1D = (LOG[0].truncate(adj_prec)(T1_mD, T2_mD).constant_coefficient())/m + O(p^prec)
    LOG2D = (LOG[1].truncate(adj_prec)(T1_mD, T2_mD).constant_coefficient())/m + O(p^prec)
    return LOG1D, LOG2D


############## LOCAL NÉRON FUNCTIONS ###############

def canonical_constants_good_reduction(f, p, n, check_assumptions = True):
    r"""
    Return constants corresponding to the
    canonical sigma function of [Bla18].
    See [Bia23, 6.2].
    INPUT:
    - ``f`` -- a monic polynomial of degree `5` either over
      `\QQ` or over `\QQ_p` with no repeated roots.
    - ``p`` -- a prime `>= 5` of good ordinary reduction
      for `y^2 = f(x)`
    - ``n`` -- an integer: the desired `p`-adic precision of the
      output.
    - ``check_assumptions`` -- `True/False` (default `True`): if
      `True`, checks that p is `>= 5` and of good ordinary reduction.
    OUTPUT: A tuple consisting of three `p`-adic numbers:
    The constants `c_{11}, c_{12}, c_{22}` corresponding to
    the canonical sigma function.

    EXAMPLES:
    The example of [Bia23, 6.6]:
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^3*(x - 1)^2 + 1
        sage: p = 11
        sage: n = 10
        sage: canonical_constants_good_reduction(f, p, n, check_assumptions = True)
        (6 + 6*11 + 3*11^2 + 6*11^4 + 2*11^5 + 10*11^6 + 11^7 + 6*11^8 + 9*11^9 + O(11^10), 3 + 10*11 + 10*11^2 + 11^4 + 11^5 + 5*11^6 + 11^7 + 3*11^8 + 4*11^9 + O(11^10),
        4 + 3*11 + 6*11^2 + 6*11^3 + 9*11^4 + 10*11^5 + 4*11^6 + 5*11^7 + 2*11^8 + 2*11^9 + O(11^10))
    """
    H = HyperellipticCurve(f)
    if check_assumptions == True:
        #Check p is at least 5
        assert p>=5, "p must be at least 5."
        #Check good reduction
        fp = f.change_ring(GF(p))
        assert fp.discriminant() %p !=0, "Bad reduction."
        #Check ordinary reduction
        fpow = fp^(ZZ((p-1)/2))
        assert Matrix([[fpow[p-1], fpow[2*p-1]],[fpow[p-2], fpow[2*p-2]]]).determinant() %p !=0, "Not ordinary."
    HK = H.change_ring(Qp(p,n))
    M_frob, _ = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HK)
    M_to_n = M_frob^(n)
    B1 = M_to_n.column(2)
    B2 = M_to_n.column(3)
    if Zp(p,n)(B2[3]) % p != 0:
        Bn1 = 3*B2/B2[3]
        Bn2 = (B1-Bn1*B1[3]/3)
    else:
        Bn1 = 3*B1/B1[3]
        Bn2 = (B2-Bn1*B2[3]/3)
        assert Zp(p,n)(B1[3]) % p !=0, "Not what I predicted (0). Is your prime good ordinary?"
    new_bas_2 = Bn2/Bn2[2]
    assert Zp(p,n)(Bn2[2]) %p !=0, "Not what I predicted (1). Is your prime good ordinary?"
    new_bas_1 = Bn1 + (2*f[4] - Bn1[2])*new_bas_2

    c11 = -new_bas_1[0]
    c12 = - new_bas_1[1] + f[3]
    c21 = -new_bas_2[0]
    c22 = -new_bas_2[1]

    assert c12 == c21, "Not isotropic? There must be an error."
    return c11, c12, c22


def canonical_sigma_function(f, p, n, check_assumptions = True):
    r"""
    Return the canonical sigma function of [Bla18].
    INPUT:
    - ``f`` -- a monic polynomial of degree `5` either over
      `\QQ` or over `\QQ_p` with no repeated roots.
    - ``p`` -- a prime `>= 5` of good ordinary reduction
      for `y^2 = f(x)`
    - ``n`` -- an integer: the desired `p`-adic precision of the
      output.
    - ``check_assumptions`` -- `True/False` (default `True`): if
      True, checks that p is `>= 5` and of good ordinary reduction.
    OUTPUT: A power series in `\QQp[[T_1,T_2]]` giving the expansion up
    to `O(T_1,T_2)^n` of the canonical sigma function.
    """
    c11, c12, c22 = canonical_constants_good_reduction(f, p, n, check_assumptions)
    return sigma_function(f, n, cij  = [c11, c12, c22])


def height_at_p(D, sigma, m = 0, p_branch = 0, mD = None):
    r"""
    Return the `p`-adic local Néron function at `p` of the point `D` of
    the Jacobian.
    INPUT:
    - ``D`` -- point on the Jacobian (either over `\QQ` or `\QQ_p`).
      For large `m`,`\QQ_p` is advisable.
    - ``sigma`` -- the sigma function for the height (given as
      a power series with coefficients in `\QQ_p`, for some prime `p`).
    - ``m`` -- an integer such that `m*D` lies in the formal group at `p`
      and sigma converges at `T_1(mD), T_2(mD)`.
      If `m` is not provided, the code computes the order of the Jacobian
      over `\F_p`, provided that `p` is of good reduction. Else it returns an
      error message.
    - ``p_branch`` -- an element of `\QQ_p` (default 0).
      The p-adic logarithm is computed with respect to the branch which
      sends `p` to `p_branch`.
    - ``mD`` -- either None or a point on the Jacobian. This should equal
      `m*D`.
    OUTPUT: A `p`-adic number, or a string (if `m` is not provided and cannot be
    computed). The precision depends on the precision of `sigma` and `D`.

    EXAMPLES:
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^5 -1
        sage: n = 20
        sage: sigma_can = sigma_function(f, n + 1)
        sage: p = 10^6 + 81
        sage: K = Qp(p,n+1)
        sage: HK = HyperellipticCurve(f.change_ring(K))
        sage: JK = Jacobian(HK)
        sage: R.<x> = PolynomialRing(K)
        sage: %time height_at_p(JK(x^2 + 2*x + 2, x - 1), sigma_can.change_ring(Qp(p,n+1)))
        verbose 0 (3848: multi_polynomial_ideal.py, groebner_basis) Warning: falling back to very slow toy implementation.
        verbose 0 (1081: multi_polynomial_ideal.py, dimension) Warning: falling back to very slow toy implementation.
        You are performing multiplication in J(Qp). Consider instead doing this on the Kummer (in Magma) and feed one of the preimages on J as mD.
        If you haven't given me the canonical sigma function, you should be careful with precision.
        790065*1000081 + 875980*1000081^2 + 899921*1000081^3 + 943161*1000081^4 + 701712*1000081^5 + 507099*1000081^6 + 399164*1000081^7 + 725683*1000081^8 + 423209*1000081^9         + 174881*1000081^10 + 96387*1000081^11 + 973189*1000081^12 + 88349*1000081^13 + 970515*1000081^14 + 117600*1000081^15 + 519019*1000081^16 + 639751*1000081^17 +
        971144*1000081^18 + 996211*1000081^19 + O(1000081^20)

        CPU time: 0.79 s, Wall time: 1.03 s

    """
    p = sigma.base_ring().prime()
    H = D.parent().curve()
    if m == 0:
        try:
            Hp = H.change_ring(GF(p))
            m = Hp.frobenius_polynomial()(1)
        except ValueError:
            return "Cannot compute a suitable m for you, as p is not of good reduction"
    if mD == None:
        if isinstance(H.base_ring(),sage.rings.padics.local_generic.LocalGeneric):
            print("You are performing multiplication in J(Qp).",
            "Consider instead doing this on the Kummer (in Magma)",
            "and feed one of the preimages on J as mD.")
        mD = m*D

    prec_1 = sigma.prec()
    print("If you haven't given me the canonical sigma function, you should be careful with precision.")
    fs = H.hyperelliptic_polynomials()[0].coefficients(sparse = False)
    for i in range(len(fs)):
        fs[i] = Rationals()(fs[i])
    T1_mD, T2_mD = T1_T2(mD, fs, p, prec_1, check_formal = True)
    assert T1_mD % p == 0 and T2_mD % p == 0, "mD is not in the formal group."
    prec_rel = prec_1 - T1_mD.valuation()

    phi_m_D = division_value_new(D, fs, m)
    try:
        lambda_p_D =  -2/m^2*log((sigma.truncate()(T1_mD,T2_mD)).change_ring(Qp(p,prec_rel))/phi_m_D)
    except ValueError:
        print("Needed branch of log, which you have chosen to be:", p_branch)
        lambda_p_D = -2/m^2*((sigma.truncate()(T1_mD,T2_mD)).change_ring(Qp(p,prec_rel))/phi_m_D).constant_coefficient().log(p_branch = p_branch)

    return lambda_p_D


def height_away_p_rat(D, q, m = 0, mD = None):
    r"""
    Return the `p`-adic local Néron function at `q` of the point `D` of
    the Jacobian, divided by `log_p(q)`. The prime `q` should be different
    from `p`. Note: the output is independent of `p`. Could also be used
    for real heights.
    INPUT:
    - ``D`` -- point on the Jacobian (either over `\QQ` or `\QQ_q`).
    - ``q`` -- a prime.
    - ``m`` -- an integer such that `m*D` lies in the formal group at `q`.
      If `m` is not provided, the code computes the order of the Jacobian
      over `\F_q`, provided that `q` is of good reduction. Else it returns an
      error message.
    OUTPUT: A rational number, or a string (if `m` is not provided and cannot be
    computed).
    """
    H = D.parent().curve()
    if m == 0:
        try:
            Hq = H.change_ring(GF(q))
            m = Hq.frobenius_polynomial()(1)
        except ValueError:
            return "Cannot compute a suitable m for you, as q is not of good reduction"
    if mD == None:
        if isinstance(H.base_ring(),sage.rings.padics.local_generic.LocalGeneric):
            print("You are performing multiplication in J(Qq).",
            "Consider instead doing this on the Kummer (in Magma)",
            "and feed one of the preimages on J as mD.")
        mD = m*D
    fs = H.hyperelliptic_polynomials()[0].coefficients(sparse = False)
    for i in range(len(fs)):
        fs[i] = Rationals()(fs[i])
    T1_mD, T2_mD = T1_T2(mD, fs, q, 10, check_formal = True)
    assert T1_mD % q == 0 and T2_mD % q == 0, "mD is not in the formal group."
    phi_m_D = division_value_new(D, fs, m)

    return 2/m^2*(T1_mD/phi_m_D).valuation(q)
