load("./heights_and_abelian_integrals.sage")
t1 = cputime()
R.<x> = PolynomialRing(Rationals())
f = x^5 - 1
[b5, b4, b3, b2, b1, b0] = f.coefficients(sparse = False)
n = 20
t_sigma_0 = cputime()
sigma_can = sigma_function(f, n + 1)
print("time", cputime()-t_sigma_0)
H = HyperellipticCurve(f)
J = Jacobian(H)
p = 10^6 + 81
HQp = H.change_ring(Qp(p,n+1))
JQp = Jacobian(HQp)
_.<x> = PolynomialRing(Qp(p,n+1))
print("lambda_p(P):", height_at_p(JQp(x^2 + 2*x + 2, x - 1), sigma_can.change_ring(Qp(p,n+1))))
t2 = cputime()
print("Time lambda_p:", t2-t1)

#Néron function at 2
q = 2
HQq = H.change_ring(Qp(q,10))
JQq = Jacobian(HQq)
_.<x> = PolynomialRing(Qp(q,10))
print("lambda_2(P)/log_p(2):", height_away_p_rat(JQq(x^2 + 2*x + 2, x-1), q, m = 2))

#Néron function at 5
q = 5
HQq = H.change_ring(Qq(q,10))
JQq = Jacobian(HQq)
_.<x> = PolynomialRing(Qp(q,10))
print("lambda_5(P)/log_p(5):", height_away_p_rat(JQq(x^2 + 2*x + 2, x-1), q, m = 50))
t3 = cputime()
print("Time lambda_2 and lambda_5:", t3-t2)
