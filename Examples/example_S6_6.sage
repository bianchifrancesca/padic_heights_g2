load("./heights_and_abelian_integrals.sage")
R.<x> = PolynomialRing(Rationals())
f = x^3*(x-1)^2 + 1
p = 11
n = 9
#canonical_constants_good_reduction(f, p, n+1, check_assumptions = True)
sigma_can = canonical_sigma_function(f, p, n+1)
H = HyperellipticCurve(f)
J = Jacobian(H)
P1 = H(1,-1)
P2 = H(0,1)
P1m = H(1,1)
P2m = H(0,-1)
v1 = J(P2m, P1)
v2 = J(P2m, P2)
v3 = J(P1m, P1)
lambdapv1 = height_at_p(v1, sigma_can, m = 116)
lambdapv2 = height_at_p(v2, sigma_can, m = 29)
lambdapv3 = height_at_p(v3, sigma_can, m = 58)
print("lambda_p(v1):", lambdapv1)
print("lambda_p(v2):", lambdapv2)
print("lambda_p(v3):", lambdapv3)
print("<D1,D2>_{p,p}^N:", -1/2*(2*lambdapv1 - lambdapv2 - lambdapv3))
lambda2v1_prime = height_away_p_rat(v1, 2, m = 12)
lambda2v2_prime = height_away_p_rat(v2, 2, m = 3)
lambda2v3_prime = height_away_p_rat(v3, 2, m = 2)
print("lambda_2(v1)/log_p(2):", lambda2v1_prime)
print("lambda_2(v2)/log_p(2):", lambda2v2_prime)
print("lambda_2(v3)/log_p(2):", lambda2v3_prime)
print("<D1,D2>_{p,2}^N/log(2):", -1/2*(2*lambda2v1_prime - lambda2v2_prime - lambda2v3_prime))
hpv2 = lambdapv2 + lambda2v2_prime*log(Qp(p,n+1)(2))
print("hp([D1]):", hpv2/16)
