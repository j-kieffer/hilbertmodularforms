
/* Check that the certified basis has the right dimension */

F := QuadraticField(5);
ZF := Integers(F);
bb := 1*ZF;
N := 1*ZF;
Gamma := Gamma0("GL+", F, N, bb);
prec := 1;
M := GradedRingOfHMFs(F, prec);
weight := [6,6];
B := HMFCertifiedBasis(M, Gamma, weight, prec);

assert #B eq 2;

F := QuadraticField(26);
ZF := Integers(F);
bb := 1*ZF;
N := 1*ZF;
Gamma := Gamma0("GL+", F, N, bb);
prec := 2;
M := GradedRingOfHMFs(F, prec);
weight := [2,2];
B := HMFCertifiedBasis(M, Gamma, weight, prec);

/* This is wrong. */
/* assert #B eq 8; */
