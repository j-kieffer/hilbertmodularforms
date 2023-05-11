
/* Generate suitable input for Atkin-Lehner */

F := QuadraticField(5);
ZF := Integers(F);
p29 := Decomposition(ZF!29)[1][1];
N := p29;
A := p29;
bb := 1*ZF;

prec := 10;
Gamma := Gamma0(F, N, bb);
M := GradedRingOfHMFs(F, prec);
weight := [4,4];
S := HMFSpace(M, Level(Gamma), weight);

/* This gets Hecke eigenforms with trivial character over a number field, but
only one representative per Galois orbit.  */
New := NewCuspForms(S: GaloisDescent := false);
for k := 1 to 3 do
    assert AtkinLehnerOnNewform(New[k], 1*ZF) eq New[k];
end for;
assert AtkinLehnerOnNewform(New[1], A) eq -1 * New[1];
assert AtkinLehnerOnNewform(New[2], A) eq -1 * New[2];
assert AtkinLehnerOnNewform(New[3], A) eq New[3];

/* Test on oldforms */
p3 := 3*ZF;
N_big := p3*p29;
S_big := HMFSpace(M, N_big, weight);

d := p3;
A := p3;
AtkinLehnerOnOldform(S_big, New[1], d, A);
