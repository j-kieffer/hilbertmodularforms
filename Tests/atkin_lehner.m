
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
f := New[1];

for k := 1 to 3 do
    assert AtkinLehnerOnNewCuspEigenform(New[k], 1*ZF) eq New[k];
end for;
assert AtkinLehnerOnNewCuspEigenform(New[1], A) eq -1 * New[1];
assert AtkinLehnerOnNewCuspEigenform(New[2], A) eq -1 * New[2];
assert AtkinLehnerOnNewCuspEigenform(New[3], A) eq New[3];
