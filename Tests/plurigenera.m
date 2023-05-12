
/* Rational surfaces */


label := "2.2.13.1-1.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
UpperBoundsOnPlurigenera(Gamma, 4);

label := "2.2.33.1-1.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
UpperBoundsOnPlurigenera(Gamma, 3);

/* General type */

label := "2.2.24.1-1.1-2.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
UpperBoundsOnPlurigenera(Gamma, 3);


label := "2.2.28.1-4.1-3.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
UpperBoundsOnPlurigenera(Gamma, 2);


/* Undecided */

label := "2.2.5.1-4.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
UpperBoundsOnPlurigenera(Gamma, 4);

/* Too slow! */
/* label := "2.2.24.1-3.1-1.1-gl-0"; */
/* Gamma := LMFDBCongruenceSubgroup(label); */
/* UpperBoundsOnPlurigenera(Gamma, 2); */

/* Lower bounds */

label := "2.2.105.1-4.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
LowerBoundsOnPlurigenera(Gamma, 2); /* Returns negative. */


////////////////////
/* Exact numbers */

label := "2.2.13.1-1.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert UpperBoundsOnPlurigenera(Gamma, 2)[2] ge Plurigenus(Gamma, 2 : ignoreElliptic);



////////////////////
/* Exact numbers */


/* General Type (Elliptic points of order 2 only) */
label := "2.2.5.1-29.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert Plurigenus(Gamma, 2 : Precision := 15) gt 0;

// Takes too long.
/* label := "2.2.8.1-71.1-1.1-gl-0"; */
/* Gamma := LMFDBCongruenceSubgroup(label); */
/* assert Plurigenus(Gamma, 2) gt 0; */



/* Rational (But with nontrival elliptic points) */

// This test fails for some reason. (Elliptic points?)
label := "2.2.8.1-7.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert [Plurigenus(Gamma, i : ignoreElliptic) : i in [1..2]] eq [0,0];


label := "2.2.13.1-3.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert [Plurigenus(Gamma, i : ignoreElliptic) : i in [1..2]] eq [0,0];


label := "2.2.5.1-1.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert [Plurigenus(Gamma, i : ignoreElliptic) : i in [1..4]] eq [0,0,0,0];


/* Probably Rational (No elliptic points) */
label := "2.2.5.1-59.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert [Plurigenus(Gamma, i : Precision:=10) : i in [1..2]] eq [0,0];

// Actually, this is perhaps not rational. Assertion fails.
/* label := "2.2.8.1-14.1-1.1-gl-0"; */
/* Gamma := LMFDBCongruenceSubgroup(label); */
/* assert [Plurigenus(Gamma, i : Precision:=10) : i in [1..2]] eq [0,0]; */

