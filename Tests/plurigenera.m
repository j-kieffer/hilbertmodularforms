
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


/* General Type (Elliptic points of order 2 only) */
label := "2.2.5.1-29.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert [Plurigenus(Gamma, i) : i in [1..4]] eq [0,0,0,0];

/* Rational (But with nontrival elliptic points) */

label := "2.2.5.1-1.1-1.1-gl-0";
Gamma := LMFDBCongruenceSubgroup(label);
assert [Plurigenus(Gamma, i) : i in [1..4]] eq [0,0,0,0];
