
intrinsic AtkinLehnerMatrix(Mk :: ModFrmHilD, dd :: RngOrdIdl : GaloisDescent:=false)
          -> Any, SeqEnum
{Constructs the Atkin-Lehner operator with respect to some basis of Eigenforms. The
second argument returned is the basis of Mk used.}
    
    // This code is dependent on Theorem~7.6.3 from Horawa's thesis.
    if CuspDimension(Mk) eq 0 then return Matrix(Integers(), 0, 0, []); end if;

    require not GaloisDescent : "Not Implemented.";
    
    // First get an eigenbasis for the space of cusp forms.
    // Note that NewCuspForms necessarily returns Eigenforms.

    /* cuspBasis, levels := CuspFormBasisWithLevels(Mk : GaloisDescent:=false, */
    /*                                                   GaloisInvariant:=false); */

    
    cuspBases, incLevels := CuspFormLevelDecompositionBasis(Mk : GaloisDescent:=false,
                                                                 GaloisInvariant:=false,
                                                                 KeepOldParents:=true);

    // Include the cuspBases elements into Mk.
    cuspBasis := _ConvertToFlattenedBasis(Mk, cuspBases, incLevels);

    // Unpack.
    N  := Level(Mk);
    wt := Weight(Mk);
    M  := Parent(Mk);

    // We will need all of the Atkin-Lehner operators.
    require dd in Divisors(N) : "Illegal level for Atkin-Lehner operator.";
    require IsSquarefree(N) : "Not implemented for nonsquarefree level.";


    // Create the matrix.
    rows := [];
    for i in [1..#cuspBases] do
        mm := incLevels[i];
        basis := cuspBases[i];
        
        for f in basis do
            // TODO: Inspect after code is plugged in.
            imf := AtkinLehnerOnOldform(Mk, f, mm, dd);

            // TODO: FIXME: May still have issues with coefficient fields.
            // print "Basis Fields: ", [* CoefficientRing(f) : f in cuspBasis *];
            // print "Fields: ", CoefficientRing(f), CoefficientRing(imf);

            // assert [] eq LinearDependence(basis);
            // print "I'm OK.";
            
            boo, combo := IsLinearCombination(imf, cuspBasis);

            // TODO: This is the actual correct error message. However, we are still developing
            //       this function.
            // msg := "Error: Atkin Lehner operator did not leave space invariant.";

            msg := "Atkin Lehner operator did not leave space invariant. " *
                   "This is probably because we don't store the entire basis if it isn't " *
                   "defined over QQ.";
            require boo : msg;

            scaled := [c/combo[1] : c in combo[2]];
            Append(~rows, scaled);
        end for;
    end for;

    ALmatrix := Matrix(rows);
    
    return ALmatrix;
end intrinsic;


intrinsic AtkinLehnerMatrices(Mk::ModFrmHilD) -> SeqEnum
{Returns the Atkin-Lehner operators for the primes dividing the level of Mk.}
    N := Level(Mk);

    facts := Factorization(N);
    
    return [AtkinLehnerMatrix(Mk, pp[1]) : pp in facts];
end intrinsic;


intrinsic AtkinLehnerDecomposition(Mk::ModFrmHilD) -> SeqEnum
{Returns the decomposition of the space of cusp forms in Mk with respect to the Atkin-Lehner
involutions. The result is returned as a list of lists of elements.}
    mats := AtkinLehnerMatrices(Mk);
    if #mats eq 0 then return [Basis(Mk)]; end if;

    print mats, "\n";

    // Decompose the abstract vector space..
    A1 := mats[1];
    spaces := [* RSpace(BaseRing(A1), Nrows(A1)) *];
    for A in mats do
        one := Eigenspace(A, 1);
        neg := Eigenspace(A, -1);

        newspaces := [* *];
        for E in spaces do
            E1  := E meet one;
            Em1 := E meet neg;
            
            if Dimension(E1) gt 0 then
                Append(~newspaces, E1);
            end if;
            
            if Dimension(Em1) gt 0 then
                Append(~newspaces, Em1);
            end if;
            
        end for;
        spaces := newspaces;
    end for;

    // Identify the basis
    cuspBasis, levels := CuspFormBasisWithLevels(Mk : GaloisDescent:=false,
                                                      GaloisInvariant:=false);
    m := #cuspBasis;
    
    // Extract the bases of forms.
    bases := [[&+[(E.j)[i] * cuspBasis[i] : i in [1..#cuspBasis]] : j in [1..Dimension(E)]]
              : E in spaces];
    return bases;
end intrinsic;


intrinsic AtkinLehnerOnNewform(f :: ModFrmHilDElt, A :: RngOrdIdl) -> ModFrmHilDElt 
{Given a cusp form for Gamma0(N) and GL2+ that is a new cusp form, compute the
action of the Atkin--Lehner operator w_A on f}
/* Cf. A. Horawa, "Motivic action on coherent cohomology of Hilbert modular
varieties", Thm. 6.25 and 6.26 */

    S := Parent(f); /* Space of Hilbert modular forms */
    Gr := Parent(S); /* Graded ring of Hilbert modular forms */
    F := BaseField(S);
    ZF := Integers(S);
    w, ww := Explode(Weight(f));

    require IsTrivial(Character(S)): "Only implemented for trivial character";
    require IsSquarefree(Level(S)): "Only implemented for squarefree level";
    require IsTrivial(NarrowClassGroup(F)): "Only implemented for trivial narrow class group";
    require IsIntegral(Level(S)/A): "A must divide the level";
    require w eq ww and w mod 2 eq 0: "f must have parallel even weight";

    /* Find totally positive generator of inverse different */
    bb := 1*ZF;
    t, u := IsNarrowlyPrincipal(Codifferent(1*ZF));
    assert t;

    /* Normalize the cusp form */
    G := CoefficientRing(f);
    nu := ReduceShintani(Gr, bb, 1*u);
    a1 := Coefficients(f)[bb][nu];
    f := 1/a1 * f;
    /* printf "Rescaling by %o\n", 1/a1; */
    coeffs := Coefficients(f)[bb];

    /* Get complex conjugation */    
    if G eq Rationals() then
        conj := map < G -> G | x :-> x >;
    else
        t, conj := HasComplexConjugate(G);
        assert t;
    end if;
    
    /* Compute lambda */
    lambda := G!1;
    pps := [fac[1]: fac in Factorization(A)];
    for pp in pps do
        t, pi := IsNarrowlyPrincipal(pp);
        assert t;
        /* Use the simpler formula for lambda_pp as cond(chi) = 1 */
        a_pp := Coefficient(f, pp);
        lambda_pp := - Norm(pp)^(1 - (w div 2)) * (a_pp @ conj);
        lambda *:= lambda_pp;
    end for;
    /* printf "lambda = %o\n", lambda; */

    /* Get new coefficient array */
    new_coeffs := coeffs;
    for nu in Keys(coeffs) do
        /* Rescale to get element of ZF */
        nu0 := ZF!(nu/u);
        /* Factor nu0 in (prime to A) . (prime to N/A) as nu0 = x * (nu0/x) */
        gcdA := Gcd(nu0*ZF, A);
        assert gcdA + (Level(S)/A) eq 1*ZF;
        t, x := IsNarrowlyPrincipal(gcdA);
        assert t;
        /* Get corresponding coefficients of f */
        nu1 := ReduceShintani(Gr, bb, x*u);
        a_nu1 := coeffs[nu1];
        nu2 := ReduceShintani(Gr, bb, (nu0/x)*u);
        a_nu2 := coeffs[nu2];
        new_coeffs[nu] := a1 * lambda * a_nu1 * (a_nu2 @ conj);
    end for;

    /* Return result as HMF */
    A := AssociativeArray();
    A[bb] := new_coeffs;

    blah := HMF(S, A);
    return blah;

end intrinsic;

/* cf. Asai, "On the Fourier coefficients of automorphic forms at various cusps", Lemma 1 */

intrinsic AtkinLehnerOnOldform(Mk :: ModFrmHilD, g :: ModFrmHilDElt, d :: RngOrdIdl,
                               A :: RngOrdIdl) -> ModFrmHilDElt
                                                      
{Given an old form f at level Gamma0(N) for GL2+ that arises as the d-level
raising of a newform g, compute the action of the Atkin--Lehner operator w_A on f}

    F := BaseField(Mk);
    ZF := Integers(F);
    N := Level(Mk);
    Mk_old := Parent(g);
    M := Level(Mk_old);
    bb := 1*ZF;

    require IsTrivial(NarrowClassGroup(F)): "Only implemented for trivial narrow class group";
    require N subset d * M: "d*M must divide the level N";
    require N subset A: "A must divide the level N";
    require IsCoprime(A, ZF !! (N/A)): "A must be a Hall divisor of N";

    /* Using Asai's unfortunate notation */
    N0 := M;
    m := d;
    m1 := ZF !! (N/(m*N0));
    M := A;
    M0 := Gcd(N0, M);
    m3 := Gcd(m, M);
    m4 := Gcd(m1, M);
    assert M eq M0 * m3 * m4;
    mu := ZF !! (m/m3);

    gp := AtkinLehnerOnNewform(g, M0);
    f := Inclusion(gp, Mk, m4*mu);
    return f;
    
end intrinsic;

