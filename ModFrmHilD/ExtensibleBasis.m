

intrinsic ExtensibleAtInfinityCuspformBasis(M::ModFrmHilDGRng,
                                            Gamma::GrpHilbert,
                                            weight::SeqEnum
                                            :
                                            Verbose := false) -> SeqEnum
{Returns a basis for the space of cusp forms which extend over the resolution at infinity.}

    F := BaseField(Gamma);
    ZF := Integers(F);
    bb := ComponentIdeal(Gamma);

    /* Get minimal sequence for cusp at infinity */
    M := bb^(-1);
    V := ZF!1; /* FIXME */
    mus := VerticesInCuspResolution(M, V);
    
    reps := ShintaniRepsForCuspExtension(M, mus, ExactQuotient(weight[1], 2));
    prec := Floor(Max([2] cat [Trace(r): r in reps]));

    if Verbose then
        printf "prec = %o\n", prec;
    end if;
    
    Gr := GradedRingOfHMFs(F, prec);
    B := HMFCertifiedCuspBasis(Gr, Gamma, weight);

    if Verbose then
        printf "Basis of cusp forms computed.\n";
    end if;
    
    /* Construct a matrix */
    // TODO: Perhaps this can be refactored with CoefficientsMatrix?
    ncols := #reps;
    nrows := #B;
    mat := ZeroMatrix(F, nrows, ncols);
    for k := 1 to #B do
        f := B[k];
        for j := 1 to #reps do
            mat[k,j] := Coefficients(f)[ComponentIdeal(Gamma)][reps[j]];
        end for;
    end for;

    
    if Verbose then
        printf "Rows, columns, rank: %o, %o, %o\n", nrows, ncols, Rank(mat);
    end if;

    result := [];
    nullBasis := Basis(Nullspace(mat));
    for i in [1..#nullBasis] do
        v := nullBasis[i];

        f := Zero(Parent(B[1]));
        for j in [1..#B] do
            f +:= B[j] * v[j];
        end for;

        Append(~result, f);
    end for;

    return result;
end intrinsic;

intrinsic ExtensibleCuspformBasis(M :: ModFrmHilDGRng, Gamma :: GrpHilbert,
                            weight :: SeqEnum) -> Any
{Returns a basis for the space of cusp forms that extend over all cusps.}

    require IsSquarefree(Level(Gamma)) : "Only implemented for squarefree level.";
    
    // Forms which extend over infinity. (For precision reasons, this step must be first.)
    
    extensibleAtInfBasis := ExtensibleAtInfinityCuspformBasis(M, Gamma, weight);

    // Extract parents.
    if #extensibleAtInfBasis eq 0 then return extensibleAtInfBasis; end if;
    Mk := Parent(extensibleAtInfBasis[1]);
    
    // Compute the Atkin-Lehner decomposition.
    ALdecomp := AtkinLehnerDecomposition(Mk);

    // Compute the intersections.
    result := [];
    for E in ALdecomp do
        result cat:= Intersection(E, extensibleAtInfBasis);
    end for;
    
    return result;
end intrinsic;

