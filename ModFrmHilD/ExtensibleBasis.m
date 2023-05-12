

intrinsic ShintaniRepsForCuspExtension(M::RngOrdFracIdl, mus::SeqEnum[FldNumElt], l::RngIntElt)
          -> SeqEnum[FldNumElt]

{Given a module M as in the isotropy group G(M,V) of a cusp, and mus as output
by VerticesInCuspResolution, compute the list of Shintani representatives of
the dual of M with the following property: a weight (l,l) cusp form extends
holomorphically to the cusp if and only if the Fourier coefficients
corresponding to the Shintani representatives vanish}
    
    maxtraces := [l / Min(RealEmbeddings(mu)): mu in mus];
    maxtrace := Floor(Max(maxtraces));

    ZF := Order(M);
    Mdual := M^(-1) * Codifferent(1*ZF);
    assert Mdual subset Codifferent(1*ZF);
    
    reps := [];
    for t := 1 to maxtrace do
        reps := reps cat ShintaniRepsOfTrace(Mdual, t);
    end for;

    printf "Sieving (%o): ", #mus;
    extras := reps;
    for mu in mus do
        printf "%o, ", #extras;
        extras := [r: r in extras | Trace(r*mu) ge l];
    end for;
    printf "\n";
    reps := SetToSequence(SequenceToSet(reps) diff SequenceToSet(extras));
    return reps;
    
end intrinsic;


intrinsic ExtensibleAtInfinityCuspformBasis(M::ModFrmHilDGRng,
                                            Gamma::GrpHilbert,
                                            weight::SeqEnum
                                            :
                                            Verbose := false) -> SeqEnum
{Returns a basis for the space of cusp forms which extend over the resolution at infinity.}

    Gr := M; // Rename input to avoid conflict with G(M,V) notation.
    F  := BaseField(Gamma);
    ZF := Integers(F);
    bb := ComponentIdeal(Gamma);

    msg := "Not implemented for nonparious or odd weights.";
    require weight[1] eq weight[2] and IsEven(weight[1]) : msg;

    /* Get minimal sequence for cusp at infinity */
    M := bb^(-1);
    V := ZF!1; /* FIXME */
    mus := VerticesInCuspResolution(M, V);
    
    reps := ShintaniRepsForCuspExtension(M, mus, ExactQuotient(weight[1], 2));

    // Decide on the preicision.
    prec := Floor(Max([2] cat [Trace(r): r in reps]));
    
    // Raise precision error if not enough precision.
    require prec le Precision(Gr) : "Insufficient precision.";
    
    if Verbose then
        printf "prec = %o\n", prec;
    end if;
    
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

intrinsic ExtensibleCuspformBasis(M :: ModFrmHilDGRng, Gamma :: GrpHilbert, weight :: SeqEnum)
          -> SeqEnum[ModFrmHilDElt]
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

