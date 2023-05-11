
import "CongruenceSubgroup.m": GAMMA_0_Type;

intrinsic EllipticPointResolution(order::RngIntElt, rot_factor::RngIntElt) ->
	      SeqEnum[RngIntElt], SeqEnum[FldRatElt], SeqEnum[FldRatElt]
                                                         
{Given the order and rotation factor of an elliptic point, returns lists c, x,
y where c contains the self-intersection numbers of curves in elliptic point
resolution}

  frac := order/rot_factor;
  c := [Ceiling(frac)];
  x := [1, frac^(-1)];
  y := [0, order^(-1)];
  Append(~x, c[1]*x[2] - x[1]);
  Append(~y, c[1]*y[2] - y[1]);
  d := c[#c] - frac;
  while (d ne 0) do
      Append(~c, Ceiling(d^(-1)));
      Append(~x, c[#c]*x[#c+1] - x[#c]);
      Append(~y, c[#c]*y[#c+1] - y[#c]);
      d := c[#c] - d^(-1);
  end while;
  return c, x, y;
end intrinsic;

intrinsic EllipticPointResolution(type :: GrpHilbRotationLabel)
          -> SeqEnum[RngIntElt], SeqEnum[FldRatElt], SeqEnum[FldRatElt]
{}
    tup := StandardizeRotationTuple(Tuple(type));
    n, _, q := Explode([Integers()!x: x in tup]);
    return EllipticPointResolution(n, q);
    
end intrinsic;



intrinsic EllipticPointK2E(order::RngIntElt, rot_factor::RngIntElt) -> FldRatElt, RngIntElt
{Given the order and rotation factor of an elliptic point, returns the local Chern cycle.}
  c,x,y := EllipticPointResolution(order, rot_factor);
  a := [x[i]+y[i]-1 : i in [2..#c+1]];
  sq := -(&+[a[i]^2*c[i] : i in [1..#c]]);
  k2 := sq + 2*&+[Rationals() | a[i]*a[i+1] : i in [1..#c-1]];

  return k2, #c;
end intrinsic;

intrinsic EulerNumber(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the EulerNumber of the resulting Hilbert modular surface.}
  if assigned Gamma`EulerNumber then return Gamma`EulerNumber; end if;

  // for these fields there are additional orders of points
  // At the moment we do not handle them.
  F := BaseField(Gamma);
  ZF := Integers(F);
  D := Discriminant(ZF);

  // require D notin [8,12]: "Discriminant not supported";
  // require (Level(Gamma) eq 1*ZF) or (GCD(Level(Gamma), 3*D*ZF) eq 1*ZF):
  //"Level is not supported";

  cusps := CuspsWithResolution(Gamma);
  vol := VolumeOfFundamentalDomain(Gamma);

  // get cusp contribution
  l := 0;
  for cusp in cusps do
    _, _, L, n := Explode(cusp);
    l +:= #L * n;
  end for;

  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);

  elliptic := 0;
  for rot_factor in Keys(a) do
    rot_tup := IntegerTuple(rot_factor);
    n := rot_tup[1];

    _, len := EllipticPointK2E(n, rot_tup[3]);
    // This is ad-hoc check for surfaces
    if rot_tup[3] eq 1 then
      // len := 1;
      assert len eq 1;
    elif rot_tup[3] eq n-1 then
      // len := n-1;
      assert len eq n-1;
    elif n eq 5 then
      assert rot_tup[3] in [2,3];
      // len := 2;
      assert len eq 2;
    elif n eq 12 then
      if rot_tup[3] eq 5 then
        // len := 3;
        assert len eq 3;
      end if;
    end if;
    elliptic +:= a[rot_tup] * (len + (n-1)/n);
  end for;

  // elliptic := a2 * (1 + 1/2) + a3_plus * (1 + 2/3) + a3_minus * (2 + 2/3);
  e := vol + l + elliptic;
  assert IsIntegral(e);
  Gamma`EulerNumber := Integers()!e;

  return Gamma`EulerNumber;
end intrinsic;

intrinsic K2(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the K2 of the resulting Hilbert modular surface.}
  if not assigned Gamma`K2 then
  // for these fields there are additional orders of points
  // At the moment we do not handle them.
  F := BaseField(Gamma);
  ZF := Integers(F);
  D := Discriminant(ZF);

  cusps := CuspsWithResolution(Gamma);
  vol := VolumeOfFundamentalDomain(Gamma);
  // get cusp contribution
  cusp_chern := 0;
  for cusp in cusps do
    _, _, L, n := Explode(cusp);
      if (n eq 1) and (#L eq 1) then
          cusp_chern +:= L[1];
      else
          cusp_chern +:= n*(&+[2+b : b in L]);
      end if;
  end for;

  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);

  elliptic := 0;
  for rot_factor in Keys(a) do
    rot_tup := IntegerTuple(rot_factor);
    n := rot_tup[1];
    k2_pt, _ := EllipticPointK2E(n, rot_tup[3]);

    // verification
    if n eq 5 then
      if rot_tup[3] in [2,3] then
        assert k2_pt eq -2/5;
      elif rot_tup[3] eq 4 then
        assert k2_pt eq 0;
      end if;
    elif n eq 3 then
      if rot_tup[3] eq 1 then
        assert k2_pt eq -1/3;
      else
        assert k2_pt eq 0;
      end if;
    elif n eq 2 then
      assert k2_pt eq 0;
    end if;
    elliptic +:= k2_pt * a[rot_factor];
  end for;

  k2 := 2*vol + cusp_chern + elliptic;
  assert IsIntegral(k2);
  Gamma`K2 := Integers()!k2;
  end if;
  return Gamma`K2;
end intrinsic;

intrinsic ChernNumbersOfMinimalResolution(Gamma::GrpHilbert) -> SeqEnum
{Returns `c1^2, c2`,  corresponding to the Chern numbers of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return ChernNumbers(Gamma);
end intrinsic;

intrinsic ChernNumbers(Gamma::GrpHilbert) -> SeqEnum
{Returns `c1^2, c2`,  corresponding to the Chern numbers of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return K2(Gamma), EulerNumber(Gamma);
end intrinsic;

intrinsic ArithmeticGenus(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the Arithmetic Genus of the resulting Hilbert modular 
surface.}
  chi := K2(Gamma) + EulerNumber(Gamma);
  assert chi mod 12 eq 0;
  return chi div 12;
end intrinsic;

intrinsic Irregularity(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the irregularity of the resulting Hilbert modular surface.
 It is always 0.}
  return 0;
end intrinsic;

intrinsic GeometricGenus(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the Geometric Genus of the resulting Hilbert modular 
surface.}
  return ArithmeticGenus(Gamma)-1;
end intrinsic;

intrinsic HodgeDiamond(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the Hodge Diamond of the resulting Hilbert modular 
surface.}
  h_0 := [1];
  q := Irregularity(Gamma);
  h_1 := [q,q];
  p_g := GeometricGenus(Gamma);
  chi := ArithmeticGenus(Gamma);
  e := EulerNumber(Gamma);
  h_2 := [p_g, e - 2*chi, p_g];
  h_3 := h_1;
  h_4 := h_0;
  return [h_0, h_1, h_2, h_3, h_4];
end intrinsic;

// TODO: Add in some overloading.
intrinsic HMFCertifiedCuspBasis(M :: ModFrmHilDGRng, Gamma :: GrpHilbert,
                            weight :: SeqEnum)
          -> SeqEnum
                 
{Compute a basis of the space of modular forms for Gamma. The q-expansion
precision is at least prec, and high enough to ensure that the basis has the
right number of elements.}

    require AmbientType(Gamma) eq GLPlus_Type: "Only Gamma0 and GL2+ is supported";
    require GammaType(Gamma) eq GAMMA_0_Type: "Only Gamma0 and GL2+ is supported";
    require weight[1] eq weight[2] and weight[1] mod 2 eq 0: "Only parallel even weight is supported";

    /* Get the dimension of space of cusp forms on all components */
    F := BaseField(Gamma);
    S := HMFSpace(M, Level(Gamma), weight);
    dim := CuspDimension(S);
    prec := M`Precision;
    done := false;
    //printf "Target dimension: %o\n", dim;
    while not done do
        //printf "HMFSpaceCertified: trying prec %o\n", prec;
        M := GradedRingOfHMFs(F, prec);
        S := HMFSpace(M, Level(Gamma), weight);
        try
            B := CuspFormBasis(S);
            done := true;
        catch e
            continue;
        end try;
        prec := prec + 1;
        //printf "Computed dimension: %o\n", #B;
    end while;

    res := [];
    bb := ComponentIdeal(Gamma);
    if not bb in M`NarrowClassGroupReps then
        error "Component ideal not found";
    end if;
    shintani := ShintaniReps(M)[bb];
    V := VectorSpace(F, #shintani);
    coef_list := [];
    span := sub<V | coef_list>;
    for f in B do
        vector := [Coefficients(f)[bb][r]: r in shintani];
        if not V!vector in span then
            Append(~res, f);
            Append(~coef_list, vector);
            span := sub<V|coef_list>;
        end if;
    end for;

    return res;
end intrinsic;

//TODO: [JK] I think the module V is actually important here
intrinsic VerticesInCuspResolution(M::RngOrdFracIdl, V::RngOrdElt) -> SeqEnum[FldNumElt]
{Given a module M as in the isotropy group G(M,V) of a cusp, compute the
lattice points appearing as vertices of the resolution polyhedron}

    ZF := Order(M);
    F := NumberField(ZF);
    assert ZF eq Integers(F);

    periodic := CuspResolutionMinimalSequence(M);
    w0 := HJReconstructPeriodic(F, periodic);
    ws := [1, w0];
    rotate := periodic;
    rep := CuspResolutionRepetition(V, periodic);
    
    for k := 1 to rep*(#periodic) do
        rotate := rotate cat [rotate[1]];
        rotate := [rotate[j]: j in [2..(#periodic+1)]];
        w := HJReconstructPeriodic(F, rotate);
        Append(~ws, ws[#ws] * w);
    end for;
    
    sM := 1*ZF + w0*ZF;
    b, s := IsNarrowlyPrincipal(sM * M^(-1));
    assert b;
    
    mus := [w/s: w in ws];
    return mus;
    
end intrinsic;

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

intrinsic Plurigenus(Gamma::GrpHilbert, n::RngIntElt : Precision:=5) -> RngIntElt
{Given a congruence subgroup of type Gamma0(N) and GL2+, compute the n-th plurigenus of
the associated Hilbert Modular Surface, i.e., compute H^0(X_Gamma, K^n), where K is the
canonical bundle.}

    require n ge 0 : "Plurigenera only defined for nonegative n.";
    if n eq 0 then return 1; end if;
    
    M := GradedRingOfHMFs(BaseField(Gamma), Precision);
    weight := [2*n, 2*n];
    
    // The basis of cusp forms 
    B := ExtensibleCuspformBasis(M, Gamma, weight);
    return #B;
end intrinsic;


intrinsic LowerBoundsOnPlurigenera(Gamma::GrpHilbert, nb::RngIntElt) -> SeqEnum[RngIntElt]

{Given a congruence subgroup of type Gamma0(N) and GL2+, compute lower bounds
for the plurigenera of the associated Hilbert modular surface, i.e.  dim
H^0(K^n) for n = 1, ..., nb, where K is the canonical bundle.}
        
    require AmbientType(Gamma) eq GLPlus_Type: "Only Gamma0 and GL2+ is supported";
    require GammaType(Gamma) eq GAMMA_0_Type: "Only Gamma0 and GL2+ is supported";
    
    F := BaseField(Gamma);
    ZF := Integers(F);
    cusps := Cusps(Gamma: WithResolution:=true); /* Get tuples (ideal, projective pt, res) */
    bb := ComponentIdeal(Gamma);
    N := Level(Gamma);

    /* For now, assume there are only elliptic points of order 2 */
    data := EllipticPointData(Gamma);
    for type in Keys(data) do
        c, _, _ := EllipticPointResolution(type);
        if not &and[x eq 2: x in c] then
            error "All elliptic points must have only -2 curves in their resolutions";
        end if;
    end for;

    printf "Computing cuspidal dimensions...\n";
    prec := 1;
    Gr := GradedRingOfHMFs(F, prec);
    bounds := [0: l in [1..nb]];
    for l:=1 to nb do
        S := HMFSpace(Gr, Level(Gamma), [l,l]);
        bounds[l] := CuspDimension(S);
    end for;
    
    for c in cusps do
        alpha, beta := Explode(Eltseq(c[2]));
        alpha, beta := NormalizeCusp(2*(bb/2), N, F!alpha, F!beta); /* -> type(bb) is FracIdl */
        M, V,  _ := CuspResolutionMV(bb, N, alpha, beta: GammaType := "Gamma0",
                                                         GroupType := "GL2+");
        /* We want M^(-1) to be integral */
        Minv := M^(-1);
        Ncl, Nclmap := NarrowClassGroup(F);
        Minv := (Minv @@ Nclmap) @ Nclmap;
        M := Minv^(-1);

        printf "Computing Shintani reps at cusp (%o, %o)\n", alpha, beta;
        mus := VerticesInCuspResolution(M, V);
        for l := 1 to nb do
            printf "Get traces for l = %o\n", l;
            reps := ShintaniRepsForCuspExtension(M, mus, l);
            bounds[l] :=  bounds[l] - #reps;
        end for;
    end for;

    return bounds;
    
end intrinsic;

intrinsic UpperBoundsOnPlurigenera(Gamma::GrpHilbert, nb::RngIntElt) -> SeqEnum[RngIntElt]
                                                                               
{Given a congruence subgroup of type Gamma0(N) and GL2+, compute upper bounds
for the plurigenera of the associated Hilbert modular surface, i.e. dim 
H^0(K^n) for n = 1, ..., nb, where K is the canonical bundle.} 
    
    require AmbientType(Gamma) eq GLPlus_Type: "Only Gamma0 and GL2+ is supported";
    require GammaType(Gamma) eq GAMMA_0_Type: "Only Gamma0 and GL2+ is supported";
    
    F := BaseField(Gamma);
    ZF := Integers(F);
    bb := ComponentIdeal(Gamma);
    printf "\nComputing %o plurigenera for %o", nb, Gamma;

    /* Get minimal sequence for cusp at infinity */
    M := bb^(-1);
    V := ZF!1; /* FIXME */
    mus := VerticesInCuspResolution(M, V);
    
    bounds := [0: l in [1..nb]];
    for l := 1 to nb do
        printf "\nComputing upper bound on plurigenus for l = %o...\n", l;
        reps := ShintaniRepsForCuspExtension(M, mus, l);
        prec := Floor(Max([2] cat [Trace(r): r in reps]));
        printf "prec = %o\n", prec;
        Gr := GradedRingOfHMFs(F, prec);
        B := HMFCertifiedCuspBasis(Gr, Gamma, [2*l,2*l]);
        printf "Basis of cusp forms computed.\n";
        
        /* Construct a matrix */
        ncols := #reps;
        nrows := #B;
        mat := ZeroMatrix(F, nrows, ncols);
        for k := 1 to #B do
            f := B[k];
            for j := 1 to #reps do
                mat[k,j] := Coefficients(f)[ComponentIdeal(Gamma)][reps[j]];
            end for;
        end for;
        printf "Rows, columns, rank: %o, %o, %o\n", nrows, ncols, Rank(mat);
        bounds[l] := Dimension(Nullspace(mat));
        printf "Upper bound: %o\n", bounds[l];
    end for;

    return bounds;
    
end intrinsic;

intrinsic Plurigenera(Gamma::GrpHilbert, nb::RngIntElt) -> SeqEnum[RngIntElt]
{Given a congruence subgroup of type Gamma0(N) and GL2+, compute the plurigenera of the
associated Hilbert modular surface, i.e. dim H^0(K^n) for n = 1, ..., nb,
where K is the canonical bundle. For now, assume that we have:
- Gamma0(N) of GL2 type
- Exactly one cusp, ie. F has class number 1}
    
    require AmbientType(Gamma) eq GLPlus_Type: "Only Gamma0 and GL2+ is supported";
    require GammaType(Gamma) eq GAMMA_0_Type: "Only Gamma0 and GL2+ is supported";
    require NumberOfCusps(Gamma) eq 1: "Only one cusp is supported at the moment";    
    
    data := EllipticPointData(Gamma);
    for type in Keys(data) do
        c, _, _ := EllipticPointResolution(type);
        if not &and[x eq 2: x in c] then
            c;
            error "All elliptic points must have only -2 curves in their resolutions";
        end if;
    end for;

    return UpperBoundsOnPlurigenera(Gamma, nb);
    
end intrinsic;

intrinsic TestArithmeticGenus(F::FldNum, NN::RngOrdIdl) -> Any
  {Compute the arithmetic genus as (1/12)*(K^2 + e), summed over all components, and as 
  dim(S_2) + #Cl^+(F); return true if these are equal. Currently only for GL+ type.}

  NCl, mp := NarrowClassGroup(F);
  chi1 := 0;
  for bb in [mp(el) : el in NCl] do
    G := CongruenceSubgroup("GL+", "Gamma0", F, NN, bb);
    chi1 +:= ArithmeticGenus(G);
    vprintf HilbertModularForms: "for bb = (%o), chi = %o\n",
                                 IdealOneLine(bb), ArithmeticGenus(G);
  end for;
  vprintf HilbertModularForms: "(1/12)*(K^2 + e) = %o\n", chi1;

  M := GradedRingOfHMFs(F, 0);
  h := HilbertSeriesCusp(M, NN);
  //h := HilbertSeriesCusp(G);
  Pow<x> := PowerSeriesRing(Rationals());
  chi2 := Coefficient(Pow!h,2) + #NCl;
  vprintf HilbertModularForms: "dim(S_2) + #Cl^+(F) = %o\n", chi2;
  return chi1 eq chi2;
end intrinsic;

// TODO
intrinsic KodairaDimension(Gamma::GrpHilbert) -> MonStgElt
  {Returns the Kodaira dimension of the Hilbert modular surface associated to Gamma. 
  Currently just returns -100}
    error "Not Implemented";
  return -100; // FIXME
end intrinsic;

// Could be improved in the future.
intrinsic KodairaDimensionPossibilities(Gamma::GrpHilbert) -> MonStgElt
{Returns a list of possible Kodaira dimensions of the Hilbert modular surface associated to 
 Gamma, based on the arithmetic genus and the rationality criterion. When the level is 1, it
 gives a more refined list based on K^2. Currently only implemented for Gamma0.}

  require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";
  F := BaseField(Gamma);
  ZF := Integers(F);
  NCl, mp := NarrowClassGroup(F);
  chi := ArithmeticGenus(Gamma);

  if (chi eq 1) then
    if (Level(Gamma) eq 1*ZF) or ((Component(Gamma) @@ mp) eq NCl.0) then
      if RationalityCriterion(Gamma) then
        return [-1];
      else
        return [-1, 2];
      end if;
    else
      return [-1, 2];
    end if;
  else
    if Norm(Level(Gamma)) eq 1 then
      k2 := K2(Gamma) + getHZExceptionalNum(Gamma); //K2 of the minimal model of the HMS.
      if (chi eq 2) and (k2 eq 0) then
        return [0, 1];
      elif (chi ge 1) and (k2 eq 0) then
        return [1];
      else
        return [2];
      end if;
    else // We don't yet know the number of exceptional curves, so K2(minimal model) >= K2(Gamma).
      k2 := K2(Gamma);
      if (chi eq 2) and (k2 le 0) then
        return [0, 1, 2];
      elif (chi ge 1) and (k2 le 0) then
        return [1, 2];
      else
        return [2];
    end if;

    end if;

  end if;
end intrinsic;

intrinsic PrimeDiscriminant(D,q) -> MonStgElt
    {Given q|D, return +-q^(Valuation(D,q)) as needed in getHZExceptionalNum. }
    assert D mod q eq 0;
    assert IsFundamentalDiscriminant(D);
    sign := (q mod 4 eq 1) select 1 else -1;
    if (q eq 2) then
      sign_list := [(-1) : p in PrimeDivisors(D) | p mod 4 eq 3];
      if #sign_list eq 0 then
        sign := 1;
      else
       sign := &*sign_list;
      end if;
      end if;
    return sign*q^Valuation(D,q);
end intrinsic;

intrinsic getHZExceptionalNum(Gamma) -> MonStgElt
{Returns number of exceptional HZ divisors if the surface is *not rational*;
 currently only implemented for level 1.}

    require Norm(Level(Gamma)) eq 1 : "Only implemented for level 1";

    A := Norm(Component(Gamma));
    D := Discriminant(Integers(BaseField(Gamma)));
    qs := PrimeDivisors(D);
    Dqs := [PrimeDiscriminant(D,q) : q in qs];
    s := 2*&*[1 + KroneckerSymbol(Dq,A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 2*A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 3*A) : Dq in Dqs] div 2;
    s +:= (1 - KroneckerSymbol(D,3)^2)*
          &*[1 + KroneckerSymbol(Dq,9*A) : Dq in Dqs];
    if D eq 105 then
        s +:= 2;
    end if;
    return s;
end intrinsic;

intrinsic RationalityCriterion(Gamma) -> BoolElt
{Checks whether the Rationality Criterion is satisfied.
 Note 1: Only implemented for Gamma0(N) level.
 Note 2: it could be refined by including more Hirzebruch--Zagier divisors and resolution cycles 
 coming from elliptic points.}

    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";

    F := BaseField(Gamma);

    //Make a list of intersection numbers of cuspidal resolution cycles.
    res := CuspsWithResolution(Gamma);
    self_int_res := [];
    for x in res do
      for y in [1..x[4]] do
          self_int_res cat:= x[3];
      end for;
    end for;

    LevelList := [];

    //Make a list of possible exceptional Hirzebruch--Zagier divisors.
    if Norm(Level(Gamma)) eq 1 then //vdG VII.4 gives the following
      A := Component(Gamma);
      if Norm(A) eq 1 then
        Append(~LevelList, 1);
        Append(~LevelList, 4);
        Append(~LevelList, 9);
      end if;

      if NormEquation(F, 2*Norm(A)) then //2 is the norm of an ideal in the genus of A.
        Append(~LevelList, 2);
      end if;

      if NormEquation(F, 3*Norm(A)) then //3 is the norm of an ideal in the genus of A.
        Append(~LevelList, 3);
      end if;

    else //for now, only consider F_N if genus(F_N) = 0
      N := Generator(Level(Gamma) meet Integers());
      require Norm(Component(Gamma)) eq 1: "Only principal genus supported for higher level.";
      if N in [1 .. 10] cat [12, 13, 16, 18, 25] then
        Append(~LevelList, N^2);
      end if;
    end if;

    if #LevelList eq 0 then
      vprintf HilbertModularForms: "No exceptional HZ divisors found";
      return false;
    end if;

    //Compute intersections of HZ divisors with cusps.
    IntList := [];
    for M in LevelList do
      HZInt := HZCuspIntersection(Gamma, M);
      HZIntList := [];
      assert #HZInt eq #res;
      for i in [1 .. #HZInt] do
        for j in [1 .. res[i][4]] do
          HZIntList cat:= HZInt[i];
        end for;
      end for;
      Append(~IntList, HZIntList);
    end for;

    //Blow down any subset of the HZ divisors and check if we have a good configuration.
    for I in Subsets({1 .. #LevelList}) do
      if #I eq 0 then //Without blowing down, nothing to do.
        continue;
      else
        // List of indices s.t. boundary curve is now exceptional
        exc_indices := [i : i in [1 .. #self_int_res] |
                        self_int_res[i] + &+[ IntList[j][i] : j in I] eq -1];

        if #exc_indices le 1 then //One (-1)-curve is not enough!
          continue;
        end if;

        // For each two blown down expectional boundary curves, do they intersect?

        for S in Subsets(Set(exc_indices), 2) do
          T := SetToSequence(S);
          for j in I do
            if IntList[j][T[1]] ne 0 and IntList[j][T[2]] ne 0 then
              vprintf HilbertModularForms: "Blow down curves F_N for N in %o\n",
                                           LevelList[SetToSequence(I)];
              return true;
            end if;
          end for;
        end for;
      end if;

    end for;

    return false;
end intrinsic;

// IO
intrinsic WriteGeometricInvariantsToRow(Gamma::GrpHilbert) -> MonStgElt
{Script for writing geometric invariants to data table row. 
Format is label:[h^[2,0], h^[1,1]]:K^2:chi.}
  h2 := HodgeDiamond(Gamma)[3];
  return StripWhiteSpace(Join([
        LMFDBLabel(Gamma),
        //Sprint(KodairaDimension(Gamma)),
        Sprint(h2[1..2]),
        Sprint(K2(Gamma)),
        Sprint(ArithmeticGenus(Gamma))
  ], ":"));
end intrinsic;

intrinsic WriteLMFDBRow(Gamma::GrpHilbert) -> MonStgElt
{Script for writing information about the surface to table row.
Format is
label:field_label:field_discr:narrow_class_nb:level_label:level_norm:component_label:is_pp:group_type:gamma_type:h20:h11:K2:chi:number_of_cusps:kposs
where is_pp is true iff component is the inverse different of the quadratic field.}
    F_label, N_label, b_label, group_type, gamma_type := Explode(Split(LMFDBLabel(Gamma), "-"));
    F := BaseField(Gamma);
    N := Level(Gamma);
    b := ComponentIdeal(Gamma);
    h2 := HodgeDiamond(Gamma)[3];
    is_pp := IsNarrowlyPrincipal(Different(Integers(F)) * Component(Gamma));
    Ngens := [Eltseq(x): x in Generators(N)];
    bgens := [Eltseq(x): x in Generators(b)];
    return StripWhiteSpace(Join([LMFDBLabel(Gamma),
                                 F_label,
                                 b_label,
                                 gamma_type,
                                 group_type,
                                 N_label,
                                 Sprint(Ngens),
                                 Sprint(bgens),
                                 Sprint(KodairaDimensionPossibilities(Gamma)),
                                 Sprint(K2(Gamma)),
                                 Sprint(ArithmeticGenus(Gamma)),
                                 Sprint(h2[1]),
                                 Sprint(h2[2]),
                                 Sprint(NarrowClassNumber(F)),
                                 Sprint(Norm(N)),
                                 Sprint(NumberOfCusps(Gamma)),                                 
                                 Sprint(Discriminant(F)),
                                 Sprint(NumberOfEllipticPoints(Gamma)),
                                 Sprint(NumberOfEllipticPoints(Gamma, 2)),
                                 Sprint(NumberOfEllipticPoints(Gamma, 3)),
                                 Sprint(NumberOfEllipticPoints(Gamma, 4)),
                                 Sprint(NumberOfEllipticPoints(Gamma, 5)),
                                 Sprint(NumberOfEllipticPoints(Gamma, 6)),
                                 Sprint(LengthOfCuspResolutions(Gamma)),
                                 Sprint(LengthOfEllipticPointResolutions(Gamma)),
                                 Sprint(LengthOfResolutions(Gamma)),
                                 Sprint(EulerNumber(Gamma)),
                                 Sprint(is_pp)
                                ], ":"));                               
end intrinsic;

/*
// is this still right even when we haven't blown down?
intrinsic EasyIsGeneralType(hs::SeqEnum) -> Any
  {}
  chi, k2 := Explode(HodgeToChiK2(hs));
  if (chi gt 1) and (k2 gt 0) then
    return true;
  end if;
  return false;
end intrinsic;
*/

intrinsic HodgeToChiK2(hs::SeqEnum) -> Any
{Compute the Arithmetic Genus and c_1^2 from Hodge numbers h^(2,0) and h^(1,1).}
  h20, h11 := Explode(hs);
  chi := h20 + 1;
  c12 := 10*(h20 + 1) - h11;
  return [chi, c12];
end intrinsic;
