///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

import "CongruenceSubgroup.m": GAMMA_0_Type;

//Auxiliary function to handle the optional parameters for Basis calls
function SubBasis(basis, IdealClassesSupport, GaloisInvariant)
  if IsNull(basis) then return basis; end if;
  Mk := Parent(basis[1]);
  // handle optional argument IdealClassesSupport
  if IdealClassesSupport cmpeq false then
    // Default is all ideals classes
    IdealClassesSupport := SequenceToSet(NarrowClassGroupReps(Parent(Mk))); 
  else
    // Optionally we may specify a subset of ideal classes  
    IdealClassesSupport := SequenceToSet(IdealClassesSupport);
  end if;
  
  IdealClassesSupportComplement := Setseq(SequenceToSet(NarrowClassGroupReps(Parent(Mk))) diff
                                                       IdealClassesSupport);

  if #IdealClassesSupportComplement eq 0 then
    // in this case LinearDependence will return the identity matrix
    basis := basis;
  else
    B := basis;
    relations := LinearDependence(B : IdealClasses:=IdealClassesSupportComplement);
    // basis is only supported over IdealClassesSupport
    basis := [ &+[rel[i]*B[i] : i in [1..#B]] : rel in relations];
  end if;

  // handle optional argument GaloisInvariant
  if GaloisInvariant then
    InvariantGenerators := [1/2*(b + Swap(b)) : b in basis];
    coeffs := CoefficientsMatrix(basis : IdealClasses:=IdealClassesSupport);
    basis := [basis[i] : i in PivotRows(coeffs)];
  end if;
  return basis;
end function;

// Currently calls the Newforms and Eisenstein series from Creations folder

intrinsic CuspFormBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false,
  GaloisDescent:=true) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}

  require #SequenceToSet(Weight(Mk)) eq 1: "We only support parallel weight.";

  if not assigned Mk`CuspFormBasis then
    N := Level(Mk);
    k := Weight(Mk);

    if k[1] ge 2 then
      Mk`CuspFormBasis := [];
      // This only works for trivial character, as we rely on the magma functionality
      msg := "We only support CuspFormBasis for characters with trivial dirichlet " *
             "restriction, as we rely on the magma functionality";
      require IsTrivial(DirichletRestriction(Character(Mk))): msg;

      for dd in Divisors(N) do
        Mkdd := HMFSpace(Parent(Mk), dd, k);
        if CuspDimension(Mkdd) gt 0 then
          if dd eq N then
            Mk`CuspFormBasis cat:= NewCuspForms(Mk : GaloisDescent:=GaloisDescent);
          else
            Mk`CuspFormBasis cat:= OldCuspForms(Mkdd, Mk : GaloisDescent:=GaloisDescent);
          end if;
        end if;
      end for;
      dim := 0;
      if #Mk`CuspFormBasis gt 0 then
        dim := &+[Degree(CoefficientRing(f)) : f in Mk`CuspFormBasis];
      end if;

      msg := Sprintf("CuspDimension(Mk) = %o != %o = #Mk`CuspFormBasis",
                     CuspDimension(Mk), #Mk`CuspFormBasis);
      require CuspDimension(Mk) eq dim : msg;
    else
      Mk`CuspFormBasis := Weight1CuspBasis(Mk);
    end if;
  end if;
  return SubBasis(Mk`CuspFormBasis, IdealClassesSupport, GaloisInvariant);
end intrinsic;


intrinsic HMFCertifiedCuspBasis(M :: ModFrmHilDGRng, Gamma :: GrpHilbert, weight :: SeqEnum)
          -> SeqEnum                 
{Compute a basis of the space of modular forms for Gamma. The q-expansion
precision is at least prec, and high enough to ensure that the basis has the
right number of elements.}

    // TODO: Add in some overloading?
    
    // require AmbientType(Gamma) eq GLPlus_Type: "Only Gamma0 and GL2+ is supported";
    require GammaType(Gamma) eq GAMMA_0_Type: "Only Gamma0 is supported.";
    msg := "Only parallel even weight is supported";
    require weight[1] eq weight[2] and weight[1] mod 2 eq 0: msg;

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


intrinsic _ConvertToFlattenedBasis(Mk, basisList, levelList) -> SeqEnum
{Essentially, converts the result of CuspFormLevelDecompositionBasis with KeepOldParents:=false
to KeepOldParent:=true.}
    
  flattened := [];
  for i in [1 .. #basisList] do
      basis := basisList[i];
      mm := levelList[i];
      
      for f in basis do
          Append(~flattened, Inclusion(f, Mk, mm));
      end for;
  end for;

  return flattened;
end intrinsic;

intrinsic CuspFormLevelDecompositionBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false,
  GaloisDescent:=true,
  KeepOldParents:=false) -> Any
{Retuns a basis of the space of cusp forms Sk(NN) that corresponds to the direct sum decomposition

    Sk(NN) = Sum_\{dd | NN\} Sum_\{m | NN/dd\} alpha_m( Sk(dd)_\{new\} ).

The default return value is as a sequences of forms in Mk. If the parameter `KeepOldParents`
is set, a list of sequences is returned instead, where each form is a new form at its respective
level; the second return value is the list of mm defining the embeddings alpha_m.}

  require #SequenceToSet(Weight(Mk)) eq 1: "We only support parallel weight.";

  N := Level(Mk);
  k := Weight(Mk);

  if k[1] lt 2 then error "Not implemented for weight 1."; end if;
  
  basisList := [* *];
  divisorList := [];
  
  // This only works for trivial character, as we rely on the magma functionality
  msg := "We only support CuspFormBasis for characters with trivial dirichlet restriction, " *
         "as we rely on the magma functionality";
  require IsTrivial(DirichletRestriction(Character(Mk))) : msg;

  // Loop over decomposition terms.
  for dd in Divisors(N) do
      for mm in Divisors(N / dd) do
          Mkdd := HMFSpace(Parent(Mk), dd, k);

          if CuspDimension(Mkdd) eq 0 then
              Append(~basisList, []); Append(~divisorList, mm); continue;
          end if;

          newforms := NewCuspForms(Mkdd : GaloisDescent:=GaloisDescent);
          Append(~basisList, newforms);
          Append(~divisorList, mm);
      end for;
  end for;
  
  if GaloisDescent then
    // if we are taking Q orbits
    totalNum := &+[#basis : basis in basisList];
      
    msg := Sprintf("CuspDimension(Mk) = %o != %o = #Mk`CuspFormBasis",
                   CuspDimension(Mk), totalNum);
      
    require CuspDimension(Mk) eq totalNum : msg;
  end if;

  if KeepOldParents then
      return basisList, divisorList;
  else
      return _ConvertToFlattenedBasis(Mk, basisList, divisorList);
  end if;

end intrinsic;


intrinsic EisensteinBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false
  ) -> SeqEnum[ModFrmHilDElt]
  { return a basis for the complement to the cuspspace of Mk }
  if not assigned Mk`EisensteinBasis then
    pairs := EisensteinAdmissibleCharacterPairs(Mk);
    eisensteinbasis := &cat[EisensteinInclusions(Mk, p[1], p[2]) : p in pairs];
    Mk`EisensteinBasis := &cat[GaloisOrbitDescent(f) : f in eisensteinbasis];
    require #Mk`EisensteinBasis eq EisensteinDimension(Mk) : "#Mk`EisensteinBasis = %o != %o = EisensteinDimension(Mk)", #Mk`EisensteinBasis, EisensteinDimension(Mk);
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`EisensteinBasis, IdealClassesSupport, GaloisInvariant);
end intrinsic;




intrinsic Basis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false
  ) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  if not assigned Mk`Basis then
    vprintf HilbertModularForms: "Computing basis for space of parallel weight %o with precision %o\n", Weight(Mk)[1], Precision(Parent(Mk));
    // Cuspforms
    CB := CuspFormBasis(Mk);
    //Eisenstein Series
    EB := EisensteinBasis(Mk);
    Mk`Basis := EB cat CB;
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`Basis, IdealClassesSupport, GaloisInvariant);
end intrinsic;

intrinsic GaloisInvariantBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for the Galois invariant subspace}

  B := Basis(Mk);
  InvariantGenerators:=[];
  for x in B do
    Append(~InvariantGenerators, 1/2*(x+Swap(x)));
  end for;
  InvariantBasis:=[];
  for x in InvariantGenerators do
    if #LinearDependence(InvariantBasis cat [x]) eq 0 then
      Append(~InvariantBasis, x);
    end if;
  end for;
  return InvariantBasis;
end intrinsic;

intrinsic ComponentBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a Basis for Mk of forms that are only supported on one component}
  bbs := NarrowClassGroupReps(Parent(Mk));
  return &cat[Basis(Mk: IdealClassesSupport := [bb]) : bb in bbs];
end intrinsic;

intrinsic SpecifiedComponentBasis(Mk::ModFrmHilD, bb::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {returns a basis of forms that are only supported on a specified component bb}
  return Basis(Mk: IdealClassesSupport := [bb]);
end intrinsic;
