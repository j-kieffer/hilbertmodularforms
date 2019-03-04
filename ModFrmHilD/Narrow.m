intrinsic ShintaniWalls(ZF::RngOrd) -> Any
  {returns lower and upper walls of the Shintani domain}
  F := NumberField(ZF);
  assert Degree(F) le 2;
  places := InfinitePlaces(F);
  eps := FundamentalUnit(F);
  if Norm(eps) eq -1 then
    // In this case CK = CK^+ so the totally positive units are squares i.e. the subgroup generated by eps^2
    eps := eps^2;
  else 
    if not IsTotallyPositive(eps) then
      // In this case CK not equal to CK^+ so there are no units of mixed signs. If the fundamental unit is not totally positive we multiply by -1 
      eps := -1*eps;
    end if;
  end if;
  eps1 := Evaluate(eps, places[1]);
  eps2 := Evaluate(eps, places[2]);
  // always returns smallest first
  if eps1/eps2 le eps2/eps1 then
    return Sqrt(eps1/eps2), Sqrt(eps2/eps1);
  else
    return Sqrt(eps2/eps1), Sqrt(eps1/eps2);
  end if;
end intrinsic;

intrinsic NiceBasis(bb::RngOrdFracIdl) -> SeqEnum
  {Given a fractional ideal bb, returns a basis (a,b) in Smith normal form where Trace(a) = n and Trace(b) = 0}
  basis := Basis(bb);
  ZF := Parent(basis[2]);
  Tr := Matrix([[Trace(basis[i]) : i in [1..#basis]]]);
  _,_,Q := SmithForm(Tr);
  ChangeofBasisMatrix := ChangeRing(Q,ZF);
  NewBasis := Eltseq(Vector(basis)*ChangeofBasisMatrix);
  return NewBasis;
end intrinsic;

// Elements of the Shintani Domain with trace t
/*
Idea: I've hopefully obtained basis {a,b} for the ideal bb where Tr(a) = n and Tr(b) = 0. Elements in ideal will look like xa+yb where x,y \in Z and have embedding xa_1+ yb_1 and xa_2+ yb_2. 
All totally positive elements of given trace t will satisfy

1).    t = Tr(xa+yb)    <=>   t = xn
2).    C_1 < (xa_1+yb_1)/(xa_2+yb_2) < C_2.     <=>   (C_1*x*a_2 -x*a_1)/(b_1-C_1*b_2) < y   and  y < (C_2*x*a_2 -x*a_1)/(b_1-C_2*b_2)

where C1 and C2 are the slope bounds on the shintani domain. Eq 1) determines the value for x while Eq 2) allows us to loop over values of y
*/

// renamed Pos_elt_of_Trace_in_Shintani_Domain by ShintaniDomainOfTrace
intrinsic ShintaniDomainOfTrace(bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given bb a fractional ideal, t a trace bound, returns the totally positive elements of bb in the balanced Shintani cone with trace t.}
  Basis := NiceBasis(bb);
  F := NumberField(Parent(Basis[1]));
  ZF := Integers(F);
  places := InfinitePlaces(NumberField(Parent(Basis[1])));
  SmallestTrace := Trace(Basis[1]);
  T := [];
  if t mod SmallestTrace eq 0 then
    x := t div SmallestTrace;
    C1,C2 := ShintaniWalls(ZF);
    a_1 := Evaluate(Basis[1],places[1]); b_1 := Evaluate(Basis[2],places[1]);
    a_2 := Evaluate(Basis[1],places[2]); b_2 := Evaluate(Basis[2],places[2]);
    B1 := (C1*x*a_2 -x*a_1)/(b_1-C1*b_2); B2 := (C2*x*a_2 -x*a_1)/(b_1-C2*b_2);
    Lower := Ceiling(Min(B1,B2));
    Upper := Max(B1,B2);
    // I need to make sure I don't include points that lie on both walls. This is bad code but removes points that lie on upper wall
    if (Upper - Floor(Upper)) lt 10^(-70) then Upper := Floor(Upper)-1; else Upper := Floor(Upper); end if;
    for y in [Lower .. Upper] do
      Append(~T, x*Basis[1]+y*Basis[2]);
    end for;
  end if;
  return T;
end intrinsic;

intrinsic ShintaniDomain(bb::RngOrdFracIdl, t::RngIntElt) -> List
  {Returns Shintani Domain of bb up to trace t.}
  F := NumberField(Parent(Order(bb).1));
  assert Degree(F) le 2;
  return &cat [ShintaniDomainOfTrace(bb, i) : i in [1..t]];
end intrinsic;    

/* // The totally positive elts of given trace */ 
/* Idea: I've hopefully obtained basis {a,b} for the ideal bb where Tr(a) = n and Tr(b) = 0. Elements in ideal will look like xa+yb where x,y \in Z and have embedding xa_1+ yb_1 and xa_2+ yb_2. */ 
/* All totally positive elements of given trace t will satisfy */

/* 1).    t = Tr(xa+yb)    <=>   t = xn */
/* 2).    xa+yb >> 0.     <=>   y > -x*a_1/b_1   and  y > -x*a_2/b_2 */ 

/* Eq 1) determines the value for x while Eq 2) allows us to loop over values of y */

// renamed PositiveElementsOfTraceForIdealOfGivenTrace by PositiveElementsOfTrace
intrinsic PositiveElementsOfTrace(bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given bb a fractional ideal, t a trace bound, returns the totally positive elements of bb with trace t.}
  Basis := NiceBasis(bb);
  places := InfinitePlaces(NumberField(Parent(Basis[1])));
  SmallestTrace := Trace(Basis[1]);
  T := [];
  if t mod SmallestTrace eq 0 then
    x := t div SmallestTrace;
    a_1 := Evaluate(Basis[1],places[1]); b_1 := Evaluate(Basis[2],places[1]);
    a_2 := Evaluate(Basis[1],places[2]); b_2 := Evaluate(Basis[2],places[2]);
    Lower := Ceiling(Min(-x*a_1/b_1,-x*a_2/b_2));
    Upper := Floor(Max(-x*a_1/b_1,-x*a_2/b_2));
    for y in [Lower .. Upper] do
      /* Append(~T, [x*Basis[1]+y*Basis[2]]); */
      Append(~T, x*Basis[1]+y*Basis[2]);
    end for;
  end if;
  return T;
end intrinsic;

// renamed PositiveElementsOfTraceForIdealOfGivenTraceUpTo by PositiveElements
intrinsic PositiveElements(bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given bb a fractional ideal, t a trace bound, returns the totally positive elements of bb with trace up to t.}
  l := [];
  for i := 1 to t do
    elts_of_trace_i := PositiveElementsOfTrace(bb, i);
    if #elts_of_trace_i gt 0 then
      l cat:= elts_of_trace_i;
    end if;
  end for;
  return l;
end intrinsic;

intrinsic EmbedNumberField(nu::RngOrdElt, places::SeqEnum) -> SeqEnum
  {
    Input: nu an element of ZF where F is totally real
    Output: A tuple of the real embeddings of nu in RR
  }
  return [Evaluate(nu, pl) : pl in places];
end intrinsic;

intrinsic Slope(alpha::RngOrdElt) -> FldReElt
  {
    Input:  alpha, an element of ZF for F a totally real quadratic number field
    Output: The "slope" defined by alpha: sigma_2(alpha)/sigma_1(alpha) where sigma_i is the ith embedding of F
  }
  OK := Parent(alpha);
  K := NumberField(OK);
  places := InfinitePlaces(K);
  return Evaluate(alpha, places[2]) / Evaluate(alpha, places[1]);
end intrinsic;

intrinsic IsShintaniReduced(nu::RngOrdElt) -> BoolElt
  {}
  // wall1<wall2
  wall1, wall2 := ShintaniWalls(Parent(nu));
  slope := Slope(nu);
  prec := Precision(Parent(slope));
  // walls with fuzz
  if (wall1-10^(-prec/2) le slope) and (slope le wall2+10^(-prec/2)) then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic ReduceShintaniComputeIdeal(nu::RngOrdElt, shintani_reps::Assoc) -> Any
  {}
  reps := [];
  for I in Keys(shintani_reps) do
    for t in Keys(shintani_reps[I]) do
      reps cat:= shintani_reps[I][t];
    end for;
  end for;
  return ReduceShintaniComputeIdeal(nu, reps);
end intrinsic;

intrinsic ReduceShintaniComputeIdeal(nu::RngOrdElt, shintani_reps::SeqEnum[RngOrdElt]) -> Any
  {}
  if nu eq 0 then
    return Parent(nu)!0;
  end if;
  assert IsTotallyPositive(nu);
  ZF := Parent(nu);
  nu_ideal := ideal<ZF|nu>;
  shintani_ideals := [ideal<ZF|a> : a in shintani_reps];
  matches := [];
  for i := 1 to #Keys(shintani_reps) do
    I := ideal<ZF|shintani_reps[i]>;
    if nu_ideal eq I then
      Append(~matches, [* I, i *]);
    end if;
  end for;
  assert #matches eq 1;
  return shintani_reps[matches[1][2]];
end intrinsic;

intrinsic ReduceShintaniMinimizeTrace(nu::RngOrdElt) -> Any
  {}
  if nu eq 0 then
    return Parent(nu)!0;
  end if;
  assert IsTotallyPositive(nu);
  ZF := Parent(nu);
  F := NumberField(ZF);
  places := InfinitePlaces(F);
  eps := FundamentalUnit(ZF);
  // determine signs of eps and make eps totally positive
  eps_RR := EmbedNumberField(eps, places);
  assert #eps_RR eq 2; // only for quadratic fields right now
  pos_count := 0;
  for i := 1 to #places do
    if eps_RR[i] gt 0 then
      pos_count +:= 1;
    end if;
  end for;
  if pos_count eq 0 then
    eps := -eps;
  elif pos_count eq 1 then
    eps := eps^2;
  else
    eps := eps;
  end if;
  eps_RR := EmbedNumberField(eps, places);
  slope_eps := Slope(eps);
  slope_nu := Slope(nu);
  // TODO: do we know calculus?
  // r := -Floor( RealField(100)!(Log(slope_nu)/Log(slope_eps)) ); // old formula
  /* r := Integers()!((1/2)*Round(Log(RealField(100)!slope_nu)/Log(RealField(100)!eps_RR[1]))); */
  RR := RealField(100);
  ratio := RR!(1/2)*Log(RR!slope_nu)/Log(RR!eps_RR[1]);
  ratio_ceiling := Ceiling(ratio);
  ratio_floor := Floor(ratio);
  nu_ceiling := eps^ratio_ceiling*nu;
  nu_floor := eps^ratio_floor*nu;
  slope_nu_ceiling := Slope(nu_ceiling);
  slope_nu_floor := Slope(nu_floor);
  slopes := [slope_nu_floor, slope_nu_ceiling];
  nus := [nu_floor, nu_ceiling];
  ParallelSort(~slopes, ~nus);
  if IsShintaniReduced(nus[1]) then
    return nus[1];
  else
    assert IsShintaniReduced(nus[2]);
    return nus[2];
  end if;
end intrinsic;

intrinsic ReduceShintani(nu::RngOrdElt, shintani_reps::Assoc) -> Any
  {}
  nu_reduced_by_ideal := ReduceShintaniComputeIdeal(nu, shintani_reps);
  nu_reduced_by_trace := ReduceShintaniMinimizeTrace(nu);
  return nu_reduced_by_ideal;
  // sanity check using trace when ready
  /* if nu_reduced_by_ideal eq nu_reduced_by_trace then */
  /*   return nu_reduced_by_ideal; */
  /* else */
  /*   error_message := Sprintf("Shintani walls?\n"); */
  /*   error_message *:= Sprintf("nu using ideals = %o\n", nu_reduced_by_ideal); */
  /*   error_message *:= Sprintf("Trace(nu using ideals) = %o\n", Trace(nu_reduced_by_ideal)); */
  /*   error_message *:= Sprintf("nu using trace = %o\n", nu_reduced_by_trace); */
  /*   error_message *:= Sprintf("Trace(nu using trace) = %o\n", Trace(nu_reduced_by_trace)); */
  /*   error error_message; */
  /* end if; */
end intrinsic;

intrinsic GetIndexPairs(bb::RngOrdFracIdl, M::ModFrmHilD) -> Assoc
  {returns list (assoc array) of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to trace bound Precision(M).}
  assert bb in ClassGroupReps(M);
  t := Precision(M);
  positive_reps := PositiveReps(M); // indexed by ideal class and then trace
  shintani_reps := ShintaniReps(M); // indexed by ideal class and then trace
  pairs := AssociativeArray(); // indexed by nu
  for i := 0 to t do // loop over trace
    for j in [0..Min(i, t - i)] do // this min guarantees Tr(nu1+nu2) < trace bound
      for nu1 in positive_reps[bb][i] do
        for nu2 in positive_reps[bb][j] do
          nu := nu1 + nu2;
          if nu in shintani_reps[bb][Trace(nu)] then
            if IsDefined(pairs, nu) then
              Append(~pairs[nu], [nu1, nu2]);
              Append(~pairs[nu], [nu2, nu1]);
            else
              pairs[nu] := [[nu1, nu2]];
              pairs[nu] := [[nu2, nu1]];
            end if;
          end if;
        end for;
      end for;
    end for;
  end for;
  // at this point pairs[nu] = [[nu1,nu2],...] with nu in the Shintani domain
  // and nu1,nu2,... totally positive (not necessarily in Shintani)
  // first eliminate multiple pairs [nu1,nu2],[nu1,nu2]
  pairs_with_redundancies_eliminated := AssociativeArray();
  for key in Keys(pairs) do
    pairs_with_redundancies_eliminated[key] := SequenceToSet(pairs[key]);
  end for;
  pairs := pairs_with_redundancies_eliminated;
  // TODO now move pairs [nu1,nu2] into shintani domain
  return pairs;
end intrinsic;
  /* F := BaseField(M); */
  /* ZF := Integers(F); */
  /* places := InfinitePlaces(F); */
  /* nus := PositiveElementsOfTraceForIdealOfGivenTraceUpTo(bb, t); */
  /* shintani_domain := Shintani_Domain(bb, t); */
  /* Shintanielts, result, trace_bound := ShintaniDomain(M,ZF,places); gens := Keys(result); */
  /* by_trace := AssociativeArray(); */
  /* for i := 0 to t do */
  /*   s_1 := PositiveElementsOfTraceForIdealOfGivenTrace(bb, i); */
  /*   by_trace[i] := s_1; */
  /*   for j in [0..Min(i, trace_bound - i)] do */
  /*     for nu_1 in s_1 do */
  /*       for nu_2 in by_trace[j] do */
  /*         nu := nu_1 + nu_2; */
  /*         if IsDefined(result, nu) then */
  /*           Append(~result[nu], [nu_1, nu_2]); */
  /*           Append(~result[nu], [nu_2, nu_1]); */
  /*         end if; */
  /*       end for; */
  /*     end for; */
  /*   end for; */
  /* end for; */

  /* indices_list := []; */
  /* shintani_reps := AssociativeArray(); */
  /* for nu in gens do */
  /*   sums_up := []; */
  /*   for x in Set(result[nu]) do */
  /*     if not IsDefined(shintani_reps, x[1]) then */
  /*       shintani_reps[x[1]] := Shintanielts[ideal<ZF |x[1]>]; */
  /*     end if; */
  /*     if not IsDefined(shintani_reps, x[2]) then */
  /*       shintani_reps[x[2]] := Shintanielts[ideal<ZF |x[2]>];; */
  /*     end if; */
  /*     Append(~sums_up, [shintani_reps[x[1]], shintani_reps[x[2]]]); */
  /*   end for; */
  /*   Append(~indices_list, [* nu, sums_up *]); */
  /* end for; */
  /* return indices_list; */
/* end intrinsic; */

/*
Reduction to Shintani Domain
*/

/* intrinsic EmbedNumberField(nu::RngOrdElt, places::SeqEnum) -> SeqEnum */
/*   { */
/*     Input: nu an element of ZF where F is totally real */
/*     Output: A tuple of the real embeddings of nu in RR */
/*   } */
/*   return [Evaluate(nu, pl) : pl in places]; */
/* end intrinsic; */

/* intrinsic Slope_F(alpha::RngOrdElt, places::SeqEnum) -> FldReElt */
/*   { */
/*     Input:  alpha, an element of ZF for F a totally real quadratic number field */
/*     Output: The "slope" defined by alpha: sigma_2(alpha)/sigma_1(alpha) where sigma_i is the ith embedding of F */
/*   } */
/*   return Evaluate(alpha, places[2]) / Evaluate(alpha, places[1]); */
/* end intrinsic; */

/* intrinsic ReduceToShintani(nu::RngOrdElt, eps::RngQuadElt, log_slope_funu::FldReElt, places::SeqEnum) -> FldNumElt */
/* intrinsic ReduceToShintani(nu::RngOrdElt) -> FldNumElt */
/*   { */
/*     Input: nu a totally nonnegative element of ZF */
/*     Output: a representative for nu in the Shintani cone */
/*   } */
/*   assert (IsTotallyPositive(nu) or (nu eq 0)); // only for totally nonnegative elements */
/*   if nu eq 0 then */
/*     return 0; */
/*   else */
/*     m_nu := Slope_F(nu, places); */
/*     r := -Floor(RealField(100) ! (Log(m_nu) / log_slope_funu)); */
/*     return nu * (eps^2)^r; */
/*   end if; */
/* end intrinsic; */
