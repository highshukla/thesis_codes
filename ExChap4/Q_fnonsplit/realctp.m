
//This script is under developement. Can even raise syntax errors.
//good_elts is already given as sequence of elements in the Etale algebra A;

almost_real := function(c)
       prec := Precision(Parent(c)); prec := prec - prec div 5;
  if AbsoluteValue(Real(c)) lt 10^(-prec) then 
    if AbsoluteValue(Imaginary(c)) lt 10^(-prec) then return true; else return false; 
    end if;
  end if;
  if AbsoluteValue(Imaginary(c)/Real(c)) lt 10^(-prec) then return true; else return false; end if;
end function;


realXGCD := function(a,b)
       P := Parent(a); b := P!b;
  s:= P!0; old_s := P!1; t := P!1; old_t := P!0; r := b;  old_r := a;
  while r ne Parent(a)!0 do 
  q := old_r div r; temp := old_r; old_r := r; r := temp mod r;
  temp := old_s; old_s := s; s := temp - q*s;
  temp := old_t; old_t := t; t := temp- q*t;
  end while;
//  print "XGCD check:", old_s*a + old_t*b-old_r;
  lcf := LeadingCoefficient(old_r);
  return old_r/lcf, old_s/lcf, old_t/lcf;
end  function;


realGCD := function(a,b)
  P := Parent(a);
  r := b; 
  while (a mod b) ne P!0 do
    r := a mod b; 
    a := b; b := r;
  end while;
  return r/(LeadingCoefficient(r));
end function;



realCR := function(La, Lm)
  PR := Parent(Lm[1]);
  La := [PR!a : a in La]; Lm := [PR!a: a in Lm];
  Mod := Lm[1];
  CR := La[1];

  for i := 2 to #Lm do
    g,c,d := realXGCD(Mod,Lm[i]); //Attention !!!! Loss of precission
    //print g, c*Mod + d*Lm[i]-g;
    //assert g eq c*Mod + d*Lm[i];
    


    //if g ne PR!1 then
    if Degree(g) ne 0 then
      error "Error, ChineseRemainderTheorem: modules must be coprime.";
    end if;
    c := c div g;
    d := d div g;
    e2 := Mod*c;
    e1 := Lm[i]*d;

    Mod := Mod*Lm[i];
    CR := (e1*CR+e2*La[i]) mod Mod;
  end for;
  return CR;
end function;



almost0pol := function(pol)
  P := Parent(pol); C := BaseRing(P); prec := Precision(C); 
  prec := prec- prec div 5;
  if forall{t : t in Coefficients(pol)| AbsoluteValue(t) lt 10^(-prec)} then 
    return true; else return false;
  end if; 
end function;


locAdd_real := function(P1, P2, f)

  if Degree(P2[1]) eq 0 then return false, P1, _; end if;
  g := Degree(f) div 2;
  if Degree(P1[1]) eq 0 then return false, P2, _; end if; //when P1 or P2 is identity.
  d1 := Degree(P1[1]); d2 := Degree(P2[1]);
  a1 := P1[1]; a2 := P2[1]; b1 := P1[2]; b2 := P2[2];
  if d1 + d2 gt g+1 then 
    d := Gcd(Gcd(a1, a2), b1+b2); a := (a1*a2) div d^2;
    b := locCR([b1 mod (a1 div d), b2 mod (a2 div d)], [a1 div d, a2 div d]);
    while Degree(a) gt (Degree(f) -1) div 2 do 
      c := (f - b^2)  div a; c := c/ LeadingCoefficient(c);
      a := c; b := -b mod a;
    end while;
    return false, [a,b],_;
  end if;

  if P2[2] eq 0 then temp := P1; P1 := P2; P2 := temp; end if;
  //swap so that P1 is the two torsion element.
  if P2[2] eq 0 then if d1+d2 lt g+1 then return false, [P1[1]*P2[1], 0], _;
    else return true, [f div P1[1]*P2[1], 0], 0; end if; end if;
  //define a1, a2, b1, b2 again because they have been changed
  a1 := P1[1]; a2 := P2[1]; b1 := P1[2]; b2 := P2[2];
  if b1 ne Parent(b1)!0 then newb := realCR([b1,b2], [a1,a2]); 
  else gcd, c, d := realXGCD(a1,a2); newb := b2*c*a1 mod (a1*a2);
  end if;
  if d1 + d2 lt g+1 then return false, [a1*a2, newb], _; end if;
  pol := f -newb^2; newa := pol div (a1*a2);
  return true, [newa, -newb mod newa], newb;

end function;


adjustPv := function(Pv, chi_val , complexWPts,f)
  S := Subsets(SequenceToSet(complexWPts));
  P := Parent(Pv[1]); C := BaseRing(P);
  R<x,y> := PolynomialRing(BaseRing(P),2);
  for s in S do 
    newPv := Pv; fctns := [];
    for i in s do 
      bool, newPv, fctn := locAdd_real([P.1-complexWPts[i], P!0], newPv, f);
    end for;
    flag := true; Pv1 := newPv; 
      newPv := Pv1; Pv1s := [P!Polynomial([ComplexConjugate(j): j in ElementToSequence(Pv1[i])]) : i in [1..2]];
    for c in chi_val do
      oldPv := newPv;
      bool, newPv, fctn := locAdd_real([P.1-complexWPts[c], P!0], newPv, f);
      fctn := y-Evaluate(fctn, x);
      if bool then Append(~fctns, [(x-complexWPts[c])*Evaluate(oldPv[1], x), fctn]);
      end if;
    end for;
    if forall{t: t in [1..2] | not almost0pol(newPv[t]-Pv1s[t])} then 
      return true, fctns, Pv1;
    end if;
  end for;
  return false, _, _;
end function;
    

realCTP:= function(ctpvec,WPts_nf,globmat, S, f, elt1, elt2s, real_mor)

  bf := Domain(real_mor);
  cur := HyperellipticCurve(f);
  curS := BaseChange(cur, S);
  l := Degree(f);
  defS := DefiningPolynomial(S);
  C := ComplexField(Precision(Codomain(real_mor)));
  Ct := PolynomialRing(C);
  R := Codomain(real_mor);
  f := Polynomial([real_mor(c): c in Coefficients(f)]);
  rS := Roots(Polynomial([C!real_mor(x): x in ElementToSequence(defS)]))[1][1];
  complex_mor := hom<S -> C| x :-> &+[y[i]*rS^(i-1) where y := ElementToSequence(x): i in
    [1..#ElementToSequence(x)]]>;
  WPts := [complex_mor(pt): pt in WPts_nf];
  real_root_index := [i : i in [1..l]| almost_real(WPts[i])];
  print "real root indices: ", real_root_index;
  complex_conjugate_index := [];
  //Computing complex conjugate indices.
  for i in  [1..l-1] do 
    if i in real_root_index then continue; end if;
    for j in [i+1 .. l] do
      if j in real_root_index then continue; end if; 
      if  almost_real(WPts[i]+WPts[j]) then Append(~complex_conjugate_index, <i,j>);
      end if; 
    end for;
  end for;
  curC := BaseChange(curS, complex_mor);
  print complex_conjugate_index;
 
    g := Polynomial([real_mor(x): x in ElementToSequence(elt1)]); 
    g := [Evaluate(g,pt): pt in WPts]; 
    chi_val := [i : i in real_root_index | Sign(Real(g[i])) eq -1];
    sqg := [C!1: i in [1..l]]; 
    for i in real_root_index do sqg[i]:= SquareRoot(Real(g[i])); end for;
    for pair in complex_conjugate_index do sqg[pair[1]] := SquareRoot(g[pair[1]]);
      sqg[pair[2]]:= ComplexConjugate(sqg[pair[1]]);
    end for;
    

    Gmat := globmat[1];
    Pgv := IdentityMatrix(C,l);
    for t in [1..l] do for h in [1..l] do 
        gpt := Gmat[t][h]; Pgv[t][h] :=
        complex_mor(gpt[1])*sqg[t]+complex_mor(gpt[2])*sqg[h];
    end for; end for;
    

// if g is a square     
    if chi_val eq [] then 
    print "real g is a square";
    for ap in [1..#elt2s] do gp := Polynomial([real_mor(x): x in ElementToSequence(elt2s[ap])]);
      gp := [Sign(Real(Evaluate(gp,pt))): pt in WPts] ;
      for i in real_root_index do 
        if gp[i] eq -1 then 
        eps_val := R!0; 
        pseq :=  [<i,j,-1>: j in [1..l]| j ne i];
        eps_val := eps_val + (&+[x[3]*Argument(Pgv[x[1]][x[2]]): x in pseq]);
        eps_val := PolarToComplex(1, eps_val);
        assert almost_real(eps_val);
        ctpvec[ap]:= ctpvec[ap]*Sign(Real(eps_val));
        printf "local contribution at ap = %o is:========================= %o", Sign(Real(eps_val));
        print "";
        end if;
      end for;
    end for;
    end if;
   print "real g is not a square"; 
   gps := [Polynomial([real_mor(x): x in ElementToSequence(elt2s[ap])]): ap in [1..#elt2s]];
   gps := [[Sign(Real(Evaluate(gp, pt))) : pt in WPts]: gp in gps];
   rel_gp_idx := [i : i in [1..#gps]| exists{t: t in real_root_index|gps[i][t] eq -1}];
   if rel_gp_idx eq [] then return ctpvec; end if;

// compute a local point 
    sortseq := real_root_index;
    Sort(~sortseq , func<s1,s2| Real(WPts[s1])-Real(WPts[s2])>);
    newwpts := [WPts[i]: i in sortseq];
    newg := [g[s]: s in sortseq];
    signchanges := [i : i in [1..#real_root_index-1]| Real(newg[i]*newg[i+1]) lt 0];
    pts := [Min(Real(newwpts[i]+1), Real(newwpts[i]+newwpts[i+1])/2) : i in signchanges];
    pts := [[pt, SquareRoot(Evaluate(f, pt))]: pt in pts];
    dega := #pts;
    M := Transpose(Matrix(C, dega, dega, [[x[1]^(dega-i) : i in [1..dega]]: x in pts]));
    vec := Vector(C, dega, [x[2] : x in pts]);
    coef := Solution(M,vec); temp := ElementToSequence(coef); coef := [temp[dega-i]: i in [0.. dega -1]];
    mumpol2 := Ct!Polynomial(coef); mumpol1 := &*[Ct.1-x[1]: x in pts];
    assert forall{t: t in real_root_index|
      Real((-1)^dega*Evaluate(mumpol1,WPts[t]))/Real(g[t]) gt 0};
    print "local points:", [mumpol1,mumpol2];

// compute 1/2 of local point, adjust it and compute function for principal divisor
    flag , Pv := IsDouble_inf(Jacobian(curC), [mumpol1,mumpol2]); //check this J is defined over a number field 
    ca := ElementToSequence(Pv[1]); ca[Degree(Pv[1])+1] := C!1; Pv[1]:= Ct!Polynomial(ca);
    assert flag eq true;

//adjust chi_val 
    print "adjusting real Pv";
    chi_val := SetToSequence({i : i in [1..l]} diff SequenceToSet(chi_val));
    bool, fctns, Pv := adjustPv(Pv, chi_val, WPts, f);
    assert bool eq true;
    print "chi_val:", chi_val;
// Base change of local matrix to complex numbers    
    
    //recall that we have skipped the first element so the size of gps is #good_elts-1
    //hence we are starting ap from a and not from a+1.
    rel_gp_idx := Sort(rel_gp_idx);
    for ap in rel_gp_idx do 
      gp := gps[ap];
      for i in real_root_index do 
        if gp[i] eq -1 then
        val := R!0;
        //contribution from Pv cup_2 x-WPts[i]
        val := -Argument((-1)^(Degree(Pv[1]))*Evaluate(Pv[1], WPts[i]));
        //Change the following because comp_epsilon assumes J and WPts defined over a
        //number field
        eps_val, pseq, sval := comp_epsilon(SequenceToSet(chi_val), i, -1, curS, WPts_nf);
        eps_val := Argument(C!eps_val);
        if pseq ne [] then 
        eps_val := eps_val + (&+[x[3]*Argument(Pgv[x[1]][x[2]]): x in pseq]); 
        end if;
        eps_val := eps_val + Argument(complex_mor(sval));
      
        for j in [1..#fctns] do
          if chi_val[j] eq i then 
  /* In this case we have fctn[i] is (x-e_i)a_old/(y+g). Therefore,
     fctn*tp^(-1) y*a_old/(g+y) := a_old/(1+g/y). Note that g is obtained by solving
     chinese remaindering of [0, b_old] mod [x-e_i, a_old]. Therefore, x-e_i is a
     factor of g. This implies that g/y(T_i)=0. Hence the pairing is a_old(e_i). 
  */   
            val := val + Argument(Evaluate(Evaluate(fctns[i][1], [Ct.1,0]) div (Ct.1-WPts[i]), WPts[i]));  
          else 
  /*else nothing vanishes on T_i by construction and so we just Numerator and denominator.*/ 
            val := val + Argument(Evaluate(fctns[j][1], [WPts[i],0]))
                   - Argument(Evaluate(fctns[j][2], [WPts[i],0]));
          end if;
        end for;
        val := val - eps_val; val := PolarToComplex(1,val); assert almost_real(val);
        printf "local contribution at ap = %o is :============================== %o", ap, Sign(Real(val));
        print "";
        ctpvec[ap]:= ctpvec[ap]*Sign(Real(val));
        end if;
      end for;
    end for;
  return ctpvec;
end function;  
