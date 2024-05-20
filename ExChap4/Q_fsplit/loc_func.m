/* Functions in this file: 
            * 1) locPolEq:
            * 2) eucXGCD
            * 3) locCR
            * 4) findlocPt
            * 5) H90pAdic
            * 6) pAdicHilbSym
            * 7) locAdd
            * 8) Comp1Cocyc
            * 9) CompDiagVal
*/


locEltEq := function(a,b)
  P := Parent(a); pi := UniformizingElement(P); OP := IntegerRing(P);
  if a eq P!0 then temp := a; a := b; b := temp; end if;
  if a eq P!0 then return true; end if;
  a := a-b;
  vala := Valuation(a);
  //technical detail otherwise prec will be computed as 0
  if Precision(a) in {0,1} then 
    prec := Min([vala,Precision(P)]);
  else prec := Precision(a);
  end if;
  
  //Precision(a); vala; Precision(P);
  if vala lt 0 then a := a/(pi^vala); end if; 
  try
    PR := quo<OP| pi^(prec-2)>; return (PR!a eq 0); 
  catch e
    print a, vala, Precision(a),Precision(P), prec;
    error "error in locPolEq";
  end try;
end function;





locPolEq := function(a,b) //input univariate polynomials a and b over a padic field
    P := Parent(a);
    if a eq P!0 then temp := a; a := b; b := temp; end if;
    if a eq P!0 then return true; end if;
    k := BaseRing(P); Ok := IntegerRing(k);
    pi := UniformizingElement(k);
    a := a-b; 
    return forall{t : t in Coefficients(a)| locEltEq(t, Parent(t)!0)};
end function;


//using for computing gcd over reals
realXGCD := function(a,b)
  P := Parent(a);
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










//locCR is the modified version of the Chinese Remainder theorem present in
///usr/local/magma/package/Ring/RngLoc/new.m. This will work for polynomials
//defined over local fields. The changes include: Instead of checking for gcd eq
//1 we check if Deg(gcd) eq 0. Removal of assertion g eq c* Mod + d* Lm[i]
//because of obvious failure of this assertion due to change of precision during
//computation of XGCD.


locCR := function(La, Lm)
  PR := Parent(Lm[1]);
  Mod := Lm[1];
  CR := La[1];

  for i := 2 to #Lm do
    g,c,d := XGCD(Mod,Lm[i]); //Attention !!!! Loss of precission
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


  



//TILL HERE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//
//
//
//Compute p-adic hilbert90 element;
H90pAdic := function(m, cocyc)
  k := Codomain(cocyc);
  if #Domain(cocyc) eq 1 then return k!1; end if;
  d := Degree(k); 
  H := Domain(cocyc);
  baselts := [k.1^i : i in [0..d-1]];
  ret_val := k!0;
  for b in baselts do 
      phi_b := &+[cocyc(h)*(m(h)(b)): h in H];
      if phi_b ne 0 then ret_val := 1/phi_b; end if;
  end for; 
  assert forall{t : t in Domain(cocyc)| locEltEq(m(t)(ret_val),ret_val*cocyc(t))};
  return ret_val;
end function; 



//compute p-adic classical hilbert's symbol
/*Comment : prec is chosen as constant 10 for computation. Should be changed while
 * generalizing to the case when the defining polynomial does not split, in which case the
 * input elements a and b might be elements of an extension of a padic field.
 */ 
pAdicHilbSym := function(a,b)
  k := Parent(a);
  f := DefiningPolynomial(k);
  Qv := BaseRing(Parent(f)); Zv := IntegerRing(Qv);
  prec := SuggestedPrecision(f)+5;
  pi := UniformizingElement(k);
  vala := Valuation(a); valb := Valuation(b);
  a := pi^(vala mod 2)* (a/pi^vala); b := pi^(valb mod 2)*(b/pi^valb);
  //fbara := MinimalPolynomial(a); fbarb := MinimalPolynomial(b);
  //etsa := ElementToSequence(fbara); etsb := ElementToSequence(b);
  res := quo<Zv | UniformizingElement(Zv)^prec>;
  fbar := Polynomial([Integers()!(res!t): t in ElementToSequence(f)]);
  assert IsIrreducible(fbar);
  K := ext<Rationals()|fbar>;
  OK := MaximalOrder(K); vdcmp := Decomposition(OK, Prime(Qv));
  //print vdcmp[1][1];
  assert #vdcmp eq 1;
  etsa := ElementToSequence(a); etsb := ElementToSequence(b); 
  etsa := [Integers()!(res!e) : e in etsa]; etsb := [Integers()!(res!e) : e in etsb];
  abar := K!etsa; bbar := K!etsb;
  if Degree(K) eq 1 then return HilbertSymbol(abar, bbar, Prime(Qv)); end if;// this seems to be 
                                                                             // because of
                                                                             // a bug in  magma.
  return HilbertSymbol(abar, bbar, vdcmp[1][1]);
  
  /*prec := Min(Precision(etsa[1]), Precision(etsb[1]));
  Zv := BaseRing(Parent(fbara));
  res := quo<Zv| UniformizingElement(Zv)^prec>; 
    fb := Polynomial([Integers()!(res!t): t in etsb]);
  K := CompositeFields(ext<Rationals()|fa>, ext<Rationals()|fb>);
  f := DefiningPolynomial(K);
  prec := RamificationIndex(k)*10;
  res := quo<IntegerRing(k)| pi^prec>;
  a := Integers()!(res!a); b := Integers()!(res!b);
  return HilbertSymbol(a,b,Prime(k));
  */
end function;




//function to add two points on the Jacobian of an odd degree hyperelliptic curve with one
//point coming from the curve.  

//TODO : Change the function to include two points on Jacobian represented by (a1,b1) and
//(a2,b2) such that deg(a1a2) <= g+1.
//
//The return value currently is bool, [pol1, pol2, deg(pol1)], pol3; such that
//P1 + P2 + [pol1, -pol2, deg(pol1)] = div(y-pol3); in case deg(P1[1]) + deg(P[2])<= g
//then bool is false denoting that there is no pol3 returned, otherwise bool is set to
//true and pol3 is assigned a non-null value. 

Genlocadd := function(P1, P2, f)
  genus := Degree(f) div 2;
  a1 := P1[1]; a2 := P2[1]; b1 := P1[2]; b2 := P2[2];
  d := Gcd(a1, a2); d := Gcd(d, b1+b2); a := a1*a2 div d^2; 
  b := locCR([b1, b2], [a1 div d, a2 div d]); assert locPolEq(f mod a, b^2 mod a);
  while Degree(a) gt genus do 
    c := (f-b^2) div a; c := c/LeadingCoefficient(c);
    a :=c ; b := -b mod a;
  end while;
  return [a,b];
end function;



locAdd := function(P1, P2, f, flag, approx)
  //print "starting locAdd with : ", P1, P2, f;
  if Degree(P2[1]) eq 0 then return false, P1, _; end if;
  g := Degree(f) div 2;
  if Degree(P1[1]) eq 0 then return false, P2, _; end if; //when P1 or P2 is identity.
  d1 := Degree(P1[1]); d2 := Degree(P2[1]);
  if d1 + d2 gt g+1 then return false, Genlocadd(P1, P2, f), _ ; end if;
  if P2[2] eq 0 then temp := P1; P1 := P2; P2 := temp; end if;
  //swap so that P1 is the two torsion element.
  if P2[2] eq 0 then if d1+d2 lt g+1 then return false, [P1[1]*P2[1], 0], _;
    else return true, [f div P1[1]*P2[1], 0], 0; end if; 
  end if; 
  a1 := P1[1]; b1 := P1[2]; a2 := P2[1]; b2 := P2[2]; kt := Parent(a1);
  if flag then assert locPolEq(Gcd(a1,a2), kt!1); end if;
  
  //currently implemented for adding points on the Jacobian with disjoint divisor
  //representations.
  if flag and (locPolEq(b1, Parent(b1)!0) eq false) then newb := locCR([b1, b2], [a1, a2]);
  elif (flag eq false) and (b1 ne Parent(b1)!0) then 
  if approx then newb := realCR([b1, b2], [a1, a2]); else newb := ChineseRemainderTheorem([b1, b2], [a1, a2]);
  end if;
  elif flag then //print "adding a Weierstrass point";
    gcd, c, d := XGCD(a1,a2); newb := b2*c*a1 mod (a1*a2);
    //print gcd, c,d;
    //print "newb mod a1", newb mod a1;
    //print "newb mod a2", newb mod a2;

    assert locPolEq(c*a1+d*a2, gcd);
  else 
    if approx then 
    gcd, c, d := realXGCD(a1,a2); newb := b2*c*a1 mod (a1*a2);
    else 
    gcd, c, d := XGCD(a1,a2); newb := b2*c*a1 mod (a1*a2);
    end if;
  end if; 
//a1*newb + qa2(x) = b2(x) for some q in k[x], there are c and d such that c*a1+d*a2=1,
//hence we have newb can be chosen to be b2*c and we return a1*newb mod a1*a2.
  if d1 + d2 lt g+1 then return false, [a1*a2, newb], _; end if;
  pol := f-newb^2; 
  
  
    if flag then 
    try 
      assert locPolEq(pol mod (a1*a2), Parent(f)!0);
    catch e
      print "pol mod (a1*a2) equals:", pol mod (a1*a2);
    end try;
    end if;
  newa := pol div (a1*a2);
  //assert correctfunc(P1, P2, [newa, newb mod newa], newb);
  if flag then 
  try
    assert locPolEq(f-newb^2, a1*a2*newa);
  catch e 
    print "f-newb^2, a1*a2*newa:", pol, a1*a2*newa, pol-a1*a2*newa;
  end try;
  end if;
  return true, [newa, -newb mod newa], newb;
end function;


//Input : SqSet is a set which has elements which are sets of tuples <PtCrv, <x-TmapTup>>
MemberUptoSq := function(SqSet, e)
  l := #e;
  if forall{t: t in [1..l]| IsSquare(e[t])} then return true, {}; end if;
  if #SqSet eq 1 then return false,_; end if;
  Exclude(~SqSet, { });
  for element in SqSet do 
    eltsqval := <&*[pts[2][t] : pts in element]: t in [1..l]>; 
    if forall{t : t in [1..l]| IsSquare(eltsqval[t]*e[t])} then return true, element; end if;
  end for;
  return false, _;
end function;




findlocPt := function(f, g, WPts, rand_hits)
  kt := Parent(f); 
  k := BaseRing(kt);
  l := #WPts;
  genus := l div 2;
  Ok := IntegerRing(k);
  pi := UniformizingElement(k);
  g := <pi^(Valuation(d) mod 2)* (d/(pi^Valuation(d))): d in g>;
  if forall{t : t in g | IsSquare(t)} then return true, [kt!1, kt!0]; end if;
  nontriv_ind := [i : i in [1..l]| Valuation(g[i]) ne 0]; 
  SqSet := {};
  subSqSet := Subsets(SqSet);  
  
  // Search for a point on the curve first.
  
  newJcPt := [kt!1,kt!0];
  for i in [1..rand_hits] do   
    if i mod 2 eq 0 then
      if nontriv_ind ne [] then x := WPts[nontriv_ind[1]] + pi*(k!(Random(Ok))); 
      else x := k!(Random(Ok)); 
      end if;
    else 
      x := k!(Random(Ok));
    end if;
//Since g is not in the image of 2-torsion, hence skip if x matches a Weierstrass point
      if exists{t: t in WPts| locEltEq(x, t) eq true} then continue; end if;
    // if f(x) is not a square in Qv then this x cannot correspond to any local point on
    // curve, therefore skip the iteration.
      if not IsSquare(Evaluate(f,x)) then continue; 
      else
        flag, seq := MemberUptoSq(subSqSet, <x-WPts[t]: t in [1..l]>);  
        if flag then continue;
        else 
          Include(~SqSet, <[kt.1-kt!x, kt!SquareRoot(Evaluate(f, x))], <x-WPts[t]: t in [1..l]>>);
          subSqSet := Subsets(SqSet);
          flag, seq := MemberUptoSq(subSqSet, g);
          if flag then 
            for t in seq do bool, newJcPt, fctn := locAdd([t[1][1], t[1][2]], newJcPt,f, true, false);
            end for;
            assert forall{t: t in [1..l]| IsSquare((-1)^(Degree(newJcPt[1]))*Evaluate(newJcPt[1],WPts[t])/g[t])};
            return true, newJcPt;
          end if; 
        end if;
      end if;
    end for;

print "No point found on the curve. Trying points on Jacobian now!";
  

  newJcPt := [kt!1,kt!0];
  for i in [1..rand_hits] do 
    coef_a := [k!Random(Ok): i in [1..genus]];
    a := kt.1^genus+kt!Polynomial(coef_a);
    d := Gcd(a, Derivative(a)); 
    if not locPolEq(Gcd(a, f), kt!1) then continue; end if;
    while Degree(d) ne 0 do 
      a := a div d; d := Gcd(a, Derivative(a));
    end while;
    flag, seq := MemberUptoSq(subSqSet,<(-1)^(Degree(a))*Evaluate(a, pt): pt in WPts>);
    if flag then continue;
    else
      fctrs_a := [ai[1]: ai in Factorization(a)];
      mod_a := <LocalField(k, ai): ai in fctrs_a>; //by assumption all factors of 
                                                    //a have multiplicity 1 
      m := <hom<kt->mod_ai | mod_ai.1> : mod_ai in mod_a>;
      f_mod_a := <mi(f): mi in m>;
      if not forall{ t : t in f_mod_a | IsSquare(t) eq true} then continue; end if;
      bmod_ai := [Polynomial(ElementToSequence(SquareRoot(fi))) : fi in f_mod_a];
      b := locCR(bmod_ai, fctrs_a);
      assert locPolEq(b^2 mod a,  f mod a);
      Include(~SqSet,<[a, b], <(-1)^(Degree(a))*Evaluate(a, pt) : pt in WPts>>);
      subSqSet := Subsets(SqSet);
      flag, seq := MemberUptoSq(subSqSet, g);
      if flag then  
        for t in seq do 
          bool, newJcPt, fctn := locAdd([t[1][1], t[1][2]], newJcPt,f, true, false);
        end for;
        return true, newJcPt;
      else 
        continue;
      end if;
    end if;
  end for;
  return false, _;
 /*
    if not forall{t: t in [1..l] | IsSquare((x-WPts[t])/g[t])} then
      flag := MemberUptoSq(SqSet, <x-WPts[t]: t in [1..l]>);
      if flag then continue; else
      if not locPolEq(Gcd(Qvt.1-x, newJcPt[1]), Qvt!1) then continue; end if;
      flag, newJcPt, h := locAdd([Qvt.1-x, SquareRoot(Evaluate(f,x))],newJcPt ,f);

      prin  t newJcPt; 
      if Degree(newJcPt[1]) gt 1 and forall{t: t in [1..l] | 
        IsSquare((-1)^(Degree(newJcPt[1]))*Evaluate(newJcPt[1], WPts[t])/g[t])} then
        a := newJcPt[1]; b := newJcPt[2];
        print newJcPt;
        if not locPolEq(Gcd(f,a), Qvt!1) then print "gcd issue"; continue; end if; //find a local point which does 
                                                  //not have a Weierstrass
                                                  //point in the support.
      fctrs_a := [ai[1]: ai in Factorization(a)];
      mod_a := <LocalField(Qv, ai): ai in fctrs_a>; //by assumption all factors of 
                                                    //a have multiplicity 1 
      m := <hom<Qvt->mod_ai | mod_ai.1> : mod_ai in mod_a>;
      f_mod_a := <mi(f): mi in m>;
      if not forall{ t : t in f_mod_a | IsSquare(t) eq true} then continue; end if;
      bmod_ai := [Polynomial(ElementToSequence(SquareRoot(fi))) : fi in f_mod_a];
      b := locCR(bmod_ai, fctrs_a);
      assert locPolEq(b^2 mod a,  f mod a);
      return [a,b];
      else continue;
      end if;
    else return [Qvt.1-x, SquareRoot(Evaluate(f, x))];
    end if;
  end for;
  */
    //if not forall{d: d in g | IsEven(Valuation(d))} then pi := UniformizingElement(Qv); end if;
  //ffact := [e[1]: e in Factorization(f)];
   /* u := [Qv!Random(Zv): i in [1..l]];
    M := Matrix(Qv, genus, genus, [[WPts[j]^(genus-i): i in [1..genus]]: j in [1..genus]]);
    M := Transpose(M);
    val := Vector(Qv,[(-1)^genus*g[t]*u[t]^2-WPts[t]^genus: t in [1..genus]]);
    coef_a, N := Solution(M, val);
    a := locCR([g[t]*u[t]^2 : t in [1..l]], ffact); 
   */
end function;





CompMinRep := function(n, d, f, flag)
  P := Parent(n);
  x := P.1; y := P.2;
  Px := Parent(f); h := hom<P -> Px | [Px.1,0]>;
  emb := hom<Px -> P | x>;
  conj_d := Evaluate(d, [x,-y]);
  d := d * conj_d;
  n := n * conj_d;
  cfn := Coefficients(n, y);
  cfd := Coefficients(d,y); 
  red_n := &+[y^((j-1) mod 2)*cfn[j]* emb(f)^((j-1) div 2): j in [1..#cfn]];
  red_d := &+[y^((j-1) mod 2)*cfd[j]* emb(f)^((j-1) div 2): j in [1..#cfd]];
  cfn := Coefficients(red_n,y);
  cfd := Coefficients(red_d, y);
  assert #cfn eq 2;
  //assert #cfd eq 1;
  return <red_n, h(red_d)>;
  /*
  if flag then
  d1 := Gcd(h(cfn[1]), h(red_d)); d2 := Gcd(h(cfn[2]), h(red_d));
  else 
  d1 := realGCD(h(cfn[1]), h(red_d)); d2 := realGCD(h(cfn[2]), h(red_d));
  end if;
  n1 := h(cfn[1]) div d1; d1 := h(cfd) div d1; n2 := h(cfn[2]) div d2; d2 := h(cfd) div d2;
  N := emb(n1*d2)+y*emb(n2*d1); D := d1*d2;
  return <N, D>;
  */
end function;


//given a function g on the coordinate field of the hyperelliptic curve and a point Pt on the
//hyperelliptic curve, compute the evaluation of g on Pt.
EvalFuncPairing1 := function(g, Pt,f, flag)
  //g is given as [N,D] i.e. a pair of polynomials representing numerator and denominator. 
  //N is of the form a + yb for two univariate polynomials a and b.
  //D is a univariate polynomial. 
  //Furthermore g is guaranteed to be a unit in the local ring at Pt.
  Px := Parent(f);
  l := Degree(f);
  N := g[1]; D:= g[2]; 
  P := Parent(N);
  pi := hom<P-> Px| [Px.1,0]>; emb := hom<Px-> P | P.1>;
  a := pi(Coefficient(N, P.2, 0)); b := pi(Coefficient(N,P.2,1));
  if Pt eq [1,0,0] then
    assert 2*Degree(D) eq  Max(2*Degree(b)+l, 2*Degree(a));
    lcfd := LeadingCoefficient(D);
    if 2*Degree(b)+l gt 2*Degree(a) then lcfn := LeadingCoefficient(b);
    else lcfn := LeadingCoefficient(a); //note that since degrees in comparison have different parity so the case when they are equal will not occur.
    end if;
    
    return lcfn/lcfd;
  end if;  
  Pt := ElementToSequence(Pt);
  if flag and (Pt[2] eq Parent(Pt[1])!0) then //d := Gcd(a, D); 
    //a := a div d; D := D div d; 
    
    return Evaluate(emb(a), [Pt[1],0])/Evaluate(emb(D), [Pt[1],0]);
  elif (flag eq false) and (Pt[2] eq Parent(Pt[1])!0) then 
    d := GCD(a, D); a := a div d; D := D div d; 
    
  return Evaluate(emb(a), [Pt[1],0])/Evaluate(emb(D), [Pt[1],0]);
  //when evaluating at 2-torsion point. 
  
  else
    if locPolEq(P!Evaluate(emb(D), [Pt[1],0]),P!0) then
      if flag then
        d := Gcd(a^2-f*b^2, D); g1 := (a^2-f*b^2) div d; g2 := D div d;
      else 
        d := GCD(a^2-f*b^2, D); g1 := (a^2-f*b^2) div d; g2 := D div d;
      end if;
      
      return Evaluate(Evaluate(N, [P.1, -P.2]),[Pt[1], Pt[2]])^(-1)*
      Evaluate(g1,Pt[1])/Evaluate(g2, Pt[1]);
    else 
    
    return Evaluate(N,[Pt[1],Pt[2]])/Evaluate(emb(D),[Pt[1],0]);  
    end if;
  end if;
end function;


IsPrincipalDivisor := function(c,Pv,Pvs,f)
  l := Degree(f); genus := l div 2;  
                                  // if chi_val is full i.e. eq zero then sigma is trivial
                                  // there is no action on Pv i.e. Pvs eq Pv and divisor 
                                  // c + Pv -Pvs= 0 = div(1);
  //c is a set of Weierstrass points, Pv is a point given by [a,b,d], and Pvs is given by
  //[as, bs,d] in mumford rep is the point Pv acted by sigma. 
  Kt := Parent(f);
  deg := Degree(Pv[1]);
  P := PolynomialRing(BaseRing(Kt),2);
  if #c eq l then return true, [P!1, P!1]; end if;
  x := P.1 ; y := P.2; emb := hom<Kt->P| x>; pi := hom<P -> Kt| [Kt.1, 0]>; 
  f_old :=[];
  cnew := c; prod := Kt!1; 
  while cnew ne [] do if Degree(prod) + deg eq genus then break; end if;
    prod := prod * (Kt.1 - cnew[1]);
    Remove(cnew,1);
  end while;
  bool, newPt, g := locAdd([prod, Kt!0], Pv, f, true, false);
  assert bool eq false; 
  //print "first new point : ",newPt; 
  if cnew eq [] and 
  forall{t: t in [locPolEq(newPt[x], Pvs[x]): x in [1..2]]| t eq true} then 
  //note that at some here in the above line I have used the fact that P=Q iff bar(P)=bar(Q).
    return true, [[P!1,P!1]]; //Need to correct it for local equalities
  elif cnew eq [] then 
    return false, _;
  end if;
  assert Degree(newPt[1]) eq genus;
  g := P!1;
  prod := Kt!1;

  //print "starting cnew: ", cnew;
  for j in cnew do 
  oldPt := newPt;
  //print "size of c: ", cnew;
  flag, newPt, g := locAdd([Kt.1-Kt!j, Kt!0], newPt, f, true, false);
  //print "exited locAdd with return flag : ", flag;
  assert flag eq true;
  g := y + emb(g);
  Append(~f_old,[(x-j)*emb(oldPt[1]),g]);
  end for;
 // return newPt;
  if forall{t: t in [locPolEq(newPt[x], Pvs[x]): x in [1..2]]| t eq true} then 
    return true, f_old; //Need to correct it for local equalities
  end if;
  return false, _;
end function;


Comp1Cocyc := function(m, H, WPts, mumrep, i, f, KtoKv, sqrtg, Pg, C)
  a := mumrep[1]; b := mumrep[2]; deg := Degree(mumrep[1]);
  Kt := Parent(a);
  l := #WPts;
  genus := l div 2;
  WPtsv := [KtoKv(pt): pt in WPts];
  //still need to interpret this in the field of functions over C
  //Da := Divisor(a);
  //Da := &+[Valuation(P, D)*P : P in Support(Da)| P[2] eq Evaluate(b, P[1])];
  //
  //We need to compute the Matrices Mij and Cij. For genus 2 it is easy but for higher
  //genus one needs to take a recursive approach to find the function f_sigma such that 
  //div(f_sig)= a(sig)+sig b- b. 

  zero := SequenceToSet([1..l]);
  H_sqrtg :=<<h,[locEltEq(m(h)(d), d): d in sqrtg]>: h in H| h ne Identity(H)>;
  //print "H_sqrtg : ", H_sqrtg;
  chi_val := [[*c[1], Indices(c[2], true)*] : c in H_sqrtg];
  //print "chi_val : ", chi_val;
  //chi_val := [[c: c in chi_val | #c[2] eq 2*i]: i in [1.. l div 2]];
  //removing empty arrays
  //chi_val := [c: c in chi_val| c ne []];
  //print "sorted chi_val :", chi_val;
  map_tups := [<Identity(H), BaseRing(Kt)!1>]; 
  //inf := Divisor([<Place(C![1,0,0]),1>]);

  for c in chi_val do
    mumrepc :=[Kt!Polynomial([m(c[1])(j): j in ElementToSequence(a)]),
              Kt!Polynomial([m(c[1])(j): j in ElementToSequence(b)])];
    flag, fctn := IsPrincipalDivisor([WPtsv[j]: j in c[2]], mumrep, mumrepc, f);
    assert flag eq true;
    //return g;
    //g := CompMinRep(g[1], g[2], f);
    //assert forall{t: t in c[2]| locEltEq(Evaluate(g[1],[WPts[t],0]), BaseRing(Qvt)!0)};
    P := Parent(fctn[1][1]);
    x := P.1 ; y := P.2; embed := hom<Kt->P| x>; pi := hom<P -> Kt| [Kt.1, 0]>; 
    val := BaseRing(Kt)!1;
      //print "val eq : ", val;
    assert not locEltEq(val, BaseRing(Kt)!0);
      //if pt[1] eq [1,0,0] then
        //OMITTING COMPUTING AT INFINITY as every element in the sequence of functions g
        //has been obtained by adding exactly one point. 
        //print "at infinity";
        //minrep := CompMinRep(g[1]*x^((#c[2])*genus),g[2]*y^(#c[2]),f, true);
        //minrep;
        //return minrep;
        //val := val*EvalFuncPairing1(minrep,pt[1],f, true)^(pt[2]);
        //elif pt[1][1] in [WPts[j]: j in c[2]] and pt[1][3] ne 0 then
        //print "at 2-torsion inside c";
        //val := val*EvalFuncPairing1(CompMinRep(g[1]*y, g[2]*(x-WPts[i]),f, true),
        //    pt[1], f, true)^(pt[2]);  
        //print "at 2-torsion ouside c";
    if #c[2] eq #fctn then
    for z in [1..#c[2]] do 
      if c[2][z] eq i then 
        val *:= Evaluate(pi(fctn[z][1]) div (Kt.1-WPtsv[i]), WPtsv[i]);
      else 
        val := val* Evaluate(fctn[z][1], [WPtsv[i], 0])/Evaluate(fctn[z][2],[WPtsv[i], 0]);
      end if;
    end for;     

    else

    end if;
      // Ti + newPt + Q := div(y-g)
        
         
// add the points from the WP corresponding to chi value c such that deg of the divisor
// represented by P and the WP's is g+1 and then keep adding extra points sequentially. 


    //a_c := Divisor([<Place(C![WPts[j],0]),1>: j in c[2]]);// divisor of frac a at c
    //a_c := a_c - Degree(a_c)*inf;
        //compute partial of the degree 2 (generically) divisor representing the
        //point in the Mumford reps
    
    //compute the value of epsilon
    eps_val, pseq, sval := comp_epsilon(SequenceToSet(c[2]), i, 1,C, WPts); 
 
    //print "comp_epsilon returned:", eps_val, pseq, sseq;
    if pseq ne [] then
    eps_val := eps_val *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq]); end if;
    eps_val := eps_val * KtoKv(sval);
    //print Norm(eps_val);
    val := val/eps_val;
    Append(~map_tups,<c[1], val>);
  end for;
    //construct the cocycle using the map represented by map_tups
  cocyc := map<H-> Domain(m(H.1))| map_tups>;
  return cocyc; 
end function;







CompDiagVal := function(Pv, sig, KtoKv, sqrtg, i, WPts, Pg, f, C)
  a := Pv[1]; b := Pv[2]; deg := Degree(a); l := #WPts; genus := l div 2;
  zero := [1..l];
  sqrt := <KtoKv(sq): sq in sqrtg>;
  chi_val := Indices([locEltEq(sig(d),d): d in sqrt],true);
  k := Domain(sig);
  //print "chi_val : ", chi_val;
  eps_val, pseq, sval := comp_epsilon(SequenceToSet(chi_val), i, -1, C, WPts);
  //print "comp_epsilon returned : ", eps_val, pseq, sseq;
  eps_val := k!eps_val;
  if pseq ne [] then  
  eps_val := eps_val *(&*[Pg[x[1]][x[2]]^(x[3]): x in pseq]); end if;
  eps_val := eps_val * KtoKv(sval);
   //need to make this step more rigourous
  a := Parent(f)!Polynomial([elt<k|ElementToSequence(c)>: c in ElementToSequence(a)]);
  WPts := [KtoKv(pt) : pt in WPts]; 

  if chi_val eq zero then
    if locEltEq(Evaluate(a, WPts[i]),0) then 
    val := k!1;
    rem := a div (Parent(a).1- WPts[i]);
      if Degree(rem) ne 0 then val := -Evaluate(rem, WPts[i]); end if; 
      val := val* (&*[WPts[i]-WPts[t]: t in [1..l]| t ne i]);
      val := elt<Parent(eps_val)| ElementToSequence(val)>; return val/eps_val;
    else
      val := ((-1)^deg)* (Evaluate(a, WPts[i]))^(-1);
      val := elt<Parent(eps_val)| ElementToSequence(val)>; return val/eps_val;
    end if;
  end if;
      
      


  b := Parent(f)!Polynomial([elt<k|ElementToSequence(c)>: c in ElementToSequence(b)]);
  Pv := [a,b];

  assert locEltEq(eps_val, k!0) eq false;
  //print "IsUnit eps_val", Valuation(eps_val);
  /*if chi_val eq zero then 
    val := ((-1)^(deg)* Evaluate(a, WPts[i]))^(-1); 
    val := elt<Parent(eps_val)| ElementToSequence(val)>; return val/eps_val;
  else
  */
    kt := Parent(f);
    Pvs := [kt!Polynomial([sig(c) : c in ElementToSequence(a)]), 
          kt!Polynomial([sig(c): c in ElementToSequence(b)])];
    flag, fctn := IsPrincipalDivisor([WPts[x]: x in chi_val], Pv, Pvs,f);
    assert flag eq true;
    P := Parent(fctn[1][1]);
    x := P.1 ; y := P.2; embed := hom<kt->P| x>; pi := hom<P -> kt| [kt.1, 0]>; 
    val := BaseRing(kt)!1;
    //evaluating g at Ti
    if #chi_val eq #fctn then
    for z in [1..#chi_val] do 
      if chi_val[z] eq i then 
        val := val *Evaluate(pi(fctn[z][1]) div (kt.1-WPts[i]), WPts[i]);
      else 
        val := val * Evaluate(fctn[z][1], [WPts[i], 0])/Evaluate(fctn[z][2], [WPts[i], 0]);
      end if;
    end for;
    
    else
    // do something else
    end if;
     //if i in chi_val then 
         ////print "Ti in chi_val";
         //val := EvalFuncPairing1(CompMinRep(g[1]*y, g[2]*(x-WPts[i]),f, true),[WPts[i], 0, 1], f, true);
     //else 
         //val := EvalFuncPairing1(CompMinRep(g[1], g[2], f, true), [WPts[i], 0, 1], f, true);
     //end if;
     ////evaluating g at infty
    assert locEltEq(val, k!0) eq false;
    //val := val * (EvalFuncPairing1(CompMinRep(g[1]*x^((#chi_val)*genus),
    //             g[2]*y^(#chi_val),f, true), [1, 0, 0], f,true))^(-1);
    //Valuation(val);
    val := val * ((-1)^(deg)*Evaluate(a, WPts[i]))^(-1); //contribution from b cup2 frak(a)'.
    //Valuation(val);
    val := elt<Parent(eps_val)| ElementToSequence(val)>; 
    assert locEltEq(val, k!0) eq false;
    //Valuation(val/eps_val);
    return val/eps_val; 
end function;





IsRealPrincipalDivisor := function(c,Pv, f, approx)
  l := Degree(f); genus := l div 2;  
                                  // if chi_val is full i.e. eq zero then sigma is trivial
                                  // there is no action on Pv i.e. Pvs eq Pv and divisor 
                                  // c + Pv -Pvs= 0 = div(1);
  //c is a set of Weierstrass points, Pv is a point given by [a,b,d], and Pvs is given by
  //[as, bs,d] in mumford rep is the point Pv acted by sigma. 
  Kt := Parent(f);
  deg := Degree(Pv[1]);
  P := PolynomialRing(BaseRing(Kt),2);
  if #c eq l then return true, [P!1, P!1]; end if;
  x := P.1 ; y := P.2; emb := hom<Kt->P| x>; pi := hom<P -> Kt| [Kt.1, 0]>; 
  f_old :=[];
  cnew := c; prod := Kt!1; 
  while cnew ne [] do if Degree(prod) + deg eq genus then break; end if;
    prod := prod * (Kt.1 - cnew[1]);
    Remove(~cnew, 1);
  end while;
  if approx then 
  bool, newPt, g := locAdd([prod, Kt!0], Pv, f, false, true);
  else 
  bool, newPt, g := locAdd([prod, Kt!0], Pv, f, false, false);
  end if;
  assert bool eq false; 
  //print "first new point : ",newPt; 
  if cnew eq [] then return false, _;
  //forall{t: t in [locPolEq(newPt[x], Pvs[x]): x in [1..2]]| t eq true} then 
  //note that at some here in the above line I have used the fact that P=Q iff bar(P)=bar(Q).
  //return false, [f_old[1]*g, f_old[2]]; //Need to correct it for local equalities
  //elif cnew eq {} then 
  //  return false, _;
  end if;
  assert Degree(newPt[1]) eq genus;
  g := P!1;
  prod := Kt!1;

  //print "starting cnew: ", cnew;
  for j in cnew do 
  //print "size of c: ", cnew;
  oldPt := newPt;
  if approx then 
  flag, newPt, g := locAdd([Kt.1-j, Kt!0], newPt, f, false, true);
  else
  flag, newPt, g := locAdd([Kt.1-j, Kt!0], newPt, f, false, false);
  end if;
  //print "exited locAdd with return flag : ", flag;
  assert flag eq true;
  g := y + emb(g);
  Append(~f_old, [(x-j)*emb(oldPt[1]), g]);
  end for;
  //print "how far is newPt from Pvs:", [newPt[x]-Pvs[x]: x in [1..2]]; 
  return true, f_old; //Need to correct it for local equalities
end function;




//Part of the code form previously existing global_computation.m which was computing the
//matrices Mv and Cv


/*

for k :=1 to l do
			Mv[k][k]:=(y1v*(x2v-roots[k])-y2v*(x1v- roots[k]))/((x1v-x2v)*(x1v-roots[k])*(x2v-roots[k]));
			for j:=k+1 to  l do
				Mv[k][j] :=(y1v*(x2v-roots[k])*(x2v-roots[j])-y2v*(x1v- roots[k])*(x1v-roots[j]))/((x1v-x2v)*(x1v-roots[k])*(x2v-roots[k])*(x1v-roots[j])*(x2v-roots[j]));
				M[j][k] := Cv[k][j];
			end for;
		end for;
		for k :=1 to l do
			Cv[k][k]:=(-y1v*x2v*(x2v-roots[k])+y2v*x1v*(x1v- roots[k]))/((x1v-x2v)*(x1v-roots[k])*(x2v-roots[k]));
			for j:=k+1 to  l do
				Cv[k][j] :=(-y1v*x2v*(x2v-roots[k])*(x2v-roots[j])+y2v*x1v*(x1v- roots[k])*(x1v-roots[j]))/((x1v-x2v)*(x1v-roots[k])*(x2v-roots[k])*(x1v-roots[j])*(x2v-roots[j]));
				Cv[j][k] := Cv[k][j];
			end for;
		end for;
*/
