/* Remarks for 28th Apr 2023 are as follows: As of now all the functions are in place,
 * some of them have been checked properly like findlocPt, padicIsDouble, CompEmbd,
 * globMatPij, nxtPtCnc. These work in principal at least. 
 * There are some things about the precision in the local computations like using the
 * suggested precision from the start or only overshoot the precision for certain
 * calculations which would need some thoughts so as to improve the performance of the
 * algorithm. 
 * Some ideas about extending the definition of eps in the manuscript to generic odd deg
 * case need to investigated soonish because it seems really plausible without too much
 * work. 
 * For the manuscript it would be interesting to formulate a valid conjecture as follows:
 * given aij for i and j in [1..k] and d1, ..., dk such that a1, ... ak appear as norms 
 * over some deg 2 subextension of \Q(\sqrt(d1),..., sqrt(dk)) then they can be written 
 * as solutions to conics.
 */ 

//load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/search_fast_ms_nf.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fsplit/check_good.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fsplit/glob_func.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fsplit/loc_func.m"; 
load "/home/himanshu/thesis_codes/ExChap4/Q_fsplit/padic_is_double.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fsplit/real_is_double.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fsplit/is_double.magma";
//function to compute an embedding of the highest field required for computing
//CTP inside the p-Adic closure. 

CompEmbd := function(pol, K, t)
  //K.1 is a root of pol
  Qvt := Parent(t);
  /*if BaseRing(Qvt) eq RealField() then 
    pol := ChangeRing(pol, ComplexField());
    root := Roots(pol)[1][1];
    KtoKv := hom<K -> BaseRing(Parent(pol))| root>;
    return KtoKv;
  end if;
  */
  prec := Precision(BaseRing(Qvt));
  Qvttemp := Qvt;
  for i in [1..2] do 
  sugprec:= SuggestedPrecision(Qvttemp!pol)+100;
  Qv := ChangePrecision(BaseRing(Qvt), sugprec);
  Qvttemp := ChangeRing(Qvttemp,Qv);
  end for;
  print sugprec;
  defpolKv := Factorization(Qvttemp!pol)[1][1];
  defpolKv := Qvt!defpolKv;

  Kv := SplittingField(defpolKv); //check if we can create an extension
                                   //directly without getting the splitting field.
  //make sure that K.1 maps to a root of defpolKv. 
  r := Roots(defpolKv, Kv)[1][1];
  KtoKv := hom<K -> Kv | r>;
  return KtoKv;
end function;


realCTP := function(ctpMat, WPts, K, GPts, Pg, defpol, sqrtg, a, goodSGelts, J, f,approx)
print "entering real computation";
  l := Degree(f);
  assert forall{t: t in [1..l-1] | WPts[t+1]-WPts[t] ge 0};
  prec := 20;
  R := RealField(prec);
  g := goodSGelts[a];
  C := ComplexField(prec);
  Ct := PolynomialRing(C);
  computed_vals := [R!0: t in [1..l]];
  //pos_gp := [<3,-33,-3,3,11>, <3, 33, 1, -3, -33>];
  pos_gp := [ap: ap in [a+1..#goodSGelts]| exists{t: t in goodSGelts[ap]| t lt 0}];
  if pos_gp eq [] then return ctpMat; end if;
  //rK := [t[1]: t  in Roots(defpol, C)][1];
  //KtoC := hom<K -> C| rK>;
  //assert IsReal(r) eq false;
  signchanges := [i : i in [1..l-1]| (g[i]*g[i+1]) lt 0];
    //Claim: If there is a point on the jacobian over reals with mumford representation
    //a,b corresponding to the selmer element g,
    //then we may as well choose a point such that a factors completely in the real
    //field. This is because a :=LQ, where L is the product of linear factors and Q a
    //product of quadratic factors, with degrees l and 2q. So we want to study the map
    //sign on the function (-1^dega a(T)), which is same as sign(-1^l L(T)) because Q(x)>0
    //for all x in R. So the set
    //signchanges has cardinality l and note that the sign function on X-T is always
    //positive in the start.
  isimaginary := true;
  KtoC := hom<K -> C| Roots(ChangeRing(defpol, C))[1][1]>;
  print "KtoC computed"; 
  if forall{d : d in g| d gt 0} then 
   Pv := [Parent(defpol).1- WPts[1], Parent(defpol)!0];
   isimaginary := false; //when all g is real then the localization of \eta at infinity is trivial and hence \epsilon is real.  
   for ap in pos_gp do 
     gp := goodSGelts[ap];
     for i in [1..l] do  
       if gp[i] gt 0 then continue; end if;
       eps_val, pseq, sval := comp_epsilon({t : t in [1..l]}, i,-1, Curve(J), WPts);
       if pseq ne [] then  
       eps_val := eps_val *(&*[Sign(((R!gpt[1])*SquareRoot(R!g[x[1]])+(R!gpt[2])*SquareRoot(R!g[x[2]])))^(x[3]) where gpt := GPts[x[1]][x[2]]: x in pseq]); end if;
      eps_val := eps_val * Sign(sval);
       if Evaluate(Pv[1], WPts[i]) eq 0 then 
       val := K!1;
       rem := Pv[1] div (Parent(Pv[1]).1- WPts[i]);
         if Degree(rem) ne 0 then val := -Sign(Real(Evaluate(rem, WPts[i]))); end if; 
         val := val* (&*[WPts[i]-WPts[t]: t in [1..l]| t ne i]);
         val := Sign(val/eps_val);
       else
         val := ((-1)^(Degree(Pv[1])))* Sign(Real(Evaluate(Pv[1], WPts[i])))^(-1);
         val := Sign(val/eps_val);
       end if;
       //print "Diag value in complex case is:", KtoC(val);
       if val eq -1 then 
         ctpMat[a][ap] := (-1)*ctpMat[a][ap];
         ctpMat[ap][a] := ctpMat[a][ap];
       end if;
     end for;
   end for;
   return ctpMat; 
 end if;

 
  if approx then 
    sqgv := <KtoC(sq): sq in sqrtg>;
    pts := [Min(WPts[i]+1, (WPts[i]+WPts[i+1])/2) : i in signchanges]; 
    pts := [[R!pt, SquareRoot(Evaluate(f,R!pt))]: pt in pts];
    dega := #pts;
    M := Transpose(Matrix(C, dega, dega, [[x[1]^(dega-i) : i in [1..dega]]: x in pts]));
    vec := Vector(C, dega, [x[2] : x in pts]);
    coef := Solution(M,vec); temp := ElementToSequence(coef); coef := [temp[dega-i]: i in [0.. dega -1]];
    mumpol2 := Polynomial(coef); mumpol1 := &*[Parent(mumpol2).1-x[1]: x in pts];
    print "local points:", [mumpol1,mumpol2];
    flag , Pv := IsDouble_inf(BaseChange(J,C), [mumpol1,mumpol2]); 
    ca := ElementToSequence(Pv[1]); ca[Degree(Pv[1])+1] := C!1; Pv[1]:= Ct!Polynomial(ca);
    //return Pv;


    assert flag eq true;
    Pgv := IdentityMatrix(C, l); 
    for t in [1..l-1] do for h in [t+1..l] do 
      gpt := GPts[t][h]; Pgv[t][h] := gpt[1]*sqgv[t]+gpt[2]*sqgv[h];
      Pgv[h][t] := Pgv[t][h]; 
    end for; end for;
       
    print "locpt and halfpt computed";
    genus := l div 2;
    chi_val := Indices([Sign(t) : t in g],1);
    f := ChangeRing(f, C);
    flag, fctn := IsRealPrincipalDivisor([WPts[t]: t in chi_val], Pv, f,approx); 
    assert flag eq true;
 // print "difference of newPt and Pvs :", [Polynomial([LtoC(z): z in Coefficients(newPt[t])])-Polynomial([ComplexConjugate(LtoC(z)): z in Coefficients(Pv[t])]): t in [1..2]];
    print "functions computed";
    P := Parent(fctn[1][1]);
    x := P.1; y := P.2; embed := hom<Ct -> P| x>;
    pi := hom<P-> Ct| [Ct.1, 0]>;
  
    
  //COMPUTING PAIRING AT INFINITY 
    // do not need the computation of the pairing at infinity because fctn in fctns looks
    // like (x-ei) a_old/(g+y) and has the valuation -1 at infinity. So using the
    // uniformizer x^(genus)/y at infinity we have h:=fctn*t_inf = (x-e_i)a_old x^genus/y(y+g). 
    // Since g has degree <= genus and aold has degree equal to genus we have evaluation
    // of h(\inf) = 1. 
    /* 
    [EvalFuncPairing1(CompMinRep(fctn[1]*x^((#chi_val)*genus),
                 fctn[2]*y^(#chi_val), f, false), [1, 0, 0], 
             f, false))^(-1);
    */
  for ap in pos_gp do
    //print goodSGelts[ap]; 
    gpv := <R!t : t in goodSGelts[ap]>;
    //gpv := <R!t : t in gp>;
    for j in [1..l] do 
      dp := gpv[j]; if dp gt 0 then continue; end if;
      if computed_vals[j] ne R!0 then val := computed_vals[j]; 
        if val lt 0 then ctpMat[a][ap]:= (-1)*ctpMat[a][ap]; ctpMat[ap][a]:= ctpMat[a][ap]; 
        end if;
        continue;
      end if;   
      //Computing in polar coordinates so val will store the argument of the computation
      val := R!0;
      val := -Argument((-1)^(Degree(Pv[1]))*Evaluate(Pv[1], WPts[j]));
      print "computing for dp and chi_val ", j, chi_val;
      eps_val, pseq, sval := comp_epsilon(SequenceToSet(chi_val), j, -1, Curve(J), WPts);
      eps_val := Argument(C!eps_val);
      if pseq ne [] then 
      eps_val := eps_val + (&+[x[3]*Argument(Pgv[x[1]][x[2]]): x in pseq]); end if;
      eps_val := eps_val + Argument(C!sval);
      print "eps_val: ", eps_val; 
      print "epsilon computed";
      if #chi_val ne l then 
        //Pvs := [Ct!Polynomial([ComplexConjugate(c): c in ElementToSequence(Pv[1])]),
        //  Ct!Polynomial([ComplexConjugate(c): c in ElementToSequence(Pv[2])])];
        if #chi_val eq #fctn then 
        for i in [1..#chi_val] do
         
        if chi_val[i] eq j then 
        // in this case we have fctn in fctns is (x-e_i)a_old/(y+g). Therefore,
        // fctn*tp^(-1) y*a_old/(g+y) := a_old/(1+g/y). Note that g is obtained by solving
        // chinese remaindering of [0, b_old] mod [x-e_i, a_old]. Therefore, x-e_i is a
        // factor of g. This implies that g/y(T_i)=0. Hence the pairing is a_old(e_i). 
        val := val + Argument(Evaluate(pi(fctn[i][1]) div (Ct.1-WPts[j]), WPts[j]));  
        else 
        //else nothing vanishes on T_i by construction and so we just Numerator and
        //denominator. 
        val := val + Argument(Evaluate(fctn[i][1], [WPts[j],0]))
                   - Argument(Evaluate(fctn[i][2], [WPts[j],0]));
        
        
        /*EvalFuncPairing1(CompMinRep(fctn[1]*y, fctn[2]*(x-WPts[j]), f, false),[WPts[j], 0, 1], f,false);
        else 
        val := val * EvalFuncPairing1(CompMinRep(fctn[1], fctn[2], f, false), [WPts[j], 0, 1], f, false);
        */
        end if;
        end for;
        
        else

        end if;
      end if;
    //evaluating g at infty
      val := val-eps_val;
      value := PolarToComplex(1,val);
      print "diag val for complex case: ", val, value;
      computed_vals[j] := Real(value);
      if Real(value) lt 0 then ctpMat[a][ap] := ctpMat[a][ap]*(-1); ctpMat[ap][a] := ctpMat[a][ap];
      end if;
      print ""; print""; print"";
    end for;
  end for;  

  return ctpMat; 
  end if;

  pts := [ WPts[i]+5 : i in signchanges];
  attrts := [K!Evaluate(f,pt): pt in pts | IsSquare(K!Evaluate(f,pt)) eq false];
  L := SplittingField([Polynomial([-rt, 0,1]): rt in attrts]);
  print "splitting field computed";
  pts := [[L!pt, SquareRoot(Evaluate(f,L!pt))]: pt in pts];
  print "square root computed";
  dega := #pts;
  M := Matrix(L, dega, dega, [[x[1]^(dega-i) : i in [1..dega]]: x in pts]);
  M := Transpose(M);
  vec := Vector(L, dega, [x[2] : x in pts]);
  print "computing solution";
  coef := Solution(M,vec); 
  print "solution computed";
  temp := ElementToSequence(coef);
  coef := [temp[dega-i]: i in [0.. dega -1]];
  mumpol2 := Polynomial(coef);
  mumpol1 := &*[Parent(mumpol2).1-x[1]: x in pts];
  //assert forall{t : t in [1..l]| Sign(Real(KtoC((-1)^dega*Evaluate(mumpol1,WPts[t])/g[t]))) eq 1};
  [mumpol1, mumpol2];
  print "another splitting field computed";
  L := SplittingField([Polynomial([-(-1)^dega*Evaluate(mumpol1, WPts[t])/g[t],0,1]): t in [1..l]| IsSquare((-1)^dega*Evaluate(mumpol1, WPts[t])/g[t]) eq false]);
  assert forall{t: t in [1..l]| IsSquare(L!(-Evaluate(mumpol1, WPts[t])/g[t]))};
  flag, Pv := IsDouble(BaseChange(J,L)![mumpol1,mumpol2]);
  assert flag eq true;
  //return [mumpol1, mumpol2], Pv;
  defpolL := DefiningPolynomial(L);
  r := Roots(defpolL,C)[1][1];
  LtoC := hom<L-> C | r>;
  Pv := ElementToSequence(Pv);
   //Pv :=[Polynomial([LtoC(t): t in ElementToSequence(Pv[1])]), Polynomial([LtoC(t): t in ElementToSequence(Pv[2])])];   
  //Pg := ChangeRing(Pg, L);
  //Pgv := ChangeRing(Pg,LtoC);
  //return Pv, Pgv;
  //gv := <R!d: d in g>;
  //sqgv := <LtoC(sq): L!sq in sqrtg>;

  //flag, locpt := findlocPt(Rt!f, gv, WPts, 1000, true);
  //assert flag eq true;
  //print locpt;
  /*Jv ;= BaseChange(J, R);
  fv := ChangeRing(f,R);
  flag, Pv := realIsDouble(BaseChange(J, C)!locpt);
  print Pv;
  */
  print "locpt and halfpt computed";
  genus := l div 2;
  //assert flag eq true;
  chi_val := SequenceToSet(Indices([Sign(t) : t in g],1));
  f := ChangeRing(f, L);
  flag, fctn, newPt := IsRealPrincipalDivisor({WPts[t]: t in chi_val}, Pv, f, approx); 
  assert flag eq true;
 // print "difference of newPt and Pvs :", [Polynomial([LtoC(z): z in Coefficients(newPt[t])])-Polynomial([ComplexConjugate(LtoC(z)): z in Coefficients(Pv[t])]): t in [1..2]];
  print "function computed";
  P := Parent(fctn[1]);
  x := P.1; y := P.2; embed := hom<Ct -> P| x>;
  pi := hom<P-> Ct| [Ct.1, 0]>;
  Pgv := ChangeRing(ChangeRing(Pg, L), LtoC);
  //computing pairing at infinity
  fval := (EvalFuncPairing1(CompMinRep(fctn[1]*x^((#chi_val)*genus),
                 fctn[2]*y^(#chi_val), f, false), [1, 0, 0], 
             f, false))^(-1);
 
  for ap in pos_gp do
    //print goodSGelts[ap]; 
    gpv := <R!t : t in goodSGelts[ap]>;
    //gpv := <R!t : t in gp>;
    for j in [1..l] do 
      dp := gpv[j]; if dp gt 0 then continue; end if;
      if computed_vals[j] ne R!0 then val := computed_vals[j]; 
        if val lt 0 then ctpMat[a][ap]:= (-1)*ctpMat[a][ap]; ctpMat[ap][a]:= ctpMat[a][ap]; 
        end if;
        continue;
      end if;   
      val := fval;
      val := val/((-1)^(Degree(Pv[1]))*Evaluate(Pv[1], WPts[j]));
      print "computing for dp and chi_val ", j, chi_val;
      eps_val, pseq, sval := comp_epsilon(chi_val, j, -1, Curve(J), WPts);
      eps_val := K!eps_val;
      if pseq ne [] then 
      eps_val := eps_val *(&*[Pg[x[1]][x[2]]^(x[3]): x in pseq]); end if;
      eps_val := eps_val * sval;
      assert eps_val ne K!0; 
      print "epsilon computed";
      if #chi_val ne l then 
        //Pvs := [Ct!Polynomial([ComplexConjugate(c): c in ElementToSequence(Pv[1])]),
        //  Ct!Polynomial([ComplexConjugate(c): c in ElementToSequence(Pv[2])])];
        if j in chi_val then 
          //print "TictpMat, WPts, K, Pg, defpol, sqrtg, a, goodSGelts, J, f in chi_val";
        //return fctn, Pv, Pvs, eps_val;
        val := val * EvalFuncPairing1(CompMinRep(fctn[1]*y, fctn[2]*(x-WPts[j]),f, false),[WPts[j], 0, 1], f,false);
        else 
        val := val * EvalFuncPairing1(CompMinRep(fctn[1], fctn[2], f, false), [WPts[j], 0, 1], f, false);
        end if;
      end if;
    //evaluating g at infty
      val := LtoC(val/eps_val); 
      print "diag val for complex case: ", val;
      computed_vals[j] := Real(val);
      if Real(val) lt 0 then ctpMat[a][ap] := ctpMat[a][ap]*(-1); ctpMat[ap][a] := ctpMat[a][ap];
      end if;
      print ""; print""; print"";
    end for;
  end for;  
  return ctpMat;  
end function;  
      






CtpCondAlgo := function(SG, AtoSG, SGtoA, goodSGelts, atinf, approx, omitprimes, verifyeps)
  Z := Integers(); A := Codomain(SGtoA); f := Modulus(A); l := Degree(f);
  C := HyperellipticCurve(f); J := Jacobian(C);
  WPts := [r[1]: r in Roots(f)];
  goodSGelts := [<Integers()!Evaluate(SGtoA(g), WPts[j]): j in [1..l]>: g in goodSGelts];
  goodSGelts := [<SquareFree(d): d in g>: g in goodSGelts];
  goodSGelts;
  
  //gp := <9,66,6,3,33>;//<Evaluate(SGtoA(TinSG.2), WPts[j]): j in [1..l]>;
// Matrix with (i,j) value equal to the value of CTP between ith and jth good
// element.

  ctpMat := Matrix(Z, #goodSGelts,#goodSGelts,[[1 : i in [1..#goodSGelts]]: j in [1..#goodSGelts]]);
  PoBR := SequenceToSet(PrimeDivisors(2*Z!Discriminant(f)));  //primes of bad reduction of C 

//Initialize ctpMat to have every entry equal to 1.

//print "step2";
  for g in [1.. #goodSGelts] do
      for h in [1..#goodSGelts] do ctpMat[g][h] := 1; end for;
  end for;
  
    
  for a in [1..#goodSGelts-1] do
    locctvals :=[];
    g := goodSGelts[a];
    g := <Integers()!d: d in g>; 
    g := <Sign(d)*(&*([p^(Valuation(d,p) mod 2): p in PrimeDivisors(d)] cat [1])): d in g>; 
    GPts, Pg, sqrtg, K := globMatPij(g, WPts);//Compute the global matrix of pij
    //print g, gp;
    //return Pg[1][2];
    // Snippet for verification of epsilon
   if verifyeps then 
     for ap in [a+1..#goodSGelts] do 
      gp := goodSGelts[ap];
      for t in [1..l] do 
      verifyepsilon(Pg, WPts, K, C, sqrtg, t, gp[t]);
      end for;
     end for;
    end if;
    
    print "eps verified";
    defpolK := DefiningPolynomial(K);
    primes := ElementToSequence(Pg);
    assert #primes eq l*l;
    primes := &join[SequenceToSet(PrimeDivisors(Integers()!Norm(Numerator(p), Rationals()))) join SequenceToSet(PrimeDivisors(Denominator(p))): p in primes];
    ramifiedPrimes := SequenceToSet(PrimeDivisors(Discriminant(K)));
    print "ramified primes computed";
    primes := primes join ramifiedPrimes;
    //return Pg;
    //return Pg, K, sqrtg;
    assert Evaluate(defpolK, K.1) eq K!0;
    //print "global matrix computed";
    //return ctpMat, WPts, K, Pg, defpolK, sqrtg, a, goodSGelts, J, f;
    
    
    if atinf then 
      ctpMat := realCTP(ctpMat, WPts, K, GPts, Pg, defpolK, sqrtg, a, goodSGelts, J, f, approx);
      //return ctpMat;
      print "exit infinity";
    end if;
    
    
    //return ctpMat; 
primes := primes join PoBR;// join {p: p in [1..50000]|IsPrime(p)};// join {p: p in [1.]| IsPrime(p)};
    primes;
    primes := primes diff omitprimes;
    primes := SetToSequence(primes); primes := Sort(primes);
    //Remove(~primes ,1);
    for v in primes do // !!!!!!!!Need to change this list to PoBR!!!!.
      print "Current prime: ", v;
      Qv := pAdicField(v, 20);
      Qvt := PolynomialRing(Qv);
      /*
      if forall{t: t in g| t ge 0} then //print "Field at infinity is Real so continuing";
      continue;
      end if;
      */

  /*********************************************************************************
          //it might be a good idea to introduce this change of precision in
          //relavant functions which require high enough precision rather than
          //a high precision. The idea is to overshoot precision when
          //necessary but output the results in relatively low precision
          //because the hilbert's symbol computation does not require really
          //high precision. 
  ********************************************************************************/
      prec := SuggestedPrecision(Qvt!f);
      Qv := ChangePrecision(Qv,prec); Qvt := ChangeRing(Qvt, Qv); 
      prec := SuggestedPrecision(Qvt!f)+ 100; Qv := ChangePrecision(Qv, prec);
      Qvt := ChangeRing(Qvt, Qv);
      fv := Qvt!f;
      //print "final precision: ", prec;
      KtoKv := CompEmbd(defpolK, K, Qvt.1);
      gv := <Qv!d : d in g>;
      //print "gv : ", gv;
      Kv := Codomain(KtoKv);
      //print "Kv is unramified", IsUnramified(Kv);
      sqrtgv := <KtoKv(sq): sq in sqrtg>;
      //print [sqrtgv[t]^2- Kv!gv[t]: t in [1..l]];
          //compute the localization of the Pgv matrix
      Pgv := ChangeRing(Pg, KtoKv);
      //[Valuation(p): p in ElementToSequence(Pgv)];
      Cv := BaseChange(C, Qv);
      Jv := BaseChange(J, Qv);
      flag := false;
      count := 10000;
      while not flag do
        count := count + 1000;  
        flag, MumPols := findlocPt(fv, gv, WPts, count); //find a local point on J
          //corresponding to g over Qv in the Mumford representation. ********
      end while;
        locPt := Jv!MumPols;
        //print locPt;
        //if Degree(Qvt!MumPols[1]) ne 0 then #Factorization(Qvt!MumPols[1]) eq 2; end if;
          //Compute half of the local point locpt in Mumford representation.
      flag, Pv := pAdicIsDouble(ChangeRing(fv, Kv), MumPols); //***************************** 
      Pv := ElementToSequence(Pv); 
 
      
      //print "local point and half of point computed";    
      //print "local point : ", MumPols; print "half point : ", Pv;
          
      //As of now we do not need to compute Mv or Cv (unless we later find
          //out that compting them gives us significant computational speedup)
          
          //Mv := MatMv(Pv, Pgv, gv);   //Compute Mij and Mii ************
          //Cv := MatCv(Pv, Pgv, gv);   //Compute Cij and Cii ************

      G,m := AutomorphismGroup(Kv, Qv);
      for ap in [a+1.. #goodSGelts] do gp := goodSGelts[ap];
        //print g, gp;
        LocCtpVal := [];
        gpv := <Qv!d : d in gp>;
        //print "gpv : ", gpv;
        for i in [1..l] do
          dp := gpv[i];
          //print "entering a prime zone";
                // if dp is square in the base field then the Hilbert symbol will be
                // trivial hence we continue. However, I should check the for loops and
                // updates in the ctpMat carefully.
         if IsSquare(Qv!dp) then Append(~LocCtpVal, 1); continue; end if;
          //print "dp was not a square in Qv. dp : ", dp;
                  //check if dp is a square in Kv 
          if IsSquare(Kv!dp) then
          //print "dp was a square in Kv. dp : ", dp;
          //print "dp is a unit", Valuation(dp);
            sqrtdp := SquareRoot(Kv!dp);
            H := sub<G | Identity(G)>;
            for h in G do 
              if (h notin H and locEltEq(m(h)(sqrtdp), sqrtdp)) then H := sub<G| H, h>; end if;
            end for;
                      //compute a representative of non-triv of coset of G/H
            nontrivrep := G.1;
            for h in G do if h notin H then nontrivrep := h; break; end if; end for;
          else 
          //print "dp was not a square in Kv. dp : ", dp;
            H := G; nontrivrep := Identity(G);
          end if;
          //Compute local 1-cocycle to apply Hilber90
          //print "computing 1 cocycle";
          //return Pv, WPts, ChangeRing(fv, Kv);
         // return m, H, WPts, Pv, i, ChangeRing(fv, Kv), <KtoKv(sq): sq in sqrtg>, Pgv, nontrivrep;
          onecocyc := Comp1Cocyc(m, H, WPts, Pv,i , ChangeRing(fv, Kv), 
                      KtoKv, <KtoKv(sq): sq in sqrtg>, Pgv,C);
          
          //print "computing hilbert 90 elt";
          h90elt := H90pAdic(m, onecocyc);//Compute the
                  //Hilber90 element for the given 1-cocycle
                  //****************************
            //Compute the value \gamma1,v(g,g) for computing
                //\delta_vi*******************************
          //print "computing delta"; 
          //print "Valuation of h90elt:", Valuation(h90elt);
          DelAtdp := (CompDiagVal(Pv, m(nontrivrep), KtoKv, sqrtg,i, WPts, 
                         Pgv, ChangeRing(fv, Kv), C))/((m(nontrivrep)(h90elt))*h90elt);
          //print "DelAtdp is a unit", IsUnit(DelAtdp);      
          pr := quo<IntegerRing(Kv)| UniformizingElement(Kv)^(Precision(DelAtdp)-5)>;
          ramind := RamificationIndex(Kv); valdel := Valuation(Kv!DelAtdp);
          //print valdel, Precision(DelAtdp);
          //if valdel ne 0 then print "at prime:", v;
          //print"Valuation of DelAtdp:", valdel;
          //end if;
          //Parent(valdel), Parent(ramind);
          //DelAtdp;
          assert IsDivisibleBy(valdel, ramind);
          if valdel lt 0 then DelAtdp := DelAtdp*((Qv!(v^2))^(-valdel div ramind)); end if;  
          //print dp, ElementToSequence(DelAtdp);
          //print "DelAtdp is unit", IsUnit(DelAtdp);
          //{t: t in G| pr!DelAtdp eq pr!(m(t)(DelAtdp))};
          //return DelAtdp;
          if forall{t: t in Generators(G)| pr!DelAtdp eq pr!(m(t)(DelAtdp))} then
            NmDel := Norm(DelAtdp, Qv); 
            polDel := Polynomial([-Qv!NmDel] cat [0: t in [1..#G-1]] cat [1]);
            rtsDel := [r[1]: r in Roots(polDel, Qv)];
            //#rtsDel;
            pr := quo<IntegerRing(Kv)| UniformizingElement(Kv)^(ramind*Precision(rtsDel[1]))>;
          try 
            DelAtdp := [t : t in rtsDel| pr!t eq pr!DelAtdp][1]; 
          catch e
            return DelAtdp;
          end try;  
            //print "succeeded";
            //print "computing loc ctp val";
            //print "DelAtdp is still a unit", IsUnit(DelAtdp);
            Append(~LocCtpVal,pAdicHilbSym(DelAtdp, dp));
          else 
          return m, G, H, WPts, Pv, i , ChangeRing(fv, Kv), <KtoKv(sq): sq in sqrtg>, Pgv, nontrivrep;

            error "inc prec";
          end if;
                  //Compute the local Hilbert symbol at v
                    //***************************
        end for;
        print v, LocCtpVal;
        if &*LocCtpVal eq -1 then Append(~locctvals, <v,&*LocCtpVal>); 
        ctpMat[a][ap] := ctpMat[a][ap]*(&*LocCtpVal);
        ctpMat[ap][a] := ctpMat[a][ap];
        end if;
      end for;
    end for;
  end for;
  locctvals;
  return ctpMat,_,_,_,_,_,_,_,_,_;
end function;







compctp := function(C : atinf:=true, approx:=true, omitprimes:={}, verifyeps:=false, SScomp:=false)
  flag, SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, goodSGelts := is_good(C, SScomp);
  print "finished computing good elements";
 /*
A := Codomain(SGtoA); f := Modulus(A); P := Parent(f); x := P.1; 
b := [-2*p, -p,0,p,2*p];
a := ChineseRemainderTheorem([P!1,P!-p,P!-p,P!-p,P!-p], [x-e: e in b]);
AtoSG(A!a) in SG;
return 0;
*/
// in case the curve has no good elements
  SSinSG := SetToSequence(SSinSG);
  if flag eq false then   
	  print "the curve is not good, try the generic algorithm";
	  return "err";
  end if;
//extracting SS elements
T := sub<SG| TinSG>; twotorssize := #T;
if exists{g: g in SSinSG | g notin T} then
  for g in SSinSG do 
    if g notin T then T := sub<SG|T,g>; Append(~goodSGelts, g);
    end if;
  end for;
end if;
if #goodSGelts eq 1 then return Matrix(Integers(),1,1,[1]); end if;
if #goodSGelts ne 0 then
 if 2^(#goodSGelts)*twotorssize eq #SG then
//temp := goodSGelts[1]; goodSGelts[1]:= goodSGelts[4]; goodSGelts[4]:= temp; 
 ctpMat := CtpCondAlgo(SG, AtoSG, SGtoA, goodSGelts, atinf, approx, omitprimes, verifyeps);
 else 
 for g in SG do  if g notin good then Append(~goodSGelts, g); break; end if; end for;
//temp := goodSGelts[1]; goodSGelts[1]:= goodSGelts[4]; goodSGelts[4]:= temp; 
ctpMat := CtpCondAlgo(SG, AtoSG, SGtoA, goodSGelts, atinf, approx, omitprimes, verifyeps);
  end if;
return ctpMat;
end if; 
return 0;
end function;
                      



                  

