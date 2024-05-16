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


load "/home/himanshu/dfg_proj/secondyear/twoselmersetextra/search_fast_ms_org.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/glob_func.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/loc_func.m"; 
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/padic_is_double.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/real_is_double.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/is_double.magma";
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
  defpolKv := Factorization(Qvt!pol)[1][1];
  Kv := SplittingField(defpolKv); //check if we can create an extension
                                   //directly without getting the splitting field.
  //make sure that K.1 maps to a root of defpolKv. 
  r := Roots(defpolKv, Kv)[1][1];
  KtoKv := hom<K -> Kv | r>;
  return KtoKv;
end function;


realCTP := function(ctpMat, WPts, K, Pg, defpol, sqrtg, a, goodSGelts, J, f,approx)
  l := Degree(f);
  assert forall{t: t in [1..l-1] | WPts[t+1]-WPts[t] ge 0};
  R := RealField();
  g := goodSGelts[a];
  C := ComplexField(400);
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
 if forall{d : d in g| d gt 0} then 
   KtoC := hom<K -> C| Roots(ChangeRing(defpol, C))[1][1]>;
   Pv := [Parent(defpol).1- WPts[1], Parent(defpol)!0];

   for ap in pos_gp do 
     gp := goodSGelts[ap];
     for i in [1..l] do  
       if gp[i] gt 0 then continue; end if;
       eps_val, pseq, sseq := comp_epsilon({t : t in [1..l]}, i,-1);
       if pseq ne [] then  
         eps_val := eps_val *(&*[Pg[x[1]][x[2]]^(x[3]): x in pseq]); end if;
       if sseq ne [] then 
         eps_val := eps_val *(&*[(WPts[x[1]]-WPts[x[2]])^(x[3]): x in sseq]); end if;

       if Evaluate(Pv[1], WPts[i]) eq 0 then 
       val := K!1;
       rem := Pv[1] div (Parent(Pv[1]).1- WPts[i]);
         if Degree(rem) ne 0 then val := -Evaluate(rem, WPts[i]); end if; 
         val := val* (&*[WPts[i]-WPts[t]: t in [1..l]| t ne i]);
         val := val/eps_val;
       else
         val := ((-1)^(Degree(Pv[1])))* (Evaluate(Pv[1], WPts[i]))^(-1);
         val := val/eps_val;
       end if;
       print "Diag value in complex case is:", KtoC(val);
       if Real(KtoC(val)) lt 0 then 
         ctpMat[a][ap] := (-1)*ctpMat[a][ap];
         ctpMat[ap][a] := ctpMat[a][ap];
       end if;
     end for;
   end for;
   return ctpMat; 
 end if;

  
  pts := [ WPts[i]+1 : i in signchanges];
  attrts := [K!Evaluate(f,pt): pt in pts | IsSquare(K!Evaluate(f,pt)) eq false];
  L := SplittingField([Polynomial([-rt, 0,1]): rt in attrts]);
  pts := [[L!pt, SquareRoot(Evaluate(f,L!pt))]: pt in pts];
  dega := #pts;
  M := Matrix(L, dega, dega, [[x[1]^(dega-i) : i in [1..dega]]: x in pts]);
  M := Transpose(M);
  vec := Vector(L, dega, [x[2] : x in pts]);
  coef := Solution(M,vec); 
  temp := ElementToSequence(coef);
  coef := [temp[dega-i]: i in [0.. dega -1]];
  mumpol2 := Polynomial(coef);
  mumpol1 := &*[Parent(mumpol2).1-x[1]: x in pts];
  //assert forall{t : t in [1..l]| Sign(Real(KtoC((-1)^dega*Evaluate(mumpol1,WPts[t])/g[t]))) eq 1};
  [mumpol1, mumpol2];
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
  flag, fctn, newPt := IsrealPrincipalDivisor({WPts[t]: t in chi_val}, Pv, f); 
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
      eps_val, pseq, sseq := comp_epsilon(chi_val, j, -1);
      eps_val := K!eps_val;
      if pseq ne [] then 
      eps_val := eps_val *(&*[Pg[x[1]][x[2]]^(x[3]): x in pseq]); end if;
      if sseq ne [] then
      eps_val := eps_val *(&*[(WPts[x[1]]-WPts[x[2]])^(x[3]): x in sseq]); end if;
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
      






CtpCondAlgo := function(SG, AtoSG, SGtoA, goodSGelts, atinf, approx)
  Z := Integers(); A := Codomain(SGtoA); f := Modulus(A); l := Degree(f);
  C := HyperellipticCurve(f); J := Jacobian(C);
  WPts := [r[1]: r in Roots(f)];
  goodSGelts := [<Evaluate(SGtoA(g), WPts[j]): j in [1..l]>: g in goodSGelts];
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
    Pg, sqrtg, K := globMatPij(g, WPts);//Compute the global matrix of pij
    //print g, gp;
    //return Pg[1][2];
    // Snippet for verification of epsilon
    /*
     *for ap in [a+1..#goodSGelts] do 
      gp := goodSGelts[ap];
      for t in [1..5] do 
      verifyepsilon(Pg, WPts, K, C, sqrtg, t, gp[t]);
      end for;
    end for;
    */
    print "eps verified";
    defpolK := DefiningPolynomial(K);
    primes := ElementToSequence(Pg);
    assert #primes eq l*l;
    primes := &join[SequenceToSet(PrimeDivisors(Integers()!Norm(Numerator(p), Rationals()))) join SequenceToSet(PrimeDivisors(Denominator(p))): p in primes];
    ramifiedPrimes := SequenceToSet(PrimeDivisors(Discriminant(K)));
    primes := primes join ramifiedPrimes;
    //return Pg;
    //return Pg, K, sqrtg;
    assert Evaluate(defpolK, K.1) eq K!0;
    //print "global matrix computed";
    //return ctpMat, WPts, K, Pg, defpolK, sqrtg, a, goodSGelts, J, f;
    
    
    if atinf then 
      ctpMat := realCTP(ctpMat, WPts, K, Pg, defpolK, sqrtg, a, goodSGelts, J, f, approx);
    end if;
    
    
    //return ctpMat; 
primes := primes join PoBR; //join {p: p in [1..500000]|IsPrime(p)};// join {p: p in [1.]| IsPrime(p)};
    primes;
    primes := SetToSequence(primes); primes := Sort(primes);
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
      prec := SuggestedPrecision(Qvt!f)+ 80; Qv := ChangePrecision(Qv, prec);
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
      count := 1000;
      while not flag do
        count := count + 1000;  
        flag, MumPols := findlocPt(fv, gv, WPts, count ,false); //find a local point on J
          //corresponding to g over Qv in the Mumford representation. ********
      end while;
        locPt := Jv!MumPols;
          //Compute half of the local point locpt in Mumford representation.
      flag, Pv := pAdicIsDouble(BaseChange(Jv,Kv)!locPt); //***************************** 
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
                      <KtoKv(sq): sq in sqrtg>, Pgv);
          
          //print "computing hilbert 90 elt";
          h90elt := H90pAdic(m, onecocyc);//Compute the
                  //Hilber90 element for the given 1-cocycle
                  //****************************
            //Compute the value \gamma1,v(g,g) for computing
                //\delta_vi*******************************
          //print "computing delta"; 
          //print "Valuation of h90elt:", Valuation(h90elt);
          DelAtdp := (CompDiagVal(Pv, m(nontrivrep), <KtoKv(sqdv): sqdv
                  in sqrtg>,i, WPts, Pgv, ChangeRing(fv, Kv)))/((m(nontrivrep)(h90elt))*h90elt);
          //print "DelAtdp is a unit", IsUnit(DelAtdp);      
          pr := quo<IntegerRing(Kv)| UniformizingElement(Kv)^(Precision(DelAtdp)-5)>;
          ramind := RamificationIndex(Kv); valdel := Valuation(Kv!DelAtdp);
          //print valdel, Precision(DelAtdp);
          //if valdel ne 0 then print "at prime:", v;
          //print"Valuation of DelAtdp:", valdel;
          //end if;
          //Parent(valdel), Parent(ramind);
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
        if exists{t : t in LocCtpVal| t eq -1} then print v, LocCtpVal; end if; 
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







compctp := function(C,atinf, approx)
  flag, SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, goodSGelts := is_good(C);
  
// in case the curve has no good elements
  SSinSG := SetToSequence(SSinSG);
  if flag eq false then   
	  //print "the curve is not good, try the generic algorithm";
	  return 0;
  end if;

ctpMat := CtpCondAlgo(SG, AtoSG, SGtoA, goodSGelts, atinf, approx);
return ctpMat;
end function;
                      



                  

