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

load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/search_fast_ms_nf.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/glob_func_nf.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/loc_func.m"; 
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/padic_is_double.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/real_is_double.m";
load "/home/himanshu/dfg_proj/secondyear/conditional_algo/gen_cond_algo/is_double.magma";
//function to compute an embedding of the highest field required for computing
//CTP inside the p-Adic closure. 

CompEmbd := function(pol, K, t, emb)
  Qvt := Parent(t);
  polv := Qvt!Polynomial([emb(c): c in Coefficients(pol)]);
  Qv := BaseRing(Qvt); 
  prec := Max(Precision(Qv),SuggestedPrecision(polv));
  Qvtemp := ChangePrecision(Qv, prec+40); 
  Qvttemp := ChangeRing(Qvt, Qvtemp);
  defpolKv := Factorization(Qvttemp!polv)[1][1];
  defpolKv := Qvt!defpolKv;
  Kv := LocalField(BaseRing(Qvt), defpolKv);
  Kv, isom := RamifiedRepresentation(Kv);
  r := Roots(polv, Kv)[1][1];
  bf := Domain(emb);
  bftoQv := hom<bf-> BaseRing(Qvt)| BaseRing(Qvt)!emb(bf.1)>; 
  h := func<x | &+[r^(t-1)*(Kv!bftoQv(y[t])) where y := ElementToSequence(x): t in [1..Degree(K)]] >;
  KtoKv := hom<K-> Kv| x:->h(x)>;
  G, m := AutomorphismGroup(Kv, BaseRing(Qvt));
  return KtoKv, G, m;
end function;


realCTP := function(ctpMat, WPts, K, real_mor, GPts, Pg, defpol, sqrtg, a, goodSGelts, J, f,approx)
print "entering real computation";
  bf := Domain(real_mor);
  l := Degree(f);
  sortseq := [1..l];
  WPts_old := WPts; WPts := [real_mor(pt): pt in WPts_old];
  f := Polynomial([real_mor(c): c in Coefficients(f)]);
  sqrtg := <sqrtg[s]: s in sortseq>;
  goodSGelts := [<real_mor(d[s]) where d := goodSGelts[ind]: s in sortseq>: ind in [1..#goodSGelts]];
  R := Codomain(real_mor);
  prec := Precision(R);
  g := goodSGelts[a];
  C := ComplexField(prec);
  Ct := PolynomialRing(C);
  computed_vals := [R!0: t in [1..l]]; //since the value of gamma_inf depends only on chi_val of 
  //complex conjugation on g and the root position at which we are computing it, we keep
  //track of what position the value gamma_inf has been computed. 
  pos_gp := [ap: ap in [a+1..#goodSGelts]| exists{t: t in goodSGelts[ap]| t lt 0}];
  if pos_gp eq [] then return ctpMat; end if;
  
  defpolv := Ct!Polynomial([real_mor(c): c in Coefficients(defpol)]);
  r := Roots(defpolv)[1][1];
  h := func<x | &+[r^(i-1)*real_mor(c[i]) where c:= ElementToSequence(x): i in 
       [1..#ElementToSequence(x)]]>;
  KtoC := hom<K -> C | x :-> h(x)>;
  print "KtoC computed"; 
  if forall{d : d in g | d gt 0} then 
    Pv := [Ct.1- WPts[1], Parent(defpolv)!0];
    for ap in pos_gp do 
      gp := goodSGelts[ap];
      for i in [1..l] do  
        if gp[i] gt 0 then continue; end if;
        eps_val, pseq, sval := comp_epsilon({t : t in [1..l]}, i,-1, Curve(J), WPts_old);
        if pseq ne [] then  
        eps_val := real_mor(eps_val) *( &*[Sign(real_mor(gpt[1])*Real(KtoC(sqrtg[x[1]]))+ real_mor(gpt[2])*Real(KtoC(sqrtg[x[2]])))^(x[3]) where gpt := GPts[x[1]][x[2]]: x in pseq]); end if;
        eps_val := eps_val * Sign(real_mor(sval));
        if Evaluate(Pv[1], WPts[i]) eq 0 then 
          val := R!1;
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
    /*  
    Claim: If there is a point on the jacobian over reals with mumford representation
    a,b corresponding to the selmer element g,
    then we may as well choose a point such that a factors completely in the real
    field. This is because a :=LQ, where L is the product of linear factors and Q a
    product of quadratic factors, with degrees l and 2q. So we want to study the map
    sign on the function (-1^dega a(T)), which is same as sign(-1^l L(T)) because Q(x)>0
    for all x in R. So the set
    signchanges has cardinality l and note that the sign function on X-T is always
    positive in the start. For this I am assuming that the WPts is arranged in an increasing order.
    So we need to sort WPts for this idea.
    */

    sqgv := <KtoC(sq): sq in sqrtg>;
    Sort(~sortseq, func<s1,s2 | WPts[s1]-WPts[s2]>);
    newwpts := [WPts[s]: s in sortseq];
    newg := [g[s]: s in sortseq];
    signchanges := [i : i in [1..l-1]| (newg[i]*newg[i+1]) lt 0];
    sortseq := [1..l];
    pts := [Min(newwpts[i]+1, (newwpts[i]+newwpts[i+1])/2) : i in signchanges]; 
    pts := [[pt, SquareRoot(Evaluate(f,pt))]: pt in pts];
    dega := #pts;
    M := Transpose(Matrix(C, dega, dega, [[x[1]^(dega-i) : i in [1..dega]]: x in pts]));
    vec := Vector(C, dega, [x[2] : x in pts]);
    coef := Solution(M,vec); temp := ElementToSequence(coef); coef := [temp[dega-i]: i in [0.. dega -1]];
    mumpol2 := Ct!Polynomial(coef); mumpol1 := &*[Ct.1-x[1]: x in pts];
    assert forall{t: t in [1..l]| Real((-1)^dega*Evaluate(mumpol1,WPts[t]))/g[t] gt 0}; //sanity check
    print "local points:", [mumpol1,mumpol2];
    flag , Pv := IsDouble_inf(BaseChange(J,C), [mumpol1,mumpol2]); 
    ca := ElementToSequence(Pv[1]); ca[Degree(Pv[1])+1] := C!1; Pv[1]:= Ct!Polynomial(ca);

    assert flag eq true;  //sanity check
    Pgv := IdentityMatrix(C, l); 
    for t in [1..l-1] do for h in [t+1..l] do 
      gpt := GPts[t][h]; Pgv[t][h] := real_mor(gpt[1])*sqgv[t]+real_mor(gpt[2])*sqgv[h];
      Pgv[h][t] := Pgv[t][h]; 
    end for; end for;
       
    print "locpt and halfpt computed";
    genus := l div 2;
    chi_val := Indices([Sign(t) : t in g],1);
    f := ChangeRing(f, C);
    flag, fctn := IsRealPrincipalDivisor([WPts[t]: t in chi_val], Pv, f,approx); 
    assert flag eq true; //sanity check
    P := Parent(fctn[1][1]);
    x := P.1; y := P.2; embed := hom<Ct -> P| x>;
    pi := hom<P-> Ct| [Ct.1, 0]>;
  
    
  /*COMPUTING PAIRING AT INFINITY 
    We do not need the computation of the pairing at infinity because fctn in fctns looks
    like (x-ei) a_old/(g+y) and has the valuation -1 at infinity. So using the
    uniformizer x^(genus)/y at infinity we have h:=fctn*t_inf = (x-e_i)a_old x^genus/y(y+g). 
    Since g has degree <= genus and aold has degree equal to genus we have evaluation
    of h(\inf) = 1. 
  */
  for ap in pos_gp do
    gpv := goodSGelts[ap];
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
      eps_val, pseq, sval := comp_epsilon(SequenceToSet(chi_val), j, -1, Curve(J), WPts_old);
      eps_val := Argument(C!eps_val);
      if pseq ne [] then 
      eps_val := eps_val + (&+[x[3]*Argument(Pgv[x[1]][x[2]]): x in pseq]); end if;
      eps_val := eps_val + Argument(C!sval);
      
      if #chi_val ne l then 
        if #chi_val eq #fctn then 
          for i in [1..#chi_val] do
            if chi_val[i] eq j then 
  /* In this case we have fctn[i] is (x-e_i)a_old/(y+g). Therefore,
     fctn*tp^(-1) y*a_old/(g+y) := a_old/(1+g/y). Note that g is obtained by solving
     chinese remaindering of [0, b_old] mod [x-e_i, a_old]. Therefore, x-e_i is a
     factor of g. This implies that g/y(T_i)=0. Hence the pairing is a_old(e_i). 
  */   
              val := val + Argument(Evaluate(pi(fctn[i][1]) div (Ct.1-WPts[j]), WPts[j]));  
            else 
  /*else nothing vanishes on T_i by construction and so we just Numerator and denominator.*/ 
              val := val + Argument(Evaluate(fctn[i][1], [WPts[j],0]))
                   - Argument(Evaluate(fctn[i][2], [WPts[j],0]));
        
            end if;
          end for;
        else
        end if;
      end if;

      val := val-eps_val;
      value := PolarToComplex(1,val);
      print "diag val for complex case: ", Sign(Real(value));
      computed_vals[j] := Real(value);
      if Real(value) lt 0 then ctpMat[a][ap] := ctpMat[a][ap]*(-1); ctpMat[ap][a] := ctpMat[a][ap];
      end if;
      print ""; print""; print"";
    end for;
  end for;  

  return ctpMat; 
  end if; 
end function;  
      






CtpCondAlgo := function(SG, AtoSG, SGtoA, goodSGelts, atinf, approx, omitprimes, verifyeps)
  Z := Integers(); A := Domain(SGtoA); f := Modulus(A); l := Degree(f);
  C := HyperellipticCurve(f); J := Jacobian(C);
  bf := BaseField(C); Obf := RingOfIntegers(bf);
  baspol := DefiningPolynomial(bf);
  WPts := [r[1]: r in Roots(f)];
  goodSGelts := [<Evaluate(g@@SGtoA, WPts[j]): j in [1..l]>: g in goodSGelts];
  goodSGelts;

  ctpMat := Matrix(Z, #goodSGelts,#goodSGelts,[[1 : i in [1..#goodSGelts]]: j in [1..#goodSGelts]]);
  PoBR := [e[1]: e in Factorization(2*Obf*Discriminant(f))];  //primes of bad reduction of C 
  PoBR := SequenceToSet(PoBR);

//Initialize ctpMat to have every entry equal to 1.
    
  for a in [1] do
    locctvals :=[];
    g := goodSGelts[a];    
    GPts, Pg, sqrtg, K := globMatPij(g, WPts);//Compute the global matrix of pij
/*-------------------------------------------------------------------------------------------------
    Snippet for verification of epsilon
-------------------------------------------------------------------------------------------------*/ 
    if verifyeps then 
      for ap in [a+1..#goodSGelts] do 
        gp := goodSGelts[ap];
        for t in [1..l] do 
          verifyepsilon(Pg, WPts, K, C, sqrtg, t, gp[t]);
        end for;
      end for;
    end if;
    
    print "Epsilon verified";
    defpolK := DefiningPolynomial(K);
    assert Degree(defpolK) eq Degree(K, bf);   //sanity check
    pgelts := ElementToSequence(Pg);
    primes := &join[SequenceToSet([p[1] : p in Factorization(Norm(Numerator(elt))*Obf)])
      join SequenceToSet([p[1]: p in Factorization(Denominator(elt)*Obf)]): elt in pgelts];
    ramifiedPrimes := SequenceToSet([p[1]: p in Factorization(Parent(2*Obf)!Discriminant(K))]);
    print "Primes computed";
    primes := primes join ramifiedPrimes;
    assert Evaluate(defpolK, K.1) eq K!0;    //sanity check
   
    
    if atinf then 
      R := RealField(40);
      for r in Roots(baspol, R) do
        h := hom<bf -> R | r[1]>;
        ctpMat := realCTP(ctpMat, WPts, K, h, GPts, Pg, defpolK, sqrtg, a, goodSGelts, J, f, approx);
      end for;
      //return ctpMat;
      print "Pairing at infinite places computed";
    end if;
    
    primes := primes join PoBR;
    if omitprimes ne {} then omitprimes := &*[p: p in omitprimes]; else omitprimes := 1;
    end if;
    omitprimes := SequenceToSet([v[1]: v in Factorization(omitprimes*Obf)]);
    primes := primes diff omitprimes;
    primes := SetToSequence(primes);
    for v in primes do 
      print "Current prime: ", v;
      Qv, embv:= Completion(bf, v : Precision:=300);
      Qv := ChangePrecision(Qv, 300);
      Qvt := PolynomialRing(Qv);

/*********************************************************************************
          //it might be a good idea to introduce this change of precision in
          //relavant functions which require high enough precision rather than
          //a high precision. The idea is to overshoot precision when
          //necessary but output the results in relatively low precision
          //because the hilbert's symbol computation does not require really
          //high precision. 
  ******C := HyperellipticCurve(f); J := Jacobian(C);**************************************************************************/
      fv := Qvt!Polynomial([embv(c): c in Coefficients(f)]);
      KtoKv, G, m := CompEmbd(defpolK, K, Qvt.1, embv);
      print "Embedding K to Kv computed";
      gv := <Qv!embv(d) : d in g>;
      Piv := UniformizingElement(Qv);
      gv := <Piv^(Valuation(d) mod 2)*(d/Piv^(Valuation(d))): d in gv>;
      Kv := Codomain(KtoKv);
      sqrtgv := <KtoKv(K!sq): sq in sqrtg>;
      Pgv := ChangeRing(Pg, KtoKv);
      Cv := BaseChange(C,  embv);
      Jv := BaseChange(J,  embv);
      flag := false;
      count := 10000;
      while not flag do 
        flag, locPt := findlocPt(fv, gv, [Qv!embv(t): t in WPts], count);
        count := count+1000;
      end while;

      assert flag eq true;   //sanity check
      
      flag, Pv := pAdicIsDouble(ChangeRing(fv,Kv), [ChangeRing(lpt, Kv): lpt in locPt]);  

      assert #G eq Degree(Kv,Qv);  //sanity check
 
// Enterning the pairing zone. The idea is to pair gv with gpv[i] for i in [1..l] and take
// the product of all these pairings to obtain the local pairing between gv and gpv at v.     
      for ap in [a+1.. #goodSGelts] do 
        gp := goodSGelts[ap];
        LocCtpVal := [];
        gpv := <Qv!embv(d) : d in gp>;
        for i in [1..l] do
          dp := gpv[i];
          if IsSquare(dp) then Append(~LocCtpVal, 1); continue; end if;
          if IsSquare(Kv!dp) then
            sqrtdp := SquareRoot(Kv!dp);
            H := sub<G | [h: h in G | locEltEq(m(h)(sqrtdp), sqrtdp)]>;
            //compute a representative of non-triv of coset of G/H
            ntrivrep := [h : h in G | h notin H][1];
          else 
            H := G; ntrivrep := Identity(G);
          end if;

          //Compute local 1-cocycle to apply Hilber90
          onecocyc := Comp1Cocyc(m, H, WPts, Pv,i , ChangeRing(fv, Kv), KtoKv, <KtoKv(sq): sq in sqrtg>, Pgv,C);
          h90elt := H90pAdic(m, onecocyc);//Compute the
          
          DelAtdp := CompDiagVal(Pv, m(ntrivrep), KtoKv, sqrtg,i, WPts, Pgv, ChangeRing(fv, Kv), C)/((m(ntrivrep)(h90elt))*h90elt);
          //Finaly computing DelAtdp over the base ring
          pr := quo<IntegerRing(Kv)| UniformizingElement(Kv)^(Precision(DelAtdp)-5)>;
          ramind := RamificationIndex(Kv, Qv); 
          valdel := Valuation(Kv!DelAtdp) div RamificationIndex(Qv);
          //assert IsDivisibleBy(valdel, ramind); //sanity check
          
          if valdel lt 0 then DelAtdp := DelAtdp*((Piv^2)^(-valdel)); end if;  
         
          if forall{t: t in Generators(G)| pr!DelAtdp eq pr!(m(t)(DelAtdp))} then
            NmDel := Norm(DelAtdp, Qv); 
            polDel := Polynomial([-Qv!NmDel] cat [0: t in [1..#G-1]] cat [1]);
            rtsDel := [r[1]: r in Roots(polDel, Qv)];
            pr := quo<IntegerRing(Kv)| UniformizingElement(Kv)^(ramind*Precision(rtsDel[1]))>;
          try 
            DelAtdp := [t : t in rtsDel| pr!(Kv!t) eq pr!DelAtdp][1]; 
          catch e
            return DelAtdp;
          end try;  
            Append(~LocCtpVal,pAdicHilbSym(DelAtdp, dp));
          else 
          return m, G, H, WPts, Pv, i , ChangeRing(fv, Kv), <KtoKv(sq): sq in sqrtg>, Pgv, ntrivrep;

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







compctp := function(C : atinf:= true, approx:= true, omitprimes:={}, verifyeps:= false, SScomp:=false)
  flag, SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, goodSGelts := is_good(C, SScomp);
  print "finished computing good elements";
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
if #goodSGelts ne 0 then
 if 2^(#goodSGelts)*twotorssize eq #SG then
 ctpMat := CtpCondAlgo(SG, AtoSG, SGtoA, goodSGelts, atinf, approx, omitprimes, verifyeps);
 else 
 for g in SG do  if g notin good then Append(~goodSGelts, g); break; end if; end for;
ctpMat := CtpCondAlgo(SG, AtoSG, SGtoA, goodSGelts, atinf, approx, omitprimes, verifyeps);  
end if;
mat := ElementToSequence(ctpMat);
tozmod2 := map<{1,-1}-> GF(2)| [<1,0>, <-1,1>]>;
mat := [tozmod2(t): t in mat];
rk := Rank(Matrix(GF(2),#goodSGelts, #goodSGelts, mat));
print "Rank of CTP matrix := ",rk;
//return m, G, H, WPts, Pv, i , fv, sqrtgv, Pgv, ntrivrep;
return ctpMat, rk;
end if; 
return 0;
end function;
                      



                  
//CODE Snippet to be attached in order to include the functionality of no approximation at
//the complex place

 /*
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
  assert forall{t: t in [1..l]| IsSquare(L!(-Evaluate(mumpol1, WPts[t])/g[t]))}; //sanity check
  flag, Pv := IsDouble(BaseChange(J,L)![mumpol1,mumpol2]);
  assert flag eq true;    //sanity check
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
  Jv ;= BaseChange(J, R);
  fv := ChangeRing(f,R);
  flag, Pv := realIsDouble(BaseChange(J, C)!locpt);
  print Pv;
  
  print "locpt and halfpt computed";
  genus := l div 2;
  //assert flag eq true;
  chi_val := SequenceToSet(Indices([Sign(t) : t in g],1));
  f := ChangeRing(f, L);
  flag, fctn, newPt := IsRealPrincipalDivisor({WPts[t]: t in chi_val}, Pv, f, approx); 
  assert flag eq true;   //sanity check
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
      assert eps_val ne K!0;   //sanity check
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
 */ 
