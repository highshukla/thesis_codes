realCTP := function(ctpMat, WPts, K, Pg, defpol, sqrtg, a, goodSGelts, J, f)
  l := Degree(f);
  assert forall{t: t in [1..l-1] | WPts[t+1]-WPts[t] ge 0};
  R := RealField();
  g := goodSGelts[a];
  if forall{d : d in g| d gt 0} then return ctpMat; end if;
  C := ComplexField(500);
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
  pts := [ (WPts[i]+WPts[i+1])/2 : i in signchanges];
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
  L := SplittingField([Polynomial([(-1)^dega*Evaluate(mumpol1, WPts[t])/g[t],0,1]): t in [1..l]| IsSquare((-1)^dega*Evaluate(mumpol1, WPts[t])/g[t]) eq false]);
  <t: t in [1..l]| IsSquare(L!(-Evaluate(mumpol1, WPts[t])/g[t]))>;
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
  flag, fctn := IsrealPrincipalDivisor({WPts[t]: t in chi_val}, Pv, f); 
  assert flag eq true;
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
      


