load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/compute_good_subgroup.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/glob_func.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/loc_func1.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/padic_is_double.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/real_is_double.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/realctp.m";
ZZ := Integers();
QQ := Rationals();

nxtPtCnc := function(coef, Pt)
  //Pt;
  assert &+[coef[i]* Pt[i]^2: i in [1..3]] eq 0; // check if the point is indeed on the
        // conic
  if forall{p : p in Pt | p ne 0} then return Pt; end if; //if all coordinates of Pt are
                                                          //non zero then just return Pt

 //make sure that the 3rd coordinate is 0 if at all any of them is zero
  zind := [x:x in [1..3]| Pt[x] eq 0][1]; 
  if zind ne 3 then Pt[zind]:= Pt[3]; Pt[3]:=0; temp := coef[zind];
    coef[zind]:= coef[3]; coef[3]:= temp;
  end if;

  for B in [1..11] do 
  for C in [1..10] do  
   //B; C; 
    x0 := Pt[1]; y0 := Pt[2];
    a := coef[1]; b := coef[2]; c := coef[3]; 
    if (C^2*b eq -B^2*c) or (C^2*b eq B^2*c) then continue; end if;
    x1 := 1; y1 := y0*(c*B^2-b*C^2)/(x0*(c*B^2+b*C^2)); 
    z1 := 2*B*y0*b*C^2/(x0*C*(b*C^2+c*B^2));
    newPt := [x1,y1,z1];
    assert &+[coef[i]*newPt[i]^2: i in [1..3]] eq 0;
    assert forall{p : p in newPt | p ne 0};
    // in case the zero coordinate was forced to be the third one then revert it again.
    if zind ne 3 then temp := newPt[zind]; newPt[zind]:= newPt[3]; newPt[3] := temp;
    end if;
    //print "Pt on Conic:", [p/newPt[3]: p in newPt];
    return [p/newPt[3]: p in newPt]; //scale the z-coordinate to be 1. 
  end for;
  end for;
end function;


CompGlobMat := function(ff,d, WPts, G, m)
  A := Parent(d); 
  S := Parent(WPts[1]);
  globmat := [[<S!0,S!0>:r in [1..#WPts]]: s in [1..#WPts]];
  primeset := [];
  if S eq Rationals() then 
    for i :=1 to (#WPts-1) do for j := i+1 to #WPts do 
       di := Evaluate(d, WPts[i]); dj := Evaluate(d, WPts[j]);
       Cij := Conic([di,-dj,WPts[i]-WPts[j]]); Pt := RationalPoint(Cij);  
       Pt := ElementToSequence(Pt);
       if exists{p: p in Pt| p eq 0} then
         Pt := nxtPtCnc([di, -dj,WPts[i]-WPts[j]],Pt);
       else Pt := [p/Pt[3]: p in Pt];
       end if;
       ll, roots := SplittingField([Polynomial([-di,0,1]),Polynomial([-dj,0,1])]);
       primeset cat:= PrimeDivisors(ZZ!Norm(Numerator(roots[2][1]*Pt[2]+roots[1][1]*Pt[1]), QQ));
       globmat[i][j] := <Pt[1], Pt[2]>; globmat[j][i]:= <Pt[2], Pt[1]>;
    end for; end for;

    /*The following code checks that the globmat is the correct one
    for i in [1..#WPts] do for j in [1..#WPts] do if i eq j then continue; end if;
    assert Evaluate(d, WPts[i])*globmat[i][j][1]^2
    -Evaluate(d, WPts[j])*globmat[i][j][2]^2+WPts[i]-WPts[j] eq 0;
    end for; end for;
    */
    return globmat;
  end if;   
  for i := 1 to #ff do 
    K := NumberField(ff[i] : DoLinearExtension); ei := K.1; PK := PolynomialRing(K);
    for j := 1 to #ff do 
      for f1 in [e[1]: e in Factorization(PK!ff[j]) | Evaluate(e[1], ei) ne 0] do 
        L := ext<K|f1:DoLinearExtension>; LL := AbsoluteField(L); ej := LL!L.1; ei :=
        LL!L!ei;
        AtoLL1 := hom<A-> LL| ei>; AtoLL2 := hom<A->LL|ej>;
        di := AtoLL1(d); dj := AtoLL2(d);
        Cij := Conic([di,-dj,ei-ej]); Pt := RationalPoint(Cij);  
        Pt := ElementToSequence(Pt);
        if exists{p: p in Pt| p eq 0} then
          Pt := nxtPtCnc([di, -dj,ei-ej],Pt);
        else Pt := [p/Pt[3]: p in Pt];
        end if;
        ll, roots := SplittingField([Polynomial([-di,0,1]),Polynomial([-dj,0,1])]);
        primeset cat:= PrimeDivisors(ZZ!Norm(Numerator(roots[2][1]*Pt[2]+roots[1][1]*Pt[1]), QQ));
        Embed(LL,S, Roots(DefiningPolynomial(LL),S)[1][1]);
        for g in G do
          r := Index(WPts,m(g)(S!ei)); s := Index(WPts, m(g)(S!ej)); 
          globmat[r][s] := <m(g)(Pt[1]),m(g)(Pt[2])>;
        end for;
          for r:=1 to #WPts do for s := 1 to #WPts do if r eq s then continue; elif
                  globmat[r][s] eq <0,0> then globmat[r][s] := <globmat[s][r][2],globmat[s][r][1]>; end if;
          end for; end for;
      end for;
    end for;
  end for;
  // The following commented code checks that the globmat is the correct one
  for i in [1..#WPts] do for j in [1..#WPts] do 
    assert Evaluate(d,WPts[i])*globmat[i][j][1]^2 - Evaluate(d, WPts[j])*globmat[i][j][2]^2 + WPts[i]-WPts[j] eq 0;
  end for; end for;
  
return [*globmat, SequenceToSet(primeset)*];
end function;



LocEmbed := function(S, Sv)
  defS := DefiningPolynomial(S);
  Svt := PolynomialRing(Sv);
  r := Roots(Evaluate(defS, Svt.1))[1][1];
  if S eq Rationals() then return hom<S-> Sv|>; end if;
  StoSv := hom<S-> Sv| r>;
  return StoSv;
end function;

CompCorrectPv := function(Pv, g, WPtsv, f, G, m)
  l := #WPtsv; genus := l div 2;
  P := Parent(Pv[1]);
  Kv := BaseRing(P);
  sqrtg := <SquareRoot(Kv!Evaluate(g,pt)): pt in WPtsv>;
  if locPolEq(Pv[1],P!1) and locPolEq(Pv[2],P!0) then 
    return true, sqrtg, [*<Identity(G),[true: i in [1..l]]>*], [[*Identity(G), [1..l]*]], Pv, {};
  end if; 
    G_sqrtg := [**];
  chi_val_func := [];
  zero := SequenceToSet([1..l]);
  for h in G do if h eq Identity(G) then continue; end if;
    chi_valh := [true: t in [1..l]];
    for j in [1..l] do 
      k := [i: i in [1..l]|locEltEq(m(h)(WPtsv[j]), WPtsv[i])][1];
      chi_valh[k]:= locEltEq(m(h)(sqrtg[j]), sqrtg[k]);
    end for;
    Append(~G_sqrtg, <h,chi_valh>);
  end for;
  chi_val := [[*c[1], Indices(c[2], true)*]: c in G_sqrtg];
  subsetWPts := Subsets(SequenceToSet([1..l]));
  subsetWPts := [s : s in subsetWPts | #s lt genus+1];
  Sort(~subsetWPts, func<x,y| #x-#y>); 
  Pv1 := Pv;

  for s in subsetWPts do //CHANGE THIS! 
    newPv := Pv;
    for i in s do bool, newPv, fctn := locAdd([P.1-WPtsv[i], P!0], newPv, f, true, false);
    end for; flag := true; Pv1 := newPv;

    //print "computed newPv for s:", s;
    for c in chi_val do
      newPv := Pv1;
      Pv1s := [P!Polynomial([m(c[1])(j): j in ElementToSequence(Pv1[1])]), 
             P!Polynomial([m(c[1])(j): j in ElementToSequence(Pv1[2])])];
      for i in c[2] do
      bool, newPv, fctn := locAdd([P.1-WPtsv[i], P!0], newPv, f, true, false);
      end for; 
      if exists{t : t in [locPolEq(newPv[x], Pv1s[x]): x in [1..2]]| t eq false} then 
        flag := false; break;
      end if;
    end for;
    
    if flag then 
      for c in chi_val do 
        Pv1s := [P!Polynomial([m(c[1])(j): j in ElementToSequence(Pv1[1])]), 
                 P!Polynomial([m(c[1])(j): j in ElementToSequence(Pv1[2])])];
        funcflag, fctn := IsPrincipalDivisor([WPtsv[j]: j in c[2]], Pv1, Pv1s,f);
        assert funcflag eq true;
        Append(~chi_val_func, [*c[1], c[2], fctn*]);
      end for;
    return true, sqrtg, G_sqrtg, chi_val_func, Pv1, s; 
    end if;
  end for;
    return false, sqrtg, G_sqrtg, chi_val, Pv, {};
  end function;



/*  
realctp := function(WPts, f, globmat, S, SGtoA, elt1, elt2)
 ctpval := 1;
Cf := ComplexField(40);     
R := RealField(40);
l := Degree(f);
g := SGtoA(elt1);            
gp := SGtoA(elt2);             
defS := DefiningPolynomial(S);  StoC:= hom<S->Cf | Roots(defS, Cf)[1][1]>;     
assert Evaluate(defS,S.1) eq 0;
realroots := [StoC(pt): pt in WPts];                                         
gp:= <Evaluate(gp, r): r in realroots>;
g:= <Evaluate(g, r): r in realroots>; 
sqg := <Cf!1: i in [1..l]>;
real_root_index := [i : i in [1..l]| almost_real(realroots[i])];
real_root_index;
complex_conjugate_index := [];
for i in [1..l-1] do if i in real_root_index then continue; end if; 
for j in [i+1..l] do if (not (j in real_root_index)) and almost_real(realroots[i]+realroots[j]) then Append(~complex_conjugate_index, <i,j>); break; end if;end for; end for;
complex_conjugate_index;
for i in real_root_index do sqg[i]:= SquareRoot(g[i]); end for;
for pair in complex_conjugate_index do sqg[pair[1]]:= SquareRoot(g[pair[1]]); sqg[pair[2]]:= ComplexConjugate(sqg[pair[1]]); end for;

gp := <Sign(Real(t)):t in gp>;
g := <Sign(Real(t)):t in g>;
print "elt1 at real roots: ",[g[i]: i in real_root_index];
print "elt2 at real roots: ",[gp[i]: i in real_root_index];
for i in real_root_index do 
  if gp[i] eq -1 then
    eps_val := 1; 
    pseq :=  [<i,j,-1>: j in [1..l]| j ne i];
    eps_val := eps_val *(&*[(sqg[t[1]]*StoC(u[1]) + sqg[t[2]]*StoC(u[2]))^(t[3]) where u := (globmat[1])[t[1]][t[2]] : t in pseq]);
    //eps_val;
    assert almost_real(eps_val);
    print "local contrinbution:================================", Sign(Real(eps_val));
    ctpval := ctpval * Sign(Real(eps_val));
    end if;
end for;
return ctpval;
end function;


*/


//main := function(p)
//p:= 107; f:= x*(x^3-p)*(x^3-2*p
//f := (x^3-p)*(x^3-2*p)*(x^3-3*p);
//f := x*(x^2-p^2)*(x^2-4*p^2);
compctp := function(f, C, SGtoA, J,elt1,elt2s)
ff  := [e[1] : e in Factorization(f)];
A := Codomain(SGtoA);
/*C := HyperellipticCurve(f);
J := Jacobian(C);
bool, SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, good_elts := is_good(C, false);
#SG/8, #good_elts;
if 2^(#good_elts) ne #SG/#TinSG then 
  T := sub<SG| TinSG, good_elts>;
  for g in SG do if g notin T then Append(~good_elts,g); break; end if; end for;
end if;
*/
//ff;
//[SGtoA(good_elts[i]): i in [1..#good_elts]];
//[P!SGtoA(good_elts[1]) mod e: e in ff];
//[P!SGtoA(good_elts[2]) mod e: e in ff];

S, roots:= SplittingField(ff);
WPts := &cat[r:r in roots];
G, p, m := AutomorphismGroup(S); 
globmat := CompGlobMat(ff, SGtoA(elt1), WPts, G, m);
PoBR := SequenceToSet(PrimeDivisors(2*Integers()!Discriminant(f)));
ctpvec := [1: i in [1..#elt2s]];
//change this later just for testing 


ctpvec := realCTP(ctpvec, WPts, globmat, S, f, elt1, elt2s, 
            hom<QQ->RealField(50)|>);
print "real_ctpvec: ", ctpvec;
//error "err";
//for a in [1..#good_elts-1] do 
  print "primes for computation: ", PoBR join globmat[2];
  for v in PoBR join globmat[2] do
//  if v eq 2 then continue; end if; 
  print "Current prime: ", v;
  Qv := pAdicField(v, 20); 
  Qvt := PolynomialRing(Qv);
  prec := SuggestedPrecision(Qvt!f);
  Qv := ChangePrecision(Qv,prec); Qvt := ChangeRing(Qvt, Qv);
  prec := SuggestedPrecision(Qvt!f)+ 100; Qv := ChangePrecision(Qv, prec);
  Qvt := ChangeRing(Qvt, Qv);
  fv := Qvt!f;
  ffv := [e[1]: e in Factorization(fv)]; //local factorization of f
  g := SGtoA(elt1);
  gvIsTrivial := false; 
  Lv := <LocalField(Qv, e): e in ffv>;  //field representation of Qv[x]/f[x]
  //<Evaluate(ffv[i],Lv[i].1): i in [1..#ffv]>;
  WPtsv := <lv.1: lv in Lv>;
  gv := <Evaluate(g, lv.1): lv in Lv>;
  Lv :=<<kv, mv> where kv, mv := RamifiedRepresentation(lv): lv in Lv>; 
  //converting local field into p-adic field
  gv := <Lv[i][2](gv[i]): i in [1..#ffv]>; WPtsv := <Lv[i][2](WPtsv[i]):i in [1..#ffv]>;
  

  count := 1000; flag := false;
   while not flag do 
    count := count + 1000;
    flag, MumPols := findlocPt(fv,gv,WPtsv, count);
  end while;
  print "local point computed"; 
  Sv, roots := SplittingField(fv); Svt := PolynomialRing(Sv);

  //--------------------------------------------------------------------
  //piece of code useful while computing delta_v
  /*
  defSvr := DefiningPolynomial(Sv); Svu := BaseRing(Parent(defSvr)); 
  defSvu := DefiningPolynomial(Svu);   defSv := DefiningPolynomial(Sv,Qv);
  LSv := LocalField(Qv, defSv); u := Roots(defSu, LSv)[1][1]; 
  Lu := sub<LSv| u>;
SvuToLu := map<Svu-> Lu| x:-> &+[c[i]*u^(i-1) where c := ElementToSequence(x): i in [1..##ElementToSequence(x)]]>;
  deflr := Polynomial([SvuToLu(c): c in ElementToSequence(defSvr)]);
  v := Roots(deflr, LSv)[1][1];
  
SvtoLv := map<Sv-> Lv | x:-> &+[Svu]>
*/
  //---------------------------------------------------------------------
  
  if [locPolEq(MumPols[1],Parent(fv)!1), locPolEq(MumPols[2], Parent(fv)!0)] eq [true, true] then 
  gvIsTrivial := true;
  Pv := [Svt!mpol : mpol in MumPols]; Kv := Sv;
  else 
  Kv := SplittingField(&*[(Svt.1^2-Evaluate(g,r)): r in roots]);
  flag, Pv := pAdicIsDouble(ChangeRing(fv, Kv), MumPols);
  end if;
  StoSv := LocEmbed(S, Sv);
  Gmat := globmat[1];
  //Gmatv := [[<StoSv(Gmat[r][s][1]), StoSv(Gmat[r][s][2])>: r in [1..#WPts]]:s in [1..#WPts]];
  WPtsv := [StoSv(pt): pt in WPts];
  /*
  for i in [1..#WPts] do for j in [1..#WPts] do 
  locEltEq(StoSv(Evaluate(g, WPts[i])), Evaluate(g, WPtsv[i])) ; 
  StoSv(Evaluate(g,WPts[i]))*StoSv(Gmat[i][j][1])^2 - StoSv(Evaluate(g, WPts[j]))*StoSv(Gmat[i][j][2])^2 + StoSv(WPts[i]-WPts[j]);
  end for; end for;
*/
  ffv := [[e[1]: e in Factorization(Qvt!ffi)]: ffi in ff]; 
  G, m := AutomorphismGroup(Kv, Qv);
    bool, sqrtg, G_sqrtg, chi_val, Pv,s := CompCorrectPv(Pv, g, WPtsv, Parent(Pv[1])!fv, G,m);
  assert bool eq true; 
  printf "Adjust 1/2 of local point obtained by the set %o of indices of Weierstrass points\n", s;
  if gvIsTrivial then 
    for h in &cat ffv do 
      if Degree(h) eq 1 then continue; end if;
      indseq := [i : i in [1..#WPtsv] | locEltEq(Evaluate(h, WPtsv[i]), Sv!0)];
      assert #indseq eq Degree(h);
      i := indseq[1];
      sqg1 := SquareRoot(Kv!Evaluate(g,WPtsv[i])); sqrtg[i]:= sqg1;
      for j in [2..Degree(h)] do for t in G do 
        if locEltEq(m(t)(WPtsv[i]),WPtsv[indseq[j]]) then
          sqrtg[indseq[j]] := m(t)(sqg1); break;
        end if;
      end for; end for;
    end for;
  end if;

    for ap in [1..#elt2s] do
    elt2 := elt2s[ap];
    gp := SGtoA(elt2); 
    for h in &cat ffv do
      lh := LocalField(Qv,h); 
      if IsSquare(Evaluate(gp,lh.1)) then 
        print "gp is square in lh";
      continue; 
      end if;
      i := 0;
      for pt in WPtsv do if locEltEq(Evaluate(h, pt), Sv!0) then i := Index(WPtsv, pt);
        break; end if; 
      end for;
      dp := Evaluate(gp, WPtsv[i]);
      Gdp := sub<G| Identity(G)>;
      //the following code is to compute galois groups Gdp and Hdp such that 
      //Gdp = Gal(Kv/Qv(e_i)) and Hdp is subgroup of Gdp fixing sqrtdp.
      for t in G do 
      if (t notin Gdp and locEltEq(m(t)(WPtsv[i]), WPtsv[i])) then Gdp := sub<G| Gdp, t>;
      end if;
      
      end for;
      if IsSquare(Kv!dp) then 
        sqrtdp := SquareRoot(Kv!dp);
        Hdp := sub<Gdp | Identity(Gdp)>;
        for t in Gdp do 
          if (t notin Hdp and locEltEq(m(t)(sqrtdp), sqrtdp)) then 
            Hdp := sub<Gdp| Hdp, t>; 
          end if; 
        end for; nontrivrep := Gdp.1;
        for t in Gdp do if t notin Hdp then nontrivrep := t; break; end if; end for;
      else
        Hdp := Gdp; nontrivrep := Identity(Gdp);
      end if;  
      if #chi_val eq 1 and chi_val[1][1] eq Identity(Hdp) then h90elt := Kv!1;
      elif #Hdp eq 1 then h90elt := Kv.1;
      else   
      chi_hdp := [c : c in chi_val | c[1] in Hdp];
        //remember that chi_val does not have Identity element.
        onecocyc := Comp1Cocyc(StoSv, g, sqrtg, Hdp, m, chi_hdp, WPts, Pv, i, Parent(Pv[1])!fv, Gmat, BaseChange(C,S));  
        h90elt := H90pAdic(m, onecocyc);
      end if;
      DelAtdp := (CompDiagVal(Pv, m(nontrivrep), StoSv, sqrtg, g,i, WPts, Gmat, Parent(Pv[1])!fv, BaseChange(C,S)))/((m(nontrivrep)(h90elt))*h90elt);
      
      /*
      for t in Gdp do 
      assert locEltEq(m(t)(DelAtdp), DelAtdp); 
      end for;
      */
      minpoldel := MinimalPolynomial(DelAtdp, Qv);
      //h,minpoldel;
      //Degree(h), Degree(minpoldel);
      //print "Evluate(minpoldel, DelAtdp) gives: ", Evaluate(minpoldel, DelAtdp);
      assert IsDivisibleBy(Degree(h),Degree(minpoldel));
      rtsdel := [r[1]: r in Roots(minpoldel, lh)];
      assert #rtsdel ne 0; 
      valdel := Valuation(rtsdel[1]); 
      lhtoKv := hom<lh -> Kv| Kv!WPtsv[i]>;
      //print "h evaluated at lh.1:", Evaluate(h, lh.1);
      //print "h evaluated at WPtsv[i]:", Evaluate(h, WPtsv[i]);
      try
      DelAtdp := [r : r in rtsdel | locEltEq(lhtoKv(r)-DelAtdp, Kv!0)][1];
      //print "DelAtdp := ",DelAtdp;
      catch e 
      [lhtoKv(r)-DelAtdp: r in rtsdel];
      error "DelAtdp did not match any roots";
      end try;
      if valdel lt 0 then 
      print "Adjusting Delta as valdel lt 0";
        DelAtdp := DelAtdp* (UniformizingElement(lh))^(-2*valdel); 
        //rtsdel := [r*(UniformizingElement(lh))^(-2*valdel): r in rtsdel];
        //DelAtdp := DelAtdp*(lhtoKv(UniformizingElement(lh))^(-2*valdel));
      end if;


      /*
      ramindKvlh := RamificationIndex(Kv,Qv) div RamificationIndex(lh);
      print "Ramification index of Kv over lh", ramindKvlh;
      prec := Min(ramindKvlh*Precision(lh), Precision(DelAtdp));
      prec;
      //pr := quo<IntegerRing(Kv)|UniformizingElement(Kv)^(prec - 10)>;
      //[<pr!lhtoKv(t), pr!DelAtdp>: t in rtsdel];
      if Degree(minpoldel) eq 1 or #rtsdel eq 1 then DelAtdp := rtsdel[1];
      else
      print "minpol del of higher degree";
      //DelAtdp := rtsdel[1];
      //
      */
      Lh,mh := RamifiedRepresentation(lh);
      ctpvalnew := pAdicHilbSym(mh(DelAtdp), Evaluate(gp, mh(lh.1)));
      printf "local contribution at ap = %o is:================================ %o", ap,  ctpvalnew;
      print "";
      ctpvec[ap] := ctpvec[ap] * ctpvalnew;

      //print "Is Lh naturally embedded in Kv: ", Lh.1 in Kv;
      
      /*
      try 
      DelAtdp := [t : t in rtsdel| pr!(lhtoKv(t)) eq pr!DelAtdp][1]; 
      ctpvalnew := pAdicHilbSym(mh(DelAtdp), Evaluate(gp, mh(lh.1)));
      ctpvalnew;
      ctpval := ctpval * ctpvalnew;
      catch e
      print "projections of roots did not match Delta";
      //rtsdel;
      //[lhtoKv(t): t in rtsdel];
      //DelAtdp;
      //[pr!(lhtoKv(t)): t in rtsdel];
      //pr!DelAtdp;
      {pAdicHilbSym(mh(rtsdel[1]), Evaluate(gp, mh(lh.1))) eq pAdicHilbSym(mh(rts), Evaluate(gp, mh(lh.1))): rts in rtsdel};
      ctpvalnew := pAdicHilbSym(mh(rtsdel[1]), Evaluate(gp, mh(lh.1)));
      print "local contribution: ",ctpvalnew;      
      ctpval := ctpval* ctpvalnew;
      end try;
      end if;


      */
           
/*
      ramind := RamificationIndex(Kv,Sv); valdel := Valuation(Kv!DelAtdp);
      assert IsDivisibleBy(valdel, ramind);
      if valdel lt 0 then DelAtdp := DelAtdp*(UniformizingElement(Sv)^2)^(valdel div ramind); end if;
      nmdel := Norm(DelAtdp, Sv);
      poldel := Svt.1^(Degree(Kv,Sv))- Sv!nmdel;
      rtsdel := [r[1]: r in Roots(poldel, Sv)];
      pr := quo<IntegerRing(Kv)|UniformizingElement(Kv)^(ramind*Precision(rtsdel[1]))>;
      DelAtdp := [t : t in rtsdel| pr!(Kv!t) eq pr!DelAtdp][1];
      Degree(Sv), Degree(h), Degree(MinimalPolynomial(DelAtdp));
      //assert DelAtdp in Sv;
*/
/*
      
defKv := DefiningPolynomial(Kv, Qv); defSv := DefiningPolynomial(Sv, Qv);
LKv := LocalField(Qv, defKv); rSv := Roots(defSV, LKv)[1][1]; 
delLv := []
*/  
  /*defKv := DefiningPolynomial(Kv,Qv);
  LKv := LocalField(Qv,defKv); eltseq := ElementToSequence(DelAtdp);
  DelAtdp := &+[LKv.1^(i-1)*eltseq[i]: i in [1..#eltseq]]; 
  Ldel := sub<LKv| DelAtdp>; Degree(LKv); Degree(Ldel);
*/
        //onecocyc := Comp1Cocyc(m, Hdp, WPtsv,Pv, i, ChangeRing(fv, Kv), StoSv, <SquareRoot(Evaluate(g, pt)): pt in WPtsv>, Gmatv, C);
    end for; // interation through local factors 
  end for; //iteration through ap
end for;//iteration through v
//end for; //iteration through a


//computation at reals

return ctpvec;
end function;
