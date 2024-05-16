load "/home/himanshu/dfg_proj/secondyear/conditional_algo/glob_func.m";
load "/home/himanshu/dfg_proj/secondyear/twoselmersetextra/search_fast_ms_org.m";


verify2cocyc := function(cocyc, m)
  K := Codomain(cocyc);
  G := Domain(cocyc);
  for sig in G do 
    for tau in G do 
      val := m(sig[1])(cocyc(tau))/cocyc(<sig[1]*tau[1], sig[2]*tau[2]>);
      if tau[2] eq 1 then val := val*cocyc(sig); else val := val/cocyc(sig); end if;
      if val ne K!1 then return false; end if;
    end for;
  end for;
  return true;
end function;



comp_eps := function(m, d, sqrtg, i)
  l := #sqrtg;
  c_dp := d[2];
  c := {t: t in [1..l]| m(d[1])(sqrtg[t]) eq sqrtg[t]};
  zero := SequenceToSet([1..5]);
  if (c_dp eq -1 and c eq zero) then return 1,[<i,j,-1>: j in [1..5]| j ne i],[];
  end if;
  if (c_dp eq 1 and c eq zero) then return 1, [], []; end if;
  if (c_dp eq -1 and c eq {i}) then return 1, [], []; end if;
  if c_dp eq 1 then
    if i in c then 
      if #c eq 1 then return 1, [<i,j,1>: j in [1..5]| j ne i], [];
      else  return -1, [<i,j,1>: j in [1..5]| j notin c], [<i,j,1>: j in c| j ne i]; 
      end if;
    else 
      if #c eq 1 then return 1, [<i,j,1>: j in c],[];
      else return -1, [<i,j,1>: j in c], [];
      end if;
    end if;
  else  
    if #c eq 1 then return  1, [<i,j,-1>: j in zero diff (c join {i})], [];
    else  
      if i in c then
        return -1, [<i,j,-1>: j in c| j ne i], [<i,j,1>: j in c| j ne i]; 
      else
        return -1, [<i,j,-1>: j in zero diff (c join {i})], [];
      end if;
    end if;
  end if;

end function;






Comp2Cocyc := function( WPts, Pg1, Pg2, sqrtg, dp, i)
  K := BaseRing(Pg1);
  G, s, m := AutomorphismGroup(K);
  CartProd := CartesianProduct(G, {1,-1});
  if IsSquare(K!dp) then 
    sqdp := SquareRoot(K!dp);
    H := sub<G|[g : g in G| m(g)(sqdp) eq sqdp]>;
    ntriv := [g : g in G | g notin H][1];
    dom := [<g, m(g)(sqdp)/sqdp>: g in G];
    dom := {CartProd!d : d in dom};
  else 
    H := G;
    dom := CartProd;
    ntriv := Identity(G);
  end if;
  maptups := [CartesianProduct(CartProd, K)|];
  for d in dom do 
    eps, pseq, sseq := comp_eps(m, d, sqrtg, i);
    eps1 := eps; eps2 := eps;
    if pseq ne [] then  
      eps1 := eps1 *(&*[Pg1[x[1]][x[2]]^(x[3]): x in pseq]); 
      eps2 := eps2 *(&*[Pg2[x[1]][x[2]]^(x[3]): x in pseq]); 
    end if;
    //Probably not needed but keep it for now
    if sseq ne [] then 
      s_val := (&*[(WPts[x[1]]-WPts[x[2]])^(x[3]): x in sseq]); 
      eps1 := eps1*s_val; eps2 := eps2*s_val;
    end if;
    Append(~maptups, <d, eps1/eps2>);
  end for;
  cocyc := map<dom -> K | maptups>;
  return H, m, ntriv, cocyc;
end function;



Comp1cocyc := function(H, twococyc)
  maptups := [<d,twococyc(<d, 1>)>: d in H];
  onecocyc := map<H -> Codomain(twococyc) | maptups>;
  return onecocyc;
end function;



CompQuaternionAlg := function(m, onecocyc, twococyc, ntriv)
  h90elt := Hilbert90(onecocyc);
  H := Domain(onecocyc); 
  assert forall{g : g in H | h90elt/(m(g)(h90elt)) eq onecocyc(g)};
  delta := twococyc(<ntriv,-1>)*(m(ntriv)(h90elt))*h90elt;
  return delta;
end function;
  





nxtPtCnc := function(coef, Pt, param)
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

  for B in [param..11] do 
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
    print "Pt on Conic:", [p/newPt[3]: p in newPt];
    return [p/newPt[3]: p in newPt]; //scale the z-coordinate to be 1. 
  end for;
  end for;
end function;



//function to compute the global matrix Pg with (i,j) entry representing pij
//(see manuscript)
globMatPij := function(g, WPts, params)
	l := #WPts;
  K := SplittingField([Polynomial([-d,0,1]): d in g]);
	sqrtg := <SquareRoot(K!d): d in g>;
	Pg1 := IdentityMatrix(K,l);
	for i:=1 to l do
		for j:=i+1 to l do 
    coef := [g[i],-g[j],WPts[i]-WPts[j]];
			Cij := Conic(coef);
   	Pt := RationalPoint(Cij);
    Pt := ElementToSequence(Pt);
    if not forall{p : p in Pt| p ne 0} then Pt := nxtPtCnc(coef, Pt, params[1]); 
    end if;
    //transpose again if we did it before calling nxtPtCnc;
    x0 := Pt[1]; y0 := Pt[2]; Pg1[i][j] := sqrtg[i]*x0 + sqrtg[j]*y0; 
    Pg1[j][i] := Pg1[i][j];
  	end for;
	end for;

	Pg2 := IdentityMatrix(K,l);
	for i:=1 to l do
		for j:=i+1 to l do 
    coef := [g[i],-g[j],WPts[i]-WPts[j]];
			Cij := Conic(coef);
   	Pt := RationalPoint(Cij);
    Pt := ElementToSequence(Pt);
    if not forall{p : p in Pt| p ne 0} then Pt := nxtPtCnc(coef, Pt, params[2]); 
    end if;
    //transpose again if we did it before calling nxtPtCnc;
    x0 := Pt[1]; y0 := Pt[2]; Pg2[i][j] := sqrtg[i]*x0 + sqrtg[j]*y0; 
    Pg2[j][i] := Pg2[i][j];
  	end for;
	end for;

	return Pg1, Pg2, sqrtg, K;
end function;








mainalgo := function(C)

  flag, SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, goodSGelts := is_good(C);
  SSinSG := SetToSequence(SSinSG);
  A := Codomain(SGtoA);
  f := Modulus(A);
  l := Degree(f);
  WPts := [r[1]: r in Roots(f)];
  QAlgs := [];
  g := <Evaluate(SGtoA(SSinSG[2]), WPts[t]): t in [1..l]>;
  gp := <Evaluate(SGtoA(goodSGelts[1]), WPts[t]): t in [1..l]>;
  Pg1, Pg2, sqrtg, K := globMatPij(g, WPts, [1,10]);
  for i in [1..l] do 
    dp := gp[i]; if IsSquare(dp) then continue; end if;
    H, m, ntriv, twococyc := Comp2Cocyc(WPts, Pg1, Pg2, sqrtg, dp, i);
    assert verify2cocyc(twococyc, m);
    print "eps is a 2-cocycle";
    onecocyc := Comp1cocyc(H, twococyc);
    delta := CompQuaternionAlg(m, onecocyc, twococyc, ntriv);
    assert delta in Rationals();
    Append(~QAlgs, <Rationals()!delta, dp>);
  end for;
  return QAlgs;
end function;
