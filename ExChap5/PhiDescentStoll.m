//IsInStollSet(l,A) checks if A is an element of l-Stoll Set (see Assumption 5.0.1). 
//If A is not an square free integer then false is returned.


//Let L := k[x]/(x^2-A) and k := Q(zeta_l). If A is an element of l-Stoll Set, then
//getSelelts(l,A) returns the Selmer group  as an abstract group selgp along with a map 
//m:L -> selgp and a map Atoll : L -> L_\lambda, where \lambda is a chosen ideal of
//maximal order of L above l. The map m has an inverse.
//The implementation of this function is based on the paper "On the arithmetic of the
//curves of the form y^2=x^l+A I" by Michael Stoll


IsInStollSet:= function(l,A)
  Fl := GF(l);
	Kl := CyclotomicField(l);
	Ol := MaximalOrder(Kl);
  if A ne SquareFree(A) then return false; end if;
  if A mod l eq 0 or IsSquare(Fl!A) then return false; end if;
  primes := PrimeDivisors(SquareFree(A));
  if 2 notin primes then Append(~primes, 2); end if;
	bad_places := &cat[[val[1] : val in Decomposition(Ol,p)] :  p in primes];
  test := [IsSquare(Completion(Kl,val)!A): val in bad_places];
  if exists{t : t in test | t eq true} then return false; end if;
	return true;
end function;	
  

getSelelts:=function(l,A)
k := CyclotomicField(l);
ql := (A^(l-1)-1)/l;
g := l div 2;
inv2 := Integers()!((GF(l)!2)^(-1));
lambda := Decomposition(MaximalOrder(k),l)[1][1];
kl, emb := Completion(k, lambda: Precision:= 60);
kl := ChangePrecision(kl, 60);
ll := ext<kl|Polynomial([-A,0,1])>;
zl := IntegerRing(kl);
bool, pi := IsPower(-kl!l, l-1);
lgens := [];
if IsDivisibleBy(Integers()!ql,l) then
  for j in [(l+1)/2..l-1] do 
    y := pi^j; assert IsPower(y-ll.1, 7);
    Append(~lgens, y-ll.1); 
  end for;
    lgens := [g/Norm(g)^inv2: g in lgens];
  assert forall{g : g in lgens | IsPower(Norm(g),l)};
else 
   if LegendreSymbol(Integers()!ql,l) eq -1 then
   aplus := SquareRoot(kl!A*ql);
   lgens := [(pi^g*aplus-ll.1)^2];
   if l gt 3 then
   for j in [1..(l-3)/2] do 
    x := -A*(1+pi*pi^j);
    y := SquareRoot(x^l+A);
    if Valuation(y/(pi)^g-aplus) eq 0 then y := -y; end if;
    Append(~lgens, (y-ll.1)*(-pi^g*aplus-ll.1));
    end for;
    end if;
  else 
  for j in [0..(l-3)/2] do 
    aplus := SquareRoot(ll!A*ql);
    xplus := -A*(1+aplus*pi*pi^j);
    xminus := -A*(1-aplus*pi*pi^j);
    yplus := SquareRoot(xplus^l+ll!A);
    yminus := SquareRoot(xminus^l+ll!A);
    if Valuation(yplus/pi^g-aplus) eq 0 then yplus := -yplus; end if; 
    if Valuation(yminus/pi^g+aplus) eq 0 then yminus := -yminus; end if;
    Append(~lgens, (yplus-ll.1)*(yminus-ll.1));
  end for;
  end if;
    lgens := [g/Norm(g)^inv2: g in lgens];
  assert forall{g: g in lgens | IsPower(Norm(g),l)};
end if;
cartprod := CartesianPower({i: i in [0..l-1]}, g);
locprod := [&*[lgens[i]^t[i]: i in [1..g]]: t in cartprod];
S := {lambda};
alg := quo<PolynomialRing(k)| Polynomial([-A,0,1])>;
SG, m := pSelmerGroup(alg, l, S);
SGk, mk :=pSelmerGroup(l,S);
SGgens := [g@@m : g in Generators(SG)];
N := hom<SG->SGk| x:-> mk(Norm(x@@m))>;
ker := Kernel(N);
//ker;
//kergens := [n@@m: n in Generators(ker)];
assert forall{t: t in Generators(ker)| IsPower(Norm(t@@m),l)};
Atoll := hom<Domain(m)->ll| t :-> &+[ll.1^(i-1)*kl!emb(s[i]): i in [1..#s]] where s :=
ElementToSequence(Domain(m)!t)>;
//lockergens := [Atoll(g): g in kergens];
Hl, ml := pSelmerGroup(l,ll);
Hlk, mlk := pSelmerGroup(l,kl);
Nl := hom<Hl->Hlk| x:-> mlk(Norm(x@@ml))>;
kerl := Kernel(Nl);
Jl := sub<kerl|[ml(g): g in lgens]>;
kerlmodJl, kermodJ  := quo<kerl| Jl>;

kertoA := hom<ker-> Domain(m)| x :-> x@@m>;
kertokerlmodJl := kertoA*Atoll*ml*kermodJ;
selgp := sub<ker|Id(ker)>;
checked := {Id(ker)};
for g in ker do 
  if g in selgp or g in checked then continue; end if;
  if kertokerlmodJl(g) eq Id(kerlmodJl) then 
    selgp := sub<ker|selgp,g>; 
  else checked := checked join (&join[{i*g+s : s in selgp}: i in [0..l-1]]);
  end if;
end for;
return selgp, m , Atoll;
  


/*
selgp := sub<ker|Id(ker)>;
notsel := {Id(ker)};
kerset := Set(ker);
last_g := Id(ker);
kerker := sub<ker|Id(ker)>;
for g in ker do 
  if g in kerker then continue; end if;
  if IsPower(Atoll(g@@m),l) then kerker := sub<ker|kerker,g>; end if;
end for;
  
for g in ker do
  if g-last_g in selgp or g in notsel then continue; end if; 
  if exists{t : t in locprod| IsPower(t/(Atoll(g@@m)),l)} then 
    selgp := sub<ker|selgp, g>;
    last_g := Id(ker); 
  else 
    notsel := notsel join Set(sub<ker|g>);
    last_g := g;
  end if;
end for;
*/
//return selgp, m, Atoll; 
end function;
