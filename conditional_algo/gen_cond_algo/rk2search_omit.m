MWrk := function(v)
  if exists{i : i in v | not (i in [-10..10])} then return v, "invalid"; end if;
  Q<x>:= PolynomialRing(Rationals());
  C := HyperellipticCurve((x-v[1])*(x^2-v[2])*(x^2-v[3]));
  g := MordellWeilGroupGenus2(Jacobian(C): SearchBounds:= 1000, SearchBounds2 := 1000,
  SearchBounds3 :=1000, MaxBound:=1000, RankOnly := true, Rankbound := 2 ); 
  if #Generators(quo<g|TorsionSubgroup(g)>) eq 2 then return v, true; else return v,
    false; end if;
end function;


if assigned seq then
    SetColumns(0);
    SetAutoColumns(false);
    seq := eval seq;
    inputs := Split(Read("Rank2searchvals.txt"),"\n");  
    input := inputs[seq];
    input := Split(input,","); input := [StringToInteger(i): i in input];
    v, bool := MWrk(input);
    print v, bool;
    exit;
end if;

