// ----------------------------------------------
// Functions
// ----------------------------------------------

Z := Integers(); Q := Rationals();
R<x> := PolynomialRing(Q);

function RandomIrreducible( _d ) // it returns a random irreducible monic polynomial of degree d over Q with coefficients in Coeffs
	local _Coeffs,_f;
	_Coeffs := [-100..100];
	repeat	
		_f := x^_d + &+[ Random(_Coeffs)*x^i : i in [0.._d-1] ];
	until IsIrreducible( _f );
	return _f;
end function;

function RandomNormal( _d ) // it returns a random irreducible and monic polynomial defining a degree-d normal extension over Q
//Warning: It works fast only for small values of d
	local _f;
	repeat	
		_f := RandomIrreducible( _d );
	until IsNormal(NumberField(_f));
	return _f;
end function;

function RootsModp( _f, _p ) // it returns the roots of f mod p
	local F, Rp, xp;
	F := GF(_p);
	Rp< xp > := PolynomialRing(F);
	return {r[1] : r in Roots( Rp!Coefficients( _f ) )};
end function;

function Ev( _X, _n ) // Evaluate an element _X in Z<a> under a->n
    local seq;
	seq := Eltseq( _X );
	return &+[ seq[i]*_n^(i-1) : i in [1..#seq] ];
end function;


// ----------------------------------------------
// Theoretical results
// ----------------------------------------------

f := R!RandomIrreducible(2);
g := R!RandomNormal(3);

Qa<a> := NumberField(f);
Qb<b> := NumberField(g);
Qt<t> := Compositum(Qa,Qb);

h := DefiningPolynomial(Qt);

repeat 
    d := Random([-100..100]);
    e := Random([-100..100]);
until GCD(d,e) eq 1;

X := e + d*t;

Xa := &+[(e+d*a)^(Degree(g)-i) * (-d)^i * Reverse(Coefficients(g))[i+1] : i in [0..Degree(g)] ];
Xb := &+[(e+d*b)^(Degree(f)-i) * (-d)^i * Reverse(Coefficients(f))[i+1] : i in [0..Degree(f)] ];

Norm(X) eq Norm(Xa) and Norm(X) eq Norm(Xb);

for p in PrimeDivisors(Z!Norm(X)) do
    Rf := RootsModp(f,p);
    Rg := RootsModp(g,p);
    Rh := RootsModp(h,p);
    // Existence
    Rh eq {_r+_s : _r in Rf, _s in Rg}; 
    // Divisibility
    {_t : _t in Rh | Z!Ev(h,_t) mod p eq 0} eq {_r+_s : _r in Rf,_s in Rg | Z!Ev(f,_r) mod p eq 0 and Z!Ev(g,_s) mod p eq 0}; 
end for;


// ----------------------------------------------
// Time testing || Warning: It takes many hours
// ----------------------------------------------

// ----------------------------------------------
// Degree-6 normal extensions
// ----------------------------------------------

n_repetitions := 10;

// Constructing test polynomials

f := [R!RandomNormal(2) : _tmp in [1..n_repetitions]];
g := [R!RandomNormal(3) : _tmp in [1..n_repetitions]];
h := [DefiningPolynomial(SplittingField([f[i],g[i]])) : i in [1..n_repetitions]];

// Testing blocks of p_size primes

p_size := 10^8;

for _e in [0..9] do _e;

_l := Max(p_size*(_e),1);
_u := p_size*(_e+1);

// Standard approach
time for i in [1..n_repetitions] do
    for p in PrimesInInterval(_l,_u) do
       tmp := RootsModp(h[i],p);
    end for;
end for;

// Composite approach
time for i in [1..n_repetitions] do
    for p in PrimesInInterval(_l,_u) do
       tmp := {_r+_s : _r in RootsModp(f[i],p), _s in RootsModp(g[i],p)};
    end for;
end for;

end for;


// ----------------------------------------------
// Smooth extensions
// ----------------------------------------------

n_repetitions := 10;

// Constructing test polynomials

repeat 

f1 := [R!RandomIrreducible(3) : _tmp in [1..n_repetitions]];
f2 := [R!RandomIrreducible(3) : _tmp in [1..n_repetitions]];
f3 := [R!RandomIrreducible(5) : _tmp in [1..n_repetitions]];
f4 := [R!RandomIrreducible(7) : _tmp in [1..n_repetitions]];
h := [];

S<y> := PolynomialRing(R);

for i in [1..n_repetitions] do
    ht := Evaluate(f1[i],y);

    for f in [f2[i],f3[i],f4[i]] do
	    g := Evaluate(f,y);
	    ht := Resultant(ht,Evaluate(f,x-y));
	    ht := Evaluate(ht,y);
end for;

h[i] := ht;
end for;

until &and[IsIrreducible(_h) : _h in h];

// Testing blocks of p_size primes

p_size := 10^5;

for _e in [0..9] do

_l := Max(p_size*(_e),1);
_u := p_size*(_e+1);

// Standard approach
S1 := [ 0 : i in [1..n_repetitions] ];
time for i in [1..n_repetitions] do
    for p in PrimesInInterval(_l,_u) do
       S1[i] +:= #RootsModp(h[i],p);
    end for;
end for;

// Composite approach
S2 := [ 0 : i in [1..n_repetitions] ];
time for i in [1..n_repetitions] do
    for p in PrimesInInterval(_l,_u) do
       S2[i] +:= #{ _r1+_r2+_r3+_r4 : _r1 in RootsModp(f1[i],p), _r2 in RootsModp(f2[i],p), _r3 in RootsModp(f3[i],p), _r4 in RootsModp(f4[i],p)};
    end for;
end for;

//Counting missing first-degree prime ideals
total1 := &+S1;
total2 := &+S2;
missing := total1-total2;

total1, total2, missing;

end for;