% 19 Dec 2025

:- [lib2025].

preference_order( A, P ):-
	 permutation( A, B ),
	 atomic_list_concat( B, P ).

n_profile( N, A, P ):-
	 length( P, N ),
	 maplist( preference_order( A ), P ).
%	 maplist( permutation( A ), P ).

domain(
	 alternatives( A ),
	 persons( I ),
	 preferences( H ),
	 size( K ),
	 profiles( D )
 ):-
	 length( I, N ),
	 findall( P, preference_order( A, P ), H ),
	 findall( P, n_profile( N, A, P ), U ),
	 select_n( D, U, K ).
%	 subsequence( K, U, D ).
%	 subsequence_length( K, U, D ).


base_case( A, I, H, K, D ):-
	 A = [a, b, c ],
	 I = [1, 2],
	 K_full is 6 ^ 2,
	 ( var( K ) -> K is K_full ; between( 1, K_full, K ) ),
	 domain(
		 alternatives( A ),
		 persons( I ),
		 preferences( H ),
		 size( K ),
		 profiles( D )
	 ).

nm_domain( N, M, A, I, H, K, D ):-
	 append( A, _,[a, b, c, d, e, f, g, h, i, j, k, l, m, n ] ),
	 length( A, M ),
	 findall( J, between( 1, N, J ), I ),
	 K_full is 6 ^ N,
	 ( var( K ) -> K is K_full ; between( 1, K_full, K ) ),
	 domain(
		 alternatives( A ),
		 persons( I ),
		 preferences( H ),
		 size( K ),
		 profiles( D )
	 ).


rank( P, X, K ):- sub_atom( P, K, 1,_,X).

preference( X, Y, P ):-
	 rank( P, X, K ), 
	 rank( P, Y, J ),
	 K < J. 

unanimous_pp( _, _, [ ] ).
unanimous_pp( X, Y, [ R | P ] ):-
	 preference( X, Y, R ),
	 unanimous_pp( X, Y, P ).

pareto_rule( P - S ):-
	 forall(
		 unanimous_pp( X, Y, P ),
		 preference( X, Y, S )
	 ).

iia_rule( P - S, F ):-
	 \+ iia_violation( P - S, F, _, _ ).

iia_referer( P-S, F, (X, Y), Q-T ):-
	 preference( X, Y, S ),
	 member( Q - T, F ),
	 \+ reversal_xy( P -> Q, (X, Y), _ ).

iia_immediate_referer( P-S, F, (X, Y), Q-T ):-
	 once( iia_referer( P-S, F, (X, Y), Q-T ) ).

iia_violation( P-S, F, (X, Y), Q-T ):-
	 preference( X, Y, S ),  % this is necessary
	 iia_immediate_referer( P-S, F, (X, Y), Q-T ),
	 %iia_referer( P-S, F, (X, Y), Q-T ),
	 \+ preference( X, Y, T ).

reversal_xy( P1 -> P2, (X, Y), [J, R->Q] ):-
	 nth1( J, P1, R ),
	 preference( X, Y, R ),
	 nth1( J, P2, Q ),
	 \+ preference( X, Y, Q ).

reversal_xy( P1 -> P2, (X, Y), [J, R->Q] ):-
	 nth1( J, P1, R ),
	 \+ preference( X, Y, R ),
	 nth1( J, P2, Q ),
	 preference( X, Y, Q ).


axiom_swf( H, P, ( P - S ), _, F ):- 
	 member( S, H ),
	 pareto_rule( P - S ),
	 iia_rule( P - S, F ).

dictatorship( [ ], [ ], dict( _ ) ). 
dictatorship( [ P | D ], [ P - S | F ], dict( J ) ):- 
	 nth1( J, P, S ),
	 dictatorship( D, F, dict( J ) ).


implied_decisiveness( D, L, P, ( X, Y ) -> ( Z, W ) ):-
	 member( P, D ),
	 mapx( axiom_swf( L ), [ P ], [ P - S ] ),
	 preference( X, Y, S ),
	 preference( Z, W, S ),
	 ( X, Y ) \= ( Z, W ),
	 \+ unanimous_pp( Z, W, P ),
	 \+ \+ (
		 mapx( axiom_swf( L ), [ P ], [ P - T ] ),
		 preference( X, Y, T ),
		 preference( Z, W, T )
	 ),
	 \+ (
		 mapx( axiom_swf( L ), [ P ], [ P - T ] ),
		 preference( X, Y, T ),
		 preference( W, Z, T )
	 ).

implied_decisiveness_profiles( D, L, X, H ):-
	 setof( P, implied_decisiveness( D, L, P, X ), H ).



/*

?- base_case( A, I, L, K, D ), hist1n( implied_decisiveness( D, L, P, X ),  X ), fail.

 [(a,b->a,c),2]
 [(a,b->c,b),2]
 [(a,c->a,b),2]
 [(a,c->b,c),2]
 [(b,a->b,c),2]
 [(b,a->c,a),2]
 [(b,c->a,c),2]
 [(b,c->b,a),2]
 [(c,a->b,a),2]
 [(c,a->c,b),2]
 [(c,b->a,b),2]
 [(c,b->c,a),2]
total:24
false.



?- base_case( A, I, L, K, D ), hist1n( setof( P, implied_decisiveness( D, L, P, X ), H ),  X:H ), fail.

 [(a,b->a,c):[[abc,bca],[bca,abc]],1]
 [(a,b->c,b):[[bca,cab],[cab,bca]],1]
 [(a,c->a,b):[[acb,cba],[cba,acb]],1]
 [(a,c->b,c):[[bac,cba],[cba,bac]],1]
 [(b,a->b,c):[[acb,bac],[bac,acb]],1]
 [(b,a->c,a):[[acb,cba],[cba,acb]],1]
 [(b,c->a,c):[[abc,cab],[cab,abc]],1]
 [(b,c->b,a):[[bca,cab],[cab,bca]],1]
 [(c,a->b,a):[[abc,bca],[bca,abc]],1]
 [(c,a->c,b):[[abc,cab],[cab,abc]],1]
 [(c,b->a,b):[[acb,bac],[bac,acb]],1]
 [(c,b->c,a):[[bac,cba],[cba,bac]],1]
total:12
false.

?- 

*/



chain_of_implied_decisiveness( _, _, (X,Y), H, H, G, [ (X,Y) | G ] ).
chain_of_implied_decisiveness( D, L, (Z,W), A, H, B, G ):-
	 implied_decisiveness( D, L, P, ( X, Y ) -> ( Z, W ) ),
	 \+ member( ( Z, W ), B ), 
	 ( A = [ ] ; A = [ Q | _ ], \+ reversal_xy( P -> Q, (Z, W), _ ) ),
	 chain_of_implied_decisiveness( D, L, (X,Y), [ P | A ], H, [ (Z,W) | B ], G ).


di_chain( D, L, B, G, H ):-
	 chain_of_implied_decisiveness( D, L, B, [], G, [ ], H ).



show_domain( L, _ ):- 
	 findall( J, nth1( J, L, _ ), H ),
	 format('~w\t~w;', ['',H] ),
	 nl,
	 fail.
show_domain( L, D ):- 
	 nth1( J, L, S ),
	 findall( T, ( 
		 nth1( _, L, X ),
		 ( nth1( I, D, [ S, X ] ) -> T = I ; T = '-' )
	 ) , W ),
	 format('~w:~w\t~w;\n', [J,S, W] ),
	 fail.
show_domain( _, _ ).



/*

?- base_case( A, I, L, K, D ), show_domain( L, D ).
        [1,2,3,4,5,6];
1:abc   [1,2,3,4,5,6];
2:acb   [1,2,3,4,5,6];
3:bac   [1,2,3,4,5,6];
4:bca   [1,2,3,4,5,6];
5:cab   [1,2,3,4,5,6];
6:cba   [1,2,3,4,5,6];
false.

?- base_case( A, I, L, K, D ), di_chain( D, L, (a,b), H, G ),  length( H, 6 ), show_domain( L, H ).
        [1,2,3,4,5,6];
1:abc   [-,-,-,1,-,-];
2:acb   [-,-,6,-,-,-];
3:bac   [-,-,-,-,-,2];
4:bca   [-,-,-,-,3,-];
5:cab   [5,-,-,-,-,-];
6:cba   [-,4,-,-,-,-];
A = [a, b, c],
I = [1, 2],
L = [abc, acb, bac, bca, cab, cba],
K = 36,
D = [[abc, abc], [abc, acb], [abc, bac], [abc, bca], [abc, cab], [abc, cba], [acb, abc], [acb|...], [...|...]|...],
H = [[abc, bca], [bac, cba], [bca, cab], [cba, acb], [cab, abc], [acb, bac]],
G = [(a, b), (a, c), (b, c), (b, a), (c, a), (c, b), (a, b)] .

?- base_case( A, I, L, K, D ), di_chain( D, L, (a,b), H, G ),  length( H, 6 ), writeln( H ), fail.
[[abc,bca],[bac,cba],[bca,cab],[cba,acb],[cab,abc],[acb,bac]]
[[abc,cab],[bac,cba],[bca,cab],[cba,acb],[cab,abc],[acb,bac]]
[[cab,abc],[cba,bac],[bca,abc],[bac,acb],[abc,cab],[acb,cba]]
[[cab,bca],[cba,bac],[bca,abc],[bac,acb],[abc,cab],[acb,cba]]
[[bca,abc],[cba,bac],[cab,bca],[acb,cba],[abc,cab],[bac,acb]]
[[cab,abc],[cba,bac],[cab,bca],[acb,cba],[abc,cab],[bac,acb]]
[[abc,cab],[bac,cba],[abc,bca],[acb,bac],[cab,abc],[cba,acb]]
[[bca,cab],[bac,cba],[abc,bca],[acb,bac],[cab,abc],[cba,acb]]
false.

?- base_case( A, I, L, K, D ), di_chain( D, L, (a,b), H, G ),  length( H, 6 ), writeln( G ), fail.
[(a,b),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(b,c),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(c,a),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
[(a,b),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
[(a,b),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(b,c),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(c,a),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
[(a,b),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
false.

?- nm_domain( 2, 3, A, I, L, K, D ), di_chain( D, L, (a,b), H, G ),  length( H, 6 ), writeln( G ), fail.
[(a,b),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(b,c),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(c,a),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
[(a,b),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
[(a,b),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(b,c),(a,c),(b,c),(b,a),(c,a),(c,b),(a,b)]
[(c,a),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
[(a,b),(c,b),(c,a),(b,a),(b,c),(a,c),(a,b)]
false.

*/


paren_profile( P, S ):-
	 atomic_list_concat( P, ',', R ),  
	 atomic_list_concat( [ '(', R, ')' ], S ).

edge_make( P, (X, Y), (Z, W), E ):- 
	 paren_profile( P, S ),
	 atom_concat( X, Y, U ),  
	 atom_concat( Z, W, V ),  
	 E = edge( U -> V, [ label = S ] ).

di_graph( _, _, (X,Y), A, B, A, [ (X,Y) | B ] ).
di_graph( D, L, (Z,W), A, B, G, H ):-
	 implied_decisiveness( D, L, P, ( X, Y ) -> ( Z, W ) ),
	 \+ member( ( Z, W ), B ), 
	 ( A = [ Q | _ ] -> \+ reversal_xy( P -> Q, (Z, W), _ ) ; true ),
	 edge_make( P, (X, Y), (Z, W), E ),
	 di_graph( D, L, (X,Y), [ E |A ], [ (Z,W) | B ], G, H ).

di_graph( D, L, B, G, H ):-
	 di_graph( D, L, B, [], [ ], G, H ).

%:- use_rendering( graphviz ). 

draw_di( D, L, digraph( [ rankdir = 'LR' | Graph ] ) ):-
	 findall( edge( U -> V, [ label = Gx ] ), (
		 implied_decisiveness_profiles( D, L, (X,Y)->(Z,W), H ),
		 atom_concat( X, Y, U ),
		 atom_concat( Z, W, V ),
		 findall( S, ( member( Q, H ), paren_profile( Q, S ) ), G ), 
		 atomic_list_concat( G, ',', Gx )
	 ), Graph ).


/*

?- paren_profile([abc,abc], A ).
A = '(abc,abc)'.


?- base_case( A, I, L, K, D ), di_graph( D, L, (a,b), H, G ), length( H, 6 ), nl, write( H ).

[edge((ab->ac),[label=(abc,bca)]),edge((ac->bc),[label=(bac,cba)]),edge((bc->ba),[label=(bca,cab)]),edge((ba->ca),[label=(acb,cba)]),edge((ca->cb),[label=(abc,cab)]),edge((cb->ab),[label=(acb,bac)])]
A = [a, b, c],
I = [1, 2],
L = [abc, acb, bac, bca, cab, cba],
K = 36,
D = [[abc, abc], [abc, acb], [abc, bac], [abc, bca], [abc, cab], [abc, cba], [acb, abc], [acb|...], [...|...]|...],
H = [edge((ab->ac), [label='(abc,bca)']), edge((ac->bc), [label='(bac,cba)']), edge((bc->ba), [label='(bca,cab)']), edge((ba->ca), [label='(acb,cba)']), edge((ca->cb), [label='(abc,cab)']), edge((cb->ab), [label='(acb,bac)'])],
G = [(a, b), (a, c), (b, c), (b, a), (c, a), (c, b), (a, b)] .

?- nm_domain( 2, 3, A, I, L, K, D ), di_graph( D, L, (a,b), H, G ), length( H, 6 ), nl, write( H ).

[edge((ab->ac),[label=(abc,bca)]),edge((ac->bc),[label=(bac,cba)]),edge((bc->ba),[label=(bca,cab)]),edge((ba->ca),[label=(acb,cba)]),edge((ca->cb),[label=(abc,cab)]),edge((cb->ab),[label=(acb,bac)])]
A = [a, b, c],
I = [1, 2],
L = [abc, acb, bac, bca, cab, cba],
K = 36,
D = [[abc, abc], [abc, acb], [abc, bac], [abc, bca], [abc, cab], [abc, cba], [acb, abc], [acb|...], [...|...]|...],
H = [edge((ab->ac), [label='(abc,bca)']), edge((ac->bc), [label='(bac,cba)']), edge((bc->ba), [label='(bca,cab)']), edge((ba->ca), [label='(acb,cba)']), edge((ca->cb), [label='(abc,cab)']), edge((cb->ab), [label='(acb,bac)'])],
G = [(a, b), (a, c), (b, c), (b, a), (c, a), (c, b), (a, b)] .

?- nm_domain( 2, 4, A, I, L, K, D ), di_graph( D, L, (a,b), H, G ), length( H, 6 ), nl, write( H ).

[edge((db->cb),[label=(abcd,acdb)]),edge((cb->db),[label=(abdc,adcb)]),edge((db->dc),[label=(abcd,adbc)]),edge((dc->bc),[label=(abdc,acbd)]),edge((bc->ac),[label=(abcd,cabd)]),edge((ac->ab),[label=(acbd,cbad)])]
A = [a, b, c, d],
I = [1, 2],
L = [abcd, abdc, acbd, acdb, adbc, adcb, bacd, badc, bcad|...],
K = 36,
D = [[abcd, abcd], [abcd, abdc], [abcd, acbd], [abcd, acdb], [abcd, adbc], [abcd, adcb], [abcd, bacd], [abcd|...], [...|...]|...],
H = [edge((db->cb), [label='(abcd,acdb)']), edge((cb->db), [label='(abdc,adcb)']), edge((db->dc), [label='(abcd,adbc)']), edge((dc->bc), [label='(abdc,acbd)']), edge((bc->ac), [label='(abcd,cabd)']), edge((ac->ab), [label='(acbd,cbad)'])],
G = [(d, b), (c, b), (d, b), (d, c), (b, c), (a, c), (a, b)] .

?- 

*/


show_values( W, F, N, SWF ):- 
	 findall( J, (
		 member( _-S, F ), nth1( J, W, S )
	 ), E ), 
	 length( E, N ),
	 atomic_list_concat( E, SWF ).

gen_swf( Size, Alternatives, Persons, L, Domain, SWF ):-
	 domain(
		 alternatives( Alternatives ),
		 persons( Persons ),
		 preferences( L ),
		 size( Size ),
		 profiles( Domain )
	 ),
	 mapx( axiom_swf( L ), Domain, SWF ).

gen_swf( Size, Alternatives, Persons, L, Domain, SWF, Dict ):-
	 gen_swf( Size, Alternatives, Persons, L, Domain, SWF ),
	 ( dictatorship( Domain, SWF, Dict )-> true ; Dict = poss ).

test_case( Size, Alternatives, Persons, Result ):-
	 gen_swf( Size, Alternatives, Persons, L, _, SWF, Dict ),
	 Dict = Result,
	 show_values( L, SWF, N, SWV ),
	 nl, write( SWV; N; Dict ),
	 fail ; true.


/*

using notebook PC in my office:


*** using modified select_n ***

with immediate referer

?- L is 6^2, A = [a,b,c], S = [1,2], test_case( L, A, S ).

123456123456123456123456123456123456;36 dict(2)
111111222222333333444444555555666666;36 dict(1)
% 215,189 inferences, 0.000 CPU in 0.019 seconds (0% CPU, Infinite Lips)
L = 36,
A = [a, b, c],
S = [1, 2].

?- L is 6^3, A = [a,b,c], S = [1,2,3], test_case( L, A, S ).

123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456;216 dict(3)
111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666;216 dict(2)
111111111111111111111111111111111111222222222222222222222222222222222222333333333333333333333333333333333333444444444444444444444444444444444444555555555555555555555555555555555555666666666666666666666666666666666666;216 dict(1)
% 35,344,948 inferences, 2.047 CPU in 2.064 seconds (99% CPU, 17267761 Lips)
L = 216,
A = [a, b, c],
S = [1, 2, 3].

% without immediate referer

?- L is 6^2, A = [a,b,c], S = [1,2], test_case( L, A, S ).

123456123456123456123456123456123456;36 dict(2)
111111222222333333444444555555666666;36 dict(1)
% 587,137 inferences, 0.047 CPU in 0.042 seconds (111% CPU, 12525589 Lips)
L = 36,
A = [a, b, c],
S = [1, 2].


?- L is 6^3, A = [a,b,c], S = [1,2,3], test_case( L, A, S ).

123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456;216 dict(3)
111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666;216 dict(2)
111111111111111111111111111111111111222222222222222222222222222222222222333333333333333333333333333333333333444444444444444444444444444444444444555555555555555555555555555555555555666666666666666666666666666666666666;216 dict(1)
% 288,062,387 inferences, 15.969 CPU in 16.333 seconds (98% CPU, 18039132 Lips)
L = 216,
A = [a, b, c],
S = [1, 2, 3].

*** using home hp ***

(select_n without immediate_referer)
n=2 % 587,460 inferences, 0.062 CPU in 0.066 seconds (95% CPU, 9399360 Lips)
n=3 % 288,064,330 inferences, 17.375 CPU in 17.495 seconds (99% CPU, 16579242 Lips)


**** using subsequence instead ****

with immediate referer

?- L is 6^2, A = [a,b,c], S = [1,2], test_case( L, A, S ).

123456123456123456123456123456123456;36 dict(2)
111111222222333333444444555555666666;36 dict(1)
% 215,511 inferences, 0.016 CPU in 0.015 seconds (102% CPU, 13792704 Lips)
L = 36,
A = [a, b, c],
S = [1, 2].

?- L is 6^3, A = [a,b,c], S = [1,2,3], test_case( L, A, S ).

123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456;216 dict(3)
111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666;216 dict(2)
111111111111111111111111111111111111222222222222222222222222222222222222333333333333333333333333333333333333444444444444444444444444444444444444555555555555555555555555555555555555666666666666666666666666666666666666;216 dict(1)
% 35,346,890 inferences, 2.000 CPU in 2.015 seconds (99% CPU, 17673445 Lips)
L = 216,
A = [a, b, c],
S = [1, 2, 3].

 without immediate referer

?- L is 6^2, A = [a,b,c], S = [1,2], test_case( L, A, S ).

123456123456123456123456123456123456;36 dict(2)
111111222222333333444444555555666666;36 dict(1)
% 587,459 inferences, 0.031 CPU in 0.034 seconds (93% CPU, 18798688 Lips)
L = 36,
A = [a, b, c],
S = [1, 2].

?- L is 6^3, A = [a,b,c], S = [1,2,3], test_case( L, A, S ).

123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456;216 dict(3)
111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666;216 dict(2)
111111111111111111111111111111111111222222222222222222222222222222222222333333333333333333333333333333333333444444444444444444444444444444444444555555555555555555555555555555555555666666666666666666666666666666666666;216 dict(1)
% 288,064,329 inferences, 16.344 CPU in 16.412 seconds (100% CPU, 17625351 Lips)
L = 216,
A = [a, b, c],
S = [1, 2, 3].


?- L is 6^2-2, time((domain( alternatives( [a,b,c] ), persons( [1,2] ), preferences( H ), size(L), profiles( D ) ), mapx( axiom_swf( H ), D, F ), show_values( H, F, N, SWF ), Write=(nl, write( SWF; N )), \+ dictatorship( D, J, F ), Write, fail; true )).

1215522255533466464466555555666666;34
1215522255512345654456555555556656;34
1215522255512345612345622255522656;34
1134422656333444444444556656666666;34
1134412345633344444444454456464466;34
1134412345633344433344412345633466;34
1234562265633466464466556656666666;34
1234562265612345654456556656556656;34
1133131233211331311344123456123456;34
1133131233233333344444454456464466;34
1133131233233333333344412345633466;34
1234561234563346646446654456464466;34
1211222222221233254456555555556656;34
1211221211221233212345612155123456;34
1211222222221233212345622255522656;34
1111111211221133131134412155123456;34
1111112222221133131134422255522656;34
1111111211223333333334441215533466;34
% 357,761,802 inferences, 22.156 CPU in 22.386 seconds (99% CPU, 16147218 Lips)
L = 34.


?- L is 6^2, A = [a,b,c], S = [1,2], test_case( L, A, S, D ).

123456123456123456123456123456123456;36;dict(2)
111111222222333333444444555555666666;36;dict(1)
L = 36,
A = [a, b, c],
S = [1, 2].

?- L is 6^2 - 2, A = [a,b,c], S = [1,2], test_case( L, A, S, poss ).

1215522255533466464466555555666666;34;poss
1215522255512345654456555555556656;34;poss
1215522255512345612345622255522656;34;poss
1134422656333444444444556656666666;34;poss
1134412345633344444444454456464466;34;poss
1134412345633344433344412345633466;34;poss
1234562265633466464466556656666666;34;poss
1234562265612345654456556656556656;34;poss
1133131233211331311344123456123456;34;poss
1133131233233333344444454456464466;34;poss
1133131233233333333344412345633466;34;poss
1234561234563346646446654456464466;34;poss
1211222222221233254456555555556656;34;poss
1211221211221233212345612155123456;34;poss
1211222222221233212345622255522656;34;poss
1111111211221133131134412155123456;34;poss
1111112222221133131134422255522656;34;poss
1111111211223333333334441215533466;34;poss
L = 34,
A = [a, b, c],
S = [1, 2].

?- 

without immediate referer (select_n)

?- L is 6^3, A = [a,b,c], S = [1,2,3], time(test_case( L, A, S, _ )).

123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456;216;dict(3)
111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666;216;dict(2)
111111111111111111111111111111111111222222222222222222222222222222222222333333333333333333333333333333333333444444444444444444444444444444444444555555555555555555555555555555555555666666666666666666666666666666666666;216;dict(1)
% 288,062,349 inferences, 17.328 CPU in 17.428 seconds (99% CPU, 16623977 Lips)
L = 216,
A = [a, b, c],
S = [1, 2, 3].

with immediate referer (select_n)

?- L is 6^3, A = [a,b,c], S = [1,2,3], time(test_case( L, A, S, _ )).

123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456123456;216;dict(3)
111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666111111222222333333444444555555666666;216;dict(2)
111111111111111111111111111111111111222222222222222222222222222222222222333333333333333333333333333333333333444444444444444444444444444444444444555555555555555555555555555555555555666666666666666666666666666666666666;216;dict(1)
% 35,344,910 inferences, 2.312 CPU in 2.358 seconds (98% CPU, 15284285 Lips)
L = 216,
A = [a, b, c],
S = [1, 2, 3].

?- 
?- between(1,19, J), assert( tmp( J )), write([J]), L is 6^3 - J, A = [a,b,c], S = [1,2,3], time(test_case( L, A, S, poss )).
 [1]
% 7,614,473,089 inferences, 462.703 CPU in 466.394 seconds (99% CPU, 16456498 Lips)
J = 1,
L = 215,
A = [a, b, c],
S = [1, 2, 3] .

?- 



*/


% サブリストを指標関数で抽出
list_projection_n( [ ], [ ], [ ], N, N ).
list_projection_n( [ 0 | A ], [ _ | Y ], Z, K, N ) :-
	number( N ), K > N, !,
	list_projection_n( A, Y, Z, K, N ).
list_projection_n( [ 1 | A ], [ X | Y ], [ X | Z ], K, N ) :-
	number( N ), K < N,
	K1 is K + 1,
	list_projection_n( A, Y, Z, K1, N ).
list_projection_n( [ 0 | A ], [ _ | Y ], Z, K, N ) :-
	number( N ), 
	list_projection_n( A, Y, Z, K, N ).
list_projection_n( [ 0 | A ], [ _ | Y ], Z, K, N ) :-
	var( N ), 
	list_projection_n( A, Y, Z, K, N ).
list_projection_n( [ 1 | A ], [ X | Y ], [ X | Z ], K, N ) :-
	var( N ), 
	K1 is K + 1,
	list_projection_n( A, Y, Z, K1, N ).


% 任意長のサブリストを抽出

select_n( A, B, K ):-
	 number( K ),
	 length( B, N ),
	 K > N / 2,
	 !,
	 M is N - K,
	 list_projection_n( X, B, _, 0, M ),
	 complementary_map( X, B, A ).
%	 subtract( B, C, A ).

select_n( A, B, K ):-
	 list_projection_n( _, B, A, 0, K ).


/*

?- time(hist1n( ( findall(I,between(1,36,I),A), I=6, select_n( _,A,I) ), 1 )).

 [1,1947792]
total:1947792
% 68,105,235 inferences, 4.750 CPU in 4.869 seconds (98% CPU, 14337944 Lips)
true.

% use subtract

?- time(hist1n( ( findall(I,between(1,36,I),A), I=30, select_n( _,A,I) ), 1 )).

 [1,1947792]
total:1947792
% 609,591,413 inferences, 38.469 CPU in 38.807 seconds (99% CPU, 15846406 Lips)
true.

% use complementary map

?- time(hist1n( ( findall(I,between(1,36,I),A), I=30, select_n( _,A,I) ), 1 )).

 [1,1947792]
total:1947792
% 212,241,845 inferences, 11.422 CPU in 11.587 seconds (99% CPU, 18582049 Lips)
true.

% use complementary map2

?- time(hist1n( ( findall(I,between(1,36,I),A), I=30, select_n( _,A,I) ), 1 )).

 [1,1947792]
total:1947792
% 216,137,429 inferences, 11.766 CPU in 12.033 seconds (98% CPU, 18370246 Lips)
true.


?- domain( alternatives( [a,b,c] ), persons( [1,2] ), H, size(3), profiles( D ) ).
H = preferences([abc, acb, bac, bca, cab, cba]),
D = [[abc, abc], [abc, acb], [abc, bac]] .

?- 


?- N=20, time(hist1n((findall( I, between(1,N,I), L ), member(K,L), select_n( A, L, K ) ), K )).

 [1,20]
 [2,190]
 [3,1140]
 [4,4845]
 [5,15504]
 [6,38760]
 [7,77520]
 [8,125970]
 [9,167960]
 [10,184756]
 [11,167960]
 [12,125970]
 [13,77520]
 [14,38760]
 [15,15504]
 [16,4845]
 [17,1140]
 [18,190]
 [19,20]
 [20,1]
total:1048575
% 77,719,337 inferences, 4.266 CPU in 4.481 seconds (95% CPU, 18219918 Lips)
N = 20.


?- N=20, M is N/2, time(hist1n((findall( I, between(1,N,I), L ), length( L1, M ), append( L1, L2, L ), member( K, L ), member(K1,L1), K2 is K - K1, select_n( A, L1, K1 ), select_n( B, L2, K2 ) ), K )).

 [1,10]
 [2,145]
 [3,1020]
 [4,4635]
 [5,15252]
 [6,38550]
 [7,77400]
 [8,125925]
 [9,167950]
 [10,184755]
 [11,167960]
 [12,125970]
 [13,77520]
 [14,38760]
 [15,15504]
 [16,4845]
 [17,1140]
 [18,190]
 [19,20]
 [20,1]
total:1047552
% 65,911,301 inferences, 3.750 CPU in 3.883 seconds (97% CPU, 17576347 Lips)
N = 20,
M = 10.

?- N=30, time(hist1n((findall( I, between(1,N,I), L ), member(K,L), select_n( A, L, K ) ), K )).
% 707,315,645 inferences, 50.719 CPU in 51.298 seconds (99% CPU, 13945841 Lips)
ERROR: Stack limit (1.0Gb) exceeded
ERROR:   Stack sizes: local: 9Kb, global: 24.0Mb, trail: 0Kb
ERROR:   Stack depth: 23, last-call: 26%, Choice points: 41
ERROR:   In:
ERROR:     [23] system:'$add_findall_bag'(10)
ERROR:     [22] '$bags':findall_loop(10, <compound (:)/2>, _1206, [])
ERROR:     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR:     [17] user:hist(<compound (',')/2>, 10, num)
ERROR:     [16] user:hist1n(<compound (',')/2>, 10)
ERROR: 
ERROR: Use the --stack_limit=size[KMG] command line option or
ERROR: ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (16) _274=true ? 

?- N=30, M is N/2, time(hist1n((findall( I, between(1,N,I), L ), length( L1, M ), append( L1, L2, L ), member( K, L ), member(K1,L1), K2 is K - K1, select_n( A, L1, K1 ), select_n( B, L2, K2 ) ), K )).
% 722,638,610 inferences, 45.141 CPU in 45.399 seconds (99% CPU, 16008609 Lips)
ERROR: [Thread 3] Stack limit (1.0Gb) exceeded
ERROR: [Thread 3]   Stack sizes: local: 9Kb, global: 24.0Mb, trail: 1Kb
ERROR: [Thread 3]   Stack depth: 25, last-call: 32%, Choice points: 43
ERROR: [Thread 3]   In:
ERROR: [Thread 3]     [25] system:'$add_findall_bag'(10)
ERROR: [Thread 3]     [24] '$bags':findall_loop(10, <compound (:)/2>, _1388, [])
ERROR: [Thread 3]     [23] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR: [Thread 3]     [19] user:hist(<compound (',')/2>, 10, num)
ERROR: [Thread 3]     [18] user:hist1n(<compound (',')/2>, 10)
ERROR: [Thread 3] 
ERROR: [Thread 3] Use the --stack_limit=size[KMG] command line option or
ERROR: [Thread 3] ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (18) _456=true ? 

*/


%--------------------------------------------------
% mapx
%--------------------------------------------------
% constructive mapping to satisfy local/accumulative conditions
% somewhat similar to arrow notation in javascript.

mapx( _, [ ], F, F ).

mapx( Axiom, [ X | D ], A, F ):-
	 apply( Axiom, [ X, Y, D, A ] ),
	 % X: current term
	 % Y: value assigned; ( X, A, D ) => Y 
	 % D: remaining list
	 % A: inductive outcome (i.e., accumulator)
	 mapx( Axiom, D, [Y|A], F ).

mapx( Axiom, D, F ):-
	 reverse( D, Dx ),
	 mapx( Axiom, Dx, [ ], F ).

% an application

% mapx==> complement_mapで0を消す
take_or_leave( X, X, _, _ ). % 要素を選ぶ
take_or_leave( _, 0, _, _ ). % 要素を選ばない

subsequence( P, H ):-
	 mapx( take_or_leave, P, M ),
	 subtract( M, [0], H ).

% slightly generalized form

mapy( _, [ ], F, F ).

mapy( Axiom, [ X | D ], A, F ):-
	 apply( Axiom, [ X, D, A, B ] ),
	 mapy( Axiom, D, B, F ).

mapy( Axiom, D, F ):-
	 reverse( D, Dx ),
	 mapy( Axiom, Dx, [ ], F ).

take_or_leave( N, X, D, A, [ X | A ] ):- length( A, K ), length( D, M ), N >= K + M + 1, !. 
take_or_leave( N, _, _, A, A ):- length( A, N ), !. 
take_or_leave( _, X, D, A, [ X | A ] ):- D \= [ ]. 
take_or_leave( _, _, D, A, A ):- D \= [ ]. 

subsequence( K, P, H ):-
	 mapy( take_or_leave( K ), P, H ).

subsequently_multiply( X, _, [ S ], [ S * X ] ).
subsequently_multiply( J, _, [ ], [ J ] ).

factorial( 0, 1 ).
factorial( K, F ):-
	 findall( J, between( 1, K, J ), D ),
	 mapy( subsequently_multiply, D, [ A ] ),
	 F is A.

combin( N, K, C, A/B ):-
	 M is N - K + 1,
	 findall( J, between( M, N, J ), D ),
	 mapy( subsequently_multiply, D, [ A ] ),
	 factorial( K, B ),
	 C is A / B,
	 !.

/*

?- A=[a,b,c], length(A,N), between(1,N, K ), subsequence( K, A, P ), nl, write( K:P), fail.

1:[a]
1:[b]
1:[c]
2:[a,b]
2:[a,c]
2:[b,c]
3:[a,b,c]
false.

?- N=10, hist((length(A,N), findall(K, between(1,N, K ), A ), member(K, A ),subsequence( K, A, P ) ),  K).

 1:10
 2:45
 3:120
 4:210
 5:252
 6:210
 7:120
 8:45
 9:10
 10:1
total:1023
N = 10.

?- N=20, hist((length(A,N), findall(K, between(1,N, K ), A ), member(K, A ),subsequence( K, A, P ) ),  K).

 1:20
 2:190
 3:1140
 4:4845
 5:15504
 6:38760
 7:77520
 8:125970
 9:167960
 10:184756
 11:167960
 12:125970
 13:77520
 14:38760
 15:15504
 16:4845
 17:1140
 18:190
 19:20
 20:1
total:1048575
N = 20.

?- between( 0,20, N ), factorial(N,P), writeln( factorial(N)=P ), fail;true.
factorial(0)=1
factorial(1)=1
factorial(2)=2
factorial(3)=6
factorial(4)=24
factorial(5)=120
factorial(6)=720
factorial(7)=5040
factorial(8)=40320
factorial(9)=362880
factorial(10)=3628800
factorial(11)=39916800
factorial(12)=479001600
factorial(13)=6227020800
factorial(14)=87178291200
factorial(15)=1307674368000
factorial(16)=20922789888000
factorial(17)=355687428096000
factorial(18)=6402373705728000
factorial(19)=121645100408832000
factorial(20)=2432902008176640000
true.

?- N=20, between( 0, N, K ), combin(N, K, X,Y), writeln( 'C_n_k'(N,K)=X ), fail;true.
C_n_k(20,0)=1
C_n_k(20,1)=20
C_n_k(20,2)=190
C_n_k(20,3)=1140
C_n_k(20,4)=4845
C_n_k(20,5)=15504
C_n_k(20,6)=38760
C_n_k(20,7)=77520
C_n_k(20,8)=125970
C_n_k(20,9)=167960
C_n_k(20,10)=184756
C_n_k(20,11)=167960
C_n_k(20,12)=125970
C_n_k(20,13)=77520
C_n_k(20,14)=38760
C_n_k(20,15)=15504
C_n_k(20,16)=4845
C_n_k(20,17)=1140
C_n_k(20,18)=190
C_n_k(20,19)=20
C_n_k(20,20)=1
true.

?- N=20, time( hist1n((findall( I, between(1,N,I), L ), member( K, L ), subsequence( K, L, A )), K )).

 [1,20]
 [2,190]
 [3,1140]
 [4,4845]
 [5,15504]
 [6,38760]
 [7,77520]
 [8,125970]
 [9,167960]
 [10,184756]
 [11,167960]
 [12,125970]
 [13,77520]
 [14,38760]
 [15,15504]
 [16,4845]
 [17,1140]
 [18,190]
 [19,20]
 [20,1]
total:1048575
% 121,634,848 inferences, 7.438 CPU in 7.632 seconds (97% CPU, 16354265 Lips)
N = 20.

?- N=20, time( hist1n((findall( I, between(1,N,I), L ), member( K, L ), select_n( A, L, K )), K )).

 [1,20]
 [2,190]
 [3,1140]
 [4,4845]
 [5,15504]
 [6,38760]
 [7,77520]
 [8,125970]
 [9,167960]
 [10,184756]
 [11,167960]
 [12,125970]
 [13,77520]
 [14,38760]
 [15,15504]
 [16,4845]
 [17,1140]
 [18,190]
 [19,20]
 [20,1]
total:1048575
% 127,926,457 inferences, 7.531 CPU in 7.742 seconds (97% CPU, 16986086 Lips)
N = 20.


?- N=30, time( hist1n((findall( I, between(1,N,I), L ), member( K, L ), select_n( A, L, K )), K )).
% 612,314,264 inferences, 39.109 CPU in 39.637 seconds (99% CPU, 15656457 Lips)
ERROR: Stack limit (1.0Gb) exceeded
ERROR:   Stack sizes: local: 8Kb, global: 24.0Mb, trail: 0Kb
ERROR:   Stack depth: 23, last-call: 26%, Choice points: 40
ERROR:   In:
ERROR:     [23] system:'$add_findall_bag'(10)
ERROR:     [22] '$bags':findall_loop(10, <compound (:)/2>, _1206, [])
ERROR:     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR:     [17] user:hist(<compound (',')/2>, 10, num)
ERROR:     [16] user:hist1n(<compound (',')/2>, 10)
ERROR: 
ERROR: Use the --stack_limit=size[KMG] command line option or
ERROR: ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (16) _274=true ? no debug

?- N=30, time( hist1n((findall( I, between(1,N,I), L ), member( K, L ), subsequence( K, L, A )), K )).
% 2,444,790,731 inferences, 145.656 CPU in 147.090 seconds (99% CPU, 16784661 Lips)
ERROR: Stack limit (1.0Gb) exceeded
ERROR:   Stack sizes: local: 7Kb, global: 41Kb, trail: 0Kb
ERROR:   Stack depth: 23, last-call: 26%, Choice points: 22
ERROR:   In:
ERROR:     [23] system:'$add_findall_bag'(10)
ERROR:     [22] '$bags':findall_loop(10, <compound (:)/2>, _1206, [])
ERROR:     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR:     [17] user:hist(<compound (',')/2>, 10, num)
ERROR:     [16] user:hist1n(<compound (',')/2>, 10)
ERROR: 
ERROR: Use the --stack_limit=size[KMG] command line option or
ERROR: ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (16) _274=true ? creep
   Exit: (16) true=true ? no debug
?- 

?- N=36, K=10, time( hist1n((findall( I, between(1,N,I), L ), select_n( A, L, K )), K )).
% 761,667,076 inferences, 54.922 CPU in 55.500 seconds (99% CPU, 13868191 Lips)
ERROR: [Thread 3] Stack limit (1.0Gb) exceeded
ERROR: [Thread 3]   Stack sizes: local: 10Kb, global: 38Kb, trail: 1Kb
ERROR: [Thread 3]   Stack depth: 25, last-call: 32%, Choice points: 47
ERROR: [Thread 3]   In:
ERROR: [Thread 3]     [25] system:'$add_findall_bag'(10)
ERROR: [Thread 3]     [24] '$bags':findall_loop(10, <compound (:)/2>, _1216, [])
ERROR: [Thread 3]     [23] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR: [Thread 3]     [19] user:hist(<compound (',')/2>, 10, num)
ERROR: [Thread 3]     [18] user:hist1n(<compound (',')/2>, 10)
ERROR: [Thread 3] 
ERROR: [Thread 3] Use the --stack_limit=size[KMG] command line option or
ERROR: [Thread 3] ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (18) _284=true ? no debug
?- 

?- N=36, K=10, time( hist1n((findall( I, between(1,N,I), L ), subsequence( K, L, A )), K )).
% 2,814,715,190 inferences, 168.453 CPU in 170.962 seconds (99% CPU, 16709190 Lips)
ERROR: Stack limit (1.0Gb) exceeded
ERROR:   Stack sizes: local: 7Kb, global: 19Kb, trail: 0Kb
ERROR:   Stack depth: 23, last-call: 26%, Choice points: 21
ERROR:   In:
ERROR:     [23] system:'$add_findall_bag'(10)
ERROR:     [22] '$bags':findall_loop(10, <compound (:)/2>, _5884, [])
ERROR:     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR:     [17] user:hist(<compound (',')/2>, 10, num)
ERROR:     [16] user:hist1n(<compound (',')/2>, 10)
ERROR: 
ERROR: Use the --stack_limit=size[KMG] command line option or
ERROR: ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (16) _1692=true ? no debug
?- 

?- N=36, findall( I, between(1,N,I), L ), member(K,L), nl, write(K:' '), time( ( findall( 1, subsequence( K, L, A ), H ), length( H, Y ), write( Y ) ) ), fail; true.

1: 36
% 9,513 inferences, 0.000 CPU in 0.001 seconds (0% CPU, Infinite Lips)

2: 630
% 111,765 inferences, 0.000 CPU in 0.007 seconds (0% CPU, Infinite Lips)

3: 7140
% 960,783 inferences, 0.016 CPU in 0.061 seconds (25% CPU, 61490112 Lips)

4: 58905
% 6,423,891 inferences, 0.375 CPU in 0.379 seconds (99% CPU, 17130376 Lips)

5: 376992
% 34,761,837 inferences, 2.172 CPU in 2.241 seconds (97% CPU, 16005450 Lips)

6: 1947792
% 156,451,713 inferences, 9.562 CPU in 9.636 seconds (99% CPU, 16360963 Lips)

7: 8347680
% 597,276,537 inferences, 35.781 CPU in 36.281 seconds (99% CPU, 16692445 Lips)

8: 30260340
% 1,962,864,233 inferences, 122.062 CPU in 123.650 seconds (99% CPU, 16080813 Lips)

9: 
% 689,482,442 inferences, 59.109 CPU in 59.973 seconds (99% CPU, 11664519 Lips)
ERROR: [Thread 3] Stack limit (1.0Gb) exceeded
ERROR: [Thread 3]   Stack sizes: local: 10Kb, global: 0.7Gb, trail: 0Kb
ERROR: [Thread 3]   Stack depth: 23, last-call: 26%, Choice points: 48
ERROR: [Thread 3]   In:
ERROR: [Thread 3]     [23] system:'$add_findall_bag'(1)
ERROR: [Thread 3]     [22] '$bags':findall_loop(1, <compound (:)/2>, _1520, [])
ERROR: [Thread 3]     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR: [Thread 3]     [18] system:'<meta-call>'(<compound (:)/2>)
ERROR: [Thread 3]     [17] system:catch(<compound (:)/2>, _1622, <compound (:)/2>)
ERROR: [Thread 3] 
ERROR: [Thread 3] Use the --stack_limit=size[KMG] command line option or
ERROR: [Thread 3] ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (18) _584=true ? no debug
?- 


?- N=36, findall( I, between(1,N,I), L ), member(K,L), nl, write(K:' '), time( ( findall( 1, select_n( A, L, K ), H ), length( H, Y ), write( Y ) ) ), fail; true.

1: 36
% 2,084 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)

2: 630
% 24,728 inferences, 0.000 CPU in 0.003 seconds (0% CPU, Infinite Lips)

3: 7140
% 215,093 inferences, 0.000 CPU in 0.017 seconds (0% CPU, Infinite Lips)

4: 58905
% 1,456,739 inferences, 0.078 CPU in 0.106 seconds (74% CPU, 18646259 Lips)

5: 376992
% 7,995,194 inferences, 0.578 CPU in 0.593 seconds (97% CPU, 13829525 Lips)

6: 1947792
% 36,556,826 inferences, 2.766 CPU in 2.788 seconds (99% CPU, 13218287 Lips)

7: 8347680
% 142,085,414 inferences, 10.969 CPU in 11.033 seconds (99% CPU, 12953656 Lips)

8: 30260340
% 476,688,254 inferences, 38.734 CPU in 39.285 seconds (99% CPU, 12306595 Lips)

9: 
% 689,482,442 inferences, 59.109 CPU in 59.973 seconds (99% CPU, 11664519 Lips)
ERROR: [Thread 3] Stack limit (1.0Gb) exceeded
ERROR: [Thread 3]   Stack sizes: local: 10Kb, global: 0.7Gb, trail: 0Kb
ERROR: [Thread 3]   Stack depth: 23, last-call: 26%, Choice points: 48
ERROR: [Thread 3]   In:
ERROR: [Thread 3]     [23] system:'$add_findall_bag'(1)
ERROR: [Thread 3]     [22] '$bags':findall_loop(1, <compound (:)/2>, _1520, [])
ERROR: [Thread 3]     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR: [Thread 3]     [18] system:'<meta-call>'(<compound (:)/2>)
ERROR: [Thread 3]     [17] system:catch(<compound (:)/2>, _1622, <compound (:)/2>)
ERROR: [Thread 3] 
ERROR: [Thread 3] Use the --stack_limit=size[KMG] command line option or
ERROR: [Thread 3] ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (18) _584=true ? no debug
?- 

?- N=25, findall( I, between(1,N,I), L ), member(K,L), write(K:' '), time( ( findall( 1, subsequence( K, L, A ), H ), length( H, Y ), write( Y ) ) ), fail; true.

1: 25
% 4,684 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)
2: 300
% 37,922 inferences, 0.000 CPU in 0.004 seconds (0% CPU, Infinite Lips)
3: 2300
% 222,122 inferences, 0.000 CPU in 0.016 seconds (0% CPU, Infinite Lips)
4: 12650
% 999,142 inferences, 0.047 CPU in 0.069 seconds (68% CPU, 21315029 Lips)
5: 53130
% 3,587,562 inferences, 0.234 CPU in 0.230 seconds (102% CPU, 15306931 Lips)
6: 177100
% 10,555,182 inferences, 0.656 CPU in 0.644 seconds (102% CPU, 16084087 Lips)
7: 480700
% 25,919,872 inferences, 1.641 CPU in 1.648 seconds (100% CPU, 15798779 Lips)
8: 1081575
% 53,838,422 inferences, 3.469 CPU in 3.537 seconds (98% CPU, 15520987 Lips)
9: 2042975
% 95,515,112 inferences, 6.312 CPU in 6.410 seconds (98% CPU, 15131107 Lips)
10: 3268760
% 145,757,002 inferences, 9.109 CPU in 9.187 seconds (99% CPU, 16000769 Lips)
11: 4457400
% 192,262,542 inferences, 11.875 CPU in 12.071 seconds (98% CPU, 16190530 Lips)
12: 5200300
% 219,898,422 inferences, 13.672 CPU in 13.740 seconds (100% CPU, 16083999 Lips)
13: 5200300
% 218,412,622 inferences, 13.703 CPU in 13.821 seconds (99% CPU, 15938891 Lips)
14: 4457400
% 188,399,462 inferences, 11.891 CPU in 12.059 seconds (99% CPU, 15844370 Lips)
15: 3268760
% 140,928,152 inferences, 9.016 CPU in 9.069 seconds (99% CPU, 15631545 Lips)
16: 2042975
% 91,140,742 inferences, 5.859 CPU in 5.882 seconds (100% CPU, 15554687 Lips)
17: 1081575
% 50,713,872 inferences, 3.250 CPU in 3.281 seconds (99% CPU, 15604268 Lips)
18: 480700
% 24,110,922 inferences, 1.516 CPU in 1.551 seconds (98% CPU, 15908237 Lips)
19: 177100
% 9,700,042 inferences, 0.641 CPU in 0.633 seconds (101% CPU, 15141529 Lips)
20: 53130
% 3,258,662 inferences, 0.219 CPU in 0.214 seconds (102% CPU, 14896741 Lips)
21: 12650
% 897,482 inferences, 0.062 CPU in 0.059 seconds (106% CPU, 14359712 Lips)
22: 2300
% 197,422 inferences, 0.000 CPU in 0.013 seconds (0% CPU, Infinite Lips)
23: 300
% 33,372 inferences, 0.000 CPU in 0.003 seconds (0% CPU, Infinite Lips)
24: 25
% 4,086 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)
25: 1
% 340 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)
true.


?- N=25, findall( I, between(1,N,I), L ), member(K,L), write(K:' '), time( ( findall( 1, select_n( A, L, K ), H ), length( H, Y ), write( Y ) ) ), fail; true.

1: 25
% 1,039 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)
2: 300
% 8,514 inferences, 0.000 CPU in 0.001 seconds (0% CPU, Infinite Lips)
3: 2300
% 50,764 inferences, 0.000 CPU in 0.006 seconds (0% CPU, Infinite Lips)
4: 12650
% 233,154 inferences, 0.000 CPU in 0.022 seconds (0% CPU, Infinite Lips)
5: 53130
% 858,064 inferences, 0.047 CPU in 0.069 seconds (67% CPU, 18305365 Lips)
6: 177100
% 2,601,234 inferences, 0.188 CPU in 0.204 seconds (92% CPU, 13873248 Lips)
7: 480700
% 6,630,259 inferences, 0.500 CPU in 0.502 seconds (100% CPU, 13260518 Lips)
8: 1081575
% 14,441,634 inferences, 1.062 CPU in 1.101 seconds (97% CPU, 13592126 Lips)
9: 2042975
% 27,252,289 inferences, 2.094 CPU in 2.123 seconds (99% CPU, 13016019 Lips)
10: 3268760
% 45,119,034 inferences, 3.406 CPU in 3.445 seconds (99% CPU, 13245955 Lips)
11: 4457400
% 66,365,974 inferences, 4.969 CPU in 5.106 seconds (97% CPU, 13356674 Lips)
12: 5200300
% 87,910,074 inferences, 6.766 CPU in 7.046 seconds (96% CPU, 12993637 Lips)
13: 5200300
% 223,117,875 inferences, 14.016 CPU in 14.482 seconds (97% CPU, 15919224 Lips)
14: 4457400
% 182,258,375 inferences, 10.594 CPU in 10.898 seconds (97% CPU, 17204330 Lips)
15: 3268760
% 130,106,795 inferences, 7.547 CPU in 7.634 seconds (99% CPU, 17239824 Lips)
16: 2042975
% 80,369,640 inferences, 4.250 CPU in 4.335 seconds (98% CPU, 18910504 Lips)
17: 1081575
% 42,562,585 inferences, 2.250 CPU in 2.315 seconds (97% CPU, 18916704 Lips)
18: 480700
% 19,128,460 inferences, 1.062 CPU in 1.112 seconds (96% CPU, 18003256 Lips)
19: 177100
% 7,205,835 inferences, 0.406 CPU in 0.445 seconds (91% CPU, 17737440 Lips)
20: 53130
% 2,239,445 inferences, 0.109 CPU in 0.128 seconds (85% CPU, 20474926 Lips)
21: 12650
% 562,055 inferences, 0.016 CPU in 0.032 seconds (48% CPU, 35971520 Lips)
22: 2300
% 110,565 inferences, 0.000 CPU in 0.006 seconds (0% CPU, Infinite Lips)
23: 300
% 16,315 inferences, 0.000 CPU in 0.001 seconds (0% CPU, Infinite Lips)
24: 25
% 1,690 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)
25: 1
% 117 inferences, 0.000 CPU in 0.000 seconds (0% CPU, Infinite Lips)
true.

?- N=23, time(hist1n((findall( I, between(1,N,I), L ), member(K,L), subsequence( K, L, A ) ), K )).
% 587,202,582 inferences, 29.781 CPU in 30.391 seconds (98% CPU, 19717191 Lips)
ERROR: Stack limit (1.0Gb) exceeded
ERROR:   Stack sizes: local: 2Kb, global: 0.4Gb, trail: 0Kb
ERROR:   Stack depth: 23, last-call: 26%, Choice points: 9
ERROR:   In:
ERROR:     [23] system:'$collect_findall_bag'(_1172, [])
ERROR:     [21] '$bags':cleanup_bag(<compound (:)/2>, <compound (:)/2>)
ERROR:     [18] '$bags':bagof(*, <compound (:)/2>, _1240)
ERROR:     [17] user:hist('<garbage_collected>', _1272, num)
ERROR:     [16] user:hist1n(<compound (',')/2>, _1300)
ERROR: 
ERROR: Use the --stack_limit=size[KMG] command line option or
ERROR: ?- set_prolog_flag(stack_limit, 2_147_483_648). to double the limit.
   Call: (16) _274=true ? no debug
?- N=22, time(hist1n((findall( I, between(1,N,I), L ), member(K,L), subsequence( K, L, A ) ), K )).

 [1,22]
 [2,231]
 [3,1540]
 [4,7315]
 [5,26334]
 [6,74613]
 [7,170544]
 [8,319770]
 [9,497420]
 [10,646646]
 [11,705432]
 [12,646646]
 [13,497420]
 [14,319770]
 [15,170544]
 [16,74613]
 [17,26334]
 [18,7315]
 [19,1540]
 [20,231]
 [21,22]
 [22,1]
total:4194303
% 494,927,997 inferences, 27.109 CPU in 27.563 seconds (98% CPU, 18256710 Lips)
N = 22.

?- 

?- N=22, time(hist1n((findall( I, between(1,N,I), L ), member(K,L), select_n( A, L, K ) ), K )).

 [1,22]
 [2,231]
 [3,1540]
 [4,7315]
 [5,26334]
 [6,74613]
 [7,170544]
 [8,319770]
 [9,497420]
 [10,646646]
 [11,705432]
 [12,646646]
 [13,497420]
 [14,319770]
 [15,170544]
 [16,74613]
 [17,26334]
 [18,7315]
 [19,1540]
 [20,231]
 [21,22]
 [22,1]
total:4194303
% 329,417,337 inferences, 16.594 CPU in 17.073 seconds (97% CPU, 19851892 Lips)
N = 22.


*/





% A naiive versions

%1. using a maplist.

zero_one( 0 ).
zero_one( 1 ).

seq01n( N, X ):-
	 length( X, N ),
	 maplist( zero_one, X ).

%2. using a recursion.

projection( [ ], [ ], H, H1 ):- reverse( H, H1 ).
projection( [ _ | A ], [ 0 | P ], L, H ):-
	 projection( A, P, L, H ).
projection( [ X | A ], [ 1 | P ], L, H ):-
	 projection( A, P, [ X | L ], H ).

projection( X, P, H ):-
	 projection( X, P, [ ], H ).

projectionx( P, H ):-
	 mapx( take_or_leave, P, G ),
	 reverse( G, M ), 
	 subtract( M, [0], H ).


% complementary projection
%--------------------------------------------------
complementary_map( [], [], [] ).
complementary_map( [1|Y], [_|B], C ):-
	 complementary_map( Y, B, C ).
complementary_map( [0|Y], [A|B], [A|C] ):-
	 complementary_map( Y, B, C ).


complementary_map2(Mask, List, Result) :-
    complementary_map_acc(Mask, List, [], Result).

complementary_map_acc([], [], Acc, Acc).
complementary_map_acc([1|Y], [_|B], Acc, Result) :-
    complementary_map_acc(Y, B, Acc, Result).
complementary_map_acc([0|Y], [A|B], Acc, Result) :-
    complementary_map_acc(Y, B, [A|Acc], Result).



% 任意のゴールをAxiomに

condx( Goal, Vars, Values ) :-
	 term_variables( Goal, Vars ),
	 copy_term( Goal, G ),
	 term_variables( G, Values ),
	 call( G ).

/*

?- condx( (member(X,[1,2]), Y is X+4, Z = X^2 + Y), M, V).
M = [X, Y, Z],
V = [1, 5, 1^2+5] ;
M = [X, Y, Z],
V = [2, 6, 2^2+6].

*/

debug_goal(Goal) :-
	 condx(Goal, Names, Values),
	 numbervars( Goal ),
	 maplist(write_pair, Names, Values).

write_pair(Name, Value) :-
    format('~w = ~w;\t', [Name, Value]).


/*

?- G= (member(X,[1,2]), Y is X+4, Z = X^2 + Y), debug_goal( G ).
A = 1;  B = 5;  C = 1^2+5;      
G = (member(A, [1, 2]), B is A+4, C=A^2+B),
X = A,
Y = B,
Z = C .

?- 
*/

% テーブル形式

writeln_pair(Name, Value) :-
    format('~w = ~w~n', [Name, Value]).

table_goal(_) :-
	 format('~`-t~50|~n'),  % 区切り線
	 fail.
table_goal(Goal) :-
	 condx(Goal, Names, Values),
	 numbervars(Goal),
	 maplist(writeln_pair, Names, Values),
	 format('~`-t~50|~n').

/*

?- G= (member(X,[1,2]), Y is X+4, Z = X^2 + Y), table_goal( G ).
--------------------------------------------------
A = 1
B = 5
C = 1^2+5
--------------------------------------------------
G = (member(A, [1, 2]), B is A+4, C=A^2+B),
X = A,
Y = B,
Z = C .

*/

table_all_solutions(Goal) :-
    table_goal(Goal),
    fail.
table_all_solutions(_).


/*

?- G= (member(X,[1,2]), Y is X+4, Z = X^2 + Y), table_all_solutions( G ).
--------------------------------------------------
A = 1
B = 5
C = 1^2+5
--------------------------------------------------
A = 2
B = 6
C = 2^2+6
--------------------------------------------------
G = (member(X, [1, 2]), Y is X+4, Z=X^2+Y).

*/




%--------------------------------------------------
% earlier code 
%--------------------------------------------------

%:- [lib2025].

subsequence_length(0, _, []).
subsequence_length(N, [H|T], [H|Sub]) :-
    N > 0,
    N1 is N - 1,
    subsequence_length(N1, T, Sub).
subsequence_length(N, [_|T], Sub) :-
    N > 0,
    subsequence_length(N, T, Sub).


alternatives( [a,b,c] ).
persons( [1,2] ).

%focus_and_frame( Data, Focus, Frame ):- select( Focus, Data, _, Frame ).

alternative( X ):- alternatives( A ), select( X, A, _ ).
person( I ):- persons( G ), select( I, G, _ ).

x( X ):- alternative( X ).


ranking( Q ):-
	 alternatives( A ),
	 permutation( A, Q ).

profile( P ):-
	 alternatives( A ),
	 persons( I ),
	 length( I, N ),
	 length( P, N ),
	 maplist( permutation( A ), P ).


all_rankings( W ):-
	 findall( Q, ranking( Q ), W ).

full_domain( U ):-
	 findall( P, profile( P ), U ).

dpair(X, Y):- alternative( X ), alternative( Y ), X \= Y.

precedence( List, Before, After ):- 
	 append( _, [ Before | Z ], List ),
	 member( After, Z ).

unanimous( X, Y, P ):-
	 dpair( X, Y ), 
	 forall( member( R, P ), p( X, Y, R ) ).

pareto( P - S ):-
	 ranking( S ),
	 forall( unanimous( X, Y, P ), p( X, Y, S ) ).

p( X, Y, R ):-
	 ranking( R ),
	 dpair( X, Y ),
	 precedence( R, X, Y ).


iia( P - S, F ):-
	 \+ not_iia( P - S, F, _ ).

not_iia( P - S, F, [ X, Y, P1 - T ] ):-
	 p( X, Y, S ),
	 once((
		 member( P1 - T, F ),
		 \+ reversal_pair( P -> P1, (X, Y), _ ) 
	 )),
	 \+ p( X, Y, T ).

axiom( swf, P, ( P - S ), F, _ ):- 
	 ranking( S ),
	 pareto( P - S ),
	 iia( P - S, F ).


reversal_pair( P1 -> P2, (X, Y), R->Q ):-
	 profile( P1 ),
	 profile( P2 ),
	 nth1( J, P1, R ),
	 nth1( J, P2, Q ),
	 p( X, Y, R ),
	 p( Y, X, Q ).


/*

?- hist( ( pairwise_reversal( X, Y, P1, P2 ) ), X:Y ).

 (a:b):108
 (a:c):108
 (b:a):108
 (b:c):108
 (c:a):108
 (c:b):108
total:648
true.

*/


values_in_a_row( F, N, SWF ):- 
	 all_rankings( W ),
	 findall( J, ( member( _-S, F ), nth1( J, W, S )), E ), 
	 length( E, N ),
	 atomic_list_concat( E, SWF ).


/*

?- full_domain( U ), mapx( swf, U, F ), values_in_a_row( F, N, SWF ), nl, write( SWF; N ), fail.

666666555555444444333333222222111111;36
654321654321654321654321654321654321;36
false.


% debug

?- full_domain( U ), mapx( swf, U, F ), values_in_a_row( F, N, SWF ), nl, write( SWF; N ), fail.

111111111111111111111111111111111111;36
222222222222222222222222222222222222;36
333333333333333333333333333333333333;36
444444444444444444444444444444444444;36
555555555555555555555555555555555555;36
666666666666666666666666666666666666;36
false.

*/



findall_nv( B, A, H ):-
       findall( B, ( A, \+ var( B ) ), H ).

hist( A, B ):-
      findall_nv( B, A, C ),
      sort( C, D ),
      \+ (
		bagof( '*', ( member( B, D ), member( B, C ) ), E ),
	    length( E, X ),
		nl,
	    tab( 1 ),
	    \+ write(  B: X  )
	  ),
	  nl,
      length( C, N ),
      write( total : N ).

/*

?- hist( ( setof( S, X^Y^( profile( P ), unanimous( X, Y, P ), pareto( P-S )  ),  L ), length( L, N ) ), N:P=>L ).

 (1:[[a,b,c],[a,b,c]]=>[[a,b,c]]):1
 (1:[[a,c,b],[a,c,b]]=>[[a,c,b]]):1
 (1:[[b,a,c],[b,a,c]]=>[[b,a,c]]):1
 (1:[[b,c,a],[b,c,a]]=>[[b,c,a]]):1
 (1:[[c,a,b],[c,a,b]]=>[[c,a,b]]):1
 (1:[[c,b,a],[c,b,a]]=>[[c,b,a]]):1
 (2:[[a,b,c],[a,c,b]]=>[[a,b,c],[a,c,b]]):1
 (2:[[a,b,c],[b,a,c]]=>[[a,b,c],[b,a,c]]):1
 (2:[[a,c,b],[a,b,c]]=>[[a,b,c],[a,c,b]]):1
 (2:[[a,c,b],[c,a,b]]=>[[a,c,b],[c,a,b]]):1
 (2:[[b,a,c],[a,b,c]]=>[[a,b,c],[b,a,c]]):1
 (2:[[b,a,c],[b,c,a]]=>[[b,a,c],[b,c,a]]):1
 (2:[[b,c,a],[b,a,c]]=>[[b,a,c],[b,c,a]]):1
 (2:[[b,c,a],[c,b,a]]=>[[b,c,a],[c,b,a]]):1
 (2:[[c,a,b],[a,c,b]]=>[[a,c,b],[c,a,b]]):1
 (2:[[c,a,b],[c,b,a]]=>[[c,a,b],[c,b,a]]):1
 (2:[[c,b,a],[b,c,a]]=>[[b,c,a],[c,b,a]]):1
 (2:[[c,b,a],[c,a,b]]=>[[c,a,b],[c,b,a]]):1
 (3:[[a,b,c],[b,c,a]]=>[[a,b,c],[b,a,c],[b,c,a]]):1
 (3:[[a,b,c],[c,a,b]]=>[[a,b,c],[a,c,b],[c,a,b]]):1
 (3:[[a,c,b],[b,a,c]]=>[[a,b,c],[a,c,b],[b,a,c]]):1
 (3:[[a,c,b],[c,b,a]]=>[[a,c,b],[c,a,b],[c,b,a]]):1
 (3:[[b,a,c],[a,c,b]]=>[[a,b,c],[a,c,b],[b,a,c]]):1
 (3:[[b,a,c],[c,b,a]]=>[[b,a,c],[b,c,a],[c,b,a]]):1
 (3:[[b,c,a],[a,b,c]]=>[[a,b,c],[b,a,c],[b,c,a]]):1
 (3:[[b,c,a],[c,a,b]]=>[[b,c,a],[c,a,b],[c,b,a]]):1
 (3:[[c,a,b],[a,b,c]]=>[[a,b,c],[a,c,b],[c,a,b]]):1
 (3:[[c,a,b],[b,c,a]]=>[[b,c,a],[c,a,b],[c,b,a]]):1
 (3:[[c,b,a],[a,c,b]]=>[[a,c,b],[c,a,b],[c,b,a]]):1
 (3:[[c,b,a],[b,a,c]]=>[[b,a,c],[b,c,a],[c,b,a]]):1
total:30
true.
*/


sc_environment( Alternatives, Members, AllRankings, FullDomain, NumberOfProfiles ):-
	 alternatives( Alternatives ),
	 persons( Members ),
	 all_rankings( AllRankings ),
	 full_domain( FullDomain ), 
	 length( FullDomain, NumberOfProfiles ).

/*

?- sc_environment( Alternatives, Members,  W, _, P ).
Alternatives = [a, b, c],
Members = [1, 2],
W = [[a, b, c], [a, c, b], [b, a, c], [b, c, a], [c, a, b], [c, b, a]],
P = 36.

*/


