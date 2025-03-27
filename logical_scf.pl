/* social choice theory in prolog: 
 integrated generation of the Gibbard-Satterthwaite-type and Arrow-type scfs
 extended with a logical formula translator: web supplement of Indo, K., 
 Experimental Study of Strategy-Proofness in Abstract Social Choice Functions Using Logic Programming. Research Bulletin of Economics, Kanto Gakuen University, 51, 1-64. (Japanese) 
*/
 * Copyright © 2025 Kenryo Indo
 * Licensed under the MIT License.
 * See LICENSE file in the project root for license information.
*/

% SWISH version of this program is available: https://swish.swi-prolog.org/p/saPQDdZf.pl

%
alternatives( [a,b,c] ).
%alternatives( [x,y,z] ).
%として代替案や選好順序を次のように生成することができる．
x( X ):- alternatives( A ), member( X, A ).
ranking( R ):- alternatives( A ), permutation( A, R ).
best( X, R ):- R = [ X | _ ]. % nth1( 1, R, X )でもよい
p( X, Y, R ):- append( _, [ X | P ], R ), member( Y, P ).
%ここで置換permutation/2，結合append/2，要素member/2といったリスト演算はISO標準に準拠したProlog処理系に備わっている．具体的なデータベース述語findall/3を用いて予め全ての順序を番号付きで生成しておくとあとで便利である．
all_rankings( D ):- findall( Q, ranking( Q ), D ).
rc( J, R ):- all_rankings( D ), nth1( J, D, R ).
%プロフィールやSCFもリストとして表現できる．任意人数のプロフィールを生成してみよう．
pp( N, P ):-
	 length( Indices, N ),
	 maplist( rc, Indices, P ).
number_of_persons( 2 ).
pp( P ):- number_of_persons( N ), pp( N, P ).
unrestricted_domain( U ):- findall( P, pp( P ), U ).
%もちろん再帰を明示的に用いてもよいが，ここではmaplistを用いている． maplistはループを明示的に書かない記法であり，モダンな手続き型言語，たとえばPythonやJavascriptでも用いられている．ノンインポーズド条件や独裁性は次のようになる．ただし\+は否定オペレータであり全称の条件を意味している（Prologの標準述語forall( A, B )は \+ ( A, \+ B ) として定義されることに注意する）．
non_imposed( F ):-
	 \+ (
		 x( X ),
		 \+ member( _ - X, F )
	 ).
dictatorial_scf( gs-type, J, [ PP1 - A | F ] ):-
	 nth1( J, PP1, R1 ),
	 best( A, R1 ),
	 \+ (
		 member( PP - X, F ),
		 nth1( J, PP, R ),
		 \+ best( X, R )
	 ).
dictatorial_scf( arrow-type, J, [ P - A | F ] ):-
	 nth1( J, P, A ),
	 \+ (
		 member( PP - S, F ),
		 nth1( J, PP, R ),
		 S \= R
	 ).

%耐戦略的かつノンインポーズドなSCFの論理プログラムはそれぞれの満たす論理条件を，再帰を用いて，ほぼ直接的に書くことができる． 
scf( Type, F, D ):-
	 f( Type, F, D, [ ] ).
%独裁性のテストを追加
scf( Type, F, D, Z ):-
	 scf( Type, F, D ),
	 ( dictatorial_scf( Type, J, F ) -> W=dict(J); W=poss ),
	 Z = W.

%ここで述語f/3は定義域Dにおいて第3引数に与えた公理的条件を累積変数の下で満たすように再帰的に関数Fを構成する．具体的に以下のようなソースコードである．
f( _, F, [ ], F ).
f( Axiom, F, [ X | D ], A ):-
%	 apply( Axiom, [ X, Y, A ] ), %swish上ではsandbox制限あり
	 scf_axiom( Axiom, X, Y, A, D ),
	 f( Axiom, F, D, [ X - Y | A ] ).
%SCFの公理とその中で用いる耐戦略性（ノンマニピュラビリティ）は以下のようになる．
scf_axiom( gs-type, X, Y, F, D ):-
	 x( Y ),
	 \+ manipulable( _, X - Y, _, F ),
	 ( D = [ ] -> non_imposed( [ X-Y | F ] ); true ).
scf_axiom( arrow-type, P, Q, F, _ ):-
	 ranking( Q ),
	 pareto( P - Q ),
	 iia( P - Q, F ).
manipulable( 1, [ R, Q ] - S, [ P, Q ] - T, F ):-
	 member( [ P, Q ] - T, F ),
	 ( p( T, S, R ); p( S, T, P ) ).
manipulable( 2, [ R, Q ] - S, [ R, W ] - T, F ):-
	 member( [ R, W ] - T, F ),
	 ( p( T, S, Q ); p( S, T, W ) ).
manipulable_n( J, PP - S, F ):-
 	member( PP1 - T, F ),
	append( A, [ R | B ], PP ),
	append( A, [ Q | B ], PP1 ),
	length( [ _ | A ], J ),
	( p( T, S, R ); p( S, T, Q ) ).

%以上の準備から，基本ケースのGS定理およびArrowの定理を自動証明することができる． 
prove( A ):-
	 unrestricted_domain( U ),
	 scf( A-type, F, U, Z ),
	 fig( A-type, F ),
	 writeln( Z ),
	 fail.
% ?- unrestricted_domain( D ), scf( gs-type, F, D, Z ).
% ?- prove(gs).
% ?- prove(arrow).


%独裁領域か可能領域かを確認する
check_scf( T, D, Z ):-
	 ( \+ scf( T, _, D, poss ) -> Z=dict; Z=poss ).
% SCF数のカウント（0のときが独裁領域）
count_scf( T, D, Z, N ):-
	 findall( 1, scf( T, _, D, Z ), L ),
	 length( L, N ).

%-----------------------------------------------------------------
% Arrow's axiom of swf
%-----------------------------------------------------------------
swf( F, D, Z ):- scf( arrow-type, F, D, Z ).
swf( F, Z ):- unrestricted_domain( D ), swf( F, D, Z ).

agree( +, X, Y, [ P, Q ] ):-
	 p( X, Y, P ),
	 p( X, Y, Q ).
agree( -, X, Y, [ P, Q ] ):-
	 agree( +, Y, X, [ P, Q ] ).

unanimous( _, _, _, [ ] ).
unanimous( X, Y, P, [ Q | L ] ):-
	 agree( +, X, Y, [ P, Q ] ),
	 unanimous( X, Y, Q, L ).

unanimous( X, Y, [ P | L ] ):-
	 unanimous( X, Y, P, L ).

/*
 pp( [P,Q] ), P\=Q, !, writeln([P,Q]), unanimous( X, Y, [P,Q] ), writeln( X-Y ), fail.
[[a, b, c], [a, c, b]]
a-b
a-c
false

*/

pareto( PP - S ):-
	 \+ (
		 unanimous( X, Y, PP ),
		 \+ p( X, Y, S )
	 ).

iia( PP - S, F ):-
	 \+ (
		 x( A ),
		 x( B ),
		 member( PP1 - T, F ),
		 \+ (
			 nth1( K, PP, P ),
			 nth1( K, PP1, Q ),
			 \+ agree( _, A, B, [ P, Q ] )
		 ),
		 \+ agree( _, A, B, [ S, T ] )
	 ).


%-----------------------------------------------------------------
% 制限領域を生成する
%-----------------------------------------------------------------

% 領域の指標表示
indexed_pp( X, PP ):-
	 maplist( rc, X, PP ).

indexed_profiles( X, D ):- 
	 maplist( maplist( rc ), X, D ).

/*  
indexed_profiles( L, U ):-
	 ( \+ var( L ) ->  X = R ; \+ var( U ) -> X = I ),
	 !,
	 findall( X, (
		 member( I, L ),
		 maplist( rc, I, R )
	 ), U ).
*/

% 超アロー領域の指標
arrow_ring_index( 1, [[2, 6], [1, 5], [3, 2], [4, 1], [6, 3], [5, 4]] ).
arrow_ring_index( 2, [[6, 2], [5, 1], [2, 3], [1, 4], [3, 6], [4, 5]] ).
arrow_ring_index( both, I ):-
	 arrow_ring_index( 1, I1 ),
	 arrow_ring_index( 2, I2 ),
	 append( I1, I2, I ).

arrow_ring( X, M ):-
	 arrow_ring_index( X, I ),
	 indexed_profiles( I, M ).


/*
?- arrow_ring( 1, M ), T=arrow-type, scf(T, F, M ), fig( T, F ), fail.

           1  2  3  4  5  6  
           ------------------
1:[a,b,c]  -  -  -  -  1  -  
2:[a,c,b]  -  -  -  -  -  2  
3:[b,a,c]  -  3  -  -  -  -  
4:[b,c,a]  4  -  -  -  -  -  
5:[c,a,b]  -  -  -  5  -  -  
6:[c,b,a]  -  -  6  -  -  -  
--

           1  2  3  4  5  6  
           ------------------
1:[a,b,c]  -  -  -  -  5  -  
2:[a,c,b]  -  -  -  -  -  6  
3:[b,a,c]  -  2  -  -  -  -  
4:[b,c,a]  1  -  -  -  -  -  
5:[c,a,b]  -  -  -  4  -  -  
6:[c,b,a]  -  -  3  -  -  -  
--
false.

*/

%?- T=gs-type, arrow_ring( 1, D ), scf( T, F, D, Z ).

/*
?- hist((arrow_ring(1, M ), select_n(D,M,K), count_scf( arrow-type, D, poss, NP ),  count_scf( arrow-type, D, dict(_), ND )), K-profiles:NP:ND ).

 (0-profiles:1:0):1
 (1-profiles:1:2):6
 (2-profiles:2:2):6
 (2-profiles:7:2):9
 (3-profiles:3:2):6
 (3-profiles:10:2):12
 (3-profiles:25:2):2
 (4-profiles:4:2):6
 (4-profiles:13:2):6
 (4-profiles:14:2):3
 (5-profiles:5:2):6
 (6-profiles:0:2):1
total:64
true.

*/

ranking_to_0_1_pattern( R, V, W, S ):-
	( p( V, W, R )-> S =1 ; S=0 ). 

profile_as_0_1_pattern( X, Z ):-
	 pp( X ),
	 findall( (V, W): L, (
		 x( V ),
		 x( W ),
		 V @< W,
		 findall( S, (
			 member( R, X ), 
			 ranking_to_0_1_pattern( R, V, W, S )
		 ), L )
	 ), Z ). 


unanimous_for_a_single_pair( P ):-
	 profile_as_0_1_pattern( P, S ),
	 findall( 1, member( (_,_): [X,X], S ), [ _ ] ).

common_subprofile_for_a_pair( P, Q, X, Y, S ):-
	 profile_as_0_1_pattern( P, S1 ),
	 profile_as_0_1_pattern( Q, S2 ),
	 intersection( S1, S2, [(X,Y): S ] ).

single_pair_inversion( P, Q ):-
	 unanimous_for_a_single_pair( P ),
	 unanimous_for_a_single_pair( Q ),
	 common_subprofile_for_a_pair( P, Q, _, _, _ ).

/*

?- setof( P, Q^single_pair_inversion( P, Q ), L ), length( L, N ), fig( domain, L ).


           1  2  3  4  5  6  
           ------------------
1:[a,b,c]  -  -  -  1  2  -  
2:[a,c,b]  -  -  3  -  -  4  
3:[b,a,c]  -  5  -  -  -  6  
4:[b,c,a]  7  -  -  -  8  -  
5:[c,a,b]  9  -  -  10 -  -  
6:[c,b,a]  -  11 12 -  -  -  
--
L = [[[a, b, c], [b, c, a]], [[a, b, c], [c, a, b]], [[a, c, b], [b, a, c]], [[a, c, b], [c, b, a]], [[b, a, c], [a, c|...]], [[b, a|...], [c|...]], [[b|...], [...|...]], [[...|...]|...], [...|...]|...],
N = 12.

*/


ranking_triple_to_0_1( R, [X,Y,Z], [S1,S2,S3] ):-
	alternatives( A ),
	append( _, [ X | B ], A ),
	append( _, [ Y | C ], B ),
	member( Z, C ),
	ranking( R ),
	ranking_to_0_1_pattern( R, X, Y, S1 ),
	ranking_to_0_1_pattern( R, Y, Z, S2 ),
	ranking_to_0_1_pattern( R, Z, X, S3 ).

profile_according_to_edge( P, Q ):-
	 edge( S1, S2, V ),
	 edge( S3, S4, V ),
	 S1 \= S3, 
	 ranking_triple_to_0_1( P1, _, S1 ),
	 ranking_triple_to_0_1( Q1, _, S2 ),
	 ranking_triple_to_0_1( P2, _, S3 ),
	 ranking_triple_to_0_1( Q2, _, S4 ),
	 P = [ P1, P2 ],
	 Q = [ Q1, Q2 ].

% Arrow環はこのグラフにマップする（第2順序は位相が2ずれる）

%:- use_rendering( graphviz ). 

draw_network( digraph( [ rankdir = 'LR' | Graph ] ) ):-
    findall(edge(((P)-> (Q)), [label=L:S]), (
		 edge_and_switch(X, Y, S, L ),
		 node( X, P ),
		 node( Y, Q ) 
	), Graph ).

node( [ 0, 0, 0 ], 'nul' ).
node( [ 1, 0, 0 ], 'acb' ).
node( [ 0, 1, 0 ], 'bac' ).
node( [ 0, 0, 1 ], 'cba' ).
node( [ 1, 1, 0 ], 'abc' ).
node( [ 1, 0, 1 ], 'cab' ).
node( [ 0, 1, 1 ], 'bca' ).
node( [ 1, 1, 1 ], 'nul' ).

edge( P, Q, S ):-
	 edge( P, Q, S, _ ).

edge( P, Q, -, A ):-
	 node( P, _ ),
	 sum_list( P, 2 ),
	 append( A, [ 1 | B ], P ),
	 node( Q, _ ),
	 append( A, [ 0 | B ], Q ).

edge( P, Q, +, A ):-
	 node( P, _ ),
	 sum_list( P, 1 ),
	 append( A, [ 0 | B ], P ),
	 node( Q, _ ),
	 append( A, [ 1 | B ], Q ).

edge_and_switch( P, Q, S, X ):-
	 edge( P, Q, S, A ),
	 switched_direction( A, X ).

switched_direction( A, X ):-
    length( A, N ),
    length( F, N ),
    append( F, [X|_], [ab,bc,ca] ).

/*

?- setof(X,A^profile_according_to_edge( X, A ),D), fig(domain,D ), count_scf( gs-type, D, poss, Z ).


           1  2  3  4  5  6  
           ------------------
1:[a,b,c]  -  -  -  1  2  -  
2:[a,c,b]  -  -  3  -  -  4  
3:[b,a,c]  -  5  -  -  -  6  
4:[b,c,a]  7  -  -  -  8  -  
5:[c,a,b]  9  -  -  10 -  -  
6:[c,b,a]  -  11 12 -  -  -  
--
D = [[[a, b, c], [b, c, a]], [[a, b, c], [c, a, b]], [[a, c, b], [b, a, c]], [[a, c, b], [c, b, a]], [[b, a, c], [a, c|...]], [[b, a|...], [c|...]], [[b|...], [...|...]], [[...|...]|...], [...|...]|...],
Z = 1341.

?- 

*/


generate_dictatorial_domain( A, D, K ):-
	 member( A, [ arrow, gs ] ),
	 unrestricted_domain( U ),
	 length( U, N ),
	 between( 1, N, K ),
%	 write( [ K ] ),
	 select_n( D, U, K ),
	 \+ scf( A-type, _, D, poss ).


generate_quasi_super_dictatorial_domain( A, D, K ):-
	 generate_dictatorial_domain( A, D, K ),
	 \+ (
		 pp( P ),
		 \+ member( P, D ),
		 scf( A-type, _, [P|D], poss )
	 ).


generate_fragile_dictatorial_domain( A, D, K ):-
	 generate_dictatorial_domain( A, D, K ),
	 \+ (
		 pp( P ),
		 \+ member( P, D ),
		 \+ scf( A-type, _, [P|D], poss )
	 ).

/*

% => Fig.4
?- time(generate_quasi_super_dictatorial_domain( arrow, D, K )), fig( domain, D ).
% 8,765,530,359 inferences, 323.297 CPU in 536.787 seconds (60% CPU, 27112945 Lips)


           1  2  3  4  5  6  
           ------------------
1:[a,b,c]  -  -  -  1  -  -  
2:[a,c,b]  -  -  2  -  -  -  
3:[b,a,c]  -  -  -  -  -  3  
4:[b,c,a]  -  -  -  -  4  - 
5:[c,a,b]  5  -  -  -  -  -  
6:[c,b,a]  -  6  -  -  -  -  
--
D = [[[a, b, c], [b, c, a]], [[a, c, b], [b, a, c]], [[b, a, c], [c, b, a]], [[b, c, a], [c, a, b]], [[c, a, b], [a, b|...]], [[c, b|...], [a|...]]],
K = 6 ;

 ?- time(generate_fragile_dictatorial_domain( arrow, D, K )).

% 115,964,138,808 inferences, 3963.063 CPU in 6931.268 seconds (57% CPU, 29261244 Lips)
D = [[[a, b, c], [a, b, c]], [[a, b, c], [a, c, b]], [[a, c, b], [a, c, b]], [[b, a, c], [b, a, c]], [[b, c, a], [b, c|...]], [[b, c|...], [c|...]], [[c|...], [...|...]], [[...|...]|...]],
K = 8 .

*/

grow_dict_domain( _, _, C, C ).
grow_dict_domain( T, M, H, C ):-
	 member( X, M ),
	 \+ member( X, H ),
	 check_scf( T-type, [ X | H ], dict ),
	 grow_dict_domain( T, M, [ X | H ], C ).

grow_dict_domain_from( T, P, D ):-
	 unrestricted_domain( M ),
	 pp( P ),
	 grow_dict_domain( T, M, [ P ], D ).

/*

?- dynamic(tmp_attain/1), abolish( tmp_attain/1 ), unrestricted_domain( U ), arrow_ring( both, A ), subtract( U, A, B ), grow_dict_domain( arrow, U, A, [X|D] ), length( D, 35 ), \+ clause( tmp_attain( X ), _ ), assert( tmp_attain( X ) ), fail.


?- findall( X, tmp_attain(X), D ), fig( domain, D ).


           1  2  3  4  5  6  
           ------------------
1:[a,b,c]  -  -  -  -  -  -  
2:[a,c,b]  -  -  -  -  -  -  
3:[b,a,c]  -  -  -  -  -  -  
4:[b,c,a]  -  -  -  -  -  -  
5:[c,a,b]  -  8  7  -  6  5  
6:[c,b,a]  4  -  -  3  2  1  
--

?- T = gs-type, hist( ( arrow_ring(1, M ), arrow_ring( both, W ), unrestricted_domain( U ), subtract( U, W, L ), between( 1, 6, K ), select_n( S, L, K ), append( M, S, D ), check_scf( T, D, Z ) ), K:Z).

 (1:poss):24
 (2:poss):276
 (3:poss):2024
 (4:poss):10626
 (5:poss):42504
 (6:dict):1
 (6:poss):134595
total:190050
T = gs-type

?- Z=dict, T = gs-type, hist( ( unrestricted_domain( U ), between( 1, 6, K ), select_n( D, U, K ),  check_scf( T, D, Z ) ), Z:K).

 (1:dict):36
 (2:dict):630
 (3:dict):1068
 (4:dict):2424
 (5:dict):5694
 (6:dict):10940
total:20792
T = gs-type,
Z = dict

?- T = gs-type, hist( ( unrestricted_domain( U ), between( 1, 6, K ), select_n( D, U, K ),  check_scf( T, D, Z ) ), K:Z).

 (1:dict):36
 (2:dict):630
 (3:dict):1068
 (3:poss):6072
 (4:dict):2424
 (4:poss):56481
 (5:dict):5694
 (5:poss):371298
 (6:dict):10940
 (6:poss):1936852
total:2391495
T = gs-type.

*/

%-----------------------------------------------------------------
% Dasgupta(1999)
%-----------------------------------------------------------------
dasgupta1999( original, [
 [zyx, yxz, yxz], [yxz, zyx, yxz], [yxz, yxz, zyx], [yzx, zyx, zxy],
 [yzx, xyz, xyz], [xzy, yxz, xzy], [xyz, xyz, yzx], [yxz, yzx, xyz],
 [yxz, xzy, xzy], [zxy, xzy, zyx], [xzy, xzy, yxz], [xyz, zxy, xzy],
 [xzy, zyx, zyx], [zyx, xzy, zyx], [zxy, zxy, xyz], [xyz, yzx, zxy],
 [zxy, yzx, yzx], [yzx, zxy, yzx], [zyx, zyx, xzy]]
).

dasgupta1999( modified, [
 [zyx, yxz, yxz], [yzx, xyz, xyz], [yxz, xzy, xzy], [xzy, zyx, zyx], [zxy, yzx, yzx],
 [yxz, zyx, yxz], [xzy, yxz, xzy], [zyx, xzy, zyx], [yzx, zxy, yzx], [zxy, xyz, zxy],
 [yxz, yxz, zyx], [xzy, xzy, yxz], [xyz, xyz, yzx], [zxy, zxy, xyz], [zyx, zyx, xzy],
 [yzx, zyx, zxy], [yxz, yzx, xyz], [xyz, zxy, xzy], [xyz, yzx, zxy] ]
).

/*

?- dasgupta1999( original, D ), dasgupta1999( modified, C ), subtract( D, C, E ), subtract( C, D, F ).
D = [[zyx, yxz, yxz], [yxz, zyx, yxz], [yxz, yxz, zyx], [yzx, zyx, zxy], [yzx, xyz, xyz], [xzy, yxz, xzy], [xyz, xyz|...], [yxz|...], [...|...]|...],
C = [[zyx, yxz, yxz], [yzx, xyz, xyz], [yxz, xzy, xzy], [xzy, zyx, zyx], [zxy, yzx, yzx], [yxz, zyx, yxz], [xzy, yxz|...], [zyx|...], [...|...]|...],
E = [[zxy, xzy, zyx]],
F = [[zxy, xyz, zxy]].

*/

dasgupta1999( D ):-
	 dasgupta1999( modified, A ),
	 findall( C, ( member( B, A ), maplist( atom_chars, B, C ) ), D ).

%　=> alternatives( [x,y,z] ).
%　=> number_of_persons( 3 ).

/*

?- dasgupta1999(D), time(check_scf( arrow-type, D, Z )).
13,346,508 inferences, 0.821 CPU in 0.821 seconds (100% CPU, 16255474 Lips)
D = [[[z, y, x], [y, x, z], [y, x, z]], [[y, z, x], [x, y, z], [x, y, z]], [[y, x, z], [x, z, y], [x, z, y]], [[x, z, y], [z, y, x], [z, y, x]], [[z, x, y], [y, z, x], [y, z, x]], [[y, x, z], [z, y, x], [y, x, z]], [[x, z, y], [y, x, z], [x, z, y]], [[z, y, x], [x, z, y], [z, y, x]], [[y, z, x], [z, x, y], [y, z, x]], [[z, x, y], [x, y, z], [z, x, y]], [[y, x, z], [y, x, z], [z, y, x]], [[x, z, y], [x, z, y], [y, x, z]], [[x, y, z], [x, y, z], [y, z, x]], [[z, x, y], [z, x, y], [x, y, z]], [[z, y, x], [z, y, x], [x, z, y]], [[y, z, x], [z, y, x], [z, x, y]], [[y, x, z], [y, z, x], [x, y, z]], [[x, y, z], [z, x, y], [x, z, y]], [[x, y, z], [y, z, x], [z, x, y]]],
Z = dict

?- dasgupta1999(D), member( G, [[P,_,O], [O,P,_],[_,O,P]] ), findall( [P,O], ( member(G,D), O\=P ), L ), fig(domain, L), check_scf( arrow-type, L, Z ), write( Z ), fail.

           1  2  3  4  5  6
           ------------------
1:[x,y,z]  -  9  -  5  12 -
2:[x,z,y]  -  -  8  -  -  10
3:[y,x,z]  6  7  -  -  -  2
4:[y,z,x]  4  -  -  -  3  -
5:[z,x,y]  11 -  -  13 -  -
6:[z,y,x]  -  14 1  -  -  -
--dict

           1  2  3  4  5  6
           ------------------
1:[x,y,z]  -  -  -  4  14 -
2:[x,z,y]  -  -  7  -  -  8
3:[y,x,z]  -  5  -  -  -  1
4:[y,z,x]  12 -  6  -  13 -
5:[z,x,y]  9  -  -  11 -  -
6:[z,y,x]  -  10 2  3  -  -
--dict
           1  2  3  4  5  6
           ------------------
1:[x,y,z]  -  -  -  6  11 -
2:[x,z,y]  -  -  4  -  9  14
3:[y,x,z]  -  8  -  -  -  1
4:[y,z,x]  5  -  -  -  10 -
5:[z,x,y]  13 -  -  12 -  3
6:[z,y,x]  -  7  2  -  -  -
--dict
*/

:- dynamic alternatives/1.
:- dynamic number_of_persons/1.

swich_model( N, Alt ):-
     abolish( alternatives/1 ), 
     abolish( number_of_persons/1), 
     assert( alternatives( Alt ) ), 
     assert( number_of_persons( N ) ).
 
/*
 ?- switch_model( 3, [x,y,z] ).
 ?- hist((dasgupta1999(L), between(16,19,K), select_n( D, L, K ), check_scf( arrow-type, D,
W), setof(X, P^Z^(member(P,D),profile_as_0_1_pattern( P, Z ), member( X, Z )), S ), length(
 S, J) ), K:J:W ).

 (16:22:poss):15
 (16:23:poss):234
 (16:24:poss):720
 (17:23:poss):15
 (17:24:poss):156
 (18:24:poss):19
 (19:24:dict):1
total:1160
true.
?- switch_model( 2, [a,b,c] ).

*/


%-----------------------------------------------------------------
% block of best alternatives 
%-----------------------------------------------------------------

best_alternatives_block( Y, B ):-
    findall( P, ( 
	 pp( P ),
	 maplist( nth1( 1 ), P, Y )
    ), B ).

/*
?- best_alternatives_block( [a,b], B ), fig( domain, B ).

           1  2  3  4  5  6  
           ------------------
1:[a, b, c]  -  -  1  2  -  -  
2:[a, c, b]  -  -  3  4  -  -  
3:[b, a, c]  -  -  -  -  -  -  
4:[b, c, a]  -  -  -  -  -  -  
5:[c, a, b]  -  -  -  -  -  -  
6:[c, b, a]  -  -  -  -  -  -  
*/


composite_domain_list( H, D ):-
	 findall( P,(
		 member( X, H ),
		 member( P, X )
	 ), D ).

composite_blocks( K, B, D ):-
	 findall( block(X,Y), (
		 x( X ),
		 x( Y )
	 ), L ),
	 select_n( B, L, K ),
	 findall( C, (
		 member( block(X,Y), B ),
		 best_alternatives_block( [X,Y], C )
	 ), H ),
	 composite_domain_list( H, D ).

/*
?- composite_blocks( 3, B, D ), fig( membership, D ).


           1  2  3  4  5  6  
           ------------------
1:[a, b, c]  pa pa g2 a2 a1 g2 
2:[a, c, b]  pa pa a2 g1 g1 a1 
3:[b, a, c]  -  -  -  -  -  -  
4:[b, c, a]  -  -  -  -  -  -  
5:[c, a, b]  -  -  -  -  -  -  
6:[c, b, a]  -  -  -  -  -  -  
--
B = [block(a,a), block(a,b), block(a,c)],
D = [[[a, b, c], [a, b, c]], [[a, b, c], [a, c, b]], ...

*/

%-----------------------------------------------------------------
% GS-type dictatorial domains: ring partiton and dictatorial sequence
%-----------------------------------------------------------------

gs_ring_index( [ [2, 4], [2, 5], [3, 1], [3, 5], [6, 1], [6, 4] ] ).
gs_ring( 1, H ):- gs_ring_index( X ),indexed_profiles( X, H ).
/*	[[a,c,b],[b,c,a]], %  -  -  -  -  -  -  
	[[a,c,b],[c,a,b]], %  -  -  -  1  2  -  
	[[b,a,c],[a,b,c]], %  3  -  -  -  4  -  
	[[b,a,c],[c,a,b]], %  -  -  -  -  -  - 
	[[c,b,a],[a,b,c]], %  -  -  -  -  -  -  
	[[c,b,a],[b,c,a]]  %  5  -  -  6  -  -  
*/

gs_ring( 2, D ):-
    gs_ring( 1, A ),
    findall( [ Q, P ], member( [ P, Q ], A ), D ).

pareto_ring( X, D ):-
    x( X ), 
    number_of_persons( N ),
    findall( X, between( 1, N, _ ), Y ),
    best_alternatives_block( Y, D ).

db_partition_domain( arrow_ring(1), D ):- arrow_ring( 1, D ).
db_partition_domain( arrow_ring(2), D ):- arrow_ring( 2, D ).
db_partition_domain( gs_ring(1), D ):- gs_ring( 1, D ).
db_partition_domain( gs_ring(2), D ):- gs_ring( 2, D ).
db_partition_domain( pareto_ring(A), D ):- x( A ), pareto_ring( A, D ).
db_partition_domain( block(A,B), D ):- x(A), x(B), best_alternatives_block( [A,B], D ).

db_partition_domain_for_short( arrow_ring(J), a(J) ).
db_partition_domain_for_short( gs_ring(J), g(J) ).
db_partition_domain_for_short( pareto_ring(J), p(J) ).
db_partition_domain_for_short( block(A,B), b(A,B) ).

current_partition( ring, X ):- member( X, [arrow_ring(_), gs_ring(_), pareto_ring(_)] ).
current_partition( block, block(_,_) ).

:- dynamic current_partition/1. 
current_partition( ring ).

partition_domain( X, D ):-
    current_partition( P ), current_partition( P, X ), db_partition_domain( X, D ).

partition_domain_for_short( X, S ):-
    current_partition( P ), current_partition( P, X ), db_partition_domain_for_short( X, S ).

partition_membership( P, D, X ):-
	 member( P, D ),
	 partition_domain( X, H ),
	 member( P, H ).

partition_membership( D, F ):-
	 findall( P-W, (
		 partition_membership( P, D, X ),
		 partition_domain_for_short( X, Y ),
		 Y =.. Z, atomic_list_concat( Z, W )
	 ), F ).

composite_partitions( K, S, D ):-
	 findall( A, partition_domain(A, X), L ),
	 length( L, N ),
	 between( 1, N, K ),
	 ( \+ var( S )-> length( S, K ); select_n( S, L, K ) ),
	 findall( P,(
		 member( A, S ),
		 partition_domain( A, X ),
		 member( P, X )
	 ), D ).

hist_rings( S, W ):-
	 findall( R:Z, (
		 partition_domain_for_short( A, B ),
		 A=..[ _, J ],
		 B=..[ R, _ ],
		 findall( J, (
			 member( A, S )
		 ), X ),
		 sort( X, Z )
	 ), W ).

test_composite_domains( T, Z, K, S, D, W ):-
	 findall( A, partition_domain(A, _), L ),
	 length( L, N ),
	 between( 1, N, K ),
	 composite_partitions( K, S, D ),
	 check_scf( T-type, D, Z ),
%	 findall( X, ( member( A, L ), ( member( A, S )-> X=1; X=0 ) ), W ),
	 hist_rings( S, W ).

test_composite_domains( T, Z ):-
	 test_composite_domains( T, Z, K, _, _, W ),
	 nl,
	 write( K:Z:W ),
	 fail.
test_composite_domains( _, _ ).


dict_node( 0, [ ], [ ] ).
dict_node( K, S, D ):-
	 findall( 1, partition_domain( _, _ ), L ),
	 length( L, N ),
	 between( 1, N, K ),
	 composite_partitions( K, S, D ),
	 A = gs,
	 Z = dict,
	 check_scf( A-type, D, Z ).

dict_edge( K, S, J, D, X, D1 ):-
	 dict_node( K, S, D ),
	 partition_domain( J, X ),
	 \+ member( J, S ),
	 append( D, X, D1 ),
	 A = gs,
	 Z = dict,
	 check_scf( A-type, D1, Z ).

%:- use_rendering( graphviz ). 
graph_of_dict_sequence( digraph( [ rankdir = 'TB' | Graph ] ) ):-
	 findall(edge(((P)-> (Q)), [label=J]), (
		 dict_edge( _, S, J, _, _, _ ), 
		 hist_rings( S, P ),
		 hist_rings( [J|S], Q )
	 ), Graph ).

shorten_block_indices( X, Y ):- 
		 findall( C, ( 
				 member( block( A, B ), X ),
				 atom_concat( A, B, C )
		 ), Y ).

edge_of_dict_triple_blocks( P, Q, D1, D2 ):-
	 dict_node( 3, X, _ ), \+ member( block( J, J ), X ), 
	 dict_node( 3, Y, _ ), \+ member( block( J, J ), Y ),
	 Y \= X,                                               
	 shorten_block_indices( X, P ),
	 shorten_block_indices( Y, Q ),
	 subtract( P, Q, [D1] ),
	 subtract( Q, P, [D2] ).

graph_of_dict_triple_blocks( digraph( [ rankdir = 'TB' | Graph ] ) ):-
	 findall(edge(((P)-> (Q)), [label=(-D1+D2)]), (
		 edge_of_dict_triple_blocks( P, Q, D1, D2 )
	 ), Graph ).

%-----------------------------------------------------------------
% utilitiy
%-----------------------------------------------------------------
% サブリストを指標関数で抽出
list_projection_n( [ ], [ ], [ ], N, N ).
list_projection_n( [ 0 | A ], [ _ | Y ], Z, K, N ) :-
	number( N ), K >= N, !,
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
	 list_projection_n( _, B, A, 0, K ).
%横線をハイフンで
hr( N ):-
	 nl,
	 between( 1, N, _ ),
	 write( '-' ),
	 fail; true.
%表のセル
fig_cell( arrow-type, [ P, Q ], F ):-
	 member( [ P, Q ] - S, F ), !,
	 rc( I, S ),
	 write( I ),
	 ( I < 10 -> tab( 2 ); tab( 1 ) ).

fig_cell( gs-type, [ P, Q ], F ):-
	 member( [ P, Q ] - X, F ), !,
	 term_string( X, T ),
	 string_length( T, K ),
	 write( T ),
	 ( K < 2 -> tab( 2 ); tab( 1 ) ).

fig_cell( _, [ P, Q ], F ):-
	 \+ member( [ P, Q ] - _, F ), !,
	 write('-' ),
	 tab( 2 ).

fig_cell( _, _, _ ):- nl,write( '--' ).
% 領域やSCFの視覚化
fig( domain, D ):-
	 findall( P-J, nth1( J, D, P ), F ),
	 fig( gs-type,  F ),
	 !.
fig( membership, D ):-
	 \+ \+ clause( partition_membership( _, _ ), _ ),
	 partition_membership( D, F ),
	 fig( gs-type,  F ),
	 !.
fig( _, _ ):-
	 nl, 
	 rc( 1, P ), nl, tab( 2 ),
	 term_string( 1 : P, A ), 
	 string_length( A, M ), tab( M ),
	 rc( K, _ ),
	 write( K ),
	 ( K < 10 -> tab( 2 ); tab( 1 ) ),
	 fail.
fig( _, _ ):-
	 rc( 1, P ), nl, tab( 2 ),
	 term_string( 1 : P, A ), % 行ヘッダ
	 string_length( A, M ), tab( M ),
	 findall( '---', rc( _, _ ), L ),
	 atomic_list_concat( L, H ),
	 write( H ),
	 fail.
fig( M, F ):-
	 rc( J, P ), nl, write( J : P ), tab( 1 ),
	 ( J < 10 -> tab( 1 ); true ),
	 rc( _, Q ), fig_cell( M, [ P, Q ], F ),
	 fail.
fig( _, _ ):- nl, write( '--' ).

%ヒストグラム
no_such_data( A ):-
       \+ clause( A, _ ),
       nl,
       write( 'no such data' ).
findall_nv( B, A, H ):-
       findall( B, ( A, \+ var( B ) ), H ).

hist( A, B ):-
      \+ no_such_data( A ),
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

%-----------------------------------------------------------------
% tables and figures
%-----------------------------------------------------------------
%表1の作表
table_1:-
	 H1 = 'ring:a',
	 H2 = 'ring:gs',
	 H3 ='scf:-ring(p) ',
	 H4 = 'scf:+ring(p)',
	 H = '~n~t~1|~w~t~8|~w~t~20|~w~t~34|~w',
	 format( H, [H1, H2, H3, H4] ), 
	 hr( 45 ),
	 composite_partitions( _, S, D ), 
	 \+ member( pareto_ring( _ ), S ), 
	 L = [pareto_ring(a),pareto_ring(b),pareto_ring(c)],
 	 union( L, S, Sx ), 
	 composite_partitions( _, Sx, Dx ), 
	 T=gs,
	 check_scf( T-type, D, Z ), 
	 check_scf( T-type, Dx, Zx ), 
	 hist_rings( S, W ), 
	 W=[a:A,g:G,p:_], 
	 M = '~n~t~1|~w~t~10|~w~t~20|~w~t~34|~w',
	 format( M, [A, G, Z, Zx] ), 
	 fail.
table_1:- hr( 45 ).

% Fig.1 
fig1:- %prove( A ).
	 unrestricted_domain( U ),
     X = gs-type, scf( X, F, U, Z ),
     fig( X, F ), write( Z ),
	 fail.

% Fig.2
fig2:- arrow_ring( both, M ), fig( domain, M ).
    
% Fig.3 (this is arrow-type SCF. gs-type is Fig.6 )
fig3:- Axiom=arrow-type, hist((arrow_ring(1, M ), select_n(D,M,K), check_scf( Axiom, D, Z) ), K-profiles:Z-domain ).

% Fig.4
fig4( K ):- time(generate_quasi_super_dictatorial_domain( arrow, D, K )), fig( domain, D ).

% Fig. 5
fig5:- Axiom=gs-type, arrow_ring(1, M ), scf( Axiom, F, M, Z ), fig( Axiom, F ), write(Z).

% Fig.6
fig6:- Axiom=gs-type, hist((arrow_ring(1, M ), select_n(D,M,K), check_scf( Axiom, D, Z) ), K-profiles:Z-domain ).

% Fig.7
fig7:- T = gs-type, hist( ( arrow_ring( 1, M ), arrow_ring( both, W ), unrestricted_domain( U ), subtract( U, W, L ), between( 1, 6, K ), select_n( S, L, K ), append( M, S, D ), check_scf( T, D, Z ) ), K : Z ).

% Fig.8  (using graphviz in SWISH)
fig8( G ):- graph_of_dict_sequence( G ).

% Fig.9  
fig9:- composite_blocks( 3, T, D ), \+ member( block(A,A), T ), check_scf( gs-type, D, dict ), fig( domain, D ), fail.

% Fig.10  (using graphviz in SWISH. Before query, partition_domain should be switched)
fig10( 'Switch current_partition/1 to block!' ):- current_partition( ring ), !.
fig10( G ):- current_partition( block ), graph_of_dict_triple_blocks( G ).

%-----------------------------------------------------------------
% Exchanging Prolog, Japanese, logic, and set operators
%-----------------------------------------------------------------

% 述語名変換マッピング（英語/アリティ → 日本語/アリティ）
変換(number_of_persons/1, 人数/1).
変換(persons/1, 個人の集合/1).
変換(alternatives/1, 代替案の集合/1).
変換(x/1, 代替案/1).
変換(ranking/1, 順序/1).
変換(best/2, 最善/2).
変換(p/3, 選好/3).
変換(all_rankings/1, 順序の全体集合/1).
変換(rc/2, 番号付き順序/2).
変換(pp/2, プロフィール生成/2).
変換(number_of_persons/1, 人数/1).
変換(pp/1, プロフィール/1).
変換(unrestricted_domain/1, 無制限領域/1).
変換(non_imposed/1, ノンインポーズド/1).
変換(dictatorial_scf/3, 独裁的SCF/3).
変換(scf/3, 社会選択関数scf/3).
変換(scf/4, 社会選択関数scf/4). %独裁チェック付き
変換(swf/2, 全域の社会厚生関数swf/2).
変換(swf/3, 社会厚生関数swf/3).
変換(f/4, 関数の構成/4).
変換(scf_axiom/5, 社会選択関数の公理/5).
変換(manipulable/4, マニピュラブル/4).
変換(prove/1, 証明/1).
変換(check_scf/3, チェックscf/3).
変換(count_scf/4, カウントscf/4).
変換(swf/3, 社会厚生関数/3).
変換(agree/4, 一致/4).
変換(unanimous/4, 全会一致/4).
変換(unanimous/3, 全会一致/3).
変換(pareto/1, パレート条件/1).
変換(iia/2, 無関係な代替案の独立性/2).
変換(fig/2, 図示/2).

変換(length/2, リスト長/2).
変換(member/2, リストの要素/2).
変換(nth1/3, リストのｎ番目/3).
変換(append/3, リストの結合/3).
変換(permutation/2, 順序の置換/2).
変換(intersection/3, リストの共通部分/3).
変換(union/3, リストの和/3).
変換(subtract/3, リストの差/3).
変換(subset/2, 部分リストか判定/2).
変換(findall/3, 全ゴール収集/3).
変換(bagof/3, パタン別ゴール収集/3).
変換(setof/3, パタン別ゴール整列/3).
変換(maplist/3, マップリスト/3).
変換(forall/2, 条件命題/2).

変換('->/2', 条件分岐/2).

変換(!/0, カット/0).
変換(nl/0, 改行/0).
変換(write/1, 印字/1).
変換(writeln/1, 印字と改行/1).
変換(tab/1, 空白/1).
変換(format/1, 成型印字/1).
変換(tell/1, ファイルに出力/1).
変換(told/1, ファイル出力終了/1).
変換(assert/1, 節登録/1).
変換(abolish/1, 述語廃止/1).
変換(retract/1, 登録抹消/1).

変換('=:='/2, 両辺計算/2).
変換(is/2, 右辺計算/2).
変換('=..'/2, ユニブ/2).
変換(functor/3, ファンクター/3).


% 述語の変換を適用する述語
述語変換(_英語述語, _日本語述語) :- 
    var( _英語述語 ), 
    var( _日本語述語 ),
    !,
    変換(_英語述語名/_アリティ, _日本語述語名/_アリティ),
    length( _引数リスト, _アリティ ),
    _英語述語 =.. [ _英語述語名 | _引数リスト ],
    _日本語述語 =.. [ _日本語述語名 | _引数リスト ].

述語変換(_英語述語, _日本語述語) :- 
    \+ var( _英語述語 ),
    !,
    _英語述語 =.. [ _英語述語名 | _引数リスト ],
    length( _引数リスト, _アリティ ),
    変換( _英語述語名/_アリティ, _日本語述語名/_アリティ),
    _日本語述語 =.. [ _日本語述語名 | _引数リスト ].

述語変換(_英語述語, _日本語述語) :- 
    \+ var( _日本語述語 ),
    !,
    _日本語述語 =.. [ _日本語述語名 | _引数リスト ],
    length( _引数リスト, _アリティ ),
    変換( _英語述語名/_アリティ, _日本語述語名/_アリティ),
    _英語述語 =.. [ _英語述語名 | _引数リスト ].

% 記号の意味：自然言語スキーマ定義
スキーマ(P, [X], [X,は,J,である] ):- 変換(F/1, J/1 ), P=..[ F, X ]. % Satoshi Watanabe風に言うと，パース流の含意

スキーマ(rc(K, R), [K, R], [第,K,順序,R] ).
スキーマ(best(X, R), [X, R], [順序,R,において,X,が最善である] ).
スキーマ(p(X, Y, R), [X,Y,R], [順序,R,において,X,は, Y,よりも好ましい] ).
 
スキーマ(scf(Type, F, D), [Type, F, D ], [Type,型scf,F,を領域,D,で生成する] ).
スキーマ(scf(Type, F, D, Z), [Type, F, D, Z ], [Type,型scf,F,を領域,D,で生成して,Z] ).
スキーマ(swf(F, D, Z), [F, D, Z ], [swf,F,を領域,D,で生成して,Z] ).
スキーマ(swf(F, Z), [F, Z ], [swf,F,を無制限領域で生成して,Z] ).

スキーマ(dictatorial_scf(Type, J, F), [Type, J, F ], [個人,J,が,Type,型の独裁者である]).
スキーマ(manipulable(Agent, P - S, Q - T, F), [Agent,P,S,Q,T,F], [個人,Agent,が選好,P,を,Q,と偽ると結果が,S,から,T,に改善する]).
スキーマ(agree(+, X, Y, PP), [X,Y,PP], [プロフィール,PP,において,X,が,Y,より好ましいことに合意する]).
スキーマ(agree(-, X, Y, PP), [X,Y,PP], [プロフィール,PP,において,X,が,Y,より好ましくないことに合意する]).
スキーマ(unanimous(X, Y, PP), [X,Y,PP], [プロフィール,PP,において全会一致で,X,は,Y,より好まれる]).
スキーマ(unanimous(X, Y, P, L), [X,Y,P,L], [再帰的に順序,P,は残りのプロフィール,L,の先頭と,X,が,Y,より好まれることに合意する]).

スキーマ(pareto(PP - S), [PP, S ], [プロフィール,PP,に対する値,S,はパレート条件を満たす]).
スキーマ(iia(PP - S, F), [PP, S, F ], [プロフィール,PP,に対する値,S,はIIA条件にかんして関数,F,において矛盾しない]).

スキーマ(f(X, F, D, A), [X,F,D,A], [公理, X, を満たす関数, F,を,領域,D,上に累積項,A,を用いて構成する] ).
スキーマ(scf_axiom(X, P, S, F, D), [X,P,S, F,D], [X,型scf公理を満たすように, P,に対する値,S,を選んで関数, F,と領域,D,を拡張する] ).
スキーマ(check_scf(X, D, Z), [X, D, Z], [プロフィール集合,D,は,X,型,Z,領域である] ).
スキーマ(count_scf(X, D, Z, N), [X, D, Z], [X,型で,W,scfは,D,上で,N,個ある] ):- 
    ( var( Z )-> W=独裁を含む ; W= Z ).
スキーマ(fig(T, X), [T,X], [タイプ,T,の図をデータ,X,について表示する] ).

スキーマ(length(A, N), [A, N], [A,の要素数は,N,である] ).
スキーマ(member(X, A), [X, A], [X,は,A,の要素である] ).
スキーマ(nth1(J, A, X), [J, A, X], [A,の,J,番目は,X,である] ).
スキーマ(append(X, Y, Z), [X,Y,Z], [X,に,Y,を結合すると, Z,である] ).
スキーマ(sort(X, Y), [X, Y], [X,を整列すると,Y,である] ).
スキーマ(subset(X, Y), [X, Y], [X,は,Y,の部分リストである] ).
スキーマ(subtract(X, Y, Z), [X,Y,Z], [X,から,Y,を除去すると, Z,である] ).
スキーマ(intersection(X, Y, Z), [X,Y,Z], [X,と,Y,の共通部分は, Z,である] ).
スキーマ(union(X, Y, Z), [X,Y,Z], [X,と,Y,を合併すると, Z,である] ).
スキーマ(permutation(X, Y), [X,Y], [X,と,Y,は互いに置換する] ).

スキーマ(findall(X, Y, Z), [X,Y,Z], [Y,が成り立つすべてのパタンで,X,を, Z,に集める] ).
スキーマ(bagof(X, Y, Z), [X,Y,Z], [Y,が成り立つあるパタンで,X,を,Z,に集める] ).
スキーマ(setof(X, Y, Z), [X,Y,Z], [Y,が成り立つあるパタンで,X,を,Z,に整列する] ).
スキーマ(bagof(X, W^Y, Z), [X,W^Y,Z], [Y,が成り立つすべての,W,のパタンで,X,を,Z,に集める] ).
スキーマ(setof(X, W^Y, Z), [X,W^Y,Z], [Y,が成り立つすべての,W,のパタンで,X,を,Z,に整列する] ).

スキーマ(maplist(X, Y, Z), [X,Y,Z], [X,の引数を,Y,と,Z,からのペアで生成する] ).
スキーマ(forall(A,B), [X,Y], [C,ならば,D,である] ):- スキーマ(A, X, C), スキーマ(B, Y, D).

スキーマ(A :- B,[A, B], [A,'は',B,という条件をすべて満たすときは正しい ]).
スキーマ(( A, B ),[X,Y],[C,かつ,D ]):- スキーマ(A,X,C), スキーマ(B,Y,D).
スキーマ(( A; B ),[X,Y],[C,または,D ]):- スキーマ(A,X,C), スキーマ(B,Y,D).
スキーマ(\+ (A,\+ B ), V, Z ):- スキーマ(forall(A,B),V,Z).
スキーマ(\+ A,X,[B,の否定 ]):- スキーマ(A,X,B).
スキーマ(!,[],[親ゴールのここまでの部分は確定 ]).

スキーマ(A is B,[A,B],[A,は,B,を計算した値である ]).
スキーマ(A =:= B,[A,B],[A,と,B,の計算結果は一致する ]).
スキーマ( A =..[ F | X ], [A,F,X], [ファンクター, A, はファンクター名, F, と引数リスト, X, から合成される ] ).
スキーマ(functor(A,F,N),[A,F,N],[] ).
スキーマ(A->B,[A,B],[A,が成功したら,B,を確定的にチェックする] ).

スキーマ(nl,[],[改行 ]).
スキーマ(write(X ),[X],[X,を印字 ]).
スキーマ(writeln(X ),[X],[X,を印字して改行 ]).
スキーマ(tab(X ),[X],[X,個の空白 ]).

スキーマ定義のテスト:-
    変換( F/N,_),
    functor( A, F, N ),
    nl, write( F/N ),
    \+ ( スキーマ(A, _, _) ),
    write( '*スキーマ生成漏れ' ),
    fail.

スキーマ定義のテスト:-
    findall( A, 述語変換(A,_), L ),
    変換(F/N,_),
    functor( A, F, N ),
    \+ member( A, L ),
    nl, write( F/N ),
    write('**述語変換/2が生成漏れ' ),
    fail.

/*
 ?- スキーマ(\+ (member(X,Y),1=1), Z,B).
B = [[member(X,Y), かつ, 1=1], の否定],
Z = [member(X,Y), 1=1]

 ?- スキーマ(\+ (member(X,Y);1 is 1 + 1), Z,B).
B = [[member(X,Y), または, 1 is 1+1], の否定],
Z = [member(X,Y), 1 is 1+1]

  ?- スキーマ定義のテスト.
false.
*/ 

% Prologの述語をスキーマ（リスト分解された自然言語文）に変換
述語toスキーマ(_述語, _日本語述語, _引数リスト, _スキーマ) :-
    述語変換(_述語, _日本語述語) ,
    スキーマ(_述語, _引数リスト, _スキーマ).
/*
 ?- 述語toスキーマ( best(D,C), _, _, Q ).
Q = [順序, C, において, D, が最善である]

 ?- 述語toスキーマ( p(A,B,C), JP, V, Q ).
JP = 選好(A,B,C),
Q = [順序, C, において, A, は, B, よりも好ましい],
V = [A, B, C]
*/ 

ルールtoスキーマ((A :- B), J, V, S ) :-
    述語変換( A, J ) ,
    スキーマ( A :- B, V, T ),
    catch( clause(A, B), Error, format("いけませんね: ~q~n",[Error]) ),
    ( ( B = true ; \+ var( Error ) ) -> S = [A,は事実 ]; S = T ).

% リストとタプル/2 <- 述語リストとゴール結合の相互変換/2 
% 「日本語による論理プログラミングの試み」関東学園大学経済学紀要46

リストとタプル( [ A ], A ):-
	 \+ A =.. [ ',' | _ ],
	 \+ A =.. [ ';' | _ ].

リストとタプル( [ X | L ], ( X, Y ) ):-
	 リストとタプル( L, Y ).

リストとタプル( L , ( A ; B ) ):-
	 リストとタプル( L1 , A ),
	 リストとタプル( L2 , B ),
	 append( L1, [ ';'( 前, 後 ) | L2 ], L ).

ルール((A :- B), J, S, T) :-
    ルールtoスキーマ((A :- B), J, [A,B], S ),
	B \= true,
    スキーマ( B, _, P ),
    numbervars( S ),
    スキーマ( J:-P, _, T ).
/*    リストとタプル( X, B ),
    findall( P, (
        member( W, X ),%writeln(W),
        once( スキーマ( W, _, P ) )
    ), C ),
    リストとタプル( C, Z ),
    スキーマ(J:-Z, _, T ).
*/
ルール((A :- B), J, [J,'<==',[] ], 事実) :-
    ルールtoスキーマ((A :- B), J, [A,B], _ ),
	B == true.

/*

ルール( A:-B, J, S, T ).
A = x(A),
B = (alternatives(B),member(A,B)),
J = 代替案(A),
S = [x(A), は, (alternatives(B),member(A,B)), という条件をすべて満たすときは正しい],
T = [代替案(A), は, [[B, は, 代替案の集合, である], かつ, [A, は, B, のメンバーである]], という条件をすべて満たすときは正しい]

ルール((non_imposed(_):-A), J, C, T ).
A = non_imposed(A),
B = (\+(x(B),\+member(C-B,A))),
J = ノンインポーズド(A),
S = [non_imposed(A), は, \+(x(B),\+member(C-B,A)), という条件をすべて満たすときは正しい],
T = [ノンインポーズド(A), は, [条件, [[B, は, 代替案, である], かつ, [条件, [C-B, は, A, のメンバーである], を満たすものはない]], を満たすものはない], という条件をすべて満たすときは正しい]

% \+ ( X, \+ Y ) => forall( X, Y )  

ルール((non_imposed(_):-A), J, C, T ).
A = (\+(x(B),\+member(C-B,A))),
C = [non_imposed(A), は, \+(x(B),\+member(C-B,A)), という条件をすべて満たすときは正しい],
J = ノンインポーズド(A),
T = [ノンインポーズド(A), は, [forall, [B, は, 代替案, である], [C-B, は, A, のメンバーである]], という条件をすべて満たすときは正しい]
false
*/ 


% 述語と数学的論理式の対応付け
% Logical formula and set theoretic equations:
% The preliminary code is generated by AI claude 3.7 Sonnet free  
% and modified by a human
% https://swish.swi-prolog.org/p/ohhlKAci.pl

:- op(1100, xfy, ':').  % 量化子のスコープ

:- op(900, fx, ∀). % 全称量化子
:- op(900, fx, ∃). % 存在量化子
:- op(900, fx, all).  % 全称量化子
:- op(900, fx, exists).  % 存在量化子

:- op(1000, xfy, ⇒).  % 含意
:- op(1000, xfy, →).  % 含意
%:- op(1000, xfy, '->').  % 含意
:- op(1000, xfy, =>).  % 含意
:- op(1000, xfy, ==>).  % 含意
:- op(1000, xfy, '←→').  % 同値
:- op(1000, xfy, '<->').  % 同値
:- op(1000, xfy, '<=>').  % 含意
:- op(1000, xfy, '<==>').  % 含意
:- op(900, yfx, '∧').   % 論理積
:- op(900, yfx, '&').   % 論理積
:- op(900, yfx, '＆').   % 論理積
:- op(900, yfx, 'and').   % 論理積
:- op(900, yfx, '∨').   % 論理和
:- op(900, yfx, 'or').   % 論理和
:- op(900, yfx, 'eor').   % 排他的論理和
:- op(900, yfx, '⊕').   % 排他的論理和
:- op(900, yfx, 'nand').   % NAND
:- op(900, yfx, '｜').   % NAND

:- op(890, fy, not).    % 否定
:- op(890, fy, ¬).    % 代替の否定記号
:- op(890, fy, ￢).    % 代替の否定記号

:- op(900, yfx, ＝).  % 等値
:- op(700, xfx, ≺).    % 選好関係
:- op(700, xfx, -<).    % 選好関係
:- op(800, xfx, ∈).    % 要素関係
:- op(800, xfx, in).   % 要素関係（ASCII版）
:- op(800, xfx, ∉).    % 要素関係
:- op(800, xfx, not_in).   % 要素関係（ASCII版）
:- op(700, xfx, ⊆).    % 包含関係
:- op(700, xfx, subset ). % 包含関係（ASCII版）
:- op(700, xfx, ⊈).    % 包含関係
:- op(700, xfx, not_subset ). % 包含関係（ASCII版）

:- op(500, yfx, ∩ ).    % 積集合
:- op(500, yfx, intersect ). % 積集合（ASCII版）
:- op(500, yfx, ∪ ).    % 和集合
:- op(500, yfx, union ). % 和集合（ASCII版）
:- op(500, yfx, ＼ ).   % 差集合
:- op(500, yfx, diff ).  % 差集合（ASCII版）


% 「すべてのXについて、あるYが存在して、XがYを愛する」
sample_formula( 1, 'all X : exists Y : loves(X, Y)' ).
sample_formula( 2, '∀ X : ∃ Y : loves(X, Y)' ).

% 「すべてのXについて、XがAかつXがBならば、XはCである」
sample_formula( 3, 'all X : a(X) & not b(X) → c(X)' ).
sample_formula( 4-x, '∀ X : a(X) & ￢b(X) ⇒ c(X)' ).
sample_formula( 4, '∀ X : a(X) & ￢b(X) → c(X)' ).

sample_formula( 5, 'X∩Y ⊆ Z  ⇒ X∪Y ∈ W' ).
sample_formula( 6, 'Z ＼ P ＝ Φ ⇒ Y ∉ W' ).
sample_formula( 7, 'Z ∉ X ∩ Y'  ).

show(1):- sample_formula( K, B ), term_string( A, B ), numbervars(A), nl, write( K: B ), fail;nl.
/*
 ?- show(1).

1:all A:exists B:loves(A,B)
2:∀A:∃B:loves(A,B)
3:all A:a(A)&not b(A)->c(A)
4:∀A:a(A) & ￢b(A)⇒c(A)
true
 */ 

show(2):-sample_formula( K, C ), term_string( A⇒B, C ), numbervars( [A, B] ), nl, write( K; A; B ), fail; nl.
/*
?- show(2).
5;A∩B⊆C;A∪B∈D
6;A＼B=C;D∉E
true
*/

% 要素関係
X ∈ List :- member(X, List).

% 包含関係（判定）
Subset ⊆ Set :- subset(Subset, Set).

% 積集合
Set1 ∩ Set2 ＝ Result :- intersection(Set1, Set2, Result).

% 和集合
Set1 ∪ Set2 ＝ Result :- union(Set1, Set2, Result).

% 差集合
Set1 ＼ Set2 ＝ Result :- subtract(Set1, Set2, Result).

論理スキーマ( X ∈ List, member(X, List), 要素関係-基本 ).
論理スキーマ( X ∉ List, \+ member(X, List), 要素要素 ).
論理スキーマ( Subset ⊆ Set, subset(Subset, Set), 包含関係-基本 ).
論理スキーマ( Subset ⊈ Set, \+ subset(Subset, Set), 包含関係 ).
論理スキーマ( Set1 ∩ Set2 ＝ Set3, intersection(Set1, Set2, Set3), 積集合 ).
論理スキーマ( Set1 ∪ Set2 ＝ Set3, union(Set1, Set2, Set3), 和集合 ).
論理スキーマ( Set1 ＼ Set2 ＝ Set3, subtract(Set1, Set2, Set3), 差集合 ).

論理スキーマ( S1 ∩ S2 ⊆ S3, (intersection(S1, S2, S),subset(S, S3) ), 集合演算 ).
論理スキーマ( S1 ∪ S2 ⊆ S3, (union(S1, S2, S),subset(S, S3)), 集合演算 ).
論理スキーマ( S1 ＼ S2 ⊆ S3, (subtract(S1, S2, S),subset(S, S3)), 集合演算 ).
/*
論理スキーマ( X ∈ S1 ∩ S2, (intersection(S1, S2, T),member(X,T)), 集合演算 ).
論理スキーマ( X ∈ S1 ∪ S2, (union(S1, S2, T),member(X,T)), 集合演算 ).
論理スキーマ( X ∈ S1 ＼ S2, (subtract(S1, S2, T),member(X,T)), 集合演算 ).
論理スキーマ( X ∉ S1 ∩ S2, (intersection(S1, S2, T),\+ member(X,T)), 集合演算 ).
論理スキーマ( X ∉ S1 ∪ S2, (union(S1, S2, T),\+ member(X,T)), 集合演算 ).
論理スキーマ( X ∉ S1 ＼ S2, (subtract(S1, S2, T),\+ member(X,T)), 集合演算 ).

論理スキーマ( ∅, [ ], 空集合 ).
論理スキーマ( ■, true, 恒真 ).
論理スキーマ( □, false, 恒偽 ).
論理スキーマ( A eor B, ( A, \+ B; B, \+ A ), 排他的論理和 ).
論理スキーマ( A ⊕ B, ( A, \+ B; B, \+ A ), 排他的論理和 ).
論理スキーマ( A nand B, \+ ( A, B ), 'NAND' ).
論理スキーマ( A ｜ B, \+ ( A, B ), 'NAND' ). % Shafer stroke
*/
論理スキーマ( ￢ Goal, \+ Goal, 否定-基本 ).
論理スキーマ( A ⇒ B, forall( A, B ), 含意-基本 ).
論理スキーマ( C, forall( A, B ), 含意 ):- member( X,[→,-->,=>,==>] ), C=..[X,A,B].
論理スキーマ( A ∧ B, ( A, B ), 連言-基本 ).
論理スキーマ( C, ( A, B ), 連言 ):- member( X,[&,＆,and] ), C=..[X,A,B].
論理スキーマ( A ∨ B, ( A; B ), 選言-基本 ).
論理スキーマ( A or B, ( A; B ), 選言 ).
論理スキーマ( ∀ X: B, B,  ルール(X)).
論理スキーマ( all X: B, B,  ルール(X)).
論理スキーマ( ∀ X: B ⇒ A, A :- B,  ルール(X)).
論理スキーマ( all X: B ⇒ A, A :- B,  ルール(X)).
論理スキーマ( ∃ X: A, A, 事実(X) ).
論理スキーマ( exists X: A, A, 事実(X) ).
論理スキーマ( ∀ X: ∃ Y: Z, maplist( F, X, Y ), 対応 ):- Z=..[F,X,Y].
論理スキーマ( all X: exists Y: Z, maplist( F, X, Y ), 対応 ):- Z=..[F,X,Y].

論理スキーマ( A, B, 特別(C) ):- 特別スキーマ( A, B, C ).

/*
?- ルール( A:-C,J,V,D),  論理スキーマ( H, C, P ).
A = x(A),
C = (alternatives(B), member(A, B)),
J = 代替案(A),
V = [x(A), は, (alternatives(B), member(A, B)), という条件をすべて満たすときは正しい],
D = [代替案(A), は, [[B, は, 代替案の集合, である], かつ, [A, は, B|...]], という条件をすべて満たすときは正しい],
H = (alternatives(B)∧member(A, B)),
P = 連言 .

?- (A∩B⊆C)=G, 論理スキーマ( G, H, X ), term_string( H, L ).
G = (A∩B⊆C),
H = (A∩B subset C),
L = "subset(∩(_47538,_47562),_47530)",
X = 包含関係
*/


% 項の中の特定の部分項を置換するための述語
%  generated by claude sonnet 3.7 free (slightly modified)
replace_term( _, _, Term, Term) :-
    var(Term), !. % bugfix( see below)
replace_term(Old, New, Term, Result) :-
    Term = Old, !,  % 置換対象と一致する場合
    Result = New.
replace_term( _, _, Term, Term) :-
    atomic(Term), !. % アトミックな項の場合（数値、アトム等）
replace_term(Old, New, Term, Result) :-
    compound(Term), !, % 複合項の場合
    Term =.. [Functor|Args],
    replace_term_list(Old, New, Args, NewArgs),
    Result =.. [Functor|NewArgs].

% リスト内の各要素に対して置換を適用
replace_term_list(_, _, [], []).
replace_term_list(Old, New, [Arg|Args], [NewArg|NewArgs]) :-
    replace_term(Old, New, Arg, NewArg),
    replace_term_list(Old, New, Args, NewArgs).
/*
 ?- replace_term( x, a, g(x:y,f(x,z)), C ).
C = g((a:y),f(a,z))
 ?- replace_term( f(X,Z), a, g(x:y,f(x,z)), C ).
C = g((x:y),a),
X = x,
Z = z
 ?- replace_term( f(X,Z), p(X,Z), g(x:y,f(x,z)), C ).
C = g((x:y),p(x,z)),
X = x,
Z = z

 ?- X = (A∩B⊆C), replace_term(A∩B, D, X, Y).
X = (A∩B⊆C),
Y = (D⊆C)

% debug (fixed)
?- X = (A+B-C), replace_term(A+B, D, X, Y).
C = A+B,
X = A+B-(A+B),
Y = D-D
?- replace_term_list(A+B, D, [A+B,C], Y).
C = A+B,
Y = [D, D]
==>
?- replace_term_list(A+B, D, [A+B,C], Y).
Y = [D, C]
?- X = (A+B-C), replace_term(A+B, D, X, Y).
X = A+B-C,
Y = D-C

 */ 

まだ変換できる部分項がある( B, C, D ):-
    sub_term( C, B ),
    \+ var( C ),
    論理スキーマ( C, D, _ ).

余すところなく変換済( B ):-
	\+ まだ変換できる部分項がある( B, _, _ ).

論理to節プログラム( A, A ):-
    余すところなく変換済( A ).

論理to節プログラム( A, B ):-
    まだ変換できる部分項がある( A, X, Y ),
    replace_term( X, Y, A, C ),
    論理to節プログラム( C, B ).

% earlier
/*
論理to節プログラム( A, B ):-
	 \+ var( A ),
	 論理スキーマ( A, C, _ ),
     論理to節プログラム( C, B ).

論理to節プログラム( A, B ):- 
	 \+ var( A ),
     A =.. [ F, Z, W ],
     \+ var( W ),
	 論理to節プログラム( W, P ),
     B =.. [ F, Z, P ].

論理to節プログラム( A, B ):- 
	 \+ var( A ),
     A =.. [ F, Z, W ],
     \+ var( Z ),
     論理to節プログラム( Z, V ),
     B =.. [ F, V, W ].
*/

特別スキーマ( A, (P, B), 式内の集合演算):-
    % ex. f( A∩B, C ) ==> (intersection(A,B,D), f(D,C))
    \+ var( A ),
    A=..[ F | L ],
    F \= ＝,
    F \= :,
    F \= \+,
    member( X, L ),
    \+ var( X ),
    論理スキーマ( X ＝ Y, P, _ ),
%    numbervars(P),
    replace_term( X, Y, A, B ).

さらに変換できる部分項がある( B, C, D ):-
    sub_term( C, B ),
    \+ var( C ),
    特別スキーマ( C, D, 式内の集合演算).

余すところなく修正済( B ):-
	\+ さらに変換できる部分項がある( B, _, _ ).

論理to節プログラムの修正( A, A ):-
    余すところなく修正済( A ).

論理to節プログラムの修正( C, B ):-
%    論理to節プログラム( A, C ),
    さらに変換できる部分項がある( C, X, Y ),
    replace_term( X, Y, C, D ),
    論理to節プログラムの修正( D, B ).

test_formula( K, X, Y ):-
    sample_formula( K, A ),
    term_string( X, A ),
    X=..Y. 

test_formula_1:-
    test_formula( K, X, _ ),
    copy_term( X, X1 ), numbervars( X1 ),
    nl, catch( write(K;X1), _, write( err( 1 ) ) ),
    findall( B, (
              論理to節プログラム( X, B )
              %論理to節プログラム( X, C ),論理to節プログラムの修正( C, B )
    ), L ),
    構造的に異なるもののリスト( L, [ ], H ),
    copy_term( H, H1 ),numbervars( H1 ),
    catch( write('' ==>H1 ), _, write( err( 2 ) ) ), 
    fail; nl.

構造的に異なるもののリスト( [ ], H, H ).
構造的に異なるもののリスト( [X|L], W, H ):-
    \+ ( member( Y, W ), Y =@= X ),
    !,
    構造的に異なるもののリスト( L, [X|W], H ).
構造的に異なるもののリスト( [_|L], W, H ):-
    構造的に異なるもののリスト( L, W, H ).

% modified: test_formula_1/0. debug the case 5, A∩B⊆C
% added: 構造的に異なるもののリスト/3

debug_point( 1, (_∩_⊆ _), C ):- nl, write( 1:C ),!.
debug_point( 2, forall( (_∩_⊆ _), _ ), C ):- nl, write( 2:C ),!.
debug_point( _, _, _ ).

/*
 ?- test_formula_1.

1;all A:exists B:loves(A,B)==>[maplist(loves,A,B), loves(C,D)]
2;∀A:∃B:loves(A,B)==>[maplist(loves,A,B), loves(C,D)]
3;all A:a(A)&not b(A)→c(A)==>[forall((a(A),not b(A)),c(A))]
4-x;∀A:a(A) & ￢b(A)⇒c(A)==>[(c(A):-a(A),\+b(A)), forall((a(B),\+b(B)),c(B))]
4;∀A:a(A) & ￢b(A)→c(A)==>[forall((a(A),\+b(A)),c(A))]
5;A∩B⊆C⇒A∪B∈D==>[forall(((subtract(A,B,C),intersection(D,E,C)),subtract(A,B,F),F subset G),(union(D,E,H),member(H,I))), forall(((union(J,K,L),intersection(M,N,L)),union(J,K,O),O subset P),(union(M,N,Q),member(Q,R))), forall(((intersection(S,T,U),intersection(S,T,U)),(intersection(S,T,U),intersection(S,T,U)),intersection(S,T,V),V subset W),(union(S,T,X),member(X,Y))), forall((intersection(Z,A1,B1),B1 subset C1),(union(Z,A1,D1),member(D1,E1)))]
6;A＼B＝C⇒D∉E==>[forall(subtract(A,B,C),\+member(D,E))]
7;A∉B∩C==>[(intersection(A,B,C),\+member(D,C)), \+(intersection(E,F,G),member(H,G))]
1true
*/

logic_edge( self, self, A, A ).

logic_edge( X, Y, A, B ):-
    まだ変換できる部分項がある( A, X, Y ),
    replace_term( X, Y, A, C ),
    logic_edge( _, _, C, B ).

logic_network( K, digraph( [ rankdir = 'LR' | G ] ) ):-
    test_formula( K, F, _ ),
    findall(edge((W-> V), [label=(S-> T)]), (
         sub_term( X, F ),
         logic_edge( X, Y, A, B ),
         term_variables( B, Z ),
         findall( P, ( nth1( J, Z, P ), concat( x, J, P ) ), Z ),
         term_string( A, S ),
         term_string( B, T ),
         term_string( X, W ),
         term_string( Y, V )
	), L ),
    構造的に異なるもののリスト( L, [ ], G ).

logic_edge_2( A, A, W, W ):-
    \+ まだ変換できる部分項がある( A, _, _ ).

logic_edge_2( A, B, Z, W ):-
    まだ変換できる部分項がある( A, X, Y ),
    replace_term( X, Y, A, C ),
    logic_edge_2( C, B, [ [ X, Y, A, C ] | Z ], W ).

logic_network_2( K, digraph( [ rankdir = 'TB' | G ] ) ):-
    test_formula( K, F, _ ),
    logic_edge_2( F, _, [ ], H ), 
    length( H, N ),
    writeln( N ),
    copy_term( H, H1 ),
%    numbervars( H1 ),
	term_variables( H1, V ),
    findall( P, ( nth1( J, V, P ), concat( x, J, P ) ), V ),
    findall(edge((S1-> T1), [label=(W1-> V1)]), (
		 member( [ X, Y, A, B ], H1 ),
         term_string( A, S1 ),
         term_string( B, T1 ),
         term_string( X, W1 ),
         term_string( Y, V1 )
	), G ).

/*
 ?- test_formula( 7, F, _ ),logic_edge_2( F, _, [ ], H ).
F = (_A∉_B∩_C),
H = [[member(_A,_B∩_C), (intersection(_B,_C,_D),member(_A,_D)), \+member(_A,_B∩_C), \+(intersection(_B,_C,_D),member(_A,_D))], [_A∉_B∩_C, \+member(_A,_B∩_C), _A∉_B∩_C, \+member(_A,_B∩_C)]]
F = (_A∉_B∩_C),
H = [[_A∉_D, \+member(_A,_D), (intersection(_B,_C,_D),_A∉_D), (intersection(_B,_C,_D),\+member(_A,_D))], [_A∉_B∩_C, (intersection(_B,_C,_D),_A∉_D), _A∉_B∩_C, (intersection(_B,_C,_D),_A∉_D)]]
false

 */ 

節プログラムto論理( A, B ):-
	 A =.. [ F | D ],
	 findall( Y, (
		 member( X, D ),
		 \+ var( X ),
		 節プログラムto論理( X, Y ) 
	 ), L ),
	 Ax =.. [ F | L ],
	 論理スキーマ( C, Ax, _ - 基本 ),
	 節プログラムto論理( C, B ).

節プログラムto論理( A, A ):-
    T = ( _ - 基本 ),
    \+ 論理スキーマ( _, A, T ), !.

test_formula_2:-
    ルールtoスキーマ((_:-A), J, _, _ ), 
    A\= true,
    節プログラムto論理( A, B ), 
    numbervars([A,B]), 
    nl, 
    write(J:-B ), 
    fail ; nl.
/*
?- test_formula_2.

順序(B):-alternatives(C)∧permutation(D,E)
順序の全体集合(B):-findall(A,ranking(A),B)
番号付き順序(B,C):-all_rankings(D)∧nth1(E,F,G)
プロフィール生成(B,C):-length(D,E)∧maplist(rc,F,G)
プロフィール(B):-number_of_persons(C)∧pp(D,E)
無制限領域(B):-findall(A,pp(A),B)
社会選択関数scf(A,B,C):-f(A,B,C,[])
社会選択関数scf(A,B,C,F):-scf(G,H,I)∧((dictatorial_scf(J,K,L)->M=dict(K))∨N=poss∧O=P)
全域の社会厚生関数swf(B,C):-unrestricted_domain(D)∧swf(E,F,G)
社会厚生関数swf(A,B,C):-scf(arrow-type,A,B,C)
関数の構成(A,F,[B|E],D):-scf_axiom(G,H,I,J,K)∧f(L,M,N,[O-P|Q])
社会選択関数の公理(gs-type,C,A,E,F):-x(G)∧(￢manipulable(H,I-J,K,L)∧((M=[]->non_imposed([N-O|P]))∨true))
社会選択関数の公理(arrow-type,B,A,C,_70378):-ranking(D)∧(pareto(E-F)∧iia(G-H,I))
証明(B):-unrestricted_domain(E)∧(scf(F-type,G,H,I)∧(fig(J-type,K)∧(writeln(L)∧fail)))
チェックscf(A,C,D):-(\+scf(E,F,G,poss)->H=dict)∨I=poss
カウントscf(A,C,D,F):-findall(1,scf(G,H,I,J),K)∧length(L,M)
社会厚生関数(A,B,C):-scf(arrow-type,A,B,C)
一致(+,A,B,[C, D]):-p(E,F,G)∧p(H,I,J)
一致(-,B,A,[C, D]):-agree(+,A,B,[C, D])
全会一致(A,B,C,[D|E]):-agree(+,F,G,[H, I])∧unanimous(J,K,L,M)
全会一致(A,B,[C|D]):-unanimous(A,B,C,D)
パレート条件(C-D) :- ￢(unanimous(E,F,G) ∧ ￢p(H,I,J))
図示(domain,C):-findall(E-F,nth1(F,G,E),H)∧(fig(gs-type,I)∧!)
図示(membership,A):-partition_membership(C,D)∧(fig(gs-type,E)∧!)
図示(_70354,_70360):-nl∧(rc(1,F)∧(nl∧(tab(2)∧(term_string((1:G),H)∧(string_length(I,J)∧(tab(K)∧(rc(L,M)∧(write(N)∧((O<10->tab(2))∨tab(1)∧fail)))))))))
図示(_70354,_70360):-rc(1,H)∧(nl∧(tab(2)∧(term_string((1:I),J)∧(string_length(K,L)∧(tab(M)∧(findall(---,rc(N,O),P)∧(atomic_list_concat(Q,R)∧(write(S)∧fail))))))))
図示(E,F):-rc(G,H)∧(nl∧(write((I:J))∧(tab(1)∧((K<10->tab(1))∨true∧(rc(L,M)∧(fig_cell(N,[O, P],Q)∧fail))))))
図示(_70354,_70360):-nl∧write(--)
リスト長(C,A):-var(F)∧(!∧($skip_list(G,H,I)∧((J==[]->K=L)∨((var(M)->M\==N,$length3(M,N,O))∨throw(error(type_error(list,P),context(length/2,Q)))))))
リスト長(C,A):-integer(G)∧(H>=0∧(!∧($skip_list(I,J,K)∧((L==[]->M=N)∨((var(O)->P is Q-R,$length(O,P))∨throw(error(type_error(list,S),context(length/2,T))))))))
リスト長(_70354,A):-integer(C)∧(!∧throw(error(domain_error(not_less_than_zero,D),context(length/2,E))))
リスト長(_70354,A):-throw(error(type_error(integer,A),context(length/2,B)))
リストの要素(B,[C|A]):-member_(A,B,C)
全ゴール収集(A,B,C):-findall(A,B,C,[])
パタン別ゴール収集(A,B,E) :- $free_variable_set(I^J,K,L)∧((M==v->findall(N,O,P),P\==[])∨(alloc_bind_key_list(Q,R)∧(findall(S-T,U,V)∧(bind_bagof_keys(W,X)∧(keysort(Y,Z)∧pick(A1,B1,C1))))))
パタン別ゴール整列(A,B,F) :- $free_variable_set(J^K,L,M)∧((N==v->findall(O,P,Q),Q\==[],sort(Q,R))∨(alloc_bind_key_list(S,T)∧(findall(U-V,W,X)∧((ground(Y)->sort(Y,Z),pick(Z,A1,B1))∨(bind_bagof_keys(C1,D1)∧(sort(E1,F1)∧(pick(G1,H1,I1)∧sort(J1,K1))))))))
条件命題(A,B) :- ￢(call(C) ∧ ￢call(D))
いけませんね: error(permission_error(access,private_procedure,!/0),context(system:clause/2,_70532))

改行:-pengine_nl
印字(A):-pengine_write(A)
印字と改行(A):-pengine_writeln(A)
空白(A):-pengine_tab(A)
成型印字(A):-pengine_format(A)
いけませんね: error(permission_error(access,private_procedure,tell/1),context(system:clause/2,_70746))
...
*/


