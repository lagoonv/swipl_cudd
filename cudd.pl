:- module(cudd,[bdd/1,
		bdd_init/0,
		bdd_quit/0,
		bdd_var/1,
		bdd_var0/1,
		bdd_zero/1,
		bdd_one/1,
		bdd_and/3,
		bdd_or/3,
		bdd_xor/3,
		bdd_not/2,
		bdd_ite/4,
		bdd_iff/3,

		bdd_cube/2,
		bdd_forall/3,
		bdd_exist/3,

		bdd_and_abstract/4,

		bdd_constrain/3,
		bdd_restrict/3,
		bdd_cofactor/3,

		bdd_satisfy/2,
		
		bdd_is_zero/1,
		bdd_is_one/1,
		bdd_eq/2,
		bdd_le/2,

		bdd_id/2,
		bdd_level/2,
		bdd_ptr/2,
		bdd_if/2,
		bdd_then/2,
		bdd_else/2,
		bdd_rename/4,
		bdd_essential/2,

		bdd_count_paths/2,
		bdd_count_paths_to_zero/2,
		bdd_count_paths_to_one/2,
		bdd_count_nodes/2,
		bdd_avg_pathlen/2,
		bdd_max_pathlen/2,
		
		bdd_dump_dot/2,

		bdd_mem/5,
		bdd_gc/0,

		bdd_enable_reordering/1,
		bdd_disable_reordering/0,
		
		bdd_eval/2

	       ]).

:- license(lgpl).

:- use_module(library(shlib)).
:- load_foreign_library('pl_cudd.so',install).

user:portray(Atom) :-
	atom(Atom),
	name(Atom,N),
	append("$bdd",[A,B,C,D|_],N),
	( bdd_is_zero(Atom) ->
	    writeq('$bdd:0')
	;
	    ( bdd_is_one(Atom) ->
		writeq('$bdd:1')
	    ;
		Addr is (((D*256)+C)*256+B)*256+A, 
		format('$bdd:0x~16r',[Addr])
	    )
	).
	    


%%bdd(X) :- atom(X), name(X,N), append("$bdd",_,N).


bdd_eval(V,V) :- var(V), !, bdd_var(V).

bdd_eval(X,X) :- bdd(X), !.

bdd_eval(false,Zero) :- !, bdd_zero(Zero).

bdd_eval(true,One) :- !, bdd_one(One).

bdd_eval(0,Zero) :- !, bdd_zero(Zero).

bdd_eval(1,One) :- !, bdd_one(One).

bdd_eval((A+B),R) :- !,		% OR
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B),
	bdd_or(BDD_A,BDD_B,R).

bdd_eval((A*B),R) :- !,		% AND
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B),
	bdd_and(BDD_A,BDD_B,R).

bdd_eval((A xor B),R) :- !,		% AND
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B),
	bdd_xor(BDD_A,BDD_B,R).

bdd_eval((A=B),R) :- !,		% IFF
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B),
	%%bdd_not(BDD_B,NB), bdd_ite(BDD_A,BDD_B,NB,R).
	bdd_iff(BDD_A,BDD_B,R).

bdd_eval((-A),R) :- !,		% NOT
	bdd_eval(A,BDD_A), bdd_not(BDD_A,R).

bdd_eval((A -> B ; C),R) :- !,	% IF -> THEN ; ELSE
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B), bdd_eval(C,BDD_C),
	bdd_ite(BDD_A,BDD_B,BDD_C,R).

bdd_eval((A -> B),R) :- !,	% IF -> THEN
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B), bdd_one(One),
	bdd_ite(BDD_A,BDD_B,One,R).

bdd_eval(forall(L,F),R) :- !,
	list_of_bdds(L),
	bdd_eval(F,F_BDD), 
	bdd_cube(L,Cube_L),
	bdd_forall(Cube_L,F_BDD,R).

bdd_eval(exist(L,F),R) :- !,
	list_of_bdds(L),
	bdd_eval(F,F_BDD), 
	bdd_cube(L,Cube_L),
	bdd_exist(Cube_L,F_BDD,R).

bdd_eval(and_abstract(L,F,G),R) :- !,
	list_of_bdds(L),
	bdd_eval(F,F_BDD),
	bdd_eval(G,G_BDD),
	bdd_cube(L,CubeL),
	bdd_and_abstract(CubeL,F_BDD,G_BDD,R).

bdd_eval(constrain(A,B),R) :- !,
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B),
	bdd_constrain(BDD_A,BDD_B,R).

bdd_eval((A^B),R) :- !,		% constrain
	bdd_eval(A,BDD_A), bdd_eval(B,BDD_B),
	bdd_constrain(BDD_A,BDD_B,R).

bdd_eval(T,_) :- print_message(error,T), fail.

bdd2int(L,BDD,Int) :- bdd2int(L,BDD,0,Int).
bdd2int([],_,Acc,Acc).
bdd2int([B|Bs],BDD,N,Res) :-
	\+ bdd_is_zero(BDD),
	(
	    bdd_eval(BDD*(-B),NewBDD),  NewN is N*2
	;
	    bdd_eval(BDD*B,NewBDD), NewN is N*2+1
	),
	bdd2int(Bs,NewBDD,NewN,Res).


list_of_bdds([]).
list_of_bdds([X|Xs]) :- var(X), !, bdd_var(X), list_of_bdds(Xs).
list_of_bdds([X|Xs]) :- bdd(X), list_of_bdds(Xs).


%%-----------------------------------------------------------------------------
:- dynamic(lemma/2).

bdd_avg_pathlen(BDD,AvgPathlen) :-
	retractall(lemma(_,_)),
	bdd_pathlens(BDD,Pathlens),
	bdd_count_paths(BDD,NumOfPaths),
	AvgPathlen is Pathlens/NumOfPaths.

bdd_pathlens(One,0) :- bdd_is_one(One), !.
bdd_pathlens(Zero,0) :- bdd_is_zero(Zero), !.
bdd_pathlens(BDD,Lens) :- bdd_ptr(BDD,Ptr), lemma(Ptr,Lens), !.
bdd_pathlens(BDD,Lens) :-
	bdd_then(BDD,T), bdd_else(BDD,E),
	bdd_pathlens(T,LensT), bdd_pathlens(E,LensE),
	bdd_count_paths(T,TPathsCnt),
	bdd_count_paths(E,EPathsCnt),
	Lens is TPathsCnt + EPathsCnt + LensT + LensE,
	bdd_ptr(BDD,Ptr),
	assert(lemma(Ptr,Lens)).


bdd_max_pathlen(BDD,MLen) :-
	retractall(lemma(_,_)), bdd_max_pathlen_rec(BDD,MLen).
bdd_max_pathlen_rec(One,0) :- bdd_is_one(One), !.
bdd_max_pathlen_rec(Zero,0) :- bdd_is_zero(Zero), !.
bdd_max_pathlen_rec(BDD,MLen) :-
	bdd_ptr(BDD,Ptr), lemma(Ptr,MLen), !.
bdd_max_pathlen_rec(BDD,MLen) :-
	bdd_then(BDD,T), bdd_else(BDD,E),
	bdd_max_pathlen_rec(T,TL), bdd_max_pathlen_rec(E,EL),
	MLen is max(TL,EL)+1,
	bdd_ptr(BDD,Ptr),
	assert(lemma(Ptr,MLen)).

	
%%-----------------------------------------------------------------------------

bdd_gc :-
	garbage_collect_atoms,
	bdd_gc_internal.

