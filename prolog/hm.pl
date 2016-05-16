% var(X).
% int(N).
% true.
% false.
% add(N1,N2).
% eq(E1,E2).
% if(B,E1,E2).
% pair(E1,E2).
% fst(E).
% snd(E).
% abs(X,E).
% app(E1,E2).
% let(X,E1,E2).

bigstep(var(X),R,V) :-
    lookup(R,X,V).
bigstep(int(N),_,int(N)).
bigstep(bool(B),_,bool(B)).
bigstep(add(N1,N2),R,int(V)) :-
    bigstep(N1,R,int(V1)),
    bigstep(N2,R,int(V2)),
    V is V1 + V2.
bigstep(eq(E1,E2),R,true) :-
    bigstep(E1,R,int(V)),
    bigstep(E2,R,int(V)).
bigstep(eq(E1,E2),R,false) :-
    bigstep(E1,R,int(V1)),
    bigstep(E2,R,int(V2)),
    V1 \== V2.
bigstep(if(B,E1,_),R,V) :-
    bigstep(B,R,true),
    bigstep(E1,R,V).
bigstep(if(B,_,E2),R,V) :-
    bigstep(B,R,false),
    bigstep(E2,R,V).
bigstep(pair(E1,E2),R,pair(V1,V2)) :-
    bigstep(E1,R,V1),
    bigstep(E2,R,V2).
bigstep(fst(E),R,V) :-
    bigstep(E,R,pair(V,_)).
bigstep(snd(E),R,V) :-
    bigstep(E,R,pair(_,V)).
bigstep(abs(X,E),R,clo(abs(X,E),R)).
bigstep(app(E1,E2),R,V) :-
    bigstep(E1,R,clo(abs(X,B),RLex)),
    bigstep(E2,R,V2),
    bigstep(B,[v(X,V2)|RLex],V).
bigstep(let(X,E1,E2),R,V) :-
    bigstep(E1,R,V1),
    bigstep(E2,[v(X,V1)|R],V).

type(G,var(X),T) :-
    lookup(G,X,T).
type(_,int(_),int).
type(_,true,bool).
type(_,false,bool).
type(G,add(N1,N2),int) :-
    type(G,N1,int),
    type(G,N2,int).
type(G,eq(N1,N2),bool) :-
    type(G,N1,int),
    type(G,N2,int).
type(G,if(B,N1,N2),T) :-
    type(G,B,bool),
    type(G,N1,T),
    type(G,N2,T).
type(G,pair(E1,E2),prod(T1,T2)) :-
    type(G,E1,T1),
    type(G,E2,T2).
type(G,fst(E),T) :-
    type(G,E,prod(T,_)).
type(G,snd(E),T) :-
    type(G,E,prod(_,T)).
type(G,abs(X,E),arrow(T1,T2)) :-
    type([v(X,T1)|G],E,T2).
type(G,app(E1,E2),X) :-
    type(G,E1,T1),
    type(G,E2,T2),
    T1 = arrow(T2,X).
type(G,let(X,E1,E2),T) :-
    type(G,E1,T1),
    type([v(X,T1)|G],E2,T).

example1(abs(a,abs(b,add(int(2),app(var(a),add(var(b),int(3))))))).
example2(app(E1,abs(x,add(var(x),int(1))))) :- example1(E1).
example3(app(E2,int(3))) :- example2(E2).
example4(let(f,abs(x,var(x)),pair(app(var(f),int(5)),app(var(f),true)))).
example5(abs(y,let(f,abs(x,var(y)),pair(app(var(f),int(5)),app(var(f),true))))).

poly(G,var(X),I) :-
    lookup(G,X,scheme(B,T)),
    instantiate(B,T,I).
poly(_,int(_),int).
poly(_,true,bool).
poly(_,false,bool).
poly(G,add(N1,N2),int) :-
    poly(G,N1,int),
    poly(G,N2,int).
poly(G,eq(N1,N2),bool) :-
    poly(G,N1,int),
    poly(G,N2,int).
poly(G,if(B,N1,N2),T) :-
    poly(G,B,bool),
    poly(G,N1,T),
    poly(G,N2,T).
poly(G,pair(E1,E2),prod(T1,T2)) :-
    poly(G,E1,T1),
    poly(G,E2,T2).
poly(G,fst(E),T) :-
    poly(G,E,prod(T,_)).
poly(G,snd(E),T) :-
    poly(G,E,prod(_,T)).
poly(G,abs(X,E),arrow(T1,T2)) :-
    poly([v(X,scheme([],T1))|G],E,T2).
poly(G,app(E1,E2),X) :-
    poly(G,E1,T1),
    poly(G,E2,T2),
    T1 = arrow(T2,X).
poly(G,let(X,E1,E2),T) :-
    poly(G,E1,T1),
    term_variables(T1,T1Free),
    term_variables(G,GFree),
    subtract(T1Free,GFree,Vars),
    poly([v(X,scheme(Vars,T1))|G],E2,T).

instantiate(Vars,T,I) :-
    copy_term(T,I),
    unify_bound(Vars,T,I), !.

unify_bound(Vars,Var,_) :-
    var(Var),
    memberchk(Var,Vars).
unify_bound(Vars,Var1,Var2) :-
    var(Var1),
    \+ memberchk(Var1,Vars),
    Var1 = Var2.
unify_bound(Vars,arrow(A1,A2),arrow(B1,B2)) :-
    unify_bound(Vars,A1,B1),
    unify_bound(Vars,A2,B2).
unify_bound(Vars,pair(A1,A2),pair(B1,B2)) :-
    unify_bound(Vars,A1,B1),
    unify_bound(Vars,A2,B2).

lookup(List,X,N) :-
    memberchk(v(X,N),List).
