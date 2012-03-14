man(adam).
man(peter).
man(paul).

woman(marry).
woman(eve).

parent(adam,peter).
parent(eve,peter).
parent(adam,paul).
parent(marry,paul).

father(F,C):-man(F),parent(F,C).
mother(M,C):-woman(M),parent(M,C).

son(C,P):-parent(P,C),man(C).
daughter(C,P):-parent(P,C),woman(C).
siblings(A,B):-parent(P,A),parent(P,B),A\=B.

is_father(F):-father(F,_).
is_mother(M):-mother(M,_).

full_siblings(A,B):-parent(F,A),parent(F,B),parent(M,A),parent(M,B),A\=B,F\=M.

/* an uncle is a brother of the child's parent or mother'*/

descendent(D,A):-parent(A,D).
descendent(D,A):-parent(P,D),descendent(P,A).

descendent(D,A):-parent(A,P),parent(P,D).

/*
simon says scientists say simon says scientists say simon says scientists say simon says scientists say whatever simon says!
*/

