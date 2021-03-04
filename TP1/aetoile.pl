%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 
	initial_state(S0),
	G0 is 0, 
	heuristique(S0, H0),
	F0 is H0 + G0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([ [F0,H0,G0], S0 ], Pf, Pf1), 
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q).



%*******************************************************************************

affichage_solution(nil, _, _).
affichage_solution(U, Pu, Q) :- 
% Verifier que U \= null ? 
	belongs([U, [_,_,_], Pere, A], Q), 
	affichage_solution(Pere, Pu, Q), 
	write_state(U), 
	writeln(A).


expand(S, [_,_, Gu], U, Action, [Fs, Hs, Gs]) :- 
	rule(Action, Cost, U, S), 
	Gs is Gu + Cost, 
	heuristique(S, Hs),
	Fs is Hs + Gs.

loop_successors([], Pf, Pu, _Q, Pf, Pu).
loop_successors([[U, [Fi, _Hi, _Gi], _, _] | Tail], Pf, Pu, Q, New_Pf, New_Pu) :- 
	(not(belongs([U, [_,_,_], _, _], Q)) -> % si S est connu dans Q
		loop_successors(Tail, Pf, Pu, Q, New_Pf, New_Pu)
	;
		(not(belongs([U, [Fu,Hu,Gu], Pereu, Actu], Pu)) -> % si S est connu dans Pu
			Fu < Fi, 
			loop_successors(Tail,  Pf, Pu, Q, New_Pf, New_Pu)
		;
			F is Fu,
			H is Hu, 
			G is Gu,
			insert([[F,H,G], U], Pf, New_Pf),
			insert([U, [F,H,G], Pereu, Actu], Pu, New_Pu)
		)
	).
	



aetoile([],[], _) :- write("PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE !").
aetoile(Pf,Pu,Q) :-
	suppress_min([Min, Final], Pf, Pf1), 
	final_state(Final),
	affiche_solution(Final, Pu, Q). 
aetoile(Pf, Pu, Qs) :- 
	suppress_min([Min, U], Pf, Pf1), 
	suppress([U, Min, Pereu, Actu], Pu, Pu1),
	insert([U, Min, Pereu, Actu], Q, Q1), 
	findall([S, Val, U, A], expand(S, Min, U, A, Val), L),
	loop_successors(L, Pf, Pu, Q, New_Pf, New_Pu),
	insert([U, Val, Pereu, Actu], New_Q), % a verifier
	aetoile(New_Pf, New_Pu, New_Q). 
	

	
