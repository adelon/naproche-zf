Axiom trivial : (forall x,(x = x)).
Axiom empty_axiom : (~(exists x,(elem x (emptyset)))).
Axiom union_eq : (forall x X,((elem x (unions X))<->(exists Y,((elem x Y)/\(elem Y X))))).
Theorem eq_refl : (forall x,(x = x)).
Admitted.
