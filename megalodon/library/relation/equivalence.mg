Let emptyset : set := Empty.
Let elem : set->set->prop := In.
Let notelem : set->set->prop := fun a A => ~(In a A).
Let pow : set->set := Power.
Let unions : set->set := Union.
Let union : set->set->set := binunion.
Let cons : set -> set -> set := fun x X => binunion {x} X.
Let xor : prop -> prop -> prop := fun p q =>  (p \/ q) /\ ~(p /\ q).
Let pair : set -> set -> set := fun a b => {{a}, {a, b}}.
Let fst : set -> set := fun p => Eps_i (fun a => exists b, p = pair a b).
Let snd : set -> set := fun p => Eps_i (fun b => exists a, p = pair a b).
Let nor : prop -> prop -> prop := fun p q => ~(p \/ q) .
Definition ni := fun x0 x1 : set => (elem x1 x0).
Fact setext : (forall A B,(((forall a,(((elem a A)<->(elem a B))))->(A = B)))).
Admitted.
Theorem neq_witness : (forall A B,(((A <> B)->(exists c,((xor((elem c A)/\~((elem c B))) (~((elem c A))/\(elem c B)))))))).
Admitted.
Definition subseteq := fun A B: set => (forall a,(((elem a A)->(elem a B)))).
Definition is_subset := fun x0 x1 : set => (subseteq x0 x1).
Theorem subseteq_refl : (forall A,((subseteq A A))).
Admitted.
Theorem subseteq_antisymmetric : (forall A B,((((subseteq A B)/\(subseteq B A))->(A = B)))).
Admitted.
Theorem elem_subseteq : (forall a A B,((((elem a A)/\(subseteq A B))->(elem a B)))).
Admitted.
Theorem not_in_subseteq : (forall A B c,((((subseteq A B)/\(notelem c B))->(notelem c A)))).
Admitted.
Theorem subseteq_transitive : (forall A B C,((((subseteq A B)/\(subseteq B C))->(subseteq A C)))).
Admitted.
Definition subset := fun A B: set => ((subseteq A B)/\(A <> B)).
Theorem subset_irrefl : (forall A,(~((subset A A)))).
Admitted.
Theorem subset_transitive : (forall A B C,((((subseteq A B)/\(subseteq B C))->(subseteq A C)))).
Admitted.
Theorem subset_witness : (forall A B,(((subset A B)->(exists b,(((elem b B)/\(notelem b A))))))).
Admitted.
Definition family_of_subsets := fun x0 x1 : set => (forall A,(((elem A x0)->(subseteq A x1)))).
Fact emptyset : (forall a,((notelem a (emptyset)))).
Admitted.
Definition inhabited := fun A: set => (exists a,((elem a A))).
Definition empty := fun x0 : set => ~((inhabited x0)).
Theorem empty_eq : (forall x y,((((empty x)/\(empty y))->(x = y)))).
Admitted.
Theorem emptyset_subseteq : (forall a,((subseteq (emptyset) a))).
Admitted.
Theorem subseteq_emptyset_iff : (forall A,(((subseteq A (emptyset))<->(A = (emptyset))))).
Admitted.
Definition disjoint := fun A B: set => ~((exists a,(((elem a A)/\(elem a B))))).
Definition notmeets := fun x0 x1 : set => (disjoint x0 x1).
Definition meets := fun x0 x1 : set => ~((disjoint x0 x1)).
Theorem disjoint_symmetric : (forall A B,(((disjoint A B)->(disjoint B A)))).
Admitted.
Fact in_cons : (forall x y X,(((elem x (cons y X))<->((x = y)\/(elem x X))))).
Admitted.
Theorem in_cons_left : (forall x X,((elem x (cons x X)))).
Admitted.
Theorem in_cons_right : (forall y X x,(((elem y X)->(elem y (cons x X))))).
Admitted.
Theorem upair_intro_left : (forall a b,((elem a (cons a (cons b (emptyset)))))).
Admitted.
Theorem upair_intro_right : (forall b a,((elem b (cons a (cons b (emptyset)))))).
Admitted.
Theorem upair_elim : (forall c a b,(((elem c (cons a (cons b (emptyset))))->((a = c)\/(b = c))))).
Admitted.
Theorem singleton_intro : (forall a,((elem a (cons a (emptyset))))).
Admitted.
Theorem singleton_elim : (forall a b,(((elem a (cons b (emptyset)))->(a = b)))).
Admitted.
Theorem singleton_iff : (forall a b,(((elem a (cons b (emptyset)))<->(a = b)))).
Admitted.
Theorem singleton_subset_intro : (forall a C,(((elem a C)->(subseteq (cons a (emptyset)) C)))).
Admitted.
Theorem singleton_subset_elim : (forall a C,(((subseteq (cons a (emptyset)) C)->(elem a C)))).
Admitted.
Fact unions_iff_exists : (forall z X,(((elem z (unions X))<->(exists Y,(((elem Y X)/\(elem z Y))))))).
Admitted.
Theorem unions_intro : (forall A B C,((((elem A B)/\(elem B C))->(elem A (unions C))))).
Admitted.
Theorem unions_emptyset : ((unions (emptyset)) = (emptyset)).
Admitted.
Definition inters := fun A : set => {x :e ((unions A))|(forall a,(((elem a A)->(elem x a))))}.
Theorem inters_iff_forall : (forall z X,(((elem z (inters X))<->((inhabited X)/\(forall Y,(((elem Y X)->(elem z Y)))))))).
Admitted.
Theorem inters_intro : (forall C A,((((inhabited C)/\(forall B,(((elem B C)->(elem A B)))))->(elem A (inters C))))).
Admitted.
Theorem inters_destr : (forall A C B,((((elem A (inters C))/\(elem B C))->(elem A B)))).
Admitted.
Theorem inters_singleton : (forall a,(((inters (cons a (emptyset))) = a))).
Admitted.
Theorem inters_emptyset : ((inters (cons (emptyset) (emptyset))) = (emptyset)).
Admitted.
Fact union_iff : (forall a A B,(((elem a (union A B))<->((elem a A)\/(elem a B))))).
Admitted.
Theorem union_intro_left : (forall c A B,(((elem c A)->(elem c (union A B))))).
Admitted.
Theorem union_intro_right : (forall c B A,(((elem c B)->(elem c (union A B))))).
Admitted.
Theorem union_comm : (forall A B,(((union A B) = (union B A)))).
Admitted.
Theorem union_assoc : (forall A B C,(((union (union A B) C) = (union A (union B C))))).
Admitted.
Theorem union_idempotent : (forall A,(((union A A) = A))).
Admitted.
Theorem union_subseteq_iff : (forall A B C,(((subseteq (union A B) C)<->((subseteq A C)/\(subseteq B C))))).
Admitted.
Theorem union_upper_left : (forall A B,((subseteq A (union A B)))).
Admitted.
Theorem union_upper_right : (forall B A,((subseteq B (union A B)))).
Admitted.
Theorem union_emptyset : (forall A,(((union A (emptyset)) = A))).
Admitted.
Theorem union_emptyset_intro : (forall A B,((((A = (emptyset))/\(B = (emptyset)))->((union A B) = (emptyset))))).
Admitted.
Theorem union_emptyset_elim_left : (forall A B,((((union A B) = (emptyset))->(A = (emptyset))))).
Admitted.
Theorem union_emptyset_elim_right : (forall A B,((((union A B) = (emptyset))->(B = (emptyset))))).
Admitted.
Theorem union_absorb_subseteq_left : (forall A B,(((subseteq A B)->((union A B) = B)))).
Admitted.
Theorem union_absorb_subseteq_right : (forall A B,(((subseteq A B)->((union B A) = B)))).
Admitted.
Theorem union_eq_self_implies_subseteq : (forall A B,((((union A B) = B)->(subseteq A B)))).
Admitted.
Theorem unions_cons : (forall b A,(((unions (cons b A)) = (union b (unions A))))).
Admitted.
Theorem union_cons : (forall b A C,(((union (cons b A) C) = (cons b (union A C))))).
Admitted.
Theorem union_absorb_left : (forall A B,(((union A (union A B)) = (union A B)))).
Admitted.
Theorem union_absorb_right : (forall A B,(((union (union A B) B) = (union A B)))).
Admitted.
Theorem union_comm_left : (forall A B C,(((union A (union B C)) = (union B (union A C))))).
Admitted.
Definition inter := fun A B : set => {a :e (A)|(elem a B)}.
Theorem inter_intro : (forall c A B,((((elem c A)/\(elem c B))->(elem c (inter A B))))).
Admitted.
Theorem inter_elim_left : (forall c A B,(((elem c (inter A B))->(elem c A)))).
Admitted.
Theorem inter_elim_right : (forall c A B,(((elem c (inter A B))->(elem c B)))).
Admitted.
Theorem inter_comm : (forall A B,(((inter A B) = (inter B A)))).
Admitted.
Theorem inter_assoc : (forall A B C,(((inter (inter A B) C) = (inter A (inter B C))))).
Admitted.
Theorem inter_idempotent : (forall A,(((inter A A) = A))).
Admitted.
Theorem inter_subseteq : (forall A B,((subseteq (inter A B) A))).
Admitted.
Theorem inter_emptyset : (forall A,(((inter A (emptyset)) = (emptyset)))).
Admitted.
Theorem inter_absorb_superseteq_right : (forall A B,(((subseteq A B)->((inter A B) = A)))).
Admitted.
Theorem inter_absorb_superseteq_left : (forall A B,(((subseteq A B)->((inter B A) = A)))).
Admitted.
Theorem inter_eq_left_implies_subseteq : (forall A B,((((inter A B) = A)->(subseteq A B)))).
Admitted.
Theorem subseteq_inter_iff : (forall C A B,(((subseteq C (inter A B))<->((subseteq C A)/\(subseteq C B))))).
Admitted.
Theorem inter_lower_left : (forall A B,((subseteq (inter A B) A))).
Admitted.
Theorem inter_lower_right : (forall A B,((subseteq (inter A B) B))).
Admitted.
Theorem inter_absorb_left : (forall A B,(((inter A (inter A B)) = (inter A B)))).
Admitted.
Theorem inter_absorb_right : (forall A B,(((inter (inter A B) B) = (inter A B)))).
Admitted.
Theorem inter_comm_left : (forall A B C,(((inter A (inter B C)) = (inter B (inter A C))))).
Admitted.
Theorem inter_distrib_union : (forall x y z,(((inter x (union y z)) = (union (inter x y) (inter x z))))).
Admitted.
Theorem union_distrib_inter : (forall x y z,(((union x (inter y z)) = (inter (union x y) (union x z))))).
Admitted.
Theorem union_inter_assoc_intro : (forall C A B,(((subseteq C A)->((union (inter A B) C) = (inter A (union B C)))))).
Admitted.
Theorem union_inter_assoc_elim : (forall A B C,((((union (inter A B) C) = (inter A (union B C)))->(subseteq C A)))).
Admitted.
Theorem union_inter_crazy : (forall A B C,(((union (union (inter A B) (inter B C)) (inter C A)) = (inter (inter (union A B) (union B C)) (union C A))))).
Admitted.
Definition setminus := fun A B : set => {a :e (A)|~((elem a B))}.
Theorem setminus_intro : (forall a A B,((((elem a A)/\(notelem a B))->(elem a (setminus A B))))).
Admitted.
Theorem setminus_elim_left : (forall a A B,(((elem a (setminus A B))->(elem a A)))).
Admitted.
Theorem setminus_elim_right : (forall a A B,(((elem a (setminus A B))->(notelem a B)))).
Admitted.
Theorem setminus_emptyset : (forall x,(((setminus x (emptyset)) = x))).
Admitted.
Theorem emptyset_setminus : (forall x,(((setminus (emptyset) x) = (emptyset)))).
Admitted.
Theorem setminus_self : (forall x,(((setminus x x) = (emptyset)))).
Admitted.
Theorem setminus_setminus : (forall x y,(((setminus x (setminus x y)) = (inter x y)))).
Admitted.
Theorem setminus_inter : (forall x y z,(((setminus x (inter y z)) = (union (setminus x y) (setminus x z))))).
Admitted.
Theorem setminus_union : (forall x y z,(((setminus x (union y z)) = (inter (setminus x y) (setminus x z))))).
Admitted.
Theorem inter_setminus : (forall x y z,(((inter x (setminus y z)) = (setminus (inter x y) (inter x z))))).
Admitted.
Theorem difference_with_proper_subset_is_inhabited : (forall A B,(((subset A B)->(inhabited (setminus B A))))).
Admitted.
Theorem setminus_subseteq : (forall B A,((subseteq (setminus B A) B))).
Admitted.
Theorem subseteq_setminus : (forall C A B,((((subseteq C A)/\((inter C B) = (emptyset)))->(subseteq C (setminus A B))))).
Admitted.
Theorem setminus_absorb_right : (forall A B,((((inter A B) = (emptyset))->((setminus A B) = A)))).
Admitted.
Theorem setminus_eq_emptyset_iff_subseteq : (forall A B,((((setminus A B) = (emptyset))<->(subseteq A B)))).
Admitted.
Theorem subseteq_setminus_cons_intro : (forall B A C c,((((subseteq B (setminus A C))/\(notelem c B))->(subseteq B (setminus A (cons c C)))))).
Admitted.
Theorem subseteq_setminus_cons_elim : (forall B A c C,(((subseteq B (setminus A (cons c C)))->((subseteq B (setminus A C))/\(notelem c B))))).
Admitted.
Theorem setminus_cons : (forall A a B,(((setminus A (cons a B)) = (setminus (setminus A (cons a (emptyset))) B)))).
Admitted.
Theorem setminus_cons_flip : (forall A a B,(((setminus A (cons a B)) = (setminus (setminus A B) (cons a (emptyset)))))).
Admitted.
Theorem setminus_disjoint : (forall A B,(((inter A (setminus B A)) = (emptyset)))).
Admitted.
Theorem setminus_partition : (forall A B,(((subseteq A B)->((union A (setminus B A)) = B)))).
Admitted.
Theorem subseteq_union_setminus : (forall A B,((subseteq A (union B (setminus A B))))).
Admitted.
Theorem double_complement : (forall A B C,((((subseteq A B)/\(subseteq B C))->((setminus B (setminus C A)) = A)))).
Admitted.
Theorem double_complement_union : (forall A B,(((setminus (union A B) (setminus B A)) = A))).
Admitted.
Theorem setminus_eq_inter_complement : (forall A C B,((((subseteq A C)/\(subseteq B C))->((setminus A B) = (inter A (setminus C B)))))).
Admitted.
Fact pair_eq_iff : (forall a b aprime bprime,((((pair a b) = (pair aprime bprime))<->((a = aprime)/\(b = bprime))))).
Admitted.
Fact pair_neq_emptyset : (forall a b,(((pair a b) <> (emptyset)))).
Admitted.
Fact pair_neq_fst : (forall a b,(((pair a b) <> a))).
Admitted.
Fact pair_neq_snd : (forall a b,(((pair a b) <> b))).
Admitted.
Theorem triple_eq_iff : (forall a b c aprime bprime cprime,((((pair a (pair b c)) = (pair aprime (pair bprime cprime)))<->(((a = aprime)/\(b = bprime))/\(c = cprime))))).
Admitted.
Fact fst_eq : (forall a b,(((fst (pair a b)) = a))).
Admitted.
Fact snd_eq : (forall a b,(((snd (pair a b)) = b))).
Admitted.
Theorem pair_eq_pair_of_proj : (forall a b,(((pair a b) = (pair (fst (pair a b)) (snd (pair a b)))))).
Admitted.
Definition times := fun A B : set => Eps_i (fun frs : set => (forall frv,(((elem frv frs)<->(exists a b,((((elem a A)/\(elem b B))/\((pair a b) = frv)))))))).
Theorem times_tuple_elim : (forall x y X Y,(((elem (pair x y) (times X Y))->((elem x X)/\(elem y Y))))).
Admitted.
Theorem times_tuple_intro : (forall x X y Y,((((elem x X)/\(elem y Y))->(elem (pair x y) (times X Y))))).
Admitted.
Theorem times_empty_left : (forall Y,(((times (emptyset) Y) = (emptyset)))).
Admitted.
Theorem times_empty_right : (forall X,(((times X (emptyset)) = (emptyset)))).
Admitted.
Theorem times_empty_iff : (forall X Y,(((empty (times X Y))<->((empty X)\/(empty Y))))).
Admitted.
Theorem fst_type : (forall c A B,(((elem c (times A B))->(elem (fst c) A)))).
Admitted.
Theorem snd_type : (forall c A B,(((elem c (times A B))->(elem (snd c) B)))).
Admitted.
Theorem times_elem_is_tuple : (forall p X Y,(((elem p (times X Y))->(exists x y,(((elem x X)/\((elem y Y)/\(p = (pair x y))))))))).
Admitted.
Theorem times_proj_elim : (forall p X Y,(((elem p (times X Y))->((elem (fst p) X)/\(elem (snd p) Y))))).
Admitted.
Definition partition := fun P: set => ((notelem (emptyset) P)/\(forall B C,(((((elem B P)/\(elem C P))/\(B <> C))->(disjoint B C))))).
Definition partition_of := fun x0 x1 : set => ((partition x0)/\((unions x0) = x1)).
Theorem partition_emptyset : (partition_of (emptyset) (emptyset)).
Admitted.
Definition partition_refinement := fun Pprime P: set => (forall Aprime,(((elem Aprime Pprime)->(exists A,(((elem A P)/\(subseteq Aprime A))))))).
Definition partition_refines := fun x0 x1 : set => (partition_refinement x0 x1).
Theorem partition_refinement_transitive : (forall Pprimeprime Pprime P,((((partition_refines Pprimeprime Pprime)/\(partition_refines Pprime P))->(partition_refines Pprimeprime P)))).
Admitted.
Definition powerset_of := fun x0 : set => (pow x0).
Fact pow_iff : (forall B A,(((elem B (pow A))<->(subseteq B A)))).
Admitted.
Theorem powerset_intro : (forall A B,(((subseteq A B)->(elem A (pow B))))).
Admitted.
Theorem powerset_elim : (forall A B,(((elem A (pow B))->(subseteq A B)))).
Admitted.
Theorem powerset_bottom : (forall A,((elem (emptyset) (pow A)))).
Admitted.
Theorem powerset_top : (forall A,((elem A (pow A)))).
Admitted.
Theorem unions_subseteq_of_powerset_is_subseteq : (forall B A,(((is_subset B (pow A))->(subseteq (unions B) A)))).
Admitted.
Theorem unions_powerset : (forall A,(((unions (pow A)) = A))).
Admitted.
Theorem inters_powerset : (forall A,(((inters (pow A)) = (emptyset)))).
Admitted.
Theorem union_powersets_subseteq : (forall A B,((subseteq (union (pow A) (pow B)) (pow (union A B))))).
Admitted.
Theorem times_subseteq_left : (forall A C B,(((subseteq A C)->(subseteq (times A B) (times C B))))).
Admitted.
Theorem times_subseteq_right : (forall B D A,(((subseteq B D)->(subseteq (times A B) (times A D))))).
Admitted.
Theorem inter_times_intro : (forall w A B C D,(((elem w (times (inter A B) (inter C D)))->(elem w (inter (times A C) (times B D)))))).
Admitted.
Theorem inter_times_elim : (forall w A C B D,(((elem w (inter (times A C) (times B D)))->(elem w (times (inter A B) (inter C D)))))).
Admitted.
Theorem inter_times : (forall A B C D,(((times (inter A B) (inter C D)) = (inter (times A C) (times B D))))).
Admitted.
Theorem inter_times_right : (forall X Y Z,(((times (inter X Y) Z) = (inter (times X Z) (times Y Z))))).
Admitted.
Theorem inter_times_left : (forall X Y Z,(((times X (inter Y Z)) = (inter (times X Y) (times X Z))))).
Admitted.
Theorem union_times_intro : (forall w A B C D,(((elem w (times (union A B) (union C D)))->(elem w (union (union (union (times A C) (times B D)) (times A D)) (times B C)))))).
Admitted.
Theorem union_times_elim : (forall w A C B D,(((elem w (union (union (union (times A C) (times B D)) (times A D)) (times B C)))->(elem w (times (union A B) (union C D)))))).
Admitted.
Theorem union_times : (forall A B C D,(((times (union A B) (union C D)) = (union (union (union (times A C) (times B D)) (times A D)) (times B C))))).
Admitted.
Theorem union_times_left : (forall X Y Z,(((times (union X Y) Z) = (union (times X Z) (times Y Z))))).
Admitted.
Theorem union_times_right : (forall X Y Z,(((times X (union Y Z)) = (union (times X Y) (times X Z))))).
Admitted.
Definition relation := fun R: set => (forall w,(((elem w R)->(exists x y,((w = (pair x y))))))).
Theorem relext : (forall R S,(((((relation R)/\(relation S))/\(forall x y,(((elem (pair x y) R)<->(elem (pair x y) S)))))->(R = S)))).
Admitted.
Definition family_of_relations := fun x0 : set => (forall x9,(((elem x9 x0)->(relation x9)))).
Theorem unions_of_family_of_relations_is_relation : (forall F,(((family_of_relations F)->(relation (unions F))))).
Admitted.
Definition converse_relation := fun R : set => let MkReplFun := fun w : set => (Eps_i (fun z=>(exists x y,(((w = (pair x y))/\(z = (pair y x))))))) in {MkReplFun w|w :e (R)}.
Theorem converse_intro : (forall y x R,(((elem (pair y x) R)->(elem (pair x y) (converse_relation R))))).
Admitted.
Theorem converse_elim : (forall x y R,(((elem (pair x y) (converse_relation R))->(elem (pair y x) R)))).
Admitted.
Theorem converse_iff : (forall x y R,(((elem (pair x y) (converse_relation R))<->(elem (pair y x) R)))).
Admitted.
Theorem converse_converse_iff : (forall x y R,(((elem (pair x y) (converse_relation (converse_relation R)))<->(elem (pair x y) R)))).
Admitted.
Theorem converse_converse_eq : (forall R,(((relation R)->((converse_relation (converse_relation R)) = R)))).
Admitted.
Theorem converse_type : (forall R A B,(((subseteq R (times A B))->(subseteq (converse_relation R) (times B A))))).
Admitted.
Theorem converse_times : (forall B A,(((converse_relation (times B A)) = (times A B)))).
Admitted.
Theorem converse_emptyset : ((converse_relation (emptyset)) = (emptyset)).
Admitted.
Theorem converse_subseteq_intro : (forall R S,(((relation R)->((subseteq R S)->(subseteq (converse_relation R) (converse_relation S)))))).
Admitted.
Theorem converse_subseteq_elim : (forall R S,(((relation R)->((subseteq (converse_relation R) (converse_relation S))->(subseteq R S))))).
Admitted.
Theorem converse_subseteq_iff : (forall R S,(((relation R)->((subseteq (converse_relation R) (converse_relation S))<->(subseteq R S))))).
Admitted.
Definition dom := fun R : set => let MkReplFun := fun w : set => (Eps_i (fun x=>(exists y,((w = (pair x y)))))) in {MkReplFun w|w :e (R)}.
Definition ran := fun R : set => let MkReplFun := fun w : set => (Eps_i (fun y=>(exists x,((w = (pair x y)))))) in {MkReplFun w|w :e (R)}.
Definition fld := fun R : set => (union (dom R) (ran R)).
Definition img := fun R A : set => {b :e ((ran R))|(exists a,(((elem a A)/\(elem (pair a b) R))))}.
Definition preimg := fun R B : set => {a :e ((dom R))|(exists b,(((elem b B)/\(elem (pair a b) R))))}.
Theorem preim_eq_img_of_converse : (forall R B,(((preimg R B) = (img (converse_relation R) B)))).
Admitted.
Theorem dom_emptyset : ((dom (emptyset)) = (emptyset)).
Admitted.
Definition upward_closure := fun R a : set => {b :e ((ran R))|(elem (pair a b) R)}.
Definition downward_closure := fun R b : set => {a :e ((dom R))|(elem (pair a b) R)}.
Definition circ := fun S R : set => {p :e ((times (dom R) (ran S)))|(exists x z y,(((p = (pair x z))/\((elem (pair x y) R)/\(elem (pair y z) S)))))}.
Theorem circ_is_relation : (forall S R,((relation (circ S R)))).
Admitted.
Theorem circ_elem_intro : (forall x y R z S,((((elem (pair x y) R)/\(elem (pair y z) S))->(elem (pair x z) (circ S R))))).
Admitted.
Theorem circ_elem_elim : (forall x z S R,(((elem (pair x z) (circ S R))->(exists y,(((elem (pair x y) R)/\(elem (pair y z) S))))))).
Admitted.
Theorem circ_iff : (forall x z S R,(((elem (pair x z) (circ S R))<->(exists y,(((elem (pair x y) R)/\(elem (pair y z) S))))))).
Admitted.
Theorem circ_assoc : (forall T S R,(((circ (circ T S) R) = (circ T (circ S R))))).
Admitted.
Theorem circ_converse_intro : (forall a c R S,(((elem (pair a c) (circ (converse_relation R) (converse_relation S)))->(elem (pair a c) (converse_relation (circ S R)))))).
Admitted.
Theorem circ_converse_elim : (forall x y S R,(((elem (pair x y) (converse_relation (circ S R)))->(elem (pair x y) (circ (converse_relation R) (converse_relation S)))))).
Admitted.
Theorem circ_converse : (forall S R,(((converse_relation (circ S R)) = (circ (converse_relation R) (converse_relation S))))).
Admitted.
Definition restrl := fun R X : set => {w :e (R)|(exists x y,(((elem x X)/\(w = (pair x y)))))}.
Theorem restrl_subseteq : (forall R X,((subseteq (restrl R X) R))).
Admitted.
Theorem elem_dom_of_restrl_implies_elem_dom_and_restr : (forall x R X,(((elem x (dom (restrl R X)))->((elem x (dom R))/\(elem x X))))).
Admitted.
Theorem elem_dom_and_restr_implies_elem_of_restr : (forall x R X,((((elem x (dom R))/\(elem x X))->(elem x (dom (restrl R X)))))).
Admitted.
Theorem restrl_eq_inter : (forall R X,(((relation R)->((restrl R X) = (inter R (times X (ran R))))))).
Admitted.
Theorem dom_of_restrl_eq_inter : (forall R X,(((relation R)->((dom (restrl R X)) = (inter (dom R) X))))).
Admitted.
Theorem restrl_restrl : (forall V U R,(((subseteq V U)->((restrl (restrl R U) V) = (restrl R V))))).
Admitted.
Theorem restrl_by_dom : (forall R,(((relation R)->((restrl R (dom R)) = R)))).
Admitted.
Theorem restrl_dom : (forall R X,((subseteq (dom (restrl R X)) X))).
Admitted.
Theorem restrl_ran : (forall X R,(((subseteq X (dom R))->((ran (restrl R X)) = (img R X))))).
Admitted.
Theorem restrl_img : (forall X R A,(((subseteq X (dom R))->((img (restrl R X) A) = (img R (inter X A)))))).
Admitted.
Definition binary_relation_on := fun x0 x1 : set => (subseteq x0 (times x1 x1)).
Theorem relation_subseteq_intro_elem : (forall R B A w,((((((relation R)/\(subseteq (ran R) B))/\(subseteq (dom R) A))/\(elem w R))->(elem w (times A B))))).
Admitted.
Theorem relation_subseteq_intro : (forall R B A,(((((relation R)/\(subseteq (ran R) B))/\(subseteq (dom R) A))->(subseteq R (times A B))))).
Admitted.
Theorem relation_subseteq_implies_dom_subseteq_elem : (forall R A B a,((((subseteq R (times A B))/\(elem a (dom R)))->(elem a A)))).
Admitted.
Theorem relation_subseteq_implies_dom_subseteq : (forall R A B,(((subseteq R (times A B))->(subseteq (dom R) A)))).
Admitted.
Theorem relation_subseteq_implies_ran_subseteq_elem : (forall R A B b,((((subseteq R (times A B))/\(elem b (ran R)))->(elem b B)))).
Admitted.
Theorem relation_subseteq_implies_ran_subseteq : (forall R A B,(((subseteq R (times A B))->(subseteq (ran R) B)))).
Admitted.
Definition rels := fun A B : set => (pow (times A B)).
Theorem rels_intro : (forall R A B,(((subseteq R (times A B))->(elem R (rels A B))))).
Admitted.
Theorem rels_intro_dom_and_ran : (forall R A B,(((((relation R)/\(subseteq (dom R) A))/\(subseteq (ran R) B))->(elem R (rels A B))))).
Admitted.
Theorem rels_elim : (forall R A B,(((elem R (rels A B))->(subseteq R (times A B))))).
Admitted.
Theorem rels_weaken_dom : (forall R A B C,((((elem R (rels A B))/\(subseteq A C))->(elem R (rels C B))))).
Admitted.
Theorem rels_weaken_codom : (forall R A B D,((((elem R (rels A B))/\(subseteq B D))->(elem R (rels A D))))).
Admitted.
Definition id := fun A : set => Eps_i (fun frs : set => (forall frv,(((elem frv frs)<->(exists a,(((elem a A)/\((pair a a) = frv)))))))).
Theorem id_elem_intro : (forall a A,(((elem a A)->(elem (pair a a) (id A))))).
Admitted.
Theorem id_elem_inspect : (forall w A,(((elem w (id A))->(exists a,(((elem a A)/\(w = (pair a a)))))))).
Admitted.
Theorem id_is_relation : (forall A,((relation (id A)))).
Admitted.
Theorem id_dom : (forall A,(((dom (id A)) = A))).
Admitted.
Theorem id_ran : (forall A,(((ran (id A)) = A))).
Admitted.
Theorem id_elem_rels : (forall A,((elem (id A) (rels A A)))).
Admitted.
Definition injective := fun R: set => (forall a b aprime,((((elem (pair a b) R)/\(elem (pair aprime b) R))->(a = aprime)))).
Theorem subseteq_of_injective_is_injective : (forall S R,((((subseteq S R)/\(injective R))->(injective S)))).
Admitted.
Theorem restrl_injective : (forall R A,(((injective R)->(injective (restrl R A))))).
Admitted.
Theorem circ_injective : (forall R S,((((injective R)/\(injective S))->(injective (circ S R))))).
Admitted.
Definition left_quasireflexive_relation := fun R: set => (forall x y,(((elem (pair x y) R)->(elem (pair x x) R)))).
Definition right_quasireflexive_relation := fun R: set => (forall x y,(((elem (pair x y) R)->(elem (pair y y) R)))).
Definition quasireflexive_relation := fun R: set => (forall x y,(((elem (pair x y) R)->((elem (pair x x) R)/\(elem (pair y y) R))))).
Definition coreflexive_relation := fun R: set => (forall x y,(((elem (pair x y) R)->(x = y)))).
Definition reflexive_on := fun x0 x1 : set => (forall x,(((elem x x1)->(elem (pair x x) x0)))).
Theorem quasireflexive_iff_reflexive_on_fld : (forall R,(((quasireflexive_relation R)<->(reflexive_on R (fld R))))).
Admitted.
Definition antisymmetric_relation := fun R: set => (forall x y,((((elem (pair x y) R)/\(elem (pair y x) R))->(x = y)))).
Definition symmetric_relation := fun R: set => (forall x y,(((elem (pair x y) R)<->(elem (pair y x) R)))).
Definition transitive_relation := fun R: set => (forall x y z,((((elem (pair x y) R)/\(elem (pair y z) R))->(elem (pair x z) R)))).
Theorem transitive_downward_elem : (forall R a b c,(((((transitive_relation R)/\(elem a (downward_closure R b)))/\(elem c (downward_closure R a)))->(elem c (downward_closure R b))))).
Admitted.
Theorem transitive_downward_subseteq : (forall R a b,((((transitive_relation R)/\(elem a (downward_closure R b)))->(subseteq (downward_closure R a) (downward_closure R b))))).
Admitted.
Definition quasiorder := fun x0 : set => ((quasireflexive_relation x0)/\(transitive_relation x0)).
Definition equivalence_relation := fun x0 : set => ((quasiorder x0)/\(symmetric_relation x0)).
Definition equiv_class := fun x0 x1 : set => (downward_closure x0 x1).
Definition equiv_class_abbr := fun x0 x1 : set => (equiv_class x0 x1).
Theorem equiv_classes_inhabited : (forall E a,((((equivalence_relation E)/\(elem a (dom E)))->(elem a (equiv_class E a))))).
Admitted.
Theorem equiv_classes_diseq_implies_disjoint : (forall E a b,((((equivalence_relation E)/\((equiv_class E a) <> (equiv_class E b)))->(disjoint (equiv_class E a) (equiv_class E b))))).
Admitted.
Definition quotient_set := fun E : set => Eps_i (fun frs : set => (forall frv,(((elem frv frs)<->(exists a,(((elem a (dom E))/\((equiv_class E a) = frv)))))))).
Theorem quotient_emptyset : ((quotient_set (emptyset)) = (emptyset)).
Admitted.
Theorem quotient_elems_disjoint : (forall E B C,((((equivalence_relation E)/\(((elem B (quotient_set E))/\(elem C (quotient_set E)))/\(B <> C)))->(disjoint B C)))).
Admitted.
Theorem quotient_elems_inhabited : (forall E A,((((equivalence_relation E)/\(elem A (quotient_set E)))->(inhabited A)))).
Admitted.
Theorem quotient_notni_emptyset : (forall E,(((equivalence_relation E)->(notelem (emptyset) (quotient_set E))))).
Admitted.
Theorem quotient_partition : (forall E,(((equivalence_relation E)->(partition (quotient_set E))))).
Admitted.
