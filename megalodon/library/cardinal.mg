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
Definition supseteq := fun x0 x1 : set => (subseteq x1 x0).
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
Theorem upair_iff : (forall c a b,(((elem c (cons a (cons b (emptyset))))<->((a = c)\/(b = c))))).
Admitted.
Theorem singleton_intro : (forall a,((elem a (cons a (emptyset))))).
Admitted.
Theorem singleton_elim : (forall a b,(((elem a (cons b (emptyset)))->(a = b)))).
Admitted.
Theorem singleton_iff : (forall a b,(((elem a (cons b (emptyset)))<->(a = b)))).
Admitted.
Definition subsingleton := fun x0 : set => (forall a b,((((elem a x0)/\(elem b x0))->(a = b)))).
Theorem singleton_inhabited : (forall a,((inhabited (cons a (emptyset))))).
Admitted.
Theorem singleton_iff_inhabited_subsingleton : (forall A a,((((subsingleton A)/\(elem a A))->(A = (cons a (emptyset)))))).
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
Theorem unions_family : (forall F X,(((family_of_subsets F X)->(subseteq (unions F) X)))).
Admitted.
Definition closedunderunions := fun x0 : set => (forall M,(((is_subset M x0)->(elem (unions M) x0)))).
Definition inters := fun A : set => {x :e ((unions A))|(forall a,(((elem a A)->(elem x a))))}.
Theorem inters_iff_forall : (forall z X,(((elem z (inters X))<->((inhabited X)/\(forall Y,(((elem Y X)->(elem z Y)))))))).
Admitted.
Theorem inters_intro : (forall C A,((((inhabited C)/\(forall B,(((elem B C)->(elem A B)))))->(elem A (inters C))))).
Admitted.
Theorem inters_destr : (forall A C B,((((elem A (inters C))/\(elem B C))->(elem A B)))).
Admitted.
Theorem inters_greatest : (forall A C,((((inhabited A)/\(forall a,(((elem a A)->(subseteq C a)))))->(subseteq C (inters A))))).
Admitted.
Theorem subseteq_inters_iff : (forall A C,(((inhabited A)->((subseteq C (inters A))<->(forall a,(((elem a A)->(subseteq C a)))))))).
Admitted.
Theorem inters_subseteq_elem : (forall B A,(((elem B A)->(subseteq (inters A) B)))).
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
Theorem subseteq_union_iff : (forall A B C,(((subseteq (union A B) C)<->((subseteq A C)/\(subseteq B C))))).
Admitted.
Theorem union_upper_left : (forall A B,((subseteq A (union A B)))).
Admitted.
Theorem union_upper_right : (forall B A,((subseteq B (union A B)))).
Admitted.
Theorem union_subseteq_union : (forall A C B D,((((subseteq A C)/\(subseteq B D))->(subseteq (union A B) (union C D))))).
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
Definition closedunderunion := fun x0 : set => (forall U V,((((elem U x0)/\(elem V x0))->(elem (union U V) x0)))).
Definition inter := fun A B : set => {a :e (A)|(elem a B)}.
Theorem inter_intro : (forall c A B,((((elem c A)/\(elem c B))->(elem c (inter A B))))).
Admitted.
Theorem inter_elim_left : (forall c A B,(((elem c (inter A B))->(elem c A)))).
Admitted.
Theorem inter_elim_right : (forall c A B,(((elem c (inter A B))->(elem c B)))).
Admitted.
Theorem inter_as_inters : (forall A B,(((inters (cons A (cons B (emptyset)))) = (inter A B)))).
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
Theorem inter_absorb_supseteq_right : (forall A B,(((subseteq A B)->((inter A B) = A)))).
Admitted.
Theorem inter_absorb_supseteq_left : (forall A B,(((subseteq A B)->((inter B A) = A)))).
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
Definition closedunderinter := fun x0 : set => (forall U V,((((elem U x0)/\(elem V x0))->(elem (inter U V) x0)))).
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
Theorem inters_distrib_union : (forall A B,((((inhabited A)/\(inhabited B))->((inters (union A B)) = (inter (inters A) (inters B)))))).
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
Theorem double_relative_complement : (forall y x,(((subseteq y x)->((setminus x (setminus x y)) = y)))).
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
Theorem subseteq_implies_setminus_supseteq : (forall A B C,(((subseteq A B)->(supseteq (setminus C A) (setminus C B))))).
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
Definition times := fun A B : set => ReplSep2 (A)(fun dummyVar => B)(fun a b => True)(fun a b => (pair a b)).
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
Theorem cons_subseteq_intro : (forall x X Y,((((elem x X)/\(subseteq Y X))->(subseteq (cons x Y) X)))).
Admitted.
Theorem cons_subseteq_elim : (forall x Y X,(((subseteq (cons x Y) X)->((elem x X)/\(subseteq Y X))))).
Admitted.
Theorem cons_subseteq_iff : (forall x Y X,(((subseteq (cons x Y) X)<->((elem x X)/\(subseteq Y X))))).
Admitted.
Theorem subseteq_cons_right : (forall C B a,(((subseteq C B)->(subseteq C (cons a B))))).
Admitted.
Theorem subseteq_cons_self : (forall X y,((subseteq X (cons y X)))).
Admitted.
Definition remove_point := fun x0 x1 : set => (setminus x1 (cons x0 (emptyset))).
Theorem subseteq_cons_intro_left : (forall a C B,((((elem a C)/\(subseteq (remove_point a C) B))->(subseteq C (cons a B))))).
Admitted.
Theorem subseteq_cons_intro_right : (forall C B a,(((subseteq C B)->(subseteq C (cons a B))))).
Admitted.
Theorem subseteq_cons_elim : (forall C a B,(((subseteq C (cons a B))->((subseteq C B)\/((elem a C)/\(subseteq (remove_point a C) B)))))).
Admitted.
Theorem subseteq_cons_iff : (forall C a B,(((subseteq C (cons a B))<->((subseteq C B)\/((elem a C)/\(subseteq (remove_point a C) B)))))).
Admitted.
Theorem remove_point_eq_setminus_singletong : (forall a B,(((remove_point a B) = (setminus B (cons a (emptyset)))))).
Admitted.
Theorem union_eq_cons : (forall a B,(((union (cons a (emptyset)) B) = (cons a B)))).
Admitted.
Theorem cons_comm : (forall a b C,(((cons a (cons b C)) = (cons b (cons a C))))).
Admitted.
Theorem cons_absorb : (forall a A,(((elem a A)->((cons a A) = A)))).
Admitted.
Theorem cons_remove : (forall a A,(((elem a A)->((cons a (setminus A (cons a (emptyset)))) = A)))).
Admitted.
Theorem cons_idempotent : (forall a B,(((cons a (cons a B)) = (cons a B)))).
Admitted.
Theorem inters_cons : (forall B a,(((inhabited B)->((inters (cons a B)) = (inter a (inters B)))))).
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
Theorem powerset_emptyset : ((pow (emptyset)) = (cons (emptyset) (emptyset))).
Admitted.
Theorem powerset_union_subseteq : (forall A B,((subseteq (union (pow A) (pow B)) (pow (union A B))))).
Admitted.
Theorem subseteq_pow_unions : (forall A,((subseteq A (pow (unions A))))).
Admitted.
Theorem unions_pow : (forall A,(((unions (pow A)) = A))).
Admitted.
Theorem unions_elem_pow_iff : (forall A B,(((elem (unions A) (pow B))<->(elem A (pow (pow B)))))).
Admitted.
Theorem pow_inter : (forall A B,(((pow (inter A B)) = (inter (pow A) (pow B))))).
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
Definition elemminimal := fun x0 x1 : set => ((elem x0 x1)/\(notmeets x0 x1)).
Theorem regularity_aux : (forall a A,(((elem a A)->(exists b,(((elem b A)/\(notmeets b A))))))).
Admitted.
Theorem regularity : (forall A,(((inhabited A)->(exists x1,((elemminimal x1 A)))))).
Admitted.
Theorem foundation : (forall A,(((A = (emptyset))\/(exists a,(((elem a A)/\(forall x,(((elem x a)->(notelem x A)))))))))).
Admitted.
Theorem in_irrefl : (forall A,(~((elem A A)))).
Admitted.
Theorem in_implies_neq : (forall a A,(((elem a A)->(a <> A)))).
Admitted.
Theorem in_asymmetric : (forall a b,(((elem a b)->(notelem b a)))).
Admitted.
Definition suc := fun x : set => (cons x x).
Theorem suc_intro_self : (forall x,((elem x (suc x)))).
Admitted.
Theorem suc_intro_in : (forall x y,(((elem x y)->(elem x (suc y))))).
Admitted.
Theorem suc_elim : (forall x y,(((elem x (suc y))->((x = y)\/(elem x y))))).
Admitted.
Theorem suc_iff : (forall x y,(((elem x (suc y))<->((x = y)\/(elem x y))))).
Admitted.
Theorem suc_neq_emptyset : (forall x,(((suc x) <> (emptyset)))).
Admitted.
Theorem suc_subseteq_implies_in : (forall x y,(((subseteq (suc x) y)->(elem x y)))).
Admitted.
Theorem suc_neq_self : (forall x,(((suc x) <> x))).
Admitted.
Theorem suc_injective : (forall x y,((((suc x) = (suc y))->(x = y)))).
Admitted.
Theorem subseteq_self_suc_intro : (forall x,((subseteq x (suc x)))).
Admitted.
Theorem suc_subseteq_intro : (forall x y,((((elem x y)/\(subseteq x y))->(subseteq (suc x) y)))).
Admitted.
Theorem suc_subseteq_elim : (forall x y,(((subseteq (suc x) y)->((elem x y)/\(subseteq x y))))).
Admitted.
Theorem suc_next_subset : (forall x,(~((exists z,(((subset x z)/\(subset z (suc x)))))))).
Admitted.
Definition relation := fun R: set => (forall w,(((elem w R)->(exists x y,((w = (pair x y))))))).
Definition comparable := fun a b R: set => ((elem (pair a b) R)\/(elem (pair b a) R)).
Theorem relext : (forall R S,(((((relation R)/\(relation S))/\(forall x y,(((elem (pair x y) R)<->(elem (pair x y) S)))))->(R = S)))).
Admitted.
Definition family_of_relations := fun x0 : set => (forall x2,(((elem x2 x0)->(relation x2)))).
Theorem unions_of_family_of_relations_is_relation : (forall F,(((family_of_relations F)->(relation (unions F))))).
Admitted.
Theorem inters_of_family_of_relations_is_relation : (forall F,(((family_of_relations F)->(relation (inters F))))).
Admitted.
Theorem union_relations_is_relation : (forall R S,((((relation R)/\(relation S))->(relation (union R S))))).
Admitted.
Theorem union_relations_is_relation_type : (forall R A B S C D,((((subseteq R (times A B))/\(subseteq S (times C D)))->(subseteq (union R S) (times (union A C) (union B D)))))).
Admitted.
Theorem inter_relations_is_relation : (forall R S,((((relation R)/\(relation S))->(relation (inter R S))))).
Admitted.
Theorem setminus_relations_is_relation : (forall R S,((((relation R)/\(relation S))->(relation (setminus R S))))).
Admitted.
Definition converse_relation := fun R : set => let MkReplFun := fun w : set => (Eps_i (fun z=>(exists x y,(((w = (pair x y))/\(z = (pair y x))))))) in {MkReplFun w|w :e (R)}.
Theorem converse_intro : (forall y x R,(((elem (pair y x) R)->(elem (pair x y) (converse_relation R))))).
Admitted.
Theorem converse_elim : (forall x y R,(((elem (pair x y) (converse_relation R))->(elem (pair y x) R)))).
Admitted.
Theorem converse_iff : (forall x y R,(((elem (pair x y) (converse_relation R))<->(elem (pair y x) R)))).
Admitted.
Theorem converse_is_relation : (forall R,((relation (converse_relation R)))).
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
Theorem converse_union : (forall R S,(((converse_relation (union R S)) = (union (converse_relation R) (converse_relation S))))).
Admitted.
Theorem converse_inter : (forall R S,(((converse_relation (inter R S)) = (inter (converse_relation R) (converse_relation S))))).
Admitted.
Theorem converse_setminus : (forall R S,(((converse_relation (setminus R S)) = (setminus (converse_relation R) (converse_relation S))))).
Admitted.
Definition dom := fun R : set => let MkReplFun := fun w : set => (Eps_i (fun x=>(exists y,((w = (pair x y)))))) in {MkReplFun w|w :e (R)}.
Theorem dom_iff : (forall a R,(((elem a (dom R))<->(exists b,((elem (pair a b) R)))))).
Admitted.
Theorem dom_intro : (forall a b R,(((elem (pair a b) R)->(elem a (dom R))))).
Admitted.
Theorem dom_emptyset : ((dom (emptyset)) = (emptyset)).
Admitted.
Theorem dom_times : (forall A B,((subseteq (dom (times A B)) A))).
Admitted.
Theorem dom_times_inhabited : (forall b B A,(((elem b B)->((dom (times A B)) = A)))).
Admitted.
Theorem dom_cons : (forall a b R,(((dom (cons (pair a b) R)) = (cons a (dom R))))).
Admitted.
Theorem dom_union : (forall A B,(((dom (union A B)) = (union (dom A) (dom B))))).
Admitted.
Theorem dom_inter : (forall A B,((subseteq (dom (inter A B)) (inter (dom A) (dom B))))).
Admitted.
Theorem dom_setminus : (forall A B,((supseteq (dom (setminus A B)) (setminus (dom A) (dom B))))).
Admitted.
Definition ran := fun R : set => let MkReplFun := fun w : set => (Eps_i (fun y=>(exists x,((w = (pair x y)))))) in {MkReplFun w|w :e (R)}.
Theorem ran_iff : (forall b R,(((elem b (ran R))<->(exists a,((elem (pair a b) R)))))).
Admitted.
Theorem ran_intro : (forall a b R,(((elem (pair a b) R)->(elem b (ran R))))).
Admitted.
Theorem ran_emptyset : ((ran (emptyset)) = (emptyset)).
Admitted.
Theorem ran_times : (forall A B,((subseteq (ran (times A B)) B))).
Admitted.
Theorem ran_times_inhabited : (forall a A B,(((elem a A)->((ran (times A B)) = B)))).
Admitted.
Theorem ran_cons : (forall a b R,(((ran (cons (pair a b) R)) = (cons b (ran R))))).
Admitted.
Theorem ran_union : (forall A B,(((ran (union A B)) = (union (ran A) (ran B))))).
Admitted.
Theorem ran_inter : (forall A B,((subseteq (ran (inter A B)) (inter (ran A) (ran B))))).
Admitted.
Theorem ran_setminus : (forall A B,((supseteq (ran (setminus A B)) (setminus (ran A) (ran B))))).
Admitted.
Theorem dom_converse : (forall R,(((dom (converse_relation R)) = (ran R)))).
Admitted.
Theorem ran_converse : (forall R,(((ran (converse_relation R)) = (dom R)))).
Admitted.
Definition fld := fun R : set => (union (dom R) (ran R)).
Theorem fld_iff : (forall c R,(((elem c (fld R))<->(exists d,(((elem (pair c d) R)\/(elem (pair d c) R))))))).
Admitted.
Theorem fld_intro_left : (forall a b R,(((elem (pair a b) R)->(elem a (fld R))))).
Admitted.
Theorem fld_intro_right : (forall a b R,(((elem (pair a b) R)->(elem b (fld R))))).
Admitted.
Theorem dom_subseteq_fld : (forall R,((subseteq (dom R) (fld R)))).
Admitted.
Theorem ran_subseteq_fld : (forall R,((subseteq (ran R) (fld R)))).
Admitted.
Theorem fld_times : (forall A B,((subseteq (fld (times A B)) (union A B)))).
Admitted.
Theorem relation_elem_times_fld : (forall R w,((((relation R)/\(elem w R))->(elem w (times (fld R) (fld R)))))).
Admitted.
Theorem relation_subseteq_times_fld : (forall R,(((relation R)->(subseteq R (times (fld R) (fld R)))))).
Admitted.
Theorem fld_universal : (forall A,(((fld (times A A)) = A))).
Admitted.
Theorem fld_emptyset : ((fld (emptyset)) = (emptyset)).
Admitted.
Theorem fld_cons : (forall a b R,(((fld (cons (pair a b) R)) = (cons a (cons b (fld R)))))).
Admitted.
Theorem fld_union : (forall A B,(((fld (union A B)) = (union (fld A) (fld B))))).
Admitted.
Theorem fld_inter : (forall A B,((subseteq (fld (inter A B)) (inter (fld A) (fld B))))).
Admitted.
Theorem fld_setminus : (forall A B,((supseteq (fld (setminus A B)) (setminus (fld A) (fld B))))).
Admitted.
Theorem fld_converse : (forall R,(((fld (converse_relation R)) = (fld R)))).
Admitted.
Definition img := fun R A : set => {b :e ((ran R))|(exists a,(((elem a A)/\(elem (pair a b) R))))}.
Theorem img_elem_intro : (forall a A b R,((((elem a A)/\(elem (pair a b) R))->(elem b (img R A))))).
Admitted.
Theorem img_iff : (forall b R A,(((elem b (img R A))<->(exists a,(((elem a A)/\(elem (pair a b) R))))))).
Admitted.
Theorem img_subseteq : (forall A B R,(((subseteq A B)->(subseteq (img R A) (img R B))))).
Admitted.
Theorem img_subseteq_ran : (forall R A,((subseteq (img R A) (ran R)))).
Admitted.
Theorem img_dom : (forall R,(((img R (dom R)) = (ran R)))).
Admitted.
Theorem img_union : (forall R A B,(((img R (union A B)) = (union (img R A) (img R B))))).
Admitted.
Theorem img_inter : (forall R A B,((subseteq (img R (inter A B)) (inter (img R A) (img R B))))).
Admitted.
Theorem img_setminus : (forall R A B,((supseteq (img R (setminus A B)) (setminus (img R A) (img R B))))).
Admitted.
Theorem img_singleton_iff : (forall b R a,(((elem b (img R (cons a (emptyset))))<->(elem (pair a b) R)))).
Admitted.
Theorem img_singleton_intro : (forall b R a,(((elem b (img R (cons a (emptyset))))->((elem b (ran R))/\(elem (pair a b) R))))).
Admitted.
Theorem img_singleton : (forall R a,(((img R (cons a (emptyset))) = {b :e ((ran R))|(elem (pair a b) R)}))).
Admitted.
Theorem img_emptyset : (forall R,(((img R (emptyset)) = (emptyset)))).
Admitted.
Definition preimg := fun R B : set => {a :e ((dom R))|(exists b,(((elem b B)/\(elem (pair a b) R))))}.
Theorem preimg_iff : (forall a R B,(((elem a (preimg R B))<->(exists b,(((elem b B)/\(elem (pair a b) R))))))).
Admitted.
Theorem preim_eq_img_of_converse : (forall R B,(((preimg R B) = (img (converse_relation R) B)))).
Admitted.
Theorem preimg_subseteq : (forall A B R,(((subseteq A B)->(subseteq (preimg R A) (preimg R B))))).
Admitted.
Theorem preimg_subseteq_dom : (forall R A,((subseteq (preimg R A) (dom R)))).
Admitted.
Theorem preimg_union : (forall R A B,(((preimg R (union A B)) = (union (preimg R A) (preimg R B))))).
Admitted.
Theorem preimg_inter : (forall R A B,((subseteq (preimg R (inter A B)) (inter (preimg R A) (preimg R B))))).
Admitted.
Theorem preimg_setminus : (forall R A B,((supseteq (preimg R (setminus A B)) (setminus (preimg R A) (preimg R B))))).
Admitted.
Definition upward_closure := fun R a : set => {b :e ((ran R))|(elem (pair a b) R)}.
Definition downward_closure := fun R b : set => {a :e ((dom R))|(elem (pair a b) R)}.
Theorem downward_closure_iff : (forall a R b,(((elem a (downward_closure R b))<->(elem (pair a b) R)))).
Admitted.
Definition circ := fun S R : set => ReplSep2 ((dom R))(fun dummyVar => (ran S))(fun x z => (exists y,(((elem (pair x y) R)/\(elem (pair y z) S)))))(fun x z => (pair x z)).
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
Theorem circ_converse_intro_tuple : (forall a c R S,(((elem (pair a c) (circ (converse_relation R) (converse_relation S)))->(elem (pair a c) (converse_relation (circ S R)))))).
Admitted.
Theorem circ_converse_elim : (forall a c S R,(((elem (pair a c) (converse_relation (circ S R)))->(elem (pair a c) (circ (converse_relation R) (converse_relation S)))))).
Admitted.
Theorem circ_converse : (forall S R,(((converse_relation (circ S R)) = (circ (converse_relation R) (converse_relation S))))).
Admitted.
Definition restrl := fun R X : set => {w :e (R)|(exists x y,(((elem x X)/\(w = (pair x y)))))}.
Theorem restrl_iff : (forall a b R X,(((elem (pair a b) (restrl R X))<->((elem (pair a b) R)/\(elem a X))))).
Admitted.
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
Theorem restrl_ran_elim : (forall X R b,((((subseteq X (dom R))/\(elem b (ran (restrl R X))))->(elem b (img R X))))).
Admitted.
Theorem restrl_ran_intro : (forall X R b,((((subseteq X (dom R))/\(elem b (img R X)))->(elem b (ran (restrl R X)))))).
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
Definition id := fun A : set => ReplSep (A)(fun a => True)(fun a => (pair a a)).
Theorem id_iff : (forall a b A,(((elem (pair a b) (id A))<->((a = b)/\(elem b A))))).
Admitted.
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
Theorem id_img : (forall A B,(((img (id A) B) = (inter A B)))).
Admitted.
Theorem id_elem_rels : (forall A,((elem (id A) (rels A A)))).
Admitted.
Definition memrel := fun A : set => ReplSep2 (A)(fun dummyVar => A)(fun a b => (elem a b))(fun a b => (pair a b)).
Theorem memrel_elem_intro : (forall a A b,(((((elem a A)/\(elem b A))/\(elem a b))->(elem (pair a b) (memrel A))))).
Admitted.
Theorem memrel_elem_inspect : (forall w A,(((elem w (memrel A))->(exists a b,((((elem a A)/\(elem b A))/\((w = (pair a b))/\(elem a b)))))))).
Admitted.
Theorem memrel_is_relation : (forall A,((relation (memrel A)))).
Admitted.
Definition subseteqrel := fun A : set => ReplSep2 (A)(fun dummyVar => A)(fun a b => (subseteq a b))(fun a b => (pair a b)).
Theorem subseteqrel_is_relation : (forall A,((relation (subseteqrel A)))).
Admitted.
Definition injective := fun R: set => (forall a b aprime,((((elem (pair a b) R)/\(elem (pair aprime b) R))->(a = aprime)))).
Definition leftunique := fun x0 : set => (injective x0).
Theorem subseteq_of_injective_is_injective : (forall S R,((((subseteq S R)/\(injective R))->(injective S)))).
Admitted.
Theorem restrl_injective : (forall R A,(((injective R)->(injective (restrl R A))))).
Admitted.
Theorem circ_injective : (forall R S,((((injective R)/\(injective S))->(injective (circ S R))))).
Admitted.
Theorem identity_injective : (forall A,((injective (id A)))).
Admitted.
Definition rightunique := fun R: set => (forall a b bprime,((((elem (pair a b) R)/\(elem (pair a bprime) R))->(b = bprime)))).
Definition onetoone := fun x0 : set => ((rightunique x0)/\(injective x0)).
Theorem subseteq_of_rightunique_is_rightunique : (forall S R,((((subseteq S R)/\(rightunique R))->(rightunique S)))).
Admitted.
Theorem circ_rightunique : (forall R S,((((rightunique R)/\(rightunique S))->(rightunique (circ S R))))).
Admitted.
Definition lefttotal := fun R A: set => (forall a,(((elem a A)->(exists b,((elem (pair a b) R)))))).
Definition righttotal := fun R B: set => (forall b,(((elem b B)->(exists a,((elem (pair a b) R)))))).
Definition surjective := fun x0 x1 : set => (righttotal x0 x1).
Definition inductive_set := fun x0 : set => ((elem (emptyset) x0)/\(forall a,(((elem a x0)->(elem (suc a) x0))))).
Definition transitiveset := fun A: set => (forall x y,((((elem x y)/\(elem y A))->(elem x A)))).
Theorem transitiveset_iff_subseteq : (forall A,(((transitiveset A)<->(forall a,(((elem a A)->(subseteq a A))))))).
Admitted.
Theorem transitiveset_iff_pow : (forall A,(((transitiveset A)<->(subseteq A (pow A))))).
Admitted.
Theorem transitiveset_iff_unions_suc : (forall A,(((transitiveset A)<->((unions (suc A)) = A)))).
Admitted.
Theorem transitiveset_iff_unions_subseteq : (forall A,(((transitiveset A)<->(subseteq (unions A) A)))).
Admitted.
Theorem transitiveset_upair : (forall A a b,((((transitiveset A)/\(elem (cons a (cons b (emptyset))) A))->((elem a A)/\(elem b A))))).
Admitted.
Theorem emptyset_transitiveset : (transitiveset (emptyset)).
Admitted.
Theorem union_of_transitiveset_is_transitiveset : (forall A B,((((transitiveset A)/\(transitiveset B))->(transitiveset (union A B))))).
Admitted.
Theorem inter_of_transitiveset_is_transitiveset : (forall A B,((((transitiveset A)/\(transitiveset B))->(transitiveset (inter A B))))).
Admitted.
Theorem suc_of_transitiveset_is_transitiveset : (forall A,(((transitiveset A)->(transitiveset (suc A))))).
Admitted.
Theorem unions_of_transitiveset_is_transitiveset : (forall A,(((transitiveset A)->(transitiveset (unions A))))).
Admitted.
Theorem unions_family_of_transitiveset_is_transitiveset : (forall A,(((forall x3,(((elem x3 A)->(transitiveset x3))))->(transitiveset (unions A))))).
Admitted.
Theorem inters_family_of_transitiveset_is_transitiveset : (forall A,(((forall x4,(((elem x4 A)->(transitiveset x4))))->(transitiveset (inters A))))).
Admitted.
Definition ordinal := fun alpha: set => ((transitiveset alpha)/\(forall x5,(((elem x5 alpha)->(transitiveset x5))))).
Theorem ordinal_intro : (forall alpha,((((transitiveset alpha)/\(forall x6,(((elem x6 alpha)->(transitiveset x6)))))->(ordinal alpha)))).
Admitted.
Theorem ordinal_is_transitiveset : (forall alpha,(((ordinal alpha)->(transitiveset alpha)))).
Admitted.
Theorem ordinal_elem_is_transitiveset : (forall alpha A,((((ordinal alpha)/\(elem A alpha))->(transitiveset A)))).
Admitted.
Theorem elem_of_ordinal_is_ordinal : (forall alpha beta,((((ordinal alpha)/\(elem beta alpha))->(ordinal beta)))).
Admitted.
Theorem suc_ordinal_implies_ordinal : (forall alpha,(((ordinal (suc alpha))->(ordinal alpha)))).
Admitted.
Theorem transitivesubseteq_of_ordinal_is_ordinal : (forall alpha beta,(((((ordinal alpha)/\(subseteq beta alpha))/\(transitiveset beta))->(ordinal beta)))).
Admitted.
Theorem ordinal_elem_implies_subseteq : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(elem alpha beta))->(subseteq alpha beta)))).
Admitted.
Theorem ordinal_transitivity : (forall alpha gamma beta,((((ordinal alpha)/\((elem gamma beta)/\(elem beta alpha)))->(elem gamma alpha)))).
Admitted.
Theorem ordinal_suc_subseteq : (forall beta alpha,((((ordinal beta)/\(elem alpha beta))->(subseteq (suc alpha) beta)))).
Admitted.
Definition ordinal_prec := fun x0 x1 : set => ((ordinal x1)/\(elem x0 x1)).
Definition ordinal_preceq := fun x0 x1 : set => ((ordinal x1)/\(subseteq x0 x1)).
Theorem prec_is_ordinal : (forall alpha beta,(((ordinal_prec alpha beta)->(ordinal alpha)))).
Admitted.
Theorem ordinal_elem_connex : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->(((elem alpha beta)\/(elem beta alpha))\/(alpha = beta))))).
Admitted.
Theorem ordinal_proper_subset_implies_elem : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(subset alpha beta))->(elem alpha beta)))).
Admitted.
Theorem ordinal_elem_implies_proper_subset : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(elem alpha beta))->(subset alpha beta)))).
Admitted.
Theorem ordinal_preceq_implies_subseteq : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(ordinal_preceq alpha beta))->(subseteq alpha beta)))).
Admitted.
Theorem ordinal_elem_or_subseteq : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->((elem alpha beta)\/(subseteq beta alpha))))).
Admitted.
Theorem ordinal_subseteq_or_subseteq : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->((subseteq alpha beta)\/(subseteq beta alpha))))).
Admitted.
Theorem ordinal_subseteq_implies_elem_or_eq : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(subseteq alpha beta))->((elem alpha beta)\/(alpha = beta))))).
Admitted.
Theorem ordinal_subset_trichotomy : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->(((subset alpha beta)\/(subset beta alpha))\/(alpha = beta))))).
Admitted.
Theorem ordinal_nor_elem_implies_eq : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(nor(elem alpha beta) (elem beta alpha)))->(alpha = beta)))).
Admitted.
Theorem ordinal_in_trichotomy : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->(((elem alpha beta)\/(elem beta alpha))\/(alpha = beta))))).
Admitted.
Theorem ordinal_prec_trichotomy : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(nor(ordinal_prec alpha beta) (ordinal_prec beta alpha)))->(alpha = beta)))).
Admitted.
Theorem ordinal_elem_or_superset : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->((elem alpha beta)\/(subseteq beta alpha))))).
Admitted.
Theorem emptyset_is_ordinal : (ordinal (emptyset)).
Admitted.
Theorem suc_ordinal : (forall alpha,(((ordinal alpha)->(ordinal (suc alpha))))).
Admitted.
Theorem ordinal_iff_suc_ordinal : (forall alpha,(((ordinal alpha)<->(ordinal (suc alpha))))).
Admitted.
Theorem ordinal_in_suc : (forall alpha,(((ordinal alpha)->(elem alpha (suc alpha))))).
Admitted.
Theorem ordinal_precedes_suc : (forall alpha,(((ordinal alpha)->(ordinal_prec alpha (suc alpha))))).
Admitted.
Theorem ordinal_elem_implies_subset_of_suc : (forall alpha beta,(((((ordinal alpha)/\(ordinal beta))/\(elem alpha beta))->(subseteq alpha (suc beta))))).
Admitted.
Theorem unions_of_ordinal_is_ordinal : (forall alpha,(((ordinal alpha)->(ordinal (unions alpha))))).
Admitted.
Theorem ordinal_subseteq_unions : (forall alpha,(((ordinal alpha)->(subseteq (unions alpha) alpha)))).
Admitted.
Theorem union_of_two_ordinals_is_ordinal : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->(ordinal (union alpha beta))))).
Admitted.
Theorem ordinal_empty_or_emptyset_elem : (forall alpha,(((ordinal alpha)->((alpha = (emptyset))\/(elem (emptyset) alpha))))).
Admitted.
Theorem transitive_set_of_ordinals_is_ordinal : (forall A,((((forall alpha,(((elem alpha A)->(ordinal alpha))))/\(transitiveset A))->(ordinal A)))).
Admitted.
Theorem buraliforti_antinomy : ~((exists Omega,((forall alpha,(((elem alpha Omega)<->(ordinal alpha))))))).
Admitted.
Theorem inters_of_ordinals_is_ordinal : (forall A,((((inhabited A)/\(forall alpha,(((elem alpha A)->(ordinal alpha)))))->(ordinal (inters A))))).
Admitted.
Theorem inters_of_ordinals_subseteq : (forall A,((((inhabited A)/\(forall alpha,(((elem alpha A)->(ordinal alpha)))))->(forall alpha,(((elem alpha A)->(subseteq (inters A) alpha))))))).
Admitted.
Theorem inters_of_ordinals_elem : (forall A,((((inhabited A)/\(forall alpha,(((elem alpha A)->(ordinal alpha)))))->(elem (inters A) A)))).
Admitted.
Theorem inters_of_ordinals_is_minimal : (forall A,((((inhabited A)/\(forall alpha,(((elem alpha A)->(ordinal alpha)))))->(elemminimal (inters A) A)))).
Admitted.
Theorem inters_of_ordinals_is_minimal_alternate : (forall A,((((inhabited A)/\(forall alpha,(((elem alpha A)->(ordinal alpha)))))->(forall alpha,(((elem alpha A)->(((inters A) = alpha)\/(elem (inters A) alpha)))))))).
Admitted.
Theorem inter_of_two_ordinals_is_ordinal : (forall alpha beta,((((ordinal alpha)/\(ordinal beta))->(ordinal (inter alpha beta))))).
Admitted.
Definition limit_ordinal := fun lambda: set => ((ordinal_prec (emptyset) lambda)/\(forall alpha,(((elem alpha lambda)->(elem (suc alpha) lambda))))).
Definition successor_ordinal := fun alpha: set => (exists beta,(((ordinal beta)/\(alpha = (suc beta))))).
Theorem positive_ordinal_is_limit_or_successor : (forall alpha,((((ordinal_prec (emptyset) alpha)/\(ordinal alpha))->((limit_ordinal alpha)\/(successor_ordinal alpha))))).
Admitted.
Theorem zero_not_successorordinal : ~((successor_ordinal (emptyset))).
Admitted.
Theorem zero_not_limitordinal : ~((limit_ordinal (emptyset))).
Admitted.
Theorem suc_elem_limitordinal : (forall lambda alpha,((((limit_ordinal lambda)/\(elem alpha lambda))->(elem (suc alpha) lambda)))).
Admitted.
Theorem limitordinal_eq_unions : (forall lambda,(((limit_ordinal lambda)->((unions lambda) = lambda)))).
Admitted.
Definition function := fun x0 : set => ((rightunique x0)/\(relation x0)).
Definition appl := fun f x : set => (unions (img f (cons x (emptyset)))).
Theorem function_rightunique : (forall f a b bprime,((((function f)/\((elem (pair a b) f)/\(elem (pair a bprime) f)))->(b = bprime)))).
Admitted.
Theorem function_appl_intro : (forall f a b,((((function f)/\(elem (pair a b) f))->((appl f a) = b)))).
Admitted.
Theorem function_member_elim : (forall f w,((((function f)/\(elem w f))->(exists x,(((elem x (dom f))/\(w = (pair x (appl f x))))))))).
Admitted.
Theorem function_appl_elim : (forall f x,((((function f)/\(elem x (dom f)))->(elem (pair x (appl f x)) f)))).
Admitted.
Theorem function_appl_iff : (forall f a b,(((function f)->((elem (pair a b) f)<->((elem a (dom f))/\((appl f a) = b)))))).
Admitted.
Theorem fun_subseteq : (forall f g,((((((function f)/\(function g))/\(subseteq (dom f) (dom g)))/\(forall x,(((elem x (dom f))->((appl f x) = (appl g x))))))->(subseteq f g)))).
Admitted.
Theorem funext : (forall f g,((((((function f)/\(function g))/\((dom f) = (dom g)))/\(forall x,(((appl f x) = (appl g x)))))->(f = g)))).
Admitted.
Definition function_on := fun x0 x1 : set => ((function x0)/\(x1 = (dom x0))).
Definition function_to := fun x0 x1 : set => ((function x0)/\(forall x,(((elem x (dom x0))->(elem (appl x0 x) x1))))).
Definition function_from_to := fun x0 x1 x2 : set => ((function_to x0 x2)/\((dom x0) = x1)).
Theorem function_on_weaken_codom : (forall f B C,((((function_to f B)/\(subseteq B C))->(function_to f C)))).
Admitted.
Theorem function_to_ran : (forall f B,(((function_to f B)->(subseteq (ran f) B)))).
Admitted.
Theorem function_from_to_weaken_codom : (forall f A B C,((((function_from_to f A B)/\(subseteq B C))->(function_from_to f A C)))).
Admitted.
Definition funs := fun A B : set => {f :e ((rels A B))|((subseteq A (dom f))/\(rightunique f))}.
Theorem funs_subseteq_rels : (forall A B,((subseteq (funs A B) (rels A B)))).
Admitted.
Theorem funs_intro : (forall f A B,(((function_from_to f A B)->(elem f (funs A B))))).
Admitted.
Theorem funs_weaken_codom : (forall f A B D,((((elem f (funs A B))/\(subseteq B D))->(elem f (funs A D))))).
Admitted.
Theorem img_of_function_intro : (forall f x X,((((function f)/\(elem x (inter (dom f) X)))->(elem (appl f x) (img f X))))).
Admitted.
Theorem img_of_function_elim : (forall f y X,((((function f)/\(elem y (img f X)))->(exists x,(((elem x (inter (dom f) X))/\(y = (appl f x)))))))).
Admitted.
Theorem img_of_function : (forall f X,(((function f)->((img f X) = ReplSep ((inter (dom f) X))(fun x => True)(fun x => (appl f x)))))).
Admitted.
Definition family_of_functions := fun x0 : set => (forall x11,(((elem x11 x0)->(function x11)))).
Theorem unions_of_compatible_family_of_function_is_function : (forall F,((((family_of_functions F)/\(forall f g,((((elem f F)/\(elem g F))->((subseteq f g)\/(subseteq g f))))))->(function (unions F))))).
Admitted.
Theorem emptyset_is_function : (function (emptyset)).
Admitted.
Theorem emptyset_is_function_on_emptyset : (function_on (emptyset) (emptyset)).
Admitted.
Theorem codom_of_emptyset_can_be_anything : (forall X,((function_to (emptyset) X))).
Admitted.
Theorem emptyset_is_injective : (injective (emptyset)).
Admitted.
Definition composable := fun x0 x1 : set => (subseteq (ran x1) (dom x0)).
Theorem function_circ : (forall f g,((((rightunique f)/\(rightunique g))->(function (circ g f))))).
Admitted.
Theorem circ_appl : (forall f g x,((((((function f)/\(function g))/\(composable g f))/\(elem x (dom f)))->((appl (circ g f) x) = (appl g (appl f x)))))).
Admitted.
Theorem dom_of_circ : (forall f g,(((((function f)/\(function g))/\(composable g f))->((dom (circ g f)) = (preimg f (dom g)))))).
Admitted.
Theorem dom_circ_exact : (forall f g,(((((function f)/\(function g))/\((ran f) = (dom g)))->((dom (circ g f)) = (dom f))))).
Admitted.
Theorem ran_of_circ_intro : (forall f g y,((((((function f)/\(function g))/\(composable g f))/\(elem y (img g (ran f))))->(elem y (ran (circ g f)))))).
Admitted.
Theorem ran_of_circ_elim : (forall f g y,((((((function f)/\(function g))/\(composable g f))/\(elem y (ran (circ g f))))->(elem y (img g (ran f)))))).
Admitted.
Theorem ran_of_circ : (forall f g,(((((function f)/\(function g))/\(composable g f))->((ran (circ g f)) = (img g (ran f)))))).
Admitted.
Theorem ran_circ_exact : (forall f g,(((((function f)/\(function g))/\((ran f) = (dom g)))->((ran (circ g f)) = (ran g))))).
Admitted.
Theorem img_of_circ_elim : (forall f g c A,((((((function f)/\(function g))/\(subseteq (ran f) (dom g)))/\(elem c (img (circ g f) A)))->(elem c (img g (img f A)))))).
Admitted.
Theorem img_of_circ : (forall f g A,(((((function f)/\(function g))/\(subseteq (ran f) (dom g)))->((img (circ g f) A) = (img g (img f A)))))).
Admitted.
Theorem restrl_of_function_is_function : (forall f A,(((function f)->(function (restrl f A))))).
Admitted.
Theorem restrl_of_function_appl : (forall f A a,(((((function f)/\(subseteq A (dom f)))/\(elem a A))->((appl (restrl f A) a) = (appl f a))))).
Admitted.
Theorem function_appl_default : (forall x f,(((notelem x (dom f))->((appl f x) = (emptyset))))).
Admitted.
Theorem injective_function : (forall f,(((function f)->((injective f)<->(forall x y,((((elem x (dom f))/\(elem y (dom f)))->(((appl f x) = (appl f y))->(x = y))))))))).
Admitted.
Definition injection := fun x0 : set => ((function x0)/\(injective x0)).
Definition surjects := fun f Y: set => (Y = ReplSep ((dom f))(fun x => True)(fun x => (appl f x))).
Theorem surjects_img : (forall f,((surjects f (img f (dom f))))).
Admitted.
Theorem surjects_implies_img : (forall f Y,(((surjects f Y)->(Y = (img f (dom f)))))).
Admitted.
Theorem surjects_implies_ran_eq : (forall f Y,((((function f)/\(surjects f Y))->((ran f) = Y)))).
Admitted.
Theorem ran_eq_implies_surjects : (forall f Y,((((function f)/\((ran f) = Y))->(surjects f Y)))).
Admitted.
Theorem surjects_iff_ran_eq : (forall f Y,(((function f)->((surjects f Y)<->((ran f) = Y))))).
Admitted.
Definition bijection := fun f X Y: set => (((dom f) = X)/\((surjects f Y)/\(injection f))).
Theorem bijection_circ : (forall f A B g C,((((bijection f A B)/\(bijection g B C))->(bijection (circ g f) A C)))).
Admitted.
Theorem converse_of_function_is_injective : (forall f,(((function f)->(injective (converse_relation f))))).
Admitted.
Theorem injective_converse_is_function : (forall f,(((injective f)->(function (converse_relation f))))).
Admitted.
Theorem bijective_converse_is_function : (forall f A B,(((bijection f A B)->(function (converse_relation f))))).
Admitted.
Theorem bijection_converse_is_bijection : (forall f A B,(((bijection f A B)->(bijection (converse_relation f) B A)))).
Admitted.
Definition leftinverse := fun x0 x1 : set => (forall x,(((elem x (dom x1))->((appl x0 (appl x1 x)) = x)))).
Definition rightinverse := fun x0 x1 : set => ((circ x1 x0) = (id (dom x0))).
Definition rightinverseon := fun x0 x1 x2 : set => ((circ x1 x0) = (id x2)).
Theorem injective_converse_is_leftinverse : (forall f,(((injection f)->(leftinverse (converse_relation f) f)))).
Admitted.
Theorem id_rightunique : (forall A,((rightunique (id A)))).
Admitted.
Theorem id_is_function : (forall A,((function (id A)))).
Admitted.
Theorem id_is_function_on : (forall A,((function_on (id A) A))).
Admitted.
Theorem id_is_function_to : (forall A,((function_to (id A) A))).
Admitted.
Theorem id_is_function_to_form : (forall A,((function_from_to (id A) A A))).
Admitted.
Theorem id_elem_funs : (forall A,((elem (id A) (funs A A)))).
Admitted.
Theorem id_appl : (forall a A f,((((elem a A)/\(f = (id A)))->((appl f a) = a)))).
Admitted.
Theorem id_is_bijection : (forall A,((bijection (id A) A A))).
Admitted.
