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
