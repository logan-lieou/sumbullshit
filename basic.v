(* in order to prove something we define some Theorem or Lemma *)
Theorem f (A : Set) (p : A -> Prop) (q: Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).

(* if something can be proven with firstorder logic then just use firstorder *)
Proof.
  firstorder.
Qed.

Print f.
(* OUTPUT:
  f =
  fun (A : Set) (p : A -> Prop) (q : Prop) =>
  conj
    (fun H : exists x : A, q /\ p x =>
    ex_ind
      (fun (x : A) (H0 : q /\ p x) =>
        and_ind
          (fun (H1 : q) (H2 : p x) =>
          conj H1 (ex_intro (fun x0 : A => p x0) x H2)) H0) H)
    (fun H : q /\ (exists x : A, p x) =>
    and_ind
      (fun (H0 : q) (H1 : exists x : A, p x) =>
        ex_ind
          (fun (x : A) (H2 : p x) =>
          ex_intro (fun x0 : A => q /\ p x0) x (conj H0 H2)) H1) H)
      : forall (A : Set) (p : A -> Prop) (q : Prop),
        (exists x : A, q /\ p x) <-> q /\ (exists x : A, p x)
*)

(* MANUAL PROOF
Proof.
  (* prove in both directions *)
  (* split into two subgoals *)
  split.
  (*
    A : Set
    p : A -> Prop
    q : Prop
    ============================
    (exists x : A, q /\ p x) -> q /\ (exists x : A, p x)

    subgoal 2 (ID 9) is:
    q /\ (exists x : A, p x) -> exists x : A, q /\ p x
  *)
  intros [x [H1 H2]].
  split.
  assumption.
  exists x.
  assumption.
  (*
    A : Set
    p : A -> Prop
    q : Prop
    ============================
    q /\ (exists x : A, p x) -> exists x : A, q /\ p x
  *)
  intros [H1 [y H2]].
  exists y.
  (*
    A : Set
    p : A -> Prop
    q : Prop
    H1 : q
    y : A
    H2 : p y
    ============================
    q /\ p y
  *)
  auto.
Qed.

Check f.
Print f.
*)
