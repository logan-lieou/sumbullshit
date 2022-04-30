Definition lem := forall p, p \/ ~p.
Print lem.

Definition f := forall (A: Set) (p: A -> Prop) (q: Prop),
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).

Theorem lem_to_f : lem -> f.

Proof.
  unfold f, lem.
  firstorder.
  assert (G := H q).
  destruct (H q); firstorder.

  (* firstorder logic
  left.
  assumption.
  right.
  intro.
  destruct (H0 x).
  elim H1.
  assumption.
  assumption.
   *)
Qed.

Print lem_to_f.
