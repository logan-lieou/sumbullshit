Inductive N : Set :=
  | zero : N
  | succ : N -> N.

Fixpoint plus (m n : N) :=
  match m with
    | zero => n
    | succ m' => succ (plus m' n)
  end.

Lemma plus_succ: forall m n, succ (plus n m) = plus n (succ m).
Proof.
  intros.
  induction n.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.

Lemma plus_n_zero: forall n, n = plus n zero.
Proof.
  induction n.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.

Theorem plus_comm: forall m n, plus m n = plus n m.
Proof.
  intros.
  induction m.
  simpl.
  apply plus_n_zero.
  simpl.
  rewrite IHm.
  apply plus_succ.
Qed.

Print plus_comm.
