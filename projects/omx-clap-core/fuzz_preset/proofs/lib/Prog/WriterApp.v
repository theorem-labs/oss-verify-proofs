From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec.
Import ListNotations.
Open Scope Z_scope.

Record wst : Type := mkW {
  w_failed : Z;
  w_text : list Z;
  w_cap : Z;
  w_cnt : Z;
  w_fail : Z;
  w_calls : list Z
}.

Definition put1 (st : wst) (b : list Z) : wst :=
  if negb (w_failed st =? 0) then st
  else
    let need := Z.of_nat (length (w_text st)) + Z.of_nat (length b) + 1 in
    if need <=? w_cap st then mkW 0 (w_text st ++ b) (w_cap st) (w_cnt st) (w_fail st) (w_calls st)
    else
      let c' := newcap (w_cap st) need in
      if w_cnt st =? w_fail st then
        mkW 1 (w_text st) (w_cap st) ((w_cnt st + 1) mod 2 ^ 64) (2 ^ 64 - 1) (w_calls st ++ [c'])
      else
        mkW 0 (w_text st ++ b) c' ((w_cnt st + 1) mod 2 ^ 64) (w_fail st) (w_calls st ++ [c']).

Definition putN (st : wst) (P : list (list Z)) : wst := fold_left put1 P st.

Definition w0 (cnt fail : Z) : wst := mkW 0 [] 0 cnt fail [].

Lemma putN_app : forall st P Q, putN st (P ++ Q) = putN (putN st P) Q.
Proof. intros. unfold putN. apply fold_left_app. Qed.

Lemma putN_nil : forall st, putN st [] = st.
Proof. reflexivity. Qed.

Lemma putN_cons : forall st b P, putN st (b :: P) = putN (put1 st b) P.
Proof. reflexivity. Qed.

Lemma putN_failed : forall P st, w_failed st <> 0 -> putN st P = st.
Proof.
  induction P as [|b P IH]; intros st H; [reflexivity|].
  rewrite putN_cons. unfold put1. destruct (w_failed st =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  cbn. apply IH. exact H.
Qed.
