From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcKind RcRec RcParse.
Import ListNotations.
Open Scope Z_scope.

Definition ir_s (g : list byte) : Z := cp_v g 26.

Definition ir_blk (g : list byte) : list byte := skipn 18 g.

Definition ir_rec (g : list byte) : list byte := firstn (Z.to_nat (ir_s g - 8)) (skipn 34 g).

Definition ir (len : Z) (g : list byte) : bool :=
  (fst (ctrlparse len g) =? 5) && (cp_v g 34 * 256 + cp_v g 35 =? 0x500) &&
  (cp_v g 32 =? 0x12) && (cp_v g 33 =? 0x12) && (14 <=? ir_s g) && (ir_s g <=? 23) &&
  (cp_v g 27 =? 0xf0) && (cp_v g (Z.to_nat (26 + ir_s g)) =? 0xf7) &&
  (blocksum (ir_blk g) =? 0) && (recsum (ir_rec g) =? 0).

Definition reply_args (fr pa pp pn : Z) : bool :=
  negb (fr =? 0) && negb (pa =? 0) && negb (pp =? 0) && negb (pn =? 0).

Definition reply_ok (fr len pa pp pn : Z) (g : list byte) : bool := reply_args fr pa pp pn && ir len g.

Definition reply_ret (fr len pa pp pn : Z) (g : list byte) : Z :=
  if reply_args fr pa pp pn then (if ir len g then 1 else 0) else -1.

Lemma cp_v_range' : forall g i, 0 <= cp_v g i < 256.
Proof.
  intros g i. unfold cp_v. pose proof (bv_unsigned_in_range 8 (cp_b g i)) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Definition reply_addr (g : list byte) : list byte := [cp_b g 37; cp_b g 36].

Lemma ir_true : forall len g, ir len g = true ->
  fst (ctrlparse len g) = 5 /\ cp_v g 34 * 256 + cp_v g 35 = 0x500 /\ cp_v g 32 = 0x12 /\ cp_v g 33 = 0x12 /\
  14 <= ir_s g <= 23 /\ cp_v g 27 = 0xf0 /\ cp_v g (Z.to_nat (26 + ir_s g)) = 0xf7 /\
  blocksum (ir_blk g) = 0 /\ recsum (ir_rec g) = 0.
Proof.
  intros len g H. unfold ir in H. rewrite !andb_true_iff, !Z.eqb_eq, !Z.leb_le in H. tauto.
Qed.

Lemma ir_bytes : forall len g, ir len g = true ->
  50 <= len /\ cp_v g 12 = 0x88 /\ cp_v g 13 = 0x19 /\ cp_v g 16 = 0xcd /\ cp_v g 17 = 0xea /\
  cp_v g 18 = 4 /\ cp_v g 19 = 3 /\ cp_v g 32 = 0x12 /\ cp_v g 33 = 0x12 /\ cp_v g 34 = 5 /\ cp_v g 35 = 0 /\
  14 <= ir_s g <= 23 /\ cp_v g 27 = 0xf0 /\ cp_v g (Z.to_nat (26 + ir_s g)) = 0xf7 /\
  blocksum (ir_blk g) = 0 /\ recsum (ir_rec g) = 0.
Proof.
  intros len g H. apply ir_true in H. destruct H as (K & T & H32 & H33 & Hs & H27 & Hf7 & Hb & Hr).
  destruct (ctrlparse_rec len g ltac:(lia)) as (HD & RC & _).
  apply cp_hdr_spec in HD. unfold cp_rec, cp_type in RC. rewrite !andb_true_iff, !Z.eqb_eq in RC.
  pose proof (cp_v_range' g 34) as R34. pose proof (cp_v_range' g 35) as R35.
  repeat split; lia.
Qed.

Lemma reply_ret_cases : forall fr len pa pp pn g,
  (reply_args fr pa pp pn = false /\ reply_ret fr len pa pp pn g = -1) \/
  (reply_ok fr len pa pp pn g = true /\ reply_ret fr len pa pp pn g = 1) \/
  (reply_args fr pa pp pn = true /\ ir len g = false /\ reply_ret fr len pa pp pn g = 0).
Proof.
  intros. unfold reply_ok, reply_ret. destruct (reply_args fr pa pp pn), (ir len g); cbn [andb]; tauto.
Qed.
