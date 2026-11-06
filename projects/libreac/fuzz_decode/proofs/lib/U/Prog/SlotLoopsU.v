From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Definition FILL : byte := Z_to_bv 8 0xa5.

Lemma nth_repeat_lt : forall (b d : byte) n i, (i < n)%nat -> nth i (repeat b n) d = b.
Proof. intros b d n. induction n as [|n IH]; intros i H; [lia|]. destruct i; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma rd_fill : forall m out n i, bytes_at rsegs m out (repeat FILL (Z.to_nat n)) -> 0 <= i < n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (out + i)) 1 = Some [FILL].
Proof.
  intros m out n i H Hi. rewrite (rd1 _ _ _ i H) by (rewrite repeat_length; lia).
  rewrite nth_repeat_lt by lia. reflexivity.
Qed.

Ltac closed_vals :=
  repeat match goal with |- context [Z_to_bv 64 ?e] =>
    lazymatch e with context [v_sltu] => let v := eval vm_compute in e in change e with v end end.

Section Loops.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
  x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (out n : Z).
Hypothesis HF : bytes_at rsegs m out (repeat FILL (Z.to_nat n)).
Hypothesis Hn : 1 <= n.
Hypothesis Hout : 0 <= out.
Hypothesis HoutN : out + n < 2^64.

Lemma chk_u1 :
  x20 = Z_to_bv 64 out -> x21 = Z_to_bv 64 n ->
  (forall y12 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 n) y12 x13 x14 x15
     x16 x17 x18 x19 (Z_to_bv 64 out) (Z_to_bv 64 n) (Z_to_bv 64 (18446744073709551615 - out)) x23 x24 x25 x26 x27
     x28 x29 x30 x31) F (Z_to_bv 64 0x1339c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
     x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1336c) fc None m (seg_rom rsegs)).
Proof.
  intros E1 E2 CONT. subst x20 x21.
  assert (L : forall (K : nat) (i : Z) (y11 y12 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y11 = i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) y11 y12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 out) (Z_to_bv 64 n) (Z_to_bv 64 (18446744073709551615 - out)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x13378) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y11 y12 HK Hi HP. apply wv in HP. subst y11.
    pose proof (rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. cnd false.
    step. step. step. step. step. step. step.
    closed_vals.
    brq BR.
    - step. cnd false. replace (i + 1) with n by lia. apply CONT.
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  step. step. step. usub. rewrite ?zb_lxor_ones by lia.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

Lemma chk_u2 :
  x20 = Z_to_bv 64 out -> x21 = Z_to_bv 64 n -> x22 = Z_to_bv 64 (18446744073709551615 - out) ->
  (forall y13 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 n) y13 x14 x15
     x16 x17 x18 x19 (Z_to_bv 64 out) (Z_to_bv 64 n) (Z_to_bv 64 (18446744073709551615 - out)) x23 x24 x25 x26 x27
     x28 x29 x30 x31) F (Z_to_bv 64 0x13450) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
     x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13424) fc None m (seg_rom rsegs)).
Proof.
  intros E1 E2 E3 CONT. subst x20 x21 x22.
  assert (L : forall (K : nat) (i : Z) (y12 y13 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y12 = i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) y12 y13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 out) (Z_to_bv 64 n) (Z_to_bv 64 (18446744073709551615 - out)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x1342c) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y12 y13 HK Hi HP. apply wv in HP. subst y12.
    pose proof (rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. cnd false.
    step. step. step. step. step. step. step.
    closed_vals.
    brq BR.
    - step. cnd false. replace (i + 1) with n by lia. apply CONT.
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  step. step.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

End Loops.
