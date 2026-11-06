From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib.
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

Lemma chg_down1 :
  x19 = Z_to_bv 64 out -> x22 = Z_to_bv 64 n ->
  (forall y14 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 (out + n))
     (Z_to_bv 64 (out + n)) y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 0x12fb0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
     x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12f88) fc None m (seg_rom rsegs)).
Proof.
  intros E19 E22 CONT. subst x19 x22.
  assert (L : forall (K : nat) (i : Z) (y13 y14 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y13 = out + i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 (out + n)) y13
      y14 x15 x16 x17 x18 (Z_to_bv 64 out) x20 x21 (Z_to_bv 64 n) x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x12f94) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y13 y14 HK Hi H13. apply wv in H13. subst y13.
    pose proof (rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. step. step. step. step. step.
    closed_vals.
    brq BR.
    - step. brq B2; [replace (out + i + 1) with (out + n) by lia; apply CONT | lia].
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  step. step. step. try rewrite !unsigned_lit by lia.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

Lemma chg_down2 :
  x19 = Z_to_bv 64 out -> x22 = Z_to_bv 64 n ->
  (forall y13 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 (out + n)) y13 x14 x15 x16 x17 x18 (Z_to_bv 64 out) x20 x21 (Z_to_bv 64 (out + n)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 0x13048) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13020) fc None m (seg_rom rsegs)).
Proof.
  intros E1 E2 CONT. subst x19 x22.
  assert (L : forall (K : nat) (i : Z) (y12 y13 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y12 = out + i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 out) x20 x21 (Z_to_bv 64 (out + n)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x1302c) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y12 y13 HK Hi HP. apply wv in HP. subst y12.
    pose proof (rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. step. step. step. step. step.
    closed_vals.
    brq BR.
    - step. brq B2; [replace (out + i + 1) with (out + n) by lia; apply CONT | lia].
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  step. step. step. try rewrite !unsigned_lit by lia.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

Lemma chg_up3 :
  x20 = Z_to_bv 64 out -> x21 = Z_to_bv 64 n ->
  (forall y12 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 (out + n)) y12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 out) (Z_to_bv 64 (out + n)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 0x131f8) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x131d0) fc None m (seg_rom rsegs)).
Proof.
  intros E1 E2 CONT. subst x20 x21.
  assert (L : forall (K : nat) (i : Z) (y11 y12 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y11 = out + i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) y11 y12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 out) (Z_to_bv 64 (out + n)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x131dc) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y11 y12 HK Hi HP. apply wv in HP. subst y11.
    pose proof (rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. step. step. step. step. step.
    closed_vals.
    brq BR.
    - step. brq B2; [replace (out + i + 1) with (out + n) by lia; apply CONT | lia].
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  step. step. step. try rewrite !unsigned_lit by lia.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

Lemma chg_up4 :
  x20 = Z_to_bv 64 out -> x21 = Z_to_bv 64 (out + n) ->
  (forall y13 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 (out + n)) y13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 out) (Z_to_bv 64 (out + n)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 0x13278) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13254) fc None m (seg_rom rsegs)).
Proof.
  intros E1 E2 CONT. subst x20 x21.
  assert (L : forall (K : nat) (i : Z) (y12 y13 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y12 = out + i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) y12 y13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 out) (Z_to_bv 64 (out + n)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x1325c) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y12 y13 HK Hi HP. apply wv in HP. subst y12.
    pose proof (rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. step. step. step. step. step.
    closed_vals.
    brq BR.
    - step. brq B2; [replace (out + i + 1) with (out + n) by lia; apply CONT | lia].
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  step. step. try rewrite !unsigned_lit by lia.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

End Loops.

Definition fd_olen (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) then 3 * nch * ns else 1.
Definition fd_fits (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) && (nch * ns <? 481) then 1 else 0.

Ltac vsimp :=
  unfold v_sltiu in *;
  repeat first
    [ progress (change (bv_wrap 64 481) with 481)
    | progress (change (bv_wrap 64 1) with 1)
    | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
        lazymatch e with context [bv_unsigned _] => fail | context [if _ then _ else _] => fail
        | _ => rewrite (unsigned_lit e) by nia end end
    | rewrite Z.shiftl_mul_pow2 by lia
    | match goal with |- context [?a <? ?b] =>
        first [ rewrite (proj2 (Z.ltb_lt a b)) by nia | rewrite (proj2 (Z.ltb_ge a b)) by nia ] end
    | progress cbn iota ];
  try nia;
  try (rewrite Z.mul_comm; reflexivity);
  try (match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; cbn iota; vm_compute; lia).

Section DA.
Variables (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
  x29 x30 x31 sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (mode nch ns : Z) (junk : list byte).
Hypothesis HM : bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)).
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HS : rw_cells rsegs m (bv_unsigned sp + 32) [CB 8 junk].
Hypothesis DMS : mode + 12 <= bv_unsigned sp + 32 \/ bv_unsigned sp + 40 <= mode + 4.
Hypothesis MI : mem_inv rsegs m.

Lemma seg_DA :
  (forall (y10 y11 y20 y22 y23 : word) (m' : word -> option byte),
     bv_unsigned y10 = fd_olen nch ns -> y20 = Z_to_bv 64 ns -> bv_unsigned y22 = fd_olen nch ns ->
     bv_unsigned y23 = fd_fits nch ns ->
     rw_cells rsegs m' (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
     munch [(bv_unsigned sp + 32, bv_unsigned sp + 40)] m m' -> wmono rsegs m m' ->
     bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
     mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x12eb4) sp x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13
       x14 x15 x16 x17 (Z_to_bv 64 mode) x19 y20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x147c4) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 sp x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 mode) x19 x20 x21
     x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12e5c) fc None m (seg_rom rsegs)).
Proof.
  intros CONT.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, length_le4 in HMB.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof HM as HM0.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  pose proof (munch_refl [(bv_unsigned sp + 32, bv_unsigned sp + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof MI as MI0.
  clear HM1 HM2.
  step. rewrite sx32_lit by lia. step. rewrite sx32_lit by lia.
  step. clear HR1 HR2.
  step. step. unfold v_slt, c_lts. rewrite !lts0_lit by lia.
  unfold fd_olen, fd_fits in CONT.
  destruct (Z.ltb_spec 0 nch) as [P1|P1]; destruct (Z.ltb_spec 0 ns) as [P2|P2]; cbn [andb] in CONT.
  - step. step. step. if_false.
    step. step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia.
    step. step. if_true. step. step. rewrite (unsigned_lit nch), (unsigned_lit ns) by lia.
    do 6 step.
    assert (0 < nch * ns <= 127 * 127) by nia.
    eapply CONT; try eassumption; try reflexivity; vsimp.
    all: rewrite (Z.mul_comm ns nch); destruct (nch * ns <? 481); reflexivity.
  - do 3 step. if_true. step. if_false. do 4 step.
    eapply CONT; try eassumption; try reflexivity; vsimp.
  - do 3 step. if_true. step. if_false. do 4 step.
    eapply CONT; try eassumption; try reflexivity; vsimp.
  - do 3 step. if_true. step. if_false. do 4 step.
    eapply CONT; try eassumption; try reflexivity; vsimp.
Qed.

End DA.
