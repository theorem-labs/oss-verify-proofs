(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AKitQ.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma le4_two_bytes : forall b0 b1 : Z, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  le4 (Z_to_bv 64 (b0 + 256 * b1)) = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros b0 b1 H0 H1. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia. change (8+8) with 16. change (16+8) with 24. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal. apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia.
Qed.

#[using="Type"] Lemma rw_C1x4_to_C4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))].
Proof.
  intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_C4_to_C1x4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))] ->
  rw_cells asegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma rw_hdr_to_C4 : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs) ->
  rw_cells asegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs).
Proof.
  intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_C4_to_hdr : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs) ->
  rw_cells asegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs).
Proof.
  intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stk_cb : forall m lo hi, stk asegs m lo hi -> lo <= hi ->
  exists bs, rw_cells asegs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros m lo hi ST Hle. destruct (stk_carve asegs m lo hi (Z.to_nat (hi - lo)) ST ltac:(lia)) as [_ [bs H]].
  exists bs. rewrite Z2Nat.id in H by lia. replace (hi - (hi - lo)) with lo in H by lia. exact H.
Qed.
#[using="Type"] Lemma stk_of_cb : forall m lo n bs, rw_cells asegs m lo [CB (Z.to_nat n) bs] -> 0 <= n -> stk asegs m lo (lo + n).
Proof.
  intros m lo n bs H Hn. pose proof (stk_of_rw_cells asegs m lo _ H) as S. cbn [cells_size csize] in S.
  rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma stk_merge3 : forall m a b c d, stk asegs m a b -> stk asegs m b c -> stk asegs m c d -> a <= b <= c -> c <= d -> stk asegs m a d.
Proof. intros. eapply stk_merge; [| eapply stk_merge; [| | ]|]; eauto; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_any_write : forall m lo hi a bs, stk asegs m lo hi -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  stk asegs (write_to_mem m (wa a) bs) lo hi.
Proof. intros. apply stk_write; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_zero_le8 : forall m A n j,
  rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  0 <= j -> 8 * j + 8 <= n ->
  bytes_at asegs m (A + 8 * j) (le8 (Z_to_bv 64 0)).
Proof.
  intros m A n j [[_ HB] _] Hj Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  (nd_pre HB 3%nat; intros H0 H1 HB; nd_post). rewrite repeat_length in H1, HB.
  split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  replace (A + 8 * j + Z.of_nat i) with (A + Z.of_nat (Z.to_nat (8 * j) + i)) by lia.
  rewrite HB by lia. rewrite nth_error_repeat' by lia.
  replace (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8) by reflexivity.
  rewrite nth_error_repeat' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u64arr_snoc : forall m A ws (w : word),
  u64arr asegs m A ws -> rw_cells asegs m (A + 8 * Z.of_nat (length ws)) [C8 w] ->
  u64arr asegs m A (ws ++ [w]).
Proof.
  intros m A ws w [HB HW] [[_ HB2] HW2]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in HB2, HW2.
  rewrite app_nil_r in HB2. split.
  - rewrite u64s_app. cbn [u64s app]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB|].
    rewrite u64s_length. replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact HB2.
  - rewrite length_app. cbn [length]. (nd_pre HW 3%nat; intros H0 H1 HW; nd_post). (nd_pre HW2 3%nat; intros _ H3 HW2; nd_post).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws))); [apply HW; lia|].
    replace (A + i) with (A + 8 * Z.of_nat (length ws) + (i - 8 * Z.of_nat (length ws))) by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_stk : forall m A len, (exists bs, rw_cells asegs m A [CB (Z.to_nat len) bs]) -> 0 <= len -> stk asegs m A (A + len).
Proof. intros m A len [bs H] Hl. eapply stk_of_cb; eauto. Qed.
#[using="Type"] Lemma stk_junk : forall m A hi, stk asegs m A hi -> A <= hi -> exists bs, rw_cells asegs m A [CB (Z.to_nat (hi - A)) bs].
Proof. intros. apply stk_cb; assumption. Qed.

#[using="Type"] Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof.
  intros m A H0 H1. split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
#[using="Type"] Lemma u64arr_one : forall m A (w : word), rw_cells asegs m A [C8 w] -> u64arr asegs m A [w].
Proof.
  intros m A w H. pose proof (rw_cells_bound asegs m A _ H) as B. cbn [cells_size csize Nat.add] in B.
  change [w] with ([] ++ [w]). apply u64arr_snoc; [apply u64arr_nil; lia|]. cbn [length Z.of_nat Z.mul]. rewrite Z.add_0_r. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma byte0_of_word : forall s0 hi, 0 <= s0 < 256 -> 0 <= hi -> Z.land (s0 + 256 * hi) 255 = s0.
Proof.
  intros s0 hi H0 Hh. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma byte0_cas_val : forall x s1, 0 <= x -> 0 <= s1 < 256 ->
  Z.lxor x (Z.land (Z.lxor x s1) 255) = x - x mod 256 + s1.
Proof.
  intros x s1 Hx Hs. set (r := x - x mod 256 + s1).
  assert (Hr : 0 <= r) by (subst r; Z.div_mod_to_equations; lia).
  assert (Rlo : r mod 2^8 = s1) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
  assert (Rhi : r / 2^8 = x / 2^8) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.lxor_spec, Z.land_spec, Z.lxor_spec. change 255 with (Z.ones 8).
  destruct (Z_lt_le_dec k 8) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. rewrite <- (Z.mod_pow2_bits_low r 8 k) by lia. rewrite Rlo.
    destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
  - rewrite Z.ones_spec_high by lia.
    replace k with ((k - 8) + 8) at 4 by lia. rewrite <- (Z.div_pow2_bits r 8 (k - 8)) by lia. rewrite Rhi.
    rewrite Z.div_pow2_bits by lia. replace (k - 8 + 8) with k by lia.
    destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma byte0_cas : forall s0 s1 hi, 0 <= s0 < 256 -> 0 <= s1 < 256 -> 0 <= hi ->
  Z.lxor (s0 + 256 * hi) (Z.land (Z.lxor (s0 + 256 * hi) s1) 255) = s1 + 256 * hi.
Proof. intros. rewrite byte0_cas_val by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition afree_unw (RNG : footprint) (lo : Z) (m : amem) (top : Z) (sp s0 ra : word) (trt : list Z) : Prop :=
  (exists tr, trt = bv_unsigned ra :: tr /\ uchain m top AFREE_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr
              /\ (length tr <= 28)%nat /\ bv_unsigned sp + 16 < top /\ rng RNG lo (top - lo))
  \/ (trt = [] /\ top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47).

#[using="Type"] Lemma afree_unw_length : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> (length trt <= 29)%nat.
Proof. intros RNG lo m top sp s0 ra trt [(tr & -> & _ & L & _)|(-> & _)]; cbn; lia. Qed.

#[using="Type"] Lemma afree_unw_sp47 : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> top <= 2^47 -> bv_unsigned sp < 2^47.
Proof. intros RNG lo m top sp s0 ra trt [(tr & _ & _ & _ & B & _)|(_ & _ & B)] T; lia. Qed.

#[using="Type"] Lemma afree_unw_frame : forall RNG lo m m' top sp s0 ra trt,
  afree_unw RNG lo m top sp s0 ra trt -> (forall a, bv_unsigned s0 - 16 <= a < top -> m' (wa a) = m (wa a)) -> afree_unw RNG lo m' top sp s0 ra trt.
Proof.
  intros RNG lo m m' top sp s0 ra trt [(tr & E & UC & L & T & R)|H] AG; [left| right; exact H].
  exists tr. split; [exact E|]. split; [| split; [exact L| split; [exact T| exact R]]].
  eapply uchain_frame; [exact UC| exact AG].
Qed.

#[using="Type"] Lemma afree_unw_rng_mono : forall RNG RNG' lo m top sp s0 ra trt,
  afree_unw RNG lo m top sp s0 ra trt -> fp_le RNG RNG' -> afree_unw RNG' lo m top sp s0 ra trt.
Proof.
  intros RNG RNG' lo m top sp s0 ra trt [(tr & E & UC & L & T & R)|H] LE; [left| right; exact H].
  exists tr. repeat (split; [assumption|]). eapply ITreeA.rng_fp_le; [exact LE| exact R].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma le4_two_bytes : forall b0 b1 : Z, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  le4 (Z_to_bv 64 (b0 + 256 * b1)) = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros b0 b1 H0 H1. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia. change (8+8) with 16. change (16+8) with 24. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
  f_equal. apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia.
Qed.

#[using="Type"] Lemma rw_C1x4_to_C4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))].
Proof.
  intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_C4_to_C1x4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))] ->
  rw_cells asegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma rw_hdr_to_C4 : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs) ->
  rw_cells asegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs).
Proof.
  intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_C4_to_hdr : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  rw_cells asegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs) ->
  rw_cells asegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs).
Proof.
  intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stk_cb : forall m lo hi, stk asegs m lo hi -> lo <= hi ->
  exists bs, rw_cells asegs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros m lo hi ST Hle. destruct (stk_carve asegs m lo hi (Z.to_nat (hi - lo)) ST ltac:(lia)) as [_ [bs H]].
  exists bs. rewrite Z2Nat.id in H by lia. replace (hi - (hi - lo)) with lo in H by lia. exact H.
Qed.
#[using="Type"] Lemma stk_of_cb : forall m lo n bs, rw_cells asegs m lo [CB (Z.to_nat n) bs] -> 0 <= n -> stk asegs m lo (lo + n).
Proof.
  intros m lo n bs H Hn. pose proof (stk_of_rw_cells asegs m lo _ H) as S. cbn [cells_size csize] in S.
  rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma stk_merge3 : forall m a b c d, stk asegs m a b -> stk asegs m b c -> stk asegs m c d -> a <= b <= c -> c <= d -> stk asegs m a d.
Proof. intros. eapply stk_merge; [| eapply stk_merge; [| | ]|]; eauto; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_any_write : forall m lo hi a bs, stk asegs m lo hi -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  stk asegs (write_to_mem m (wa a) bs) lo hi.
Proof. intros. apply stk_write; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_zero_le8 : forall m A n j,
  rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  0 <= j -> 8 * j + 8 <= n ->
  bytes_at asegs m (A + 8 * j) (le8 (Z_to_bv 64 0)).
Proof.
  intros m A n j [[_ HB] _] Hj Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  (nd_pre HB 3%nat; intros H0 H1 HB; nd_post). rewrite repeat_length in H1, HB.
  split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  replace (A + 8 * j + Z.of_nat i) with (A + Z.of_nat (Z.to_nat (8 * j) + i)) by lia.
  rewrite HB by lia. rewrite nth_error_repeat' by lia.
  replace (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8) by reflexivity.
  rewrite nth_error_repeat' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u64arr_snoc : forall m A ws (w : word),
  u64arr asegs m A ws -> rw_cells asegs m (A + 8 * Z.of_nat (length ws)) [C8 w] ->
  u64arr asegs m A (ws ++ [w]).
Proof.
  intros m A ws w [HB HW] [[_ HB2] HW2]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in HB2, HW2.
  rewrite app_nil_r in HB2. split.
  - rewrite u64s_app. cbn [u64s app]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB|].
    rewrite u64s_length. replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact HB2.
  - rewrite length_app. cbn [length]. (nd_pre HW 3%nat; intros H0 H1 HW; nd_post). (nd_pre HW2 3%nat; intros _ H3 HW2; nd_post).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws))); [apply HW; lia|].
    replace (A + i) with (A + 8 * Z.of_nat (length ws) + (i - 8 * Z.of_nat (length ws))) by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_stk : forall m A len, (exists bs, rw_cells asegs m A [CB (Z.to_nat len) bs]) -> 0 <= len -> stk asegs m A (A + len).
Proof. intros m A len [bs H] Hl. eapply stk_of_cb; eauto. Qed.
#[using="Type"] Lemma stk_junk : forall m A hi, stk asegs m A hi -> A <= hi -> exists bs, rw_cells asegs m A [CB (Z.to_nat (hi - A)) bs].
Proof. intros. apply stk_cb; assumption. Qed.

#[using="Type"] Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof.
  intros m A H0 H1. split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
#[using="Type"] Lemma u64arr_one : forall m A (w : word), rw_cells asegs m A [C8 w] -> u64arr asegs m A [w].
Proof.
  intros m A w H. pose proof (rw_cells_bound asegs m A _ H) as B. cbn [cells_size csize Nat.add] in B.
  change [w] with ([] ++ [w]). apply u64arr_snoc; [apply u64arr_nil; lia|]. cbn [length Z.of_nat Z.mul]. rewrite Z.add_0_r. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma byte0_of_word : forall s0 hi, 0 <= s0 < 256 -> 0 <= hi -> Z.land (s0 + 256 * hi) 255 = s0.
Proof.
  intros s0 hi H0 Hh. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma byte0_cas_val : forall x s1, 0 <= x -> 0 <= s1 < 256 ->
  Z.lxor x (Z.land (Z.lxor x s1) 255) = x - x mod 256 + s1.
Proof.
  intros x s1 Hx Hs. set (r := x - x mod 256 + s1).
  assert (Hr : 0 <= r) by (subst r; Z.div_mod_to_equations; lia).
  assert (Rlo : r mod 2^8 = s1) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
  assert (Rhi : r / 2^8 = x / 2^8) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.lxor_spec, Z.land_spec, Z.lxor_spec. change 255 with (Z.ones 8).
  destruct (Z_lt_le_dec k 8) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. rewrite <- (Z.mod_pow2_bits_low r 8 k) by lia. rewrite Rlo.
    destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
  - rewrite Z.ones_spec_high by lia.
    replace k with ((k - 8) + 8) at 4 by lia. rewrite <- (Z.div_pow2_bits r 8 (k - 8)) by lia. rewrite Rhi.
    rewrite Z.div_pow2_bits by lia. replace (k - 8 + 8) with k by lia.
    destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma byte0_cas : forall s0 s1 hi, 0 <= s0 < 256 -> 0 <= s1 < 256 -> 0 <= hi ->
  Z.lxor (s0 + 256 * hi) (Z.land (Z.lxor (s0 + 256 * hi) s1) 255) = s1 + 256 * hi.
Proof. intros. rewrite byte0_cas_val by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition afree_unw (RNG : footprint) (lo : Z) (m : amem) (top : Z) (sp s0 ra : word) (trt : list Z) : Prop :=
  (exists tr, trt = bv_unsigned ra :: tr /\ uchain m top AFREE_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr
              /\ (length tr <= 28)%nat /\ bv_unsigned sp + 16 < top /\ rng RNG lo (top - lo))
  \/ (trt = [] /\ top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47).

#[using="Type"] Lemma afree_unw_length : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> (length trt <= 29)%nat.
Proof. intros RNG lo m top sp s0 ra trt [(tr & -> & _ & L & _)|(-> & _)]; cbn; lia. Qed.

#[using="Type"] Lemma afree_unw_sp47 : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> top <= 2^47 -> bv_unsigned sp < 2^47.
Proof. intros RNG lo m top sp s0 ra trt [(tr & _ & _ & _ & B & _)|(_ & _ & B)] T; lia. Qed.

#[using="Type"] Lemma afree_unw_frame : forall RNG lo m m' top sp s0 ra trt,
  afree_unw RNG lo m top sp s0 ra trt -> (forall a, bv_unsigned s0 - 16 <= a < top -> m' (wa a) = m (wa a)) -> afree_unw RNG lo m' top sp s0 ra trt.
Proof.
  intros RNG lo m m' top sp s0 ra trt [(tr & E & UC & L & T & R)|H] AG; [left| right; exact H].
  exists tr. split; [exact E|]. split; [| split; [exact L| split; [exact T| exact R]]].
  eapply uchain_frame; [exact UC| exact AG].
Qed.

#[using="Type"] Lemma afree_unw_rng_mono : forall RNG RNG' lo m top sp s0 ra trt,
  afree_unw RNG lo m top sp s0 ra trt -> fp_le RNG RNG' -> afree_unw RNG' lo m top sp s0 ra trt.
Proof.
  intros RNG RNG' lo m top sp s0 ra trt [(tr & E & UC & L & T & R)|H] LE; [left| right; exact H].
  exists tr. repeat (split; [assumption|]). eapply ITreeA.rng_fp_le; [exact LE| exact R].
Qed.
End CANSEC1.
End TwB.
End AKitQ.

(* [comment removed for export] *)
Module ARepQP.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma size_of_class_24 : size_of_class K_BATCH_CLASS = 8192.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma batches_bytes_app : forall l1 l2, batches_bytes (l1 ++ l2) = batches_bytes l1 + batches_bytes l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; unfold batches_bytes; lia]. Qed.
#[using="Type"] Lemma batches_bytes_cons : forall b l, batches_bytes (b :: l) = b_size b + batches_bytes l.
Proof. reflexivity. Qed.
#[using="Type"] Lemma batches_bytes_nil : batches_bytes [] = 0.
Proof. reflexivity. Qed.

#[using="Type"] Lemma batches_bytes_lb : forall l, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> Q_BATCH_BYTES * Z.of_nat (length l) <= batches_bytes l.
Proof.
  induction l as [|b l IH]; intros HF; cbn [length]; [rewrite batches_bytes_nil; lia|].
  rewrite batches_bytes_cons. inversion HF; subst. specialize (IH ltac:(assumption)). unfold Q_BATCH_BYTES in *. lia.
Qed.
#[using="Type"] Lemma batches_bytes_In : forall l b, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> In b l -> Q_BATCH_BYTES <= b_size b <= batches_bytes l.
Proof.
  induction l as [|a l IH]; intros b HF Hin; [destruct Hin|].
  rewrite batches_bytes_cons. inversion HF; subst. pose proof (batches_bytes_lb l ltac:(assumption)) as LB.
  destruct Hin as [<-|Hin]; [unfold Q_BATCH_BYTES in *; lia|]. specialize (IH b ltac:(assumption) Hin). unfold Q_BATCH_BYTES in *; lia.
Qed.

#[using="Type"] Lemma qaddrs_app : forall L qs1 qs2, qaddrs L (qs1 ++ qs2) = qaddrs L qs1 ++ qaddrs L qs2.
Proof. intros. unfold qaddrs. apply map_app. Qed.
#[using="Type"] Lemma qfirst_cons : forall L q qs, qfirst L (q :: qs) = abatch_addr L (qb_slot q).
Proof. reflexivity. Qed.
#[using="Type"] Lemma qfirst_nil : forall L, qfirst L [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma qlast_nil : forall L, qlast L [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma qlast_app1 : forall L qs q, qlast L (qs ++ [q]) = abatch_addr L (qb_slot q).
Proof. intros. unfold qlast. rewrite qaddrs_app. cbn [qaddrs map]. apply last_last. Qed.
#[using="Type"] Lemma qfirst_app : forall L qs1 qs2, qs1 <> [] -> qfirst L (qs1 ++ qs2) = qfirst L qs1.
Proof. intros L [|q qs1] qs2 NE; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma last_app_ne : forall {A} (l1 l2 : list A) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros A l1 l2 d NE. rewrite (app_removelast_last d NE) at 1. rewrite app_assoc, last_last.
  reflexivity.
Qed.
#[using="Type"] Lemma qlast_app : forall L qs1 qs2, qs2 <> [] -> qlast L (qs1 ++ qs2) = qlast L qs2.
Proof.
  intros L qs1 qs2 NE. unfold qlast. rewrite qaddrs_app. apply last_app_ne.
  unfold qaddrs. destruct qs2; [congruence| discriminate].
Qed.

#[using="Type"] Lemma qhdrs_length : forall L chs ks, length ks = length chs -> length (qhdrs L chs ks) = length chs.
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try lia.
  rewrite length_app, IH by lia. cbn. lia.
Qed.
#[using="Type"] Lemma qhdrs_cons : forall L ch chs k ks, qhdrs L (ch :: chs) (k :: ks) = qhdrs L chs ks ++ [qhdr L ch k].
Proof. reflexivity. Qed.

#[using="Type"] Lemma qentries_app : forall bs1 qs1 bs2 qs2, length qs1 = length bs1 ->
  qentries (bs1 ++ bs2) (qs1 ++ qs2) = qentries bs1 qs1 ++ qentries bs2 qs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 LEN; cbn in *; try lia; [reflexivity|].
  rewrite IH by lia. rewrite app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma abatches_to_length : forall L m bs qs nxt, abatches_to L m bs qs nxt -> length qs = length bs.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB; cbn in *; try tauto.
  destruct AB as [_ AB]. rewrite (IH qs nxt AB). reflexivity.
Qed.
#[using="Type"] Lemma abatches_length : forall L m bs qs, abatches L m bs qs -> length qs = length bs.
Proof. intros. eapply abatches_to_length. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma abatches_to_app : forall L m bs1 qs1 bs2 qs2 nxt, length qs1 = length bs1 ->
  abatches_to L m (bs1 ++ bs2) (qs1 ++ qs2) nxt <-> abatches_to L m bs1 qs1 (hd nxt (qaddrs L qs2)) /\ abatches_to L m bs2 qs2 nxt.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 nxt LEN; cbn in *; try lia; [tauto|].
  rewrite IH by lia. rewrite qaddrs_app.
  assert (E : hd nxt (qaddrs L qs1 ++ qaddrs L qs2) = hd (hd nxt (qaddrs L qs2)) (qaddrs L qs1)).
  { destruct qs1; cbn; reflexivity. }
  rewrite E. tauto.
Qed.
#[using="Type"] Lemma abatches_to_last : forall L m b q nxt, abatches_to L m [b] [q] nxt <-> abatch_cells L m b q nxt.
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n HF; cbn; [exact I|]. inversion HF; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

#[using="MU WM"] Lemma abatch_cells_frame : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frame; [exact H1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frame; [exact H2 | exact MU | exact WM |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frame; [exact H3 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.

#[using="MU WM"] Lemma abatches_to_frame : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply abatch_cells_frame; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
#[using="MU WM"] Lemma abatches_frame : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frame; eassumption. Qed.

#[using="MU WM"] Lemma aqcache_frame : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frame; [exact QC | exact MU | exact WM | exact D].
  - eapply abatches_frame; [exact AB | exact DB].
Qed.

#[using="MU WM"] Lemma aintal_frame : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frame; [exact F | exact MU | exact WM | exact DF].
  - eapply stk_transport_disjoint; [exact S | exact MU | exact WM |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.

#[using="MU WM"] Lemma aquar_glob_const_frame :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frame; [exact A | exact MU | exact WM | exact D1].
  - eapply cells_frame; [exact B | exact MU | exact WM | exact D2].
Qed.
End Frames.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_bslot_busy : forall L st X Q q,
  qcoupled L st X Q -> In q (q_loc Q ++ q_glob Q) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = qb_slot q.
Proof.
  intros L st X Q q (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS (qb_slot q))). apply in_map. exact Hin.
Qed.

#[using="Type"] Theorem AQUAR_frame_at : forall L st st' X X' Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono asegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR_at L st' X' Q m'.
Proof.
  intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold AQUAR_at. rewrite E1, E2, E3, E4.
  (* [comment removed for export] *)
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  (nd_pre DG 3%nat; intros DG1 DG2 DG3; nd_post).
  assert (DI1 : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE).
  { unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
    split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia. }
  destruct DI1 as [DF DB].
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
    apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [| split]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - eapply aintal_frame; eassumption.
  - (* [comment removed for export] *)
    (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qcoupled. cbv zeta. rewrite E1, E3.
    split; [exact LN1|]. split; [exact LN2|]. split.
    { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c n | mb ms n]; [| exact I]. (nd_pre HOK 3%nat; intros b1 ctx Hin; nd_post). exists b1, ctx.
      specialize (FW _ Hin). cbn in FW. exact FW. }
    split; [exact ND1|]. split; [exact ND2|]. split.
    { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
      - specialize (FW b Hb). rewrite Sb in FW. exact FW.
      - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
    split; [| exact NN].
    intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
    + specialize (FW b Hb). rewrite Sb in FW. exact FW.
    + specialize (BW b Hb). rewrite Sb in BW. exact BW.
  - unfold qnum in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.
#[using="Type"] Theorem AQUAR_frame : forall L st st' X X' m m' W,
  AQUAR L st X m -> munch W m m' -> wmono asegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU WM UT QS. exists Q. exact (AQUAR_frame_at L st st' X X' Q m m' W AQ MU WM UT QS). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_init : forall L st X m,
  a_qloc st = [] -> a_qloc_bytes st = 0 -> a_qglob st = [] -> a_qglob_bytes st = 0 ->
  aquar_glob_const m ->
  rw_cells asegs m (aq_tcache L) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  aintal false m ->
  (forall b, In b (x_busy X) -> exists p, xb_st b = BLive p) ->
  AQUAR L st X m.
Proof.
  intros L st X m Q1 Q2 Q3 Q4 GC TC GL IA LIVE. exists qconc0. unfold AQUAR_at. rewrite Q1, Q2, Q3, Q4. cbn [q_loc q_glob q_ia q_pend qconc0].
  split; [exact GC|]. split; [split; [exact TC| exact I]|]. split; [split; [exact GL| exact I]|]. split; [exact IA|]. split.
  - unfold qcoupled. cbn. rewrite Q1, Q3. cbn. repeat split; try constructor; try (intros; tauto).
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
  - unfold qnum. rewrite Q1, Q2, Q3, Q4. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma size_of_class_24 : size_of_class K_BATCH_CLASS = 8192.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma batches_bytes_app : forall l1 l2, batches_bytes (l1 ++ l2) = batches_bytes l1 + batches_bytes l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; unfold batches_bytes; lia]. Qed.
#[using="Type"] Lemma batches_bytes_cons : forall b l, batches_bytes (b :: l) = b_size b + batches_bytes l.
Proof. reflexivity. Qed.
#[using="Type"] Lemma batches_bytes_nil : batches_bytes [] = 0.
Proof. reflexivity. Qed.

#[using="Type"] Lemma batches_bytes_lb : forall l, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> Q_BATCH_BYTES * Z.of_nat (length l) <= batches_bytes l.
Proof.
  induction l as [|b l IH]; intros HF; cbn [length]; [rewrite batches_bytes_nil; lia|].
  rewrite batches_bytes_cons. inversion HF; subst. specialize (IH ltac:(assumption)). unfold Q_BATCH_BYTES in *. lia.
Qed.
#[using="Type"] Lemma batches_bytes_In : forall l b, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> In b l -> Q_BATCH_BYTES <= b_size b <= batches_bytes l.
Proof.
  induction l as [|a l IH]; intros b HF Hin; [destruct Hin|].
  rewrite batches_bytes_cons. inversion HF; subst. pose proof (batches_bytes_lb l ltac:(assumption)) as LB.
  destruct Hin as [<-|Hin]; [unfold Q_BATCH_BYTES in *; lia|]. specialize (IH b ltac:(assumption) Hin). unfold Q_BATCH_BYTES in *; lia.
Qed.

#[using="Type"] Lemma qaddrs_app : forall L qs1 qs2, qaddrs L (qs1 ++ qs2) = qaddrs L qs1 ++ qaddrs L qs2.
Proof. intros. unfold qaddrs. apply map_app. Qed.
#[using="Type"] Lemma qfirst_cons : forall L q qs, qfirst L (q :: qs) = abatch_addr L (qb_slot q).
Proof. reflexivity. Qed.
#[using="Type"] Lemma qfirst_nil : forall L, qfirst L [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma qlast_nil : forall L, qlast L [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma qlast_app1 : forall L qs q, qlast L (qs ++ [q]) = abatch_addr L (qb_slot q).
Proof. intros. unfold qlast. rewrite qaddrs_app. cbn [qaddrs map]. apply last_last. Qed.
#[using="Type"] Lemma qfirst_app : forall L qs1 qs2, qs1 <> [] -> qfirst L (qs1 ++ qs2) = qfirst L qs1.
Proof. intros L [|q qs1] qs2 NE; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma last_app_ne : forall {A} (l1 l2 : list A) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros A l1 l2 d NE. rewrite (app_removelast_last d NE) at 1. rewrite app_assoc, last_last.
  reflexivity.
Qed.
#[using="Type"] Lemma qlast_app : forall L qs1 qs2, qs2 <> [] -> qlast L (qs1 ++ qs2) = qlast L qs2.
Proof.
  intros L qs1 qs2 NE. unfold qlast. rewrite qaddrs_app. apply last_app_ne.
  unfold qaddrs. destruct qs2; [congruence| discriminate].
Qed.

#[using="Type"] Lemma qhdrs_length : forall L chs ks, length ks = length chs -> length (qhdrs L chs ks) = length chs.
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try lia.
  rewrite length_app, IH by lia. cbn. lia.
Qed.
#[using="Type"] Lemma qhdrs_cons : forall L ch chs k ks, qhdrs L (ch :: chs) (k :: ks) = qhdrs L chs ks ++ [qhdr L ch k].
Proof. reflexivity. Qed.

#[using="Type"] Lemma qentries_app : forall bs1 qs1 bs2 qs2, length qs1 = length bs1 ->
  qentries (bs1 ++ bs2) (qs1 ++ qs2) = qentries bs1 qs1 ++ qentries bs2 qs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 LEN; cbn in *; try lia; [reflexivity|].
  rewrite IH by lia. rewrite app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma abatches_to_length : forall L m bs qs nxt, abatches_to L m bs qs nxt -> length qs = length bs.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB; cbn in *; try tauto.
  destruct AB as [_ AB]. rewrite (IH qs nxt AB). reflexivity.
Qed.
#[using="Type"] Lemma abatches_length : forall L m bs qs, abatches L m bs qs -> length qs = length bs.
Proof. intros. eapply abatches_to_length. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma abatches_to_app : forall L m bs1 qs1 bs2 qs2 nxt, length qs1 = length bs1 ->
  abatches_to L m (bs1 ++ bs2) (qs1 ++ qs2) nxt <-> abatches_to L m bs1 qs1 (hd nxt (qaddrs L qs2)) /\ abatches_to L m bs2 qs2 nxt.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 nxt LEN; cbn in *; try lia; [tauto|].
  rewrite IH by lia. rewrite qaddrs_app.
  assert (E : hd nxt (qaddrs L qs1 ++ qaddrs L qs2) = hd (hd nxt (qaddrs L qs2)) (qaddrs L qs1)).
  { destruct qs1; cbn; reflexivity. }
  rewrite E. tauto.
Qed.
#[using="Type"] Lemma abatches_to_last : forall L m b q nxt, abatches_to L m [b] [q] nxt <-> abatch_cells L m b q nxt.
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n HF; cbn; [exact I|]. inversion HF; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

#[using="MU WM"] Lemma abatch_cells_frame : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frame; [exact H1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frame; [exact H2 | exact MU | exact WM |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frame; [exact H3 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.

#[using="MU WM"] Lemma abatches_to_frame : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply abatch_cells_frame; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
#[using="MU WM"] Lemma abatches_frame : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frame; eassumption. Qed.

#[using="MU WM"] Lemma aqcache_frame : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frame; [exact QC | exact MU | exact WM | exact D].
  - eapply abatches_frame; [exact AB | exact DB].
Qed.

#[using="MU WM"] Lemma aintal_frame : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frame; [exact F | exact MU | exact WM | exact DF].
  - eapply stk_transport_disjoint; [exact S | exact MU | exact WM |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.

#[using="MU WM"] Lemma aquar_glob_const_frame :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frame; [exact A | exact MU | exact WM | exact D1].
  - eapply cells_frame; [exact B | exact MU | exact WM | exact D2].
Qed.
End Frames.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_bslot_busy : forall L st X Q q,
  qcoupled L st X Q -> In q (q_loc Q ++ q_glob Q) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = qb_slot q.
Proof.
  intros L st X Q q (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS (qb_slot q))). apply in_map. exact Hin.
Qed.

#[using="Type"] Theorem AQUAR_frame_at : forall L st st' X X' Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono asegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR_at L st' X' Q m'.
Proof.
  intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold AQUAR_at. rewrite E1, E2, E3, E4.
  (* [comment removed for export] *)
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  (nd_pre DG 3%nat; intros DG1 DG2 DG3; nd_post).
  assert (DI1 : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE).
  { unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
    split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia. }
  destruct DI1 as [DF DB].
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
    apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [| split]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - eapply aintal_frame; eassumption.
  - (* [comment removed for export] *)
    (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qcoupled. cbv zeta. rewrite E1, E3.
    split; [exact LN1|]. split; [exact LN2|]. split.
    { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c n | mb ms n]; [| exact I]. (nd_pre HOK 3%nat; intros b1 ctx Hin; nd_post). exists b1, ctx.
      specialize (FW _ Hin). cbn in FW. exact FW. }
    split; [exact ND1|]. split; [exact ND2|]. split.
    { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
      - specialize (FW b Hb). rewrite Sb in FW. exact FW.
      - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
    split; [| exact NN].
    intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
    + specialize (FW b Hb). rewrite Sb in FW. exact FW.
    + specialize (BW b Hb). rewrite Sb in BW. exact BW.
  - unfold qnum in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.
#[using="Type"] Theorem AQUAR_frame : forall L st st' X X' m m' W,
  AQUAR L st X m -> munch W m m' -> wmono asegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU WM UT QS. exists Q. exact (AQUAR_frame_at L st st' X X' Q m m' W AQ MU WM UT QS). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_init : forall L st X m,
  a_qloc st = [] -> a_qloc_bytes st = 0 -> a_qglob st = [] -> a_qglob_bytes st = 0 ->
  aquar_glob_const m ->
  rw_cells asegs m (aq_tcache L) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  aintal false m ->
  (forall b, In b (x_busy X) -> exists p, xb_st b = BLive p) ->
  AQUAR L st X m.
Proof.
  intros L st X m Q1 Q2 Q3 Q4 GC TC GL IA LIVE. exists qconc0. unfold AQUAR_at. rewrite Q1, Q2, Q3, Q4. cbn [q_loc q_glob q_ia q_pend qconc0].
  split; [exact GC|]. split; [split; [exact TC| exact I]|]. split; [split; [exact GL| exact I]|]. split; [exact IA|]. split.
  - unfold qcoupled. cbn. rewrite Q1, Q3. cbn. repeat split; try constructor; try (intros; tauto).
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
  - unfold qnum. rewrite Q1, Q2, Q3, Q4. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.
End TwB.
End ARepQP.

(* [comment removed for export] *)
Module ARepQR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Record qrconc := mkQR {
  qr_loc : list qbatchc;              (* [comment removed for export] *)
  qr_glob : list qbatchc;             (* [comment removed for export] *)
  qr_ia : bool;                       (* [comment removed for export] *)
  qr_tmp : list (abatch * qbatchc);   (* [comment removed for export] *)
  qr_pendb : list Z;                  (* [comment removed for export] *)
  qr_pend : list (achunk * Z);        (* [comment removed for export] *)
  qr_qpend : list (Z * Z)             (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition qr_entries (st : astate) (R : qrconc) : list (achunk * Z) :=
  qentries (a_qloc st) (qr_loc R) ++ qentries (a_qglob st) (qr_glob R)
  ++ qentries (map fst (qr_tmp R)) (map snd (qr_tmp R)) ++ qr_pend R.
Definition qr_bslots (R : qrconc) : list Z :=
  map qb_slot (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) ++ qr_pendb R.

Definition qcoupled_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) : Prop :=
  let es := qr_entries st R in let bslots := qr_bslots R in
     length (qr_loc R) = length (a_qloc st) /\ length (qr_glob R) = length (a_qglob st)
  /\ Forall (qentry_ok X) es
  /\ List.NoDup (qprim_ids es ++ qr_qpend R) /\ List.NoDup bslots
  /\ (forall k, In k bslots <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k)
  /\ (forall c k, In (c, k) (qprim_ids es ++ qr_qpend R) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c /\ xb_slot b = k)
  /\ Forall (fun k => 0 <= k) bslots.

(* [comment removed for export] *)
Definition qnum_tmp (bs : list abatch) : Prop := Forall (fun b => Q_BATCH_BYTES <= b_size b) bs.

(* [comment removed for export] *)
Definition aquar_mutex (m : amem) (mc mr : Z) : Prop :=
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 mc); C1 (Z_to_bv 8 mr); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition aquar_consts (m : amem) : Prop :=
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)].

Definition AQUAR_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) (TMP mc mr : Z) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ aqcache L m TMP (map fst (qr_tmp R)) (map snd (qr_tmp R)) (batches_bytes (map fst (qr_tmp R)))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnum st /\ qnum_tmp (map fst (qr_tmp R)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qr_of_q (Q : qconc) : qrconc := mkQR (q_loc Q) (q_glob Q) (q_ia Q) [] [] [] (q_pend Q).

#[using="Type"] Lemma qentries_nil : qentries [] [] = []. Proof. reflexivity. Qed.

#[using="Type"] Lemma AQUAR_rec_of_at : forall L st X Q TMP m,
  AQUAR_at L st X Q m ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  AQUAR_rec L st X (qr_of_q Q) TMP 0 0 m.
Proof.
  intros L st X Q TMP m ([QK MX] & TC & GL & IA & CP & NUM) TMPC.
  unfold AQUAR_rec, qr_of_q. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
  split; [exact QK|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|].
  split. { split; [| exact I]. cbn [length batches_bytes fold_right qfirst qlast qaddrs map hd List.last]. exact TMPC. }
  split; [exact IA|].
  split.
  { (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qcoupled_rec, qr_entries, qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb qr_pend qr_qpend map fst snd qentries].
    rewrite !app_nil_r.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN]. }
  split; [exact NUM| constructor].
Qed.

#[using="Type"] Lemma AQUAR_at_of_rec : forall L st X R TMP m,
  AQUAR_rec L st X R TMP 0 0 m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R TMP m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split; [| exact NUM].
  (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
  unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
  unfold qcoupled. cbv zeta.
  split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
  split; [exact BS|]. split; [exact PS| exact NN].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Record qrconc := mkQR {
  qr_loc : list qbatchc;              (* [comment removed for export] *)
  qr_glob : list qbatchc;             (* [comment removed for export] *)
  qr_ia : bool;                       (* [comment removed for export] *)
  qr_tmp : list (abatch * qbatchc);   (* [comment removed for export] *)
  qr_pendb : list Z;                  (* [comment removed for export] *)
  qr_pend : list (achunk * Z);        (* [comment removed for export] *)
  qr_qpend : list (Z * Z)             (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition qr_entries (st : astate) (R : qrconc) : list (achunk * Z) :=
  qentries (a_qloc st) (qr_loc R) ++ qentries (a_qglob st) (qr_glob R)
  ++ qentries (map fst (qr_tmp R)) (map snd (qr_tmp R)) ++ qr_pend R.
Definition qr_bslots (R : qrconc) : list Z :=
  map qb_slot (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) ++ qr_pendb R.

Definition qcoupled_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) : Prop :=
  let es := qr_entries st R in let bslots := qr_bslots R in
     length (qr_loc R) = length (a_qloc st) /\ length (qr_glob R) = length (a_qglob st)
  /\ Forall (qentry_ok X) es
  /\ List.NoDup (qprim_ids es ++ qr_qpend R) /\ List.NoDup bslots
  /\ (forall k, In k bslots <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k)
  /\ (forall c k, In (c, k) (qprim_ids es ++ qr_qpend R) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c /\ xb_slot b = k)
  /\ Forall (fun k => 0 <= k) bslots.

(* [comment removed for export] *)
Definition qnum_tmp (bs : list abatch) : Prop := Forall (fun b => Q_BATCH_BYTES <= b_size b) bs.

(* [comment removed for export] *)
Definition aquar_mutex (m : amem) (mc mr : Z) : Prop :=
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 mc); C1 (Z_to_bv 8 mr); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition aquar_consts (m : amem) : Prop :=
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)].

Definition AQUAR_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) (TMP mc mr : Z) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ aqcache L m TMP (map fst (qr_tmp R)) (map snd (qr_tmp R)) (batches_bytes (map fst (qr_tmp R)))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnum st /\ qnum_tmp (map fst (qr_tmp R)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qr_of_q (Q : qconc) : qrconc := mkQR (q_loc Q) (q_glob Q) (q_ia Q) [] [] [] (q_pend Q).

#[using="Type"] Lemma qentries_nil : qentries [] [] = []. Proof. reflexivity. Qed.

#[using="Type"] Lemma AQUAR_rec_of_at : forall L st X Q TMP m,
  AQUAR_at L st X Q m ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  AQUAR_rec L st X (qr_of_q Q) TMP 0 0 m.
Proof.
  intros L st X Q TMP m ([QK MX] & TC & GL & IA & CP & NUM) TMPC.
  unfold AQUAR_rec, qr_of_q. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
  split; [exact QK|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|].
  split. { split; [| exact I]. cbn [length batches_bytes fold_right qfirst qlast qaddrs map hd List.last]. exact TMPC. }
  split; [exact IA|].
  split.
  { (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qcoupled_rec, qr_entries, qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb qr_pend qr_qpend map fst snd qentries].
    rewrite !app_nil_r.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN]. }
  split; [exact NUM| constructor].
Qed.

#[using="Type"] Lemma AQUAR_at_of_rec : forall L st X R TMP m,
  AQUAR_rec L st X R TMP 0 0 m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R TMP m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split; [| exact NUM].
  (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
  unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
  unfold qcoupled. cbv zeta.
  split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
  split; [exact BS|]. split; [exact PS| exact NN].
Qed.
End CANSEC1.
End TwB.
End ARepQR.
