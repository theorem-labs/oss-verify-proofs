(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 78 of its 111 lines of code are new or changed and 2524 lines of the source are left out. *)
(* Core round-trip helper lemmas of the fuzz_ctrl LLVMFuzzerTestOneInput slot proof, image A (asan), ported from the
   ubsan twins lib/U/Prog/Seg/Tac_u2.v and Tac_u2m.v (a working branch).  A SMALL, bounded set: the frame
   model-length lemmas a_row_len / a_rtX_len / a_rtn (u2_row_len / u2_rtX_len / u2_rtn), the byte-keep across a run
   a_keep (u2_keep), the round-trip bundle keeps a_RB_keep / a_RFb_keep (u2_RB_keep / u2_RFb_keep), and the harness
   block placement a_hb (u2_hb).  Unlike the ubsan twin the asan evt runs on the real memory (no normalize step; see
   A/Prog/Seg/Tac_slot.v), so the byte-keep is the real-memory transport RcAsanFPLib.fl_bytes (munch W + outside W),
   and the round-trip bundles carry the asan `fr`-indexed slots OURb (fr+2624) / IDBr (fr+2176) / FGBr (fr+2256) of
   A/Prog/SlotInv.v.  These unblock the R6-R13 full-wrapper proofs. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcEmit RcEmitLib RcSynth RcSynthLib RcLay
  RcFin RcFinLib RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* ---- Lengths of the round-trip model (u2_row_len / u2_rtX_len / u2_rtn) ---- *)

Lemma a_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma a_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, reac_ctrl_build_as_c.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply a_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b != 0: E(b), 124 <= n_b <= 1492, and F_b has n_b bytes. *)
Lemma a_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, reac_ctrl_build_as_c.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, a_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* ---- Bytes a segment does not touch are kept across a run (u2_keep).  The asan evt runs on the real memory, so this
   is the real-memory transport RcAsanFPLib.fl_bytes: a munch W whose write set W is outside the bytes' range. ---- *)
Lemma a_keep : forall W m m' a bs, munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. intros W m m' a bs MU HO H. exact (fl_bytes W m m' a bs H MU HO). Qed.

(* ---- The round-trip bundles across a run (asan registers s6 22, s7 23, s8 24, s9 25; slots fr+2624 / fr+2176 /
   fr+2256; the block at phi) (u2_RB_keep / u2_RFb_keep) ---- *)

(* RB across a run that keeps the frame slots [fr+2176, fr+2630) (OURb fr+2624, IDBr fr+2176, FGBr fr+2256) and the
   RB registers s6 (22), s7 (23), s9 (25). *)
Lemma a_RB_keep : forall g fr b idb fgb regs regs' W m m',
  munch W m m' -> length idb = 38%nat -> length fgb = 72%nat ->
  (forall x, fr + 2176 <= x < fr + 2630 -> outside W x) ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  RB g fr b idb fgb regs m -> RB g fr b idb fgb regs' m'.
Proof.
  intros g fr b idb fgb regs regs' W m m' MU L1 L2 HD E22 E23 E25
    (Hb & (Hc & H22 & H25) & HO & H23 & HI & HF).
  unfold RB, CUR, OURb, IDBr, FGBr, rg in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite E22; exact H22 | rewrite E25; exact H25]|].
  split.
  { apply (a_keep W m m' (fr + 2624) (OUR (g_in g)) MU); [|exact HO].
    rewrite OUR_length. intros x Hx. apply HD. lia. }
  split; [rewrite E23; exact H23|].
  split.
  { apply (a_keep W m m' (fr + 2176) idb MU); [|exact HI].
    rewrite L1. intros x Hx. apply HD. lia. }
  { apply (a_keep W m m' (fr + 2256) fgb MU); [|exact HF].
    rewrite L2. intros x Hx. apply HD. lia. }
Qed.

(* RFb across a run that keeps the frame slots and the block [phi, phi + n_b), plus the RFb register s8 (24). *)
Lemma a_RFb_keep : forall g fr b idb fgb phi regs regs' W m m',
  munch W m m' -> length idb = 38%nat -> length fgb = 72%nat ->
  (forall x, fr + 2176 <= x < fr + 2630 -> outside W x) ->
  (forall x, phi <= x < phi + rnb g b -> outside W x) ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  RFb g fr b idb fgb phi regs m -> RFb g fr b idb fgb phi regs' m'.
Proof.
  intros g fr b idb fgb phi regs regs' W m m' MU L1 L2 HD HDp E22 E23 E24 E25
    (HRB & Hnz & H24 & HF).
  unfold rnb in *.
  destruct (a_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HBd & HL).
  unfold RFb, rg in *. rewrite E24.
  split; [exact (a_RB_keep g fr b idb fgb regs regs' W m m' MU L1 L2 HD E22 E23 E25 HRB)|].
  split; [exact Hnz|]. split; [exact H24|].
  apply (a_keep W m m' phi (rt_F (g_in g) (Z.of_nat b)) MU); [|exact HF].
  rewrite HL. intros x Hx. apply HDp. rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

(* ---- HBR: a live harness block (phi, n) lies in AppMem below the real stack (u2_hb) ---- *)

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

(* The single live harness block (phi, n) carried by FRA's heap is placed, aligned low, below the real stack, in
   application memory and writable (Contract.a_laws AH1). *)
Lemma a_hb : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  phi <> 0 /\ 4096 <= phi /\ phi + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\
  end_in_app phi n /\ (forall a, phi <= a < phi + n -> app_mem a /\ writable_at rsegs mem a).
Proof.
  intros g fr phi n regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & _ & HAH & _).
  pose proof (AC.a_laws_blocks AC.ASYMS _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API)
                (hb1 phi n ++ g_H g) mem md phi n HAH
                ltac:(unfold hb1; apply in_or_app; left; apply in_eq))
    as (Hal & Hlo & Hhi & Hein & Hbytes).
  split; [lia|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hein|].
  intros a Ha. destruct (Hbytes a Ha) as (Hap & Hwr & _). split; [exact Hap | exact Hwr].
Qed.

End S.
