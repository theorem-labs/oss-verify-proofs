(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_ERRL_x.v, with its module paths changed; 9 of its 83 lines of code are new or changed. *)
(* rule 24: no function proved (kind: image law at the instance: errno's four bytes are readable and writable).
   Written for a Theorem Labs lane's top_x row ERRL_x (a Theorem Labs lane F1; integrator ReallocPrimary).

   errno's law is a fact of the IMAGE alone: errno's four bytes are bytes of reply's segment table, so every
   memory's ASan view reads a value there (LPS's mbyte falls back to the segment byte for an absent byte), and they
   lie in a writable segment.  The relation is never read: zz_ERRL (W_LLVMFuzzerTestOneInput_addI.v:247-275) drops
   its AR premise.  So the fact is stated ONCE, relation-free ([errno_rw_core], zz_ERRL's script for every W and
   mem), and both relation forms are 2-line corollaries:
   - [errno_law_of_core] : errno_law B (the AR form, W_LLVMFuzzerTestOneInput_cut.v:328, zz_ERRL's statement);
   - [errno_law_x_holds] : errno_law_x B ARx for EVERY ARx (W_LLVMFuzzerTestOneInput_cut_x.v:214, top_x's ERRL_x
     hypothesis `errno_law_x TfibB ARX`), in particular at reply's ARX (ARcf at CfParams_reply /\ Hp = []).
   Unit facts used: TfibSyms B (zz_HEV: as_errno B = TFIB_ERRNO_A), reply's segment table (seg_rom on errno's bytes,
   by vm_compute) and its writable-segment table (segwb, by vm_compute), exactly as zz_ERRL.
   [errno_azs] : azs B (as_errno B) 4 (W_contract.v:314), the drain stages' HERRZ, from the start-up table alone. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_addI.
Import ListNotations.
Local Open Scope Z_scope.

Section p.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).

(* errno's four bytes read a value and are writable, in every world and memory (zz_ERRL's script, relation-free). *)
Lemma errno_rw_core : forall B, TfibSyms B -> forall (W : world segs) (mem : word -> option byte),
  (exists v, val_mem segs (arm W mem) (as_errno B) 4 v /\ 0 <= v < 2 ^ 32) /\ awr W mem (as_errno B) 4.
Proof.
  intros B TS W mem. rewrite (zz_HEV B TS).
  assert (HS : forall j, 0 <= j < 8 -> seg_rom segs (Z_to_bv 64 (TFIB_ERRNO_A + j)) <> None).
  { intros j Hj.
    assert (Hb : forallb (fun i => match seg_rom segs (Z_to_bv 64 (TFIB_ERRNO_A + Z.of_nat i)) with
                                   Some _ => true | None => false end) (seq 0 8) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat j) ltac:(apply in_seq; lia)).
    rewrite Z2Nat.id in Hb by lia. destruct (seg_rom segs (Z_to_bv 64 (TFIB_ERRNO_A + j))); [discriminate | discriminate Hb]. }
  split.
  - destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 0) (HS 0 ltac:(lia))) as (b0 & E0).
    destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 1) (HS 1 ltac:(lia))) as (b1 & E1).
    destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 2) (HS 2 ltac:(lia))) as (b2 & E2).
    destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 3) (HS 3 ltac:(lia))) as (b3 & E3).
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
    pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
    unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3. change (2 ^ 8) with 256 in R0, R1, R2, R3.
    destruct (zz_le4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3) R0 R1 R2 R3)
      as (L0 & L1 & L2 & L3 & Hv).
    exists (zz_v4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3)). split; [|exact Hv].
    intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    + change (Z.of_nat 0) with 0. rewrite E0. f_equal. rewrite <- (zz_bv_of_u b0) at 1. f_equal. symmetry. exact L0.
    + change (Z.of_nat 1) with 1. rewrite E1. f_equal. rewrite <- (zz_bv_of_u b1) at 1. f_equal. symmetry. exact L1.
    + change (Z.of_nat 2) with 2. rewrite E2. f_equal. rewrite <- (zz_bv_of_u b2) at 1. f_equal. symmetry. exact L2.
    + change (Z.of_nat 3) with 3. rewrite E3. f_equal. rewrite <- (zz_bv_of_u b3) at 1. f_equal. symmetry. exact L3.
  - intros i Hi. unfold arm. apply wr_of_seg. apply segwb_ok.
    apply (rng_all_in (segwb segs) [(TFIB_ERRNO_A, 4)]); [vm_compute; reflexivity|].
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* The AR form (W_LLVMFuzzerTestOneInput_cut.v:328), zz_ERRL's statement. *)
Lemma errno_law_of_core : forall B, TfibSyms B -> errno_law B.
Proof. intros B TS ly S W mem md _. exact (errno_rw_core B TS W mem). Qed.

(* The ARx form (W_LLVMFuzzerTestOneInput_cut_x.v:214), top_x's ERRL_x, for every relation ARx. *)
Lemma errno_law_x_holds : forall B, TfibSyms B ->
  forall ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop,
  errno_law_x B ARx.
Proof. intros B TS ARx ly S Hp W mem md _. exact (errno_rw_core B TS W mem). Qed.

(* errno's four bytes lie in one of the instance's zero-shadow ranges (W_contract.v:314 azs), so every AR / ARx state
   reads shadow 0 there (W_contract.v:443 azs_range_addressable, W_contract_x.v:416 azs_range_addressable_x): AF0m's
   Tfib_zero_shadow range (0x5d8b60, 0x5fb000 - 0x5d8b60) holds [TFIB_ERRNO, TFIB_ERRNO + 4) = [0x5d93cc, 0x5d93d0).
   A fact of the start-up table alone; zz_HZS's script (W_LLVMFuzzerTestOneInput_addI.v:60-66). *)
Lemma errno_azs : forall B, TfibSyms B -> azs B (as_errno B) 4.
Proof.
  intros B TS. unfold azs. rewrite (@ts_zsh B TS), (@ts_errno B TS).
  exists (0x5d8b60, 0x5fb000 - 0x5d8b60). split.
  - unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
  - vm_compute. repeat split; first [reflexivity | discriminate | (let H := fresh in intro H; discriminate H)].
Qed.
End p.
