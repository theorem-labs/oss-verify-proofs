(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.StreamExec — extra value facts and syscall post-state collapses
      needed by the streamcat binaries.

    PURELY ADDITIVE over [Common.PropExec] / [Common.CatExec] /
    [Common.SeqExec]. Image-INDEPENDENT.

    Notes:
    - [step_bgeu_ft]/[step_bgeu_tk] live in PropExec (instances of the
      generic branch pipeline; the taken variant has no [align4]
      hypothesis). This file does not restate them.
    - [c_ltu_small] also lives in PropExec, as the hypothesis-free
      definitional restatement [c_ltu x y = bv_ltu x y].
    - The [write_to_mem] frame/read-back lemmas below are thin corollaries
      of the CatExec/SeqExec [wbytes] theory (the interpreter's byte
      writer IS [wbytes], [CatExec.write_to_mem_wbytes]); the wrapping
      [bv] address walk gives them the CatExec-standard no-overflow
      hypotheses, trivially discharged downstream. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import ExitSim PropExec CatSim CatExec SeqExec.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ================================================================= *)
(* New value/condition shapes                                        *)
(* ================================================================= *)

(* v_addiw, c_ltu, step_addiw, step_bgeu_ft/tk, and c_ltu_small all live
   in PropExec; see the header note. *)

(* ================================================================= *)
(* Value facts used by the streamcat loops                            *)
(* ================================================================= *)

Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.

(** [blez]/[bge x0,a0] outcomes on the read return value. *)
Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

(* [c_lts_0_pos] lives in PropExec.  Do not restate it here: a second
   lemma of that name would make [apply c_lts_0_pos] mean different
   things in different files, depending on Require order. *)

(* ================================================================= *)
(* Round-trip: bytes just written to memory read straight back.       *)
(* ================================================================= *)

(** Below the written region, [write_to_mem] leaves memory unchanged.
    The no-overflow hypothesis [buf + length data <= 2^64] is needed
    because the write walk is a wrapping [bv] add — mirrors
    [CatExec.wbytes_below]. *)
Lemma write_to_mem_below : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  (bv_unsigned a < bv_unsigned buf)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Hnw Ha.
  rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

(** Outside [buf, buf + length data), [write_to_mem] leaves memory alone
    (above-side companion of [write_to_mem_below]; no extra no-overflow
    needed — [a < 2^64] already caps the walk). *)
Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Ha.
  rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

(** [rdn] reads through a disjoint [write_to_mem].  The two no-overflow
    hypotheses are the standard [rdn_ext]/[wbytes_below] ones. *)
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
  intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply write_to_mem_above. lia.
  - apply write_to_mem_below; [exact Hnb | lia].
Qed.

(** [rdn] reads back exactly the bytes just written by [write_to_mem]
    (no-overflow hypothesis, as in [SeqExec.rdn_wbytes_hit]). *)
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
  intros segs data mem buf Hnw.
  rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

(* ================================================================= *)
(* mkst-normal-form bridges for the syscall post-states.              *)
(* ================================================================= *)

(** [advance_past_svc] of [apply_effect] with a single-buffer write effect
    (the read post-state): sets x10 to the return value, advances pc by 4,
    clears svc, and writes [data] into [ms_mem] at [buf].  The input
    record carries the (post-ecall) [ms_resv := None]. *)
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(** The same bridge for the canonical [delivered_writes] shape (see
    Specs.v): a zero-byte delivery carries no write entry, and
    [write_to_mem] of [] is the identity, so both shapes normalize to
    the same [mkst]. *)
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  destruct data as [|b rest]; [|apply adv_apply_write].
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes
       delivered_writes write_to_mem].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.
End WithFP1.
