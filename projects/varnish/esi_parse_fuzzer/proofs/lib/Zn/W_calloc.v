(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux W_ge3a6 W_al5bs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Definition calloc_to_malloc_post (sp gp tp t0 t1 t2 s0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s1 j0 : word) (n : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 m1,
    ms' = MS (mkR (wz 0x2313c) (wz (bv_unsigned sp - 32)) gp tp t0 t1 t2 s0 (wz n) (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x23364) fc None m1 (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ rw_cells rsegs m1 (bv_unsigned sp - 32) [C8 j0; C8 s1; C8 s0; C8 ra].

Lemma calloc_to_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (j0 j1 j2 j3 : word) (cnt sz : Z),
  bv_unsigned a0 = cnt -> bv_unsigned a1 = sz -> cnt * sz < 2^64 ->
  32 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp - 32) [C8 j0; C8 j1; C8 j2; C8 j3] -> mem_inv rsegs m ->
  evt rsegs (calloc_to_malloc_post sp gp tp t0 t1 t2 s0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s1 j0 (cnt * sz) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 calloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until sz. intros HA0 HA1 PR SPLO FR MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in FR by lia.
  unfold calloc_entry.
  step. step. step. step.
  step. if_cases K; zify_cond K.
  all: cycle 1.
  (* [comment removed for export] *)
  1: step; replace ((bv_unsigned a1 * bv_unsigned a0) ≫ 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; nia);
     step; if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
  (* [comment removed for export] *)
  all: step; step; step; rewrite HA0, HA1; replace (sz * cnt) with (cnt * sz) by lia;
       replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in * by lia;
       apply evt_done; unfold calloc_to_malloc_post; eexists _, _;
       (split; [reflexivity| split; [exact MU| split; [exact WM| split; [exact MI| exact FR]]]]).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition calloc_null_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR RA (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 S0 S1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc RA) fc None m (seg_rom rsegs).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition calloc_to_allzerop_post (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR (wz 0x2321c) sp gp tp t0 t1 t2 (wz p) s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz allzerop_entry) fc None m (seg_rom rsegs).

Lemma calloc_after_malloc_ptr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (p : Z),
  bv_unsigned a0 = p -> p <> 0 ->
  rw_cells rsegs m MALLOC_REPLACED [C4 (wz 0)] ->
  evt rsegs (calloc_to_allzerop_post sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2313c) fc None m (seg_rom rsegs)).
Proof.
  intros until p. intros HA0 PNZ MRP.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  assert (EA0 : a0 = wz p) by (rewrite <- HA0; symmetry; apply Z_to_bv_bv_unsigned).
  unfold MALLOC_REPLACED in MRP.
  step. if_cases K; zify_cond K. { exfalso. lia. }
  step. step. step. rewrite ?sx32_wz by lia. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. lia. }
  step. step. rewrite EA0.
  apply evt_done. unfold calloc_to_allzerop_post, allzerop_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition calloc_to_memset_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 : word) (p n : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR RA (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 S0 S1 (wz p) (wz 0) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x2b3f8) (* [comment removed for export] *) fc None m (seg_rom rsegs).

Lemma calloc_after_allzerop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (j0 RA S0 S1 : word) (p n : Z),
  bv_unsigned a0 = 0 -> bv_unsigned s0 = p -> bv_unsigned s1 = n -> 0 <= n < 4096 -> bv_unsigned sp + 32 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned sp) [C8 j0; C8 S1; C8 S0; C8 RA] ->
  evt rsegs (calloc_to_memset_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 p n F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2321c) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros HA0 HS0 HS1 NR SPHI FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ES0 : s0 = wz p) by (rewrite <- HS0; symmetry; apply Z_to_bv_bv_unsigned).
  assert (ES1 : s1 = wz n) by (rewrite <- HS1; symmetry; apply Z_to_bv_bv_unsigned).
  step. if_cases K; zify_cond K. { exfalso. lia. }
  step. step. rewrite HS1. replace (n ≫ 12) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  step. step. step. step. step. step. step. step. rewrite ES0, ES1.
  apply evt_done. unfold calloc_to_memset_post. reflexivity.
Qed.

(* [comment removed for export] *)
Definition calloc_ret_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 : word) (p : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR RA (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 S0 S1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc RA) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
