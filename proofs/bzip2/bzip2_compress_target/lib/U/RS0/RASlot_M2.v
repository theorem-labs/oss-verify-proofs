(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W9 ASlot_I ASlot_M0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocKit_A2 RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4 RASlot_W9.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_entry MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W12.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocKit_A2 RMalloc_fp RF_malloc_entry. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RASlot_W12.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W12.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RMallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.
 Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma rag_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (rt1_regs sc (Z_to_bv 64 0x2a3fc) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
                   (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a3e4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
  pose proof (size_class_range sc SC) as SZR.
  step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
  pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (69272 + 2 * sc) with (69272 + sc * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  step. apply evt_done. reflexivity.
Qed.
End AG1.

(* [comment removed for export] *)
Lemma rag_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
  0 <= gm < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if gm =? 0 then 0x2aa64 else 0x2a408)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a3fc) fc None m (seg_rom rsegs)).
Proof.
  intros until gm. intros GR MI.
  step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
  - replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.


(* [comment removed for export] *)
Lemma rnest_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' a3' a4',
      ms' = MS (mkR (Z_to_bv 64 0x2a5e4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a514) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI.
  assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
  set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
  pose proof rstc_q_eq as STC. fold q in STC.
  unfold RSIZE_CLASSES, ralloc_slot_entry in *.
  (* [comment removed for export] *)
  assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
    evt rsegs (fun ms' => exists a2'' a3'' a4'',
      ms' = MS (mkR (Z_to_bv 64 0x2a5e4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 69272) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 172548) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 69272) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a5d8) fc None m (seg_rom rsegs))).
  { intros a0' a2' a3' jv ->.
    pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
    step. rewrite sextw_small by lia. step. step.
    apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
  step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
  - (* [comment removed for export] *)
    apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (unfold n' in K; nia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    cps_pose (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
    assert (K13 : 3 <= k <= 12).
    { unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (69272 + (i + 1) * 2) with (69272 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt rsegs (fun ms' => exists a2'' a3'' a4'',
        ms' = MS (mkR (Z_to_bv 64 0x2a5e4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 69272) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 172548) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 69240) (Z_to_bv 64 q) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 69272) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2a5bc) fc None m (seg_rom rsegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (69272 + i1 * 2) with (69272 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.
(* [comment removed for export] *)
Lemma rnest_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
  -1 <= idx < 32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if idx =? -1 then 0x2a65c else 0x2a5e8)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a5e4) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros IR MI.
  step. if_cases K; zify_cond K.
  - replace (idx =? -1) with true.
    2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
        change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
    apply evt_done. reflexivity.
  - replace (idx =? -1) with false.
    2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
    apply evt_done. reflexivity.
Qed.

End ACeilS1.
End RASlot_W12.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
Module RASlot_W19.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  evt rsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2aa64) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cps_pose MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  bz_ceil; unfold RSSP_GUARD, rta_frame in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.

End ACeilS1.
End RASlot_W19.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W18.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
Module RASlot_M0.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W18 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.



(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rgmf_of_facts st LB sc g :
  RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
  (intros F; cps_intros (MEM & NX & PV); intros GSC SCR). assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  cps_destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
  cps_pose (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. cps_destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
  - intros i Hi Hb. cps_destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  cps_pose (lf_lists _ LF) as (L1 & L2 & L3).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. cps_destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. cps_destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    cps_destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. cps_destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    cps_destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - cps_pose (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
  0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x13000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x13000 \/ 0x32000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x32000 \/ 0x33000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x33000 \/ 0x66000 <= r_base r).
Proof.
  intros Hr. cps_destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
  pose proof MR as (WF & _). cps_pose WF as (_ & WR & _).
  cps_destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). cps_pose (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. bz_ceil. lia.
Qed.

Lemma rmalloc_fp_cases_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
  intros (WF2 & _) H. cps_pose WF2 as (_ & WR2 & _).
  bz_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. cps_destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - right. cps_destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - right. cps_destruct (rst0_region (fst b) r Hr) as (_ & RC & _). bz_ceil. lia.
  - right. cps_destruct (rst0_region (fst b) r Hr) as (_ & RC & _). bz_ceil. lia.
  - right. bz_ceil. lia.
Qed.

Lemma rmalloc_fp_image_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
  0x10000 <= a < 0x66000 -> RCTX <= a < RCTX + 928 \/ 0x4413c <= a < 0x44140.
Proof.
  intros (WF2 & _) H CLO HA. cps_pose WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
  bz_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - exfalso. cps_destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. cps_destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. cps_destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. cps_destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
  rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
    cps_destruct AUX as (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). bz_ceil. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL in Ha.
    destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
  rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells rsegs m1 A cs ->
  sp <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
  intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End ACeilS1.
End RASlot_M0.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.RASlot_W12 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.RASlot_W19 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.RASlot_M0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv4.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

(* [comment removed for export] *)
Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
  mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Definition rHAG_stmt : Prop :=
  forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
  IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
  am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
  rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
  rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
  brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  rimplT o (ag_body f sc req k bail st2 mm) s' Q
    (MS (rag_regs (Z_to_bv 64 0x2a3fc) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
        F (Z_to_bv 64 0x2a408) fc None m3 (seg_rom rsegs)).
Hypothesis HAG : rHAG_stmt.

Lemma rerrno_lit2 : errno_addr tp = 0x4413c.
Proof. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  (intros REL; cps_intros (ar & arr & kk & Ha & Hk & ->)). pose proof MR as (WF & _). cps_pose WF as (_ & _ & _ & WA & _).
  cps_destruct (WA ar arr Ha) as (r & Hr & _). cps_destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

(* [comment removed for export] *)
Lemma rta_fp_malloc_fp stE mE a :
  rmrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
  rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 stE lo (bv_unsigned sp) a.
Proof.
  intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - left. left. exact X.
  - left. right. right. left. exact X.
  - left. do 3 right.
    pose proof (AREAS q MSq) as MSq'.
    cps_destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
    exists rid0, r0. split; [exact H0|]. split; [exact K0|].
    rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
  - do 3 right. left. pose proof MR as (WF & _).
    cps_destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct ER as [_ EG EGR _ _ _ _ _].
    destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
    exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
    rewrite Cb in Xq. lia.
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_image a : 0x10000 <= a < 0x66000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
  intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - bz_ceil. lia.
  - exact (Hc X).
  - cps_destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
  - pose proof MR as (WF & _). cps_destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
    cps_destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
    pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
  pose proof (RAS_STACK_ge sc) as ASG. bz_ceil.
  intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - unfold RCTX in X. lia.
  - cps_destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
  - pose proof MR as (WF & _). cps_destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). bz_ceil. lia.
Qed.

(* [comment removed for export] *)
Lemma runk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { cps_intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_inband rid r off :
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
  ~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
  intros Hr Hk Ho NG. pose proof MR as (WF & _). cps_pose WF as (_ & WR & DJ & _).
  cps_destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). bz_ceil.
  intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - cps_destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
  - cps_destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
  - cps_destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct (N.eq_dec (fst bq) rid) as [E|NE].
    + apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

Lemma rag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  rmrep st1 m1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
  rimplT o (as_grp full_lay f sc req k bail st1) s Q
    (MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a3e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. bz_ceil.
  pose proof rerrno_lit2 as EA.
  pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). cps_pose WF as (RS & WR & DJ & WA & WG).
  rewrite (as_grp_eq f sc req k bail st1).
  riprefixT. unfold rag_regs.
  eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
  cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
  assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
  assert (BL1 : brk_link_ps st1 s).
  { unfold brk_link_ps in *. unfold ctx in *. cps_destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
    unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
  assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
  { apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| bz_ceil; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
    - intros a Ha. apply rta_fp_not_high. exact Ha.
    - intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
  assert (ERR2 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
  eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
    [ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
    | rewrite unsigned_lit by lia; exact ST1 | exact CLO
    | rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
  intros st2 mo s' ms' PO BL2 LF.
  cps_destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL).
  rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
  replace (ret_pc (Z_to_bv 64 0x2a3fc)) with (Z_to_bv 64 0x2a3fc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof MR3 as (WF3 & _). cps_pose WF3 as (RS0 & WR3 & DJ3 & _).
  (* [comment removed for export] *)
  assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x66000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x4413c <= a < 0x44140)) ->
            ~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
  { intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
    - lia.
    - rewrite unsigned_lit in X by lia. lia.
    - unfold RCTX in *. lia.
    - cps_destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). bz_ceil.
      cps_pose (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
    - destruct X as [XC XF]. bz_ceil.
      pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk)).
  { eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }
  (* [comment removed for export] *)
  assert (REL02 : mrel st st2).
  { split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
    intros rid r Hr. rewrite <- REG1 in Hr. cps_destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
  assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
  { (intros q; cps_intros (ar & arr & kk & Ha & Hk & E)). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
    exists ar, arr', kk. auto. }
  assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
    - eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
      + left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
      + do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
        * rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
        * intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. cps_destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }
  (* [comment removed for export] *)
  assert (UA3 : unk_agree st2 o m3).
  { eapply (runk_agree_keep st2 m3).
    - rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
    - intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
      + cps_destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      + exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
    - intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
    - intros rid r off h Hr Hk Ho Hc NG.
      cps_destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). bz_ceil.
      transitivity (m1 (wa (r_base r + off))).
      + refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
        * lia.
        * rewrite unsigned_lit in X by lia. cps_destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
          specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
        * cps_destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
        * assert (Hr2 : (s_regions st2) !! rid = Some r).
          { rewrite <- REG1 in Hr. cps_destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
          assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
          pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
        * rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
      + refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
  destruct mo as [mm|].
  - (* [comment removed for export] *)
    destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
    cps_pose (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [bz_ceil; lia| exact MI3]. }
    cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done.
    eapply (HAG st1 st2 mm m3 s'); try eassumption.
    + eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
    + eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
    + eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
    + eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
  - (* [comment removed for export] *)
    cbn iota.
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
    cbv beta. intros ms' ->. cbn [Z.eqb].
    eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
    cbv beta. (intros ms'; cps_intros (a1x & a2x & -> & ST4)). apply evt_done.
    apply HK. unfold ras_post2.
    do 14 eexists. exists m3, errv3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
    split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
    split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
    split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split. { rewrite (amr_counter _ _ _ REL). unfold ctx. cps_destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
             pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
    left. reflexivity.
Qed.
End LEVEL.

End ACeilS1.
