(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncNewLineXA EncNewLineZXA EncNewLine16XA EncNewLineZ16XA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ENLFA.
Import PMES.
Definition PC_NEW_LINE : Z := 763924.     (* [comment removed for export] *)

Section NewLine.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable CL : Z.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xasan CL 1040708.          (* [comment removed for export] *)
Hypothesis PUSHB_OK : PMESA.str_push_back_x_specA L ar HI CL 1041292.                        (* [comment removed for export] *)

Theorem new_line_ok : PMESA.new_line_specA L ar HI PMLA.C_xasan PMESA.EC_xasan CL PC_NEW_LINE.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  assert (D0 : 0 <= depth (g_es g)) by (unfold depth; clear; lia).
  assert (PAR : sp mod 32 = 0 \/ sp mod 32 = 16).
  { destruct Hstk as (S1 & _). clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D16. pose proof (Z_div_mod_eq_full sp 32) as D32.
    pose proof (Z.mod_pos_bound sp 32 ltac:(lia)) as B32. lia. }
  destruct (Z.eq_dec (depth (g_es g)) 0) as [Hd0|Hd1]; destruct PAR as [P0|P16].
  - exact (new_line_zero0_ok L ar C HI HIok LAY FPM CL APPEND_OK LBo FF LK cr A sp r V S2 kx bx g Hd0 P0 fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont).
  - exact (new_line_zero16_ok L ar C HI HIok LAY FPM CL APPEND_OK LBo FF LK cr A sp r V S2 kx bx g Hd0 P16 fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont).
  - exact (new_line_pos0_ok L ar C HI HIok LAY FPM CL APPEND_OK PUSHB_OK LBo FF LK cr A sp r V S2 kx bx g ltac:(clear - D0 Hd1; lia) P0 fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont).
  - exact (new_line_pos16_ok L ar C HI HIok LAY FPM CL APPEND_OK PUSHB_OK LBo FF LK cr A sp r V S2 kx bx g ltac:(clear - D0 Hd1; lia) P16 fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont).
Qed.
End NewLine.
End ENLFA.
Print Assumptions ENLFA.new_line_ok.
