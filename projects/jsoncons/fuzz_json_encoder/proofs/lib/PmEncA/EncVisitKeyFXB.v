(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncVisitKey0XB EncVisitKeyKXB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVKFA.
Import PMES.
Section VisitKey.
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
Hypothesis ACC_COMMA : PMESA.img_aacc HI 0x24b7c 2.
Hypothesis ACC_COLON : PMESA.img_aacc HI 0x24b74 2.
Hypothesis FOOTXC : forall a, PMLA.in_footx PMLA.C_xboth a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis NEWLINE2_OK : PMESA.new_line2_specA L ar HI PMLA.C_xboth CL 0xbc29c.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xboth CL 0x101abc.
Hypothesis PUSHB_OK : PMESA.str_push_back_x_specA L ar HI CL 0x101d04.
Hypothesis ESCAPE_OK : PMESA.escape_string_specA L ar HI PMLA.C_xboth CL 0xbfd34.

Lemma es_cases : forall es : estate, es = [] \/ (exists c0 r0, es = c0 :: r0).
Proof. intros [|c0 r0]; [left; reflexivity | right; exists c0, r0; reflexivity]. Qed.

Theorem visit_key_ok : PMESA.visit_key_specA L ar HI PMLA.C_xboth PMESA.EC_xboth 12800 CL PMESA.PC_VISIT_KEY_xboth.
Proof.
  intros bs sv LBo FF LK cr A sp r V S2 kx bx g.
  destruct (es_cases (g_es g)) as [Hes|(c0 & r0 & Hes)].
  - unfold PMSA.cps_asan. intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (_ & _ & _ & _ & _ & HG & _) Hcont. exfalso. rewrite Hes in HG. exact (HG eq_refl).
  - destruct (Z.eq_dec (ec_count c0) 0) as [Hc|Hc].
    + exact (visit_key_cnt0_ok L ar C HI HIok LAY FPM CL ACC_COLON FOOTXC NEWLINE2_OK APPEND_OK PUSHB_OK ESCAPE_OK bs sv LBo FF LK cr A sp r V S2 kx bx g c0 r0 Hes Hc).
    + exact (visit_key_cntk_ok L ar C HI HIok LAY FPM CL ACC_COMMA ACC_COLON FOOTXC NEWLINE2_OK APPEND_OK PUSHB_OK ESCAPE_OK bs sv LBo FF LK cr A sp r V S2 kx bx g c0 r0 Hes Hc).
Qed.
End VisitKey.
End EVKFA.
Print Assumptions EVKFA.visit_key_ok.
