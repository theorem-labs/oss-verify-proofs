(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import AfterValueW_u5 BeginArrayWU BeginMemberW_u5 BeginObjectWU EndArrayWU EndFractionValueWU EndIntegerValueWU EndObjectWU EndStringValueWU ParseFalseWU ParseNullWU ParseTrueWU SkipSpaceW_u5 ValidateW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseNumberWU ParseSomeZU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseSW Require Import ParseStringWU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Asm.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
(* [comment removed for export] *)
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis PUSHB_OK : PMS.str_push_back_spec L HI.
Hypothesis APPEND_OK : PMS.str_append_spec L HI.
Hypothesis APPR_OK : PMS.str_append_range_spec L HI.
Hypothesis DECU64_OK : PMS.dec_u64_spec L.
Hypothesis DECSTR_OK : PMS.decstr_to_double_spec L PML.STRTOD_SCR_V.
(* [comment removed for export] *)
Hypothesis VNULL : PMES.visit_null_specU L HI PMES.WD_SCR_X.
Hypothesis VBOOL : PMES.visit_bool_specU L HI PMES.WD_SCR_X.
Hypothesis VBOBJ : PMES.visit_begin_object_specU L HI PMES.WD_SCR_X.
Hypothesis VBARR : PMES.visit_begin_array_specU L HI PMES.WD_SCR_X.
Hypothesis VEOBJ : PMES.visit_end_object_specU L HI PMES.WD_SCR_X.
Hypothesis VEARR : PMES.visit_end_array_specU L HI PMES.WD_SCR_X.
Hypothesis VUINT64 : PMES.visit_uint64_specU L HI PMES.WD_SCR_X.
Hypothesis VINT64 : PMES.visit_int64_specU L HI PMES.WD_SCR_X.
Hypothesis VDOUBLE : PMES.visit_double_specU L HI PMES.WD_SCR_X.
Hypothesis VSTRING : PMES.visit_string_specU L HI PMES.WD_SCR_X.
Hypothesis VKEY : PMES.visit_key_specU L HI PMES.WD_SCR_X.

Theorem parse_some_okw_libU : PMW.parse_some_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Proof.
  pose proof (ValidateProof.validate_okw L FPM) as VA.
  pose proof (EndStringValueProofU.end_string_value_okw L HI HIok LAY FPM VA PARENT_OK POP_OK SETEC_OK VKEY VSTRING) as ESV.
  pose proof (AfterValueProof.after_value_okw L HI HIok LAY FPM PARENT_OK) as AV.
  pose proof (EndIntegerValueProofU.end_integer_value_okw L HI HIok LAY FPM DECU64_OK AV VUINT64 VINT64 VSTRING) as EI.
  pose proof (EndFractionValueProofU.end_fraction_value_okw L HI HIok LAY FPM DECSTR_OK AV VDOUBLE VSTRING) as EF.
  exact (PSZU.parse_some_okw L HI HIok LAY FPM SETEC_OK POP_OK PARENT_OK VECPUSH_OK PUSHB_OK
           (SkipSpaceProof.skip_space_okw L HI HIok LAY FPM VECPUSH_OK)
           (BeginMemberProof.begin_member_okw L HI HIok LAY FPM PARENT_OK)
           (BeginObjectProofU.begin_object_okw L HI HIok LAY FPM VECPUSH_OK SETEC_OK VBOBJ)
           (BeginArrayProofU.begin_array_okw L HI HIok LAY FPM VECPUSH_OK SETEC_OK VBARR)
           (EndObjectProofU.end_object_okw L HI HIok LAY FPM POP_OK SETEC_OK VEOBJ)
           (EndArrayProofU.end_array_okw L HI HIok LAY FPM POP_OK SETEC_OK VEARR)
           (ParseNullProofU.parse_null_okw L HI HIok LAY FPM SETEC_OK VNULL)
           (ParseTrueProofU.parse_true_okw L HI HIok LAY FPM SETEC_OK VBOOL)
           (ParseFalseProofU.parse_false_okw L HI HIok LAY FPM SETEC_OK VBOOL)
           (ParseStringWU.parse_string_okwU L HI HIok LAY FPM PUSHB_OK APPEND_OK SETEC_OK ESV)
           (PNWU.parse_number_okwU L HI HIok LAY FPM APPR_OK SETEC_OK EI EF)
           EI EF
           VNULL VBOOL).
Qed.
End Asm.
Print Assumptions parse_some_okw_libU.
