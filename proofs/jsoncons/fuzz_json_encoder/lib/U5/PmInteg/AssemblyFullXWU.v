(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The reader of the ubsan target at its U spec (PMXW.read_specxwU), assembled from the library walks of the ubsan
   image. Each input whose walk is not proved yet is one Section hypothesis:
   - MXU: malloc at its U spec (the heap instance proves it). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeap CutHeap2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5
  PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5 PmTopSpecsXW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopSpecs_u5 TopSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import TopSpecsW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Skel_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutDemo Require Pm6Memmove_u5 DemoAppend11_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Memcpy1_u5 VecPush_u5 StrPushBack_u5 AppendRange_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require SetEc_u5 PopState_u5 Parent_u5 DecU64_u5 DecstrToDouble_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require StrtodClosed_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require XsgetnW_u5 DetectW_u5 ChunkW_u5 PcdW_u5 SkipWsW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require SkipSpaceW_u5 BeginMemberW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require VbhObjRootXU VbhObjInobjXU VbhObjInarrXU VbhArrRootXU
  VbhArrInobjXU VbhArrInarrXU VbmOrXU VbmOnXU VbmArXU VbmAoXU VbmAaXU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require OpNewXU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require EncAppendU EncPushBackU EncNewLineU EncNewLine2U EncBeginScalarFU
  EncLiterals_u5 EncVisitNullU EncVisitBoolU EncVisitEndU EncVBeginTailOU EncVBeginTailAU EncVisitBeginU
  EncToCodepoint_u5 EncEscapeZU EncWriteBignumU EncWriteStringU EncVisitU64U EncVisitI64U EncVisitStrU EncVisitKeyU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require FromIntU64XU FromIntI64XU VisitDoubleXU WriteDoubleClosedXU Pm6DecstrGClosed_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FloatX Require SnprintfClosedX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseAsmW Require ParseAsmWU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require ReadXWU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ASMFXWU.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation SS := PML.STRTOD_SCR_V.
Abbreviation WD := PMES.WD_SCR_X.
Section A.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis MXU : malloc_u_spec L SCFG HI.

Lemma GUARD_ACQ : PMS.guard_acquire_spec L.
Proof. apply Skel_u5.SK.guard_acquire_ok; assumption. Qed.
Lemma GUARD_REL : PMS.guard_release_spec L.
Proof. apply Skel_u5.SK.guard_release_ok; assumption. Qed.
Lemma CXA_ATEXIT : PMS.cxa_atexit_spec L.
Proof. apply Skel_u5.SK.cxa_atexit_ok; assumption. Qed.
Lemma MEMMOVE : CH2.copy1_spec L Pm6Memmove_u5.MEMMOVE.
Proof. exact (Pm6Memmove_u5.memmove_copy1 L (PmLayout.ly_segs L LAY)). Qed.
Lemma MEMCPY : CH2.copy1_spec L Memcpy1_u5.MC1.MEMCPY.
Proof. exact (Memcpy1_u5.MC1.memcpy_copy1 L (PmLayout.ly_segs L LAY)). Qed.
Lemma VPUSH : PMS.vec_push_spec L HI.
Proof. apply VecPush_u5.VP.vec_push_ok; assumption. Qed.
Lemma SETEC : PMS.set_ec_spec L.
Proof. apply SetEc_u5.SetEcProof.set_ec_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL | exact CXA_ATEXIT]. Qed.
Lemma XSGETNW : TPSW.xsgetn_specw L.
Proof. apply XsgetnW_u5.XSW.xsgetn_okw; first [assumption | exact MEMMOVE]. Qed.
Lemma DETECTW : TPSW.detect_json_specw L.
Proof. apply DetectW_u5.DJW.detect_json_okw; assumption. Qed.
Lemma READCHUNKW : TPSW.read_chunk_specw L.
Proof. apply ChunkW_u5.CHKW.read_chunk_okw; first [assumption | exact XSGETNW | exact DETECTW | exact SETEC]. Qed.
Lemma PCDW : PMW.parser_check_done_specw L HI SS PMR.the_rm.
Proof. apply PcdW_u5.PCDW.parser_check_done_okw; first [assumption | exact SETEC]. Qed.
Lemma SKIPSPACEW : PMW.skip_space_specw L HI SS PMR.the_rm.
Proof. exact (SkipSpaceW_u5.SkipSpaceProof.skip_space_okw L HI HIok LAY FPM VPUSH). Qed.
(* Inputs of the parse-some walk that are proved. *)
Lemma POPSTATE : PMS.pop_state_spec L.
Proof. apply PopState_u5.PopStateProof.pop_state_ok; assumption. Qed.
Lemma PARENT : PMS.parent_spec L.
Proof. apply Parent_u5.ParentProof.parent_ok; first [assumption | exact SETEC]. Qed.
Lemma DECU64 : PMS.dec_u64_spec L.
Proof. apply DecU64_u5.DecU64Proof.dec_u64_ok; first [assumption | exact SETEC]. Qed.
Lemma STRTOD : PMS.strtod_spec L SS.
Proof. exact (StrtodClosed_u5.STC.strtod_closed L). Qed.
Lemma DECSTR : PMS.decstr_to_double_spec L SS.
Proof. apply DecstrToDouble_u5.DecstrProof.decstr_to_double_ok; first [assumption | exact STRTOD]. Qed.
Lemma STRPUSHBACK : PMS.str_push_back_spec L HI.
Proof. apply StrPushBack_u5.SPB.str_push_back_ok; first [assumption | exact MEMMOVE | exact MEMCPY]. Qed.
Lemma STPPEND : PMS.str_append_spec L HI.
Proof. apply DemoAppend11_u5.str_append_ok; first [assumption | exact MEMMOVE | exact MEMCPY]. Qed.
Lemma STPPENDRANGE : PMS.str_append_range_spec L HI.
Proof. apply AppendRange_u5.AR.str_append_range_ok; first [assumption | exact MEMMOVE | exact MEMCPY]. Qed.
Lemma BMEMBER : PMW.begin_member_specw L HI SS PMR.the_rm.
Proof. apply BeginMemberW_u5.BeginMemberProof.begin_member_okw; first [assumption | exact PARENT]. Qed.
(* The encoder visits the parse-some walk calls, at their U specs. *)
Lemma OPNEWXU : PMES.opnew_x_specU L HI.
Proof. apply OpNewXU.ONXU.opnew_x_okU; assumption. Qed.
Lemma APPENDXU : PMES.str_append_x_specU L HI.
Proof. apply EncAppendU.EAPU.str_append_x_okU; first [assumption | exact OPNEWXU]. Qed.
Lemma PUSHBXU : PMES.str_push_back_x_specU L HI.
Proof. apply EncPushBackU.EPBU.str_push_back_x_okU; first [assumption | exact OPNEWXU]. Qed.
Lemma NEWLINEU : PMES.new_line_specU L HI.
Proof. apply EncNewLineU.ENLU.new_line_ok; first [assumption | exact APPENDXU | exact PUSHBXU]. Qed.
Lemma BSCALARU : PMES.begin_scalar_specU L HI.
Proof. apply EncBeginScalarFU.EBFU.begin_scalar_ok; first [assumption | exact APPENDXU | exact NEWLINEU]. Qed.
Lemma LITNULL : PMES.null_literal_spec L.
Proof. apply EncLiterals_u5.ELTN.null_literal_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL]. Qed.
Lemma LITTRUE : PMES.true_literal_spec L.
Proof. apply EncLiterals_u5.ELTT.true_literal_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL]. Qed.
Lemma LITFALSE : PMES.false_literal_spec L.
Proof. apply EncLiterals_u5.ELTF.false_literal_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL]. Qed.
Lemma VNULLU : PMES.visit_null_specU L HI WD.
Proof. apply EncVisitNullU.EVNFU.visit_null_ok; first [assumption | exact BSCALARU | exact LITNULL | exact APPENDXU]. Qed.
Lemma VBOOLU : PMES.visit_bool_specU L HI WD.
Proof. apply EncVisitBoolU.EVBFU.visit_bool_ok; first [assumption | exact BSCALARU | exact LITTRUE | exact LITFALSE | exact APPENDXU]. Qed.
Lemma NEWLINE2U : PMES.new_line2_specU L HI.
Proof. apply EncNewLine2U.ENL2U.new_line2_ok; first [assumption | exact APPENDXU | exact PUSHBXU]. Qed.
Lemma VEOBJU : PMES.visit_end_object_specU L HI WD.
Proof. apply EncVisitEndU.EVEFU.visit_end_object_ok; first [assumption | exact NEWLINE2U | exact APPENDXU]. Qed.
Lemma VEARRU : PMES.visit_end_array_specU L HI WD.
Proof. apply EncVisitEndU.EVEFU.visit_end_array_ok; first [assumption | exact NEWLINE2U | exact APPENDXU]. Qed.
(* The begin visits: head, middle and tail parts for objects and arrays. *)
Lemma HEAD_OR : PMES2.head_obj_root_spec L HI.
Proof. apply VbhObjRootXU.VBH_OR.head_ok; assumption. Qed.
Lemma HEAD_OO : PMES2.head_obj_inobj_spec L HI.
Proof. apply VbhObjInobjXU.VBH_OO.head_ok; assumption. Qed.
Lemma HEAD_OA : PMES2.head_obj_inarr_spec L HI.
Proof. apply VbhObjInarrXU.VBH_OAU.head_ok; first [assumption | exact APPENDXU | exact NEWLINE2U]. Qed.
Lemma HEAD_AR : PMES2.head_arr_root_spec L HI.
Proof. apply VbhArrRootXU.VBH_AR.head_ok; assumption. Qed.
Lemma HEAD_AO : PMES2.head_arr_inobj_spec L HI.
Proof. apply VbhArrInobjXU.VBH_AO.head_ok; assumption. Qed.
Lemma HEAD_AA : PMES2.head_arr_inarr_spec L HI.
Proof. apply VbhArrInarrXU.VBH_AAU.head_ok; first [assumption | exact APPENDXU | exact NEWLINE2U]. Qed.
Lemma MID_OR : PMES2.mid_obj_root_spec L HI.
Proof. apply VbmOrXU.VBM_ORU.mid_ok; first [assumption | exact OPNEWXU]. Qed.
Lemma MID_ON : PMES2.mid_obj_nested_spec L HI.
Proof. apply VbmOnXU.VBM_ONU.mid_ok; first [assumption | exact OPNEWXU]. Qed.
Lemma MID_AR : PMES2.mid_arr_root_spec L HI.
Proof. apply VbmArXU.VBM_ARU.mid_ok; first [assumption | exact OPNEWXU]. Qed.
Lemma MID_AO : PMES2.mid_arr_inobj_spec L HI.
Proof. apply VbmAoXU.VBM_AOU.mid_ok; first [assumption | exact OPNEWXU]. Qed.
Lemma MID_AA : PMES2.mid_arr_inarr_spec L HI.
Proof. apply VbmAaXU.VBM_AAU.mid_ok; first [assumption | exact OPNEWXU]. Qed.
Lemma TAIL_O : PMES2.tail_obj_spec L HI.
Proof. apply EncVBeginTailOU.EVBTOU.tail_ok; first [assumption | exact APPENDXU]. Qed.
Lemma TAIL_A : PMES2.tail_arr_spec L HI.
Proof. apply EncVBeginTailAU.EVBTAU.tail_ok; first [assumption | exact APPENDXU]. Qed.
Lemma VBOBJU : PMES.visit_begin_object_specU L HI WD.
Proof.
  apply EncVisitBeginU.EVBFU.visit_begin_object_ok;
    first [assumption | exact HEAD_OR | exact HEAD_OO | exact HEAD_OA | exact HEAD_AR | exact HEAD_AO | exact HEAD_AA
          | exact MID_OR | exact MID_ON | exact MID_AR | exact MID_AO | exact MID_AA | exact TAIL_O | exact TAIL_A].
Qed.
Lemma VBARRU : PMES.visit_begin_array_specU L HI WD.
Proof.
  apply EncVisitBeginU.EVBFU.visit_begin_array_ok;
    first [assumption | exact HEAD_OR | exact HEAD_OO | exact HEAD_OA | exact HEAD_AR | exact HEAD_AO | exact HEAD_AA
          | exact MID_OR | exact MID_ON | exact MID_AR | exact MID_AO | exact MID_AA | exact TAIL_O | exact TAIL_A].
Qed.
(* The scalar and string visits. *)
Lemma FROMU : PMES.from_integer_u64_x_specU L HI.
Proof. apply FromIntU64XU.FIUU.from_integer_u64_x_ok; first [assumption | exact PUSHBXU]. Qed.
Lemma FROMI : PMES.from_integer_i64_x_specU L HI.
Proof. apply FromIntI64XU.FIIU.from_integer_i64_x_ok; first [assumption | exact PUSHBXU]. Qed.
Lemma VU64U : PMES.visit_uint64_specU L HI WD.
Proof. apply EncVisitU64U.EVU64FU.visit_uint64_ok; first [assumption | exact BSCALARU | exact FROMU]. Qed.
Lemma VI64U : PMES.visit_int64_specU L HI WD.
Proof. apply EncVisitI64U.EVI64FU.visit_int64_ok; first [assumption | exact BSCALARU | exact FROMI]. Qed.
Lemma TOCP : PMES.to_codepoint_spec L.
Proof. apply EncToCodepoint_u5.ETC.to_codepoint_ok; assumption. Qed.
Lemma ESCAPEU : PMES.escape_string_specU L HI.
Proof. apply EncEscapeZU.EEZU.escape_string_ok; first [assumption | exact PUSHBXU | exact TOCP]. Qed.
Lemma WBIGNUMU : PMES.write_bignum_specU L HI.
Proof. apply EncWriteBignumU.EWBU.write_bignum_ok; first [assumption | exact APPENDXU]. Qed.
Lemma WSTRINGU : PMES.write_string_specU L HI.
Proof. apply EncWriteStringU.EWSU.write_string_ok; first [assumption | exact PUSHBXU | exact APPENDXU | exact ESCAPEU | exact WBIGNUMU]. Qed.
Lemma VSTRU : PMES.visit_string_specU L HI WD.
Proof. apply EncVisitStrU.EVStrFU.visit_string_ok; first [assumption | exact BSCALARU | exact WSTRINGU]. Qed.
Lemma WDOUBLE : PMES.write_double_x_specU L HI WD.
Proof.
  apply WriteDoubleClosedXU.WDCU.write_double_closed;
    first [assumption | exact PUSHBXU | exact (SnprintfClosedX_u5.snprintf_g_closed L)
          | apply Pm6DecstrGClosed_u5.DSGC.decstr_to_double_g_closed; assumption].
Qed.
Lemma VDBLU : PMES.visit_double_specU L HI WD.
Proof. apply VisitDoubleXU.EVDFU.visit_double_ok; first [assumption | exact BSCALARU | exact LITNULL | exact APPENDXU | exact WDOUBLE]. Qed.
Lemma VKEYU : PMES.visit_key_specU L HI WD.
Proof. apply EncVisitKeyU.EVKU.visit_key_ok; first [assumption | exact NEWLINEU | exact PUSHBXU | exact APPENDXU | exact ESCAPEU]. Qed.
Lemma PSOMEWU : PMW.parse_some_specwU L HI SS WD PMR.the_rm.
Proof.
  apply ParseAsmWU.parse_some_okw_libU;
    first [assumption | exact SETEC | exact POPSTATE | exact PARENT | exact VPUSH | exact STRPUSHBACK | exact STPPEND
          | exact STPPENDRANGE | exact DECU64 | exact DECSTR | exact VNULLU | exact VBOOLU | exact VBOBJU | exact VBARRU
          | exact VEOBJU | exact VEARRU | exact VU64U | exact VI64U | exact VSTRU | exact VDBLU | exact VKEYU].
Qed.
Lemma SKIPWSW : PMW.skip_whitespace_specw L HI SS PMR.the_rm.
Proof. apply SkipWsW_u5.SWW.skip_whitespace_okw; first [assumption | exact SKIPSPACEW | exact POPSTATE]. Qed.

Theorem read_okU : PMXW.read_specxwU L HI SS WD.
Proof. exact (@ReadXWU.RDXWU.read_xw_okU SCFG_P L HI SS WD HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC READCHUNKW). Qed.
End A.
End ASMFXWU.
