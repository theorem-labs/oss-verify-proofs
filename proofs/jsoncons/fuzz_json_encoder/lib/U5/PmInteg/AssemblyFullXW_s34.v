(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core PmLibDefs PmLibSpecs PmLayout
  PmEncSpecs PmEncSpecs2 PmLibSpecsX HeapIfaceX PmFloatXSpecs
  PmLibSpecsW PmRef PmTopSpecsXW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeap CutHeap2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require Import TopSpecs TopSpecs2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require Import TopSpecsW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require Skel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm6Island.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require TopLeaves.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require IosbDtor.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutDemo Require Pm6Memmove.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require Memcpy1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require OpNew.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require OpDel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require StrInit.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require StrReserve.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require VecReserve.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require VecPush.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require StrPushBack.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutDemo Require DemoAppend11.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require AppendRange.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require SetEc.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require PopState.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Parent.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require DecU64.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require ParserDtor.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require SourceDtor.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require IosbInit.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require SbufCtor.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require IssCtor.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require ReaderCtor.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require StrtodClosed.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require DecstrToDouble.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmGrow Require OpNewX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncPushBack.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncAppend.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FloatX Require SnprintfClosedX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Pm6DecstrGClosed.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require FromIntU64X.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require FromIntI64X.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require WriteDoubleClosedX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncNewLine.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncNewLine2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncBeginScalarF.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncWriteBignum.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncToCodepoint.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncEscapeZ.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncWriteString.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncLiterals.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbhObjRootX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbhObjInobjX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbhObjInarrX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbhArrRootX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbhArrInobjX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbhArrInarrX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbmOrX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbmOnX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbmArX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbmAoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VbmAaX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVBeginTailO.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVBeginTailA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitBegin.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitEnd.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitNull.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitBool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitU64.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitI64.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require VisitDoubleX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitKey.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require EncVisitStr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require EncCtorX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require EncDtorX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require XsgetnW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require DetectW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require ChunkW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require PcdW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmallW Require SkipSpaceW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require SkipWsW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseAsmW Require ParseAsmW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopW Require ReadXW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require HarnessXW_s34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ASMFXW16.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation SS := PML.STRTOD_SCR_V.
Abbreviation WD := PMES.WD_SCR_X.
Abbreviation PHI := (PMXW.phi_lim (2 ^ 34)).
Section A.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis MX : HeapIfaceX.malloc_x_spec L SCFG HI.
(* [comment removed for export] *)
Hypothesis HFIT : forall LB cr M VM A n, hi_heap HI LB cr M VM -> In (A, n) LB -> n <= 2 ^ 27 \/ n <= 2 ^ 34.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma GUARD_ACQ : PMS.guard_acquire_spec L.
Proof. apply Skel.SK.guard_acquire_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma GUARD_REL : PMS.guard_release_spec L.
Proof. apply Skel.SK.guard_release_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma CXA_ATEXIT : PMS.cxa_atexit_spec L.
Proof. apply Skel.SK.cxa_atexit_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma SYSCAT : PMS.system_category_spec L.
Proof. apply Skel.SK.system_category_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma LOCLATER : PMS.locale_ctor_later_spec L.
Proof. apply Skel.SK.locale_ctor_later_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma LOCFIRST : PMS.locale_ctor_first_spec L.
Proof. apply Pm6Island.ISL0.locale_ctor_first_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma LOCDTOR : PMS.locale_dtor_spec L.
Proof. apply TopLeaves.TL.locale_dtor_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma ISTRDTOR : TPS.istream_dtor_spec L.
Proof. apply TopLeaves.TL.istream_dtor_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma IOSBDTOR : TPS.iosb_dtor_spec L.
Proof. apply (IosbDtor.ID.iosb_dtor_ok FPM L HI HIok LAY); exact LOCDTOR. Qed.
(* [comment removed for export] *)
Lemma MEMMOVE : CH2.copy1_spec L 0xbaa60.
Proof. exact (Pm6Memmove.memmove_copy1 L (PmLayout.ly_segs L LAY)). Qed.
(* [comment removed for export] *)
Lemma MEMCPY : CH2.copy1_spec L 0xba65c.
Proof. exact (Memcpy1.MC1.memcpy_copy1 L (PmLayout.ly_segs L LAY)). Qed.
(* [comment removed for export] *)
Lemma OPNEW : PMS.opnew_spec L HI.
Proof. apply OpNew.ON.opnew_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma OPDELS : PMS.opdel_sized_spec L HI.
Proof. apply OpDel.OD.opdel_sized_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma STRINIT : PMS.strinit_spec L HI.
Proof. apply StrInit.SI.strinit_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma STRRSV : PMS.str_reserve_spec L HI.
Proof. apply StrReserve.SRV.str_reserve_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma VRSV : PMS.vec_reserve_spec L HI.
Proof. apply VecReserve.VR.vec_reserve_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma VPUSH : PMS.vec_push_spec L HI.
Proof. apply VecPush.VP.vec_push_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma STRPUSHBACK : PMS.str_push_back_spec L HI.
Proof. apply StrPushBack.SPB.str_push_back_ok; first [assumption | exact MEMMOVE | exact MEMCPY]. Qed.
(* [comment removed for export] *)
Lemma STRAPPEND : PMS.str_append_spec L HI.
Proof. apply DemoAppend11.str_append_ok; first [assumption | exact MEMMOVE | exact MEMCPY]. Qed.
(* [comment removed for export] *)
Lemma STRAPPENDRANGE : PMS.str_append_range_spec L HI.
Proof. apply AppendRange.AR.str_append_range_ok; first [assumption | exact MEMMOVE | exact MEMCPY]. Qed.
(* [comment removed for export] *)
Lemma SETEC : PMS.set_ec_spec L.
Proof. apply SetEc.SetEcProof.set_ec_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL | exact CXA_ATEXIT]. Qed.
(* [comment removed for export] *)
Lemma POPSTATE : PMS.pop_state_spec L.
Proof. apply PopState.PopStateProof.pop_state_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma PARENT : PMS.parent_spec L.
Proof. apply Parent.ParentProof.parent_ok; first [assumption | exact SETEC]. Qed.
(* [comment removed for export] *)
Lemma DECU64 : PMS.dec_u64_spec L.
Proof. apply DecU64.DecU64Proof.dec_u64_ok; first [assumption | exact SETEC]. Qed.
(* [comment removed for export] *)
Lemma PDTOR : PMS.parser_dtor_spec L HI.
Proof. apply ParserDtor.PD.parser_dtor_ok; first [assumption | exact OPDELS]. Qed.
(* [comment removed for export] *)
Lemma SDTOR : PMS.source_dtor_spec L HI.
Proof. apply SourceDtor.SD.source_dtor_ok; first [assumption | exact OPDELS | exact LOCDTOR | exact ISTRDTOR | exact IOSBDTOR]. Qed.
(* [comment removed for export] *)
Lemma IOSBINIT_LATER : TPS2.iosb_init_later_spec L.
Proof. exact (IosbInit.II.iosb_init_later_ok L FPM LOCLATER). Qed.
(* [comment removed for export] *)
Lemma IOSBINIT_FIRST : TPS2.iosb_init_first_spec L.
Proof. exact (IosbInit.II.iosb_init_first_ok L FPM LOCFIRST). Qed.
(* [comment removed for export] *)
Lemma SBUFCTOR : TPS2.sbuf_ctor_spec L HI.
Proof. apply SbufCtor.SBC.sbuf_ctor_ok; first [assumption | exact LOCLATER | exact OPNEW | exact MEMMOVE | exact MEMCPY]. Qed.
(* [comment removed for export] *)
Lemma ISS : PMS.iss_ctor_spec L HI.
Proof. apply IssCtor.IC.iss_ctor_ok; first [assumption | exact IOSBINIT_FIRST | exact IOSBINIT_LATER | exact SBUFCTOR]. Qed.
(* [comment removed for export] *)
Lemma RCTOR : PMS.reader_ctor_spec L HI.
Proof. apply ReaderCtor.RC.reader_ctor_ok; first [assumption | exact IOSBINIT_LATER | exact LOCLATER | exact OPNEW | exact STRRSV | exact VRSV | exact VPUSH]. Qed.
(* [comment removed for export] *)
Lemma STRTOD : PMS.strtod_spec L SS.
Proof. exact (StrtodClosed.STC.strtod_closed L). Qed.
(* [comment removed for export] *)
Lemma DECSTR : PMS.decstr_to_double_spec L SS.
Proof. apply DecstrToDouble.DecstrProof.decstr_to_double_ok; first [assumption | exact STRTOD]. Qed.
(* [comment removed for export] *)
Lemma OPNEWX : PMES.opnew_x_spec L HI.
Proof. apply OpNewX.ONX.opnew_x_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma STRPUSHBACKX : PMES.str_push_back_x_spec L HI.
Proof. apply EncPushBack.EPB.str_push_back_x_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma STRAPPENDX : PMES.str_append_x_spec L HI.
Proof. apply EncAppend.EAP.str_append_x_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma SNPRINTFG : PMFX.snprintf_g_spec L.
Proof. exact (SnprintfClosedX.snprintf_g_closed L). Qed.
(* [comment removed for export] *)
Lemma DECSTRG : PMFX.decstr_to_double_g_spec L SS.
Proof. apply Pm6DecstrGClosed.DSGC.decstr_to_double_g_closed; assumption. Qed.
(* [comment removed for export] *)
Lemma FROMU : PMES.from_integer_u64_x_spec L HI.
Proof. apply FromIntU64X.FIU.from_integer_u64_x_ok; first [assumption | exact STRPUSHBACKX]. Qed.
(* [comment removed for export] *)
Lemma FROMI : PMES.from_integer_i64_x_spec L HI.
Proof. apply FromIntI64X.FII.from_integer_i64_x_ok; first [assumption | exact STRPUSHBACKX]. Qed.
(* [comment removed for export] *)
Lemma WDOUBLE : PMES.write_double_x_spec L HI WD.
Proof. apply WriteDoubleClosedX.WDC.write_double_closed; first [assumption | exact STRPUSHBACKX | exact SNPRINTFG | exact DECSTRG]. Qed.
(* [comment removed for export] *)
Lemma NEWLINE : PMES.new_line_spec L HI.
Proof. apply EncNewLine.ENL.new_line_ok; first [assumption | exact STRAPPENDX | exact STRPUSHBACKX]. Qed.
(* [comment removed for export] *)
Lemma NEWLINE2 : PMES.new_line2_spec L HI.
Proof. apply EncNewLine2.ENL2.new_line2_ok; first [assumption | exact STRAPPENDX | exact STRPUSHBACKX]. Qed.
(* [comment removed for export] *)
Lemma BEGINSCALAR : PMES.begin_scalar_spec L HI.
Proof. apply EncBeginScalarF.EBF.begin_scalar_ok; first [assumption | exact STRAPPENDX | exact NEWLINE | exact STRPUSHBACKX]. Qed.
(* [comment removed for export] *)
Lemma WBIGNUM : PMES.write_bignum_spec L HI.
Proof. apply EncWriteBignum.EWB.write_bignum_ok; first [assumption | exact STRAPPENDX | exact STRPUSHBACKX]. Qed.
(* [comment removed for export] *)
Lemma TOCP : PMES.to_codepoint_spec L.
Proof. apply EncToCodepoint.ETC.to_codepoint_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma ESCAPE : PMES.escape_string_spec L HI.
Proof. apply EncEscapeZ.EEZ.escape_string_ok; first [assumption | exact STRPUSHBACKX | exact TOCP]. Qed.
(* [comment removed for export] *)
Lemma WSTRING : PMES.write_string_spec L HI.
Proof. apply EncWriteString.EWS.write_string_ok; first [assumption | exact STRPUSHBACKX | exact STRAPPENDX | exact ESCAPE | exact WBIGNUM]. Qed.
(* [comment removed for export] *)
Lemma LITNULL : PMES.null_literal_spec L.
Proof. apply EncLiterals.ELTN.null_literal_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL]. Qed.
(* [comment removed for export] *)
Lemma LITTRUE : PMES.true_literal_spec L.
Proof. apply EncLiterals.ELTT.true_literal_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL]. Qed.
(* [comment removed for export] *)
Lemma LITFALSE : PMES.false_literal_spec L.
Proof. apply EncLiterals.ELTF.false_literal_ok; first [assumption | exact GUARD_ACQ | exact GUARD_REL]. Qed.
(* [comment removed for export] *)
Lemma HEAD_OR : PMES2.head_obj_root_spec L HI.
Proof. apply VbhObjRootX.VBH_OR.head_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma HEAD_OO : PMES2.head_obj_inobj_spec L HI.
Proof. apply VbhObjInobjX.VBH_OO.head_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma HEAD_OA : PMES2.head_obj_inarr_spec L HI.
Proof. apply VbhObjInarrX.VBH_OA.head_ok; first [assumption | exact STRAPPENDX | exact NEWLINE2]. Qed.
(* [comment removed for export] *)
Lemma HEAD_AR : PMES2.head_arr_root_spec L HI.
Proof. apply VbhArrRootX.VBH_AR.head_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma HEAD_AO : PMES2.head_arr_inobj_spec L HI.
Proof. apply VbhArrInobjX.VBH_AO.head_ok; assumption. Qed.
(* [comment removed for export] *)
Lemma HEAD_AA : PMES2.head_arr_inarr_spec L HI.
Proof. apply VbhArrInarrX.VBH_AA.head_ok; first [assumption | exact STRAPPENDX | exact NEWLINE2]. Qed.
(* [comment removed for export] *)
Lemma MID_OR : PMES2.mid_obj_root_spec L HI.
Proof. apply VbmOrX.VBM_OR.mid_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma MID_ON : PMES2.mid_obj_nested_spec L HI.
Proof. apply VbmOnX.VBM_ON.mid_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma MID_AR : PMES2.mid_arr_root_spec L HI.
Proof. apply VbmArX.VBM_AR.mid_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma MID_AO : PMES2.mid_arr_inobj_spec L HI.
Proof. apply VbmAoX.VBM_AO.mid_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma MID_AA : PMES2.mid_arr_inarr_spec L HI.
Proof. apply VbmAaX.VBM_AA.mid_ok; first [assumption | exact OPNEWX]. Qed.
(* [comment removed for export] *)
Lemma TAIL_O : PMES2.tail_obj_spec L HI.
Proof. exact (EncVBeginTailO.EVBTO.tail_ok L HI HIok LAY FPM STRAPPENDX). Qed.
(* [comment removed for export] *)
Lemma TAIL_A : PMES2.tail_arr_spec L HI.
Proof. exact (EncVBeginTailA.EVBTA.tail_ok L HI HIok LAY FPM STRAPPENDX). Qed.
(* [comment removed for export] *)
Lemma VBOBJ : PMES.visit_begin_object_spec L HI WD.
Proof. exact (EncVisitBegin.EVBF.visit_begin_object_ok L HI HIok LAY HEAD_OR HEAD_OO HEAD_OA MID_OR MID_ON TAIL_O). Qed.
(* [comment removed for export] *)
Lemma VBARR : PMES.visit_begin_array_spec L HI WD.
Proof. exact (EncVisitBegin.EVBF.visit_begin_array_ok L HI HIok LAY HEAD_AR HEAD_AO HEAD_AA MID_AR MID_AO MID_AA TAIL_A). Qed.
(* [comment removed for export] *)
Lemma VEOBJ : PMES.visit_end_object_spec L HI WD.
Proof. apply EncVisitEnd.EVEF.visit_end_object_ok; first [assumption | exact NEWLINE2 | exact STRAPPENDX]. Qed.
(* [comment removed for export] *)
Lemma VEARR : PMES.visit_end_array_spec L HI WD.
Proof. apply EncVisitEnd.EVEF.visit_end_array_ok; first [assumption | exact NEWLINE2 | exact STRAPPENDX]. Qed.
(* [comment removed for export] *)
Lemma VNULL : PMES.visit_null_spec L HI WD.
Proof. apply EncVisitNull.EVNF.visit_null_ok; first [assumption | exact BEGINSCALAR | exact LITNULL | exact STRAPPENDX]. Qed.
(* [comment removed for export] *)
Lemma VBOOL : PMES.visit_bool_spec L HI WD.
Proof. apply EncVisitBool.EVBF.visit_bool_ok; first [assumption | exact BEGINSCALAR | exact LITTRUE | exact LITFALSE | exact STRAPPENDX]. Qed.
(* [comment removed for export] *)
Lemma VU64 : PMES.visit_uint64_spec L HI WD.
Proof. apply EncVisitU64.EVU64F.visit_uint64_ok; first [assumption | exact BEGINSCALAR | exact FROMU]. Qed.
(* [comment removed for export] *)
Lemma VI64 : PMES.visit_int64_spec L HI WD.
Proof. apply EncVisitI64.EVI64F.visit_int64_ok; first [assumption | exact BEGINSCALAR | exact FROMI]. Qed.
(* [comment removed for export] *)
Lemma VDBL : PMES.visit_double_spec L HI WD.
Proof. apply VisitDoubleX.EVDF.visit_double_ok; first [assumption | exact BEGINSCALAR | exact LITNULL | exact STRAPPENDX | exact WDOUBLE]. Qed.
(* [comment removed for export] *)
Lemma VKEY : PMES.visit_key_spec L HI WD.
Proof. apply EncVisitKey.EVK.visit_key_ok; first [assumption | exact NEWLINE | exact STRPUSHBACKX | exact STRAPPENDX | exact ESCAPE]. Qed.
(* [comment removed for export] *)
Lemma VSTR : PMES.visit_string_spec L HI WD.
Proof. apply EncVisitStr.EVStrF.visit_string_ok; first [assumption | exact BEGINSCALAR | exact WSTRING]. Qed.
(* [comment removed for export] *)
Lemma ENC_CTOR : PMES.enc_ctor_spec L HI.
Proof. exact (EncCtorX.ECX.enc_ctor_ok L HI HIok LAY FPM). Qed.
(* [comment removed for export] *)
Lemma ENC_DTOR : PMES.enc_dtor_spec L HI.
Proof. exact (EncDtorX.EDX.enc_dtor_ok L HI HIok LAY FPM OPDELS). Qed.
(* [comment removed for export] *)
Lemma XSGETNW : TPSW.xsgetn_specw L.
Proof. apply XsgetnW.XSW.xsgetn_okw; first [assumption | exact MEMMOVE]. Qed.
(* [comment removed for export] *)
Lemma DETECTW : TPSW.detect_json_specw L.
Proof. apply DetectW.DJW.detect_json_okw; assumption. Qed.
(* [comment removed for export] *)
Lemma READCHUNKW : TPSW.read_chunk_specw L.
Proof. apply ChunkW.CHKW.read_chunk_okw; first [assumption | exact XSGETNW | exact DETECTW | exact SETEC]. Qed.
(* [comment removed for export] *)
Lemma PCDW : PMW.parser_check_done_specw L HI SS PMR.the_rm.
Proof. apply PcdW.PCDW.parser_check_done_okw; first [assumption | exact SETEC]. Qed.
(* [comment removed for export] *)
Lemma SKIPSPACEW : PMW.skip_space_specw L HI SS PMR.the_rm.
Proof. exact (SkipSpaceW.SkipSpaceProof.skip_space_okw L HI HIok LAY FPM VPUSH). Qed.
(* [comment removed for export] *)
Lemma SKIPWSW : PMW.skip_whitespace_specw L HI SS PMR.the_rm.
Proof. apply SkipWsW.SWW.skip_whitespace_okw; first [assumption | exact SKIPSPACEW | exact POPSTATE]. Qed.
(* [comment removed for export] *)
Lemma PSOMEW : PMW.parse_some_specw L HI SS WD PMR.the_rm.
Proof. exact (ParseAsmW.parse_some_okw_lib L HI HIok LAY FPM SETEC POPSTATE PARENT VPUSH STRPUSHBACK STRAPPEND STRAPPENDRANGE DECU64 DECSTR VNULL VBOOL VBOBJ VBARR VEOBJ VEARR VU64 VI64 VDBL VSTR VKEY). Qed.
(* [comment removed for export] *)
Lemma READXW : PMXW.read_specxw L HI SS WD.
Proof. exact (ReadXW.RDXW.read_xw_ok L HI SS WD HIok LAY FPM VPUSH PSOMEW SKIPWSW PCDW SETEC READCHUNKW). Qed.
(* [comment removed for export] *)
Lemma LIBTOPXW : PMS.strinit_spec L HI -> PMS.iss_ctor_spec L HI -> PMES.enc_ctor_spec L HI -> PMS.reader_ctor_spec L HI -> PMS.system_category_spec L ->
  PMXW.read_specxw L HI SS WD -> (forall LB cr M VM A n, hi_heap HI LB cr M VM -> In (A, n) LB -> n <= 2 ^ 27 \/ n <= 2 ^ 34) ->
  PMS.parser_dtor_spec L HI -> PMS.source_dtor_spec L HI -> PMES.enc_dtor_spec L HI -> PMS.opdel_sized_spec L HI ->
  PMS.locale_dtor_spec L -> TPS.istream_dtor_spec L -> TPS.iosb_dtor_spec L ->
  forall Lay, PMXW.lib_specxw L HI SS WD PHI Lay.
Proof. intros S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14. exact (HarnessXW_s34.HNXW16.lib_ok_xw L HI SS WD HIok LAY FPM S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14). Qed.

Theorem lib_ok_xw_full : forall Lay, PMXW.lib_specxw L HI SS WD PHI Lay.
Proof using HIok LAY FPM MX HFIT. exact (LIBTOPXW STRINIT ISS ENC_CTOR RCTOR SYSCAT READXW HFIT PDTOR SDTOR ENC_DTOR OPDELS LOCDTOR ISTRDTOR IOSBDTOR). Qed.
End A.
End ASMFXW16.
