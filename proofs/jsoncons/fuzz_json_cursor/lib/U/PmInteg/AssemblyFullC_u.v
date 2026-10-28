(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u
  PmCurSpecs_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require StrtodClosed_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FloatC Require SnprintfClosed_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutHeap CutHeap2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u DemoAppend11_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require OpNew_u OpDel_u StrInit_u StrReserve_u VecReserve_u VecPush_u Memcpy1_u StrPushBack_u AppendRange_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require SkipSpace_u PopState_u SetEc_u Parent_u Validate_u DecU64_u AfterValue_u BeginMember_u BeginObject_u BeginArray_u EndObject_u EndArray_u ParseTrue_u ParseFalse_u ParseNull_u
  EndStringValue_u EndIntegerValue_u EndFractionValue_u DecstrToDouble_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require ParseString_u ParseNumber_u ParseSomeZ_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Xsgetn_u VisitC_u VisitD_u Pm10DecstrGClosed_u AssemblyC_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTU Require TuFromInt_u TuFi64_u TuWdF_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ASMFC.
Section A.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma guard_acquire : PMS.guard_acquire_spec L.  Proof. apply AssemblyC_u.ASMC.guard_acquire; assumption. Qed.
Lemma guard_release : PMS.guard_release_spec L.  Proof. apply AssemblyC_u.ASMC.guard_release; assumption. Qed.
Lemma cxa_atexit : PMS.cxa_atexit_spec L.        Proof. apply AssemblyC_u.ASMC.cxa_atexit; assumption. Qed.
Lemma set_ec : PMS.set_ec_spec L.                Proof. apply AssemblyC_u.ASMC.set_ec; assumption. Qed.
Lemma memmove1 : CH2.copy1_spec L Xsgetn_u.XS.MEMMOVE.  Proof. apply AssemblyC_u.ASMC.memmove1; assumption. Qed.
Lemma memcpy1 : CH2.copy1_spec L Memcpy1_u.MC1.MEMCPY.   Proof. apply AssemblyC_u.ASMC.memcpy1; assumption. Qed.
Lemma vec_push : PMS.vec_push_spec L HI.          Proof. apply VecPush_u.VP.vec_push_ok; assumption. Qed.
Lemma pop_state : PMS.pop_state_spec L.           Proof. apply PopState_u.PopStateProof.pop_state_ok; assumption. Qed.
Lemma parent : PMS.parent_spec L.                 Proof. apply Parent_u.ParentProof.parent_ok; first [assumption | exact set_ec]. Qed.
Lemma validate : PMS.validate_spec L.             Proof. apply Validate_u.ValidateProof.validate_ok; first [assumption | exact set_ec]. Qed.
Lemma dec_u64 : PMS.dec_u64_spec L.               Proof. apply DecU64_u.DecU64Proof.dec_u64_ok; first [assumption | exact set_ec]. Qed.

Lemma vis_null : PMS.visit_null_spec L PMS.PC_VIS_NULL.                       Proof. apply VisitC_u.VIS.visit_null_ok; assumption. Qed.
Lemma vis_bool : PMS.visit_bool_spec L PMS.PC_VIS_BOOL.                       Proof. apply VisitC_u.VIS.visit_bool_ok; assumption. Qed.
Lemma vis_u64 : PMS.visit_u64_spec L PMS.PC_VIS_U64.                          Proof. apply VisitC_u.VIS.visit_u64_ok; assumption. Qed.
Lemma vis_i64 : PMS.visit_i64_spec L PMS.PC_VIS_I64.                          Proof. apply VisitC_u.VIS.visit_i64_ok; assumption. Qed.
Lemma vis_key : PMS.visit_key_spec L PMS.PC_VIS_KEY.                          Proof. apply VisitC_u.VIS.visit_key_ok; assumption. Qed.
Lemma vis_string : PMS.visit_string_spec L PMS.PC_VIS_STRING.                 Proof. apply VisitC_u.VIS.visit_string_ok; assumption. Qed.
Lemma vis_bobj : PMS.visit_begin_object_spec L PMS.PC_VIS_BEGIN_OBJECT_TAG.  Proof. apply VisitC_u.VIS.visit_begin_object_ok; assumption. Qed.
Lemma vis_barr : PMS.visit_begin_array_spec L PMS.PC_VIS_BEGIN_ARRAY_TAG.    Proof. apply VisitC_u.VIS.visit_begin_array_ok; assumption. Qed.
Lemma vis_eobj : PMS.visit_end_object_spec L PMS.PC_VIS_END_OBJECT.          Proof. apply VisitC_u.VIS.visit_end_object_ok; assumption. Qed.
Lemma vis_earr : PMS.visit_end_array_spec L PMS.PC_VIS_END_ARRAY.            Proof. apply VisitC_u.VIS.visit_end_array_ok; assumption. Qed.
Lemma vis_double : PMS.visit_double_spec L PMS.PC_VIS_DOUBLE.                 Proof. apply VisitD_u.VISD.visit_double_ok; assumption. Qed.
Local Ltac vis := first [exact vis_null | exact vis_bool | exact vis_u64 | exact vis_i64 | exact vis_key | exact vis_string | exact vis_bobj | exact vis_barr
                        | exact vis_eobj | exact vis_earr | exact vis_double].

Lemma skip_space : PMS.skip_space_spec L HI PML.STRTOD_SCR_V.   Proof. apply SkipSpace_u.SkipSpaceProof.skip_space_ok; first [assumption | exact vec_push]. Qed.
Lemma after_value : PMS.after_value_spec L HI.                  Proof. apply AfterValue_u.AfterValueProof.after_value_ok; first [assumption | exact parent | exact set_ec]. Qed.
Lemma begin_member : PMS.begin_member_spec L HI PML.STRTOD_SCR_V. Proof. apply BeginMember_u.BeginMemberProof.begin_member_ok; first [assumption | exact parent | exact set_ec]. Qed.
Lemma begin_object : PMS.begin_object_spec L HI PML.STRTOD_SCR_V. Proof. apply BeginObject_u.BeginObjectProof.begin_object_ok; first [assumption | exact vec_push | exact set_ec | vis]. Qed.
Lemma begin_array : PMS.begin_array_spec L HI PML.STRTOD_SCR_V.   Proof. apply BeginArray_u.BeginArrayProof.begin_array_ok; first [assumption | exact vec_push | exact set_ec | vis]. Qed.
Lemma end_object : PMS.end_object_spec L HI PML.STRTOD_SCR_V.     Proof. apply EndObject_u.EndObjectProof.end_object_ok; first [assumption | exact pop_state | exact set_ec | vis]. Qed.
Lemma end_array : PMS.end_array_spec L HI PML.STRTOD_SCR_V.       Proof. apply EndArray_u.EndArrayProof.end_array_ok; first [assumption | exact pop_state | exact set_ec | vis]. Qed.
Lemma parse_true : PMS.parse_true_spec L HI PML.STRTOD_SCR_V.     Proof. apply ParseTrue_u.ParseTrueProof.parse_true_ok; first [assumption | exact set_ec | vis]. Qed.
Lemma parse_false : PMS.parse_false_spec L HI PML.STRTOD_SCR_V.   Proof. apply ParseFalse_u.ParseFalseProof.parse_false_ok; first [assumption | exact set_ec | vis]. Qed.
Lemma parse_null : PMS.parse_null_spec L HI PML.STRTOD_SCR_V.     Proof. apply ParseNull_u.ParseNullProof.parse_null_ok; first [assumption | exact set_ec | vis]. Qed.
Lemma end_string_value : PMS.end_string_value_spec L HI.
Proof. apply EndStringValue_u.EndStringValueProof.end_string_value_ok; first [assumption | exact validate | exact parent | exact pop_state | exact set_ec | vis]. Qed.
Lemma strtod : PMS.strtod_spec L PML.STRTOD_SCR_V.                Proof. exact (StrtodClosed_u.STC.strtod_closed L). Qed.
Lemma decstr_to_double : PMS.decstr_to_double_spec L PML.STRTOD_SCR_V.
Proof. apply DecstrToDouble_u.DecstrProof.decstr_to_double_ok; first [assumption | exact strtod]. Qed.
Lemma end_integer_value : PMS.end_integer_value_spec L HI PML.STRTOD_SCR_V.
Proof. apply EndIntegerValue_u.EndIntegerValueProof.end_integer_value_ok; first [assumption | exact dec_u64 | exact after_value | exact decstr_to_double | exact set_ec | vis]. Qed.
Lemma end_fraction_value : PMS.end_fraction_value_spec L HI PML.STRTOD_SCR_V.
Proof. apply EndFractionValue_u.EndFractionValueProof.end_fraction_value_ok; first [assumption | exact decstr_to_double | exact after_value | exact set_ec | vis]. Qed.
Lemma str_push_back : PMS.str_push_back_spec L HI.   Proof. apply StrPushBack_u.SPB.str_push_back_ok; first [assumption | exact memmove1 | exact memcpy1]. Qed.
Lemma str_append_range : PMS.str_append_range_spec L HI. Proof. apply AppendRange_u.AR.str_append_range_ok; first [assumption | exact memmove1 | exact memcpy1]. Qed.
Lemma str_append : PMS.str_append_spec L HI.         Proof. apply DemoAppend11_u.str_append_ok; first [assumption | exact memmove1 | exact memcpy1]. Qed.

Lemma parse_string : PMS.parse_string_spec L HI PML.STRTOD_SCR_V.
Proof. apply ParseString_u.parse_string_ok; first [assumption | exact str_push_back | exact str_append | exact set_ec | exact end_string_value]. Qed.
Lemma parse_number : PMS.parse_number_spec L HI PML.STRTOD_SCR_V.
Proof. apply ParseNumber_u.parse_number_ok; first [assumption | exact str_append_range | exact set_ec | exact end_integer_value | exact end_fraction_value]. Qed.

Lemma parse_some : PMS.parse_some_spec L HI PML.STRTOD_SCR_V.
Proof.
  apply ParseSomeZ_u.PSZ.parse_some_ok; first [assumption | exact set_ec | exact pop_state | exact parent | exact vec_push | exact str_push_back | exact skip_space | exact begin_member
    | exact begin_object | exact begin_array | exact end_object | exact end_array | exact parse_null | exact parse_true | exact parse_false | exact parse_string | exact parse_number
    | exact end_integer_value | exact end_fraction_value | vis].
Qed.

Lemma snprintf_g : PMFC.snprintf_g_spec L.                                  Proof. exact (SnprintfClosed_u.snprintf_g_closed L). Qed.
Lemma decstr_g : PMFC.decstr_to_double_g_spec L PML.STRTOD_SCR_V.            Proof. apply Pm10DecstrGClosed_u.DSGC.decstr_to_double_g_closed; assumption. Qed.
Lemma from_integer_u64 : PMFC.from_integer_u64_spec L HI.                    Proof. apply TuFromInt_u.TFI.from_integer_u64_ok; assumption. Qed.
Lemma from_integer_i64 : PMFC.from_integer_i64_spec L HI.                    Proof. apply TuFi64_u.TFI64.from_integer_i64_ok; assumption. Qed.
Lemma write_double : PMFC.write_double_spec L HI PML.STRTOD_SCR_V.
Proof. apply TuWdF_u.TWDF.write_double_ok; first [assumption | exact snprintf_g | exact decstr_g]. Qed.

Theorem lib_ok_c_full : forall Lay, PMCS.lib_spec_c L HI PML.STRTOD_SCR_V Lay.
Proof.
  apply AssemblyC_u.ASMC.lib_ok_c; first [assumption | exact parse_some | exact from_integer_u64 | exact from_integer_i64 | exact write_double].
Qed.
End A.
End ASMFC.
