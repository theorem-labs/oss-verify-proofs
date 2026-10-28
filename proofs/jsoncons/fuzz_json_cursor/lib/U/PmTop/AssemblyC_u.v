(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u
  PmCurSpecs_u PmFloatCSpecs_u Pm10Island_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutHeap CutHeap2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Import Pm10Memmove_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopSpecs_u TopSpecs2_u TopLeaves_u Skel_u SkelC_u IosbDtor_u IosbInit_u IssCtor_u SbufCtorStretch_u SbufCtor_u ParserDtor_u SourceDtor_u Xsgetn_u Detect_u ChunkC_u CStrCtor_u
  CCtor_u GetStr_u ReadNext_u HarnessC_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import StrInit_u StrInit2_u OpDel_u OpNew_u StrReserve_u VecPush_u VecReserve_u Memcpy1_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SetEc_u SetEc2_u ConvEc_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ASMC.
Abbreviation RSEGS := PML.RSEGS.
Section A.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.

Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Hypothesis PSOME : PMS.parse_some_spec L HI PML.STRTOD_SCR_V.

Hypothesis FROMU : PMFC.from_integer_u64_spec L HI.
Hypothesis FROMI : PMFC.from_integer_i64_spec L HI.
Hypothesis WD : PMFC.write_double_spec L HI PML.STRTOD_SCR_V.

Lemma guard_acquire : PMS.guard_acquire_spec L.     Proof. exact (SK.guard_acquire_ok L FPM). Qed.
Lemma guard_release : PMS.guard_release_spec L.     Proof. exact (SK.guard_release_ok L FPM). Qed.
Lemma cxa_atexit : PMS.cxa_atexit_spec L.           Proof. exact (SK.cxa_atexit_ok L FPM). Qed.
Lemma cxa_atexit2 : PMS.cxa_atexit2_spec L.         Proof. exact (SKC.cxa_atexit2_ok L FPM). Qed.
Lemma system_category : PMS.system_category_spec L. Proof. exact (SK.system_category_ok L FPM). Qed.
Lemma locale_ctor_later : PMS.locale_ctor_later_spec L. Proof. exact (SK.locale_ctor_later_ok L FPM). Qed.
Lemma locale_ctor_first : PMS.locale_ctor_first_spec L. Proof. exact (ISL10.locale_ctor_first_ok L). Qed.
Lemma locale_dtor : PMS.locale_dtor_spec L.         Proof. exact (TL.locale_dtor_ok L FPM). Qed.
Lemma istream_dtor : TPS.istream_dtor_spec L.       Proof. exact (TL.istream_dtor_ok L). Qed.
Lemma iosb_dtor : TPS.iosb_dtor_spec L.             Proof. exact (ID.iosb_dtor_ok FPM L HI HIok LAY locale_dtor). Qed.
Lemma set_ec : PMS.set_ec_spec L.                   Proof. exact (SetEcProof.set_ec_ok L FPM guard_acquire guard_release cxa_atexit cxa_atexit2). Qed.
Lemma set_ec2 : PMCS.set_ec2_spec L.                Proof. exact (SetEc2Proof.set_ec2_ok L FPM guard_acquire guard_release cxa_atexit cxa_atexit2). Qed.
Lemma conv_ec : PMS.conv_ec_spec L.                 Proof. exact (ConvEcProof.conv_ec_ok L FPM guard_acquire guard_release cxa_atexit cxa_atexit2). Qed.
Lemma memmove1 : CH2.copy1_spec L XS.MEMMOVE.       Proof. exact (Pm10Memmove_u.memmove_copy1 L (PmLayout.ly_segs L LAY)). Qed.
Lemma memcpy1 : CH2.copy1_spec L MC1.MEMCPY.        Proof. exact (MC1.memcpy_copy1 L (PmLayout.ly_segs L LAY)). Qed.
Lemma xsgetn : TPS.xsgetn_spec L.                   Proof. exact (XS.xsgetn_ok FPM L LAY memmove1). Qed.
Lemma detect_json : TPS.detect_json_spec L.         Proof. exact (DJ.detect_json_ok L FPM). Qed.
Lemma read_chunk_c : PMCS.read_chunk_c_spec L.      Proof. exact (CHKC.read_chunk_c_ok L LAY FPM xsgetn detect_json set_ec). Qed.
Lemma opdel_sized : PMS.opdel_sized_spec L HI.      Proof. exact (OD.opdel_sized_ok L HI HIok LAY FPM). Qed.
Lemma opnew : PMS.opnew_spec L HI.                  Proof. exact (ON.opnew_ok L HI HIok LAY FPM). Qed.
Lemma str_reserve : PMS.str_reserve_spec L HI.      Proof. exact (SRV.str_reserve_ok L HI HIok LAY FPM). Qed.
Lemma vec_reserve : PMS.vec_reserve_spec L HI.      Proof. exact (VR.vec_reserve_ok L HI HIok LAY FPM). Qed.
Lemma vec_push : PMS.vec_push_spec L HI.            Proof. exact (VP.vec_push_ok L HI HIok LAY FPM). Qed.
Lemma strinit : PMS.strinit_spec L HI.              Proof. exact (SI.strinit_ok L HI HIok LAY FPM). Qed.
Lemma strinit2 : PMCS.strinit2_spec L HI.           Proof. exact (SI2.strinit2_ok L HI HIok LAY FPM). Qed.
Lemma cstr_ctor : PMCS.cstr_ctor_spec L HI.         Proof. exact (CSTR.cstr_ctor_ok L HI HIok LAY FPM). Qed.
Lemma parser_dtor : PMS.parser_dtor_spec L HI.      Proof. exact (PD.parser_dtor_ok L HI HIok LAY FPM opdel_sized). Qed.
Lemma source_dtor : PMS.source_dtor_spec L HI.      Proof. exact (SD.source_dtor_ok L HI HIok LAY FPM opdel_sized locale_dtor istream_dtor iosb_dtor). Qed.
Lemma iosb_init_later : TPS2.iosb_init_later_spec L. Proof. exact (II.iosb_init_later_ok L FPM locale_ctor_later). Qed.
Lemma iosb_init_first : TPS2.iosb_init_first_spec L. Proof. exact (II.iosb_init_first_ok L FPM locale_ctor_first). Qed.
Lemma sbuf_ctor : TPS2.sbuf_ctor_spec L HI.         Proof. exact (SBC.sbuf_ctor_ok L HI HIok LAY FPM locale_ctor_later opnew memmove1 memcpy1). Qed.
Lemma iss_ctor : PMS.iss_ctor_spec L HI.            Proof. exact (IC.iss_ctor_ok L HI HIok LAY FPM iosb_init_first iosb_init_later sbuf_ctor). Qed.
Lemma read_next : PMCS.read_next_spec L HI PML.STRTOD_SCR_V.
Proof. exact (RNX.read_next_ok L HI PML.STRTOD_SCR_V HIok LAY FPM PSOME set_ec read_chunk_c). Qed.
Lemma cursor_ctor : PMCS.cursor_ctor_spec L HI PML.STRTOD_SCR_V.
Proof. exact (CCR.cursor_ctor_ok L HI HIok LAY FPM iosb_init_later locale_ctor_later opnew str_reserve vec_reserve vec_push PML.STRTOD_SCR_V system_category read_next set_ec2). Qed.
Lemma get_string : PMCS.get_string_spec L HI PML.STRTOD_SCR_V.
Proof. exact (GTS.get_string_ok L HI HIok LAY FPM PML.STRTOD_SCR_V ltac:(unfold PML.STRTOD_SCR_V; lia) strinit2 cstr_ctor FROMU FROMI WD conv_ec). Qed.

Theorem lib_ok_c : forall Lay, PMCS.lib_spec_c L HI PML.STRTOD_SCR_V Lay.
Proof.
  exact (HNC.lib_ok L HI PML.STRTOD_SCR_V HIok LAY FPM ltac:(unfold PML.STRTOD_SCR_V; lia) strinit iss_ctor system_category cursor_ctor get_string read_next
           parser_dtor source_dtor opdel_sized locale_dtor istream_dtor iosb_dtor).
Qed.
End A.
End ASMC.

