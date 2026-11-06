(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5DefsA XIcptAs0 L5CoreAS8 HeapIfaceAEx HeapIfaceAExI HeapIfaceAEr LibIface LibIfaceAB LibIfaceAE.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PeSpecsAmc PeAImgGap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCStatics PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCTxtSpecsA PeCValSpecA PeCDtorSpecsA PeTopAL PeCTopA PeACStr PeACIss PeACParse PeAEncDbl PeAEncEnd PeACRdVal PeCEPushSpecsA PeAEPush PeAEPusq PeASinkPush PeAEncBgn PeAEncBgnL PeAOpnew PeAOpdel PeALoc PeASys PeAIosDtor PeASrcDtor PeAResize PeAEncFlush PeAAnn PeAEmu PeAEmb PeACReset PeACErr PeACEnd PeACRdCtor PeACRtv PeAOpnewN PeAEmm PeAEms PeAEncNull PeAEncBool PeAEncU64 PeAEncI64 PeAEncPutLen PeAEncKey PeACHarness PeACRdKey PeACGetLen PeASnkDtor PeASnkAnn PeAEstkDtor PeAEstkAnn PeACSrcFill PeACSrcPeek PeACSrcIgn PeACSrcRead PeACRdSpan3 PeACSrd5 PeACResize PeACSrcFillTb PeAEncStr PeACVal PeACValR PeAB10 PeAVecDtor PeACBegArr PeACBegObj.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECASMA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.

Section Asm.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (ar : asan_run) (HIk : list (list Z) -> asan_iface).
Variable P : PESKA.sink_policyA.

Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.
Hypothesis LEARNOK : forall n, 0 < n <= PESKA.spa_nmax P -> HAR.ngrant n -> PESKA.spa_cap P n.

Definition inst_ok (HI : asan_iface) : Prop :=
  HAJ.asan_iface_okR L ar C SCFG HI /\ aicpt_ok L ar IL SCFG HI /\ HAJ.asan_ext_ok L ar SCFG HI PMA.EXT /\ PMAGAP.rt_img_gap HI.

Definition fam_ok : Prop := HAR.asan_famR_ok L ar C SCFG LR HIk /\ (forall D, inst_ok (HIk D)).
Hypothesis FAM : fam_ok.

Definition HI : asan_iface := HIk [].
Let IOK : inst_ok HI := proj2 FAM [].
Let HIok : HAJ.asan_iface_okR L ar C SCFG HI := proj1 IOK.
Let ICok : aicpt_ok L ar IL SCFG HI := proj1 (proj2 IOK).
Let EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT := proj1 (proj2 (proj2 IOK)).
Let GAP : PMAGAP.rt_img_gap HI := proj2 (proj2 (proj2 IOK)).

Let MALLOCN : HAR.amallocN_spec L ar SCFG (fun _ => HI) := fun D => HAR.fr_mallocN L ar C SCFG LR HIk (proj1 FAM) [].

Let MEMCPYN : HAR.amemcpyN_spec_at L ar SCFG (fun _ => HI) (hl_asan_memcpy L) := fun D => HAR.fr_memcpyN L ar C SCFG LR HIk (proj1 FAM) [].

Definition TOPK0 : Z := 1024.
Definition TOPB0 : Z := 2 ^ 32.
Definition tk : Z := TOPK0 + fst (PESKA.spa_pot P 0).
Definition tb : Z := TOPB0 + snd (PESKA.spa_pot P 0).
Definition LayA : lib_layoutA := PECTA.LayA tk tb L.
Definition TopLSA : lib_statics := PECTA.TopLSA.

Definition harness_stmt : Prop :=
  forall (PayOk PayExport : list byte -> Prop),
    PECSA.pay_in P PayOk -> PECSA.pay_out P PayExport ->
    lib_call_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.

Record rows_open : Prop := ROWS {
  ro_all_closed : PECSA.parse_spec L ar HI P -> True
}.
Variable RO : rows_open.
Lemma rows_closed : rows_open.
Proof. exact (ROWS (fun _ => I)). Qed.

Let opnew : PMSPA.opnew_spec RSEGS AD L ar HI :=
  PMAOPN.opnew_ok L ar C HI LY HIok.
Let opdel : PMSPA.opdel_spec RSEGS AD L ar HI :=
  PMAOPD.opdel_ok L ar C HI LY HIok.
Let opdel_sized : PMSPA.opdel_sized_spec RSEGS AD L ar HI :=
  PMAOPD.opdel_sized_ok L ar C HI LY HIok.
Let locale_ctor : PMSPA.locale_ctor_spec RSEGS AD L ar HI :=
  PMALOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC.
Let locale_dtor : PMSPA.locale_dtor_spec RSEGS AD L ar HI :=
  PMALOC.locale_dtor_ok L ar C HI LY HIok.
Let syscat : PMSPA.syscat_spec RSEGS AD L ar HI :=
  PMASY.syscat_ok L ar C HI LY HIok.
Let ios_dtor : PMSPA.ios_dtor_spec RSEGS AD L ar HI :=
  PMAID.ios_dtor_ok L ar C HI LY HIok EXT locale_dtor.
Let src_dtor : PMSPA.src_dtor_spec RSEGS AD L ar HI :=
  PMASD.src_dtor_ok L ar C HI LY HIok opdel locale_dtor ios_dtor.
Let is_base10 : PMSPA.is_base10_spec RSEGS AD L ar HI :=
  PMAB10.is_base10_ok L ar C HI LY HIok IL ICok ILY.
Let str_resize : PMSPA.str_resize_spec RSEGS AD L ar HI :=
  PMARZ.str_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.
Let push_mi : PECSA.push_mi_spec L ar HI :=
  PMAEB.push_mi_ok L ar C HI LY HIok EXT opnew opdel.
Let push_miu : PECSA.push_miu_spec L ar HI :=
  PMAEU.push_miu_ok L ar C HI LY HIok EXT opnew opdel.
Let push_ms : PECSA.push_ms_spec L ar HI :=
  PMAEM.push_ms_ok L ar C HI LY HIok EXT opnew opdel.
Let push_msu : PECSA.push_msu_spec L ar HI :=
  PMAES.push_msu_ok L ar C HI LY HIok EXT opnew opdel.
Let ann_shrink : PECSA.ann_shrink_spec L ar HI :=
  PMAANN.ann_shrink_ok L ar C HI LY HIok EXT.
Let ann_delete : PECSA.ann_delete_spec L ar HI :=
  PMAANN.ann_delete_ok L ar C HI LY HIok EXT.
Let vec_dtor : PMSPA.vec_dtor_spec RSEGS AD L ar HI :=
  PMAVD.vec_dtor_ok L ar C HI LY HIok ann_shrink ann_delete opdel.
Let make_ec : PECSA.make_ec_spec L ar HI :=
  PEACERR.make_ec_ok L ar C HI LY HIok EXT.
Let reader_ctor : PECSA.reader_ctor_spec L ar HI :=
  PMARD.reader_ctor_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew push_mi.
Let reset : PECSA.reset_spec L ar HI :=
  PEACRS.reset_ok L ar C HI LY HIok ann_shrink push_miu.
Let str_ctor_c : PECSA.str_ctor_c_spec L ar HI :=
  PEACSTR.str_ctor_c_ok L ar C HI LY HIok opnew.
Let iss_ctor_c : PECSA.iss_ctor_c_spec L ar HI :=
  PEACISS.iss_ctor_c_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew.
Let validate_rd : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD) :=
  PECVALAR.validate_fun_ok L ar C HI LY HIok GAP.
Let validate_enc : PECVSA.validate_fun_spec RSEGS AD L ar HI (pe_validate_enc EE) :=
  PECVALA.validate_fun_ok L ar C HI LY HIok GAP.
Let OPNWP : PESKA.opnew_n_spec RSEGS AD L ar HI (PESKA.spa_nmax P) (PESKA.spa_cap P) :=
  PESKA.opnew_n_spec_mono RSEGS AD L ar HI _ _ _ _ NMAXOK LEARNOK (PMAOPNW.opnew_n_ok L ar C HI LY HIok MALLOCN).
Let push_back : PESKA.push_back_specA RSEGS AD EE L ar HI P :=
  PEASKP.push_back_ok L ar C HI P LY HIok EXT PO OPNWP opdel MEMCPYN NMAXOK.
Let epush_k : PECEPX.epush_k_spec RSEGS AD EE L ar HI :=
  PEAEPUSH.epush_k_ok L ar C HI LY HIok EXT opnew opdel.
Let epush_kl : PECEPX.epush_kl_spec RSEGS AD EE L ar HI :=
  PEAEQPUSH.epush_kl_ok L ar C HI LY HIok EXT opnew opdel.
Let put_length : PECSA.put_length_spec L ar HI P :=
  PEAENCPL.put_length_ok L ar C HI P LY HIok PO push_back.
Let v_null : PECSA.v_null_spec L ar HI P :=
  PEAENCN.v_null_ok L ar C HI P LY HIok PO push_back.
Let v_bool : PECSA.v_bool_spec L ar HI P :=
  PEAENCT.v_bool_ok L ar C HI P LY HIok PO push_back.
Let v_uint64 : PECSA.v_uint64_spec L ar HI P :=
  PEAENCVU.v_uint64_ok L ar C HI P LY HIok PO push_back.
Let v_int64 : PECSA.v_int64_spec L ar HI P :=
  PEAENCVI.v_int64_ok L ar C HI P LY HIok PO push_back.
Let v_double : PECSA.v_double_spec L ar HI P :=
  PEAENCD.v_double_ok L ar C HI P LY HIok PO push_back.
Let v_flush : PECSA.v_flush_spec L ar HI P :=
  PEAENCF.v_flush_ok L ar C HI P LY HIok.
Let v_begin_arr : PECSA.v_begin_arr_spec L ar HI P :=
  PEAENCBG.v_begin_arr_ok L ar C HI P LY HIok PO push_back make_ec epush_k.
Let v_begin_arr_len : PECSA.v_begin_arr_len_spec L ar HI P :=
  PEAENCBL.v_begin_arr_len_ok L ar C HI P LY HIok PO push_back make_ec put_length epush_kl.
Let v_begin_obj : PECSA.v_begin_obj_spec L ar HI P :=
  PEAENCBG.v_begin_obj_ok L ar C HI P LY HIok PO push_back make_ec epush_k.
Let v_begin_obj_len : PECSA.v_begin_obj_len_spec L ar HI P :=
  PEAENCBL.v_begin_obj_len_ok L ar C HI P LY HIok PO push_back make_ec put_length epush_kl.
Let v_end_arr : PECSA.v_end_arr_spec L ar HI P :=
  PEAENCE.v_end_arr_ok L ar C HI P LY HIok PO push_back make_ec (PEAEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).
Let v_end_obj : PECSA.v_end_obj_spec L ar HI P :=
  PEAENCE.v_end_obj_ok L ar C HI P LY HIok PO push_back make_ec (PEAEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).
Let v_key : PECSA.v_key_spec L ar HI P :=
  PEAENCK.v_key_ok L ar C HI P LY HIok PO push_back put_length validate_enc.
Let v_string : PECSA.v_string_spec L ar HI P :=
  PEAENCST.v_string_ok L ar C HI P LY HIok PO push_back put_length make_ec validate_enc.
Let fill_buffer : PECSA.fill_buffer_spec L ar HI :=
  PECFILLA.fill_buffer_ok L ar C HI LY HIok IL ICok ILY.
Let peek : PECSA.peek_spec L ar HI :=
  PECPEEKA.peek_ok L ar C HI LY HIok fill_buffer.
Let ignore : PECSA.ignore_spec L ar HI :=
  PECIGNA.ignore_ok L ar C HI LY HIok fill_buffer.
Let src_read : PECSA.src_read_spec L ar HI :=
  PECREADA.src_read_ok L ar C HI LY HIok IL ICok ILY fill_buffer.
Let cstr_resize : PECTXSA.cstr_resize_spec RSEGS AD L ar HI :=
  PECRSZA.cstr_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.
Let csrd_read : PECTXSA.csrd_read_spec RSEGS AD L ar HI :=
  PECSRD5A.csrd_read_ok L ar C HI LY HIok IL ICok ILY cstr_resize fill_buffer (PECFILLTBA.cfill_tb_ok L ar C HI LY HIok IL ICok ILY).
Let read_span : PECSA.read_span_spec L ar HI :=
  PECRS3A.read_span_ok L ar C HI LY HIok IL ICok ILY fill_buffer csrd_read.
Let get_length : PECSA.get_length_spec L ar HI P :=
  PEACGL.get_length_ok L ar C HI P LY HIok src_read make_ec.
Let end_array : PECSA.end_array_spec L ar HI P :=
  PEACEND.end_array_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_arr.
Let end_object : PECSA.end_object_spec L ar HI P :=
  PEACEND.end_object_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_obj.
Let read_key : PECSA.read_key_spec L ar HI P :=
  PEACRDKEY.read_key_ok L ar C HI P LY HIok IL ICok ILY PO get_length read_span validate_rd make_ec v_key.
Let begin_array : PECSA.begin_array_spec L ar HI P :=
  PEACBA.begin_array_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec push_mi push_ms push_msu v_begin_arr v_begin_arr_len.
Let begin_object : PECSA.begin_object_spec L ar HI P :=
  PEACBO.begin_object_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec push_mi push_ms push_msu v_begin_obj v_begin_obj_len.
Let read_value : PECSA.read_value_spec L ar HI P :=
  PEACRV.read_value_ok L ar C HI P LY HIok IL ICok ILY PO src_read get_length read_span validate_rd is_base10 make_ec begin_array begin_object v_null v_bool v_uint64 v_int64 v_double v_string.
Let rtv : PECSA.rtv_spec L ar HI P :=
  PEACRTV.rtv_ok L ar C HI P LY HIok IL ICok ILY src_read make_ec read_value.
Let parse : PECSA.parse_spec L ar HI P :=
  PEACLP.parse_ok L ar C HI P LY HIok IL ICok ILY rtv read_value read_key end_array end_object peek ignore make_ec ann_shrink.
Let estk_dtor : PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb140c :=
  PEAEKD.estk_dtor_ok L ar C HI LY HIok (PEAEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT) (PEAEKAN.ann_delete_e_ok L ar C HI LY HIok EXT) opdel.
Let sink_dtor : PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaa5cc :=
  PEASKD.sink_dtor_ok L ar C HI P LY HIok (PEASKAN.ann_shrink_b_ok L ar C HI LY HIok EXT) (PEASKAN.ann_delete_b_ok L ar C HI LY HIok EXT) opdel.
Let HARN : harness_stmt :=
  PEACHN.harness_call_ok L ar C IL HI P LY HIok ICok ILY EXT PO PMODE str_ctor_c iss_ctor_c reader_ctor syscat reset parse vec_dtor opdel src_dtor locale_dtor ios_dtor estk_dtor sink_dtor.

Theorem top_iface_asm (PayOk PayExport : list byte -> Prop) :
  PECSA.pay_in P PayOk -> PECSA.pay_out P PayExport ->
  lib_iface_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.
Proof using LY ILY MCC PO PMODE NMAXOK LEARNOK FAM RO.
  intros PIN POUT. apply (PECTA.top_iface_okA_x L ar C tk tb LY). exact (HARN PayOk PayExport PIN POUT).
Qed.
End Asm.
End PECASMA.
