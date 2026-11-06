(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5DefsA XIcptAs0B0 L5CoreAS9 HeapIfaceAEx HeapIfaceAExI HeapIfaceAEr LibIface LibIfaceAB LibIfaceAE.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PeSpecsAmc PeBImgGap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCStatics PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCTxtSpecsA PeCValSpecA PeCDtorSpecsA PeTopAL PeCTopB PeBCStr PeBCIss PeBCParse PeBEPusq PeBSinkPush PeBCBegArr PeBCBegObj PeBEncBgn PeBEncBgnL PeBEncDbl PeBEncEnd PeBCRdVal PeCEPushSpecsA PeBEPushF PeBEPusqF PeBEPush PeBOpnew PeBOpdel PeBLoc PeBSys PeBIosDtor PeBSrcDtor PeBResize PeBEncFlush PeSpecsBXJ PeBAnn PeBVecClear PeBConeMiu PeBCReset PeBCErr PeBCEnd PeBCRdCtor PeBCRtv PeBSlowMi PeBOpnewN PeBConeMi PeBConeMs PeBConeMsu PeBSlowMs PeBSlowMsu PeBSlowMiu PeBEncBool PeBCHarness PeBCRdKey PeBCGetLen PeBSnkDtor PeBSnkClr PeBSnkAnn PeBEstkDtor PeBEstkClr PeBEstkAnn PeBCSrcFill PeBCSrcPeek PeBCSrcIgn PeBCSrcRead PeBCRdSpan3 PeBCSrd5 PeBCResize PeBCSrcFillTb PeBPbIndSpec PeBPbInd PeBEncStr PeBCVal PeBCValR PeBB10 PeBVecDtor PeBEncNull PeBEncU64 PeBEncPutLen PeBEncI64 PeBEncKey PeCRdReadSpecZ PeBCRdRead.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECASMB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Section Asm.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (ar : asan_run) (HIk : list (list Z) -> asan_iface).
Variable P : PESKA.sink_policyA.

Hypothesis LY : PMB.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.
Hypothesis LEARNOK : forall n, 0 < n <= PESKA.spa_nmax P -> HAR.ngrant n -> PESKA.spa_cap P n.

Definition inst_ok (HI : asan_iface) : Prop :=
  HAJ.asan_iface_okR L ar C SCFG HI /\ aicpt_ok L ar IL SCFG HI /\ HAJ.asan_ext_ok L ar SCFG HI PMB.EXT /\ PMBGAP.rt_img_gap HI.

Definition fam_ok : Prop := HAR.asan_famR_ok L ar C SCFG LR HIk /\ (forall D, inst_ok (HIk D)).
Hypothesis FAM : fam_ok.

Definition HI : asan_iface := HIk [].
Let IOK : inst_ok HI := proj2 FAM [].
Let HIok : HAJ.asan_iface_okR L ar C SCFG HI := proj1 IOK.
Let ICok : aicpt_ok L ar IL SCFG HI := proj1 (proj2 IOK).
Let EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT := proj1 (proj2 (proj2 IOK)).
Let GAP : PMBGAP.rt_img_gap HI := proj2 (proj2 (proj2 IOK)).

Let MALLOCN : HAR.amallocN_spec L ar SCFG (fun _ => HI) := fun D => HAR.fr_mallocN L ar C SCFG LR HIk (proj1 FAM) [].

Let MEMCPYN : HAR.amemcpyN_spec_at L ar SCFG (fun _ => HI) (hl_asan_memcpy L) := fun D => HAR.fr_memcpyN L ar C SCFG LR HIk (proj1 FAM) [].

Definition TOPK0 : Z := 1024.
Definition TOPB0 : Z := 2 ^ 32.
Definition tk : Z := TOPK0 + fst (PESKA.spa_pot P 0).
Definition tb : Z := TOPB0 + snd (PESKA.spa_pot P 0).
Definition LayA : lib_layoutA := PECTB.LayA tk tb L.
Definition TopLSA : lib_statics := PECTB.TopLSA.

Definition harness_stmt : Prop :=
  forall (PayOk PayExport : list byte -> Prop),
    PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
    lib_call_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.

Record rows_open : Prop := ROWS {
  ro_all_closed : PECSB.parse_spec L ar HI P -> True
}.
Variable RO : rows_open.
Lemma rows_closed : rows_open.
Proof. exact (ROWS (fun _ => I)). Qed.

Let opnew : PMSPA.opnew_spec RSEGS AD L ar HI :=
  PMBOPN.opnew_ok L ar C HI LY HIok.
Let opdel : PMSPA.opdel_spec RSEGS AD L ar HI :=
  PMBOPD.opdel_ok L ar C HI LY HIok.
Let opdel_sized : PMSPA.opdel_sized_spec RSEGS AD L ar HI :=
  PMBOPD.opdel_sized_ok L ar C HI LY HIok.
Let locale_ctor : PMSPA.locale_ctor_spec RSEGS AD L ar HI :=
  PMBLOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC.
Let locale_dtor : PMSPA.locale_dtor_spec RSEGS AD L ar HI :=
  PMBLOC.locale_dtor_ok L ar C HI LY HIok.
Let syscat : PMSPA.syscat_spec RSEGS AD L ar HI :=
  PMBSY.syscat_ok L ar C HI LY HIok.
Let ios_dtor : PMSPA.ios_dtor_spec RSEGS AD L ar HI :=
  PMBID.ios_dtor_ok L ar C HI LY HIok EXT locale_dtor.
Let src_dtor : PMSPA.src_dtor_spec RSEGS AD L ar HI :=
  PMBSD.src_dtor_ok L ar C HI LY HIok opdel locale_dtor ios_dtor.
Let is_base10 : PMSPA.is_base10_spec RSEGS AD L ar HI :=
  PMBB10.is_base10_ok L ar C HI LY HIok IL ICok ILY.
Let str_resize : PMSPA.str_resize_spec RSEGS AD L ar HI :=
  PMBRZ.str_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.
Let ann_shrink : PMBX.ann_shrink_spec L ar HI :=
  PMBANN.ann_shrink_ok L ar C HI LY HIok EXT.
Let ann_delete : PMBX.ann_delete_spec L ar HI :=
  PMBANN.ann_delete_ok L ar C HI LY HIok EXT.
Let vec_clear : PMBX.vec_clear_spec L ar HI :=
  PMBVC.vec_clear_ok L ar C HI LY HIok ann_shrink.
Let vec_dtor : PMSPA.vec_dtor_spec RSEGS AD L ar HI :=
  PMBVD.vec_dtor_ok L ar C HI LY HIok vec_clear ann_delete opdel.
Let cone_mi : PMBX.cone_mi_spec L ar HI :=
  PMBCOMI.cone_mi_ok L ar C HI LY HIok EXT.
Let cone_miu : PMBX.cone_miu_spec L ar HI :=
  PMBCOMIU.cone_miu_ok L ar C HI LY HIok EXT.
Let cone_ms : PMBX.cone_ms_spec L ar HI :=
  PMBCOMS.cone_ms_ok L ar C HI LY HIok EXT.
Let cone_msu : PMBX.cone_msu_spec L ar HI :=
  PMBCOMSU.cone_msu_ok L ar C HI LY HIok EXT.
Let slow_ms : PMBX.slow_ms_spec L ar HI :=
  PMBSLMS.slow_ms_ok L ar C HI LY HIok EXT opnew opdel.
Let slow_msu : PMBX.slow_msu_spec L ar HI :=
  PMBSLMSU.slow_msu_ok L ar C HI LY HIok EXT opnew opdel.
Let slow_miu : PMBX.slow_miu_spec L ar HI :=
  PMBSLMIU.slow_miu_ok L ar C HI LY HIok EXT opnew opdel.
Let slow_mi : PMBX.slow_mi_spec L ar HI :=
  PMBSLMI.slow_mi_ok L ar C HI LY HIok EXT opnew opdel.
Let make_ec : PECSB.make_ec_spec L ar HI :=
  PEBCERR.make_ec_ok L ar C HI LY HIok EXT.
Let reader_ctor : PECSB.reader_ctor_spec L ar HI :=
  PMBRD.reader_ctor_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew slow_mi.
Let reset : PECSB.reset_spec L ar HI :=
  PEBCRS.reset_ok L ar C HI LY HIok vec_clear cone_miu.
Let str_ctor_c : PECSB.str_ctor_c_spec L ar HI :=
  PEBCSTR.str_ctor_c_ok L ar C HI LY HIok opnew.
Let iss_ctor_c : PECSB.iss_ctor_c_spec L ar HI :=
  PEBCISS.iss_ctor_c_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew.
Let validate_rd : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD) :=
  PECVALBR.validate_fun_ok L ar C HI LY HIok GAP.
Let validate_enc : PECVSA.validate_fun_spec RSEGS AD L ar HI (pe_validate_enc EE) :=
  PECVALB.validate_fun_ok L ar C HI LY HIok GAP.
Let OPNWP : PESKA.opnew_n_spec RSEGS AD L ar HI (PESKA.spa_nmax P) (PESKA.spa_cap P) :=
  PESKA.opnew_n_spec_mono RSEGS AD L ar HI _ _ _ _ NMAXOK LEARNOK (PMBOPNW.opnew_n_ok L ar C HI LY HIok MALLOCN).
Let push_back : PESKA.push_back_specA RSEGS AD EE L ar HI P :=
  PEBSKP.push_back_ok L ar C HI P LY HIok EXT PO OPNWP opdel MEMCPYN NMAXOK.
Let push_back_ind : PEPBI.push_back_indZ_specA RSEGS AD L ar HI 0xb2794 P :=
  PEBPBI.push_back_ind_ok L ar C HI P LY HIok push_back.
Let econe_k : PECEPX.econe_k_spec RSEGS AD EE L ar HI :=
  PEBEPF.econe_k_ok L ar C HI LY HIok EXT.
Let econe_kl : PECEPX.econe_kl_spec RSEGS AD EE L ar HI :=
  PEBEQF.econe_kl_ok L ar C HI LY HIok EXT.
Let eslow_k : PECEPX.eslow_k_spec RSEGS AD EE L ar HI :=
  PEBEPUSH.eslow_k_ok L ar C HI LY HIok EXT opnew opdel.
Let eslow_kl : PECEPX.eslow_kl_spec RSEGS AD EE L ar HI :=
  PEBEQPUSH.eslow_kl_ok L ar C HI LY HIok EXT opnew opdel.
Let put_length : PECSB.put_length_spec L ar HI P :=
  PEBENCPL.put_length_ok L ar C HI P LY HIok PO push_back push_back_ind.
Let v_null : PECSB.v_null_spec L ar HI P :=
  PEBENCN.v_null_ok L ar C HI P LY HIok PO push_back_ind.
Let v_bool : PECSB.v_bool_spec L ar HI P :=
  PEBENCT.v_bool_ok L ar C HI P LY HIok PO push_back.
Let v_uint64 : PECSB.v_uint64_spec L ar HI P :=
  PEBENCVU.v_uint64_ok L ar C HI P LY HIok PO push_back push_back_ind.
Let v_int64 : PECSB.v_int64_spec L ar HI P :=
  PEBENCVI.v_int64_ok L ar C HI P LY HIok PO push_back push_back_ind.
Let v_double : PECSB.v_double_spec L ar HI P :=
  PEBENCD.v_double_ok L ar C HI P LY HIok PO push_back push_back_ind.
Let v_flush : PECSB.v_flush_spec L ar HI P :=
  PEBENCF.v_flush_ok L ar C HI P LY HIok.
Let v_begin_arr : PECSB.v_begin_arr_spec L ar HI P :=
  PEBENCBG.v_begin_arr_ok L ar C HI P LY HIok PO push_back make_ec econe_k eslow_k.
Let v_begin_arr_len : PECSB.v_begin_arr_len_spec L ar HI P :=
  PEBENCBL.v_begin_arr_len_ok L ar C HI P LY HIok PO push_back make_ec put_length econe_kl eslow_kl.
Let v_begin_obj : PECSB.v_begin_obj_spec L ar HI P :=
  PEBENCBG.v_begin_obj_ok L ar C HI P LY HIok PO push_back make_ec econe_k eslow_k.
Let v_begin_obj_len : PECSB.v_begin_obj_len_spec L ar HI P :=
  PEBENCBL.v_begin_obj_len_ok L ar C HI P LY HIok PO push_back make_ec put_length econe_kl eslow_kl.
Let v_end_arr : PECSB.v_end_arr_spec L ar HI P :=
  PEBENCE.v_end_arr_ok L ar C HI P LY HIok PO push_back make_ec (PEBEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).
Let v_end_obj : PECSB.v_end_obj_spec L ar HI P :=
  PEBENCE.v_end_obj_ok L ar C HI P LY HIok PO push_back make_ec (PEBEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).
Let v_key : PECSB.v_key_spec L ar HI P :=
  PEBENCK.v_key_ok L ar C HI P LY HIok PO push_back put_length validate_enc.
Let v_string : PECSB.v_string_spec L ar HI P :=
  PEBENCST.v_string_ok L ar C HI P LY HIok PO push_back put_length make_ec validate_enc.
Let fill_buffer : PECSB.fill_buffer_spec L ar HI :=
  PECFILLB.fill_buffer_ok L ar C HI LY HIok IL ICok ILY.
Let peek : PECSB.peek_spec L ar HI :=
  PECPEEKB.peek_ok L ar C HI LY HIok fill_buffer.
Let ignore : PECSB.ignore_spec L ar HI :=
  PECIGNB.ignore_ok L ar C HI LY HIok fill_buffer.
Let src_read : PECSB.src_read_spec L ar HI :=
  PECREADB.src_read_ok L ar C HI LY HIok IL ICok ILY fill_buffer.
Let cstr_resize : PECTXSA.cstr_resize_spec RSEGS AD L ar HI :=
  PECRSZB.cstr_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.
Let csrd_read : PECTXSA.csrd_read_spec RSEGS AD L ar HI :=
  PECSRD5B.csrd_read_ok L ar C HI LY HIok IL ICok ILY cstr_resize fill_buffer (PECFILLTBB.cfill_tb_ok L ar C HI LY HIok IL ICok ILY).
Let read_span : PECSB.read_span_spec L ar HI :=
  PECRS3B.read_span_ok L ar C HI LY HIok IL ICok ILY fill_buffer csrd_read.
Let get_length : PECSB.get_length_spec L ar HI P :=
  PEBCGL.get_length_ok L ar C HI P LY HIok src_read make_ec.
Let end_array : PECSB.end_array_spec L ar HI P :=
  PEBCEND.end_array_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_arr.
Let end_object : PECSB.end_object_spec L ar HI P :=
  PEBCEND.end_object_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_obj.
Let read_key : PECSB.read_key_spec L ar HI P :=
  PEBCRDKEY.read_key_ok L ar C HI P LY HIok IL ICok ILY PO get_length read_span validate_rd make_ec v_key.
Let begin_array : PECSB.begin_array_spec L ar HI P :=
  PEBCBA.begin_array_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec cone_mi slow_mi cone_ms slow_ms cone_msu slow_msu v_begin_arr v_begin_arr_len.
Let begin_object : PECSB.begin_object_spec L ar HI P :=
  PEBCBO.begin_object_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec cone_mi slow_mi cone_ms slow_ms cone_msu slow_msu v_begin_obj v_begin_obj_len.
Let read_value : PECSB.read_value_spec L ar HI P :=
  PEBCRV.read_value_ok L ar C HI P LY HIok IL ICok ILY PO src_read get_length read_span validate_rd is_base10 make_ec begin_array begin_object v_null v_bool v_uint64 v_int64 v_double v_string.
Let rtv : PECSB.rtv_spec L ar HI P :=
  PEBCRTV.rtv_ok L ar C HI P LY HIok IL ICok ILY src_read make_ec read_value.
Let parse : PECSB.parse_spec L ar HI P :=
  PEBCLP.parse_ok L ar C HI P LY HIok IL ICok ILY rtv read_value read_key end_array end_object peek ignore make_ec vec_clear.
Let reader_read : PECRRZ.reader_read_specZ RSEGS AD AAD EE L ar HI P :=
  PEBCRR.reader_read_ok L ar C HI P LY HIok reset parse.
Let estk_dtor : PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb4794 :=
  PEBEKD.estk_dtor_ok L ar C HI LY HIok (PEBEKC.clear_e_ok L ar C HI LY HIok EXT) (PEBEKAN.ann_delete_e_ok L ar C HI LY HIok EXT) opdel.
Let sink_dtor : PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaafe4 :=
  PEBSKD.sink_dtor_ok L ar C HI P LY HIok (PEBSKC.clear_b_ok L ar C HI LY HIok EXT) (PEBSKAN.ann_delete_b_ok L ar C HI LY HIok EXT) opdel.
Let HARN : harness_stmt :=
  PEBCHN.harness_call_ok L ar C IL HI P LY HIok ICok ILY EXT PO PMODE str_ctor_c iss_ctor_c reader_ctor syscat reader_read vec_dtor opdel src_dtor locale_dtor ios_dtor estk_dtor sink_dtor.

Theorem top_iface_asm (PayOk PayExport : list byte -> Prop) :
  PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
  lib_iface_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.
Proof using LY ILY MCC PO PMODE NMAXOK LEARNOK FAM RO.
  intros PIN POUT. apply (PECTB.top_iface_okA_x L ar C tk tb LY). exact (HARN PayOk PayExport PIN POUT).
Qed.
End Asm.
End PECASMB.
