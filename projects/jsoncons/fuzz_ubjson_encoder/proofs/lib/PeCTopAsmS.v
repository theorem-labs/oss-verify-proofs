(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceE L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PeSpecsS PeLayoutS PeCLayout PeCLayoutS PeCSink PeCModel PeCSpecs PeCSpecsS PeCValSpec PeCStatics PeCTopS
     PeCValS PeCValSr PeB10S PeSCEnd PeSCRtv PeSEvec PeHeapP PeSSinkPush Es0Opnew Es0Opdel PeLocS PeSysS PeSIosDtor PeSSrcDtor PeSResize PeSEncEnd PeSEncBeg PeSEncBegL PeSEncKey PeSEncStr PeSEncFlush PeSCReset PeSCErr PeSCRdCtor PeSCStr PeSCIss PeCRdValS PeCGetLenS PeCRdKeyS PeSCParseD PeSCParse1 PeSCParse2 PeSCParse3 PeSCParse4 PeSCParse5 PeSCParse PeSCHarness PeCBegArrS PeCSrcFillS PeCBegObjS PeSEncNull PeSEncBool PeCSrcReadS PeCSrcPeekS PeCSrcIgnS PeSEncPutLen PeSEncU64 PeSEncI64 PeSEncDbl PeCResizeS PeCSrcFillTbS PeCSrd5S PeCRdSpan3S PeCTxtSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCTopAsmS () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCSpecsS5PECSS6pay_inC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCSpecsS5PECSS7pay_outC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCTopS5PECTS>top_iface_ok_xC13~~~K47Corelib7Numbers7BinNums8positive03c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmS7PECASMS2tbC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECASMS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Section Asm.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
(* [comment removed for export] *)
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPM : hl_k_per_malloc L <= 1.          (* [comment removed for export] *)
Hypothesis PO : PESK.sink_policy_ok P.
Hypothesis PMODE : PESK.sp_mode P.

(* [comment removed for export] *)
Definition tb : Z := PECTS.TOPB0 + PESK.sp_B P.
(* [comment removed for export] *)
Definition harness_stmt : Prop :=
  forall (PayOk PayExport : list byte -> Prop),
    PECSS.pay_in P PayOk -> PECSS.pay_out P PayExport ->
    lib_call_ok_x (PECTS.TopLay L tb) SCFG HI PECTS.TopLS PayOk PayExport.

(* [comment removed for export] *)
Record rows_open : Prop := ROWS {
  ro_OPNP : PEHP.opnewP_spec RSEGS PeLayoutS.ADDR_S L HI P PESSK.NMAXP   (* [comment removed for export] *);
  ro_OPDP : PEHP.opdelP_spec RSEGS PeLayoutS.ADDR_S L HI P   (* [comment removed for export] *)
}.
Variable RO : rows_open.
Let OPNP : PEHP.opnewP_spec RSEGS PeLayoutS.ADDR_S L HI P PESSK.NMAXP := ro_OPNP RO.
Let OPDP : PEHP.opdelP_spec RSEGS PeLayoutS.ADDR_S L HI P := ro_OPDP RO.

(* [comment removed for export] *)
Let opnew : PMSP.opnew_spec RSEGS AD L HI :=
  L5NEW.opnew_ok L HI LY HIok.   (* [comment removed for export] *)
Let opdel : PMSP.opdel_spec RSEGS AD L HI :=
  L5DEL.opdel_ok L HI LY HIok.   (* [comment removed for export] *)
Let opdel_sized : PMSP.opdel_sized_spec RSEGS AD L HI :=
  L5DEL.opdel_sized_ok L HI LY HIok.   (* [comment removed for export] *)
Let locale_ctor : PMSP.locale_ctor_spec RSEGS AD L HI :=
  PMLOC.locale_ctor_ok L HI LY HIok.   (* [comment removed for export] *)
Let locale_dtor : PMSP.locale_dtor_spec RSEGS AD L :=
  PMLOC.locale_dtor_ok L.   (* [comment removed for export] *)
Let syscat : PMSP.syscat_spec RSEGS AD L HI :=
  PMSYS.syscat_ok L HI LY HIok.   (* [comment removed for export] *)
Let ios_dtor : PMSP.ios_dtor_spec RSEGS AD L HI :=
  PMSID.ios_dtor_ok L HI LY HIok locale_dtor.   (* [comment removed for export] *)
Let src_dtor : PMSP.src_dtor_spec RSEGS AD L HI :=
  PMSSD.src_dtor_ok L HI LY HIok opdel locale_dtor ios_dtor.   (* [comment removed for export] *)
Let is_base10 : PMSP.is_base10_spec RSEGS AD L :=
  PEB10S.is_base10_ok L.   (* [comment removed for export] *)
Let str_resize : PMSP.str_resize_spec RSEGS AD L HI :=
  PMSRZ.str_resize_ok L HI LY HIok opnew opdel.   (* [comment removed for export] *)
Let make_ec : PECSS.make_ec_spec L HI :=
  PESCERR.make_ec_ok L HI LY HIok.   (* [comment removed for export] *)
Let reader_ctor : PMSP.reader_ctor_spec RSEGS AD L HI :=
  PESCRC.reader_ctor_ok L HI LY HIok locale_ctor opnew.   (* [comment removed for export] *)
Let reset : PMSP.reset_spec RSEGS AD L HI :=
  PESCRS.reset_ok L HI LY HIok.   (* [comment removed for export] *)
Let str_ctor_c : PECSS.str_ctor_c_spec L HI :=
  PESCSTR.str_ctor_c_ok L HI LY HIok opnew.   (* [comment removed for export] *)
Let iss_ctor_c : PECSS.iss_ctor_c_spec L HI :=
  PESCISS.iss_ctor_c_ok L HI LY HIok locale_ctor opnew.   (* [comment removed for export] *)
Let validate_rd : PECVS.validate_fun_spec RSEGS AD L (pa_validate AD) :=
  PECVALSR.validate_fun_ok L.   (* [comment removed for export] *)
Let validate_enc : PECVS.validate_fun_spec RSEGS AD L (pe_validate_enc EE) :=
  PECVALS.validate_fun_ok L.   (* [comment removed for export] *)
Let push_back : PESK.push_back_spec RSEGS AD EE L HI PMSP.T3 PMSP.T4 P :=
  PESSK.push_back_ok L HI EE P LY HIok eq_refl (PESK.spo_nmax P PO) OPNP OPDP.   (* [comment removed for export] *)
Let evec_alloc : PECSS.evec_alloc_spec L HI :=
  PESEV.evec_alloc_ok L HI EE LY HIok eq_refl opnew.   (* [comment removed for export] *)
Let evec_sbdtor : PECSS.evec_sbdtor_spec L HI :=
  PESEV.evec_sbdtor_ok L HI EE LY HIok eq_refl opdel.   (* [comment removed for export] *)
Let put_length : PECSS.put_length_spec L HI P :=
  PESENCPL.put_length_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_null : PECSS.v_null_spec L HI P :=
  PESENCN.v_null_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_bool : PECSS.v_bool_spec L HI P :=
  PESENCT.v_bool_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_uint64 : PECSS.v_uint64_spec L HI P :=
  PESENCU6.v_uint64_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_int64 : PECSS.v_int64_spec L HI P :=
  PESENCI6.v_int64_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_double : PECSS.v_double_spec L HI P :=
  PESENCD.v_double_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_flush : PECSS.v_flush_spec L HI P :=
  PESENCF.v_flush_ok L HI P.   (* [comment removed for export] *)
Let v_begin_arr : PECSS.v_begin_arr_spec L HI P :=
  PESENCB.v_begin_arr_ok L HI P LY HIok PO push_back make_ec evec_alloc evec_sbdtor.   (* [comment removed for export] *)
Let v_begin_arr_len : PECSS.v_begin_arr_len_spec L HI P :=
  PESENCBL.v_begin_arr_len_ok L HI P LY HIok PO push_back make_ec evec_alloc evec_sbdtor put_length.   (* [comment removed for export] *)
Let v_begin_obj : PECSS.v_begin_obj_spec L HI P :=
  PESENCB.v_begin_obj_ok L HI P LY HIok PO push_back make_ec evec_alloc evec_sbdtor.   (* [comment removed for export] *)
Let v_begin_obj_len : PECSS.v_begin_obj_len_spec L HI P :=
  PESENCBL.v_begin_obj_len_ok L HI P LY HIok PO push_back make_ec evec_alloc evec_sbdtor put_length.   (* [comment removed for export] *)
Let v_end_arr : PECSS.v_end_arr_spec L HI P :=
  PESENC.v_end_arr_ok L HI P LY HIok PO push_back make_ec.   (* [comment removed for export] *)
Let v_end_obj : PECSS.v_end_obj_spec L HI P :=
  PESENC.v_end_obj_ok L HI P LY HIok PO push_back make_ec.   (* [comment removed for export] *)
Let v_key : PECSS.v_key_spec L HI P :=
  PESENCK.v_key_ok L HI P LY HIok PO push_back put_length validate_enc.   (* [comment removed for export] *)
Let v_string : PECSS.v_string_spec L HI P :=
  PESENCS.v_string_ok L HI P LY HIok PO push_back put_length make_ec validate_enc.   (* [comment removed for export] *)
Let fill_buffer : PECSS.fill_buffer_spec L HI :=
  PECFILLS.fill_buffer_ok L HI LY HIok.   (* [comment removed for export] *)
Let peek : PECSS.peek_spec L HI :=
  PECPEEKS.peek_ok L HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let ignore : PECSS.ignore_spec L HI :=
  PECIGNS.ignore_ok L HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let src_read : PECSS.src_read_spec L HI :=
  PECREADS.src_read_ok L HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let cstr_resize : PECTXS.cstr_resize_spec RSEGS AD L HI :=
  PECRSZS.cstr_resize_ok L HI LY HIok opnew opdel.   (* [comment removed for export] *)
Let cfill_tb : PECFILLTBS.cfill_tb_spec L HI :=
  PECFILLTBS.cfill_tb_ok L HI LY HIok.   (* [comment removed for export] *)
Let csrd_read : PECTXS.csrd_read_spec RSEGS AD L HI :=
  PECSRD5S.csrd_read_ok L HI LY HIok cstr_resize fill_buffer cfill_tb.   (* [comment removed for export] *)
Let read_span : PECSS.read_span_spec L HI :=
  PECRS3S.read_span_ok L HI LY HIok fill_buffer csrd_read.   (* [comment removed for export] *)
Let get_length : PECSS.get_length_spec L HI P :=
  PECGLS.get_length_ok L HI P LY HIok src_read make_ec.   (* [comment removed for export] *)
Let end_array : PECSS.end_array_spec L HI P :=
  PESCEND.end_array_ok L HI P LY HIok v_end_arr.   (* [comment removed for export] *)
Let end_object : PECSS.end_object_spec L HI P :=
  PESCEND.end_object_ok L HI P LY HIok v_end_obj.   (* [comment removed for export] *)
Let read_key : PECSS.read_key_spec L HI P :=
  PECRKS.read_key_ok L HI P LY HIok PO get_length read_span validate_rd make_ec v_key.   (* [comment removed for export] *)
Let begin_array : PECSS.begin_array_spec L HI P :=
  PECBAS.begin_array_ok L HI P LY HIok PO peek ignore src_read get_length make_ec opnew opdel v_begin_arr v_begin_arr_len.   (* [comment removed for export] *)
Let begin_object : PECSS.begin_object_spec L HI P :=
  PECBOS.begin_object_ok L HI P LY HIok PO peek ignore src_read get_length make_ec opnew opdel v_begin_obj v_begin_obj_len.   (* [comment removed for export] *)
Let read_value : PECSS.read_value_spec L HI P :=
  PECRVS.read_value_ok L HI P LY HIok PO src_read get_length read_span validate_rd is_base10 make_ec begin_array begin_object v_null v_bool v_uint64 v_int64 v_double v_string.   (* [comment removed for export] *)
Let rtv : PECSS.rtv_spec L HI P :=
  PESCRTV.rtv_ok L HI P LY HIok src_read make_ec read_value.   (* [comment removed for export] *)
Let parse_it1 : PESCLPD.iter_ok L HI P PESCLPD.lpG1 :=
  PESCLP1.parse_iter1 L HI P LY HIok PO rtv read_value.   (* [comment removed for export] *)
Let parse_it2 : PESCLPD.iter_ok L HI P PESCLPD.lpG2 :=
  PESCLP2.parse_iter2 L HI P LY HIok PO rtv read_value end_array.   (* [comment removed for export] *)
Let parse_it3 : PESCLPD.iter_ok L HI P PESCLPD.lpG3 :=
  PESCLP3.parse_iter3 L HI P LY HIok PO read_key end_object.   (* [comment removed for export] *)
Let parse_it4 : PESCLPD.iter_ok L HI P PESCLPD.lpG4 :=
  PESCLP5.parse_iter4G L HI P LY HIok PO peek ignore rtv end_array read_key end_object make_ec.   (* [comment removed for export] *)
Let parse : PECSS.parse_spec L HI P :=
  PESCLP.parse_ok L HI P LY HIok PO parse_it1 parse_it2 parse_it3 parse_it4.   (* [comment removed for export] *)
Let HARN : harness_stmt :=
  PESCH.harness_call_ok L HI P LY HIok KPM PO PMODE (PESCH.HDEPS L HI P str_ctor_c iss_ctor_c reader_ctor syscat reset parse opdel src_dtor OPDP locale_dtor ios_dtor).   (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem top_iface_asm (PayOk PayExport : list byte -> Prop) :
  PECSS.pay_in P PayOk -> PECSS.pay_out P PayExport ->
  lib_iface_ok_x (PECTS.TopLay L tb) SCFG HI PECTS.TopLS PayOk PayExport.
Proof using LY HIok KPM PO PMODE RO.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmS ()) ["Asm"] "h09PayExporth15PayOkh23PINh34POUTp;1p;2p;9g0000j10Tg000Uj17Tg0013j12Tg001Vj11Tg0026j26Tg003Gj25Tg004Yj13Tg005_l94Tg0076#0#0#0#7#2#1p-0[R0p,1PR1f1R2'61512p,6SCFG_P#3p,3bmKp,1Lp,2HIg007[p,2LYf3R1f2R3p,4HARNP1P3P2f0R3O4M94W3W2X00X10P2P3O2X00W1o"). Qed.
End Asm.
End PECASMS.
