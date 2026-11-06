(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceE L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PmSpecsX PeSpecsU PeLayoutU PeCLayout PeCLayoutU PeCSink PeCModel PeCSpecs PeCSpecsU PeCValSpec PeCStatics PeCTopU
     PeCValU PeCValUr PeB10U PeUCEnd PeUCRtv PeHeapP PeUSinkPush Eu0Opnew Eu0Opdel PeLocU PeSysU PeUIosDtor PeUSrcDtor PeUResize PeUEncEnd PeUEncFlush PeUCReset PeUCErr PeUCRdCtor PeUCStr PeUCIss PeUVecDtorP32 PeCRdValU PeCGetLenU PeCRdKeyU PeUCParseD PeUCParse1 PeUCParse2 PeUCParse3 PeUCParse4 PeUCParse5 PeUCParse PeURdRead PeUCHarness PeUEncKey PeUEncStr PeCSrcFillU PeUEncNull PeUEncBool PeCSrcReadU PeCSrcPeekU PeCSrcIgnU PeUEncBeg PeUEncPutLen PeUEncBegL PeCBegArrU PeCBegObjU PeUEncU64 PeUEncI64 PeUEncDbl PeCResizeU PeCSrcFillTbU PeCSrd5U PeCRdSpan3U PeCTxtSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCTopAsmU () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCSpecsU5PECSU6pay_inC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCSpecsU5PECSU7pay_outC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCTopU5PECTU>top_iface_ok_xC13~~~K47Corelib7Numbers7BinNums8positive03c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmU7PECASMU2tbC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECASMU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PeCLayoutU.CADDR_U.
Abbreviation EE := PeCLayoutU.EADDR_U.

Section Asm.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
(* [comment removed for export] *)
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPM : hl_k_per_malloc L <= 1.          (* [comment removed for export] *)
Hypothesis PO : PESK.sink_policy_ok P.
Hypothesis PMODE : PESK.sp_mode P.

(* [comment removed for export] *)
Definition tb : Z := PECTU.TOPB0 + PESK.sp_B P.
(* [comment removed for export] *)
Definition harness_stmt : Prop :=
  forall (PayOk PayExport : list byte -> Prop),
    PECSU.pay_in P PayOk -> PECSU.pay_out P PayExport ->
    lib_call_ok_x (PECTU.TopLay L tb) SCFG HI PECTU.TopLS PayOk PayExport.

(* [comment removed for export] *)
Record rows_open : Prop := ROWS {
  ro_OPNP : PEHP.opnewP_spec RSEGS PeLayoutU.ADDR_U L HI P PEUSK.NMAXP   (* [comment removed for export] *);
  ro_OPDP : PEHP.opdelP_spec RSEGS PeLayoutU.ADDR_U L HI P   (* [comment removed for export] *)
}.
Variable RO : rows_open.
Let OPNP : PEHP.opnewP_spec RSEGS PeLayoutU.ADDR_U L HI P PEUSK.NMAXP := ro_OPNP RO.
Let OPDP : PEHP.opdelP_spec RSEGS PeLayoutU.ADDR_U L HI P := ro_OPDP RO.

(* [comment removed for export] *)
Let opnew : PMSP.opnew_spec RSEGS AD L HI :=
  L5NEWU.opnew_ok L HI LY HIok.   (* [comment removed for export] *)
Let opdel : PMSP.opdel_spec RSEGS AD L HI :=
  L5DELU.opdel_ok L HI LY HIok.   (* [comment removed for export] *)
Let opdel_sized : PMSP.opdel_sized_spec RSEGS AD L HI :=
  L5DELU.opdel_sized_ok L HI LY HIok.   (* [comment removed for export] *)
Let locale_ctor : PMSP.locale_ctor_spec RSEGS AD L HI :=
  PMLOCU.locale_ctor_ok L HI LY HIok.   (* [comment removed for export] *)
Let locale_dtor : PMSP.locale_dtor_spec RSEGS AD L :=
  PMLOCU.locale_dtor_ok L.   (* [comment removed for export] *)
Let syscat : PMSP.syscat_spec RSEGS AD L HI :=
  PMSYSU.syscat_ok L HI LY HIok.   (* [comment removed for export] *)
Let ios_dtor : PMSP.ios_dtor_spec RSEGS AD L HI :=
  PMUID.ios_dtor_ok L HI LY HIok locale_dtor.   (* [comment removed for export] *)
Let src_dtor : PMSP.src_dtor_spec RSEGS AD L HI :=
  PMUSD.src_dtor_ok L HI LY HIok opdel locale_dtor ios_dtor.   (* [comment removed for export] *)
Let is_base10 : PMSP.is_base10_spec RSEGS AD L :=
  PEB10U.is_base10_ok L.   (* [comment removed for export] *)
Let str_resize : PMSP.str_resize_spec RSEGS AD L HI :=
  PMURZ.str_resize_ok L HI LY HIok opnew opdel.   (* [comment removed for export] *)
Let vec_dtor : PMSX.vec_dtor_spec RSEGS AD L HI :=
  PEUVD32.vec_dtor_ok L HI LY HIok opdel.   (* [comment removed for export] *)
Let make_ec : PECSU.make_ec_spec L HI :=
  PEUCERR.make_ec_ok L HI LY HIok.   (* [comment removed for export] *)
Let reader_ctor : PMSP.reader_ctor_spec RSEGS AD L HI :=
  PEUCRC.reader_ctor_ok L HI LY HIok locale_ctor opnew.   (* [comment removed for export] *)
Let reset : PMSP.reset_spec RSEGS AD L HI :=
  PEUCRS.reset_ok L HI LY HIok.   (* [comment removed for export] *)
Let str_ctor_c : PECSU.str_ctor_c_spec L HI :=
  PEUCSTR.str_ctor_c_ok L HI LY HIok opnew.   (* [comment removed for export] *)
Let iss_ctor_c : PECSU.iss_ctor_c_spec L HI :=
  PEUCISS.iss_ctor_c_ok L HI LY HIok locale_ctor opnew.   (* [comment removed for export] *)
Let validate_rd : PECVS.validate_fun_spec RSEGS AD L (pa_validate AD) :=
  PECVALUR.validate_fun_ok L.   (* [comment removed for export] *)
Let validate_enc : PECVS.validate_fun_spec RSEGS AD L (pe_validate_enc EE) :=
  PECVALU.validate_fun_ok L.   (* [comment removed for export] *)
Let push_back : PESK.push_back_spec RSEGS AD EE L HI PMSP.T3 PMSP.T4 P :=
  PEUSK.push_back_ok L HI EE P LY HIok eq_refl (PESK.spo_nmax P PO) OPNP OPDP.   (* [comment removed for export] *)
Let push_back_ind : PESK.push_back_ind_spec RSEGS AD L HI PMSP.T3 PMSP.T4 0x3898c P :=
  PEUSK.push_back_ind_ok L HI EE P LY HIok eq_refl push_back.   (* [comment removed for export] *)
Let put_length : PECSU.put_length_spec L HI P :=
  PEUENCPL.put_length_ok L HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_null : PECSU.v_null_spec L HI P :=
  PEUENCN.v_null_ok L HI P LY HIok PO push_back_ind.   (* [comment removed for export] *)
Let v_bool : PECSU.v_bool_spec L HI P :=
  PEUENCT.v_bool_ok L HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_uint64 : PECSU.v_uint64_spec L HI P :=
  PEUENCU6.v_uint64_ok L HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_int64 : PECSU.v_int64_spec L HI P :=
  PEUENCI6.v_int64_ok L HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_double : PECSU.v_double_spec L HI P :=
  PEUENCD.v_double_ok L HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_flush : PECSU.v_flush_spec L HI P :=
  PEUENCF.v_flush_ok L HI P.   (* [comment removed for export] *)
Let v_begin_arr : PECSU.v_begin_arr_spec L HI P :=
  PEUENCB.v_begin_arr_ok L HI P LY HIok PO push_back make_ec opnew opdel.   (* [comment removed for export] *)
Let v_begin_arr_len : PECSU.v_begin_arr_len_spec L HI P :=
  PEUENCBL.v_begin_arr_len_ok L HI P LY HIok PO push_back make_ec opnew opdel put_length.   (* [comment removed for export] *)
Let v_begin_obj : PECSU.v_begin_obj_spec L HI P :=
  PEUENCB.v_begin_obj_ok L HI P LY HIok PO push_back make_ec opnew opdel.   (* [comment removed for export] *)
Let v_begin_obj_len : PECSU.v_begin_obj_len_spec L HI P :=
  PEUENCBL.v_begin_obj_len_ok L HI P LY HIok PO push_back make_ec opnew opdel put_length.   (* [comment removed for export] *)
Let v_end_arr : PECSU.v_end_arr_spec L HI P :=
  PEUENC.v_end_arr_ok L HI P LY HIok PO push_back make_ec.   (* [comment removed for export] *)
Let v_end_obj : PECSU.v_end_obj_spec L HI P :=
  PEUENC.v_end_obj_ok L HI P LY HIok PO push_back make_ec.   (* [comment removed for export] *)
Let v_key : PECSU.v_key_spec L HI P :=
  PEUENCK.v_key_ok L HI P LY HIok PO push_back put_length validate_enc.   (* [comment removed for export] *)
Let v_string : PECSU.v_string_spec L HI P :=
  PEUENCS.v_string_ok L HI P LY HIok PO push_back put_length make_ec validate_enc.   (* [comment removed for export] *)
Let fill_buffer : PECSU.fill_buffer_spec L HI :=
  PECFILLU.fill_buffer_ok L HI LY HIok.   (* [comment removed for export] *)
Let peek : PECSU.peek_spec L HI :=
  PECPEEKU.peek_ok L HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let ignore : PECSU.ignore_spec L HI :=
  PECIGNU.ignore_ok L HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let src_read : PECSU.src_read_spec L HI :=
  PECREADU.src_read_ok L HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let cstr_resize : PECTXS.cstr_resize_spec RSEGS AD L HI :=
  PECRSZU.cstr_resize_ok L HI LY HIok opnew opdel.   (* [comment removed for export] *)
Let cfill_tb : PECFILLTBU.cfill_tb_spec L HI :=
  PECFILLTBU.cfill_tb_ok L HI LY HIok.   (* [comment removed for export] *)
Let csrd_read : PECTXS.csrd_read_spec RSEGS AD L HI :=
  PECSRD5U.csrd_read_ok L HI LY HIok cstr_resize fill_buffer cfill_tb.   (* [comment removed for export] *)
Let read_span : PECSU.read_span_spec L HI :=
  PECRS3U.read_span_ok L HI LY HIok fill_buffer csrd_read.   (* [comment removed for export] *)
Let get_length : PECSU.get_length_spec L HI P :=
  PECGLU.get_length_ok L HI P LY HIok src_read make_ec.   (* [comment removed for export] *)
Let end_array : PECSU.end_array_spec L HI P :=
  PEUCEND.end_array_ok L HI P LY HIok v_end_arr.   (* [comment removed for export] *)
Let end_object : PECSU.end_object_spec L HI P :=
  PEUCEND.end_object_ok L HI P LY HIok v_end_obj.   (* [comment removed for export] *)
Let read_key : PECSU.read_key_spec L HI P :=
  PECRKU.read_key_ok L HI P LY HIok PO get_length read_span validate_rd make_ec v_key.   (* [comment removed for export] *)
Let begin_array : PECSU.begin_array_spec L HI P :=
  PECBAU.begin_array_ok L HI P LY HIok PO peek ignore src_read get_length make_ec opnew opdel v_begin_arr v_begin_arr_len.   (* [comment removed for export] *)
Let begin_object : PECSU.begin_object_spec L HI P :=
  PECBOU.begin_object_ok L HI P LY HIok PO peek ignore src_read get_length make_ec opnew opdel v_begin_obj v_begin_obj_len.   (* [comment removed for export] *)
Let read_value : PECSU.read_value_spec L HI P :=
  PECRVU.read_value_ok L HI P LY HIok PO src_read get_length read_span validate_rd is_base10 make_ec begin_array begin_object v_null v_bool v_uint64 v_int64 v_double v_string.   (* [comment removed for export] *)
Let rtv : PECSU.rtv_spec L HI P :=
  PEUCRTV.rtv_ok L HI P LY HIok src_read make_ec read_value.   (* [comment removed for export] *)
Let parse_it1 : PEUCLPD.iter_ok L HI P PEUCLPD.lpG1 :=
  PEUCLP1.parse_iter1 L HI P LY HIok PO rtv read_value.   (* [comment removed for export] *)
Let parse_it2 : PEUCLPD.iter_ok L HI P PEUCLPD.lpG2 :=
  PEUCLP2.parse_iter2 L HI P LY HIok PO rtv read_value end_array.   (* [comment removed for export] *)
Let parse_it3 : PEUCLPD.iter_ok L HI P PEUCLPD.lpG3 :=
  PEUCLP3.parse_iter3 L HI P LY HIok PO read_key end_object.   (* [comment removed for export] *)
Let parse_it4 : PEUCLPD.iter_ok L HI P PEUCLPD.lpG4 :=
  PEUCLP5.parse_iter4G L HI P LY HIok PO peek ignore rtv end_array read_key end_object make_ec.   (* [comment removed for export] *)
Let parse : PECSU.parse_spec L HI P :=
  PEUCLP.parse_ok L HI P LY HIok PO parse_it1 parse_it2 parse_it3 parse_it4.   (* [comment removed for export] *)
Let reader_read : PECSU.reader_read_spec L HI P :=
  PEURR.reader_read_ok L HI P LY HIok reset parse.   (* [comment removed for export] *)
Let HARN : harness_stmt :=
  PEUCH.harness_call_ok L HI P LY HIok KPM PO PMODE (PEUCH.HDEPS L HI P str_ctor_c iss_ctor_c reader_ctor syscat reader_read vec_dtor opdel src_dtor OPDP locale_dtor ios_dtor).   (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem top_iface_asm (PayOk PayExport : list byte -> Prop) :
  PECSU.pay_in P PayOk -> PECSU.pay_out P PayExport ->
  lib_iface_ok_x (PECTU.TopLay L tb) SCFG HI PECTU.TopLS PayOk PayExport.
Proof using LY HIok KPM PO PMODE RO.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmU ()) ["Asm"] "h09PayExporth15PayOkh23PINh34POUTp;1p;2p;9g0000j10Tg000Uj17Tg0013j12Tg001Vj11Tg0026j26Tg003Gj25Tg004Yj13Tg005_l94Tg0076#0#0#0#7#2#1p-0[R0p,1PR1f1R2'61512p,6SCFG_P#3p,3bmKp,1Lp,2HIg007[p,2LYf3R1f2R3p,4HARNP1P3P2f0R3O4M94W3W2X00X10P2P3O2X00X10P2P3O2X00W1o"). Qed.
End Asm.
End PECASMU.
