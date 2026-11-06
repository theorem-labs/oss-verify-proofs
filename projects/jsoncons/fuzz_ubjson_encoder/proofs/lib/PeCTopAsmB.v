(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5DefsA XIcptAs0B0 L5CoreA
     HeapIfaceAEx HeapIfaceAExI HeapIfaceAEr LibIface LibIfaceAB LibIfaceAE
     PmLayout PmLayoutA PnLayout PeLayoutA PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PeSpecsAmc PeBImgGap
     PeCLayout PeCLayoutB PeCSink PeCModel PeCSpecs PeCStatics PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCTxtSpecsA PeCValSpecA PeCDtorSpecsA PeTopAL PeCTopB
     PeBCStr PeBCIss PeBCParse PeBEPusq PeBSinkPush PeBCBegArr PeBCBegObj PeBEncBgn PeBEncBgnL PeBEncDbl PeBEncEnd PeBCRdVal PeCEPushSpecsA PeBEPushF PeBEPusqF PeBEPush PeBOpnew PeBOpdel PeBLoc PeBSys PeBIosDtor PeBSrcDtor PeBResize PeBEncFlush PeSpecsBXJ PeBAnn PeBVecClear PeBConeMiu PeBCReset PeBCErr PeBCEnd PeBCRdCtor PeBCRtv PeBSlowMi PeBOpnewN PeBConeMi PeBConeMs PeBConeMsu PeBSlowMs PeBSlowMsu PeBSlowMiu PeBEncBool PeBCHarness PeBCRdKey PeBCGetLen PeBSnkDtor PeBSnkClr PeBSnkAnn PeBEstkDtor PeBEstkClr PeBEstkAnn PeBCSrcFill PeBCSrcPeek PeBCSrcIgn PeBCSrcRead PeBCRdSpan3 PeBCSrd5 PeBCResize PeBCSrcFillTb PeBPbIndSpec PeBPbInd PeBEncStr PeBCVal PeBCValR PeBB10 PeBVecDtor PeBEncNull PeBEncU64 PeBEncPutLen PeBEncI64 PeBEncKey PeCRdReadSpecZ PeBCRdRead.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCTopAsmB () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ri_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan7L5CoreA4L5CA9amodel_okC13~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCSinkA5PESKA<opnew_n_specC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M?loaded_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCLayoutB7CADDR_BC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmB7PECASMB2HIC13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAb5PECSB:parse_specC13~~~k89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmB7PECASMB9rows_open01C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAb5PECSB6pay_inC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAb5PECSB7pay_outC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ9strict_ofC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCTopB5PECTB?top_iface_okA_xC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmB7PECASMB2tkC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmB7PECASMB2tbC13~~~".
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
(* [comment removed for export] *)
Hypothesis LY : PMB.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition inst_ok (HI : asan_iface) : Prop :=
  HAJ.asan_iface_okR L ar C SCFG HI /\ aicpt_ok L ar IL SCFG HI /\ HAJ.asan_ext_ok L ar SCFG HI PMB.EXT /\ PMBGAP.rt_img_gap HI.
(* [comment removed for export] *)
Definition fam_ok : Prop := HAR.asan_famR_ok L ar C SCFG LR HIk /\ (forall D, inst_ok (HIk D)).
Hypothesis FAM : fam_ok.

(* [comment removed for export] *)
Definition HI : asan_iface := HIk [].
Let IOK : inst_ok HI := proj2 FAM [].
Let HIok : HAJ.asan_iface_okR L ar C SCFG HI := proj1 IOK.
Let ICok : aicpt_ok L ar IL SCFG HI := proj1 (proj2 IOK).
Let EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT := proj1 (proj2 (proj2 IOK)).
Let GAP : PMBGAP.rt_img_gap HI := proj2 (proj2 (proj2 IOK)).
(* [comment removed for export] *)
Let MALLOCN : HAR.amallocN_spec L ar SCFG (fun _ => HI) := fun D => HAR.fr_mallocN L ar C SCFG LR HIk (proj1 FAM) [].
(* [comment removed for export] *)
Let MEMCPYN : HAR.amemcpyN_spec_at L ar SCFG (fun _ => HI) (hl_asan_memcpy L) := fun D => HAR.fr_memcpyN L ar C SCFG LR HIk (proj1 FAM) [].
(* [comment removed for export] *)
Local Lemma opnew_n_le (N N' : Z) : N <= N' -> PESKA.opnew_n_spec RSEGS AD L ar HI N' -> PESKA.opnew_n_spec RSEGS AD L ar HI N.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmB ()) ["Asm"] "h01Nh12N'h24__x1h34__x2h44__x3h52AMh62Awh72FFh83G10h92HKh:2Hnh;1Kh<2LBh=2LEh>2LKh?1Mh@1RhA2RIhB1WhC7__arithhD4__ffhE8__varmaphF5__withG2crhH2fxhI5modelhJ1nhK1rhL2spp;2p;1p;8p;3p;4p;7g0000j21Tg000Lj10Tg0011j1HTg001Vj19Tg0024j1BTg002Wj2QTg003Cj1PTg003ej2NTg004Ej14Tg004ej1GTg0061j8FTg007=j2ETg008Sj1DTg0093j1\Tg009Qj3VTg00:4j2UTg00;<j2TTg00;bj3?Tg00<<j25Tg00<Xj27Tg00=3j1>Tg00=Rj26Tg00>;j3=Tg00>dj2OTg00?Pj3MTg00@0j2;Tg00@Nj1LTg00@lj4:Tg00AJj1ITg00Ahj1JTg00BSj2KTg00C6j23Tg00CYj4<Tg00DDj1RTg00Dfj2STg00EHj2_Tg00Ebj2^Tg00FNj3]Tg00Fmj4[Tg00G_j7WTg00I5j7XTg00IYj7YTg00J=j8ZTf3R0g00Jag00L3f2R1f1R2g00M@R3f0R4FWp=CP2g00NPR5g00NoR6P6g00OOR7P4g00OoFXp=2g00POR8P2g00PmP4C<p=8P1P5P6P6P7P2P4FYp=AP0P5P6P6P7P1P2P4GZp=@1124p,6SCFG_PR5p,1LR9p,2arR:P2CCg00QTg00RaR;#0R<#HR=#9R>%0<#0R?#0#0#0#9R@#BRA'Q%9?#B#P\Ag00SFg00T<1N88#4R?g00UD#4RBg00VPP3f7R3f6RCf5RDP0f4REf:RFf9RG#GGF1EDFPFg00W[#DO1f>RH%0=#\g00XQ5V>'U1T@D5?Ag00XmRA/5CfDR@,1C'7fBfAf@f?PHf=f<f;PFPGf8RGP3PCPDPEP0P1P2g00YKREg00Z7RD#>RC#>,68168C168D5=85=8g00ZV'O%DE3M%4EP81;81P2P81;80P0%L8C:C:%I8%J8REP81K8Ag00[B138;R;C<,2ERD138=R=,8;,2E5AE%R6R6PE138<R<,8=,2EP618;<,2E9AEDC@C@1SE7P4P1g00[iREg00\IR7'_1^41=?E7dA]8A2C[bDbEbFX28X38X4815A41141'7110115A11110'7[[^28^38^48P4fFfEPGP2P@O5bCOBW:W8W9W5WAXK8XL8XJ8WGX6?X>BW7W<W;WIW?W@WHP5P9P:P0CCeWBW=X18X08P2P4O2X18X08P2P4O2X18X08o"). Qed.

(* [comment removed for export] *)
Definition TOPK0 : Z := 1024.
Definition TOPB0 : Z := 2 ^ 32.
Definition tk : Z := TOPK0 + fst (PESKA.spa_pot P 0).
Definition tb : Z := TOPB0 + snd (PESKA.spa_pot P 0).
Definition LayA : lib_layoutA := PECTB.LayA tk tb L.
Definition TopLSA : lib_statics := PECTB.TopLSA.
(* [comment removed for export] *)
Definition harness_stmt : Prop :=
  forall (PayOk PayExport : list byte -> Prop),
    PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
    lib_call_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.

(* [comment removed for export] *)
Record rows_open : Prop := ROWS {
  ro_all_closed : PECSB.parse_spec L ar HI P -> True
}.
Variable RO : rows_open.
Lemma rows_closed : rows_open.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmB ()) ["Asm"] "p;5p;1g00\ij51Tg00^?j10Tp,6SCFG_Pp,1Lp,2arg00M@p,1PD1g00XQU#0o"). Qed.

(* [comment removed for export] *)
Let opnew : PMSPA.opnew_spec RSEGS AD L ar HI :=
  PMBOPN.opnew_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let opdel : PMSPA.opdel_spec RSEGS AD L ar HI :=
  PMBOPD.opdel_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let opdel_sized : PMSPA.opdel_sized_spec RSEGS AD L ar HI :=
  PMBOPD.opdel_sized_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let locale_ctor : PMSPA.locale_ctor_spec RSEGS AD L ar HI :=
  PMBLOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC.   (* [comment removed for export] *)
Let locale_dtor : PMSPA.locale_dtor_spec RSEGS AD L ar HI :=
  PMBLOC.locale_dtor_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let syscat : PMSPA.syscat_spec RSEGS AD L ar HI :=
  PMBSY.syscat_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let ios_dtor : PMSPA.ios_dtor_spec RSEGS AD L ar HI :=
  PMBID.ios_dtor_ok L ar C HI LY HIok EXT locale_dtor.   (* [comment removed for export] *)
Let src_dtor : PMSPA.src_dtor_spec RSEGS AD L ar HI :=
  PMBSD.src_dtor_ok L ar C HI LY HIok opdel locale_dtor ios_dtor.   (* [comment removed for export] *)
Let is_base10 : PMSPA.is_base10_spec RSEGS AD L ar HI :=
  PMBB10.is_base10_ok L ar C HI LY HIok IL ICok ILY.   (* [comment removed for export] *)
Let str_resize : PMSPA.str_resize_spec RSEGS AD L ar HI :=
  PMBRZ.str_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.   (* [comment removed for export] *)
Let ann_shrink : PMBX.ann_shrink_spec L ar HI :=
  PMBANN.ann_shrink_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let ann_delete : PMBX.ann_delete_spec L ar HI :=
  PMBANN.ann_delete_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let vec_clear : PMBX.vec_clear_spec L ar HI :=
  PMBVC.vec_clear_ok L ar C HI LY HIok ann_shrink.   (* [comment removed for export] *)
Let vec_dtor : PMSPA.vec_dtor_spec RSEGS AD L ar HI :=
  PMBVD.vec_dtor_ok L ar C HI LY HIok vec_clear ann_delete opdel.   (* [comment removed for export] *)
Let cone_mi : PMBX.cone_mi_spec L ar HI :=
  PMBCOMI.cone_mi_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let cone_miu : PMBX.cone_miu_spec L ar HI :=
  PMBCOMIU.cone_miu_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let cone_ms : PMBX.cone_ms_spec L ar HI :=
  PMBCOMS.cone_ms_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let cone_msu : PMBX.cone_msu_spec L ar HI :=
  PMBCOMSU.cone_msu_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let slow_ms : PMBX.slow_ms_spec L ar HI :=
  PMBSLMS.slow_ms_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let slow_msu : PMBX.slow_msu_spec L ar HI :=
  PMBSLMSU.slow_msu_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let slow_miu : PMBX.slow_miu_spec L ar HI :=
  PMBSLMIU.slow_miu_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let slow_mi : PMBX.slow_mi_spec L ar HI :=
  PMBSLMI.slow_mi_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let make_ec : PECSB.make_ec_spec L ar HI :=
  PEBCERR.make_ec_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let reader_ctor : PECSB.reader_ctor_spec L ar HI :=
  PMBRD.reader_ctor_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew slow_mi.   (* [comment removed for export] *)
Let reset : PECSB.reset_spec L ar HI :=
  PEBCRS.reset_ok L ar C HI LY HIok vec_clear cone_miu.   (* [comment removed for export] *)
Let str_ctor_c : PECSB.str_ctor_c_spec L ar HI :=
  PEBCSTR.str_ctor_c_ok L ar C HI LY HIok opnew.   (* [comment removed for export] *)
Let iss_ctor_c : PECSB.iss_ctor_c_spec L ar HI :=
  PEBCISS.iss_ctor_c_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew.   (* [comment removed for export] *)
Let validate_rd : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD) :=
  PECVALBR.validate_fun_ok L ar C HI LY HIok GAP.   (* [comment removed for export] *)
Let validate_enc : PECVSA.validate_fun_spec RSEGS AD L ar HI (pe_validate_enc EE) :=
  PECVALB.validate_fun_ok L ar C HI LY HIok GAP.   (* [comment removed for export] *)
Let OPNWP : PESKA.opnew_n_spec RSEGS AD L ar HI (PESKA.spa_nmax P) :=
  opnew_n_le _ _ NMAXOK (PMBOPNW.opnew_n_ok L ar C HI LY HIok MALLOCN).   (* [comment removed for export] *)
Let push_back : PESKA.push_back_specA RSEGS AD EE L ar HI P :=
  PEBSKP.push_back_ok L ar C HI P LY HIok EXT PO OPNWP opdel MEMCPYN NMAXOK.   (* [comment removed for export] *)
Let push_back_ind : PEPBI.push_back_indZ_specA RSEGS AD L ar HI 0xb2794 P :=
  PEBPBI.push_back_ind_ok L ar C HI P LY HIok push_back.   (* [comment removed for export] *)
Let econe_k : PECEPX.econe_k_spec RSEGS AD EE L ar HI :=
  PEBEPF.econe_k_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let econe_kl : PECEPX.econe_kl_spec RSEGS AD EE L ar HI :=
  PEBEQF.econe_kl_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let eslow_k : PECEPX.eslow_k_spec RSEGS AD EE L ar HI :=
  PEBEPUSH.eslow_k_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let eslow_kl : PECEPX.eslow_kl_spec RSEGS AD EE L ar HI :=
  PEBEQPUSH.eslow_kl_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let put_length : PECSB.put_length_spec L ar HI P :=
  PEBENCPL.put_length_ok L ar C HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_null : PECSB.v_null_spec L ar HI P :=
  PEBENCN.v_null_ok L ar C HI P LY HIok PO push_back_ind.   (* [comment removed for export] *)
Let v_bool : PECSB.v_bool_spec L ar HI P :=
  PEBENCT.v_bool_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_uint64 : PECSB.v_uint64_spec L ar HI P :=
  PEBENCVU.v_uint64_ok L ar C HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_int64 : PECSB.v_int64_spec L ar HI P :=
  PEBENCVI.v_int64_ok L ar C HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_double : PECSB.v_double_spec L ar HI P :=
  PEBENCD.v_double_ok L ar C HI P LY HIok PO push_back push_back_ind.   (* [comment removed for export] *)
Let v_flush : PECSB.v_flush_spec L ar HI P :=
  PEBENCF.v_flush_ok L ar C HI P LY HIok.   (* [comment removed for export] *)
Let v_begin_arr : PECSB.v_begin_arr_spec L ar HI P :=
  PEBENCBG.v_begin_arr_ok L ar C HI P LY HIok PO push_back make_ec econe_k eslow_k.   (* [comment removed for export] *)
Let v_begin_arr_len : PECSB.v_begin_arr_len_spec L ar HI P :=
  PEBENCBL.v_begin_arr_len_ok L ar C HI P LY HIok PO push_back make_ec put_length econe_kl eslow_kl.   (* [comment removed for export] *)
Let v_begin_obj : PECSB.v_begin_obj_spec L ar HI P :=
  PEBENCBG.v_begin_obj_ok L ar C HI P LY HIok PO push_back make_ec econe_k eslow_k.   (* [comment removed for export] *)
Let v_begin_obj_len : PECSB.v_begin_obj_len_spec L ar HI P :=
  PEBENCBL.v_begin_obj_len_ok L ar C HI P LY HIok PO push_back make_ec put_length econe_kl eslow_kl.   (* [comment removed for export] *)
Let v_end_arr : PECSB.v_end_arr_spec L ar HI P :=
  PEBENCE.v_end_arr_ok L ar C HI P LY HIok PO push_back make_ec (PEBEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).   (* [comment removed for export] *)
Let v_end_obj : PECSB.v_end_obj_spec L ar HI P :=
  PEBENCE.v_end_obj_ok L ar C HI P LY HIok PO push_back make_ec (PEBEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).   (* [comment removed for export] *)
Let v_key : PECSB.v_key_spec L ar HI P :=
  PEBENCK.v_key_ok L ar C HI P LY HIok PO push_back put_length validate_enc.   (* [comment removed for export] *)
Let v_string : PECSB.v_string_spec L ar HI P :=
  PEBENCST.v_string_ok L ar C HI P LY HIok PO push_back put_length make_ec validate_enc.   (* [comment removed for export] *)
Let fill_buffer : PECSB.fill_buffer_spec L ar HI :=
  PECFILLB.fill_buffer_ok L ar C HI LY HIok IL ICok ILY.   (* [comment removed for export] *)
Let peek : PECSB.peek_spec L ar HI :=
  PECPEEKB.peek_ok L ar C HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let ignore : PECSB.ignore_spec L ar HI :=
  PECIGNB.ignore_ok L ar C HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let src_read : PECSB.src_read_spec L ar HI :=
  PECREADB.src_read_ok L ar C HI LY HIok IL ICok ILY fill_buffer.   (* [comment removed for export] *)
Let cstr_resize : PECTXSA.cstr_resize_spec RSEGS AD L ar HI :=
  PECRSZB.cstr_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.   (* [comment removed for export] *)
Let csrd_read : PECTXSA.csrd_read_spec RSEGS AD L ar HI :=
  PECSRD5B.csrd_read_ok L ar C HI LY HIok IL ICok ILY cstr_resize fill_buffer (PECFILLTBB.cfill_tb_ok L ar C HI LY HIok IL ICok ILY).   (* [comment removed for export] *)
Let read_span : PECSB.read_span_spec L ar HI :=
  PECRS3B.read_span_ok L ar C HI LY HIok IL ICok ILY fill_buffer csrd_read.   (* [comment removed for export] *)
Let get_length : PECSB.get_length_spec L ar HI P :=
  PEBCGL.get_length_ok L ar C HI P LY HIok src_read make_ec.   (* [comment removed for export] *)
Let end_array : PECSB.end_array_spec L ar HI P :=
  PEBCEND.end_array_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_arr.   (* [comment removed for export] *)
Let end_object : PECSB.end_object_spec L ar HI P :=
  PEBCEND.end_object_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_obj.   (* [comment removed for export] *)
Let read_key : PECSB.read_key_spec L ar HI P :=
  PEBCRDKEY.read_key_ok L ar C HI P LY HIok IL ICok ILY PO get_length read_span validate_rd make_ec v_key.   (* [comment removed for export] *)
Let begin_array : PECSB.begin_array_spec L ar HI P :=
  PEBCBA.begin_array_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec cone_mi slow_mi cone_ms slow_ms cone_msu slow_msu v_begin_arr v_begin_arr_len.   (* [comment removed for export] *)
Let begin_object : PECSB.begin_object_spec L ar HI P :=
  PEBCBO.begin_object_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec cone_mi slow_mi cone_ms slow_ms cone_msu slow_msu v_begin_obj v_begin_obj_len.   (* [comment removed for export] *)
Let read_value : PECSB.read_value_spec L ar HI P :=
  PEBCRV.read_value_ok L ar C HI P LY HIok IL ICok ILY PO src_read get_length read_span validate_rd is_base10 make_ec begin_array begin_object v_null v_bool v_uint64 v_int64 v_double v_string.   (* [comment removed for export] *)
Let rtv : PECSB.rtv_spec L ar HI P :=
  PEBCRTV.rtv_ok L ar C HI P LY HIok IL ICok ILY src_read make_ec read_value.   (* [comment removed for export] *)
Let parse : PECSB.parse_spec L ar HI P :=
  PEBCLP.parse_ok L ar C HI P LY HIok IL ICok ILY rtv read_value read_key end_array end_object peek ignore make_ec vec_clear.   (* [comment removed for export] *)
Let reader_read : PECRRZ.reader_read_specZ RSEGS AD AAD EE L ar HI P :=
  PEBCRR.reader_read_ok L ar C HI P LY HIok reset parse.   (* [comment removed for export] *)
Let estk_dtor : PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb4794 :=
  PEBEKD.estk_dtor_ok L ar C HI LY HIok (PEBEKC.clear_e_ok L ar C HI LY HIok EXT) (PEBEKAN.ann_delete_e_ok L ar C HI LY HIok EXT) opdel.   (* [comment removed for export] *)
Let sink_dtor : PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaafe4 :=
  PEBSKD.sink_dtor_ok L ar C HI P LY HIok (PEBSKC.clear_b_ok L ar C HI LY HIok EXT) (PEBSKAN.ann_delete_b_ok L ar C HI LY HIok EXT) opdel.   (* [comment removed for export] *)
Let HARN : harness_stmt :=
  PEBCHN.harness_call_ok L ar C IL HI P LY HIok ICok ILY EXT PO PMODE str_ctor_c iss_ctor_c reader_ctor syscat reader_read vec_dtor opdel src_dtor locale_dtor ios_dtor estk_dtor sink_dtor.   (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem top_iface_asm (PayOk PayExport : list byte -> Prop) :
  PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
  lib_iface_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.
Proof using LY ILY MCC PO PMODE NMAXOK FAM RO.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmB ()) ["Asm"] "h09PayExporth15PayOkh23PINh34POUTp;1p;2p;;g000Lj10Tg001Vj18Tg0024j12Tg004Ej11Tg00_Xj27Tg00`jj26Tg00b=j13Tg00cCj14Tg00dXl;5Tg00Ra#0#0#0#8#2#1p-0[R0p,1PR1f1R2'71612p,1Lp,2arp,1Cg00f0g00g@p,2LYp,6SCFG_P#3g00M@#4f3R1f2R3p,4HARNP1P3P2f0R3O4M;5W3W2X00X10P2P3O2X00X10P2P3O2X00W1o"). Qed.
End Asm.
End PECASMB.
