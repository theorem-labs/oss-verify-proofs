(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5DefsA XIcptAs0 L5CoreA
     HeapIfaceAEx HeapIfaceAExI HeapIfaceAEr LibIface LibIfaceAB LibIfaceAE
     PmLayout PmLayoutA PnLayout PeLayoutA PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PeSpecsAmc PeAImgGap
     PeCLayout PeCLayoutA PeCSink PeCModel PeCSpecs PeCStatics PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCTxtSpecsA PeCValSpecA PeCDtorSpecsA PeTopAL PeCTopA
     PeACStr PeACIss PeACParse PeAEncDbl PeAEncEnd PeACRdVal PeCEPushSpecsA PeAEPush PeAEPusq PeASinkPush PeAEncBgn PeAEncBgnL PeAOpnew PeAOpdel PeALoc PeASys PeAIosDtor PeASrcDtor PeAResize PeAEncFlush PeAAnn PeAEmu PeAEmb PeACReset PeACErr PeACEnd PeACRdCtor PeACRtv PeAOpnewN PeAEmm PeAEms PeAEncNull PeAEncBool PeAEncU64 PeAEncI64 PeAEncPutLen PeAEncKey PeACHarness PeACRdKey PeACGetLen PeASnkDtor PeASnkAnn PeAEstkDtor PeAEstkAnn PeACSrcFill PeACSrcPeek PeACSrcIgn PeACSrcRead PeACRdSpan3 PeACSrd5 PeACResize PeACSrcFillTb PeAEncStr PeACVal PeACValR PeAB10 PeAVecDtor PeACBegArr PeACBegObj.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCTopAsmA () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ri_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan7L5CoreA4L5CA9amodel_okC13~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCSinkA5PESKA<opnew_n_specC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCLayoutA7CADDR_AC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA2HIC13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAa5PECSA:parse_specC13~~~k89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA9rows_open01C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAa5PECSA6pay_inC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAa5PECSA7pay_outC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ9strict_ofC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCTopA5PECTA?top_iface_okA_xC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA2tkC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA2tbC13~~~".
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
(* [comment removed for export] *)
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition inst_ok (HI : asan_iface) : Prop :=
  HAJ.asan_iface_okR L ar C SCFG HI /\ aicpt_ok L ar IL SCFG HI /\ HAJ.asan_ext_ok L ar SCFG HI PMA.EXT /\ PMAGAP.rt_img_gap HI.
(* [comment removed for export] *)
Definition fam_ok : Prop := HAR.asan_famR_ok L ar C SCFG LR HIk /\ (forall D, inst_ok (HIk D)).
Hypothesis FAM : fam_ok.

(* [comment removed for export] *)
Definition HI : asan_iface := HIk [].
Let IOK : inst_ok HI := proj2 FAM [].
Let HIok : HAJ.asan_iface_okR L ar C SCFG HI := proj1 IOK.
Let ICok : aicpt_ok L ar IL SCFG HI := proj1 (proj2 IOK).
Let EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT := proj1 (proj2 (proj2 IOK)).
Let GAP : PMAGAP.rt_img_gap HI := proj2 (proj2 (proj2 IOK)).
(* [comment removed for export] *)
Let MALLOCN : HAR.amallocN_spec L ar SCFG (fun _ => HI) := fun D => HAR.fr_mallocN L ar C SCFG LR HIk (proj1 FAM) [].
(* [comment removed for export] *)
Let MEMCPYN : HAR.amemcpyN_spec_at L ar SCFG (fun _ => HI) (hl_asan_memcpy L) := fun D => HAR.fr_memcpyN L ar C SCFG LR HIk (proj1 FAM) [].
(* [comment removed for export] *)
Local Lemma opnew_n_le (N N' : Z) : N <= N' -> PESKA.opnew_n_spec RSEGS AD L ar HI N' -> PESKA.opnew_n_spec RSEGS AD L ar HI N.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmA ()) ["Asm"] "h01Nh12N'h24__x1h34__x2h44__x3h52AMh62Awh72FFh83G10h92HKh:2Hnh;1Kh<2LBh=2LEh>2LKh?1Mh@1RhA2RIhB1WhC7__arithhD4__ffhE8__varmaphF5__withG2crhH2fxhI5modelhJ1nhK1rhL2spp;2p;1p;8p;3p;4p;7g0000j21Tg000Lj10Tg0011j1HTg001Vj19Tg0024j1BTg002Wj2QTg003Cj1PTg003ej2NTg004Ej14Tg004ej1GTg0061j8FTg007=j2ETg008Sj1DTg0093j1\Tg009Qj3VTg00:4j2UTg00;<j2TTg00;bj3?Tg00<<j25Tg00<Xj27Tg00=3j1>Tg00=Rj26Tg00>;j3=Tg00>dj2OTg00?Pj3MTg00@0j2;Tg00@Nj1LTg00@lj4:Tg00AJj1ITg00Ahj1JTg00BSj2KTg00C6j23Tg00CYj4<Tg00DDj1RTg00Dfj2STg00EHj2_Tg00Ebj2^Tg00FNj3]Tg00Fmj4[Tg00G_j7WTg00I5j7XTg00IYj7YTg00J=j8ZTf3R0g00Jag00Knf2R1f1R2g00M;R3f0R4FWp=CP2g00NKR5g00NjR6P6g00OJR7P4g00OjFXp=2g00PJR8P2g00PhP4C<p=8P1P5P6P6P7P2P4FYp=AP0P5P6P6P7P1P2P4GZp=@1124p,6SCFG_PR5p,1LR9p,2arR:P2CCg00QOg00R\R;#0R<#HR=#9R>%0<#0R?#0#0#0#9R@#BRA'Q%9?#B#P\Ag00SAg00T71N88#4R?g00U?#4RBg00VKP3f7R3f6RCf5RDP0f4REf:RFf9RG#GGF1EDFPFg00WV#DO1f>RH%0=#\g00XL5V>'U1T@D5?Ag00XhRA/5CfDR@,1C'7fBfAf@f?PHf=f<f;PFPGf8RGP3PCPDPEP0P1P2g00YFREg00Z2RD#>RC#>,68168C168D5=85=8g00ZQ'O%DE3M%4EP81;81P2P81;80P0%L8C:C:%I8%J8REP81K8Ag00[=138;R;C<,2ERD138=R=,8;,2E5AE%R6R6PE138<R<,8=,2EP618;<,2E9AEDC@C@1SE7P4P1g00[dREg00\DR7'_1^41=?E7dA]8A2C[bDbEbFX28X38X4815A41141'7110115A11110'7[[^28^38^48P4fFfEPGP2P@O5bCOBW:W8W9W5WAXK8XL8XJ8WGX6?X>BW7W<W;WIW?W@WHP5P9P:P0CCeWBW=X18X08P2P4O2X18X08P2P4O2X18X08o"). Qed.

(* [comment removed for export] *)
Definition TOPK0 : Z := 1024.
Definition TOPB0 : Z := 2 ^ 32.
Definition tk : Z := TOPK0 + fst (PESKA.spa_pot P 0).
Definition tb : Z := TOPB0 + snd (PESKA.spa_pot P 0).
Definition LayA : lib_layoutA := PECTA.LayA tk tb L.
Definition TopLSA : lib_statics := PECTA.TopLSA.
(* [comment removed for export] *)
Definition harness_stmt : Prop :=
  forall (PayOk PayExport : list byte -> Prop),
    PECSA.pay_in P PayOk -> PECSA.pay_out P PayExport ->
    lib_call_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.

(* [comment removed for export] *)
Record rows_open : Prop := ROWS {
  ro_all_closed : PECSA.parse_spec L ar HI P -> True
}.
Variable RO : rows_open.
Lemma rows_closed : rows_open.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmA ()) ["Asm"] "p;5p;1g00\dj51Tg00^:j10Tp,6SCFG_Pp,1Lp,2arg00M;p,1PD1g00XLU#0o"). Qed.

(* [comment removed for export] *)
Let opnew : PMSPA.opnew_spec RSEGS AD L ar HI :=
  PMAOPN.opnew_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let opdel : PMSPA.opdel_spec RSEGS AD L ar HI :=
  PMAOPD.opdel_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let opdel_sized : PMSPA.opdel_sized_spec RSEGS AD L ar HI :=
  PMAOPD.opdel_sized_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let locale_ctor : PMSPA.locale_ctor_spec RSEGS AD L ar HI :=
  PMALOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC.   (* [comment removed for export] *)
Let locale_dtor : PMSPA.locale_dtor_spec RSEGS AD L ar HI :=
  PMALOC.locale_dtor_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let syscat : PMSPA.syscat_spec RSEGS AD L ar HI :=
  PMASY.syscat_ok L ar C HI LY HIok.   (* [comment removed for export] *)
Let ios_dtor : PMSPA.ios_dtor_spec RSEGS AD L ar HI :=
  PMAID.ios_dtor_ok L ar C HI LY HIok EXT locale_dtor.   (* [comment removed for export] *)
Let src_dtor : PMSPA.src_dtor_spec RSEGS AD L ar HI :=
  PMASD.src_dtor_ok L ar C HI LY HIok opdel locale_dtor ios_dtor.   (* [comment removed for export] *)
Let is_base10 : PMSPA.is_base10_spec RSEGS AD L ar HI :=
  PMAB10.is_base10_ok L ar C HI LY HIok IL ICok ILY.   (* [comment removed for export] *)
Let str_resize : PMSPA.str_resize_spec RSEGS AD L ar HI :=
  PMARZ.str_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.   (* [comment removed for export] *)
Let push_mi : PECSA.push_mi_spec L ar HI :=
  PMAEB.push_mi_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let push_miu : PECSA.push_miu_spec L ar HI :=
  PMAEU.push_miu_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let push_ms : PECSA.push_ms_spec L ar HI :=
  PMAEM.push_ms_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let push_msu : PECSA.push_msu_spec L ar HI :=
  PMAES.push_msu_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let ann_shrink : PECSA.ann_shrink_spec L ar HI :=
  PMAANN.ann_shrink_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let ann_delete : PECSA.ann_delete_spec L ar HI :=
  PMAANN.ann_delete_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let vec_dtor : PMSPA.vec_dtor_spec RSEGS AD L ar HI :=
  PMAVD.vec_dtor_ok L ar C HI LY HIok ann_shrink ann_delete opdel.   (* [comment removed for export] *)
Let make_ec : PECSA.make_ec_spec L ar HI :=
  PEACERR.make_ec_ok L ar C HI LY HIok EXT.   (* [comment removed for export] *)
Let reader_ctor : PECSA.reader_ctor_spec L ar HI :=
  PMARD.reader_ctor_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew push_mi.   (* [comment removed for export] *)
Let reset : PECSA.reset_spec L ar HI :=
  PEACRS.reset_ok L ar C HI LY HIok ann_shrink push_miu.   (* [comment removed for export] *)
Let str_ctor_c : PECSA.str_ctor_c_spec L ar HI :=
  PEACSTR.str_ctor_c_ok L ar C HI LY HIok opnew.   (* [comment removed for export] *)
Let iss_ctor_c : PECSA.iss_ctor_c_spec L ar HI :=
  PEACISS.iss_ctor_c_ok L ar C IL HI LY HIok ICok ILY locale_ctor opnew.   (* [comment removed for export] *)
Let validate_rd : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD) :=
  PECVALAR.validate_fun_ok L ar C HI LY HIok GAP.   (* [comment removed for export] *)
Let validate_enc : PECVSA.validate_fun_spec RSEGS AD L ar HI (pe_validate_enc EE) :=
  PECVALA.validate_fun_ok L ar C HI LY HIok GAP.   (* [comment removed for export] *)
Let OPNWP : PESKA.opnew_n_spec RSEGS AD L ar HI (PESKA.spa_nmax P) :=
  opnew_n_le _ _ NMAXOK (PMAOPNW.opnew_n_ok L ar C HI LY HIok MALLOCN).   (* [comment removed for export] *)
Let push_back : PESKA.push_back_specA RSEGS AD EE L ar HI P :=
  PEASKP.push_back_ok L ar C HI P LY HIok EXT PO OPNWP opdel MEMCPYN NMAXOK.   (* [comment removed for export] *)
Let epush_k : PECEPX.epush_k_spec RSEGS AD EE L ar HI :=
  PEAEPUSH.epush_k_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let epush_kl : PECEPX.epush_kl_spec RSEGS AD EE L ar HI :=
  PEAEQPUSH.epush_kl_ok L ar C HI LY HIok EXT opnew opdel.   (* [comment removed for export] *)
Let put_length : PECSA.put_length_spec L ar HI P :=
  PEAENCPL.put_length_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_null : PECSA.v_null_spec L ar HI P :=
  PEAENCN.v_null_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_bool : PECSA.v_bool_spec L ar HI P :=
  PEAENCT.v_bool_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_uint64 : PECSA.v_uint64_spec L ar HI P :=
  PEAENCVU.v_uint64_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_int64 : PECSA.v_int64_spec L ar HI P :=
  PEAENCVI.v_int64_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_double : PECSA.v_double_spec L ar HI P :=
  PEAENCD.v_double_ok L ar C HI P LY HIok PO push_back.   (* [comment removed for export] *)
Let v_flush : PECSA.v_flush_spec L ar HI P :=
  PEAENCF.v_flush_ok L ar C HI P LY HIok.   (* [comment removed for export] *)
Let v_begin_arr : PECSA.v_begin_arr_spec L ar HI P :=
  PEAENCBG.v_begin_arr_ok L ar C HI P LY HIok PO push_back make_ec epush_k.   (* [comment removed for export] *)
Let v_begin_arr_len : PECSA.v_begin_arr_len_spec L ar HI P :=
  PEAENCBL.v_begin_arr_len_ok L ar C HI P LY HIok PO push_back make_ec put_length epush_kl.   (* [comment removed for export] *)
Let v_begin_obj : PECSA.v_begin_obj_spec L ar HI P :=
  PEAENCBG.v_begin_obj_ok L ar C HI P LY HIok PO push_back make_ec epush_k.   (* [comment removed for export] *)
Let v_begin_obj_len : PECSA.v_begin_obj_len_spec L ar HI P :=
  PEAENCBL.v_begin_obj_len_ok L ar C HI P LY HIok PO push_back make_ec put_length epush_kl.   (* [comment removed for export] *)
Let v_end_arr : PECSA.v_end_arr_spec L ar HI P :=
  PEAENCE.v_end_arr_ok L ar C HI P LY HIok PO push_back make_ec (PEAEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).   (* [comment removed for export] *)
Let v_end_obj : PECSA.v_end_obj_spec L ar HI P :=
  PEAENCE.v_end_obj_ok L ar C HI P LY HIok PO push_back make_ec (PEAEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT).   (* [comment removed for export] *)
Let v_key : PECSA.v_key_spec L ar HI P :=
  PEAENCK.v_key_ok L ar C HI P LY HIok PO push_back put_length validate_enc.   (* [comment removed for export] *)
Let v_string : PECSA.v_string_spec L ar HI P :=
  PEAENCST.v_string_ok L ar C HI P LY HIok PO push_back put_length make_ec validate_enc.   (* [comment removed for export] *)
Let fill_buffer : PECSA.fill_buffer_spec L ar HI :=
  PECFILLA.fill_buffer_ok L ar C HI LY HIok IL ICok ILY.   (* [comment removed for export] *)
Let peek : PECSA.peek_spec L ar HI :=
  PECPEEKA.peek_ok L ar C HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let ignore : PECSA.ignore_spec L ar HI :=
  PECIGNA.ignore_ok L ar C HI LY HIok fill_buffer.   (* [comment removed for export] *)
Let src_read : PECSA.src_read_spec L ar HI :=
  PECREADA.src_read_ok L ar C HI LY HIok IL ICok ILY fill_buffer.   (* [comment removed for export] *)
Let cstr_resize : PECTXSA.cstr_resize_spec RSEGS AD L ar HI :=
  PECRSZA.cstr_resize_ok L ar C IL HI LY HIok ICok ILY opnew opdel.   (* [comment removed for export] *)
Let csrd_read : PECTXSA.csrd_read_spec RSEGS AD L ar HI :=
  PECSRD5A.csrd_read_ok L ar C HI LY HIok IL ICok ILY cstr_resize fill_buffer (PECFILLTBA.cfill_tb_ok L ar C HI LY HIok IL ICok ILY).   (* [comment removed for export] *)
Let read_span : PECSA.read_span_spec L ar HI :=
  PECRS3A.read_span_ok L ar C HI LY HIok IL ICok ILY fill_buffer csrd_read.   (* [comment removed for export] *)
Let get_length : PECSA.get_length_spec L ar HI P :=
  PEACGL.get_length_ok L ar C HI P LY HIok src_read make_ec.   (* [comment removed for export] *)
Let end_array : PECSA.end_array_spec L ar HI P :=
  PEACEND.end_array_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_arr.   (* [comment removed for export] *)
Let end_object : PECSA.end_object_spec L ar HI P :=
  PEACEND.end_object_ok L ar C HI P LY HIok IL ICok ILY ann_shrink v_end_obj.   (* [comment removed for export] *)
Let read_key : PECSA.read_key_spec L ar HI P :=
  PEACRDKEY.read_key_ok L ar C HI P LY HIok IL ICok ILY PO get_length read_span validate_rd make_ec v_key.   (* [comment removed for export] *)
Let begin_array : PECSA.begin_array_spec L ar HI P :=
  PEACBA.begin_array_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec push_mi push_ms push_msu v_begin_arr v_begin_arr_len.   (* [comment removed for export] *)
Let begin_object : PECSA.begin_object_spec L ar HI P :=
  PEACBO.begin_object_ok L ar C HI P LY HIok IL ICok ILY PO peek ignore src_read get_length make_ec push_mi push_ms push_msu v_begin_obj v_begin_obj_len.   (* [comment removed for export] *)
Let read_value : PECSA.read_value_spec L ar HI P :=
  PEACRV.read_value_ok L ar C HI P LY HIok IL ICok ILY PO src_read get_length read_span validate_rd is_base10 make_ec begin_array begin_object v_null v_bool v_uint64 v_int64 v_double v_string.   (* [comment removed for export] *)
Let rtv : PECSA.rtv_spec L ar HI P :=
  PEACRTV.rtv_ok L ar C HI P LY HIok IL ICok ILY src_read make_ec read_value.   (* [comment removed for export] *)
Let parse : PECSA.parse_spec L ar HI P :=
  PEACLP.parse_ok L ar C HI P LY HIok IL ICok ILY rtv read_value read_key end_array end_object peek ignore make_ec ann_shrink.   (* [comment removed for export] *)
Let estk_dtor : PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb140c :=
  PEAEKD.estk_dtor_ok L ar C HI LY HIok (PEAEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT) (PEAEKAN.ann_delete_e_ok L ar C HI LY HIok EXT) opdel.   (* [comment removed for export] *)
Let sink_dtor : PECDTA.sink_dtor_spec RSEGS AD L ar HI P 0xaa5cc :=
  PEASKD.sink_dtor_ok L ar C HI P LY HIok (PEASKAN.ann_shrink_b_ok L ar C HI LY HIok EXT) (PEASKAN.ann_delete_b_ok L ar C HI LY HIok EXT) opdel.   (* [comment removed for export] *)
Let HARN : harness_stmt :=
  PEACHN.harness_call_ok L ar C IL HI P LY HIok ICok ILY EXT PO PMODE str_ctor_c iss_ctor_c reader_ctor syscat reset parse vec_dtor opdel src_dtor locale_dtor ios_dtor estk_dtor sink_dtor.   (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem top_iface_asm (PayOk PayExport : list byte -> Prop) :
  PECSA.pay_in P PayOk -> PECSA.pay_out P PayExport ->
  lib_iface_okA_x LayA ar SCFG (HAJ.strict_of HI) TopLSA PayOk PayExport.
Proof using LY ILY MCC PO PMODE NMAXOK FAM RO.
ltac2:(KReplay.run1 (kr_t_PeCTopAsmA ()) ["Asm"] "h09PayExporth15PayOkh23PINh34POUTp;1p;2p;;g000Lj10Tg001Vj18Tg0024j12Tg004Ej11Tg00_Sj27Tg00`ej26Tg00b8j13Tg00c>j14Tg00dSl;5Tg00R\#0#0#0#8#2#1p-0[R0p,1PR1f1R2'71612p,1Lp,2arp,1Cg00ekg00g;p,2LYp,6SCFG_P#3g00M;#4f3R1f2R3p,4HARNP1P3P2f0R3O4M;5W3W2X00X10P2P3O2X00X10P2P3O2X00W1o"). Qed.
End Asm.
End PECASMA.
