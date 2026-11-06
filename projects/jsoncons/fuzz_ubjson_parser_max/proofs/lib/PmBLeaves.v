(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5DefsAB0 HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb PmSpecsBX PmSpecsAmc PmBImgGap PmBLibOk PmBClose
PmBOpdel PmBAnn PmBVecClear PmBVecDtor PmBLoc PmBIosDtor PmBSrcDtor PmBConeMiu PmBReset PmBOpnew PmBSlowMi PmBRd
PmBErr PmBSrcXsgetn PmBSrcFill PmBSrcRead PmBGetLen PmBResize PmBSrcFillTb PmBSrd5 PmBRdSpan3 PmBB10 PmBVal PmBRdVal PmBRtv PmBRdKey PmBEnd
PmBSrcPeek PmBSrcIgnore PmBParse.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBLeaves () := ([""; "Corelib.Init.Logic."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBLeaves.PMBLV.SCFG_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBLibOk.PMBLO."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."], [["1and"; "0HI"; "0L"; "2open_leaves"; "3harness_depsB"; "4end_array_spec"; "4end_object_spec"; "4get_length_spec"; "4ignore_spec"; "4is_base10_spec"; "4make_ec_spec"; "4peek_spec"; "4read_key_spec"; "4read_span_spec"; "4read_value_spec"; "4rtv_spec"]; ["4src_read_spec"; "4validate_spec"; "5ann_shrink_spec"; "5vec_clear_spec"; "0SCFG_P"; "0ar"]]).
Module PMBLV.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition open_leaves (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
PMB.begin_array_spec L ar HI /\ PMB.begin_object_spec L ar HI.
Section Callees.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Hypothesis GAP : PMBGAP.rt_img_gap HI.
Hypothesis BA : PMB.begin_array_spec L ar HI.
Hypothesis BO : PMB.begin_object_spec L ar HI.
Theorem parse_callees : ltac2:(TCodec.tc2 tcn__PmBLeaves "QA'0&?vDv2vEv1%544321&>%146543&<%148765&5%14:987&6%14<;:9&;%14>=<;&8%14@?>=&:%14BA@?&B%14DCBA&C%14FEDC&@%14HGFE&7%14JIHG&=%14LKJI&A%14NMLK&9%14Q0ONM%Q3231%Q4261%Q5291%Q62<1%Q72?1%Q82B1%Q92E1%Q:2H1%Q;2K1%Q<2N1%Q=2Q11%Q>2Q41%Q?2Q71%Q@2Q:1").
Proof using All.
pose proof (PMBOPN.opnew_ok L ar C HI LY HIok) as OPN.
pose proof (PMBOPD.opdel_ok L ar C HI LY HIok) as OPD.
pose proof (PMBERR.make_ec_ok L ar C HI LY HIok EXT) as MKE.
pose proof (PMBANN.ann_shrink_ok L ar C HI LY HIok EXT) as ASH.
pose proof (PMBXG.xsgetn_ok L ar C IL HI LY HIok ICok ILY) as XG.
pose proof (PMBSFB.fill_buffer_ok L ar C HI LY HIok IL ICok ILY XG) as FB.
pose proof (PMBSRD.src_read_ok L ar C HI LY HIok IL ICok ILY FB XG) as SR.
pose proof (PMBGLN.get_length_ok L ar C HI LY HIok SR MKE) as GL.
pose proof (PMBRZ.str_resize_ok L ar C IL HI LY HIok ICok ILY OPN OPD) as RZ.
pose proof (PMBSFBT.fill_buffer_tb_ok L ar C HI LY HIok IL ICok ILY XG) as FBT.
pose proof (PMBSR5.srd_read_ok L ar C HI LY HIok IL ICok ILY RZ SR FBT) as SRD.
pose proof (PMBRSP3.read_span_ok L ar C HI LY HIok FB SRD) as RS.
pose proof (PMBVAL.validate_ok L ar C HI LY HIok GAP) as VAL.
pose proof (PMBB10.is_base10_ok L ar C HI LY HIok IL ICok ILY) as B10.
pose proof (PMBRV.read_value_ok L ar C HI LY HIok IL ICok ILY SR GL RS VAL B10 BA BO MKE) as RV.
pose proof (PMBRTV.rtv_ok L ar C HI LY HIok IL ICok ILY SR MKE RV) as RTV.
pose proof (PMBRDK.read_key_ok L ar C HI LY HIok IL ICok ILY GL RS VAL MKE) as RK.
pose proof (PMBEND.end_array_ok L ar C HI LY HIok IL ICok ILY ASH) as EA.
pose proof (PMBEND.end_object_ok L ar C HI LY HIok IL ICok ILY ASH) as EO.
pose proof (PMBSPK.peek_ok L ar C HI LY HIok FB) as PK.
pose proof (PMBSIG.ignore_ok L ar C HI LY HIok FB) as IG.
pose proof (PMBVC.vec_clear_ok L ar C HI LY HIok ASH) as VCL.
repeat split; assumption.
Qed.
End Callees.
Section Leaves.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Hypothesis GAP : PMBGAP.rt_img_gap HI.
Theorem deps_of_leaves : ltac2:(TCodec.tc2 tcn__PmBLeaves "9&3v2vEv1%43321&4vD%241654p041").
Proof using All.
intros (BA & BO).
destruct (parse_callees L ar C IL HI LY HIok ICok ILY EXT GAP BA BO) as (RTV & RV & RK & EA & EO & PK & IG & MKE & ASH0 & VCL & _).
pose proof (PMBLP.parse_ok L ar C HI LY HIok IL ICok ILY RTV RV RK EA EO PK IG MKE VCL) as PARSE.
pose proof (PMBOPN.opnew_ok L ar C HI LY HIok) as OPN.
pose proof (PMBLOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC) as LCC.
pose proof (PMBOPD.opdel_ok L ar C HI LY HIok) as OPD.
pose proof (PMBANN.ann_shrink_ok L ar C HI LY HIok EXT) as ASH.
pose proof (PMBANN.ann_delete_ok L ar C HI LY HIok EXT) as ADL.
pose proof (PMBRD.reader_ctor_ok L ar C IL HI LY HIok ICok ILY LCC OPN (PMBSLMI.slow_mi_ok L ar C HI LY HIok EXT OPN OPD)) as RDC.
pose proof (PMBRS.reset_ok L ar C HI LY HIok (PMBVC.vec_clear_ok L ar C HI LY HIok ASH) (PMBCOMIU.cone_miu_ok L ar C HI LY HIok EXT)) as RST.
pose proof (PMBVD.vec_dtor_ok L ar C HI LY HIok (PMBVC.vec_clear_ok L ar C HI LY HIok ASH) ADL OPD) as VDT.
pose proof (PMBLOC.locale_dtor_ok L ar C HI LY HIok) as LCD.
pose proof (PMBID.ios_dtor_ok L ar C HI LY HIok EXT LCD) as IOD.
pose proof (PMBSD.src_dtor_ok L ar C HI LY HIok OPD LCD IOD) as SRCD.
exact (PMBCL.deps_closed L ar C IL HI LY HIok ICok ILY MCC RDC RST PARSE VDT SRCD IOD).
Qed.
End Leaves.
End SCFG_1.
End PMBLV.
