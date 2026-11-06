(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5DefsA HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAa PmSpecsAmc PmAImgGap
PmAOpnew PmAOpdel PmAErr PmAAnn PmAEmb PmAEmu PmALoc PmASrcXsgetn PmASrcFill PmASrcFillTb PmASrcRead PmASrcPeek PmASrcIgnore PmAGetLen
PmAResize PmASrd5 PmARdSpan3 PmAVal PmAB10 PmARdKey PmARdVal PmARtv PmAEnd PmAParse.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmALeaves () := ([""; "Corelib.Init.Logic."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."], [["1and"; "0HI"; "0L"; "2ann_delete_spec"; "2ann_shrink_spec"; "2locale_ctor_spec"; "2locale_dtor_spec"; "2parse_spec"; "2push_mi_spec"; "2push_miu_spec"; "0SCFG_P"; "0ar"]]).
Module PMALV.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Leaves.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Hypothesis MCC : PMAMC.mcmp_cells C.
Hypothesis GAP : PMAGAP.rt_img_gap HI.
Hypothesis BA : PMA.begin_array_spec L ar HI.
Hypothesis BO : PMA.begin_object_spec L ar HI.
Theorem parse_closed : ltac2:(TCodec.tc2 tcn__PmALeaves "6&7v:v2v;v1%544321").
Proof.
pose proof (PMAOPN.opnew_ok L ar C HI LY HIok) as OPN.
pose proof (PMAOPD.opdel_ok L ar C HI LY HIok) as OPD.
pose proof (PMAERR.make_ec_ok L ar C HI LY HIok EXT) as MKE.
pose proof (PMAANN.ann_shrink_ok L ar C HI LY HIok EXT) as ASH.
pose proof (PMAXG.xsgetn_ok L ar C IL HI LY HIok ICok ILY) as XG.
pose proof (PMASFB.fill_buffer_ok L ar C HI LY HIok IL ICok ILY XG) as FB.
pose proof (PMASRD.src_read_ok L ar C HI LY HIok IL ICok ILY FB XG) as SR.
pose proof (PMAGLN.get_length_ok L ar C HI LY HIok SR MKE) as GL.
pose proof (PMARZ.str_resize_ok L ar C IL HI LY HIok ICok ILY OPN OPD) as RZ.
pose proof (PMASFBT.fill_buffer_tb_ok L ar C HI LY HIok IL ICok ILY XG) as FBT.
pose proof (PMASR5.srd_read_ok L ar C HI LY HIok IL ICok ILY RZ SR FBT) as SRD.
pose proof (PMARSP3.read_span_ok L ar C HI LY HIok FB SRD) as RS.
pose proof (PMAVAL.validate_ok L ar C HI LY HIok GAP) as VAL.
pose proof (PMAB10.is_base10_ok L ar C HI LY HIok IL ICok ILY) as B10.
pose proof (PMARV.read_value_ok L ar C HI LY HIok IL ICok ILY SR GL RS VAL B10 BA BO MKE) as RV.
pose proof (PMARTV.rtv_ok L ar C HI LY HIok IL ICok ILY SR MKE RV) as RTV.
pose proof (PMARDK.read_key_ok L ar C HI LY HIok IL ICok ILY GL RS VAL MKE) as RK.
pose proof (PMAEND.end_array_ok L ar C HI LY HIok IL ICok ILY ASH) as EA.
pose proof (PMAEND.end_object_ok L ar C HI LY HIok IL ICok ILY ASH) as EO.
pose proof (PMASPK.peek_ok L ar C HI LY HIok FB) as PK.
pose proof (PMASIG.ignore_ok L ar C HI LY HIok FB) as IG.
exact (PMALP.parse_ok L ar C HI LY HIok IL ICok ILY RTV RV RK EA EO PK IG MKE ASH).
Qed.
Theorem leaves_closed : ltac2:(TCodec.tc2 tcn__PmALeaves "I'0&5v:v2v;v1%544321&6%146543&8%148765&9%14:987&4%14<;:9&3%14>=<;&7%14@?>=%C231%D261%E291%F2<1%G2?1%H2B1").
Proof.
pose proof (PMAOPN.opnew_ok L ar C HI LY HIok) as OPN.
pose proof (PMAOPD.opdel_ok L ar C HI LY HIok) as OPD.
split; [exact (PMALOC.locale_ctor_ok L ar C IL HI LY HIok ICok ILY MCC)|].
split; [exact (PMALOC.locale_dtor_ok L ar C HI LY HIok)|].
split; [exact (PMAEB.push_mi_ok L ar C HI LY HIok EXT OPN OPD)|].
split; [exact (PMAEU.push_miu_ok L ar C HI LY HIok EXT OPN OPD)|].
split; [exact (PMAANN.ann_shrink_ok L ar C HI LY HIok EXT)|].
split; [exact (PMAANN.ann_delete_ok L ar C HI LY HIok EXT)|].
exact parse_closed.
Qed.
End Leaves.
End SCFG_1.
End PMALV.
