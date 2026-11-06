(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6 ae.

(* [comment removed for export] *)
Module F0A_d0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be"; "ED_0Be_1"; "ED_0Be_2"; "q_0Be"; "TD_0Be_1"; "TD_0Be_2"; "RD_0Be_1"; "RD_0Be_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_0Be_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0Be_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_0Be_1, TD_of, RD_0Be_1; reflexivity. Qed.
Theorem hdf_0Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Be_1 TD_0Be_1 (sD_of ED_0Be_1 1) RD_0Be_1 HeD_0Be_1 HchkD_0Be_1 HTD_0Be_1 DCHK_0Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Be_1 TD_0Be_1 (sD_of ED_0Be_1 1) RD_0Be_1 HeD_0Be_1 HchkD_0Be_1 HTD_0Be_1 DCHK_0Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_0Be_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0Be_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_0Be_2, TD_of, RD_0Be_2; reflexivity. Qed.
Theorem hdf_0Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Be_2 TD_0Be_2 (sD_of ED_0Be_2 2) RD_0Be_2 HeD_0Be_2 HchkD_0Be_2 HTD_0Be_2 DCHK_0Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Be_2 TD_0Be_2 (sD_of ED_0Be_2 2) RD_0Be_2 HeD_0Be_2 HchkD_0Be_2 HTD_0Be_2 DCHK_0Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d0Be.

(* [comment removed for export] *)
Module F0A_d0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf"; "ED_0Bf_1"; "ED_0Bf_2"; "q_0Bf"; "TD_0Bf_1"; "TD_0Bf_2"; "RD_0Bf_1"; "RD_0Bf_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_0Bf_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0Bf_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_0Bf_1, TD_of, RD_0Bf_1; reflexivity. Qed.
Theorem hdf_0Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Bf_1 TD_0Bf_1 (sD_of ED_0Bf_1 1) RD_0Bf_1 HeD_0Bf_1 HchkD_0Bf_1 HTD_0Bf_1 DCHK_0Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Bf_1 TD_0Bf_1 (sD_of ED_0Bf_1 1) RD_0Bf_1 HeD_0Bf_1 HchkD_0Bf_1 HTD_0Bf_1 DCHK_0Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_0Bf_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0Bf_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_0Bf_2, TD_of, RD_0Bf_2; reflexivity. Qed.
Theorem hdf_0Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Bf_2 TD_0Bf_2 (sD_of ED_0Bf_2 2) RD_0Bf_2 HeD_0Bf_2 HchkD_0Bf_2 HTD_0Bf_2 DCHK_0Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0Bf_2 TD_0Bf_2 (sD_of ED_0Bf_2 2) RD_0Bf_2 HeD_0Bf_2 HchkD_0Bf_2 HTD_0Bf_2 DCHK_0Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d0Bf.

(* [comment removed for export] *)
Module F0A_d1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A"; "q_1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "RD_1A_1"; "RD_1A_2"; "RD_1A_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_1A_1 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z1M0SaSdS22SaG0A2S10A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1A_1 : ltac2:(tb__ "0|1|
S6S32SdS30S33S22SaZ1M0A2S38G0A1S37G0A1SaS10A5S18S31SaA1A1A2A3").
Proof. unfold TD_1A_1, TD_of, RD_1A_1; reflexivity. Qed.
Theorem hdf_1A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1A_1 TD_1A_1 (sD_of ED_1A_1 1) RD_1A_1 HeD_1A_1 HchkD_1A_1 HTD_1A_1 DCHK_1A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1A_1 TD_1A_1 (sD_of ED_1A_1 1) RD_1A_1 HeD_1A_1 HchkD_1A_1 HTD_1A_1 DCHK_1A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_1A_2 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z2M0SbSeS22SbG0A2S11A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1A_2 : ltac2:(tb__ "0|1|
S6S32SeS30S33S22SbZ2M0A2S38G0A1S37G0A1SbS11A5S18S31SbA1A1A2A3").
Proof. unfold TD_1A_2, TD_of, RD_1A_2; reflexivity. Qed.
Theorem hdf_1A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SbSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1A_2 TD_1A_2 (sD_of ED_1A_2 2) RD_1A_2 HeD_1A_2 HchkD_1A_2 HTD_1A_2 DCHK_1A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SbSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1A_2 TD_1A_2 (sD_of ED_1A_2 2) RD_1A_2 HeD_1A_2 HchkD_1A_2 HTD_1A_2 DCHK_1A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_1A_3 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z3M0ScSfS22ScG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1A_3 : ltac2:(tb__ "0|1|
S6S32SfS30S33S22ScZ3M0A2S38G0A1S37G0A1ScS12A5S18S31ScA1A1A2A3").
Proof. unfold TD_1A_3, TD_of, RD_1A_3; reflexivity. Qed.
Theorem hdf_1A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6ScSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1A_3 TD_1A_3 (sD_of ED_1A_3 3) RD_1A_3 HeD_1A_3 HchkD_1A_3 HTD_1A_3 DCHK_1A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6ScSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1A_3 TD_1A_3 (sD_of ED_1A_3 3) RD_1A_3 HeD_1A_3 HchkD_1A_3 HTD_1A_3 DCHK_1A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d1A.

(* [comment removed for export] *)
Module F0A_d1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be"; "q_1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "RD_1Be_1"; "RD_1Be_2"; "RD_1Be_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_1Be_1 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z1M0SaSdS22SaG0A2S10A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1Be_1 : ltac2:(tb__ "0|1|
S6S32SdS30S33S22SaZ1M0A2S38G0A1S37G0A1SaS10A5S18S31SaA1A1A2A3").
Proof. unfold TD_1Be_1, TD_of, RD_1Be_1; reflexivity. Qed.
Theorem hdf_1Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Be_1 TD_1Be_1 (sD_of ED_1Be_1 1) RD_1Be_1 HeD_1Be_1 HchkD_1Be_1 HTD_1Be_1 DCHK_1Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Be_1 TD_1Be_1 (sD_of ED_1Be_1 1) RD_1Be_1 HeD_1Be_1 HchkD_1Be_1 HTD_1Be_1 DCHK_1Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_1Be_2 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z2M0SbSeS22SbG0A2S11A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1Be_2 : ltac2:(tb__ "0|1|
S6S32SeS30S33S22SbZ2M0A2S38G0A1S37G0A1SbS11A5S18S31SbA1A1A2A3").
Proof. unfold TD_1Be_2, TD_of, RD_1Be_2; reflexivity. Qed.
Theorem hdf_1Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SbSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Be_2 TD_1Be_2 (sD_of ED_1Be_2 2) RD_1Be_2 HeD_1Be_2 HchkD_1Be_2 HTD_1Be_2 DCHK_1Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SbSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Be_2 TD_1Be_2 (sD_of ED_1Be_2 2) RD_1Be_2 HeD_1Be_2 HchkD_1Be_2 HTD_1Be_2 DCHK_1Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_1Be_3 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z3M0ScSfS22ScG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1Be_3 : ltac2:(tb__ "0|1|
S6S32SfS30S33S22ScZ3M0A2S38G0A1S37G0A1ScS12A5S18S31ScA1A1A2A3").
Proof. unfold TD_1Be_3, TD_of, RD_1Be_3; reflexivity. Qed.
Theorem hdf_1Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6ScSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Be_3 TD_1Be_3 (sD_of ED_1Be_3 3) RD_1Be_3 HeD_1Be_3 HchkD_1Be_3 HTD_1Be_3 DCHK_1Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6ScSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Be_3 TD_1Be_3 (sD_of ED_1Be_3 3) RD_1Be_3 HeD_1Be_3 HchkD_1Be_3 HTD_1Be_3 DCHK_1Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d1Be.

(* [comment removed for export] *)
Module F0A_d1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf"; "q_1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "RD_1Bf_1"; "RD_1Bf_2"; "RD_1Bf_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_1Bf_1 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z1M0SaSdS22SaG0A2S10A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1Bf_1 : ltac2:(tb__ "0|1|
S6S32SdS30S33S22SaZ1M0A2S38G0A1S37G0A1SaS10A5S18S31SaA1A1A2A3").
Proof. unfold TD_1Bf_1, TD_of, RD_1Bf_1; reflexivity. Qed.
Theorem hdf_1Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Bf_1 TD_1Bf_1 (sD_of ED_1Bf_1 1) RD_1Bf_1 HeD_1Bf_1 HchkD_1Bf_1 HTD_1Bf_1 DCHK_1Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Bf_1 TD_1Bf_1 (sD_of ED_1Bf_1 1) RD_1Bf_1 HeD_1Bf_1 HchkD_1Bf_1 HTD_1Bf_1 DCHK_1Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_1Bf_2 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z2M0SbSeS22SbG0A2S11A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1Bf_2 : ltac2:(tb__ "0|1|
S6S32SeS30S33S22SbZ2M0A2S38G0A1S37G0A1SbS11A5S18S31SbA1A1A2A3").
Proof. unfold TD_1Bf_2, TD_of, RD_1Bf_2; reflexivity. Qed.
Theorem hdf_1Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SbSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Bf_2 TD_1Bf_2 (sD_of ED_1Bf_2 2) RD_1Bf_2 HeD_1Bf_2 HchkD_1Bf_2 HTD_1Bf_2 DCHK_1Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SbSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Bf_2 TD_1Bf_2 (sD_of ED_1Bf_2 2) RD_1Bf_2 HeD_1Bf_2 HchkD_1Bf_2 HTD_1Bf_2 DCHK_1Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_1Bf_3 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z3M0ScSfS22ScG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_1Bf_3 : ltac2:(tb__ "0|1|
S6S32SfS30S33S22ScZ3M0A2S38G0A1S37G0A1ScS12A5S18S31ScA1A1A2A3").
Proof. unfold TD_1Bf_3, TD_of, RD_1Bf_3; reflexivity. Qed.
Theorem hdf_1Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6ScSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_1Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Bf_3 TD_1Bf_3 (sD_of ED_1Bf_3 3) RD_1Bf_3 HeD_1Bf_3 HchkD_1Bf_3 HTD_1Bf_3 DCHK_1Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_1Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6ScSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_1Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_1Bf_3 TD_1Bf_3 (sD_of ED_1Bf_3 3) RD_1Bf_3 HeD_1Bf_3 HchkD_1Bf_3 HTD_1Bf_3 DCHK_1Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d1Bf.

(* [comment removed for export] *)
Module F0A_dL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A"; "ED_L0A_1"; "ED_L0A_2"; "q_L0A"; "TD_L0A_1"; "TD_L0A_2"; "RD_L0A_1"; "RD_L0A_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L0A_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L0A_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_L0A_1, TD_of, RD_L0A_1; reflexivity. Qed.
Theorem hdf_L0A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_L0A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0A_1 TD_L0A_1 (sD_of ED_L0A_1 1) RD_L0A_1 HeD_L0A_1 HchkD_L0A_1 HTD_L0A_1 DCHK_L0A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L0A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_L0A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0A_1 TD_L0A_1 (sD_of ED_L0A_1 1) RD_L0A_1 HeD_L0A_1 HchkD_L0A_1 HTD_L0A_1 DCHK_L0A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L0A_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L0A_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_L0A_2, TD_of, RD_L0A_2; reflexivity. Qed.
Theorem hdf_L0A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_L0A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0A_2 TD_L0A_2 (sD_of ED_L0A_2 2) RD_L0A_2 HeD_L0A_2 HchkD_L0A_2 HTD_L0A_2 DCHK_L0A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L0A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_L0A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0A_2 TD_L0A_2 (sD_of ED_L0A_2 2) RD_L0A_2 HeD_L0A_2 HchkD_L0A_2 HTD_L0A_2 DCHK_L0A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL0A.

