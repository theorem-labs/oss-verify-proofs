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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bg bh br bf ah.

(* [comment removed for export] *)
Module F0A_d2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf"; "q_2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "RD_2Bf_1"; "RD_2Bf_2"; "RD_2Bf_3"; "RD_2Bf_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_2Bf_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Bf_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_2Bf_1, TD_of, RD_2Bf_1; reflexivity. Qed.
Theorem hdf_2Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_1 TD_2Bf_1 (sD_of ED_2Bf_1 1) RD_2Bf_1 HeD_2Bf_1 HchkD_2Bf_1 HTD_2Bf_1 DCHK_2Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_1 TD_2Bf_1 (sD_of ED_2Bf_1 1) RD_2Bf_1 HeD_2Bf_1 HchkD_2Bf_1 HTD_2Bf_1 DCHK_2Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2Bf_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Bf_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_2Bf_2, TD_of, RD_2Bf_2; reflexivity. Qed.
Theorem hdf_2Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_2 TD_2Bf_2 (sD_of ED_2Bf_2 2) RD_2Bf_2 HeD_2Bf_2 HchkD_2Bf_2 HTD_2Bf_2 DCHK_2Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_2 TD_2Bf_2 (sD_of ED_2Bf_2 2) RD_2Bf_2 HeD_2Bf_2 HchkD_2Bf_2 HTD_2Bf_2 DCHK_2Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2Bf_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Bf_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_2Bf_3, TD_of, RD_2Bf_3; reflexivity. Qed.
Theorem hdf_2Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_3 TD_2Bf_3 (sD_of ED_2Bf_3 3) RD_2Bf_3 HeD_2Bf_3 HchkD_2Bf_3 HTD_2Bf_3 DCHK_2Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_3 TD_2Bf_3 (sD_of ED_2Bf_3 3) RD_2Bf_3 HeD_2Bf_3 HchkD_2Bf_3 HTD_2Bf_3 DCHK_2Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2Bf_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Bf_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_2Bf_4, TD_of, RD_2Bf_4; reflexivity. Qed.
Theorem hdf_2Bf_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Bf 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_4 TD_2Bf_4 (sD_of ED_2Bf_4 4) RD_2Bf_4 HeD_2Bf_4 HchkD_2Bf_4 HTD_2Bf_4 DCHK_2Bf_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Bf_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Bf 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Bf_4 TD_2Bf_4 (sD_of ED_2Bf_4 4) RD_2Bf_4 HeD_2Bf_4 HchkD_2Bf_4 HTD_2Bf_4 DCHK_2Bf_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d2Bf.

(* [comment removed for export] *)
Module MallocHitTail0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineMallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9j OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.DepotCallI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineMallocS5t.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0T.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S9S8VCST;R1A2S8S20R2A2S1dF_;F_;Fa;").

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S8VCST;R1A2S1eS21R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S17VAInv;VW;Vst;VA;VKc;S1PcA1A6").

Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Definition KEEP (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S1fVCST;VXGL;VA;Va;A4").

Theorem malloc_hit_tail_0_P : ltac2:(tb__ "0|1|
ScOF_;S1aS14S0S5S1cQ40A1A1S5S7SeS10A2M0A1SfVsegs;SdR3R2R1A5SaS22G0S6SeS10S18S13VW0;Vst0;A3S16VAInv;VCST;VXGL;R6R5A5A4R2A3S15R6A1S4Vsegs;R9S2R7A1A3S11Vsegs;RaS2R8A1A3S0SbVsegs;RcS3Vsegs;S1bVW0;Vst0;RbRaR9A5S12VW0;Vst0;Z2A3R1R8A5R6A4FrhoX;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl.
  pose proof (depot_call_HD_0 CST XGL HCST HXGL HCSTD ok A Kc rho Q HKc Hokl Hokpl) as HD.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).
  set (nv := bv_unsigned (rw rho 12%positive)).

  apply (spine_s3p_tail 0%nat st0 2 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 ok A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.

  apply (spine_s4 0%nat st0 2 Cert4_0 (KEEP A) ok A Kc rho tp Q HUS HKc (Hokf A) HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  pose proof Hokl as HokA'.

  assert (K7 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s7 0%nat st0 2 Cert7_0 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt').
    - intros Hm0 rhoY8.
      apply (spine_s8_gen 0%nat st0 2 (C8 W0 st0 2) (C9 W0 st0 2) (E8a W0 st0 2) (E8b W0 st0 2) CC8ma_0 Cert8_0 HCC8ma_0 W8a_0 D8a_0 NX8a_0 s8_0 sd8_0 R8_0 T8_0 He8_0 Hchk8_0 HT8_0 FBC8_0 FBT8_0 ENT8_0 SID8_0 NXC8_0 i8_0 S8s_0 SPL8_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i.s8b_0 sd8b_0 R8b_0 T8b_0 He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0 i9_0 SU_0 SM_0 ENTU_0 SIDU_0 MRG_0 s9m_0 ENTM_0 SIDM_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9_P 0%nat st0 CST XGL HCST HXGL HCSTM law_die false (C9 W0 st0 2) F9a_nf F9b_nf Cert9a_0 Cert9b_0 NX9_0 FGC_0
               swc_a scells_a hcells_a swc_b scells_b hcells_b s9_a s9_b FH_a_0 FH_b_0 ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (spine_s7p 0%nat st0 2 Cert7p_0 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY8.
      apply (spine_s8_gen 0%nat st0 2 (C8p W0 st0 2) (C9p W0 st0 2) (E8pa W0 st0 2) (E8pb W0 st0 2) CC8map_0 Cert8p_0 HCC8map_0 W8ap_0 D8ap_0 NX8ap_0 s8p_0 sd8p_0 R8p_0 T8p_0 He8p_0 Hchk8p_0 HT8p_0 FBC8p_0 FBT8p_0 ENT8p_0 SID8p_0 NXC8p_0 i8p_0 S8sp_0 SPL8p_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i.s8bp_0 sd8bp_0 R8bp_0 T8bp_0 He8bp_0 Hchk8bp_0 HT8bp_0 FBC8bp_0 FBT8bp_0 NXC8bp_0 i9p_0 SUp_0 SMp_0 ENTUp_0 SIDUp_0 MRGp_0 s9mp_0 ENTMp_0 SIDMp_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9_P 0%nat st0 CST XGL HCST HXGL HCSTM law_die true (C9p W0 st0 2) F9pa_nf F9pb_nf Cert9pa_0 Cert9pb_0 NX9p_0 FGCp_0
               swc_pa scells_pa hcells_pa swc_pb scells_pb hcells_pb s9_pa s9_pb FH_pa_0 FH_pb_0 ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }

  assert (K6 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s6 0%nat st0 2 Cert6_0 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    apply (spine_s6l 0%nat st0 2 Cert6l_0 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6_0 ok A' Kc rho' tpY Q HUS HKc HokA').
    intros rhoY6b tpY6b.
    apply (spine_s6b 0%nat st0 2 Cert6b_0 s7j_0 ENT7j_0 SID7j_0 ok A' Kc rho' tpY6b Q HUS HKc HokA'). exact (K7 tpY6b). }

  apply (spine_s5 0%nat st0 2 Cert5_0 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (spine_s5b 0%nat st0 2 Cert5b_0 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0
           ok A' Kc rho' tp' Q HUS HKc HokA').
  intros rhoX5c.
  apply (spine_s5c 0%nat st0 2 Cert5c_0 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0
           ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt').
  intros rhoX5d tp5d.
  apply (spine_s5d 0%nat st0 2 Cert5d_0 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0
           ok A' Kc rho' tp5d Q HUS HKc HokA' Hcnt').
  intros rhoX5e tp5e.
  apply (spine_s5e 0%nat st0 2 Cert5e_0 s6j_0 ENT6j_0 SID6j_0 ok A' Kc rho' tp5e Q HUS HKc HokA'). exact (K6 tp5e).
Qed.

Theorem malloc_hit_tail_0 : ltac2:(tb__ "0|0|
ScOF_;S1aS14S0S5S1cQ40A1A1SfVsegs;SdR2R1S19S13VAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5SaS15R4A1S4Vsegs;R7S2R5A1A3S11Vsegs;R8S2R6A1A3S0SbVsegs;RaS3Vsegs;S1bVW0;Vst0;R9R8R7A5S12VW0;Vst0;Z2A3R1R6A5R5A4FrhoX;F_;F_;F_;TQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp. exact (malloc_hit_tail_0_P ok A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0T.
End MallocHitTail0.

(* [comment removed for export] *)
Module F0A_dL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A"; "q_L1A"; "ED_L1A_1"; "ED_L1A_2"; "ED_L1A_3"; "TD_L1A_1"; "TD_L1A_2"; "TD_L1A_3"; "RD_L1A_1"; "RD_L1A_2"; "RD_L1A_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L1A_1 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z1M0SaSdS22SaG0A2S10A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1A_1 : ltac2:(tb__ "0|1|
S6S32SdS30S33S22SaZ1M0A2S38G0A1S37G0A1SaS10A5S18S31SaA1A1A2A3").
Proof. unfold TD_L1A_1, TD_of, RD_L1A_1; reflexivity. Qed.
Theorem hdf_L1A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1A_1 TD_L1A_1 (sD_of ED_L1A_1 1) RD_L1A_1 HeD_L1A_1 HchkD_L1A_1 HTD_L1A_1 DCHK_L1A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1A_1 TD_L1A_1 (sD_of ED_L1A_1 1) RD_L1A_1 HeD_L1A_1 HchkD_L1A_1 HTD_L1A_1 DCHK_L1A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L1A_2 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z2M0SbSeS22SbG0A2S11A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1A_2 : ltac2:(tb__ "0|1|
S6S32SeS30S33S22SbZ2M0A2S38G0A1S37G0A1SbS11A5S18S31SbA1A1A2A3").
Proof. unfold TD_L1A_2, TD_of, RD_L1A_2; reflexivity. Qed.
Theorem hdf_L1A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SbSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1A_2 TD_L1A_2 (sD_of ED_L1A_2 2) RD_L1A_2 HeD_L1A_2 HchkD_L1A_2 HTD_L1A_2 DCHK_L1A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SbSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1A_2 TD_L1A_2 (sD_of ED_L1A_2 2) RD_L1A_2 HeD_L1A_2 HchkD_L1A_2 HTD_L1A_2 DCHK_L1A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L1A_3 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z3M0ScSfS22ScG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1A_3 : ltac2:(tb__ "0|1|
S6S32SfS30S33S22ScZ3M0A2S38G0A1S37G0A1ScS12A5S18S31ScA1A1A2A3").
Proof. unfold TD_L1A_3, TD_of, RD_L1A_3; reflexivity. Qed.
Theorem hdf_L1A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6ScSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1A_3 TD_L1A_3 (sD_of ED_L1A_3 3) RD_L1A_3 HeD_L1A_3 HchkD_L1A_3 HTD_L1A_3 DCHK_L1A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6ScSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1A_3 TD_L1A_3 (sD_of ED_L1A_3 3) RD_L1A_3 HeD_L1A_3 HchkD_L1A_3 HTD_L1A_3 DCHK_L1A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL1A.

(* [comment removed for export] *)
Module F0A_dL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf"; "q_L1Bf"; "ED_L1Bf_1"; "ED_L1Bf_2"; "ED_L1Bf_3"; "TD_L1Bf_1"; "TD_L1Bf_2"; "TD_L1Bf_3"; "RD_L1Bf_1"; "RD_L1Bf_2"; "RD_L1Bf_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L1Bf_1 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z1M0SaSdS22SaG0A2S10A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1Bf_1 : ltac2:(tb__ "0|1|
S6S32SdS30S33S22SaZ1M0A2S38G0A1S37G0A1SaS10A5S18S31SaA1A1A2A3").
Proof. unfold TD_L1Bf_1, TD_of, RD_L1Bf_1; reflexivity. Qed.
Theorem hdf_L1Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Bf_1 TD_L1Bf_1 (sD_of ED_L1Bf_1 1) RD_L1Bf_1 HeD_L1Bf_1 HchkD_L1Bf_1 HTD_L1Bf_1 DCHK_L1Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Bf_1 TD_L1Bf_1 (sD_of ED_L1Bf_1 1) RD_L1Bf_1 HeD_L1Bf_1 HchkD_L1Bf_1 HTD_L1Bf_1 DCHK_L1Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L1Bf_2 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z2M0SbSeS22SbG0A2S11A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1Bf_2 : ltac2:(tb__ "0|1|
S6S32SeS30S33S22SbZ2M0A2S38G0A1S37G0A1SbS11A5S18S31SbA1A1A2A3").
Proof. unfold TD_L1Bf_2, TD_of, RD_L1Bf_2; reflexivity. Qed.
Theorem hdf_L1Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SbSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Bf_2 TD_L1Bf_2 (sD_of ED_L1Bf_2 2) RD_L1Bf_2 HeD_L1Bf_2 HchkD_L1Bf_2 HTD_L1Bf_2 DCHK_L1Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SbSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Bf_2 TD_L1Bf_2 (sD_of ED_L1Bf_2 2) RD_L1Bf_2 HeD_L1Bf_2 HchkD_L1Bf_2 HTD_L1Bf_2 DCHK_L1Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L1Bf_3 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z3M0ScSfS22ScG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1Bf_3 : ltac2:(tb__ "0|1|
S6S32SfS30S33S22ScZ3M0A2S38G0A1S37G0A1ScS12A5S18S31ScA1A1A2A3").
Proof. unfold TD_L1Bf_3, TD_of, RD_L1Bf_3; reflexivity. Qed.
Theorem hdf_L1Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6ScSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Bf_3 TD_L1Bf_3 (sD_of ED_L1Bf_3 3) RD_L1Bf_3 HeD_L1Bf_3 HchkD_L1Bf_3 HTD_L1Bf_3 DCHK_L1Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6ScSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Bf_3 TD_L1Bf_3 (sD_of ED_L1Bf_3 3) RD_L1Bf_3 HeD_L1Bf_3 HchkD_L1Bf_3 HTD_L1Bf_3 DCHK_L1Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL1Bf.

(* [comment removed for export] *)
Module F0A_dL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be"; "q_L1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "RD_L1Be_1"; "RD_L1Be_2"; "RD_L1Be_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L1Be_1 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z1M0SaSdS22SaG0A2S10A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1Be_1 : ltac2:(tb__ "0|1|
S6S32SdS30S33S22SaZ1M0A2S38G0A1S37G0A1SaS10A5S18S31SaA1A1A2A3").
Proof. unfold TD_L1Be_1, TD_of, RD_L1Be_1; reflexivity. Qed.
Theorem hdf_L1Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Be_1 TD_L1Be_1 (sD_of ED_L1Be_1 1) RD_L1Be_1 HeD_L1Be_1 HchkD_L1Be_1 HTD_L1Be_1 DCHK_L1Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Be_1 TD_L1Be_1 (sD_of ED_L1Be_1 1) RD_L1Be_1 HeD_L1Be_1 HchkD_L1Be_1 HTD_L1Be_1 DCHK_L1Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L1Be_2 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z2M0SbSeS22SbG0A2S11A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1Be_2 : ltac2:(tb__ "0|1|
S6S32SeS30S33S22SbZ2M0A2S38G0A1S37G0A1SbS11A5S18S31SbA1A1A2A3").
Proof. unfold TD_L1Be_2, TD_of, RD_L1Be_2; reflexivity. Qed.
Theorem hdf_L1Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6SbSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Be_2 TD_L1Be_2 (sD_of ED_L1Be_2 2) RD_L1Be_2 HeD_L1Be_2 HchkD_L1Be_2 HTD_L1Be_2 DCHK_L1Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6SbSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Be_2 TD_L1Be_2 (sD_of ED_L1Be_2 2) RD_L1Be_2 HeD_L1Be_2 HchkD_L1Be_2 HTD_L1Be_2 DCHK_L1Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L1Be_3 : ltac2:(tb__ "0|1|
S6S4S1eU1S9Z3M0ScSfS22ScG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L1Be_3 : ltac2:(tb__ "0|1|
S6S32SfS30S33S22ScZ3M0A2S38G0A1S37G0A1ScS12A5S18S31ScA1A1A2A3").
Proof. unfold TD_L1Be_3, TD_of, RD_L1Be_3; reflexivity. Qed.
Theorem hdf_L1Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S15S1aS8R2S19R11A1A3S34S8R3S19R12A1A3S35U1S25S1bR19R18R14A3R4R14R13S21R14R12RfReRdRcA6ScSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 1 q_L1Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Be_3 TD_L1Be_3 (sD_of ED_L1Be_3 3) RD_L1Be_3 HeD_L1Be_3 HchkD_L1Be_3 HTD_L1Be_3 DCHK_L1Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L1Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S29R2A1S2bR2A1S0S2aR5R1A2S7S2cR2A1A1F_;Fa;S27S23S17S1S2eQ40M2A1A1S13S0S0S0S1fS24R8A1S26S8RaR8R7R6A5S2dG0S2S0S0R6R5A4S28RbA1A3S1cR7R6A2S6S0S2fG2S16RbPcA2A2R8A3S1dReRcR9R8R7R6A6S20S9RfA2S14OF_;S36U1S25S1bR16R15R11A3R11R10S21R11RfRcRbRaR9A6ScSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 1 q_L1Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L1Be_3 TD_L1Be_3 (sD_of ED_L1Be_3 3) RD_L1Be_3 HeD_L1Be_3 HchkD_L1Be_3 HTD_L1Be_3 DCHK_L1Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL1Be.

(* [comment removed for export] *)
Module F0A_dL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A"; "q_L2A"; "ED_L2A_1"; "ED_L2A_2"; "ED_L2A_3"; "ED_L2A_4"; "TD_L2A_1"; "TD_L2A_2"; "TD_L2A_3"; "TD_L2A_4"; "RD_L2A_1"; "RD_L2A_2"; "RD_L2A_3"; "RD_L2A_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L2A_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_L2A_1, TD_of, RD_L2A_1; reflexivity. Qed.
Theorem hdf_L2A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_1 TD_L2A_1 (sD_of ED_L2A_1 1) RD_L2A_1 HeD_L2A_1 HchkD_L2A_1 HTD_L2A_1 DCHK_L2A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_1 TD_L2A_1 (sD_of ED_L2A_1 1) RD_L2A_1 HeD_L2A_1 HchkD_L2A_1 HTD_L2A_1 DCHK_L2A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2A_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_L2A_2, TD_of, RD_L2A_2; reflexivity. Qed.
Theorem hdf_L2A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_2 TD_L2A_2 (sD_of ED_L2A_2 2) RD_L2A_2 HeD_L2A_2 HchkD_L2A_2 HTD_L2A_2 DCHK_L2A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_2 TD_L2A_2 (sD_of ED_L2A_2 2) RD_L2A_2 HeD_L2A_2 HchkD_L2A_2 HTD_L2A_2 DCHK_L2A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2A_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_L2A_3, TD_of, RD_L2A_3; reflexivity. Qed.
Theorem hdf_L2A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_3 TD_L2A_3 (sD_of ED_L2A_3 3) RD_L2A_3 HeD_L2A_3 HchkD_L2A_3 HTD_L2A_3 DCHK_L2A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_3 TD_L2A_3 (sD_of ED_L2A_3 3) RD_L2A_3 HeD_L2A_3 HchkD_L2A_3 HTD_L2A_3 DCHK_L2A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2A_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2A_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_L2A_4, TD_of, RD_L2A_4; reflexivity. Qed.
Theorem hdf_L2A_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2A 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_4 TD_L2A_4 (sD_of ED_L2A_4 4) RD_L2A_4 HeD_L2A_4 HchkD_L2A_4 HTD_L2A_4 DCHK_L2A_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2A_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2A 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2A_4 TD_L2A_4 (sD_of ED_L2A_4 4) RD_L2A_4 HeD_L2A_4 HchkD_L2A_4 HTD_L2A_4 DCHK_L2A_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL2A.

