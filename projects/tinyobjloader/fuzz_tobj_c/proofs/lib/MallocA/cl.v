(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_044.   (* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.

(* [comment removed for export] *)
Module F0A_d2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A"; "q_2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "RD_2A_1"; "RD_2A_2"; "RD_2A_3"; "RD_2A_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_2A_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2A_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_2A_1, TD_of, RD_2A_1; reflexivity. Qed.
Theorem hdf_2A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_1 TD_2A_1 (sD_of ED_2A_1 1) RD_2A_1 HeD_2A_1 HchkD_2A_1 HTD_2A_1 DCHK_2A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_1 TD_2A_1 (sD_of ED_2A_1 1) RD_2A_1 HeD_2A_1 HchkD_2A_1 HTD_2A_1 DCHK_2A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2A_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2A_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_2A_2, TD_of, RD_2A_2; reflexivity. Qed.
Theorem hdf_2A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_2 TD_2A_2 (sD_of ED_2A_2 2) RD_2A_2 HeD_2A_2 HchkD_2A_2 HTD_2A_2 DCHK_2A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_2 TD_2A_2 (sD_of ED_2A_2 2) RD_2A_2 HeD_2A_2 HchkD_2A_2 HTD_2A_2 DCHK_2A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2A_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2A_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_2A_3, TD_of, RD_2A_3; reflexivity. Qed.
Theorem hdf_2A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_3 TD_2A_3 (sD_of ED_2A_3 3) RD_2A_3 HeD_2A_3 HchkD_2A_3 HTD_2A_3 DCHK_2A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2A_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2A 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_3 TD_2A_3 (sD_of ED_2A_3 3) RD_2A_3 HeD_2A_3 HchkD_2A_3 HTD_2A_3 DCHK_2A_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2A_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2A_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_2A_4, TD_of, RD_2A_4; reflexivity. Qed.
Theorem hdf_2A_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2A 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_4 TD_2A_4 (sD_of ED_2A_4 4) RD_2A_4 HeD_2A_4 HchkD_2A_4 HTD_2A_4 DCHK_2A_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2A_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2A 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2A_4 TD_2A_4 (sD_of ED_2A_4 4) RD_2A_4 HeD_2A_4 HchkD_2A_4 HTD_2A_4 DCHK_2A_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d2A.

(* [comment removed for export] *)
Module F0A_dL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "q_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "RD_L0Be_1"; "RD_L0Be_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L0Be_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L0Be_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_L0Be_1, TD_of, RD_L0Be_1; reflexivity. Qed.
Theorem hdf_L0Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_L0Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Be_1 TD_L0Be_1 (sD_of ED_L0Be_1 1) RD_L0Be_1 HeD_L0Be_1 HchkD_L0Be_1 HTD_L0Be_1 DCHK_L0Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L0Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_L0Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Be_1 TD_L0Be_1 (sD_of ED_L0Be_1 1) RD_L0Be_1 HeD_L0Be_1 HchkD_L0Be_1 HTD_L0Be_1 DCHK_L0Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L0Be_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L0Be_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_L0Be_2, TD_of, RD_L0Be_2; reflexivity. Qed.
Theorem hdf_L0Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_L0Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Be_2 TD_L0Be_2 (sD_of ED_L0Be_2 2) RD_L0Be_2 HeD_L0Be_2 HchkD_L0Be_2 HTD_L0Be_2 DCHK_L0Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L0Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_L0Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Be_2 TD_L0Be_2 (sD_of ED_L0Be_2 2) RD_L0Be_2 HeD_L0Be_2 HchkD_L0Be_2 HTD_L0Be_2 DCHK_L0Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL0Be.

(* [comment removed for export] *)
Module F0A_dL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Bf"; "ED_L0Bf_1"; "ED_L0Bf_2"; "q_L0Bf"; "TD_L0Bf_1"; "TD_L0Bf_2"; "RD_L0Bf_1"; "RD_L0Bf_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L0Bf_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L0Bf_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_L0Bf_1, TD_of, RD_L0Bf_1; reflexivity. Qed.
Theorem hdf_L0Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_L0Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Bf_1 TD_L0Bf_1 (sD_of ED_L0Bf_1 1) RD_L0Bf_1 HeD_L0Bf_1 HchkD_L0Bf_1 HTD_L0Bf_1 DCHK_L0Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L0Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_L0Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Bf_1 TD_L0Bf_1 (sD_of ED_L0Bf_1 1) RD_L0Bf_1 HeD_L0Bf_1 HchkD_L0Bf_1 HTD_L0Bf_1 DCHK_L0Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L0Bf_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L0Bf_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_L0Bf_2, TD_of, RD_L0Bf_2; reflexivity. Qed.
Theorem hdf_L0Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_L0Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Bf_2 TD_L0Bf_2 (sD_of ED_L0Bf_2 2) RD_L0Bf_2 HeD_L0Bf_2 HchkD_L0Bf_2 HTD_L0Bf_2 DCHK_L0Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L0Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_L0Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L0Bf_2 TD_L0Bf_2 (sD_of ED_L0Bf_2 2) RD_L0Bf_2 HeD_L0Bf_2 HchkD_L0Bf_2 HTD_L0Bf_2 DCHK_L0Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL0Bf.

(* [comment removed for export] *)
Module F0A_d2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be"; "q_2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "RD_2Be_1"; "RD_2Be_2"; "RD_2Be_3"; "RD_2Be_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_2Be_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Be_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_2Be_1, TD_of, RD_2Be_1; reflexivity. Qed.
Theorem hdf_2Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_1 TD_2Be_1 (sD_of ED_2Be_1 1) RD_2Be_1 HeD_2Be_1 HchkD_2Be_1 HTD_2Be_1 DCHK_2Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_1 TD_2Be_1 (sD_of ED_2Be_1 1) RD_2Be_1 HeD_2Be_1 HchkD_2Be_1 HTD_2Be_1 DCHK_2Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2Be_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Be_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_2Be_2, TD_of, RD_2Be_2; reflexivity. Qed.
Theorem hdf_2Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_2 TD_2Be_2 (sD_of ED_2Be_2 2) RD_2Be_2 HeD_2Be_2 HchkD_2Be_2 HTD_2Be_2 DCHK_2Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_2 TD_2Be_2 (sD_of ED_2Be_2 2) RD_2Be_2 HeD_2Be_2 HchkD_2Be_2 HTD_2Be_2 DCHK_2Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2Be_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Be_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_2Be_3, TD_of, RD_2Be_3; reflexivity. Qed.
Theorem hdf_2Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_3 TD_2Be_3 (sD_of ED_2Be_3 3) RD_2Be_3 HeD_2Be_3 HchkD_2Be_3 HTD_2Be_3 DCHK_2Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_3 TD_2Be_3 (sD_of ED_2Be_3 3) RD_2Be_3 HeD_2Be_3 HchkD_2Be_3 HTD_2Be_3 DCHK_2Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_2Be_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_2Be_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_2Be_4, TD_of, RD_2Be_4; reflexivity. Qed.
Theorem hdf_2Be_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_2Be 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_4 TD_2Be_4 (sD_of ED_2Be_4 4) RD_2Be_4 HeD_2Be_4 HchkD_2Be_4 HTD_2Be_4 DCHK_2Be_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_2Be_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_2Be 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_2Be_4 TD_2Be_4 (sD_of ED_2Be_4 4) RD_2Be_4 HeD_2Be_4 HchkD_2Be_4 HTD_2Be_4 DCHK_2Be_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d2Be.

(* [comment removed for export] *)
Module DepotCallMW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cl.DepotCallMW2.INST"; "T4_i"; "nobj_i"; "CP1"; "CP2"; "CP3"; "CP4"; "sd_1"; "sd_2"; "sd_3"; "sd_4"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "list"; "nil"; "option"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.DepotCallW"; "T40"; "T4a"; "T4b"; "T4c"; "T4d"; "T4m1"; "T4m2"; "T4m3"; "X4"; "X4a"; "X4b"; "X4c"; "X4r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C5"; "E4d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.DepotCallW.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLe. Let tmax : Z := 4.

Lemma by_casesN : ltac2:(tb__ "0|2|
S26OF_;R1Z1M0A1R2Z2A1R3Z3A1R4Z4M1A1S26S2S15G0R1A2S15R1G1A2A2R7R2A1F_;Fsz;F_;F_;F_;F_;FP;").
Proof. intros P H1 H2 H3 H4 sz Hsz. assert (E : sz = 1 \/ sz = 2 \/ sz = 3 \/ sz = 4) by lia. destruct E as [-> | [-> | [-> | ->]]]; assumption. Qed.
Ltac memo_rw t M := lazymatch goal with |- context [t] => pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta | _ => fail "memo_rw: stage term not found" t end.
Ltac vmc := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma mE : ltac2:(tb__ "0|0|
S3S0S0S1S0S2aS28U2A1Vst;Vtmax;A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mC5 : ltac2:(tb__ "0|0|
S3S0S0S1S0S29S28U2A1Vst;Vtmax;A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U2Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 2) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU2Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 2%nat st tmax 1) mXr_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U2Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 2%nat st tmax 1) mXa_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U2Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 2%nat st tmax 1) mXb_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU2Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 2%nat st tmax 1) mXc_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U2Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 2) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU2Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 2%nat st tmax 2) mXr_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U2Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 2%nat st tmax 2) mXa_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U2Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 2%nat st tmax 2) mXb_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU2Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 2%nat st tmax 2) mXc_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U2Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 2) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU2Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 2%nat st tmax 3) mXr_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U2Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 2%nat st tmax 3) mXa_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U2Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 2%nat st tmax 3) mXb_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU2Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 2%nat st tmax 3) mXc_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U2Vst;Vtmax;Z4A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 2) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU2Vst;Vtmax;Z4A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 2%nat st tmax 4) mXr_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U2Vst;Vtmax;Z4A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 2%nat st tmax 4) mXa_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U2Vst;Vtmax;Z4A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 2%nat st tmax 4) mXb_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU2Vst;Vtmax;Z4A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 2%nat st tmax 4) mXc_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.

Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S12SfSfS23S10S24A1M0A2S0A2M1A1G1Lo;Vo;G1R1Lx;S13SfS10SfS27S25A2M2A1M3G0A2S0S13G3G0S11G2A1S11S24A1A4S2bZ0A1A4X12x2").
Definition CP1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_1) 1)).
Definition CP2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_2) 2)).
Definition CP3 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_3) 3)).
Definition CP4 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_4) 4)).
Definition CP (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|1|
SeSfSfS23S10S24A1A2S0A2L_;M0S14Vsz;Z1A2S6G0S14Vsz;Z2A2S7G0S14Vsz;Z3A2S8S9Xex2Xex2Xex2").
Definition s4_i (sz : Z) : wsub := fst (fst (CP sz)).
Definition R4_i (sz : Z) : list sobj := snd (fst (CP sz)).
Definition T4_i (sz : Z) : axst := snd (CP sz).
Definition nobj_i : nat := 50%nat.
Lemma mT0_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S16U2Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 2%nat st tmax 1) mX_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U2Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 2%nat st tmax T4_i 1) mT0_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U2Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 2%nat st tmax T4_i 1) mTa_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U2Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 2%nat st tmax T4_i 1) mTb_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU2Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 2%nat st tmax T4_i nobj_i 1) mTc_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU2Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 2%nat st tmax T4_i nobj_i 1) mT1_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU2Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 2%nat st tmax T4_i nobj_i 1) mT2_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU2Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 2%nat st tmax T4_i nobj_i 1) mT3_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT0_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S16U2Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 2%nat st tmax 2) mX_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U2Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 2%nat st tmax T4_i 2) mT0_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U2Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 2%nat st tmax T4_i 2) mTa_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U2Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 2%nat st tmax T4_i 2) mTb_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU2Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 2%nat st tmax T4_i nobj_i 2) mTc_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU2Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 2%nat st tmax T4_i nobj_i 2) mT1_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU2Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 2%nat st tmax T4_i nobj_i 2) mT2_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU2Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 2%nat st tmax T4_i nobj_i 2) mT3_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT0_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S16U2Vst;Vtmax;S4Z3A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 2%nat st tmax 3) mX_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U2Vst;Vtmax;S4Z3A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 2%nat st tmax T4_i 3) mT0_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U2Vst;Vtmax;S4Z3A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 2%nat st tmax T4_i 3) mTa_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U2Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 2%nat st tmax T4_i 3) mTb_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU2Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 2%nat st tmax T4_i nobj_i 3) mTc_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU2Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 2%nat st tmax T4_i nobj_i 3) mT1_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU2Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 2%nat st tmax T4_i nobj_i 3) mT2_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU2Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 2%nat st tmax T4_i nobj_i 3) mT3_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT0_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S16U2Vst;Vtmax;S4Z4A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 2%nat st tmax 4) mX_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U2Vst;Vtmax;S4Z4A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 2%nat st tmax T4_i 4) mT0_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U2Vst;Vtmax;S4Z4A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 2%nat st tmax T4_i 4) mTa_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U2Vst;Vtmax;S4S5Z4A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 2%nat st tmax T4_i 4) mTb_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU2Vst;Vtmax;S4S5Z4A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 2%nat st tmax T4_i nobj_i 4) mTc_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU2Vst;Vtmax;S4S5Z4A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 2%nat st tmax T4_i nobj_i 4) mT1_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU2Vst;Vtmax;S4S5Z4A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 2%nat st tmax T4_i nobj_i 4) mT2_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_4 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU2Vst;Vtmax;S4S5Z4A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 2%nat st tmax T4_i nobj_i 4) mT3_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Definition sd_1 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_1)) (ax_S (proj1_sig mC5))).
Definition sd_2 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_2)) (ax_S (proj1_sig mC5))).
Definition sd_3 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_3)) (ax_S (proj1_sig mC5))).
Definition sd_4 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_4)) (ax_S (proj1_sig mC5))).
Definition sd_i (sz : Z) : wsub := ltac2:(tb__ "0|1|
SeS23L_;M0S14Vsz;Z1A2SaG0S14Vsz;Z2A2SbG0S14Vsz;Z3A2ScSdXex2Xex2Xex2").

End INST.
End DepotCallMW2.

