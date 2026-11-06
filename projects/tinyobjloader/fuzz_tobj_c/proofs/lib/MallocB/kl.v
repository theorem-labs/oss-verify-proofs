(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3 ie.

(* [comment removed for export] *)
Module F0A_d2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "q_2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "RD_2A_1"; "RD_2A_2"; "RD_2A_3"; "RD_2A_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A.
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
Module F0A_d2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "q_2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "RD_2Be_1"; "RD_2Be_2"; "RD_2Be_3"; "RD_2Be_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be.
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
Module F0A_d2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "q_2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "RD_2Bf_1"; "RD_2Bf_2"; "RD_2Bf_3"; "RD_2Bf_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.
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
Module F0A_dL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A"; "q_L1A"; "ED_L1A_1"; "ED_L1A_2"; "ED_L1A_3"; "TD_L1A_1"; "TD_L1A_2"; "TD_L1A_3"; "RD_L1A_1"; "RD_L1A_2"; "RD_L1A_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A.
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
Module F0A_dL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be"; "q_L1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "RD_L1Be_1"; "RD_L1Be_2"; "RD_L1Be_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be.
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
Module F0A_dL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf"; "q_L1Bf"; "ED_L1Bf_1"; "ED_L1Bf_2"; "ED_L1Bf_3"; "TD_L1Bf_1"; "TD_L1Bf_2"; "TD_L1Bf_3"; "RD_L1Bf_1"; "RD_L1Bf_2"; "RD_L1Bf_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface Inv InvLaws SegD_wf SegD_states DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.F0A_cL1Bf.
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

