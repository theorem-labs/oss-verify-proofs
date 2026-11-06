(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From Stdlib Require NArith PArith FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.

(* [comment removed for export] *)
Module F0A_d1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be"; "q_1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "RD_1Be_1"; "RD_1Be_2"; "RD_1Be_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf"; "q_1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "RD_1Bf_1"; "RD_1Bf_2"; "RD_1Bf_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.
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
Module F0A_depotG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "ex"; "not"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "andb"; "app"; "prod"; "pair"; "Some"; "cons"; "false"; "fst"; "nat"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SAlu"; "SLit"; "ss_facts"; "SVar"; "sprop_below"; "ss_next"; "valuation"; "sprop_eqb"; "ss_objs"; "sv_eqb"; "agree_below"; "holds"; "rw"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "chain_pre"; "free_depth"; "F_depth"; "Wcan"; "V_DEPTH"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone"; "rng_below"; "zoneF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "coveredb"; "KEEPD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG.FD.SITE"; "site_factsF"; "@stdpp.bitvector.definitions"; "bv"; "bv_signed"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "HDF"; "HDFE"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_depot"; "AA"; "aa_geom"; "aa_sec"; "ageom"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "opp"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF"; "KD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "dchkbG_sound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "JLD"; "DFP"; "JD"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface SegQ_defs Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ik.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dchkbG (nW : nat) (rdok : sobj -> bool) (sz : Z) (ED TD : axst) (sD : wsub) (RD : list sobj) : bool := ltac2:(tb__ "0|a|
SaS52ScS16S16A2M0S27VED;A1A2SaS52G0S27VTD;A1A2SaS46S31S1dS26VED;A1M1A1M2A2SaS29S15S1cG2A1S1aG1A1M3A3SaS29S15S1cS1dS26S34VsD;S32Vsz;A1M4S33Vsz;A1M5VED;VRD;A5A1A1A1G3A3SaS21S2cVsD;PaM6A2S18S2bS1bG6A1M7S19N880A1A3A2SaS21S2cVsD;PfM8A2S18S2bS1bG8A1S19Z880A1A3A2SaS21S2cVsD;PcA2S18S2bG7S19N840A1A3A2SaS29S17Vrdok;VRD;A3SaS29S17S40S31A1VRD;A3SaS29S15S15S2aS15S1fR1A1G3A3Lf;SbS15S3aS3dVnW;A1A1S3cS3bA1A3A3SaS52S17S42S26G4A1S26G5A1A2A2SaS52G0S27G5A1A2S44S1aS26VTD;A1M9A1VRD;S20G9A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma dchkbG_sound : ltac2:(tb__ "0|d|
S12S17S7F_;S47S28S28S30S8S17A1M0S0S7S6aR7R6R5R4R3R2R1A7S6A3S1S0S8ScS16S16A2M1A1M2S27R5A1S9G1A1M3A3S1S0G2S27R4A1G3A3S1S0S7S46S31S1dS26R5A1M4A1M5A2S6A3S1S0S7S29S15S1cG5A1S1aG4A1M6A3S6A3S1S0S7S29S15S1cS1dS26S34R3S32R6A1M7S33R6A1M8R5R2A5A1A1A1G6A3S6A3S1S0S16S2cR3PaM9A2S18S2bS1bG9A1MaS19N880A1A3A3S1S0S16S2cR3PfMbA2S18S2bS1bGbA1S19Z880A1A3A3S1S0S16S2cR3PcA2S18S2bGaS19N840A1A3A3S1S0S7S29S17R7R2A3S6A3S1S0S7S29S17S40S31A1R2A3S6A3S1S0S7S29S15S15S2aS15S1fR1A1S1aS26R6A1A1A3Lf;SbS15S3aS3dR8A1A1S3cS3bA1A3A3S6A3S1S0G0S42S26G7A1S26G8A1A2S9S17A1A3S1S0G2S27G8A1G3A3S0S7S44S1aS26R4A1McA1R2S20GcA1A3S6A3A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FRD;FsD;FTD;FED;Fsz;Frdok;FnW;").
Proof.
  intros nW rdok sz ED TD sD RD H. unfold dchkbG in H.
  repeat (apply andb_prop in H as [?X H]).
  repeat match goal with X : isnil _ = true |- _ => apply isnil_sound in X | X : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in X end.
  apply isnil_sound in X10, X11 || idtac.
  repeat split; assumption.
Qed.

Section FD.
Variable nW : nat. Variable rdok : sobj -> bool. Variable sz : Z.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S47S73VCST;R1A2S5S6fR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis Hsz : 1 <= sz <= SZMAX.

Variables (ED TD : axst) (sD : wsub) (RD : list sobj).
Hypothesis HER : ltac2:(tb__ "0|1|
S0S13S8S17A1M0A1S38VED;S32Vsz;A1VsD;A3SeG0VRD;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S7S37VED;S32Vsz;A1VsD;VRD;SfS28S33Vsz;A1S9S28A1A3A5S6A3").
Hypothesis HTD : ltac2:(tb__ "0|0|
S0S28VTD;S70S34VsD;S32Vsz;A1S33Vsz;A1VED;VRD;A5S1aS26VED;A1A1A2A3").
Hypothesis DCHK : ltac2:(tb__ "0|0|
S0S7S6aVnW;Vrdok;Vsz;VED;VTD;VsD;VRD;A7S6A3").
Let PARTS := dchkbG_sound nW rdok sz ED TD sD RD DCHK.
Let XXE : ax_X ED = [] := proj1 PARTS.
Let XTD : ax_X TD = [] := proj1 (proj2 PARTS).
Let NXE : Pos.leb GW (ss_next (ax_S ED)) = true := proj1 (proj2 (proj2 PARTS)).
Let FBX : forallb (sprop_below (ss_next (ax_S ED))) (ss_facts (ax_S ED)) = true := proj1 (proj2 (proj2 (proj2 PARTS))).
Let FBT : forallb (sprop_below (ss_next (ax_S (import_postA sD (PreD sz) (PostD sz) ED RD)))) (ss_facts (ax_S ED)) = true := proj1 (proj2 (proj2 (proj2 (proj2 PARTS)))).
Let WG10 : wsub_get sD 10 = SAlu ALU_ADD (SVar 10) (SLit (-2176)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))).
Let WG15 : wsub_get sD 15 = SAlu ALU_ADD (SVar 15) (SLit 2176) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))).
Let WG12 : wsub_get sD 12 = SAlu ALU_ADD (SVar 10) (SLit (-2112)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))).
Let RDOK : forallb rdok RD = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))).
Let RDWF : forallb (rng_below GW) RD = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))).
Let FCH : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S ED))) (chain_pre W ++ F_depth free_depth) = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))).
Let NEWO : new_objs (ax_S (PreD sz)) (ax_S (PostD sz)) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))).
Let XPost : ax_X (PostD sz) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).
Let RDcov : coveredb (ss_facts (ax_S TD)) RD (ss_objs (ax_S TD)) = true := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).

Section SITE.
Variables (A : AA) (Kc : KcA) (rho1 : valuation).
Hypothesis HKc : Kc_ok Kc.

Hypothesis HZ : ltac2:(tb__ "0|1|
S1eS22S31Vrho1;R1A3S3fVA;R2A2S5dS4eQ40S24R3S3eA2A2S5eS3bA1A2S67S15S23R4A1S3aVW;A1A3S17S0S7Vrdok;R1A1S6A3S0S7S40S31R2A2S6A3S47S1S5dS11S47S47S25R9R4A2M0A3R1A2S5fR1S14S47S47G0A3A2A2S41VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;").

Definition site_factsF (rhoE : valuation) : Prop := ltac2:(tb__ "0|1|
S1S22S31Vrho1;VrhoE;A3S1S3fVA;VrhoE;A2S1S1S5dS5eS60Z2Z28A2A1S4eQ40S24VrhoE;S3eA2A2M0A2S5dG0S5eS3bA1A2A2S67S15S23VrhoE;A1S3aVW;A1A3A2A2A2").

Lemma fd_facts : ltac2:(tb__ "0|0|
S1eS8S4dQ40A1A1S50S61Vsegs;S53VnW;Vst;S6VA;VKc;Vrho1;A6VED;R3R2R1A6S4cR4A1F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Htop).
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (FIN : forall f, In f (chain_pre W ++ F_depth free_depth) -> holds rhoE f).
  { intros f Hf. pose proof (proj1 (forallb_forall _ _) FCH f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  split; [exact Hag|]. split; [exact Htop|]. split.
  - assert (D1 : holds rhoE (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoE (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia.
  - apply Forall_forall. intros f Hf. apply FIN. apply in_or_app. left. exact Hf.
Qed.

Lemma fd_R4 : ltac2:(tb__ "0|2|
S1eS4cR1A1S58S1eS8S4dQ40M0A1M1A1S48G1S72R5R4R3R2A4S0S5bS59R6A1S59VA;A1A3S0S8S5cA1S5aR7A1S5aVA;A1A3S2fRaVRD;R4A3S5S6dS57R9A1S4fG0R5A2A2A1F_;F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;FrhoE;").
Proof.
  intros rhoE (Hag & Htop & Hdep & Hch) Ax rx tpx mdx a HX EG ES (o & Ho & Hoa).
  apply (zoneF_not_DFP A Ax rx tpx mdx (bv_unsigned a) HX EG ES).
  exact (HZ rhoE Hag Htop (proj2 Hdep) Hch o (proj1 (forallb_forall _ _) RDOK o Ho) (proj1 (forallb_forall _ _) RDWF o Ho) (bv_unsigned a) Hoa).
Qed.

Lemma fd_entry : ltac2:(tb__ "0|1|
S1eS8S4dQ40A1A1S8S49A1M0S4aS48S4cR5A1S62Vsegs;R6R5VED;SdG0S68R4S69R3R2A2A4A5S53VnW;Vst;S6VA;VKc;Vrho1;R7R6R5R3AaS6eS66S65VA;VKc;R8A3S57VA;A1S2eS2dR8VRD;S4bR4R7R5A3A3VsD;A2R7R6R4A7F_;F_;F_;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md SF Hsm0 [Hag0 HJ0].
  pose proof SF as (_ & Htop & Hdep & _). unfold top_high in Htop. unfold free_depth in Hdep.
  pose proof HJ0 as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2176 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2176)))) = bv_unsigned (rw rhoE 10%positive) - 2176).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2176))) with (2 ^ 64 - 2176) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE HB HKm0 HKf0 tp tr0 md HA HK). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite WG10, WG15, WG12, !eval_absorb, Em2176, Em2112.
    rewrite signed_add_lit by (cbn [eval]; unfold V_DEPTH in Hdep; lia). cbn [eval]. unfold V_DEPTH in Htop, Hdep. lia.
  - destruct (AInvA_X A rhoE tp md HA) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (fd_R4 rhoE SF A rhoE tp md _ HX0 eq_refl eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma fd_exit_ok : ltac2:(tb__ "0|2|
S1eS8S4dQ40A1A1M0S8S49A1M1S4aS48S1eG0G1S4aS48S4cRaA1S6cS66S65VA;VKc;RbA3S57VA;A1A3S35S2eS2dRcVRD;S4bR8RbR9A3A3VsD;A2S1eR2R1RcR8R7R6R4A6S39ReS4bRaRdRbA3VRD;VsD;S32Vsz;A1S33Vsz;A1VED;R9A8F_;TrhoC;TJL;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' ms' md' SF JL rhoC HJL. subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (fd_R4 rhoE SF _ rhoE tpL md' a HXK eq_refl eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite NEWO in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite XPost in Hr. destruct Hr.
  - intros r a j Hr. rewrite XXE in Hr. destruct Hr.
Qed.

Lemma fd_exit_core : ltac2:(tb__ "0|4|
S1eS8S4dQ40A1A1M0S8S49A1M1S4aS48S1eG0G1S4aS48S4cRaA1S6cS66S65VA;VKc;RbA3S57VA;A1A3S35S2eS2dRcVRD;S4bR8RbR9A3A3VsD;A2S1eS62Vsegs;RdRcVED;SdG1S68RbS69RaR9A2A4A5S53VnW;Vst;S6VA;VKc;Vrho1;ReRdRcRaAaR4R3ReRaR9R8R6A6S1eS50S43R12S4bReR11RfA3VRD;VsD;S26S32Vsz;A1M2A1S26VED;A1S26S33Vsz;A1M3A1R2RdA9S61Vsegs;S36R8R7R12ReRdA5S34VsD;G2G3VED;VRD;A5R3RdR2A6S4S58S58S4S1eS1eS4S1eS1eS1S56VA;R3A2S1S74S45VCST;VXGL;VA;A3Vrho1;R2A3S61Vsegs;S53VnW;Vst;S10R3VKc;R2A6VTD;R1R11R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;TrhoC;TJL;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' ms' md' SF JL rhoC Hsm0 [Hag0 HJ0] HJL rho' w' HLK [Hsm' HJ'].
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0' & HU0 & HL0 & HK0 & Htp0 & _ & Htop0). unfold top_high in Htop0.
  subst JL.
  destruct (entails_frA_sound segs ED (PreD sz) sD RD rhoE tp tr0 ms0 md HER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S ED))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S ED))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros f Hf.
    exact (proj1 (holds_agree_vals _ rhoE rho' f Hag' (proj1 (forallb_forall _ _) FBX f Hf)) (proj1 (Forall_forall _ _) Hfacts4 f Hf)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE RD (vms md tp ms0)) sD) tp rhoL tpL) TD rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite HTD. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact FBT | intros _; exact HF4]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.

  assert (RNG : forall o, In o RD -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S ED))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpKf (with_depot A G2)).
  set (rho5 := rho_absorb rho' RD (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho1) (rl rho1) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' RD a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' RD a <-> in_ranges rhoE RD a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE RD a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (fd_R4 rhoE SF A' rhoE tpL md2 a HX2 eq_refl eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' RD a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE RD a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' RD a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall a, SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP G2 a).
  { intros a HB'. apply (zoneF_not_DFP A A' rhoE tpL md2 a HX2 eq_refl eq_refl). unfold zoneF. cbn zeta. do 5 right. left. exact HB'. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE RD (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' RD (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' RD (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md HA0') as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpKf with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJF5 : JF nW st false A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold rho''. cbn [rw]. rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite (Hagl l). exact (proj2 Hag' l).
      + intros a. reflexivity.
    - split; [exact HA5|]. split; [exact (stopJ_le _ _)|].
      split; [rewrite (RW5 12%positive), (RW5 13%positive) by (unfold GW; lia); exact HL0|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact I|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JF nW st false A' Kc rho'') TD rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT40)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact XTD | | exact HT40 | exact HJF5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT RDcov Ho Ha). }
  exists A', rho'', rho5. split; [|split; [|exact HT5]].
  - unfold depot_onlyKf, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpKf with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [symmetry; exact (Hagm a)|].
      exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); exact Hdef|]. exact (BAND (bv_unsigned a) HBa).
Qed.

Theorem depot_call_HDFG : ltac2:(tb__ "0|1|
S50OF_;S51S64Vsegs;R2S63VKc;A1M0A3S71Vsegs;R3G0A3S54VnW;Vst;S45VCST;VXGL;VA;A3R4VA;VKc;Vrho1;VED;VTD;R3AaF_;F_;FQ;Fok;").
Proof.
  intros ok Q Hokl Hokpl rhoE tp Hcont k HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (fd_facts rhoE tp _ Hw) as SF.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB. pose proof (proj1 HA) as HG.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t0 tr0 md1, KD A Kc rhoE G r t0 tr0 md1 -> alloc_top (m_vmmaps md1) = topG (aa_geom A)).
  { intros G r t0 tr0 md1 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t0 tr0 md1 HKG). }
  apply (call_soundPA segs ok (JF nW st true A Kc rho1) (JD segsA (KD A Kc rhoE) (aa_depot A)) ED (PreD sz) sD RD
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp HER).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact Hchk.
  - intros rhoP tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_D_sound2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE HKc HB HKm0 HKf0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz Hsz rhoP tp1 (aa_depot A) (dN_entry A rhoE HB tp md HA) (hcD_entry A rhoE HB tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t0 tr0 ms0 md1 msv' HKG HMI Hh Hp Hs. exact (Hokl r t0 tr0 ms0 md1 msv' (KD_Kc A Kc rhoE G r t0 tr0 md1 HKG) HMI Hh Hp Hs).
    + intros G r t0 tr0 ms0 md1 x8 HKG Hp Hok. exact (Hokpl r t0 tr0 ms0 md1 x8 (KD_Kc A Kc rhoE G r t0 tr0 md1 HKG) Hp Hok).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (fd_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (fd_exit_ok rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF HJL)|].
    intros rho' HLK n' Hg' w' Hw'.
    destruct (fd_exit_core rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
    exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
  - exact HgQ.
  - exact Hw.
Qed.

Theorem depot_call_HDFEG : ltac2:(tb__ "0|0|
S50OF_;S55VnW;Vst;S45VCST;VXGL;VA;A3VA;VKc;Vrho1;VED;VTD;R1A9FQ;").
Proof.
  intros Q rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (fd_facts rhoE tp _ Hw) as SF.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB. pose proof (proj1 HA) as HG.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t0 tr0 md1, KD A Kc rhoE G r t0 tr0 md1 -> alloc_top (m_vmmaps md1) = topG (aa_geom A)).
  { intros G r t0 tr0 md1 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t0 tr0 md1 HKG). }
  apply (call_completePA segs (JF nW st true A Kc rho1) (JD segsA (KD A Kc rhoE) (aa_depot A)) ED (PreD sz) sD RD
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp HER).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact Hchk.
  - intros rhoP tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_D_complete2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE HKc HB HKm0 HKf0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz Hsz rhoP tp1 (aa_depot A) (dN_entry A rhoE HB tp md HA) (hcD_entry A rhoE HB tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (fd_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (fd_exit_ok rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF HJL)|].
    intros rho' HLK w' Hw'.
    destruct (fd_exit_core rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
    exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
  - exact Hw.
Qed.
End SITE.
End FD.
End F0A_depotG.

(* [comment removed for export] *)
Module F0A_dL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "q_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "RD_L0Be_1"; "RD_L0Be_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.
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
Module F0A_dL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A"; "ED_L0A_1"; "ED_L0A_2"; "q_L0A"; "TD_L0A_1"; "TD_L0A_2"; "RD_L0A_1"; "RD_L0A_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A.
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

(* [comment removed for export] *)
Module F0A_dL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf"; "ED_L0Bf_1"; "ED_L0Bf_2"; "q_L0Bf"; "TD_L0Bf_1"; "TD_L0Bf_2"; "RD_L0Bf_1"; "RD_L0Bf_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.
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

