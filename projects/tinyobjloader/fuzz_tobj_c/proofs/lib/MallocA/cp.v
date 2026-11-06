(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6 ah.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_lib F0A_blind b2.

(* [comment removed for export] *)
Module F0A_dL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be"; "q_L2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "RD_L2Be_1"; "RD_L2Be_2"; "RD_L2Be_3"; "RD_L2Be_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L2Be_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_L2Be_1, TD_of, RD_L2Be_1; reflexivity. Qed.
Theorem hdf_L2Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_1 TD_L2Be_1 (sD_of ED_L2Be_1 1) RD_L2Be_1 HeD_L2Be_1 HchkD_L2Be_1 HTD_L2Be_1 DCHK_L2Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_1 TD_L2Be_1 (sD_of ED_L2Be_1 1) RD_L2Be_1 HeD_L2Be_1 HchkD_L2Be_1 HTD_L2Be_1 DCHK_L2Be_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Be_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_L2Be_2, TD_of, RD_L2Be_2; reflexivity. Qed.
Theorem hdf_L2Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_2 TD_L2Be_2 (sD_of ED_L2Be_2 2) RD_L2Be_2 HeD_L2Be_2 HchkD_L2Be_2 HTD_L2Be_2 DCHK_L2Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_2 TD_L2Be_2 (sD_of ED_L2Be_2 2) RD_L2Be_2 HeD_L2Be_2 HchkD_L2Be_2 HTD_L2Be_2 DCHK_L2Be_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Be_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_L2Be_3, TD_of, RD_L2Be_3; reflexivity. Qed.
Theorem hdf_L2Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_3 TD_L2Be_3 (sD_of ED_L2Be_3 3) RD_L2Be_3 HeD_L2Be_3 HchkD_L2Be_3 HTD_L2Be_3 DCHK_L2Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_3 TD_L2Be_3 (sD_of ED_L2Be_3 3) RD_L2Be_3 HeD_L2Be_3 HchkD_L2Be_3 HTD_L2Be_3 DCHK_L2Be_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Be_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Be_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_L2Be_4, TD_of, RD_L2Be_4; reflexivity. Qed.
Theorem hdf_L2Be_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Be 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_4 TD_L2Be_4 (sD_of ED_L2Be_4 4) RD_L2Be_4 HeD_L2Be_4 HchkD_L2Be_4 HTD_L2Be_4 DCHK_L2Be_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Be_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Be 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Be_4 TD_L2Be_4 (sD_of ED_L2Be_4 4) RD_L2Be_4 HeD_L2Be_4 HchkD_L2Be_4 HTD_L2Be_4 DCHK_L2Be_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL2Be.

(* [comment removed for export] *)
Module F0A_dL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf"; "q_L2Bf"; "ED_L2Bf_1"; "ED_L2Bf_2"; "ED_L2Bf_3"; "ED_L2Bf_4"; "TD_L2Bf_1"; "TD_L2Bf_2"; "TD_L2Bf_3"; "TD_L2Bf_4"; "RD_L2Bf_1"; "RD_L2Bf_2"; "RD_L2Bf_3"; "RD_L2Bf_4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_L2Bf_1 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z1M0SaSeS25SaG0A2S12A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_1 : ltac2:(tb__ "0|1|
S6S35SeS33S36S25SaZ1M0A2S3bG0A1S3aG0A1SaS12A5S1bS34SaA1A1A2A3").
Proof. unfold TD_L2Bf_1, TD_of, RD_L2Bf_1; reflexivity. Qed.
Theorem hdf_L2Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SaSeR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_1 TD_L2Bf_1 (sD_of ED_L2Bf_1 1) RD_L2Bf_1 HeD_L2Bf_1 HchkD_L2Bf_1 HTD_L2Bf_1 DCHK_L2Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SaSeR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_1 TD_L2Bf_1 (sD_of ED_L2Bf_1 1) RD_L2Bf_1 HeD_L2Bf_1 HchkD_L2Bf_1 HTD_L2Bf_1 DCHK_L2Bf_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Bf_2 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z2M0SbSfS25SbG0A2S13A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_2 : ltac2:(tb__ "0|1|
S6S35SfS33S36S25SbZ2M0A2S3bG0A1S3aG0A1SbS13A5S1bS34SbA1A1A2A3").
Proof. unfold TD_L2Bf_2, TD_of, RD_L2Bf_2; reflexivity. Qed.
Theorem hdf_L2Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SbSfR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_2 TD_L2Bf_2 (sD_of ED_L2Bf_2 2) RD_L2Bf_2 HeD_L2Bf_2 HchkD_L2Bf_2 HTD_L2Bf_2 DCHK_L2Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SbSfR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_2 TD_L2Bf_2 (sD_of ED_L2Bf_2 2) RD_L2Bf_2 HeD_L2Bf_2 HchkD_L2Bf_2 HTD_L2Bf_2 DCHK_L2Bf_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Bf_3 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z3M0ScS10S25ScG0A2S14A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_3 : ltac2:(tb__ "0|1|
S6S35S10S33S36S25ScZ3M0A2S3bG0A1S3aG0A1ScS14A5S1bS34ScA1A1A2A3").
Proof. unfold TD_L2Bf_3, TD_of, RD_L2Bf_3; reflexivity. Qed.
Theorem hdf_L2Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6ScS10R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_3 TD_L2Bf_3 (sD_of ED_L2Bf_3 3) RD_L2Bf_3 HeD_L2Bf_3 HchkD_L2Bf_3 HTD_L2Bf_3 DCHK_L2Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_3 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6ScS10R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 3 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_3 TD_L2Bf_3 (sD_of ED_L2Bf_3 3) RD_L2Bf_3 HeD_L2Bf_3 HchkD_L2Bf_3 HTD_L2Bf_3 DCHK_L2Bf_3
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_L2Bf_4 : ltac2:(tb__ "0|1|
S6S4S21U2S9Z4M0SdS11S25SdG0A2S15A7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_L2Bf_4 : ltac2:(tb__ "0|1|
S6S35S11S33S36S25SdZ4M0A2S3bG0A1S3aG0A1SdS15A5S1bS34SdA1A1A2A3").
Proof. unfold TD_L2Bf_4, TD_of, RD_L2Bf_4; reflexivity. Qed.
Theorem hdf_L2Bf_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S18S1dS8R2S1cR11A1A3S37S8R3S1cR12A1A3S38U2S28S1eR19R18R14A3R4R14R13S24R14R12RfReRdRcA6SdS11R3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 2 q_L2Bf 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_4 TD_L2Bf_4 (sD_of ED_L2Bf_4 4) RD_L2Bf_4 HeD_L2Bf_4 HchkD_L2Bf_4 HTD_L2Bf_4 DCHK_L2Bf_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_L2Bf_4 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S2cR2A1S2eR2A1S0S2dR5R1A2S7S2fR2A1A1F_;Fa;S2aS26S1aS1S31Q40M2A1A1S16S0S0S0S22S27R8A1S29S8RaR8R7R6A5S30G0S2S0S0R6R5A4S2bRbA1A3S1fR7R6A2S6S0S32G2S19RbPcA2A2R8A3S20ReRcR9R8R7R6A6S23S9RfA2S17OF_;S39U2S28S1eR16R15R11A3R11R10S24R11RfRcRbRaR9A6SdS11R1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 2 q_L2Bf 4 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_L2Bf_4 TD_L2Bf_4 (sD_of ED_L2Bf_4 4) RD_L2Bf_4 HeD_L2Bf_4 HchkD_L2Bf_4 HTD_L2Bf_4 DCHK_L2Bf_4
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_dL2Bf.

(* [comment removed for export] *)
Module F0A_asm.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "prod"; "true"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "j_min"; "j_qb"; "j_qf"; "qcond"; "rhoF_of"; "j_st"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "AA"; "aa_internal_inited"; "aa_live"; "ag_thread"; "qbatch"; "topG"; "aa_q_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "AE_A"; "J_free_preT"; "KcA"; "Pre_freeI"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm"; "entry_pureF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma junkF_ok_min : ltac2:(tb__ "0|a|
S1bScS4S16Q40A1A1S17S18SaR4R3R2R1A5S3SeSeS1S2S0SfR1A1M0S29A3S1S1S26Z0M1G0A2S27G0S28Z2Z40A2M2A2A2S1S1S26G1S14R1A1M3A2S27G3G2A2A2S1S1S26G1S11R1A1M4A2S27G4G2A2A2S1S1S26G1S10R1A1M5A2S27G5G2A2A2S1S22S24SaSdR5A1A2M6S23S25S19Z48A2U8M7G0A3A2S1S22G6S23S25S1eS1aR6A1A1Zae0A2G7G3A3A2S2S4S1fA1S21R6A1S9S1fA1A3S1S22S24SaSdR6A1A2M8S23S25S1eS1aR7A1A1M9Z58A2G7S11R2A1A3A2S22G8S23S25G9Z60A2G7S10R2A1A3A2A2F_;A2A2A2A2A2A2A2Ljv;A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. destruct (junkF_ok A rho tp md HA) as (jv & J1 & J2 & J3 & J4 & C1 & C2 & C3).
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _).
  destruct HQR as (_ & _ & _ & _ & _ & _ & QMIN & _).
  exists (mkJF kQuarantineMin (j_st jv) (j_qf jv) (j_qb jv)). cbn [j_min j_st j_qf j_qb].
  split; [reflexivity|]. split; [unfold kQuarantineMin; lia|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|].
  split; [|split; [exact C2 | exact C3]].
  eapply cell_ok_agree; [|exact QMIN]. cbn [c_addr c_w]. intros k Hk. symmetry. apply (MV_img A rho tp md HA). unfold QG. lia.
Qed.

Theorem instF_facts_ok3 : ltac2:(tb__ "0|1|
S5S4S2fA1S30S2eS1bScS4S16Q40M0A1A1S17S0S0S18SaR6R5R4R3A5S35S7S0S0A2S6S0S0R3R2A4S1dR7A1A3S2aRcR4R3A3S2S5S1cR9A1S8A3S12RbRaA2S2S0S15G0SbRaPcA2A2R7A3S2S0S15G0SbRbPdA2A2R7A3S3S0S0S3SeSeS1S2bRfReRbRaR2R1A6S1S2S0SfR1A1S29A3S2cR13R12R11R10S13RfReRbRaR2R1A6RbRaS2dRaA1S20S1aRfA1A1A9A2A2Ljv;A2Lt;A2F_;F_;F_;F_;F_;F_;F_;Fn;Fp;Fmd;Ftp;Frho;FA;Fq;Fst;FW;Fkhi;").
Proof.
  intros khi W st q A rho tp md p n HA HL HK Hii QC Hp Hn. pose proof (cls_hyp_blk khi p n HK) as HHI.
  destruct (blkF_mem A rho tp md p n HA HL HHI) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp md HA) as (jv & JM & Hjv).
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|]. split; [exact JM|].
  exact (instF_here A rho tp md p n HA HL HHI Hii Hp Hn t (conj T1 (conj T2 (conj T3 T4))) jv Hjv khi W st q HK QC).
Qed.

Definition entry_pureF (khi : bool) (W : list ulink) (st : ustop) (q : qvar) (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S15Q40M0SbVrho;PcA2A2S0S15G0SbVrho;PdA2A2S0S1S35S7S0S0A2S6S0S0R2R1A4S1dVA;A1A3S1S3S4S16G0A1A1M1G1S3S17S17S18SaVA;Vrho;R2R1A5Lmd0;A2Ltp0;A2S3S0S0S3SeSeS1S2bVA;Vrho;R4R3R2R1A6S1S2S0SfR1A1S29A3S2cVkhi;VW;Vst;Vq;S13VA;Vrho;R4R3R2R1A6R4R3S2dR3A1S20S1aVA;A1A1A9A2A2Ljv;A2Lt;A2A2A2Tn;Tp;").
Lemma entry_pure : ltac2:(tb__ "0|1|
S5S4S2fA1S30S2eS1bS33ScS4S16Q40M0A1A1S36S2aR9S15G0SbR3PcA2A2S15G0SbR3PdA2A2A3S2S5S1cR6A1S8A3S12R8R7A2S37SaS32S18SaA1RbRaR8R7A5S34S31RbRaA3R6R5R4A6S38RdRcRbRaR9R7A6F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fq;Fst;FW;Fkhi;").
Proof.
  intros khi W st q A Kc rho tp w HHI Hii QC [_ HJ]. destruct HJ as (HA & _ & HL & _).
  split; [exact HL|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  exact (instF_facts_ok3 khi W st q A rho tp _ _ _ HA HL HHI Hii QC eq_refl eq_refl).
Qed.
End F0A_asm.

(* [comment removed for export] *)
Module F0A_depotG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "ex"; "not"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "andb"; "app"; "prod"; "pair"; "Some"; "cons"; "false"; "fst"; "nat"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SAlu"; "SLit"; "ss_facts"; "SVar"; "sprop_below"; "ss_next"; "valuation"; "sprop_eqb"; "ss_objs"; "sv_eqb"; "agree_below"; "holds"; "rw"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "chain_pre"; "free_depth"; "F_depth"; "Wcan"; "V_DEPTH"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "rng_below"; "zoneF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "coveredb"; "KEEPD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG.FD.SITE"; "site_factsF"; "@stdpp.bitvector.definitions"; "bv"; "bv_signed"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "HDF"; "HDFE"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_depot"; "AA"; "aa_geom"; "aa_sec"; "ageom"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "opp"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKF"; "KD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG"; "dchkbG"; "dchkbG_sound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "JLD"; "DFP"; "JD"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot.
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
Module F0A_hbN_step.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "rm"; "rw"; "rl"; "ss_objs"; "eval"; "holds"; "odefault"; "sprop"; "DUnknown"; "DZero"; "agree_below"; "ob_dflt"; "ss_facts"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nat"; "pair"; "app"; "length"; "bool"; "option"; "true"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "dspec"; "dobj"; "keepN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "Forall2"; "combine"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step.StepW"; "ro_condW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "s_C"; "s_bs"; "s_Cd"; "s_F"; "s_M"; "s_N"; "s_T"; "s_ZDn"; "s_ZDo"; "s_k"; "s_ok"; "strans"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "in_zoneW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "carve_okq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegQS_lib F0A_zones F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section StepW.
Variables (Zn TZ : Z -> Prop).
Variable J : jpredA.
Hypothesis HST : ltac2:(tb__ "0|0|
S36S5S49VJ;A3").
Let JWn : jpredA := ltac2:(tb__ "0|0|
S44S5VZn;VTZ;VJ;A4").

Definition ro_condW (rho : valuation) (d : dspec) : Prop := ltac2:(tb__ "0|d|
S19S19S19S19S9S6A2M0S6A2M1S18S19S19S6S1aA2M2S9A2M3A1M4A2M5S6A2OLd;Vd;G5S6G5OLp;R2G1G4G1OLp0;R2G0S6G0OLp1;R2S9S6S0S1S2eQ40M6A1M7SfVrho;R2A2M8S2fG6R7A2A3S0S0S22Z0M9R7A2S23R7S26Z2Z3eA2MaA2A2S0S22S25GaA1R1A2S0S22R1R3A2S0S22R3GaA2S0S22G9S21R7R1A2A2S0S56R1R3R5A3S0S6S0S22S21R8R2A2R1A2S23R1S21R8R4A2A2A2MbS2S6S6S2S1aS1aS2S9S9S2S6S6S0S40G3S1bG2S9S1bS6S1aR4R3A4R2A4RbA3S0S0S22S21RdR4A2McR6A2S23R6S21GcS24R3A1A2A2A2S0S1G7G8S2fG6R1A2A3S2cS2aS5SbVrho;A1A2S2dGcR3R1A3A2A2A2A2Lval;A2Le;A2Lk;A2Loff;A2F_;Fz;S6GbVTZ;R2A1F_;Fz;A2A2A2A2A2A2A2A2Llo;Lb;X19x1Lhi;Lp1;X19x1Lcs;Lp0;X19x1La;Lp;X19x1").

Lemma ro_dissolveW : ltac2:(tb__ "0|3|
S39S18S8A1M0S18S27A1SaS18S2eQ40A1M1A1S18S3cA1M2S3aS3bS1G0SeS37R8A1A1S1cS8R7S32S27S8S28R6A4A3A3S35S5VJWn;R9R6R5S1bG2S33R4S34R3R2A2A4A6S31S27S45R7A1R8A3S3dR8S32S27S8S28R9A4S3fR4R7R5A3A3SaS0S35S5VJWn;S38RcS43S37RcA1RbA2A2R1R8S1bG2S33R7S34R6R5A2A4A6S0S7S1G1ScR2R1A2ScRaR1A2A3Fi;S0S7S1S18S2eQ8A1A1SdR2R1A2SdRaR1A2A3Fl;S1S2bS2aS5SbR1A1A2S2aS5SbR9A1A2A3A2A2A2Trho3;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fds;FBASE;FC;").
Proof.
  intros C BASE ds rho tp tr ms md HOBJ HS HD rho3.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)).
  assert (INZ : forall z, dzone ds z -> v3 z = v z).
  { intros z Hz. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. destruct d as [[[[b lo] hi] cs] a].
    destruct X as (Eb & A1' & L1 & L2 & L3 & L4 & CI & HC & _).
    destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) BASE (map dobj ds) b lo hi cs Hsm HOBJ (in_map dobj ds _ Hd) ltac:(lia) ltac:(lia) ltac:(lia) CI
                ltac:(rewrite Eb, u64_lit by lia; lia) ltac:(rewrite Eb, u64_lit by lia; lia)) as [AVc PRc].
    fold rho3 in AVc, PRc. rewrite Eb, u64_lit in AVc, PRc by lia.
    destruct (HC z Hz) as (off & k & e & val & Hin & Hzc & Ee & Cv).
    pose proof (av_cell (view segsA (rm rho3)) a off k e val rho (fun j Hj => AVc off k e j Hin Hj) Ee) as C3.
    exact (cell_ok_same v v3 _ Cv C3 z ltac:(cbn [c_addr c_w]; lia)). }
  assert (INRG : forall x, in_ranges rho (map dobj ds) x -> dzone ds (bv_unsigned x)).
  { intros x (o & Ho & Hz). apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. apply List.Exists_exists. exists d. split; [exact Hd|].
    destruct d as [[[[b lo] hi] cs] a]. destruct X as (Eb & A1' & L1 & L2 & L3 & _). rewrite (dobj_range rho b lo hi cs a Eb A1' L1 L2 L3) in Hz. cbn [fst snd] in Hz. exact Hz. }
  destruct (absorb_out rho (map dobj ds) (vms md tp ms) (dzone ds) INRG) as [FR FRrm]. fold rho3 in FR, FRrm.
  assert (EV : v3 = v).
  { apply functional_extensionality. intros z. destruct (dzone_dec ds z) as [Hz|Nz]; [exact (INZ z Hz) | exact (FR z Nz)]. }
  pose proof (SPA_unobj segsA JWn rho C BASE (map dobj ds) tp tr ms md HOBJ HS) as HU. cbn zeta in HU. fold rho3 in HU.
  split; [|split; [intros i; reflexivity | split; [intros l; reflexivity | exact EV]]].
  apply HU. intros HJ. apply (JW_change segsA Zn TZ J rho rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | | exact HJ].
  - intros z _. fold v3 v. rewrite EV. reflexivity.
  - intros z _ Hp. fold v3. rewrite EV. exact Hp.
  - intros a0 NT. apply FRrm. intros Hz. apply NT. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X.
    destruct d as [[[[b lo] hi] cs] a]. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & HT). exact (HT _ Hz).
Qed.

Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis Hsep : ltac2:(tb__ "0|3|
S1aS1aS40S1aR2VZU;A3M0G0S4S1S1aR4R3A3A1S3S22S21Vzb;R5A1M1Vzhi;R5A1A2S21Vzb;R4A1M2Vzlo;R4A1A2A2S22S21G2Vzhi;R4A1A2S21G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Lemma s_stepW : ltac2:(tb__ "0|8|
S55S18S27A1S18S2eQ40A1M0A1M1SaG1S18S3cA1M2S3aS3bS1S1eS54R8A1S20A3S1S18S8A1SeS37S4aR9A1M3A1A1S1cS8S29G3S53R9A1A2S32S27S8S28R8A4A3A3S1S1aS1dG0R8A2S1dS7S4bRaA1A2A3S35S5VJWn;S4aRbA1R8R7S1bG2S33R6S34R5R4A2A4A6S31S27S45R9A1RbA3S3dRaS32S27S8S28RcA4S3fR6R9R7A3A3SaS58R1S42S7G0S4bReA1RcA4A2SaS1S2bS2aS5SbR2A1A2S2aS5SbRcA1A2A3VJWn;R2RcRbR9A4S0S31S47S59R3A1S4fR11A1M4A3S0S41S8S46S57R3Vzb;Vzlo;Vzhi;VZU;A5M5S32S47S8S48G4A4S51R11A1A5S0S41S8S46G5SeS37S4cR11A1A1M6A1S52R11A1A5S31S12S10R3A1S17G6A1A3S31S12S10R4A1S4dR12A1A3F_;A2A2A2F_;F_;S2SaSaS0S35S5VJWn;S50R11A1R1RdS1bG2S33RcS34RbRaA2A4A6S0S7S9S40S19S7S9A2S1bS7S9R2R1A4S4eR13A1A3S1G0ScR4R3A2SfR6R2A2A3F_;Fe;Fv;S0S1G0S1fS2eQ8A1A1F_;SbR1A1SbR4A1M7A3S0S15S49R3R1A3S1S2bS2aS5G7A2S2aS5SbReA1A2A3A2A2A2A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fvals;FdsD;Ft;").
Proof.
  intros t dsD vals rho tp tr ms md HOK HOBJ HLEN HS HDC rho3 rho4 HCONT.
  pose proof (JW_stable segsA NPRE Zn TZ J HST) as HSTW. fold JWn in HSTW.
  unfold s_ok in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb (fun d => forallb _ _) _ = true |- _ => rename H into OKZX end.
  match goal with H : zcheck _ = true |- _ => rename H into OKZC end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf _ = true |- _ => rename H into OKSWF end.
  match goal with H : forallb _ (s_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (s_C t) = []) by (destruct (ax_X (s_C t)); [reflexivity | discriminate HOK]).
  destruct (ro_dissolveW (s_C t) (keepN (s_C t) (s_k t)) dsD rho tp tr ms md HOBJ HS HDC) as (H1 & RW3 & RL3 & EV).
  fold rho3 in H1, RW3, RL3, EV. change (SPA segsA JWn (s_Cd t) rho3 tp (tr, mkCfg ms md)) in H1.
  assert (MF : map fst (combine (s_bs t) vals) = s_bs t).
  { clear - HLEN. revert vals HLEN. induction (s_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA JWn (s_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (s_Cd t) rho3 tp _ _ HX HSTW); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply Pos.leb_le. exact X. }
  destruct (HCONT EV (proj2 H2)) as (CC & ZN & ZO & HFN).
  pose proof (SPA_facts_hold segsA _ rho4 (s_Cd t) tp _ H2) as HFa.
  assert (H3 : SPA segsA JWn (s_Ca t) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA JWn rho4 (s_Cd t) tp _ (s_N t) (ss_next (ax_S (s_Cd t))) H2) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX | exact CC].
    - exact (zonesW_cross rho4 zb zlo zhi ZU Hsep _ _ _ _ ZN ZO OKZX).
    - exact (zonesW_pd rho4 zb zlo zhi ZU Hsep _ _ ZN OKZC). }
  assert (H4 : SPA segsA JWn (s_Cc t) rho4 tp (tr, mkCfg ms md)).
  { unfold s_Cc, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA JWn _ (s_T t) (s_M t) rho4 tp _ OKENT HSTW H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. split; [|split; [exact AG5 | exact EV]]. rewrite RM5. unfold rho4. apply rm_rho_sets.
Qed.
End StepW.

Section DissolveZ.
Variables (Zn TZ : Z -> Prop).
Variable J : jpredA.
Hypothesis HZT : ltac2:(tb__ "0|0|
S6VZn;R1A1VTZ;R2A1F_;Fz;").
Let JWn : jpredA := ltac2:(tb__ "0|0|
S44S5VZn;VTZ;VJ;A4").
Lemma dissolveZW : ltac2:(tb__ "0|5|
S39S18S8A1M0G0SaS18S2eQ40M1A1M2A1S18S3cA1M3S3aS3bS1G0SeS37R8A1A1S1cS8R7R6A3A3S35S5VJWn;R9R6R5S1bG3S33R4S34R3R2A2A4A6G2S3eR8R9R1A3VZn;S30G1R2A2A1F_;Fx;S31S8S8S3S1S11S16R1A1M4S13A3S1S11G4S14A3A2Lo;R9A3S3dR9RaS3fR5R8R6A3A3SaS0S35S5VJWn;S38RdS43S37RdA1RcA2A2R1R9S1bG3S33R8S34R7R6A2A4A6S0S7S1G2ScR2R1A2ScRbR1A2A3Fv;S7S1S18S2eQ8A1A1SdR2R1A2SdRbR1A2A3Fl;A2A2Trho2;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;FBASE;FC;").
Proof.
  intros C BASE R rho tp tr ms md HOBJ HS IRZ HD rho2.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (v := view segsA (rm rho)). set (v2 := view segsA (rm rho2)).
  assert (PRS : forall z, v z <> None -> v2 z <> None).
  { intros z Hd. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|unfold v2, rho2; rewrite (proj2 (absorb_io rho R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj rho _ tr (vms md tp ms) (vmd md) BASE R o Hsm HOBJ Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    pose proof (proj1 (Forall_forall _ _) HD o Ho) as Do. unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 Do (z - bv_unsigned (eval rho (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v2, rho2. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (z - bv_unsigned (eval rho (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  assert (EQF : forall z, ~ Zn z -> v2 z = v z).
  { intros z NC. apply (proj2 (absorb_io rho R (vms md tp ms)) z). intros [Hz Hin]. apply NC. pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  pose proof (SPA_unobj segsA JWn rho C BASE R tp tr ms md HOBJ HS) as HU. cbn zeta in HU. fold rho2 in HU.
  split; [|split; [intros v0; reflexivity | intros l; reflexivity]].
  apply HU. intros HJ. apply (JW_change segsA Zn TZ J rho rho2 tp tr md); [intros i; reflexivity | intros l; reflexivity | exact EQF | intros z _ Hp; exact (PRS z Hp) | | exact HJ].
  intros a0 NT. apply (proj1 (absorb_io rho R (vms md tp ms))). intros Hin. apply NT. apply HZT. exact (IRZ _ Hin).
Qed.
End DissolveZ.
End F0A_hbN_step.

