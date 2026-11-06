(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP CertMallocST.

(* [comment removed for export] *)
Module SegQ3R_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "app"; "list"; "pair"; "bool"; "true"; "option"; "Some"; "prod"; "None"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "sv"; "valuation"; "SLit"; "ss_facts"; "rm"; "eval"; "rw"; "SAlu"; "SPBranch"; "SVar"; "sprop_below"; "ss_next"; "SPAlign"; "SPNot"; "SPUle"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "True"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "aa_q_global"; "aa_q_thread"; "aa_cache_inited"; "aa_geom"; "ag_thread"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXSplit"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "ZQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "gsz"; "vTN"; "ReQ3e"; "ReQ3n"; "vTB"; "vGF"; "KEEP3"; "O_gmax"; "O_gq"; "O_mtx"; "O_tq"; "vMIN"; "O_glb"; "vGN"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "BC_EQ"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "PreR2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "F_sp"; "X4e"; "X4n"; "X1e"; "X1n"; "X2e"; "X2n"; "gn'"; "HVP"; "KEPT6e"; "KEPT6n"; "NFe"; "NFn"; "XSPLIT"; "FRM"; "MEe"; "MEn"; "REST1e"; "REST2n"; "RMEM"; "X2e'"; "X2n'"; "X5e"; "X5n"; "tlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel.Recycle"; "JRQ"; "@Stdlib.Lists.List"; "forallb"; "removelast"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "pow"; "modulo"; "le"; "mul"; "add"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "qhdr_repr"; "qlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep"; "last_addr"; "hd_addr"; "qlinks_to"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "HIGH_SHADOW_END"; "kQuarantineMax"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "A1T"; "rhoT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "JQ3"; "qbounded"; "qzone"; "QFP"; "QRD"; "batch_mem"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece"; "keeps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "entsM"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "@Stdlib.Sorting.Permutation"; "Permutation"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FRM (A0 : AA) (rho0 rho : valuation) : Prop := ltac2:(tb__ "0|7|
S1fS93S83Vrho0;Vrho;A3S1fS45Q40M0A1M1S20S8bVA0;S46G0R1A2M2A2A1S1eS8S45Q8A1M3A1M4S13Vrho;R2A2S13Vrho0;R2A2M5A3F_;Fa;S1fS2cS20S8aVA0;R1A2A1S1eG4S78S30S13Vrho;A1R2A3S78S30S13Vrho0;A1R2A3A3F_;Fz;G1S1fS70S7fG2A2S6dG2S7eA2A2S20S1eG4G5SbG3A1M6A3A1S20S1eG4S13Vrho;R3A2G6A3A1F_;F_;Fa;A2A2A2").

Definition tlinks (m : bview) (pre : list qbatch) : Prop := ltac2:(tb__ "0|1|
S4S24A1M0OLpre;Vpre;S22S24G0S7bVm;S6cS24Vpre;A2S79Vpre;A1A3Ll;Lq;X4x2").

Definition RMEM (m : bview) (G : ageom) (pre rest : list qbatch) : Prop := ltac2:(tb__ "0|0|
S1fS90S24S8cVm;A1S3S24Vpre;Vrest;A3A3S1fS69Vm;Vpre;A2S1fS77Vm;Vrest;A2S76Vm;S72S2aVG;A1Z50A2S2S24A1A3A2A2A2").

Definition HVP (rho : valuation) (all : list qbatch) : Prop := ltac2:(tb__ "0|2|
S1fS1eS45Q40M0A1M1S15Vrho;PccA2S47G0S73ScS24Vall;A2A1A2A3S1fS1eG1S15Vrho;PcdA2S47G0S7aVall;A1A2A3S1fS1eG1S15Vrho;PceA2S47G0S79Vall;A1A2A3S1fS1eG1S15Vrho;PcfA2S47G0S75Vall;A1A2A3S1eG1S15Vrho;Pd0A2S47G0S80A2A3A2A2A2A2").

Definition KEPT6n : list sobj := ltac2:(tb__ "0|0|
S3SeS0SeS82S81A3S0SeS40S11Z100A1A1S0SeS3fS84S44S38A2S3cS3bS37A4S0SeS3eS2SeA1A3A3A3A3").
Definition REST2n : list sobj := ltac2:(tb__ "0|0|
S0SeS41S36S36S36S36A4S0SeS43S18Pc9A1A1S2SeA1A3A3").
Definition X1n : axst := ltac2:(tb__ "0|0|
S2fS3aS4bS2dS3aA1S3SeS5bS63A3A2A2").
Lemma X1n_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S3aS0S31S33S0S1U0S0S1U1S0S1U2S0S1U4S0S1U5S0S1U6S0S1U3S0S1U7S2S1A1A3A3A3A3A3A3A3A3A1S2S31A1A3A2S9S2eS55A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X2n : axst := ltac2:(tb__ "0|0|
S2fS55S4bS2dS55A1S5bA2A2").
Definition F_sp : sprop := SPUle (SLit 140735332483072) (SVar 10).
Definition X2n' : axst := ltac2:(tb__ "0|0|
S4cS57S3SdS12S2dS57A1A1S0SdS51S2SdA1A3A3A2").
Definition XSPLIT : list axform := ltac2:(tb__ "0|4|
S0S31S34U0M0S11Na8A1A2S0S31S34G0S11Nb8M1A1A2S0S31S34G0S11Nc0M2A1A2S0S31S35G0G2A2S0S31S35U2M3G1A2S0S31S33S0S1G0S0S1U1S0S1G3S0S1U3S0S1U6S0S1U8S0S1U4S0S1U5S0S1U7S2S1A1A3A3A3A3A3A3A3A3A3A1S2S31A1A3A3A3A3A3A3").
Definition X4n : axst := Eval vm_compute in (match apply_axforms X2n' XSPLIT with Some X => X | None => X2n' end).
Lemma X4n_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S66S5eA2S9S2eS53A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition gn' : sv := add vGN vTN.
Definition NFn : list sprop := ltac2:(tb__ "0|0|
S0SdS1cS17S49S58S11Z0A1A3A1S0SdS1dS11S7cA1S3cA2S0SdS1bPcdZ3A2S0SdS17S4aS37S16S48S58S11ZdA1A3A3S2SdA1A3A3A3A3").
Definition X5n : axst := ltac2:(tb__ "0|0|
S4cS53S3SdS12S2dS53A1A1S5dA3A2").
Definition MEn : vmap := ltac2:(tb__ "0|1|
S0SaS2bSfA2M0S5S2bSfPccS58A4S0G0S5S2bSfPcdS3cA4S0G0S5S2bSfPceS3bA4S0G0S5S2bSfPcfS37A4S0G0S5S2bSfPd0S42A4S2G0A1A3A3A3A3A3").
Lemma X5n_ent : ltac2:(tb__ "0|0|
S1eS6S8fS68S50S61A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X2n'_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS57A1M0A1A1S3SdS12G0A1S0SdS51S2SdA1A3A3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X5n_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS53A1M0A1A1S3SdS12G0A1S5dA3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition KEPT6e : list sobj := ltac2:(tb__ "0|0|
S3SeS0SeS82S81A3S0SeS40S11Z100A1A1S0SeS3fS38S18Pc9A1S3bS37A4S0SeS3eS2SeA1A3A3A3A3").
Definition REST1e : list sobj := ltac2:(tb__ "0|0|
S0SeS41S36S36S36S36A4S2SeA1A3").
Definition X1e : axst := ltac2:(tb__ "0|0|
S2fS39S4bS2dS39A1S3SeS5aS62A3A2A2").
Lemma X1e_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S39S0S31S33S0S1U0S0S1U1S0S1U2S0S1U4S0S1U5S0S1U6S0S1U3S2S1A1A3A3A3A3A3A3A3A1S2S31A1A3A2S9S2eS54A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X2e : axst := ltac2:(tb__ "0|0|
S2fS54S4bS2dS54A1S5aA2A2").
Definition X2e' : axst := ltac2:(tb__ "0|0|
S4cS56S3SdS12S2dS56A1A1S0SdS51S2SdA1A3A3A2").
Definition X4e : axst := Eval vm_compute in (match apply_axforms X2e' XSPLIT with Some X => X | None => X2e' end).
Lemma X4e_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S65S5eA2S9S2eS52A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition NFe : list sprop := ltac2:(tb__ "0|1|
S0SdS1cS17S49S38S11Z0A1A3A1S0SdS1dS11S7cA1S18Pc9M0A1A2S0SdS1bG0Z3A2S0SdS17S4aS37S16S48S38S11ZdA1A3A3S2SdA1A3A3A3A3").
Definition X5e : axst := ltac2:(tb__ "0|0|
S4cS52S3SdS12S2dS52A1A1S5cA3A2").
Definition MEe : vmap := ltac2:(tb__ "0|1|
S0SaS2bSfA2M0S5S2bSfPccS38A4S0G0S5S2bSfPcdS18Pc9A1A4S0G0S5S2bSfPceS3bA4S0G0S5S2bSfPcfS37A4S0G0S5S2bSfPd0S42A4S2G0A1A3A3A3A3A3").
Lemma X5e_ent : ltac2:(tb__ "0|0|
S1eS6S8fS67S50S60A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X2e'_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS56A1M0A1A1S3SdS12G0A1S0SdS51S2SdA1A3A3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X5e_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS52A1M0A1A1S3SdS12G0A1S5cA3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma U_sll2' : ltac2:(tb__ "0|3|
S10SfSfS1eS2cS46Q40M0S14R3S16S48R2R1A3A2A2S6fS71S46G0S14R3R2A2A2S6eZ2M1S6fS46G0S14R3R1A2A2Z40M2A2A2A2S6eG1G2A2A2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold alu64, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 63) with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  unfold bv_wrap. reflexivity.
Qed.
Lemma U_sllk : ltac2:(tb__ "0|3|
S10SfS2cS1fS70Z0R1A2S6dR1Z40M0A2A2S1eS2cS46Q40M1S14R4S16S48R3S11R2A1A3A2A2S6fS71S46G1S14R4R3A2A2S6eZ2M2R2A2A2S6eG2G0A2A2A3F_;Fk;Fa;Frho;").
Proof. intros rho a k Hk. rewrite U_sll2'. cbn [eval]. rewrite u64_lit by lia. rewrite (Z.mod_small k 64) by lia. reflexivity. Qed.
Lemma qzone_perm : ltac2:(tb__ "0|1|
S25S4S24A1M0G0S2cS95S24S94R4A1S3S24R3R2A3A3S23S89S8dR5R4R3A3R2A2S89R5R2A2A2F_;Fz;Fg;Ft;FA;").
Proof.
  intros A t g z HP. unfold qzone. change (qall (set_q A t g)) with (t ++ g). split; intros H; apply Exists_exists in H as (b & Hb & Hz); apply Exists_exists; exists b; (split; [|exact Hz]).
  - eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb].
  - eapply Permutation_in; [exact HP | exact Hb].
Qed.

Section Recycle.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.

Definition JRQ (A0 : AA) (rho0 : valuation) (A1 : AA) (pre rest : list qbatch) : jpredA := ltac2:(tb__ "0|0|
S10S4S45Q40A1A1S4S92A1S91S1fVK;VA1;R4R3R2R1A5S1fS64S78S30S13R4A1A2S29VA1;A1Vpre;Vrest;A4S5fVA0;Vrho0;R4A3A2A2Lmd;Ltr;Ltp;Lrho;").
Lemma JRQ_stable : ltac2:(tb__ "0|1|
S25S10S25S4S24A1M0G0S4fS30S83S6aR5R4R3R2R1A5A3Frest;Fpre;FA1;Frho0;FA0;").
Proof.
  intros A0 rho0 A1 pre rest rho rho' tp tr md md' Hag Hme (HK & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A1); eauto|]. split; [rewrite Erm; exact HR|].
  destruct HF as ((F1 & F1') & F2 & F3 & F4). split; [|rewrite Erm; auto].
  split; [intros i Hi; rewrite (F1 i Hi); apply (proj1 Hag); exact Hi | intros l; rewrite (F1' l); apply (proj1 (proj2 Hag))].
Qed.
Lemma JRQ_okf : ltac2:(tb__ "0|1|
S74OF_;S25S10S25S4S24A1M0G0S25S4eS30R7VK;R1A1A3FA;S4eS30R7S6aR6R5R4R3R2A5A3F_;Frest;Fpre;FA1;Frho0;FA0;Fok;").
Proof. intros ok A0 rho0 A1 pre rest HOK rho tp tr ms md msv' (HK & _). exact (HOK A1 rho tp tr ms md msv' HK). Qed.

Lemma entry_Rn : ltac2:(tb__ "0|4|
S25S10S10S4S45Q40A1A1S74S20S1eS4S24A1M0S27R5A1S2S24A1M1A3A1S20S1eG0S26R6A1G1A3A1S1eS6S28R7A1S7A3S88R8A1S8eS3dS86R9S7aS26R9A1M2A1S79G2A1R8A4R7A3S4dS30S87S30VK;RaA3S3aR8R7R6A6S21S10S10S1fS4dS30S6aRcRbS85RcA1G1S3S24S26RcA1S27RcA1A3M3A5S50R1R9R8A6S1fS59R1G3A2S6dS7dS75G3A1A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp w HTL HGL HCI HBND [Hag Hkeep] H0. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho' ReQ3n X1n tp _ X1n_eq H0) as H. clear H0.
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (tl := aa_q_thread A) in *. set (gl := aa_q_global A) in *. set (T := ag_thread (aa_geom A)).
  destruct (kq_facts segsA K HL A rho' tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T in E151.

  destruct (rhoT_vals A (hd_addr gl) (last_addr gl) rho) as (R200 & R201 & R202 & R203 & R204 & R205 & R206 & R207 & R208 & R209 & RRM & RAG).
  assert (KV : forall v, In v KEEP3 -> rw rho' v = rw (rhoT A (hd_addr gl) (last_addr gl) rho) v) by exact Hkeep.
  assert (E200 : rw rho' 200%positive = Z_to_bv 64 (Z.of_nat (length tl))) by (rewrite KV by (cbn; tauto); exact R200).
  assert (E201 : rw rho' 201%positive = Z_to_bv 64 (hd_addr tl)) by (rewrite KV by (cbn; tauto); exact R201).
  assert (E202 : rw rho' 202%positive = Z_to_bv 64 (last_addr tl)) by (rewrite KV by (cbn; tauto); exact R202).
  assert (E203 : rw rho' 203%positive = Z_to_bv 64 (qsize tl)) by (rewrite KV by (cbn; tauto); exact R203).
  assert (E204 : rw rho' 204%positive = Z_to_bv 64 (Z.of_nat (length gl))) by (rewrite KV by (cbn; tauto); exact R204).
  assert (E205 : rw rho' 205%positive = Z_to_bv 64 (hd_addr gl)) by (rewrite KV by (cbn; tauto); exact R205).
  assert (E206 : rw rho' 206%positive = Z_to_bv 64 (last_addr gl)) by (rewrite KV by (cbn; tauto); exact R206).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 (qsize gl)) by (rewrite KV by (cbn; tauto); exact R207).
  assert (E208 : rw rho' 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite KV by (cbn; tauto); exact R208).
  clear KV R200 R201 R202 R203 R204 R205 R206 R207 R208 R209.

  pose proof (SPA_facts_hold segsA _ rho' X1n tp _ H) as HFa.
  assert (U13 : bv_unsigned (rw rho' 13%positive) = T + 80).
  { assert (X : holds rho' (SPBranch BC_EQ (SVar 13) (add vT (SLit 80)))) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
    cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  assert (FGT : holds rho' F_gt) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  assert (Hhigh : holds rho' F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  destruct (stack_win_range _ rho' _ _ Hsm ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND, HBM. fold tl gl in HBP, HND, HBM, HLT, HLG, HHT, HHG.
  assert (LEN2 : Z.of_nat (length tl) < 2 ^ 35 /\ Z.of_nat (length gl) < 2 ^ 35 /\ 0 <= qsize tl /\ 0 <= qsize gl
                 /\ 8192 * Z.of_nat (length tl) <= qsize tl /\ 8192 * Z.of_nat (length gl) <= qsize gl).
  { destruct HBND as [B1 B2]. fold tl gl in B1, B2. apply Forall_app in HBP as [HBPt HBPg]. apply Forall_app in HBM as [HBMt HBMg].
    pose proof (qsize_ge A _ _ HBPt HBMt). pose proof (qsize_ge A _ _ HBPg HBMg). unfold kQuarantineBatchSize, kQuarantineMax in *. lia. }
  destruct LEN2 as (LT & LG & ST0 & SG0 & SGEt & SGEg). destruct HBND as [BT BG]. fold tl gl in BT, BG. unfold kQuarantineMax in BG.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (cv_bounds _ _ _ _ _ (HCLS HCI c Hc)) as (B1 & B2 & B3 & _). unfold kUserMapSize in *. lia. }
  pose proof (conj HBP HND : q_pure A) as HQP.
  destruct (batch_slot A HQP HAU HG0 _ (in_or_app _ _ _ (or_intror (In_last gl qb_dflt HGL)))) as (yb & GB1 & GB2 & GB3 & GB4 & GB5 & GB6 & GB7 & _).
  change (qb_addr (last gl qb_dflt)) with (last_addr gl) in GB1, GB5, GB6, GB7. set (gb := last_addr gl) in *. unfold HIGH_SHADOW_END in GB5.
  assert (GBhi : gb + 8192 <= 140737479966720) by (clear -GB6 G14 ACV; lia).
  destruct (batch_slot A HQP HAU HG0 _ (in_or_app _ _ _ (or_intror (In_hd gl qb_dflt HGL)))) as (yh & GH1 & GH2 & GH3 & GH4 & GH5 & GH6 & GH7 & _).
  change (qb_addr (hd qb_dflt gl)) with (hd_addr gl) in GH1, GH5, GH6, GH7. unfold HIGH_SHADOW_END in GH5.

  assert (OBJS : ss_objs (ax_S X1n) = KEPT6n ++ REST2n) by reflexivity.
  set (rho3 := rho_absorb rho' REST2n (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v' := view segsA (rm rho')).
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT6n REST2n (SVar 13) 0 32 _ Hsm OBJS ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite U13; lia) ltac:(cbn [eval]; rewrite U13; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT6n REST2n vGB 0 8 _ Hsm OBJS ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(unfold vGB; cbn [eval]; rewrite E206, u64_lit by (fold gb; lia); fold gb; lia)
                ltac:(unfold vGB; cbn [eval]; rewrite E206, u64_lit by (fold gb; lia); fold gb; lia)) as [AV5 PR5].
  fold rho3 v3 in AV1, PR1, AV5, PR5. cbn [eval] in AV1, PR1. rewrite U13 in AV1, PR1.
  unfold vGB in AV5, PR5. cbn [eval] in AV5, PR5. rewrite E206, u64_lit in AV5, PR5 by (fold gb; lia). fold gb in AV5, PR5.
  assert (C_t0 : cell_ok v3 (mkACell (T + 80) 8 0)) by (replace (T + 80) with (T + 80 + 0) by lia; exact (av_cell v3 (T + 80) 0 8 ZQ 0 rho' (fun j => AV1 0 8%nat ZQ j (or_introl eq_refl)) eq_refl)).
  assert (C_t3 : cell_ok v3 (mkACell (T + 80 + 24) 8 0)) by exact (av_cell v3 (T + 80) 24 8 ZQ 0 rho' (fun j => AV1 24 8%nat ZQ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) eq_refl).
  assert (C_lnk : cell_ok v3 (mkACell gb 8 (hd_addr tl))) by (replace gb with (gb + 0) at 1 by lia; exact (av_cell v3 gb 0 8 _ _ rho' (fun j => AV5 _ _ _ j (or_introl eq_refl)) E201)).
  clear AV1 AV5.
  set (P := fun z : Z => T + 80 <= z < T + 112 \/ gb <= z < gb + 8).
  assert (INR : forall a, in_ranges rho' REST2n a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. cbn [REST2n In] in Ho.
    destruct Ho as [<-|[<-|[]]]; unfold O_tq, O_glb, carved, vGB in Hz; rewrite obj_range_mk in Hz by lia;
      cbn [fst snd eval] in Hz; rewrite ?U13, ?E206, ?u64_lit in Hz by (fold gb; lia); fold gb in Hz; lia. }
  assert (FR : forall z, ~ P z -> v3 z = v' z).
  { intros z Hz. unfold v3, v'. apply view_agree. intros Hr. unfold rho3, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho' REST2n (Z_to_bv 64 z)) as [Hin|]; [|reflexivity]. exfalso. apply Hz. pose proof (INR _ Hin) as X. rewrite u64_lit in X by exact Hr. exact X. }
  assert (FRrm : forall a, ~ P (bv_unsigned a) -> rm rho3 a = rm rho' a).
  { intros a Hz. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' REST2n a) as [Hin|]; [|reflexivity]. exfalso. exact (Hz (INR _ Hin)). }
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).

  assert (LASTIN : In (last gl qb_dflt) (qall A)) by (unfold qall; fold tl gl; apply in_or_app; right; apply In_last; exact HGL).
  assert (ADDR_INJ : forall b, In b (qall A) -> qb_addr b = gb -> b = last gl qb_dflt).
  { intros b Hb E. apply (NoDup_map_In_inj qb_addr (qall A)); [unfold qall; fold tl gl; exact HND | exact Hb | exact LASTIN | exact E]. }
  assert (IT_OUT : forall it, In it (qitems (qall A)) -> forall z, ifoot it z -> ~ P z).
  { intros it Hit z Hz HP.
    assert (QF : q_foot A z).
    { destruct (qitems_In A it Hit) as (b & Hb & Hib). unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it. split; [exact Hib|].
      unfold ifoot, it_ab in Hz. exact Hz. }
    pose proof (HSEP z QF) as NT. fold T in NT.
    destruct (qitems_In A it Hit) as (b & Hb & Hib).
    pose proof (proj1 (Forall_forall _ _) (proj1 HQP) b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hib) as (IP1 & IP2 & IP3 & IP4).
    pose proof (rz_facts (snd it)) as [RZ1 RZ2]. unfold IMG_HI in IP1.
    assert (SHlo : 0x7fff8000 <= Sh (fst it)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)); lia).
    unfold P in HP. unfold ifoot, it_ab in Hz.
    destruct HP as [HP|HP]; [lia|].
    destruct (is_primary (snd it)) eqn:EP.
    - pose proof (item_batch_apart A HQP HIDS HAU HG0 it _ Hit EP LASTIN) as AP. change (qb_addr (last gl qb_dflt)) with gb in AP.
      pose proof (item_zones A HQP HAU HG0 it Hit EP) as IZ. cbv zeta in IZ. destruct IZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). unfold it_ab, HIGH_SHADOW_END in *.
      destruct Hz as [Hz|Hz]; lia.
    - pose proof (HKSECQ it Hit EP) as [SQ SQ2]. rewrite KSV in SQ.
      assert (SHhi : Sh (fst it) + (snd it + 7) / 8 <= 0x10007fff8000).
      { unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (fst it) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fst it) 8 ltac:(lia)).
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)). lia. }
      destruct Hz as [Hz|Hz]; lia. }
  assert (BX_OUT : forall b, In b (qall A) -> forall z, qb_addr b + (if Z.eq_dec (qb_addr b) gb then 8 else 0) <= z < qb_addr b + 8192 -> ~ P z).
  { intros b Hb z Hz HP.
    assert (QF : q_foot A z).
    { unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. destruct (Z.eq_dec (qb_addr b) gb); lia. }
    pose proof (HSEP z QF) as NT. fold T in NT.
    unfold P in HP. destruct HP as [HP|HP]; [lia|].
    destruct (Z.eq_dec (qb_addr b) gb) as [E|NE]; [lia|].
    pose proof (batches_apart A HQP HAU HG0 b _ Hb LASTIN NE) as AP. change (qb_addr (last gl qb_dflt)) with gb in AP. lia. }
  assert (BF_OUT : forall b, In b (qall A) -> forall z, bfoot b z -> ~ P z).
  { intros b Hb z [Hz|Hz].
    - apply (BX_OUT b Hb). unfold kQuarantineBatchSize in Hz. destruct (Z.eq_dec (qb_addr b) gb); lia.
    - apply Exists_exists in Hz as (it & Hit & Hz). apply (IT_OUT it); [|exact Hz]. unfold qitems. apply in_flat_map. exists b. exact (conj Hb Hit). }
  assert (LK_OUT : forall b, In b (qall A) -> b <> last gl qb_dflt -> forall z, qb_addr b <= z < qb_addr b + 8 -> ~ P z).
  { intros b Hb NE z Hz. apply (BX_OUT b Hb). destruct (Z.eq_dec (qb_addr b) gb) as [E|_]; [exfalso; exact (NE (ADDR_INJ b Hb E)) | lia]. }
  assert (PQW : forall z, P z -> QW A z).
  { intros z HP. unfold P in HP. destruct HP as [HP|HP].
    - right. left. left. fold T. lia.
    - left. unfold qzone. apply Exists_exists. exists (last gl qb_dflt). split; [exact LASTIN|]. left. change (qb_addr (last gl qb_dflt)) with gb. unfold kQuarantineBatchSize. lia. }
  assert (PPR : forall z, P z -> exists b, v3 z = Some b).
  { intros z HP. unfold P in HP. destruct HP as [HP|HP]; [apply PR1 | apply PR5]; lia. }
  assert (HK3 : K A rho3 tp tr md).
  { apply (kq_view segsA K HL A rho' rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. destruct (PD z) as [HP|NP]; [exfalso; exact (NQ (PQW z HP)) | exact (FR z NP)].
    - intros z _ Hd. destruct (PD z) as [HP|NP]; [destruct (PPR z HP) as [b Hb]; fold v3; rewrite Hb; discriminate | fold v3 v' in Hd |- *; rewrite (FR z NP); exact Hd]. }
  assert (HK1 : K (A1T A) rho3 tp tr md).
  { unfold A1T. apply (kq_perm segsA K HL A [] (gl ++ tl) rho3 tp tr md); [|exact HK3]. unfold qall. fold tl gl. cbn [app]. apply Permutation_app_comm. }
  assert (INT : forall b, In b tl -> In b (qall A)) by (intros b Hb; unfold qall; fold tl gl; apply in_or_app; left; exact Hb).
  assert (ING : forall b, In b gl -> In b (qall A)) by (intros b Hb; unfold qall; fold tl gl; apply in_or_app; right; exact Hb).
  assert (TL_NOT_LAST : forall b, In b tl -> b <> last gl qb_dflt).
  { intros b Hb E. subst b.
    pose proof (NoDup_app_disj (map qb_addr tl) (map qb_addr gl) gb) as X. rewrite map_app in HND.
    apply (X HND); [apply in_map_iff; exists (last gl qb_dflt); split; [reflexivity | exact Hb] | apply in_map_iff; exists (last gl qb_dflt); split; [reflexivity | apply In_last; exact HGL]]. }
  assert (HR3 : RMEM v3 (aa_geom (A1T A)) [] (gl ++ tl)).
  { unfold RMEM. cbn [app tlinks]. split; [|split; [exact I | split]].
    - apply Forall_forall. intros b Hb.
      assert (Hb' : In b (qall A)) by (apply in_app_or in Hb as [Hb|Hb]; [exact (ING b Hb) | exact (INT b Hb)]).
      apply (batch_mem_frame A v' v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b Hb')); [intros z Hz; exact (FR z (BF_OUT b Hb' z Hz))|].
      exact (proj1 (Forall_forall _ _) HBM b ltac:(unfold qall in Hb'; fold tl gl in Hb'; exact Hb')).
    - apply qlinks_to_0. apply qlinks_to_app; [exact HTL | |].
      + apply (qlinks_to_relast v' v3 gl 0 (hd_addr tl) HGL); [| exact C_lnk | apply qlinks_to_0; exact HLG].
        intros b z Hb Hz. apply FR. apply (LK_OUT b (ING b (in_removelast_q _ _ Hb))); [|exact Hz].
        intros E. subst b. rewrite map_app in HND. exact (removelast_not_last gl HGL (NoDup_app_r _ _ HND) Hb).
      + apply (qlinks_to_frame v' v3 tl 0); [|apply qlinks_to_0; exact HLT].
        intros b z Hb Hz. apply FR. exact (LK_OUT b (INT b Hb) (TL_NOT_LAST b Hb) z Hz).
    - unfold A1T. cbn [aa_geom set_q]. fold T. unfold qhdr_repr. cbn [length]. change (T + 0x50) with (T + 80).
      split; [exact C_t0|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros z Hz; apply PR1; lia|]. exact C_t3. }
  assert (ERM : forall a, rm rho' a = rm rho a) by (intros a; rewrite <- (proj2 (proj2 Hag) a), RRM; reflexivity).
  assert (EV' : forall z, v' z = view segsA (rm rho) z) by (intros z; unfold v'; apply view_agree; intros _; apply ERM).
  assert (HF3 : FRM A rho rho3).
  { split; [|split; [|split]].
    - apply (agree_vals_trans NPRE rho (rhoT A (hd_addr gl) (last_addr gl) rho)); [exact (agree_below_vals _ _ _ RAG)|].
      apply (agree_vals_trans NPRE _ rho'); [exact (agree_below_vals _ _ _ Hag) | split; intros; reflexivity].
    - intros a NQ. rewrite <- ERM. apply FRrm. intros HP. apply NQ. left. left. exact (PQW _ HP).
    - intros z NQ. fold v3. rewrite <- EV'. apply FR. intros HP. apply NQ. left. exact (PQW _ HP).
    - intros a HB Hdef. rewrite FRrm; [rewrite ERM; exact Hdef|].
      intros HP. unfold P in HP. pose proof (geom_bands _ HG0) as (_ & TBD & _). fold T in TBD.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -HP HB TBD GB5. lia. }

  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ X1n rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho' X1n KEPT6n REST2n tp tr ms md OBJS HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. fold X2n in HU.
  set (J3 := JRQ A rho (A1T A) [] (gl ++ tl)).
  assert (H2 : SPA segsA J3 X2n rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK1 (conj HR3 HF3))]).

  assert (H2' : SPA segsA J3 X2n' rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact X2n'_below |]. intros HF. apply Forall_app. split; [exact HF|]. apply Forall_cons; [|apply Forall_nil].
    unfold F_sp. cbn [holds eval]. rewrite u64_lit by lia. change (rw rho3 10%positive) with (rw rho' 10%positive). clear -SW1 SW2 SW3. lia. }
  pose proof (SPA_axforms segsA J3 _ rho3 X2n' X4n tp _ X4n_eq H2') as H4.

  assert (EGN : eval rho3 gn' = Z_to_bv 64 (Z.of_nat (length gl) + Z.of_nat (length tl))) by (apply eval_add_z; [exact E204 | exact E200 | lia | lia | lia]).
  assert (EGS : eval rho3 gsz = Z_to_bv 64 (qsize gl + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
  assert (H5 : SPA segsA J3 X5n rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H4 | exact X5n_below |]. intros HF. apply Forall_app. split; [exact HF|]. unfold NFn.
    repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds branch_taken]. rewrite EGN. cbn [eval]. unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E.
      assert (0 < Z.of_nat (length gl)) by (destruct gl; [congruence | cbn; lia]). lia.
    - unfold vGF. cbn [holds eval]. change (rw rho3 205%positive) with (rw rho' 205%positive). rewrite E205, !u64_lit by (unfold HIGH_SHADOW_END; lia). unfold HIGH_SHADOW_END. lia.
    - cbn [holds]. split; [lia|]. change (rw rho3 205%positive) with (rw rho' 205%positive). rewrite E205, u64_lit by lia.
      clear -GH7. pose proof (Z.div_mod (hd_addr gl) 8192 ltac:(lia)) as D. rewrite GH7, Z.add_0_r in D. rewrite D. replace (8192 * (hd_addr gl / 8192)) with (1024 * (hd_addr gl / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia.
    - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite U_sllk by lia. rewrite EGN, EGS, !u64_lit by lia.
      rewrite Z.mod_small by lia. lia. }
  destruct (entM_SPA J3 X5n PreR2 MEn rho3 tp _ X5n_ent (JRQ_stable _ _ _ _ _) H5) as (H6 & AG6 & V6 & RM6).
  exists (rho_sub rho3 (infer_sub NPRE (ax_S X5n) (ax_S PreR2))). split; [exact H6|]. split.
  - unfold HVP. rewrite length_app, Nat2Z.inj_add, qsize_app.
    split; [rewrite (V6 _ _ (or_introl eq_refl)); exact EGN|].
    split; [rewrite (V6 _ _ (or_intror (or_introl eq_refl))); unfold vGF; cbn [eval]; change (rw rho3 205%positive) with (rw rho' 205%positive); rewrite E205; f_equal; unfold hd_addr; destruct gl; [congruence | reflexivity]|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_introl eq_refl)))); unfold vTB; cbn [eval]; change (rw rho3 202%positive) with (rw rho' 202%positive); rewrite E202; f_equal; unfold last_addr; rewrite (last_app_ne gl tl qb_dflt HTL); reflexivity|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))); exact EGS|].
    rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))). unfold vMIN. cbn [eval]. exact E208.
  - assert (EGS' : eval rho' gsz = Z_to_bv 64 (qsize gl + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
    rewrite qsize_app. unfold F_gt in FGT. cbn [holds branch_taken] in FGT. rewrite EGS' in FGT. cbn [eval] in FGT.
    apply not_true_is_false in FGT. apply negb_false_iff in FGT. unfold bv_ltu in FGT. apply Z.ltb_lt in FGT. rewrite !u64_lit in FGT by (unfold kQuarantineMax; lia). exact FGT.
Qed.

Lemma entry_Re : ltac2:(tb__ "0|3|
S25S2cS2cS10S10S4S45Q40A1A1S74S20S1eS4S24A1M0S27R7A1S2S24A1M1A3A1S1eG0S26R8A1G1A3S1eS6S28R9A1S7A3S88RaA1S8eS3dS86RbRaR9R8A4R7A3S4dS30S87S30VK;RcA3S39R8R7R6A6S21S10S10S1fS4dS30S6aReRbS85ReA1G1S3S24S26ReA1S27ReA1A3M2A5S50R1R9R8A6S1fS59R1G2A2S6dS7dS75G2A1A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;Fgb;Fgf;FA;").
Proof.
  intros A gf gb rho rho' tp w HTL HGL HCI HBND [Hag Hkeep] H0. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho' ReQ3e X1e tp _ X1e_eq H0) as H. clear H0.
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (tl := aa_q_thread A) in *. set (T := ag_thread (aa_geom A)).
  destruct (kq_facts segsA K HL A rho' tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T in E151.
  destruct (rhoT_vals A gf gb rho) as (R200 & R201 & R202 & R203 & R204 & R205 & R206 & R207 & R208 & R209 & RRM & RAG).
  assert (KV : forall v, In v KEEP3 -> rw rho' v = rw (rhoT A gf gb rho) v) by exact Hkeep.
  assert (E200 : rw rho' 200%positive = Z_to_bv 64 (Z.of_nat (length tl))) by (rewrite KV by (cbn; tauto); exact R200).
  assert (E201 : rw rho' 201%positive = Z_to_bv 64 (hd_addr tl)) by (rewrite KV by (cbn; tauto); exact R201).
  assert (E202 : rw rho' 202%positive = Z_to_bv 64 (last_addr tl)) by (rewrite KV by (cbn; tauto); exact R202).
  assert (E203 : rw rho' 203%positive = Z_to_bv 64 (qsize tl)) by (rewrite KV by (cbn; tauto); exact R203).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 0) by (rewrite KV by (cbn; tauto); rewrite R207, HGL; reflexivity).
  assert (E208 : rw rho' 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite KV by (cbn; tauto); exact R208).
  clear KV R200 R201 R202 R203 R204 R205 R206 R207 R208 R209.
  pose proof (SPA_facts_hold segsA _ rho' X1e tp _ H) as HFa.
  assert (U13 : bv_unsigned (rw rho' 13%positive) = T + 80).
  { assert (X : holds rho' (SPBranch BC_EQ (SVar 13) (add vT (SLit 80)))) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
    cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  assert (FGT : holds rho' F_gt) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  assert (Hhigh : holds rho' F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  destruct (stack_win_range _ rho' _ _ Hsm ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND, HBM. rewrite HGL, app_nil_r in HBP, HND, HBM. fold tl in HBP, HND, HBM, HLT, HHT.
  assert (LEN2 : Z.of_nat (length tl) < 2 ^ 35 /\ 0 <= qsize tl /\ 8192 * Z.of_nat (length tl) <= qsize tl).
  { destruct HBND as [B1 B2]. fold tl in B1. pose proof (qsize_ge A _ _ HBP HBM). unfold kQuarantineBatchSize in *. lia. }
  destruct LEN2 as (LT & ST0 & SGEt). destruct HBND as [BT _]. fold tl in BT.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (cv_bounds _ _ _ _ _ (HCLS HCI c Hc)) as (B1 & B2 & B3 & _). unfold kUserMapSize in *. lia. }
  assert (HQP : q_pure A) by (split; unfold qall; rewrite HGL, app_nil_r; assumption).
  assert (QALL : qall A = tl) by (unfold qall; rewrite HGL, app_nil_r; reflexivity).
  destruct (batch_slot A HQP HAU HG0 (hd qb_dflt tl) ltac:(rewrite QALL; apply In_hd; exact HTL)) as (yh & GH1 & GH2 & GH3 & GH4 & GH5 & GH6 & GH7 & _).
  change (qb_addr (hd qb_dflt tl)) with (hd_addr tl) in GH1, GH5, GH6, GH7. unfold HIGH_SHADOW_END in GH5.
  assert (OBJS : ss_objs (ax_S X1e) = KEPT6e ++ REST1e) by reflexivity.
  set (rho3 := rho_absorb rho' REST1e (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v' := view segsA (rm rho')).
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT6e REST1e (SVar 13) 0 32 _ Hsm OBJS ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite U13; lia) ltac:(cbn [eval]; rewrite U13; lia)) as [AV1 PR1].
  fold rho3 v3 in AV1, PR1. cbn [eval] in AV1, PR1. rewrite U13 in AV1, PR1.
  assert (C_t0 : cell_ok v3 (mkACell (T + 80) 8 0)) by (replace (T + 80) with (T + 80 + 0) by lia; exact (av_cell v3 (T + 80) 0 8 ZQ 0 rho' (fun j => AV1 0 8%nat ZQ j (or_introl eq_refl)) eq_refl)).
  assert (C_t3 : cell_ok v3 (mkACell (T + 80 + 24) 8 0)) by exact (av_cell v3 (T + 80) 24 8 ZQ 0 rho' (fun j => AV1 24 8%nat ZQ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) eq_refl).
  clear AV1.
  set (P := fun z : Z => T + 80 <= z < T + 112).
  assert (INR : forall a, in_ranges rho' REST1e a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. cbn [REST1e In] in Ho.
    destruct Ho as [<-|[]]; unfold O_tq, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd eval] in Hz; rewrite ?U13 in Hz; lia. }
  assert (FR : forall z, ~ P z -> v3 z = v' z).
  { intros z Hz. unfold v3, v'. apply view_agree. intros Hr. unfold rho3, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho' REST1e (Z_to_bv 64 z)) as [Hin|]; [|reflexivity]. exfalso. apply Hz. pose proof (INR _ Hin) as X. rewrite u64_lit in X by exact Hr. exact X. }
  assert (FRrm : forall a, ~ P (bv_unsigned a) -> rm rho3 a = rm rho' a).
  { intros a Hz. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' REST1e a) as [Hin|]; [|reflexivity]. exfalso. exact (Hz (INR _ Hin)). }
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (QF_OUT : forall z, q_foot A z -> ~ P z) by (intros z QF HP; pose proof (HSEP z QF) as NT; fold T in NT; unfold P in HP; lia).
  assert (BF_OUT : forall b, In b (qall A) -> forall z, bfoot b z -> ~ P z).
  { intros b Hb z Hz. apply QF_OUT. unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. unfold bfoot in Hz.
    destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right]. apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it.
    split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz. }
  assert (LK_OUT : forall b, In b (qall A) -> forall z, qb_addr b <= z < qb_addr b + 8 -> ~ P z).
  { intros b Hb z Hz. apply QF_OUT. unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. lia. }
  assert (PQW : forall z, P z -> QW A z) by (intros z HP; unfold P in HP; right; left; left; fold T; lia).
  assert (HK3 : K A rho3 tp tr md).
  { apply (kq_view segsA K HL A rho' rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. destruct (PD z) as [HP|NP]; [exfalso; exact (NQ (PQW z HP)) | exact (FR z NP)].
    - intros z _ Hd. destruct (PD z) as [HP|NP]; [destruct (PR1 z ltac:(unfold P in HP; lia)) as [b Hb]; fold v3; rewrite Hb; discriminate | fold v3 v' in Hd |- *; rewrite (FR z NP); exact Hd]. }
  assert (HK1 : K (A1T A) rho3 tp tr md).
  { unfold A1T. apply (kq_perm segsA K HL A [] (aa_q_global A ++ tl) rho3 tp tr md); [|exact HK3]. unfold qall. fold tl. cbn [app]. apply Permutation_app_comm. }
  rewrite HGL. cbn [app].
  assert (HR3 : RMEM v3 (aa_geom (A1T A)) [] tl).
  { unfold RMEM. cbn [app tlinks]. split; [|split; [exact I | split]].
    - apply Forall_forall. intros b Hb. assert (Hb' : In b (qall A)) by (rewrite QALL; exact Hb).
      apply (batch_mem_frame A v' v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b Hb')); [intros z Hz; exact (FR z (BF_OUT b Hb' z Hz))|].
      exact (proj1 (Forall_forall _ _) HBM b Hb).
    - apply qlinks_to_0. apply (qlinks_to_frame v' v3 tl 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. exact (LK_OUT b ltac:(rewrite QALL; exact Hb) z Hz).
    - unfold A1T. cbn [aa_geom set_q]. fold T. unfold qhdr_repr. cbn [length]. change (T + 0x50) with (T + 80).
      split; [exact C_t0|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros z Hz; apply PR1; unfold P; lia|]. exact C_t3. }
  assert (ERM : forall a, rm rho' a = rm rho a) by (intros a; rewrite <- (proj2 (proj2 Hag) a), RRM; reflexivity).
  assert (EV' : forall z, v' z = view segsA (rm rho) z) by (intros z; unfold v'; apply view_agree; intros _; apply ERM).
  assert (HF3 : FRM A rho rho3).
  { split; [|split; [|split]].
    - apply (agree_vals_trans NPRE rho (rhoT A gf gb rho)); [exact (agree_below_vals _ _ _ RAG)|].
      apply (agree_vals_trans NPRE _ rho'); [exact (agree_below_vals _ _ _ Hag) | split; intros; reflexivity].
    - intros a NQ. rewrite <- ERM. apply FRrm. intros HP. apply NQ. left. left. exact (PQW _ HP).
    - intros z NQ. fold v3. rewrite <- EV'. apply FR. intros HP. apply NQ. left. exact (PQW _ HP).
    - intros a HB Hdef. rewrite FRrm; [rewrite ERM; exact Hdef|].
      intros HP. unfold P in HP. pose proof (geom_bands _ HG0) as (_ & TBD & _). fold T in TBD.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -HP HB TBD. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ X1e rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho' X1e KEPT6e REST1e tp tr ms md OBJS HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. fold X2e in HU.
  set (J3 := JRQ A rho (A1T A) [] tl).
  assert (H2 : SPA segsA J3 X2e rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK1 (conj HR3 HF3))]).
  assert (H2' : SPA segsA J3 X2e' rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact X2e'_below |]. intros HF. apply Forall_app. split; [exact HF|]. apply Forall_cons; [|apply Forall_nil].
    unfold F_sp. cbn [holds eval]. rewrite u64_lit by lia. change (rw rho3 10%positive) with (rw rho' 10%positive). clear -SW1 SW2 SW3. lia. }
  pose proof (SPA_axforms segsA J3 _ rho3 X2e' X4e tp _ X4e_eq H2') as H4.
  assert (EGS : eval rho3 gsz = Z_to_bv 64 (0 + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
  assert (H5 : SPA segsA J3 X5e rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H4 | exact X5e_below |]. intros HF. apply Forall_app. split; [exact HF|]. unfold NFe.
    repeat apply Forall_cons; try apply Forall_nil.
    - unfold vTN. cbn [holds branch_taken eval]. change (rw rho3 200%positive) with (rw rho' 200%positive). rewrite E200. unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E.
      assert (0 < Z.of_nat (length tl)) by (destruct tl; [congruence | cbn; lia]). lia.
    - cbn [holds eval]. change (rw rho3 201%positive) with (rw rho' 201%positive). rewrite E201, !u64_lit by (unfold HIGH_SHADOW_END; lia). unfold HIGH_SHADOW_END. lia.
    - cbn [holds]. split; [lia|]. change (rw rho3 201%positive) with (rw rho' 201%positive). rewrite E201, u64_lit by lia.
      clear -GH7. pose proof (Z.div_mod (hd_addr tl) 8192 ltac:(lia)) as D. rewrite GH7, Z.add_0_r in D. rewrite D. replace (8192 * (hd_addr tl / 8192)) with (1024 * (hd_addr tl / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia.
    - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite U_sllk by lia. rewrite EGS. unfold vTN. cbn [eval]. change (rw rho3 200%positive) with (rw rho' 200%positive).
      rewrite E200, !u64_lit by lia. rewrite Z.mod_small by lia. lia. }
  destruct (entM_SPA J3 X5e PreR2 MEe rho3 tp _ X5e_ent (JRQ_stable _ _ _ _ _) H5) as (H6 & AG6 & V6 & RM6).
  exists (rho_sub rho3 (infer_sub NPRE (ax_S X5e) (ax_S PreR2))). split; [exact H6|]. split.
  - unfold HVP.
    split; [rewrite (V6 _ _ (or_introl eq_refl)); unfold vTN; cbn [eval]; exact E200|].
    split; [rewrite (V6 _ _ (or_intror (or_introl eq_refl))); cbn [eval]; exact E201|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_introl eq_refl)))); unfold vTB; cbn [eval]; exact E202|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))); rewrite EGS; f_equal; lia|].
    rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))). unfold vMIN. cbn [eval]. exact E208.
  - assert (EGS' : eval rho' gsz = Z_to_bv 64 (0 + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
    unfold F_gt in FGT. cbn [holds branch_taken] in FGT. rewrite EGS' in FGT. cbn [eval] in FGT.
    apply not_true_is_false in FGT. apply negb_false_iff in FGT. unfold bv_ltu in FGT. apply Z.ltb_lt in FGT. rewrite !u64_lit in FGT by (unfold kQuarantineMax; lia). lia.
Qed.

End Recycle.
End SegQ3R_skel.

(* [comment removed for export] *)
Module F0A_sem.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "mul"; "land"; "lt"; "pow"; "div"; "lxor"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "zsext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem"; "aceilF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "casx"; "hw2"; "len_e"; "rup_e"; "usz_e"; "vH3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition aceilF : Z := 140737479966720.
Lemma alloc_ceiling_valF : aceilF = 0x7fffff800000. Proof. reflexivity. Qed.

Lemma land_255 : ltac2:(tb__ "0|0|
S0S4Z0R1A2S2S0S8R2ZffA2S6R2Z100A2A3F_;Fa;").
Proof. intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_3 : ltac2:(tb__ "0|0|
S0S4Z0R1A2S2S0S8R2Z3A2S6R2Z4A2A3F_;Fa;").
Proof. intros a Ha. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lxor_1_even : ltac2:(tb__ "0|2|
S0S4Z0M0R1A2S2S0S6R2Z2A2G0A3S2S0ScR3Z1M1A2S5R3G1A2A3F_;F_;Fa;").
Proof.
  intros a Ha He. symmetry. apply Z.add_nocarry_lxor. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. exact He.
Qed.
Lemma land_lxor_distr : ltac2:(tb__ "0|0|
S0S0S0S2S0S8ScR3R2A2R1A2ScS8R3R1A2S8R2R1A2A2A3Fc;Fb;Fa;").
Proof.
  intros a b c. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit c i); reflexivity.
Qed.
Lemma zsext_small : ltac2:(tb__ "0|0|
S0S0S3S4Z0R1A2S9R1SaZ2SdR2Z1A2A2A2A2S2S0S12R3R2A2R2A3F_;Fm;Fw;").
Proof. intros w m Hm. unfold zsext. destruct (Z.ltb_spec m (2 ^ (w - 1))); [reflexivity | lia]. Qed.

Definition semF (rho : valuation) (t : Z) : Prop := ltac2:(tb__ "0|b|
S1S10Q40SfVrho;R1A2A2Li;S1S0Fi;S3S3S3S4Z0M0Vt;A2S9Vt;Z100M1A2A2S2S0S6Vt;Z4A2Z1M2A3A2S3S2S0S6R1PcA1M3Z10M4A2G0A3S3S4G4G3A2S3S4G2R1PdA1M5A2S3S4S5G3R1P69A1M6A2S13A2S3S2S0R1P67A1S6G5SaZ2M7Z20A2M8A2A3S3S2S0R1P68A1M9S5S5G7S7G1Vt;A2A2S7Z10000SbG5G8A2A2A2A3S3S2S0R1P6bA1S5G9G2A2A3S3S2S0G6S7SbS5G5Z7A2Z8MaA2GaA2A3S2S0R1P6aA1SbG6GaA2A3A2A2A2A2A2A2A2A2A2TU;").

Section SemF.
Variable rho : valuation.
Let U (i : positive) : Z := bv_unsigned (rw rho i).
Variable t : Z.
Hypothesis HH : semF rho t.
Let Ht : 0 <= t < 256 /\ t mod 4 = 1. Proof. exact (proj1 HH). Qed.
Let Hp16 : U 12%positive mod 16 = 0. Proof. exact (proj1 (proj2 HH)). Qed.
Let Hp_lo : 16 <= U 12%positive. Proof. exact (proj1 (proj2 (proj2 HH))). Qed.
Let Hn : 1 <= U 13%positive. Proof. exact (proj1 (proj2 (proj2 (proj2 HH)))). Qed.
Let Hpn : U 12%positive + U 105%positive <= aceilF. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HH))))). Qed.
Let H103 : U 103%positive = U 13%positive mod 2 ^ 32. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HH)))))). Qed.
Let H104 : U 104%positive = 2 + 256 * t + 65536 * (U 13%positive / 2 ^ 32). Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH))))))). Qed.
Let H107 : U 107%positive = U 104%positive + 1. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH)))))))). Qed.
Let H105 : U 105%positive = (U 13%positive + 7) / 8 * 8. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH))))))))). Qed.
Let H106 : U 106%positive = U 105%positive / 8. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH))))))))). Qed.

Let p : Z := U 12%positive.
Let n : Z := U 13%positive.
Let q : Z := U 13%positive / 2 ^ 32.

Lemma n_lt : n < 2 ^ 47.
Proof. pose proof alloc_ceiling_valF. unfold n, p in *. rewrite H105 in Hpn. pose proof (Z.mul_div_le (U 13%positive + 7) 8 ltac:(lia)). lia. Qed.
Lemma q_lt : 0 <= q < 2 ^ 15.
Proof. pose proof n_lt. unfold q, n in *. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma hw_lt : ltac2:(tb__ "0|3|
S3S3S4Z0M0VU;P68A1M1A2S9G1SaZ2M2Z1fA2A2A2S3S2S0S6G1Z100A2G2A3S2S0S6G1G2A2G0A3A2A2").
Proof.
  pose proof q_lt as Q. fold q in H104. rewrite H104. split; [lia|]. split.
  - replace (2 + 256 * t + 65536 * q) with (2 + (t + 256 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (2 + 256 * t + 65536 * q) with (0 + (1 + 128 * t + 32768 * q) * 2) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma h3_val : ltac2:(tb__ "0|1|
S3S2S0VU;P6bA1M0S5S5Z3S7Z100Vt;A2A2S7Z10000Vq;A2A2A3S3S4Z0G0A2S9G0SaZ2Z1fA2A2A2A2").
Proof. pose proof q_lt. fold q in H104. rewrite H107, H104. split; lia. Qed.
Lemma n8_facts : ltac2:(tb__ "0|2|
S3S3S4Vn;VU;P69A1M0A2S9G0S5Vn;Z8M1A2A2A2S3S2S0S6G0G1A2Z0A3S3S4G1G0A2S2S0S7VU;P6aA1G1A2G0A3A2A2A2").
Proof.
  unfold n in *. rewrite H106, H105. pose proof (Z.div_mod (U 13%positive + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U 13%positive + 7) 8 ltac:(lia)).
  split; [lia|]. split; [apply Z.mod_mul; lia|]. split; [|rewrite Z.div_mul by lia; lia].
  assert (1 <= (U 13%positive + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma U_hw2 : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S15A2A2VU;P68A1A3").
Proof.
  pose proof hw_lt as (R & _ & _). unfold hw2, vHW. rewrite U_sext_e by lia. cbn [eval]. fold (U 104%positive). change (Z.of_N 32) with 32.
  rewrite Z.mod_small by lia. apply zsext_small. change (2 ^ (32 - 1)) with (2 ^ 31). lia.
Qed.

Lemma sem_casx : ltac2:(tb__ "0|0|
S2S11Q40A1SeVrho;S14A2SeVrho;S19A2A3").
Proof.
  pose proof hw_lt as (R & M256 & M2). apply bv_eq. unfold casx. rewrite U_xor2, U_and2, U_xor2, !U_hw2, !U_lit. unfold vH3. cbn [eval]. fold (U 107%positive).
  change (3 mod M64v) with 3. change (255 mod M64v) with 255.
  rewrite land_lxor_distr. rewrite !land_255 by lia. rewrite M256. change (3 mod 256) with 3. change (Z.lxor 2 3) with 1.
  rewrite lxor_1_even by lia. symmetry. exact H107.
Qed.

Lemma sem_typ : Forall (holds rho) F_typ.
Proof.
  pose proof h3_val as [E3 R3]. pose proof Ht as [Tt T4]. pose proof q_lt as Q.
  unfold F_typ, vH3. repeat apply Forall_cons; try apply Forall_nil.
  - apply (proj2 (holds_nbne rho _ _)). rewrite U_sext_e, U_lit by lia. cbn [eval]. fold (U 107%positive). change (Z.of_N 8) with 8. change (3 mod M64v) with 3.
    replace (U 107%positive mod 2 ^ 8) with 3.
    2:{ rewrite E3. replace (3 + 256 * t + 65536 * q) with (3 + (t + 256 * q) * 2 ^ 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    reflexivity.
  - apply (proj2 (holds_nbne rho _ _)). rewrite U_lit, U_and2, U_zext_e, U_srl_lit, U_lit by lia. cbn [eval]. fold (U 107%positive).
    change (Z.of_N 8) with 8. change (8 mod 64) with 8. change (1 mod M64v) with 1. change (3 mod M64v) with 3.
    rewrite E3. replace (3 + 256 * t + 65536 * q) with (3 + (t + 256 * q) * 2 ^ 8) by lia. rewrite Z.div_add by lia. change (3 / 2 ^ 8) with 0.
    rewrite Z.add_0_l. replace (t + 256 * q) with (t + q * 2 ^ 8) by lia. rewrite Z.mod_add by lia. rewrite (Z.mod_small t) by lia.
    rewrite land_3 by lia. symmetry. exact T4.
  - apply (proj2 (holds_ult rho _ _)). rewrite U_lit. cbn [eval]. fold (U 107%positive). change ((2 ^ 32) mod M64v) with (2 ^ 32). lia.
Qed.

Lemma sem_usz : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S18A2A2Vn;A3").
Proof.
  pose proof h3_val as [E3 R3]. pose proof Ht as [Tt T4]. pose proof q_lt as Q. pose proof n_lt as N. pose proof (urange (rw rho 103%positive)) as R103.
  unfold usz_e, vH3, vNLO. rewrite U_or2, U_sll_lit, U_srl_lit, U_zext_e by lia. cbn [eval]. fold (U 107%positive) (U 103%positive).
  change (16 mod 64) with 16. change (32 mod 64) with 32. change (Z.of_N 32) with 32.
  replace (U 107%positive / 2 ^ 16) with q.
  2:{ rewrite E3. replace (3 + 256 * t + 65536 * q) with ((3 + 256 * t) + q * 2 ^ 16) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  unfold M64v. rewrite (Z.mod_small (q * 2 ^ 32)) by lia. rewrite H103. fold n. rewrite (Z.mod_small (n mod 2 ^ 32)) by (pose proof (Z.mod_pos_bound n (2 ^ 32)); lia).
  rewrite lor_disjoint_add; [| lia | pose proof (Z.mod_pos_bound n (2 ^ 32)); lia | rewrite Z.land_comm; apply land_low_high; try lia; pose proof (Z.mod_pos_bound n (2 ^ 32)); lia].
  unfold q, n. pose proof (Z.div_mod (U 13%positive) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma sem_rup : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S17A2A2VU;P69A1A3").
Proof.
  pose proof n_lt as N. pose proof n8_facts as (A & B & C & D).
  unfold rup_e. rewrite (U_and_hmask rho _ 18446744073709551608 8 eq_refl). rewrite U_add, sem_usz, U_lit. change (7 mod M64v) with 7.
  unfold M64v. rewrite Z.mod_small by (unfold n; lia). rewrite H105. fold n.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). lia.
Qed.
Lemma sem_d3 : diffs_ok rho d3F.
Proof.
  unfold diffs_ok, d3F. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; apply bv_eq.
  - rewrite sem_rup. reflexivity.
  - rewrite sem_usz. reflexivity.
  - rewrite sem_usz. reflexivity.
Qed.

Lemma sem_len : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S16A2A2VU;P6aA1A3").
Proof.
  pose proof n_lt as N. pose proof n8_facts as (A & B & C & D). pose proof alloc_ceiling_valF as ACV.
  unfold len_e, vN8. rewrite U_sub, U_add, !U_srl_lit, !U_add, !U_lit. cbn [eval]. fold (U 12%positive) (U 105%positive). fold p.
  change (3 mod 64) with 3. change ((-8) mod M64v) with (M64v - 8). change (1 mod M64v) with 1.
  rewrite (Z.mod_small (p + U 105%positive)) by (unfold M64v, p in *; lia).
  replace (p + U 105%positive + (M64v - 8)) with ((p + U 105%positive - 8) + 1 * M64v) by lia. rewrite Z.mod_add by (unfold M64v; lia).
  rewrite (Z.mod_small (p + U 105%positive - 8)) by (unfold M64v, p in *; lia).
  pose proof (Z.div_mod p 16 ltac:(lia)) as P16. fold p in Hp16.
  replace (p + U 105%positive - 8) with ((p / 16 * 2 + U 106%positive - 1) * 2 ^ 3) by lia.
  replace p with ((p / 16 * 2) * 2 ^ 3) at 2 by lia.
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by (unfold M64v, p in *; lia).
  replace (p / 16 * 2 + U 106%positive - 1 + 1 - p / 16 * 2) with (U 106%positive) by lia. apply Z.mod_small. unfold M64v; lia.
Qed.
Lemma sem_d4 : diffs_ok rho d4F.
Proof. unfold diffs_ok, d4F. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply bv_eq. rewrite sem_len. reflexivity. Qed.

Lemma sem_cas : Forall (holds rho) F_cas.
Proof.
  pose proof hw_lt as (R & M256 & M2). pose proof n_lt as N. pose proof n8_facts as (A & _). pose proof alloc_ceiling_valF as ACV.
  assert (E : forall k, 0 <= k < 2 ^ 31 -> bv_unsigned (eval rho (SAluW ALU_SLL (SLit k) m8)) = k).
  { intros k Hk. unfold m8. rewrite U_sllw, U_sll_lit, U_add, !U_lit. cbn [eval]. fold (U 12%positive). fold p. change (3 mod 64) with 3.
    change ((-16) mod M64v) with (M64v - 16).
    assert (Ep : (p + (M64v - 16)) mod M64v = p - 16).
    { replace (p + (M64v - 16)) with ((p - 16) + 1 * M64v) by lia. rewrite Z.mod_add by (unfold M64v; lia). apply Z.mod_small. unfold M64v, p in *; lia. }
    rewrite Ep.
    set (sh := ((((p - 16) * 2 ^ 3) mod M64v) mod 2 ^ 32) mod 32).
    replace sh with 0.
    2:{ subst sh. unfold M64v. pose proof (Z.div_mod p 16 ltac:(lia)) as P16. fold p in Hp16.
        rewrite (Z.mod_mod_divide _ 18446744073709551616 (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
        rewrite (Z.mod_mod_divide _ (2 ^ 32) 32) by (exists (2 ^ 27); reflexivity).
        replace ((p - 16) * 2 ^ 3) with (0 + (p / 16 - 1) * 4 * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
    rewrite Z.pow_0_r, Z.mul_1_r. unfold M64v. rewrite !(Z.mod_small k) by (clear - Hk; lia). apply zsext_small. change (2 ^ (32 - 1)) with (2 ^ 31). lia. }
  unfold F_cas. repeat apply Forall_cons; try apply Forall_nil.
  - apply (proj2 (holds_nbne rho _ _)). rewrite U_and2, U_hw2, !U_lit. change (255 mod M64v) with 255. change (2 mod M64v) with 2. rewrite land_255 by lia. exact M256.
  - apply (proj2 (holds_ult rho _ _)). unfold vHW. rewrite U_lit. cbn [eval]. fold (U 104%positive). change ((2 ^ 32) mod M64v) with (2 ^ 32). lia.
  - apply (proj2 (holds_beq rho _ _)). rewrite E, U_lit by lia. reflexivity.
  - apply (proj2 (holds_beq rho _ _)). rewrite E, U_lit by lia. reflexivity.
  - apply (proj2 (holds_beq rho _ _)). rewrite E, U_lit by lia. reflexivity.
Qed.
End SemF.
End F0A_sem.

(* [comment removed for export] *)
Module CertCallocSS.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "app"; "prod"; "option"; "false"; "list"; "None"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "SPUle"; "sobj"; "SAlu"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "SPUlt"; "mkSS"; "DZero"; "SPNot"; "cell"; "mkObj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_setS"; "sym_runA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_MS"; "V_NS"; "msx"; "V_NCH"; "V_NRES"; "V_PAB"; "RT_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS.W"; "CS1"; "nxS"; "regs_ss"; "ES1"; "ES1f"; "SS0"; "SSa_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayReserve"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "E_regs"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition V_NS : positive := 141%positive.
Definition V_MS : positive := 142%positive.
Definition V_PAB : positive := 145%positive.
Definition V_NRES : positive := 146%positive.
Definition V_NCH : positive := 147%positive.

Definition N_sec : list carve_spec := ltac2:(tb__ "0|d|
S1S5S5S5ScSbA2M0SbA2M1S8S5S5SbS2A2M2ScA2M3A1M4A2M5S0G1G4S0G0SbS0ScSbSeZ0A1M6S1dA4S1eS1dZ40A2M7A4S1G3S0G2ScS0SbS2S1dU8M8A4SeS3dA1A4S1G3S0G2ScS0SbS2S1eS1dZ8A2G8A4SfS2dA1M9A4S1G3S0G2ScS0SbS2S1eS1dZ10A2G8A4G9A4S1G3S0G2ScS0SbS2S1eS1dZ18A2G8A4SeS3bA1A4S1G3S0G2ScS0SbS2S1eS1dZ30A2G8A4SfS2cA1A4S1G3S0G2ScS0SbS2S1eS1dZ38A2G8A4SfS2bA1A4S3G3A1MaA3A3A3A3A3A3A4S1G5S0G1G4S0G0SbS0ScSbG6G7A4Zead00MbA4GaA4S1G5S0G1G4S0G0SbS0ScSbG6GbA4Zead04A4S1G3S0G2ScS0SbS2GbU4A4G6A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Zead08A4Zead30A4GaA4S1G5S0G1G4S0G0SbS0ScSbG6Ze67b8McA4Ze67c0A4S1G3S0G2ScS0SbS2GcG8A4SeZ1a309A1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Z170320A4Z170322A4S1G3S0G2ScS0SbS2Z170321U1A4SeZ1A1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6S3eA4S1eS3eZ4A2A4GaA4S1G5S0G1G4S0G0SbS0ScSbS48Zad0A4Zc60A4GaA4S3G5A1A3A3A3A3A3A3A3A3").
Definition RT_sec : list sobj := map carve_obj N_sec.
Definition O_seci : sobj := nth 0 RT_sec O_st. Definition O_secs : sobj := nth 1 RT_sec O_st. Definition O_secm : sobj := nth 2 RT_sec O_st.
Definition O_secg : sobj := nth 3 RT_sec O_st. Definition O_san : sobj := nth 4 RT_sec O_st. Definition O_oom : sobj := nth 5 RT_sec O_st.
Definition O_errno : sobj := nth 6 RT_sec O_st.

Definition msx : sv := ltac2:(tb__ "0|0|
S12S21S12S23S12S21SfS29A1SeZfffA1A3SeZfffffffffffff000A1A3SeZ1000A1A3").
Definition F_sgen : list sprop := ltac2:(tb__ "0|6|
S1SdS14S29Z3A2S1SdS10SeZ10c08A1SfS29A1M0A2S1SdS16G0SeS1eS1fZ2M1Z27A2Z1008A2A1A2S1SdS14S28ZcA2S1SdS10S12S21G0SeZ1000A1A3SfS28A1M2A2S1SdS10G2S12S21G0SeZ1fffA1A3A2S1SdS16G2SeS1fG1Z28A2A1M3A2S1SdS15S22G2S2aA3S1SdS10SeS3cA1SfS2dA1M4A2S1SdS10G4SeS20Z7fffff800000S3bA2A1A2S1SdS10SfS2bA1SfS2cA1M5A2S1SdS10G5SeS1fG1Z14A2A1A2S1SdS10G0S2aA2S1SdS10S2aG3A2S1SdS19S15S22S12S21SfPaA1SeN9c8A1A3SeZ0A1A3A1S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.

Let FACTS1 : list sprop := ltac2:(tb__ "0|0|
S4SdS4SdS4SdS4SdS4cVW;Vst;A2S4bS4aA1A3S39A3S44A3S43Vtmax;Z8A2A3").
Let OBJS1 : list sobj := ltac2:(tb__ "0|0|
S4S11S1S11S45S4S11S4dVW;A1S49A3A3S47A3").

Definition regs_ss : list sv := ltac2:(tb__ "0|2|
S37S41Z8A1S1S5S2ScA2M0S0S2ScUcSfS29A1M1A4S1G0S0S2ScU13G1A4S3G0A1A3A3A2").
Definition SSa_S : sstate := ltac2:(tb__ "0|0|
S17Z40bacS31S36S13S9ScA1VOBJS1;VFACTS1;S38S7A9").
Definition SSa : axst := ltac2:(tb__ "0|0|
S25S42VW;Vst;Vtmax;Z8A4S35A2").
Definition SSb_S : sstate := ltac2:(tb__ "0|0|
S17Z40bacS31S36S13S9ScA1S4S11VOBJS1;S2eA3VFACTS1;S38S7A9").
Definition SSb : axst := ax_setS SSa SSb_S.
Definition SS0 : axst := ax_add_facts F_sgen SSb.
Definition runS1 : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ706a0S3SbA1A3S34SaA5G0R1Ll;S3S24A1X6x2").
Definition ES1 : axst := leaf 0 runS1.

Definition CS1 : axst := ltac2:(tb__ "0|1|
S46VW;Vst;Vtmax;S32Z706a0S1S5S2ScA2M0S0S2ScUbSfS28A1A4S3G0A1A3S3S11A1S7S3SdA1A9").

Definition ES1f : axst := ltac2:(tb__ "0|0|
S40S2fSeS20S1fZ2Z40A2ZcA2A1A2").
Definition runSf : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ5e768S3SbA1A3S33SaA5G0R1Ll;S3S24A1X6x2").
Definition ESn : axst := leaf 0 runSf.

Definition nxS : positive := ss_next (ax_S CS1).
Definition ES1g : axst := ltac2:(tb__ "0|2|
S25S2fS3fS27S2fA1M0SfS30A1M1S4S11S1cG0A1S1S11S1bG1SeZ0A1SfS28A1S3S1aA1S18A5S3S11A1A3A3S4eS30A1A4A2").
End W.

Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runS1 (Wcan 0) UStopLe 2) = [(0x706a0, RsCut)]
  /\ nth 11 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SVar V_NS) (SLit 4095)) (SLit 18446744073709547520)) (SLit 8191)) (SLit 18446744073709547520)
  /\ nth 17 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SLit 222.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runSf (Wcan 0) UStopLe 2) = [(0x5e768, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertCallocSS.

(* [comment removed for export] *)
Module CertCallocSR.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "prod"; "false"; "option"; "true"; "list"; "bool"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "cell"; "sobj"; "mkCell"; "SAlu"; "SVar"; "SPUle"; "mkObj"; "DUnknown"; "ss_objs"; "SPAlign"; "ss_facts"; "SPBranch"; "DZero"; "SMd"; "SPNot"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "SPUlt"; "ss_next"; "ss_pc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "M_MUL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "leafA"; "cell_eqb"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "vK"; "F_pop"; "pcof"; "updR"; "vMU"; "nxt"; "rst"; "addobjs"; "vNEW"; "vAU"; "vNF"; "F_new"; "O_cell"; "nobj"; "vCHX"; "vMC"; "vMFA"; "F_r0"; "F_r1"; "LNX"; "LV3"; "PV4"; "PV6"; "beg1"; "beg2"; "choffK"; "keepn"; "sMS"; "vRI"; "F_x"; "GR"; "HINT_au"; "HINT_k"; "HINT_map"; "LV0"; "LV2"; "O_pccK"; "O_pckK"; "O_pcm"; "O_ri"; "PNX"; "PNX1"; "PV5"; "PV7"; "cE3a"; "cE3b"; "cR0a"; "idx_rot"; "rMS"; "req_e"; "ri_cells"; "rotM"; "selobjs"; "setobj"; "sh1"; "sh2"; "tMS"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_SIZE"; "pc_base"; "V_CLS"; "O_pcs"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vSB"; "vRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "gsv"; "shb"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA EntailA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Open Scope Z_scope.

Definition GR : positive := 240%positive.
Definition vMC : sv := SVar 220.  Definition vNF : sv := SVar 221.  Definition vMFA : sv := SVar 222.  Definition vAU : sv := SVar 223.
Definition vMU : sv := SVar 224.  Definition vRI : sv := SVar 225.  Definition vFA : sv := SVar 226.   Definition vK : sv := SVar 227.
Definition vNEW : sv := SVar 228.

Definition O_pcm : sobj := ltac2:(tb__ "0|2|
S15S6dScZ4M0A1M1ScZ8A1S0SfS11G1G0S41A3S1SfA1A3S16A5").
Definition O_pch : sobj := ltac2:(tb__ "0|0|
S15S6dScZ10A1ScZ50A1S1SfA1S16A5").

Definition ri_cells : list cell := ltac2:(tb__ "0|2|
S0SfS11ScZ0A1M0Z8M1G0A3S0SfS11ScZ10A1G1S3cA3S0SfS11ScZ18A1G1S42A3S0SfS11ScZ20A1G1S3bA3S0SfS11ScZ28A1G1G0A3S0SfS11ScZ30A1G1S36A3S0SfS11ScZ38A1G1G0A3S0SfS11ScZ44A1Z1G0A3S1SfA1A3A3A3A3A3A3A3A3").
Definition O_ri : sobj := ltac2:(tb__ "0|0|
S15S4eScZ0A1ScZ80A1S64S16A5").

Definition ri_e : sv := ltac2:(tb__ "0|0|
S12S28S7bS12S29S13S6eA1ScZ7A1A3A3").
Definition rb_e : sv := ltac2:(tb__ "0|0|
S12S28S7aS12S29S13S6eA1ScZ20A1A3A3").
Definition fa_e : sv := ltac2:(tb__ "0|0|
S12S28S7aS12S28S12S29S13S6eA1ScZ20A1A3ScZe0000000A1A3A3").
Definition k_e : sv := SAluW ALU_SRL vMC (SLit 1).

Definition F_r0 : list sprop := ltac2:(tb__ "0|0|
S0SdS14ScZ2A1S41A2S0SdS14S41ScZ10A1A2S1SdA1A3A3").
Definition F_r1 : list sprop := ltac2:(tb__ "0|0|
S0SdS18Pe1Z7A2S0SdS18Pe2ZcA2S0SdS14ScZ1A1S32A2S0SdS14S32ScZ8A1A2S0SdS14S3cScZ8000000A1A2S0SdS14S3bS36A2S0SdS18Pe0Z12A2S0SdS18P9bZ10A2S1SdA1A3A3A3A3A3A3A3A3").
Definition req_e : sv := SAlu ALU_SUB vK vNF.

Definition HINT_map : sprop := ltac2:(tb__ "0|0|
S1aS2aS36S12S28S3bS1cS2bS13S6cA1S63A3A3A3").

Definition runC (cutpcs : list Z) (C : axst) : list leafA := ltac2:(tb__ "0|1|
S7S9S2fA1M0A1G0Lx;S31S7fUfa0Vcutpcs;VC;S8A5G0R1Ll;S1S2fA1X7x2").

Definition updR (FR : list sprop) (E : axst) (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (reset : bool) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S2dVE;A1S24S2eVE;S1eVpc;S81S22R1A1Vru;A2S20R1A1S1fR1A1S23R1A1S4S10S17R1A1Vobjs;A3S4SdSaS9SdA1Lreset;Vreset;VFR;S19R1A1Xax2Vfacts;A3Vnx;S21R1A1A9A2TS;").
Definition nxt (E : axst) : positive := ss_next (ax_S E).
Definition pcof (E : axst) : Z := ss_pc (ax_S E).

Definition rst (FR : list sprop) (E : axst) (ru : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S35VFR;VE;S34VE;A1Vru;S1S10A1S8Vfacts;S37VE;A1A8").

Definition addobjs (E : axst) (objs : list sobj) (nx : positive) : axst := ltac2:(tb__ "0|0|
S2dVE;A1S24S2eVE;S1eS27R1A1S22R1A1S20R1A1S1fR1A1S23R1A1S4S10S17R1A1Vobjs;A3S19R1A1Vnx;S21R1A1A9A2TS;").

Definition keepn (E : axst) (n : nat) : axst := ltac2:(tb__ "0|1|
S2eVE;S74S2dVE;A1M0S75S10Vn;S17G0A1A3A2A2").

Definition setobj (E : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|2|
S2eVE;S74S2dVE;A1M0S4S10S75S10Vi;S17G0A1M1A3S0S10Vo;S77S10SbVi;A1G1A3A3A3A2A2").

Definition selobjs (E : axst) (idxs : list nat) : axst := ltac2:(tb__ "0|1|
S2eVE;S74S2dVE;A1M0S83S17G0A1Vidxs;A2A2A2").

Definition factsR (E3 : axst) : list sprop := ltac2:(tb__ "0|0|
S4SdS19S2dVE3;A1A1S4SdS43S44A3A3").

Definition F_pop : list sprop := ltac2:(tb__ "0|0|
S0SdS1aS2aS3cS32A3S0SdS53S0SdS14S36ScZdffc0000A1A2S1SdA1A3A3A3").
Definition F_new : list sprop := ltac2:(tb__ "0|0|
S0SdS14ScZ4A1S3aA2S0SdS14S3aScZ2001A1A2S0SdS14S42ScZ1ffc0000A1A2S0SdS18PdeZ12A2S1SdA1A3A3A3A3").

Definition HINT_au : sprop := ltac2:(tb__ "0|0|
S1dS1aS2aS12S28S36ScZ40000A1A3S12S28S3bS1cS2bS3aS13S6cA1A3A3A3A1").
Definition HINT_k : sprop := ltac2:(tb__ "0|0|
S1dS1aS2aS12S28S3cS3aA3S32A3A1").

Definition beg1 : sv := SAlu ALU_ADD vMU rb_e.
Definition O_up : sobj := ltac2:(tb__ "0|0|
S15S49ScZ0A1ScZ40000A1S1SfA1S1bA5").
Definition sh1 : sv := ltac2:(tb__ "0|0|
S12S28S7cS49A1S7dA3").
Definition O_sh1 : sobj := ltac2:(tb__ "0|0|
S15S68ScZ0A1ScZ8000A1S1SfA1S16A5").
Definition fa_e2 : sv := SAlu ALU_ADD rb_e (SLit 3758096384).
Definition beg2 : sv := SAlu ALU_ADD vMFA fa_e2.
Definition O_fp : sobj := ltac2:(tb__ "0|0|
S15S4aScZ0A1ScZ40000A1S1SfA1S1bA5").
Definition sh2 : sv := ltac2:(tb__ "0|0|
S12S28S7cS4aA1S7dA3").
Definition O_sh2 : sobj := ltac2:(tb__ "0|0|
S15S69ScZ0A1ScZ8000A1S1SfA1S16A5").

Definition cR0a (E3 : axst) : axst := ltac2:(tb__ "0|0|
S39VE3;S0S10S58S0S10S59S1S10A1A3A3S50A3").
Definition cR0 (E3 : axst) : axst := ltac2:(tb__ "0|0|
S79S60VE3;A1S4SdS19S2dVE3;A1A1S4SdS43S44A3A3A2").
Definition cR1 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU8S4eA4S0G0S3S2SeU14S6bA4S0G0S3S2SeUeS32A4S1G0A1A3A3A3S1SdA1A4").

Definition cPa (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU15S13S6cA1A4S1G0A1A3S33A4").
Definition cPb (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU15S13S6cA1A4S1G0A1A3S33A4").
Definition cP2 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU13ScZ40000A1A4S0G0S3S2SeU14S36A4S1G0A1A3A3S33A4").

Definition cP2c (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S35VFR;VE;S34VE;A1S0S5S2SeA2M0S3S2SeU13ScZ40000A1A4S0G0S3S2SeU14S36A4S0G0S3S2SeUbS13Pf1A1A4S0G0S3S2SeUfS13Pf5A1A4S0G0S3S2SeU10S13Pf6A1A4S1G0A1A3A3A3A3A3S1S10A1S8S33PfaA8").
Definition cX (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUaVeb;A4S1G1A1A3S1S10A1S6G0S37VE;A1A8").
Definition gX (C : axst) (eb : sv) (o : sobj) : axst := ltac2:(tb__ "0|1|
S2eVC;S82S2dVC;A1M0Veb;S4S10S17G0A1S0S10Vo;S1S10A1A3A3S26G0A1A4A2").
Definition cM (E : axst) (osh : sobj) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUcScZ8000A1A4S1G1A1A3S0S10Vosh;S1S10A1A3S6G0S37VE;A1A8").

Definition sMS (C : axst) : wsub := ltac2:(tb__ "0|0|
S78P1S2dVC;A1S2dS72A1A3").
Definition rMS (C : axst) : list sobj := ltac2:(tb__ "0|1|
S7S9S10A1M0A1G0Lx;S85VC;S72S4dVC;A1A3G0R1LR;S1S10A1X7x2").
Definition tMS (C : axst) : axst := ltac2:(tb__ "0|0|
S86S4dVC;A1S72S80S87S73A1A1VC;S62VC;A1A5").
Definition dMS (C : axst) : axst := ltac2:(tb__ "0|0|
S79S6aVC;A1S19S2dVC;A1A1A2").

Definition nobj (E : axst) : nat := length (ss_objs (ax_S E)).
Definition idx_rot (E : axst) : list nat := ltac2:(tb__ "0|1|
S4S2S76U1M0S70S3fVE;A1G0A2A2S0S2U0S1S2A1A3A3").
Definition rotM (E : axst) : axst := ltac2:(tb__ "0|0|
S66VE;S61VE;A1A2").
Definition relM (E : axst) : axst := ltac2:(tb__ "0|0|
S4cS65VE;A1S70S3fVE;A1U2A2A2").
Definition cD (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU13S3aA4S1G0A1A3S4SdS33S3dA3A4").
Definition cFm (E : axst) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeU8S12S28S42ScZ40000A1A3A4S1G1A1A3S1S10A1S6G0S37VE;A1A8").

Definition LV0 : positive := 400%positive. Definition LV2 : positive := 402%positive. Definition LV3 : positive := 403%positive.
Definition LNX : positive := 410%positive.
Definition O_cell (v : positive) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15S13Vv;A1ScZ0A1ScZ4A1Vcs;S16A5").
Definition cL0 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|2|
S35VFR;VE;S34VE;A1S0S5S2SeA2M0S3S2SeUaS13S54A1A4S0G0S3S2SeUcS13S55A1M1A4S0G0S3S2SeUeS12S2cG1ScZ4A1A3A4S0G0S3S2SeUfS13S46A1A4S1G0A1A3A3A3A3S1S10A1S8S4SdS33S3dA3S45A8").
Definition cL1 (C : axst) : axst := ltac2:(tb__ "0|0|
S39VC;S0S10S3eS46S1SfA1A2S1S10A1A3S45A3").
Definition cXL (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|0|
S38VFR;VE;S1S5S2SeA2A1S4SdS33S4SdS3dS0SdS51S0SdS52S1SdA1A3A3A3A3A4").

Definition PV4 : positive := 524%positive. Definition PV5 : positive := 525%positive. Definition PV6 : positive := 526%positive.
Definition PV7 : positive := 527%positive. Definition PNX : positive := 527%positive. Definition PNX1 : positive := 528%positive.
Definition cT0 (E : axst) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUdS13S47A1A4S0G1S3S2SeU14S13S48A1A4S0G1S3S2SeUcS13S5cA1A4S1G1A1A3A3A3S1S10A1S6G0S5aA8").
Definition cT1 (C : axst) : axst := ltac2:(tb__ "0|1|
S39VC;S0S10S3eS48S0SfS11ScZ0A1Z4S13S5dA1A3S1SfA1M0A3A2S0S10S3eS47G0A2S1S10A1A3A3S5bA3").

Definition vCHX : sv := SVar 229.
Definition choffK : sv := ltac2:(tb__ "0|0|
S12S28S12S29S12S28S32ScN1A1A3ScZ2A1A3ScZ10A1A3").
Definition O_pccK : sobj := ltac2:(tb__ "0|2|
S15S6dScZ0A1M0ScZ4M1A1S0SfS11G0G1S32A3S1SfA1A3S16A5").
Definition O_pckK : sobj := ltac2:(tb__ "0|0|
S15S6dS4bScZ50A1S0SfS11S4bZ4S40A3S1SfA1A3S16A5").
Definition F_x : list sprop := ltac2:(tb__ "0|0|
S0SdS25S40ScS8aZ2Z1cA2A1A2S1SdA1A3").
Definition s_exit (E Ep : axst) : wsub := ltac2:(tb__ "0|1|
S0S5S71SeA2M0S3S71SeP95S32A4S0G0S3S71SeP9fS40A4S78S7eS2dVE;A1S2dVEp;A1A3A3A3").

Definition cE1 (E : axst) (ic : nat) : axst := ltac2:(tb__ "0|0|
S67VE;Vic;S56A3").
Definition cE2 (E : axst) : axst := ltac2:(tb__ "0|0|
S4cVE;S70S3fVE;A1U2A2A2").
Definition cE3a (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S0S10S6fS1S10A1A3S37VE;A1A3").
Definition cE3b (E : axst) : axst := ltac2:(tb__ "0|0|
S39S5eVE;A1S0S10S57S1S10A1A3S37VE;A1A3").
Definition cE3 (E : axst) : axst := ltac2:(tb__ "0|0|
S84S4fS5fVE;A1A2").

Definition ri_has (cells : list cell) (e16 e24 e32 e48 : sv) : bool := ltac2:(tb__ "0|2|
S89SfSfS88SfS30R1A1Vcells;A3Lcc;S0SfS11ScZ0A1M0Z8M1G0A3S0SfS11ScZ10A1G1Ve16;A3S0SfS11ScZ18A1G1Ve24;A3S0SfS11ScZ20A1G1Ve32;A3S0SfS11ScZ28A1G1G0A3S0SfS11ScZ30A1G1Ve48;A3S0SfS11ScZ38A1G1G0A3S0SfS11ScZ44A1Z1G0A3S1SfA1A3A3A3A3A3A3A3A3A3").
End CertCallocSR.

(* [comment removed for export] *)
Module SecOKInv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "modulo"; "pow"; "sub"; "div"; "ge"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "alloc_top"; "event"; "m_vm_lazy"; "vm_noaccess"; "vm_reserved"; "region_free"; "vm_limit"; "with_vmmaps"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "app"; "cons"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "GN"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "FS_total"; "IMG_HI"; "IMG_LO"; "dyn_in"; "kPtrArrayReserve"; "kSpaceSize"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_V"; "aa_depot"; "aa_geom"; "aa_sec"; "sec_chunk"; "DG"; "aa_Kf"; "aa_Km"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "ageom"; "budget_ok_alloc"; "mkAA"; "sc_map_beg"; "sc_map_size"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "bumpV"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGS"; "JGs"; "SHC"; "JGsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "depot_vm"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bumpV (A : AA) (n : Z) : AA := ltac2:(tb__ "0|0|
S4fS38VA;A1S3fVA;A1S3eVA;A1S39VA;A1S44VA;A1S43VA;A1S46VA;A1S45VA;A1S37VA;A1S41VA;A1S40VA;A1S42VA;A1S5S36VA;A1Vn;A2S3dVA;A1S3cVA;A1Af").

Definition pendS (A : AA) (ua L : Z) (md : Model) : Prop := ltac2:(tb__ "0|6|
S38VA;A1S4dS1S33S1aS20Q40M0A1M1G1A2S19G1G1S21G0Vua;A2S21G0VL;A2A4SfSdVmd;A1A1A3S1S2S0S8Vua;S2cA2Z0M2A3S1S6G2VL;A2S1S30S52R1A1Vua;VL;A3S1S26S19S0S0Vua;VL;A4M3S19S0S0S4cR1A1Z1000M4A4A2S1S26G3S19S0S0S47R1A1G4A4A2S1S26G3S19S0S0S48R1A1G4A4A2S1S26G3S19S0S0S49R1A1S2dA4A2S1S26G3S19S0S0S4bR1A1S5S32G4A2A4A2S1S26G3S19S0S0S4aR1A1S31A4A2S1S3aS33S3aR1S39VA;A1A3S26G3S19S0S0S50R2A1S51R2A1A4A2F_;Fch;S1aS0S0A2M5S33G5R1S66S37VA;A1A1A3S26R2G3A2F_;Fbn;A2A2A2A2A2A2A2A2A2A2A2TG;").

Section S.
Let segs : list Segment := segsA.

Lemma depot_vm_grow : ltac2:(tb__ "0|6|
S3bSeSeS18S20Q40A1M0A1S1aG0G0A2M1S33G1R1SfSdR4A1M2A1M3A3S33G1R2G3A3F_;Fe;S2S18G1A1M4S12R3A1S12R4A1A3S2G4S13G2A1S13SdR5A1M5A1A3S2S0S10G5A1S10SdR6A1A1A3S65R8R7R5A3S65R9R7R6A3F_;F_;F_;F_;F_;Ftp;Fmd';Fmd;FG;").
Proof.
  intros G md md' tp Hm Hl Hna Htop [A B C D E F]. constructor.
  - intros bn Hbn. apply Hm. exact (A bn Hbn).
  - intros b Hb. rewrite Hl. exact (B b Hb).
  - intros b j Hb Hj. rewrite Hna. exact (C b j Hb Hj).
  - exact D.
  - intros bn Hbn. rewrite Htop. exact (E bn Hbn).
  - rewrite Htop. exact F.
Qed.

Lemma AInvA_sec_grant : ltac2:(tb__ "0|a|
S35S0S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1M3SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1M4A1A3A3S2G3S13G4A1S13SdR6A1M5A1A3S2G3S14G5A1S14SdR7A1M6A1A3S2S0S16G6A1S16SdR8A1M7A1A3S2S0S10G7A1S10SdR9A1A1A3S2G3S12R9A1S12RaA1A3S2S0S1fG0R8A2R7A3S6Z0R8A2S4R9S7Z2R10A2A2S4S27R11A2S2S1bS15S1dG2S14SdRfA1M8A1SfG8A1A3RdRcA3S1cA3S4S53RfR11A2S5S53R10R11A2RcA2A2S4S5S25S36R15A1M9A1RdA2S25S5G9R14A2A1A2S34Vsegs;R16R14R13R12A5S34Vsegs;S57R17R16A2R15R14R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;Fnv;FA;").
Proof.
  intros A nv rho tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL HL2 HGN Hfree Hpaid Hac (HG & HR & HF & HRest & HM & HI3 & HB).
  cbn [aa_geom bumpV] in *.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|].
  split.
  { unfold rest_inv in HRest |- *. cbn [aa_geom aa_live aa_cls aa_sec aa_ptr_committed aa_q_thread aa_q_global aa_depot aa_internal_inited aa_cache_inited aa_fs_busy aa_fs_hint bumpV] in HRest |- *.
    exact HRest. }
  split; [|exact (conj HI3 HB)].
  unfold model_inv, ledger_inv in HM |- *.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpV] in HM |- *.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split.
  { destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold vm_geom. cbn [aa_geom aa_sec bumpV]. rewrite Hna, Hlz.
    split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
    - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
    - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
    - exact G9. }
  split.
  { rewrite (PrimCredit.prim_credit_same A (bumpV A nv) eq_refl).
    unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV] in V2 |- *. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 Hpaid Hac. lia. }
  split; [rewrite Hlm; exact V3|]. split; [clear -V4 HGN; unfold GN in HGN; lia|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
  split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
  split.
  { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot bumpV] in L4 |- *.
    rewrite Hrs, Hvm. destruct L4 as [N4 S4].
    pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
    pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
    split; [clear -N4 IN HGN; unfold GN in *; nia | clear -S4 IS HL2; lia]. }
  split.
  { eapply depot_vm_grow; [| exact Hlz | exact Hna | exact Htop | exact L5]. intros e He. rewrite Hvm. right. exact He. }
  split; [exact L6|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

  destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
  intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
Qed.

Lemma pendS_intro : ltac2:(tb__ "0|6|
S35S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1A1A3A3S2S0S1fG0R3A2R2A3S4Z11c01R3A2S2S0S8S1fG0R6A2S2cA2Z0M3A3S6G3S1fG0R7A2A2S4S5S1fG0R8A2R6A2S10SdRaA1A1A2S0S1S4S1fG0RaA2M4R1A2S6R1S5G4R8A2A2A2S3S1S4S2fR2A2S6R2S2eA2A2A1F_;Fx;S2S1bS15S1dG2S14SdRcA1M5A1SfG5A1A3RaR9A3S1cA3S34Vsegs;R10RfReRdA5S58R11S1fG0RcA2RaRdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md md' a n L Hvm HnL HL Hal Hpos Hceil Himg Hfree (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  destruct HM as (VG & _ & _ & _ & _ & _ & V7 & L1 & L2 & L3 & L4 & L5 & _).
  destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A)) as TGR.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (ua, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  unfold pendS. cbn zeta.
  split. { rewrite Hvm. left. unfold ua. rewrite Z_to_bv_bv_unsigned. rewrite <- HnL, Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hal|]. split; [lia|].
  split.
  { assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
    { apply band_covered_app_r. exact L2. }
    pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
    rewrite HnL in W. unfold dyn_in. rewrite TG, <- V7. unfold IMG_LO, IMG_HI, PG in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact W].
    right. destruct (Z_lt_le_dec ua 6565888) as [Hlt|Hge]; [|exact Hge]. exfalso.
    destruct (Z_lt_le_dec ua 65536) as [X|X]; [apply (Himg 65536); lia | apply (Himg ua); lia]. }
  split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
  split; [apply APT; replace (ag_spacebeg (aa_geom A) + (kSpaceSize + 4096)) with (ag_spacebeg (aa_geom A) + kSpaceSize + 4096) by lia; exact G2|].
  split; [apply APT; exact G7|].
  split.
  - intros ch Hch. destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as (D1 & D2 & D3 & _).
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
  - intros bn Hbn. destruct L5 as [DVM _ _ _ DVT DR].
    pose proof (apart_of_region_free _ a n Hfree (wentry bn) ltac:(apply in_or_app; right; exact (DVM bn Hbn))) as X.
    pose proof (DVT bn Hbn) as T. destruct HRest as (_ & _ & _ & _ & _ & HD & _).
    assert (B : IMG_HI <= fst bn /\ 0 < snd bn).
    { unfold dblocks in Hbn. apply in_app_or in Hbn as [Hb|Hb]; apply in_map_iff in Hb as (b & <- & Hb); cbn [fst snd].
      - destruct (dm_nb _ _ HD b Hb) as (_ & Y & _). unfold NBSZ. split; [exact Y | lia].
      - destruct (dm_fbases _ _ HD b Hb) as (_ & Y & _). unfold FBSZ. split; [exact Y | lia]. }
    unfold wentry, apartW in X. cbn [fst snd] in X. unfold IMG_HI in B.
    rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.
End S.

Section JGS.
Variable W : list ulink. Variable st : ustop. Variable tmax : Z.
Let segs : list Segment := segsA.

Definition JGs (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S22S18S20Q40M0A1M1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S24S56S2bVA;Vrho;A2R5A3S1S2G1S23R5S55VW;Vst;Vtmax;A3A2Va;A3S1S34Vsegs;S57VA;R1A2R5R4R2A5S1S58VA;S1fG0Va;A2S29R1A1R2A4S1VKc;R3R2A2S1S60VA;R5A2S1S61VW;Vst;R5A3S1S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S1S5fVA;R5A2S4eVA;R1A2A2A2A2A2A2A2A2A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Definition SHC (nv : Z) : Z := ltac2:(tb__ "0|0|
S7S2cS5SbS29Vnv;A1S7Z8S2cA2A2Z2A2A2").
Definition JGsC (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|1|
S22S18S20Q40M0A1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S62VA;VKc;Vrho;Va;R5R4R3R2A8S4S5S5S53R2R4A2S69VA;A1A2S63R1A1A2S28S57VA;R1A2A1A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Lemma acost_step' : ltac2:(tb__ "0|1|
S0S0S4Z0R2A2M0G0ScS7Z4SaS25S5R4R3A2A1S25R4A1A2A2SaS7Z7R3A2Z3A2A2F_;F_;Fn;FV;").
Proof.
  intros V n HV Hn. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * (V + n) + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (V + n) + 4 - 1) 4 ltac:(lia)).
  pose proof (Z.div_mod (7 * V + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * V + 4 - 1) 4 ltac:(lia)). lia.
Qed.
Lemma acost_pays_map : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S25R4A1S29R3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS.
  assert (B : secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  lia.
Qed.

Lemma JGs_grant : ltac2:(tb__ "0|3|
S35S5dS22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S5eRbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S56S55VW;Vst;Vtmax;A3M2A2S1cA3S62R14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc [Hag HJ] HMI nv Hnv HnZ Hpl Hnx.
  pose proof Hag as (Hagw & Hagl & Hagm). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & _ & _ & _ & HM & _).
  pose proof HM as (_ & _ & _ & V0 & _ & _ & V7 & L1 & _).
  destruct (grant_facts_A addr flags md len a Hpl L1) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof Hpl as (_ & _ & _ & Gfree & _).
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  assert (NEQ : forall i, (i < GW)%positive -> i <> nxS W st tmax).
  { intros i Hi E. rewrite <- E in Hnx. apply Pos.leb_le in Hnx. exact (proj1 (Pos.lt_nle _ _) Hi Hnx). }
  set (h' := mmap_rw_vm (m_vmmaps md) len a). set (rho1 := rho_set_rw rhoX (nxS W st tmax) a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB, HN. rewrite E12 in HB, HN. fold nv in HB, HN.
  assert (Hag1 : agree_below GW rhoX rho1) by (unfold rho1; apply agree_below_set_rw; apply Pos.leb_le; exact Hnx).
  pose proof Hag1 as (A1w & A1l & A1m).
  assert (SMB : 72705 <= secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  unfold JGs. fold nv. cbn zeta.
  split.
  { split; [|split].
    - intros i Hi. rewrite (Hagw i Hi). apply A1w. exact Hi.
    - intros l. rewrite (Hagl l). apply A1l.
    - intros x. rewrite (Hagm x). apply A1m. }
  split; [unfold rho1; apply rho_set_rw_at|].
  split.
  { assert (Erm : rm rho1 = rm rhoX) by reflexivity.
    unfold AInvA. rewrite Erm. fold (AInvA segs (bumpV A nv) rhoX tp (with_vmmaps h' md)).
    refine (AInvA_sec_grant A nv rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv) _ _ _ _ _ _ En ltac:(lia) ltac:(lia) ltac:(unfold GN; lia) Gfree _ _ HA);
      rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try reflexivity.
    - rewrite paid_with_vmmaps.
      pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
      rewrite En in U. lia.
    - unfold budget_ok_alloc, limit_ok_alloc in HB. apply acost_pays_map; [exact V0 | lia]. }
  split.
  { apply (pendS_intro A rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv)); try assumption. clear -SMB. lia. }
  split.
  { replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity). apply HKc. exact HK. }
  split; [unfold tp_ok in Htp |- *; unfold rho1; rewrite rho_set_rw_other by (apply NEQ; unfold GW; lia); exact Htp|].
  split; [apply (HUS rhoX rho1); [eapply agree_below_le; [|exact Hag1]; unfold GW, NF; lia | exact HU]|].
  split; [exact Hnv|].
  split; [|exact HB].
  unfold top_high in Htop |- *. unfold rho1. rewrite !rho_set_rw_other by (apply NEQ; unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma secmapsize_bounds : ltac2:(tb__ "0|1|
S0S4Zfc01R1A2S1S1S4Z12000S29R2A1M0A2S4G0S5R2Z3007A2A2A2S2S0S8G0S2cA2Z0A3A2F_;Fnv;").
Proof.
  intros nv Hn. unfold secmapsize, secneeded, round_up, PG.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
  set (r8 := (nv + 8 - 1) / 8 * 8).
  pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)).
  split; [lia|]. rewrite Z.add_mod, Z_mod_mult by lia. reflexivity.
Qed.

Lemma SHC_pays : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S5S25R4A1S29R3A1A2S63R3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS. pose proof (secmapsize_bounds nv Hn) as [B _].
  unfold SHC, PG. pose proof (Z.div_mod (secmapsize nv) (8 * 4096) ltac:(lia)). pose proof (Z.mod_pos_bound (secmapsize nv) (8 * 4096) ltac:(lia)). lia.
Qed.

Lemma JGsC_grant : ltac2:(tb__ "0|3|
S35S5dS22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S5eRbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S56S55VW;Vst;Vtmax;A3M2A2S1cA3S64R14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI nv Hnv HnZ Hpl Hnx.
  split; [exact (JGs_grant A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI Hnv HnZ Hpl Hnx)|].
  destruct HJG as [Hag HJ]. pose proof Hag as (Hagw & _ & _). destruct HJ as (HA & _ & _ & _ & HB & _).
  pose proof HA as (_ & _ & _ & _ & HM & _). pose proof HM as (_ & V2 & _ & V0 & _ & _ & V7 & L1 & _).
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  set (h' := mmap_rw_vm (m_vmmaps md) len a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  rewrite paid_with_vmmaps.
  pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
  rewrite En in U.
  pose proof (SHC_pays (aa_V A) nv V0 ltac:(lia)) as SP.
  unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV]. fold nv. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 U SP. lia.
Qed.
End JGS.
End SecOKInv.

(* [comment removed for export] *)
Module CertMallocSU.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SVar"; "SLit"; "sprop"; "SPBranch"; "SPNot"; "sv"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "nat"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "rstS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import CertMallocST.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_g4 : list sprop := ltac2:(tb__ "0|1|
SaS5S7S6S1S2S0S3S10A1S2S0S3Vnx;A1M0S4Z1000A1A3A3S2S0S2S0G0S4Z1800A1A3S3PcA1A3A3A1S9S5A1A3").
End NX.

Definition DPENT : Z := 0x7e9e4.
Definition DPRET : Z := 0x3c720.
Definition U4p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S11VE;S9ScSbS8A2A1S13Vnx;A1A3").
Definition runT5 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
SfS14Ufa0SaSeS12S9SeA1A3VT;SdA5").
End CertMallocSU.

