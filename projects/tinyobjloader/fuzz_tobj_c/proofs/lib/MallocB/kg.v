(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp k3 ib.

(* [comment removed for export] *)
Module DepotCallMW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.DepotCallMW2.INST"; "T4_i"; "nobj_i"; "CP1"; "CP2"; "CP3"; "CP4"; "sd_1"; "sd_2"; "sd_3"; "sd_4"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "list"; "nil"; "option"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.DepotCallW"; "T40"; "T4a"; "T4b"; "T4c"; "T4d"; "T4m1"; "T4m2"; "T4m3"; "X4"; "X4a"; "X4b"; "X4c"; "X4r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C5"; "E4d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.DepotCallW.
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

(* [comment removed for export] *)
Module F0A_asm.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "prod"; "true"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "j_min"; "j_qb"; "j_qf"; "qcond"; "rhoF_of"; "j_st"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "AA"; "aa_internal_inited"; "aa_live"; "ag_thread"; "qbatch"; "topG"; "aa_q_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "AE_A"; "J_free_preT"; "KcA"; "Pre_freeI"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm"; "entry_pureF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot.
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
Module F0A_d0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A"; "ED_0A_1"; "ED_0A_2"; "q_0A"; "TD_0A_1"; "TD_0A_2"; "RD_0A_1"; "RD_0A_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma DCHK_0A_1 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ1M0S9ScS1fS9G0A2SeA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0A_1 : ltac2:(tb__ "0|1|
S6S2fScS2dS30S1fS9Z1M0A2S35G0A1S34G0A1S9SeA5S15S2eS9A1A1A2A3").
Proof. unfold TD_0A_1, TD_of, RD_0A_1; reflexivity. Qed.
Theorem hdf_0A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6S9ScR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_1 TD_0A_1 (sD_of ED_0A_1 1) RD_0A_1 HeD_0A_1 HchkD_0A_1 HTD_0A_1 DCHK_0A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0A_1 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6S9ScR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0A 1 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_1 TD_0A_1 (sD_of ED_0A_1 1) RD_0A_1 HeD_0A_1 HchkD_0A_1 HTD_0A_1 DCHK_0A_1
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

Lemma DCHK_0A_2 : ltac2:(tb__ "0|1|
S6S4S1bU0SbZ2M0SaSdS1fSaG0A2SfA7S5A3"). Proof. Time vmr. Qed.
Lemma HTD_0A_2 : ltac2:(tb__ "0|1|
S6S2fSdS2dS30S1fSaZ2M0A2S35G0A1S34G0A1SaSfA5S15S2eSaA1A1A2A3").
Proof. unfold TD_0A_2, TD_of, RD_0A_2; reflexivity. Qed.
Theorem hdf_0A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S12S17S8R2S16R11A1A3S31S8R3S16R12A1A3S32U0S22S18R19R18R14A3R4R14R13S1eR14R12RfReRdRcA6SaSdR3AaF_;F_;FQ;Fok;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp.
  exact (depot_call_HDF 0 q_0A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_2 TD_0A_2 (sD_of ED_0A_2 2) RD_0A_2 HeD_0A_2 HchkD_0A_2 HTD_0A_2 DCHK_0A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC ok Q Hok Hokp).
Qed.
Theorem hdfe_0A_2 : ltac2:(tb__ "0|3|
S1S3S0S0A2M0A1M1G1S26R2A1S28R2A1S0S27R5R1A2S7S29R2A1A1F_;Fa;S24S20S14S1S2bQ40M2A1A1S10S0S0S0S1cS21R8A1S23S8RaR8R7R6A5S2aG0S2S0S0R6R5A4S25RbA1A3S19R7R6A2S6S0S2cG2S13RbPcA2A2R8A3S1aReRcR9R8R7R6A6S1dSbRfA2S11OF_;S33U0S22S18R16R15R11A3R11R10S1eR11RfRcRbRaR9A6SaSdR1A9FQ;F_;F_;F_;F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd0;Ftp0;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HC HX HD A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q.
  exact (depot_call_HDFE 0 q_0A 2 CST XGL HC HX HD ltac:(unfold SZMAX; lia) ED_0A_2 TD_0A_2 (sD_of ED_0A_2 2) RD_0A_2 HeD_0A_2 HchkD_0A_2 HTD_0A_2 DCHK_0A_2
           A Kc rho tp0 md0 p n t jv HKc HA HL HHI Hp HTJ QC Q).
Qed.

End F0A_d0A.

(* [comment removed for export] *)
Module F0A_d0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be"; "ED_0Be_1"; "ED_0Be_2"; "q_0Be"; "TD_0Be_1"; "TD_0Be_2"; "RD_0Be_1"; "RD_0Be_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf"; "ED_0Bf_1"; "ED_0Bf_2"; "q_0Bf"; "TD_0Bf_1"; "TD_0Bf_2"; "RD_0Bf_1"; "RD_0Bf_2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A"; "q_1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "RD_1A_1"; "RD_1A_2"; "RD_1A_3"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "dchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "qcond"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "sD_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PostD"; "PreD"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A.
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

