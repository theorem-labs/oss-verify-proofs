(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7 aa.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From Stdlib Require NArith PArith FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.

(* [comment removed for export] *)
Module CertMallocSPd.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "leaf"; "C7"; "C7p"; "C8"; "C8p"; "C9a"; "C9b"; "C9pa"; "C9pb"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8a"; "E8b"; "E8pa"; "E8pb"; "run9a"; "run9b"; "run9pa"; "run9pb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd"; "F9a"; "F9b"; "F9pa"; "F9pb"; "vn0"; "vn1"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Open Scope Z_scope.

Definition vn1 (a : axst) : vnodeA := mkVNA a 1 (SLit 0).
Definition vn0 (a : axst) : vnodeA := mkVNA a 0 (SLit 0).
Definition cert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S6SbUfa0Vcutpcs;SaS0S8Vc;S1S8A1A3Ves;A6").
Definition ecert (cutpcs : list Z) (c : axst) (es : list axst) : bool := ltac2:(tb__ "0|0|
S7SbUfa0Vcutpcs;SaS0S4S29Vc;A1S1S4A1A3S2aS8S4S28Ves;A4A6").

Definition F9a (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
SeU0S20VW;Vst;Vtmax;A3A2").
Definition F9b (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
SeU0S21VW;Vst;Vtmax;A3A2").
Definition F9pa (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
SeU0S22VW;Vst;Vtmax;A3A2").
Definition F9pb (W : list ulink) (st : ustop) (tmax : Z) : axst := ltac2:(tb__ "0|0|
SeU0S23VW;Vst;Vtmax;A3A2").

Section INST.
Let W := Wcan 0. Let st := UStopLe. Let tmax := 2.
Lemma s7_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S0S9Z3c728S0S9Z3c870S1S9A1A3A3SaS0S8SfVW;Vst;Vtmax;A3S1S8A1M0A3S0S8S17VW;Vst;Vtmax;A3S0S8S18VW;Vst;Vtmax;A3S0S8S19VW;Vst;Vtmax;A3G0A3A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [0x3c728; 0x3c870] GW (C7 W st tmax) [E7c1 W st tmax; E7c2 W st tmax; E7p W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s7_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S0S9Z3c728S0S9Z3c870S1S9A1A3A3SaS0S4S5SfVW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S17VW;Vst;Vtmax;A3G0G1A3S0S4S5S18VW;Vst;Vtmax;A3G0G1A3S0S4S5S19VW;Vst;Vtmax;A3G0G1A3G2A3A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [0x3c728; 0x3c870] GW (mkVNA (C7 W st tmax) 1 (SLit 0)) [mkVNA (E7c1 W st tmax) 0 (SLit 0); mkVNA (E7c2 W st tmax) 0 (SLit 0); mkVNA (E7p W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s7p_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S0S9Z3c870S1S9A1A3SaS0S8S10VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S1aVW;Vst;Vtmax;A3S0S8S1bVW;Vst;Vtmax;A3G0A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [0x3c870] GW (C7p W st tmax) [E7q1 W st tmax; E7q2 W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7p); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7p, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s7p_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S0S9Z3c870S1S9A1A3SaS0S4S5S10VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S1aVW;Vst;Vtmax;A3G0G1A3S0S4S5S1bVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [0x3c870] GW (mkVNA (C7p W st tmax) 1 (SLit 0)) [mkVNA (E7q1 W st tmax) 0 (SLit 0); mkVNA (E7q2 W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7p); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run7p, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s8_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S8S11VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S1cVW;Vst;Vtmax;A3S0S8S1dVW;Vst;Vtmax;A3G0A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [0xde378; 0x3c8c0] GW (C8 W st tmax) [E8a W st tmax; E8b W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s8_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S4S5S11VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S1cVW;Vst;Vtmax;A3G0G1A3S0S4S5S1dVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [0xde378; 0x3c8c0] GW (mkVNA (C8 W st tmax) 1 (SLit 0)) [mkVNA (E8a W st tmax) 0 (SLit 0); mkVNA (E8b W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s8p_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S8S12VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S1eVW;Vst;Vtmax;A3S0S8S1fVW;Vst;Vtmax;A3G0A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [0xde378; 0x3c8c0] GW (C8p W st tmax) [E8pa W st tmax; E8pb W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8p); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8p, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s8p_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S0S9Zde378S0S9Z3c8c0S1S9A1A3A3SaS0S4S5S12VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S1eVW;Vst;Vtmax;A3G0G1A3S0S4S5S1fVW;Vst;Vtmax;A3G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [0xde378; 0x3c8c0] GW (mkVNA (C8p W st tmax) 1 (SLit 0)) [mkVNA (E8pa W st tmax) 0 (SLit 0); mkVNA (E8pb W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8p); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run8p, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9a_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S1S9A1SaS0S8S13VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S24VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [] GW (C9a W st tmax) [F9a W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9a); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9a_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S1S9A1SaS0S4S5S13VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S24VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [] GW (mkVNA (C9a W st tmax) 1 (SLit 0)) [mkVNA (F9a W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9a); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9b_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S1S9A1SaS0S8S14VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S25VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [] GW (C9b W st tmax) [F9b W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9b); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9b, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9b_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S1S9A1SaS0S4S5S14VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S25VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [] GW (mkVNA (C9b W st tmax) 1 (SLit 0)) [mkVNA (F9b W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9b); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9b, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9pa_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S1S9A1SaS0S8S15VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S26VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [] GW (C9pa W st tmax) [F9pa W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pa); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pa, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9pa_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S1S9A1SaS0S4S5S15VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S26VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [] GW (mkVNA (C9pa W st tmax) 1 (SLit 0)) [mkVNA (F9pa W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pa); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pa, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9pb_cert_0 : ltac2:(tb__ "0|1|
ScS2S6SbUfa0S1S9A1SaS0S8S16VW;Vst;Vtmax;A3S1S8A1M0A3S0S8S27VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA 4000%nat [] GW (C9pb W st tmax) [F9pb W st tmax] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pb); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
Lemma s9pb_ecert_0 : ltac2:(tb__ "0|3|
ScS2S7SbUfa0S1S9A1SaS0S4S5S16VW;Vst;Vtmax;A3Z1SdZ0M0A1M1A3S1S4A1M2A3S0S4S5S27VW;Vst;Vtmax;A3G0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA 4000%nat [] GW (mkVNA (C9pb W st tmax) 1 (SLit 0)) [mkVNA (F9pb W st tmax) 0 (SLit 0)] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pb); [ cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.m_run9pb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | cbv beta zeta delta [W st tmax F9a F9b F9pa F9pb]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc ]. Qed.
End INST.
End CertMallocSPd.

(* [comment removed for export] *)
Module SegQIP_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "true"; "nil"; "pair"; "false"; "prod"; "list"; "app"; "None"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sobj"; "ss_next"; "SVar"; "ss_lenient"; "SPUle"; "ss_facts"; "SPBranch"; "SPAlign"; "sprop_below"; "sprop_eqb"; "SPNot"; "FcsrFrm0"; "mkSS"; "swf"; "SAlu"; "SExt"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "axwf"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "NPRE"; "vSB"; "add"; "vST"; "DEPTH_Q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "updQ"; "vCLS"; "NXI"; "QI1"; "QCENTI"; "MSENTQ"; "PSENT"; "QI0"; "QI2"; "QI3"; "vSZ"; "vN8"; "XF"; "bgv"; "LENq"; "O_cb"; "O_hdrI"; "O_ish"; "O_rie"; "O_stq"; "RTI"; "XOBJ"; "dI0"; "dI1a"; "dI1b"; "dI2"; "dI3"; "dI4"; "dI5"; "dI6"; "optR"; "regsI"; "updF"; "vHW"; "NXQI"; "QIENT"; "cacheI"; "hw'"; "kAllocBegMagic"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "sdiff"; "one_at"; "entsI"; "two_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states"; "pC5a"; "pC5b"; "PreQIP"; "pC1a"; "pC1b"; "pE1ba"; "pE1bb"; "ps5a"; "ps5b"; "F_QIP"; "pC0a"; "pC0b"; "pC2a"; "pC2b"; "pC3a"; "pC3b"; "pC4a"; "pC4b"; "pE1aa"; "pE1ab"; "pR5a"; "pR5b"; "prun1a"; "prun1b"; "PostQIP"; "pC6a"; "pC6b"; "pE0a"; "pE0b"; "pE2a"; "pE2b"; "pE3a"; "pE3b"; "pE4a"; "pE4b"; "pE5a"; "pE5b"; "pE6a"; "pE6b"; "pT5a"; "pT5b"; "pT5fa"; "pT5fb"; "prun0a"; "prun0b"; "prun2a"; "prun2b"; "prun3a"; "prun3b"; "prun4a"; "prun4b"; "prun5a"; "prun5b"; "prun6a"; "prun6b"; "pE1aa'"; "pE1ab'"; "pE1ba'"; "pE1bb'"; "ALLOC_I"; "OBJS_IP"; "post_ruP"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "ALU_AND"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "mkA"; "stack_win"; "pre_facts"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "vRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_SIZE"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition F_QIP : list sprop := ltac2:(tb__ "0|9|
S9S12Sb2S30A1S9S12Sb5S0S12S1bPdM0Z4M1A2S0S12S1bPcZ3M2A2S0S12S1bP9bZ10M3A2S0S12S18S13SaeA1S2dA2S0S12S18S2dS13Sb3Sb3Z7fffff800000M4SadA2Z1000A2A1A2S0S12S1aS9fSb6S2eS2dS13SadA1A2M5A3S0S12S18S13Z1A1S32A2S0S12S18S32S13Z1eA1A2S0S12S18S13G3A1M6S3bA2S0S12S18S3bS13Z10000A1A2S0S12S1bSb7G1A2S0S12S18S2dS16G0A1M7A2S0S12S24G7G5A2S0S12S1eS1aSa0S22S9eS23S3Q20S52A3S13ZffA1A3S13G2A1A3A1S0S12S18S13Z8A1S3cA2S0S12S18S3cS13Sb4Z2Z28A2A1A2S0S12S1bP91G2A2S0S12S18S2eS2eG7G6A2S3cA2M8G5A2S0S12S18G8S13G4A1A2S4S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition OBJS_IP (hw : sv) (st : sv) : list sobj := ltac2:(tb__ "0|0|
S9S14S0S14Sb1SafA3S9S14S45S0S14S40S0S14S43S0S14S41Vhw;A1S0S14S42S0S14S44Vst;A1S4S14A1A3A3A3A3A3A3A3").
Definition PreQIP (vb : bool) : axst := ltac2:(tb__ "0|0|
Sb0S20S54S50Sa9S1fSaS11A1S9S14S9bS52S2fA2S46Vvb;S13S57A1A2A3S9S12S68S3dVvb;A1A3S2cS6A9S4S7S11S11A2A1A2").
Lemma preQIP_wf : ltac2:(tb__ "0|2|
S1S10SfS1S28S61R1A1M0A1S3A3S10SfS1S21S25G0A1M1A1S3A3S10SfSeS15G1A1S2cA3SfS1S17G1A1S6A3A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition prun0a : list leafA := ltac2:(tb__ "0|0|
S2aU12cS0SdS38S0SdZ3e63cS4SdA1A3A3S61S6A1A3").
Definition pE0a : axst := leaf 0 prun0a.
Definition pC0a : axst := ltac2:(tb__ "0|1|
S31S7aS38S0S7S2S11A2M0S5S2S11UcS32A4S0G0S5S2S11UdS32A4S4G0A1A3A3A3").
Definition prun1a : list leafA := ltac2:(tb__ "0|0|
S2aU12cS0SdS34S0SdZ3e63cS0SdZ3e810S0SdZ3e804S4SdA1A3A3A3A3S69A3").
Definition pE1aa : axst := leaf 0 prun1a.
Definition pE1ba : axst := leaf 1 prun1a.
Definition pE1aa' : axst := ltac2:(tb__ "0|1|
S31S71S34S0S7S2S11A2M0S5S2S11UfS3bA4S4G0A1A3A3").
Definition pE1ba' : axst := ltac2:(tb__ "0|1|
S31S64S34S0S7S2S11A2M0S5S2S11UfS3bA4S4G0A1A3A3").
Definition pC1a : axst := ltac2:(tb__ "0|1|
S51S64S34S0S7S2S11A2M0S5S2S11UfS3bA4S0G0S5S2S11U10S16Pb9A1A4S0G0S5S2S11U11S16PbaA1A4S4G0A1A3A3A3S9S12S68S3dS6A1A3S33A5").
Definition prun2a : list leafA := ltac2:(tb__ "0|0|
S2aU12cS0SdS39S4SdA1A3S62A3").
Definition pE2a : axst := leaf 0 prun2a.
Definition pC2a : axst := ltac2:(tb__ "0|1|
S31S7cS39S0S7S2S11A2M0S5S2S11U12S3eS6A1A4S4G0A1A3A3").
Definition prun3a : list leafA := ltac2:(tb__ "0|0|
S2aU258S0SdS3aS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS4SdA1A3A3A3A3S6bA3").
Definition pE3a : axst := leaf 0 prun3a.
Definition pC3a : axst := ltac2:(tb__ "0|1|
S31S7eS3aS0S7S2S11A2M0S5S2S11UdS13Z3A1A4S0G0S5S2S11UeS13ZffA1A4S4G0A1A3A3A3").
Definition prun4a : list leafA := ltac2:(tb__ "0|0|
S2aU320S0SdS37S0SdZ3e818S4SdA1A3A3S6dA3").
Definition pE4a : axst := leaf 0 prun4a.
Definition pC4a : axst := ltac2:(tb__ "0|1|
S31S80S37S0S7S2S11A2M0S5S2S11UbS3cA4S4G0A1A3A3").
Definition prun5a : list leafA := ltac2:(tb__ "0|0|
S2aU320S0SdS36S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S4SdA1A3A3A3A3A3A3A3S6fA3").
Definition pE5a : axst := leaf 0 prun5a.
Definition pC5a : axst := ltac2:(tb__ "0|1|
S31S82S36S0S7S2S11A2M0S5S2S11UcS3fA4S4G0A1A3A3").
Definition ps5a : wsub := ltac2:(tb__ "0|0|
SabP1S25S5fA1S25S5cA1A3").
Definition pR5a : list sobj := ltac2:(tb__ "0|0|
S4fSa2S5fS5cS66A3A1").
Definition pT5a : axst := ltac2:(tb__ "0|0|
Sa3S66S5cSa1Sa5S5dA1A1S5fS73A5").
Definition pT5fa : axst := ltac2:(tb__ "0|0|
SacS86S19S25S5fA1A1A2").
Definition prun6a : list leafA := ltac2:(tb__ "0|0|
S2aU320S0SdS35S0SdZ3e7b8S0SdZ3e7d8S4SdA1A3A3A3S88A3").
Definition pE6a : axst := leaf 0 prun6a.
Definition pC6a : axst := ltac2:(tb__ "0|1|
S31S84S35S0S7S2S11A2M0S5S2S11UcS32A4S4G0A1A3A3").

Lemma prun0a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU12cS0SdS38S0SdZ3e63cS4SdA1A3A3S61S6A1A3S8aA3"). Proof. unfold prun0a. reflexivity. Qed.
Lemma pchk0a : ltac2:(tb__ "0|0|
SfS1S59S8aS38A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd0a : ltac2:(tb__ "0|0|
SfS1S58S7aS69S47A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun1a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU12cS0SdS34S0SdZ3e63cS0SdZ3e810S0SdZ3e804S4SdA1A3A3A3A3S69A3S75A3"). Proof. unfold prun1a. reflexivity. Qed.
Lemma pchk1a : ltac2:(tb__ "0|0|
SfS1S5bS75S34A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd1aa : ltac2:(tb__ "0|0|
SfS1S58S71S96S48A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd1ba : ltac2:(tb__ "0|0|
SfS1S58S64S98S49A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pent1aa : ltac2:(tb__ "0|0|
SfS1S5aS96S62A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pent1ba : ltac2:(tb__ "0|0|
SfS1S5aS98S62A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pbr1aa : ltac2:(tb__ "0|0|
SfS1Sa6S12S1dS1aS9dS32S13Z11A1A3A1S19S25S71A1A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pbr1ba : ltac2:(tb__ "0|0|
SfS1Sa6S12S1dS1eS1aS9dS32S13Z11A1A3A1A1S19S25S64A1A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun2a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU12cS0SdS39S4SdA1A3S62A3S8cA3"). Proof. unfold prun2a. reflexivity. Qed.
Lemma pchk2a : ltac2:(tb__ "0|0|
SfS1S59S8cS39A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd2a : ltac2:(tb__ "0|0|
SfS1S58S7cS6bS4aS6A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun3a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU258S0SdS3aS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS4SdA1A3A3A3A3S6bA3S8eA3"). Proof. unfold prun3a. reflexivity. Qed.
Lemma pchk3a : ltac2:(tb__ "0|0|
SfS1S59S8eS3aA2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd3a : ltac2:(tb__ "0|0|
SfS1S58S7eS6dS4bA3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun4a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU320S0SdS37S0SdZ3e818S4SdA1A3A3S6dA3S90A3"). Proof. unfold prun4a. reflexivity. Qed.
Lemma pchk4a : ltac2:(tb__ "0|0|
SfS1S59S90S37A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd4a : ltac2:(tb__ "0|0|
SfS1S58S80S6fS4cA3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun5a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU320S0SdS36S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S4SdA1A3A3A3A3A3A3A3S6fA3S92A3"). Proof. unfold prun5a. reflexivity. Qed.
Lemma pchk5a : ltac2:(tb__ "0|0|
SfS1S59S92S36A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd5a : ltac2:(tb__ "0|0|
SfS1S58S82S5fS4dA3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pHe5a : ltac2:(tb__ "0|1|
SfScS8S14A1M0A1Sa2S5fS5cS66A3SbG0S73A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pHchk5a : ltac2:(tb__ "0|0|
SfS1Sa4S5fS5cS66S73Sa8S27S26S29S5eA4A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pHT5a : ltac2:(tb__ "0|0|
SfS26Sa3S66S5cSa1Sa5S5dA1A1S5fS73A5S86A3"). Proof. unfold pT5a. reflexivity. Qed.
Lemma pFBC5a : ltac2:(tb__ "0|1|
SfS1Sa7S12S1cS15S25S5fA1M0A1A1S19G0A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pFBT5a : ltac2:(tb__ "0|0|
SfS1Sa7S12S1cS15S25S86A1A1A1S19S25S5fA1A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun6a_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU320S0SdS35S0SdZ3e7b8S0SdZ3e7d8S4SdA1A3A3A3S88A3S94A3"). Proof. unfold prun6a. reflexivity. Qed.
Lemma pchk6a : ltac2:(tb__ "0|0|
SfS1S59S94S35A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd6a : ltac2:(tb__ "0|0|
SfS1S58S84S78S4eS6A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pnxC0a : ltac2:(tb__ "0|1|
S10SfSeS15S25S69A1M0A1S2cA3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC1a : ltac2:(tb__ "0|1|
S10SfSeS15S25S62A1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC2a : ltac2:(tb__ "0|1|
S10SfSeS15S25S6bA1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC3a : ltac2:(tb__ "0|1|
S10SfSeS15S25S6dA1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC4a : ltac2:(tb__ "0|1|
S10SfSeS15S25S6fA1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC5a : ltac2:(tb__ "0|1|
S10SfSeS15S25S5fA1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxT5fa : ltac2:(tb__ "0|1|
S10SfSeS15S25S88A1M0A1Pf0A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC6a : ltac2:(tb__ "0|1|
S10SfSeS15S25S78A1M0A1Pf2A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pE0a_def : ltac2:(tb__ "0|0|
SfS26S2bU0S8aA2S7aA3"). Proof. unfold pE0a. reflexivity. Qed.
Lemma pE1aa_def : ltac2:(tb__ "0|0|
SfS26S2bU0S75A2S71A3"). Proof. unfold pE1aa. reflexivity. Qed.
Lemma pE1ba_def : ltac2:(tb__ "0|0|
SfS26S2bU1S75A2S64A3"). Proof. unfold pE1ba. reflexivity. Qed.
Lemma pE2a_def : ltac2:(tb__ "0|0|
SfS26S2bU0S8cA2S7cA3"). Proof. unfold pE2a. reflexivity. Qed.
Lemma pE3a_def : ltac2:(tb__ "0|0|
SfS26S2bU0S8eA2S7eA3"). Proof. unfold pE3a. reflexivity. Qed.
Lemma pE4a_def : ltac2:(tb__ "0|0|
SfS26S2bU0S90A2S80A3"). Proof. unfold pE4a. reflexivity. Qed.
Lemma pE5a_def : ltac2:(tb__ "0|0|
SfS26S2bU0S92A2S82A3"). Proof. unfold pE5a. reflexivity. Qed.
Lemma pE6a_def : ltac2:(tb__ "0|0|
SfS26S2bU0S94A2S84A3"). Proof. unfold pE6a. reflexivity. Qed.

Definition prun0b : list leafA := ltac2:(tb__ "0|0|
S2aU12cS0SdS38S0SdZ3e63cS4SdA1A3A3S61S3A1A3").
Definition pE0b : axst := leaf 0 prun0b.
Definition pC0b : axst := ltac2:(tb__ "0|1|
S31S7bS38S0S7S2S11A2M0S5S2S11UcS32A4S0G0S5S2S11UdS32A4S4G0A1A3A3A3").
Definition prun1b : list leafA := ltac2:(tb__ "0|0|
S2aU12cS0SdS34S0SdZ3e63cS0SdZ3e810S0SdZ3e804S4SdA1A3A3A3A3S6aA3").
Definition pE1ab : axst := leaf 0 prun1b.
Definition pE1bb : axst := leaf 1 prun1b.
Definition pE1ab' : axst := ltac2:(tb__ "0|1|
S31S72S34S0S7S2S11A2M0S5S2S11UfS3bA4S4G0A1A3A3").
Definition pE1bb' : axst := ltac2:(tb__ "0|1|
S31S65S34S0S7S2S11A2M0S5S2S11UfS3bA4S4G0A1A3A3").
Definition pC1b : axst := ltac2:(tb__ "0|1|
S51S65S34S0S7S2S11A2M0S5S2S11UfS3bA4S0G0S5S2S11U10S16Pb9A1A4S0G0S5S2S11U11S16PbaA1A4S4G0A1A3A3A3S9S12S68S3dS3A1A3S33A5").
Definition prun2b : list leafA := ltac2:(tb__ "0|0|
S2aU12cS0SdS39S4SdA1A3S63A3").
Definition pE2b : axst := leaf 0 prun2b.
Definition pC2b : axst := ltac2:(tb__ "0|1|
S31S7dS39S0S7S2S11A2M0S5S2S11U12S3eS3A1A4S4G0A1A3A3").
Definition prun3b : list leafA := ltac2:(tb__ "0|0|
S2aU258S0SdS3aS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS4SdA1A3A3A3A3S6cA3").
Definition pE3b : axst := leaf 0 prun3b.
Definition pC3b : axst := ltac2:(tb__ "0|1|
S31S7fS3aS0S7S2S11A2M0S5S2S11UdS13Z3A1A4S0G0S5S2S11UeS13ZffA1A4S4G0A1A3A3A3").
Definition prun4b : list leafA := ltac2:(tb__ "0|0|
S2aU320S0SdS37S0SdZ3e818S4SdA1A3A3S6eA3").
Definition pE4b : axst := leaf 0 prun4b.
Definition pC4b : axst := ltac2:(tb__ "0|1|
S31S81S37S0S7S2S11A2M0S5S2S11UbS3cA4S4G0A1A3A3").
Definition prun5b : list leafA := ltac2:(tb__ "0|0|
S2aU320S0SdS36S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S4SdA1A3A3A3A3A3A3A3S70A3").
Definition pE5b : axst := leaf 0 prun5b.
Definition pC5b : axst := ltac2:(tb__ "0|1|
S31S83S36S0S7S2S11A2M0S5S2S11UcS3fA4S4G0A1A3A3").
Definition ps5b : wsub := ltac2:(tb__ "0|0|
SabP1S25S60A1S25S5cA1A3").
Definition pR5b : list sobj := ltac2:(tb__ "0|0|
S4fSa2S60S5cS67A3A1").
Definition pT5b : axst := ltac2:(tb__ "0|0|
Sa3S67S5cSa1Sa5S5dA1A1S60S74A5").
Definition pT5fb : axst := ltac2:(tb__ "0|0|
SacS87S19S25S60A1A1A2").
Definition prun6b : list leafA := ltac2:(tb__ "0|0|
S2aU320S0SdS35S0SdZ3e7b8S0SdZ3e7d8S4SdA1A3A3A3S89A3").
Definition pE6b : axst := leaf 0 prun6b.
Definition pC6b : axst := ltac2:(tb__ "0|1|
S31S85S35S0S7S2S11A2M0S5S2S11UcS32A4S4G0A1A3A3").

Lemma prun0b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU12cS0SdS38S0SdZ3e63cS4SdA1A3A3S61S3A1A3S8bA3"). Proof. unfold prun0b. reflexivity. Qed.
Lemma pchk0b : ltac2:(tb__ "0|0|
SfS1S59S8bS38A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd0b : ltac2:(tb__ "0|0|
SfS1S58S7bS6aS47A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun1b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU12cS0SdS34S0SdZ3e63cS0SdZ3e810S0SdZ3e804S4SdA1A3A3A3A3S6aA3S76A3"). Proof. unfold prun1b. reflexivity. Qed.
Lemma pchk1b : ltac2:(tb__ "0|0|
SfS1S5bS76S34A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd1ab : ltac2:(tb__ "0|0|
SfS1S58S72S97S48A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd1bb : ltac2:(tb__ "0|0|
SfS1S58S65S99S49A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pent1ab : ltac2:(tb__ "0|0|
SfS1S5aS97S63A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pent1bb : ltac2:(tb__ "0|0|
SfS1S5aS99S63A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pbr1ab : ltac2:(tb__ "0|0|
SfS1Sa6S12S1dS1aS9dS32S13Z11A1A3A1S19S25S72A1A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pbr1bb : ltac2:(tb__ "0|0|
SfS1Sa6S12S1dS1eS1aS9dS32S13Z11A1A3A1A1S19S25S65A1A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun2b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU12cS0SdS39S4SdA1A3S63A3S8dA3"). Proof. unfold prun2b. reflexivity. Qed.
Lemma pchk2b : ltac2:(tb__ "0|0|
SfS1S59S8dS39A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd2b : ltac2:(tb__ "0|0|
SfS1S58S7dS6cS4aS3A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun3b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU258S0SdS3aS0SdZ3e818S0SdZ3e83cS0SdZ3e73cS4SdA1A3A3A3A3S6cA3S8fA3"). Proof. unfold prun3b. reflexivity. Qed.
Lemma pchk3b : ltac2:(tb__ "0|0|
SfS1S59S8fS3aA2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd3b : ltac2:(tb__ "0|0|
SfS1S58S7fS6eS4bA3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun4b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU320S0SdS37S0SdZ3e818S4SdA1A3A3S6eA3S91A3"). Proof. unfold prun4b. reflexivity. Qed.
Lemma pchk4b : ltac2:(tb__ "0|0|
SfS1S59S91S37A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd4b : ltac2:(tb__ "0|0|
SfS1S58S81S70S4cA3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun5b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU320S0SdS36S0SdZ3e73cS0SdZ5fa44S0SdZ5fa24S0SdZ5fa64S0SdZ5fa84S0SdZ5fa04S4SdA1A3A3A3A3A3A3A3S70A3S93A3"). Proof. unfold prun5b. reflexivity. Qed.
Lemma pchk5b : ltac2:(tb__ "0|0|
SfS1S59S93S36A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd5b : ltac2:(tb__ "0|0|
SfS1S58S83S60S4dA3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pHe5b : ltac2:(tb__ "0|1|
SfScS8S14A1M0A1Sa2S60S5cS67A3SbG0S74A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pHchk5b : ltac2:(tb__ "0|0|
SfS1Sa4S60S5cS67S74Sa8S27S26S29S5eA4A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pHT5b : ltac2:(tb__ "0|0|
SfS26Sa3S67S5cSa1Sa5S5dA1A1S60S74A5S87A3"). Proof. unfold pT5b. reflexivity. Qed.
Lemma pFBC5b : ltac2:(tb__ "0|1|
SfS1Sa7S12S1cS15S25S60A1M0A1A1S19G0A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pFBT5b : ltac2:(tb__ "0|0|
SfS1Sa7S12S1cS15S25S87A1A1A1S19S25S60A1A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prun6b_eq : ltac2:(tb__ "0|0|
SfS8S27A1S2aU320S0SdS35S0SdZ3e7b8S0SdZ3e7d8S4SdA1A3A3A3S89A3S95A3"). Proof. unfold prun6b. reflexivity. Qed.
Lemma pchk6b : ltac2:(tb__ "0|0|
SfS1S59S95S35A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma psd6b : ltac2:(tb__ "0|0|
SfS1S58S85S79S4eS3A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pnxC0b : ltac2:(tb__ "0|1|
S10SfSeS15S25S6aA1M0A1S2cA3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC1b : ltac2:(tb__ "0|1|
S10SfSeS15S25S63A1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC2b : ltac2:(tb__ "0|1|
S10SfSeS15S25S6cA1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC3b : ltac2:(tb__ "0|1|
S10SfSeS15S25S6eA1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC4b : ltac2:(tb__ "0|1|
S10SfSeS15S25S70A1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC5b : ltac2:(tb__ "0|1|
S10SfSeS15S25S60A1M0A1S33A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxT5fb : ltac2:(tb__ "0|1|
S10SfSeS15S25S89A1M0A1Pf0A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pnxC6b : ltac2:(tb__ "0|1|
S10SfSeS15S25S79A1M0A1Pf2A3SfS1S17G0A1S6A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pE0b_def : ltac2:(tb__ "0|0|
SfS26S2bU0S8bA2S7bA3"). Proof. unfold pE0b. reflexivity. Qed.
Lemma pE1ab_def : ltac2:(tb__ "0|0|
SfS26S2bU0S76A2S72A3"). Proof. unfold pE1ab. reflexivity. Qed.
Lemma pE1bb_def : ltac2:(tb__ "0|0|
SfS26S2bU1S76A2S65A3"). Proof. unfold pE1bb. reflexivity. Qed.
Lemma pE2b_def : ltac2:(tb__ "0|0|
SfS26S2bU0S8dA2S7dA3"). Proof. unfold pE2b. reflexivity. Qed.
Lemma pE3b_def : ltac2:(tb__ "0|0|
SfS26S2bU0S8fA2S7fA3"). Proof. unfold pE3b. reflexivity. Qed.
Lemma pE4b_def : ltac2:(tb__ "0|0|
SfS26S2bU0S91A2S81A3"). Proof. unfold pE4b. reflexivity. Qed.
Lemma pE5b_def : ltac2:(tb__ "0|0|
SfS26S2bU0S93A2S83A3"). Proof. unfold pE5b. reflexivity. Qed.
Lemma pE6b_def : ltac2:(tb__ "0|0|
SfS26S2bU0S95A2S85A3"). Proof. unfold pE6b. reflexivity. Qed.

Definition ALLOC_I : Z := 0xedd98.
Definition post_ruP (vb : bool) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S7S2S11A2M0S5S2S11U0S16Pb8A1A4S0G0S5S2S11U5S16Pb9A1A4S0G0S5S2S11U6S16PbaA1A4S0G0S5S2S11U7S16PbbA1A4S0G0S5S2S11UeS16Pc0A1A4S0G0S5S2S11UfS16Pc1A1A4S0G0S5S2S11U10S16Pc2A1A4S0G0S5S2S11U11S16Pc3A1A4S0G0S5S2S11U1cS16Pc4A1A4S0G0S5S2S11U1dS16Pc5A1A4S0G0S5S2S11U1eS16Pc6A1A4S0G0S5S2S11U1fS16Pc7A1A4S0G0S5S2S11UaS55A4S0G0S5S2S11UbS13S9aA1A4S0G0S5S2S11UcS32A4S0G0S5S2S11UdS3eVvb;A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PostQIP (vb : bool) : axst := ltac2:(tb__ "0|0|
Sb0S20S35SaaS50S9cVvb;A1A2Sa9S1fSaS11A1S0S14S42S9S14S0S14Sb1SafA3S9S14S45S9S14S0S14S40S0S14S43S0S14S41S56A1S0S14S44S2fA1S4S14A1A3A3A3A3S46Vvb;S13Z0A1A2A3A3A3A3S9S12S68S3dVvb;A1A3S53S6A9S4S7S11S11A2A1A2").
Lemma pent6a : ltac2:(tb__ "0|0|
SfS1S5aS78S77S6A1A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pent6b : ltac2:(tb__ "0|0|
SfS1S5aS79S77S3A1A2S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma postQIP_wf : ltac2:(tb__ "0|1|
S1S10SfS1S28S77R1A1M0A1S3A3SfS1S21S25G0A1A1S3A3A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SegQIP_states.

(* [comment removed for export] *)
Module SegQI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "false"; "pair"; "prod"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "stableA_mono"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "ss_next"; "ss_lenient"; "ss_facts"; "rw"; "sprop"; "SLit"; "SPBranch"; "sprop_below"; "sprop_eqb"; "SPNot"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "sdiff"; "one_at"; "JQ"; "entsI"; "two_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "NXI"; "PreQI"; "PostQI"; "dI0"; "dI1a"; "dI1b"; "dI2"; "dI3"; "dI4"; "dI5"; "dI6"; "MSENTQ"; "PSENT"; "QCENTI"; "QI0"; "QI1"; "QI2"; "QI3"; "vCLS"; "QIRET"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI"; "le_NPRE_240"; "le_NPRE_242"; "le_NPRE_NXI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Lemma le_NPRE_NXI : (NPRE <= NXI)%positive. Proof. unfold NPRE, NXI, Pos.le. cbn. discriminate. Qed.
Lemma le_NPRE_240 : (NPRE <= 240)%positive. Proof. unfold NPRE, Pos.le. cbn. discriminate. Qed.
Lemma le_NPRE_242 : (NPRE <= 242)%positive. Proof. unfold NPRE, Pos.le. cbn. discriminate. Qed.

Section QI.

Variable vb : bool.
Variables (run0 run1 run2 run3 run4 run5 run6 run7 : list leafA).
Variables (E0 C0 E1a E1b E1a' E1b' C1 E2 C2 E3 C3 E4 C4 E5 C5 T5 T5f E6 C6 E7 : axst) (s5 : wsub) (R5 : list sobj).
Hypothesis run0_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U12cS6S3S44S6S3Z3e63cS9S3A1A3A3S37Vvb;A1A3Vrun0;A3").
Hypothesis chk0 : ltac2:(tb__ "0|0|
S0S5S2dVrun0;S44A2S7A3").
Hypothesis E0_def : leaf 0 run0 = E0.
Hypothesis sd0 : ltac2:(tb__ "0|0|
S0S5S2cVE0;VC0;S39A3S7A3").
Hypothesis C0_def : ltac2:(tb__ "0|0|
S0S12S14VE0;S11VC0;A1A2VC0;A3").
Hypothesis nxC0 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC0;A1M0A1SfA3S0S5S1eG0A1SaA3A2").
Hypothesis run1_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U12cS6S3S45S6S3Z3e63cS6S3Z3e810S6S3Z3e804S9S3A1A3A3A3A3VC0;A3Vrun1;A3").
Hypothesis chk1 : ltac2:(tb__ "0|0|
S0S5S30Vrun1;S45A2S7A3").
Hypothesis E1a_def : leaf 0 run1 = E1a.
Hypothesis E1b_def : leaf 1 run1 = E1b.
Hypothesis sd1a : ltac2:(tb__ "0|0|
S0S5S2cVE1a;VE1a';S3aA3S7A3").
Hypothesis sd1b : ltac2:(tb__ "0|0|
S0S5S2cVE1b;VE1b';S3bA3S7A3").
Hypothesis E1a'_def : ltac2:(tb__ "0|0|
S0S12S14VE1a;S11VE1a';A1A2VE1a';A3").
Hypothesis E1b'_def : ltac2:(tb__ "0|0|
S0S12S14VE1b;S11VE1b';A1A2VE1b';A3").
Hypothesis ent1a : ltac2:(tb__ "0|0|
S0S5S2fVE1a';VC1;A2S7A3").
Hypothesis ent1b : ltac2:(tb__ "0|0|
S0S5S2fVE1b';VC1;A2S7A3").
Hypothesis br1a : ltac2:(tb__ "0|0|
S0S5S51S21S25S23S50S48S22Z11A1A3A1S1fS11VE1a;A1A1A3S7A3").
Hypothesis br1b : ltac2:(tb__ "0|0|
S0S5S51S21S25S26S23S50S48S22Z11A1A3A1A1S1fS11VE1b;A1A1A3S7A3").
Hypothesis nxC1 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC1;A1M0A1S36A3S0S5S1eG0A1SaA3A2").
Hypothesis run2_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U12cS6S3S46S9S3A1A3VC1;A3Vrun2;A3").
Hypothesis chk2 : ltac2:(tb__ "0|0|
S0S5S2dVrun2;S46A2S7A3").
Hypothesis E2_def : leaf 0 run2 = E2.
Hypothesis sd2 : ltac2:(tb__ "0|0|
S0S5S2cVE2;VC2;S3cVvb;A1A3S7A3").
Hypothesis C2_def : ltac2:(tb__ "0|0|
S0S12S14VE2;S11VC2;A1A2VC2;A3").
Hypothesis nxC2 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC2;A1M0A1S36A3S0S5S1eG0A1SaA3A2").
Hypothesis run3_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U258S6S3S47S6S3Z3e818S6S3Z3e83cS6S3Z3e73cS9S3A1A3A3A3A3VC2;A3Vrun3;A3").
Hypothesis chk3 : ltac2:(tb__ "0|0|
S0S5S2dVrun3;S47A2S7A3").
Hypothesis E3_def : leaf 0 run3 = E3.
Hypothesis sd3 : ltac2:(tb__ "0|0|
S0S5S2cVE3;VC3;S3dA3S7A3").
Hypothesis C3_def : ltac2:(tb__ "0|0|
S0S12S14VE3;S11VC3;A1A2VC3;A3").
Hypothesis nxC3 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC3;A1M0A1S36A3S0S5S1eG0A1SaA3A2").
Hypothesis run4_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U320S6S3S42S6S3Z3e818S9S3A1A3A3VC3;A3Vrun4;A3").
Hypothesis chk4 : ltac2:(tb__ "0|0|
S0S5S2dVrun4;S42A2S7A3").
Hypothesis E4_def : leaf 0 run4 = E4.
Hypothesis sd4 : ltac2:(tb__ "0|0|
S0S5S2cVE4;VC4;S3eA3S7A3").
Hypothesis C4_def : ltac2:(tb__ "0|0|
S0S12S14VE4;S11VC4;A1A2VC4;A3").
Hypothesis nxC4 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC4;A1M0A1S36A3S0S5S1eG0A1SaA3A2").
Hypothesis run5_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U320S6S3S41S6S3Z3e73cS6S3Z5fa44S6S3Z5fa24S6S3Z5fa64S6S3Z5fa84S6S3Z5fa04S9S3A1A3A3A3A3A3A3A3VC4;A3Vrun5;A3").
Hypothesis chk5 : ltac2:(tb__ "0|0|
S0S5S2dVrun5;S41A2S7A3").
Hypothesis E5_def : leaf 0 run5 = E5.
Hypothesis sd5 : ltac2:(tb__ "0|0|
S0S5S2cVE5;VC5;S3fA3S7A3").
Hypothesis C5_def : ltac2:(tb__ "0|0|
S0S12S14VE5;S11VC5;A1A2VC5;A3").
Hypothesis nxC5 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC5;A1M0A1S36A3S0S5S1eG0A1SaA3A2").
Hypothesis He5 : ltac2:(tb__ "0|1|
S0SeS8S27A1M0A1S34VC5;S4dVs5;A3SdG0VR5;A2A3").
Hypothesis Hchk5 : ltac2:(tb__ "0|0|
S0S5S33VC5;S4dVs5;VR5;S55S13S12S15S4eA4A5S7A3").
Hypothesis HT5 : ltac2:(tb__ "0|0|
S0S12S35Vs5;S4dS56S58S4fA1A1VC5;VR5;A5VT5;A3").
Hypothesis FBC5 : ltac2:(tb__ "0|1|
S0S5S52S21S24S1dS11VC5;A1M0A1A1S1fG0A1A3S7A3").
Hypothesis FBT5 : ltac2:(tb__ "0|0|
S0S5S52S21S24S1dS11VT5;A1A1A1S1fS11VC5;A1A1A3S7A3").
Hypothesis T5f_def : ltac2:(tb__ "0|0|
S0S12S57VT5;S1fS11VC5;A1A1A2VT5f;A3").
Hypothesis nxT5f : ltac2:(tb__ "0|1|
S1S0S4S1dS11VT5f;A1M0A1Pf0A3S0S5S1eG0A1SaA3A2").
Hypothesis run6_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U320S6S3S43S6S3Z3e7b8S6S3Z3e7d8S9S3A1A3A3A3VT5f;A3Vrun6;A3").
Hypothesis chk6 : ltac2:(tb__ "0|0|
S0S5S2dVrun6;S43A2S7A3").
Hypothesis E6_def : leaf 0 run6 = E6.
Hypothesis sd6 : ltac2:(tb__ "0|0|
S0S5S2cVE6;VC6;S40Vvb;A1A3S7A3").
Hypothesis C6_def : ltac2:(tb__ "0|0|
S0S12S14VE6;S11VC6;A1A2VC6;A3").
Hypothesis nxC6 : ltac2:(tb__ "0|1|
S1S0S4S1dS11VC6;A1M0A1Pf2A3S0S5S1eG0A1SaA3A2").
Hypothesis run7_eq : ltac2:(tb__ "0|0|
S0S8S13A1S10U320S6S3Z3eb64S6S3Z3eabcS6S3Z3ea78S6S3Z3ea98S9S3A1A3A3A3A3VC6;A3Vrun7;A3").
Hypothesis chk7 : ltac2:(tb__ "0|0|
S0S5S2dVrun7;S49A2S7A3").
Hypothesis E7_def : leaf 0 run7 = E7.
Hypothesis ent7 : ltac2:(tb__ "0|0|
S0S5S2fVE7;S38Vvb;A1A2S7A3").

Variables (J : jpredA) (ok : world -> Prop) (rho : valuation) (tp : list word).
Hypothesis HOK : ok_frameA segsA ok J.
Hypothesis HST : ltac2:(tb__ "0|0|
S17S2SfVJ;A3").
Hypotheses (HD0 : diffs_ok rho dI0)
           (HD1a : 17 <= bv_unsigned (rw rho V_CLS) -> diffs_ok rho dI1a) (HD1b : bv_unsigned (rw rho V_CLS) < 17 -> diffs_ok rho dI1b)
           (HD2 : diffs_ok rho (dI2 vb))
           (HD3 : diffs_ok rho dI3) (HD4 : diffs_ok rho dI4) (HD5 : diffs_ok rho dI5) (HD6 : diffs_ok rho (dI6 vb)).
Let Q : assn := ltac2:(tb__ "0|1|
S32S2SfVrho;Vtp;S6ScS12S31A2M0SbS12S31S38Vvb;A1S2eVJ;A1A4S9G0A1A3A5").
Let ST200 : stableA segsA NXI J := ltac2:(tb__ "0|0|
S18S2SfS36VJ;S5bVHST;A6").
Let ST240 : stableA segsA 240 J := ltac2:(tb__ "0|0|
S18S2SfPf0VJ;S59VHST;A6").
Let ST242 : stableA segsA 242 J := ltac2:(tb__ "0|0|
S18S2SfPf2VJ;S5aVHST;A6").
Let DB := dI_below vb.

Lemma from_C6 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC6;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [0x3eb64; 0x3eabc; 0x3ea78; 0x3ea98] C6 run7 242 E7 (proj2 nxC6) (proj1 nxC6) run7_eq E7_def QIRET J ok rhoC tp Q chk7 HOK ST242).
  intros rhoL HagL. apply (leaf_post J ok E7 (PostQI vb) rho rhoL tp [(PostQI vb, JQ J)] ent7 HST (or_introl eq_refl)).
  eapply agree_below_trans; [exact Hag | eapply agree_below_le; [exact le_NPRE_242 | exact HagL]].
Qed.

Lemma from_T5f : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VT5f;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [QCENTI; 0x3e7b8; 0x3e7d8] T5f run6 240 E6 (proj2 nxT5f) (proj1 nxT5f) run6_eq E6_def QCENTI J ok rhoC tp Q chk6 HOK ST240).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_240 HagL)) as HagR.
  apply (restate_cont J ok E6 C6 (dI6 vb) rhoL tp Q sd6); [| exact C6_def | apply from_C6; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI6 vb) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD6).
Qed.

Lemma from_C5 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC5;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag.
  apply (call_cont C5 Pre_memsetA Posts_memsetA s5 R5 T5 NPRE
           (fun ok0 Jx r t Ho Hs => memset_sumA ok0 Jx r t Ho Hs) He5 Hchk5 ltac:(intros P [<-|[]]; exact HT5) FBC5 FBT5 ltac:(rewrite (proj1 nxC5); exact le_NPRE_NXI)
           J ok rhoC tp Q HOK HST).
  intros rho' Hag'. rewrite T5f_def. apply from_T5f. eapply agree_below_trans; [exact Hag | eapply agree_below_le; [| exact Hag']]. rewrite (proj1 nxC5). exact le_NPRE_NXI.
Qed.

Lemma from_C4 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC4;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [MSENTQ; 0x3e73c; 0x5fa44; 0x5fa24; 0x5fa64; 0x5fa84; 0x5fa04] C4 run5 NXI E5 (proj2 nxC4) (proj1 nxC4) run5_eq E5_def MSENTQ J ok rhoC tp Q chk5 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E5 C5 dI5 rhoL tp Q sd5); [| exact C5_def | apply from_C5; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI5 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD5).
Qed.

Lemma from_C3 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC3;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [PSENT; 0x3e818] C3 run4 NXI E4 (proj2 nxC3) (proj1 nxC3) run4_eq E4_def PSENT J ok rhoC tp Q chk4 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E4 C4 dI4 rhoL tp Q sd4); [| exact C4_def | apply from_C4; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DB)))))) HagR HD4).
Qed.

Lemma from_C2 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC2;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 600%nat [QI3; 0x3e818; 0x3e83c; 0x3e73c] C2 run3 NXI E3 (proj2 nxC2) (proj1 nxC2) run3_eq E3_def QI3 J ok rhoC tp Q chk3 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E3 C3 dI3 rhoL tp Q sd3); [| exact C3_def | apply from_C3; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI3 (proj1 (proj2 (proj2 (proj2 (proj2 DB))))) HagR HD3).
Qed.

Lemma from_C1 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC1;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 300%nat [QI2] C1 run2 NXI E2 (proj2 nxC1) (proj1 nxC1) run2_eq E2_def QI2 J ok rhoC tp Q chk2 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E2 C2 (dI2 vb) rhoL tp Q sd2); [| exact C2_def | apply from_C2; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI2 vb) (proj1 (proj2 (proj2 (proj2 DB)))) HagR HD2).
Qed.

Lemma from_C0 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS2Vok;S16S2VJ;VC0;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont2 300%nat [QI1; 0x3e63c; 0x3e810; 0x3e804] C0 run1 NPRE E1a E1b (proj2 nxC0) (proj1 nxC0) run1_eq E1a_def E1b_def QI1 J ok rhoC tp Q chk1 HOK HST).
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_contF J ok E1a E1a' dI1a rhoL tp Q sd1a); [| exact E1a'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1a (proj1 (proj2 DB)) HagR). apply HD1a.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_geu_lit rhoL V_CLS 17 _ ltac:(lia) br1a HF).
    + apply (ent_cont J ok E1a' C1 rhoL tp Q ent1a HST). intros rho' Hag'. apply from_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_contF J ok E1b E1b' dI1b rhoL tp Q sd1b); [| exact E1b'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1b (proj1 (proj2 (proj2 DB))) HagR). apply HD1b.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_ltu_lit rhoL V_CLS 17 _ ltac:(lia) br1b HF).
    + apply (ent_cont J ok E1b' C1 rhoL tp Q ent1b HST). intros rho' Hag'. apply from_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
Qed.

Theorem seg_QI_sound_sec : ltac2:(tb__ "0|0|
S2aS2Vok;S16S2VJ;S37Vvb;A1Vrho;Vtp;A5VQ;A4").
Proof.
  apply (run_cont1 300%nat [QI0; 0x3e63c] (PreQI vb) run0 NPRE E0 (proj2 (proj2 (proj2 (preQI_wf vb)))) (proj1 (proj2 (proj2 (preQI_wf vb)))) run0_eq E0_def QI0 J ok rho tp Q chk0 HOK HST).
  intros rhoL HagL.
  apply (restate_cont J ok E0 C0 dI0 rhoL tp Q sd0); [| exact C0_def | apply from_C0; exact HagL].
  exact (diffs_ok_agree NPRE rho rhoL dI0 (proj1 DB) HagL HD0).
Qed.

Lemma efrom_C6 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC6;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [0x3eb64; 0x3eabc; 0x3ea78; 0x3ea98] C6 run7 242 E7 (proj2 nxC6) (proj1 nxC6) run7_eq E7_def QIRET J rhoC tp Q chk7 ST242).
  intros rhoL HagL. apply (leaf_epost J E7 (PostQI vb) rho rhoL tp [(PostQI vb, JQ J)] ent7 HST (or_introl eq_refl)).
  eapply agree_below_trans; [exact Hag | eapply agree_below_le; [exact le_NPRE_242 | exact HagL]].
Qed.

Lemma efrom_T5f : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VT5f;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [QCENTI; 0x3e7b8; 0x3e7d8] T5f run6 240 E6 (proj2 nxT5f) (proj1 nxT5f) run6_eq E6_def QCENTI J rhoC tp Q chk6 ST240).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_240 HagL)) as HagR.
  apply (restate_econt J E6 C6 (dI6 vb) rhoL tp Q sd6); [| exact C6_def | apply efrom_C6; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI6 vb) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD6).
Qed.

Lemma efrom_C5 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC5;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag.
  apply (call_econt C5 Pre_memsetA Posts_memsetA s5 R5 T5 NPRE
           (fun Jx r t Hs => memset_sumA_ex Jx r t Hs) He5 Hchk5 ltac:(intros P [<-|[]]; exact HT5) FBC5 FBT5 ltac:(rewrite (proj1 nxC5); exact le_NPRE_NXI)
           J rhoC tp Q HST).
  intros rho' Hag'. rewrite T5f_def. apply efrom_T5f. eapply agree_below_trans; [exact Hag | eapply agree_below_le; [| exact Hag']]. rewrite (proj1 nxC5). exact le_NPRE_NXI.
Qed.

Lemma efrom_C4 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC4;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [MSENTQ; 0x3e73c; 0x5fa44; 0x5fa24; 0x5fa64; 0x5fa84; 0x5fa04] C4 run5 NXI E5 (proj2 nxC4) (proj1 nxC4) run5_eq E5_def MSENTQ J rhoC tp Q chk5 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E5 C5 dI5 rhoL tp Q sd5); [| exact C5_def | apply efrom_C5; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI5 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD5).
Qed.

Lemma efrom_C3 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC3;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [PSENT; 0x3e818] C3 run4 NXI E4 (proj2 nxC3) (proj1 nxC3) run4_eq E4_def PSENT J rhoC tp Q chk4 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E4 C4 dI4 rhoL tp Q sd4); [| exact C4_def | apply efrom_C4; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DB)))))) HagR HD4).
Qed.

Lemma efrom_C2 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC2;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 600%nat [QI3; 0x3e818; 0x3e83c; 0x3e73c] C2 run3 NXI E3 (proj2 nxC2) (proj1 nxC2) run3_eq E3_def QI3 J rhoC tp Q chk3 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E3 C3 dI3 rhoL tp Q sd3); [| exact C3_def | apply efrom_C3; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI3 (proj1 (proj2 (proj2 (proj2 (proj2 DB))))) HagR HD3).
Qed.

Lemma efrom_C1 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC1;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 300%nat [QI2] C1 run2 NXI E2 (proj2 nxC1) (proj1 nxC1) run2_eq E2_def QI2 J rhoC tp Q chk2 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E2 C2 (dI2 vb) rhoL tp Q sd2); [| exact C2_def | apply efrom_C2; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI2 vb) (proj1 (proj2 (proj2 (proj2 DB)))) HagR HD2).
Qed.

Lemma efrom_C0 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S2S16S2VJ;VC0;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt2 300%nat [QI1; 0x3e63c; 0x3e810; 0x3e804] C0 run1 NPRE E1a E1b (proj2 nxC0) (proj1 nxC0) run1_eq E1a_def E1b_def QI1 J rhoC tp Q chk1 HST).
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_econtF J E1a E1a' dI1a rhoL tp Q sd1a); [| exact E1a'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1a (proj1 (proj2 DB)) HagR). apply HD1a.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_geu_lit rhoL V_CLS 17 _ ltac:(lia) br1a HF).
    + apply (ent_econt J E1a' C1 rhoL tp Q ent1a HST). intros rho' Hag'. apply efrom_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_econtF J E1b E1b' dI1b rhoL tp Q sd1b); [| exact E1b'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1b (proj1 (proj2 (proj2 DB))) HagR). apply HD1b.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_ltu_lit rhoL V_CLS 17 _ ltac:(lia) br1b HF).
    + apply (ent_econt J E1b' C1 rhoL tp Q ent1b HST). intros rho' Hag'. apply efrom_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
Qed.

Theorem seg_QI_complete_sec : ltac2:(tb__ "0|0|
S29S2S16S2VJ;S37Vvb;A1Vrho;Vtp;A5VQ;A3").
Proof.
  apply (run_econt1 300%nat [QI0; 0x3e63c] (PreQI vb) run0 NPRE E0 (proj2 (proj2 (proj2 (preQI_wf vb)))) (proj1 (proj2 (proj2 (preQI_wf vb)))) run0_eq E0_def QI0 J rho tp Q chk0 HST).
  intros rhoL HagL.
  apply (restate_econt J E0 C0 dI0 rhoL tp Q sd0); [| exact C0_def | apply efrom_C0; exact HagL].
  exact (diffs_ok_agree NPRE rho rhoL dI0 (proj1 DB) HagL HD0).
Qed.
End QI.

Theorem seg_QI_sound : ltac2:(tb__ "0|3|
S5S19S2bOF_;S1bS8S4cQ40M0A1A1S1aS2R3R4A3S17S2SfR5A3S28R4S39A2S53Z11M1S4bG0S20R5S4aA2A2A2S28R6S3aA2F_;S54S4bG0S20R6S4aA2A2G1A2S28R7S3bA2F_;S28R7S3cRaA1A2S28R8S3dA2S28R9S3eA2S28RaS3fA2S28RbS40ReA1A2S2aS2RdS16S2ReS37RfA1RcRbA5S32S2SfRcRbS6ScS12S31A2M2SbS12S31S38RfA1S2eReA1A4S9G2A1A3A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Fok;FJ;Fvb;").
Proof.
  intros [|]; intros.
  - eapply (seg_QI_sound_sec true run0b run1b run2b run3b run4b run5b run6b run7b E0b C0b E1ab E1bb E1ab' E1bb' C1b E2b C2b E3b C3b E4b C4b E5b C5b T5b T5fb E6b C6b E7b s5b R5b
            run0b_eq chk0b E0b_def sd0b eq_refl nxC0b run1b_eq chk1b E1ab_def E1bb_def sd1ab sd1bb eq_refl eq_refl ent1ab ent1bb br1ab br1bb nxC1b run2b_eq chk2b E2b_def sd2b eq_refl nxC2b
            run3b_eq chk3b E3b_def sd3b eq_refl nxC3b run4b_eq chk4b E4b_def sd4b eq_refl nxC4b run5b_eq chk5b E5b_def sd5b eq_refl nxC5b
            He5b Hchk5b HT5b FBC5b FBT5b eq_refl nxT5fb run6b_eq chk6b E6b_def sd6b eq_refl nxC6b run7b_eq chk7b E7b_def ent7b); eassumption.
  - eapply (seg_QI_sound_sec false run0a run1a run2a run3a run4a run5a run6a run7a E0a C0a E1aa E1ba E1aa' E1ba' C1a E2a C2a E3a C3a E4a C4a E5a C5a T5a T5fa E6a C6a E7a s5a R5a
            run0a_eq chk0a E0a_def sd0a eq_refl nxC0a run1a_eq chk1a E1aa_def E1ba_def sd1aa sd1ba eq_refl eq_refl ent1aa ent1ba br1aa br1ba nxC1a run2a_eq chk2a E2a_def sd2a eq_refl nxC2a
            run3a_eq chk3a E3a_def sd3a eq_refl nxC3a run4a_eq chk4a E4a_def sd4a eq_refl nxC4a run5a_eq chk5a E5a_def sd5a eq_refl nxC5a
            He5a Hchk5a HT5a FBC5a FBT5a eq_refl nxT5fa run6a_eq chk6a E6a_def sd6a eq_refl nxC6a run7a_eq chk7a E7a_def ent7a); eassumption.
Qed.
Theorem seg_QI_complete : ltac2:(tb__ "0|3|
S5S19S1bS8S4cQ40M0A1A1S17S2SfR3A3S28R3S39A2S53Z11M1S4bG0S20R4S4aA2A2A2S28R5S3aA2F_;S54S4bG0S20R5S4aA2A2G1A2S28R6S3bA2F_;S28R6S3cR8A1A2S28R7S3dA2S28R8S3eA2S28R9S3fA2S28RaS40RcA1A2S29S2S16S2RcS37RdA1RbRaA5S32S2SfRbRaS6ScS12S31A2M2SbS12S31S38RdA1S2eRcA1A4S9G2A1A3A5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FJ;Fvb;").
Proof.
  intros [|]; intros.
  - eapply (seg_QI_complete_sec true run0b run1b run2b run3b run4b run5b run6b run7b E0b C0b E1ab E1bb E1ab' E1bb' C1b E2b C2b E3b C3b E4b C4b E5b C5b T5b T5fb E6b C6b E7b s5b R5b
            run0b_eq chk0b E0b_def sd0b eq_refl nxC0b run1b_eq chk1b E1ab_def E1bb_def sd1ab sd1bb eq_refl eq_refl ent1ab ent1bb br1ab br1bb nxC1b run2b_eq chk2b E2b_def sd2b eq_refl nxC2b
            run3b_eq chk3b E3b_def sd3b eq_refl nxC3b run4b_eq chk4b E4b_def sd4b eq_refl nxC4b run5b_eq chk5b E5b_def sd5b eq_refl nxC5b
            He5b Hchk5b HT5b FBC5b FBT5b eq_refl nxT5fb run6b_eq chk6b E6b_def sd6b eq_refl nxC6b run7b_eq chk7b E7b_def ent7b); eassumption.
  - eapply (seg_QI_complete_sec false run0a run1a run2a run3a run4a run5a run6a run7a E0a C0a E1aa E1ba E1aa' E1ba' C1a E2a C2a E3a C3a E4a C4a E5a C5a T5a T5fa E6a C6a E7a s5a R5a
            run0a_eq chk0a E0a_def sd0a eq_refl nxC0a run1a_eq chk1a E1aa_def E1ba_def sd1aa sd1ba eq_refl eq_refl ent1aa ent1ba br1aa br1ba nxC1a run2a_eq chk2a E2a_def sd2a eq_refl nxC2a
            run3a_eq chk3a E3a_def sd3a eq_refl nxC3a run4a_eq chk4a E4a_def sd4a eq_refl nxC4a run5a_eq chk5a E5a_def sd5a eq_refl nxC5a
            He5a Hchk5a HT5a FBC5a FBT5a eq_refl nxT5fa run6a_eq chk6a E6a_def sd6a eq_refl nxC6a run7a_eq chk7a E7a_def ent7a); eassumption.
Qed.
End SegQI.

(* [comment removed for export] *)
Module DepotKP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "app"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP.DepotKP"; "KDP"; "pendD"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "vm_maps"; "m_vmmaps"; "VmMaps"; "region_free"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "DG"; "aa_depot"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK"; "KD"; "TOPr"; "hcD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "dtrans"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2"; "KD_laws2"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DepotKP.
Let segs : list Segment := segsA.
Variables (A0 : AA) (Kc : KcA) (rhoE : valuation) (nreq : Z).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HB : budget_ok_alloc A0 nreq.
Hypothesis Hn : 0 <= nreq.
Hypothesis HKm0 : 0 <= aa_Km A0.

Variables (ua L : Z).
Hypothesis Hua : 0 <= ua. Hypothesis HL : 0 <= L. Hypothesis HuaL : ltac2:(tb__ "0|0|
S25S24Vua;VL;A2S26Z2Z40A2A2").

Definition pendD (G : DG) (md : Model) : Prop := ltac2:(tb__ "0|3|
S19S17S4SaQ40M0A1M1G1A2S3G1G1SbG0Vua;A2SbG0VL;A2A4SfS10Vmd;A1A1A3S4S0S0A2M2S17G2R1S1eVG;A1A3S18R2S3S0S0Vua;VL;A4A2F_;Fbn;A2").
Definition KDP (G : DG) : jpredA := ltac2:(tb__ "0|0|
S14S2SaQ40A1A1S2SeA1SdS19S1bVA0;VKc;VrhoE;VG;R4R3R2R1A8S9VG;R1A2A2Lmd;Ltr;Ltp;Lrho;").

Lemma KDP_KD : ltac2:(tb__ "0|0|
S15S14S2SaQ40A1A1S2SeA1SdS8R5R4R3R2R1A5S1bVA0;VKc;VrhoE;R6R5R4R3R2A8F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md [H _]. exact H. Qed.
Lemma KDP_pend : ltac2:(tb__ "0|0|
S15S14S2SaQ40A1A1S2SeA1SdS8R5R4R3R2R1A5S9R6R2A2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md [_ H]. exact H. Qed.

Lemma KDP_stable : ltac2:(tb__ "0|0|
S1S20P10R1A2S15S21Vsegs;R3S8R1A1A3FG;F_;Fn;").
Proof.
  intros n Hn16 G rho rho' tp tr md md' Hag Hme (HK & HP). split; [exact (KD_stable A0 Kc rhoE HKc n Hn16 G rho rho' tp tr md md' Hag Hme HK)|].
  destruct Hme as ((mat' & ->) & _). unfold pendD in HP |- *. rewrite m_vmmaps_with_vm_backing. exact HP.
Qed.

Lemma grant_sep : ltac2:(tb__ "0|3|
S11SaQ40M0A1M1G1S0S1aS6S12S5S4G1G1A2M2S13R4A1SfR4A1A3R3R2A3S7A3S17G2S3G1G1SbG0Vua;A2SbG0VL;A2A4SfR5A1A3S1aS0ScG0R4A2R3A3S18S3S0S0ScG0R6A2R4A4S3S0S0Vua;VL;A4A2F_;F_;F_;Fsz;Fn;Fa;FV;").
Proof.
  intros V a n sz Hfree Hin Hsz.
  pose proof (apart_of_region_free _ a n Hfree _ ltac:(apply in_or_app; right; exact Hin)) as X. unfold apartW in X. cbn [fst snd] in X.
  rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.

Theorem KDP_trans : ltac2:(tb__ "0|1|
S15S2SaQ40A1A1M0SdS15G0SdS14S2SeA1S1fR8R7R6R5R4R3A6S8R9R3R8R2R7A5S8R7R4R6R3R5A5F_;F_;Ftr;Frho;Fmd';Ftp';FG';Fmd;Ftp;FG;").
Proof.
  intros G tp md G' tp' md' rho tr HT (HK & HIn & HSep).
  split; [exact (KD_trans A0 Kc rhoE HKc G tp md G' tp' md' rho tr HT HK)|]. destruct HT.
  - split; [exact HIn|]. intros bn Hbn. apply HSep. exact Hbn.
  - split.
    + rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps. rewrite H. right. exact HIn.
    + intros bn Hbn. unfold G_fblk, dblocks in Hbn. cbn [dNB dFB] in Hbn. rewrite <- (app_nil_r (dNB G)) in Hbn.
      destruct (in_dblocks_app G bn [] [bv_unsigned a] Hbn) as [X|X]; [exact (HSep bn X)|]. cbn in X. destruct X as [<-|[]].
      exact (grant_sep (m_vmmaps md) a n FBSZ H8 HIn H4).
  - split.
    + rewrite m_vmmaps_with_vmmaps. rewrite H. right. exact HIn.
    + intros bn Hbn. unfold G_nblk, dblocks in Hbn. cbn [dNB dFB] in Hbn. rewrite <- (app_nil_r (dFB G)) in Hbn.
      destruct (in_dblocks_app G bn [bv_unsigned a] [] Hbn) as [X|X]; [exact (HSep bn X)|]. cbn in X. destruct X as [<-|[]].
      exact (grant_sep (m_vmmaps md) a n NBSZ H8 HIn H4).
  - split; [exact HIn|]. intros bn Hbn. apply HSep. exact Hbn.
Qed.

Theorem KDP_laws : ltac2:(tb__ "0|0|
S1S20P10R1A2S23Vsegs;S8R2S1dVA0;A1A4F_;Fn;").
Proof.
  intros n Hn16. pose proof (KD_laws A0 Kc rhoE nreq HKc HB Hn HKm0 n Hn16) as [K1 K2 K3 K4 K5 K6 K7]. constructor.
  - exact (KDP_stable n Hn16).
  - intros G rho rho' tp tr md Hw Hl Hv (HK & HP). split; [exact (K2 G rho rho' tp tr md Hw Hl Hv HK) | exact HP].
  - exact KDP_trans.
  - intros G rho tp tr md (HK & _) HD. exact (K4 G rho tp tr md HK HD).
  - intros G rho tp tr md (HK & _). exact (K5 G rho tp tr md HK).
  - intros G rho tp tr md a n0 x (HK & _). exact (K6 G rho tp tr md a n0 x HK).
  - intros G rho tp tr md L0 (HK & _). exact (K7 G rho tp tr md L0 HK).
Qed.

Lemma KDP_intro : ltac2:(tb__ "0|4|
S2SaQ40M0A1M1A1S2SeA1SdS22Vsegs;VA0;VrhoE;R3R1A5VKc;R3R2A2S17S4G1G1A2S3G1G1SbG0Vua;A2SbG0VL;A2A4SfS10R3A1A1A3S4S0S0A2M2S17G2R1S1eS16VA0;A1M3A1A3S18R2S3S0S0Vua;VL;A4A2F_;Fbn;S14S1cVA0;R1A2S8G3R2R9R8R7A5F_;Frho;F_;F_;F_;F_;Fmd;Ftr;Ftp;").
Proof. intros tp tr md HA HK HIn HSep rho HT. split; [exact (KD_intro A0 Kc rhoE nreq HB HKm0 tp tr md HA HK rho HT) | exact (conj HIn HSep)]. Qed.
End DepotKP.
End DepotKP.

(* [comment removed for export] *)
Module DepotKF.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "app"; "length"; "prod"; "pair"; "bool"; "true"; "cons"; "nat"; "option"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "ge"; "modulo"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "event"; "vm_maps"; "vm_reserved"; "vm_noaccess"; "alloc_top"; "vm_limit"; "region_free"; "vm_init_sp"; "with_vmmaps"; "VmMaps"; "page_in_ranges"; "vm_add_lazy"; "m_vm_lazy"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKF.DepotKF"; "KD"; "AK"; "hcD"; "TOPr"; "dfp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "DG"; "dFB"; "dNB"; "aa_geom"; "aa_depot"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_ptr_committed"; "aa_sec"; "dFP"; "sec_chunk"; "aa_cls"; "aa_live"; "dN"; "topG"; "AA"; "ag_top"; "ageom"; "class_state"; "depot_state"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rl"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "NBSZ"; "FBSZ"; "dep_cost"; "dblocks"; "sumZ"; "DNMAX"; "DFPw"; "FBPAGES"; "G_fblk"; "G_ins"; "G_nblk"; "G_page"; "depot_inv"; "droom"; "dtrans"; "fpage"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "with_depot"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "PG"; "dyn_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "band_page"; "in_maps"; "secondary_repr"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "U0"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvKf"; "bumpKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "BETA1"; "Q1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2"; "KD_laws2"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DepotKF.
Let segs : list Segment := segsA.
Variables (A0 : AA) (Kc : KcA) (rhoE : valuation).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HB : budget_ok_free A0.
Hypothesis HKm0 : 0 <= aa_Km A0.
Hypothesis HKf0 : 0 <= aa_Kf A0.

Definition AK (G : DG) : AA := ltac2:(tb__ "0|0|
S77S61VA0;VG;A2A1").

Definition TOPr (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S12S41S35VA0;A1A1M0S11S29Q40M1S4aVrho;PaA2A2S2cG1S4aVrho;S76A2A2A2A2S12G0S29G1S4aVrho;PcA2A2A2A2").

Definition dfp_ok (G : DG) : Prop := ltac2:(tb__ "0|3|
S3S2SfS9S0S3cVG;A1M0A2S9S0S33VG;A1A2M1A3SfS6bR1G1A2S12Z0M2S63S0R2G0G2A4A2F_;Fb;A2").
Definition KD (G : DG) : jpredA := ltac2:(tb__ "0|0|
S49S7S2aQ40A1A1S7S1cA1S1bS3S60S2eVG;A1VrhoE;R3R1A4S3VKc;R2R1A2S3S31VG;A1S30R4A1A2A2A2Lmd;Ltr;Ltp;Lrho;").

Definition hcD : Z := ltac2:(tb__ "0|0|
S19S73S11S11S11S11S74S75S39VA0;A1A1A2S15S78S11S38VA0;A1S11S37VA0;A1Z1A2A2A2A2S79A2S3aVA0;A1A2A2").

Lemma AK_proj : ltac2:(tb__ "0|1|
S32S3S2S44S35S2eR1A1M0A1S35VA0;A1A3S3S2S7S45A1S3eG0A1S3eVA0;A1A3S3S2S7S3dA1S3bG0A1S3bVA0;A1A3S3S2S7SaS0S0A2A1S3fG0A1S3fVA0;A1A3S3S2S46S36G0A1R1A3S3S2S0S39G0A1S39VA0;A1A3S3S2S0S38G0A1S38VA0;A1A3S3S2S0S37G0A1S11S37VA0;A1Z1A2A3S2S0S3aG0A1S3aVA0;A1A3A2A2A2A2A2A2A2A2FG;").
Proof. intros G. repeat split; reflexivity. Qed.

Lemma AK_credit : ltac2:(tb__ "0|0|
S32S2S0S6cS2eR1A1A1S6cVA0;A1A3FG;").
Proof. intros G. apply PrimCredit.prim_credit_same. reflexivity. Qed.

Lemma KD_room : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5S16S11S4fR2R4A2S52R6A1A2S2fA2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _).
  destruct HM as (_ & V2 & V3 & _). unfold headroom, hcD. rewrite V3.
  rewrite AK_credit in V2. pose proof (PrimCredit.prim_credit_nonneg A0) as PCN.
  unfold budget_boundD in V2. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed AK bumpKf with_depot] in V2. lia.
Qed.

Lemma KD_reserved : ltac2:(tb__ "0|1|
S32S49S7S2aQ40A1M0A1S7S1cA1S1bS2dR5R4R3R2R1A5S2S7SaG0G0A2A1S1eS1aR2A1A1S70Vsegs;A1A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & L1 & _). exact L1. Qed.

Lemma KD_noacc : ltac2:(tb__ "0|5|
S32S49S7S2aQ40M0A1M1A1S7S1cA1S1bG1G1S0S2dR8R7R6R5R4A5S4dSaG1G1A2M2SbG1G1R4R3A4S1fS1aR5A1A1A3S3S12S29G0R5A2M3R3A2S13R3S11G3S29G0R4A2A2A2A2S5G1G1S5G1G1S3S4dG2SbG1G1R2R1A4S1dS1aR9A1A1A3S3S12S29G0R2A2M4R6A2S13R6S11G4S29G0R1A2A2A2A2A2Lm;A2Lb;A2F_;F_;F_;Fx;Fn;Fa;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md a n x ((_ & _ & _ & _ & HM & _) & _) Hin Hx. destruct HM as ((V1 & _) & _).
  destruct (V1 (a, n) x Hin Hx) as ([b m] & Hbm & Hr). exists b, m. exact (conj Hbm Hr).
Qed.

Lemma KD_top : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5S2S0S20S1aR2A1A1S43S35VA0;A1A1A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _). destruct HM as (_ & _ & _ & _ & _ & _ & V7 & _). exact V7. Qed.

Lemma KD_Kc : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5VKc;R3R2A2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md (_ & HK & _). exact HK. Qed.

Lemma KD_view : ltac2:(tb__ "0|2|
S32S49S49S7S2aQ40A1M0A1S7S1cA1S1bS1S2G0S4aR5R1A2S4aR6R1A2A3Fi;S1S2S7S2aQ8A1M1A1S4bR6R1A2S4bR7R1A2A3Fl;S0S6S56R9R1A2A1S2S10G1A1S6dVsegs;S4cR8A1R2A3S6dVsegs;S4cR9A1R2A3A3F_;Fz;S2dR9R8R6R5R4A5S2dRaR8R7R6R5A5F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FG;").
Proof. intros G rho rho' tp tr md Hw _ _ (HX & HK & HL & HT). unfold KD, TOPr in *. rewrite !Hw. exact (conj HX (conj HK (conj HL HT))). Qed.

Lemma KD_stable : ltac2:(tb__ "0|0|
S1S6fP10R1A2S32S72Vsegs;R3S2dR1A1A3FG;F_;Fn;").
Proof.
  intros n Hn16 G rho rho' tp tr md md' Hag Hme (HX & HK & HL & HT). split; [exact (AInvX_mat (AK G) rhoE tp md md' HX Hme)|].
  split; [|split; [exact HL | destruct Hag as (Hw & _ & _); unfold TOPr, V_DEPTH in *; rewrite <- (Hw 10%positive), <- (Hw 15%positive), <- (Hw 12%positive) by lia; exact HT]].
  destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
Qed.

Lemma AInvX_depot_cost : ltac2:(tb__ "0|5|
S32S32S7S2aQ40M0A1M1A1M2G2S1bS2S7S0A1M3S34R4A1S34R5A1A3S2G3S33R5A1S33R6A1A3S12S11S4eR3R4A2S52R7A1A2S11S4eR3R5A2S52R6A1A2A2G1S4dG1R1R6A3S4S4dG1R2R8A3S6S68S29G0R2A2A1A1A2F_;Fq;S60S2eR9A1M4VrhoE;R7R5A4S60G4VrhoE;R7R6A4F_;F_;F_;F_;F_;Fmd;Ftp';Ftp;FG';FG;").
Proof.
  intros G G' tp tp' md EN EF HP HTP (HG & HR & HF & HRest & HM & HI3 & HBT).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|split].
  - unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD in HM |- *.
    rewrite !AK_credit in HM |- *.
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpKf with_depot] in HM |- *. rewrite EN, EF.
    destruct HM as (V1 & V2 & VR). split; [exact V1|]. split; [clear -V2 HP; lia | exact VR].
  - unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global aa_cls AK bumpKf with_depot] in HI3 |- *.
    unfold dblocks in HI3 |- *. rewrite EN, EF. exact HI3.
  - eapply bandtp_grow; [exact HBT|]. intros q Hq. destruct (HTP q Hq) as [H|H]; [left; exact H | right; intros Hb; exfalso; exact (H Hb)].
Qed.

Lemma u64_of_Z0 : ltac2:(tb__ "0|1|
S0S3S12Z0R1A2S13R1S18Z2Z40A2A2A2S2S0S29Q40M0S2bG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma KD_trans_page : ltac2:(tb__ "0|3|
S32S7S2aQ40M0A1M1A1S1bSfG1S49S7S1cA1S6bR4S9S0S33R7A1A2A2S13S63S0R5S3cR8A1Z0M2A4S57A2S2G1R5S2bG0S5fR9R6S63S0R6S3cR9A1G2A4A3A2A3S2dRaR5R9R4R8A5S2dS5bRbR8A2R6SeG1R7RaA3R5R9A5F_;F_;F_;F_;Ftr;Frho;Fp;Fb;Fmd;Ftp;FG;").
Proof.
  intros G tp md b p rho tr Hb Hk Hp (HX & HK & [HL HNN] & HT). subst p. split; [|split; [exact HK | split; [| exact HT]]].
  2:{ split; [unfold G_page; cbn [dFP dFB]; rewrite length_list_upd; exact HL|].
      intros b' Hb'. unfold G_page in Hb' |- *. cbn [dFP dFB] in Hb' |- *.
      destruct (Nat.eq_dec b' b) as [->|Hne].
      - rewrite Model.nth_list_upd_same by (rewrite HL; exact Hb). pose proof (HNN b Hb). lia.
      - rewrite Model.nth_list_upd_other by (intros E; exact (Hne (eq_sym E))). exact (HNN b' Hb'). }
  apply (AInvX_depot_cost G (G_page G b) tp (_ :: tp) md); [reflexivity | reflexivity | | | exact HX].
  - rewrite (dep_cost_G_page G b) by (rewrite HL; exact Hb). pose proof (paid_cons_le md (Z_to_bv 64 (fpage G b (nth b (dFP G) 0))) tp). unfold PG. unfold page_size in *. lia.
  -
    intros q [<-|Hq]; [right | left; exact Hq].
    destruct HX as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
    cbn [aa_geom aa_depot AK bumpKf with_depot] in X5.
    destruct (X5 (nth b (dFB G) 0, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists (nth b (dFB G) 0); split; [reflexivity | apply nth_In; exact Hb])) as (DI & _).
    cbn [fst snd] in DI. destruct DI as (D1 & _ & D3 & _ & D5). pose proof (topG_range (aa_geom A0)) as TG. pose proof (HNN b Hb) as K0.
    unfold fpage. rewrite u64_of_Z0 by (unfold FBSZ, FBPAGES, PG in *; lia).
    intros HBP. apply band_page_band in HBP. unfold FBSZ, FBPAGES, PG in *. clear -D5 HBP K0 Hk D1 D3 TG. lia.
Qed.

Lemma apart_in_maps : ltac2:(tb__ "0|3|
S25S2aQ40M0A1M1G1S0S0S2ScS22S8SaG1G1A2S1eR5A1S1dR5A1A3R4R3A3SdA3S69R6R3R2A3S4S12S11S29G0R6A2M2S29G0R5A2A2R4A2S12R3G2A2A2F_;F_;Fhi;Flo;Fn;Fa;FV;").
Proof.
  intros V a n lo hi Hfree (e & Hin & H1 & H2).
  destruct (apart_of_region_free _ a n Hfree e ltac:(apply in_or_app; right; exact Hin)) as [X|X]; cbn [fst snd] in X; [left | right]; lia.
Qed.

Lemma sec_dyn : ltac2:(tb__ "0|0|
S6eS42S3dS6aR3R2A2S4dS3dR2S3bR3A1A3S66S41S35R4A1A1S47R3A1S48R3A1A3F_;F_;Fch;FA;Fm;").
Proof.
  intros m A ch (HS & _) Hin. apply In_nth_error in Hin as (i & Hi).
  destruct (HS i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DI & _). exact DI.
Qed.

Lemma u64_of_Z : ltac2:(tb__ "0|1|
S0S3S12Z0R1A2S13R1S18Z2Z40A2A2A2S2S0S29Q40M0S2bG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma AInvX_grant : ltac2:(tb__ "0|e|
S32S32S7S2aQ40M0A1M1A1S1bS1bG1G1S0S2S7SaG1G1A2M2A1M3S1dS1aR4A1A1SeG2SbG1G1R3R2A4S1dS1aR5A1M4A1A3A3S2G3S1fG4A1S1fS1aR6A1M5A1A3S2G3S1eG5A1S1eS1aR7A1M6A1A3S2S0S21G6A1S21S1aR8A1M7A1A3S2S0S20G7A1S20S1aR9A1A1A3G1S2ScS26R1S28RbA1M8A2SdA3S2ScS26R2G8A2SdA3F_;Fp;S2S0S29G0R8A2R7A3S13Z0R8A2S12S64S29G0RbA2A2S12S11S29G0RcA2RaA2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M9A1S1dG9A1A3RdRcA3SdA3S12S11S4eRfR11A2S52R13A1A2S11S4eR10R11A2S52R12A1A2A2SaS0S0A2MaS4dGaR1S53R14A1A3S4S4dGaR2S53R16A1A3S2GaR2SbS0S0S29G0R11A2RfA4A3A2F_;Fbn;S2S0S11S14S9S0S34R14A1A2A1S14S9S0S33R14A1A2A1A2S11S11S14S9S0S34R15A1A2A1MbS14S9S0S33R15A1A2A1McA2Z1A2A3S2S0S11S15S50GbA2S15S51GcA2A2S11S11S15S50S14S9S0S34R16A1A2A1A2S15S51S14S9S0S33R16A1A2A1A2A2RfA2A3S60S2eR17A1MdVrhoE;R15R14A4S60GdVrhoE;R16R14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;FG';FG;").
Proof.
  intros G G' tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL Himg Hceil Hfree Hpaid Hblk Hcnt Hsz (HG & HR & HF & HRest & HM & HI3 & HBT).
  cbn [aa_geom AK bumpKf with_depot] in HG, HR, HF, HRest.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|].
  unfold model_inv_nd, ledger_inv_nd in HM. rewrite AK_credit in HM.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpKf with_depot] in HM.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & _ & L7 & L8 & L9).
  set (G0g := aa_geom A0) in *.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (bv_unsigned a, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split; [|split; [|exact HBT]].
  -
    unfold model_inv_nd, ledger_inv_nd. rewrite AK_credit.
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpKf with_depot].
    destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    split.
    { unfold vm_geom. cbn [aa_geom aa_sec AK bumpKf with_depot]. fold G0g. rewrite Hna.
      split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
      - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
      - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
      - intros p Hal Hw. destruct (G9 p Hal Hw) as [P1 P2]. split; [apply Hlz; exact P1 | exact P2]. }
    split.
    { unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed AK bumpKf with_depot] in V2 |- *. clear -V2 Hpaid. lia. }
    split; [rewrite Hlm; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
    split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
    split.
    { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot AK bumpKf with_depot] in L4 |- *.
      rewrite Hrs, Hvm. destruct L4 as [N4 S4].
      pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
      pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
      split; [clear -N4 IN Hcnt; unfold GN in *; lia | clear -S4 IS Hsz; lia]. }
    split; [exact I|]. split; [exact I|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

    destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
    intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
  -
    unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global aa_cls AK bumpKf with_depot] in HI3 |- *. fold G0g in HI3 |- *.
    destruct HI3 as (X1 & X2 & X3 & X4 & X5 & X6).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact X6].
    intros bn Hbn. destruct (Hblk bn Hbn) as [Hold | ->]; [exact (X5 bn Hold)|].
    destruct VG as (_ & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). fold G0g in G2, G3, G4, G5, G6, G7.
    cbn [fst snd]. split.
    {
      pose proof (geom_top _ HG) as TG. fold G0g in TG.
      assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
      { apply band_covered_app_r. exact L2. }
      pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
      rewrite HnL in W. unfold dyn_in. unfold IMG_HI in *. rewrite TG. rewrite <- V7. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; lia | exact W]. }
    split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
    split; [apply APT; replace (ag_spacebeg G0g + (kSpaceSize + 4096)) with (ag_spacebeg G0g + kSpaceSize + 4096) by lia; exact G2|]. split; [apply APT; exact G7|].
    intros ch Hch.
    destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as DI. cbn [aa_geom AK bumpKf with_depot] in DI. fold G0g in DI.
    destruct DI as (D1 & D2 & D3 & _). pose proof (topG_range G0g) as TGR.
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.

Lemma sumZ_app : ltac2:(tb__ "0|1|
S7S0A1M0G0S2S0S54S8S0R2R1A3A1S11S54R2A1S54R1A1A2A3Fl2;Fl1;").
Proof. induction l1; intros l2; cbn; [reflexivity | rewrite IHl1; unfold sumZ; cbn; lia]. Qed.

Lemma in_dblocks_app : ltac2:(tb__ "0|4|
S32SaS0S0A2M0S7S0A1M1G1S4dG0R3S8G0S62S0G0S0SbS0S0R1S50A4Lb;M2S8S0S34R4A1R2A3A4S62S0G0S0SbS0S0R1S51A4Lb;M3S8S0S33R4A1R1A3A4A3A3S4S4dG0R4S53R5A1A3S4dG0R4S8G0S62S0G0G2R3A4S62S0G0G3R2A4A3A3A2F_;Fl2;Fl1;Fbn;FG;").
Proof.
  intros G bn l1 l2 H. unfold dblocks. rewrite !map_app in H.
  apply in_app_or in H as [H|H]; apply in_app_or in H as [H|H].
  - left. apply in_or_app. left. exact H.
  - right. apply in_or_app. left. exact H.
  - left. apply in_or_app. right. exact H.
  - right. apply in_or_app. right. exact H.
Qed.

Lemma KD_trans_fblk : ltac2:(tb__ "0|5|
S32S7S2aQ40M0A1M1A1S1bS25G1G1S49S7S1cA1S2S7SaG1G1A2M2A1M3S1dR5A1SeG2SbG1G1R4R3A4S1dS1aR6A1A1A3A3S2G3S1fR6A1S1fS1aR7A1A1A3S2G3S1eR7A1S1eS1aR8A1A1A3S2S0S21R8A1S21S1aR9A1A1A3S2G1S23R9A1S23S1aRaA1A1A3S2S0S29G0R8A2S51A3S2S0S17S29G0RaA2S65A2Z0A3S12S64S29G0RbA2A2S12S11S29G0RcA2S51A2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M4A1S1dG4A1A3RdRcA3SdA3S12S4eS27ReRdS24RfR10A2A3R11A2S4eR10R11A2A2S2dR13RdR12RcR11A5S2dS58R14S29G0R10A2A2ReR13RdS27R10RfS24R11R12A2A3A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftr;Frho;Fn;Fa;Fh';Fmd;Ftp;FG;").
Proof.
  intros G tp md h' a n rho tr Hvm Hna Hrs Hlm Hsp HnL Hal Himg Hceil Hfree Hpaid (HX & HK & HL & HT).
  split; [|split; [|split; [|exact HT]]].
  - apply (AInvX_grant G (G_fblk G (bv_unsigned a)) tp md _ a n FBSZ); rewrite ?m_vmmaps_vm_add_lazy, ?m_vmmaps_with_vmmaps, ?m_vm_lazy_vm_add_lazy, ?m_vm_lazy_with_vmmaps;
      try assumption.
    + apply alloc_top_same. exact Hsp.
    + intros p Hp. rewrite page_in_ranges_app, Hp. apply orb_true_r.
    + unfold FBSZ; lia.
    + unfold dep_cost, dep_pages, G_fblk. cbn [dNB dFP]. rewrite sumZ_app. cbn [sumZ fold_right]. lia.
    + intros bn Hbn. unfold G_fblk in Hbn. cbn [dNB dFB] in Hbn. unfold dblocks in Hbn. cbn [dNB dFB] in Hbn.
      rewrite <- (app_nil_r (dNB G)) in Hbn.
      destruct (in_dblocks_app G bn [] [bv_unsigned a] Hbn) as [X|X]; [left; exact X | right]. cbn in X. destruct X as [X|[]]. symmetry. exact X.
    + unfold G_fblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
    + unfold G_fblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
  - unfold vm_add_lazy. rewrite with_vm_backing_with_vm. apply HKc.
    replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity).
    apply HKc. exact HK.
  - destruct HL as [HL HNN]. split; [unfold G_fblk; cbn [dFP dFB]; rewrite !length_app; cbn [length]; lia|].
    intros b Hb. unfold G_fblk in Hb |- *. cbn [dFP dFB] in Hb |- *. rewrite length_app in Hb. cbn [length] in Hb.
    destruct (Nat.lt_ge_cases b (length (dFB G))) as [Hlt|Hge].
    + rewrite app_nth1 by (rewrite HL; exact Hlt). exact (HNN b Hlt).
    + rewrite app_nth2 by (rewrite HL; exact Hge). replace (b - length (dFP G))%nat with 0%nat by (rewrite HL; lia). cbn. lia.
Qed.

Lemma KD_trans_nblk : ltac2:(tb__ "0|5|
S32S7S2aQ40M0A1M1A1S1bS25G1G1S49S7S1cA1S2S7SaG1G1A2M2A1M3S1dR5A1SeG2SbG1G1R4R3A4S1dS1aR6A1A1A3A3S2G3S1fR6A1S1fS1aR7A1A1A3S2G3S1eR7A1S1eS1aR8A1A1A3S2S0S21R8A1S21S1aR9A1A1A3S2G1S23R9A1S23S1aRaA1A1A3S2S0S29G0R8A2S50A3S2S0S17S29G0RaA2S65A2Z0A3S12S64S29G0RbA2A2S12S11S29G0RcA2S50A2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M4A1S1dG4A1A3RdRcA3SdA3S12S4eS24RfR10A2R11A2S11S4eR10R11A2S50A2A2S2dR13RdR12RcR11A5S2dS5aR14S29G0R10A2A2ReR13RdS24R11R12A2A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftr;Frho;Fn;Fa;Fh';Fmd;Ftp;FG;").
Proof.
  intros G tp md h' a n rho tr Hvm Hna Hrs Hlm Hsp HnL Hal Himg Hceil Hfree Hpaid (HX & HK & HL & HT).
  split; [|split; [|split; [|exact HT]]].
  - apply (AInvX_grant G (G_nblk G (bv_unsigned a)) tp md _ a n NBSZ); rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try assumption.
    + apply alloc_top_same. exact Hsp.
    + intros p Hp. exact Hp.
    + unfold NBSZ; lia.
    + unfold dep_cost, dep_pages, G_nblk. cbn [dNB dFP]. rewrite length_app. cbn [length]. lia.
    + intros bn Hbn. unfold G_nblk in Hbn. cbn [dNB dFB] in Hbn. unfold dblocks in Hbn. cbn [dNB dFB] in Hbn.
      rewrite <- (app_nil_r (dFB G)) in Hbn.
      destruct (in_dblocks_app G bn [bv_unsigned a] [] Hbn) as [X|X]; [left; exact X | right]. cbn in X. destruct X as [X|[]]. symmetry. exact X.
    + unfold G_nblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
    + unfold G_nblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
  - replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity).
    apply HKc. exact HK.
  - unfold dfp_ok, G_nblk. cbn [dFP dFB]. exact HL.
Qed.

Lemma KD_trans_ins : ltac2:(tb__ "0|0|
S32S7S2aQ40A1A1S1bS0S49S7S1cA1S2dR6R2R5R1R4A5S2dS59R7R4A2R3R6R2R5A5F_;Ftr;Frho;FdF';Fmd;Ftp;FG;").
Proof.
  intros G tp md dF' rho tr (HX & HK & HL & HT). split; [|split; [exact HK | split; [unfold dfp_ok, G_ins; cbn [dFP dFB]; exact HL | exact HT]]].
  apply (AInvX_depot_cost G (G_ins G dF') tp tp md); [reflexivity | reflexivity | | intros q Hq; left; exact Hq | exact HX].
  unfold dep_cost, dep_pages, G_ins. cbn [dNB dFP]. lia.
Qed.

Theorem KD_trans : ltac2:(tb__ "0|1|
S32S7S2aQ40A1A1M0S1bS32G0S1bS49S7S1cA1S5eR8R7R6R5R4R3A6S2dR9R3R8R2R7A5S2dR7R4R6R3R5A5F_;F_;Ftr;Frho;Fmd';Ftp';FG';Fmd;Ftp;FG;").
Proof.
  intros G tp md G' tp' md' rho tr HT HK. destruct HT.
  - eapply KD_trans_page; eassumption.
  - apply KD_trans_fblk; assumption.
  - eapply KD_trans_nblk; eassumption.
  - apply KD_trans_ins; assumption.
Qed.

Lemma KD_place : ltac2:(tb__ "0|2|
S32S49S7S2aQ40M0A1M1A1S7S1cA1S1bS0S2dR6R5R4R3R2A5S5cVsegs;R7R6R3R5A5S12S40R8A1S55A2S4S2S0R4S50A3S2S0R4S51A3A2S5G1G1S71S2bG0Z0A2R7S2bG0R6A2R1A4La;A2F_;F_;F_;F_;FL;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md L ((HG & _ & _ & _ & HM & _) & _) [DM _] HDN HL.
  cbn [aa_geom AK bumpKf with_depot] in HG.
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & V7 & _ & _ & _ & L4 & _).
  pose proof (dm_map1_len _ _ DM) as [_ M2]. pose proof (dm_fb_len _ _ DM) as [[_ F2] _].
  pose proof (dm_N _ _ DM) as [[N1 _] _]. pose proof (dm_F _ _ DM) as (F0 & _ & F32 & _).
  apply (depot_place (AK G) md L).
  - exact L4.
  - cbn [aa_V AK bumpKf with_depot]. cbn [aa_V aa_Km aa_Kf AK bumpKf with_depot] in V4, V5, V6. unfold budget_ok_free in HB.
    pose proof (VCAP_limit_free (aa_V A0) (aa_Km A0) (aa_Kf A0) ltac:(lia) HKm0 HKf0 HB) as VC. lia.
  - cbn [aa_depot AK bumpKf with_depot]. unfold nblk in M2. unfold NBMAX, DNMAX in *.
    destruct (Z.eqb_spec (dN G + 1) 0); [lia|].
    pose proof (Z.div_le_mono (dN G + 1) (2 ^ 28 + 2) 65536 ltac:(lia) ltac:(lia)) as DV. change ((2 ^ 28 + 2) / 65536) with 4096 in DV. lia.
  - cbn [aa_depot AK bumpKf with_depot]. unfold fblk in F2. unfold FBMAX.
    pose proof (Z.div_le_mono (dF G + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia.
  - rewrite V7. cbn [aa_geom AK bumpKf with_depot]. pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A0)). rewrite GAPC_eq. unfold alloc_ceiling_lo. lia.
  - exact HL.
Qed.

Theorem KD_laws : ltac2:(tb__ "0|0|
S1S6fP10R1A2S7aVsegs;S2dR2S2fA4F_;Fn;").
Proof.
  intros n Hn16. constructor.
  - exact (KD_stable n Hn16).
  - exact KD_view.
  - exact KD_trans.
  - intros G rho tp tr md HK _. exact (KD_room G rho tp tr md HK).
  - exact KD_reserved.
  - exact KD_noacc.
  - exact KD_place.
Qed.

Lemma KD_intro : ltac2:(tb__ "0|0|
S7S2aQ40A1A1S7S1cA1S1bS67Vsegs;VA0;VrhoE;R3R1A5VKc;R3R2A2S49S30R1A1S2dS36VA0;A1R2R7R6R5A5F_;Frho;F_;F_;Fmd;Ftr;Ftp;").
Proof.
  intros tp tr md HA HK rho HT. destruct (AInvA_X A0 rhoE tp md HA) as (HX & HD & _).
  split; [|split; [exact HK | split; [split; [exact (proj2 (dm_fb_len _ _ (proj1 HD))) | intros b Hb; exact (proj1 (proj1 (dm_fp _ _ (proj1 HD) b Hb)))] | exact HT]]].
  unfold AK. replace (with_depot A0 (aa_depot A0)) with A0 by (destruct A0; reflexivity). exact (AInvX_bumpKf A0 rhoE tp md HX).
Qed.

Lemma dN_entry : ltac2:(tb__ "0|0|
S7S2aQ40A1A1S1bS67Vsegs;VA0;VrhoE;R2R1A5S12S11S40S36VA0;A1A1Z1A2S55A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as ((_ & _ & _ & _ & HM & _) & _ & L6).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & _). unfold budget_ok_free in HB.
  pose proof (limit_ok_free_K (aa_V A0) (aa_Km A0) (aa_Kf A0) ltac:(lia) HB). unfold DNMAX. lia.
Qed.

Lemma QMAX_Q1 : QMAX - Q1 = 2813952.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma hcD_entry : ltac2:(tb__ "0|1|
S7S2aQ40A1A1S1bS67Vsegs;VA0;VrhoE;R2R1A5S16S2fS11S52S36VA0;A1M0A1S5dG0A1A2A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as ((_ & _ & _ & _ & HM & _) & HD & L6).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & _ & _ & _ & _ & _ & _ & _ & L7 & _).
  pose proof (dep_cost_bound segs _ _ _ _ HD) as DC. pose proof (dm_F _ _ (proj1 HD)) as (F0 & F11 & F32 & _). pose proof (dm_N _ _ (proj1 HD)) as [[N1 _] _].
  assert (FB : fblk (dF (aa_depot A0)) <= 4094).
  { unfold fblk. pose proof (Z.div_le_mono (dF (aa_depot A0) + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia. }
  unfold budget_ok_free, limit_ok_free in HB. unfold hcD.
  pose proof QMAX_Q1 as CL.
  assert (DR : droom (aa_depot A0) <= PG + NBSZ) by (unfold droom; destruct ((dN (aa_depot A0) + 1) mod 65536 =? 0); unfold PG, NBSZ; lia).
  unfold DEPC, PG, NBSZ, BETA1, BETA_M, BETA_F, kPtrArrayCommit, LIMIT in *.
  set (q1 := Q1) in *. set (qm := QMAX) in *. set (u0 := U0) in *. set (dc := dep_cost (aa_depot A0)) in *. set (dr := droom (aa_depot A0)) in *.
  set (av := acost (aa_V A0)) in *. set (fb := fblk (dF (aa_depot A0))) in *.
  clearbody q1 qm u0 dc dr av fb. lia.
Qed.
End DepotKF.

End DepotKF.

(* [comment removed for export] *)
Module LiveGeom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "sub"; "lt"; "div"; "mul"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "rz"; "is_primary"; "region_beg"; "ClassID"; "PG"; "Size"; "needed"; "dyn_in"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_live"; "AA"; "sec_chunk"; "aa_geom"; "ag_spacebeg"; "aa_cls"; "aa_sec"; "ageom"; "class_state"; "cs_cache"; "cs_empty"; "cs_free_array"; "sc_map_beg"; "sc_map_size"; "topG"; "@Corelib.Init.Datatypes"; "pair"; "bool"; "list"; "nat"; "prod"; "Some"; "false"; "option"; "true"; "app"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "live_ids"; "nthZ"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma nodup_map_filter_pos : forall (T U : Type) (f : T -> U) (p : T -> bool) (l : list T) i j x y,
  NoDup (map f (List.filter p l)) -> (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y ->
  p x = true -> p y = true -> f x <> f y.
Proof.
  intros T U f p. induction l as [|h l IH]; intros i j x y ND Hij Hi Hj Px Py; [destruct i; discriminate|].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. cbn [List.filter] in ND. rewrite Px in ND. cbn [map] in ND.
    inversion ND as [|? ? NI ND']; subst. intros E. apply NI. rewrite E. apply list_elem_of_In. apply in_map. apply filter_In. split; [exact (nth_error_In _ _ Hj) | exact Py].
  - cbn [nth_error] in Hi. apply (IH i j x y); try assumption; [|lia].
    cbn [List.filter] in ND. destruct (p h); [cbn [map] in ND; inversion ND; subst; assumption | exact ND].
Qed.

Lemma nodup_map_sfilter_pos : forall (T U : Type) (f : T -> U) (p : T -> bool) (l : list T) i j x y,
  NoDup (map f (filter (fun t => Is_true (p t)) l)) -> (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y ->
  p x = true -> p y = true -> f x <> f y.
Proof.
  intros T U f p. induction l as [|h l IH]; intros i j x y ND Hij Hi Hj Px Py; [destruct i; discriminate|].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. rewrite list_basics.list.filter_cons_True in ND by (rewrite Px; exact I). cbn [map] in ND.
    inversion ND as [|? ? NI ND']; subst. intros E. apply NI. rewrite E. apply list_elem_of_In. apply in_map. apply list_elem_of_In.
    apply list_basics.list.list_elem_of_filter. split; [rewrite Py; exact I | apply list_elem_of_In; exact (nth_error_In _ _ Hj)].
  - cbn [nth_error] in Hi. apply (IH i j x y); try assumption; [|lia].
    destruct (p h) eqn:Ph.
    + rewrite list_basics.list.filter_cons_True in ND by (rewrite Ph; exact I). cbn [map] in ND. inversion ND; subst; assumption.
    + rewrite list_basics.list.filter_cons_False in ND by (rewrite Ph; intros []). exact ND.
Qed.

Lemma live_prim_facts : ltac2:(tb__ "0|5|
S17S32S27S36Q40A1A1S31S0S0S33Vsegs;R6R5R4R3A5S2fS29S0S0A2S25S0S0R3R2A4S16R7A1A3S9S26SeR3A1S2dA3S10S13R4A1A1S0SfS1aS19RaA1A1R1A2S0S4S4R7SdR6A1A2R1A2S0S8S8S1Z1M0R7A2S1R7Zfc00A2A2S8S8S1G0R3A2S1R3Z1eA2A2S8S1Z0M1R1A2S8S9S0S3R1S12R3A1M2A2G1A3S8S1S2R1G2A2S15A2S8S1S2SdR7A1M3R7A2G2A2S8S9S0S3G2Z10M4A2G1A3S8S8S1G4G3A2S1G3Z800A2A2S9S0S3G3G4A2G1A3A2A2A2A2A2A2A2A2Tx;Trb;Tc;F_;F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n (HG & HR & HF & HRest & HM & HI3 & HB) Hin HP c rb x.
  destruct HRest as (Hsep & _ & HPR & _). destruct (Hsep b n Hin) as (Hn1 & _).
  assert (Hn : 1 <= n <= 64512).
  { split; [exact Hn1|]. destruct (Z_le_dec 64513 n) as [L|L]; [|lia]. rewrite (not_primary_large n L) in HP. discriminate. }
  pose proof (slot_ok_all n Hn) as SO. unfold slot_ok in SO.
  apply andb_prop in SO as [SO S5]. apply andb_prop in SO as [SO S4]. apply andb_prop in SO as [SO S3]. apply andb_prop in SO as [_ S2].
  apply Z.leb_le in S2, S4, S5. apply Z.eqb_eq in S3. unfold slot in S2, S3. fold c in S2, S3, S4, S5.
  destruct HPR as (_ & _ & _ & P4). destruct (P4 c (conj S4 S5)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
  destruct (LV b n Hin HP eq_refl) as (L1 & L2 & L3). fold rb in L1, L2, L3. fold x in L2, L3.
  pose proof (rz_bound n) as RZ.
  assert (RZ16 : rz n mod 16 = 0).
  { unfold rz. rewrite Z.shiftl_mul_pow2 by (unfold rz_log; repeat destruct (_ <=? _); lia). rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (ND : rz n + n <= needed n).
  { unfold needed, kChunkHeader2Size. pose proof (Z.div_mod (Z.max n 16 + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (Z.max n 16 + 8 - 1) 8 ltac:(lia)) as MB. unfold round_up. lia. }
  repeat split; try lia.
Qed.

Lemma live_sec_facts : ltac2:(tb__ "0|3|
S17S32S27S36Q40A1A1S31S0S0S33Vsegs;R6R5R4R3A5S2fS29S0S0A2S25S0S0R3R2A4S16R7A1A3S9S26SeR3A1S2bA3SaS28S28SaS18S18S8S9S2cS18A1S30S18S1cRbA1R2A3S2aS18R1A2A3S8S9S0R7S2S2S22R1A1M0S11A2Z800M1A2A3S8S1Z1R6A2S8S1S2S2R7R6A2G1A2S2G0S23R1A1M2A2A2S8S9S0S3G0S11A2Z0A3S14S24S19RbA1A1G0G2A3A2A2A2A2A2Lch;A2Li;A2F_;F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n (HG & HR & HF & HRest & HM & HI3 & HB) Hin HP.
  destruct HRest as (Hsep & _ & _ & HS & _). destruct (Hsep b n Hin) as (Hn1 & _).
  destruct HI3 as (_ & LIV3 & _). destruct (LIV3 b n Hin) as [E|(ch & Hch & Eb & Esz)]; [rewrite E in HP; discriminate|].
  destruct (In_nth_error _ _ Hch) as (i & Hi). exists i, ch. split; [exact Hi|]. split; [exact Eb|]. split; [exact Hn1|].
  destruct HS as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _).
  pose proof (round_up_ge8 n) as R8. unfold PG in *. split; [lia|]. split; [exact D6 | exact D10].
Qed.

Lemma rz_sec : ltac2:(tb__ "0|0|
S0S1Z1R1A2S9S26SeR2A1S2bA3S9S0SdR3A1Z800A3F_;F_;Fn;").
Proof.
  intros n Hn HP. apply rz_large. destruct (Z_le_dec 64513 n) as [L|L]; [exact L|]. rewrite (primary_small n ltac:(lia)) in HP. discriminate.
Qed.

Lemma aligned_apart : ltac2:(tb__ "0|1|
S0S0S0S5Z0M0R3A2S9S0S3R3R4A2G0A3S9S0S3R3R5A2G0A3SbS9S0R5R4A3A1ScS1S2R6R7A2R5A2S1S2R5R7A2R6A2A2F_;F_;F_;F_;Fy;Fx;FS;").
Proof.
  intros S x y HS Hx Hy Hne. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hy; [|lia].
  destruct Hx as [p ->]. destruct Hy as [q ->]. assert (p <> q) by (intros ->; apply Hne; reflexivity). nia.
Qed.

Lemma live_pair_apart : ltac2:(tb__ "0|2|
S17S32S27S36Q40A1A1S31S28S28S0S0S0S0S33Vsegs;RaR9R8R7A5S37R7R6A2S9S2cS29S0S0A2M0A1M1S30G0S16RcA1R8A3S2aG0S25S0S0R6R5A4A2A3S9G1S30G0S16RdA1R8A3S2aG0S25S0S0R5R4A4A2A3ScS1S2R8R7A2S4R6SdR5A1A2A2S1S2R6R5A2S4R8SdR7A1A2A2A2F_;F_;F_;F_;Fn';Fb';Fn;Fb;Fj;Fi;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md i j b n b' n' HA Hij Hi Hj.
  pose proof (nth_error_In _ _ Hi) as Hin. pose proof (nth_error_In _ _ Hj) as Hin'.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite kSpaceSize_val in SP2.
  destruct (is_primary n) eqn:EP; destruct (is_primary n') eqn:EP'.
  -
    pose proof (live_prim_facts A rho tp md b n HA Hin EP) as F. pose proof (live_prim_facts A rho tp md b' n' HA Hin' EP') as F'. cbn zeta in F, F'.
    set (c := ClassID (needed n)) in *. set (c' := ClassID (needed n')) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16). destruct F' as (Hn' & Hc' & X0' & XM' & XU' & XS' & S16' & RZ' & RZ16').
    destruct (Z.eq_dec c c') as [Ec|Nc].
    +
      destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & P4).
      destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
      apply list_relations.list.NoDup_app in ND as (_ & _ & ND). apply list_relations.list.NoDup_app in ND as (_ & _ & ND). apply list_relations.list.NoDup_app in ND as (ND & _ & _).
      unfold live_ids in ND.
      pose proof (nodup_map_sfilter_pos _ _ (fun bn : Z * Z => (fst bn - rz (snd bn) - region_beg (ag_spacebeg (aa_geom A)) c) / 16)
                    (fun bn : Z * Z => is_primary (snd bn) && (ClassID (needed (snd bn)) =? c)) (aa_live A) i j (b, n) (b', n') ND Hij Hi Hj) as NE.
      cbn [fst snd] in NE. rewrite EP, EP' in NE. fold c c' in NE. rewrite <- Ec in NE. rewrite Z.eqb_refl in NE. specialize (NE eq_refl eq_refl).
      rewrite <- Ec in *. pose proof (Size_pos c Hc) as SPc.
      assert (NX : b - rz n - region_beg (ag_spacebeg (aa_geom A)) c <> b' - rz n' - region_beg (ag_spacebeg (aa_geom A)) c) by (intros E; apply NE; rewrite E; reflexivity).
      destruct (aligned_apart (Size c) _ _ SPc XM XM' NX) as [D|D]; [left | right]; lia.
    +
      unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. pose proof (Size_pos c Hc). pose proof (Size_pos c' Hc').
      assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; [left | right]; nia.
  -
    pose proof (live_prim_facts A rho tp md b n HA Hin EP) as F. cbn zeta in F. set (c := ClassID (needed n)) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (live_sec_facts A rho tp md b' n' HA Hin' EP') as (k & ch & Hk & Eb & Hn1 & Hend & _ & _). pose proof (rz_sec n' Hn1 EP') as RZs.
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, PG in *. pose proof (Size_pos c Hc).
    destruct DS as [DS|DS]; [right | left]; nia.
  -
    pose proof (live_prim_facts A rho tp md b' n' HA Hin' EP') as F. cbn zeta in F. set (c := ClassID (needed n')) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (live_sec_facts A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _). pose proof (rz_sec n Hn1 EP) as RZs.
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, PG in *. pose proof (Size_pos c Hc).
    destruct DS as [DS|DS]; [left | right]; nia.
  -
    destruct (live_sec_facts A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _).
    destruct (live_sec_facts A rho tp md b' n' HA Hin' EP') as (k' & ch' & Hk' & Eb' & Hn1' & Hend' & _ & _).
    pose proof (rz_sec n Hn1 EP) as RZs. pose proof (rz_sec n' Hn1' EP') as RZs'.
    destruct HI3 as (_ & _ & SEC3 & _ & _ & ND6 & _).
    apply list_relations.list.NoDup_app in ND6 as (ND6 & _ & _).
    pose proof (nodup_map_filter_pos _ _ (fun bn : Z * Z => fst bn) (fun bn : Z * Z => negb (is_primary (snd bn))) (aa_live A) i j (b, n) (b', n') ND6 Hij Hi Hj) as NE.
    cbn [fst snd] in NE. rewrite EP, EP' in NE. specialize (NE eq_refl eq_refl).
    destruct (Nat.eq_dec k k') as [Ek|Nk].
    + exfalso. subst k'. rewrite Hk in Hk'. injection Hk' as <-. apply NE. lia.
    + destruct (SEC3 k ch Hk) as (_ & _ & _ & _ & DJ & _). destruct (DJ k' ch' Hk' Nk) as [D|D]; unfold PG in *; [left | right]; lia.
Qed.

Lemma live_id_in : ltac2:(tb__ "0|0|
S1dS17S0S0S0S2fS29S0S0A2S25S0S0R3R2A4S16R4A1A3S9S26SeR3A1S2dA3S9S0S10S13R4A1A1R3A3S2fS0S6S4S4R6SdR5A1A2SfS1aR8A1R4A2A2Z10A2S34R8R7R4A3A3F_;F_;F_;Fc;Fn;Fb;FA;FG;").
Proof.
  intros G A b n c Hin HP Hc. unfold live_ids. apply in_map_iff. exists (b, n). split; [reflexivity|].
  apply list_elem_of_In. apply list_basics.list.list_elem_of_filter. split; [|apply list_elem_of_In; exact Hin].
  cbn [snd]. rewrite HP, Hc, Z.eqb_refl. exact I.
Qed.

Lemma slot_not_live : ltac2:(tb__ "0|2|
S17S32S27S36Q40A1A1S31S0S0S0S33Vsegs;R7R6R5R4A5S8S1Z1R4A2S1R4Z1eA2A2S2fS0R4S2eS0S21S35S1eS1bR9A1R5S20A4M0A1S1fG0A1A3A3S8S1S2SfS1aS19RaA1A1R6A2S7Z10R5A2A2M1R4A2S5R4S2G1S12R6A1A2A2A2SbS38S16RbA1R5A2A1F_;F_;F_;F_;Fz;Fx;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c x z HA Hc Hx Hz (b & n & Hin & Hzb).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite kSpaceSize_val in SP2.
  destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & P4).
  destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND & _).
  destruct (N7 x Hx) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia. change (2 ^ 4) with 16 in X2, X3.
  pose proof (Size_pos c Hc) as SPc.
  destruct (is_primary n) eqn:EP.
  - pose proof (live_prim_facts A rho tp md b n HA Hin EP) as F. cbn zeta in F. set (c' := ClassID (needed n)) in *.
    destruct F as (Hn & Hc' & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (Z.eq_dec c' c) as [Ec|Nc].
    +
      pose proof (live_id_in (aa_geom A) A b n c Hin EP Ec) as Hid. rewrite Ec in *.
      set (o := b - rz n - region_beg (ag_spacebeg (aa_geom A)) c) in *.
      assert (NE : x <> o / 16).
      { intros E. apply list_relations.list.NoDup_app in ND as (_ & D1 & ND). apply list_relations.list.NoDup_app in ND as (_ & D2 & _).
        apply in_app_or in Hx as [Hf|Hcch].
        - apply (D1 x (proj2 (list_elem_of_In _ _) Hf)). apply list_elem_of_In. apply in_or_app. right. apply in_or_app. left. rewrite E. exact Hid.
        - apply (D2 x (proj2 (list_elem_of_In _ _) Hcch)). apply list_elem_of_In. apply in_or_app. left. rewrite E. exact Hid. }
      assert (O16 : o = 16 * (o / 16)).
      { assert (D16 : (16 | o)) by (apply (Z.divide_trans _ (Size c)); [apply Z.mod_divide; [lia | exact S16] | apply Z.mod_divide; [lia | exact XM]]).
        destruct D16 as [q Eq]. rewrite Eq. rewrite Z.div_mul by lia. lia. }
      assert (NX : 16 * x <> o) by lia.
      rewrite Z.mul_comm in X2.
      destruct (aligned_apart (Size c) (16 * x) o SPc X2 XM NX) as [D|D]; unfold o in *; lia.
    +
      unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. pose proof (Size_pos c' Hc').
      assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; nia.
  - destruct (live_sec_facts A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _).
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, PG in *. destruct DS as [DS|DS]; nia.
Qed.

End WithSegs.
End LiveGeom.

