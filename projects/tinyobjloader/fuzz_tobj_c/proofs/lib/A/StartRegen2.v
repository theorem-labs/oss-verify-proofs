(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the runs and facts of A/Start4States.v, A/e9.v (Start4) and A/e6.v (Start4Fail): each over the states of A/StartRegenS2.v, for both values of CONFIG_RSEQ, proved per value by the recorded proofs; with the equations that give the node lemmas' grant states as A/StartRegenS2.v's. *)
(* Segment 4's runs and facts (A/Start4States.v's lemmas that A/e9.v Start4 reads, A/e9.v's
   restatement data [sd8], and A/e6.v's fail-path run and CFG check), made of the states
   A/StartRegenS2.v computes, each for both values of CONFIG_RSEQ ([intros [|]], then the recorded
   proof).  With them, the equations that give the grant state a node lemma of A/e7.v builds from
   [E r] ([null_none_ok], [eager_ok]) as the state A/StartRegenS2.v names: a conversion the segment
   proofs made on the recorded states, which a free flag no longer reduces. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts e2 StartDefsA Start4States e4 e5 e7 StartRegenS StartRegenS2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Start4FailCut.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start3R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2.Start4R.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma run7_ok : forall r : bool, (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k7ok r) true) = (Some [mkLeafA (E_k8 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run7_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k7 r)) true) = (Some [mkLeafA (SPIN7 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin7 : forall r : bool, (sym_runA segsA 2%nat [SPIN_RAR] (SPIN7 r) true) = (Some [mkLeafA (SPIN7 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run8a : forall r : bool, (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k8ok r)) true) = (Some [mkLeafA (L8mx r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L8m_eq : forall r : bool, noX (L8mx r) = (L8m r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run8b : forall r : bool, (sym_runA segsA 3000%nat [ECALL_MMAP] (M8 r) true) = (Some [mkLeafA (E_k9 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run9_ok : forall r : bool, (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k9ok r) true) = (Some [mkLeafA (E_k10 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run9_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k9 r)) true) = (Some [mkLeafA (SPIN9 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin9 : forall r : bool, (sym_runA segsA 2%nat [SPIN_RAR] (SPIN9 r) true) = (Some [mkLeafA (SPIN9 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run10_ok : forall r : bool, (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k10ok r) true) = (Some [mkLeafA (E_k11 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run10_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k10 r)) true) = (Some [mkLeafA (SPIN10 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin10 : forall r : bool, (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN10 r) true) = (Some [mkLeafA (SPIN10 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run11_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k11 r)) true) = (Some [mkLeafA (SPIN11 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin11 : forall r : bool, (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN11 r) true) = (Some [mkLeafA (SPIN11 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run11a : forall r : bool, forall hi : bool, (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c r hi)) true) = (Some [mkLeafA (L11mx r hi) RsCut]).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L11m_eq : forall r : bool, forall hi : bool, (noX (L11mx r hi)) = (L11m r hi).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_11_eq : forall r : bool, forall hi : bool, (move_obj_last (ax_S (L11m r hi)) 13%nat) = (T1_11 r hi).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T1_11 : forall r : bool, forall hi : bool, (same_but_objs (ax_S (L11m r hi)) (T1_11 r hi)) = true.
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma split_T2_11 : forall r : bool, forall hi : bool, (split_obj_at (T1_11 r hi) 15%nat (SLit 512)) = (Some (T2_11 r hi)).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run11b : forall r : bool, forall hi : bool, (sym_runA segsA 6000%nat [ECALL_MMAP] (M11 r hi) true) = (Some [mkLeafA (E_k12c r hi) RsCut]).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k12_split : forall r : bool, forall hi : bool, (ss_objs (ax_S (E_k12c r hi))) = ((ss_objs (ax_S (E_k12 r))) ++ [last (ss_objs (ax_S (E_k12c r hi))) objShB6]).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma merge12_ok : forall r : bool, forall hi : bool, (entailsA (ax_setS (E_k12c r hi) (set_objs (ax_S (E_k12c r hi)) (ss_objs (ax_S (E_k12 r))))) (E_k12d r) (infer_sub 36%positive (set_objs (ax_S (E_k12c r hi)) (ss_objs (ax_S (E_k12 r)))) (ax_S (E_k12d r)))) = true.
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* The grant states of the node lemmas (A/e7.v [null_none_ok], [eager_ok]) over the computed exits. *)
Lemma S_k7ok_eq : forall r : bool, null_none_ok (E_k7 r) 0x2000011000 31%positive = S_k7ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S_k9ok_eq : forall r : bool, null_none_ok (E_k9 r) 0x800000 33%positive = S_k9ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S_k10ok_eq : forall r : bool, eager_ok (E_k10 r) 4096 34%positive = S_k10ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S_k11ok_eq : forall r : bool, eager_ok (E_k11 r) 65536 35%positive = S_k11ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* [E_k8 r] restated as [E_k8x r] (A/e9.v [restate8]): the state difference and its facts. *)
Lemma E_k8x_setS : forall r : bool, E_k8x r = ax_setS (E_k8 r) (ax_S (E_k8x r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sd8 (r : bool) : list (sv * sv) * list sprop :=
  match state_diff (ax_S (E_k8 r)) (ax_S (E_k8x r)) with Some p => p | None => ([], []) end.
Lemma sd8_eq : forall r : bool, state_diff (ax_S (E_k8 r)) (ax_S (E_k8x r)) = Some (sd8 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pair8_ok (p : sv * sv) : bool :=
  orb (orb (andb (sv_eqb (fst p) e_rid) (sv_eqb (snd p) ri30)) (andb (sv_eqb (fst p) e_ri) (sv_eqb (snd p) ri30)))
      (andb (sv_eqb (fst p) e_sb) (sv_eqb (snd p) (SVar 30%positive))).
Lemma sd8_shape : forall r : bool, forallb pair8_ok (fst (sd8 r)) = true /\ snd (sd8 r) = F8x.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma swf8x : forall r : bool, swf (ax_S (E_k8x r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* The fail path of the segment's first fixed mmap (A/e6.v Start4Fail). *)
Lemma spin_ok : forall r : bool, sym_runA segsA 2%nat [PC_SPIN] (E_spin r) true = Some [mkLeafA (E_spin r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_s8f : forall r : bool, check_cfgA segsA FUEL1 [PC_OUT; PC_SPIN] 31%positive [F0 r; C2 r] [E_spin r] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
