(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up checks of B/n1.v (Start4States) and B/ng.v (Start4): each run and fact the fourth start-up segment reads, over the states of B/StartRegenS2.v, for both values of CONFIG_RSEQ, with the segment's state difference for its restatement of E_k8 as E_k8x and the node lemmas' grant states shown to be the per-flag states. *)
(* The runs and facts that B/n1.v (Start4States) and B/ng.v (Start4) proved of the recorded
   states of the fourth start-up segment, made of the states B/StartRegenS2.v computes, each for
   both values of CONFIG_RSEQ ([intros [|]], with [hi] destructed too where the state has it):
   every run reaches the state the next step starts from, the object moves and splits give the
   states named for them, and the merge after the [hi] runs is entailed.  With them, the state
   difference of [E_k8 r] and [E_k8x r] ([sd8]) and its shape, which B/ng.v's [restate8] reads.
   Each computation on a state destructs [r] first. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG SymCall SymHeap SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8 n1 StartRegenS StartRegenS2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS.Start3R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2.Start4R.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma run7_ok : forall r : bool,
  (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k7ok r) true) = (Some [mkLeafA (E_k8 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run7_fail : forall r : bool,
  (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k7 r)) true) = (Some [mkLeafA (SPIN7 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin7 : forall r : bool,
  (sym_runA segsA 2%nat [SPIN_RAR] (SPIN7 r) true) = (Some [mkLeafA (SPIN7 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run8a : forall r : bool,
  (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k8ok r)) true) = (Some [mkLeafA (L8mx r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L8m_eq : forall r : bool,
  noX (L8mx r) = L8m r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run8b : forall r : bool,
  (sym_runA segsA 3000%nat [ECALL_MMAP] (M8 r) true) = (Some [mkLeafA (E_k9 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run9_ok : forall r : bool,
  (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k9ok r) true) = (Some [mkLeafA (E_k10 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run9_fail : forall r : bool,
  (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k9 r)) true) = (Some [mkLeafA (SPIN9 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin9 : forall r : bool,
  (sym_runA segsA 2%nat [SPIN_RAR] (SPIN9 r) true) = (Some [mkLeafA (SPIN9 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run10_ok : forall r : bool,
  (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k10ok r) true) = (Some [mkLeafA (E_k11 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run10_fail : forall r : bool,
  (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k10 r)) true) = (Some [mkLeafA (SPIN10 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin10 : forall r : bool,
  (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN10 r) true) = (Some [mkLeafA (SPIN10 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run11_fail : forall r : bool,
  (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k11 r)) true) = (Some [mkLeafA (SPIN11 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin11 : forall r : bool,
  (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN11 r) true) = (Some [mkLeafA (SPIN11 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run11a : forall r hi : bool,
  (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c r hi)) true) = (Some [mkLeafA (L11mx r hi) RsCut]).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L11m_eq : forall r hi : bool,
  (noX (L11mx r hi)) = (L11m r hi).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_11_eq : forall r hi : bool,
  (move_obj_last (ax_S (L11m r hi)) 13%nat) = (T1_11 r hi).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T1_11 : forall r hi : bool,
  (same_but_objs (ax_S (L11m r hi)) (T1_11 r hi)) = true.
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma split_T2_11 : forall r hi : bool,
  (split_obj_at (T1_11 r hi) 15%nat (SLit 512)) = (Some (T2_11 r hi)).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run11b : forall r hi : bool,
  (sym_runA segsA 6000%nat [ECALL_MMAP] (M11 r hi) true) = (Some [mkLeafA (E_k12c r hi) RsCut]).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k12_split : forall r hi : bool,
  (ss_objs (ax_S (E_k12c r hi))) = ((ss_objs (ax_S (E_k12 r))) ++ [last (ss_objs (ax_S (E_k12c r hi))) objShB6]).
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma merge12_ok : forall r hi : bool,
  (entailsA (ax_setS (E_k12c r hi) (set_objs (ax_S (E_k12c r hi)) (ss_objs (ax_S (E_k12 r))))) (E_k12d r) (infer_sub 36%positive (set_objs (ax_S (E_k12c r hi)) (ss_objs (ax_S (E_k12 r)))) (ax_S (E_k12d r)))) = true.
Proof. intros [|] [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* B/ng.v's restatement of [E_k8 r] as [E_k8x r]: their state difference, per value of the flag. *)
Definition sd8_0 : list (sv * sv) * list sprop := Eval vm_compute in
  match state_diff (ax_S (E_k8 false)) (ax_S (E_k8x false)) with Some p => p | None => ([], []) end.
Definition sd8_1 : list (sv * sv) * list sprop := Eval vm_compute in
  match state_diff (ax_S (E_k8 true)) (ax_S (E_k8x true)) with Some p => p | None => ([], []) end.
Definition sd8 (r : bool) : list (sv * sv) * list sprop := if r then sd8_1 else sd8_0.
Lemma sd8_eq : forall r : bool,
  (state_diff (ax_S (E_k8 r)) (ax_S (E_k8x r))) = (Some (sd8 r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pair8_ok (p : sv * sv) : bool :=
  orb (orb (andb (sv_eqb (fst p) e_rid) (sv_eqb (snd p) ri30)) (andb (sv_eqb (fst p) e_ri) (sv_eqb (snd p) ri30))) (andb (sv_eqb (fst p) e_sb) (sv_eqb (snd p) (SVar 30%positive))).
Lemma sd8_shape : forall r : bool,
  ((forallb pair8_ok (fst (sd8 r))) = true) /\ ((snd (sd8 r)) = F8x).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma swf8x : forall r : bool,
  (swf (ax_S (E_k8x r))) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* The node lemmas' grant states (B/n1.v StartNodes [null_none_ok], [eager_ok]) are the per-flag
   states B/ng.v runs from, and [E_k8x r] is [E_k8 r] with its restated sstate (B/ng.v
   [restate8]); each equation computes the next variable of the state, so it destructs [r]. *)
Lemma S_k7ok_eq : forall r : bool,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.null_none_ok (E_k7 r) 0x2000011000 31 = S_k7ok r.
Proof. intros [|]; reflexivity. Qed.
Lemma S_k9ok_eq : forall r : bool,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.null_none_ok (E_k9 r) 0x800000 33 = S_k9ok r.
Proof. intros [|]; reflexivity. Qed.
Lemma S_k10ok_eq : forall r : bool,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.eager_ok (E_k10 r) 4096 34 = S_k10ok r.
Proof. intros [|]; reflexivity. Qed.
Lemma S_k11ok_eq : forall r : bool,
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.eager_ok (E_k11 r) 65536 35 = S_k11ok r.
Proof. intros [|]; reflexivity. Qed.
Lemma E_k8x_setS : forall r : bool, E_k8x r = ax_setS (E_k8 r) (ax_S (E_k8x r)).
Proof. intros [|]; reflexivity. Qed.
