(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the runs, call checks and facts of A/e4.v (Start5States), A/fn.v (Start5CallStates) and A/ec.v (Start5bStates): each over the states of A/StartRegenS2b.v, for both values of CONFIG_RSEQ, proved per value by the recorded proofs; with the equations that give the eager mmap nodes' grant states as A/StartRegenS2b.v's. *)
(* Segment 5's runs, call checks and facts (the lemmas of A/e4.v Start5States, A/fn.v
   Start5CallStates and A/ec.v Start5bStates that A/fl.v Start5 reads), made of the states
   A/StartRegenS2b.v computes, each for both values of CONFIG_RSEQ ([intros [|]], then the
   recorded proof).  With them, the equations that give the grant state the eager mmap node of
   A/e7.v builds from [E r] ([eager_ok]) as the state A/StartRegenS2b.v names: a conversion the
   segment proofs made on the recorded states, which a free flag no longer reduces. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code e2 StartDefsA Start4States e4 e7 fh fi fj fn ec StartRegenS2 StartRegenS2b.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2.Start4R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2b.Start5R.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* A/e4.v Start5States. *)
Lemma run12a : forall r : bool, (sym_runA segsA 4000%nat [RIP_ENTRY; ECALL_MMAP] (S_s12ok r) true) = (Some [mkLeafA (L12r r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run12_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k12d r)) true) = (Some [mkLeafA (SPIN12 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin12 : forall r : bool, (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN12 r) true) = (Some [mkLeafA (SPIN12 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L12x_eq : forall r : bool, (mkAX (unknown_obj_at (ax_S (L12r r)) 0%nat) [rX12] (SLit SHB)) = (L12x r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_L12u : forall r : bool, (same_but_objs (ax_S (L12r r)) (unknown_obj_at (ax_S (L12r r)) 0%nat)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L12r_facts35 : forall r : bool, ((existsb (sprop_eqb (SPEq (SAlu ALU_SLL (SVar 35%positive) (SLit 3)) (SVar 34%positive))) (ss_facts (ax_S (L12r r)))) = true) /\ ((existsb (sprop_eqb (SPUle (SVar 35%positive) (SLit ((2 ^ 61) - 1)))) (ss_facts (ax_S (L12r r)))) = true).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma L12r_facts1 : forall r : bool, ((existsb (sprop_eqb (SPAlign 1%positive 4)) (ss_facts (ax_S (L12r r)))) = true) /\ (((existsb (sprop_eqb (SPUle (SLit 140735340871680) (SVar 1%positive))) (ss_facts (ax_S (L12r r)))) = true) /\ ((existsb (sprop_eqb (SPUle (SVar 1%positive) (SLit 140737488355104))) (ss_facts (ax_S (L12r r)))) = true)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma split12_ok : forall r : bool, (split_chain (ax_S (L12x r)) splits12) = (Some (C12c r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma o12rtc2_nth : forall r : bool, (nth_error (ss_objs (C12c r)) 13%nat) = (Some (o12rtc2 r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C12d_eq : forall r : bool, (replace_obj_at (C12c r) 13%nat (o12rtc2a r)) = (C12d r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_C12d : forall r : bool, (same_but_objs (C12c r) (replace_obj_at (C12c r) 13%nat (o12rtc2a r))) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma o12rtc2a_nth : forall r : bool, (nth_error (ss_objs (C12d r)) 13%nat) = (Some (o12rtc2a r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C12e_eq : forall r : bool, (replace_obj_at (C12d r) 13%nat (o12rtc2b r)) = (C12e r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_C12e : forall r : bool, (same_but_objs (C12d r) (replace_obj_at (C12d r) 13%nat (o12rtc2b r))) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rtc2_clear : forall r : bool, ((cells_clear_lit (ob_cells (o12rtc2 r)) 991472 8) = true) /\ ((cells_clear_lit (ob_cells (o12rtc2a r)) 991464 8) = true).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

(* A/fn.v Start5CallStates. *)
Lemma entails12 : forall r : bool, (entails_frA (C12 r) Pre_rip (s12 r)) = (Some (R12 r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma callcheck12 : forall r : bool, (call_checkA (C12 r) Pre_rip (s12 r) (R12 r) (map la_state Posts_rip)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP12_eq : forall r : bool, (import_postA (s12 r) Pre_rip P_ret (C12 r) (R12 r)) = (IP12 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP12f_eq : forall r : bool, (ax_with_facts (ax_setX (IP12 r) []) ((ss_facts (ax_S (IP12 r))) ++ ss_facts (C12e r))) = (IP12f r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C12e_facts_below : forall r : bool, (forallb (sprop_below 37%positive) (ss_facts (C12e r))) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run12c : forall r : bool, (sym_runA segsA 6000%nat [ECALL_MMAP] (IP12f r) true) = (Some [mkLeafA (E_s13 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13a_eq : forall r : bool, (move_obj_last (ax_S (E_s13 r)) 0%nat) = (T13a r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T13a : forall r : bool, (same_but_objs (ax_S (E_s13 r)) (T13a r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13a_split : forall r : bool, (ss_objs (T13a r)) = ((ss_objs (T13b r)) ++ [ostk13 r]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13b_eq : forall r : bool, (set_objs (T13a r) (ss_objs (T13b r))) = (T13b r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13c_eq : forall r : bool, move_obj_last (T13b r) 3 = (T13c r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T13c : forall r : bool, (same_but_objs (T13b r) (T13c r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13d_eq : forall r : bool, (mkSS (ss_pc (T13c r)) (ss_regs (T13c r)) (ss_fregs (T13c r)) (ss_fcsr (T13c r)) (ss_resv (T13c r)) ((ss_objs (T13c r)) ++ [mstk13]) (ss_facts (T13c r)) (ss_next (T13c r)) (ss_lenient (T13c r))) = (T13d r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13e_eq : forall r : bool, (merge_objs_at (T13d r) 23%nat) = (Some (T13e r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13f_eq : forall r : bool, move_obj_last (T13e r) 3 = (T13f r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T13f : forall r : bool, (same_but_objs (T13e r) (T13f r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13g_eq : forall r : bool, (merge_objs_at (T13f r) 22%nat) = (Some (T13g r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s13g_at : forall r : bool, ((ss_pc (ax_S (E_s13g r))) = ECALL_MMAP) /\ (((ss_next (ax_S (E_s13g r))) = 77%positive) /\ (((instr_at segsA (ss_pc (ax_S (E_s13g r)))) = (Some Ecall)) /\ (((length (ss_objs (T13b r))) = 24%nat) /\ (((length (ss_objs (ax_S (E_s13 r)))) = 25%nat) /\ (((length (ss_objs (T13e r))) = 24%nat) /\ ((ax_X (E_s13 r)) = [])))))).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

(* A/ec.v Start5bStates. *)
Lemma run13_ok : forall r : bool, (sym_runA segsA 3000%nat [ECALL_MMAP] (S_s13ok r) true) = (Some [mkLeafA (E_s14 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run13_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_s13g r)) true) = (Some [mkLeafA (SPIN13 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin13 : forall r : bool, (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN13 r) true) = (Some [mkLeafA (SPIN13 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run14_ok : forall r : bool, (sym_runA segsA 3000%nat [ECALL_MUNMAP; ECALL_MMAP] (S_s14ok r) true) = (Some [mkLeafA (E_s15 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run14_fail : forall r : bool, (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_s14 r)) true) = (Some [mkLeafA (SPIN14 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin14 : forall r : bool, (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN14 r) true) = (Some [mkLeafA (SPIN14 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15_split : forall r : bool, (ss_objs (ax_S (E_s15 r))) = ((ss_objs (ax_S (E_s15u r))) ++ [last (ss_objs (ax_S (E_s15 r))) (mmap_obj 78%positive 4096)]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15u_eq : forall r : bool, (ax_setS (E_s15 r) (set_objs (ax_S (E_s15 r)) (ss_objs (ax_S (E_s15u r))))) = (E_s15u r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15u_facts : forall r : bool, ((existsb (sprop_eqb (SPUle (SVar 1%positive) (SLit 140737488355104))) (ss_facts (ax_S (E_s15u r)))) = true) /\ (((existsb (sprop_eqb (SPEq (SAlu ALU_SLL (SVar 35%positive) (SLit 3)) (SVar 34%positive))) (ss_facts (ax_S (E_s15u r)))) = true) /\ (((existsb (sprop_eqb (SPUle (SVar 35%positive) (SLit ((2 ^ 61) - 1)))) (ss_facts (ax_S (E_s15u r)))) = true) /\ ((existsb (sprop_eqb (SPAlign 1%positive 4)) (ss_facts (ax_S (E_s15u r)))) = true))).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

(* The grant states of the eager mmap node (A/e7.v [eager_ok]) over the computed states. *)
Lemma S_s12ok_eq : forall r : bool, eager_ok (E_k12d r) 4096 37%positive = S_s12ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S_s13ok_eq : forall r : bool, eager_ok (E_s13g r) 4096 78%positive = S_s13ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S_s14ok_eq : forall r : bool, eager_ok (E_s14 r) 4096 79%positive = S_s14ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
