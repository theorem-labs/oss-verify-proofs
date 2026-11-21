(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up checks of B/np.v (Start6States), B/nt.v and B/nv.v (Start6Run0-7), B/nz.v (Start6JStates), B/o2.v (Start6Aux) and B/o3.v (Start6bStates): each run, call check and fact the sixth start-up segment reads, over the states of B/StartRegenS2c.v, for both values of CONFIG_RSEQ; the join's restatement names A/StartDefsA.v's noX, as B/nz.v's does. *)
(* The runs, memset call checks and facts that B/np.v, B/nt.v, B/nv.v, B/nz.v, B/o2.v and B/o3.v
   proved of the recorded states of the sixth start-up segment, made of the states B/StartRegenS2c.v
   computes, each for both values of CONFIG_RSEQ ([intros [|]]): the run to the memset site, the
   restatement of each memset class ([sd16]), each class's call and run ([pack16_t], [cls16]), the
   join ([sd17]) and the run to malloc's entry.  Each computation on a state destructs [r] first. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG SymCall SymHeap SymObj SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8 n1 n4 n5 np nz o3 Str_memcpy StartRegenS2b StartRegenS2c.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2b.Start5R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2c.Start6R.
Close Scope bv_scope.
Open Scope Z_scope.

(* B/np.v Start6States. *)
Lemma run15b : forall r : bool,
  (sym_runA segsA 2000%nat [SITE16] (S_s15ok r) true) = (Some [mkLeafA (R16pre r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R16pre_at : forall r : bool,
  ((ss_pc (ax_S (R16pre r))) = SITE16) /\ (((ss_next (ax_S (R16pre r))) = 79%positive) /\ (((nth 10%nat (ss_regs (ax_S (R16pre r))) (SLit 0)) = a0_16) /\ (((ax_X (R16pre r)) = []) /\ (((ax_base (R16pre r)) = (SLit SHB)) /\ ((length (ss_objs (ax_S (R16pre r)))) = 24%nat))))).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sd16 : forall (r : bool) (t : Z),
  (In t classes16) -> ((state_diff (R16b r) (R16r r t)) = (Some ([(a0_16, SAlu ALU_ADD (SVar 79%positive) (SLit (c1 t)))], F16c t))) /\ (((swf (R16r r t)) = true) /\ (((swf (R16m r t)) = true) /\ (((swf (ax_S (R16c r t))) = true) /\ (((nth_error (ss_objs (R16r r t)) 21%nat) = (Some (mkObj (SVar 36%positive) (SLit 0) (SLit 4096) ((byte_cells17 0 ES17) ++ []) DZero))) /\ (((same_but_objs (R16r r t) (R16m r t)) = true) /\ (((ss_objs (ax_S (R16c r t))) = (((ss_objs (R16m r t)) ++ [O_lowpg]) ++ [O_ss t])) /\ (((ss_next (R16m r t)) = 81%positive) /\ ((length (ss_objs (R16m r t))) = 24%nat)))))))).
Proof.
  intros r t Ht. destruct r; destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2).
Qed.

(* B/nt.v and B/nv.v Start6Run0-7, and B/o2.v Start6Aux: each memset class. *)
Lemma run16_0 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 0)) true = Some [mkLeafA (M16_0 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_0 : forall r : bool,
  entails_frA (M16_0 r) Pre_mszA (s16_0 r) = Some (R16_0 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_0 : forall r : bool,
  call_checkA (M16_0 r) Pre_mszA (s16_0 r) (R16_0 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_0_eq : forall r : bool,
  import_postA (s16_0 r) Pre_mszA (liftA P_msz) (M16_0 r) (R16_0 r) = IP16_0 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_0 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_0 r) true = Some [mkLeafA (F17_0 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_0 : forall r : bool,
  pack16 r 0 (M16_0 r) (s16_0 r) (R16_0 r) (IP16_0 r) (IPm_0 r) (IPr_0 r) (F17_0 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_0 r)|]. split; [exact (fr16_0 r)|]. split; [exact (cc16_0 r)|]. split; [exact (IP16_0_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_0 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_1 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 1)) true = Some [mkLeafA (M16_1 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_1 : forall r : bool,
  entails_frA (M16_1 r) Pre_mszA (s16_1 r) = Some (R16_1 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_1 : forall r : bool,
  call_checkA (M16_1 r) Pre_mszA (s16_1 r) (R16_1 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_1_eq : forall r : bool,
  import_postA (s16_1 r) Pre_mszA (liftA P_msz) (M16_1 r) (R16_1 r) = IP16_1 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_1 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_1 r) true = Some [mkLeafA (F17_1 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_1 : forall r : bool,
  pack16 r 1 (M16_1 r) (s16_1 r) (R16_1 r) (IP16_1 r) (IPm_1 r) (IPr_1 r) (F17_1 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_1 r)|]. split; [exact (fr16_1 r)|]. split; [exact (cc16_1 r)|]. split; [exact (IP16_1_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_1 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_2 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 2)) true = Some [mkLeafA (M16_2 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_2 : forall r : bool,
  entails_frA (M16_2 r) Pre_mszA (s16_2 r) = Some (R16_2 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_2 : forall r : bool,
  call_checkA (M16_2 r) Pre_mszA (s16_2 r) (R16_2 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_2_eq : forall r : bool,
  import_postA (s16_2 r) Pre_mszA (liftA P_msz) (M16_2 r) (R16_2 r) = IP16_2 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_2 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_2 r) true = Some [mkLeafA (F17_2 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_2 : forall r : bool,
  pack16 r 2 (M16_2 r) (s16_2 r) (R16_2 r) (IP16_2 r) (IPm_2 r) (IPr_2 r) (F17_2 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_2 r)|]. split; [exact (fr16_2 r)|]. split; [exact (cc16_2 r)|]. split; [exact (IP16_2_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_2 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_3 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 3)) true = Some [mkLeafA (M16_3 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_3 : forall r : bool,
  entails_frA (M16_3 r) Pre_mszA (s16_3 r) = Some (R16_3 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_3 : forall r : bool,
  call_checkA (M16_3 r) Pre_mszA (s16_3 r) (R16_3 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_3_eq : forall r : bool,
  import_postA (s16_3 r) Pre_mszA (liftA P_msz) (M16_3 r) (R16_3 r) = IP16_3 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_3 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_3 r) true = Some [mkLeafA (F17_3 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_3 : forall r : bool,
  pack16 r 3 (M16_3 r) (s16_3 r) (R16_3 r) (IP16_3 r) (IPm_3 r) (IPr_3 r) (F17_3 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_3 r)|]. split; [exact (fr16_3 r)|]. split; [exact (cc16_3 r)|]. split; [exact (IP16_3_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_3 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_4 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 4)) true = Some [mkLeafA (M16_4 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_4 : forall r : bool,
  entails_frA (M16_4 r) Pre_mszA (s16_4 r) = Some (R16_4 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_4 : forall r : bool,
  call_checkA (M16_4 r) Pre_mszA (s16_4 r) (R16_4 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_4_eq : forall r : bool,
  import_postA (s16_4 r) Pre_mszA (liftA P_msz) (M16_4 r) (R16_4 r) = IP16_4 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_4 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_4 r) true = Some [mkLeafA (F17_4 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_4 : forall r : bool,
  pack16 r 4 (M16_4 r) (s16_4 r) (R16_4 r) (IP16_4 r) (IPm_4 r) (IPr_4 r) (F17_4 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_4 r)|]. split; [exact (fr16_4 r)|]. split; [exact (cc16_4 r)|]. split; [exact (IP16_4_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_4 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_5 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 5)) true = Some [mkLeafA (M16_5 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_5 : forall r : bool,
  entails_frA (M16_5 r) Pre_mszA (s16_5 r) = Some (R16_5 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_5 : forall r : bool,
  call_checkA (M16_5 r) Pre_mszA (s16_5 r) (R16_5 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_5_eq : forall r : bool,
  import_postA (s16_5 r) Pre_mszA (liftA P_msz) (M16_5 r) (R16_5 r) = IP16_5 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_5 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_5 r) true = Some [mkLeafA (F17_5 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_5 : forall r : bool,
  pack16 r 5 (M16_5 r) (s16_5 r) (R16_5 r) (IP16_5 r) (IPm_5 r) (IPr_5 r) (F17_5 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_5 r)|]. split; [exact (fr16_5 r)|]. split; [exact (cc16_5 r)|]. split; [exact (IP16_5_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_5 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_6 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 6)) true = Some [mkLeafA (M16_6 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_6 : forall r : bool,
  entails_frA (M16_6 r) Pre_mszA (s16_6 r) = Some (R16_6 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_6 : forall r : bool,
  call_checkA (M16_6 r) Pre_mszA (s16_6 r) (R16_6 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_6_eq : forall r : bool,
  import_postA (s16_6 r) Pre_mszA (liftA P_msz) (M16_6 r) (R16_6 r) = IP16_6 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_6 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_6 r) true = Some [mkLeafA (F17_6 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_6 : forall r : bool,
  pack16 r 6 (M16_6 r) (s16_6 r) (R16_6 r) (IP16_6 r) (IPm_6 r) (IPr_6 r) (F17_6 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_6 r)|]. split; [exact (fr16_6 r)|]. split; [exact (cc16_6 r)|]. split; [exact (IP16_6_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_6 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma run16_7 : forall r : bool,
  sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r 7)) true = Some [mkLeafA (M16_7 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr16_7 : forall r : bool,
  entails_frA (M16_7 r) Pre_mszA (s16_7 r) = Some (R16_7 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_7 : forall r : bool,
  call_checkA (M16_7 r) Pre_mszA (s16_7 r) (R16_7 r) (map la_state Posts_mszA) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP16_7_eq : forall r : bool,
  import_postA (s16_7 r) Pre_mszA (liftA P_msz) (M16_7 r) (R16_7 r) = IP16_7 r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17x_7 : forall r : bool,
  sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_7 r) true = Some [mkLeafA (F17_7 r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pack16_7 : forall r : bool,
  pack16 r 7 (M16_7 r) (s16_7 r) (R16_7 r) (IP16_7 r) (IPm_7 r) (IPr_7 r) (F17_7 r).
Proof.
  intros r. unfold pack16. split; [exact (run16_7 r)|]. split; [exact (fr16_7 r)|]. split; [exact (cc16_7 r)|]. split; [exact (IP16_7_eq r)|].
  do 9 (split; [destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]).
  split; [exact (run17x_7 r)|]. repeat split; destruct r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma cls16 : forall (r : bool) (t : Z),
  (In t classes16) -> pack16 r t (M16_of r t) (s16_of r t) (R16_of r t) (IP16_of r t) (IPm_of r t) (IPr_of r t) (F17_of r t).
Proof.
  intros r t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    [exact (pack16_0 r) | exact (pack16_1 r) | exact (pack16_2 r) | exact (pack16_3 r) | exact (pack16_4 r) | exact (pack16_5 r) | exact (pack16_6 r) | exact (pack16_7 r)].
Qed.

(* B/nz.v Start6JStates: the join of the eight classes. *)
Lemma sd17 : forall (r : bool) (t : Z),
  (In t classes16) -> exists nf : list sprop, ((state_diff (bump_next (F17n r t) 83%positive) (ax_S (E_s17 r))) = (Some (DX17 t, nf))) /\ (((forallb (fun f : sprop => existsb (sprop_eqb f) CF16) nf) = true) /\ (((swf (ax_S (E_s17 r))) = true) /\ (((swf (F17n r t)) = true) /\ ((axwf (ax_setS (StartDefsA.noX (F17_of r t)) (F17n r t))) = true)))).
Proof.
  intros r t Ht. destruct r; destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; eexists;
    (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]]]).
Qed.

(* B/o3.v Start6bStates. *)
Lemma run17b : forall r : bool,
  (sym_runA segsA 8000%nat [MALLOC_ENTRY] (S_s17ok r) true) = (Some [mkLeafA (E18 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17_fail : forall r : bool,
  (sym_runA segsA 300%nat [SPIN_MMAPORDIE] (fail_state (E_s17 r)) true) = (Some [mkLeafA (SPIN17 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin17 : forall r : bool,
  (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN17 r) true) = (Some [mkLeafA (SPIN17 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
