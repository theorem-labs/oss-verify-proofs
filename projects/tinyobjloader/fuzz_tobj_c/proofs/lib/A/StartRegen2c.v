(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the runs, call checks and facts of A/fl.v (Start6States), A/fm.v, A/g0.v and A/g1.v (Start6Run0-7), A/fq.v (Start6JStates) and A/fs.v (Start6Aux, Start6bStates): each over the states of A/StartRegenS2c.v, for both values of CONFIG_RSEQ, proved per value by the recorded proofs; with the equations that give the join's restated state and the eager mmap node's grant state as A/StartRegenS2c.v's. *)
(* Segment 6's runs, call checks and facts (the lemmas of A/fl.v Start6States, A/fq.v
   Start6JStates and A/fs.v Start6Aux and Start6bStates that A/Start6.v reads, the per-class facts
   [pack16_k] gathering what A/fm.v, A/g0.v and A/g1.v proved of each memset class), made of the
   states A/StartRegenS2c.v computes, each for both values of CONFIG_RSEQ ([intros [|]], then the
   recorded proof; a per-class lemma proves each conjunct by computation, as the recorded class
   lemmas did).  With them, the equations that give [bump_next (ax_S (R16pre r)) 81] and the grant
   state the eager mmap node of A/e7.v builds from [E_s17 r] ([eager_ok]) as the states
   A/StartRegenS2c.v names: conversions the segment proofs made on the recorded states, which a
   free flag no longer reduces. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts e2 StartDefsA e7 e8 Start4States fl Str_memcpy fi fq fs StartRegenS2b StartRegenS2c.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2b.Start5R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2c.Start6R.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* A/fl.v Start6States. *)
Lemma run15b : forall r : bool, (sym_runA segsA 2000%nat [SITE16] (S_s15ok r) true) = (Some [mkLeafA (R16pre r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R16pre_at : forall r : bool, ((ss_pc (ax_S (R16pre r))) = SITE16) /\ (((ss_next (ax_S (R16pre r))) = 79%positive) /\ (((nth 10%nat (ss_regs (ax_S (R16pre r))) (SLit 0)) = a0_16) /\ (((ax_X (R16pre r)) = []) /\ (((ax_base (R16pre r)) = (SLit SHB)) /\ ((length (ss_objs (ax_S (R16pre r)))) = 24%nat))))).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sd16 : forall r : bool, forall t : Z, (In t classes16) -> (((state_diff (R16b r) (R16r r t)) = (Some ([(a0_16, SAlu ALU_ADD (SVar 79%positive) (SLit (c1 t)))], F16c t))) /\ (((swf (R16r r t)) = true) /\ (((swf (R16m r t)) = true) /\ (((swf (ax_S (R16c r t))) = true) /\ (((nth_error (ss_objs (R16r r t)) 21%nat) = (Some (mkObj (SVar 36%positive) (SLit 0) (SLit 4096) ((byte_cells17 0 ES17) ++ []) DZero))) /\ (((same_but_objs (R16r r t) (R16m r t)) = true) /\ (((ss_objs (ax_S (R16c r t))) = (((ss_objs (R16m r t)) ++ [O_lowpg]) ++ [O_ss t])) /\ (((ss_next (R16m r t)) = 81%positive) /\ ((length (ss_objs (R16m r t))) = 24%nat))))))))).
Proof.
  intros [|] t Ht; destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2).
Qed.
(* The conversion A/Start6.v made of the recorded [R16pre] ([change (bump_next (ax_S R16pre) 81)
   with R16b]), per value of the flag. *)
Lemma R16b_bump : forall r : bool, bump_next (ax_S (R16pre r)) 81%positive = R16b r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* A/fq.v Start6JStates. *)
Lemma sd17 : forall r : bool, forall t : Z, (In t classes16) -> (exists nf : list sprop, ((state_diff (bump_next (F17n r t) 83%positive) (ax_S (E_s17 r))) = (Some (DX17 t, nf))) /\ (((forallb (fun f : sprop => existsb (sprop_eqb f) CF16) nf) = true) /\ (((swf (ax_S (E_s17 r))) = true) /\ (((swf (F17n r t)) = true) /\ ((axwf (ax_setS (StartDefsA.noX (F17_of r t)) (F17n r t))) = true))))).
Proof.
  intros [|] t Ht; destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; eexists;
    (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]]]).
Qed.

(* A/fs.v Start6Aux: the facts of each memset class (A/fm.v, A/g0.v, A/g1.v Start6Run0-7), each
   conjunct by computation as the recorded class lemmas proved it. *)
Lemma pack16_0 : forall r : bool, pack16 r 0 (M16_0 r) (s16_0 r) (R16_0 r) (IP16_0 r) (IPm_0 r) (IPr_0 r) (F17_0 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_1 : forall r : bool, pack16 r 1 (M16_1 r) (s16_1 r) (R16_1 r) (IP16_1 r) (IPm_1 r) (IPr_1 r) (F17_1 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_2 : forall r : bool, pack16 r 2 (M16_2 r) (s16_2 r) (R16_2 r) (IP16_2 r) (IPm_2 r) (IPr_2 r) (F17_2 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_3 : forall r : bool, pack16 r 3 (M16_3 r) (s16_3 r) (R16_3 r) (IP16_3 r) (IPm_3 r) (IPr_3 r) (F17_3 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_4 : forall r : bool, pack16 r 4 (M16_4 r) (s16_4 r) (R16_4 r) (IP16_4 r) (IPm_4 r) (IPr_4 r) (F17_4 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_5 : forall r : bool, pack16 r 5 (M16_5 r) (s16_5 r) (R16_5 r) (IP16_5 r) (IPm_5 r) (IPr_5 r) (F17_5 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_6 : forall r : bool, pack16 r 6 (M16_6 r) (s16_6 r) (R16_6 r) (IP16_6 r) (IPm_6 r) (IPr_6 r) (F17_6 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma pack16_7 : forall r : bool, pack16 r 7 (M16_7 r) (s16_7 r) (R16_7 r) (IP16_7 r) (IPm_7 r) (IPr_7 r) (F17_7 r).
Proof.
  intros [|]; unfold pack16; do 14 (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]);
    repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma cls16 : forall r : bool, forall t : Z, (In t classes16) -> pack16 r t (M16_of r t) (s16_of r t) (R16_of r t) (IP16_of r t) (IPm_of r t) (IPr_of r t) (F17_of r t).
Proof.
  intros r t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    [exact (pack16_0 r) | exact (pack16_1 r) | exact (pack16_2 r) | exact (pack16_3 r) | exact (pack16_4 r) | exact (pack16_5 r) | exact (pack16_6 r) | exact (pack16_7 r)].
Qed.

(* A/fs.v Start6bStates. *)
Lemma run17b : forall r : bool, (sym_runA segsA 8000%nat [MALLOC_ENTRY] (S_s17ok r) true) = (Some [mkLeafA (E18 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run17_fail : forall r : bool, (sym_runA segsA 300%nat [SPIN_MMAPORDIE] (fail_state (E_s17 r)) true) = (Some [mkLeafA (SPIN17 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spin17 : forall r : bool, (sym_runA segsA 2%nat [SPIN_MMAPORDIE] (SPIN17 r) true) = (Some [mkLeafA (SPIN17 r) RsCut]).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* The grant state of the eager mmap node (A/e7.v [eager_ok]) at the join's computed state; the
   length is A/Start6.v's [n17] (0xb09000). *)
Lemma S_s17ok_eq : forall r : bool, eager_ok (E_s17 r) 11571200 84%positive = S_s17ok r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
