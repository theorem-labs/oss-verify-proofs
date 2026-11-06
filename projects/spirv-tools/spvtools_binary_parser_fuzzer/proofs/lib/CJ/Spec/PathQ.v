(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode NodesMM Gap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KLink
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_TF2 MI_WFree2 MI_WGroup MI_WSlot MI_WMalloc MI_WEnframe2 MI_Cnt MI_Sim MI_Contracts
  LB_Logic LB_Kernel LB_Embed LB_Tables LB_Inv LB_Sum LB_Bound LB_Tree LB_StmtA LB_WFree LB_Raw LB_WMalloc LB_Alloc LB_Count MPos CtxMono Path.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma twl_tpath {R} B : forall (t : itree node R) mo P r mo',
  twl B t mo P -> tpath nstep t mo [] r mo' -> P r mo'.
Proof.
  induction t as [r0|n k IH]; intros mo P r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & _). exact H.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & E). destruct evs; [| discriminate E]. destruct tr'; [| discriminate E].
    destruct (H _ _ _ Hst) as [_ Hk]. eapply IH; eauto.
Qed.

Lemma qtree_of_QI X P n (s : PState) st L BL LS :
  0 <= n -> strip st = ps_m s -> INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P ->
  Permutation (map xs X) (map bs BL) -> ROOMX X P n -> PHI P + R63X X + bigb n <= LBUDGET ->
  qtree LBUDGET L (cmalloc (ps_m s) n) (fun _ _ => True).
Proof.
  intros Hn E INV SI HAQ HP HRX HB.
  pose proof (R63X_eq _ _ HP) as R63E. pose proof (ROOMX_eq X BL P n HP HRX) as HR.
  assert (HBB : PHI P + R63 BL + bigb n <= LBUDGET + 3 * PGSZ) by (unfold PGSZ; lia).
  rewrite <- E.
  eapply (qtree_of_full8 pans0 pupd0 pans0_range (RR := MREL)).
  - exact (malloc_INVL st L BL LS n INV Hn).
  - exact (malloc_fbnd8 malloc_core_fq_proof st L BL LS P n LBUDGET INV SI HAQ Hn HR HBB).
  - exact (malloc_control pans0 pupd0 pans0_range st n tt).
  - intros; exact I.
Qed.

Lemma QI_shift X P s mo : QI X P s mo -> cshift (ps_m s) <= NMETA P.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & _) _]. rewrite <- E. unfold cshift. cbn [s_ctx strip].
  exact (shift_bound x0 st L BL LS P INV SI HAQ).
Qed.

Lemma QI_init01 X P s mo : QI X P s mo -> cinit (ps_m s) = 0 \/ cinit (ps_m s) = 1.
Proof.
  intros [(st & L & BL & LS & E & INV & _) _]. rewrite <- E. unfold cinit. cbn [s_ctx strip].
  destruct INV as (_ & IA & _). destruct (ia_secret _ IA) as [_ [[H _]|[H _]]]; auto.
Qed.

Definition rres (cs' : mstate) (n : Z) (p : option cptr) : option bptr :=
  match p with Some slot => Some (slot, fresh_off cs' slot n) | None => None end.

Lemma raw_malloc_tpath_intro n s mo cs' p s' mo' :
  tpath nstep (membed (cmalloc (ps_m s) n) s) mo [] (Ok ((cs', p), s')) mo' ->
  tpath nstep (raw_malloc n s) mo [] (Ok (rres cs' n p, set_m cs' s')) mo'.
Proof.
  intros Hp. unfold raw_malloc, mbind, mget. rewrite ebind_ret_ok. cbn [fst snd].
  apply (proj2 (tpath_ebind _ _ _ _ _ _ _ _)). right. exists [], ((cs', p), s'), mo', []. split; [exact Hp|]. split; [| reflexivity].
  cbn. destruct p; cbn; auto.
Qed.

Lemma raw_malloc_tpath_elim n s mo p s'' mo' :
  tpath nstep (raw_malloc n s) mo [] (Ok (p, s'')) mo' ->
  exists cs' p0 s', tpath nstep (membed (cmalloc (ps_m s) n) s) mo [] (Ok ((cs', p0), s')) mo' /\ s'' = set_m cs' s' /\ p = rres cs' n p0.
Proof.
  intros Hp. unfold raw_malloc, mbind, mget in Hp. rewrite ebind_ret_ok in Hp. cbn [fst snd] in Hp.
  apply (proj1 (tpath_ebind _ _ _ _ _ _ _ _)) in Hp. destruct Hp as [[_ E]|(tr1 & [[cs' p'] s'] & mo1 & tr2 & H1 & H2 & Etr)]; [discriminate E|].
  destruct tr1; [| discriminate Etr]. destruct tr2; [| discriminate Etr]. cbn in H2. destruct H2 as (E1 & -> & _).
  exists cs', p', s'. split; [exact H1|]. inversion E1; subst. destruct p'; auto.
Qed.

Section SUCC.
Variables (P : Z -> Z) (SMAX ETOT NR RBY NMAXr : Z).
Hypothesis SMAX0 : 0 <= SMAX.
Hypothesis NR0 : 0 <= NR.
Hypothesis RBY0 : 0 <= RBY.
Hypothesis HSMAX : NMETA P <= SMAX.
Hypothesis HETOT : NE P + Z.of_nat (MALLOC_DEPTH + 0) <= ETOT.
Hypothesis HNMAX : NMAXr < 2 ^ 62.
Hypothesis HGAP : forall n, 0 <= n <= NMAXr -> GAPOK n SMAX ETOT NR RBY.

End SUCC.

End AC_1.
