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
  LB_Logic LB_Kernel LB_Embed LB_Tables LB_Inv LB_Sum LB_Bound LB_Tree LB_StmtA LB_WFree LB_Raw LB_WMalloc LB_Alloc LB_Count MPos CtxMono
  Path PathQ PathCfg.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma raw_malloc_tpath_elim_cfg n s mo p s'' mo' :
  tpath nstep_cfg (raw_malloc n s) mo [] (Ok (p, s'')) mo' ->
  exists cs' p0 s', tpath nstep_cfg (membed (cmalloc (ps_m s) n) s) mo [] (Ok ((cs', p0), s')) mo'
                    /\ s'' = set_m cs' s' /\ p = rres cs' n p0.
Proof.
  intros Hp. unfold raw_malloc, mbind, mget in Hp. rewrite ebind_ret_ok in Hp. cbn [fst snd] in Hp.
  apply (proj1 (tpath_ebind _ _ _ _ _ _ _ _)) in Hp. destruct Hp as [[_ E]|(tr1 & [[cs' p'] s'] & mo1 & tr2 & H1 & H2 & Etr)]; [discriminate E|].
  destruct tr1; [| discriminate Etr]. destruct tr2; [| discriminate Etr]. cbn in H2. destruct H2 as (E1 & -> & _).
  exists cs', p', s'. split; [exact H1|]. inversion E1; subst. destruct p'; auto.
Qed.

Section SUCC_CFG.
Variables (P : Z -> Z) (SMAX ETOT NR RBY NMAXr : Z).
Hypothesis SMAX0 : 0 <= SMAX.
Hypothesis NR0 : 0 <= NR.
Hypothesis RBY0 : 0 <= RBY.
Hypothesis HSMAX : NMETA P <= SMAX.
Hypothesis HETOT : NE P + Z.of_nat (MALLOC_DEPTH + 0) <= ETOT.
Hypothesis HNMAX : NMAXr < 2 ^ 62.
Hypothesis HGAP : forall n, 0 <= n <= NMAXr -> GAPOK n SMAX ETOT NR RBY.

Theorem raw_malloc_all_succ X n s mo :
  QI X P s mo -> ROOMX X P n -> PHI P + R63X X + bigb n <= LBUDGET -> 0 <= n <= NMAXr ->
  LBUDGET <= vm_limit (m_vmmaps mo) -> RSV NR RBY (m_vmmaps mo) ->
  forall p s'' mo', tpath nstep_cfg (raw_malloc n s) mo [] (Ok (p, s'')) mo' -> p <> None.
Proof.
  intros HQI HRX HB Hn Hlim HRSV p s'' mo' Hp0.
  destruct (raw_malloc_tpath_elim_cfg n s mo p s'' mo' Hp0) as (cs' & p0 & s' & Hp & _ & ->).
  pose proof HQI as [(st & L & BL & LS & E & INV & SI & HAQ & HK & HLI & HP) HB0].
  assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; lia).
  destruct (all_succ_path n SMAX ETOT NR RBY SMAX0 RBY0 (HGAP n Hn) (cmalloc (ps_m s) n) (MALLOC_DEPTH + 0) L s mo)
    with (r := Ok ((cs', p0), s')) (mo' := mo') as (cs2 & p2 & s2 & Er).
  - exact (cmalloc_pos (ps_m s) n Hov).
  - apply (qtree_of_QI X P n s st L BL LS); auto; lia.
  - destruct (cmalloc_tok n (ps_m s) (QI_init01 X P s mo HQI)) as (_ & N & _). exact N.
  - constructor; [exact HK| exact HLI| exact Hlim| exact HRSV|].
    pose proof (count_bound x0 st L BL LS P INV SI HAQ eq_refl eq_refl). lia.
  - intros r s3 mo3 Hp3. destruct r as [cs3 q]. cbn [fst].
    pose proof (raw_malloc_LQ X P n ltac:(lia) s mo (conj HQI (conj HRX HB))) as W.
    pose proof (twl_tpath _ _ _ _ _ _ W (raw_malloc_tpath_intro n s mo cs3 q s3 mo3 Hp3)) as Post. cbn [fst snd] in Post.
    assert (HQ' : exists X', QI X' P (set_m cs3 s3) mo3) by (destruct q as [c|]; cbn [rres] in Post; [eexists; apply (proj1 Post)| exists X; exact Post]).
    destruct HQ' as [X' HQ']. pose proof (QI_shift X' P _ _ HQ') as SH. cbn [ps_m set_m] in SH. lia.
  - exact Hp.
  - injection Er as _ Ep _. subst p0. cbn [rres]. discriminate.
Qed.
End SUCC_CFG.

End AC_1.
