(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF BzCSewH BzCSortPost BzCLemmasMs BzCLemmasMs4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsFs BzCScanF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsBs BzCFactsBs2 BzCFactsBs3 BzCFactsBs4 BzCLemmasMs6 CmpCut.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewH OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortPost OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCScanF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2.BzCFactsMs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2 ms_ro_init ms_sh_shift ms_sh_pass ms_shell ms_step1 ms_copy_init
               ms_copy_fwd ms_copy_bwd ms_mark ms_shifts ms_quad ms_big ms_bigs mainSort blockSort mainQSort3 mqs_loop mainSimpleSort find_orig].
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma step1_noexit_budget : forall n qoff nb ss j s,
  (s_exit s = false -> 0 <= s_budget s) ->
  s_exit (ms_step1 n qoff nb ss j s) = false -> 0 <= s_budget (ms_step1 n qoff nb ss j s).
Proof.
  induction n as [|n IH]; intros qoff nb ss j s H; [exact H|].
  rewrite ms_step1_S. destruct (s_exit s) eqn:E; [intros C; rewrite E in C; discriminate|].
  destruct (j =? ss); [apply IH; intros _; exact (H eq_refl)|]. cbv zeta.
  destruct (negb (has_setmask (zget (s_ft s) (Z.shiftl ss 8 + j)))).
  - destruct (clearmask (zget (s_ft s) (Z.shiftl ss 8 + j)) <? clearmask (zget (s_ft s) (Z.shiftl ss 8 + j + 1)) - 1).
    + destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 budget] mql].
      destruct (Z.ltb_spec budget 0) as [BL|BG].
      * cbn [s_exit]. intros; discriminate.
      * apply IH. cbn [s_exit s_budget]. intros _. exact BG.
    + apply IH. cbn [s_exit s_budget]. intros _. exact (H eq_refl).
  - apply IH. cbn [s_exit s_budget]. intros _. exact (H eq_refl).
Qed.

Lemma big_noexit_budget : forall ro qoff nb i s,
  (s_exit s = false -> 0 <= s_budget s) ->
  s_exit (ms_big ro qoff nb i s) = false -> 0 <= s_budget (ms_big ro qoff nb i s).
Proof.
  intros ro qoff nb i s H. rewrite ms_big_eq. cbv zeta.
  pose proof (step1_noexit_budget 256 qoff nb (zget ro i) 0 s H) as B.
  set (s1 := ms_step1 256 qoff nb (zget ro i) 0 s) in *. clearbody s1.
  destruct (s_exit s1) eqn:EX; [intros C; rewrite EX in C; discriminate|].
  destruct (ms_copy_init _ _ _ _ _ _) as [cs ce]. destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[a1 cs0] j1].
  destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[a3 ce0] j2]. cbn [s_budget s_exit]. intros _. exact (B eq_refl).
Qed.

Lemma bigs_noexit_budget : forall n ro qoff nb i s,
  (s_exit s = false -> 0 <= s_budget s) ->
  s_exit (ms_bigs n ro qoff nb i s) = false -> 0 <= s_budget (ms_bigs n ro qoff nb i s).
Proof.
  induction n as [|n IH]; intros ro qoff nb i s H; [exact H|].
  rewrite ms_bigs_S. cbv zeta.
  pose proof (big_noexit_budget ro qoff nb i s H) as B.
  set (X := ms_big ro qoff nb i s) in *. clearbody X.
  destruct (s_exit X) eqn:EX; [intros C; rewrite EX in C; discriminate|].
  apply IH. intros _. exact (B eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E.
  Variable e : est.
  Hypothesis OK1 : zbok (e_arr1 e).
  Hypothesis BB : zbok (e_arr2 e).
  Hypothesis FTW : forall i, 0 <= zget (e_ftab e) i < 4294967296.
  Hypothesis NB : 1 <= e_nblock e <= 899990.

  Let n := e_nblock e.

  (* [comment removed for export] *)
  Lemma bp_mainSort_eq :
    mainSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew znew znew znew (bp_qoff e) (bp_n e) (bp_budget0 e) =
    let st := bp_ms e in
    MSR (s_a1 st) (s_a2 st) (s_ft st) (s_budget st) (bp_ro6 e) (s_bd st) (s_cs st) (s_ce st) (s_mql st) (s_nqs st).
  Proof.
    cbv zeta. apply (mainSort_shape (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew znew znew znew (bp_qoff e) (bp_n e) (bp_budget0 e)
             (fun r => r = MSR (s_a1 (bp_ms e)) (s_a2 (bp_ms e)) (s_ft (bp_ms e)) (s_budget (bp_ms e)) (bp_ro6 e) (s_bd (bp_ms e))
                               (s_cs (bp_ms e)) (s_ce (bp_ms e)) (s_mql (bp_ms e)) (s_nqs (bp_ms e)))).
    intros a2a ft2 x1 a1a ft4 x2 bd ro st E1 E2 E3 Est.
    assert (H1 : bp_r1 e = (a2a, ft2, x1)).
    { rewrite E_r1, E_ft0, E_j0. unfold bp_a2, bp_ft. exact E1. }
    assert (Ha2r : bp_a2r e = a2a) by (rewrite E_a2r, H1; reflexivity).
    assert (Hft1 : bp_ft1 e = ft2) by (rewrite E_ft1, H1; reflexivity).
    assert (Ha2o : bp_a2o e = ms_overshoot 34 a2a (bp_qoff e) (bp_n e) 0) by (rewrite E_a2o, Ha2r; reflexivity).
    assert (H4 : bp_r4 e = (a1a, ft4, x2)).
    { rewrite E_r4, E_ft3, E_s0, Hft1, Ha2o. unfold bp_a1. exact E2. }
    assert (Ha1r : bp_a1r e = a1a) by (rewrite E_a1r, H4; reflexivity).
    assert (Hft4 : bp_ft4 e = ft4) by (rewrite E_ft4, H4; reflexivity).
    assert (H5 : bp_bd5 = bd /\ bp_ro5 = ro).
    { unfold bp_bd5, bp_ro5. rewrite E3. split; reflexivity. }
    destruct H5 as [Hbd5 Hro5].
    assert (Hro6 : bp_ro6 e = ms_shell 8 ro ft4 364) by (unfold bp_ro6; rewrite Hro5, Hft4; reflexivity).
    unfold bp_ms, bp_S0. rewrite Hro6, Ha1r, Ha2o, Hft4, Hbd5. subst st. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bp_ms_facts :
    let st := bp_ms e in
    zbok (s_a1 st) /\ zbok (s_a2 st) /\ (forall i, 0 <= zget (s_ft st) i < 4294967296) /\
    (s_exit st = false -> 0 <= s_budget st) /\
    (0 <= s_budget st -> fm_perm (s_a1 st) n).
  Proof.
    cbv zeta.
    pose proof (mainSort_post (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew znew znew znew (bp_qoff e) (bp_n e) (bp_budget0 e)
                  BB OK1 ltac:(unfold bp_n; lia) (QO e)) as MP.
    pose proof (mainSort_ftab (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew znew znew znew (bp_qoff e) (bp_n e) (bp_budget0 e)
                  BB ltac:(unfold bp_n; lia) (QO e) FTW) as MF.
    rewrite bp_mainSort_eq in MP, MF. cbv zeta in MP. cbn [mr_ptr mr_block mr_budget mr_ftab] in MP, MF.
    cps_destruct MP as (Z1 & Z2 & _ & PM).
    split; [exact Z1|]. split; [exact Z2|]. split; [exact MF|]. split.
    - apply bigs_noexit_budget. unfold bp_S0. cbn [s_exit s_budget]. intros _. unfold bp_budget0. unfold bp_n. pose proof (budget0_rng (e_nblock e) ltac:(lia)). lia.
    - intros Hb. replace n with (bp_n e) by reflexivity. apply (proj1 (PM ltac:(apply Z.ltb_ge; exact Hb))).
  Qed.
End E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fs_site_ok : forall a1 a2 ft nb, zbok a1 -> zbok a2 -> bh_w32 ft -> 1 <= nb <= 900000 -> fs_site a1 a2 ft nb.
Proof.
  intros a1 a2 ft nb B1 B2 W NB. unfold fs_site. cbv zeta.
  split; [apply fs_facts_intro; assumption|].
  pose proof (fallbackSort_out a1 a2 ft nb B1 B2 W NB) as FO. cbv zeta in FO. cps_destruct FO as (Z1 & _ & _ & PM & _).
  split; [exact Z1|].
  cps_destruct (fm_perm_onto _ _ PM 0 ltac:(lia)) as (x & Hx & E). exists x. split; [exact Hx| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section X.
  Variable e : est.
  Hypothesis EOK : est_ok e.
  Hypothesis NB : 1 <= e_nblock e <= NBLOCKMAX + 9.

  Let OK1 : zbok (e_arr1 e) := proj1 EOK.
  Let BB : zbok (e_arr2 e) := proj1 (proj2 EOK).
  Let FTW : forall i, 0 <= zget (e_ftab e) i < 4294967296 := proj1 (proj2 (proj2 EOK)).
  Lemma NB' : 1 <= e_nblock e <= 899990. Proof. bz_params. lia. Qed.

  Lemma bsC_small_ok : bsC_small e.
  Proof. intros LT. apply fs_site_ok; [exact OK1| exact BB| exact FTW| pose proof NB'; lia]. Qed.

  Lemma bsD_high_ok : bsD_high e.
  Proof.
    intros GE. cbv zeta. pose proof (bp_ms_facts e OK1 BB FTW NB') as F. cbv zeta in F. cps_destruct F as (Z1 & Z2 & W & NX & PM).
    split.
    - intros EX. split; [exact W|]. apply fs_site_ok; [exact Z1| exact Z2| exact W| pose proof NB'; lia].
    - intros EX. cps_destruct (fm_perm_onto _ _ (PM (NX EX)) 0 ltac:(pose proof NB'; lia)) as (x & Hx & E). exists x. split; [exact Hx| exact E].
  Qed.

  Lemma bsB_big_ok : 10000 <= e_nblock e -> bsB_big e.
  Proof. intros GE cs ce nl nh nd k Hk. unfold bp_S0x. exact (bsB_bigF_ok e BB ltac:(pose proof NB'; lia) cs ce nl nh nd k Hk). Qed.

  Lemma bsB_pr_ok : 10000 <= e_nblock e -> bsB_pr e.
  Proof.
    intros GE x Hx. pose proof NB' as NB2.
    assert (BBr : forall i, 0 <= rd8 (bp_a2 e) i < 256) by (intros i; unfold rd8, bp_a2; apply BB).
    cps_destruct (KpM_onto (bp_a2 e) (bp_n e) ltac:(unfold bp_n; lia) x ltac:(unfold bp_n in *; lia)) as (i & Hi & Ei).
    rewrite <- Ei. rewrite (pt_KpM e BB ltac:(lia) i Hi). unfold bp_n in *. lia.
  Qed.

  Lemma bs_facts_ok : 10000 <= e_nblock e -> bs_facts e.
  Proof. intros GE. apply bs_facts_intro; [exact BB| pose proof NB'; lia]. Qed.
End X.

Theorem bsX_intro : forall e, est_ok e -> 1 <= e_nblock e <= NBLOCKMAX + 9 -> bsX e.
Proof.
  intros e EOK NB. unfold bsX.
  split; [apply bsC_small_ok; assumption|]. split; [apply bsD_high_ok; assumption|].
  intros GE. split; [apply bs_facts_ok; assumption|]. split; [apply bsB_big_ok; assumption| apply bsB_pr_ok; assumption].
Qed.

End ACeilS1.
