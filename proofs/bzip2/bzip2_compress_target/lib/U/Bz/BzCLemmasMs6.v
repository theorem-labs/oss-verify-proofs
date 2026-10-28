(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock BzCLemmasMs BzCLemmasMs4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsBs BzCFactsBs2 BzCFactsBs4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD BzCSewF BzCSewH.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2.BzCFactsMs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewH.
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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition est_sorted (e : est) (a1 a2 ft : zarr) : est :=
  EST (e_mode e) (e_state e) (e_avail_in_expect e) a1 a2 ft (find_orig (Z.to_nat (e_nblock e)) a1 0)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).

(* [comment removed for export] *)
Definition fs_site (a1 a2 ft : zarr) (nb : Z) : Prop :=
  let r := fallbackSort a1 a2 ft znew znew znew znew nb in
  fs_facts a1 a2 ft nb /\ zbok (fr_fm r) /\ (exists i, 0 <= i < nb /\ rd32 (fr_fm r) i = 0).

(* [comment removed for export] *)
Definition bp_S0x (e : est) (cs ce nl nh nd : zarr) : mss :=
  MSS (bp_a1r e) (bp_a2o e) (bp_ft4 e) bp_bd5 cs ce (bp_budget0 e) 0 (MQL znew znew znew nl nh nd) false.
Definition bsB_big (e : est) : Prop :=
  forall cs ce nl nh nd k, (k < 256)%nat -> let s' := ms_bigs k (bp_ro6 e) (bp_qoff e) (bp_n e) 0 (bp_S0x e cs ce nl nh nd) in
    s_exit s' = false -> bigF (bp_qoff e) (bp_n e) (bp_ro6 e) (0 + Z.of_nat k) s'.
(* [comment removed for export] *)
Definition bsC_small (e : est) : Prop := e_nblock e < 10000 -> fs_site (e_arr1 e) (e_arr2 e) (e_ftab e) (e_nblock e).
(* [comment removed for export] *)
Definition bsD_high (e : est) : Prop :=
  10000 <= e_nblock e -> let st := bp_ms e in
  (s_exit st = true -> (forall i, 0 <= zget (s_ft st) i < 4294967296) /\ fs_site (s_a1 st) (s_a2 st) (s_ft st) (e_nblock e)) /\
  (s_exit st = false -> exists i, 0 <= i < e_nblock e /\ rd32 (s_a1 st) i = 0).
(* [comment removed for export] *)
Definition bsB_pr (e : est) : Prop := pr (bp_n e) (bp_a1r e) 0 (bp_n e - 1).
(* [comment removed for export] *)
Definition bsX (e : est) : Prop := bsC_small e /\ bsD_high e /\ (10000 <= e_nblock e -> bs_facts e /\ bsB_big e /\ bsB_pr e).

(* [comment removed for export] *)
Lemma ro_init_bd_zero : forall n bd ro i c, (forall c, zget bd c = 0) -> zget (fst (ms_ro_init n bd ro i)) c = 0.
Proof.
  induction n as [|n IH]; intros bd ro i c H; cbn [ms_ro_init fst]; [apply H|].
  apply IH. intros c'. rewrite zget_zset. destruct (c' =? i); [reflexivity| apply H].
Qed.
Lemma bd5_zero : forall c, zget bp_bd5 c = 0.
Proof. intros c. unfold bp_bd5. apply ro_init_bd_zero. intros; apply zget_znew. Qed.
Lemma bd5_zbok : zbok bp_bd5.
Proof. intros c. rewrite bd5_zero. lia. Qed.

(* [comment removed for export] *)
Lemma bs_radix_facts : forall e QO, bs_facts e -> bp_qoff e = QO ->
  let n := e_nblock e in let a1 := e_arr1 e in let a2 := e_arr2 e in let ft := bp_ft0 e in let qo := QO in
  let j0 := Z.shiftl (rd8 a2 0) 8 in
  let r1 := ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 in let a2r := fst (fst r1) in let ft1 := snd (fst r1) in
  let a2o := ms_overshoot 34 a2r qo n 0 in let ft3 := ms_accum 65536 ft1 1 in let s0 := Z.shiftl (rd8 a2o 0) 8 in
  (forall v, 0 <= v <= 65536 -> 0 <= zget ft3 v <= n) /\ r2ok n (Z.to_nat n) a1 a2o ft3 (n - 1) s0.
Proof.
  (intros e QO; cps_intros (FAacc & FAr2 & FAmono); intros EQOF). subst QO. cbv zeta. split.
  - intros v Hv. pose proof (FAacc v Hv) as C. unfold bp_ft3, bp_ft1, bp_r1, bp_j0, bp_n, bp_a2 in C. exact C.
  - pose proof FAr2 as C. unfold bsA_radix2, bp_s0, bp_a2o, bp_a2r, bp_ft3, bp_ft1, bp_r1, bp_j0, bp_n, bp_a1, bp_a2 in C. exact C.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Names.
  Variable e : est. Variable QO : Z.
  Variables (a2b ftb : zarr) (jb : Z) (a1c ftc : zarr) (sc : Z).
  Hypothesis EQOF : bp_qoff e = QO.
  Let n := e_nblock e.
  Let j0 := Z.shiftl (rd8 (e_arr2 e) 0) 8.
  Hypothesis Er : ms_radix1 (Z.to_nat n) (e_arr2 e) (bp_ft0 e) QO (n - 1) j0 = (a2b, ftb, jb).
  Let a2o' := ms_overshoot 34 a2b QO n 0.
  Hypothesis Eqn : ms_radix2 (Z.to_nat n) (e_arr1 e) a2o' (ms_accum 65536 ftb 1) (n - 1) (Z.shiftl (rd8 a2o' 0) 8) = (a1c, ftc, sc).
  Let ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ftc 364.

  Lemma nm_a2r : bp_a2r e = a2b.
  Proof. unfold bp_a2r, bp_r1, bp_j0, bp_n, bp_a2. rewrite EQOF. subst n j0. rewrite Er. reflexivity. Qed.
  Lemma nm_a2o : bp_a2o e = a2o'.
  Proof. unfold bp_a2o. rewrite nm_a2r, EQOF. reflexivity. Qed.
  Lemma nm_ft1 : bp_ft1 e = ftb.
  Proof. unfold bp_ft1, bp_r1, bp_j0, bp_n, bp_a2. rewrite EQOF. subst n j0. rewrite Er. reflexivity. Qed.
  Lemma nm_r4 : bp_r4 e = (a1c, ftc, sc).
  Proof. unfold bp_r4, bp_s0, bp_ft3, bp_n, bp_a1. rewrite nm_a2o, nm_ft1. exact Eqn. Qed.
  Lemma nm_a1r : bp_a1r e = a1c. Proof. unfold bp_a1r. rewrite nm_r4. reflexivity. Qed.
  Lemma nm_ft4 : bp_ft4 e = ftc. Proof. unfold bp_ft4. rewrite nm_r4. reflexivity. Qed.
  Lemma nm_ro6 : bp_ro6 e = ro6. Proof. unfold bp_ro6, bp_ro5. rewrite nm_ft4. reflexivity. Qed.
  Lemma nm_budget : bp_budget0 e = n * budget_q. Proof. reflexivity. Qed.
  Lemma nm_pr : bsB_pr e -> pr n a1c 0 (n - 1).
  Proof. intros P. unfold bsB_pr, bp_n in P. rewrite nm_a1r in P. exact P. Qed.

  (* [comment removed for export] *)
  Lemma nm_mono : bs_facts e -> forall b, 0 <= b < 256 -> 0 <= zget ftc (b * 256) <= zget ftc ((b + 1) * 256) /\ zget ftc ((b + 1) * 256) <= n.
  Proof. (cps_intros (_ & _ & M); intros b Hb). pose proof (M b Hb) as C. rewrite nm_ft4 in C. exact C. Qed.

  (* [comment removed for export] *)
  Lemma nm_big : bsB_big e -> forall cs ce nl nh nd k, 0 + Z.of_nat k <= 255 ->
    let s' := ms_bigs k ro6 QO n 0 (MSS a1c a2o' ftc bp_bd5 cs ce (n * budget_q) 0 (MQL znew znew znew nl nh nd) false) in
    s_exit s' = false -> bigF QO n ro6 (0 + Z.of_nat k) s'.
  Proof.
    intros B cs ce nl nh nd k Hk. pose proof (B cs ce nl nh nd k ltac:(lia)) as C. unfold bp_S0x in C.
    rewrite nm_ro6, nm_a1r, nm_a2o, nm_ft4, EQOF, nm_budget in C. exact C.
  Qed.

  (* [comment removed for export] *)
  Lemma nm_mainSort : forall cs0 ce0 sl sh sd,
    mainSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew cs0 ce0 sl sh sd QO n (n * budget_q) =
    let st := ms_bigs 256 ro6 QO n 0 (MSS a1c a2o' ftc bp_bd5 cs0 ce0 (n * budget_q) 0 (MQL sl sh sd sl sh sd) false) in
    MSR (s_a1 st) (s_a2 st) (s_ft st) (s_budget st) ro6 (s_bd st) (s_cs st) (s_ce st) (s_mql st) (s_nqs st).
  Proof.
    intros. unfold mainSort. change (ms_ftab_zero 65537 (e_ftab e) 65536) with (bp_ft0 e). cbv zeta.
    subst n j0. rewrite Er. subst a2o'. rewrite Eqn.
    change (ms_ro_init 256 znew znew 0) with (bp_bd5, snd (ms_ro_init 256 znew znew 0)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Variables (CSJ CEJ a1' a2' ft' bd' cs' ce' : zarr) (b' nqs' : Z) (L' : mqloc) (ex : bool).
  Hypothesis OK1c : zbok a1c. Hypothesis OKo : zbok a2o'. Hypothesis RK6 : rook ro6.
  Hypothesis EB : ms_bigs 256 ro6 QO n 0 (MSS a1c a2o' ftc bp_bd5 CSJ CEJ (n * budget_q) 0 (MQL znew znew znew znew znew znew) false)
                  = MSS a1' a2' ft' bd' cs' ce' b' nqs' L' ex.

  Lemma nm_bigs_znew : exists cs'' ce'',
    ms_bigs 256 ro6 QO n 0 (MSS a1c a2o' ftc bp_bd5 znew znew (n * budget_q) 0 (MQL znew znew znew znew znew znew) false)
    = MSS a1' a2' ft' bd' cs'' ce'' b' nqs' L' ex.
  Proof.
    cps_destruct (ms_bigs_csce 256 ro6 QO n 0 (MSS a1c a2o' ftc bp_bd5 CSJ CEJ (n * budget_q) 0 (MQL znew znew znew znew znew znew) false) znew znew
                OK1c OKo RK6 ltac:(lia) ltac:(cbn; lia)) as (cs'' & ce'' & E).
    exists cs'', ce''. unfold setcs in E. cbn [s_a1 s_a2 s_ft s_bd s_budget s_nqs s_mql s_exit] in E. rewrite EB in E.
    cbn [s_a1 s_a2 s_ft s_bd s_budget s_nqs s_mql s_exit] in E. exact E.
  Qed.

  Lemma nm_ms : s_a1 (bp_ms e) = a1' /\ s_a2 (bp_ms e) = a2' /\ s_ft (bp_ms e) = ft' /\ s_budget (bp_ms e) = b' /\ s_exit (bp_ms e) = ex.
  Proof.
    unfold bp_ms, bp_S0, bp_n. rewrite nm_ro6, nm_a1r, nm_a2o, nm_ft4, EQOF, nm_budget. fold n.
    cps_destruct nm_bigs_znew as (cs'' & ce'' & E). rewrite E. cbn [s_a1 s_a2 s_ft s_budget s_exit]. repeat split; reflexivity.
  Qed.

  Lemma nm_blockSort_high : 10000 <= n ->
    fst (fst (fst (blockSort e znew))) =
    (if b' <? 0 then let r := fallbackSort a1' a2' ft' znew znew znew znew n in est_sorted e (fr_fm r) (fr_ec r) (fr_bh r)
     else est_sorted e a1' a2' ft').
  Proof.
    intros NB. unfold blockSort. fold n. replace (n <? 10000) with false by (symmetry; apply Z.ltb_ge; exact NB). cbv beta iota zeta.
    change (if Z.land (n + BZ_N_OVERSHOOT) 1 =? 0 then n + BZ_N_OVERSHOOT else n + BZ_N_OVERSHOOT + 1) with (bp_qoff e). rewrite EQOF.
    change (n * (((if WORKFACTOR <? 1 then 1 else if 100 <? WORKFACTOR then 100 else WORKFACTOR) - 1) / 3)) with (n * budget_q).
    rewrite (nm_mainSort znew znew znew znew znew). cbv zeta.
    cps_destruct nm_bigs_znew as (cs'' & ce'' & E). rewrite E. cbn [s_a1 s_a2 s_ft s_budget s_bd s_cs s_ce s_mql s_nqs mr_budget mr_ptr mr_block mr_ftab].
    destruct (b' <? 0); cbn [fst snd]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma nm_exit_false : bsD_high e -> 10000 <= n -> ex = false ->
    (exists i, 0 <= i < n /\ rd32 a1' i = 0) /\ (0 <= b' -> fst (fst (fst (blockSort e znew))) = est_sorted e a1' a2' ft').
  Proof.
    intros D NB EX. destruct (D NB) as [_ D2]. cps_destruct nm_ms as (E1 & E2 & E3 & E4 & E5).
    rewrite E1, E5 in D2. split; [exact (D2 EX)|].
    intros Hb. rewrite (nm_blockSort_high NB). replace (b' <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.
  Lemma nm_exit_true : bsD_high e -> 10000 <= n -> ex = true -> b' < 0 ->
    (forall i, 0 <= zget ft' i < 4294967296) /\ fs_site a1' a2' ft' n /\
    let r := fallbackSort a1' a2' ft' znew znew znew znew n in fst (fst (fst (blockSort e znew))) = est_sorted e (fr_fm r) (fr_ec r) (fr_bh r).
  Proof.
    intros D NB EX Hb. destruct (D NB) as [D1 _]. cps_destruct nm_ms as (E1 & E2 & E3 & E4 & E5).
    rewrite E1, E2, E3, E5 in D1. destruct (D1 EX) as [W FS]. split; [exact W|]. split; [exact FS|].
    cbv zeta. rewrite (nm_blockSort_high NB). replace (b' <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.
End Names.

Lemma nm_blockSort_small : forall e, e_nblock e < 10000 ->
  fst (fst (fst (blockSort e znew))) =
  let r := fallbackSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew (e_nblock e) in est_sorted e (fr_fm r) (fr_ec r) (fr_bh r).
Proof.
  intros e NB. unfold blockSort. replace (e_nblock e <? 10000) with true by (symmetry; apply Z.ltb_lt; exact NB). cbv beta iota zeta.
  cbn [fst snd]. reflexivity.
Qed.

End ACeilS1.
