(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg AHandoffLib MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AEntryLib AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_artR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_img RT_kitL RT_init1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_init2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_init2.RT_initK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_init2.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition LSH_LO : Z := 2147459072.   (* [comment removed for export] *)
Definition LSH_HI : Z := 2148236800.   (* [comment removed for export] *)
Lemma LSH_vals : SH AIMG_LO = LSH_LO /\ SH AIMG_HI = LSH_HI.
Proof. split; reflexivity. Qed.

(* [comment removed for export] *)
Definition run_of (f : mfact) : list (Z * Z * Z) :=
  let ok a n := (LSH_LO <=? a) && (a + n <=? LSH_HI) && (0 <=? n) in
  match f with
  | MZero (ZLit a) n => if ok a n then [(a, n, 0)] else []
  | MZeroC (ZLit a) n => if ok a n then [(a, n, 0)] else []
  | MFill (ZLit a) n c => if ok a n then [(a, n, c)] else []
  | MCell (ZLit a) 1 (ZLit v) => if ok a 1 then [(a, 1, v)] else []
  | _ => []
  end.
Definition lowsh_runs (l : list mfact) : list (Z * Z * Z) := flat_map run_of l.

(* [comment removed for export] *)
Fixpoint all_eqb (v : Z) (l : list Z) : bool :=
  match l with [] => true | x :: r => (x =? v) && all_eqb v r end.
Fixpoint seg_chk (runs : list (Z * list Z)) (lo n v : Z) {struct runs} : bool :=
  match runs with
  | [] => (n <=? 0) || (v =? 0)
  | (rlo, bs) :: r =>
      let rhi := rlo + Z.of_nat (length bs) in
      if (lo + n <=? rlo) || (rhi <=? lo) || (n <=? 0) then seg_chk r lo n v
      else seg_chk r lo (rlo - lo) v
           && all_eqb v (firstn (Z.to_nat (Z.min (lo + n) rhi - Z.max lo rlo)) (skipn (Z.to_nat (Z.max lo rlo - rlo)) bs))
           && seg_chk r rhi (lo + n - rhi) v
  end.
Definition run_chk (lo : Z) (n : nat) (v : Z) : bool := seg_chk ALOWSH_RUNS lo (Z.of_nat n) v.
Fixpoint runs_chk (start : Z) (l : list (Z * Z * Z)) : bool :=
  match l with
  | [] => start =? LSH_HI
  | (lo, n, v) :: l' => (lo =? start) && (0 <=? n) && run_chk lo (Z.to_nat n) v && runs_chk (lo + n) l'
  end.
Lemma lowsh_chk : runs_chk LSH_LO (lowsh_runs asan_mem_facts) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_eqb_sound : forall v l, all_eqb v l = true -> forall t, (t < length l)%nat -> nth t l 0 = v.
Proof.
  intros v l. induction l as [|x l IH]; intros H t Ht; cbn in *; [lia|].
  apply andb_prop in H as [H1 H2]. destruct t as [|t]; [apply Z.eqb_eq; exact H1| apply IH; [exact H2| lia]].
Qed.
Lemma nth_firstn_skipn : forall (k j t : nat) (l : list Z), (t < k)%nat -> (j + t < length l)%nat ->
  nth t (firstn k (skipn j l)) 0 = nth (j + t) l 0.
Proof.
  intros k j t l Ht Hl. rewrite nth_firstn. replace (t <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Ht).
  rewrite nth_skipn. reflexivity.
Qed.
Lemma seg_chk_sound : forall runs lo n v, seg_chk runs lo n v = true -> forall g, lo <= g < lo + n -> runs_lookup runs g = v.
Proof.
  induction runs as [|[rlo bs] r IH]; intros lo n v H g Hg; cbn [seg_chk runs_lookup] in H |- *.
  - apply orb_prop in H. destruct H as [H|H]; [apply Z.leb_le in H; lia| apply Z.eqb_eq in H; lia].
  - set (rhi := rlo + Z.of_nat (length bs)) in *.
    destruct ((lo + n <=? rlo) || (rhi <=? lo) || (n <=? 0)) eqn:D.
    + assert (E : (rlo <=? g) && (g <? rhi) = false).
      { apply orb_prop in D. destruct D as [D|D]; [apply orb_prop in D; destruct D as [D|D]|]; try apply Z.leb_le in D;
        [apply andb_false_iff; left; apply Z.leb_gt; subst rhi; lia| apply andb_false_iff; right; apply Z.ltb_ge; subst rhi; lia| exfalso; lia]. }
      rewrite E. apply (IH _ _ _ H). exact Hg.
    + apply orb_false_iff in D as [D D3]. apply orb_false_iff in D as [D1 D2].
      apply Z.leb_gt in D1. apply Z.leb_gt in D2. apply Z.leb_gt in D3.
      apply andb_prop in H as [H HA]. apply andb_prop in H as [HB HM].
      destruct (Z_lt_le_dec g rlo) as [L|GE].
      * replace ((rlo <=? g) && (g <? rhi)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
        apply (IH _ _ _ HB). lia.
      * destruct (Z_lt_le_dec g rhi) as [L2|GE2].
        -- replace ((rlo <=? g) && (g <? rhi)) with true
             by (symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia]).
           pose proof (all_eqb_sound _ _ HM) as AM.
           set (j := Z.to_nat (Z.max lo rlo - rlo)) in AM. set (k := Z.to_nat (Z.min (lo + n) rhi - Z.max lo rlo)) in AM.
           assert (T : (Z.to_nat (g - rlo) = j + (Z.to_nat (g - rlo) - j))%nat) by (subst j; lia).
           specialize (AM (Z.to_nat (g - rlo) - j)%nat).
           rewrite length_firstn, length_skipn in AM.
           assert (Hk : ((Z.to_nat (g - rlo) - j) < k)%nat) by (subst j k rhi; lia).
           assert (Hl : (j + (Z.to_nat (g - rlo) - j) < length bs)%nat) by (subst j rhi; lia).
           rewrite (nth_firstn_skipn k j _ bs Hk Hl) in AM. rewrite <- T in AM. apply AM. lia.
        -- replace ((rlo <=? g) && (g <? rhi)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
           apply (IH _ _ _ HA). lia.
Qed.
Lemma run_chk_sound : forall n lo v, run_chk lo n v = true -> forall i, 0 <= i < Z.of_nat n -> alowsh (lo + i) = v.
Proof.
  intros n lo v H i Hi. unfold run_chk in H. unfold alowsh. apply (seg_chk_sound _ _ _ _ H). lia.
Qed.

Section LSH.
Variables (V : nat -> Z) (m : word -> option byte).

Lemma runs_chk_sound : forall l s, runs_chk s l = true ->
  Forall (fun r => brun m (fst (fst r)) (snd (fst r)) (snd r)) l ->
  forall g, s <= g < LSH_HI -> m (wa g) = Some (zb (alowsh g)).
Proof.
  induction l as [|[[lo n] v] l IH]; intros s H FB g Hg; cbn [runs_chk] in H.
  - apply Z.eqb_eq in H. lia.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.leb_le in H2. subst lo. apply Forall_cons_iff in FB as [B FB]. cbn [fst snd] in B.
    destruct (Z_lt_le_dec g (s + n)).
    + replace g with (s + (g - s)) by lia. rewrite (run_chk_sound _ _ _ H3 (g - s)) by lia. apply B. lia.
    + apply (IH _ H4 FB). lia.
Qed.

Lemma run_of_sound : forall f, mfact_ok asegs V m f -> Forall (fun r => brun m (fst (fst r)) (snd (fst r)) (snd r)) (run_of f).
Proof.
  intros f Hf. destruct f as [a w v|a k|a w v|a k|a k c|lo hi|a k|a k|a k]; cbn [run_of]; try apply Forall_nil.
  - (* [comment removed for export] *) destruct a as [a| | | | |]; try apply Forall_nil. destruct w as [|[|w]]; try apply Forall_nil.
    destruct v as [v| | | | |]; try apply Forall_nil.
    destruct ((LSH_LO <=? a) && (a + 1 <=? LSH_HI) && (0 <=? 1)) eqn:E; [| apply Forall_nil].
    apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. cbn [mfact_ok zv cellw] in Hf.
    apply brun_w1; [exact (proj1 Hf)| unfold LSH_LO, LSH_HI, AIMG_HI in *; lia].
  - (* [comment removed for export] *) destruct a as [a| | | | |]; try apply Forall_nil.
    destruct ((LSH_LO <=? a) && (a + k <=? LSH_HI) && (0 <=? k)) eqn:E; [| apply Forall_nil].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. cbn [mfact_ok zv] in Hf.
    apply brun_zero. apply zeroc_zfill; [exact Hf| exact E3| unfold LSH_LO, AIMG_HI in *; lia].
  - (* [comment removed for export] *) destruct a as [a| | | | |]; try apply Forall_nil.
    destruct ((LSH_LO <=? a) && (a + k <=? LSH_HI) && (0 <=? k)) eqn:E; [| apply Forall_nil].
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. cbn [mfact_ok zv] in Hf. intros i Hi. exact (Hf i Hi).
  - (* [comment removed for export] *) destruct a as [a| | | | |]; try apply Forall_nil.
    destruct ((LSH_LO <=? a) && (a + k <=? LSH_HI) && (0 <=? k)) eqn:E; [| apply Forall_nil].
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. cbn [mfact_ok zv] in Hf. intros i Hi. exact (Hf i Hi).
Qed.

Lemma lowsh_runs_sound : forall l, Forall (mfact_ok asegs V m) l ->
  Forall (fun r => brun m (fst (fst r)) (snd (fst r)) (snd r)) (lowsh_runs l).
Proof.
  induction l as [|f l IH]; intros HF; [apply Forall_nil|]. apply Forall_cons_iff in HF as [Hf HF].
  unfold lowsh_runs. cbn [flat_map]. apply Forall_app. split; [exact (run_of_sound f Hf)| exact (IH HF)].
Qed.
End LSH.

Section INIT2B.
Variables (w : bool) (V : nat -> Z) (usp : Z) (m : word -> option byte).
Hypothesis IP : init_pure (hw w) V usp.
Hypothesis HFW : Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w).
Let st := st_main (hw w) V usp.
Let HF : Forall (mfact_ok asegs V m) asan_mem_facts := proj1 (proj1 (Forall_app _ _ _) HFW).

Lemma L_lowshadow : R_lowshadow m.
Proof.
  pose proof (runs_chk_sound m _ _ lowsh_chk (lowsh_runs_sound V m _ HF)) as G.
  destruct LSH_vals as [E1 E2]. intros g Hg. rewrite E1, E2 in Hg. pose proof (G g Hg) as E. unfold LSH_LO, LSH_HI in Hg.
  split; [split; [wf|]|].
  - unfold bytes_at. cbn [length cells_bytes cbytes app]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0%nat) as -> by lia.
    cbn. rewrite Z.add_0_r. unfold mrd. rewrite E. reflexivity.
  - unfold wr_at. cbn [cells_size Cells.csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) as -> by lia.
    rewrite Z.add_0_r. rewrite wview_empty. rewrite E. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem st_main_rep : RTREP st m.
Proof.
  constructor.
  - eapply L_link; eassumption.
  - eapply L_consts; eassumption.
  - eapply L_alloc; eassumption.
  - eapply L_rinfo; eassumption.
  - eapply L_regions; eassumption.
  - eapply L_avail; eassumption.
  - eapply L_cache; eassumption.
  - eapply L_thread; eassumption.
  - eapply L_live; eassumption.
  - eapply L_quar; eassumption.
  - eapply L_batches; eassumption.
  - eapply L_ptrarr; eassumption.
  - eapply L_depot; eassumption.
  - eapply L_fs; eassumption.
  - eapply L_ia; eassumption.
  - exact L_lowshadow.
Qed.
End INIT2B.

End CeilWrap.
