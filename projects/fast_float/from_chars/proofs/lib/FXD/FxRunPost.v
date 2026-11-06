(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec SeqExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint set_regs (R : tree lin) (sets : list (reg * lin)) : tree lin :=
  match sets with [] => R | (r, l) :: ss => set_regs (rset R (rkey r) l) ss end.
Fixpoint hav_regs (R : tree lin) (havs : list reg) (n : positive) : tree lin :=
  match havs with [] => R | r :: hs => hav_regs (rset R (rkey r) (lvar n)) hs (Pos.succ n) end.
Fixpoint pos_add (n : positive) (k : nat) : positive := match k with O => n | Datatypes.S k' => pos_add (Pos.succ n) k' end.
Definition run_post (S : sst) (pc' : Z) (sets : list (reg * lin)) (havs : list reg) : sst :=
  SST pc' (hav_regs (set_regs (s_regs S) sets) havs (s_next S)) (s_rgs S) (s_facts S) (pos_add (s_next S) (length havs)) (s_resv S).
(* [comment removed for export] *)
Fixpoint hav_val (E : valu) (regs' : bvmap 5 word) (havs : list reg) (n : positive) : valu :=
  match havs with [] => E | r :: hs => hav_val (upd E n (getr regs' r)) regs' hs (Pos.succ n) end.
(* [comment removed for export] *)
Fixpoint upd_sets (regs : bvmap 5 word) (sets : list (reg * lin)) (regs' : bvmap 5 word) : bvmap 5 word :=
  match sets with [] => regs | (r, _) :: ss => upd_sets (regupd regs r (getr regs' r)) ss regs' end.
Fixpoint upd_havs (regs : bvmap 5 word) (havs : list reg) (regs' : bvmap 5 word) : bvmap 5 word :=
  match havs with [] => regs | r :: hs => upd_havs (regupd regs r (getr regs' r)) hs regs' end.

Lemma pos_add_le : forall k n, (n <= pos_add n k)%positive.
Proof. induction k as [|k IH]; intros n; cbn [pos_add]; [lia|]. specialize (IH (Pos.succ n)). lia. Qed.
Lemma pos_add_succ : forall k n, pos_add (Pos.succ n) k = Pos.succ (pos_add n k).
Proof. induction k as [|k IH]; intros n; cbn [pos_add]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma pos_add_lt : forall k i n, (i < k)%nat -> (pos_add n i < pos_add n k)%positive.
Proof.
  induction k as [|k IH]; intros i n Hi; [lia|]. destruct i as [|i]; cbn [pos_add].
  - pose proof (pos_add_le k (Pos.succ n)). lia.
  - apply IH. lia.
Qed.

Lemma hav_val_agree : forall havs E regs' n, agree n E (hav_val E regs' havs n).
Proof.
  induction havs as [|r hs IH]; intros E regs' n; cbn [hav_val]; [apply agree_refl|].
  apply (agree_trans n E (upd E n (getr regs' r))); [apply agree_upd|].
  apply (agree_mono n (Pos.succ n)); [lia|]. apply IH.
Qed.
Lemma hav_val_at : forall havs E regs' n i, (i < length havs)%nat ->
  hav_val E regs' havs n (pos_add n i) = getr regs' (nth i havs 0%bv).
Proof.
  induction havs as [|r hs IH]; intros E regs' n i Hi; cbn [length] in Hi; [lia|]. cbn [hav_val].
  destruct i as [|i].
  - cbn [pos_add nth].
    assert (Hag : agree (Pos.succ n) (upd E n (getr regs' r)) (hav_val (upd E n (getr regs' r)) regs' hs (Pos.succ n))) by apply hav_val_agree.
    rewrite <- (Hag n ltac:(lia)). unfold upd. rewrite Pos.eqb_refl. reflexivity.
  - cbn [pos_add nth]. exact (IH _ regs' (Pos.succ n) i ltac:(lia)).
Qed.

Lemma regs_ok_upd' : forall E R regs (rd : reg) l v, rd <> 0%bv -> regs_ok E R regs -> lden E l = v ->
  regs_ok E (rset R (rkey rd) l) (regupd regs rd v).
Proof.
  intros E R regs rd l v Hne HR Hv. pose proof (regs_ok_upd E R regs rd l v HR Hv) as X.
  rewrite (PropExec.bv_eqb_neq rd 0%bv Hne) in X. exact X.
Qed.
Lemma regs_ok_set' : forall sets E R regs regs',
  regs_ok E R regs -> Forall (fun p => fst p <> 0%bv /\ getr regs' (fst p) = lden E (snd p)) sets ->
  regs_ok E (set_regs R sets) (upd_sets regs sets regs').
Proof.
  induction sets as [|[r l] ss IH]; intros E R regs regs' HR Hs; cbn [set_regs upd_sets]; [exact HR|].
  inversion Hs as [|? ? [Hr0 Hv] Hs']; subst. cbn [fst snd] in *.
  apply IH; [|exact Hs']. apply regs_ok_upd'; [exact Hr0 | exact HR | symmetry; exact Hv].
Qed.
Lemma regs_ok_hav' : forall havs E R regs regs' n,
  regs_ok E R regs -> Forall (fun r => r <> 0%bv) havs ->
  (forall i, (i < length havs)%nat -> E (pos_add n i) = getr regs' (nth i havs 0%bv)) ->
  regs_ok E (hav_regs R havs n) (upd_havs regs havs regs').
Proof.
  induction havs as [|r hs IH]; intros E R regs regs' n HR Hnz Hv; cbn [hav_regs upd_havs]; [exact HR|].
  inversion Hnz as [|? ? Hr0 Hnz']; subst.
  apply (IH E _ _ regs' (Pos.succ n)); [| exact Hnz' |].
  - apply regs_ok_upd'; [exact Hr0 | exact HR |]. rewrite lden_lvar. exact (Hv O ltac:(cbn; lia)).
  - intros i Hi. exact (Hv (Datatypes.S i) ltac:(cbn; lia)).
Qed.
Lemma upd_sets_get : forall sets regs regs' r,
  getr (upd_sets regs sets regs') r = if existsb (fun p => bv_eqb (fst p) r) sets then getr regs' r else getr regs r.
Proof.
  induction sets as [|[r0 l] ss IH]; intros regs regs' r; cbn [upd_sets existsb]; [reflexivity|].
  rewrite IH. cbn [fst]. destruct (bv_eqb r0 r) eqn:E0; cbn [orb].
  - apply bv_eqb_eq in E0. subst r0. destruct (existsb _ ss); [reflexivity|].
    destruct (decide (r = 0%bv)) as [->|Hne]; [rewrite !getr_zero; reflexivity | rewrite getr_same by exact Hne; reflexivity].
  - destruct (existsb _ ss); [reflexivity|]. rewrite getr_other; [reflexivity|].
    intros Hc. subst r. rewrite bv_eqb_refl in E0. discriminate.
Qed.
Lemma upd_havs_get : forall havs regs regs' r,
  getr (upd_havs regs havs regs') r = if existsb (fun h => bv_eqb h r) havs then getr regs' r else getr regs r.
Proof.
  induction havs as [|r0 hs IH]; intros regs regs' r; cbn [upd_havs existsb]; [reflexivity|].
  rewrite IH. destruct (bv_eqb r0 r) eqn:E0; cbn [orb].
  - apply bv_eqb_eq in E0. subst r0. destruct (existsb _ hs); [reflexivity|].
    destruct (decide (r = 0%bv)) as [->|Hne]; [rewrite !getr_zero; reflexivity | rewrite getr_same by exact Hne; reflexivity].
  - destruct (existsb _ hs); [reflexivity|]. rewrite getr_other; [reflexivity|].
    intros Hc. subst r. rewrite bv_eqb_refl in E0. discriminate.
Qed.
Lemma regs_ok_ext : forall E R regs regs2, regs_ok E R regs -> (forall r, getr regs r = getr regs2 r) -> regs_ok E R regs2.
Proof. intros E R regs regs2 HR Hx r. rewrite <- Hx. apply HR. Qed.

Section Run.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
#[using="Hwx"] Theorem den_run_post : forall E S M ms model T (regs' : bvmap 5 word) (pc' : Z) (sets : list (reg * lin)) (havs : list reg),
  DEN segs LIMIT model0 mem0 E S M ms model -> s_resv S = RNone ->
  isteps segs (restrict (Hof E M model) ms)
    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') (mrestrict (Hof E M model) (ms_mem ms)) (ms_rom ms)) ->
  Forall (fun p => fst p <> 0%bv /\ lwf (s_next S) (snd p) = true /\ getr regs' (fst p) = lden E (snd p)) sets ->
  Forall (fun r => r <> 0%bv) havs ->
  (forall r, existsb (fun p => bv_eqb (fst p) r) sets = false -> existsb (fun h => bv_eqb h r) havs = false ->
     getr regs' r = getr (ms_regs ms) r) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (run_post S pc' sets havs) M ms' model' ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T regs' pc' sets havs Hd Hrv Hst Hsets Hnz Ho Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (n := s_next S) in *.
  set (E1 := hav_val E regs' havs n).
  assert (Ha1 : agree n E E1) by apply hav_val_agree.
  set (S1 := bump S (pos_add n (length havs))).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump; cbn [s_next]; apply pos_add_le).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model)
    by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | apply pos_add_le]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  assert (Hpost : sden segs E1 (run_post S pc' sets havs)
                    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') (mrestrict H (ms_mem ms)) (ms_rom ms))).
  { pose proof (sden_regs segs E1 S1 (restrict H ms) (s_regs (run_post S pc' sets havs)) regs' pc'
                  ltac:(rewrite <- HH1; exact (dn_sden _ _ _ _ _ _ _ _ _ HdS1))) as X.
    cbn [restrict ms_fregs ms_fcsr ms_resv ms_mem ms_rom] in X. rewrite Hrsv in X.
    unfold run_post at 1. unfold mkst. cbn [fp_regs fp_csr]. apply X.
    intros E' Ha' HR'. cbn [S1 bump s_regs restrict ms_regs] in HR'.
    assert (HaE : agree n E E') by exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' Hnx Ha')).
    unfold run_post. cbn [s_regs].
    apply (regs_ok_ext E' _ (upd_havs (upd_sets (ms_regs ms) sets regs') havs regs')).
    - apply regs_ok_hav'; [| exact Hnz |].
      + apply regs_ok_set'; [exact HR'|]. rewrite Forall_forall in Hsets |- *. intros p Hp.
        destruct (Hsets p Hp) as (Hp0 & Hpw & Hpv). split; [exact Hp0|]. rewrite Hpv. symmetry. exact (lden_agree_wf n E E' _ Hpw HaE).
      + intros i Hi. rewrite <- (hav_val_at havs E regs' n i Hi). symmetry. apply Ha'. unfold S1, bump. cbn [s_next].
        apply pos_add_lt. exact Hi.
    - intros r. rewrite upd_havs_get, upd_sets_get.
      destruct (existsb (fun h => bv_eqb h r) havs) eqn:Eh; [reflexivity|].
      destruct (existsb (fun p => bv_eqb (fst p) r) sets) eqn:Es; [reflexivity|].
      symmetry. exact (Ho r Es Eh). }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 (s_pc S)) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. subst pcv. reflexivity. }
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (run_post S pc' sets havs)
           (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') (mrestrict H (ms_mem ms)) (ms_rom ms)) E1 HdS1).
  - rewrite HH1. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - unfold run_post, S1, bump. cbn [s_next]. apply Pos.le_refl.
  - intros y _. rewrite HH1. reflexivity.
  - reflexivity.
  - intros E2 ms2 model2 HD2 Ha2. apply (Hk E2 ms2 model2); [|exact HD2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
End Run.

(* [comment removed for export] *)
Definition run_post_fw (S : sst) (pc' : Z) (sets : list (reg * lin)) (havs : list reg) (j0 : nat) (lo hi : Z) : sst :=
  match nth_error (s_rgs S) j0 with
  | Some R0 => SST pc' (hav_regs (set_regs (s_regs S) sets) havs (s_next S))
                   (upd_nth (s_rgs S) j0 (RG (rg_base R0) (rg_size R0) (rg_kind R0) (havoc_range (rg_cont R0) lo hi)))
                   (s_facts S) (pos_add (s_next S) (length havs)) (s_resv S)
  | None => run_post S pc' sets havs
  end.

Section RunFW.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_run_post_fw : forall E S M ms model T (regs' : bvmap 5 word) (pc' : Z) (sets : list (reg * lin)) (havs : list reg)
    (j0 : nat) (R0 : region) (lo hi : Z) (mem' : word -> option byte),
  DEN segs LIMIT model0 mem0 E S M ms model -> s_resv S = RNone ->
  nth_error (s_rgs S) j0 = Some R0 -> rg_kind R0 = RW -> 0 <= lo -> lo <= hi -> hi <= rsz E R0 ->
  isteps segs (restrict (Hof E M model) ms)
    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)) ->
  (forall w : word, ~ (uE E (rg_base R0) + lo <= bv_unsigned w < uE E (rg_base R0) + hi) -> mem' w = mrestrict (Hof E M model) (ms_mem ms) w) ->
  (forall i, lo <= i < hi -> rd1 segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None /\ wview segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None) ->
  Forall (fun p => fst p <> 0%bv /\ lwf (s_next S) (snd p) = true /\ getr regs' (fst p) = lden E (snd p)) sets ->
  Forall (fun r => r <> 0%bv) havs ->
  (forall r, existsb (fun p => bv_eqb (fst p) r) sets = false -> existsb (fun h => bv_eqb h r) havs = false ->
     getr regs' r = getr (ms_regs ms) r) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (run_post_fw S pc' sets havs j0 lo hi) M ms' model' ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T regs' pc' sets havs j0 R0 lo hi mem' Hd Hrv Hj0 Hk0 Hlo Hlh Hhi Hst Hfr Hwr Hsets Hnz Ho Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (n := s_next S) in *.
  set (E1 := hav_val E regs' havs n).
  assert (Ha1 : agree n E E1) by apply hav_val_agree.
  set (S1 := bump S (pos_add n (length havs))).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump; cbn [s_next]; apply pos_add_le).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model)
    by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | apply pos_add_le]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (R0' := RG (rg_base R0) (rg_size R0) (rg_kind R0) (havoc_range (rg_cont R0) lo hi)).
  assert (Hpw : run_post_fw S pc' sets havs j0 lo hi = SST pc' (hav_regs (set_regs (s_regs S) sets) havs n) (upd_nth (s_rgs S) j0 R0')
                   (s_facts S) (pos_add n (length havs)) (s_resv S)) by (unfold run_post_fw; rewrite Hj0; reflexivity).
  set (msr' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)).
  assert (Hpost : sden segs E1 (run_post_fw S pc' sets havs j0 lo hi) msr').
  { rewrite Hpw. intros E' Ha'.
    assert (HaE : agree n E E') by exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' (pos_add_le (length havs) n) Ha')).
    destruct (Hsd E' HaE) as (Hpc' & Hsvc' & Hrsv' & HR' & HG' & HD' & HF' & Hfrm').
    cbn [restrict ms_regs ms_mem ms_fcsr ms_resv] in HR', HG', Hfrm', Hrsv'.
    assert (HbE : lden E' (rg_base R0) = lden E (rg_base R0)).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 _].
      exact (lden_agree_wf n E E' _ B1 HaE). }
    assert (HsE : rsz E' R0 = rsz E R0).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [_ B2].
      unfold rsz. rewrite (lden_agree_wf n E E' _ B2 HaE). reflexivity. }
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv msr' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|]. split.
    - apply (regs_ok_ext E' _ (upd_havs (upd_sets (ms_regs ms) sets regs') havs regs')).
      + apply regs_ok_hav'; [| exact Hnz |].
        * apply regs_ok_set'; [exact HR'|]. rewrite Forall_forall in Hsets |- *. intros p Hp.
          destruct (Hsets p Hp) as (Hp0 & Hpw' & Hpv). split; [exact Hp0|]. rewrite Hpv. symmetry. exact (lden_agree_wf n E E' _ Hpw' HaE).
        * intros i Hi. rewrite <- (hav_val_at havs E regs' n i Hi). symmetry. apply Ha'. cbn [s_next]. apply pos_add_lt. exact Hi.
      + intros r. rewrite upd_havs_get, upd_sets_get.
        destruct (existsb (fun h => bv_eqb h r) havs) eqn:Eh; [reflexivity|].
        destruct (existsb (fun p => bv_eqb (fst p) r) sets) eqn:Es; [reflexivity|].
        symmetry. exact (Ho r Es Eh).
    - split; [|split; [|split; [exact HF' | exact Hfrm']]].
      + (* [comment removed for export] *)
        apply Forall_nth'. intros j R HRj. rewrite Forall_nth' in HG'.
        destruct (Nat.eq_dec j j0) as [->|Hne].
        * rewrite (nth_upd_same (s_rgs S) j0 R0' R0 Hj0) in HRj. injection HRj as <-.
          destruct (HG' j0 R0 Hj0) as (Hsz & Hflat & Hall & Hcont).
          assert (Hrsz : rsz E' R0' = rsz E R0) by (unfold R0', rsz; cbn [rg_size]; unfold rsz in HsE; exact HsE).
          assert (Hbase : lden E' (rg_base R0') = lden E (rg_base R0)) by (unfold R0'; cbn [rg_base]; exact HbE).
          assert (HkR' : rg_kind R0' = RW) by (unfold R0'; cbn [rg_kind]; exact Hk0).
          assert (Hcont' : rg_cont R0' = havoc_range (rg_cont R0) lo hi) by reflexivity.
          unfold rg_ok. rewrite Hrsz, Hbase, HkR', Hcont'. rewrite Hk0 in Hall. rewrite HbE, HsE in *. fold (uE E (rg_base R0)) in *.
          split; [exact Hsz|]. split; [exact Hflat|]. split.
          -- intros i Hi. specialize (Hall i Hi).
             destruct (Z_lt_le_dec i lo) as [Hl|Hl]; [|destruct (Z_lt_le_dec i hi) as [Hh2|Hh2]].
             ++ unfold rd1, wview in *. rewrite Hfr; [exact Hall|]. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia.
             ++ exact (Hwr i ltac:(lia)).
             ++ unfold rd1, wview in *. rewrite Hfr; [exact Hall|]. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia.
          -- intros p v Hp. unfold havoc_range in Hp. rewrite tget_tfilter in Hp.
             destruct (tget p (rg_cont R0)) as [x|] eqn:Hx; [|discriminate].
             destruct (negb (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)) eqn:Hn; [|discriminate]. injection Hp as <-.
             destruct (Hcont p x Hx) as [Hp1 Hp2]. rewrite ?HbE, ?HsE in Hp1, Hp2. fold (uE E (rg_base R0)) in Hp2. split; [exact Hp1|].
             apply negb_true_iff in Hn. apply andb_false_iff in Hn.
             unfold rd1 in *. rewrite Hfr; [exact Hp2|]. pose proof (Pos2Z.is_pos p). pose proof (uE_range E (rg_base R0)).
             rewrite u_small64 by (unfold two64 in *; lia).
             destruct Hn as [Hn|Hn]; [apply Z.leb_gt in Hn | apply Z.ltb_ge in Hn]; lia.
        * rewrite (nth_upd_other (s_rgs S) j0 j R0' ltac:(lia)) in HRj.
          apply (rg_ok_frame segs E' (mrestrict H (ms_mem ms)) mem' R (HG' j R HRj)).
          intros x Hx. apply Hfr.
          pose proof (rgs_disj_nth E' (s_rgs S) j j0 R R0 HD' Hne HRj Hj0) as Hdis. unfold rg_disj in Hdis.
          rewrite HbE, HsE in Hdis. fold (uE E (rg_base R0)) in Hdis. unfold uE in *. lia.
      + apply (rgs_disj_upd E' (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl HD'). }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 (s_pc S)) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. subst pcv. reflexivity. }
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (run_post_fw S pc' sets havs j0 lo hi) msr' E1 HdS1).
  - rewrite HH1. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - rewrite Hpw. unfold S1, bump. cbn [s_next]. apply Pos.le_refl.
  - intros y Hy. rewrite HH1. unfold msr', mkst. cbn [ms_mem]. apply Hfr.
    unfold outside in Hy. rewrite Forall_forall in Hy. specialize (Hy R0 (nth_error_In _ _ Hj0)).
    cbn [S1 bump s_rgs] in Hy.
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 B2].
    assert (HbE1 : lden E1 (rg_base R0) = lden E (rg_base R0)) by exact (lden_agree_wf n E E1 _ B1 Ha1).
    assert (HsE1 : rsz E1 R0 = rsz E R0) by (unfold rsz; rewrite (lden_agree_wf n E E1 _ B2 Ha1); reflexivity).
    rewrite HbE1, HsE1 in Hy. unfold uE. lia.
  - rewrite Hpw. cbn [s_rgs S1 bump]. exact (shape_upd (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl).
  - intros E2 ms2 model2 HD2 Ha2. apply (Hk E2 ms2 model2); [|exact HD2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
End RunFW.
