(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Module MEX_big.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma am_init_eq st :
  s_regions (am_init st) = s_regions st /\ s_metas (am_init st) = s_metas st /\ s_slots (am_init st) = s_slots st
  /\ s_groups (am_init st) = s_groups st /\ s_next_rid (am_init st) = s_next_rid st /\ s_reserved (am_init st) = s_reserved st
  /\ c_free_meta_head (s_ctx (am_init st)) = c_free_meta_head (s_ctx st)
  /\ c_avail_meta (s_ctx (am_init st)) = c_avail_meta (s_ctx st)
  /\ c_avail_meta_count (s_ctx (am_init st)) = c_avail_meta_count (s_ctx st)
  /\ c_active (s_ctx (am_init st)) = c_active (s_ctx st)
  /\ c_usage (s_ctx (am_init st)) = c_usage (s_ctx st)
  /\ c_bounces (s_ctx (am_init st)) = c_bounces (s_ctx st)
  /\ c_unmap_seq (s_ctx (am_init st)) = c_unmap_seq (s_ctx st).
Proof. unfold am_init. destruct (c_init_done (ctx st) =? 0); repeat split; reflexivity. Qed.

Lemma step_seq_eq st :
  s_regions (step_seq st) = s_regions st /\ s_metas (step_seq st) = s_metas st /\ s_slots (step_seq st) = s_slots st
  /\ s_groups (step_seq st) = s_groups st /\ s_next_rid (step_seq st) = s_next_rid st /\ s_reserved (step_seq st) = s_reserved st
  /\ c_free_meta_head (s_ctx (step_seq st)) = c_free_meta_head (s_ctx st)
  /\ c_avail_meta (s_ctx (step_seq st)) = c_avail_meta (s_ctx st)
  /\ c_avail_meta_count (s_ctx (step_seq st)) = c_avail_meta_count (s_ctx st)
  /\ c_active (s_ctx (step_seq st)) = c_active (s_ctx st)
  /\ c_usage (s_ctx (step_seq st)) = c_usage (s_ctx st)
  /\ c_bounces (s_ctx (step_seq st)) = c_bounces (s_ctx st).
Proof. unfold step_seq, ctx. destruct (c_seq (s_ctx st) =? 255); repeat split; reflexivity. Qed.

Lemma unmap_seq_step_seq st : (forall i, unmap_seq st i = 0) -> forall i, unmap_seq (step_seq st) i = 0.
Proof.
  intros H i. unfold step_seq, unmap_seq, ctx in *. destruct (c_seq (s_ctx st) =? 255); cbn; [| apply H].
  rewrite lookup_empty. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma am_post_free st f :
  c_free_meta_head (ctx st) = Some f -> m_next (get_meta_rec st f) = Some f ->
  am_post st = (upd_meta f (fun r => m_set_prev None (m_set_next None r)) (set_head LFree None (am_init st)), f).
Proof.
  intros H1 H2. pose proof (am_init_eq st) as (_ & M & _ & _ & _ & _ & F & _).
  unfold am_post. unfold ctx in *. rewrite F, H1. rewrite dequeue_self; [reflexivity|].
  rewrite (get_meta_rec_ext st (am_init st) f M). exact H2.
Qed.

Lemma am_post_avail st p :
  c_free_meta_head (ctx st) = None -> c_avail_meta (ctx st) = Some p ->
  am_post st = (upd_meta p (fun r => m_set_prev None (m_set_next None r))
                  (upd_ctx (fun c => set_avail_meta (Some (aadd p META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) (am_init st)), p).
Proof.
  intros H1 H2. pose proof (am_init_eq st) as (_ & _ & _ & _ & _ & _ & F & A & _).
  unfold am_post. unfold ctx in *. rewrite F, H1, A, H2. reflexivity.
Qed.

(* [comment removed for export] *)
Section BIGTAIL.
Variables (st3 : mstate) (g : aptr) (rid : N) (needed : Z).
Let st' := big_tail lay_none st3 g rid needed.
Let REC := mkMeta (m_prev (get_meta_rec st3 g)) (m_next (get_meta_rec st3 g)) (Some (rid, 0)) 0 0 0 1 63 (Z.land ((needed + 4095) / 4096) (2 ^ 52 - 1)).

Lemma big_tail_meta x : get_meta_rec st' x = if aptr_eqb x g then REC else get_meta_rec st3 x.
Proof.
  unfold st', big_tail. rewrite get_meta_rec_upd_ctx.
  rewrite (get_meta_rec_ext (put_group (rid, 0) (Some g) _ _) _ x) by (rewrite s_metas_add_slots; reflexivity).
  rewrite (get_meta_rec_ext (upd_meta g _ st3) _ x) by (rewrite s_metas_put_group; reflexivity).
  rewrite get_meta_rec_upd. destruct (aptr_eqb x g); [| reflexivity].
  unfold REC. destruct (get_meta_rec st3 g); cbn. reflexivity.
Qed.

Lemma big_tail_fields :
  s_regions st' = s_regions st3 /\ s_next_rid st' = s_next_rid st3 /\ s_reserved st' = s_reserved st3
  /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st3)
  /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st3)
  /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st3)
  /\ c_active (s_ctx st') = c_active (s_ctx st3)
  /\ c_usage (s_ctx st') = c_usage (s_ctx st3)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st3)
  /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st3)
  /\ s_groups st' = <[(rid, 0) := mkGhdr (Some g) (Z.land (group_active_idx (upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3) (rid, 0)) 31)]> (s_groups st3).
Proof. unfold st', big_tail. cbn [lh_hdr lay_none]. repeat split; reflexivity.  (* [comment removed for export] *) Qed.

Lemma big_tail_slots s : 0 < needed -> needed < 2 ^ 60 ->
  s_slots st' !! s = if aptr_eqb s (rid, 16) then Some (g, 0) else s_slots st3 !! s.
Proof.
  intros Hn Hn2. unfold st', big_tail. rewrite s_slots_upd_ctx.
  assert (MLp : 0 < (needed + 4095) / 4096 < 2 ^ 52).
  { split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (HL : Z.land ((needed + 4095) / 4096) (2 ^ 52 - 1) = (needed + 4095) / 4096) by (apply land_small_ones; lia).
  match goal with |- context [add_slots g (rid, 0) ?str 1 ?s5] => set (stride := str); set (st5 := s5) end.
  assert (HS : stride = (needed + 4095) / 4096 * 4096 - UNIT).
  { unfold stride. rewrite (get_meta_rec_ext (upd_meta g _ st3)) by (rewrite s_metas_put_group; reflexivity).
    rewrite get_meta_rec_upd_same. unfold get_stride. cbn [m_last_idx m_maplen m_set_freed m_set_avail m_set_maplen m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem].
    rewrite HL. change (Z.land 0 31) with 0. cbn [Z.eqb andb]. replace ((needed + 4095) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite lookup_add_slots; [| lia| rewrite HS; unfold UNIT; lia].
  cbn [fst snd]. destruct (aptr_eqb_spec s (rid, 16)) as [->|NE].
  - cbn [fst snd]. rewrite N.eqb_refl. replace (16 - 0 - UNIT) with 0 by reflexivity.
    rewrite Z.mod_0_l, Z.div_0_l by (rewrite HS; unfold UNIT; lia). cbn. reflexivity.
  - destruct (N.eqb_spec (fst s) rid) as [E|E]; cbn [andb]; [| unfold st5; reflexivity].
    destruct (Z.leb_spec 0 (snd s - 0 - UNIT)); cbn [andb]; [| unfold st5; reflexivity].
    destruct (Z.eqb_spec ((snd s - 0 - UNIT) mod stride) 0); cbn [andb]; [| unfold st5; reflexivity].
    destruct (Z.ltb_spec ((snd s - 0 - UNIT) / stride) 1); [| unfold st5; reflexivity].
    exfalso. apply NE. destruct s as [sr so]; cbn in *. subst sr. f_equal.
    assert (D0 : (so - 0 - UNIT) / stride = 0) by (pose proof (Z.div_pos (so - 0 - UNIT) stride ltac:(lia) ltac:(rewrite HS; unfold UNIT; lia)); lia).
    pose proof (Z.div_mod (so - 0 - UNIT) stride ltac:(rewrite HS; unfold UNIT; lia)) as DM. unfold UNIT in *. lia.
Qed.
End BIGTAIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma am_post_facts st fl p :
  c_free_meta_head (ctx st) = fl -> c_avail_meta (ctx st) = Some p ->
  (forall f, fl = Some f -> m_next (get_meta_rec st f) = Some f) ->
  let '(st3, g) := am_post st in
  s_regions st3 = s_regions st /\ s_next_rid st3 = s_next_rid st /\ s_slots st3 = s_slots st /\ s_groups st3 = s_groups st
  /\ s_reserved st3 = s_reserved st
  /\ (forall x, get_meta_rec st3 x = if aptr_eqb x g then m_set_prev None (m_set_next None (get_meta_rec st g)) else get_meta_rec st x)
  /\ c_active (s_ctx st3) = c_active (s_ctx st) /\ c_usage (s_ctx st3) = c_usage (s_ctx st)
  /\ c_bounces (s_ctx st3) = c_bounces (s_ctx st) /\ c_unmap_seq (s_ctx st3) = c_unmap_seq (s_ctx st)
  /\ c_free_meta_head (s_ctx st3) = None
  /\ ((fl = Some g /\ c_avail_meta (s_ctx st3) = Some p /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx st))
      \/ (fl = None /\ g = p /\ c_avail_meta (s_ctx st3) = Some (aadd p META_SIZE) /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx st) - 1)).
Proof.
  intros Hfl Hp Hself. pose proof (am_init_eq st) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13).
  destruct fl as [f|].
  - rewrite (am_post_free st f Hfl (Hself f eq_refl)). cbn [set_head].
    unfold set_active. autorewrite with mst. cbn. autorewrite with mst.
    repeat split; try assumption; try reflexivity.
    + intros x. rewrite get_meta_rec_upd. unfold set_active. rewrite !get_meta_rec_upd_ctx. rewrite !(get_meta_rec_ext st (am_init st) _ I2). reflexivity.
    + left. unfold ctx in Hp. rewrite I8, I9, Hp. repeat split; reflexivity.
  - rewrite (am_post_avail st p Hfl Hp). autorewrite with mst. cbn. autorewrite with mst.
    unfold ctx in Hfl. repeat split; try assumption; try reflexivity; [| rewrite I7; exact Hfl|].
    + intros x. rewrite get_meta_rec_upd, !get_meta_rec_upd_ctx. rewrite !(get_meta_rec_ext st (am_init st) _ I2). reflexivity.
    + right. repeat split; try reflexivity. rewrite I9. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma RP_strip cs D fl lo : RP cs D fl lo -> strip cs = cs.
Proof.
  intros H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SH & TK).
  destruct cs; cbn in *. unfold strip. cbn. rewrite SH, TK. reflexivity.
Qed.

Section BIG.
Variables (cs : mstate) (D : list dblk) (fl : optr) (lo n : Z).
Hypothesis HRP : RP cs D fl lo.
Hypothesis Hn : MMAP_THRESHOLD <= n <= 2 ^ 26.
Let needed := n + IB + UNIT.
Let rid := s_next_rid cs.

Lemma big_ov : size_overflows n = false.
Proof. unfold size_overflows. apply Z.leb_gt. unfold MMAP_THRESHOLD in Hn. lia. Qed.

(* [comment removed for export] *)
Let st2 (r : Z) := step_seq (fst (new_region RKGroup r needed cs)).

Lemma st2_facts r :
  s_regions (st2 r) = <[rid := mkRegion RKGroup r needed]> (s_regions cs) /\ s_next_rid (st2 r) = N.succ rid
  /\ s_slots (st2 r) = s_slots cs /\ s_groups (st2 r) = s_groups cs /\ s_reserved (st2 r) = s_reserved cs
  /\ s_metas (st2 r) = s_metas cs
  /\ c_free_meta_head (s_ctx (st2 r)) = c_free_meta_head (s_ctx cs)
  /\ c_avail_meta (s_ctx (st2 r)) = c_avail_meta (s_ctx cs)
  /\ c_avail_meta_count (s_ctx (st2 r)) = c_avail_meta_count (s_ctx cs)
  /\ c_active (s_ctx (st2 r)) = c_active (s_ctx cs) /\ c_usage (s_ctx (st2 r)) = c_usage (s_ctx cs)
  /\ c_bounces (s_ctx (st2 r)) = c_bounces (s_ctx cs)
  /\ (forall i, unmap_seq cs i = 0 -> unmap_seq (st2 r) i = 0).
Proof.
  unfold st2. pose proof (step_seq_eq (fst (new_region RKGroup r needed cs))) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12. autorewrite with mst. repeat split; try reflexivity.
  intros i Hi. apply unmap_seq_step_seq. intros j. unfold unmap_seq, ctx. autorewrite with mst. apply (proj1 (proj2 (proj2 (proj2 (proj2 HRP))))).
Qed.

Lemma big_am_ok r : am_ok (st2 r).
Proof.
  pose proof (st2_facts r) as (_ & _ & _ & _ & _ & _ & F & A & C & _).
  destruct HRP as (_ & _ & _ & _ & _ & (p & Hp & _ & _ & Hlo & _ & Hfl & _) & _).
  unfold am_ok, ctx in *. rewrite F, A, C. destruct fl as [f|]; [left; rewrite Hfl; discriminate| right]. split; [lia| rewrite Hp; discriminate].
Qed.

Theorem big_site_ok_gen : big_site cs n.
Proof.
  unfold big_site, one_mmap_site.
  destruct (tnode_Some _ _ (malloc_core_big_node lay_none cs n (proj1 Hn) big_ov)) as (k0 & E & Ek).
  exists needed, (fun a => sbind (k0 a) cm_fin).
  split; [rewrite cmalloc_eq, E; reflexivity|].
  split; [unfold needed, IB, UNIT; lia|].
  split. { intros r Hr. rewrite <- Ek. apply rejects_sbind. apply malloc_core_big_bad; [exact (proj1 Hn)| exact big_ov| exact Hr]. }
  split. { intros r Hr He. rewrite <- Ek. rewrite (malloc_core_big_err lay_none cs n (proj1 Hn) big_ov r Hr He). exists (strip cs). reflexivity. }
  split. { rewrite <- Ek. rewrite (malloc_core_big_err lay_none cs n (proj1 Hn) big_ov ENOMEM_ans (ENOMEM_ans_ok _ _) ENOMEM_ans_err). exists (strip cs). reflexivity. }
  intros r NR He. rewrite <- Ek in NR |- *.
  destruct (mmap_answer_ok (live_ranges cs) needed r) eqn:Hr.
  2:{ exfalso. apply NR. apply rejects_sbind. apply malloc_core_big_bad; [exact (proj1 Hn)| exact big_ov| exact Hr]. }
  pose proof (malloc_core_big_ok lay_none cs n (proj1 Hn) big_ov r Hr He (big_am_ok r)) as EQ. cbn zeta in EQ.
  fold needed in EQ. fold (st2 r) in EQ. destruct (am_post (st2 r)) as [st3 g] eqn:AP.
  rewrite EQ. cbn [sbind cm_fin]. eexists _, _. reflexivity.
Qed.
End BIG.

Theorem big_site_ok : big_site_stmt.
Proof. intros cs D fl lo n HRP Hn. exact (big_site_ok_gen cs D fl lo n HRP Hn). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BIGRP.
Variables (cs : mstate) (d : dblk) (fl : optr) (n r : Z).
Let lo := match fl with None => 51 | Some _ => 50 end.
Hypothesis HRP : RP cs [d] fl lo.
Hypothesis Hn : MMAP_THRESHOLD <= n <= 2 ^ 26.
Let needed := n + IB + UNIT.
Let rid := s_next_rid cs.
Let st2 := step_seq (fst (new_region RKGroup r needed cs)).
Let st3 := fst (am_post st2).
Let g := snd (am_post st2).
Definition big_cs' : mstate := strip (big_tail lay_none st3 g rid needed).
Definition big_dnew : dblk := mkDB rid r needed g 63.

Lemma ml_facts : 0 < (needed + 4095) / 4096 < 2 ^ 52 /\ Z.land ((needed + 4095) / 4096) (2 ^ 52 - 1) = (needed + 4095) / 4096.
Proof.
  assert (0 < (needed + 4095) / 4096 < 2 ^ 52).
  { unfold needed, IB, UNIT, MMAP_THRESHOLD in *. split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  split; [exact H|]. apply land_small_ones; lia.
Qed.

Theorem big_RP2 : RP big_cs' [d; big_dnew] None 50.
Proof.
  destruct HRP as (HB & HA & HU & HBo & HUs & (p & Hp & Hp0 & Hp1 & Hlo & HDp & (HFL1 & HFL2)) & (r0 & Hr0 & Hk0 & Hl0) & HRex & HRfr & HGfr & HND1 & HND2 & HLen & HSH & HTK).
  apply Forall_cons_iff in HB as [Bd _]. destruct Bd as (Bd1 & Bd2 & Bd3 & Bd4 & Bd5 & Bd6 & Bd7).
  assert (Hcnt : 50 <= c_avail_meta_count (ctx cs) /\ (fl = None -> 51 <= c_avail_meta_count (ctx cs))).
  { unfold lo in Hlo. destruct fl; split; intros; try discriminate; lia. }
  destruct Hcnt as [Hcnt HcntN]. unfold ctx in Hcnt, HcntN.
  pose proof (st2_facts cs [d] fl lo n HRP r) as SF. cbn zeta in SF. fold needed in SF. fold rid in SF. fold st2 in SF.
  destruct SF as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
  assert (Hself : forall f, fl = Some f -> m_next (get_meta_rec st2 f) = Some f).
  { intros f Hf. rewrite (get_meta_rec_ext cs st2 f S6). destruct (HFL2 f Hf) as (E & _). rewrite E. reflexivity. }
  pose proof (am_post_facts st2 fl p ltac:(unfold ctx; rewrite S7; exact HFL1) ltac:(unfold ctx; rewrite S8; exact Hp) Hself) as AF.
  rewrite (surjective_pairing (am_post st2)) in AF. cbv iota beta in AF. fold st3 g in AF.
  destruct AF as (A1 & A2 & A3 & A4 & A5 & AM & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof (big_tail_fields st3 g rid needed) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11).
  pose proof (big_tail_meta st3 g rid needed) as TM.
  pose proof ml_facts as [ML1 ML2].
  assert (NEEDpos : 0 < needed) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof (big_tail_slots st3 g rid needed) as TS.
  (* [comment removed for export] *)
  assert (Gfacts : g <> db_meta d /\ fst g = 0%N /\ snd g < snd p + META_SIZE /\
                   exists p', c_avail_meta (s_ctx st3) = Some p' /\ fst p' = 0%N /\ snd p <= snd p' /\ snd g < snd p' /\ 50 <= c_avail_meta_count (s_ctx st3)).
  { destruct A12 as [(Hf & AV & AC)|(Hf & Gp & AV & AC)].
    - destruct (HFL2 g Hf) as (_ & F0 & Fs & NI). split; [intros E; apply NI; left; symmetry; exact E|]. split; [exact F0|].
      split; [unfold META_SIZE; lia|]. exists p. rewrite AV, AC, S9. repeat split; auto; lia.
    - split.
      { intros E. specialize (HDp d (or_introl eq_refl)). rewrite <- E, Gp in HDp. lia. }
      rewrite Gp.
      split; [exact Hp0|]. split; [unfold META_SIZE; lia|]. exists (aadd p META_SIZE). rewrite AV, AC, S9. unfold aadd, META_SIZE; cbn.
      specialize (HDp d (or_introl eq_refl)). specialize (HcntN Hf). repeat split; auto; lia. }
  destruct Gfacts as (Gne & G0 & Gs & (p' & P'1 & P'2 & P'3 & P'4 & P'5)).
  assert (RIDd : (db_rid d < rid)%N) by (unfold rid; eapply HRfr; exact Bd1).
  assert (RID0 : (0 < rid)%N) by (unfold rid; eapply HRfr; exact Hr0).
  unfold big_cs'. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]]]].
  - (* [comment removed for export] *)
    constructor; [| constructor; [| constructor]].
    + (* [comment removed for export] *)
      unfold blk_ok. rewrite s_regions_strip, s_slots_strip, get_meta_rec_strip, T1, A1, S1, TM.
      rewrite lookup_insert_ne by (intros E; rewrite E in RIDd; lia).
      rewrite (aptr_eqb_neq _ _ (not_eq_sym Gne)). rewrite AM. rewrite (aptr_eqb_neq _ _ (not_eq_sym Gne)).
      rewrite (get_meta_rec_ext cs st2 _ S6).
      rewrite TS by (unfold needed, IB, UNIT in *; lia). rewrite A3, S3.
      replace (aptr_eqb (db_slot d) (rid, 16)) with false.
      2:{ symmetry. apply aptr_eqb_neq. unfold db_slot. intros E. injection E. intros E1. rewrite E1 in RIDd. lia. }
      exact (conj Bd1 (conj Bd2 (conj Bd3 (conj Bd4 (conj Bd5 (conj Bd6 Bd7)))))).
    + (* [comment removed for export] *)
      unfold blk_ok, big_dnew, db_slot, db_ml. cbn [db_rid db_base db_len db_meta db_sc].
      rewrite s_regions_strip, s_slots_strip, get_meta_rec_strip, T1, A1, S1, TM, lookup_insert_eq.
      rewrite aptr_eqb_refl. rewrite TS by (unfold needed, IB, UNIT in *; lia). rewrite aptr_eqb_refl.
      rewrite AM, aptr_eqb_refl. cbn [m_prev m_next m_set_prev m_set_next]. rewrite ML2.
      unfold blk_meta. change (63 =? 44) with false.
      assert (NB : 0 < needed <= 2 ^ 26 + 20) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
      repeat split; try reflexivity; try lia. all: try (left; reflexivity). all: intros E; rewrite E in RID0; lia.
  - (* [comment removed for export] *)
    intros sc. rewrite active_strip. unfold active, ctx. rewrite T7, A7, S10. cbn [find44 find]. unfold big_dnew; cbn [db_sc].
    change (63 =? 44) with false. specialize (HA sc). unfold active, ctx in HA. rewrite HA. cbn [find44 find]. destruct (db_sc d =? 44); reflexivity.
  - (* [comment removed for export] *)
    intros sc. rewrite usage_strip. unfold usage, ctx. rewrite T8, A8, S11. specialize (HU sc). unfold usage, ctx in HU. rewrite HU.
    cbn [find44 find]. unfold big_dnew; cbn [db_sc]. change (63 =? 44) with false. destruct (db_sc d =? 44); reflexivity.
  - intros i. rewrite bounces_strip. unfold bounces, ctx. rewrite T9, A9, S12. apply HBo.
  - intros i. rewrite unmap_seq_strip. unfold unmap_seq, ctx. rewrite T10, A10. apply (S13 i (HUs i)).
  - (* [comment removed for export] *)
    exists p'. unfold freelist_ok, ctx. rewrite !s_ctx_strip, T5, T6, T4. split; [exact P'1|]. split; [exact P'2|]. split; [lia|]. split; [lia|].
    split.
    + intros x [<-|[<-|[]]]; [| cbn; exact P'4]. specialize (HDp d (or_introl eq_refl)). lia.
    + split; [exact A11|]. intros f Hf. discriminate.
  - (* [comment removed for export] *)
    exists r0. rewrite s_regions_strip, T1, A1, S1. rewrite lookup_insert_ne by (intros E; rewrite <- E in RID0; lia). auto.
  - (* [comment removed for export] *)
    intros q rq. rewrite s_regions_strip, T1, A1, S1. destruct (N.eq_dec q rid) as [->|NE].
    + intros _. right. cbn. right. left. reflexivity.
    + rewrite lookup_insert_ne by congruence. intros Hq. destruct (HRex q rq Hq) as [Z0|IN]; [left; exact Z0| right]. cbn in IN |- *. destruct IN as [IN|[]]. left; exact IN.
  - (* [comment removed for export] *)
    intros q rq. rewrite s_regions_strip, s_next_rid_strip, T1, T2, A1, A2, S1, S2. destruct (N.eq_dec q rid) as [->|NE]; [intros _; lia|].
    rewrite lookup_insert_ne by congruence. intros Hq. pose proof (HRfr q rq Hq). unfold rid. lia.
  - (* [comment removed for export] *)
    intros b h. rewrite s_groups_strip, s_next_rid_strip, T11, T2, A2, S2, A4, S4.
    destruct (aptr_eqb_spec b (rid, 0)) as [->|NE]; [intros _; cbn; lia|].
    rewrite lookup_insert_ne by congruence. intros Hb. pose proof (HGfr b h Hb). unfold rid. lia.
  - (* [comment removed for export] *)
    cbn. constructor; [| constructor; [intros []| constructor]]. intros [E|[]]. rewrite <- E in RIDd. lia.
  - cbn. constructor; [| constructor; [intros []| constructor]]. intros [E|[]]. exact (Gne E).
  - cbn. lia.
  - reflexivity.
  - reflexivity.
Qed.
End BIGRP.

Theorem big_follow_ok : big_follow_stmt.
Proof.
  intros cs d n ans cs' res [fl HRP] Hn Hf.
  pose proof (big_ov cs n Hn) as Hov.
  rewrite cmalloc_eq in Hf. destruct (tnode_Some _ _ (malloc_core_big_node lay_none cs n (proj1 Hn) Hov)) as (k0 & E & Ek).
  rewrite E in Hf. cbn [sbind follow] in Hf. destruct ans as [|r rest]; [discriminate|].
  rewrite <- Ek in Hf.
  destruct (mmap_answer_ok (live_ranges cs) (n + IB + UNIT) r) eqn:Hr.
  2:{ rewrite follow_rejects in Hf; [discriminate|]. apply rejects_sbind. apply malloc_core_big_bad; assumption || exact (proj1 Hn). }
  destruct (is_err r) eqn:He.
  - rewrite (malloc_core_big_err lay_none cs n (proj1 Hn) Hov r Hr He) in Hf. cbn in Hf.
    inversion Hf; subst. exact (RP_strip _ _ _ _ HRP).
  - pose proof (malloc_core_big_ok lay_none cs n (proj1 Hn) Hov r Hr He (big_am_ok cs [d] fl _ n HRP r)) as EQ. cbn zeta in EQ.
    rewrite (surjective_pairing (am_post _)) in EQ. rewrite EQ in Hf. cbn [sbind cm_fin ret follow] in Hf.
    inversion Hf; subst. clear Hf.
    exists (big_dnew cs n r). split; [| split; [| split; [reflexivity| split; [cbn [big_dnew db_len]; unfold IB, UNIT; lia| split; [reflexivity| split]]]]].
    + split; [exact (big_RP2 cs d fl n r HRP Hn)| reflexivity].
    + unfold slot_of, db_slot, big_dnew. cbn [db_rid]. rewrite big_tail_meta, aptr_eqb_refl. unfold slot_start'. cbn [m_mem default fst snd aadd]. unfold aadd. cbn [fst snd]. f_equal. rewrite Z.mul_0_r. reflexivity.
    + exists r, rest. split; reflexivity.
    + cbn [db_rid db_base big_dnew]. unfold big_cs'. rewrite s_regions_strip.
      destruct (big_tail_fields (fst (am_post (step_seq (fst (new_region RKGroup r (n + IB + UNIT) cs))))) (snd (am_post (step_seq (fst (new_region RKGroup r (n + IB + UNIT) cs))))) (s_next_rid cs) (n + IB + UNIT)) as (T1 & _).
      rewrite T1. destruct (st2_facts cs [d] fl _ n HRP r) as (S1 & _).
      destruct (HRP) as (_ & _ & _ & _ & _ & (p & Hp & _ & _ & _ & _ & (HFL1 & HFL2)) & _).
      assert (Hself : forall f, fl = Some f -> m_next (get_meta_rec (step_seq (fst (new_region RKGroup r (n + IB + UNIT) cs))) f) = Some f).
      { intros f Hf. destruct (step_seq_eq (fst (new_region RKGroup r (n + IB + UNIT) cs))) as (_ & M & _). rewrite (get_meta_rec_ext cs); [| rewrite M; reflexivity].
        destruct (HFL2 f Hf) as (E2 & _). rewrite E2. reflexivity. }
      pose proof (am_post_facts (step_seq (fst (new_region RKGroup r (n + IB + UNIT) cs))) fl p) as AF.
      destruct (step_seq_eq (fst (new_region RKGroup r (n + IB + UNIT) cs))) as (_ & _ & _ & _ & _ & _ & F7 & F8 & _).
      specialize (AF ltac:(unfold ctx; rewrite F7; autorewrite with mst; exact HFL1) ltac:(unfold ctx; rewrite F8; autorewrite with mst; exact Hp) Hself).
      rewrite (surjective_pairing (am_post _)) in AF. cbv iota beta in AF. destruct AF as (A1 & _). rewrite A1, S1. replace (n + 20) with (n + IB + UNIT) by (unfold IB, UNIT; lia). apply lookup_insert_eq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREE.
Variables (cs : mstate) (dold dnew : dblk).
Hypothesis HRP : RP2 cs dold dnew.
Let g := db_meta dold.
Let rid := db_rid dold.
Let sc := db_sc dold.
Let ml := db_ml dold.
Let st1 := free_pre cs g sc.
Let st2 := del_slots (rid, 0) (ml * 4096 - UNIT) 1 (del_group (rid, 0) st1).
Let st3 := record_seq sc (step_seq st2).
Let cs'' := free_post cs g rid sc ml.

Lemma dold_facts :
  blk_ok cs dold /\ blk_ok cs dnew /\ db_sc dnew = 63 /\ 0 < ml /\ (sc = 63 \/ (sc = 44 /\ ml = 17))
  /\ active cs 44 = (if sc =? 44 then Some g else None) /\ db_meta dnew <> g /\ db_rid dnew <> rid.
Proof.
  destruct HRP as [(HB & HA & HU & _ & _ & _ & _ & _ & _ & _ & ND1 & ND2 & _) Hsc].
  apply Forall_cons_iff in HB as [B1 HB]. apply Forall_cons_iff in HB as [B2 _].
  pose proof B1 as (_ & _ & _ & L1 & SC1 & _). 
  assert (HML : 0 < ml /\ (sc = 63 \/ (sc = 44 /\ ml = 17))).
  { unfold ml, sc, db_ml. split; [apply Z.div_str_pos; lia|]. destruct SC1 as [E|[E EL]]; [left; exact E| right]. rewrite EL. split; [exact E| reflexivity]. }
  split; [exact B1|]. split; [exact B2|]. split; [exact Hsc|]. split; [apply HML|]. split; [apply HML|]. split.
  - rewrite (HA 44). cbn [find44 find]. unfold sc, g. destruct (db_sc dold =? 44) eqn:E; [reflexivity|]. rewrite Hsc. reflexivity.
  - split.
    + intros E. cbn in ND2. inversion ND2; subst. apply H1. left. unfold g in E. exact E.
    + intros E. cbn in ND1. inversion ND1; subst. apply H1. left. unfold rid in E. exact E.
Qed.

Lemma st1_eq : st1 = (if sc =? 44 then set_usage 44 (usage cs 44 - 1) (upd_meta g (fun r => m_set_prev None (m_set_next None r)) (set_active 44 None cs)) else cs).
Proof.
  destruct dold_facts as (B1 & _ & _ & _ & SC & _).
  unfold st1, free_pre. destruct SC as [E|[E _]]; rewrite E; [reflexivity|].
  change (44 =? 44) with true. change (44 <? 48) with true. cbv iota.
  rewrite dequeue_self.
  2:{ destruct B1 as (_ & _ & M & _). unfold g. rewrite M. unfold blk_meta. fold sc. rewrite E. reflexivity. }
  reflexivity.
Qed.

Lemma st3_facts :
  s_regions st3 = s_regions cs /\ s_next_rid st3 = s_next_rid cs /\ s_reserved st3 = s_reserved cs
  /\ s_groups st3 = delete (rid, 0) (s_groups cs)
  /\ (forall s, s_slots st3 !! s = if aptr_eqb s (rid, 16) then None else s_slots cs !! s)
  /\ (forall x, x <> g -> get_meta_rec st3 x = get_meta_rec cs x)
  /\ (forall j, active st3 j = if (sc =? 44) && (j =? 44) then None else active cs j)
  /\ (forall j, usage st3 j = if (sc =? 44) && (j =? 44) then usage cs 44 - 1 else usage cs j)
  /\ (forall i, bounces st3 i = bounces cs i)
  /\ (forall i, unmap_seq cs i = 0 -> unmap_seq st3 i = 0)
  /\ c_free_meta_head (s_ctx st3) = c_free_meta_head (s_ctx cs)
  /\ c_avail_meta (s_ctx st3) = c_avail_meta (s_ctx cs)
  /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx cs).
Proof.
  destruct dold_facts as (B1 & _ & _ & ML & SC & _).
  assert (RS : record_seq sc (step_seq st2) = step_seq st2).
  { unfold record_seq. replace (sc_in_seq_range sc) with false; [reflexivity|]. unfold sc_in_seq_range. symmetry. destruct SC as [E|[E _]]; rewrite E; reflexivity. }
  unfold st3. rewrite RS.
  pose proof (step_seq_eq st2) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold active, usage, bounces, ctx. rewrite A1, A4, A5, A6, A7, A8, A9, A10, A11, A12.
  unfold st2. autorewrite with mst.
  assert (SL : forall s, s_slots (del_slots (rid, 0) (ml * 4096 - UNIT) 1 (del_group (rid, 0) st1)) !! s = if aptr_eqb s (rid, 16) then None else s_slots st1 !! s).
  { intros s. rewrite lookup_del_slots; [| lia| unfold UNIT; lia]. cbn [fst snd].
    destruct (aptr_eqb_spec s (rid, 16)) as [->|NE].
    - cbn [fst snd]. rewrite N.eqb_refl. replace (16 - 0 - UNIT) with 0 by reflexivity. rewrite Z.mod_0_l, Z.div_0_l by (unfold UNIT; lia). cbn. reflexivity.
    - destruct (N.eqb_spec (fst s) rid) as [E|E]; cbn [andb]; [| reflexivity].
      destruct (Z.leb_spec 0 (snd s - 0 - UNIT)); cbn [andb]; [| reflexivity].
      destruct (Z.eqb_spec ((snd s - 0 - UNIT) mod (ml * 4096 - UNIT)) 0); cbn [andb]; [| reflexivity].
      destruct (Z.ltb_spec ((snd s - 0 - UNIT) / (ml * 4096 - UNIT)) 1); [| reflexivity].
      exfalso. apply NE. destruct s as [sr so]; cbn in *. subst sr. f_equal.
      assert (D0 : (so - 0 - UNIT) / (ml * 4096 - UNIT) = 0) by (pose proof (Z.div_pos (so - 0 - UNIT) (ml * 4096 - UNIT) ltac:(lia) ltac:(unfold UNIT; lia)); lia).
      pose proof (Z.div_mod (so - 0 - UNIT) (ml * 4096 - UNIT) ltac:(unfold UNIT; lia)) as DM. unfold UNIT in *. lia. }
  rewrite st1_eq in SL |- *. destruct (sc =? 44).
  - unfold set_active. autorewrite with mst. cbn [c_usage c_active set_usage_map set_active_map c_free_meta_head c_avail_meta c_avail_meta_count c_bounces c_unmap_seq].
    autorewrite with mst.
    repeat split; try reflexivity.
    + intros s. rewrite SL. unfold set_usage, set_active. autorewrite with mst. reflexivity.
    + intros x NE. rewrite (get_meta_rec_ext (set_usage 44 (default 0 (c_usage (s_ctx cs) !! 44) - 1) (upd_meta g (λ r : meta, m_set_prev None (m_set_next None r)) (upd_ctx (λ c : mctx, set_active_map (delete 44 (c_active c)) c) cs)))).
      2:{ autorewrite with mst. reflexivity. }
      unfold set_usage. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_other, get_meta_rec_upd_ctx by exact NE. reflexivity.
    + intros j. destruct (Z.eqb_spec j 44) as [->|NE]; [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
    + intros j. destruct (Z.eqb_spec j 44) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
    + intros i Hi. apply unmap_seq_step_seq. intros i'. unfold unmap_seq, ctx. autorewrite with mst. cbn. apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRP)))))).
  - cbn [andb]. repeat split; try reflexivity.
    + intros s. rewrite SL. reflexivity.
    + intros x NE. apply get_meta_rec_ext. autorewrite with mst. reflexivity.
    + intros i Hi. apply unmap_seq_step_seq. intros i'. unfold unmap_seq, ctx. autorewrite with mst. apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRP)))))).
Qed.
End FREE.

Lemma fm_post_empty g st :
  c_free_meta_head (ctx st) = None ->
  fm_post g st = upd_ctx (set_free_meta_head (Some g))
                   (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) (put_meta g meta0 st)).
Proof. intros H. unfold fm_post, q_post. cbn [get_head]. unfold ctx in *. rewrite s_ctx_put_meta, H. reflexivity. Qed.

Section FREE2.
Variables (cs : mstate) (dold dnew : dblk).
Hypothesis HRP : RP2 cs dold dnew.
Definition free_cs' : mstate := free_post cs (db_meta dold) (db_rid dold) (db_sc dold) (db_ml dold).

Lemma free_post0_eq : free_post0 cs (db_meta dold) (db_rid dold) (db_sc dold) (db_ml dold) = upd_ctx (set_free_meta_head (Some (db_meta dold)))
                   (upd_meta (db_meta dold) (fun r => m_set_prev (Some (db_meta dold)) (m_set_next (Some (db_meta dold)) r)) (put_meta (db_meta dold) meta0
                      (record_seq (db_sc dold) (step_seq (del_slots (db_rid dold, 0) (db_ml dold * 4096 - UNIT) 1 (del_group (db_rid dold, 0) (free_pre cs (db_meta dold) (db_sc dold)))))))).
Proof.
  unfold free_post0. apply fm_post_empty.
  destruct (st3_facts cs dold dnew HRP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _).
  destruct HRP as [(_ & _ & _ & _ & _ & (p & _ & _ & _ & _ & _ & (HFL & _)) & _) _].
  unfold ctx in *. rewrite F. exact HFL.
Qed.

Theorem free_RP1 : RP free_cs' [dnew] (Some (db_meta dold)) 50.
Proof.
  pose proof (dold_facts cs dold dnew HRP) as (B1 & B2 & SC2 & ML & SC & ACT & NEg & NErid).
  pose proof (st3_facts cs dold dnew HRP) as SF.
  destruct HRP as [(HB & HA & HU & HBo & HUs & (p & Hp & Hp0 & Hp1 & Hlo & HDp & (HFL1 & HFL2)) & (r0 & Hr0 & Hk0 & Hl0) & HRex & HRfr & HGfr & HND1 & HND2 & HLen & HSH & HTK) Hsc].
  destruct B1 as (Bo1 & Bo2 & Bo3 & Bo4 & Bo5 & Bo6 & Bo7). destruct B2 as (Bn1 & Bn2 & Bn3 & Bn4 & Bn5 & Bn6 & Bn7).
  unfold free_cs', free_post. rewrite free_post0_eq.
  set (g := db_meta dold) in *. set (rid := db_rid dold) in *. set (sc := db_sc dold) in *. set (ml := db_ml dold) in *.
  remember (record_seq sc (step_seq (del_slots (rid, 0) (ml * 4096 - UNIT) 1 (del_group (rid, 0) (free_pre cs g sc))))) as s3 eqn:Hs3 in *. clear Hs3.
  destruct SF as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
  set (st4 := upd_ctx _ (upd_meta g _ (put_meta g meta0 s3))).
  assert (M4 : forall x, get_meta_rec st4 x = if aptr_eqb x g then mkMeta (Some g) (Some g) None 0 0 0 0 0 0 else get_meta_rec s3 x).
  { intros x. unfold st4. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd, get_meta_rec_put_same, get_meta_rec_put. destruct (aptr_eqb x g); reflexivity. }
  assert (C4 : s_regions st4 = s_regions cs /\ s_next_rid st4 = s_next_rid cs /\ s_groups st4 = delete (rid, 0) (s_groups cs) /\ s_slots st4 = s_slots s3
               /\ c_active (s_ctx st4) = c_active (s_ctx s3) /\ c_usage (s_ctx st4) = c_usage (s_ctx s3) /\ c_bounces (s_ctx st4) = c_bounces (s_ctx s3)
               /\ c_unmap_seq (s_ctx st4) = c_unmap_seq (s_ctx s3) /\ c_free_meta_head (s_ctx st4) = Some g
               /\ c_avail_meta (s_ctx st4) = c_avail_meta (s_ctx cs) /\ c_avail_meta_count (s_ctx st4) = c_avail_meta_count (s_ctx cs)).
  { unfold st4. autorewrite with mst. cbn. rewrite S1, S2, S4, S12, S13. repeat split; reflexivity. }
  destruct C4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  assert (RIDn0 : rid <> 0%N) by exact Bo6.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]]]].
  - constructor; [| constructor]. unfold blk_ok.
    rewrite s_regions_strip, s_slots_strip, get_meta_rec_strip, lookup_drop_region, C1.
    replace (db_rid dnew =? rid)%N with false by (symmetry; apply N.eqb_neq; exact NErid).
    unfold drop_region. rewrite s_slots_set_shadow, s_slots_set_regions, C4, S5.
    replace (aptr_eqb (db_slot dnew) (rid, 16)) with false by (symmetry; apply aptr_eqb_neq; unfold db_slot; intros E; injection E; intros E1; exact (NErid E1)).
    rewrite (get_meta_rec_ext st4); [| reflexivity]. rewrite M4. rewrite (aptr_eqb_neq _ _ NEg). rewrite (S6 _ NEg).
    exact (conj Bn1 (conj Bn2 (conj Bn3 (conj Bn4 (conj Bn5 (conj Bn6 Bn7)))))).
  - intros j. rewrite active_strip. unfold active, ctx. unfold drop_region. autorewrite with mst. rewrite ?C5.
    pose proof (S7 j) as A. unfold active, ctx in A. rewrite A.
    pose proof (HA j) as B. unfold active, ctx in B. rewrite B. cbn [find44 find]. rewrite SC2. change (63 =? 44) with false. unfold sc.
    destruct (db_sc dold =? 44); cbn [andb]; [destruct (j =? 44); reflexivity| reflexivity].
  - intros j. rewrite usage_strip. unfold usage, ctx. unfold drop_region. autorewrite with mst. rewrite ?C6.
    pose proof (S8 j) as A. unfold usage, ctx in A. rewrite A. cbn [find44 find]. rewrite SC2. change (63 =? 44) with false.
    pose proof (HU 44) as U44. pose proof (HU j) as Uj. cbn [find44 find] in U44, Uj. rewrite SC2 in U44, Uj. change (63 =? 44) with false in U44. change (63 =? 44) with false in Uj.
    unfold usage, ctx in U44, Uj. unfold sc.
    destruct (db_sc dold =? 44); cbn [andb]; [| exact Uj]. destruct (j =? 44); [| exact Uj]. rewrite U44. reflexivity.
  - intros i. rewrite bounces_strip. unfold bounces, ctx, drop_region. autorewrite with mst. rewrite ?C7. pose proof (S9 i) as A. unfold bounces, ctx in A. rewrite A. apply HBo.
  - intros i. rewrite unmap_seq_strip. unfold unmap_seq, ctx, drop_region. autorewrite with mst. rewrite ?C8. pose proof (S10 i (HUs i)) as A. unfold unmap_seq, ctx in A. exact A.
  - exists p. unfold freelist_ok, ctx, drop_region. rewrite !s_ctx_strip. autorewrite with mst. rewrite ?C10, ?C11, ?C9, ?S12, ?S13.
    unfold ctx in Hp, Hlo. cbn [c_free_meta_head set_free_meta_head].
    split; [exact Hp|]. split; [exact Hp0|]. split; [exact Hp1|]. split; [lia|]. split.
    + intros x [<-|[]]. apply HDp. right; left; reflexivity.
    + split; [reflexivity|]. intros f Hf. injection Hf. intros <-. rewrite get_meta_rec_strip.
      rewrite (get_meta_rec_ext st4); [| reflexivity]. rewrite M4, aptr_eqb_refl.
      split; [reflexivity|]. split; [exact Bo7|]. split; [apply HDp; left; reflexivity|].
      cbn. intros [E|[]]. exact (NEg E).
  - exists r0. rewrite s_regions_strip, lookup_drop_region. unfold drop_region. autorewrite with mst. rewrite ?C1, ?S1. replace (0 =? rid)%N with false by (symmetry; apply N.eqb_neq; congruence). auto.
  - intros q rq. rewrite s_regions_strip, lookup_drop_region. unfold drop_region. autorewrite with mst. rewrite ?C1, ?S1. destruct (N.eqb_spec q rid) as [->|NE]; [discriminate|].
    intros Hq. destruct (HRex q rq Hq) as [Z0|IN]; [left; exact Z0|]. cbn in IN. destruct IN as [E|[E|[]]]; [exfalso; apply NE; rewrite <- E; reflexivity| right; left; exact E].
  - intros q rq. rewrite s_regions_strip, s_next_rid_strip, lookup_drop_region. unfold drop_region. autorewrite with mst. rewrite ?C1, ?C2, ?S1, ?S2.
    destruct (N.eqb_spec q rid); [discriminate|]. apply HRfr.
  - intros b h. rewrite s_groups_strip, s_next_rid_strip. unfold drop_region. autorewrite with mst. rewrite ?C3, ?C2, ?S4, ?S2.
    destruct (aptr_eqb_spec b (rid, 0)) as [->|NE]; [rewrite lookup_delete_eq; discriminate|]. rewrite lookup_delete_ne by congruence. apply HGfr.
  - cbn. constructor; [intros []| constructor].
  - cbn. constructor; [intros []| constructor].
  - cbn. lia.
  - reflexivity.
  - reflexivity.
Qed.

Theorem free_site_gen :
  exists k,
    cfree cs (Some (db_slot dold)) = SVis (EMunmap (db_base dold) (db_ml dold * 4096)) k
    /\ db_ml dold * 4096 = round_up_pg (db_len dold)
    /\ s_regions cs !! db_rid dold = Some (mkRegion RKGroup (db_base dold) (db_len dold))
    /\ (forall ru, munmap_answer_ok ru = true -> k ru = SRet free_cs')
    /\ (forall ru, munmap_answer_ok ru = false -> rejects (k ru))
    /\ RP1 free_cs' dnew /\ s_regions free_cs' !! db_rid dold = None
    /\ (forall q, q <> db_rid dold -> s_regions free_cs' !! q = s_regions cs !! q).
Proof.
  pose proof (dold_facts cs dold dnew HRP) as (B1 & B2 & SC2 & ML & SC & ACT & NEg & NErid).
  destruct B1 as (Bo1 & Bo2 & Bo3 & Bo4 & Bo5 & Bo6 & Bo7).
  set (g := db_meta dold) in *. set (rid := db_rid dold) in *. set (sc := db_sc dold) in *. set (ml := db_ml dold) in *.
  assert (CL : blk_class_ok cs g sc ml).
  { unfold blk_class_ok. destruct SC as [E|[E EM]]; [left; exact E| right]. split; [exact E|]. split; [exact EM|]. rewrite ACT, E. reflexivity. }
  destruct (cfree_blk cs (db_slot dold) g rid sc ml Bo2 Bo3 ML CL) as (TN & TOK & TBAD).
  destruct (tnode_Some _ _ TN) as (k & E & Ek).
  assert (CONC : conc (free_post0 cs g rid sc ml) (rid, 0) = db_base dold).
  { rewrite (free_post0_eq). unfold conc, get_region. rewrite s_regions_upd_ctx, s_regions_upd_meta, s_regions_put_meta.
    destruct (st3_facts cs dold dnew HRP) as (S1 & _). rewrite S1. unfold rid. rewrite Bo1. cbn. lia. }
  exists k. rewrite E, CONC. split; [reflexivity|]. split.
  { unfold ml, db_ml. pose proof (MI_Cnt.round_up_pg_spec (db_len dold)) as [R1 R2].
    pose proof (Z.div_mod (round_up_pg (db_len dold)) 4096 ltac:(lia)) as DM. rewrite R2 in DM.
    assert ((db_len dold + 4095) / 4096 = round_up_pg (db_len dold) / 4096) as ->.
    { symmetry. apply Z.div_unique with (r := db_len dold + 4095 - round_up_pg (db_len dold)); [left; lia| lia]. }
    lia. }
  split; [exact Bo1|].
  split; [intros ru Hru; rewrite <- Ek; exact (TOK ru Hru)|].
  split; [intros ru Hru; rewrite <- Ek; exact (TBAD ru Hru)|].
  split; [exists (Some g); exact free_RP1|].
  destruct (st3_facts cs dold dnew HRP) as (S1 & _).
  unfold free_cs', free_post. rewrite free_post0_eq. split.
  - rewrite s_regions_strip, lookup_drop_region, N.eqb_refl. reflexivity.
  - intros q NE. rewrite s_regions_strip, lookup_drop_region, s_regions_upd_ctx, s_regions_upd_meta, s_regions_put_meta, S1.
    replace (q =? rid)%N with false by (symmetry; apply N.eqb_neq; exact NE). reflexivity.
Qed.
End FREE2.

Theorem free_site_ok : free_site_stmt.
Proof.
  intros cs dold dnew HRP. destruct (free_site_gen cs dold dnew HRP) as (k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exists k, (free_cs' cs dold). repeat split; assumption.
Qed.

Theorem free_follow_ok : free_follow_stmt.
Proof.
  intros cs dold dnew ans cs' HRP Hf. destruct (free_site_gen cs dold dnew HRP) as (k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  rewrite H1 in Hf. cbn [follow] in Hf. destruct ans as [|ru rest]; [discriminate|].
  destruct (munmap_answer_ok ru) eqn:Hru.
  - rewrite (H4 ru Hru) in Hf. cbn in Hf. destruct rest; inversion Hf; subst; exact H6.
  - rewrite (follow_rejects _ _ (H5 ru Hru)) in Hf. discriminate.
Qed.


End CeilWrap.
End MEX_big.

(* [comment removed for export] *)
Module MEX_m0rp.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_m0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma follow_step {R} (T : M R) L e K a rest :
  tsubs T L = SVis e K -> match e with EUndef _ => False | _ => True end ->
  follow (tsubs T L) (a :: rest) = follow (tsubs T (L ++ [a])) rest.
Proof. intros H He. rewrite tsubs_app. cbn [tsubs]. rewrite H. cbn [tsub follow]. destruct e; try reflexivity. destruct He. Qed.

Lemma follow_stop {R} (T : M R) L e K : tsubs T L = SVis e K -> follow (tsubs T L) [] = None.
Proof. intros H. rewrite H. cbn. destruct e; reflexivity. Qed.

Lemma follow_end {R} (T : M R) L x rest : tsubs T L = SRet x -> follow (tsubs T L) rest = Some x.
Proof. intros H. rewrite H. destruct rest; reflexivity. Qed.

(* [comment removed for export] *)
Definition cm_val (x : mstate * option (aptr * Z)) : mstate * option cptr :=
  (strip (fst x), match snd x with Some (g, idx) => Some (slot_of (fst x) g idx) | None => None end).

Lemma cm_fin_val x : cm_fin x = SRet (cm_val x).
Proof. destruct x as [st [[g idx]|]]; reflexivity. Qed.

Lemma follow_sbind_leaf {R S} (f : R -> M S) (h : R -> S) :
  (forall x, f x = SRet (h x)) -> forall (t : M R) ans, follow (sbind t f) ans = option_map h (follow t ans).
Proof.
  intros Hf. induction t as [r|e k IH]; intros ans; cbn.
  - rewrite Hf. destruct ans; reflexivity.
  - destruct e; destruct ans; cbn; try reflexivity; apply IH.
Qed.

Lemma follow_cmalloc cs n ans : follow (cmalloc cs n) ans = option_map cm_val (follow (malloc_core lay_none cs n) ans).
Proof. rewrite cmalloc_eq. apply (follow_sbind_leaf cm_fin cm_val cm_fin_val). Qed.

Lemma follow_ret {R} (x : R) rest : follow (ret x) rest = Some x.
Proof. destruct rest; reflexivity. Qed.

Lemma some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. intros H. injection H. auto. Qed.

Lemma some_pair_inj {A B} (a c : A) (b d : B) : Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof. intros H. injection H. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section M0RP.
Variable resv : list (Z * Z).

Lemma m0_RP1_A cur r : RP (m0_post resv (VA cur) r) [d0 r] None 51.
Proof.
  set (v := VA cur). set (R0 := mkRegion RKBrk (round_up_pg cur) (2 * PGSZ)).
  unfold RP. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]]]].
  - constructor; [| constructor]. unfold blk_ok, d0, db_slot, db_ml; cbn [db_rid db_base db_len db_meta db_sc].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|]. split; [right; split; reflexivity|]. split; [discriminate| reflexivity].
  - intros sc. cbn [find44 find d0 db_sc Z.eqb Pos.eqb db_meta].
    change (active (m0_post resv v r) sc) with ((<[44 := m0]> (∅ : gmap Z aptr)) !! sc).
    destruct (Z.eq_dec sc 44) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
    rewrite lookup_insert_ne by congruence. rewrite lookup_empty. replace (sc =? 44) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
  - intros sc. cbn [find44 find d0 db_sc Z.eqb Pos.eqb db_meta].
    change (usage (m0_post resv v r) sc) with (default 0 ((<[44 := 0 + 1]> (∅ : gmap Z Z)) !! sc)).
    destruct (Z.eq_dec sc 44) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
    rewrite lookup_insert_ne by congruence. rewrite lookup_empty. replace (sc =? 44) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
  - intros i. change (bounces (m0_post resv v r) i) with (default 0 ((∅ : gmap Z Z) !! i)). rewrite lookup_empty. reflexivity.
  - intros i. change (unmap_seq (m0_post resv v r) i) with (default 0 ((∅ : gmap Z Z) !! i)). rewrite lookup_empty. reflexivity.
  - exists (0%N, 4160). split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|].
    split; [change (c_avail_meta_count (ctx (m0_post resv v r))) with (101 - 1); lia|].
    split; [intros d [<-|[]]; cbn; lia|].
    split; [reflexivity|]. intros f Hf; discriminate.
  - exists R0. split; [reflexivity|]. split; [discriminate| reflexivity].
  - intros rid rg. 
    change (s_regions (m0_post resv v r)) with (<[1%N := mkRegion RKGroup r 69632]> (<[0%N := R0]> (∅ : gmap N region))).
    destruct (N.eq_dec rid 1%N) as [->|N1]; [intros _; right; left; reflexivity|].
    destruct (N.eq_dec rid 0%N) as [->|N0]; [intros _; left; reflexivity|].
    rewrite lookup_insert_ne, lookup_insert_ne, lookup_empty by congruence. discriminate.
  - intros rid rg. change (s_next_rid (m0_post resv v r)) with 2%N.
    change (s_regions (m0_post resv v r)) with (<[1%N := mkRegion RKGroup r 69632]> (<[0%N := R0]> (∅ : gmap N region))).
    destruct (N.eq_dec rid 1%N) as [->|N1]; [intros _; lia|].
    destruct (N.eq_dec rid 0%N) as [->|N0]; [intros _; lia|].
    rewrite lookup_insert_ne, lookup_insert_ne, lookup_empty by congruence. discriminate.
  - intros b h. change (s_next_rid (m0_post resv v r)) with 2%N.
    change (s_groups (m0_post resv v r)) with (<[(1%N, 0) := mkGhdr (Some m0) (Z.land 0 31)]> (∅ : gmap aptr ghdr)).
    destruct (aptr_eqb_spec b (1%N, 0)) as [->|NE]; [intros _; cbn; lia|].
    rewrite lookup_insert_ne, lookup_empty by congruence. discriminate.
  - cbn. constructor; [intros []| constructor].
  - cbn. constructor; [intros []| constructor].
  - cbn. lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma m0_RP1_B am r : RP (m0_post resv (VB am) r) [d0 r] None 51.
Proof.
  set (v := VB am). set (R0 := mkRegion RKMeta am (2 * PGSZ)).
  unfold RP. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]]]].
  - constructor; [| constructor]. unfold blk_ok, d0, db_slot, db_ml; cbn [db_rid db_base db_len db_meta db_sc].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|]. split; [right; split; reflexivity|]. split; [discriminate| reflexivity].
  - intros sc. cbn [find44 find d0 db_sc Z.eqb Pos.eqb db_meta].
    change (active (m0_post resv v r) sc) with ((<[44 := m0]> (∅ : gmap Z aptr)) !! sc).
    destruct (Z.eq_dec sc 44) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
    rewrite lookup_insert_ne by congruence. rewrite lookup_empty. replace (sc =? 44) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
  - intros sc. cbn [find44 find d0 db_sc Z.eqb Pos.eqb db_meta].
    change (usage (m0_post resv v r) sc) with (default 0 ((<[44 := 0 + 1]> (∅ : gmap Z Z)) !! sc)).
    destruct (Z.eq_dec sc 44) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
    rewrite lookup_insert_ne by congruence. rewrite lookup_empty. replace (sc =? 44) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
  - intros i. change (bounces (m0_post resv v r) i) with (default 0 ((∅ : gmap Z Z) !! i)). rewrite lookup_empty. reflexivity.
  - intros i. change (unmap_seq (m0_post resv v r) i) with (default 0 ((∅ : gmap Z Z) !! i)). rewrite lookup_empty. reflexivity.
  - exists (0%N, 4160). split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|].
    split; [change (c_avail_meta_count (ctx (m0_post resv v r))) with (101 - 1); lia|].
    split; [intros d [<-|[]]; cbn; lia|].
    split; [reflexivity|]. intros f Hf; discriminate.
  - exists R0. split; [reflexivity|]. split; [discriminate| reflexivity].
  - intros rid rg. 
    change (s_regions (m0_post resv v r)) with (<[1%N := mkRegion RKGroup r 69632]> (<[0%N := R0]> (∅ : gmap N region))).
    destruct (N.eq_dec rid 1%N) as [->|N1]; [intros _; right; left; reflexivity|].
    destruct (N.eq_dec rid 0%N) as [->|N0]; [intros _; left; reflexivity|].
    rewrite lookup_insert_ne, lookup_insert_ne, lookup_empty by congruence. discriminate.
  - intros rid rg. change (s_next_rid (m0_post resv v r)) with 2%N.
    change (s_regions (m0_post resv v r)) with (<[1%N := mkRegion RKGroup r 69632]> (<[0%N := R0]> (∅ : gmap N region))).
    destruct (N.eq_dec rid 1%N) as [->|N1]; [intros _; lia|].
    destruct (N.eq_dec rid 0%N) as [->|N0]; [intros _; lia|].
    rewrite lookup_insert_ne, lookup_insert_ne, lookup_empty by congruence. discriminate.
  - intros b h. change (s_next_rid (m0_post resv v r)) with 2%N.
    change (s_groups (m0_post resv v r)) with (<[(1%N, 0) := mkGhdr (Some m0) (Z.land 0 31)]> (∅ : gmap aptr ghdr)).
    destruct (aptr_eqb_spec b (1%N, 0)) as [->|NE]; [intros _; cbn; lia|].
    rewrite lookup_insert_ne, lookup_empty by congruence. discriminate.
  - cbn. constructor; [intros []| constructor].
  - cbn. constructor; [intros []| constructor].
  - cbn. lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma m0_RP1 v r : RP (m0_post resv v r) [d0 r] None 51.
Proof. destruct v; [apply m0_RP1_A| apply m0_RP1_B]. Qed.

Corollary m0_post_RP1 v r : RP1 (m0_post resv v r) (d0 r).
Proof. exists None. apply m0_RP1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac kill H := rewrite (follow_rejects _ _ H) in *; discriminate.

Theorem m0_follow ans st res :
  follow (M0c resv) ans = Some (st, res) -> res <> None ->
  exists v r, st = m0_pre resv v r /\ res = Some (m0, 0) /\ is_err r = false
    /\ mmap_answer_ok (live_ranges (m0_st7 resv v)) 69632 r = true.
Proof.
  intros Hf Hres.
  destruct ans as [|cur ans1]; [rewrite (M0c_eq resv) in Hf; cbn in Hf; discriminate|].
  change (M0c resv) with (tsubs (M0c resv) (@nil Z)) in Hf at 1.
  rewrite (follow_step (M0c resv) [] _ _ cur ans1 (M0c_eq resv) I) in Hf. cbn [app] in Hf.
  destruct (brk0_answer_ok cur) eqn:V0; [| kill (M0c_1_bad resv cur V0)].
  destruct ans1 as [|a ans2]; [rewrite (follow_stop (M0c resv) [cur] _ _ (M0c_1 resv cur V0)) in Hf; discriminate|].
  rewrite (follow_step (M0c resv) [cur] _ _ a ans2 (M0c_1 resv cur V0) I) in Hf. cbn [app] in Hf.
  destruct (brk_answer_ok cur (round_up_pg cur + 2 * PGSZ) a) eqn:V1; [| kill (M0c_2_bad resv cur a V0 V1)].
  pose proof (brk0_ok_facts cur V0) as (C1 & C2 & C3).
  assert (CASE : a = round_up_pg cur + 2 * PGSZ \/ a = cur).
  { unfold brk_answer_ok in V1. apply orb_true_iff in V1 as [V1|V1]; apply Z.eqb_eq in V1; auto. }
  destruct CASE as [-> | ->].
  - (* [comment removed for export] *)
    destruct (brk_pages_ok (m0_st1 resv) (round_up_pg cur) (2 * PGSZ)) eqn:V2; [| kill (M0c_2A_bad resv cur V0 V2)].
    destruct ans2 as [|rg ans3]; [rewrite (follow_stop (M0c resv) _ _ _ (M0c_2A resv cur V0 V2)) in Hf; discriminate|].
    rewrite (follow_step (M0c resv) _ _ _ rg ans3 (M0c_2A resv cur V0 V2) I) in Hf. cbn [app] in Hf.
    destruct (mmap_fixed_answer_ok (round_up_pg cur) rg) eqn:V3; [| kill (M0c_3A_bad resv cur rg V0 V2 V3)].
    destruct ans3 as [|r ans4]; [rewrite (follow_stop (M0c resv) _ _ _ (M0c_3A resv cur rg V0 V2 V3)) in Hf; discriminate|].
    rewrite (follow_step (M0c resv) _ _ _ r ans4 (M0c_3A resv cur rg V0 V2 V3) I) in Hf. cbn [app] in Hf.
    assert (E4 : tsubs (M0c resv) [cur; round_up_pg cur + 2 * PGSZ; rg; r] = ag_kmm lay_none 44 (as_k2 44 (msc_k 44 mc_k (mc_bail (cs0 resv))) (mc_bail (cs0 resv))) (mc_bail (cs0 resv)) (m0_st7 resv (VA cur)) m0 1 69632 r).
    { change (tsubs (M0c resv) [cur; round_up_pg cur + 2 * PGSZ; rg; r]) with (tsub (tsubs (M0c resv) [cur; round_up_pg cur + 2 * PGSZ; rg]) r). rewrite (M0c_3A resv cur rg V0 V2 V3). reflexivity. }
    rewrite E4 in Hf.
    destruct (mmap_answer_ok (live_ranges (m0_st7 resv (VA cur))) 69632 r) eqn:V4; [| kill (ag_kmm_m0_bad resv (VA cur) r V4)].
    destruct (is_err r) eqn:V5.
    + rewrite (ag_kmm_m0_err resv (VA cur) r V4 V5), follow_ret in Hf. apply some_pair_inj in Hf as [_ <-]. exfalso; apply Hres; reflexivity.
    + rewrite (ag_kmm_m0_ok resv (VA cur) r V4 V5), follow_ret in Hf. apply some_pair_inj in Hf as [<- <-]. exists (VA cur), r. repeat split; assumption.
  - (* [comment removed for export] *)
    destruct ans2 as [|am ans3]; [rewrite (follow_stop (M0c resv) _ _ _ (M0c_2B resv cur V0)) in Hf; discriminate|].
    rewrite (follow_step (M0c resv) _ _ _ am ans3 (M0c_2B resv cur V0) I) in Hf. cbn [app] in Hf.
    destruct (mmap_answer_ok (resv ++ []) 8192 am) eqn:V3; [| kill (M0c_3B_bad resv cur am V0 V3)].
    destruct (is_err am) eqn:V3e.
    { rewrite (follow_end (M0c resv) _ _ ans3 (M0c_3B_err resv cur am V0 V3 V3e)) in Hf. apply some_pair_inj in Hf as [_ <-]. exfalso; apply Hres; reflexivity. }
    destruct ans3 as [|mp ans4]; [rewrite (follow_stop (M0c resv) _ _ _ (M0c_3B resv cur am V0 V3 V3e)) in Hf; discriminate|].
    rewrite (follow_step (M0c resv) _ _ _ mp ans4 (M0c_3B resv cur am V0 V3 V3e) I) in Hf. cbn [app] in Hf.
    destruct (mprotect_answer_ok mp) eqn:V4; [| kill (M0c_4B_bad resv cur am mp V0 V3 V3e V4)].
    destruct (Z.eq_dec mp 0) as [E0|N0]; [| destruct (Z.eq_dec mp (TWO64 - ENOSYS)) as [E1|N1]].
    3:{ rewrite (follow_end (M0c resv) _ _ ans4 (M0c_4B_fail resv cur am mp V0 V3 V3e V4 N0 N1)) in Hf. apply some_pair_inj in Hf as [_ <-]. exfalso; apply Hres; reflexivity. }
    1: pose proof (M0c_4B resv cur am mp V0 V3 V3e V4 (or_introl E0)) as H4.
    2: pose proof (M0c_4B resv cur am mp V0 V3 V3e V4 (or_intror E1)) as H4.
    all: destruct ans4 as [|r ans5]; [rewrite (follow_stop (M0c resv) _ _ _ H4) in Hf; discriminate|].
    all: rewrite (follow_step (M0c resv) _ _ _ r ans5 H4 I) in Hf; cbn [app] in Hf.
    all: assert (E5 : tsubs (M0c resv) [cur; cur; am; mp; r] = ag_kmm lay_none 44 (as_k2 44 (msc_k 44 mc_k (mc_bail (cs0 resv))) (mc_bail (cs0 resv))) (mc_bail (cs0 resv)) (m0_st7 resv (VB am)) m0 1 69632 r)
      by (change (tsubs (M0c resv) [cur; cur; am; mp; r]) with (tsub (tsubs (M0c resv) [cur; cur; am; mp]) r); rewrite H4; reflexivity).
    all: rewrite E5 in Hf.
    all: destruct (mmap_answer_ok (live_ranges (m0_st7 resv (VB am))) 69632 r) eqn:V6; [| kill (ag_kmm_m0_bad resv (VB am) r V6)].
    all: destruct (is_err r) eqn:V7;
      [rewrite (ag_kmm_m0_err resv (VB am) r V6 V7), follow_ret in Hf; apply some_pair_inj in Hf as [_ <-]; exfalso; apply Hres; reflexivity|].
    all: rewrite (ag_kmm_m0_ok resv (VB am) r V6 V7), follow_ret in Hf; apply some_pair_inj in Hf as [<- <-]; exists (VB am), r; repeat split; assumption.
Qed.

Theorem m0_intro_gen ans cs' c :
  follow (cmalloc (cs0 resv) 65536) ans = Some (cs', Some c) ->
  exists v r, cs' = m0_post resv v r /\ c = (1%N, 16) /\ is_err r = false /\ RP1 cs' (d0 r).
Proof.
  intros Hf. rewrite follow_cmalloc in Hf. change (malloc_core lay_none (cs0 resv) 65536) with (M0c resv) in Hf.
  destruct (follow (M0c resv) ans) as [[st res]|] eqn:HT; [| discriminate]. cbn in Hf.
  destruct res as [[g idx]|]; apply some_pair_inj in Hf as [E1 E2]; [| discriminate].
  destruct (m0_follow ans st _ HT ltac:(discriminate)) as (v & r & Est & E & He & Hv).
  apply some_pair_inj in E as [-> ->]. subst st. apply some_inj in E2. subst c. subst cs'.
  exists v, r. split; [reflexivity|]. split; [apply slot_of_m0_pre|]. split; [exact He|].
  apply m0_post_RP1.
Qed.
End M0RP.

Theorem m0_intro_ok : m0_intro_stmt.
Proof. intros resv ans cs' c Hf. exact (m0_intro_gen resv ans cs' c Hf). Qed.


End CeilWrap.
End MEX_m0rp.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WSlot2.
Module MEX_small.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface MEX_big.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MQ (st : mstate) (PM : list aptr) : Prop :=
  exists p, c_avail_meta (ctx st) = Some p /\ fst p = 0%N /\ 0 <= snd p
    /\ (forall m, In m PM -> fst m = 0%N /\ snd m < snd p)
    /\ (c_free_meta_head (ctx st) = None
        \/ exists fr, c_free_meta_head (ctx st) = Some fr /\ m_next (get_meta_rec st fr) = Some fr
                      /\ fst fr = 0%N /\ snd fr < snd p /\ ~ In fr PM).

Lemma MQ_am_ok st PM : MQ st PM -> 1 <= c_avail_meta_count (ctx st) -> am_ok st.
Proof.
  intros (p & Hp & _ & _ & _ & FL) Hc. unfold am_ok. destruct FL as [FL|(fr & FL & _)]; [right| left; rewrite FL; discriminate].
  split; [lia| rewrite Hp; discriminate].
Qed.

(* [comment removed for export] *)
Lemma am_post_MQ st PM :
  MQ st PM ->
  let '(st3, g) := am_post st in
  ~ In g PM /\ fst g = 0%N /\ MQ st3 (g :: PM)
  /\ c_avail_meta_count (ctx st) - 1 <= c_avail_meta_count (ctx st3)
  /\ c_free_meta_head (ctx st3) = None
  /\ (forall x, get_meta_rec st3 x = if aptr_eqb x g then m_set_prev None (m_set_next None (get_meta_rec st g)) else get_meta_rec st x)
  /\ s_regions st3 = s_regions st /\ s_reserved st3 = s_reserved st /\ c_active (s_ctx st3) = c_active (s_ctx st)
  /\ s_next_rid st3 = s_next_rid st /\ s_slots st3 = s_slots st /\ s_groups st3 = s_groups st.
Proof.
  intros (p & Hp & Hp0 & Hp1 & HPM & FL).
  assert (Hself : forall f, c_free_meta_head (ctx st) = Some f -> m_next (get_meta_rec st f) = Some f).
  { intros f Hf. destruct FL as [FL|(fr & FL & NX & _)]; [rewrite FL in Hf; discriminate|]. rewrite FL in Hf. injection Hf. intros <-. exact NX. }
  pose proof (am_post_facts st (c_free_meta_head (ctx st)) p eq_refl Hp Hself) as AF.
  destruct (am_post st) as [st3 g]. destruct AF as (A1 & A2 & A3 & A4 & A5 & AM & A7 & A8 & A9 & A10 & A11 & A12).
  unfold ctx. rewrite A11.
  destruct A12 as [(Hf & AV & AC)|(Hf & -> & AV & AC)].
  - destruct FL as [FL|(fr & FL & NX & F0 & Fs & NI)]; [rewrite FL in Hf; discriminate|]. rewrite FL in Hf. injection Hf. intros ->.
    split; [exact NI|]. split; [exact F0|]. split.
    { exists p. unfold ctx. rewrite AV, A11. split; [reflexivity|]. split; [exact Hp0|]. split; [exact Hp1|]. split; [| left; reflexivity].
      intros m [<-|Hm]; [auto| apply HPM; exact Hm]. }
    rewrite AC. unfold ctx. repeat split; auto; lia.
  - split. { intros Hin. destruct (HPM p Hin). lia. } split; [exact Hp0|]. split.
    { exists (aadd p META_SIZE). unfold ctx. rewrite AV, A11. unfold aadd, META_SIZE. cbn. split; [reflexivity|]. split; [exact Hp0|]. split; [lia|]. split; [| left; reflexivity].
      intros m [<-|Hm]; [split; [exact Hp0| lia]|]. destruct (HPM m Hm). split; [assumption| lia]. }
    rewrite AC. unfold ctx. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seqb_frame sc st :
  let st' := step_seq (account_bounce sc st) in
  (forall x, get_meta_rec st' x = get_meta_rec st x) /\ (forall j, active st' j = active st j)
  /\ s_regions st' = s_regions st /\ s_reserved st' = s_reserved st /\ live_ranges st' = live_ranges st
  /\ c_avail_meta (ctx st') = c_avail_meta (ctx st) /\ c_avail_meta_count (ctx st') = c_avail_meta_count (ctx st)
  /\ c_free_meta_head (ctx st') = c_free_meta_head (ctx st)
  /\ s_next_rid st' = s_next_rid st /\ s_slots st' = s_slots st /\ s_groups st' = s_groups st.
Proof.
  cbn zeta. pose proof (step_seq_eq (account_bounce sc st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold active, ctx, live_ranges. rewrite A1, A3, A4, A5, A6, A7, A8, A9, A10. autorewrite with mst.
  repeat split; try reflexivity. intros x. apply get_meta_rec_ext. rewrite A2. autorewrite with mst. reflexivity.
Qed.

Lemma MQ_frame st st' PM :
  (forall x, get_meta_rec st' x = get_meta_rec st x) ->
  c_avail_meta (ctx st') = c_avail_meta (ctx st) -> c_free_meta_head (ctx st') = c_free_meta_head (ctx st) ->
  MQ st PM -> MQ st' PM.
Proof.
  intros M A F (p & Hp & H0 & H1 & HPM & FL). exists p. rewrite A, F. split; [exact Hp|]. split; [exact H0|]. split; [exact H1|]. split; [exact HPM|].
  destruct FL as [FL|(fr & FL & NX & R)]; [left; exact FL| right]. exists fr. rewrite M. auto.
Qed.

(* [comment removed for export] *)
Lemma upd_meta_metas m f st : s_metas (upd_meta m f st) = <[m := f (get_meta_rec st m)]> (s_metas st).
Proof. reflexivity. Qed.

Lemma ag_mm_post_frame sc m c3 n3 st1 r :
  let st' := ag_mm_post lay_none sc m c3 n3 st1 r in
  (exists F, (forall r0, m_next (F r0) = m_next r0 /\ m_prev (F r0) = m_prev r0)
             /\ forall x, get_meta_rec st' x = if aptr_eqb x m then F (get_meta_rec st1 m) else get_meta_rec st1 x)
  /\ (forall j, active st' j = active st1 j).
Proof.
  cbn zeta. unfold ag_mm_post. cbn [new_region fst snd]. unfold ag_tail_post. cbn [lh_hdr lay_none].
  set (ai := if (if c3 - 1 <? _ then _ else _) <? 0 then 0 else _). clearbody ai.
  split.
  - exists (fun r0 => m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (c3 - 1) (m_set_mem (Some (s_next_rid st1, 0))
              (m_set_freed (mask_upto (c3 - 1) - mask_upto ai) (m_set_avail (mask_upto ai) (m_set_maplen (Z.shiftr n3 12) r0))))))).
    split; [intros r0; destruct r0; split; reflexivity|].
    intros x. unfold get_meta_rec, set_usage. rewrite !s_metas_add_slots, !s_metas_put_group, !upd_meta_metas, !s_metas_upd_ctx, !upd_meta_metas, !s_metas_set_next_rid, !s_metas_set_regions.
    destruct (aptr_eqb_spec x m) as [->|NE].
    + rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_meta_rec. rewrite !s_metas_upd_ctx, upd_meta_metas, lookup_insert_eq. cbn [default from_option id].
      unfold get_meta_rec. rewrite s_metas_set_next_rid, s_metas_set_regions. reflexivity.
    + rewrite !lookup_insert_ne by congruence. reflexivity.
  - intros j. unfold active, ctx, set_usage. autorewrite with mst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ag_nest_post_frame sc m p cnt stX :
  let st' := ag_tail_post lay_none (upd_meta m (m_set_maplen 0) stX) sc m p cnt (cnt - 1) in
  (exists F, (forall r0, m_next (F r0) = m_next r0 /\ m_prev (F r0) = m_prev r0)
             /\ forall x, get_meta_rec st' x = if aptr_eqb x m then F (get_meta_rec stX m) else get_meta_rec stX x)
  /\ (forall j, active st' j = active stX j).
Proof.
  cbn zeta. unfold ag_tail_post. cbn [lh_hdr lay_none].
  split.
  - exists (fun r0 => m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1) (m_set_mem (Some p)
              (m_set_freed (mask_upto (cnt - 1) - mask_upto (cnt - 1)) (m_set_avail (mask_upto (cnt - 1)) (m_set_maplen 0 r0))))))).
    split; [intros r0; destruct r0; split; reflexivity|].
    intros x. unfold get_meta_rec, set_usage. rewrite !s_metas_add_slots, !s_metas_put_group, !upd_meta_metas, !s_metas_upd_ctx, !upd_meta_metas.
    destruct (aptr_eqb_spec x m) as [->|NE].
    + rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_meta_rec. rewrite !s_metas_upd_ctx, upd_meta_metas, lookup_insert_eq. cbn [default from_option id]. reflexivity.
    + rewrite !lookup_insert_ne by congruence. reflexivity.
  - intros j. unfold active, ctx, set_usage. autorewrite with mst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma as_k2_post_frame j mj st :
  active st j = None ->
  let st' := as_k2_post j mj st in
  (forall x, x <> mj -> get_meta_rec st' x = get_meta_rec st x)
  /\ (forall x, active st' x = if x =? j then Some mj else active st x).
Proof.
  intros HA. cbn zeta. unfold as_k2_post, q_post. cbn [get_head]. rewrite active_upd_meta, HA. cbn [set_head].
  split.
  - intros x NE. unfold set_active. rewrite get_meta_rec_upd_ctx, !get_meta_rec_upd_other by exact NE. reflexivity.
  - intros x. rewrite active_set_active, !active_upd_meta. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AGQ.
Context {R : Type}.

(* [comment removed for export] *)
Definition AGPOST (st st' : mstate) (m : aptr) (PM : list aptr) (sc : Z) : Prop :=
  ~ In m PM /\ (forall x, In x PM -> get_meta_rec st' x = get_meta_rec st x)
  /\ m_next (get_meta_rec st' m) = None /\ m_prev (get_meta_rec st' m) = None
  /\ (forall x, x <= sc -> active st' x = active st x).

Definition AGSPEC (T : M R) (st : mstate) (sc : Z) (k : mstate -> optr -> M R) (PM : list aptr) : Prop :=
  exists len KK,
    T = SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) KK
    /\ 4096 <= len <= 2 ^ 20 /\ len mod 4096 = 0
    /\ (forall r, mmap_answer_ok (live_ranges st) len r = false -> rejects (KK r))
    /\ (forall r, mmap_answer_ok (live_ranges st) len r = true -> is_err r = true -> exists st', KK r = k st' None)
    /\ (forall r, mmap_answer_ok (live_ranges st) len r = true -> is_err r = false ->
          exists st' m, KK r = k st' (Some m) /\ AGPOST st st' m PM sc).

(* [comment removed for export] *)
Definition RECOK (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R)
           (st : mstate) (sc : Z) (k : mstate -> optr -> M R) (bail : M R) (PM : list aptr) : Prop :=
  forall st3 g c1 j n',
    sc < j <= 23 -> 0 <= n' -> n' + IB <= UNIT * size_class j ->
    MQ st3 (g :: PM) -> 48 - j <= c_avail_meta_count (ctx st3) ->
    ~ In g PM -> (forall x, In x PM -> get_meta_rec st3 x = get_meta_rec st x) ->
    m_next (get_meta_rec st3 g) = None -> m_prev (get_meta_rec st3 g) = None ->
    live_ranges st3 = live_ranges st -> (forall x, active st3 x = active st x) ->
    AGSPEC (rec st3 j n' (ag_knest lay_none sc k bail g c1 j) bail) st sc k PM.

Lemma AG_level rec st sc req (k : mstate -> optr -> M R) bail PM :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall j, sc < j <= 23 -> active st j = None) ->
  MQ st PM -> 48 - sc <= c_avail_meta_count (ctx st) ->
  RECOK rec st sc k bail PM ->
  AGSPEC (alloc_group R lay_none rec st sc req k bail) st sc k PM.
Proof.
  intros Hsc Hreq Hfit QA MQ0 CNT REC.
  rewrite alloc_group_eq.
  pose proof (am_post_MQ st PM MQ0) as AMQ.
  rewrite (alloc_meta_silent st _ bail (MQ_am_ok st PM MQ0 ltac:(lia))).
  destruct (am_post st) as [st3 g] eqn:EAP. cbn [fst snd].
  destruct AMQ as (NIg & G0 & MQ3 & CNT3 & FH3 & AM3 & R3 & RS3 & ACT3 & NR3 & SL3 & GR3).
  assert (LR3 : live_ranges st3 = live_ranges st) by (unfold live_ranges; rewrite R3, RS3; reflexivity).
  assert (ACT3' : forall x, active st3 x = active st x) by (intros x; unfold active, ctx; rewrite ACT3; reflexivity).
  assert (MG : m_next (get_meta_rec st3 g) = None /\ m_prev (get_meta_rec st3 g) = None).
  { rewrite AM3, aptr_eqb_refl. destruct (get_meta_rec st g); split; reflexivity. }
  destruct MG as [MGn MGp].
  assert (PMK : forall x, In x PM -> get_meta_rec st3 x = get_meta_rec st x).
  { intros x Hx. rewrite AM3. destruct (aptr_eqb_spec x g) as [->|]; [exfalso; exact (NIg Hx)| reflexivity]. }
  unfold ag_k. cbv beta iota. cbv zeta.
  pose proof (ag_arith sc req (usage st3 sc)) as AR.
  set (c1 := ag_cnt1 sc (usage st3 sc)) in *.
  destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
  - (* [comment removed for export] *)
    set (ns := is_bouncing sc st3) in *. set (st3' := step_seq (account_bounce sc st3)) in *.
    set (u1 := if Z.even sc && (sc <? 32) then usage st3 sc + usage st3' (sc + 1) else usage st3 sc) in *.
    destruct (ag_cn3 sc req (ag_cnt2 sc c1 u1 ns) u1 ns) as [c3 n3] eqn:E3.
    destruct (proj1 (AR u1 ns c3 n3 Hsc Hreq Hfit) HB E3) as [GRP _].
    pose proof (grp_ok_sound sc c3 n3 GRP) as GS. cbn zeta in GS. destruct GS as (_ & Gmod & Gb & _).
    pose proof (seqb_frame sc st3) as SB. cbn zeta in SB. fold st3' in SB. destruct SB as (SBm & SBa & SBr & SBrs & SBl & _).
    exists n3, (ag_kmm lay_none sc k bail st3' g c3 n3).
    split; [reflexivity|]. split; [lia|]. split; [exact Gmod|].
    rewrite <- LR3, <- SBl.
    split; [intros r Hr; apply ag_kmm_bad; exact Hr|].
    split; [intros r Hr He; exists (fm_post g st3'); apply ag_kmm_err; assumption|].
    intros r Hr He. exists (ag_mm_post lay_none sc g c3 n3 st3' r), g. split; [apply ag_kmm_ok; assumption|].
    destruct (ag_mm_post_frame sc g c3 n3 st3' r) as [(F & HF & MF) AF].
    split; [exact NIg|]. split.
    { intros x Hx. rewrite MF. destruct (aptr_eqb_spec x g) as [->|NE]; [exfalso; exact (NIg Hx)|]. rewrite SBm. apply PMK. exact Hx. }
    split; [rewrite MF, aptr_eqb_refl, (proj1 (HF _)), SBm; exact MGn|].
    split; [rewrite MF, aptr_eqb_refl, (proj2 (HF _)), SBm; exact MGp|].
    intros x _. rewrite AF, SBa. apply ACT3'.
  - (* [comment removed for export] *)
    pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST. apply nest_ok_sound in NEST. cbn zeta in NEST. fold c1 in NEST.
    destruct NEST as (Hc1 & Hj & Hfit' & _ & Hn'0 & Hn'1).
    apply REC; try assumption. all: unfold IB in *; lia.
Qed.

Theorem AG_quiet : forall f st sc req (k : mstate -> optr -> M R) bail PM,
  24 - sc <= Z.of_nat f -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall j, sc < j <= 23 -> active st j = None) ->
  MQ st PM -> 48 - sc <= c_avail_meta_count (ctx st) ->
  AGSPEC (alloc_group R lay_none (alloc_slot lay_none f) st sc req k bail) st sc k PM.
Proof.
  induction f as [|f IH]; intros st sc req k bail PM Hf Hsc Hreq Hfit QA MQ0 CNT.
  - apply AG_level; try assumption. intros st3 g c1 j n' Hj. exfalso. cbn in Hf. lia.
  - apply AG_level; try assumption. intros st3 g c1 j n' Hj Hn'0 Hn'1 MQ3 CNT3 NIg PMK MGn MGp LR3 ACT3.
    rewrite alloc_slot_S, (try_avail_none j st3) by (rewrite ACT3; apply QA; lia). rewrite as_k1_zero.
    assert (IHj : AGSPEC (alloc_group R lay_none (alloc_slot lay_none f) st3 j n' (as_k2 j (ag_knest lay_none sc k bail g c1 j) bail) bail)
                         st3 j (as_k2 j (ag_knest lay_none sc k bail g c1 j) bail) (g :: PM)).
    { apply IH; try assumption; try lia. intros x Hx. rewrite ACT3. apply QA. lia. }
    destruct IHj as (len & KK & EQ & Hlen & Hmod & Hbad & Herr & Hok).
    exists len, KK. split; [exact EQ|]. split; [exact Hlen|]. split; [exact Hmod|]. rewrite <- LR3.
    split; [exact Hbad|]. split.
    { intros r Hr He. destruct (Herr r Hr He) as (st' & E). exists (fm_post g st'). rewrite E, as_k2_none. unfold ag_knest. cbn [Z.ltb]. change (-1 <? 0) with true. cbv iota. apply free_meta_eq. }
    intros r Hr He. destruct (Hok r Hr He) as (st' & mj & E & (NImj & PMK' & MJn & MJp & ACT')).
    rewrite E. rewrite (as_k2_some j _ bail st' mj MJn MJp).
    assert (Aj : active st' j = None) by (rewrite ACT' by lia; rewrite ACT3; apply QA; lia).
    destruct (as_k2_post_frame j mj st' Aj) as [QM QAc].
    unfold ag_knest. change (0 <? 0) with false. cbv iota. rewrite (QAc j), Z.eqb_refl. cbn [lh_nest lay_none].
    rewrite ag_tail_eq. eexists _, g. split; [reflexivity|].
    destruct (ag_nest_post_frame sc g (slot_of (as_k2_post j mj st') mj 0) c1 (as_k2_post j mj st')) as [(F & HF & MF) AF].
    assert (Gmj : g <> mj) by (intros ->; apply NImj; left; reflexivity).
    split; [exact NIg|]. split.
    { intros x Hx. rewrite MF. destruct (aptr_eqb_spec x g) as [->|NE]; [exfalso; exact (NIg Hx)|].
      rewrite QM by (intros ->; apply NImj; right; exact Hx). rewrite PMK' by (right; exact Hx). apply PMK. exact Hx. }
    split; [rewrite MF, aptr_eqb_refl, (proj1 (HF _)), QM by exact Gmj; rewrite PMK' by (left; reflexivity); exact MGn|].
    split; [rewrite MF, aptr_eqb_refl, (proj2 (HF _)), QM by exact Gmj; rewrite PMK' by (left; reflexivity); exact MGp|].
    intros x Hx. rewrite AF, QAc. replace (x =? j) with false by (symmetry; apply Z.eqb_neq; lia). rewrite ACT' by lia. apply ACT3.
Qed.
End AGQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msc_sc_ok st n : 0 <= n < MMAP_THRESHOLD -> 0 <= msc_sc st n < 48 /\ n + IB <= UNIT * size_class (msc_sc st n).
Proof.
  intros Hn. pose proof (size_to_class_ok n Hn) as [SC FIT]. unfold msc_sc.
  set (sc0 := size_to_class n) in *. destruct (active st sc0); [auto|].
  destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [|auto].
  match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [|auto].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
  pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia.
Qed.

Section SMALL.
Variables (cs : mstate) (D : list dblk) (fl : optr) (lo n : Z).
Hypothesis HRP : RP cs D fl lo.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Let sc := msc_sc cs n.
Let bail := mc_bail cs.
Let K := msc_k sc mc_k bail.
(* [comment removed for export] *)
Let st0 := match active cs sc with Some m => dequeue (LActive sc) m cs | None => cs end.

Lemma small_ov : size_overflows n = false.
Proof. unfold size_overflows. apply Z.leb_gt. unfold MMAP_THRESHOLD in Hn. lia. Qed.

Lemma st0_facts :
  malloc_core lay_none cs n = alloc_group _ lay_none (alloc_slot lay_none 63) st0 sc n (as_k2 sc K bail) bail
  /\ active st0 sc = None
  /\ (forall j, j <> sc -> active st0 j = active cs j)
  /\ (forall x, ~ In x (map db_meta D) -> get_meta_rec st0 x = get_meta_rec cs x)
  /\ live_ranges st0 = live_ranges cs
  /\ c_avail_meta (ctx st0) = c_avail_meta (ctx cs) /\ c_avail_meta_count (ctx st0) = c_avail_meta_count (ctx cs)
  /\ c_free_meta_head (ctx st0) = c_free_meta_head (ctx cs).
Proof.
  destruct HRP as (HB & HA & HU & HBo & HUs & HP & HR0 & HRex & HRfr & HGfr & HND1 & HND2 & HLen & HSH & HTK).
  rewrite (malloc_core_small lay_none cs n small_ov (proj2 Hn)).
  assert (COND : match active cs sc with Some gp => m_avail (get_meta_rec cs gp) = 0 | None => True end).
  { rewrite (HA sc). destruct (find44 D) as [d|] eqn:F; [| exact I]. destruct (sc =? 44); [| exact I].
    apply find_some in F as [Hin _]. apply (proj1 (List.Forall_forall _ _) HB) in Hin. destruct Hin as (_ & _ & M & _). rewrite M. unfold blk_meta. destruct (db_sc d =? 44); reflexivity. }
  rewrite (malloc_small_ctrl_eq lay_none cs n mc_k bail COND). fold sc. unfold FUEL. rewrite alloc_slot_S.
  unfold st0. pose proof (HA sc) as HAsc. destruct (active cs sc) as [m|] eqn:EA.
  - destruct (find44 D) as [d|] eqn:F; [| discriminate]. destruct (Z.eqb_spec sc 44) as [E44|]; [| discriminate].
    injection HAsc. intros Em. subst m. apply find_some in F as [Hin F44]. apply Z.eqb_eq in F44.
    assert (INm : In (db_meta d) (map db_meta D)) by (apply in_map; exact Hin).
    apply (proj1 (List.Forall_forall _ _) HB) in Hin. destruct Hin as (_ & _ & M & _).
    assert (MM : get_meta_rec cs (db_meta d) = blk_meta (db_meta d) (db_rid d) 44 (db_ml d)) by (rewrite M, F44; reflexivity).
    set (m := db_meta d) in *.
    assert (NX : m_next (get_meta_rec cs m) = Some m) by (rewrite MM; reflexivity).
    rewrite (try_avail_dead sc cs m _ bail EA) by (rewrite MM; reflexivity). rewrite as_k1_zero.
    rewrite (dequeue_self (LActive sc) m cs NX). cbn [set_head].
    split; [reflexivity|]. split; [rewrite active_upd_meta, active_set_active, Z.eqb_refl; reflexivity|].
    split; [intros j NE; rewrite active_upd_meta, active_set_active, (proj2 (Z.eqb_neq _ _) NE); reflexivity|].
    split. { intros x NI. rewrite get_meta_rec_upd_other by (intros ->; exact (NI INm)). unfold set_active. apply get_meta_rec_upd_ctx. }
    unfold live_ranges, ctx, set_active. autorewrite with mst. cbn. repeat split; reflexivity.
  - rewrite (try_avail_none sc cs _ bail EA), as_k1_zero. repeat split; auto.
Qed.

Theorem small_site_gen : small_site cs n.
Proof.
  pose proof st0_facts as (EQ0 & A0 & A1 & M0' & LR0 & AV0 & AC0 & FH0).
  destruct HRP as (HB & HA & HU & HBo & HUs & (p & Hp & Hp0 & Hp1 & Hlo & HDp & (HFL1 & HFL2)) & HR0 & HRex & HRfr & HGfr & HND1 & HND2 & HLen & HSH & HTK).
  pose proof (msc_sc_ok cs n Hn) as [SC FIT]. fold sc in SC, FIT.
  assert (QA : forall j, sc < j <= 23 -> active st0 j = None).
  { intros j Hj. rewrite A1 by lia. rewrite (HA j). destruct (find44 D); [| reflexivity]. replace (j =? 44) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (MQ0 : MQ st0 []).
  { exists p. rewrite AV0, FH0. split; [exact Hp|]. split; [exact Hp0|]. split; [exact Hp1|]. split; [intros m []|].
    destruct fl as [f|]; [right| left; exact HFL1]. exists f. destruct (HFL2 f eq_refl) as (Mf & F0 & Fs & NI).
    split; [exact HFL1|]. rewrite (M0' f NI), Mf. cbn. repeat split; auto. }
  assert (CNT : 48 - sc <= c_avail_meta_count (ctx st0)) by (rewrite AC0; lia).
  destruct (AG_quiet (R := mstate * option (aptr * Z)) 63 st0 sc n (as_k2 sc K bail) bail [] ltac:(cbn; lia) SC (proj1 Hn) FIT QA MQ0 CNT)
    as (len & KK & EQ & Hlen & Hmod & Hbad & Herr & Hok).
  unfold small_site, one_mmap_site.
  exists len, (fun a => sbind (KK a) cm_fin).
  rewrite LR0 in Hbad, Herr, Hok.
  split; [rewrite cmalloc_eq, EQ0, EQ; reflexivity|].
  split; [lia|].
  split; [intros r Hr; apply rejects_sbind; apply Hbad; exact Hr|].
  assert (ERR : forall r, mmap_answer_ok (live_ranges cs) len r = true -> is_err r = true -> exists csf, sbind (KK r) cm_fin = SRet (csf, None)).
  { intros r Hr He. destruct (Herr r Hr He) as (st' & E). rewrite E, as_k2_none. unfold K. rewrite msc_k_neg. eexists. reflexivity. }
  split; [exact ERR|]. split; [apply ERR; [apply ENOMEM_ans_ok| apply ENOMEM_ans_err]|].
  intros r NR He. destruct (mmap_answer_ok (live_ranges cs) len r) eqn:Hr.
  2:{ exfalso. apply NR. apply rejects_sbind. apply Hbad. exact Hr. }
  destruct (Hok r Hr He) as (st' & m & E & (NIm & _ & MJn & MJp & ACT')).
  rewrite E, (as_k2_some sc K bail st' m MJn MJp). unfold K.
  rewrite (msc_k_zero sc mc_k bail _ m) by (apply active_as_k2_post; rewrite (ACT' sc) by lia; exact A0).
  eexists _, _. reflexivity.
Qed.
End SMALL.

Theorem small_site_ok : small_site_stmt.
Proof. intros cs D fl lo n HRP Hn. exact (small_site_gen cs D fl lo n HRP Hn). Qed.


End CeilWrap.
End MEX_small.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap fin_maps list.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Export MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_m0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Export MEX_iface.
Export MEX_big.
Export MEX_m0rp.
Export MEX_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem m0_intro : m0_intro_stmt.
Proof. exact m0_intro_ok. Qed.

Theorem big_site : big_site_stmt.
Proof. exact big_site_ok. Qed.

Theorem small_site : small_site_stmt.
Proof. exact small_site_ok. Qed.

Theorem big_follow : big_follow_stmt.
Proof. exact big_follow_ok. Qed.

Theorem free_site : free_site_stmt.
Proof. exact free_site_ok. Qed.

Theorem free_follow : free_follow_stmt.
Proof. exact free_follow_ok. Qed.

Lemma rp1_RP cs d : RP1 cs d -> exists fl lo, RP cs [d] fl lo.
Proof. intros [fl H]. eexists fl, _. exact H. Qed.

Lemma rp2_RP cs dold dnew : RP2 cs dold dnew -> RP cs [dold; dnew] None 50.
Proof. intros [H _]. exact H. Qed.

(* [comment removed for export] *)
Theorem rp_site cs D fl lo n :
  RP cs D fl lo -> 0 <= n <= 2 ^ 26 ->
  one_mmap_site cs n (if n <? MMAP_THRESHOLD then 4096 else n + 20) (if n <? MMAP_THRESHOLD then 2 ^ 20 else n + 20).
Proof.
  intros HRP Hn. destruct (Z.ltb_spec n MMAP_THRESHOLD).
  - apply (small_site cs D fl lo n HRP). lia.
  - apply (big_site cs D fl lo n HRP). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rp_bounds : rp_bounds_stmt.
Proof.
  intros cs D fl lo HRP.
  destruct HRP as (HB & HA & HU & HBo & HUs & HP & (r0 & Hr0 & Hk0 & Hl0) & HRex & HRfr & HGfr & HND1 & HND2 & HLen & HSH & HTK).
  assert (REG : forall rid r, s_regions cs !! rid = Some r ->
       (rid = 0%N /\ r_len r = 2 * PGSZ /\ r_kind r <> RKGroup)
       \/ (exists d, In d D /\ rid = db_rid d /\ r = mkRegion RKGroup (db_base d) (db_len d))).
  { intros rid r Hr. destruct (HRex rid r Hr) as [->|Hin].
    - left. rewrite Hr0 in Hr. injection Hr. intros <-. auto.
    - right. apply in_map_iff in Hin as (d & <- & Hd). exists d.
      pose proof (proj1 (List.Forall_forall _ _) HB d Hd) as (B1 & _). rewrite B1 in Hr. injection Hr. intros <-. auto. }
  split; [exact REG|]. split.
  { intros d Hd. pose proof (proj1 (List.Forall_forall _ _) HB d Hd) as (_ & _ & _ & B4 & _). exact B4. }
  split; [exact HLen|].
  rewrite <- (length_map_to_list (s_regions cs)).
  rewrite <- (length_fmap fst).
  transitivity (length (0%N :: map db_rid D)); [| cbn; rewrite length_map; lia].
  apply submseteq_length. apply NoDup_submseteq; [apply NoDup_fst_map_to_list|].
  intros rid Hin. apply list_elem_of_fmap in Hin as ([rid' r] & -> & Hin). cbn.
  apply elem_of_map_to_list in Hin. apply list_elem_of_In.
  destruct (HRex rid' r Hin) as [->|Hin']; [left; reflexivity| right; exact Hin'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma blk_conc cs d : blk_ok cs d -> conc cs (db_slot d) = db_base d + 16.
Proof. intros (B1 & _). unfold conc, get_region, db_slot. cbn [fst snd]. rewrite B1. reflexivity. Qed.

Lemma RP_blk_ok cs D fl lo d : RP cs D fl lo -> In d D -> blk_ok cs d.
Proof. intros (HB & _) Hd. exact (proj1 (List.Forall_forall _ _) HB d Hd). Qed.

Lemma RP1_conc cs d : RP1 cs d -> conc cs (db_slot d) = db_base d + 16.
Proof. intros [fl H]. apply blk_conc. eapply RP_blk_ok; [exact H| left; reflexivity]. Qed.

Lemma RP2_conc cs dold dnew : RP2 cs dold dnew ->
  conc cs (db_slot dold) = db_base dold + 16 /\ conc cs (db_slot dnew) = db_base dnew + 16.
Proof.
  intros [H _]. split; apply blk_conc; eapply RP_blk_ok; try exact H; [left; reflexivity| right; left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma live_ranges_cs0 resv : live_ranges (cs0 resv) = resv ++ [].
Proof. reflexivity. Qed.

Lemma live_ranges_m0_st1 resv : live_ranges (m0_st1 resv) = resv ++ [].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m0_post_region resv v r : s_regions (m0_post resv v r) !! 1%N = Some (mkRegion RKGroup r 69632).
Proof. destruct v; reflexivity. Qed.

Lemma m0_post_conc resv v r : conc (m0_post resv v r) (1%N, 16) = r + 16.
Proof. destruct v; reflexivity. Qed.


End CeilWrap.
