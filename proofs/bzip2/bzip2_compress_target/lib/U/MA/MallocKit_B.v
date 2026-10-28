(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep Arr SFMisc.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


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
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
  forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. intros P lo hi a []. Qed.

Lemma ivs_avoid_cons : forall lo hi W P,
  (forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
  intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
  - inversion E; subst. apply H1. exact Ha.
  - eapply H2; eauto.
Qed.

Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
  - intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
  - apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

(* [comment removed for export] *)
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma munch_agree : forall W m m' P A n,
  munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
  agree_on m m' A n.
Proof.
  intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : forall st g mr g',
  get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.

Lemma mrep_put_meta_frame : forall st m m' g mr',
  mrep st m -> meta_slot st g ->
  munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (conc st g) (meta_cells st mr') ->
  mrep (put_meta g mr' st) m'.
Proof.
  (intros st m m' g mr' MR; cps_intros (a & ar & k & Ha & Hk & Eg); intros MU WM CH).
  cps_pose MR as (WF & CX & GL & AR & GR & SH).
  cps_destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). bz_ceil.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  cps_pose WF as (Hres & WR & DJ & WA & WG).
  cps_destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (reserved_disjoint _ _ RFa) as [_ DRa].
  pose proof (round_up_pg_ge (r_len ra)) as RU.
  (* [comment removed for export] *)
  assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
  assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  assert (TC : forall A cs, rw_cells asegs m A cs ->
            (A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells asegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply mrep_ctx_ext; [reflexivity|exact Hconc|].
    cps_destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold mrep_ctx. unfold CTX in *.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | cbn; lia].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
    + apply TC; [exact C6 | cbn; lia].
  - cps_destruct GL as (G1 & G2 & G3). unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A in *.
    split; [|split]; (apply TC; [assumption | cbn; lia]).
  - intros a' ar' Ha'. cbn in Ha'.
    cps_destruct (area_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    destruct (decide (a' = a)) as [->|NEa].
    + rewrite Ha in Ha'. inversion Ha'; subst ar'.
      cps_destruct (AR a ar Ha) as (HD & SL & PD). unfold area_rep. rewrite !Hconc, Hpw.
      split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k' Hk'. rewrite Hmc, get_meta_rec_put.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
      * apply TC; [exact PD| cbn; lia].
    + assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
      { rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
        - pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (area_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
        - rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
      eapply area_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
        replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
      cps_destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
      * apply TC; [exact PD| cbn; lia].
  - intros b gh Hb. cbn in Hb. eapply group_rep_ext; [exact Hconc|].
    cps_destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    cps_destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
    destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply shadow_rep_ext; [reflexivity|].
    destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [|exact I].
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
    rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. (intros st st' g E; cps_intros (a & ar & k & Ha & Hk & Eg)). exists a, ar, k. rewrite E. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
  intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
  intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
  nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
  intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
  nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
  intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma actives_length st : length (actives st) = 48%nat.
Proof. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
Lemma usages_length st : length (usages st) = 48%nat.
Proof. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

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


Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.

Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
  intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
  destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p. Proof. reflexivity. Qed.
Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p. Proof. reflexivity. Qed.
Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st. Proof. reflexivity. Qed.
Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => fm_link st0 g head
  | None => fm_single st0 h g
  end.

Lemma queue_eq : forall R h g st0 (k : mstate -> M R) bail,
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold queue_st, fm_link, fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
  intros. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition free_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  (lo <= a < sp
   \/ CTX <= a < CTX + 928
   \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma outside_of_cover : forall (C : Z -> Prop) W a,
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
  - intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
  - apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
  end.

Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
  destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
  intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn in Hx |- *. tauto.
Qed.
End ACeilS1.


Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)


Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : mrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.

(* [comment removed for export] *)

(* [comment removed for export] *)
End CTXFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
End ACeilS2.


Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
(* [comment removed for export] *)
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

(* [comment removed for export] *)
Lemma le4_lor_sxv : forall f s, 0 <= f < 2^32 -> 0 <= s < 2^32 ->
  le4 (Z_to_bv 64 (Z.lor (sxv s) (sxv f))) = le4 (wz (Z.lor f s)).
Proof.
  intros f s Hf Hs. apply le4_congr. pose proof (lor_range64 (sxv s) (sxv f) (sxv_range _) (sxv_range _)).
  pose proof (Z_lor_range f s ltac:(lia) ltac:(lia)).
  rewrite unsigned_lit by lia. rewrite wz_unsigned.
  2:{ split; [lia|]. apply (Z.lt_le_trans _ (2^32)); [|lia]. apply Z_bounded_by_bits; [lia|lia|].
      intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity. }
  rewrite lor_sxv_mod32 by lia. rewrite Z.lor_comm. symmetry. apply Z.mod_small.
  split; [lia|]. apply Z_bounded_by_bits; [lia|lia|].
  intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


End ACeilS3.
