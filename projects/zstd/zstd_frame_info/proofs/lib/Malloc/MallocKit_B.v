(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition repfoot (st : mstate) (a : Z) : Prop :=
  (CTX <= a < CTX + 928) \/ (MLOCK <= a < MLOCK + 4) \/ (NEED_LOCKS <= a < NEED_LOCKS + 1) \/ (PAGE_SIZE_A <= a < PAGE_SIZE_A + 8)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma repfoot_ctx st a : CTX <= a < CTX + 928 -> repfoot st a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma repfoot_mlock st a : MLOCK <= a < MLOCK + 4 -> repfoot st a. Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_nl st a : NEED_LOCKS <= a < NEED_LOCKS + 1 -> repfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_pgsz st a : PAGE_SIZE_A <= a < PAGE_SIZE_A + 8 -> repfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> repfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma repfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> repfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma repfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> repfoot st a.
Proof. intros; do 6 right. exists rid, r, v. auto. Qed.

(* [comment removed for export] *)
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
  forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

#[using="Type"] Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. intros P lo hi a []. Qed.

#[using="Type"] Lemma ivs_avoid_cons : forall lo hi W P,
  (forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
  intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
  - inversion E; subst. apply H1. exact Ha.
  - eapply H2; eauto.
Qed.

#[using="Type"] Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
  - intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
  - apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

(* [comment removed for export] *)
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

#[using="Type"] Lemma munch_agree : forall W m m' P A n,
  munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
  agree_on m m' A n.
Proof.
  intros W m m' P A n MU HW HP HA HB a Ha. apply MU. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56765667309.1400000:S2HA2HB2Ha".
rewrite wa_unsigned by lia.
  eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma get_meta_rec_put : forall st g mr g',
  get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

#[using="Type"] Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
  intros X f n. Local Ltac2 Set LiaHints.tbl := fun () => "0040=16108255286.725362592459.653768766698.868029264571.800000400800<00@S2HiS2HiS2HiS2Hi".
induction n as [|n IH]; intros s i Hi; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
  intros st sc H. unfold actives. Local Ltac2 Set LiaHints.tbl := fun () => "0020=26013967764.443018341876.4000003006S1HS1H".
rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc H. unfold usages. Local Ltac2 Set LiaHints.tbl := fun () => "0020=26013967764.443018341876.4000003006S1HS1H".
rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
  nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
  intros st i H. unfold bouncess. Local Ltac2 Set LiaHints.tbl := fun () => "0020=2124284962.4 61871601826.4000003006S1HS1H".
rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
  nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
  intros st i H. unfold unmap_seqs. Local Ltac2 Set LiaHints.tbl := fun () => "0020=2124284962.4 61871601826.4000003006S1HS1H".
rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma actives_length st : length (actives st) = 48%nat.
Proof. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma usages_length st : length (usages st) = 48%nat.
Proof. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.

#[using="Type"] Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
  intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
  destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

#[using="Type"] Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

#[using="Type"] Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

#[using="Type"] Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p. Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p. Proof. reflexivity. Qed.
#[using="Type"] Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
#[using="Type"] Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r. Proof. reflexivity. Qed.

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

#[using="Type"] Lemma queue_eq : forall R h g st0 (k : mstate -> M R) bail,
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold queue_st, fm_link, fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

#[using="Type"] Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
  intros. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

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

#[using="Type"] Lemma free_fp_stack st lo sp a : lo <= a < sp -> free_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
#[using="Type"] Lemma free_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> free_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma free_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> free_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma free_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> free_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_fp_mono : forall st st' lo sp sp' a,
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
  (forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
  sp' <= sp ->
  free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
  intros st st' lo sp sp' a ER ES HG HS H.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  destruct H as [H|[H|H]].
  - left. Local Ltac2 Set LiaHints.tbl := fun () => "0010>12574408705.13000006S2HS1H".
destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
    right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
  - right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
    rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma outside_of_cover : forall (C : Z -> Prop) W a,
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
  - intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
  - apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.

(* [comment removed for export] *)
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
  end.

#[using="Type"] Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
  destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
  intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn in Hx |- *. tauto.
Qed.

End CANSEC1.
Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CANSEC2. Context {rc : runConstT}.
Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MU : munch W m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.

#[using="MU WIN"] Lemma ctxW_avoid : forall A n, (A + n <= CTX \/ CTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
  0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
  intros A n HD HA HB a Ha. apply MU. Local Ltac2 Set LiaHints.tbl := fun () => "0020>53507296417.1256765667309.2100000900CS2HD2Ha1HS2HA2HB2Ha".
rewrite wa_unsigned by lia.
  clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - destruct HD as [HD|HD].
    + pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
    + pose proof (HD lo hi ltac:(left; reflexivity)). lia.
  - apply IH.
    + intros lo' hi' Hin. apply WIN. right; exact Hin.
    + destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CTXFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
#[using="Type"] Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. Local Ltac2 Set LiaHints.tbl := fun () => "0010=56765665761.4000004S2Ha".
rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC2.
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
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
#[using="Type"] Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma le4_lor_sxv : forall f s, 0 <= f < 2^32 -> 0 <= s < 2^32 ->
  le4 (Z_to_bv 64 (Z.lor (sxv s) (sxv f))) = le4 (wz (Z.lor f s)).
Proof.
  intros f s Hf Hs. apply le4_congr. pose proof (lor_range64 (sxv s) (sxv f) (sxv_range _) (sxv_range _)).
  Local Ltac2 Set LiaHints.tbl := fun () => "00<0=10364763902.915196228076.718621106750.625729666054.725729671899.925923953424.736112118186.644015161774.744015173491.961382951247.961382963090.78929201186.7 00000400800<00@00D00E00I00J00K00O00S00VS2HkS2H0S2HsS2HsS2HsSS2HfSSS2HfS2HfS1H".
pose proof (Z_lor_range f s ltac:(lia) ltac:(lia)).
  rewrite unsigned_lit by lia. rewrite wz_unsigned.
  2:{ split; [lia|]. apply (Z.lt_le_trans _ (2^32)); [|lia]. apply Z_bounded_by_bits; [lia|lia|].
      intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity. }
  rewrite lor_sxv_mod32 by lia. rewrite Z.lor_comm. symmetry. apply Z.mod_small.
  split; [lia|]. apply Z_bounded_by_bits; [lia|lia|].
  intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition ntf_mid_post (pc : Z) (R : list cell -> word -> Prop (* [comment removed for export] *)) : Prop := True.



End CANSEC3.
