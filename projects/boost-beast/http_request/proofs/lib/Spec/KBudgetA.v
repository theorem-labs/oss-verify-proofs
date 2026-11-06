(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Kit MI_Arith MI_Cnt KLink KLink3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TB.
Context {R : Type}.
Implicit Types (P : R -> Prop) (bail : M R).

Lemma tb_undef' u (k0 : Z -> M R) cb ck P : 0 <= cb -> 0 <= ck -> tbound (SVis (EUndef u) k0) cb ck P.
Proof. intros. cbn. split; [lia|]. split; [lia|]. intros z []. Qed.

Lemma tb_bad bail cb ck P : 0 <= cb -> 0 <= ck -> tbound (bad_answer bail) cb ck P.
Proof. intros. unfold bad_answer. apply tb_undef'; assumption. Qed.

Lemma tb_guard' tag c (t : M R) bail cb ck P : 0 <= cb -> 0 <= ck -> tbound t cb ck P -> tbound (guard tag c t bail) cb ck P.
Proof. intros. unfold guard. destruct c; [assumption| apply tb_undef'; assumption]. Qed.

Lemma tb_ret r cb ck P : P r -> tbound (SRet r : M R) cb ck P.
Proof. intros. cbn. assumption. Qed.

(* [comment removed for export] *)
Lemma ev_fixed_34 : ev_fixed (MAP_PRIVATE + MAP_ANON) = false. Proof. vm_compute. reflexivity. Qed.
Lemma ev_fixed_50 : ev_fixed (MAP_PRIVATE + MAP_ANON + MAP_FIXED) = true. Proof. vm_compute. reflexivity. Qed.
Lemma tb_mmap a len prot (k : Z -> M R) cb ck P :
  mmap_len len <= cb -> 1 <= ck -> (forall z, is_err z = false -> tbound (k z) (cb - mmap_len len) (ck - 1) P) ->
  tbound (SVis (EMmap a len prot (MAP_PRIVATE + MAP_ANON)) k) cb ck P.
Proof. intros. cbn [tbound ev_costb ev_costk ans_cont]. rewrite ev_fixed_34. auto. Qed.
Lemma tb_mmap_fixed a len prot (k : Z -> M R) cb ck P :
  0 <= cb -> 0 <= ck -> (forall z, tbound (k z) cb ck P) -> tbound (SVis (EMmap a len prot (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) cb ck P.
Proof. intros Hb Hk H. cbn [tbound ev_costb ev_costk ans_cont]. rewrite ev_fixed_50. split; [lia|]. split; [lia|]. intros z _. rewrite !Z.sub_0_r. apply H. Qed.
Lemma tb_brk req (k : Z -> M R) cb ck P :
  2 * PGSZ <= cb -> 1 <= ck -> (forall z cb' ck', cb - 2 * PGSZ <= cb' -> ck - 1 <= ck' -> tbound (k z) cb' ck' P) ->
  tbound (SVis (EBrk req) k) cb ck P.
Proof. intros Hb Hk H. cbn. unfold PGSZ in *. destruct (req =? 0); (split; [lia|]; split; [lia|]); intros z _; apply H; lia. Qed.
Lemma tb_brk0 (k : Z -> M R) cb ck P : 0 <= cb -> 0 <= ck -> (forall z, tbound (k z) cb ck P) -> tbound (SVis (EBrk 0) k) cb ck P.
Proof. intros Hb Hk H. cbn. split; [lia|]. split; [lia|]. intros z _. rewrite !Z.sub_0_r. apply H. Qed.
Lemma tb_mprotect a l p (k : Z -> M R) cb ck P : 0 <= cb -> 0 <= ck -> tbound (k 0) cb ck P -> tbound (SVis (EMprotect a l p) k) cb ck P.
Proof. intros Hb Hk H. cbn. split; [lia|]. split; [lia|]. intros z ->. rewrite !Z.sub_0_r. apply H. Qed.
Lemma tb_munmap a l (k : Z -> M R) cb ck P : 0 <= cb -> 0 <= ck -> (forall z, tbound (k z) cb ck P) -> tbound (SVis (EMunmap a l) k) cb ck P.
Proof. intros Hb Hk H. cbn. split; [lia|]. split; [lia|]. intros z _. rewrite !Z.sub_0_r. apply H. Qed.

(* [comment removed for export] *)
Definition MF (st st' : mstate) : Prop :=
  c_avail_meta_count (ctx st') = c_avail_meta_count (ctx st) /\ c_meta_alloc_shift (ctx st') = c_meta_alloc_shift (ctx st).
Lemma MF_refl st : MF st st. Proof. split; reflexivity. Qed.
Lemma MF_trans a b c : MF a b -> MF b c -> MF a c. Proof. intros [A1 A2] [B1 B2]. split; congruence. Qed.

Local Ltac mf := unfold MF, ctx in *; cbn -[Z.add Z.sub Z.mul Z.shiftl Z.land Z.lor]; autorewrite with mst; auto.

Lemma MF_upd_meta st m f : MF st (upd_meta m f st). Proof. split; reflexivity. Qed.
Lemma MF_set_active st sc v : MF st (set_active sc v st). Proof. split; reflexivity. Qed.
Lemma MF_set_head st h v : MF st (set_head h v st). Proof. destruct h; split; reflexivity. Qed.
Lemma MF_dequeue st h m : MF st (dequeue h m st).
Proof.
  unfold dequeue. destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _)|]; destruct h; split; reflexivity.
Qed.
Lemma MF_set_group_active_idx st g ai : MF st (set_group_active_idx g ai st). Proof. unfold set_group_active_idx. destruct (get_group st g); split; reflexivity. Qed.
Lemma MF_set_bounce st i v : MF st (set_bounce i v st). Proof. split; reflexivity. Qed.
Lemma MF_decay_bounces st sc : MF st (decay_bounces sc st).
Proof. unfold decay_bounces. destruct (_ && _); [apply MF_set_bounce| apply MF_refl]. Qed.
Lemma MF_account_bounce st sc : MF st (account_bounce sc st).
Proof. unfold account_bounce. destruct (sc_in_seq_range sc); [| apply MF_refl]. destruct (_ && _); [| apply MF_refl]. destruct (_ <? _); apply MF_set_bounce. Qed.
Lemma MF_step_seq st : MF st (step_seq st).
Proof. unfold step_seq. destruct (_ =? _); split; reflexivity. Qed.
Lemma MF_new_region st k b l : MF st (fst (new_region k b l st)). Proof. split; reflexivity. Qed.

Lemma tb_queue' h m st (k1 : mstate -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck -> (forall st', MF st st' -> tbound (k1 st') cb ck P) -> tbound (queue h m st k1 bail) cb ck P.
Proof.
  intros Hb Hk H. unfold queue. apply tb_guard'; [lia|lia|]. apply tb_guard'; [lia|lia|].
  destruct (get_head st h); [destruct (m_prev _)|]; apply H.
  - eapply MF_trans; [eapply MF_trans; [apply MF_upd_meta| apply MF_upd_meta]| apply MF_upd_meta].
  - eapply MF_trans; [apply MF_upd_meta| apply MF_upd_meta].
  - eapply MF_trans; [apply MF_upd_meta| apply MF_set_head].
Qed.

Lemma tb_free_meta' m st (k1 : mstate -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck -> (forall st', tbound (k1 st') cb ck P) -> tbound (free_meta m st k1 bail) cb ck P.
Proof. intros Hb Hk H. unfold free_meta. apply tb_queue'; [lia|lia|]. intros; apply H. Qed.

Lemma tb_activate_group' m st (k2 : mstate -> Z -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck -> (forall st' z, MF st st' -> tbound (k2 st' z) cb ck P) -> tbound (activate_group m st k2 bail) cb ck P.
Proof. intros Hb Hk H. unfold activate_group. apply tb_guard'; [lia|lia|]. apply H. apply MF_upd_meta. Qed.

(* [comment removed for export] *)
Local Opaque span_loop group_active_idx get_meta_rec dequeue set_active set_group_active_idx.
Lemma tb_try_avail sc st (k : mstate -> Z -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck -> (forall st1 first, MF st st1 -> tbound (k st1 first) cb ck P) ->
  tbound (try_avail sc st k bail) cb ck P.
Proof.
  intros Hb Hk H. unfold try_avail.
  destruct (active st sc) as [m|]; [| apply H; apply MF_refl].
  destruct (negb _); [apply H; apply MF_upd_meta|].
  set (step1 := if m_freed _ =? 0 then _ else _).
  destruct step1 as [[st1 m1]|] eqn:E1.
  - assert (F1 : MF st st1).
    { subst step1. destruct (_ =? 0).
      - destruct (active (dequeue (LActive sc) m st) sc); [| discriminate]. injection E1 as <- _. apply MF_dequeue.
      - destruct (m_next _); [| discriminate]. injection E1 as <- _. apply MF_set_active. }
    clearbody step1. clear E1.
    set (p2 := if _ && _ then _ else _). destruct p2 as [[st2 m2] mask] eqn:E2.
    assert (F2 : MF st st2).
    { subst p2. destruct (_ && _); [destruct (m_next _)|]; injection E2 as <- _ _; first [exact F1| eapply MF_trans; [exact F1| apply MF_set_active]]. }
    clearbody p2. clear E2.
    set (p3 := if _ =? 0 then _ else _). destruct p3 as [st3 m3] eqn:E3.
    assert (F3 : MF st st3).
    { subst p3. destruct (_ =? 0); [destruct (negb _); [destruct (m_next _)| destruct (m_mem _)]|]; injection E3 as <- _;
      first [exact F2| eapply MF_trans; [exact F2|]; first [apply MF_set_active| apply MF_set_group_active_idx]]. }
    clearbody p3. clear E3.
    apply tb_activate_group'; [lia|lia|]. intros st4 mk F4. apply tb_guard'; [lia|lia|].
    unfold ta_fin. apply H. eapply MF_trans; [exact F3|]. eapply MF_trans; [exact F4|]. eapply MF_trans; [apply MF_decay_bounces| apply MF_upd_meta].
  - destruct (_ =? 0); [apply H; apply MF_dequeue| apply tb_undef'; lia].
Qed.
Local Transparent span_loop group_active_idx get_meta_rec dequeue set_active set_group_active_idx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MCOST (st : mstate) : Z := 2 * PGSZ + Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ.

(* [comment removed for export] *)
Definition MPOT (st : mstate) (lv : nat) (mb mk : Z) : Prop :=
  0 <= mb /\ 0 <= mk /\ 0 <= c_meta_alloc_shift (ctx st) /\
  (Z.of_nat lv <= c_avail_meta_count (ctx st) \/ (MCOST st <= mb /\ 2 <= mk)).

Lemma MPOT_MF st st' lv mb mk : MPOT st lv mb mk -> MF st st' -> MPOT st' lv mb mk.
Proof. unfold MPOT, MCOST. intros (A & B & C & D) [E1 E2]. rewrite E1, E2. auto. Qed.
Lemma MPOT_le st lv lv' mb mk : MPOT st lv mb mk -> (lv' <= lv)%nat -> MPOT st lv' mb mk.
Proof. unfold MPOT. intros (A & B & C & D) LE. split; [lia|]. split; [lia|]. split; [lia|]. destruct D; [left; lia| right; assumption]. Qed.
Lemma MPOT_nonneg st lv mb mk : MPOT st lv mb mk -> 0 <= mb /\ 0 <= mk.
Proof. intros (A & B & _). auto. Qed.

Lemma shiftl2_eq s : 0 <= s -> Z.shiftl 2 s = 2 ^ (s + 1).
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. lia. Qed.

Lemma tb_am_take st (k : mstate -> optr -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck ->
  (forall st' m, c_avail_meta_count (ctx st') = c_avail_meta_count (ctx st) - 1 -> c_meta_alloc_shift (ctx st') = c_meta_alloc_shift (ctx st) ->
     tbound (k st' (Some m)) cb ck P) ->
  tbound (am_take st k bail) cb ck P.
Proof.
  intros Hb Hk H. unfold am_take. destruct (c_avail_meta _) as [m|]; [| apply tb_undef'; lia]. apply H; reflexivity.
Qed.

Lemma tb_am_carve st p (k : mstate -> optr -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck ->
  (forall st' m, c_avail_meta_count (ctx st') = NSLOTS - 1 -> c_meta_alloc_shift (ctx st') = c_meta_alloc_shift (ctx st) -> tbound (k st' (Some m)) cb ck P) ->
  tbound (am_carve st p k bail) cb ck P.
Proof.
  intros Hb Hk H. unfold am_carve. apply tb_am_take; [lia|lia|]. intros st' m E1 E2. apply H.
  - rewrite E1. destruct (c_meta_area_tail _); reflexivity.
  - rewrite E2. destruct (c_meta_area_tail _); reflexivity.
Qed.

Lemma tb_am_finish st nu (k : mstate -> optr -> M R) bail cb ck P :
  0 <= cb -> 0 <= ck ->
  (forall st' m, c_avail_meta_count (ctx st') = NSLOTS - 1 -> c_meta_alloc_shift (ctx st') = c_meta_alloc_shift (ctx st) -> tbound (k st' (Some m)) cb ck P) ->
  tbound (am_finish st nu k bail) cb ck P.
Proof.
  intros Hb Hk H. unfold am_finish. destruct (c_avail_meta_areas _) as [p|]; [| apply tb_undef'; lia].
  destruct (if negb _ then false else nu).
  - apply tb_mprotect; [lia|lia|]. cbn [mprotect_answer_ok negb Z.eqb orb]. apply tb_am_carve; [lia|lia| exact H].
  - apply tb_am_carve; [lia|lia| exact H].
Qed.

Lemma mmap_answer_cont st len r : is_err r = false -> negb (mmap_answer_ok (live_ranges st) len r) = false ->
  mmap_answer_ok (live_ranges st) len r = true.
Proof. intros _ H. destruct (mmap_answer_ok _ _ _); [reflexivity| discriminate]. Qed.

Lemma tb_am_after_brk st nu (k : mstate -> optr -> M R) bail gb gk mb mk P :
  0 <= gb -> 0 <= gk -> 0 <= c_meta_alloc_shift (ctx st) ->
  Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ <= mb -> 1 <= mk ->
  (forall st' m mb' mk', 0 <= mb' -> 0 <= mk' -> c_avail_meta_count (ctx st') = NSLOTS - 1 -> 0 <= c_meta_alloc_shift (ctx st') ->
     tbound (k st' (Some m)) (gb + mb') (gk + mk') P) ->
  tbound (am_after_brk st nu k bail) (gb + mb) (gk + mk) P.
Proof.
  intros Hgb Hgk Hs Hmb Hmk H. unfold am_after_brk.
  pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (ctx st) + 1) ltac:(lia) ltac:(lia)) as PP. rewrite shiftl2_eq in * by lia.
  destruct (_ =? 0).
  - assert (ML : mmap_len (2 ^ (c_meta_alloc_shift (ctx st) + 1) * PGSZ) = 2 ^ (c_meta_alloc_shift (ctx st) + 1) * PGSZ).
    { apply mmap_len_of_aligned; [unfold PGSZ; lia| unfold PGSZ; apply Z_mod_mult]. }
    apply tb_mmap; [rewrite ML; lia| lia|]. intros z Hz. rewrite ML.
    destruct (negb (mmap_answer_ok _ _ _)) eqn:E; [apply tb_bad; lia|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st1 rid] eqn:EN.
    replace (gb + mb - _) with (gb + (mb - 2 ^ (c_meta_alloc_shift (ctx st) + 1) * PGSZ)) by lia.
    replace (gk + mk - 1) with (gk + (mk - 1)) by lia.
    apply tb_am_finish; [lia|lia|]. intros st' m E1 E2. apply H; [lia|lia| exact E1|].
    rewrite E2. apply (f_equal fst) in EN. cbn in EN. subst st1. cbn. unfold ctx in *. lia.
  - apply tb_am_finish; [unfold PGSZ in *; lia|lia|]. intros st' m E1 E2. apply H; [unfold PGSZ in *; lia|lia| exact E1| rewrite E2; exact Hs].
Qed.

(* [comment removed for export] *)
Lemma tb_alloc_meta st (k : mstate -> optr -> M R) bail lv gb gk mb mk P :
  (1 <= lv)%nat -> (lv <= 101)%nat -> MPOT st lv mb mk -> 0 <= gb -> 0 <= gk ->
  (forall st' m mb' mk', MPOT st' (lv - 1) mb' mk' -> tbound (k st' (Some m)) (gb + mb') (gk + mk') P) ->
  tbound (alloc_meta st k bail) (gb + mb) (gk + mk) P.
Proof.
  intros L1 L2 MP Hgb Hgk H. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  assert (MP0 : MPOT st0 lv mb mk) by (subst st0; destruct (_ =? 0); [eapply MPOT_MF; [exact MP| split; reflexivity]| exact MP]).
  clearbody st0. clear MP st. destruct MP0 as (Hmb & Hmk & Hs & D).
  destruct (c_free_meta_head _) as [m|].
  { apply H. eapply MPOT_MF; [| apply MF_dequeue]. split; [lia|]. split; [lia|]. split; [lia|]. destruct D; [left; lia| right; assumption]. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx st0)) 0) as [C0|C0]; cbn [negb].
  2:{ apply tb_am_take; [lia|lia|]. intros st' m' E1 E2. apply H. unfold MPOT, MCOST. rewrite E1, E2. split; [lia|]. split; [lia|]. split; [lia|].
      destruct D; [left; lia| right; assumption]. }
  (* [comment removed for export] *)
  destruct D as [D|[DM DK]]; [exfalso; lia|]. unfold MCOST in DM.
  pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (ctx st0) + 1) ltac:(lia) ltac:(lia)) as PP. rewrite shiftl2_eq in DM by lia.
  assert (AFTER : forall st1 nu cb ck, MF st0 st1 \/ (c_meta_alloc_shift (ctx st1) = c_meta_alloc_shift (ctx st0)) ->
            gb + (mb - 2 * PGSZ) <= cb -> gk + (mk - 1) <= ck ->
            tbound (am_after_brk st1 nu k bail) cb ck P).
  { intros st1 nu cb ck F LEb LEk.
    assert (ES : c_meta_alloc_shift (ctx st1) = c_meta_alloc_shift (ctx st0)) by (destruct F as [[_ F]|F]; exact F).
    replace cb with (gb + (cb - gb)) by lia. replace ck with (gk + (ck - gk)) by lia.
    apply tb_am_after_brk; [lia|lia| rewrite ES; lia| rewrite ES, shiftl2_eq by lia; unfold PGSZ in *; lia| lia|].
    intros st' m' mb' mk' H1 H2 E1 E3. apply H. split; [lia|]. split; [lia|]. split; [exact E3|]. left. rewrite E1. unfold NSLOTS. lia. }
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && _); [| apply AFTER; [left; apply MF_refl| unfold PGSZ; lia| lia]].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - (* [comment removed for export] *)
    apply tb_brk0; [lia|lia|]. intros cur. destruct (negb (brk0_answer_ok cur)); [apply tb_bad; lia|].
    apply tb_brk; [unfold PGSZ in *; lia| lia|]. intros r cb' ck' LEb LEk.
    destruct (negb (brk_answer_ok _ _ _)); [apply tb_bad; unfold PGSZ in *; lia|].
    destruct (negb (r =? _)); [apply AFTER; [right; reflexivity| unfold PGSZ in *; lia| lia]|].
    destruct (negb (brk_pages_ok _ _ _)); [apply tb_bad; unfold PGSZ in *; lia|].
    apply tb_mmap_fixed; [unfold PGSZ in *; lia| lia|]. intros rg.
    destruct (negb (mmap_fixed_answer_ok _ _)); [apply tb_bad; unfold PGSZ in *; lia|].
    destruct (new_region _ _ _ _) as [st1 rid] eqn:EN.
    apply AFTER; [right; apply (f_equal fst) in EN; cbn in EN; subst st1; reflexivity| unfold PGSZ in *; lia| lia].
  - (* [comment removed for export] *)
    apply AFTER; [left; apply MF_refl| unfold PGSZ; lia| lia].
  - (* [comment removed for export] *)
    apply tb_brk; [unfold PGSZ in *; lia| lia|]. intros r cb' ck' LEb LEk.
    destruct (negb (brk_answer_ok _ _ _)); [apply tb_bad; unfold PGSZ in *; lia|].
    destruct (negb (r =? _)); [apply AFTER; [right; reflexivity| unfold PGSZ in *; lia| lia]|].
    destruct (negb (brk_pages_ok _ _ _)); [apply tb_bad; unfold PGSZ in *; lia|].
    apply AFTER; [right; unfold ctx; cbn -[Z.add]; rewrite s_ctx_upd_region; reflexivity| unfold PGSZ in *; lia| lia].
Qed.
End TB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GB : Z := 2^20.

(* [comment removed for export] *)
Definition KANY {R} {A} (P : R -> Prop) (ok : A -> Prop) (k : mstate -> A -> M R) : Prop :=
  forall st1 a cb ck, ok a -> 0 <= cb -> 0 <= ck -> tbound (k st1 a) cb ck P.

Lemma grp_ok_needed sc c3 n3 : grp_ok sc c3 n3 = true -> mmap_len n3 = n3 /\ 0 < n3 <= GB.
Proof.
  intros G. pose proof (grp_ok_sound sc c3 n3 G) as S. cbn zeta in S. destruct S as (_ & MOD & RNG & _).
  split; [apply mmap_len_of_aligned; [lia| exact MOD]| unfold GB; lia].
Qed.

Section AG.
Context {R : Type}.
Variable P : R -> Prop.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Variable lvr : nat.
Hypothesis LVR : (lvr <= 64)%nat.
Hypothesis REC : forall st j req (k : mstate -> Z -> M R) bail mb mk,
  0 <= j < 48 -> 0 <= req -> req + IB <= UNIT * size_class j -> MPOT st lvr mb mk ->
  KANY P (fun idx => 0 <= idx) k ->
  tbound (rec st j req k bail) (GB + mb) (1 + mk) P.

Lemma tb_alloc_group st sc req (k : mstate -> optr -> M R) bail mb mk :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc -> MPOT st (S lvr) mb mk ->
  KANY P (fun go => go <> None) k ->
  tbound (alloc_group R lay_none rec st sc req k bail) (GB + mb) (1 + mk) P.
Proof.
  intros Hsc Hreq Hfit MP HK. unfold alloc_group.
  apply (tb_alloc_meta st _ bail (S lvr) GB 1 mb mk P); [lia| lia| exact MP| unfold GB; lia| lia|].
  intros st1 m mb' mk' MP1. replace (S lvr - 1)%nat with lvr in MP1 by lia. pose proof (MPOT_nonneg _ _ _ _ MP1) as [Hmb' Hmk'].
  cbn beta iota.
  change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
    with (cnt0_of sc (usage st1 sc)).
  change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
    with (MI_WSlot2.ag_cnt1 sc (usage st1 sc)).
  pose proof (MI_WSlot2.ag_arith sc req (usage st1 sc)) as AR.
  set (c1 := MI_WSlot2.ag_cnt1 sc (usage st1 sc)) in *.
  destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
  - (* [comment removed for export] *)
    set (ns := is_bouncing sc st1).
    set (st1' := step_seq (account_bounce sc st1)).
    set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
    change (if (u1 <? 4 * c1) && negb ns
            then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                 else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                 else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                 else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                 else c1
            else c1) with (MI_WSlot2.ag_cnt2 sc c1 u1 ns).
    set (c2 := MI_WSlot2.ag_cnt2 sc c1 u1 ns).
    specialize (AR u1 ns).
    assert (GO : forall c3 n3, MI_WSlot2.ag_cn3 sc req c2 u1 ns = (c3, n3) ->
      tbound (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
        else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
        else let '(st2, rid) := new_region RKGroup r n3 st1' in
             ag_tail lay_none (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
               (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) (GB + mb') (1 + mk') P).
    { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP _].
      destruct (grp_ok_needed _ _ _ GRP) as [ML RNG].
      apply tb_mmap; [rewrite ML; lia| lia|]. intros z Hz. rewrite ML.
      destruct (negb (mmap_answer_ok _ _ _)); [apply tb_bad; lia|]. rewrite Hz.
      destruct (new_region _ _ _ _) as [st2 rid]. unfold ag_tail. apply HK; [discriminate| lia| lia]. }
    unfold MI_WSlot2.ag_cn3 in GO. cbn zeta in GO.
    destruct (negb ns && (c2 <=? 7)).
    * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
      -- cbn beta iota. exact (GO _ _ eq_refl).
      -- cbn beta iota. exact (GO _ _ eq_refl).
    * cbn beta iota. exact (GO _ _ eq_refl).
  - (* [comment removed for export] *)
    pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
    pose proof (nest_ok_sound _ _ NEST) as NS. cbn zeta in NS. destruct NS as (Hc1 & Hj & FIT & _ & N0 & N2048).
    set (req' := UNIT + c1 * (UNIT * size_class sc) - IB) in *.
    pose proof (size_to_class_ok req' ltac:(unfold MMAP_THRESHOLD, IB in *; lia)) as [J1 J2].
    apply REC; [exact J1| exact N0| exact J2| exact MP1|].
    intros st2 idx cb ck Hidx Hcb Hck. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st2 _) as [g|]; [| apply tb_undef'; lia].
    unfold ag_tail. apply HK; [discriminate| lia| lia].
Qed.
End AG.

Lemma ctz32_nonneg x : 0 <= ctz32 x.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma tb_alloc_slot {R} (P : R -> Prop) f : forall st sc req (k : mstate -> Z -> M R) bail mb mk,
  (f <= 64)%nat -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc -> MPOT st f mb mk ->
  KANY P (fun idx => 0 <= idx) k ->
  tbound (alloc_slot lay_none f st sc req k bail) (GB + mb) (1 + mk) P.
Proof.
  induction f as [|f IH]; intros st sc req k bail mb mk Hf Hsc Hreq Hfit MP HK.
  - pose proof (MPOT_nonneg _ _ _ _ MP). cbn [alloc_slot]. apply tb_undef'; unfold GB; lia.
  - pose proof (MPOT_nonneg _ _ _ _ MP) as [Hmb Hmk]. cbn [alloc_slot].
    apply tb_try_avail; [unfold GB; lia| lia|]. intros st1 first F1.
    destruct (negb (first =? 0)); [apply HK; [apply ctz32_nonneg| unfold GB; lia| lia]|].
    apply (tb_alloc_group P (alloc_slot lay_none f) f ltac:(lia)).
    + intros st' j req' k' bail' mb' mk' Hj Hr' Hfit' MP' HK'. apply IH; auto. lia.
    + exact Hsc. + exact Hreq. + exact Hfit.
    + eapply MPOT_MF; [exact MP| exact F1].
    + intros st2 [g|] cb ck Hg Hcb Hck; [| exfalso; exact (Hg eq_refl)].
      apply tb_queue'; [lia|lia|]. intros st4 _. apply HK; [lia|lia|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tb_malloc_small {R} (P : R -> Prop) st n (k : mstate -> option (aptr * Z) -> M R) bail mb mk :
  0 <= n < MMAP_THRESHOLD -> MPOT st 64 mb mk ->
  KANY P (fun r => r <> None) k ->
  tbound (malloc_small_ctrl lay_none st n k bail) (GB + mb) (1 + mk) P.
Proof.
  intros Hn MP HK. pose proof (MPOT_nonneg _ _ _ _ MP) as [Hmb Hmk]. unfold malloc_small_ctrl.
  pose proof (size_to_class_ok n Hn) as [S1 S2]. set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
  assert (SC : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { subst sc. destruct (active st sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
    destruct (_ <=? 12); [| auto].
    apply andb_prop in E as [E _]. apply andb_prop in E as [E EV]. apply andb_prop in E as [E _]. apply andb_prop in E as [E4 E32].
    apply Z.leb_le in E4. apply Z.ltb_lt in E32.
    rewrite (lor1_even sc0) by (lia || exact EV).
    pose proof (size_class_le sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. split; [lia| nia]. }
  clearbody sc. destruct SC as [SC1 SC2].
  assert (SLOT : tbound (alloc_slot lay_none FUEL st sc n (fun st1 idx =>
             if idx <? 0 then k st1 None
             else match active st1 sc with Some gp => k st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => bail) end) bail) (GB + mb) (1 + mk) P).
  { apply tb_alloc_slot; [unfold FUEL; lia| exact SC1| lia| exact SC2| exact MP|].
    intros st1 idx cb ck Hidx Hcb Hck. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st1 sc); [apply HK; [discriminate|lia|lia]| apply tb_undef'; lia]. }
  destruct (active st sc) as [gp|]; [| exact SLOT].
  destruct (negb (lowbit _ =? 0)); [| exact SLOT].
  apply HK; [discriminate| unfold GB; lia| lia].
Qed.

Lemma size_overflows_false n : n <= 2^32 -> size_overflows n = false.
Proof. intros. unfold size_overflows. apply Z.leb_gt. lia. Qed.

Definition GBIG (n : Z) : Z := if MMAP_THRESHOLD <=? n then mmap_len (n + IB + UNIT) else GB.

Lemma tb_malloc_core st n mb mk :
  0 <= n <= 2^32 -> MPOT st 64 mb mk ->
  tbound (malloc_core lay_none st n) (GBIG n + mb) (1 + mk) (fun r => snd r <> None).
Proof.
  intros Hn MP. pose proof (MPOT_nonneg _ _ _ _ MP) as [Hmb Hmk]. unfold malloc_core, GBIG.
  rewrite size_overflows_false by lia.
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [BIG|SMALL].
  - apply tb_mmap; [lia|lia|]. intros r Hr.
    destruct (negb (mmap_answer_ok _ _ _)); [apply tb_bad; lia|]. rewrite Hr.
    destruct (new_region _ _ _ _) as [st1 rid] eqn:EN.
    replace (mmap_len (n + IB + UNIT) + mb - mmap_len (n + IB + UNIT)) with (0 + mb) by lia.
    replace (1 + mk - 1) with (0 + mk) by lia.
    apply (tb_alloc_meta _ _ _ 64 0 0 mb mk); [lia| lia| | lia| lia|].
    + eapply MPOT_MF; [exact MP|]. eapply MF_trans; [| apply MF_step_seq]. apply (f_equal fst) in EN. cbn [fst] in EN. rewrite <- EN. apply MF_new_region.
    + intros st3 g mb' mk' MP3. cbn. discriminate.
  - apply tb_malloc_small; [lia| exact MP|]. intros st1 [[g idx]|] cb ck Hr Hcb Hck; [cbn; discriminate| exfalso; exact (Hr eq_refl)].
Qed.

Lemma tb_bind {A B} (P : A -> Prop) (Q : B -> Prop) : forall (t : M A) (f : A -> M B) cb ck,
  tbound t cb ck P -> 0 <= cb -> 0 <= ck ->
  (forall a cb' ck', P a -> 0 <= cb' -> 0 <= ck' -> tbound (f a) cb' ck' Q) ->
  tbound (sbind t f) cb ck Q.
Proof.
  induction t as [r|e k IH]; intros f cb ck H Hb Hk Hf; cbn in *; [apply Hf; auto|].
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros z Hz.
  apply IH; [apply H3; exact Hz| lia| lia| exact Hf].
Qed.

(* [comment removed for export] *)
Definition CB_malloc (cs : mstate) (n : Z) : Z := GBIG n + MCOST cs.
Definition CK_malloc : Z := 3.

Theorem tbound_cmalloc cs n :
  0 <= n <= 2^32 -> 0 <= c_meta_alloc_shift (ctx cs) ->
  tbound (cmalloc cs n) (CB_malloc cs n) CK_malloc (fun r => snd r <> None).
Proof.
  intros Hn Hs. unfold cmalloc, CB_malloc, CK_malloc.
  assert (MC : 0 <= MCOST cs).
  { unfold MCOST. rewrite shiftl2_eq by lia. pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (ctx cs) + 1) ltac:(lia) ltac:(lia)). unfold PGSZ. lia. }
  assert (G0 : 0 <= GBIG n).
  { unfold GBIG, GB. destruct (_ <=? _); [| lia]. pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT in *. lia. }
  change 3 with (1 + 2).
  apply (tb_bind (fun r : mstate * option (aptr * Z) => snd r <> None)).
  - apply tb_malloc_core; [exact Hn|]. split; [exact MC|]. split; [lia|]. split; [exact Hs|]. right. split; [lia| lia].
  - lia.
  - lia.
  - intros [st1 [[g idx]|]] cb' ck' Hr Hcb Hck; cbn in Hr |- *; [discriminate| exfalso; exact (Hr eq_refl)].
Qed.

Lemma CB_malloc_le cs n : 0 <= n < 2^63 - 4096 -> 0 <= c_meta_alloc_shift (ctx cs) ->
  CB_malloc cs n <= Z.max (n + IB + UNIT + 4096) GB + 2 * PGSZ + 2^(c_meta_alloc_shift (ctx cs) + 1) * PGSZ.
Proof.
  intros Hn Hs. unfold CB_malloc, GBIG, MCOST. rewrite shiftl2_eq by lia.
  destruct (_ <=? _); [pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)); unfold IB, UNIT, PGSZ in *; lia| unfold PGSZ; lia].
Qed.
