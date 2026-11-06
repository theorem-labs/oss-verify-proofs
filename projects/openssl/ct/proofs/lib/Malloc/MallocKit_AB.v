(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
  forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros P lo hi a []. Qed.

Lemma ivs_avoid_cons : forall lo hi W P,
  (forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
  - inversion E; subst. apply H1. exact Ha.
  - eapply H2; eauto.
Qed.

Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
  - intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
  - apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

(* [comment removed for export] *)
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : forall st g mr g',
  get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.

Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
  nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma actives_length st : length (actives st) = 48%nat.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
Lemma usages_length st : length (usages st) = 48%nat.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
  destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p. Proof. reflexivity. Qed.
Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p. Proof. reflexivity. Qed.
Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r. Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma outside_of_cover : forall (C : Z -> Prop) W a,
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
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

(* [comment removed for export] *)
Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn in Hx |- *. tauto.
Qed.

End WithCeiling0.
Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeiling1. Context {CE__ : Ceiling}.
Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MU : munch W m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
End CTXFRAME.

(* [comment removed for export] *)
Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

End WithCeiling1.
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
Section WithCeiling2. Context {CE__ : Ceiling}.
Lemma step_seq_eq st :
  step_seq st = if c_seq (ctx st) =? 255
                then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
                else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma record_seq_eq sc st :
  record_seq sc st = if sc_in_seq_range sc
                     then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
                     else st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.

Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q. Proof. reflexivity. Qed.
Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q. Proof. intros H; exact H. Qed.
Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q. Proof. intros H; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (LI & FB & SCR & ML).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (LI & FB & SCR & ML).
  change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (LI & FB & SCR & ML).
  assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^6) with 64. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (LI & FB & SCR & ML).
  rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land. reflexivity.
Qed.

Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hf Ha.
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hf Ha. split; [apply Z.land_nonneg; lia|].
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
  rewrite sxv_mod32. reflexivity.
Qed.

Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
  rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.

(* [comment removed for export] *)
End WithCeiling2.
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).

(* [comment removed for export] *)
Section WithCeiling3. Context {CE__ : Ceiling}.
Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.
End WithCeiling3.
