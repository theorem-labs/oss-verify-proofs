(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Decode.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc KInv MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRes.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.MB Require Import MBBase.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AREA (PA : Z) : Z := Z.max 0 ((2 * PGSZ * PA) / NSLOTS).
(* [comment removed for export] *)
Definition XB (PA : Z) : Z := 2 * PGSZ + AREA PA.

Lemma AREA_nonneg PA : 0 <= AREA PA. Proof. unfold AREA. lia. Qed.
Lemma XB_nonneg PA : 0 <= XB PA. Proof. unfold XB. pose proof (AREA_nonneg PA). rewrite PGSZ_val. lia. Qed.

(* [comment removed for export] *)
Definition INV (PA : Z) (ph : bool) (r : Z) (st : mstate) : Prop :=
  0 <= shift_of (scal st) /\ pot st + r <= PA /\ (ph = true -> r <= cnt_of (scal st)).

Definition evs (ph : bool) : nat := if ph then 0%nat else 5%nat.
Definition cost (PA : Z) (ph : bool) : Z := if ph then 0 else XB PA.

Lemma cost_nonneg PA ph : 0 <= cost PA ph.
Proof. unfold cost. destruct ph; [lia| apply XB_nonneg]. Qed.

Lemma INV_scal PA ph r a b : scal a = scal b -> INV PA ph r b -> INV PA ph r a.
Proof. intros H [I1 [I2 I3]]. unfold INV. rewrite (pot_of_scal b a H), H. auto. Qed.

Lemma INV_le PA ph r r' st : r' <= r -> INV PA ph r st -> INV PA ph r' st.
Proof. intros Hr [I1 [I2 I3]]. split; [exact I1|]. split; [lia|]. intros Hp. specialize (I3 Hp). lia. Qed.

Lemma INV_potPA PA ph r st : 0 <= r -> INV PA ph r st -> pot st <= PA.
Proof. intros Hr [_ [I2 _]]. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Context {R : Type}.
Variable E : ev -> Prop.
Variable PA : Z.
Hypothesis E_brk : forall a, E (EBrk a).
Hypothesis E_fix : forall a l p, E (EMmap a l p (MAP_PRIVATE + MAP_ANON + MAP_FIXED)).
Hypothesis E_area : forall l, NSLOTS * l <= 2 * PGSZ * PA -> E (EMmap 0 l PROT_NONE (MAP_PRIVATE + MAP_ANON)).
Hypothesis E_prot : forall a l p, E (EMprotect a l p).

(* [comment removed for export] *)
Lemma am_finish_g st nu (k : mstate -> optr -> M R) bail ne bb Q :
  (forall st' x, scal st' = (NSLOTS - 1, ac_of (scal st) - 1, shift_of (scal st)) -> x <> None ->
                 gtree E ne bb (k st' x) Q) ->
  0 <= bb ->
  gtree E (S ne) bb (am_finish st nu k bail) Q.
Proof.
  intros HK Hbb. unfold am_finish, ctx.
  destruct (c_avail_meta_areas (s_ctx st)) as [p|]; [| apply gtree_undef; exact I]. cbv zeta.
  gcase.
  - apply gtree_vis; [apply E_prot| rewrite ecost_mprotect; lia|].
    intros z Hz. cbn in Hz. subst z. rewrite mprotect_answer_ok_0. cbn [negb Z.eqb orb].
    rewrite ecost_mprotect, Z.sub_0_r.
    eapply gtree_retK; [apply am_carve_shape|]. cbv beta. intros st' x [H1 H2]. apply HK; [exact H1| exact H2].
  - eapply gtree_retK; [apply am_carve_shape|]. cbv beta. intros st' x [H1 H2].
    eapply gtree_le; [| | apply HK; [exact H1| exact H2]]; lia.
Qed.

(* [comment removed for export] *)
Lemma am_after_brk_g st nu (k : mstate -> optr -> M R) bail ne bb Q :
  0 <= shift_of (scal st) -> cnt_of (scal st) = 0 -> pot st <= PA ->
  (forall st' x, 0 <= shift_of (scal st') -> cnt_of (scal st') = NSLOTS - 1 -> pot st' <= pot st + 1 ->
                 x <> None -> gtree E ne bb (k st' x) Q) ->
  0 <= bb ->
  gtree E (S (S ne)) (AREA PA + bb) (am_after_brk st nu k bail) Q.
Proof.
  intros Hsh Hcnt Hpot HK Hbb. pose proof (AREA_nonneg PA) as HA. pose proof PGSZ_val as HPG. pose proof NSLOTS_val as HNS.
  unfold am_after_brk, ctx. rewrite ac_scal, shift_scal.
  destruct (Z.eqb_spec (ac_of (scal st)) 0) as [Hac|Hac].
  - cbv zeta. rewrite shiftl_2 by exact Hsh.
    set (nn := 2 * 2 ^ shift_of (scal st)).
    assert (Hpot_eq : pot st = NSLOTS * 2 ^ shift_of (scal st)).
    { rewrite pot_scal. destruct (scal st) as [[c a] s]. cproj_in Hac. cproj_in Hcnt. cproj. subst. lia. }
    assert (Hlen : NSLOTS * (nn * PGSZ) <= 2 * PGSZ * PA) by (subst nn; lia).
    assert (Hal : (nn * PGSZ) mod 4096 = 0) by (rewrite PGSZ_val; apply Z_mod_mult).
    assert (Hnn : 1 <= 2 ^ shift_of (scal st)) by (apply pow2_pos; exact Hsh).
    assert (Hcost : mmap_len (nn * PGSZ) <= AREA PA).
    { rewrite mmap_len_eq, round_up_pg_id by exact Hal. unfold AREA.
      pose proof (div_le_of_mul NSLOTS (nn * PGSZ) (2 * PGSZ * PA) ltac:(rewrite NSLOTS_val; lia) Hlen). lia. }
    apply gtree_vis; [apply E_area; exact Hlen| rewrite ecost_mmap_anon; lia|].
    intros z Hz. apply good_mmap_anon in Hz. rewrite ecost_mmap_anon.
    gcase; [apply gtree_undef; exact I|]. rewrite Hz. cbn [new_region]. cbv zeta.
    match goal with |- gtree _ _ _ (am_finish ?s _ _ _) _ => set (st2 := s) end.
    assert (S2 : scal st2 = (cnt_of (scal st), nn - 1, shift_of (scal st) + 1)) by (subst st2; sproj; reflexivity).
    apply am_finish_g; [| lia]. intros st' x H1 H2. rewrite S2 in H1. cproj_in H1.
    eapply gtree_le; [apply le_n| | apply HK; [rewrite H1; cproj; lia| rewrite H1; reflexivity| | exact H2]]; [lia|].
    rewrite pot_scal, H1, Hpot_eq. unfold potf. subst nn. rewrite Z.pow_add_r, NSLOTS_val by lia. change (2 ^ 1) with 2. lia.
  - apply (gtree_le E Q _ (S ne) (S (S ne)) bb (AREA PA + bb)); [lia| lia|]. apply am_finish_g; [| lia].
    intros st' x H1 H2. apply HK; [rewrite H1; cproj; exact Hsh| rewrite H1; reflexivity| | exact H2].
    rewrite !pot_scal, H1. destruct (scal st) as [[c a] s]. cproj_in Hcnt. cproj. subst c. rewrite NSLOTS_val. lia.
Qed.

(* [comment removed for export] *)
Theorem alloc_meta_g ph r st (k : mstate -> optr -> M R) bail ne bb Q :
  INV PA ph r st -> 1 <= r <= NSLOTS ->
  (forall st' x ph', INV PA ph' (r - 1) st' -> x <> None ->
                     gtree E (evs ph' + ne)%nat (cost PA ph' + bb) (k st' x) Q) ->
  0 <= bb ->
  gtree E (evs ph + ne)%nat (cost PA ph + bb) (alloc_meta st k bail) Q.
Proof.
  intros HI Hr HK Hbb. pose proof (AREA_nonneg PA) as HA. pose proof PGSZ_val as HPG. pose proof NSLOTS_val as HNS.
  unfold alloc_meta. cbv zeta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else _).
  assert (S0 : scal st0 = scal st) by (subst st0; destruct (_ =? 0); reflexivity).
  assert (HI0 : INV PA ph r st0) by (eapply INV_scal; [exact S0| exact HI]).
  clearbody st0. clear HI. rename HI0 into HI. revert HI. generalize st0. clear st st0 S0. intros st HI.
  unfold ctx. destruct (c_free_meta_head (s_ctx st)) as [m|].
  { (* [comment removed for export] *) apply (HK _ _ ph); [| discriminate]. eapply INV_scal; [apply scal_dequeue|]. eapply INV_le; [| exact HI]. lia. }
  rewrite cnt_scal, ac_scal. destruct (Z.eqb_spec (cnt_of (scal st)) 0) as [Hc|Hc]; cbn [negb].
  2:{ (* [comment removed for export] *)
      eapply gtree_retK; [apply am_take_shape|]. cbv beta. intros st' x [H1 H2].
      apply (HK _ _ ph); [| exact H2]. destruct HI as [I1 [I2 I3]].
      rewrite cnt_scal, ac_scal, shift_scal in H1.
      split; [| split]; rewrite ?pot_scal, ?H1 in *; [cproj; exact I1| |].
      - revert I2. destruct (scal st) as [[c a] s]. cproj. lia.
      - intros Hp. specialize (I3 Hp). cproj. lia. }
  (* [comment removed for export] *)
  destruct HI as [I1 [I2 I3]].
  destruct ph. { exfalso. specialize (I3 eq_refl). lia. }
  clear I3. cbn [evs cost]. unfold XB.
  (* [comment removed for export] *)
  assert (TAIL : forall X nu ne' bb', 0 <= shift_of (scal X) -> cnt_of (scal X) = 0 -> pot X <= pot st -> 0 <= bb' ->
            (ne <= ne')%nat -> bb <= bb' ->
            gtree E (S (S ne')) (AREA PA + bb') (am_after_brk X nu k bail) Q).
  { intros X nu ne' bb' X1 X2 X3 X4 X5 X6. apply am_after_brk_g; [exact X1| exact X2| lia| | exact X4].
    intros st' x H1 H2 H3 H4. eapply gtree_le; [| | apply (HK st' x true); [| exact H4]]; [exact X5| cbn [cost]; lia|].
    split; [exact H1|]. split; [lia|]. intros _. rewrite H2. lia. }
  destruct (c_brk (s_ctx st)) as [| |rid off] eqn:HB; cbn [andb negb];
    destruct (Z.eqb_spec (ac_of (scal st)) 0) as [Ha|Ha]; cbn [andb].
  - (* [comment removed for export] *)
    apply gtree_vis; [apply E_brk| rewrite ecost_brk0; lia|]. intros cur _. rewrite ecost_brk0, Z.sub_0_r.
    gcase; [apply gtree_undef; exact I|]. cbv zeta.
    apply gtree_vis; [apply E_brk| pose proof (ecost_brk_le (round_up_pg cur + 2 * PGSZ)); lia|]. intros z _.
    pose proof (ecost_brk_le (round_up_pg cur + 2 * PGSZ)) as HC.
    gcase; [apply gtree_undef; exact I|].
    gcase.
    + (* [comment removed for export] *) eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; first [lia| exact I1| exact Hc| apply Z.le_refl].
    + gcase; [apply gtree_undef; exact I|].
      apply gtree_vis; [apply E_fix| rewrite ecost_mmap_fixed; lia|]. intros rg _. rewrite ecost_mmap_fixed, Z.sub_0_r.
      gcase; [apply gtree_undef; exact I|]. cbn [new_region]. cbv zeta.
      match goal with |- gtree _ _ _ (am_after_brk ?s _ _ _) _ => set (st2 := s) end.
      assert (S2 : scal st2 = (cnt_of (scal st), 1, shift_of (scal st))) by (subst st2; sproj; reflexivity).
      eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; rewrite ?S2; first [lia| cproj; exact I1| cproj; exact Hc| idtac].
      rewrite !pot_scal, S2. destruct (scal st) as [[c a] s]; cproj_in Hc; cproj_in Ha; cproj. rewrite NSLOTS_val. lia.
  - (* [comment removed for export] *)
    eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; first [lia| exact I1| exact Hc| apply Z.le_refl].
  - (* [comment removed for export] *)
    eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; first [lia| exact I1| exact Hc| apply Z.le_refl].
  - eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; first [lia| exact I1| exact Hc| apply Z.le_refl].
  - (* [comment removed for export] *)
    cbv zeta. apply gtree_vis; [apply E_brk| pose proof (ecost_brk_le (conc st (rid, off) + PGSZ)); lia|]. intros z _.
    pose proof (ecost_brk_le (conc st (rid, off) + PGSZ)) as HC.
    gcase; [apply gtree_undef; exact I|].
    gcase.
    + eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; first [lia| exact I1| exact Hc| apply Z.le_refl].
    + gcase; [apply gtree_undef; exact I|]. cbv zeta.
      match goal with |- gtree _ _ _ (am_after_brk ?s _ _ _) _ => set (st2 := s) end.
      assert (S2 : scal st2 = (cnt_of (scal st), 1, shift_of (scal st))).
      { subst st2. unfold upd_region. destruct (get_region st rid); sproj; reflexivity. }
      eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; rewrite ?S2; first [lia| cproj; exact I1| cproj; exact Hc| idtac].
      rewrite !pot_scal, S2. destruct (scal st) as [[c a] s]; cproj_in Hc; cproj_in Ha; cproj. rewrite NSLOTS_val. lia.
  - eapply gtree_le; [| | apply (TAIL _ _ ne bb)]; first [lia| exact I1| exact Hc| apply Z.le_refl].
Qed.

End AM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SH (st : mstate) : Prop := 0 <= shift_of (scal st).

Lemma SH_scal a b : scal a = scal b -> SH b -> SH a.
Proof. intros H. unfold SH. rewrite H. auto. Qed.

Section AMLV.
Context {R : Type}.
Variable P : R -> Prop.

Lemma am_finish_lv st nu (k : mstate -> optr -> M R) bail :
  SH st -> (forall st' x, SH st' -> leaves P (k st' x)) -> leaves P (am_finish st nu k bail).
Proof.
  intros HS HK. unfold am_finish, ctx.
  destruct (c_avail_meta_areas (s_ctx st)) as [p|]; [| apply leaves_undef; exact I]. cbv zeta.
  assert (CV : leaves P (am_carve st p k bail)).
  { eapply leaves_retK; [apply am_carve_shape|]. cbv beta. intros st' x [H1 H2]. apply HK.
    unfold SH. rewrite H1. cproj. exact HS. }
  gcase; [| exact CV]. apply leaves_vis. intros z.
  gcase; [apply leaves_undef; exact I|]. gcase; [exact CV|]. apply HK. exact HS.
Qed.

Lemma am_after_brk_lv st nu (k : mstate -> optr -> M R) bail :
  SH st -> (forall st' x, SH st' -> leaves P (k st' x)) -> leaves P (am_after_brk st nu k bail).
Proof.
  intros HS HK. unfold am_after_brk, ctx. gcase.
  - cbv zeta. apply leaves_vis. intros z. gcase; [apply leaves_undef; exact I|]. gcase; [apply HK; exact HS|].
    cbn [new_region]. cbv zeta. apply am_finish_lv; [| exact HK].
    unfold SH in HS |- *. sproj_in HS. sproj. lia.
  - apply am_finish_lv; [exact HS| exact HK].
Qed.

Theorem alloc_meta_lv st (k : mstate -> optr -> M R) bail :
  SH st -> (forall st' x, SH st' -> leaves P (k st' x)) -> leaves P (alloc_meta st k bail).
Proof.
  intros HS HK. unfold alloc_meta. cbv zeta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else _).
  assert (S0 : scal st0 = scal st) by (subst st0; destruct (_ =? 0); reflexivity).
  assert (HS0 : SH st0) by (eapply SH_scal; [exact S0| exact HS]).
  clearbody st0. clear HS. revert HS0. generalize st0. clear st st0 S0. intros st HS.
  assert (HSd : SH (upd_ctx (set_brk BrkDead) st)) by exact HS.
  unfold ctx. destruct (c_free_meta_head (s_ctx st)) as [m|].
  { apply HK. eapply SH_scal; [apply scal_dequeue| exact HS]. }
  gcase.
  { eapply leaves_retK; [apply am_take_shape|]. cbv beta. intros st' x [H1 _]. apply HK.
    unfold SH. rewrite H1. cproj. exact HS. }
  cbv zeta.
  destruct (c_brk (s_ctx st)) as [| |rid off]; cbn [andb negb]; gcase;
    try (apply am_after_brk_lv; [exact HS| exact HK]).
  - apply leaves_vis. intros cur. gcase; [apply leaves_undef; exact I|]. cbv zeta.
    apply leaves_vis. intros z. gcase; [apply leaves_undef; exact I|].
    gcase; [apply am_after_brk_lv; [exact HSd| exact HK]|].
    gcase; [apply leaves_undef; exact I|].
    apply leaves_vis. intros rg. gcase; [apply leaves_undef; exact I|]. cbn [new_region]. cbv zeta.
    apply am_after_brk_lv; [| exact HK]. unfold SH in HS |- *. sproj_in HS. sproj. exact HS.
  - apply leaves_vis. intros z. gcase; [apply leaves_undef; exact I|].
    gcase; [apply am_after_brk_lv; [exact HSd| exact HK]|].
    gcase; [apply leaves_undef; exact I|]. cbv zeta.
    apply am_after_brk_lv; [| exact HK]. unfold SH in HS |- *. sproj_in HS.
    unfold upd_region. destruct (get_region st rid); sproj; exact HS.
Qed.

End AMLV.
End CEIL_WRAP_1.

