(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgMontCorrect BgNumTheory BgMontSpec BgRecpSpec BgInvSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mont_n0_fact : forall Ri b0, 1 < b0 -> 0 <= Ri < b0 -> (Ri * 2 ^ 64) mod b0 = 1 ->
  let K := (Ri * 2 ^ 64) / b0 in K * b0 = Ri * 2 ^ 64 - 1 /\ 0 <= K < BW /\ (K * b0 + 1) mod BW = 0.
Proof.
  intros Ri b0 Hb0 HRi Hm. cbv zeta. set (K := Ri * 2 ^ 64 / b0).
  pose proof (Z.div_mod (Ri * 2 ^ 64) b0 ltac:(lia)) as E. fold K in E. rewrite Hm in E.
  assert (HK : K * b0 = Ri * 2 ^ 64 - 1) by lia.
  assert (HK0 : 0 <= K) by (apply Z.div_pos; lia).
  assert (HK1 : K < BW).
  { destruct (Z.lt_ge_cases K BW) as [|Hge]; [assumption|exfalso].
    assert (BW * b0 <= K * b0) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (Ri * 2 ^ 64 <= (b0 - 1) * 2 ^ 64) by (apply Z.mul_le_mono_nonneg_r; lia).
    unfold BW in *. lia. }
  split; [exact HK|]. split; [lia|]. rewrite HK. replace (Ri * 2 ^ 64 - 1 + 1) with (Ri * BW) by (unfold BW; lia).
  apply Z.mod_mul. unfold BW. lia.
Qed.

Lemma div64_limbs : forall nb nl, 64 * (nl - 1) < nb <= 64 * nl -> (nb + 63) / 64 = nl.
Proof.
  intros nb nl H. pose proof (Z_div_mod_eq_full (nb + 63) 64) as E. pose proof (Z.mod_pos_bound (nb + 63) 64 ltac:(lia)) as B. lia.
Qed.

Section MontSpec2.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).

Lemma hoare_set_nod : forall r (b : BN) F s (Q : unit -> ST -> Prop),
  (r < length (st_bns s))%nat -> r <> ROne -> bg_ok b -> bn_d b = None -> bn_d (getbn r s) = None ->
  Q tt (setbn r b s) -> bn_flags b = bn_flags (getbn r s) -> hoare F s (bset ops r b) Q.
Proof.
  intros r b F s Q Hr Hn Hb Ed Ed0 HQ Ef X Hs Hfl (HP & HF). cbn. split; [apply st_wf_setbn; assumption|].
  split; [apply fl_ok_setbn; assumption|]. split; [|exact HQ].
  split; [|exact HF]. rewrite blocks_of_setbn_same; [exact HP|exact Hr|]. unfold bn_blocks. rewrite Ed, Ed0. reflexivity.
Qed.

Lemma hoare_bind_set_nod : forall {B} r (b : BN) (f : unit -> BMu B) F s Q,
  (r < length (st_bns s))%nat -> r <> ROne -> bg_ok b -> bn_d b = None -> bn_d (getbn r s) = None ->
  bn_flags b = bn_flags (getbn r s) ->
  hoare F (setbn r b s) (f tt) Q -> hoare F s (bbind ops (bset ops r b) f) Q.
Proof.
  intros B r b f F s Q Hr Hn Hb Ed Ed0 Ef H.
  eapply hoare_bind; [apply hoare_set_nod with (Q := fun _ s' => s' = setbn r b s); try assumption; reflexivity|].
  intros [] s' _ ->. exact H.
Qed.

Lemma hoare_bind_getst_setmont : forall {B} (fri fn0 : ST -> Z) (f : unit -> BMu B) F s Q,
  hoare F (set_mont (fri s) (fn0 s) s) (f tt) Q ->
  hoare F s (bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops (fri st) (fn0 st))) f) Q.
Proof.
  intros B fri fn0 f F s Q H.
  eapply hoare_bind with (R := fun _ s' => s' = set_mont (fri s) (fn0 s) s); [apply hoare_bind_getst; apply hoare_setmont; reflexivity|].
  intros [] s' _ ->. exact H.
Qed.

Lemma getbn_set_mont : forall r ri n0 (s : ST), getbn r (set_mont ri n0 s) = getbn r s.
Proof. reflexivity. Qed.
Lemma st_bns_set_mont : forall ri n0 (s : ST), st_bns (set_mont ri n0 s) = st_bns s.
Proof. reflexivity. Qed.
Lemma st_ctx_set_mont : forall ri n0 (s : ST), st_ctx (set_mont ri n0 s) = st_ctx s.
Proof. reflexivity. Qed.

Definition tmod (b0 : Z) : BN := mkBN None [b0; 0] 1%nat false 0.

Lemma tmod_ok : forall b0, limb b0 -> bg_ok (tmod b0).
Proof.
  intros b0 Hb. unfold bg_ok, tmod, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags length].
  split; [constructor; [exact Hb|constructor; [exact limb_0|constructor]]|]. split; [lia|]. split; [lia|left; reflexivity].
Qed.

Lemma tmod_mag : forall b0, bn_mag (tmod b0) = b0.
Proof. intros b0. unfold bn_mag, tmod. cbn [bn_top bn_buf firstn lval]. lia. Qed.

Lemma tmod_norm : forall b0, b0 <> 0 -> bn_norm (tmod b0).
Proof. intros b0 H. right. cbn. exact H. Qed.

Lemma tmod_is_one : forall b0, is_one_pure (tmod b0) = (b0 =? 1).
Proof. intros b0. unfold is_one_pure, abs_is_word_pure, tmod. cbn [bn_top bn_buf bn_neg nth Nat.eqb negb andb orb Z.eqb]. destruct (b0 =? 1); reflexivity. Qed.

Lemma mag_top_le1 : forall b : BN, (bn_top b <= 1)%nat -> (if (0 <? bn_top b)%nat then nth 0 (bn_buf b) 0 else 0) = bn_mag b.
Proof.
  intros b Ht. unfold bn_mag. destruct (Nat.ltb_spec 0 (bn_top b)) as [H|H].
  - replace (bn_top b) with 1%nat by lia. destruct (bn_buf b) as [|x l]; cbn [firstn nth lval]; lia.
  - replace (bn_top b) with 0%nat by lia. reflexivity.
Qed.

Lemma BN_div_spec2 : forall dv rm num divisor F s,
  div_pre dv rm num divisor s ->
  hoare F s (BN_div ops dv rm num divisor) (fun _ s' =>
     keeps (gx_used (st_ctx s)) (opt_refs dv ++ opt_refs rm) s s' /\
     div_res dv rm (getbn num s) (getbn divisor s) s' /\
     (forall r, rm = Some r -> (bn_top (getbn divisor s) <= bn_dmax (getbn r s'))%nat)).
Proof.
  intros dv rm num divisor F s Hpre. pose proof Hpre as (Lnum & Ldiv & Hdv & Hrm & Hdepth & Hpool & Hn2 & Htop2 & Ht1 & Ht2).
  apply hoare_wf. intros Hs. unfold BN_div. apply hoare_bind_get.
  destruct (Nat.eqb_spec (bn_top (getbn divisor s)) 0) as [|_]; [lia|].
  destruct Hn2 as [Hz|Hnz]; [lia|].
  destruct (Z.eqb_spec (nth (bn_top (getbn divisor s) - 1) (bn_buf (getbn divisor s)) 0) 0) as [E|_]; [contradiction|].
  set (u := gx_used (st_ctx s)) in *. set (num0 := getbn num s) in *. set (div0 := getbn divisor s) in *.
  eapply hoare_bind; [apply bn_div_fixed_top_spec; exact Hpre|].
  intros [] s1 Hs1 (K1 & Q1 & R1). fold u num0 div0 in K1, Q1, R1.
  assert (Hval1 : forall r, live r s -> (r < length (st_bns s1))%nat).
  { intros r Hr. apply live_valid; [exact Hs1|]. eapply keeps_live; eassumption. }
  eapply hoare_bind; [apply opt_correct_top_spec|].
  { intros r Er. destruct (Hdv r Er) as (A1 & A2 & A3). split; [apply Hval1; exact A1|exact A2]. }
  intros [] s2 Hs2 E2.
  assert (K2 : keeps u (opt_refs dv ++ opt_refs rm) s s2 /\ (forall r, rm = Some r -> getbn r s2 = getbn r s1) /\ length (st_bns s2) = length (st_bns s1)).
  { destruct dv as [d|]; [|subst s2; split; [exact K1|split; [intros; reflexivity|reflexivity]]]. subst s2. split; [|split].
    - eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
      intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [exact Hin|]. cbn [opt_refs app]. left. reflexivity.
    - intros r Er. destruct (Hrm r Er) as (_ & _ & _ & A4). apply getbn_setbn_other. congruence.
    - apply length_setbn. }
  destruct K2 as (K2 & Hrm2 & Len2).
  eapply hoare_mono; [apply opt_correct_top_spec|].
  { intros r Er. destruct (Hrm r Er) as (A1 & A2 & A3 & A4). split; [rewrite Len2; apply Hval1; exact A1|exact A2]. }
  intros [] s3 Hs3 E3.
  assert (RM : forall r, rm = Some r -> let x := getbn r s3 in
     (bn_canon x /\ bn_mag x = bn_mag num0 mod bn_mag div0 /\ bn_neg x = (bn_neg num0 && negb (bn_top x =? 0)%nat) /\ (bn_top x <= bn_top div0)%nat) /\
     (bn_top div0 <= bn_dmax x)%nat).
  { intros r Er. cbv zeta.
    assert (Hr1 : (r < length (st_bns s1))%nat) by (destruct (Hrm r Er) as (A1 & _); apply Hval1; exact A1).
    assert (Hrn : r <> ROne) by (destruct (Hrm r Er) as (_ & A2 & _); exact A2).
    rewrite Er in E3. subst s3. rewrite getbn_setbn_same by (rewrite Len2; exact Hr1). rewrite (Hrm2 r Er).
    pose proof (st_wf_ok r s1 Hs1 Hr1 Hrn) as Hok1.
    destruct (bg_correct_top_ok (getbn r s1) Hok1) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    destruct (R1 r Er) as (M1 & M2 & M3). split.
    - split; [exact C2|]. split; [rewrite C3; exact M1|]. split; [rewrite C7, M2; reflexivity|lia].
    - unfold bn_dmax. rewrite C5. destruct Hok1 as (_ & B2 & _). unfold bn_dmax in B2. lia. }
  split; [|split].
  - destruct rm as [r|]; [|subst s3; exact K2]. subst s3.
    eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K2|apply keeps_setbn]].
    intros r' Hin _. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [exact Hin|]. apply in_or_app. right. left. reflexivity.
  - split.
    + intros d Ed. cbv zeta.
      assert (Hd1 : (d < length (st_bns s1))%nat) by (destruct (Hdv d Ed) as (A1 & _); apply Hval1; exact A1).
      assert (Hdn : d <> ROne) by (destruct (Hdv d Ed) as (_ & A2 & _); exact A2).
      assert (Eg : getbn d s3 = bn_correct_top_pure (getbn d s1)).
      { rewrite Ed in E2. subst s2. destruct rm as [r|].
        - subst s3. destruct (Hrm r eq_refl) as (_ & _ & _ & A4). rewrite getbn_setbn_other by congruence.
          apply getbn_setbn_same. exact Hd1.
        - subst s3. apply getbn_setbn_same. exact Hd1. }
      rewrite Eg. destruct (bg_correct_top_ok (getbn d s1) (st_wf_ok d s1 Hs1 Hd1 Hdn)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      destruct (Q1 d Ed) as (M1 & M2 & M3). split; [exact C2|]. split; [rewrite C3; exact M1|]. split; [rewrite C7, M2; reflexivity|lia].
    + intros r Er. exact (proj1 (RM r Er)).
  - intros r Er. exact (proj2 (RM r Er)).
Qed.

Local Notation "x <- m ;; k" := (bbind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).

Definition montset_pre (rmod : bnref) (s : ST) : Prop :=
  live rmod s /\ ndiff rmod RMontN /\ ndiff rmod RMontRR /\ ndiff rmod RTmod /\
  (length (gx_frames (st_ctx s)) + 3 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 12 <= BG_POOL)%nat /\
  getbn RTmod s = bn_nil 0 /\
  (let m := getbn rmod s in bn_norm m /\ (1 <= bn_top m <= 127)%nat /\ Z.odd (bn_mag m) = true).

Definition keepsM (u : nat) (outs : list bnref) (s s' : ST) : Prop :=
  keeps0 u (RMontN :: RMontRR :: outs) s s' /\ st_rbits s' = st_rbits s /\ st_rshift s' = st_rshift s.

Definition montset_post (s : ST) (N : Z) (nl : nat) : unit -> ST -> Prop :=
  fun _ s' => keepsM (gx_used (st_ctx s)) [] s s' /\ st_ri s' = 64 * Z.of_nat nl /\ mont_ok s' N nl.

Definition mset_frame (s sk : ST) (rRi : bnref) (ri : Z) : Prop :=
  rRi = RPool (gx_used (st_ctx s)) /\ gx_used (st_ctx sk) = S (gx_used (st_ctx s)) /\
  gx_frames (st_ctx sk) = gx_frames (st_ctx s) ++ [gx_used (st_ctx s)] /\
  (length (st_bns s) <= length (st_bns sk))%nat /\
  (forall x, (x < NFIX + gx_used (st_ctx s))%nat -> x <> RMontN -> x <> RMontRR -> x <> RTmod -> getbn x sk = getbn x s) /\
  st_ri sk = ri /\ st_rbits sk = st_rbits s /\ st_rshift sk = st_rshift s.

Definition mset_N (s sk : ST) (rmod : bnref) : Prop :=
  bn_top (getbn RMontN sk) = bn_top (getbn rmod s) /\ bn_neg (getbn RMontN sk) = false /\
  bn_mag (getbn RMontN sk) = bn_mag (getbn rmod s) /\ bn_norm (getbn RMontN sk) /\
  nth 0 (bn_buf (getbn RMontN sk)) 0 = nth 0 (bn_buf (getbn rmod s)) 0.

Lemma mset_frame_keeps : forall s sk sk' rRi ri o,
  mset_frame s sk rRi ri -> keeps (S (gx_used (st_ctx s))) o sk sk' ->
  (forall r, In r o -> (NFIX + gx_used (st_ctx s) <= r)%nat \/ r = RMontN \/ r = RMontRR \/ r = RTmod) -> mset_frame s sk' rRi ri.
Proof.
  intros s sk sk' rRi ri o (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8) K Ho.
  destruct K as [[(C1 & C2 & C3) Sl] (S1 & S2 & S3 & S4)].
  unfold mset_frame. split; [exact E1|]. split; [rewrite C2; exact E2|]. split; [rewrite C3; exact E3|]. split; [lia|]. split.
  - intros x Hx H1 H2 H3. rewrite (Sl x); [apply E5; assumption|lia|].
    intros Hin. destruct (Ho x Hin) as [H|[H|[H|H]]]; [lia|congruence|congruence|congruence].
  - rewrite S1, S3, S4. split; [exact E6|]. split; [exact E7|exact E8].
Qed.

Lemma mset_frame_setbn : forall s sk rRi ri r b, mset_frame s sk rRi ri ->
  ((NFIX + gx_used (st_ctx s) <= r)%nat \/ r = RMontN \/ r = RMontRR \/ r = RTmod) -> mset_frame s (setbn r b sk) rRi ri.
Proof.
  intros s sk rRi ri r b (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8) Hr. unfold mset_frame. rewrite st_ctx_setbn, length_setbn.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split.
  - intros x Hx H1 H2 H3. rewrite getbn_setbn_other by (destruct Hr as [H|[H|[H|H]]]; [lia|congruence|congruence|congruence]). apply E5; assumption.
  - change (st_ri (setbn r b sk)) with (st_ri sk). change (st_rbits (setbn r b sk)) with (st_rbits sk).
    change (st_rshift (setbn r b sk)) with (st_rshift sk). split; [exact E6|]. split; [exact E7|exact E8].
Qed.

Lemma mset_frame_setmont : forall s sk rRi ri n0, mset_frame s sk rRi ri -> mset_frame s (set_mont ri n0 sk) rRi ri.
Proof.
  intros s sk rRi ri n0 (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). unfold mset_frame. rewrite st_ctx_set_mont, st_bns_set_mont.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split.
  - intros x Hx H1 H2 H3. rewrite getbn_set_mont. apply E5; assumption.
  - change (st_rbits (set_mont ri n0 sk)) with (st_rbits sk). change (st_rshift (set_mont ri n0 sk)) with (st_rshift sk).
    split; [reflexivity|]. split; [exact E7|exact E8].
Qed.

Lemma mset_N_eq : forall s sk sk' rmod, getbn RMontN sk' = getbn RMontN sk -> mset_N s sk rmod -> mset_N s sk' rmod.
Proof. intros s sk sk' rmod E H. unfold mset_N in *. rewrite E. exact H. Qed.

Definition montset_tailC (rRi : bnref) (ri : Z) : BMu unit :=
    BN_div ops (Some rRi) None rRi RTmod ;;;
    x <- bget ops rRi ;;
    let n0 := if (0 <? bn_top x)%nat then nth 0 (bn_buf x) 0 else 0 in
    (st <- bgetst ops ;; bsetmont ops (st_ri st) n0) ;;;
    BN_zero ops RMontRR ;;;
    st <- bgetst ops ;;
    if negb (st_ri st =? ri) then bunr ops else
    BN_set_bit ops RMontRR (ri * 2) ;;;
    BN_mod ops RMontRR RMontRR RMontN ;;;
    rr <- bget ops RMontRR ;;
    n <- bget ops RMontN ;;
    if (bn_dmax rr <? bn_top n)%nat then bunr ops else
    bset ops RMontRR (mkBN (bn_d rr) (splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr))) (bn_top n)
                       (bn_neg rr) (bn_flags rr)) ;;;
    BN_CTX_end ops ;;;
    tm <- bget ops RTmod ;;
    if (match bn_d tm with Some _ => true | None => false end) then bunr ops else
    bset ops RTmod (bn_nil 0).

Lemma montset_tailC_spec : forall rmod rRi F (s s9 : ST) K,
  st_wf s -> montset_pre rmod s ->
  mset_frame s s9 rRi (64 * Z.of_nat (bn_top (getbn rmod s))) -> mset_N s s9 rmod ->
  getbn RTmod s9 = tmod (nth 0 (bn_buf (getbn rmod s)) 0) ->
  bn_norm (getbn rRi s9) /\ bn_neg (getbn rRi s9) = false /\ (bn_top (getbn rRi s9) <= 3)%nat /\
    bn_mag (getbn rRi s9) = K * nth 0 (bn_buf (getbn rmod s)) 0 ->
  0 <= K < BW -> (K * nth 0 (bn_buf (getbn rmod s)) 0 + 1) mod BW = 0 ->
  hoare F s9 (montset_tailC rRi (64 * Z.of_nat (bn_top (getbn rmod s))))
    (montset_post s (bn_mag (getbn rmod s)) (bn_top (getbn rmod s))).
Proof.
  intros rmod rRi F s s9 K Hs Hpre F9 N9 T9 X9 HK HKm.
  destruct Hpre as (Lm & NmN & NmRR & NmT & Hdepth & Hpool & ET & (Nm & Tm & Om)).
  pose proof F9 as (ErRi & Eu9 & Ef9 & L9 & G9 & Eri9 & Erb9 & Ersh9). destruct N9 as (Tn9 & Sn9 & Mn9 & Nn9 & Bn9).
  destruct X9 as (Nx9 & Sx9 & Tx9 & Mx9).
  set (u := gx_used (st_ctx s)) in *. set (m := getbn rmod s) in *. set (N := bn_mag m) in *. set (nl := bn_top m) in *.
  set (b0 := nth 0 (bn_buf m) 0) in *. set (n := getbn RMontN s9) in *.
  apply hoare_wf. intros Hs9. unfold montset_tailC.
  pose proof (live_valid _ _ Hs Lm) as Vm. unfold live in Lm. fold u in Lm.
  pose proof (st_wf_okv rmod s Hs Vm) as Okm. fold m in Okm.
  assert (Lb0 : limb b0) by (apply limbs_nth; destruct Okm as [H _]; exact H).
  assert (Ob0 : Z.odd b0 = true).
  { pose proof (is_odd_pure_spec m Okm) as E. fold N in E. rewrite Om in E. unfold is_odd_pure in E.
    destruct (Nat.ltb_spec 0 (bn_top m)); [|lia]. cbn [andb] in E. fold b0 in E. exact E. }
  assert (Hb0 : b0 <> 0) by (intros E; rewrite E in Ob0; discriminate).
  assert (HN1 : 1 <= N).
  { pose proof (okv_mag_nonneg _ Okm) as H0. fold N in H0. destruct (Z.eq_dec N 0) as [E|]; [rewrite E in Om; discriminate|lia]. }
  assert (V9 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s9))%nat).
  { intros x Hx. apply live_valid; [exact Hs9|]. unfold live. rewrite Eu9. exact Hx. }
  assert (DD : ndiff rRi RMontN /\ ndiff rRi RMontRR /\ ndiff rRi RTmod /\ rRi <> ROne /\ RMontN <> ROne /\ RMontRR <> ROne /\ RTmod <> ROne /\
               ndiff RMontRR RMontN /\ ndiff RMontRR RTmod /\ ndiff RMontN RTmod).
  { rewrite ErRi. unfold ndiff, RPool, RMontN, RMontRR, RTmod, ROne, NFIX in *. repeat split; lia. }
  destruct DD as (D2 & D3 & D4 & NR1 & NN1 & NRR1 & NT1 & D5 & D6 & D7).
  assert (VRi : (rRi < length (st_bns s9))%nat) by (apply V9; rewrite ErRi; unfold RPool; lia).

  eapply hoare_bind.
  { apply (BN_div_spec2 (Some rRi) None rRi RTmod). unfold div_pre, live. rewrite Eu9, Ef9, length_app, T9. cbn [length].
    split; [rewrite ErRi; unfold RPool; lia|]. split; [unfold RTmod, NFIX; lia|]. split.
    - intros d Ed. injection Ed as <-. split; [rewrite ErRi; unfold RPool; lia|]. split; [exact NR1|exact D4].
    - split; [intros r Er; discriminate|]. split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|].
      split; [apply tmod_norm; exact Hb0|]. split; [cbn; lia|]. split; [unfold BG_DMAX; lia|unfold BG_DMAX; cbn; lia]. }
  intros [] s10 Hs10 (K10 & Q10 & _). rewrite Eu9 in K10. cbn [opt_refs app] in K10.
  destruct Q10 as [Q10 _]. specialize (Q10 rRi eq_refl). cbv zeta in Q10. rewrite T9, tmod_mag, Mx9, Sx9 in Q10.
  destruct Q10 as (Cq & Mq & Sq & _). cbn [xorb andb bn_neg tmod] in Sq. rewrite Z.div_mul in Mq by exact Hb0.
  set (q := getbn rRi s10) in *.
  pose proof (mset_frame_keeps s s9 s10 rRi _ [rRi] F9 K10 ltac:(intros r [<-|[]]; left; rewrite ErRi; unfold RPool; lia)) as F10.
  pose proof F10 as (_ & Eu10 & Ef10 & L10 & G10 & Eri10 & Erb10 & Ersh10).
  assert (V10 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s10))%nat).
  { intros x Hx. apply live_valid; [exact Hs10|]. unfold live. rewrite Eu10. exact Hx. }
  assert (EN10 : getbn RMontN s10 = n) by (apply (keeps_get _ _ _ _ RMontN K10); [unfold RMontN, NFIX; lia|intros [E|[]]; apply D2; exact E]).
  assert (ET10 : getbn RTmod s10 = tmod b0) by (rewrite <- T9; apply (keeps_get _ _ _ _ RTmod K10); [unfold RTmod, NFIX; lia|intros [E|[]]; apply D4; exact E]).
  assert (En010 : st_n0 s10 = st_n0 s9) by (destruct K10 as [_ (_ & S2 & _)]; exact S2).
  pose proof (st_wf_okv rRi s10 Hs10 (V10 rRi ltac:(rewrite ErRi; unfold RPool; lia))) as Okq. fold q in Okq.
  assert (Tq : (bn_top q <= 1)%nat) by (apply norm_top_lt; [exact Okq|exact (proj1 Cq)|rewrite Mq, Bp_1; lia]).
  assert (En0 : (if (0 <? bn_top q)%nat then nth 0 (bn_buf q) 0 else 0) = K) by (rewrite mag_top_le1 by exact Tq; exact Mq).

  apply hoare_bind_get. fold q. cbv zeta. rewrite En0.
  apply (hoare_bind_getst_setmont (fun st => st_ri st) (fun _ => K)). rewrite Eri10.
  set (s11 := set_mont (64 * Z.of_nat nl) K s10).
  pose proof (mset_frame_setmont s s10 rRi _ K F10) as F11. fold s11 in F11.
  assert (V11 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s11))%nat) by (intros x Hx; unfold s11; rewrite st_bns_set_mont; apply V10; exact Hx).

  eapply hoare_bind; [apply BN_zero_spec; [apply V11; unfold RMontRR, NFIX; lia|exact NRR1]|].
  intros [] s12 Hs12 (rr12 & -> & (Trr12 & Srr12)).

  apply hoare_bind_getst. cbv beta. change (st_ri (setbn RMontRR rr12 s11)) with (64 * Z.of_nat nl). rewrite Z.eqb_refl. cbn [negb].
  assert (Hri2 : 64 * Z.of_nat nl * 2 / 64 = 2 * Z.of_nat nl).
  { replace (64 * Z.of_nat nl * 2) with (2 * Z.of_nat nl * 64) by lia. apply Z.div_mul. lia. }
  eapply hoare_bind.
  { apply BN_set_bit_zero_spec; [rewrite length_setbn; apply V11; unfold RMontRR, NFIX; lia|exact NRR1|lia|rewrite Hri2; unfold BG_DMAX; lia|].
    rewrite getbn_setbn_same by (apply V11; unfold RMontRR, NFIX; lia). exact Trr12. }
  intros [] s13 Hs13 (rr13 & -> & (Mrr13 & Nrr13 & Trr13 & Srr13)).
  rewrite getbn_setbn_same in Srr13 by (apply V11; unfold RMontRR, NFIX; lia). rewrite Srr12 in Srr13. rewrite setbn_setbn_same.
  rewrite Hri2 in Trr13. replace (Z.to_nat (2 * Z.of_nat nl) + 1)%nat with (2 * nl + 1)%nat in Trr13 by lia.
  set (s13 := setbn RMontRR rr13 s11) in *.
  pose proof (mset_frame_setbn s s11 rRi _ RMontRR rr13 F11 ltac:(right; right; left; reflexivity)) as F13. fold s13 in F13.
  pose proof F13 as (_ & Eu13 & Ef13 & L13 & G13 & Eri13 & Erb13 & Ersh13).
  assert (V13 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s13))%nat) by (intros x Hx; unfold s13; rewrite length_setbn; apply V11; exact Hx).
  assert (EN13 : getbn RMontN s13 = n) by (unfold s13, s11; rewrite getbn_setbn_other by exact D5; rewrite getbn_set_mont; exact EN10).
  assert (ERR13 : getbn RMontRR s13 = rr13) by (unfold s13; apply getbn_setbn_same; apply V11; unfold RMontRR, NFIX; lia).
  assert (ET13 : getbn RTmod s13 = tmod b0) by (unfold s13, s11; rewrite getbn_setbn_other by exact D6; rewrite getbn_set_mont; exact ET10).
  unfold BN_mod. eapply hoare_bind.
  { apply (BN_div_spec2 None (Some RMontRR) RMontRR RMontN). unfold div_pre, live. rewrite Eu13, Ef13, length_app, EN13, ERR13. cbn [length].
    split; [unfold RMontRR, NFIX; lia|]. split; [unfold RMontN, NFIX; lia|]. split; [intros d Ed; discriminate|]. split.
    - intros r Er. injection Er as <-. split; [unfold RMontRR, NFIX; lia|]. split; [exact NRR1|]. split; [exact D5|discriminate].
    - split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact Nn9|]. split; [rewrite Tn9; lia|].
      split; [rewrite Trr13; unfold BG_DMAX; lia|rewrite Tn9; unfold BG_DMAX; lia]. }
  intros [] s14 Hs14 (K14 & Q14 & D14). rewrite Eu13 in K14. cbn [opt_refs app] in K14.
  destruct Q14 as [_ Q14]. specialize (Q14 RMontRR eq_refl). cbv zeta in Q14. specialize (D14 RMontRR eq_refl).
  rewrite EN13, ERR13 in Q14. rewrite EN13 in D14. rewrite Tn9 in Q14, D14. rewrite Mrr13, Mn9, Srr13 in Q14.
  destruct Q14 as (Crr & Mrr & Srr & Trr). cbn [andb] in Srr.
  set (rr := getbn RMontRR s14) in *.
  pose proof (mset_frame_keeps s s13 s14 rRi _ [RMontRR] F13 K14 ltac:(intros r [<-|[]]; right; right; left; reflexivity)) as F14.
  pose proof F14 as (_ & Eu14 & Ef14 & L14 & G14 & Eri14 & Erb14 & Ersh14).
  assert (V14 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s14))%nat).
  { intros x Hx. apply live_valid; [exact Hs14|]. unfold live. rewrite Eu14. exact Hx. }
  assert (EN14 : getbn RMontN s14 = n) by (rewrite <- EN13; apply (keeps_get _ _ _ _ RMontN K14); [unfold RMontN, NFIX; lia|intros [E|[]]; apply D5; exact E]).
  assert (ET14 : getbn RTmod s14 = tmod b0) by (rewrite <- ET13; apply (keeps_get _ _ _ _ RTmod K14); [unfold RTmod, NFIX; lia|intros [E|[]]; apply D6; exact E]).
  assert (En014 : st_n0 s14 = K) by (destruct K14 as [_ (_ & S2 & _)]; rewrite S2; reflexivity).
  pose proof (st_wf_ok RMontRR s14 Hs14 (V14 RMontRR ltac:(unfold RMontRR, NFIX; lia)) NRR1) as OKrr. fold rr in OKrr.
  pose proof OKrr as (O1 & O2 & O3 & O4). unfold bn_dmax in O2, O3, D14.

  apply hoare_bind_get. apply hoare_bind_get. fold rr. rewrite EN14, Tn9.
  replace (bn_dmax rr <? nl)%nat with false by (symmetry; apply Nat.ltb_ge; unfold bn_dmax; lia).
  set (pad := mkBN (bn_d rr) (splice (bn_buf rr) (bn_top rr) (repeat 0 (nl - bn_top rr))) nl (bn_neg rr) (bn_flags rr)).
  assert (Lpad : length (splice (bn_buf rr) (bn_top rr) (repeat 0 (nl - bn_top rr))) = length (bn_buf rr)) by (apply splice_length; rewrite repeat_length; lia).
  eapply hoare_bind_set; [apply V14; unfold RMontRR, NFIX; lia|exact NRR1| |reflexivity|cbn [pad bn_buf]; exact Lpad|reflexivity|].
  { unfold bg_ok, bn_dmax. cbn [pad bn_buf bn_top bn_flags]. rewrite Lpad.
    split; [apply splice_limbs; [exact O1|apply limbs_repeat; exact limb_0]|]. split; [lia|]. split; [exact O3|exact O4]. }
  set (s15 := setbn RMontRR pad s14).

  eapply hoare_bind; [apply (BN_CTX_end_spec F s15 (gx_frames (st_ctx s)) u); unfold s15; rewrite st_ctx_setbn; exact Ef14|].
  intros [] s16 Hs16 (Eb16 & Sc16 & Eu16 & Ef16). destruct Sc16 as (S1 & S2 & S3 & S4).
  assert (G16 : forall x, getbn x s16 = getbn x s15) by (intros x; unfold getbn; rewrite Eb16; reflexivity).

  apply hoare_bind_get. replace (bn_d (getbn RTmod s16)) with (@None ptr) by (rewrite G16; unfold s15; rewrite getbn_setbn_other by exact D6; rewrite ET14; reflexivity).
  apply hoare_set_nod; [rewrite Eb16; unfold s15; rewrite length_setbn; apply V14; unfold RTmod, NFIX; lia|exact NT1|apply bg_ok_nil; left; reflexivity|reflexivity| | |].
  { rewrite G16. unfold s15. rewrite getbn_setbn_other by exact D6. rewrite ET14. reflexivity. }
  2:{ rewrite G16. unfold s15. rewrite getbn_setbn_other by exact D6. rewrite ET14. reflexivity. }
  unfold montset_post. split; [|split].
  - unfold keepsM, keeps0, ctx_keep, slots_same. rewrite st_ctx_setbn, length_setbn, Eb16, Eu16, Ef16. unfold s15. rewrite length_setbn.
    split; [split; [split; [exact L14|split; reflexivity]|]|].
    + intros x Hx Hnin. destruct (Nat.eq_dec x RTmod) as [->|HxT].
      * rewrite getbn_setbn_same by (rewrite Eb16; unfold s15; rewrite length_setbn; apply V14; unfold RTmod, NFIX; lia). symmetry. exact ET.
      * rewrite getbn_setbn_other by (intros E; apply HxT; symmetry; exact E). rewrite G16. unfold s15.
        rewrite getbn_setbn_other by (intros E; apply Hnin; right; left; exact E).
        apply G14; [exact Hx|intros E; apply Hnin; left; symmetry; exact E|intros E; apply Hnin; right; left; symmetry; exact E|exact HxT].
    + change (st_rbits (setbn RTmod (bn_nil 0) s16)) with (st_rbits s16). change (st_rshift (setbn RTmod (bn_nil 0) s16)) with (st_rshift s16).
      rewrite S3, S4. unfold s15. change (st_rbits (setbn RMontRR pad s14)) with (st_rbits s14). change (st_rshift (setbn RMontRR pad s14)) with (st_rshift s14).
      split; [exact Erb14|exact Ersh14].
  - change (st_ri (setbn RTmod (bn_nil 0) s16)) with (st_ri s16). rewrite S1. unfold s15. change (st_ri (setbn RMontRR pad s14)) with (st_ri s14). exact Eri14.
  - unfold mont_ok. cbv zeta. rewrite getbn_setbn_other by (exact (ndiff_sym _ _ D7)). rewrite G16. unfold s15. rewrite getbn_setbn_other by exact D5. rewrite EN14.
    change (st_n0 (setbn RTmod (bn_nil 0) s16)) with (st_n0 s16). rewrite S2. change (st_n0 s15) with (st_n0 s14). rewrite En014.
    rewrite getbn_setbn_other by (exact (ndiff_sym _ _ D6)). rewrite G16. unfold s15. rewrite getbn_setbn_same by (apply V14; unfold RMontRR, NFIX; lia).
    rewrite Tn9, Sn9, Mn9, Bn9. fold b0.
    split; [reflexivity|]. split; [exact Tm|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Om|]. split; [exact HN1|].
    split; [exact HK|]. split; [exact HKm|].
    cbn [pad bn_top bn_neg]. split; [reflexivity|]. split; [exact Srr|].
    unfold bn_mag, pad. cbn [bn_top bn_buf]. replace nl with (bn_top rr + (nl - bn_top rr))%nat at 1 by lia.
    rewrite firstn_pad_zeros by lia. rewrite lval_app, lval_repeat0, Z.mul_0_r, Z.add_0_r.
    change (lval (firstn (bn_top rr) (bn_buf rr))) with (bn_mag rr). rewrite Mrr. fold N. f_equal.
    rewrite Bp_pow2, <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Definition montset_tailB (rRi : bnref) (ri : Z) : BMu unit :=
    BN_lshift ops rRi rRi 64 ;;;
    x <- bget ops rRi ;;
    (if negb (is_zero_pure x) then (if lval (firstn (bn_top x) (bn_buf x)) <? 1 then bunr ops else BN_sub_word ops rRi 1) else BN_set_word ops rRi BN_MASK2) ;;;
    montset_tailC rRi ri.

Lemma montset_tailB_spec : forall rmod rRi F (s s7 : ST),
  st_wf s -> montset_pre rmod s ->
  mset_frame s s7 rRi (64 * Z.of_nat (bn_top (getbn rmod s))) -> mset_N s s7 rmod ->
  getbn RTmod s7 = tmod (nth 0 (bn_buf (getbn rmod s)) 0) ->
  (let r := getbn rRi s7 in let b0 := nth 0 (bn_buf (getbn rmod s)) 0 in
   bn_canon r /\ bn_neg r = false /\ (bn_top r <= 1)%nat /\
   ((b0 = 1 /\ bn_mag r = 0) \/ (1 < b0 /\ 0 <= bn_mag r < b0 /\ (bn_mag r * 2 ^ 64) mod b0 = 1))) ->
  hoare F s7 (montset_tailB rRi (64 * Z.of_nat (bn_top (getbn rmod s))))
    (montset_post s (bn_mag (getbn rmod s)) (bn_top (getbn rmod s))).
Proof.
  intros rmod rRi F s s7 Hs Hpre F7 N7 T7 R7. cbv zeta in R7. destruct R7 as (Cr & Sr & Tr & CASES).
  pose proof Hpre as (Lm & NmN & NmRR & NmT & Hdepth & Hpool & ET & (Nm & Tm & Om)).
  pose proof F7 as (ErRi & Eu7 & Ef7 & L7 & G7 & Eri7 & Erb7 & Ersh7).
  set (u := gx_used (st_ctx s)) in *. set (m := getbn rmod s) in *. set (nl := bn_top m) in *.
  set (b0 := nth 0 (bn_buf m) 0) in *. set (r7 := getbn rRi s7) in *.
  apply hoare_wf. intros Hs7. unfold montset_tailB.
  assert (V7 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s7))%nat).
  { intros x Hx. apply live_valid; [exact Hs7|]. unfold live. rewrite Eu7. exact Hx. }
  assert (NR1 : rRi <> ROne) by (rewrite ErRi; unfold RPool, ROne, NFIX; lia).
  assert (HRi : (NFIX + u <= rRi)%nat) by (rewrite ErRi; unfold RPool; lia).
  assert (D2 : rRi <> RMontN) by (unfold RMontN, NFIX in *; lia).
  assert (D4 : rRi <> RTmod) by (unfold RTmod, NFIX in *; lia).
  assert (VRi : (rRi < length (st_bns s7))%nat) by (apply V7; rewrite ErRi; unfold RPool; lia).
  pose proof (st_wf_okv rRi s7 Hs7 VRi) as Okr. fold r7 in Okr. pose proof (okv_mag_nonneg _ Okr) as Mr0.

  eapply hoare_bind.
  { apply BN_lshift_spec; [exact VRi|exact NR1|exact VRi|lia|]. fold r7. replace (64 / 64) with 1 by reflexivity. unfold BG_DMAX. lia. }
  intros [] s8 Hs8 (x8 & -> & (C8 & M8 & S8 & T8)). fold r7 in M8, S8, T8. rewrite Sr in S8. cbn [andb] in S8.
  replace (Z.to_nat (64 / 64)) with 1%nat in T8 by reflexivity.
  pose proof (st_wf_okv rRi _ Hs8 ltac:(rewrite length_setbn; exact VRi)) as Ok8. rewrite getbn_setbn_same in Ok8 by exact VRi.
  apply hoare_bind_get. rewrite getbn_setbn_same by exact VRi. unfold is_zero_pure.
  eapply hoare_bind with (R := fun _ s9 => exists K x9, s9 = setbn rRi x9 (setbn rRi x8 s7) /\
      bn_norm x9 /\ bn_neg x9 = false /\ (bn_top x9 <= 3)%nat /\ bn_mag x9 = K * b0 /\ 0 <= K < BW /\ (K * b0 + 1) mod BW = 0).
  { destruct CASES as [[Eb0 Mr]|(Hb0 & HRb & HRm)].
    -
      rewrite Mr, Z.mul_0_l in M8.
      assert (Tx8 : bn_top x8 = 0%nat) by (apply (norm_zero_iff x8 Ok8 (proj1 C8)); exact M8).
      rewrite Tx8. cbn [Nat.eqb negb].
      eapply hoare_mono; [apply BN_set_word_spec; [rewrite length_setbn; exact VRi|exact NR1|unfold limb, BN_MASK2, BW; lia]|].
      intros [] s9 _ (x9 & -> & (M9 & C9 & S9 & T9)). exists (BW - 1), x9.
      split; [reflexivity|]. split; [exact (proj1 C9)|]. split; [exact S9|]. split; [lia|]. split; [rewrite M9, Eb0; unfold BN_MASK2; lia|].
      split; [unfold BW; lia|]. rewrite Eb0. replace ((BW - 1) * 1 + 1) with BW by lia. apply Z.mod_same. unfold BW. lia.
    -
      assert (Hm8 : 0 < bn_mag x8).
      { rewrite M8. assert (Hr0 : bn_mag r7 <> 0) by (intros E; rewrite E, Z.mul_0_l, Z.mod_0_l in HRm by lia; lia).
        apply Z.mul_pos_pos; [lia|]. apply Z.pow_pos_nonneg; lia. }
      destruct (Nat.eqb_spec (bn_top x8) 0) as [E|_]; [rewrite (bn_mag_top0 x8 E) in Hm8; lia|]. cbn [negb].

      change (lval (firstn (bn_top x8) (bn_buf x8))) with (bn_mag x8). replace (bn_mag x8 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      eapply hoare_mono.
      { apply BN_sub_word_spec; [rewrite length_setbn; exact VRi|exact NR1|unfold BW; lia| | |];
          rewrite getbn_setbn_same by exact VRi; [exact (proj1 C8)|exact S8|lia]. }
      intros [] s9 _ (x9 & -> & (M9 & N9 & S9 & T9)). rewrite getbn_setbn_same in M9, T9 by exact VRi.
      pose proof (mont_n0_fact (bn_mag r7) b0 Hb0 HRb HRm) as KF. cbv zeta in KF. destruct KF as (K1 & K2 & K3).
      exists (bn_mag r7 * 2 ^ 64 / b0), x9.
      split; [reflexivity|]. split; [exact N9|]. split; [exact S9|]. split; [lia|]. split; [rewrite M9, M8, K1; lia|]. split; [exact K2|exact K3]. }
  intros [] s9 Hs9 (K & x9 & -> & N9 & S9 & T9 & M9 & HK & HKm). rewrite setbn_setbn_same.
  apply (montset_tailC_spec rmod rRi F s _ K Hs Hpre).
  - apply mset_frame_setbn; [exact F7|left; exact HRi].
  - eapply mset_N_eq; [|exact N7]. apply getbn_setbn_other. exact D2.
  - rewrite getbn_setbn_other by exact D4. exact T7.
  - rewrite getbn_setbn_same by exact VRi. split; [exact N9|]. split; [exact S9|]. split; [exact T9|exact M9].
  - exact HK.
  - exact HKm.
Qed.

Lemma BN_MONT_CTX_set_spec : forall rmod F s,
  montset_pre rmod s ->
  hoare F s (BN_MONT_CTX_set ops rmod) (montset_post s (bn_mag (getbn rmod s)) (bn_top (getbn rmod s))).
Proof.
  intros rmod F s Hpre. pose proof Hpre as (Lm & NmN & NmRR & NmT & Hdepth & Hpool & ET & (Nm & Tm & Om)).
  apply hoare_wf. intros Hs. unfold BN_MONT_CTX_set. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid _ _ Hs Lm) as Vm. unfold live in Lm. fold u in Lm.
  set (m := getbn rmod s) in *. set (N := bn_mag m) in *. set (nl := bn_top m) in *. set (b0 := nth 0 (bn_buf m) 0).
  pose proof (st_wf_okv rmod s Hs Vm) as Okm. fold m in Okm.
  assert (Lb0 : limb b0) by (apply limbs_nth; destruct Okm as [H _]; exact H).
  assert (Ob0 : Z.odd b0 = true).
  { pose proof (is_odd_pure_spec m Okm) as E. fold N in E. rewrite Om in E. unfold is_odd_pure in E.
    destruct (Nat.ltb_spec 0 (bn_top m)); [|lia]. cbn [andb] in E. fold b0 in E. exact E. }
  assert (Hb0 : b0 <> 0) by (intros E; rewrite E in Ob0; discriminate).
  assert (HN1 : 1 <= N).
  { pose proof (okv_mag_nonneg _ Okm) as H0. fold N in H0. destruct (Z.eq_dec N 0) as [E|]; [rewrite E in Om; discriminate|lia]. }
  assert (HNlt : N < Bp nl) by (apply okv_mag_lt; exact Okm).
  assert (HNge : Bp (nl - 1) <= N) by (apply okv_mag_ge; [exact Okm|exact Nm|lia]).
  assert (DD : RMontN <> ROne /\ RMontRR <> ROne /\ RTmod <> ROne /\ ndiff RMontRR RMontN /\ ndiff RMontRR RTmod /\ ndiff RMontN RTmod).
  { unfold ndiff, RMontN, RMontRR, RTmod, ROne. repeat split; lia. }
  destruct DD as (NN1 & NRR1 & NT1 & D5 & D6 & D7).
  apply hoare_bind_get. fold m. unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top m) 0) as [|_]; [lia|].

  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros rRi s1 Hs1 (ErRi & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in ErRi, Eu1. rewrite Ef0 in Ef1. rewrite Eb0 in Len1.
  assert (G1 : forall x, x <> rRi -> getbn x s1 = getbn x s) by (intros x Hx; rewrite (Oth1 x Hx); unfold getbn; rewrite Eb0; reflexivity).
  assert (V1 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s1))%nat).
  { intros x Hx. apply live_valid; [exact Hs1|]. unfold live. rewrite Eu1. exact Hx. }
  assert (NR1 : rRi <> ROne) by (rewrite ErRi; unfold RPool, ROne, NFIX; lia).
  assert (HRi : (NFIX + u <= rRi)%nat) by (rewrite ErRi; unfold RPool; lia).
  assert (D1 : rmod <> rRi) by lia.
  assert (D2 : rRi <> RMontN) by (unfold RMontN, NFIX in *; lia).
  assert (D3 : rRi <> RMontRR) by (unfold RMontRR, NFIX in *; lia).
  assert (D4 : rRi <> RTmod) by (unfold RTmod, NFIX in *; lia).

  eapply hoare_bind; [apply BN_copy_spec; [apply V1; unfold RMontN, NFIX; lia|exact NN1|apply V1; lia]|].
  intros [] s2 Hs2 (n2 & -> & (Tn2 & Sn2 & Fn2)).
  rewrite (G1 rmod D1) in Tn2, Sn2, Fn2. fold m in Tn2, Sn2, Fn2. fold nl in Tn2, Fn2.
  pose proof (mag_of_firstn_eq n2 m Tn2 Fn2) as Mn2. pose proof (norm_of_firstn_eq n2 m Tn2 Fn2 Nm) as Nn2.
  assert (Bn2 : nth 0 (bn_buf n2) 0 = b0) by (unfold b0; apply (nth_of_firstn_eq _ _ nl); [exact Fn2|lia]).
  eapply hoare_bind.
  { apply (set_neg_spec RMontN false F (setbn RMontN n2 s1) (fun b => b = bn_with_neg n2 false));
      [rewrite length_setbn; apply V1; unfold RMontN, NFIX; lia|exact NN1|].
    rewrite getbn_setbn_same by (apply V1; unfold RMontN, NFIX; lia). reflexivity. }
  intros [] s3 Hs3 (n3 & -> & ->). rewrite setbn_setbn_same.

  eapply hoare_bind; [apply BN_num_bits_spec; rewrite length_setbn; apply V1; lia|].
  intros nb s3 _ [-> ->]. rewrite getbn_setbn_other by (exact (ndiff_sym _ _ NmN)). rewrite (G1 rmod D1). fold m.
  pose proof (num_bits_pure_spec m Okm Nm) as (NB1 & NB2 & NB3 & NB4). specialize (NB3 ltac:(lia)). fold N nl in NB3, NB4.
  assert (Hnl : (num_bits_pure m + 63) / 64 = Z.of_nat nl).
  { apply div64_limbs. split; [|lia]. destruct (Z.lt_ge_cases (64 * (Z.of_nat nl - 1)) (num_bits_pure m)) as [|Hge]; [assumption|exfalso].
    assert (2 ^ num_bits_pure m <= Bp (nl - 1)); [|lia]. rewrite Bp_pow2. apply Z.pow_le_mono_r; lia. }
  cbv zeta. rewrite Hnl. replace (Z.of_nat nl * 64) with (64 * Z.of_nat nl) by lia.
  apply (hoare_bind_getst_setmont (fun _ => 64 * Z.of_nat nl) (fun st => st_n0 st)). cbn beta.
  match goal with |- hoare _ ?st _ _ => set (s4 := st) end.
  assert (F4 : mset_frame s s4 rRi (64 * Z.of_nat nl)).
  { unfold mset_frame, s4. rewrite st_ctx_set_mont, st_bns_set_mont, st_ctx_setbn, length_setbn.
    split; [exact ErRi|]. split; [exact Eu1|]. split; [exact Ef1|]. split; [exact Len1|]. split.
    - intros x Hx H1 H2 H3. rewrite getbn_set_mont. rewrite getbn_setbn_other by (intros E; apply H1; symmetry; exact E). apply G1. lia.
    - cbn [set_mont setbn set_bns st_ri st_rbits st_rshift]. split; [reflexivity|].
      destruct Sc1 as (_ & _ & S3 & S4). destruct Sc0 as (_ & _ & S3' & S4'). rewrite S3, S4, S3', S4'. split; reflexivity. }
  assert (N4 : mset_N s s4 rmod).
  { unfold mset_N, s4. rewrite getbn_set_mont, getbn_setbn_same by (apply V1; unfold RMontN, NFIX; lia). fold m.
    split; [exact Tn2|]. split; [reflexivity|]. split; [exact Mn2|]. split; [exact Nn2|exact Bn2]. }
  assert (V4 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s4))%nat) by (intros x Hx; unfold s4; rewrite st_bns_set_mont, length_setbn; apply V1; exact Hx).
  assert (Em4 : getbn rmod s4 = m) by (unfold s4; rewrite getbn_set_mont, getbn_setbn_other by (exact (ndiff_sym _ _ NmN)); apply G1; exact D1).
  assert (ET4 : getbn RTmod s4 = bn_nil 0).
  { unfold s4. rewrite getbn_set_mont, getbn_setbn_other by exact D7. rewrite G1 by (intros E; apply D4; symmetry; exact E). exact ET. }

  eapply hoare_bind; [apply BN_zero_spec; [apply V4; unfold RMontRR, NFIX; lia|exact NRR1]|].
  intros [] s5 Hs5 (rr5 & -> & (Trr5 & Srr5)).
  eapply hoare_bind.
  { apply BN_set_bit_zero_spec; [rewrite length_setbn; apply V4; unfold RMontRR, NFIX; lia|exact NRR1|lia|replace (64 / 64) with 1 by reflexivity; unfold BG_DMAX; lia|].
    rewrite getbn_setbn_same by (apply V4; unfold RMontRR, NFIX; lia). exact Trr5. }
  intros [] s6 Hs6 (rr6 & -> & (Mrr6 & Nrr6 & Trr6 & Srr6)).
  rewrite getbn_setbn_same in Srr6 by (apply V4; unfold RMontRR, NFIX; lia). rewrite Srr5 in Srr6. rewrite setbn_setbn_same.
  replace (Z.to_nat (64 / 64) + 1)%nat with 2%nat in Trr6 by reflexivity.
  set (s6 := setbn RMontRR rr6 s4) in *.
  pose proof (mset_frame_setbn s s4 rRi _ RMontRR rr6 F4 ltac:(right; right; left; reflexivity)) as F6. fold s6 in F6.
  assert (V6 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s6))%nat) by (intros x Hx; unfold s6; rewrite length_setbn; apply V4; exact Hx).
  assert (Em6 : getbn rmod s6 = m) by (unfold s6; rewrite getbn_setbn_other by (exact (ndiff_sym _ _ NmRR)); exact Em4).
  assert (ET6 : getbn RTmod s6 = bn_nil 0) by (unfold s6; rewrite getbn_setbn_other by exact D6; exact ET4).
  assert (N6 : mset_N s s6 rmod) by (eapply mset_N_eq; [unfold s6; apply getbn_setbn_other; exact D5|exact N4]).
  assert (ERR6 : getbn RMontRR s6 = rr6) by (unfold s6; apply getbn_setbn_same; apply V4; unfold RMontRR, NFIX; lia).

  apply hoare_bind_get. rewrite Em6. destruct (Nat.eqb_spec (bn_top m) 0) as [|_]; [lia|]. cbv zeta. fold b0.
  replace (if b0 =? 0 then 0%nat else 1%nat) with 1%nat by (destruct (Z.eqb_spec b0 0); [lia|reflexivity]).
  change (mkBN None [b0; 0] 1%nat false 0) with (tmod b0).
  eapply hoare_bind_set_nod; [apply V6; unfold RTmod, NFIX; lia|exact NT1|apply tmod_ok; exact Lb0|reflexivity|rewrite ET6; reflexivity|rewrite ET6; reflexivity|].
  set (s7 := setbn RTmod (tmod b0) s6) in *.
  pose proof (mset_frame_setbn s s6 rRi _ RTmod (tmod b0) F6 ltac:(right; right; right; reflexivity)) as F7. fold s7 in F7.
  pose proof F7 as (_ & Eu7 & Ef7 & _).
  assert (V7 : forall x, (x < NFIX + S u)%nat -> (x < length (st_bns s7))%nat) by (intros x Hx; unfold s7; rewrite length_setbn; apply V6; exact Hx).
  assert (ET7 : getbn RTmod s7 = tmod b0) by (unfold s7; apply getbn_setbn_same; apply V6; unfold RTmod, NFIX; lia).
  assert (N7 : mset_N s s7 rmod) by (eapply mset_N_eq; [unfold s7; apply getbn_setbn_other; exact (ndiff_sym _ _ D7)|exact N6]).
  assert (ERR7 : getbn RMontRR s7 = rr6) by (unfold s7; rewrite getbn_setbn_other by (exact (ndiff_sym _ _ D6)); exact ERR6).

  apply hoare_bind_get. rewrite ET7, tmod_is_one.
  eapply hoare_bind with (R := fun _ s8 => mset_frame s s8 rRi (64 * Z.of_nat nl) /\ mset_N s s8 rmod /\ getbn RTmod s8 = tmod b0 /\
     (let r := getbn rRi s8 in bn_canon r /\ bn_neg r = false /\ (bn_top r <= 1)%nat /\
      ((b0 = 1 /\ bn_mag r = 0) \/ (1 < b0 /\ 0 <= bn_mag r < b0 /\ (bn_mag r * 2 ^ 64) mod b0 = 1)))).
  { destruct (Z.eqb_spec b0 1) as [Eb01|Hb1].
    - eapply hoare_mono; [apply BN_zero_spec; [apply V7; rewrite ErRi; unfold RPool; lia|exact NR1]|].
      intros [] s8 _ (r8 & -> & (Tr8 & Sr8)). split; [apply mset_frame_setbn; [exact F7|left; exact HRi]|].
      split; [eapply mset_N_eq; [apply getbn_setbn_other; exact D2|exact N7]|].
      split; [rewrite getbn_setbn_other by exact D4; exact ET7|]. cbv zeta. rewrite getbn_setbn_same by (apply V7; rewrite ErRi; unfold RPool; lia).
      split; [split; [left; exact Tr8|intros _; exact Sr8]|]. split; [exact Sr8|]. split; [rewrite Tr8; lia|].
      left. split; [exact Eb01|apply bn_mag_top0; exact Tr8].
    - assert (Hb1' : 1 < b0) by (destruct Lb0; lia).
      eapply hoare_mono.
      { apply BN_mod_inverse_spec. unfold modinv_pre, live. rewrite Eu7, Ef7, ERR7, ET7, tmod_mag, length_app. cbn [length].
        split; [rewrite ErRi; unfold RPool; lia|]. split; [unfold RMontRR, NFIX; lia|]. split; [unfold RTmod, NFIX; lia|].
        split; [exact NR1|]. split; [exact D4|]. split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split.
        + split; [apply tmod_norm; exact Hb0|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ob0|exact Hb1'].
        + split; [exact Nrr6|]. split; [exact Srr6|]. split; [rewrite Trr6; lia|]. rewrite Mrr6. apply gcd_pow2_odd; [lia|exact Ob0]. }
      intros [] s8 _ (K8 & P8). cbv zeta in P8. rewrite ERR7, ET7, tmod_mag, Mrr6 in P8. destruct P8 as (C8 & S8 & M8 & T8 & I8).
      rewrite Eu7 in K8.
      split; [eapply mset_frame_keeps; [exact F7|exact K8|intros r [<-|[]]; left; exact HRi]|].
      split; [eapply mset_N_eq; [apply (keeps_get _ _ _ _ RMontN K8); [unfold RMontN, NFIX; lia|intros [E|[]]; apply D2; exact E]|exact N7]|].
      split; [rewrite <- ET7; apply (keeps_get _ _ _ _ RTmod K8); [unfold RTmod, NFIX; lia|intros [E|[]]; apply D4; exact E]|].
      cbv zeta. split; [exact C8|]. split; [exact S8|]. split; [exact T8|]. right. split; [exact Hb1'|]. split; [exact M8|exact I8]. }
  intros [] s8 Hs8 (F8 & N8 & T8 & R8).
  apply (montset_tailB_spec rmod rRi F s s8 Hs Hpre F8 N8 T8 R8).
Qed.

End MontSpec2.
