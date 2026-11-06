(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63Axioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxNum FxCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma sgn64_eqmN : forall k, eqm (sgn64 k) k.
Proof.
  intros k. unfold sgn64, eqm. destruct (Z.ltb k T63); [reflexivity|].
  replace (k - two64) with (k + (-1) * two64) by lia. rewrite Z.mod_add by (unfold two64; lia). reflexivity.
Qed.
Lemma mod64_neg : forall v, - two64 <= v < 0 -> v mod two64 = v + two64.
Proof.
  intros v H. unfold two64 in *. rewrite <- (Z.mod_small (v + 18446744073709551616) 18446744073709551616) by lia.
  replace (v + 18446744073709551616) with (v + 1 * 18446744073709551616) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma sgn64_unique : forall x v, 0 <= x < two64 -> eqm x v -> - T63 <= v < T63 -> sgn64 x = v.
Proof.
  intros x v Hx He Hv. unfold eqm in He. rewrite (Z.mod_small x) in He by exact Hx. unfold sgn64.
  destruct (Z.leb_spec 0 v).
  - rewrite (Z.mod_small v) in He by (unfold T63, two64 in *; lia). subst x. destruct (Z.ltb_spec v T63); lia.
  - rewrite mod64_neg in He by (unfold T63, two64 in *; lia). subst x. unfold T63, two64 in *.
    destruct (Z.ltb_spec (v + 18446744073709551616) 9223372036854775808); lia.
Qed.
Lemma sgn64_w64_add : forall a b, - T63 <= sgn64 a + sgn64 b < T63 -> sgn64 (w64 (a + b)) = sgn64 a + sgn64 b.
Proof.
  intros a b H. apply sgn64_unique; [apply w64_range| |exact H].
  eapply eqm_trans; [apply eqm_w64|]. apply eqm_sym, eqm_add; apply sgn64_eqmN.
Qed.
Lemma eqm_small0 : forall v, - two64 < v < two64 -> eqm v 0 -> v = 0.
Proof.
  intros v Hv H. unfold eqm in H. rewrite Zmod_0_l in H. destruct (Z.leb_spec 0 v).
  - rewrite Z.mod_small in H by lia. exact H.
  - rewrite mod64_neg in H by lia. lia.
Qed.
Lemma w64_add_eq0 : forall a b, - two64 < sgn64 a + sgn64 b < two64 -> Z.eqb (w64 (a + b)) 0 = Z.eqb (sgn64 a + sgn64 b) 0.
Proof.
  intros a b H. destruct (Z.eqb_spec (sgn64 a + sgn64 b) 0) as [E|E].
  - apply Z.eqb_eq. rewrite w64_mod. assert (Hm : eqm (a + b) 0).
    { eapply eqm_trans; [apply eqm_add; apply eqm_sym, sgn64_eqmN|]. rewrite E. apply eqm_refl. }
    unfold eqm in Hm. rewrite Hm. reflexivity.
  - apply Z.eqb_neq. intros Hz. apply E. apply eqm_small0; [exact H|].
    eapply eqm_trans; [apply eqm_add; apply sgn64_eqmN|]. eapply eqm_trans; [apply eqm_sym, eqm_w64|]. rewrite Hz. apply eqm_refl.
Qed.
Lemma negw_range : forall c, 0 <= negw c < two64.
Proof. intros c. unfold negw. pose proof (w64_range c). destruct (Z.eqb_spec (w64 c) 0); unfold two64 in *; lia. Qed.
Lemma eqm_negw : forall c, eqm (negw c) (- c).
Proof.
  intros c. rewrite negw_eq. eapply eqm_trans; [apply eqm_w64|]. unfold eqm.
  replace (M64 * c) with (- c + c * two64) by (unfold M64, two64; lia). rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma eqm_opp : forall a b, eqm a b -> eqm (- a) (- b).
Proof.
  intros a b H. replace (- a) with (-1 * a) by lia. replace (- b) with (-1 * b) by lia. apply eqm_mul; [apply eqm_refl | exact H].
Qed.
Lemma sgn64_negw : forall c, - T63 < sgn64 c < T63 -> sgn64 (negw c) = - sgn64 c.
Proof.
  intros c H. apply sgn64_unique; [apply negw_range| |lia].
  eapply eqm_trans; [apply eqm_negw|]. apply eqm_opp, eqm_sym, sgn64_eqmN.
Qed.
Lemma negw_eq0 : forall c, - two64 < sgn64 c < two64 -> Z.eqb (negw c) 0 = Z.eqb (sgn64 c) 0.
Proof.
  intros c H. unfold negw. destruct (Z.eqb_spec (w64 c) 0) as [E|E].
  - assert (Hs : sgn64 c = 0).
    { apply eqm_small0; [exact H|]. eapply eqm_trans; [apply sgn64_eqmN|]. eapply eqm_trans; [apply eqm_sym, eqm_w64|]. rewrite E. apply eqm_refl. }
    rewrite Hs. reflexivity.
  - pose proof (w64_range c). destruct (Z.eqb_spec (two64 - w64 c) 0) as [E'|E']; [lia|].
    symmetry. apply Z.eqb_neq. intros Hs. apply E. rewrite w64_mod. pose proof (sgn64_eqmN c) as Hm. unfold eqm in Hm. rewrite <- Hm, Hs. reflexivity.
Qed.
Lemma k2c_sgn : forall k c, k2c k = Some c -> ival c = sgn64 k /\ Z.abs (ival c) < 1152921504606846976.
Proof.
  intros k c H. apply k2c_spec in H as [[Hk Hc]|[Hk Hc]]; rewrite Hc; unfold sgn64, T63.
  - destruct (Z.ltb_spec k 9223372036854775808); [|lia]. split; [reflexivity | lia].
  - destruct (Z.ltb_spec k 9223372036854775808); [lia|]. unfold two64. split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma ival_add_s : forall x y, small x -> small y -> ival (PrimInt63.add x y) = ival x + ival y.
Proof. intros x y Hx Hy. apply ival_add. unfold small in *. lia. Qed.
Lemma ival_sub_s : forall x y, small x -> small y -> ival (PrimInt63.sub x y) = ival x - ival y.
Proof. intros x y Hx Hy. apply ival_sub. unfold small in *. lia. Qed.
Lemma small_i0 : small i0. Proof. unfold small. rewrite ival_i0. lia. Qed.
Lemma max_if : forall x y, Z.max x y = if Z.ltb x y then y else x.
Proof. intros x y. destruct (Z.ltb_spec x y); lia. Qed.
Lemma min_if : forall x y, Z.min x y = if Z.ltb y x then y else x.
Proof. intros x y. destruct (Z.ltb_spec y x); lia. Qed.

(* [comment removed for export] *)
Definition wok (w : wiv) (r : Z * Z) : Prop :=
  small (w_al w) /\ small (w_bl w) /\ small (w_ah w) /\ small (w_bh w) /\ wv (w_al w) (w_bl w) = fst r /\ wv (w_ah w) (w_bh w) = snd r.
Lemma wok_wiv2z : forall w r, wok w r -> wiv2z w = r.
Proof. intros [al bl ah bh] [lo hi] (_ & _ & _ & _ & H1 & H2). unfold wiv2z. cbn [fst snd w_al w_bl w_ah w_bh] in *. rewrite H1, H2. reflexivity. Qed.

Lemma wlt_iff : forall a1 b1 a2 b2, small a1 -> small a2 -> wlt a1 b1 a2 b2 = Z.ltb (wv a1 b1) (wv a2 b2).
Proof.
  intros a1 b1 a2 b2 H1 H2. destruct (wlt a1 b1 a2 b2) eqn:E; symmetry.
  - apply Z.ltb_lt. apply (wlt_spec a1 b1 a2 b2 H1 H2). exact E.
  - apply Z.ltb_ge. apply (wlt_false a1 b1 a2 b2 H1 H2). exact E.
Qed.

Lemma wok_intro : forall al bl ah bh r, small al -> small bl -> small ah -> small bh -> wv al bl = fst r -> wv ah bh = snd r -> wok (WI al bl ah bh) r.
Proof. intros. unfold wok. cbn [w_al w_bl w_ah w_bh]. tauto. Qed.
Lemma wv_sub : forall a1 b1 a2 b2, small a1 -> small b1 -> small a2 -> small b2 -> wv (PrimInt63.sub a1 a2) (PrimInt63.sub b1 b2) = wv a1 b1 - wv a2 b2.
Proof. intros. unfold wv. rewrite !ival_sub_s by assumption. lia. Qed.
Lemma wv_add : forall a1 b1 a2 b2, small a1 -> small b1 -> small a2 -> small b2 -> wv (PrimInt63.add a1 a2) (PrimInt63.add b1 b2) = wv a1 b1 + wv a2 b2.
Proof. intros. unfold wv. rewrite !ival_add_s by assumption. lia. Qed.
Lemma wv_i0_i4 : wv i0 i4 = two64. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wmeet_win_ok : forall acc c A C r, wok acc A -> wok c C -> wmeet_win acc c = Some r -> wok r (meet_win A C).
Proof.
  intros [aal abl aah abh] [cal cbl cah cbh] [A1 A2] [C1 C2] r
         (Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6) (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6) H.
  cbn [w_al w_bl w_ah w_bh fst snd] in *. unfold wmeet_win in H. cbv beta iota zeta in H.
  rewrite (wlt_iff aah abh cah cbh Ha3 Hc3), (wlt_iff cal cbl aal abl Hc1 Ha1), Ha6, Hc6, Ha5, Hc5 in H.
  unfold meet_win, window, iv_meet. cbn [fst snd].
  destruct (Z.ltb_spec A2 C2) as [Eh|Eh]; destruct (Z.ltb_spec C1 A1) as [El|El]; cbv beta iota in H;
  repeat match type of H with context [smallb ?t] => let E := fresh "S" in destruct (smallb t) eqn:E; [apply smallb_true in E|] end;
  try discriminate H;
  repeat match type of H with
  | context [wlt ?a1 ?b1 ?a2 ?b2] => rewrite (wlt_iff a1 b1 a2 b2 ltac:(assumption) ltac:(first [assumption | exact small_i0])) in H
  end;
  rewrite ?wv_sub in H by assumption; rewrite ?wv_i0_i4 in H; rewrite ?Ha5, ?Ha6, ?Hc5, ?Hc6 in H;
  repeat (first [rewrite Z.max_r by lia | rewrite Z.max_l by lia]); repeat (first [rewrite Z.min_r by lia | rewrite Z.min_l by lia]);
  repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) end;
  try discriminate H; injection H as <-; apply wok_intro; cbn [fst snd]; assumption || lia.
Qed.

(* [comment removed for export] *)
Definition vok (e : ventry) (r : Z * Z) : Prop :=
  small (v_al e) /\ small (v_bl e) /\ small (v_ah e) /\ small (v_bh e) /\ wv (v_al e) (v_bl e) = fst r /\ wv (v_ah e) (v_bh e) = snd r /\
  to_Z (v_h e) <= to_Z (PrimInt63.head0 (iabs (v_al e))) /\ to_Z (v_h e) <= to_Z (PrimInt63.head0 (iabs (v_bl e))) /\
  to_Z (v_h e) <= to_Z (PrimInt63.head0 (iabs (v_ah e))) /\ to_Z (v_h e) <= to_Z (PrimInt63.head0 (iabs (v_bh e))).
Lemma vok_intro : forall al bl ah bh h r, small al -> small bl -> small ah -> small bh -> wv al bl = fst r -> wv ah bh = snd r ->
  to_Z h <= to_Z (PrimInt63.head0 (iabs al)) -> to_Z h <= to_Z (PrimInt63.head0 (iabs bl)) ->
  to_Z h <= to_Z (PrimInt63.head0 (iabs ah)) -> to_Z h <= to_Z (PrimInt63.head0 (iabs bh)) -> vok (VE al bl ah bh h) r.
Proof. intros. unfold vok. cbn [v_al v_bl v_ah v_bh v_h]. tauto. Qed.
Lemma mk_ve_ok : forall r e, mk_ve r = Some e -> vok e r.
Proof.
  intros [lo hi] e H. unfold mk_ve in H. cbn [fst snd] in H.
  destruct (z2w lo) as [[al bl]|] eqn:E1; [|discriminate]. destruct (z2w hi) as [[ah bh]|] eqn:E2; [|discriminate].
  injection H as <-. apply z2w_spec in E1 as (H1 & H2 & H3). apply z2w_spec in E2 as (H4 & H5 & H6).
  pose proof (imin_le (PrimInt63.head0 (iabs al)) (PrimInt63.head0 (iabs bl))) as [M1 M2].
  pose proof (imin_le (PrimInt63.head0 (iabs ah)) (PrimInt63.head0 (iabs bh))) as [M3 M4].
  pose proof (imin_le (imin (PrimInt63.head0 (iabs al)) (PrimInt63.head0 (iabs bl))) (imin (PrimInt63.head0 (iabs ah)) (PrimInt63.head0 (iabs bh)))) as [M5 M6].
  apply vok_intro; cbn [fst snd]; try assumption; lia.
Qed.

Section Conv.
Variables (ne all bfs mfs : list fact).
Definition tok (B : Z) (ct : cterm) (t : positive * Z) : Prop :=
  ct_x ct = fst t /\ ival (ct_c ct) = sgn64 (snd t) /\ Z.abs (ival (ct_c ct)) < B /\ vok (ct_e ct) (IrN.vrangeN ne all bfs (fst t)).
#[using="Type"] Lemma tok_intro : forall B x c e t, x = fst t -> ival c = sgn64 (snd t) -> Z.abs (ival c) < B -> vok e (IrN.vrangeN ne all bfs (fst t)) -> tok B (CT x c e) t.
Proof. intros. unfold tok. cbn [ct_x ct_c ct_e]. tauto. Qed.
Definition clok (cl : clin) (l : lin) : Prop :=
  ival (cl_c cl) = sgn64 (l_c l) /\ Z.abs (ival (cl_c cl)) < 1152921504606846976 /\ Forall2 (tok 1152921504606846976) (cl_t cl) (l_t l).
Definition Tok (T : tree ventry) : Prop := forall x e, tget x T = Some e -> vok e (IrN.vrangeN ne all bfs x).

#[using="Type"] Lemma tok_weak : forall B B' ct t, B <= B' -> Forall2 (tok B) ct t -> Forall2 (tok B') ct t.
Proof.
  intros B B' ct t HB H. induction H as [|a b ct t Hab _ IH]; constructor; [|exact IH].
  destruct a as [x c e]. destruct Hab as (H1 & H2 & H3 & H4). cbn [ct_x ct_c ct_e] in *. apply tok_intro; try assumption. lia.
Qed.
#[using="Type"] Lemma tok_weak1 : forall B B' c t, B <= B' -> tok B c t -> tok B' c t.
Proof. intros B B' [x c e] t HB (H1 & H2 & H3 & H4). cbn [ct_x ct_c ct_e] in *. apply tok_intro; try assumption. lia. Qed.
#[using="Type"] Lemma Tok_empty : Tok TEmpty.
Proof. intros x e H. destruct x; cbn in H; discriminate. Qed.
#[using="Type"] Lemma get_ve_ok : forall T x T' e, Tok T -> IrN.get_ve ne all bfs T x = Some (T', e) -> Tok T' /\ vok e (IrN.vrangeN ne all bfs x).
Proof.
  intros T x T' e HT H. unfold IrN.get_ve in H. destruct (tget x T) as [e0|] eqn:Eg.
  - injection H as <- <-. split; [exact HT | exact (HT x e0 Eg)].
  - destruct (mk_ve (IrN.vrangeN ne all bfs x)) as [e0|] eqn:Em; [|discriminate]. injection H as <- <-.
    apply mk_ve_ok in Em. split; [|exact Em].
    intros y e1 Hy. destruct (Pos.eq_dec x y) as [<-|Hne].
    + rewrite tget_tset_same in Hy. injection Hy as <-. exact Em.
    + rewrite tget_tset_other in Hy by exact Hne. exact (HT y e1 Hy).
Qed.
#[using="Type"] Lemma conv_t_ok : forall t T T' ct, Tok T -> IrN.conv_t ne all bfs T t = Some (T', ct) -> Tok T' /\ Forall2 (tok 1152921504606846976) ct t.
Proof.
  induction t as [|[x k] t IH]; intros T T' ct HT H; cbn [IrN.conv_t] in H.
  - injection H as <- <-. split; [exact HT | constructor].
  - destruct (k2c k) as [c|] eqn:Ek; [|discriminate]. destruct (IrN.get_ve ne all bfs T x) as [[T1 e]|] eqn:Eg; [|discriminate].
    destruct (IrN.conv_t ne all bfs T1 t) as [[T2 r]|] eqn:Ec; [|discriminate]. injection H as <- <-.
    apply get_ve_ok in Eg as [HT1 He]; [|exact HT]. apply IH in Ec as [HT2 Hr]; [|exact HT1].
    split; [exact HT2|]. constructor; [|exact Hr].
    apply k2c_sgn in Ek as [Ec1 Ec2]. apply tok_intro; cbn [fst snd]; try reflexivity; assumption.
Qed.
#[using="Type"] Lemma conv_l_ok : forall T l T' cl, Tok T -> IrN.conv_l ne all bfs T l = Some (T', cl) -> Tok T' /\ clok cl l.
Proof.
  intros T l T' cl HT H. unfold IrN.conv_l in H. destruct (k2c (l_c l)) as [c|] eqn:Ek; [|discriminate].
  destruct (IrN.conv_t ne all bfs T (l_t l)) as [[T1 t]|] eqn:Ec; [|discriminate]. injection H as <- <-.
  apply conv_t_ok in Ec as [HT1 Ht]; [|exact HT]. apply k2c_sgn in Ek as [E1 E2].
  split; [exact HT1|]. unfold clok. cbn [cl_c cl_t]. split; [exact E1|]. split; [exact E2 | exact Ht].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ct_neg_ok : forall ct t, Forall2 (tok 1152921504606846976) ct t -> Forall2 (tok 1152921504606846976) (ct_neg ct) (tneg t).
Proof.
  intros ct t H. induction H as [|[x c e] [y k] ct t Hab _ IH]; [constructor|]. cbn [ct_neg tneg].
  destruct Hab as (Hx & Hc & HB & He). cbn [ct_x ct_c ct_e fst snd] in *. subst y.
  assert (Hs : - T63 < sgn64 k < T63) by (unfold T63; lia).
  rewrite (negw_eq0 k) by (unfold two64; lia). rewrite <- Hc.
  destruct (PrimInt63.eqb c i0) eqn:E0.
  - apply Uint63Axioms.eqb_correct in E0. subst c. rewrite ival_i0. cbn. exact IH.
  - assert (Hn : ival c <> 0). { intros Hz. assert (c = i0) by (apply ival_inj; rewrite Hz; reflexivity). subst c. rewrite Uint63Axioms.eqb_refl in E0. discriminate. }
    destruct (Z.eqb_spec (ival c) 0) as [Hz|_]; [contradiction|]. constructor; [|exact IH].
    apply tok_intro; cbn [fst snd]; try reflexivity; try exact He;
      rewrite ival_sub by (rewrite ival_i0; lia); rewrite ival_i0; [rewrite sgn64_negw by exact Hs|]; lia.
Qed.
#[using="Type"] Lemma ct_add_cons_cons : forall ta a tb b, ct_add (ta :: a) (tb :: b) =
  match Pos.compare (ct_x ta) (ct_x tb) with
  | Eq => let k := PrimInt63.add (ct_c ta) (ct_c tb) in if PrimInt63.eqb k i0 then ct_add a b else CT (ct_x ta) k (ct_e ta) :: ct_add a b
  | Lt => ta :: ct_add a (tb :: b)
  | Gt => tb :: ct_add (ta :: a) b
  end.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ct_add_nil_r : forall a, ct_add a [] = a.
Proof. intros [|ta a]; reflexivity. Qed.
#[using="Type"] Lemma ct_add_ok : forall ca a cb b, Forall2 (tok 1152921504606846976) ca a -> Forall2 (tok 1152921504606846976) cb b ->
  Forall2 (tok 2305843009213693952) (ct_add ca cb) (tadd a b).
Proof.
  intros ca a cb b H1. revert cb b. induction H1 as [|ta [x kx] ca a Hta Hca IH]; intros cb b H2.
  - cbn. eapply tok_weak; [|exact H2]. lia.
  - induction H2 as [|tb [y ky] cb b Htb Hcb IH2].
    + rewrite ct_add_nil_r, tadd_nil_r. eapply tok_weak; [|constructor; eassumption]. lia.
    + rewrite ct_add_cons_cons, tadd_cons_cons.
      pose proof Hta as (Hx & Hc1 & HB1 & He1). pose proof Htb as (Hy & Hc2 & HB2 & He2). cbn [fst snd] in *. rewrite Hx, Hy.
      destruct (Pos.compare_spec x y) as [<-|Hlt|Hgt].
      * cbv zeta. assert (Hs : ival (PrimInt63.add (ct_c ta) (ct_c tb)) = sgn64 kx + sgn64 ky).
        { rewrite ival_add by lia. lia. }
        rewrite (w64_add_eq0 kx ky) by (unfold two64; lia).
        destruct (PrimInt63.eqb (PrimInt63.add (ct_c ta) (ct_c tb)) i0) eqn:E0.
        -- apply Uint63Axioms.eqb_correct in E0. rewrite E0, ival_i0 in Hs. rewrite <- Hs. cbn [Z.eqb]. apply IH. exact Hcb.
        -- assert (Hn : sgn64 kx + sgn64 ky <> 0).
           { intros Hz. rewrite Hz in Hs. assert (PrimInt63.add (ct_c ta) (ct_c tb) = i0) by (apply ival_inj; rewrite Hs; reflexivity).
             rewrite H, Uint63Axioms.eqb_refl in E0. discriminate. }
           destruct (Z.eqb_spec (sgn64 kx + sgn64 ky) 0) as [Hz|_]; [contradiction|]. constructor; [|apply IH; exact Hcb].
           apply tok_intro; cbn [fst snd]; try reflexivity; try assumption; [rewrite sgn64_w64_add by (unfold T63; lia); exact Hs | lia].
      * constructor; [eapply tok_weak1; [|exact Hta]; lia|]. apply IH. constructor; assumption.
      * constructor; [eapply tok_weak1; [|exact Htb]; lia|]. exact IH2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mul_ok : forall c L h, to_Z h <= to_Z (PrimInt63.head0 (iabs L)) -> PrimInt63.leb i65 (PrimInt63.add (PrimInt63.head0 (iabs c)) h) = true ->
  ival (PrimInt63.mul c L) = ival c * ival L /\ small (PrimInt63.mul c L).
Proof.
  intros c L h Hh Hg. pose proof (mul_guard c L h Hh Hg) as Hm.
  assert (E : ival (PrimInt63.mul c L) = ival c * ival L) by (apply ival_mul; lia). split; [exact E|]. unfold small. rewrite E. lia.
Qed.
#[using="Type"] Lemma neg_spec : forall c, PrimInt63.leb B62 c = negb (Z.leb 0 (ival c)).
Proof.
  intros c. unfold ival. pose proof (to_Z_rng c). destruct (PrimInt63.leb B62 c) eqn:E.
  - apply leb_spec in E. rewrite to_Z_B62 in E. destruct (Z.ltb_spec (to_Z c) 4611686018427387904); [lia|].
    symmetry. apply negb_true_iff. apply Z.leb_gt. lia.
  - assert (to_Z c < 4611686018427387904). { destruct (Z.lt_ge_cases (to_Z c) 4611686018427387904) as [h|h]; [exact h|].
      assert (PrimInt63.leb B62 c = true) by (apply leb_spec; rewrite to_Z_B62; lia). congruence. }
    destruct (Z.ltb_spec (to_Z c) 4611686018427387904); [|lia]. symmetry. apply negb_false_iff. apply Z.leb_le. lia.
Qed.
#[using="Type"] Lemma wok_eq : forall w p q, wok w p -> p = q -> wok w q.
Proof. intros w p q H <-. exact H. Qed.
#[using="Type"] Lemma ct_iv_ok : forall B ct t al bl ah bh w, Forall2 (tok B) ct t -> small al -> small bl -> small ah -> small bh ->
  ct_iv ct al bl ah bh = Some w -> wok w (iv_add (wv al bl, wv ah bh) (IrN.t_ivN ne all bfs t)).
Proof.
  intros B ct t al bl ah bh w H. revert al bl ah bh w.
  induction H as [|[x' c e] [x k] ct t Hab Hct IH]; intros al bl ah bh w Hal Hbl Hah Hbh Hw.
  - cbn [ct_iv] in Hw. injection Hw as <-. apply wok_intro; try assumption; cbn [IrN.t_ivN iv_add fst snd]; lia.
  - cbn [ct_iv] in Hw. cbv zeta in Hw. destruct Hab as (Hx & Hc & HB & He). cbn [ct_x ct_c ct_e fst snd] in *. subst x'.
    destruct (PrimInt63.leb i65 (PrimInt63.add (PrimInt63.head0 (iabs c)) (v_h e))) eqn:Eg; [|discriminate].
    destruct e as [el1 el2 eh1 eh2 h]. cbn [v_al v_bl v_ah v_bh v_h] in *.
    destruct He as (S1 & S2 & S3 & S4 & V1 & V2 & G1 & G2 & G3 & G4). cbn [v_al v_bl v_ah v_bh v_h] in *.
    pose proof (mul_ok c el1 h G1 Eg) as [M1 T1]. pose proof (mul_ok c el2 h G2 Eg) as [M2 T2].
    pose proof (mul_ok c eh1 h G3 Eg) as [M3 T3]. pose proof (mul_ok c eh2 h G4 Eg) as [M4 T4].
    rewrite neg_spec in Hw. rewrite Hc in *. cbn [IrN.t_ivN]. destruct (IrN.vrangeN ne all bfs x) as [lo hi] eqn:Ev. cbn [fst snd] in V1, V2.
    unfold iv_scale. cbn [fst snd].
    destruct (Z.leb 0 (sgn64 k)) eqn:Es; cbn [negb] in Hw; cbv beta iota in Hw |- *;
    repeat match type of Hw with context [smallb ?t] => let E := fresh "S" in destruct (smallb t) eqn:E; [apply smallb_true in E | discriminate Hw] end;
    (eapply IH in Hw; [|assumption..]);
    (eapply wok_eq; [exact Hw|]);
    unfold iv_add; cbn [fst snd]; unfold wv in *; rewrite !ival_add_s by assumption; rewrite M1, M2, M3, M4;
    subst lo hi; f_equal; ring.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma l_ivN_lsub : forall l g, IrN.l_ivN ne all bfs (lsub l g) =
  iv_add (sgn64 (w64 (l_c l + negw (l_c g))), sgn64 (w64 (l_c l + negw (l_c g)))) (IrN.t_ivN ne all bfs (tadd (l_t l) (tneg (l_t g)))).
Proof. intros [cl tl] [cg tg]. reflexivity. Qed.
#[using="Type"] Lemma l_ivN_ladd : forall l g, IrN.l_ivN ne all bfs (ladd l g) =
  iv_add (sgn64 (w64 (l_c l + l_c g)), sgn64 (w64 (l_c l + l_c g))) (IrN.t_ivN ne all bfs (tadd (l_t l) (l_t g))).
Proof. intros [cl tl] [cg tg]. reflexivity. Qed.
#[using="Type"] Lemma wv_c0 : forall c, wv c i0 = ival c. Proof. intros c. unfold wv. rewrite ival_i0. lia. Qed.
#[using="Type"] Lemma wstep_iv_ok : forall cl cg l g loa lob hia hib acc A acc',
  clok cl l -> clok cg g -> wok acc A -> small loa -> small lob -> small hia -> small hib ->
  wstep_iv cl cg loa lob hia hib acc = Some acc' ->
  wok acc' (meet_win (meet_win A (wv loa lob + fst (IrN.l_ivN ne all bfs (lsub l g)), wv hia hib + snd (IrN.l_ivN ne all bfs (lsub l g))))
                     (fst (IrN.l_ivN ne all bfs (ladd l g)) - wv hia hib, snd (IrN.l_ivN ne all bfs (ladd l g)) - wv loa lob)).
Proof.
  intros cl cg l g loa lob hia hib acc A acc' (Cl1 & Cl2 & Cl3) (Cg1 & Cg2 & Cg3) HA Hla Hlb Hha Hhb H.
  unfold wstep_iv in H. cbv zeta in H.
  assert (Hc1 : ival (PrimInt63.sub (cl_c cl) (cl_c cg)) = sgn64 (l_c l) - sgn64 (l_c g)) by (rewrite ival_sub by lia; lia).
  assert (Hc2 : ival (PrimInt63.add (cl_c cl) (cl_c cg)) = sgn64 (l_c l) + sgn64 (l_c g)) by (rewrite ival_add by lia; lia).
  assert (Sc1 : small (PrimInt63.sub (cl_c cl) (cl_c cg))) by (unfold small; lia).
  assert (Sc2 : small (PrimInt63.add (cl_c cl) (cl_c cg))) by (unfold small; lia).
  destruct (ct_iv (ct_add (cl_t cl) (ct_neg (cl_t cg))) _ i0 _ i0) as [r1|] eqn:E1; [|discriminate].
  destruct (ct_iv (ct_add (cl_t cl) (cl_t cg)) _ i0 _ i0) as [r2|] eqn:E2; [|discriminate].
  apply (ct_iv_ok 2305843009213693952 _ (tadd (l_t l) (tneg (l_t g)))) in E1; [|apply ct_add_ok; [exact Cl3 | apply ct_neg_ok; exact Cg3] | exact Sc1 | exact small_i0 | exact Sc1 | exact small_i0].
  apply (ct_iv_ok 2305843009213693952 _ (tadd (l_t l) (l_t g))) in E2; [|apply ct_add_ok; assumption | exact Sc2 | exact small_i0 | exact Sc2 | exact small_i0].
  rewrite !wv_c0, Hc1 in E1. rewrite !wv_c0, Hc2 in E2.
  rewrite l_ivN_lsub, l_ivN_ladd.
  rewrite sgn64_w64_add by (rewrite sgn64_negw by (unfold T63; lia); unfold T63; lia). rewrite sgn64_negw by (unfold T63; lia).
  rewrite sgn64_w64_add by (unfold T63; lia).
  replace (sgn64 (l_c l) + - sgn64 (l_c g)) with (sgn64 (l_c l) - sgn64 (l_c g)) by lia.
  set (R1 := iv_add (sgn64 (l_c l) - sgn64 (l_c g), sgn64 (l_c l) - sgn64 (l_c g)) (IrN.t_ivN ne all bfs (tadd (l_t l) (tneg (l_t g))))) in *.
  set (R2 := iv_add (sgn64 (l_c l) + sgn64 (l_c g), sgn64 (l_c l) + sgn64 (l_c g)) (IrN.t_ivN ne all bfs (tadd (l_t l) (l_t g)))) in *.
  destruct r1 as [p1 q1 p2 q2]; destruct r2 as [u1 v1 u2 v2]. destruct E1 as (P1 & Q1 & P2 & Q2 & V1 & V2). destruct E2 as (U1 & W1 & U2 & W2 & X1 & X2).
  cbn [w_al w_bl w_ah w_bh] in *.
  repeat match type of H with context [smallb ?t] => let E := fresh "S" in destruct (smallb t) eqn:E; [apply smallb_true in E | discriminate H] end.
  destruct (wmeet_win acc _) as [acc1|] eqn:M1; [|discriminate].
  eapply wmeet_win_ok in M1; [|exact HA|].
  - eapply wmeet_win_ok in H; [exact H | exact M1 |]. apply wok_intro; try assumption; cbn [fst snd]; rewrite wv_sub by assumption; lia.
  - apply wok_intro; try assumption; cbn [fst snd]; rewrite wv_add by assumption; lia.
Qed.
#[using="Type"] Lemma wstep_ok : forall T cl l g lo hi acc A T' acc', Tok T -> clok cl l -> wok acc A ->
  IrN.wstep ne all bfs T cl g lo hi acc = Some (T', acc') ->
  Tok T' /\ wok acc' (meet_win (meet_win A (lo + fst (IrN.l_ivN ne all bfs (lsub l g)), hi + snd (IrN.l_ivN ne all bfs (lsub l g))))
                               (fst (IrN.l_ivN ne all bfs (ladd l g)) - hi, snd (IrN.l_ivN ne all bfs (ladd l g)) - lo)).
Proof.
  intros T cl l g lo hi acc A T' acc' HT Hcl HA H. unfold IrN.wstep in H.
  destruct (IrN.conv_l ne all bfs T g) as [[T1 cg]|] eqn:Ec; [|discriminate].
  destruct (z2w lo) as [[loa lob]|] eqn:Elo; [|discriminate]. destruct (z2w hi) as [[hia hib]|] eqn:Ehi; [|discriminate].
  destruct (wstep_iv cl cg loa lob hia hib acc) as [a1|] eqn:Ew; [|discriminate]. injection H as <- <-.
  apply conv_l_ok in Ec as [HT1 Hcg]; [|exact HT]. apply z2w_spec in Elo as (L1 & L2 & L3). apply z2w_spec in Ehi as (H1 & H2 & H3).
  split; [exact HT1|]. rewrite <- L3, <- H3. exact (wstep_iv_ok cl cg l g loa lob hia hib acc A a1 Hcl Hcg HA L1 L2 H1 H2 Ew).
Qed.
#[using="Type"] Lemma rel_N_ok : forall l cl, clok cl l -> forall fs T acc A, Tok T -> wok acc A -> IrN.rel_N ne all bfs l cl fs T acc = IrN.rel_ivN ne all bfs fs l A.
Proof.
  intros l cl Hcl fs. induction fs as [|f fs IH]; intros T acc A HT HA; cbn [IrN.rel_N IrN.rel_ivN].
  - exact (wok_wiv2z acc A HA).
  - destruct (IrN.rel_okN l f); [|apply IH; assumption].
    destruct (IrN.fact_gN ne all bfs f) as [[[g lo] hi]|]; [|apply IH; assumption].
    destruct (IrN.wstep ne all bfs T cl g lo hi acc) as [[T' acc']|] eqn:Ew.
    + apply wstep_ok with (l := l) (A := A) in Ew as [HT' HA']; [|assumption..]. apply IH; assumption.
    + rewrite (wok_wiv2z acc A HA). cbn [IrN.rel_ivN]. reflexivity.
Qed.
#[using="Type"] Lemma rel_topN_ok : forall l, IrN.rel_topN ne all bfs l = IrN.rel_ivN ne all bfs all l (IrN.l_ivN ne all bfs l).
Proof.
  intros l. unfold IrN.rel_topN. destruct (IrN.conv_l ne all bfs TEmpty l) as [[T cl]|] eqn:Ec; [|reflexivity].
  destruct (cl_iv cl) as [acc|] eqn:Ei; [|reflexivity].
  apply conv_l_ok in Ec as [HT Hcl]; [|exact Tok_empty].
  pose proof Hcl as (C1 & C2 & C3).
  assert (Sc : small (cl_c cl)) by (unfold small; lia).
  unfold cl_iv in Ei. apply (ct_iv_ok 1152921504606846976 _ (l_t l)) in Ei; [|exact C3 | exact Sc | exact small_i0 | exact Sc | exact small_i0].
  rewrite !wv_c0, C1 in Ei. apply rel_N_ok; [exact Hcl | exact HT | exact Ei].
Qed.

(* [comment removed for export] *)
Definition cand_ok (c : IrN.cand) : Prop :=
  match c with
  | IrN.CDZ _ _ _ => True
  | IrN.CDN g lo hi cg loa lob hia hib => clok cg g /\ small loa /\ small lob /\ small hia /\ small hib /\ wv loa lob = lo /\ wv hia hib = hi
  end.
Definition cd_g (c : IrN.cand) : lin := match c with IrN.CDZ g _ _ => g | IrN.CDN g _ _ _ _ _ _ _ => g end.
Definition cd_lo (c : IrN.cand) : Z := match c with IrN.CDZ _ lo _ => lo | IrN.CDN _ lo _ _ _ _ _ _ => lo end.
Definition cd_hi (c : IrN.cand) : Z := match c with IrN.CDZ _ _ hi => hi | IrN.CDN _ _ hi _ _ _ _ _ => hi end.
#[using="Type"] Lemma rel_ivC_cons : forall l c cs acc, IrN.rel_ivC ne all bfs l (c :: cs) acc = IrN.rel_ivC ne all bfs l cs (IrN.zstep ne all bfs l (cd_g c) (cd_lo c) (cd_hi c) acc).
Proof. intros l [g lo hi|g lo hi cg loa lob hia hib] cs acc; reflexivity. Qed.
#[using="Type"] Lemma cand_of_ok : forall T g lo hi T' c, Tok T -> IrN.cand_of ne all bfs T g lo hi = (T', c) ->
  Tok T' /\ cand_ok c /\ cd_g c = g /\ cd_lo c = lo /\ cd_hi c = hi.
Proof.
  intros T g lo hi T' c HT H. unfold IrN.cand_of in H. destruct (IrN.conv_l ne all bfs T g) as [[T1 cg]|] eqn:Ec.
  - apply conv_l_ok in Ec as [HT1 Hcg]; [|exact HT].
    destruct (z2w lo) as [[loa lob]|] eqn:Elo; destruct (z2w hi) as [[hia hib]|] eqn:Ehi; injection H as <- <-;
      (split; [exact HT1|]); cbn [cand_ok cd_g cd_lo cd_hi]; try (repeat split; reflexivity).
    apply z2w_spec in Elo as (L1 & L2 & L3). apply z2w_spec in Ehi as (H1 & H2 & H3).
    split; [|repeat split; reflexivity]. split; [exact Hcg|]. split; [exact L1|]. split; [exact L2|]. split; [exact H1|]. split; [exact H2|].
    split; [exact L3 | exact H3].
  - injection H as <- <-. split; [exact HT|]. cbn [cand_ok cd_g cd_lo cd_hi]. repeat split; reflexivity.
Qed.
#[using="Type"] Lemma prep_ok : forall l fs T T' cs, Tok T -> IrN.prep ne all bfs l fs T = (T', cs) ->
  Tok T' /\ Forall cand_ok cs /\
  (forall l', (forall f, IrN.rel_okN l' f = IrN.rel_okN l f) -> forall acc, IrN.rel_ivC ne all bfs l' cs acc = IrN.rel_ivN ne all bfs fs l' acc).
Proof.
  intros l fs. induction fs as [|f fs IH]; intros T T' cs HT H; cbn [IrN.prep] in H.
  - injection H as <- <-. split; [exact HT|]. split; [constructor|]. intros; reflexivity.
  - destruct (IrN.rel_okN l f) eqn:Er.
    + destruct (IrN.fact_gN ne all bfs f) as [[[g lo] hi]|] eqn:Eg.
      * destruct (IrN.cand_of ne all bfs T g lo hi) as [T1 c] eqn:Ec. destruct (IrN.prep ne all bfs l fs T1) as [T2 cs'] eqn:Ep.
        injection H as <- <-. apply cand_of_ok in Ec as (HT1 & Hc & Cg & Clo & Chi); [|exact HT].
        destruct (IH T1 T2 cs' HT1 Ep) as (HT2 & Hcs & Heq). split; [exact HT2|]. split; [constructor; assumption|].
        intros l' Hl acc. rewrite rel_ivC_cons, Heq by exact Hl. cbn [IrN.rel_ivN]. rewrite Hl, Er, Eg, Cg, Clo, Chi. reflexivity.
      * destruct (IH T T' cs HT H) as (HT2 & Hcs & Heq). split; [exact HT2|]. split; [exact Hcs|].
        intros l' Hl acc. rewrite Heq by exact Hl. cbn [IrN.rel_ivN]. rewrite Hl, Er, Eg. reflexivity.
    + destruct (IH T T' cs HT H) as (HT2 & Hcs & Heq). split; [exact HT2|]. split; [exact Hcs|].
      intros l' Hl acc. rewrite Heq by exact Hl. cbn [IrN.rel_ivN]. rewrite Hl, Er. reflexivity.
Qed.
#[using="Type"] Lemma rel_P_ok : forall l cl, clok cl l -> forall cs acc A, Forall cand_ok cs -> wok acc A -> IrN.rel_P ne all bfs l cl cs acc = IrN.rel_ivC ne all bfs l cs A.
Proof.
  intros l cl Hcl cs. induction cs as [|c cs IH]; intros acc A Hcs HA.
  - cbn [IrN.rel_P IrN.rel_ivC]. exact (wok_wiv2z acc A HA).
  - inversion Hcs as [|c0 cs0 Hc Hcs' E1]; subst c0 cs0.
    destruct c as [g lo hi|g lo hi cg loa lob hia hib]; cbn [IrN.rel_P].
    + rewrite (wok_wiv2z acc A HA). reflexivity.
    + destruct (wstep_iv cl cg loa lob hia hib acc) as [acc'|] eqn:Ew; [|rewrite (wok_wiv2z acc A HA); reflexivity].
      destruct Hc as (Hcg & S1 & S2 & S3 & S4 & V1 & V2).
      pose proof (wstep_iv_ok cl cg l g loa lob hia hib acc A acc' Hcl Hcg HA S1 S2 S3 S4 Ew) as Hw.
      rewrite V1, V2 in Hw. rewrite (IH acc' _ Hcs' Hw). reflexivity.
Qed.
#[using="Type"] Lemma rel_topP_ok : forall T cs l, Tok T -> Forall cand_ok cs -> IrN.rel_topP ne all bfs T cs l = IrN.rel_ivC ne all bfs l cs (IrN.l_ivN ne all bfs l).
Proof.
  intros T cs l HT Hcs. unfold IrN.rel_topP. destruct (IrN.conv_l ne all bfs T l) as [[T1 cl]|] eqn:Ec; [|reflexivity].
  destruct (cl_iv cl) as [acc|] eqn:Ei; [|reflexivity].
  apply conv_l_ok in Ec as [HT1 Hcl]; [|exact HT].
  pose proof Hcl as (C1 & C2 & C3).
  assert (Sc : small (cl_c cl)) by (unfold small; lia).
  unfold cl_iv in Ei. apply (ct_iv_ok 1152921504606846976 _ (l_t l)) in Ei; [|exact C3 | exact Sc | exact small_i0 | exact Sc | exact small_i0].
  rewrite !wv_c0, C1 in Ei. apply rel_P_ok; [exact Hcl | exact Hcs | exact Ei].
Qed.
#[using="Type"] Lemma prepL_ok : forall l T cs, IrN.prepL ne all bfs l = (T, cs) ->
  Tok T /\ Forall cand_ok cs /\ (forall l', (forall f, IrN.rel_okN l' f = IrN.rel_okN l f) -> forall acc, IrN.rel_ivC ne all bfs l' cs acc = IrN.rel_ivN ne all bfs all l' acc).
Proof.
  intros l T cs H. unfold IrN.prepL in H. apply prep_ok in H; [exact H|].
  destruct (IrN.conv_t ne all bfs TEmpty (l_t l)) as [[T0 ct]|] eqn:E; [|exact Tok_empty].
  apply conv_t_ok in E as [HT0 _]; [exact HT0 | exact Tok_empty].
Qed.
#[using="Type"] Lemma irange0P_ok : forall T cs l, Tok T -> Forall cand_ok cs -> (forall acc, IrN.rel_ivC ne all bfs l cs acc = IrN.rel_ivN ne all bfs all l acc) ->
  IrN.irange0P ne all bfs mfs T cs l = IrN.irange0N ne all bfs mfs l.
Proof. intros T cs l HT Hcs Heq. unfold IrN.irange0P, IrN.irange0N. rewrite rel_topP_ok by assumption. rewrite Heq, rel_topN_ok. reflexivity. Qed.

(* [comment removed for export] *)
Definition Sok (Sv : tree unit) (L : list positive) : Prop := forall x, In x L -> tget x Sv <> None.
#[using="Type"] Lemma touch_ok : forall t Sv L Sv' L', IrN.touch t Sv L = (Sv', L') -> Sok Sv L -> Sok Sv' L'.
Proof.
  induction t as [|[x k] t IH]; intros Sv L Sv' L' H HS; cbn [IrN.touch] in H.
  - injection H as <- <-. exact HS.
  - destruct (tget x Sv) as [u|] eqn:E.
    + exact (IH Sv L Sv' L' H HS).
    + apply (IH (tset x tt Sv) (x :: L) Sv' L' H). intros y [<-|Hy].
      * rewrite tget_tset_same. discriminate.
      * destruct (Pos.eq_dec x y) as [<-|Hne]; [rewrite tget_tset_same; discriminate|]. rewrite tget_tset_other by exact Hne. exact (HS y Hy).
Qed.
Fixpoint rel_ivR (l : lin) (raw : list (lin * Z * Z)) (acc : Z * Z) : Z * Z :=
  match raw with [] => acc | (g, lo, hi) :: r => rel_ivR l r (IrN.zstep ne all bfs l g lo hi acc) end.
#[using="Type"] Lemma prep0_ok : forall l fs Sv L Sv' L' raw, IrN.prep0 ne all bfs l fs Sv L = (Sv', L', raw) -> Sok Sv L -> Sok Sv' L' /\
  (forall l', (forall f, IrN.rel_okN l' f = IrN.rel_okN l f) -> forall acc, rel_ivR l' raw acc = IrN.rel_ivN ne all bfs fs l' acc).
Proof.
  intros l fs. induction fs as [|f fs IH]; intros Sv L Sv' L' raw H HS; cbn [IrN.prep0] in H.
  - injection H as <- <- <-. split; [exact HS|]. intros; reflexivity.
  - destruct (IrN.rel_okN l f) eqn:Er.
    + destruct (IrN.fact_gN ne all bfs f) as [[[g lo] hi]|] eqn:Eg.
      * destruct (IrN.touch (l_t g) Sv L) as [Sv1 L1] eqn:Et. destruct (IrN.prep0 ne all bfs l fs Sv1 L1) as [[Sv2 L2] r] eqn:Ep.
        injection H as <- <- <-. apply touch_ok in Et; [|exact HS]. destruct (IH Sv1 L1 Sv2 L2 r Ep Et) as [HS2 Heq].
        split; [exact HS2|]. intros l' Hl acc. cbn [rel_ivR]. rewrite Heq by exact Hl. cbn [IrN.rel_ivN]. rewrite Hl, Er, Eg. reflexivity.
      * destruct (IH Sv L Sv' L' raw H HS) as [HS2 Heq]. split; [exact HS2|].
        intros l' Hl acc. rewrite Heq by exact Hl. cbn [IrN.rel_ivN]. rewrite Hl, Er, Eg. reflexivity.
    + destruct (IH Sv L Sv' L' raw H HS) as [HS2 Heq]. split; [exact HS2|].
      intros l' Hl acc. rewrite Heq by exact Hl. cbn [IrN.rel_ivN]. rewrite Hl, Er. reflexivity.
Qed.
#[using="Type"] Lemma conv_cands_ok : forall raw T T' cs, Tok T -> IrN.conv_cands ne all bfs T raw = (T', cs) ->
  Tok T' /\ Forall cand_ok cs /\ (forall l acc, IrN.rel_ivC ne all bfs l cs acc = rel_ivR l raw acc).
Proof.
  induction raw as [|[[g lo] hi] raw IH]; intros T T' cs HT H; cbn [IrN.conv_cands] in H.
  - injection H as <- <-. split; [exact HT|]. split; [constructor|]. intros; reflexivity.
  - destruct (IrN.cand_of ne all bfs T g lo hi) as [T1 c] eqn:Ec. destruct (IrN.conv_cands ne all bfs T1 raw) as [T2 cs'] eqn:Ecs.
    injection H as <- <-. apply cand_of_ok in Ec as (HT1 & Hc & Cg & Clo & Chi); [|exact HT].
    destruct (IH T1 T2 cs' HT1 Ecs) as (HT2 & Hcs & Heq). split; [exact HT2|]. split; [constructor; assumption|].
    intros l acc. rewrite rel_ivC_cons, Cg, Clo, Chi. cbn [rel_ivR]. apply Heq.
Qed.
#[using="Type"] Lemma mk_tblV_ok : forall Zt L T, (forall x, In x L -> vr_get Zt x = var_range bfs x) -> Tok T -> Tok (IrN.mk_tbl ne all Zt L T).
Proof.
  intros Zt L. induction L as [|x L IH]; intros T HZ HT; cbn [IrN.mk_tbl]; [exact HT|].
  rewrite (HZ x (or_introl eq_refl)). fold (IrN.vrangeN ne all bfs x).
  destruct (mk_ve (IrN.vrangeN ne all bfs x)) as [e|] eqn:Em.
  - apply IH; [intros y Hy; apply HZ; right; exact Hy|]. apply mk_ve_ok in Em.
    intros y e1 Hy. destruct (Pos.eq_dec x y) as [<-|Hne].
    + rewrite tget_tset_same in Hy. injection Hy as <-. exact Em.
    + rewrite tget_tset_other in Hy by exact Hne. exact (HT y e1 Hy).
  - apply IH; [intros y Hy; apply HZ; right; exact Hy | exact HT].
Qed.
End Conv.

(* [comment removed for export] *)
Lemma vr_get_setN : forall t y r x, vr_get (tset y r t) x = if Pos.eqb x y then r else vr_get t x.
Proof.
  intros t y r x. unfold vr_get. destruct (Pos.eqb x y) eqn:E.
  - apply Pos.eqb_eq in E. subst. rewrite tget_tset_same. reflexivity.
  - apply Pos.eqb_neq in E. rewrite tget_tset_other by congruence. reflexivity.
Qed.
Lemma vr_tbl_eqN : forall fs x, vr_get (vr_tbl fs) x = var_range fs x.
Proof.
  induction fs as [|f fs IH]; intros x; [unfold vr_get; cbn [vr_tbl var_range]; destruct x; reflexivity|].
  destruct f as [c a b tk|l lo hi|l k r|l m v|l o z|l bs]; cbn [vr_tbl var_range]; try apply IH.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k] t1]; try apply IH.
    destruct k as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
    cbv zeta. rewrite vr_get_setN. destruct (Pos.eqb x y) eqn:E; [|apply IH]. apply Pos.eqb_eq in E. subst. rewrite IH. reflexivity.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k] t1]; try apply IH.
    destruct k as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
    destruct (Z.leb 0 m) eqn:Em.
    + cbv zeta. rewrite vr_get_setN. destruct (Pos.eqb x y) eqn:E; cbn [andb]; [|apply IH]. apply Pos.eqb_eq in E. subst. rewrite IH. reflexivity.
    + rewrite andb_false_r. apply IH.
Qed.
Lemma occN_eq : forall x u, IrN.occN x u = existsb (fun '(y, _) => Pos.eqb x y) u.
Proof. intros x u. induction u as [|[y k] u IH]; [reflexivity|]. cbn [IrN.occN existsb]. rewrite IH. reflexivity. Qed.
Lemma sharesN_eq : forall t u, IrN.sharesN t u = shares t u.
Proof.
  intros t u. unfold shares. induction t as [|[x k] t IH]; [reflexivity|]. cbn [IrN.sharesN existsb]. rewrite occN_eq, IH. reflexivity.
Qed.
Lemma rel_okN_eq : forall l f, IrN.rel_okN l f = rel_ok l f.
Proof.
  intros l f. destruct f as [c a b tk|g lo hi|? ? ?|? ? ?|? ? ?|? ?]; try reflexivity.
  - cbn [IrN.rel_okN rel_ok]. rewrite !sharesN_eq. reflexivity.
  - unfold IrN.rel_okN, rel_ok. destruct g as [c0 t0]. destruct c0 as [|p|p]; try (cbn [l_t]; apply sharesN_eq).
    destruct t0 as [|[y k] t1]; try (cbn [l_t]; apply sharesN_eq).
    destruct k as [|q|q]; try (cbn [l_t]; apply sharesN_eq). destruct q; try (cbn [l_t]; apply sharesN_eq).
    destruct t1; [reflexivity|]. cbn [l_t]. apply sharesN_eq.
Qed.
Lemma var_range_bare : forall fs x, var_range (List.filter IrN.is_bare fs) x = var_range fs x.
Proof.
  induction fs as [|f fs IH]; intros x; [reflexivity|].
  destruct f as [c a b tk|l lo hi|l k r|l m v|l o z|l bs]; cbn [List.filter IrN.is_bare var_range]; try apply IH.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k] t1]; try apply IH.
    destruct k as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
    cbn [var_range]. rewrite IH. reflexivity.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k] t1]; try apply IH.
    destruct k as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
    cbn [var_range]. rewrite IH. reflexivity.
Qed.
Lemma var_align_mod : forall fs x, var_align (List.filter IrN.is_modb fs) x = var_align fs x.
Proof.
  induction fs as [|f fs IH]; intros x; [reflexivity|].
  destruct f as [c a b tk|l lo hi|l k r|l m v|l o z|l bs]; cbn [List.filter IrN.is_modb var_align]; try apply IH.
  destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k0] t1]; try apply IH.
  destruct k0 as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
  cbn [var_align]. rewrite IH. reflexivity.
Qed.
Lemma var_lowb_mod : forall fs x k, var_lowb (List.filter IrN.is_modb fs) x k = var_lowb fs x k.
Proof.
  induction fs as [|f fs IH]; intros x k; [reflexivity|].
  destruct f as [c a b tk|l lo hi|l k1 r|l m v|l o z|l bs]; cbn [List.filter IrN.is_modb var_lowb]; try apply IH.
  destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k0] t1]; try apply IH.
  destruct k0 as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
  cbn [var_lowb]. rewrite IH. reflexivity.
Qed.
Lemma t_align_mod : forall fs t, t_align (List.filter IrN.is_modb fs) t = t_align fs t.
Proof. intros fs t. induction t as [|[x k] t IH]; [reflexivity|]. cbn [t_align]. rewrite var_align_mod, IH. reflexivity. Qed.
Lemma lalign_mod : forall fs l, lalign (List.filter IrN.is_modb fs) l = lalign fs l.
Proof. intros fs l. unfold lalign. rewrite t_align_mod. reflexivity. Qed.
Lemma t_lowb_mod : forall fs t k, t_lowb (List.filter IrN.is_modb fs) t k = t_lowb fs t k.
Proof. intros fs t k. induction t as [|[x c] t IH]; [reflexivity|]. cbn [t_lowb]. rewrite IH, !var_lowb_mod. reflexivity. Qed.
Lemma lround_mod : forall fs l v, lround (List.filter IrN.is_modb fs) l v = lround fs l v.
Proof. intros fs l v. unfold lround, lowb. rewrite t_lowb_mod. reflexivity. Qed.
Section NF.
Variables (ne all : list fact).
Let bfs := List.filter IrN.is_bare all.
Let mfs := List.filter IrN.is_modb all.
#[using="Type"] Lemma vrangeN_eq : forall x, IrN.vrangeN ne all bfs x = var_rangeF (vr_tbl all) ne all x.
Proof. intros x. unfold IrN.vrangeN, var_rangeF, bfs. rewrite var_range_bare, vr_tbl_eqN. reflexivity. Qed.
#[using="Type"] Lemma t_ivN_eq : forall t, IrN.t_ivN ne all bfs t = t_ivF (vr_tbl all) ne all t.
Proof. induction t as [|[x k] t IH]; [reflexivity|]. cbn [IrN.t_ivN t_ivF]. rewrite vrangeN_eq, IH. reflexivity. Qed.
#[using="Type"] Lemma l_ivN_eq : forall l, IrN.l_ivN ne all bfs l = l_ivF (vr_tbl all) ne all l.
Proof. intros l. unfold IrN.l_ivN, l_ivF. rewrite t_ivN_eq. reflexivity. Qed.
#[using="Type"] Lemma fact_gN_eq : forall f, IrN.fact_gN ne all bfs f = fact_gF (vr_tbl all) ne all f.
Proof.
  intros f. destruct f as [c a b tk|? ? ?|? ? ?|? ? ?|? ? ?|? ?]; try reflexivity.
  unfold IrN.fact_gN, fact_gF, IrN.base_rangeN, base_rangeF, IrN.srangeN, srangeF. rewrite !l_ivN_eq. reflexivity.
Qed.
#[using="Type"] Lemma rel_ivN_eq : forall fs l acc, IrN.rel_ivN ne all bfs fs l acc = rel_ivF (vr_tbl all) ne all fs l acc.
Proof.
  induction fs as [|f fs IH]; intros l acc; [reflexivity|]. cbn [IrN.rel_ivN rel_ivF]. rewrite rel_okN_eq.
  destruct (rel_ok l f); [|apply IH]. rewrite fact_gN_eq. destruct (fact_gF (vr_tbl all) ne all f) as [[[g lo] hi]|]; [|apply IH].
  rewrite !l_ivN_eq. apply IH.
Qed.
#[using="Type"] Theorem irange0N_eq_gen : forall l, IrN.irange0N ne all bfs mfs l = irange0F (vr_tbl all) ne all l.
Proof.
  intros l. unfold IrN.irange0N, irange0F. rewrite rel_topN_ok, rel_ivN_eq, l_ivN_eq. unfold mfs. rewrite lround_mod, lalign_mod. reflexivity.
Qed.
End NF.
Theorem irange0N_eq : forall ne all l, IrN.irange0N ne all (List.filter IrN.is_bare all) (List.filter IrN.is_modb all) l = irange0F (vr_tbl all) ne all l.
Proof. intros ne all l. exact (irange0N_eq_gen ne all l). Qed.

(* [comment removed for export] *)
Lemma sharesN_fst : forall t t' u, List.map fst t = List.map fst t' -> IrN.sharesN t u = IrN.sharesN t' u.
Proof.
  induction t as [|[x k] t IH]; intros [|[x' k'] t'] u H; cbn in H; try discriminate; [reflexivity|].
  injection H as <- H. cbn [IrN.sharesN]. rewrite (IH t' u H). reflexivity.
Qed.
Lemma map_fst_div : forall (h : Z -> Z) (t : list (positive * Z)), List.map fst (List.map (fun '(x, c) => (x, h c)) t) = List.map fst t.
Proof. intros h t. induction t as [|[x c] t IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma rel_okN_ldiv8 : forall l l', ldiv8 l = Some l' -> forall f, IrN.rel_okN l' f = IrN.rel_okN l f.
Proof.
  intros l l' H f. unfold ldiv8 in H. destruct (_ && _)%bool; [|discriminate]. injection H as <-.
  assert (Ht : forall u, IrN.sharesN (List.map (fun '(x, c) => (x, w64 (Z.quot (sgn64 c) 8))) (l_t l)) u = IrN.sharesN (l_t l) u).
  { intros u. apply sharesN_fst. apply (map_fst_div (fun c => w64 (Z.quot (sgn64 c) 8))). }
  destruct f as [c a b tk|g lo hi|? ? ?|? ? ?|? ? ?|? ?]; try reflexivity.
  - cbn [IrN.rel_okN l_t]. rewrite !Ht. reflexivity.
  - unfold IrN.rel_okN. destruct g as [c0 t0]. cbn [l_t]. rewrite !Ht. reflexivity.
Qed.
Lemma vr_tblS_eq : forall Sv fs x, tget x Sv <> None -> vr_get (IrN.vr_tblS Sv fs) x = var_range fs x.
Proof.
  intros Sv fs x Hx. induction fs as [|f fs IH]; [unfold vr_get; cbn [IrN.vr_tblS var_range]; destruct x; reflexivity|].
  destruct f as [c a b tk|l lo hi|l k r|l m v|l o z|l bs]; cbn [IrN.vr_tblS var_range]; try exact IH.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try exact IH. destruct t0 as [|[y k] t1]; try exact IH.
    destruct k as [|q|q]; try exact IH. destruct q; try exact IH. destruct t1; try exact IH.
    cbv zeta. destruct (tget y Sv) as [u|] eqn:Ey.
    + rewrite vr_get_setN. destruct (Pos.eqb x y) eqn:E; [|exact IH]. apply Pos.eqb_eq in E. subst. rewrite IH. reflexivity.
    + destruct (Pos.eqb x y) eqn:E; [|exact IH]. apply Pos.eqb_eq in E. subst. contradiction.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try exact IH. destruct t0 as [|[y k] t1]; try exact IH.
    destruct k as [|q|q]; try exact IH. destruct q; try exact IH. destruct t1; try exact IH.
    cbv zeta. destruct (tget y Sv) as [u|] eqn:Ey.
    + destruct (Z.leb 0 m) eqn:Em.
      * rewrite vr_get_setN. destruct (Pos.eqb x y) eqn:E; cbn [andb]; [|exact IH]. apply Pos.eqb_eq in E. subst. rewrite IH. reflexivity.
      * rewrite andb_false_r. exact IH.
    + destruct (Pos.eqb x y) eqn:E; cbn [andb]; [|exact IH]. apply Pos.eqb_eq in E. subst. contradiction.
Qed.
Lemma prepS_ok : forall ne all bfs l T cs, IrN.prepS ne all bfs l = (T, cs) ->
  Tok ne all bfs T /\ Forall (cand_ok ne all bfs) cs /\
  (forall l', (forall f, IrN.rel_okN l' f = IrN.rel_okN l f) -> forall acc, IrN.rel_ivC ne all bfs l' cs acc = IrN.rel_ivN ne all bfs all l' acc).
Proof.
  intros ne all bfs l T cs H. unfold IrN.prepS in H.
  destruct (IrN.touch (l_t l) TEmpty []) as [Sv0 L0] eqn:E0.
  destruct (IrN.prep0 ne all bfs l all Sv0 L0) as [[Sv L] raw] eqn:E1.
  assert (HS0 : Sok Sv0 L0) by (apply (touch_ok _ _ _ _ _ E0); intros x []).
  destruct (prep0_ok ne all bfs l all Sv0 L0 Sv L raw E1 HS0) as [HS Heq].
  assert (HT : Tok ne all bfs (IrN.mk_tbl ne all (IrN.vr_tblS Sv bfs) L TEmpty)).
  { apply mk_tblV_ok; [|apply Tok_empty]. intros x Hx. apply vr_tblS_eq. exact (HS x Hx). }
  destruct (conv_cands_ok ne all bfs raw _ T cs HT H) as (HT' & Hcs & Hc). split; [exact HT'|]. split; [exact Hcs|].
  intros l' Hl acc. rewrite Hc. apply Heq. exact Hl.
Qed.
Theorem irange0S_eq : forall fs l T cs, IrN.prepS (ne_sub fs) fs (List.filter IrN.is_bare fs) l = (T, cs) ->
  forall l', (forall f, IrN.rel_okN l' f = IrN.rel_okN l f) ->
  IrN.irange0P (ne_sub fs) fs (List.filter IrN.is_bare fs) (List.filter IrN.is_modb fs) T cs l' = irange0F (vr_tbl fs) (ne_sub fs) fs l'.
Proof.
  intros fs l T cs H l' Hl. destruct (prepS_ok (ne_sub fs) fs (List.filter IrN.is_bare fs) l T cs H) as (HT & Hc & Heq).
  rewrite (irange0P_ok (ne_sub fs) fs (List.filter IrN.is_bare fs) (List.filter IrN.is_modb fs) T cs l' HT Hc (Heq l' Hl)). apply irange0N_eq.
Qed.

(* [comment removed for export] *)
Section XT.
Variables (ne all bfs : list fact).
#[using="Type"] Lemma rel_NT_ok : forall l cl, clok ne all bfs cl l -> forall fs T acc A, Tok ne all bfs T -> wok acc A ->
  Tok ne all bfs (fst (IrX.rel_NT ne all bfs l cl fs T acc)) /\ snd (IrX.rel_NT ne all bfs l cl fs T acc) = IrN.rel_ivN ne all bfs fs l A.
Proof.
  intros l cl Hcl fs. induction fs as [|f fs IH]; intros T acc A HT HA.
  - cbn [IrX.rel_NT IrN.rel_ivN fst snd]. split; [exact HT | exact (wok_wiv2z acc A HA)].
  - cbn [IrX.rel_NT]. destruct (IrN.rel_okN l f) eqn:Er.
    + destruct (IrN.fact_gN ne all bfs f) as [[[g lo] hi]|] eqn:Eg.
      * destruct (IrN.wstep ne all bfs T cl g lo hi acc) as [[T' acc']|] eqn:Ew.
        -- apply wstep_ok with (l := l) (A := A) in Ew as [HT' HA']; [|assumption..].
           destruct (IH T' acc' _ HT' HA') as [H1 H2]. split; [exact H1|]. rewrite H2. cbn [IrN.rel_ivN]. rewrite Er, Eg. reflexivity.
        -- cbn [fst snd]. split; [exact HT|]. rewrite (wok_wiv2z acc A HA). reflexivity.
      * destruct (IH T acc A HT HA) as [H1 H2]. split; [exact H1|]. rewrite H2. cbn [IrN.rel_ivN]. rewrite Er, Eg. reflexivity.
    + destruct (IH T acc A HT HA) as [H1 H2]. split; [exact H1|]. rewrite H2. cbn [IrN.rel_ivN]. rewrite Er. reflexivity.
Qed.
#[using="Type"] Lemma rel_topT_ok : forall T l, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.rel_topT ne all bfs T l)) /\ snd (IrX.rel_topT ne all bfs T l) = IrN.rel_ivN ne all bfs all l (IrN.l_ivN ne all bfs l).
Proof.
  intros T l HT. unfold IrX.rel_topT. destruct (IrN.conv_l ne all bfs T l) as [[T1 cl]|] eqn:Ec; [|split; [exact HT | reflexivity]].
  apply conv_l_ok in Ec as [HT1 Hcl]; [|exact HT].
  destruct (cl_iv cl) as [acc|] eqn:Ei; [|split; [exact HT1 | reflexivity]].
  pose proof Hcl as (C1 & C2 & C3).
  assert (Sc : small (cl_c cl)) by (unfold small; lia).
  unfold cl_iv in Ei. apply (ct_iv_ok ne all bfs 1152921504606846976 _ (l_t l)) in Ei; [|exact C3 | exact Sc | exact small_i0 | exact Sc | exact small_i0].
  rewrite !wv_c0, C1 in Ei. exact (rel_NT_ok l cl Hcl all T1 acc _ HT1 Ei).
Qed.
#[using="Type"] Lemma rel_baseT_ok : forall T d, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.rel_baseT ne all bfs T d)) /\
  snd (IrX.rel_baseT ne all bfs T d) = frange_same all d (ne_int ne d (IrN.rel_ivN ne all bfs all d (IrN.l_ivN ne all bfs d))).
Proof.
  intros T d HT. unfold IrX.rel_baseT. destruct (rel_topT_ok T d HT) as [H1 H2].
  destruct (IrX.rel_topT ne all bfs T d) as [T1 r]. cbn [fst snd] in *. subst r. split; [exact H1 | reflexivity].
Qed.
End XT.
Section XF.
Variables (ne all : list fact).
Local Abbreviation bfs := (List.filter IrN.is_bare all).
Local Abbreviation mfs := (List.filter IrN.is_modb all).
Local Abbreviation vt := (vr_tbl all).
#[using="Type"] Lemma rel_baseT_okF : forall T d, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.rel_baseT ne all bfs T d)) /\ snd (IrX.rel_baseT ne all bfs T d) = rel_baseF vt ne all d.
Proof.
  intros T d HT. destruct (rel_baseT_ok ne all bfs T d HT) as [H1 H2]. split; [exact H1|]. rewrite H2.
  unfold rel_baseF. rewrite rel_ivN_eq, l_ivN_eq. reflexivity.
Qed.
#[using="Type"] Lemma rel_iv2T_ok : forall fs ta l T acc, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.rel_iv2T ne all bfs fs ta l T acc)) /\ snd (IrX.rel_iv2T ne all bfs fs ta l T acc) = rel_iv2F vt ne all fs ta l acc.
Proof.
  induction fs as [|f fs IH]; intros ta l T acc HT; cbn [IrX.rel_iv2T rel_iv2F]; [split; [exact HT | reflexivity]|].
  destruct (rel_ok3 ta f); [|apply IH; exact HT].
  rewrite fact_gN_eq. destruct (fact_gF vt ne all f) as [[[g lo0] hi0]|]; [|apply IH; exact HT].
  destruct (ne_int_fixl all ne g (lo0, hi0)) as [lo hi].
  destruct (rel_baseT_okF T (lsub l g) HT) as [H1 H2]. destruct (IrX.rel_baseT ne all bfs T (lsub l g)) as [T1 r1]. cbn [fst snd] in H1, H2. subst r1.
  destruct (rel_baseT_okF T1 (ladd l g) H1) as [H3 H4]. destruct (IrX.rel_baseT ne all bfs T1 (ladd l g)) as [T2 r2]. cbn [fst snd] in H3, H4. subst r2.
  apply IH. exact H3.
Qed.
#[using="Type"] Lemma srl_oneT_ok : forall T l g lo hi q k acc, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.srl_oneT ne all bfs T l g lo hi q k acc)) /\ snd (IrX.srl_oneT ne all bfs T l g lo hi q k acc) = srl_oneF vt ne all l g lo hi q k acc.
Proof.
  intros T l g lo hi q k acc HT. unfold IrX.srl_oneT, srl_oneF. cbv zeta.
  destruct (Z.eqb _ 0); [split; [exact HT | reflexivity]|].
  match goal with |- context [IrX.rel_baseT ne all bfs T ?m] => set (M := m) end.
  destruct (rel_baseT_okF T M HT) as [H1 H2]. destruct (IrX.rel_baseT ne all bfs T M) as [T1 b]. cbn [fst snd] in H1, H2. subst b.
  destruct (rel_iv2T_ok all (l_t M) M T1 (rel_baseF vt ne all M) H1) as [H3 H4].
  destruct (IrX.rel_iv2T ne all bfs all (l_t M) M T1 (rel_baseF vt ne all M)) as [T2 wm]. cbn [fst snd] in H3, H4. subst wm.
  split; [exact H3 | reflexivity].
Qed.
#[using="Type"] Lemma srl_termsT_ok : forall t T l g lo hi acc, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.srl_termsT ne all bfs T l g lo hi t acc)) /\ snd (IrX.srl_termsT ne all bfs T l g lo hi t acc) = srl_termsF vt ne all l g lo hi t acc.
Proof.
  induction t as [|[q cq] t IH]; intros T l g lo hi acc HT; cbn [IrX.srl_termsT srl_termsF]; [split; [exact HT | reflexivity]|].
  destruct (pow2_neg cq) as [k|]; [|apply IH; exact HT].
  destruct (srl_oneT_ok T l g lo hi q k acc HT) as [H1 H2]. destruct (IrX.srl_oneT ne all bfs T l g lo hi q k acc) as [T1 a1].
  cbn [fst snd] in H1, H2. subst a1. apply IH. exact H1.
Qed.
#[using="Type"] Lemma srl_ivT_ok : forall fs l T acc, Tok ne all bfs T ->
  Tok ne all bfs (fst (IrX.srl_ivT ne all bfs fs l T acc)) /\ snd (IrX.srl_ivT ne all bfs fs l T acc) = srl_ivF vt ne all fs l acc.
Proof.
  induction fs as [|f fs IH]; intros l T acc HT; [split; [exact HT | reflexivity]|].
  destruct f as [c a b tk|g lo hi|? ? ?|? ? ?|? ? ?|? ?]; cbn [IrX.srl_ivT srl_ivF]; try (apply IH; exact HT).
  - rewrite !sharesN_eq. destruct (shares (l_t l) (l_t a)); cbn [orb];
      [|destruct (shares (l_t l) (l_t b)); [|apply IH; exact HT]];
      (rewrite fact_gN_eq; destruct (fact_gF vt ne all (FCond c a b tk)) as [[[g lo] hi]|]; [|apply IH; exact HT];
       destruct (srl_termsT_ok (l_t g) T l g lo hi acc HT) as [H1 H2]; destruct (IrX.srl_termsT ne all bfs T l g lo hi (l_t g) acc) as [T1 a1];
       cbn [fst snd] in H1, H2; subst a1; apply IH; exact H1).
  - rewrite sharesN_eq. destruct (shares (l_t l) (l_t g)); [|apply IH; exact HT].
    destruct (srl_termsT_ok (l_t g) T l g lo hi acc HT) as [H1 H2]. destruct (IrX.srl_termsT ne all bfs T l g lo hi (l_t g) acc) as [T1 a1].
    cbn [fst snd] in H1, H2. subst a1. apply IH. exact H1.
Qed.
#[using="Type"] Theorem irange_x0N_eq_gen : forall l, IrX.irange_x0N ne all bfs mfs l = irange_x0F vt ne all l.
Proof.
  intros l. unfold IrX.irange_x0N, irange_x0F.
  destruct (rel_topT_ok ne all bfs TEmpty l (Tok_empty ne all bfs)) as [H1 H2]. destruct (IrX.rel_topT ne all bfs TEmpty l) as [T1 a0].
  cbn [fst snd] in H1, H2. subst a0. rewrite rel_ivN_eq, l_ivN_eq.
  set (A0 := rel_ivF vt ne all all l (l_ivF vt ne all l)).
  destruct (rel_iv2T_ok all (l_t l) l T1 A0 H1) as [H3 H4].
  destruct (IrX.rel_iv2T ne all bfs all (l_t l) l T1 A0) as [T2 a1]. cbn [fst snd] in H3, H4. subst a1.
  set (A1 := rel_iv2F vt ne all all (l_t l) l A0).
  destruct (srl_ivT_ok all l T2 A1 H3) as [H5 H6]. destruct (IrX.srl_ivT ne all bfs all l T2 A1) as [T3 a2]. cbn [fst snd] in H5, H6. subst a2.
  rewrite lround_mod, lalign_mod. reflexivity.
Qed.
End XF.
Theorem irange_x0N_eq : forall ne all l, IrX.irange_x0N ne all (List.filter IrN.is_bare all) (List.filter IrN.is_modb all) l = irange_x0F (vr_tbl all) ne all l.
Proof. intros ne all l. exact (irange_x0N_eq_gen ne all l). Qed.
