(** * Bridge.Infl.IArmLenExt — pair I10 (helper pci-len): the fallthrough arms LENEXT, DIST
    and DISTEXT, each entered from the one before with [icb] and the ranges [tent] gives
    (length extra <= 5 bits and length <= 258; distance extra <= 13 bits and
    1 <= offset <= 32768), ending in MATCH ([IArmLit.arm_MATCH_ok]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmLitKit IArmLit IArmLenDec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma us_eq : forall f w, IS.us f w = IS.ARun tt (IS.wset_s w (f (IS.w_s w))).
Proof. reflexivity. Qed.

Lemma aux_eq : forall f w, IA.aux IS.ivar_ref f w = IS.ARun tt (IS.wset_s w (f (IS.w_s w))).
Proof. reflexivity. Qed.

Lemma set_mode_eq : forall m w, IA.set_mode m w = IS.ARun tt (IS.wset_s w (IS.iset_mode (IS.w_s w) m)).
Proof. reflexivity. Qed.

Lemma abind_us : forall {B} f (g : unit -> IS.AM B) w,
  IS.abind (IS.us f) g w = g tt (IS.wset_s w (f (IS.w_s w))).
Proof. reflexivity. Qed.

Lemma abind_aux : forall {B} f (g : unit -> IS.AM B) w,
  IS.abind (IA.aux IS.ivar_ref f) g w = g tt (IS.wset_s w (f (IS.w_s w))).
Proof. reflexivity. Qed.

Lemma icore_tab : forall w q, icore w q ->
  IS.is_lenbits (IS.w_s w) = RI.t_lenbits (RI.s_tab (RI.q_st q))
  /\ IS.is_distbits (IS.w_s w) = RI.t_distbits (RI.s_tab (RI.q_st q)).
Proof.
  intros w q H. revert H. icore_unf. cbv zeta. intros H. destr_all. split; assumption.
Qed.

Lemma bits_of_range : forall n b, 0 <= n -> 0 <= RB.br_bits_of n b < 2 ^ n.
Proof. intros n b Hn. unfold RB.br_bits_of. apply land_mask_range. exact Hn. Qed.

(* ------------------------------------------------------------------------- *)
(* DISTEXT                                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma arm_DISTEXT_ok' : forall w q, icb w q -> RI.q_mode q = RI.M_DISTEXT ->
  0 <= RI.u_length (RI.s_cur (RI.q_st q)) <= 258 ->
  0 <= RI.u_extra (RI.s_cur (RI.q_st q)) <= 13 -> 1 <= RI.u_offset (RI.s_cur (RI.q_st q)) ->
  RI.u_offset (RI.s_cur (RI.q_st q)) + 2 ^ RI.u_extra (RI.s_cur (RI.q_st q)) <= 32769 ->
  step_ok (IA.arm_DISTEXT IS.ivar_ref w) (RI.inf_DISTEXT q).
Proof.
  intros w q Hb Hmode HL HE HO1 HO2.
  pose proof Hb as [H Ht].
  pose proof (icore_cur w q H) as (EL & EO & EE & EB & _).
  assert (Hnh : forall Q, RI.q_mode Q = RI.M_DISTEXT -> RI.q_mode Q <> RI.M_HEAD)
    by (intros Q HQ; rewrite HQ; discriminate).
  unfold RI.inf_DISTEXT. cbv zeta.
  unfold IA.arm_DISTEXT. cbn [IS.abind IS.gs].
  rewrite EE.
  destruct (Z.eqb_spec (RI.u_extra (RI.s_cur (RI.q_st q))) 0) as [E0|E0].
  - cbn [negb IS.abind IS.aret IA.set_mode IS.us].
    apply arm_MATCH_ok; [|reflexivity].
    apply inv_match; [| reflexivity | exact HL |].
    + apply B_mode; [exact Hb | | reflexivity].
      apply (icore_not_head _ _ H). apply Hnh. exact Hmode.
    + rt_cbn. rewrite E0 in HO2. cbn [Z.pow Z.pow_pos Pos.iter] in HO2. lia.
  - destruct (RI.inf_nb (RI.u_extra (RI.s_cur (RI.q_st q))) (RI.q_br q)) as [b1|b1] eqn:Enb.
    2: { apply step_ok_leave_ok. exact (icore_ret w q H). }
    set (E := RI.u_extra (RI.s_cur (RI.q_st q))) in *.
    cbn [negb].
    destruct (needbits_sim w (RI.q_br q) b1 E (icb_brel _ _ Hb) ltac:(lia) Enb)
      as (E1 & Hb1 & HE1 & Hin1 & Hsum1).
    pose proof (nb_bnx _ _ _ Enb) as (Hbn1 & _).
    assert (Hc1 : icb (wbr w b1) (RI.qset_br q b1)) by (apply B_br; [exact Hb|exact Hb1|exact Hin1|exact Hsum1|lia]).
    rewrite abind_assoc. astep E1.
    rewrite abind_assoc. astep (bits_sim (wbr w b1) b1 E Hb1 ltac:(lia)).
    pose proof (bits_of_range E b1 ltac:(lia)) as Hv.
    set (v := RB.br_bits_of E b1) in *.
    rewrite abind_assoc. rewrite abind_us; cbv beta.
    assert (Hc2 : icb (IS.wset_s (wbr w b1) (IS.iset_offset (IS.w_s (wbr w b1)) (wrap32 (IS.is_offset (IS.w_s (wbr w b1)) + v))))
                      (RI.qset_st (RI.qset_br q b1) (RI.set_offset (RI.q_st (RI.qset_br q b1))
                                     (RI.u_offset (RI.s_cur (RI.q_st q)) + v)))).
    { apply B_offset; [exact Hc1|]. rewrite wbr_s, EO. apply wrap32_id. lia. }
    match type of Hc2 with icb ?W ?Q => set (W2 := W) in *; set (Q2 := Q) in * end.
    destruct (dropbits_sim W2 b1 E (icb_brel _ _ Hc2) ltac:(lia)) as (E3 & Hb3).
    rewrite abind_assoc. astep E3.
    assert (Hc3 : icb (wbr W2 (RB.br_dropbits E b1)) (RI.qset_br Q2 (RB.br_dropbits E b1))).
    { apply B_br; [exact Hc2 | exact Hb3 | reflexivity | reflexivity |].
      rewrite drop_bnx. change (RI.q_br Q2) with b1. lia. }
    astep_back.
    pose proof (B_addback _ _ E Hc3) as Hc4.
    match type of Hc4 with icb ?W ?Q => set (W4 := W) in *; set (Q4 := Q) in * end.
    cbn [IS.abind IA.set_mode IS.us].
    apply arm_MATCH_ok; [|reflexivity].
    apply inv_match; [| reflexivity | |].
    + apply B_mode; [exact Hc4 | | reflexivity].
      apply (icore_not_head _ _ (proj1 Hc4)). apply Hnh. exact Hmode.
    + rt_cbn. exact HL.
    + rt_cbn. fold E. fold v. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* DIST                                                                      *)
(* ------------------------------------------------------------------------- *)

Definition dist_tail (here : Z) : IS.AM unit :=
  if negb (Z.land (IS.code_op here) 64 =? 0) then IA.go_bad MSG_invalid_distance_code
  else IS.abind (IS.us (fun s => IS.iset_extra (IS.iset_offset s (IS.code_val here)) (Z.land (IS.code_op here) 15)))
         (fun _ => IS.abind (IA.set_mode IS.DISTEXT) (fun _ => IA.arm_DISTEXT IS.ivar_ref)).

Lemma arm_DIST_eq : forall w, IA.arm_DIST IS.ivar_ref w =
  IS.abind (IS.gs (fun s => s)) (fun s => dseq (IS.is_distcode s) (IS.is_distbits s) KDists dist_tail) w.
Proof. reflexivity. Qed.

Lemma tent_dist : forall h, code_rng h -> tent KDists (RBa.code_enc h) -> tsub KDists (RBa.c_op h) = false ->
  Z.land (RBa.c_op h) 64 = 0 ->
  0 <= Z.land (RBa.c_op h) 15 <= 13 /\ 1 <= RBa.c_val h /\ RBa.c_val h + 2 ^ Z.land (RBa.c_op h) 15 <= 32769.
Proof.
  intros h Hr Ht Hs H64. unfold tent in Ht. cbv zeta iota beta in Ht.
  rewrite (enc_op _ Hr), (enc_val _ Hr) in Ht.
  destruct Ht as (_ & H16 & H0).
  unfold tsub in Hs. apply Z.eqb_neq in Hs.
  destruct (Z.eq_dec (Z.land (RBa.c_op h) 16) 0) as [E|E].
  - exfalso. apply Hs. apply H0; assumption.
  - destruct (H16 E) as (A & B & C). split; [|split; assumption].
    split; [apply Z.land_nonneg; lia | exact A].
Qed.

Lemma arm_DIST_ok' : forall w q, icb w q -> RI.q_mode q = RI.M_DIST ->
  0 <= RI.u_length (RI.s_cur (RI.q_st q)) <= 258 ->
  step_ok (IA.arm_DIST IS.ivar_ref w) (RI.inf_DIST q).
Proof.
  intros w q Hb Hmode HL.
  pose proof Hb as [H Ht].
  pose proof (icore_tab w q H) as (_ & Hdb).
  rewrite arm_DIST_eq. cbn [IS.abind IS.gs].
  unfold RI.inf_DIST. cbv zeta.
  destruct (RI.inf_decode RI.sub_dist (RI.tbl_of (RI.q_st q) (RI.t_distcode (RI.s_tab (RI.q_st q))))
              (RI.t_distbits (RI.s_tab (RI.q_st q))) (RI.q_br q)) as [h b' nb|b'|] eqn:Ed.
  3: { exact I. }
  2: { apply step_ok_leave_ok. exact (icore_ret w q H). }
  rewrite <- Hdb in Ed.
  destruct (dseq_sim KDists (IS.is_distcode (IS.w_s w)) (IS.is_distbits (IS.w_s w))
              (RI.tbl_of (RI.q_st q) (RI.t_distcode (RI.s_tab (RI.q_st q)))) dist_tail w q h b' nb
              Hb (proj2 Ht) Ed)
    as (W1 & E1 & Hc1 & Hr & Hte & Hts).
  rewrite E1. unfold dist_tail.
  rewrite (enc_op _ Hr), (enc_val _ Hr).
  destruct (Z.eqb_spec (Z.land (RBa.c_op h) 64) 0) as [E64|E64].
  2: { apply step_ok_bad. reflexivity. }
  cbn [negb].
  rewrite abind_us; cbv beta.
  pose proof (B_offext _ _ (RBa.c_val h) (RBa.c_val h) (Z.land (RBa.c_op h) 15) (Z.land (RBa.c_op h) 15)
                Hc1 eq_refl eq_refl) as Hc2.
  match type of Hc2 with icb ?W ?Q => set (W2 := W) in *; set (Q2 := Q) in * end.
  cbn [IS.abind IA.set_mode IS.us].
  destruct (tent_dist h Hr Hte Hts E64) as (HE & HO1 & HO2).
  apply arm_DISTEXT_ok'; [| reflexivity | | | |].
  - apply B_mode; [exact Hc2 | | reflexivity].
    apply (icore_not_head _ _ (proj1 Hc2)). change (RI.q_mode q <> RI.M_HEAD). rewrite Hmode. discriminate.
  - rt_cbn. exact HL.
  - rt_cbn. exact HE.
  - rt_cbn. exact HO1.
  - rt_cbn. exact HO2.
Qed.

(* ------------------------------------------------------------------------- *)
(* LENEXT                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma arm_LENEXT_ok' : forall w q, icb w q -> RI.q_mode q = RI.M_LENEXT ->
  0 <= RI.u_extra (RI.s_cur (RI.q_st q)) <= 5 -> 0 <= RI.u_length (RI.s_cur (RI.q_st q)) ->
  RI.u_length (RI.s_cur (RI.q_st q)) + 2 ^ RI.u_extra (RI.s_cur (RI.q_st q)) <= 259 ->
  step_ok (IA.arm_LENEXT IS.ivar_ref w) (RI.inf_LENEXT q).
Proof.
  intros w q Hb Hmode HE HL0 HL1.
  pose proof Hb as [H Ht].
  pose proof (icore_cur w q H) as (EL & EO & EE & EB & _).
  assert (Hnh : RI.q_mode q <> RI.M_HEAD) by (rewrite Hmode; discriminate).
  unfold RI.inf_LENEXT. cbv zeta.
  unfold IA.arm_LENEXT. cbn [IS.abind IS.gs].
  rewrite EE.
  destruct (Z.eqb_spec (RI.u_extra (RI.s_cur (RI.q_st q))) 0) as [E0|E0].
  - cbn [negb IS.abind IS.aret].
    rewrite abind_aux; cbv beta.
    cbn [IS.abind IA.set_mode IS.us].
    pose proof (B_was _ _ (IS.is_length (IS.w_s w)) (RI.u_length (RI.s_cur (RI.q_st q))) Hb EL) as Hc1.
    apply arm_DIST_ok'; [| reflexivity |].
    + apply B_mode; [exact Hc1 | | reflexivity].
      apply (icore_not_head _ _ (proj1 Hc1)). exact Hnh.
    + rt_cbn. rewrite E0 in HL1. cbn [Z.pow Z.pow_pos Pos.iter] in HL1. lia.
  - destruct (RI.inf_nb (RI.u_extra (RI.s_cur (RI.q_st q))) (RI.q_br q)) as [b1|b1] eqn:Enb.
    2: { apply step_ok_leave_ok. exact (icore_ret w q H). }
    set (E := RI.u_extra (RI.s_cur (RI.q_st q))) in *.
    cbn [negb].
    destruct (needbits_sim w (RI.q_br q) b1 E (icb_brel _ _ Hb) ltac:(lia) Enb)
      as (E1 & Hb1 & HE1 & Hin1 & Hsum1).
    pose proof (nb_bnx _ _ _ Enb) as (Hbn1 & _).
    assert (Hc1 : icb (wbr w b1) (RI.qset_br q b1)) by (apply B_br; [exact Hb|exact Hb1|exact Hin1|exact Hsum1|lia]).
    rewrite abind_assoc. astep E1.
    rewrite abind_assoc. astep (bits_sim (wbr w b1) b1 E Hb1 ltac:(lia)).
    pose proof (bits_of_range E b1 ltac:(lia)) as Hv.
    set (v := RB.br_bits_of E b1) in *.
    rewrite abind_assoc. rewrite abind_us; cbv beta.
    assert (Hc2 : icb (IS.wset_s (wbr w b1) (IS.iset_length (IS.w_s (wbr w b1)) (wrap32 (IS.is_length (IS.w_s (wbr w b1)) + v))))
                      (RI.qset_st (RI.qset_br q b1) (RI.set_length (RI.q_st (RI.qset_br q b1))
                                     (RI.u_length (RI.s_cur (RI.q_st q)) + v)))).
    { apply B_length; [exact Hc1|]. rewrite wbr_s, EL. apply wrap32_id. lia. }
    match type of Hc2 with icb ?W ?Q => set (W2 := W) in *; set (Q2 := Q) in * end.
    destruct (dropbits_sim W2 b1 E (icb_brel _ _ Hc2) ltac:(lia)) as (E3 & Hb3).
    rewrite abind_assoc. astep E3.
    assert (Hc3 : icb (wbr W2 (RB.br_dropbits E b1)) (RI.qset_br Q2 (RB.br_dropbits E b1))).
    { apply B_br; [exact Hc2 | exact Hb3 | reflexivity | reflexivity |].
      rewrite drop_bnx. change (RI.q_br Q2) with b1. lia. }
    astep_back.
    pose proof (B_addback _ _ E Hc3) as Hc4.
    match type of Hc4 with icb ?W ?Q => set (W4 := W) in *; set (Q4 := Q) in * end.
    rewrite abind_aux; cbv beta.
    assert (Hc5 : icb (IS.wset_s W4 (IS.iset_was (IS.w_s W4) (IS.is_length (IS.w_s W4))))
                      (RI.qset_st Q4 (RI.set_was (RI.q_st Q4) (RI.u_length (RI.s_cur (RI.q_st Q4)))))).
    { apply B_was; [exact Hc4|]. exact (proj1 (icore_cur _ _ (proj1 Hc4))). }
    cbn [IS.abind IA.set_mode IS.us].
    apply arm_DIST_ok'; [| reflexivity |].
    + apply B_mode; [exact Hc5 | | reflexivity].
      apply (icore_not_head _ _ (proj1 Hc5)). exact Hnh.
    + rt_cbn. fold E. fold v. lia.
Qed.
