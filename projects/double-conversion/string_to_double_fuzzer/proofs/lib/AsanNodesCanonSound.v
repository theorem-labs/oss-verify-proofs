(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanNodesCanon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.

Section FPW. Context {fx : PropExec.FPState}.

Lemma u_eaddz_any : forall E a z, 0 <= u (edenot E a) + z < 2 ^ 64 -> u (edenot E (eaddz a z)) = u (edenot E a) + z.
Proof.
  intros E a z Hb. unfold eaddz. rewrite mkAlu_denot. rewrite u_add64. cbn [edenot].
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Section Canon.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable LINV : (word -> option byte) -> Prop.
  Variable FS0 : Fs.Fs.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH LINV FS0) (only parsing).

  Lemma kn_node_sound' : forall (node : acs -> option acs),
    (forall cs cs' E R FULL model, CSOK E cs R FULL model -> node cs = Some cs' ->
        exists k', cs' = set_kn cs k' /\ know_ok SEGS E (Mr A argH E cs model FULL) k') ->
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always node.
  Proof.
    intros node Hnode cs cs' E R FULL model T HC _ Hn Hk.
    destruct (Hnode cs cs' E R FULL model HC Hn) as (k' & -> & HK').
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity]. apply cs_ok_set_kn; [exact HC | exact HK'].
  Qed.

  (* [comment removed for export] *)
  Section RS.
    Variables (E : env) (M : word -> option byte) (B B' : expr) (lo hi d : Z).
    Hypothesis HB : u (edenot E B') = u (edenot E B) + d.

    Lemma rs_sa_estart : forall a, estart E (CAN.rs_sa B lo hi B' d a) = estart E a.
    Proof.
      intros [b o]. unfold CAN.rs_sa.
      destruct (expr_eqb b B && Z.leb lo o && Z.ltb o hi)%bool eqn:Hc; [|reflexivity].
      apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hb _]. apply expr_eqb_eq in Hb. subst b.
      unfold estart. cbn [a_base a_off]. rewrite HB. lia.
    Qed.
    Lemma rs_sa_adenot : forall a, adenot E (CAN.rs_sa B lo hi B' d a) = adenot E a.
    Proof.
      intros a. pose proof (rs_sa_estart a) as He.
      destruct a as [b o]. destruct (CAN.rs_sa B lo hi B' d (SA b o)) as [b' o'] eqn:Hr.
      rewrite !APSX.adenot_SA. rewrite He. reflexivity.
    Qed.
    Lemma rs_sa_flat : forall a n, flat E (CAN.rs_sa B lo hi B' d a) n <-> flat E a n.
    Proof. intros a n. unfold flat. rewrite rs_sa_estart. tauto. Qed.

    Lemma rs_k_ok : forall K, kentry_ok SEGS E M K -> kentry_ok SEGS E M (CAN.rs_k B lo hi B' d K).
    Proof.
      intros K HK. destruct K as [a w v|a n|a n j|lo' hi'|e m|e lo' hi'|a n|a1 n1 a2 n2|a n c|a n]; cbn [CAN.rs_k kentry_ok] in *;
        rewrite ?rs_sa_adenot, ?rs_sa_estart, ?rs_sa_flat; exact HK.
    Qed.
    Lemma rs_know_ok : forall k, know_ok SEGS E M k -> know_ok SEGS E M (map (CAN.rs_k B lo hi B' d) k).
    Proof.
      intros k HK. unfold know_ok in *. apply Forall_map. eapply Forall_impl; [|exact HK]. intros K; apply rs_k_ok.
    Qed.
  End RS.

  Theorem node_rsbase_sound : forall B lo hi B' d,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_rsbase cs B lo hi B' d).
  Proof.
    intros B lo hi B' d. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn.
    unfold CAN.node_rsbase in Hn. cbv zeta in Hn.
    destruct (xlo (kn cs) B) as [blo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) B) as [bhi|] eqn:Hhi; [|discriminate].
    destruct (Z.leb 0 (blo + d) && Z.ltb (bhi + d) two64 && expr_vars_lt (nxt cs) B' && respell_ok (kn cs) (eaddz B d) B')%bool eqn:Hc;
      [|discriminate].
    injection Hn as <-. eexists; split; [reflexivity|].
    apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1. unfold two64 in H1.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) B blo HK Hlo) as L. pose proof (xhi_sound SEGS E _ (kn cs) B bhi HK Hhi) as H.
    pose proof (respell_ok_sound SEGS E _ (kn cs) (eaddz B d) B' HK Hok) as Heq.
    assert (HB : u (edenot E B') = u (edenot E B) + d) by (rewrite <- Heq; apply u_eaddz_any; lia).
    exact (rs_know_ok E _ B B' lo hi d HB (kn cs) HK).
  Qed.

  (* [comment removed for export] *)
  Theorem node_addzero_sound : forall b o n,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_addzero cs b o n).
  Proof.
    intros b o n. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn.
    unfold CAN.node_addzero in Hn. cbv zeta in Hn.
    destruct (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && flat_x (kn cs) b o n && kzero_x (kn cs) (kn cs) b o n)%bool eqn:Hc; [|discriminate].
    injection Hn as <-. eexists; split; [reflexivity|].
    apply andb_prop in Hc as [Hc Hz]. apply andb_prop in Hc as [_ Hf].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (APSX.kzero_x_sound SEGS E _ (kn cs) (kn cs) b o n HK HK Hz) as (Z0 & Lo & Hi).
    destruct (APSX.w_flat_x_sound SEGS E _ (kn cs) b o n HK Hf) as (F1 & F2 & F3).
    constructor; [|exact HK]. cbn [kentry_ok]. split; [|exact Z0].
    unfold flat. pose proof (u64_range (edenot E n)). unfold elenZ in *. lia.
  Qed.

  Theorem node_addwr_sound : forall b o n,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_addwr A cs b o n).
  Proof.
    intros b o n. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn.
    unfold CAN.node_addwr in Hn. cbv zeta in Hn.
    destruct (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && flat_x (kn cs) b o n && kwritable_x A (kn cs) (kn cs) b o n)%bool eqn:Hc; [|discriminate].
    injection Hn as <-. eexists; split; [reflexivity|].
    apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [_ Hf].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (APSX.kwritable_x_sound SEGS A E _ (kn cs) (kn cs) b o n HK HK Hw) as (W0 & Lo & Hi).
    destruct (APSX.w_flat_x_sound SEGS E _ (kn cs) b o n HK Hf) as (F1 & F2 & F3).
    constructor; [|exact HK]. cbn [kentry_ok]. split.
    - unfold flat. pose proof (u64_range (edenot E n)). unfold elenZ in *. lia.
    - intros dd m Hd Hdm. destruct m as [|m']; [reflexivity|]. remember (S m') as m eqn:Hm'.
      assert (Hm : Z.of_nat (Z.to_nat (elenZ E n)) <= elenZ E n) by lia.
      pose proof (W0 (Z.to_nat (elenZ E n)) Hm) as Wall.
      refine (APSX.store_ok_sub SEGS _ (Z_to_bv 64 (estart E (SA b o))) (Z.to_nat (elenZ E n)) _ m _ Wall _ _);
        rewrite ?u64_lit by lia; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma upd_nth_length {T} : forall (l : list T) i x, length (CAN.upd_nth l i x) = length l.
  Proof. induction l as [|y r IH]; intros [|i] x; cbn [CAN.upd_nth length]; try reflexivity. rewrite IH. reflexivity. Qed.
  Lemma existsb_upd {T} : forall (P : T -> bool) l i p p',
    nth_error l i = Some p -> P p' = P p -> existsb P (CAN.upd_nth l i p') = existsb P l.
  Proof.
    intros P l. induction l as [|y r IH]; intros [|i] p p' Hn Hp; cbn [nth_error] in Hn; try discriminate;
      cbn [CAN.upd_nth existsb].
    - injection Hn as ->. rewrite Hp. reflexivity.
    - rewrite (IH i p p' Hn Hp). reflexivity.
  Qed.
  Lemma flat_map_upd {T U} : forall (f : T -> list U) l i p p' g,
    nth_error l i = Some p -> f p' = f p -> flat_map f (CAN.upd_nth l i p' ++ g) = flat_map f (l ++ g).
  Proof.
    intros f l. induction l as [|y r IH]; intros [|i] p p' g Hn Hp; cbn [nth_error] in Hn; try discriminate;
      cbn [CAN.upd_nth app flat_map].
    - injection Hn as ->. rewrite Hp. reflexivity.
    - rewrite (IH i p p' g Hn Hp). reflexivity.
  Qed.

  Theorem node_rsvis_sound : forall i e',
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_rsvis cs i e').
  Proof.
    intros i e' cs cs' E R FULL model T HC _ Hn Hk.
    unfold CAN.node_rsvis in Hn. cbv zeta in Hn.
    destruct (nth_error (a_vis cs) i) as [[b n]|] eqn:Hi; [|discriminate].
    destruct (expr_vars_lt (nxt cs) e' && respell_ok (kn cs) b e')%bool eqn:Hc; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [_ Hok].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (respell_ok_sound SEGS E _ (kn cs) b e' HK Hok) as Heq.
    set (cs' := ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (CAN.upd_nth (a_vis cs) i (e', n))
                    (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)).
    assert (Huv : uE E e' = uE E b) by (unfold uE; rewrite Heq; reflexivity).
    assert (Vis : forall z, in_vis E cs' z = in_vis E cs z).
    { intros z. unfold in_vis. cbn [cs' a_vis]. eapply existsb_upd; [exact Hi|]. cbn [fst snd]. rewrite Huv. reflexivity. }
    assert (Sh : forall z, in_sh A E cs' z = in_sh A E cs z).
    { intros z. unfold in_sh. cbn [cs' a_vis]. eapply existsb_upd; [exact Hi|]. unfold sh_lo, sh_hi. cbn [fst snd]. rewrite Huv. reflexivity. }
    assert (Al : allowA A E cs' = allowA A E cs).
    { unfold allowA. cbn [cs' a_vis a_ghost]. eapply flat_map_upd; [exact Hi|]. unfold allow1, sh_lo, sh_hi. cbn [fst snd]. rewrite Huv. reflexivity. }
    assert (Gh : forall z, in_ghost E cs' z = in_ghost E cs z) by reflexivity.
    assert (Hid : forall a, hid A argH E cs' model a = hid A argH E cs model a).
    { intros a. unfold hid, vis, in_allow. rewrite Vis, Sh. reflexivity. }
    assert (HM : Mr A argH E cs' model FULL = Mr A argH E cs model FULL).
    { unfold Mr. apply functional_extensionality. intros a. unfold mrestrict. rewrite Hid. reflexivity. }
    assert (HC' : CSOK E cs' R FULL model).
    { destruct HC; constructor; cbn [cs' a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn];
        try assumption.
      - rewrite HM. exact co_know0.
      - rewrite Al. exact co_abytes0.
      - rewrite Al. exact co_minv0.
      - intros a Hh. rewrite Hid in Hh. exact (co_zero0 a Hh). }
    exact (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E)) HC' eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma rep_denot : forall E a x t, edenot E x = edenot E a -> edenot E (CAN.rep a x t) = edenot E t.
  Proof.
    intros E a x t Hx. induction t; cbn [CAN.rep];
      (destruct (expr_eqb _ a) eqn:Ha; [apply expr_eqb_eq in Ha; subst; exact Hx|]);
      try reflexivity; cbn [edenot]; rewrite ?IHt, ?IHt1, ?IHt2; reflexivity.
  Qed.

  Theorem node_rscase_sound : forall r e a,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_rscase cs r e a).
  Proof.
    intros r e a cs cs' E R FULL model T HC _ Hn Hk.
    unfold CAN.node_rscase in Hn. cbv zeta in Hn.
    destruct (xlo (kn cs) a) as [alo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) a) as [ahi|] eqn:Hhi; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?H] end.
    rename Hc into Hr0, H into Hall, H0 into Hw, H1 into Hl0, H2 into Hev, H3 into Hr1.
    apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr1. apply Z.leb_le in Hw. apply Z.leb_le in Hl0.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) a alo HK Hlo) as L. pose proof (xhi_sound SEGS E _ (kn cs) a ahi HK Hhi) as H.
    set (v := u (edenot E a)) in *.
    rewrite forallb_forall in Hall.
    specialize (Hall (Z.to_nat (v - alo))). rewrite in_seq in Hall.
    specialize (Hall ltac:(lia)). cbn beta in Hall.
    replace (alo + Z.of_nat (Z.to_nat (v - alo))) with v in Hall by lia.
    pose proof (respell_ok_sound SEGS E _ (kn cs) _ _ HK Hall) as Heq.
    assert (Hx : edenot E (ELit v) = edenot E a).
    { cbn [edenot]. unfold v. apply Z_to_bv_bv_unsigned. }
    rewrite !(rep_denot E a (ELit v)) in Heq by exact Hx.
    assert (HC' : CSOK E (set_reg cs r e) R FULL model).
    { destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
        try assumption; try reflexivity.
      apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq]. }
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E)) HC' eq_refl).
    exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma low3_val : forall E x, u (edenot E (CAN.low3 x)) = u (edenot E x) mod 8.
  Proof.
    intros E x. unfold CAN.low3. rewrite mkAlu_denot, u_sub64.
    replace (edenot E (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3)))) with (mul_div M_MUL (Z_to_bv 64 8) (edenot E (EAlu ALU_SRL x (ELit 3)))) by reflexivity.
    rewrite u_mul64, u_srl_lit. rewrite (u64_lit 8) by lia.
    pose proof (u64_range (edenot E x)) as Hx. set (X := u (edenot E x)) in *.
    replace ((3 mod two64) mod 64) with 3 by reflexivity.
    change (2 ^ 3) with 8.
    assert (H1 : 0 <= 8 * (X / 8) <= X) by (split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | apply Z.mul_div_le; lia]).
    rewrite (Z.mod_small (8 * (X / 8))) by lia.
    assert (E8 : X - 8 * (X / 8) = X mod 8) by (rewrite Z.mod_eq by lia; ring).
    rewrite E8. pose proof (Z.mod_pos_bound X 8 ltac:(lia)). apply Z.mod_small. lia.
  Qed.
  Lemma and7_val : forall E x, u (edenot E (EAlu ALU_AND x (ELit 7))) = u (edenot E x) mod 8.
  Proof.
    intros E x. cbn [edenot]. rewrite u_and64, (u64_lit 7) by lia.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
  Qed.
  Lemma low3_ok : forall E M k x lo hi,
    know_ok SEGS E M k ->
    match erange k (EAlu ALU_AND x (ELit 7)) with Some (l, h) => lo = Z.max l 0 /\ hi = Z.min h 7 | None => lo = 0 /\ hi = 7 end ->
    kentry_ok SEGS E M (KRange (CAN.low3 x) lo hi).
  Proof.
    intros E M k x lo hi HK H. cbn [kentry_ok]. rewrite low3_val.
    pose proof (Z.mod_pos_bound (u (edenot E x)) 8 ltac:(lia)) as Hb.
    destruct (erange k (EAlu ALU_AND x (ELit 7))) as [[l h]|] eqn:Hr.
    - destruct H as [-> ->]. pose proof (erange_sound SEGS E M k _ l h HK Hr) as Hs. rewrite and7_val in Hs. lia.
    - destruct H as [-> ->]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rup3_ok : forall E M x, u (edenot E x) < two64 - 8 -> kentry_ok SEGS E M (KRange (CAN.rup3 x) 0 7).
  Proof.
    intros E M x Hx. cbn [kentry_ok]. unfold CAN.rup3. rewrite mkAlu_denot, u_sub64.
    replace (edenot E (EMd M_MUL (ELit 8) (EAlu ALU_SRL (mkAlu ALU_ADD x (ELit 7)) (ELit 3))))
      with (mul_div M_MUL (Z_to_bv 64 8) (edenot E (EAlu ALU_SRL (mkAlu ALU_ADD x (ELit 7)) (ELit 3)))) by reflexivity.
    rewrite u_mul64, u_srl_lit. rewrite (u64_lit 8) by lia.
    rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite (u64_lit 7) by lia.
    pose proof (u64_range (edenot E x)) as Hr. set (X := u (edenot E x)) in *. unfold two64 in Hx.
    rewrite (Z.mod_small (X + 7)) by lia.
    replace ((3 mod two64) mod 64) with 3 by reflexivity. change (2 ^ 3) with 8.
    assert (H1 : X <= 8 * ((X + 7) / 8) <= X + 7).
    { pose proof (Z.mul_div_le (X + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (X + 7) 8 ltac:(lia)).
      pose proof (Z_div_mod_eq_full (X + 7) 8). lia. }
    rewrite (Z.mod_small (8 * ((X + 7) / 8))) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xt1 : forall E e c, xt_den E [(e, c)] = u (edenot E e) + c.
  Proof. intros. cbn [xt_den]. lia. Qed.
  Lemma zbv8_of_lit64 : forall c, Z_to_bv 8 (u (Z_to_bv 64 c)) = Z_to_bv 8 c.
  Proof.
    intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8).
    rewrite Z.mod_mod_divide; [reflexivity | exists (2 ^ 56); reflexivity].
  Qed.
  Lemma rdn1_of_M : forall M (a : word) b, M a = Some b -> rdn SEGS M a 1 = Some [b].
  Proof. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.
  Lemma find_byte_sound : forall E M allk k ab off w,
    know_ok SEGS E M allk -> know_ok SEGS E M k -> CAN.find_byte k allk ab off = Some w ->
    flat E (SA ab off) 1 ->
    rdn SEGS M (adenot E (SA ab off)) 1 = Some (word_to_le_bytes 1 (edenot E w)).
  Proof.
    intros E M allk k ab off w Hall. induction k as [|K k IH]; intros HK H Hfl; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hk]. cbn [CAN.find_byte] in H.
    destruct K as [a n v | | | | | | | | fa fl c | ]; try (exact (IH Hk H Hfl)).
    - (* [comment removed for export] *) destruct a as [b o]. destruct n as [|[|n]]; try (exact (IH Hk H Hfl)).
      destruct (expr_eqb b ab) eqn:Hb; [|exact (IH Hk H Hfl)]. destruct (Z.eqb_spec o off) as [Ho|Ho]; [|exact (IH Hk H Hfl)].
      cbn [andb] in H. injection H as <-. apply expr_eqb_eq in Hb. subst b o.
      cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & HR). exact HR.
    - (* [comment removed for export] *) destruct fa as [b o].
      destruct (expr_eqb b ab) eqn:Hb; [|exact (IH Hk H Hfl)]. destruct (Z.leb_spec o off) as [Ho|Ho]; [|exact (IH Hk H Hfl)].
      destruct (xlo allk fl) as [lo|] eqn:Hlo; [|exact (IH Hk H Hfl)].
      destruct (Z.ltb_spec (off - o) lo) as [Hol|Hol]; [|exact (IH Hk H Hfl)].
      cbn [andb] in H. injection H as <-. apply expr_eqb_eq in Hb. subst b.
      pose proof (xlo_sound SEGS E M allk fl lo Hall Hlo) as Xlo.
      cbn [kentry_ok] in HKK. destruct HKK as [Hff HF]. unfold elenZ in HF, Hff.
      specialize (HF (off - o) ltac:(lia)). unfold estart in HF. cbn [a_base a_off] in HF.
      replace (u (edenot E ab) + o + (off - o)) with (u (edenot E ab) + off) in HF by lia.
      assert (Ha : adenot E (SA ab off) = Z_to_bv 64 (u (edenot E ab) + off)).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA ab off))). rewrite (flat_u E (SA ab off) 1 Hfl). reflexivity. }
      rewrite Ha. rewrite (rdn1_of_M M _ _ HF). cbn [word_to_le_bytes Z_to_le_bytes edenot]. rewrite zbv8_of_lit64. reflexivity.
  Qed.
  Theorem node_bytespell_sound : forall a off V,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_bytespell cs a off V).
  Proof.
    intros a off V. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_bytespell in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (split_lit (eaddz a off)) as [ab ao].
    destruct (CAN.find_byte (kn cs) (kn cs) ab ao) as [w|] eqn:Hfb; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hc G2]. apply andb_prop in Hc as [Hfl G1].
    set (M := Mr A argH E cs model FULL) in *.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G2) as L2.
    rewrite !xt1 in L1, L2. rewrite (extK_denot SEGS E M (kn cs) w HK) in L1, L2.
    assert (HV : edenot E V = edenot E w) by (apply bv_eq; lia).
    destruct (flat_x_sound SEGS E M (kn cs) ab ao (ELit 1) HK Hfl) as (F1 & F2 & _).
    replace (u (edenot E (ELit 1))) with 1 in F2 by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    assert (Hflat : flat E (SA ab ao) 1) by (unfold flat; lia).
    eexists. split; [reflexivity|]. constructor; [|exact HK].
    cbn [kentry_ok]. split; [lia|]. split; [exact Hflat|].
    rewrite HV. exact (find_byte_sound E M (kn cs) (kn cs) ab ao w HK HK Hfb Hflat).
  Qed.

  (* [comment removed for export] *)
  Theorem node_bytecase_sound : forall a off V atom,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_bytecase cs a off V atom).
  Proof.
    intros a off V atom. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_bytecase in Hn. cbv zeta in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (split_lit (eaddz a off)) as [ab ao].
    destruct (CAN.find_byte (kn cs) (kn cs) ab ao) as [w|] eqn:Hfb; [|discriminate].
    destruct (xlo (kn cs) atom) as [alo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) atom) as [ahi|] eqn:Hhi; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?H] end.
    rename Hc into Hfl, H into Hall, H0 into Hw, H1 into Hl0, H2 into Hev.
    apply Z.leb_le in Hw. apply Z.leb_le in Hl0.
    set (M := Mr A argH E cs model FULL) in *.
    pose proof (xlo_sound SEGS E _ (kn cs) atom alo HK Hlo) as L. pose proof (xhi_sound SEGS E _ (kn cs) atom ahi HK Hhi) as H.
    set (v := u (edenot E atom)) in *.
    rewrite forallb_forall in Hall.
    specialize (Hall (Z.to_nat (v - alo))). rewrite in_seq in Hall.
    specialize (Hall ltac:(lia)). cbn beta in Hall.
    replace (alo + Z.of_nat (Z.to_nat (v - alo))) with v in Hall by lia.
    pose proof (respell_ok_sound SEGS E _ (kn cs) _ _ HK Hall) as Heq.
    assert (Hx : edenot E (ELit v) = edenot E atom).
    { cbn [edenot]. unfold v. apply Z_to_bv_bv_unsigned. }
    rewrite !(rep_denot E atom (ELit v)) in Heq by exact Hx.
    rewrite (extK_denot SEGS E M (kn cs) w HK) in Heq.
    destruct (flat_x_sound SEGS E M (kn cs) ab ao (ELit 1) HK Hfl) as (F1 & F2 & _).
    replace (u (edenot E (ELit 1))) with 1 in F2 by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    assert (Hflat : flat E (SA ab ao) 1) by (unfold flat; lia).
    eexists. split; [reflexivity|]. constructor; [|exact HK].
    cbn [kentry_ok]. split; [lia|]. split; [exact Hflat|].
    rewrite <- Heq. exact (find_byte_sound E M (kn cs) (kn cs) ab ao w HK HK Hfb Hflat).
  Qed.

  (* [comment removed for export] *)
  Theorem node_rsval_sound : forall b o e,
    node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_rsval cs b o e).
  Proof.
    intros b o e. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_rsval in Hn. cbv zeta in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (expr_vars_lt (nxt cs) e && forallb _ (kn cs))%bool eqn:Hc; [|discriminate].
    injection Hn as <-. apply andb_prop in Hc as [_ Hall]. rewrite forallb_forall in Hall.
    eexists; split; [reflexivity|].
    unfold know_ok. apply Forall_map. apply Forall_forall. intros K Hin.
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    specialize (Hall K Hin).
    destruct K as [[b' o'] w v| | | | | | | | | ]; cbn [CAN.rs_val]; try exact HKK.
    destruct (expr_eqb b' b && Z.eqb o' o)%bool eqn:Hm; [|exact HKK].
    pose proof (respell_ok_sound SEGS E _ (kn cs) v e HK Hall) as Heq.
    cbn [kentry_ok] in HKK |- *. rewrite <- Heq. exact HKK.
  Qed.

  Theorem node_low3_sound : forall x, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_low3 cs x).
  Proof.
    intros x. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_low3 in Hn.
    destruct (expr_vars_lt (nxt cs) x); [|discriminate].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (erange (kn cs) (EAlu ALU_AND x (ELit 7))) as [[l h]|] eqn:Hr; injection Hn as <-;
      (eexists; split; [reflexivity|]); (constructor; [|exact HK]); eapply low3_ok; try exact HK; rewrite Hr; auto.
  Qed.
  Theorem node_rup3_sound : forall x, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_rup3 cs x).
  Proof.
    intros x. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_rup3 in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xhi (kn cs) x) as [h|] eqn:Hh; [|discriminate].
    destruct (expr_vars_lt (nxt cs) x && Z.ltb h (two64 - 8))%bool eqn:Hc; [|discriminate].
    injection Hn as <-. apply andb_prop in Hc as [_ Hc]. apply Z.ltb_lt in Hc.
    pose proof (xhi_sound SEGS E _ (kn cs) x h HK Hh) as Hx.
    eexists; split; [reflexivity|]. constructor; [apply rup3_ok; lia | exact HK].
  Qed.
  Theorem node_addzero0_sound : forall b o n, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_addzero0 cs b o n).
  Proof.
    intros b o n. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_addzero0 in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xhi (kn cs) n) as [[|hp|hn]|] eqn:Hh; try discriminate.
    destruct (base_range (kn cs) b) as [[blo bhi]|] eqn:Hb; [|discriminate].
    destruct (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb 0 (blo + o) && Z.ltb (bhi + o) two64)%bool eqn:Hc; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [_ H1]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (xhi_sound SEGS E _ (kn cs) n 0 HK Hh) as Hn0.
    pose proof (base_range_sound SEGS E _ (kn cs) b blo bhi HK Hb) as [Bl Bh].
    eexists; split; [reflexivity|]. constructor; [|exact HK].
    cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off]. unfold two64 in H2.
    pose proof (u64_range (edenot E n)). split; [lia|]. intros i Hi. lia.
  Qed.
  Theorem node_kimgcut_sound : forall a n, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => Some (set_kn cs (kimg_cut (kn cs) a n))).
  Proof.
    intros a n. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. injection Hn as <-.
    eexists; split; [reflexivity|]. apply APSX.kimg_cut_sound. exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  (* [comment removed for export] *)
  Lemma probe_val : forall E d, u (edenot E (EAlu ALU_SLTU d (ELit 1))) = if u (edenot E d) <? 1 then 1 else 0.
  Proof.
    intros E d. cbn [edenot]. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite (u64_lit 1) by lia.
    destruct (u (edenot E d) <? 1); [apply u64_lit; lia | apply u64_lit; lia].
  Qed.
  Lemma lowp_fact_ok : forall E M k x P r K,
    know_ok SEGS E M k -> u (edenot E P) = (if u (edenot E x) mod 8 <? 1 then 1 else 0) ->
    erange k P = r -> CAN.lowp_fact x r = Some K -> kentry_ok SEGS E M K.
  Proof.
    intros E M k x P r K HK HP Hr HF. unfold CAN.lowp_fact in HF. destruct r as [[lo hi]|]; [|discriminate].
    pose proof (erange_sound SEGS E M k P lo hi HK Hr) as Hb. rewrite HP in Hb.
    pose proof (Z.mod_pos_bound (u (edenot E x)) 8 ltac:(lia)) as Hm.
    destruct (Z.eqb_spec hi 0) as [->|_].
    - injection HF as <-. cbn [kentry_ok]. rewrite and7_val. destruct (Z.ltb_spec (u (edenot E x) mod 8) 1); lia.
    - destruct (Z.eqb_spec lo 1) as [->|_]; [|discriminate]. injection HF as <-. cbn [kentry_ok]. rewrite and7_val.
      destruct (Z.ltb_spec (u (edenot E x) mod 8) 1); lia.
  Qed.
  Theorem node_lowp_sound : forall x, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_lowp cs x).
  Proof.
    intros x. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_lowp in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (expr_vars_lt (nxt cs) x); [|discriminate].
    assert (Praw : u (edenot E (CAN.probe_raw x)) = (if u (edenot E x) mod 8 <? 1 then 1 else 0)).
    { unfold CAN.probe_raw. rewrite probe_val. rewrite <- (low3_val E x). unfold CAN.low3. rewrite mkAlu_denot. reflexivity. }
    assert (Plow : u (edenot E (CAN.probe_low3 x)) = (if u (edenot E x) mod 8 <? 1 then 1 else 0)).
    { unfold CAN.probe_low3. rewrite probe_val, low3_val. reflexivity. }
    destruct (erange (kn cs) (CAN.probe_raw x)) as [r|] eqn:Er.
    - destruct (CAN.lowp_fact x (Some r)) as [K|] eqn:HF; [|discriminate]. injection Hn as <-.
      eexists; split; [reflexivity|]. constructor; [|exact HK]. exact (lowp_fact_ok E _ (kn cs) x _ _ K HK Praw Er HF).
    - destruct (CAN.lowp_fact x (erange (kn cs) (CAN.probe_low3 x))) as [K|] eqn:HF; [|discriminate]. injection Hn as <-.
      eexists; split; [reflexivity|]. constructor; [|exact HK]. exact (lowp_fact_ok E _ (kn cs) x _ _ K HK Plow eq_refl HF).
  Qed.

  (* [comment removed for export] *)
  Lemma sr3diff_val : forall E x, u (edenot E x) < two64 - 8 ->
    u (edenot E (CAN.sr3diff x)) = (u (edenot E x) + 7) / 8 - u (edenot E x) / 8.
  Proof.
    intros E x Hx. unfold CAN.sr3diff. rewrite mkAlu_denot, u_sub64. rewrite !u_srl_lit.
    rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite (u64_lit 7) by lia.
    pose proof (u64_range (edenot E x)) as Hr. set (X := u (edenot E x)) in *. unfold two64 in Hx.
    rewrite (Z.mod_small (X + 7)) by lia.
    replace ((3 mod two64) mod 64) with 3 by reflexivity. change (2 ^ 3) with 8.
    assert (H1 : X / 8 <= (X + 7) / 8) by (apply Z.div_le_mono; lia).
    assert (H2 : (X + 7) / 8 <= X / 8 + 1).
    { replace (X + 7) with (X - 1 + 1 * 8) by lia. rewrite Z.div_add by lia. pose proof (Z.div_le_mono (X - 1) X 8 ltac:(lia) ltac:(lia)). lia. }
    assert (H3 : 0 <= X / 8) by (apply Z.div_pos; lia).
    apply Z.mod_small. assert (X / 8 < 2 ^ 64) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.
  Lemma low3z_facts_ok : forall E M k x r Ks,
    know_ok SEGS E M k -> u (edenot E x) < two64 - 8 ->
    erange k (EAlu ALU_AND x (ELit 7)) = r -> CAN.low3z_facts x r = Some Ks -> know_ok SEGS E M (Ks ++ k).
  Proof.
    intros E M k x r Ks HK Hx Hr HF. unfold CAN.low3z_facts in HF. destruct r as [[lo hi]|]; [|discriminate].
    pose proof (erange_sound SEGS E M k _ lo hi HK Hr) as Hb. rewrite and7_val in Hb.
    pose proof (Z.mod_pos_bound (u (edenot E x)) 8 ltac:(lia)) as Hm.
    pose proof (u64_range (edenot E x)) as Hrg. set (X := u (edenot E x)) in *.
    pose proof (Z_div_mod_eq_full X 8) as HX.
    destruct (Z.eqb_spec hi 0) as [->|_].
    - injection HF as <-. cbn [app]. constructor; [|constructor; [|exact HK]].
      + cbn [kentry_ok]. rewrite (sr3diff_val E x Hx). fold X.
        assert (X mod 8 = 0) by lia. replace (X + 7) with (7 + (X / 8) * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
      + cbn [kentry_ok]. rewrite low3_val. fold X. lia.
    - destruct (Z.leb_spec 1 lo) as [Hlo|_]; [|discriminate]. injection HF as <-. cbn [app]. constructor; [|exact HK].
      cbn [kentry_ok]. rewrite (sr3diff_val E x Hx). fold X.
      replace (X + 7) with ((X mod 8 - 1) + (X / 8 + 1) * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small (X mod 8 - 1) 8) by lia. lia.
  Qed.
  Theorem node_low3z_sound : forall x, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => CAN.node_low3z cs x).
  Proof.
    intros x. apply kn_node_sound'. intros cs cs' E R FULL model HC Hn. unfold CAN.node_low3z in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xhi (kn cs) x) as [h|] eqn:Hh; [|discriminate].
    destruct (expr_vars_lt (nxt cs) x && Z.ltb h (two64 - 8))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [_ Hc]. apply Z.ltb_lt in Hc.
    pose proof (xhi_sound SEGS E _ (kn cs) x h HK Hh) as Hx.
    destruct (CAN.low3z_facts x (erange (kn cs) (EAlu ALU_AND x (ELit 7)))) as [Ks|] eqn:HF; [|discriminate]. injection Hn as <-.
    eexists; split; [reflexivity|]. exact (low3z_facts_ok E _ (kn cs) x _ Ks HK ltac:(lia) eq_refl HF).
  Qed.

  Theorem can_xn_ref_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (CAN.xn_ref A args).
  Proof.
    intros args.
    assert (NONE : node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun _ => None)) by (intros cs cs' E R FULL model TT _ _ H; discriminate H).
    destruct args as [|[op| | | | | | | ] rest]; try exact NONE. unfold CAN.xn_ref.
    destruct (Z.eqb op 0). { destruct rest as [|B [|[lo| | | | | | | ] [|[hi| | | | | | | ] [|B' [|[d| | | | | | | ] [|? ?]]]]]]; try exact NONE. apply node_rsbase_sound. }
    destruct (Z.eqb op 1). { destruct rest as [|b [|[o| | | | | | | ] [|n [|? ?]]]]; try exact NONE. apply node_addzero_sound. }
    destruct (Z.eqb op 2). { destruct rest as [|b [|[o| | | | | | | ] [|n [|? ?]]]]; try exact NONE. apply node_addwr_sound. }
    destruct (Z.eqb op 4). { destruct rest as [|[i| | | | | | | ] [|e' [|? ?]]]; try exact NONE. apply node_rsvis_sound. }
    destruct (Z.eqb op 5). { destruct rest as [|[r| | | | | | | ] [|e [|a [|? ?]]]]; try exact NONE. apply node_rscase_sound. }
    destruct (Z.eqb op 6). { destruct rest as [|[a| | | | | | | ] [|[n| | | | | | | ] [|? ?]]]; try exact NONE. apply node_kimgcut_sound. }
    destruct (Z.eqb op 7). { destruct rest as [|x [|? ?]]; try exact NONE. apply node_low3_sound. }
    destruct (Z.eqb op 8). { destruct rest as [|x [|? ?]]; try exact NONE. apply node_rup3_sound. }
    destruct (Z.eqb op 9). { destruct rest as [|a [|[off| | | | | | | ] [|V [|atom [|? ?]]]]]; try exact NONE. apply node_bytecase_sound. }
    destruct (Z.eqb op 10). { destruct rest as [|b [|[o| | | | | | | ] [|n [|? ?]]]]; try exact NONE. apply node_addzero0_sound. }
    destruct (Z.eqb op 11). { destruct rest as [|b [|[o| | | | | | | ] [|e [|? ?]]]]; try exact NONE. apply node_rsval_sound. }
    destruct (Z.eqb op 12). { destruct rest as [|x [|? ?]]; try exact NONE. apply node_lowp_sound. }
    destruct (Z.eqb op 13). { destruct rest as [|x [|? ?]]; try exact NONE. apply node_low3z_sound. }
    destruct (Z.eqb op 34). { destruct rest as [|a [|[off| | | | | | | ] [|V [|? ?]]]]; try exact NONE. apply node_bytespell_sound. }
    exact NONE.
  Qed.
  (* [comment removed for export] *)
  Theorem can_xn_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (CAN.xn A args).
  Proof.
    intros args cs cs' E R FULL model T HC Hal Hn Hk. rewrite CAN.xn_eq in Hn.
    exact (can_xn_ref_sound args cs cs' E R FULL model T HC Hal Hn Hk).
  Qed.
End Canon.
End FPW.
