(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BImMove BRegPoisoned.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_amm stops := wp_go 0x1bcf68 220%nat C_amemmove_eq C_amemmove stops.

Section AMM.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (d s n S : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hn : 0 <= n <= 2 ^ 40.
Hypothesis Hms : memrange s n.
Hypothesis Hmd : memrange d n.
Hypothesis Hsd : s < d.
Hypothesis Hoks : addr_ok M s n.
Hypothesis Hokd : addr_ok M d n.
Hypothesis Hshs : 0 < n -> shw_ok M s n.
Hypothesis Hshd : 0 < n -> shw_ok M d n.
Hypothesis Hrd : rd_ok M s n.
Hypothesis Hwr : wr_ok BSEGS M d n.
Hypothesis HS : B_IMG_END <= S - 2224 /\ S < 2 ^ 63.
Hypothesis HSz : S <= SB \/ HIMEM_BEG <= S - 2224.
Hypothesis Hfr : wr_ok BSEGS M (S - 2224) 2224.
Hypothesis Hdj : d + n <= S - 2224 \/ S <= d.

Definition KS : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17]%nat.
Definition KSI : list nat := [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22]%nat.
Definition FP (x : word) : Prop := inr x (S - 2224) 2224 \/ inr x d n.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' ->
  unch M M' FP -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition M1 : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (W (S + -2032 + 2024)) (word_to_le_bytes 8 (rget l0 1)))
    (W (S + -2032 + 2016)) (word_to_le_bytes 8 (rget l0 8)))
    (W (S + -2032 + 2008)) (word_to_le_bytes 8 (rget l0 9)))
    (W (S + -2032 + 2000)) (word_to_le_bytes 8 (rget l0 18)))
    (W (S + -2032 + 1992)) (word_to_le_bytes 8 (rget l0 19)))
    (W (S + -2032 + 1984)) (word_to_le_bytes 8 (rget l0 20)))
    (W (S + -2032 + 1976)) (word_to_le_bytes 8 (rget l0 21)))
    (W (S + -2032 + 1968)) (word_to_le_bytes 8 (rget l0 22)).

Definition SAVE_SLOTS : list (nat * Z) :=
  [(1%nat, 2024); (8%nat, 2016); (9%nat, 2008); (18%nat, 2000); (19%nat, 1992); (20%nat, 1984); (21%nat, 1976); (22%nat, 1968)].

(* [comment removed for export] *)
Definition FPlow (x : word) : Prop := inr x (S - 2224) 80.
Definition MI (M' : mem) : Prop := unch M1 M' FPlow /\ mem_grows M1 M'.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1, B_IMG_END in *. solve_grows. Qed.

Lemma M1_unch : unch M M1 FP.
Proof. unfold M1, B_IMG_END in *. solve_unch ltac:(unfold FP, inr in *; lia). Qed.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma M1_saved : forall k off, In (k, off) SAVE_SLOTS -> cell BSEGS M1 (S + -2032 + off) 8 (rget l0 k).
Proof.
  intros k off Hin. unfold B_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Definition FPstk (x : word) : Prop := inr x (S - 2224) 2224.

Lemma FPstk_app : forall y, FPstk y -> B_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold FPstk, inr in Hy. lia. Qed.
Lemma FPstk_nosh : forall y, FPstk y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof. intros y Hy. unfold FPstk, inr in Hy. lia. Qed.

Lemma MI_stk : forall M', MI M' -> unch M M' FPstk /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. split.
  - apply (unch_trans M M1 M').
    + unfold M1, B_IMG_END in *. solve_unch ltac:(unfold FPstk, inr in *; lia).
    + eapply unch_weaken; [exact HU|]. intros x Hx. unfold FPlow, FPstk, inr in *. lia.
  - eapply mem_grows_trans; [apply M1_grows | exact HG].
Qed.

Lemma MI_final : forall M', MI M' -> unch M M' FP /\ mem_grows M M'.
Proof.
  intros M' HMI. destruct (MI_stk _ HMI) as [HU HG]. split; [|exact HG].
  eapply unch_weaken; [exact HU|]. intros x Hx. left. exact Hx.
Qed.

Lemma MI_saved : forall M' k off, MI M' -> In (k, off) SAVE_SLOTS ->
  cell BSEGS M' (S + -2032 + off) 8 (rget l0 k).
Proof.
  intros M' k off [HU HG] Hin. unfold B_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply M1_saved; exact Hin];
    unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
    try lia; intros x Hx; unfold FPlow, inr in *; lia.
Qed.

Lemma MI_rt : forall M', MI M' -> rt_ok M'.
Proof. intros M' HMI. destruct (MI_stk _ HMI) as [HU _]. eapply rt_ok_unch; [exact HU | apply FPstk_app | exact Hrt]. Qed.

Lemma s_bounds : 0 <= s /\ s + n + 8 <= HIMEM_END /\ 0 <= d /\ d + n + 8 <= HIMEM_END.
Proof.
  destruct Hms as [_ Hr1]. destruct Hmd as [_ Hr2]. unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia.
Qed.

Lemma MI_oks : forall M', MI M' -> addr_ok M' s n.
Proof.
  intros M' HMI. destruct (MI_stk _ HMI) as [HU _]. pose proof s_bounds as (H1 & H2 & H3 & H4).
  eapply addr_ok_unch; [exact HU | lia | lia | apply FPstk_nosh | exact Hoks].
Qed.
Lemma MI_okd : forall M', MI M' -> addr_ok M' d n.
Proof.
  intros M' HMI. destruct (MI_stk _ HMI) as [HU _]. pose proof s_bounds as (H1 & H2 & H3 & H4).
  eapply addr_ok_unch; [exact HU | lia | lia | apply FPstk_nosh | exact Hokd].
Qed.
Lemma MI_rd : forall M' a k, MI M' -> rd_ok M a k -> rd_ok M' a k.
Proof. intros M' a k HMI H. destruct (MI_stk _ HMI) as [_ HG]. eapply rd_ok_grows; [exact HG | exact H]. Qed.
Lemma MI_wr : forall M' a k, MI M' -> wr_ok BSEGS M a k -> wr_ok BSEGS M' a k.
Proof. intros M' a k HMI H. destruct (MI_stk _ HMI) as [_ HG]. eapply wr_ok_grows; [exact HG | exact H]. Qed.

Ltac pose_saved HMI :=
  pose proof (MI_saved _ 1%nat 2024 HMI ltac:(cbv; tauto)) as Csv1;
  pose proof (MI_saved _ 8%nat 2016 HMI ltac:(cbv; tauto)) as Csv8;
  pose proof (MI_saved _ 9%nat 2008 HMI ltac:(cbv; tauto)) as Csv9;
  pose proof (MI_saved _ 18%nat 2000 HMI ltac:(cbv; tauto)) as Csv18;
  pose proof (MI_saved _ 19%nat 1992 HMI ltac:(cbv; tauto)) as Csv19;
  pose proof (MI_saved _ 20%nat 1984 HMI ltac:(cbv; tauto)) as Csv20;
  pose proof (MI_saved _ 21%nat 1976 HMI ltac:(cbv; tauto)) as Csv21;
  pose proof (MI_saved _ 22%nat 1968 HMI ltac:(cbv; tauto)) as Csv22.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI l0 l /\ rget l 2 = W (S - 2144)
  /\ rget l 10 = W d /\ rget l 11 = W s /\ rget l 12 = W n.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H10 & ?H11 & ?H12); regs_open l Hl.

Ltac prove_stable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Lemma final : forall l M', MI M' -> stable l -> reach BSEGS rom (Z_to_bv 64 0x1bd048) l M' Post.
Proof.
  intros l M' HMI Hst. pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1). unfold HIMEM_END in *.
  open_stable Hst l. subst sp a0 a1 a2.
  wp_amm (@nil Z).
  replace (Z_to_bv 64 1899936) with (Z_to_bv 64 0x1cfda0) by reflexivity.
  eapply (imemmove_cps rom Post M' d s n); [lia | lia | lia | apply (MI_rd _ _ _ HMI Hrd) | apply (MI_wr _ _ _ HMI Hwr)
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' Hl' Hse' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1822796) 0) with (Z_to_bv 64 0x1bd04c) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (Hsv : forall k off, In (k, off) SAVE_SLOTS -> cell BSEGS M'' (S + -2032 + off) 8 (rget l0 k)).
  { intros k off Hin. unfold B_IMG_END in *.
    eapply cell_unch; [exact HU' | | | | apply (MI_saved _ _ _ HMI Hin)];
      unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
      try lia; intros x Hx; unfold BImMove.FP, inr in *; lia. }
  pose proof (Hsv 1%nat 2024 ltac:(cbv; tauto)) as Csv1. pose proof (Hsv 8%nat 2016 ltac:(cbv; tauto)) as Csv8.
  pose proof (Hsv 9%nat 2008 ltac:(cbv; tauto)) as Csv9. pose proof (Hsv 18%nat 2000 ltac:(cbv; tauto)) as Csv18.
  pose proof (Hsv 19%nat 1992 ltac:(cbv; tauto)) as Csv19. pose proof (Hsv 20%nat 1984 ltac:(cbv; tauto)) as Csv20.
  pose proof (Hsv 21%nat 1976 ltac:(cbv; tauto)) as Csv21. pose proof (Hsv 22%nat 1968 ltac:(cbv; tauto)) as Csv22.
  clear Hsv. unfold B_IMG_END in *.
  wp_amm (@nil Z). rewrite ?addi_W. replace (S - 2144 + 112) with (S + -2032) by lia. mem_auto.
  destruct (MI_final _ HMI) as [HU HG].
  apply K; [reflexivity | | | eapply mem_grows_trans; eassumption].
  - same_fix Hse. rewrite H0sp. f_equal. lia.
  - eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU'|]. intros x Hx. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma dst_rp : forall l M', MI M' -> stable l -> 0 < n -> reach BSEGS rom (Z_to_bv 64 0x1bd26c) l M' Post.
Proof.
  intros l M' HMI Hst Hn0. unfold B_IMG_END in *.
  open_stable Hst l. subst sp a0 a1 a2.
  wp_amm (@nil Z).
  replace (Z_to_bv 64 1834564) with (Z_to_bv 64 0x1bfe44) by reflexivity.
  eapply (regpoisoned_cps rom Post M' d n (S - 2144));
    [ apply (MI_rt _ HMI) | exact Hmd | lia | apply (MI_okd _ HMI) | unfold B_IMG_END; lia | lia
    | eapply wr_ok_sub; [apply (MI_wr _ _ _ HMI Hfr) | lia | lia]
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' Hl' Hse' H10' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1823360) 0) with (Z_to_bv 64 0x1bd280) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  assert (HMI2 : MI M'').
  { destruct HMI as [HU1 HG1]. split; [|eapply mem_grows_trans; eassumption]. eapply unch_trans; [exact HU1|].
    eapply unch_weaken; [exact HU'|]. intros x Hx. unfold BRegPoisoned.FP, FPlow, inr in *. lia. }
  wp_amm [0x1bd048].
  split; intros Hb; [|exfalso; apply Hb; reflexivity].
  apply final; [exact HMI2|]. prove_stable Hse.
Qed.

(* [comment removed for export] *)
Lemma dst_scan_loop : forall k t l M', sha (d + n - 1) - t = Z.of_nat k -> sha d <= t < sha (d + n - 1) ->
  MI M' -> stable l -> 0 < n -> rget l 13 = W t -> rget l 14 = W (sha (d + n - 1)) -> rget l 15 = W 0 ->
  reach BSEGS rom (Z_to_bv 64 0x1bd254) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros t l M' Hk Ht HMI Hst Hn0 H13 H14 H15.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range d ltac:(lia)) as Hr1. pose proof (sha_range (d + n - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' d n (MI_okd _ HMI) Hd0 Hn0) as Hz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp a0 a1 a2 a3 a4 a5.
  wp_amm [0x1bd254; 0x1bd048; 0x1bd26c].
  exists (W 0). split; [eapply load1_zeros; [exact Hz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (d + n - 1) - (t + 1)))) with (t := t + 1); try lia; try exact HMI; try exact Hn0;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply final; [exact HMI|]. prove_stable Hse.
Qed.

(* [comment removed for export] *)
Lemma dst_scan : forall l M', MI M' -> stable l -> 0 < n ->
  rget l 13 = W (sha d) -> rget l 14 = W (sha (d + n - 1)) -> rget l 15 = W (d + n - 1) ->
  reach BSEGS rom (Z_to_bv 64 0x1bd238) l M' Post.
Proof.
  intros l M' HMI Hst Hn0 H13 H14 H15.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range d ltac:(lia)) as Hr1. pose proof (sha_range (d + n - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono d (d + n - 1) ltac:(lia)) as Hmono.
  destruct (sh_load BSEGS M' (d + n - 1) (MI_okd _ HMI (d + n - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp a0 a1 a2 a3 a4 a5.
  wp_amm [0x1bd254; 0x1bd048; 0x1bd26c].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((d + n - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply final; [exact HMI|]. prove_stable Hse.
  - eapply (dst_scan_loop (Z.to_nat (sha (d + n - 1) - sha d))) with (t := sha d); try lia; try exact HMI; try exact Hn0;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma dst_chk : forall l M', MI M' -> stable l -> rget l 19 = W (n + -65) ->
  reach BSEGS rom (Z_to_bv 64 0x1bcffc) l M' Post.
Proof.
  intros l M' HMI Hst H19.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_stable Hst l. subst sp a0 a1 a2 s3.
  assert (Hfin : forall r13 r14 r15 r16 r17, reach BSEGS rom (Z_to_bv 64 0x1bd048)
     [x0; ra; Z_to_bv 64 (S - 2144); gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 d; Z_to_bv 64 s; Z_to_bv 64 n; r13; r14; r15; r16; r17;
      s2; Z_to_bv 64 (n + -65); s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
  { intros. apply final; [exact HMI|]. prove_stable Hse. }
  wp_amm [0x1bd048; 0x1bd108; 0x1bd238; 0x1bd26c].
  unfold HIMEM_END in *. rewrite u_not_W by lia. rewrite (Wu n) by lia.
  split; intros Hb0; [exfalso; lia|]. clear Hb0.
  change (bv_unsigned (Z_to_bv 64 (-65))) with (2 ^ 64 - 65).
  split; intros Hb1.
  - (* [comment removed for export] *)
    split; intros Hb2; [|apply Hfin].
    assert (Hn1 : 0 < n) by (destruct (Z.eq_dec n 0) as [->|]; [exfalso; apply Hb2; reflexivity | lia]).
    apply dst_rp; [exact HMI | prove_stable Hse | exact Hn1].
  - (* [comment removed for export] *)
    assert (Hn1 : 0 < n <= 64).
    { destruct (Z_lt_le_dec n 65) as [Hlt|Hge].
      - destruct (Z.eq_dec n 0) as [E0|]; [|lia]. exfalso. rewrite Wu_neg in Hb1 by lia. lia.
      - exfalso. rewrite Wu in Hb1 by lia. lia. }
    pose proof (sha_range d ltac:(unfold HIMEM_END; lia)) as Hr1. pose proof (sha_range (d + n - 1) ltac:(unfold HIMEM_END; lia)) as Hr2.
    pose proof (sha_mono d (d + n - 1) ltac:(lia)) as Hmono.
    pose proof (MI_rd _ _ _ HMI (Hshd ltac:(lia))) as Hw. unfold shw_ok in Hw.
    unfold SB, HIMEM_BEG in *.
    mem_auto. rewrite ?add_W, ?addi_W. replace (d + n + -1) with (d + n - 1) by lia.
    rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
    pose proof (align_dn_le (sha d)) as Ha1. pose proof (align_dn_le (sha (d + n - 1))) as Ha2.
    assert (Hdiv : sha d / 8 <= sha (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
    destruct (load_rd BSEGS M' _ _ (sha d / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
    destruct (load_rd BSEGS M' _ _ (sha (d + n - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
    exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
    split; intros Hb3; [|apply Hfin].
    apply dst_scan; [exact HMI | prove_stable Hse | lia | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_rp : forall l M', MI M' -> stable l -> 0 < n -> rget l 19 = W (n + -65) ->
  reach BSEGS rom (Z_to_bv 64 0x1bd1c8) l M' Post.
Proof.
  intros l M' HMI Hst Hn0 H19. unfold B_IMG_END in *.
  open_stable Hst l. subst sp a0 a1 a2 s3.
  wp_amm (@nil Z).
  replace (Z_to_bv 64 1834564) with (Z_to_bv 64 0x1bfe44) by reflexivity.
  eapply (regpoisoned_cps rom Post M' s n (S - 2144));
    [ apply (MI_rt _ HMI) | exact Hms | lia | apply (MI_oks _ HMI) | unfold B_IMG_END; lia | lia
    | eapply wr_ok_sub; [apply (MI_wr _ _ _ HMI Hfr) | lia | lia]
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' Hl' Hse' H10' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1823200) 0) with (Z_to_bv 64 0x1bd1e0) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  assert (HMI2 : MI M'').
  { destruct HMI as [HU1 HG1]. split; [|eapply mem_grows_trans; eassumption]. eapply unch_trans; [exact HU1|].
    eapply unch_weaken; [exact HU'|]. intros x Hx. unfold BRegPoisoned.FP, FPlow, inr in *. lia. }
  wp_amm [0x1bcffc].
  split; intros Hb; [|exfalso; apply Hb; reflexivity].
  apply dst_chk; [exact HMI2 | prove_stable Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_scan_loop : forall k t l M', sha (s + n - 1) - t = Z.of_nat k -> sha s <= t < sha (s + n - 1) ->
  MI M' -> stable l -> 0 < n -> rget l 19 = W (n + -65) ->
  rget l 13 = W t -> rget l 14 = W (sha (s + n - 1)) -> rget l 15 = W 0 ->
  reach BSEGS rom (Z_to_bv 64 0x1bd1b0) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros t l M' Hk Ht HMI Hst Hn0 H19 H13 H14 H15.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range s ltac:(lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' s n (MI_oks _ HMI) Hs0 Hn0) as Hz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp a0 a1 a2 a3 a4 a5 s3.
  wp_amm [0x1bd1b0; 0x1bcffc; 0x1bd1c8].
  exists (W 0). split; [eapply load1_zeros; [exact Hz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (s + n - 1) - (t + 1)))) with (t := t + 1); try lia; try exact HMI; try exact Hn0;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply dst_chk; [exact HMI | prove_stable Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_scan : forall l M', MI M' -> stable l -> 0 < n -> rget l 19 = W (n + -65) ->
  rget l 13 = W (sha s) -> rget l 14 = W (sha (s + n - 1)) -> rget l 15 = W (s + n - 1) ->
  reach BSEGS rom (Z_to_bv 64 0x1bd194) l M' Post.
Proof.
  intros l M' HMI Hst Hn0 H19 H13 H14 H15.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range s ltac:(lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono s (s + n - 1) ltac:(lia)) as Hmono.
  destruct (sh_load BSEGS M' (s + n - 1) (MI_oks _ HMI (s + n - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (s + n - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp a0 a1 a2 a3 a4 a5 s3.
  wp_amm [0x1bd1b0; 0x1bcffc; 0x1bd1c8].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((s + n - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply dst_chk; [exact HMI | prove_stable Hse | reflexivity].
  - eapply (src_scan_loop (Z.to_nat (sha (s + n - 1) - sha s))) with (t := sha s); try lia; try exact HMI; try exact Hn0;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_chk : forall l M', MI M' -> stable l -> reach BSEGS rom (Z_to_bv 64 0x1bcfa4) l M' Post.
Proof.
  intros l M' HMI Hst.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_stable Hst l. subst sp a0 a1 a2.
  assert (Hdst : forall r13 r14 r15 r16 r17 r20, reach BSEGS rom (Z_to_bv 64 0x1bcffc)
     [x0; ra; Z_to_bv 64 (S - 2144); gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 d; Z_to_bv 64 s; Z_to_bv 64 n; r13; r14; r15; r16; r17;
      s2; Z_to_bv 64 (n + -65); r20; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
  { intros. apply dst_chk; [exact HMI | prove_stable Hse | reflexivity]. }
  wp_amm [0x1bcffc; 0x1bd078; 0x1bd194; 0x1bd1c8].
  unfold HIMEM_END in *. rewrite u_not_W by lia. rewrite (Wu n) by lia. rewrite ?addi_W.
  split; intros Hb0; [exfalso; lia|]. clear Hb0.
  change (bv_unsigned (Z_to_bv 64 (-65))) with (2 ^ 64 - 65).
  split; intros Hb1.
  - split; intros Hb2; [|apply Hdst].
    assert (Hn1 : 0 < n) by (destruct (Z.eq_dec n 0) as [->|]; [exfalso; apply Hb2; reflexivity | lia]).
    apply src_rp; [exact HMI | prove_stable Hse | exact Hn1 | reflexivity].
  - assert (Hn1 : 0 < n <= 64).
    { destruct (Z_lt_le_dec n 65) as [Hlt|Hge].
      - destruct (Z.eq_dec n 0) as [E0|]; [|lia]. exfalso. rewrite Wu_neg in Hb1 by lia. lia.
      - exfalso. rewrite Wu in Hb1 by lia. lia. }
    pose proof (sha_range s ltac:(unfold HIMEM_END; lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(unfold HIMEM_END; lia)) as Hr2.
    pose proof (sha_mono s (s + n - 1) ltac:(lia)) as Hmono.
    pose proof (MI_rd _ _ _ HMI (Hshs ltac:(lia))) as Hw. unfold shw_ok in Hw.
    unfold SB, HIMEM_BEG in *.
    mem_auto. rewrite ?add_W, ?addi_W. replace (s + n + -1) with (s + n - 1) by lia.
    rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
    pose proof (align_dn_le (sha s)) as Ha1. pose proof (align_dn_le (sha (s + n - 1))) as Ha2.
    assert (Hdiv : sha s / 8 <= sha (s + n - 1) / 8) by (apply Z.div_le_mono; lia).
    destruct (load_rd BSEGS M' _ _ (sha s / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
    destruct (load_rd BSEGS M' _ _ (sha (s + n - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
    exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
    split; intros Hb3; [|apply Hdst].
    apply src_scan; [exact HMI | prove_stable Hse | lia | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma flag_chk : forall l M', MI M' -> stable l -> reach BSEGS rom (Z_to_bv 64 0x1bcf94) l M' Post.
Proof.
  intros l M' HMI Hst.
  pose proof (MI_rt _ HMI) as (_ & _ & _ & _ & _ & _ & _ & _ & Hg & (fb & Hfb)). unfold G_RINTRIN, C_RINTRIN in *.
  open_stable Hst l. subst sp a0 a1 a2.
  wp_amm [0x1bcfa4; 0x1bd048].
  mem_auto.
  split; intros Hb.
  - apply final; [exact HMI|]. prove_stable Hse.
  - apply src_chk; [exact HMI|]. prove_stable Hse.
Qed.

Lemma amm_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  reach BSEGS rom (Z_to_bv 64 0x1bcf68) l M Post.
Proof.
  intros l Hl El H10 H11 H12. assert (Hse : same_except KSI l0 l) by (subst l; apply same_except_refl).
  assert (E2 : rget l 2 = W S) by (rewrite El; exact H0sp).
  assert (E1 : rget l 1 = rget l0 1 /\ rget l 8 = rget l0 8 /\ rget l 9 = rget l0 9 /\ rget l 18 = rget l0 18
               /\ rget l 19 = rget l0 19 /\ rget l 20 = rget l0 20 /\ rget l 21 = rget l0 21 /\ rget l 22 = rget l0 22)
    by (rewrite El; repeat split).
  clear El. unfold B_IMG_END in *. regs_open l Hl. cbn [rget lget] in E1, E2.
  destruct E1 as (? & ? & ? & ? & ? & ? & ? & ?). subst a0 a1 a2 sp ra s0 s1 s2 s3 s4 s5 s6.
  wp_amm [0x1bcf94].
  rewrite ?addi_W.
  repeat (split; [solve_store|]).
  change (wbytes _ _ _) with M1.
  apply flag_chk; [apply MI_M1|].
  split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|].
  cbn [rget lget]. repeat split; try reflexivity. f_equal. lia.
Qed.

End AMM.

(* [comment removed for export] *)
Theorem amemmove_cps : forall rom Post M d s n S l,
  rt_ok M -> 0 <= n <= 2 ^ 40 -> memrange s n -> memrange d n -> s < d ->
  addr_ok M s n -> addr_ok M d n -> (0 < n -> shw_ok M s n) -> (0 < n -> shw_ok M d n) ->
  rd_ok M s n -> wr_ok BSEGS M d n ->
  B_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok BSEGS M (S - 2224) 2224 ->
  (d + n <= S - 2224 \/ S <= d) ->
  length l = 32%nat -> rget l 2 = W S -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> unch M M' (FP d n S) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1bcf68) l M Post.
Proof.
  intros rom Post M d s n S l; intros.
  eapply (amm_body rom Post M d s n S) with (l0 := l); eauto.
Qed.
