(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt ASaves ArCode ARtIc AMMemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_amc stops := wp_go 0x1c197c 295%nat C_amemcpy_eq C_amemcpy stops.

Section AMC.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (d s n S : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hic : ic_ok M.
Hypothesis Hn : 0 <= n < 32.
Hypothesis Hms : memrange s n.
Hypothesis Hmd : memrange d n.
Hypothesis Hnov : d + n <= s \/ s + n <= d.
Hypothesis Hoks : addr_ok M s n.
Hypothesis Hokd : addr_ok M d n.
Hypothesis Hshs : 0 < n -> shw_ok M s n.
Hypothesis Hshd : 0 < n -> shw_ok M d n.
Hypothesis Hrd : rd_ok M s n.
Hypothesis Hwr : wr_ok ASEGS M d n.
Hypothesis HS : A_IMG_END <= S - 2224 /\ S < 2 ^ 63.
Hypothesis HSz : S <= SB \/ HIMEM_BEG <= S - 2224.
Hypothesis Hfr : wr_ok ASEGS M (S - 2224) 2224.
Hypothesis Hdj : d + n <= S - 2224 \/ S <= d.
Hypothesis Hdapp : A_IMG_END <= d.

Definition KSI : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28; 29; 30; 31]%nat.
Definition FP (x : word) : Prop := inr x (S - 2224) 2224 \/ inr x d n.
Definition FPstk (x : word) : Prop := inr x (S - 2224) 2224.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSC l0 l' -> rget l' 10 = W d ->
  unch M M' FP -> mem_grows M M' ->
  reach ASEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition SL : list (Z * word) :=
  [(2024, rget l0 1); (2016, rget l0 8); (2008, rget l0 9); (2000, rget l0 18); (1992, rget l0 19); (1984, rget l0 20);
   (1976, rget l0 21); (1968, rget l0 22); (1960, rget l0 23)].
Definition M1 : mem := saves M (S + -2032) SL.

Lemma SL_ok : slots_ok 2032 SL = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition FPlow (x : word) : Prop := inr x (S - 2224) 80.
Definition MI (M' : mem) : Prop := unch M1 M' FPlow /\ mem_grows M1 M'.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma FPstk_app : forall y, FPstk y -> A_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold FPstk, inr in Hy. lia. Qed.
Lemma FPstk_nosh : forall y, FPstk y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof. intros y Hy. unfold FPstk, inr in Hy. lia. Qed.

Lemma MI_stk : forall M', MI M' -> unch M M' FPstk /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. unfold A_IMG_END in *. split.
  - apply (unch_trans M M1 M').
    + unfold M1. apply (saves_unch SL M M (S + -2032) 2032); [lia | lia | exact SL_ok | | apply unch_refl].
      intros x Hx. unfold FPstk, inr in *. lia.
    + eapply unch_weaken; [exact HU|]. intros x Hx. unfold FPlow, FPstk, inr in *. lia.
  - eapply mem_grows_trans; [apply saves_grows | exact HG].
Qed.

Lemma MI_saved : forall M' off v, MI M' -> In (off, v) SL -> cell ASEGS M' (S + -2032 + off) 8 v.
Proof.
  intros M' off v [HU HG] Hin. unfold A_IMG_END in *.
  pose proof (slots_ok_in 2032 SL off v SL_ok Hin) as Ho.
  eapply cell_unch; [exact HU | lia | (cbn; lia) | | apply (saves_cell ASEGS SL M (S + -2032) 2032); [lia | lia | exact SL_ok | exact Hin]].
  intros x Hx. cbn in Hx. unfold FPlow, inr in *. lia.
Qed.

Lemma MI_rt : forall M', MI M' -> rt_ok M'.
Proof. intros M' HMI. destruct (MI_stk _ HMI) as [HU _]. eapply rt_ok_unch; [exact HU | apply FPstk_app | exact Hrt]. Qed.
Lemma MI_ic : forall M', MI M' -> ic_ok M'.
Proof. intros M' HMI. destruct (MI_stk _ HMI) as [HU _]. eapply ic_ok_unch; [exact HU | apply FPstk_app | exact Hic]. Qed.

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
Lemma MI_rd : forall M' a m, MI M' -> rd_ok M a m -> rd_ok M' a m.
Proof. intros M' a m HMI H. destruct (MI_stk _ HMI) as [_ HG]. eapply rd_ok_grows; [exact HG | exact H]. Qed.
Lemma MI_wr : forall M' a m, MI M' -> wr_ok ASEGS M a m -> wr_ok ASEGS M' a m.
Proof. intros M' a m HMI H. destruct (MI_stk _ HMI) as [_ HG]. eapply wr_ok_grows; [exact HG | exact H]. Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI l0 l /\ rget l 2 = W (S - 2144) /\ rget l 8 = W S
  /\ rget l 10 = W d /\ rget l 11 = W s /\ rget l 12 = W n.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H10 & ?H11 & ?H12); regs_open l Hl.

Ltac prove_stable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Lemma final : forall l M', MI M' -> stable l -> reach ASEGS rom (Z_to_bv 64 0x1c1a6c) l M' Post.
Proof.
  intros l M' HMI Hst. pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1). unfold HIMEM_END in *.
  pose proof (MI_ic _ HMI) as (_ & _ & _ & _ & _ & _ & _ & Hreal & _). unfold R_MEMCPY in *.
  open_stable Hst l. subst sp s0 a0 a1 a2.
  wp_amc (@nil Z). mem_auto.
  replace (v_jalr (Z_to_bv 64 5416120) 0) with (Z_to_bv 64 0x52a4b8) by reflexivity.
  eapply (memcpy_cps rom Post M' d s n); [lia | lia | lia | apply (MI_rd _ _ _ HMI Hrd) | apply (MI_wr _ _ _ HMI Hwr)
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' Hl' Hse' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1841784) 0) with (Z_to_bv 64 0x1c1a78) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (Hsv : forall off v, In (off, v) SL -> cell ASEGS M'' (S + -2032 + off) 8 v).
  { intros off v Hin. unfold A_IMG_END in *. pose proof (slots_ok_in 2032 SL off v SL_ok Hin) as Ho.
    eapply cell_unch; [exact HU' | lia | (cbn; lia) | | apply (MI_saved _ _ _ HMI Hin)].
    intros x Hx. cbn in Hx. unfold AMMemcpy.FP, inr in *. lia. }
  pose proof (Hsv 2024 _ ltac:(unfold SL; in_list)) as Csv1. pose proof (Hsv 2016 _ ltac:(unfold SL; in_list)) as Csv8.
  pose proof (Hsv 2008 _ ltac:(unfold SL; in_list)) as Csv9. pose proof (Hsv 2000 _ ltac:(unfold SL; in_list)) as Csv18.
  pose proof (Hsv 1992 _ ltac:(unfold SL; in_list)) as Csv19. pose proof (Hsv 1984 _ ltac:(unfold SL; in_list)) as Csv20.
  pose proof (Hsv 1976 _ ltac:(unfold SL; in_list)) as Csv21. pose proof (Hsv 1968 _ ltac:(unfold SL; in_list)) as Csv22.
  pose proof (Hsv 1960 _ ltac:(unfold SL; in_list)) as Csv23.
  clear Hsv. unfold A_IMG_END in *.
  wp_amc (@nil Z). rewrite ?addi_W. replace (S - 2144 + 112) with (S + -2032) by lia. mem_auto.
  destruct (MI_stk _ HMI) as [HU HG].
  apply K; [reflexivity | | reflexivity | | eapply mem_grows_trans; eassumption].
  - same_fix Hse. rewrite H0sp. f_equal. lia.
  - eapply unch_trans; [eapply unch_weaken; [exact HU | intros x Hx; left; exact Hx]|].
    eapply unch_weaken; [exact HU'|]. intros x Hx. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma dst_scan_loop : forall f t l M', sha (d + n - 1) - t = Z.of_nat f -> sha d <= t < sha (d + n - 1) ->
  MI M' -> stable l -> 0 < n -> rget l 13 = W t -> rget l 14 = W (sha (d + n - 1)) -> rget l 15 = W 0 ->
  reach ASEGS rom (Z_to_bv 64 0x1c1d94) l M' Post.
Proof.
  induction f as [f IH] using lt_wf_ind; intros t l M' Hf Ht HMI Hst Hn0 H13 H14 H15.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range d ltac:(lia)) as Hr1. pose proof (sha_range (d + n - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' d n (MI_okd _ HMI) Hd0 Hn0) as Hzz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp s0 a0 a1 a2 a3 a4 a5.
  wp_amc [0x1c1d94; 0x1c1a6c; 0x1c1dac].
  exists (W 0). split; [eapply load1_zeros; [exact Hzz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (d + n - 1) - (t + 1)))) with (t := t + 1); try lia; try exact HMI;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply final; [exact HMI|]. prove_stable Hse.
Qed.

(* [comment removed for export] *)
Lemma dst_scan : forall l M', MI M' -> stable l -> 0 < n ->
  rget l 13 = W (sha d) -> rget l 14 = W (sha (d + n - 1)) -> rget l 19 = W (d + n - 1) ->
  reach ASEGS rom (Z_to_bv 64 0x1c1d78) l M' Post.
Proof.
  intros l M' HMI Hst Hn0 H13 H14 H19.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range d ltac:(lia)) as Hr1. pose proof (sha_range (d + n - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono d (d + n - 1) ltac:(lia)) as Hmono.
  destruct (sh_load ASEGS M' (d + n - 1) (MI_okd _ HMI (d + n - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hcu).
  pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp s0 a0 a1 a2 a3 a4 s3.
  wp_amc [0x1c1d94; 0x1c1a6c; 0x1c1dac].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((d + n - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply final; [exact HMI|]. prove_stable Hse.
  - eapply (dst_scan_loop (Z.to_nat (sha (d + n - 1) - sha d))) with (t := sha d); try lia; try exact HMI;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma dst_chk : forall l M', MI M' -> stable l -> rget l 22 = W (n + -65) -> rget l 19 = W (d + n) ->
  reach ASEGS rom (Z_to_bv 64 0x1c1a24) l M' Post.
Proof.
  intros l M' HMI Hst H22 H19.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_stable Hst l. subst sp s0 a0 a1 a2 s3 s6.
  assert (Hfin : forall r13 r14 r15 r16 r17 r19, reach ASEGS rom (Z_to_bv 64 0x1c1a6c)
     [x0; ra; Z_to_bv 64 (S - 2144); gp; tp; t0; t1; t2; Z_to_bv 64 S; s1; Z_to_bv 64 d; Z_to_bv 64 s; Z_to_bv 64 n; r13; r14; r15; r16; r17;
      s2; r19; s4; s5; Z_to_bv 64 (n + -65); s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
  { intros. apply final; [exact HMI|]. prove_stable Hse. }
  wp_amc [0x1c1a6c; 0x1c1afc; 0x1c1d78; 0x1c1dac].
  unfold HIMEM_END in *. rewrite u_not_W by lia. rewrite (Wu n) by lia.
  split; intros Hb0; [exfalso; lia|]. clear Hb0.
  change (bv_unsigned (Z_to_bv 64 (-65))) with (2 ^ 64 - 65).
  split; intros Hb1.
  - (* [comment removed for export] *)
    split; intros Hb2; [|apply Hfin].
    exfalso. destruct (Z.eq_dec n 0) as [E0|]; [apply Hb2; rewrite E0; reflexivity|]. rewrite Wu_neg in Hb1 by lia. lia.
  - (* [comment removed for export] *)
    assert (Hn1 : 0 < n).
    { destruct (Z.eq_dec n 0) as [E0|]; [|lia]. exfalso. rewrite E0 in Hb1. change (bv_unsigned (Z_to_bv 64 (0 + -65))) with (2 ^ 64 - 65) in Hb1. lia. }
    pose proof (sha_range d ltac:(unfold HIMEM_END; lia)) as Hr1. pose proof (sha_range (d + n - 1) ltac:(unfold HIMEM_END; lia)) as Hr2.
    pose proof (sha_mono d (d + n - 1) ltac:(lia)) as Hmono.
    pose proof (MI_rd _ _ _ HMI (Hshd ltac:(lia))) as Hw. unfold shw_ok in Hw.
    unfold SB, HIMEM_BEG in *.
    mem_auto. rewrite ?add_W, ?addi_W. replace (d + n + -1) with (d + n - 1) by lia.
    rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
    pose proof (align_dn_le (sha d)) as Ha1. pose proof (align_dn_le (sha (d + n - 1))) as Ha2.
    assert (Hdiv : sha d / 8 <= sha (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
    destruct (load_rd ASEGS M' _ _ (sha d / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
    destruct (load_rd ASEGS M' _ _ (sha (d + n - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
    exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
    split; intros Hb3; [|apply Hfin].
    apply dst_scan; [exact HMI | prove_stable Hse | lia | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_scan_loop : forall f t l M', sha (s + n - 1) - t = Z.of_nat f -> sha s <= t < sha (s + n - 1) ->
  MI M' -> stable l -> 0 < n -> rget l 22 = W (n + -65) -> rget l 19 = W (d + n) ->
  rget l 13 = W t -> rget l 14 = W (sha (s + n - 1)) -> rget l 15 = W 0 ->
  reach ASEGS rom (Z_to_bv 64 0x1c1cf0) l M' Post.
Proof.
  induction f as [f IH] using lt_wf_ind; intros t l M' Hf Ht HMI Hst Hn0 H22 H19 H13 H14 H15.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range s ltac:(lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' s n (MI_oks _ HMI) Hs0 Hn0) as Hzz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp s0 a0 a1 a2 a3 a4 a5 s3 s6.
  wp_amc [0x1c1cf0; 0x1c1a24; 0x1c1d08].
  exists (W 0). split; [eapply load1_zeros; [exact Hzz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (s + n - 1) - (t + 1)))) with (t := t + 1); try lia; try exact HMI;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply dst_chk; [exact HMI | prove_stable Hse | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_scan : forall l M', MI M' -> stable l -> 0 < n -> rget l 22 = W (n + -65) -> rget l 19 = W (d + n) ->
  rget l 13 = W (sha s) -> rget l 14 = W (sha (s + n - 1)) -> rget l 21 = W (s + n - 1) ->
  reach ASEGS rom (Z_to_bv 64 0x1c1cd4) l M' Post.
Proof.
  intros l M' HMI Hst Hn0 H22 H19 H13 H14 H21.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (sha_range s ltac:(lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono s (s + n - 1) ltac:(lia)) as Hmono.
  destruct (sh_load ASEGS M' (s + n - 1) (MI_oks _ HMI (s + n - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hcu).
  pose proof (Z.mod_pos_bound (s + n - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp s0 a0 a1 a2 a3 a4 s3 s5 s6.
  wp_amc [0x1c1cf0; 0x1c1a24; 0x1c1d08].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((s + n - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply dst_chk; [exact HMI | prove_stable Hse | reflexivity | reflexivity].
  - eapply (src_scan_loop (Z.to_nat (sha (s + n - 1) - sha s))) with (t := sha s); try lia; try exact HMI;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma src_chk : forall l M', MI M' -> stable l -> rget l 21 = W (s + n) -> rget l 19 = W (d + n) ->
  reach ASEGS rom (Z_to_bv 64 0x1c19d8) l M' Post.
Proof.
  intros l M' HMI Hst H21 H19.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_stable Hst l. subst sp s0 a0 a1 a2 s3 s5.
  assert (Hdc : forall r13 r14 r15 r16 r17 r21, reach ASEGS rom (Z_to_bv 64 0x1c1a24)
     [x0; ra; Z_to_bv 64 (S - 2144); gp; tp; t0; t1; t2; Z_to_bv 64 S; s1; Z_to_bv 64 d; Z_to_bv 64 s; Z_to_bv 64 n; r13; r14; r15; r16; r17;
      s2; Z_to_bv 64 (d + n); s4; r21; Z_to_bv 64 (n + -65); s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
  { intros. apply dst_chk; [exact HMI | prove_stable Hse | reflexivity | reflexivity]. }
  wp_amc [0x1c1a24; 0x1c1c44; 0x1c1cd4; 0x1c1d08]. rewrite ?addi_W.
  unfold HIMEM_END in *. rewrite u_not_W by lia. rewrite (Wu n) by lia.
  split; intros Hb0; [exfalso; lia|]. clear Hb0.
  change (bv_unsigned (Z_to_bv 64 (-65))) with (2 ^ 64 - 65).
  split; intros Hb1.
  - (* [comment removed for export] *)
    split; intros Hb2; [|apply Hdc].
    exfalso. destruct (Z.eq_dec n 0) as [E0|]; [apply Hb2; rewrite E0; reflexivity|]. rewrite Wu_neg in Hb1 by lia. lia.
  - assert (Hn1 : 0 < n).
    { destruct (Z.eq_dec n 0) as [E0|]; [|lia]. exfalso. rewrite E0 in Hb1. change (bv_unsigned (Z_to_bv 64 (0 + -65))) with (2 ^ 64 - 65) in Hb1. lia. }
    pose proof (sha_range s ltac:(unfold HIMEM_END; lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(unfold HIMEM_END; lia)) as Hr2.
    pose proof (sha_mono s (s + n - 1) ltac:(lia)) as Hmono.
    pose proof (MI_rd _ _ _ HMI (Hshs ltac:(lia))) as Hw. unfold shw_ok in Hw.
    unfold SB, HIMEM_BEG in *.
    mem_auto. rewrite ?add_W, ?addi_W. replace (s + n + -1) with (s + n - 1) by lia.
    rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
    pose proof (align_dn_le (sha s)) as Ha1. pose proof (align_dn_le (sha (s + n - 1))) as Ha2.
    assert (Hdiv : sha s / 8 <= sha (s + n - 1) / 8) by (apply Z.div_le_mono; lia).
    destruct (load_rd ASEGS M' _ _ (sha s / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
    destruct (load_rd ASEGS M' _ _ (sha (s + n - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
    exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
    split; intros Hb3; [|apply Hdc].
    apply src_scan; [exact HMI | prove_stable Hse | lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma amc_body : forall l, l = l0 -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  reach ASEGS rom (Z_to_bv 64 0x1c197c) l M Post.
Proof.
  intros l El H10 H11 H12. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2.
  assert (HM1 : M1 = M1) by reflexivity. unfold M1 at 1 in HM1. unfold SL in HM1. rewrite <- El in HM1. clear El.
  pose proof s_bounds as (Hs0 & Hs1 & Hd0 & Hd1).
  unfold A_IMG_END in *.
  regs_open l Hl. subst sp a0 a1 a2.
  wp_amc [0x1c1aa8; 0x1c19bc]. rewrite ?addi_W. mem_auto. replace (S + -2032 + 2032) with S by lia.
  replace (S + -2032 + -112) with (S - 2144) by lia.
  match goal with |- context [reach _ _ _ _ ?Mx _] => replace Mx with M1 by (symmetry; exact HM1) end. clear HM1.
  pose proof MI_M1 as HMI. generalize dependent M1. intros M' HMI.
  pose proof (MI_rt _ HMI) as (_ & _ & _ & _ & _ & _ & _ & _ & Hgri & (fb & Hfb)). unfold G_RINTRIN, C_RINTRIN in *.
  mem_auto.
  split; intros Hflag.
  - (* [comment removed for export] *)
    wp_amc (@nil Z).
    replace (Z_to_bv 64 1874276) with (Z_to_bv 64 0x1c9964) by reflexivity.
    pose proof (MI_ic _ HMI) as (Hini & _).
    eapply (inited_cps rom Post M'); [exact Hini | reflexivity |].
    intros l1 Hl1 Hse1 H10'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1841848) 0) with (Z_to_bv 64 0x1c1ab8) by reflexivity.
    regs_open l1 Hl1. se_subst Hse1. clear Hse1. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
    wp_amc [0x1c1a6c]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
    split; intros Hb; [|exfalso; lia].
    apply final; [exact HMI | prove_stable Hse].
  - (* [comment removed for export] *)
    wp_amc [0x1c19d8; 0x1c1b88]. rewrite ?add_W. unfold HIMEM_END in *. rewrite !Wu by lia.
    assert (Hsc : forall r13 r20, reach ASEGS rom (Z_to_bv 64 0x1c19d8)
      [x0; ra; Z_to_bv 64 (S - 2144); gp; tp; t0; t1; t2; Z_to_bv 64 S; s1; Z_to_bv 64 d; Z_to_bv 64 s; Z_to_bv 64 n; r13; a4; a5; a6; a7;
       s2; Z_to_bv 64 (d + n); r20; Z_to_bv 64 (s + n); s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
    { intros. apply src_chk; [exact HMI | prove_stable Hse | reflexivity | reflexivity]. }
    split; intros Hb1; [apply Hsc|].
    split; intros Hb2; [apply Hsc|].
    split; intros Hb3; [exfalso; lia | apply Hsc].
Qed.

End AMC.

(* [comment removed for export] *)
Theorem amemcpy_cps : forall rom Post M d s n S l,
  rt_ok M -> ic_ok M -> 0 <= n < 32 -> memrange s n -> memrange d n -> (d + n <= s \/ s + n <= d) ->
  addr_ok M s n -> addr_ok M d n -> (0 < n -> shw_ok M s n) -> (0 < n -> shw_ok M d n) ->
  rd_ok M s n -> wr_ok ASEGS M d n ->
  A_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok ASEGS M (S - 2224) 2224 ->
  (d + n <= S - 2224 \/ S <= d) -> A_IMG_END <= d ->
  length l = 32%nat -> rget l 2 = W S -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KSC l l' -> rget l' 10 = W d ->
                 unch M M' (FP d n S) -> mem_grows M M' ->
                 reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach ASEGS rom (Z_to_bv 64 0x1c197c) l M Post.
Proof.
  intros rom Post M d s n S l; intros.
  eapply (amc_body rom Post M d s n S) with (l0 := l); eauto.
Qed.

Print Assumptions amemcpy_cps.
