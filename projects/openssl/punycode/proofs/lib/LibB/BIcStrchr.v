(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BRegPoisoned BrCode BRtIc BMStrchr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_isc stops := wp_go 0x1a860c 184%nat C_ic_strchr_eq C_ic_strchr stops.

Section IcStrchr.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (p N : Z) (B : Z -> byte) (k r c S : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hic : ic_ok M.
Hypothesis HB : bytes_at M p N B.
Hypothesis Hp : 0 < p /\ p + N < 2 ^ 63.
Hypothesis Hk : 0 <= k <= r.
Hypothesis Hr : r < N.
Hypothesis Hc : 0 < c < 256.
Hypothesis Hlen : r - k < 2 ^ 31.
Hypothesis HBr : bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c.
Hypothesis HBn : forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c.
Hypothesis Hslack : (p + r) / 8 * 8 + 8 <= p + N.
Hypothesis Hmr : memrange (p + k) (r - k + 1).
Hypothesis Hok : addr_ok M (p + k) (r - k + 1).
Hypothesis Hshw : shw_ok M (p + k) (r - k + 1).
Hypothesis HS : B_IMG_END <= S - 2224 /\ S < 2 ^ 63.
Hypothesis HSz : S <= SB \/ HIMEM_BEG <= S - 2224.
Hypothesis Hfr : wr_ok BSEGS M (S - 2224) 2224.
Hypothesis Hdj : p + N <= S - 2224 \/ S <= p.

Let s := p + k.
Let len := r - k.
Let n := r - k + 1.
Let res := if Z.eqb (bv_unsigned (B r)) c then p + r else 0.

Definition KSI : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28; 29; 30; 31]%nat.
Definition FP (x : word) : Prop := inr x (S - 2224) 2224.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSC l0 l' ->
  rget l' 10 = W (if Z.eqb (bv_unsigned (B r)) c then p + r else 0) ->
  unch M M' FP -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition M1 : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (W (S + -2032 + 2024)) (word_to_le_bytes 8 (rget l0 1)))
    (W (S + -2032 + 2016)) (word_to_le_bytes 8 (rget l0 8)))
    (W (S + -2032 + 2008)) (word_to_le_bytes 8 (rget l0 9)))
    (W (S + -2032 + 2000)) (word_to_le_bytes 8 (rget l0 18)))
    (W (S + -2032 + 1992)) (word_to_le_bytes 8 (rget l0 19)))
    (W (S + -2032 + 1984)) (word_to_le_bytes 8 (rget l0 20)))
    (W (S + -2032 + 1976)) (word_to_le_bytes 8 (rget l0 21)))
    (W (S + -2032 + 1968)) (word_to_le_bytes 8 (rget l0 22)))
    (W (S + -2032 + 1960)) (word_to_le_bytes 8 (rget l0 23)).

Definition SAVE_SLOTS : list (nat * Z) :=
  [(1%nat, 2024); (8%nat, 2016); (9%nat, 2008); (18%nat, 2000); (19%nat, 1992); (20%nat, 1984); (21%nat, 1976);
   (22%nat, 1968); (23%nat, 1960)].

Definition FPlow (x : word) : Prop := inr x (S - 2224) 80.
Definition MI (M' : mem) : Prop := unch M1 M' FPlow /\ mem_grows M1 M'.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1, B_IMG_END in *. solve_grows. Qed.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma M1_saved : forall q off, In (q, off) SAVE_SLOTS -> cell BSEGS M1 (S + -2032 + off) 8 (rget l0 q).
Proof.
  intros q off Hin. unfold B_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Lemma FP_app : forall y, FP y -> B_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold FP, inr in Hy. lia. Qed.
Lemma FP_nosh : forall y, FP y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof. intros y Hy. unfold FP, inr in Hy. lia. Qed.

Lemma MI_final : forall M', MI M' -> unch M M' FP /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. split.
  - apply (unch_trans M M1 M').
    + unfold M1, B_IMG_END in *. solve_unch ltac:(unfold FP, inr in *; lia).
    + eapply unch_weaken; [exact HU|]. intros x Hx. unfold FPlow, FP, inr in *. lia.
  - eapply mem_grows_trans; [apply M1_grows | exact HG].
Qed.

Lemma MI_saved : forall M' q off, MI M' -> In (q, off) SAVE_SLOTS -> cell BSEGS M' (S + -2032 + off) 8 (rget l0 q).
Proof.
  intros M' q off [HU HG] Hin. unfold B_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply M1_saved; exact Hin];
    unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
    try lia; intros x Hx; unfold FPlow, inr in *; lia.
Qed.

Lemma MI_rt : forall M', MI M' -> rt_ok M'.
Proof. intros M' HMI. destruct (MI_final _ HMI) as [HU _]. eapply rt_ok_unch; [exact HU | apply FP_app | exact Hrt]. Qed.
Lemma MI_ic : forall M', MI M' -> ic_ok M'.
Proof. intros M' HMI. destruct (MI_final _ HMI) as [HU _]. eapply ic_ok_unch; [exact HU | apply FP_app | exact Hic]. Qed.

Lemma s_bounds : 0 < s /\ s + n + 8 <= HIMEM_END /\ 0 <= len < 2 ^ 31.
Proof. subst s n len. destruct Hmr as [_ Hr']. unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. Qed.

Lemma MI_ok : forall M', MI M' -> addr_ok M' s n.
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _]. pose proof s_bounds as (H1 & H2 & H3).
  eapply addr_ok_unch; [exact HU | lia | lia | apply FP_nosh | exact Hok].
Qed.
Lemma MI_rd : forall M' a m, MI M' -> rd_ok M a m -> rd_ok M' a m.
Proof. intros M' a m HMI H. destruct (MI_final _ HMI) as [_ HG]. eapply rd_ok_grows; [exact HG | exact H]. Qed.
Lemma MI_wr : forall M' a m, MI M' -> wr_ok BSEGS M a m -> wr_ok BSEGS M' a m.
Proof. intros M' a m HMI H. destruct (MI_final _ HMI) as [_ HG]. eapply wr_ok_grows; [exact HG | exact H]. Qed.
Lemma MI_bytes : forall M', MI M' -> bytes_at M' p N B.
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _].
  eapply bytes_at_unch; [exact HU | lia | lia | | exact HB]. intros x Hx. unfold FP, inr in *. lia.
Qed.

Lemma MI_step : forall M' M'' (P : word -> Prop), MI M' -> unch M' M'' P -> mem_grows M' M'' ->
  (forall x, P x -> FPlow x) -> MI M''.
Proof.
  intros M' M'' P [HU1 HG1] HU' HG' HP. split; [|eapply mem_grows_trans; eassumption].
  eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU' | exact HP].
Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI l0 l /\ rget l 2 = W (S - 2144) /\ rget l 8 = W S.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8); regs_open l Hl.

Ltac prove_stable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; cbn [rget lget]; repeat split; reflexivity.

Ltac pose_saved HMI :=
  pose proof (MI_saved _ 1%nat 2024 HMI ltac:(cbv; tauto)) as Csv1;
  pose proof (MI_saved _ 8%nat 2016 HMI ltac:(cbv; tauto)) as Csv8;
  pose proof (MI_saved _ 9%nat 2008 HMI ltac:(cbv; tauto)) as Csv9;
  pose proof (MI_saved _ 18%nat 2000 HMI ltac:(cbv; tauto)) as Csv18;
  pose proof (MI_saved _ 19%nat 1992 HMI ltac:(cbv; tauto)) as Csv19;
  pose proof (MI_saved _ 20%nat 1984 HMI ltac:(cbv; tauto)) as Csv20;
  pose proof (MI_saved _ 21%nat 1976 HMI ltac:(cbv; tauto)) as Csv21;
  pose proof (MI_saved _ 22%nat 1968 HMI ltac:(cbv; tauto)) as Csv22;
  pose proof (MI_saved _ 23%nat 1960 HMI ltac:(cbv; tauto)) as Csv23.

(* [comment removed for export] *)
Lemma epilogue : forall l M', MI M' -> stable l -> rget l 10 = W res ->
  reach BSEGS rom (Z_to_bv 64 0x1a8730) l M' Post.
Proof.
  intros l M' HMI Hst H10. pose_saved HMI. unfold B_IMG_END in *.
  open_stable Hst l. subst sp s0 a0.
  wp_isc (@nil Z). rewrite ?addi_W. replace (S - 2144 + 112) with (S + -2032) by lia. mem_auto.
  destruct (MI_final _ HMI) as [HU HG].
  apply K; [reflexivity | | reflexivity | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma slow_rp : forall l M', MI M' -> stable l -> rget l 9 = W n -> rget l 18 = W s -> rget l 10 = W res ->
  reach BSEGS rom (Z_to_bv 64 0x1a8808) l M' Post.
Proof.
  intros l M' HMI Hst H9 H18 H10. pose proof s_bounds as (Hs0 & Hs1 & Hs2). unfold B_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst sp s0 s1 s2 a0.
  wp_isc (@nil Z).
  replace (Z_to_bv 64 1834564) with (Z_to_bv 64 0x1bfe44) by reflexivity.
  eapply (regpoisoned_cps rom Post M' s n (S - 2144));
    [ apply (MI_rt _ HMI) | exact Hmr | subst n; lia | apply (MI_ok _ HMI) | unfold B_IMG_END; lia | lia
    | eapply wr_ok_sub; [apply (MI_wr _ _ _ HMI Hfr) | lia | lia]
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' Hl' Hse' H10' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1738776) 0) with (Z_to_bv 64 0x1a8818) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  assert (HMI2 : MI M'').
  { eapply MI_step; [exact HMI | exact HU' | exact HG' |]. intros x Hx. unfold BRegPoisoned.FP, FPlow, inr in *. lia. }
  wp_isc [0x1a8730].
  split; intros Hb; [|exfalso; apply Hb; reflexivity].
  apply epilogue; [exact HMI2 | prove_stable Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma scan_loop : forall m t l M', sha (s + n - 1) - t = Z.of_nat m -> sha s <= t < sha (s + n - 1) ->
  MI M' -> stable l -> rget l 9 = W n -> rget l 18 = W s -> rget l 10 = W res ->
  rget l 11 = W t -> rget l 12 = W (sha (s + n - 1)) -> rget l 13 = W 0 ->
  reach BSEGS rom (Z_to_bv 64 0x1a87f0) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros t l M' Hm Ht HMI Hst H9 H18 H10 H11 H12 H13.
  pose proof s_bounds as (Hs0 & Hs1 & Hs2).
  pose proof (sha_range s ltac:(lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' s n (MI_ok _ HMI) ltac:(lia) ltac:(subst n; lia)) as Hzz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp s0 s1 s2 a0 a1 a2 a3.
  wp_isc [0x1a87f0; 0x1a8730; 0x1a8808].
  exists (W 0). split; [eapply load1_zeros; [exact Hzz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (s + n - 1) - (t + 1)))) with (t := t + 1); try lia; try exact HMI;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply epilogue; [exact HMI | prove_stable Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma scan : forall l M', MI M' -> stable l -> rget l 9 = W n -> rget l 18 = W s -> rget l 10 = W res ->
  rget l 11 = W (sha s) -> rget l 12 = W (sha (s + n - 1)) -> rget l 19 = W (s + n - 1) ->
  reach BSEGS rom (Z_to_bv 64 0x1a87d4) l M' Post.
Proof.
  intros l M' HMI Hst H9 H18 H10 H11 H12 H19.
  pose proof s_bounds as (Hs0 & Hs1 & Hs2).
  assert (Hn1 : 0 < n) by (subst n; lia).
  pose proof (sha_range s ltac:(lia)) as Hr1. pose proof (sha_range (s + n - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono s (s + n - 1) ltac:(lia)) as Hmono.
  destruct (sh_load BSEGS M' (s + n - 1) (MI_ok _ HMI (s + n - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hcu).
  pose proof (Z.mod_pos_bound (s + n - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_stable Hst l. subst sp s0 s1 s2 s3 a0 a1 a2.
  wp_isc [0x1a87f0; 0x1a8730; 0x1a8808].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((s + n - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    apply epilogue; [exact HMI | prove_stable Hse | reflexivity].
  - eapply (scan_loop (Z.to_nat (sha (s + n - 1) - sha s))) with (t := sha s); try lia; try exact HMI;
      [prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma check : forall l M', MI M' -> stable l -> rget l 18 = W s -> rget l 19 = W len -> rget l 10 = W res ->
  reach BSEGS rom (Z_to_bv 64 0x1a86dc) l M' Post.
Proof.
  intros l M' HMI Hst H18 H19 H10.
  pose proof s_bounds as (Hs0 & Hs1 & Hs2).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_stable Hst l. subst sp s0 s2 s3 a0.
  wp_isc [0x1a8730; 0x1a8760; 0x1a87d4; 0x1a8808]. rewrite ?addi_W.
  unfold HIMEM_END in *. rewrite u_not_W by lia. rewrite (Wu (len + 1)) by lia.
  split; intros Hb0; [exfalso; lia|]. clear Hb0.
  change (bv_unsigned (Z_to_bv 64 64)) with 64. rewrite (Wu len) by lia.
  split; intros Hb1.
  - (* [comment removed for export] *)
    split; intros Hb2; [|exfalso; lia].
    apply slow_rp; [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity].
  - (* [comment removed for export] *)
    assert (Hn1 : 0 < n) by (subst n; lia).
    pose proof (sha_range s ltac:(unfold HIMEM_END; lia)) as Hr1.
    pose proof (sha_range (s + n - 1) ltac:(unfold HIMEM_END; lia)) as Hr2.
    pose proof (sha_mono s (s + n - 1) ltac:(lia)) as Hmono.
    pose proof (MI_rd _ _ _ HMI Hshw) as Hw. unfold shw_ok in Hw. fold s n in Hw.
    unfold SB, HIMEM_BEG in *.
    mem_auto. rewrite ?add_W, ?addi_W. replace (len + s) with (s + n - 1) by (subst n len; lia).
    rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
    pose proof (align_dn_le (sha s)) as Ha1. pose proof (align_dn_le (sha (s + n - 1))) as Ha2.
    assert (Hdiv : sha s / 8 <= sha (s + n - 1) / 8) by (apply Z.div_le_mono; lia).
    destruct (load_rd BSEGS M' _ _ (sha s / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
    destruct (load_rd BSEGS M' _ _ (sha (s + n - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
    exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
    split; intros Hb3.
    + apply scan; [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
    + apply epilogue; [exact HMI | prove_stable Hse | reflexivity].
Qed.

Lemma first_nul : bv_unsigned (B r) <> c -> bv_unsigned (B r) = 0 /\ forall j, k <= j < r -> bv_unsigned (B j) <> 0.
Proof. intros Hne. split; [destruct HBr; [assumption | contradiction] | intros j Hj; apply (HBn j Hj)]. Qed.

(* [comment removed for export] *)
Lemma after_real : forall l M', MI M' -> stable l -> rget l 18 = W s -> rget l 19 = W 1 -> rget l 10 = W res ->
  reach BSEGS rom (Z_to_bv 64 0x1a8668) l M' Post.
Proof.
  intros l M' HMI Hst H18 H19 H10.
  pose proof s_bounds as (Hs0 & Hs1 & Hs2).
  pose proof (MI_ic _ HMI) as (_ & Hgcf & Hf245 & _ & Hf253 & _). unfold G_CF, C_CF in *.
  open_stable Hst l. subst sp s0 s2 s3 a0.
  wp_isc [0x1a8730; 0x1a86dc; 0x1a86d0].
  change (bv_unsigned (Z_to_bv 64 1)) with 1.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  mem_auto.
  change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) mod 2 ^ (8 * Z.of_nat 1)))) with 1.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  mem_auto.
  change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) mod 2 ^ (8 * Z.of_nat 1)))) with 0.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  split; intros Hb.
  - (* [comment removed for export] *)
    assert (Hne : bv_unsigned (B r) <> c).
    { intros E. unfold res in Hb. rewrite E, Z.eqb_refl in Hb. rewrite Wu in Hb by lia. lia. }
    destruct (first_nul Hne) as [Hz0 Hnz].
    wp_isc (@nil Z).
    replace (Z_to_bv 64 1900364) with (Z_to_bv 64 0x1cff4c) by reflexivity.
    eapply (istrlen0_cps rom Post M' p N B k r);
      [apply (MI_bytes _ HMI) | lia | lia | lia | lia | exact Hz0 | exact Hnz | reflexivity | reflexivity |].
    intros l' Hl' Hse' H10'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1738452) 0) with (Z_to_bv 64 0x1a86d4) by reflexivity.
    regs_open l' Hl'. se_subst Hse'. clear Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
    wp_isc [0x1a86dc].
    apply check; [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity].
  - (* [comment removed for export] *)
    assert (He : res = p + r).
    { unfold res in *. destruct (Z.eqb_spec (bv_unsigned (B r)) c); [reflexivity|]. exfalso. apply Hb. reflexivity. }
    rewrite sub_W.
    apply check; [exact HMI | prove_stable Hse | reflexivity | cbn [rget lget]; f_equal; rewrite He; subst len s; lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ic_body : forall l, l = l0 -> rget l 10 = W s -> bv_unsigned (rget l 11) mod 256 = c ->
  reach BSEGS rom (Z_to_bv 64 0x1a860c) l M Post.
Proof.
  intros l El H10 H11. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2.
  assert (HM1 : M1 = M1) by reflexivity. unfold M1 at 1 in HM1. rewrite <- El in HM1. clear El.
  unfold B_IMG_END in *.
  regs_open l Hl. subst sp a0.
  wp_isc (@nil Z). rewrite ?addi_W. mem_auto. replace (S + -2032 + 2032) with S by lia.
  replace (S + -2032 + -112) with (S - 2144) by lia.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with M1 by (symmetry; exact HM1) end. clear HM1.
  pose proof MI_M1 as HMI. generalize dependent M1. intros M' HMI.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1853556) with (Z_to_bv 64 0x1c4874) by reflexivity.
  pose proof (MI_ic _ HMI) as (Hini & _).
  eapply (inited_cps rom Post M'); [exact Hini | reflexivity |].
  intros l1 Hl1 Hse1 H10'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1738312) 0) with (Z_to_bv 64 0x1a8648) by reflexivity.
  regs_open l1 Hl1. se_subst Hse1. clear Hse1. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  wp_isc [0x1a8690]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1857412) with (Z_to_bv 64 0x1c5784) by reflexivity.
  eapply (tryinit_cps rom Post M' (S - 2144)); [exact Hini | unfold B_IMG_END; lia
    | eapply wr_ok_sub; [apply (MI_wr _ _ _ HMI Hfr) | lia | lia] | reflexivity | reflexivity |].
  intros l2 M2 Hl2 Hse2 H10'' HU2 HG2. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1738320) 0) with (Z_to_bv 64 0x1a8650) by reflexivity.
  regs_open l2 Hl2. se_subst Hse2. clear Hse2. cbn [rget lget] in H10''. match type of H10'' with ?x = _ => subst x end.
  assert (HMI2 : MI M2).
  { eapply MI_step; [exact HMI | exact HU2 | exact HG2 |]. intros x Hx. unfold FPlow, inr in *. lia. }
  clear HMI Hini HU2 HG2.
  (* [comment removed for export] *)
  pose proof (MI_ic _ HMI2) as (_ & _ & _ & _ & _ & _ & Hreal & _ & Hi1 & Hi2). unfold R_STRCHR in *.
  wp_isc (@nil Z). mem_auto.
  replace (v_jalr (Z_to_bv 64 5650480) 0) with (Z_to_bv 64 0x563830) by reflexivity.
  eapply (strchr_cps rom Post M2 p N B k r c (S - 2144));
    [ apply (MI_bytes _ HMI2) | lia | lia | lia | lia | lia | exact HBr | exact HBn | exact Hslack | exact Hi1 | exact Hi2
    | lia | lia | eapply wr_ok_sub; [apply (MI_wr _ _ _ HMI2 Hfr) | lia | lia] | lia
    | reflexivity | reflexivity | reflexivity | exact H11 |].
  intros l3 M3 Hl3 Hse3 H10''' HU3 HG3. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1738344) 0) with (Z_to_bv 64 0x1a8668) by reflexivity.
  regs_open l3 Hl3. se_subst Hse3. clear Hse3. cbn [rget lget] in H10'''. match type of H10''' with ?x = _ => subst x end.
  assert (HMI3 : MI M3).
  { eapply MI_step; [exact HMI2 | exact HU3 | exact HG3 |]. intros x Hx. unfold FR2, FPlow, inr in *. lia. }
  apply after_real; [exact HMI3 | prove_stable Hse | reflexivity | reflexivity | reflexivity].
Qed.

End IcStrchr.

(* [comment removed for export] *)
Theorem istrchr_cps : forall rom Post M p N B k r c S l,
  rt_ok M -> ic_ok M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= r -> r < N -> 0 < c < 256 ->
  r - k < 2 ^ 31 ->
  (bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c) ->
  (forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c) ->
  (p + r) / 8 * 8 + 8 <= p + N ->
  memrange (p + k) (r - k + 1) -> addr_ok M (p + k) (r - k + 1) -> shw_ok M (p + k) (r - k + 1) ->
  B_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok BSEGS M (S - 2224) 2224 ->
  (p + N <= S - 2224 \/ S <= p) ->
  length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) -> bv_unsigned (rget l 11) mod 256 = c ->
  (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
                 rget l' 10 = W (if Z.eqb (bv_unsigned (B r)) c then p + r else 0) ->
                 unch M M' (FP S) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1a860c) l M Post.
Proof.
  intros rom Post M p N B k r c S l; intros.
  eapply (ic_body rom Post M p N B k r c S) with (l0 := l); eauto.
Qed.

(* [comment removed for export] *)
Theorem istrchr_stub_cps : forall rom Post M p N B k r c S l,
  rt_ok M -> ic_ok M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= r -> r < N -> 0 < c < 256 ->
  r - k < 2 ^ 31 ->
  (bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c) ->
  (forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c) ->
  (p + r) / 8 * 8 + 8 <= p + N ->
  memrange (p + k) (r - k + 1) -> addr_ok M (p + k) (r - k + 1) -> shw_ok M (p + k) (r - k + 1) ->
  B_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok BSEGS M (S - 2224) 2224 ->
  (p + N <= S - 2224 \/ S <= p) ->
  length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) -> bv_unsigned (rget l 11) mod 256 = c ->
  (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
                 rget l' 10 = W (if Z.eqb (bv_unsigned (B r)) c then p + r else 0) ->
                 unch M M' (FP S) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1a74e4) l M Post.
Proof.
  intros rom Post M p N B k r c S l Hrt Hic HB Hp Hk Hr Hc Hlen HBr HBn Hsl Hmr Hok Hshw HS HSz Hfr Hdj Hl H2 H10 H11 K.
  pose proof Hl as Hl'. regs_open l Hl'.
  wp_go 0x1a74d4 36%nat C_stubs_eq C_stubs (@nil Z).
  replace (Z_to_bv 64 1738252) with (Z_to_bv 64 0x1a860c) by reflexivity.
  eapply (istrchr_cps rom Post M p N B k r c S); try eassumption; try reflexivity.
Qed.

Print Assumptions istrchr_stub_cps.
