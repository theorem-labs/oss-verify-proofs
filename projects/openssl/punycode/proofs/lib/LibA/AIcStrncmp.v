(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt ASaves ArCode ARtIc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_icm stops := wp_go 0x1ad120 375%nat C_ic_strncmp_eq C_ic_strncmp stops.

Lemma load_ok_agree : forall M M' a (m : nat) v, 0 <= a -> a + Z.of_nat m < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat m) -> M' x = M x) -> load_ok ASEGS M (W a) m v -> load_ok ASEGS M' (W a) m v.
Proof.
  intros M M' a m v Ha Hm Hag (bs & Hr & Hv). exists bs. split; [|exact Hv]. rewrite <- Hr.
  apply rdn_ext; [rewrite Wu by lia; lia|]. intros x Hx. rewrite Wu in Hx by lia. apply Hag. exact Hx.
Qed.

Lemma sltu_W : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_sltu (W a) (W b) = W (if Z.ltb a b then 1 else 0).
Proof.
  intros a b Ha Hb. unfold v_sltu, c_ltu, bv_ltu. rewrite !Wu by lia.
  destruct (Z.ltb_spec a b); reflexivity.
Qed.

Lemma memrange_sub : forall a m a' m', memrange a m -> a <= a' -> 0 <= m' -> a' + m' <= a + m -> memrange a' m'.
Proof. intros a m a' m' [Hm Hr] Ha Hm' Hle. split; [exact Hm'|]. unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. Qed.

Section IcStrncmp.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (p N : Z) (B : Z -> byte) (k z q n : Z) (RB : Z -> byte) (S : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hic : ic_ok M.
Hypothesis HB : bytes_at M p N B.
Hypothesis Hp : 0 < p /\ p + N < 2 ^ 63.
Hypothesis Hk : 0 <= k <= z.
Hypothesis Hz : z < N.
Hypothesis HBz : bv_unsigned (B z) = 0.
Hypothesis HBnz : forall j, k <= j < z -> bv_unsigned (B j) <> 0.
Hypothesis Hn : 0 < n <= 64.
Hypothesis Hq : 0 < q /\ q + n < 2 ^ 63.
Hypothesis HRB : forall i, 0 <= i < n -> load_ok ASEGS M (W (q + i)) 1 (W (bv_unsigned (RB i))).
Hypothesis HRBnz : forall i, 0 <= i < n -> bv_unsigned (RB i) <> 0.
Hypothesis Hmr1 : memrange (p + k) (Z.min (z - k + 1) n).
Hypothesis Hok1 : addr_ok M (p + k) (Z.min (z - k + 1) n).
Hypothesis Hshw1 : shw_ok M (p + k) (Z.min (z - k + 1) n).
Hypothesis Hmr2 : memrange q n.
Hypothesis Hok2 : addr_ok M q n.
Hypothesis Hshw2 : shw_ok M q n.
Hypothesis HS : A_IMG_END <= S - 2256 /\ S < 2 ^ 63.
Hypothesis HSz : S <= SB \/ HIMEM_BEG <= S - 2256.
Hypothesis Hfr : wr_ok ASEGS M (S - 2256) 2256.
Hypothesis Hdj : p + N <= S - 2256 \/ S <= p.
Hypothesis Hdjq : q + n <= S - 2256 \/ S <= q.

Let s1p := p + k.

Definition KSI : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition FP (x : word) : Prop := inr x (S - 2256) 2256.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSC l0 l' ->
  (bv_unsigned (rget l' 10) = 0 -> forall i, 0 <= i < n -> B (k + i) = RB i) ->
  unch M M' FP -> mem_grows M M' ->
  reach ASEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition SL : list (Z * word) :=
  [(2024, rget l0 1); (2016, rget l0 8); (2008, rget l0 9); (2000, rget l0 18); (1992, rget l0 19); (1984, rget l0 20);
   (1976, rget l0 21); (1968, rget l0 22); (1960, rget l0 23); (1952, rget l0 24); (1944, rget l0 25); (1936, rget l0 26);
   (1928, rget l0 27)].
Definition M1 : mem := saves M (S + -2032) SL.

Lemma SL_ok : slots_ok 2032 SL = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition FPlow (x : word) : Prop := inr x (S - 2256) 80.
Definition MI (M' : mem) : Prop := unch M1 M' FPlow /\ mem_grows M1 M'.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma FP_app : forall y, FP y -> A_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold FP, inr in Hy. lia. Qed.
Lemma FP_nosh : forall y, FP y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof. intros y Hy. unfold FP, inr in Hy. lia. Qed.

Lemma MI_final : forall M', MI M' -> unch M M' FP /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. unfold A_IMG_END in *. split.
  - apply (unch_trans M M1 M').
    + unfold M1. apply (saves_unch SL M M (S + -2032) 2032); [lia | lia | exact SL_ok | | apply unch_refl].
      intros x Hx. unfold FP, inr in *. lia.
    + eapply unch_weaken; [exact HU|]. intros x Hx. unfold FPlow, FP, inr in *. lia.
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
Proof. intros M' HMI. destruct (MI_final _ HMI) as [HU _]. eapply rt_ok_unch; [exact HU | apply FP_app | exact Hrt]. Qed.
Lemma MI_ic : forall M', MI M' -> ic_ok M'.
Proof. intros M' HMI. destruct (MI_final _ HMI) as [HU _]. eapply ic_ok_unch; [exact HU | apply FP_app | exact Hic]. Qed.
Lemma MI_rd : forall M' a m, MI M' -> rd_ok M a m -> rd_ok M' a m.
Proof. intros M' a m HMI H. destruct (MI_final _ HMI) as [_ HG]. eapply rd_ok_grows; [exact HG | exact H]. Qed.
Lemma MI_wr : forall M' a m, MI M' -> wr_ok ASEGS M a m -> wr_ok ASEGS M' a m.
Proof. intros M' a m HMI H. destruct (MI_final _ HMI) as [_ HG]. eapply wr_ok_grows; [exact HG | exact H]. Qed.
Lemma MI_bytes : forall M', MI M' -> bytes_at M' p N B.
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _].
  eapply bytes_at_unch; [exact HU | lia | lia | | exact HB]. intros x Hx. unfold FP, inr in *. lia.
Qed.
Lemma MI_RB : forall M' i, MI M' -> 0 <= i < n -> load_ok ASEGS M' (W (q + i)) 1 (W (bv_unsigned (RB i))).
Proof.
  intros M' i HMI Hi. destruct (MI_final _ HMI) as [HU _].
  eapply load_ok_agree; [lia | cbn; lia | | apply HRB; exact Hi].
  intros x Hx. apply HU. cbn in Hx. unfold FP, inr in *. lia.
Qed.

Lemma MI_step : forall M' M'' (P : word -> Prop), MI M' -> unch M' M'' P -> mem_grows M' M'' ->
  (forall x, P x -> FPlow x) -> MI M''.
Proof.
  intros M' M'' P [HU1 HG1] HU' HG' HP. split; [|eapply mem_grows_trans; eassumption].
  eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU' | exact HP].
Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI l0 l /\ rget l 2 = W (S - 2176) /\ rget l 8 = W S
  /\ rget l 9 = W n /\ rget l 18 = W q /\ rget l 19 = W s1p.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H9 & ?H18 & ?H19); regs_open l Hl.

Ltac prove_stable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Definition exit_ok (m c1 c2 : Z) : Prop :=
  0 <= m <= n /\ 0 <= c1 < 256 /\ 0 <= c2 < 256 /\ (forall j, 0 <= j < m -> B (k + j) = RB j)
  /\ (m = n -> c1 = c2) /\ (m < n -> c1 <> c2) /\ k + Z.min (m + 1) n - 1 <= z.

Definition xst (l : regfile) (m c1 c2 : Z) : Prop :=
  stable l /\ rget l 24 = W c1 /\ rget l 25 = W c2 /\ rget l 27 = W m.

Ltac open_xst H l :=
  let Hst := fresh "Hst" in destruct H as (Hst & ?H24 & ?H25 & ?H27); open_stable Hst l.
Ltac prove_xst Hse := split; [prove_stable Hse|]; cbn [rget lget]; repeat split; reflexivity.

Ltac pose_saved HMI :=
  pose proof (MI_saved _ 2024 _ HMI ltac:(unfold SL; in_list)) as Csv1;
  pose proof (MI_saved _ 2016 _ HMI ltac:(unfold SL; in_list)) as Csv8;
  pose proof (MI_saved _ 2008 _ HMI ltac:(unfold SL; in_list)) as Csv9;
  pose proof (MI_saved _ 2000 _ HMI ltac:(unfold SL; in_list)) as Csv18;
  pose proof (MI_saved _ 1992 _ HMI ltac:(unfold SL; in_list)) as Csv19;
  pose proof (MI_saved _ 1984 _ HMI ltac:(unfold SL; in_list)) as Csv20;
  pose proof (MI_saved _ 1976 _ HMI ltac:(unfold SL; in_list)) as Csv21;
  pose proof (MI_saved _ 1968 _ HMI ltac:(unfold SL; in_list)) as Csv22;
  pose proof (MI_saved _ 1960 _ HMI ltac:(unfold SL; in_list)) as Csv23;
  pose proof (MI_saved _ 1952 _ HMI ltac:(unfold SL; in_list)) as Csv24;
  pose proof (MI_saved _ 1944 _ HMI ltac:(unfold SL; in_list)) as Csv25;
  pose proof (MI_saved _ 1936 _ HMI ltac:(unfold SL; in_list)) as Csv26;
  pose proof (MI_saved _ 1928 _ HMI ltac:(unfold SL; in_list)) as Csv27.

(* [comment removed for export] *)
Lemma result : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  reach ASEGS rom (Z_to_bv 64 0x1ad374) l M' Post.
Proof.
  intros l M' m c1 c2 HMI (Hm & Hc1 & Hc2 & Heq & Hmn & Hmlt & _) Hx. pose_saved HMI. unfold A_IMG_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11.
  wp_icm (@nil Z).
  replace (v_jalr (Z_to_bv 64 1758104) 0) with (Z_to_bv 64 0x1ad398) by reflexivity.
  wp_icm (@nil Z). rewrite ?addi_W. replace (S - 2176 + 144) with (S + -2032) by lia. mem_auto.
  destruct (MI_final _ HMI) as [HU HG].
  apply K; [reflexivity | | | exact HU | exact HG].
  - same_fix Hse. rewrite H0sp. f_equal. lia.
  - cbn [rget lget]. rewrite !sltu_W by lia. rewrite sub_W. intros H0 i Hi.
    destruct (Z.eq_dec m n) as [E|E]; [apply Heq; lia|]. exfalso.
    assert (Hne : c1 <> c2) by (apply Hmlt; lia).
    destruct (Z.ltb_spec c2 c1), (Z.ltb_spec c1 c2); try lia.
    + change (1 - 0) with 1 in H0. rewrite Wu in H0 by lia. lia.
    + rewrite Wu_neg in H0 by lia. lia.
Qed.

(* [comment removed for export] *)
Definition sz (m : Z) : Z := Z.min (m + 1) n.

Lemma q_bounds : 0 < q /\ q + n + 8 <= HIMEM_END.
Proof. destruct Hmr2 as [_ Hr]. unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. Qed.

Lemma MI_ok2 : forall M' m, MI M' -> 0 <= m <= n -> addr_ok M' q (sz m).
Proof.
  intros M' m HMI Hm. destruct (MI_final _ HMI) as [HU _]. pose proof q_bounds as (H1 & H2). unfold sz.
  eapply addr_ok_unch; [exact HU | lia | lia | apply FP_nosh |].
  eapply addr_ok_sub; [exact Hok2 | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma scan2_loop : forall f t l M' m c1 c2, sha (q + sz m - 1) - t = Z.of_nat f -> sha q <= t < sha (q + sz m - 1) ->
  MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  rget l 10 = W t -> rget l 11 = W (sha (q + sz m - 1)) -> rget l 12 = W 0 ->
  reach ASEGS rom (Z_to_bv 64 0x1ad5d8) l M' Post.
Proof.
  induction f as [f IH] using lt_wf_ind; intros t l M' m c1 c2 Hf Ht HMI Hex Hx H10 H11 H12.
  pose proof q_bounds as (Hq0 & Hq1). pose proof Hex as (Hm & _).
  assert (Hsz : 0 < sz m <= n) by (unfold sz; lia).
  pose proof (sha_range q ltac:(lia)) as Hr1. pose proof (sha_range (q + sz m - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' q (sz m) (MI_ok2 _ m HMI Hm) ltac:(lia) ltac:(lia)) as Hzz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11 a0 a1 a2.
  wp_icm [0x1ad5d8; 0x1ad374; 0x1ad5f0].
  exists (W 0). split; [eapply load1_zeros; [exact Hzz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (q + sz m - 1) - (t + 1)))) with (t := t + 1) (m := m) (c1 := c1) (c2 := c2);
      try lia; try exact HMI; try exact Hex; [prove_xst Hse | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    eapply (result _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse].
Qed.

(* [comment removed for export] *)
Lemma scan2 : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  rget l 10 = W (sha q) -> rget l 11 = W (sha (q + sz m - 1)) -> rget l 12 = W (q + sz m - 1) ->
  reach ASEGS rom (Z_to_bv 64 0x1ad5bc) l M' Post.
Proof.
  intros l M' m c1 c2 HMI Hex Hx H10 H11 H12.
  pose proof q_bounds as (Hq0 & Hq1). pose proof Hex as (Hm & _).
  assert (Hsz : 0 < sz m <= n) by (unfold sz; lia).
  pose proof (sha_range q ltac:(lia)) as Hr1. pose proof (sha_range (q + sz m - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono q (q + sz m - 1) ltac:(lia)) as Hmono.
  destruct (sh_load ASEGS M' (q + sz m - 1) (MI_ok2 _ m HMI Hm (q + sz m - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hcu).
  pose proof (Z.mod_pos_bound (q + sz m - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11 a0 a1 a2.
  wp_icm [0x1ad5d8; 0x1ad374; 0x1ad5f0].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((q + sz m - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    eapply (result _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse].
  - eapply (scan2_loop (Z.to_nat (sha (q + sz m - 1) - sha q)) (sha q) _ _ m c1 c2); try lia; try exact HMI; try exact Hex;
      [prove_xst Hse | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma check2 : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 -> rget l 21 = W (sz m) ->
  reach ASEGS rom (Z_to_bv 64 0x1ad32c) l M' Post.
Proof.
  intros l M' m c1 c2 HMI Hex Hx H21.
  pose proof q_bounds as (Hq0 & Hq1). pose proof Hex as (Hm & _).
  assert (Hsz : 0 < sz m <= n) by (unfold sz; lia).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s5 s8 s9 s11.
  wp_icm [0x1ad374; 0x1ad458; 0x1ad5bc]. rewrite ?addi_W.
  change (bv_unsigned (Z_to_bv 64 (-65))) with (2 ^ 64 - 65). rewrite Wu_neg by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  pose proof (sha_range q ltac:(unfold HIMEM_END in *; lia)) as Hr1.
  pose proof (sha_range (q + sz m - 1) ltac:(unfold HIMEM_END in *; lia)) as Hr2.
  pose proof (sha_mono q (q + sz m - 1) ltac:(lia)) as Hmono.
  assert (Hw : rd_ok M' (sha q / 8 * 8) (sha (q + sz m - 1) / 8 * 8 + 8 - sha q / 8 * 8)).
  { apply (MI_rd _ _ _ HMI). apply (shw_ok_sub M q n q (sz m) Hshw2); lia. }
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  mem_auto. rewrite ?add_W, ?addi_W. replace (q + sz m + -1) with (q + sz m - 1) by lia.
  rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
  pose proof (align_dn_le (sha q)) as Ha1. pose proof (align_dn_le (sha (q + sz m - 1))) as Ha2.
  assert (Hdiv : sha q / 8 <= sha (q + sz m - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (load_rd ASEGS M' _ _ (sha q / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
  destruct (load_rd ASEGS M' _ _ (sha (q + sz m - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
  exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
  split; intros Hb3.
  - eapply (scan2 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | reflexivity | reflexivity | reflexivity].
  - eapply (result _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse].
Qed.

(* [comment removed for export] *)
Lemma mid : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  reach ASEGS rom (Z_to_bv 64 0x1ad31c) l M' Post.
Proof.
  intros l M' m c1 c2 HMI Hex Hx.
  pose proof q_bounds as (Hq0 & Hq1). pose proof Hex as (Hm & _). unfold HIMEM_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11.
  wp_icm [0x1ad32c; 0x1ad3e8]. rewrite ?addi_W. rewrite u_not_W by lia. rewrite !Wu by lia.
  split; intros Hb.
  - split; intros Hb2; [|exfalso; lia].
    eapply (check2 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | cbn [rget lget]; f_equal; unfold sz; lia].
  - split; intros Hb2; [exfalso; lia|].
    eapply (check2 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | cbn [rget lget]; f_equal; unfold sz; lia].
Qed.

Lemma s1_bounds : forall m c1 c2, exit_ok m c1 c2 ->
  0 < s1p /\ s1p + sz m + 8 <= HIMEM_END /\ 0 < sz m <= n /\ sz m <= Z.min (z - k + 1) n.
Proof.
  intros m c1 c2 (Hm & _ & _ & _ & _ & _ & Hzz). destruct Hmr1 as [_ Hr]. subst s1p. unfold sz in *.
  unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia.
Qed.

Lemma MI_ok1 : forall M' m c1 c2, MI M' -> exit_ok m c1 c2 -> addr_ok M' s1p (sz m).
Proof.
  intros M' m c1 c2 HMI Hex. destruct (MI_final _ HMI) as [HU _]. pose proof (s1_bounds _ _ _ Hex) as (H1 & H2 & H3 & H4).
  eapply addr_ok_unch; [exact HU | lia | lia | apply FP_nosh |].
  eapply addr_ok_sub; [exact Hok1 | subst s1p; lia | subst s1p; lia].
Qed.

(* [comment removed for export] *)
Lemma scan1_loop : forall f t l M' m c1 c2, sha (s1p + sz m - 1) - t = Z.of_nat f -> sha s1p <= t < sha (s1p + sz m - 1) ->
  MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  rget l 10 = W t -> rget l 11 = W (sha (s1p + sz m - 1)) -> rget l 12 = W 0 ->
  reach ASEGS rom (Z_to_bv 64 0x1ad510) l M' Post.
Proof.
  induction f as [f IH] using lt_wf_ind; intros t l M' m c1 c2 Hf Ht HMI Hex Hx H10 H11 H12.
  pose proof (s1_bounds _ _ _ Hex) as (Hs0 & Hs1 & Hsz & _).
  pose proof (sha_range s1p ltac:(lia)) as Hr1. pose proof (sha_range (s1p + sz m - 1) ltac:(lia)) as Hr2.
  pose proof (addr_ok_scan_zeros M' s1p (sz m) (MI_ok1 _ _ _ _ HMI Hex) ltac:(lia) ltac:(lia)) as Hzz.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11 a0 a1 a2.
  wp_icm [0x1ad510; 0x1ad31c; 0x1ad528].
  exists (W 0). split; [eapply load1_zeros; [exact Hzz | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb.
  - eapply (IH (Z.to_nat (sha (s1p + sz m - 1) - (t + 1)))) with (t := t + 1) (m := m) (c1 := c1) (c2 := c2);
      try lia; try exact HMI; try exact Hex; [prove_xst Hse | reflexivity | reflexivity | reflexivity].
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    eapply (mid _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse].
Qed.

(* [comment removed for export] *)
Lemma scan1 : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  rget l 10 = W (sha s1p) -> rget l 11 = W (sha (s1p + sz m - 1)) -> rget l 12 = W (s1p + sz m - 1) ->
  reach ASEGS rom (Z_to_bv 64 0x1ad4f4) l M' Post.
Proof.
  intros l M' m c1 c2 HMI Hex Hx H10 H11 H12.
  pose proof (s1_bounds _ _ _ Hex) as (Hs0 & Hs1 & Hsz & _).
  pose proof (sha_range s1p ltac:(lia)) as Hr1. pose proof (sha_range (s1p + sz m - 1) ltac:(lia)) as Hr2.
  pose proof (sha_mono s1p (s1p + sz m - 1) ltac:(lia)) as Hmono.
  destruct (sh_load ASEGS M' (s1p + sz m - 1) (MI_ok1 _ _ _ _ HMI Hex (s1p + sz m - 1) ltac:(lia)) ltac:(lia)) as (u & Hu & Hcu).
  pose proof (Z.mod_pos_bound (s1p + sz m - 1) 8 ltac:(lia)) as Hm8.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11 a0 a1 a2.
  wp_icm [0x1ad510; 0x1ad31c; 0x1ad528].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  rewrite andi7_W by lia. rewrite (poisoned_zero u ((s1p + sz m - 1) mod 8)) by lia.
  rewrite !Wu by lia.
  split; intros Hb.
  - change (v_andi (Z_to_bv 64 0) 255) with (W 0).
    split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    eapply (mid _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse].
  - eapply (scan1_loop (Z.to_nat (sha (s1p + sz m - 1) - sha s1p)) (sha s1p) _ _ m c1 c2); try lia; try exact HMI; try exact Hex;
      [prove_xst Hse | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma check1 : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 -> rget l 21 = W (sz m) ->
  reach ASEGS rom (Z_to_bv 64 0x1ad2d4) l M' Post.
Proof.
  intros l M' m c1 c2 HMI Hex Hx H21.
  pose proof (s1_bounds _ _ _ Hex) as (Hs0 & Hs1 & Hsz & Hsz2).
  pose proof (MI_rt _ HMI) as (Hg & Hsb & _). unfold G_SB, C_SB in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s5 s8 s9 s11.
  wp_icm [0x1ad31c; 0x1ad4ec; 0x1ad4f4]. rewrite ?addi_W.
  change (bv_unsigned (Z_to_bv 64 (-65))) with (2 ^ 64 - 65). rewrite Wu_neg by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  pose proof (sha_range s1p ltac:(unfold HIMEM_END in *; lia)) as Hr1.
  pose proof (sha_range (s1p + sz m - 1) ltac:(unfold HIMEM_END in *; lia)) as Hr2.
  pose proof (sha_mono s1p (s1p + sz m - 1) ltac:(lia)) as Hmono.
  assert (Hw : rd_ok M' (sha s1p / 8 * 8) (sha (s1p + sz m - 1) / 8 * 8 + 8 - sha s1p / 8 * 8)).
  { apply (MI_rd _ _ _ HMI). apply (shw_ok_sub M s1p (Z.min (z - k + 1) n) s1p (sz m) Hshw1); lia. }
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  mem_auto. rewrite ?add_W, ?addi_W. replace (s1p + sz m + -1) with (s1p + sz m - 1) by lia.
  rewrite !sha_addr_l by lia. rewrite !andi_m8_W by lia.
  pose proof (align_dn_le (sha s1p)) as Ha1. pose proof (align_dn_le (sha (s1p + sz m - 1))) as Ha2.
  assert (Hdiv : sha s1p / 8 <= sha (s1p + sz m - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (load_rd ASEGS M' _ _ (sha s1p / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v1 Hv1].
  destruct (load_rd ASEGS M' _ _ (sha (s1p + sz m - 1) / 8 * 8) 8 Hw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [v2 Hv2].
  exists v1. split; [exact Hv1|]. exists v2. split; [exact Hv2|].
  split; intros Hb3.
  - eapply (scan1 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | reflexivity | reflexivity | reflexivity].
  - eapply (mid _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse].
Qed.

(* [comment removed for export] *)
Lemma after_loop : forall l M' m c1 c2, MI M' -> exit_ok m c1 c2 -> xst l m c1 c2 ->
  reach ASEGS rom (Z_to_bv 64 0x1ad1b4) l M' Post.
Proof.
  intros l M' m c1 c2 HMI Hex Hx.
  pose proof (s1_bounds _ _ _ Hex) as (Hs0 & Hs1 & Hsz & Hsz2). pose proof Hex as (Hm & _).
  pose proof (MI_ic _ HMI) as (_ & Hgcf & Hf245 & _). unfold G_CF, C_CF in *.
  unfold HIMEM_END in *.
  open_xst Hx l. subst sp s0 s1 s2 s3 s8 s9 s11.
  wp_icm [0x1ad2d4; 0x1ad47c; 0x1ad1d0]. rewrite ?addi_W. rewrite ?u_not_W by lia. rewrite !Wu by lia.
  split; intros Hb.
  - (* [comment removed for export] *)
    split; intros Hb1; [exfalso; lia|].
    split; intros Hb2; [|exfalso; lia].
    eapply (check1 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | cbn [rget lget]; f_equal; unfold sz; lia].
  - mem_auto.
    change (bv_unsigned (v_andi (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) mod 2 ^ (8 * Z.of_nat 1))) 1)) with 0.
    split; intros Hb0; [|exfalso; apply Hb0; reflexivity]. clear Hb0.
    split; intros Hb1.
    + split; intros Hb2; [|exfalso; lia].
      eapply (check1 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | cbn [rget lget]; f_equal; unfold sz; lia].
    + split; intros Hb2; [exfalso; lia|].
      eapply (check1 _ _ m c1 c2); [exact HMI | exact Hex | prove_xst Hse | cbn [rget lget]; f_equal; unfold sz; lia].
Qed.

(* [comment removed for export] *)
Lemma cmp_loop : forall f i l M', n - i = Z.of_nat f -> 0 <= i < n ->
  (forall j, 0 <= j < i -> B (k + j) = RB j) ->
  MI M' -> stable l -> rget l 27 = W i ->
  reach ASEGS rom (Z_to_bv 64 0x1ad18c) l M' Post.
Proof.
  induction f as [f IH] using lt_wf_ind; intros i l M' Hf Hi Heq HMI Hst H27.
  assert (Hki : k + i <= z).
  { destruct (Z_le_gt_dec (k + i) z) as [Hle|Hgt]; [exact Hle|]. exfalso.
    assert (Hj : 0 <= z - k < i) by lia. pose proof (Heq (z - k) Hj) as E. replace (k + (z - k)) with z in E by lia.
    apply (HRBnz (z - k)); [lia|]. rewrite <- E. exact HBz. }
  pose proof (MI_bytes _ HMI) as HB'. pose proof (MI_RB _ i HMI Hi) as HRi.
  pose proof (bv_unsigned_in_range 8 (B (k + i))) as Hc1. change (bv_modulus 8) with 256 in Hc1.
  pose proof (bv_unsigned_in_range 8 (RB i)) as Hc2. change (bv_modulus 8) with 256 in Hc2.
  open_stable Hst l. subst sp s0 s1 s2 s3 s11.
  wp_icm [0x1ad18c; 0x1ad1b4]. rewrite ?add_W.
  exists (W (bv_unsigned (B (k + i)))). split.
  { replace (s1p + i) with (p + (k + i)) by (unfold s1p; lia). apply (load1_bytes_at ASEGS M' p N B _ HB'); lia. }
  exists (W (bv_unsigned (RB i))). split; [exact HRi|].
  rewrite !Wu by lia. rewrite ?addi_W.
  assert (Hex1 : bv_unsigned (B (k + i)) <> bv_unsigned (RB i) ->
                 exit_ok i (bv_unsigned (B (k + i))) (bv_unsigned (RB i))).
  { intros Hne. unfold exit_ok. repeat split; try lia; try exact Heq. }
  split; intros Hb1.
  - eapply (after_loop _ _ i _ _); [exact HMI | apply Hex1; pose proof (HRBnz i Hi); lia | prove_xst Hse].
  - split; intros Hb2.
    + eapply (after_loop _ _ i _ _); [exact HMI | apply Hex1; exact Hb2 | prove_xst Hse].
    + assert (EB : B (k + i) = RB i) by (apply bv_eq; exact Hb2).
      assert (Heq' : forall j, 0 <= j < i + 1 -> B (k + j) = RB j).
      { intros j Hj. destruct (Z.eq_dec j i) as [->|]; [exact EB | apply Heq; lia]. }
      rewrite (Wu (i + 1)) by lia.
      split; intros Hb3.
      * eapply (IH (Z.to_nat (n - (i + 1)))) with (i := i + 1); try lia; try exact HMI; try exact Heq';
          [prove_stable Hse | reflexivity].
      * eapply (after_loop _ _ n (bv_unsigned (B (k + i))) (bv_unsigned (B (k + i)))); [exact HMI | | prove_xst Hse].
        unfold exit_ok. repeat split; try lia. intros j Hj. apply Heq'. lia.
Qed.

(* [comment removed for export] *)
Lemma ic_body : forall l, l = l0 -> rget l 10 = W s1p -> rget l 11 = W q -> rget l 12 = W n ->
  reach ASEGS rom (Z_to_bv 64 0x1ad124) l M Post.
Proof.
  intros l El H10 H11 H12. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2.
  assert (HM1 : M1 = M1) by reflexivity. unfold M1 at 1 in HM1. unfold SL in HM1. rewrite <- El in HM1. clear El.
  unfold A_IMG_END in *.
  regs_open l Hl. subst sp a0 a1 a2.
  wp_icm (@nil Z). rewrite ?addi_W. mem_auto. replace (S + -2032 + 2032) with S by lia.
  replace (S + -2032 + -144) with (S - 2176) by lia.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with M1 by (symmetry; exact HM1) end. clear HM1.
  pose proof MI_M1 as HMI. generalize dependent M1. intros M' HMI.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1874276) with (Z_to_bv 64 0x1c9964) by reflexivity.
  pose proof (MI_ic _ HMI) as (Hini & _).
  eapply (inited_cps rom Post M'); [exact Hini | reflexivity |].
  intros l1 Hl1 Hse1 H10'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1757560) 0) with (Z_to_bv 64 0x1ad178) by reflexivity.
  regs_open l1 Hl1. se_subst Hse1. clear Hse1. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  wp_icm [0x1ad20c]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1878132) with (Z_to_bv 64 0x1ca874) by reflexivity.
  eapply (tryinit_cps rom Post M' (S - 2176)); [exact Hini | unfold A_IMG_END; lia
    | eapply wr_ok_sub; [apply (MI_wr _ _ _ HMI Hfr) | lia | lia] | reflexivity | reflexivity |].
  intros l2 M2 Hl2 Hse2 H10'' HU2 HG2. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1757568) 0) with (Z_to_bv 64 0x1ad180) by reflexivity.
  regs_open l2 Hl2. se_subst Hse2. clear Hse2. cbn [rget lget] in H10''. match type of H10'' with ?x = _ => subst x end.
  assert (HMI2 : MI M2).
  { eapply MI_step; [exact HMI | exact HU2 | exact HG2 |]. intros x Hx. unfold FPlow, inr in *. lia. }
  clear HMI Hini HU2 HG2.
  wp_icm [0x1ad258; 0x1ad2ac; 0x1ad18c]. change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  eapply (cmp_loop (Z.to_nat (n - 0)) 0); [lia | lia | intros j Hj; lia | exact HMI2 | prove_stable Hse | reflexivity].
Qed.

End IcStrncmp.

(* [comment removed for export] *)
Theorem istrncmp_cps : forall rom Post M p N B k z q n RB S l,
  rt_ok M -> ic_ok M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= z -> z < N ->
  bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) ->
  0 < n <= 64 -> 0 < q /\ q + n < 2 ^ 63 ->
  (forall i, 0 <= i < n -> load_ok ASEGS M (W (q + i)) 1 (W (bv_unsigned (RB i)))) ->
  (forall i, 0 <= i < n -> bv_unsigned (RB i) <> 0) ->
  memrange (p + k) (Z.min (z - k + 1) n) -> addr_ok M (p + k) (Z.min (z - k + 1) n) -> shw_ok M (p + k) (Z.min (z - k + 1) n) ->
  memrange q n -> addr_ok M q n -> shw_ok M q n ->
  A_IMG_END <= S - 2256 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2256) -> wr_ok ASEGS M (S - 2256) 2256 ->
  (p + N <= S - 2256 \/ S <= p) -> (q + n <= S - 2256 \/ S <= q) ->
  length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) -> rget l 11 = W q -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
     (bv_unsigned (rget l' 10) = 0 -> forall i, 0 <= i < n -> B (k + i) = RB i) ->
     unch M M' (FP S) -> mem_grows M M' ->
     reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach ASEGS rom (Z_to_bv 64 0x1ad124) l M Post.
Proof.
  intros rom Post M p N B k z q n RB S l; intros.
  eapply (ic_body rom Post M p N B k z q n RB S) with (l0 := l); eauto.
Qed.

(* [comment removed for export] *)
Theorem istrncmp_stub_cps : forall rom Post M p N B k z q n RB S l,
  rt_ok M -> ic_ok M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= z -> z < N ->
  bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) ->
  0 < n <= 64 -> 0 < q /\ q + n < 2 ^ 63 ->
  (forall i, 0 <= i < n -> load_ok ASEGS M (W (q + i)) 1 (W (bv_unsigned (RB i)))) ->
  (forall i, 0 <= i < n -> bv_unsigned (RB i) <> 0) ->
  memrange (p + k) (Z.min (z - k + 1) n) -> addr_ok M (p + k) (Z.min (z - k + 1) n) -> shw_ok M (p + k) (Z.min (z - k + 1) n) ->
  memrange q n -> addr_ok M q n -> shw_ok M q n ->
  A_IMG_END <= S - 2256 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2256) -> wr_ok ASEGS M (S - 2256) 2256 ->
  (p + N <= S - 2256 \/ S <= p) -> (q + n <= S - 2256 \/ S <= q) ->
  length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) -> rget l 11 = W q -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
     (bv_unsigned (rget l' 10) = 0 -> forall i, 0 <= i < n -> B (k + i) = RB i) ->
     unch M M' (FP S) -> mem_grows M M' ->
     reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach ASEGS rom (Z_to_bv 64 0x1ac5d0) l M Post.
Proof.
  intros rom Post M p N B k z q n RB S l Hrt Hic HB Hp Hk Hz HBz HBnz Hn Hq HRB HRBnz Hm1 Ho1 Hs1 Hm2 Ho2 Hs2 HS HSz Hfr
         Hdj Hdjq Hl H2 H10 H11 H12 K.
  pose proof Hl as Hl'. regs_open l Hl'.
  wp_go 0x1ac5c4 36%nat C_stubs_eq C_stubs (@nil Z).
  replace (Z_to_bv 64 1757476) with (Z_to_bv 64 0x1ad124) by reflexivity.
  eapply (istrncmp_cps rom Post M p N B k z q n RB S); try eassumption; try reflexivity.
Qed.

Print Assumptions istrncmp_stub_cps.
