(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ACheck ASaves.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BCode2 BRt BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sh0 (M : mem) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> M (W (sha x)) = Some (Z_to_bv 8 0).

Lemma sh0_load : forall M a n x, sh0 M a n -> a <= x < a + n -> load_ok BSEGS M (W (sha x)) 1 (W 0).
Proof. intros M a n x H Hx. exists [Z_to_bv 8 0]. split; [|reflexivity]. cbn [rdn]. rewrite (H x Hx). reflexivity. Qed.

Lemma sh0_sub : forall M a n a' n', sh0 M a n -> a <= a' -> a' + n' <= a + n -> sh0 M a' n'.
Proof. intros M a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma sh0_unch : forall M0 M (P : word -> Prop) a n,
  unch M0 M P -> 0 <= a -> a + n <= HIMEM_END -> (forall y, P y -> ~ (SB <= bv_unsigned y < HIMEM_BEG)) ->
  sh0 M0 a n -> sh0 M a n.
Proof.
  intros M0 M P a n HU Ha Hn HP H x Hx. rewrite HU; [apply H, Hx|]. intros HPy. apply (HP _ HPy).
  pose proof (sha_range x ltac:(lia)) as Hr. unfold SB, HIMEM_BEG in *. rewrite Wu by lia. exact Hr.
Qed.

Lemma sh0_addr_ok : forall M a n, sh0 M a n -> addr_ok M a n.
Proof. intros M a n H x Hx. exists (Z_to_bv 8 0). split; [apply H, Hx | left; reflexivity]. Qed.

(* [comment removed for export] *)
Definition pkt_at (M : mem) (pk out wr mx sb : Z) (eb : word) : Prop :=
  cell BSEGS M pk 8 (W 0) /\ cell BSEGS M (pk + 8) 8 (W out) /\ cell BSEGS M (pk + 16) 8 (W wr)
  /\ cell BSEGS M (pk + 24) 8 (W wr) /\ cell BSEGS M (pk + 32) 8 (W mx) /\ cell BSEGS M (pk + 40) 8 (W sb)
  /\ cell BSEGS M (pk + 48) 1 eb.

Definition pkt_wf (pk out wr mx sb : Z) (eb : word) : Prop :=
  B_IMG_END <= pk /\ memrange pk 56 /\ 0 < out /\ out + mx < 2 ^ 63 /\ 0 <= wr <= mx /\ 0 < sb < 2 ^ 64
  /\ (bv_unsigned eb mod 2 ^ 8) mod 2 = 0.

(* [comment removed for export] *)
Lemma pkt_at_unch : forall M M' (P : word -> Prop) pk out wr mx sb eb,
  unch M M' P -> 0 <= pk -> pk + 56 < 2 ^ 63 -> (forall x, inr x pk 56 -> ~ P x) ->
  pkt_at M pk out wr mx sb eb -> pkt_at M' pk out wr mx sb eb.
Proof.
  intros M M' P pk out wr mx sb eb HU Hpk Hpk2 HP (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  unfold pkt_at; repeat split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
    intros x Hx; apply HP; unfold inr in *; cbn in Hx; lia.
Qed.

(* [comment removed for export] *)
Ltac chk0 Hsh :=
  rewrite ?addi_W; rewrite sha_addr_r by lia;
  exists (W 0); split; [eapply (sh0_load _ _ _ _ Hsh); lia|];
  rewrite ?(lb_small 0) by lia; change (bv_unsigned (Z_to_bv 64 0)) with 0;
  split; [let Hb := fresh "Hb" in intros Hb; exfalso; apply Hb; reflexivity | intros _].

Ltac wp_gc stops := wp_go 0x2723cc 87%nat C_wp_get_curr_eq C_wp_get_curr stops.

(* [comment removed for export] *)
Section GetCurr.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv : Z) (eb : word).
Hypothesis Hrt : rt_ok M.
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hpk8 : pk mod 8 = 0.
Hypothesis Hsh : sh0 M pk 56.
Hypothesis Hsp : B_IMG_END <= spv - 16 /\ spv < 2 ^ 63 /\ (spv <= SB \/ HIMEM_BEG <= spv - 16)
                 /\ (pk + 56 <= spv - 16 \/ spv <= pk).
Hypothesis Hfr : wr_ok BSEGS M (spv - 16) 16.

Definition KS_gc : list nat := [10; 11; 12; 13; 14; 15]%nat.
Definition FR_gc (x : word) : Prop := inr x (spv - 16) 16.

Lemma get_curr_cps : forall l, length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W pk ->
  (forall l' M', length l' = 32%nat -> same_except KS_gc l l' -> rget l' 10 = W (out + wr) ->
                 unch M M' FR_gc -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x2723cc) l M Post.
Proof.
  intros l Hl H2 H10 K. destruct HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  destruct HW as (Hpk0 & Hmr & Hout & Hout2 & Hwr & Hsb & Heb).
  destruct Hrt as (G1 & G2 & _). destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4).
  assert (Hpk : 0 <= pk /\ pk + 64 <= HIMEM_END) by (destruct Hmr as [_ Hm]; unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *; lia).
  unfold G_SB, C_SB, B_IMG_END, HIMEM_END in *.
  regs_open l Hl. subst sp a0.
  wp_gc [0x2724f0; 0x272504; 0x2724a0; 0x2724f4; 0x272458; 0x27250c]. mem_auto.
  name_mem M1.
  assert (HU1 : unch M M1 FR_gc) by (unname_mems; solve_unch ltac:(unfold FR_gc, inr in *; lia)).
  assert (Hsh1 : sh0 M1 pk 56).
  { eapply sh0_unch; [exact HU1 | lia | unfold HIMEM_END; lia | | exact Hsh].
    intros y Hy. unfold FR_gc, inr, SB, HIMEM_BEG in *. lia. }
  rewrite (Wu pk) by lia. split; intros Hb; [exfalso; lia|]. clear Hb.
  rewrite (andi7_W pk) by lia. rewrite Hpk8. change (bv_unsigned (W 0)) with 0.
  split; intros Hb; [exfalso; apply Hb; reflexivity|]. clear Hb.
  mem_auto. chk0 Hsh1. mem_auto. rewrite Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  chk0 Hsh1. mem_auto.
  assert (Hbit : bv_unsigned (v_andi (W (bv_unsigned eb mod 2 ^ (8 * Z.of_nat 1))) 1) = 0).
  { change 1 with (Z.ones 1). rewrite u_andi_ones by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned eb) (2 ^ 8) ltac:(lia)).
    rewrite Wu by (change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8); lia). exact Heb. }
  split; intros Hb; [exfalso; apply Hb; exact Hbit|]. clear Hb.
  chk0 Hsh1. mem_auto.
  rewrite (u_not_W out) by lia. rewrite (Wu wr) by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  mem_auto. rewrite ?add_W.
  match goal with |- reach _ _ (v_jalr ?r 0) ?l' _ _ =>
    replace (v_jalr r 0) with (v_jalr (rget [x0; ra; Z_to_bv 64 spv; gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 pk; a1; a2; a3; a4;
       a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] 1) 0) by reflexivity end.
  apply K; [reflexivity | | reflexivity | exact HU1 | unname_mems; solve_grows].
  intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail | cbn [rget lget]; f_equal; lia]|]).
  rewrite !rget_beyond by (cbn [length]; lia). reflexivity.
Qed.
End GetCurr.

Ltac wp_rb stops := wp_go 0x272128 120%nat C_wp_reserve_eq C_wp_reserve stops.

(* [comment removed for export] *)
Definition KS_rb : list nat := [10; 11; 12; 13; 14; 15]%nat.
Definition KSI_rb : list nat := [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20; 21]%nat.
Definition FR_rb (spv ab : Z) (x : word) : Prop := inr x (spv - 80) 80 \/ inr x ab 8.
Definition rb_ok (wr mx len : Z) : Prop := len <> 0 /\ len <= mx - wr.
Definition RB_SLOTS : list (nat * Z) :=
  [(1%nat, 56); (8%nat, 48); (9%nat, 40); (18%nat, 32); (19%nat, 24); (20%nat, 16); (21%nat, 8)].

Section Reserve.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv len ab : Z) (eb : word).
Hypothesis Hrt : rt_ok M.
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hpk8 : pk mod 8 = 0.
Hypothesis Hsh : sh0 M pk 56.
Hypothesis Hsp : B_IMG_END <= spv - 80 /\ spv < 2 ^ 63 /\ (spv <= SB \/ HIMEM_BEG <= spv - 80)
                 /\ (pk + 56 <= spv - 80 \/ spv <= pk) /\ (ab + 8 <= spv - 80 \/ spv <= ab).
Hypothesis Hfr : wr_ok BSEGS M (spv - 80) 80.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hab : B_IMG_END <= ab /\ memrange ab 8 /\ (ab + 8 <= pk \/ pk + 56 <= ab) /\ ab mod 8 = 0.
Hypothesis Hshab : sh0 M ab 8.
Hypothesis Hwab : wr_ok BSEGS M ab 8.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W spv.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS_rb l0 l' ->
  (rb_ok wr mx len -> rget l' 10 = W 1 /\ cell BSEGS M' ab 8 (W (out + wr))) ->
  (~ rb_ok wr mx len -> rget l' 10 = W 0) ->
  pkt_at M' pk out wr mx sb eb ->
  unch M M' (FR_rb spv ab) -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition saved (M2 : mem) : Prop :=
  forall k off, In (k, off) RB_SLOTS -> cell BSEGS M2 (spv + -64 + off) 8 (rget l0 k).

Lemma rb_bounds : 0 <= pk /\ pk + 64 <= HIMEM_END /\ 0 <= ab /\ ab + 16 <= HIMEM_END.
Proof.
  destruct HW as (_ & [_ Hm] & _). destruct Hab as (_ & [_ Hm2] & _).
  unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia.
Qed.

Lemma rb_nosh : forall y, FR_rb spv ab y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof.
  intros y Hy. destruct Hab as (_ & [_ Hm] & _). destruct Hsp as (Hs1 & Hs2 & Hs3 & _).
  unfold FR_rb, inr, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rb_exit : forall l2 M2 r, length l2 = 32%nat -> same_except KSI_rb l0 l2 ->
  rget l2 2 = W (spv + -64) -> rget l2 20 = W r -> saved M2 ->
  (rb_ok wr mx len -> r = 1 /\ cell BSEGS M2 ab 8 (W (out + wr))) -> (~ rb_ok wr mx len -> r = 0) ->
  pkt_at M2 pk out wr mx sb eb -> unch M M2 (FR_rb spv ab) -> mem_grows M M2 ->
  reach BSEGS rom (Z_to_bv 64 0x2722a0) l2 M2 Post.
Proof.
  intros l2 M2 r Hl Hse H2 H20 Hsv Hok Hno HP2 HU2 HG2.
  pose proof (Hsv 1%nat 56 ltac:(unfold RB_SLOTS; in_list)) as Csv1. pose proof (Hsv 8%nat 48 ltac:(unfold RB_SLOTS; in_list)) as Csv8.
  pose proof (Hsv 9%nat 40 ltac:(unfold RB_SLOTS; in_list)) as Csv9. pose proof (Hsv 18%nat 32 ltac:(unfold RB_SLOTS; in_list)) as Csv18.
  pose proof (Hsv 19%nat 24 ltac:(unfold RB_SLOTS; in_list)) as Csv19. pose proof (Hsv 20%nat 16 ltac:(unfold RB_SLOTS; in_list)) as Csv20.
  pose proof (Hsv 21%nat 8 ltac:(unfold RB_SLOTS; in_list)) as Csv21. clear Hsv.
  destruct Hsp as (Hs1 & Hs2 & _). unfold B_IMG_END in *.
  regs_open l2 Hl. subst sp s4.
  wp_rb (@nil Z). mem_auto.
  apply K; [reflexivity | | | | exact HP2 | exact HU2 | exact HG2].
  - same_fix Hse. rewrite H0sp. f_equal. lia.
  - intros Hy. destruct (Hok Hy) as [-> Hc]. split; [reflexivity | exact Hc].
  - intros Hn. rewrite (Hno Hn). reflexivity.
Qed.

(* [comment removed for export] *)
Definition RI (M2 : mem) : Prop :=
  saved M2 /\ pkt_at M2 pk out wr mx sb eb /\ unch M M2 (FR_rb spv ab) /\ mem_grows M M2.

Lemma RI_sh : forall M2, RI M2 -> sh0 M2 pk 56 /\ sh0 M2 ab 8 /\ rt_ok M2.
Proof.
  intros M2 (_ & _ & HU & _). pose proof rb_bounds as (B1 & B2 & B3 & B4). pose proof rb_nosh as Hn.
  split; [|split].
  - eapply sh0_unch; [exact HU | lia | lia | exact Hn | exact Hsh].
  - eapply sh0_unch; [exact HU | lia | lia | exact Hn | exact Hshab].
  - eapply rt_ok_unch; [exact HU | | exact Hrt]. intros y Hy. destruct Hsp as (Hs1 & _). destruct Hab as (Ha1 & _).
    unfold FR_rb, inr, B_IMG_END in *. lia.
Qed.

Ltac exit0 Hse Hsv HP2 HU2 HG2 :=
  eapply (rb_exit _ _ 0); [reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity | reflexivity
    | exact Hsv | | intros _; reflexivity | exact HP2 | exact HU2 | exact HG2].

(* [comment removed for export] *)
Lemma rb_tail : forall l2 M2, RI M2 -> length l2 = 32%nat -> same_except KSI_rb l0 l2 ->
  rget l2 2 = W (spv + -64) -> rget l2 9 = W ab -> rget l2 19 = W pk -> rget l2 20 = W 1 -> rget l2 21 = W SB ->
  rget l2 10 = W (out + wr) -> rb_ok wr mx len ->
  reach BSEGS rom (Z_to_bv 64 0x27224c) l2 M2 Post.
Proof.
  intros l2 M2 HRI Hl Hse H2 H9 H19 H20 H21 H10 Hrb.
  destruct (RI_sh _ HRI) as (Hsh2 & Hshab2 & _). pose proof HRI as (Hsv & HP2 & HU2 & HG2).
  pose proof HP2 as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk0 & Hmr & Hout & Hout2 & Hwr & Hsb & Heb).
  pose proof rb_bounds as (B1 & B2 & B3 & B4). destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5).
  destruct Hab as (Hab0 & Hmab & Hab1 & Hab8).
  assert (Hwab2 : wr_ok BSEGS M2 ab 8) by (eapply wr_ok_grows; [exact HG2 | exact Hwab]).
  unfold B_IMG_END, HIMEM_END in *.
  regs_open l2 Hl. subst sp s1 s3 s4 s5 a0.
  wp_rb [0x2722a0; 0x2722c8; 0x2722f8; 0x2722cc; 0x272288].
  rewrite (andi7_W ab) by lia. rewrite Hab8. change (bv_unsigned (W 0)) with 0.
  split; intros Hb; [exfalso; apply Hb; reflexivity|]. clear Hb.
  chk0 Hshab2.
  split; [eapply wr_ok_store; [exact Hwab2 | lia | lia]|].
  name_mem M3.
  assert (HU3 : unch M2 M3 (fun x => inr x ab 8)).
  { unname_mems. apply unch_store; [apply unch_refl | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. exact Hx. }
  assert (Cab : cell BSEGS M3 ab 8 (W (out + wr))) by (unname_mems; apply cell_store_same; lia).
  assert (HG3 : mem_grows M2 M3) by (unname_mems; apply wbytes_grows).
  clearbody M3.
  assert (HRI3 : RI M3).
  { split; [|split; [|split]].
    - intros k off Hin. eapply cell_unch; [exact HU3 | | | | apply Hsv; exact Hin];
        unfold RB_SLOTS in Hin; cbn [In] in Hin;
        repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
        try lia; intros x Hx; unfold inr in *; cbn in Hx; lia.
    - eapply pkt_at_unch; [exact HU3 | lia | lia | | exact HP2]. intros x Hx. unfold inr in *. lia.
    - eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU3|]. intros x Hx. right. exact Hx.
    - eapply mem_grows_trans; eassumption. }
  destruct (RI_sh _ HRI3) as (Hsh3 & _ & _). destruct HRI3 as (Hsv3 & HP3 & HU3' & HG3').
  pose proof HP3 as (_ & _ & _ & _ & _ & _ & C48').
  chk0 Hsh3. mem_auto.
  assert (Hbit : bv_unsigned (v_andi (W (bv_unsigned eb mod 2 ^ (8 * Z.of_nat 1))) 1) = 0).
  { change 1 with (Z.ones 1). rewrite u_andi_ones by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned eb) (2 ^ 8) ltac:(lia)).
    rewrite Wu by (change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8); lia). exact Heb. }
  split; intros Hb; [clear Hb | exfalso; apply Hb; exact Hbit].
  eapply (rb_exit _ _ 1); [reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity | reflexivity
    | exact Hsv3 | intros _; split; [reflexivity | exact Cab] | intros Hn; exfalso; apply Hn; exact Hrb
    | exact HP3 | exact HU3' | exact HG3'].
Qed.

(* [comment removed for export] *)
Lemma rb_main : forall l2 M2, RI M2 -> length l2 = 32%nat -> same_except KSI_rb l0 l2 ->
  rget l2 2 = W (spv + -64) -> rget l2 10 = W pk -> rget l2 11 = W len -> rget l2 12 = W ab ->
  reach BSEGS rom (Z_to_bv 64 0x272148) l2 M2 Post.
Proof.
  intros l2 M2 HRI Hl Hse H2 H10 H11 H12.
  destruct (RI_sh _ HRI) as (Hsh2 & Hshab2 & Hrt2). pose proof HRI as (Hsv & HP2 & HU2 & HG2).
  pose proof HP2 as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk0 & Hmr & Hout & Hout2 & Hwr & Hsb & Heb).
  pose proof Hrt2 as (G1 & G2 & _).
  pose proof rb_bounds as (B1 & B2 & B3 & B4). destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5).
  destruct Hab as (Hab0 & Hmab & Hab1 & Hab8).
  unfold G_SB, C_SB, B_IMG_END, HIMEM_END in *.
  regs_open l2 Hl. subst sp a0 a1 a2.
  wp_rb [0x2722a0; 0x2722c8; 0x2722dc; 0x2722e0; 0x2722e4; 0x2722ec; 0x2721ec].
  rewrite (Wu pk) by lia. split; intros Hb; [exfalso; lia|]. clear Hb.
  rewrite (andi7_W pk) by lia. rewrite Hpk8. change (bv_unsigned (W 0)) with 0.
  split; intros Hb; [exfalso; apply Hb; reflexivity|]. clear Hb.
  mem_auto. chk0 Hsh2. rewrite Wu by lia.
  split; intros Hb.
  { exit0 Hse Hsv HP2 HU2 HG2. intros [Hy _]. exfalso. lia. }
  mem_auto. rewrite Wu by lia. split; intros Hb2; [exfalso; lia|]. clear Hb2.
  chk0 Hsh2. chk0 Hsh2. mem_auto. rewrite ?sub_W. rewrite !Wu by lia.
  split; intros Hb2.
  - chk0 Hsh2. mem_auto. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    split; intros Hb3; [clear Hb3 | exfalso; apply Hb3; reflexivity].
    rewrite ?Wu by lia. split; intros Hb3; [exfalso; lia|]. clear Hb3.
    eapply (get_curr_cps rom Post M2 pk out wr mx sb (spv - 64) eb Hrt2 HP2 HW Hpk8 Hsh2);
      [ unfold B_IMG_END, SB, HIMEM_BEG in *; lia
      | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG2 | exact Hfr] | lia | lia]
      | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity |].
    intros l' M' Hl' Hse' H10' HU' HG'. cbn [rget lget].
    match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ =>
      replace (v_jalr (Z_to_bv 64 x) 0) with (Z_to_bv 64 0x27224c) by reflexivity end.
    assert (HRI' : RI M').
    { split; [|split; [|split]].
      - intros k off Hin. eapply cell_unch; [exact HU' | | | | apply Hsv; exact Hin];
          unfold RB_SLOTS in Hin; cbn [In] in Hin;
          repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
          try lia; intros x Hx; unfold FR_gc, inr in *; cbn in Hx; lia.
      - eapply pkt_at_unch; [exact HU' | lia | lia | | exact HP2]. intros x Hx. unfold FR_gc, inr in *. lia.
      - eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU'|].
        intros x Hx. unfold FR_gc, FR_rb, inr in *. lia.
      - eapply mem_grows_trans; eassumption. }
    regs_open l' Hl'. se_subst Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
    apply rb_tail; [exact HRI' | reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                   | reflexivity | split; lia].
    eapply same_except_call; [ | exact Hse' | ]; [eapply same_except_trans; [exact Hse | same_ex] |].
    unfold KS_gc, KSI_rb. subset_tac.
  - exit0 Hse Hsv HP2 HU2 HG2. intros [_ Hy]. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma reserve_body : forall l, l = l0 -> rget l 10 = W pk -> rget l 11 = W len -> rget l 12 = W ab ->
  reach BSEGS rom (Z_to_bv 64 0x272128) l M Post.
Proof.
  intros l El H10 H11 H12.
  assert (Hl : length l = 32%nat) by (rewrite El; exact Hl0).
  assert (Hse0 : same_except [] l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. clear El.
  destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5). destruct Hab as (Hab0 & Hmab & Hab1 & Hab8).
  pose proof HW as (Hpk0 & Hmr & _). pose proof rb_bounds as (B1 & B2 & B3 & B4).
  unfold B_IMG_END, HIMEM_END in *.
  regs_open l Hl. subst sp a0 a1 a2. se_subst Hse0.
  wp_rb [0x272148]. mem_auto.
  pose (SL := [(56, rget l0 1); (48, rget l0 8); (40, rget l0 9); (32, rget l0 18); (24, rget l0 19);
               (16, rget l0 20); (8, rget l0 21)]).
  match goal with |- reach _ _ _ _ ?Mx _ => change Mx with (saves M (spv + -64) SL) end.
  assert (Hok : slots_ok 64 SL = true) by reflexivity.
  assert (HRI : RI (saves M (spv + -64) SL)).
  { split; [|split; [|split]].
    - intros k off Hin. unfold RB_SLOTS in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin];
              [injection Hin as <- <-; apply (saves_cell BSEGS SL M (spv + -64) 64); [lia | lia | exact Hok | unfold SL; in_list]|]).
      contradiction.
    - destruct HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
      unfold pkt_at; repeat split; (apply (saves_cell_out BSEGS SL _ (spv + -64) 64); [lia | lia | exact Hok | lia | (cbn; lia) | (cbn; lia) | assumption]).
    - apply (saves_unch SL M M (spv + -64) 64); [lia | lia | exact Hok | | apply unch_refl].
      intros x Hx. unfold FR_rb, inr in *. lia.
    - apply saves_grows. }
  set (M1 := saves M (spv + -64) SL) in *. clearbody M1. clear Hok. clearbody SL.
  apply rb_main; [exact HRI | reflexivity | | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | reflexivity].
  intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail]|]).
  rewrite !rget_beyond by (cbn [length]; rewrite ?Hl0; lia). reflexivity.
Qed.

End Reserve.

Theorem reserve_cps : forall rom Post M pk out wr mx sb spv len ab eb l,
  rt_ok M -> pkt_at M pk out wr mx sb eb -> pkt_wf pk out wr mx sb eb -> pk mod 8 = 0 -> sh0 M pk 56 ->
  B_IMG_END <= spv - 80 /\ spv < 2 ^ 63 /\ (spv <= SB \/ HIMEM_BEG <= spv - 80)
    /\ (pk + 56 <= spv - 80 \/ spv <= pk) /\ (ab + 8 <= spv - 80 \/ spv <= ab) ->
  wr_ok BSEGS M (spv - 80) 80 -> 0 <= len < 2 ^ 62 ->
  B_IMG_END <= ab /\ memrange ab 8 /\ (ab + 8 <= pk \/ pk + 56 <= ab) /\ ab mod 8 = 0 -> sh0 M ab 8 -> wr_ok BSEGS M ab 8 ->
  length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W pk -> rget l 11 = W len -> rget l 12 = W ab ->
  (forall l' M', length l' = 32%nat -> same_except KS_rb l l' ->
     (rb_ok wr mx len -> rget l' 10 = W 1 /\ cell BSEGS M' ab 8 (W (out + wr))) ->
     (~ rb_ok wr mx len -> rget l' 10 = W 0) ->
     pkt_at M' pk out wr mx sb eb ->
     unch M M' (FR_rb spv ab) -> mem_grows M M' ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x272128) l M Post.
Proof.
  intros rom Post M pk out wr mx sb spv len ab eb l; intros.
  eapply (reserve_body rom Post M pk out wr mx sb spv len ab eb) with (l0 := l); eauto.
Qed.

Ltac wp_al stops := wp_go 0x272074 45%nat C_wp_alloc_eq C_wp_alloc stops.

(* [comment removed for export] *)
Definition KS_al : list nat := [10; 11; 12; 13; 14; 15]%nat.
Definition FR_al (spv ab pk : Z) (x : word) : Prop := inr x (spv - 128) 128 \/ inr x ab 8 \/ inr x (pk + 16) 16.

Section Alloc.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv len ab : Z) (eb : word).
Hypothesis Hrt : rt_ok M.
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hpk8 : pk mod 8 = 0.
Hypothesis Hsh : sh0 M pk 56.
Hypothesis Hsp : B_IMG_END <= spv - 128 /\ spv < 2 ^ 63 /\ (spv <= SB \/ HIMEM_BEG <= spv - 128)
                 /\ (pk + 56 <= spv - 128 \/ spv <= pk) /\ (ab + 8 <= spv - 128 \/ spv <= ab).
Hypothesis Hfr : wr_ok BSEGS M (spv - 128) 128.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hab : B_IMG_END <= ab /\ memrange ab 8 /\ (ab + 8 <= pk \/ pk + 56 <= ab) /\ ab mod 8 = 0.
Hypothesis Hshab : sh0 M ab 8.
Hypothesis Hwab : wr_ok BSEGS M ab 8.
Hypothesis Hwpk : wr_ok BSEGS M (pk + 16) 16.

Lemma alloc_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = W len -> rget l 12 = W ab ->
  (forall l' M' wr', length l' = 32%nat -> same_except KS_al l l' ->
                 (rb_ok wr mx len -> rget l' 10 = W 1 /\ wr' = wr + len /\ cell BSEGS M' ab 8 (W (out + wr))) ->
                 (~ rb_ok wr mx len -> rget l' 10 = W 0 /\ wr' = wr) ->
                 pkt_at M' pk out wr' mx sb eb ->
                 unch M M' (FR_al spv ab pk) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x272074) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk0 & Hmr & Hout & Hout2 & Hwr & Hsb & Heb).
  destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5). destruct Hab as (Hab0 & Hmab & Hab1 & Hab8).
  assert (Hpkb : 0 <= pk /\ pk + 64 <= HIMEM_END) by (destruct Hmr as [_ Hm]; unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *; lia).
  assert (Habb : 0 <= ab /\ ab + 16 <= HIMEM_END) by (destruct Hmab as [_ Hm]; unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *; lia).
  pose proof Hrt as (G1 & G2 & _). unfold G_SB, C_SB, B_IMG_END, HIMEM_END in *.
  regs_open l Hl. subst sp a0 a1 a2.
  wp_al [0x27211c]. mem_auto. name_mem M1.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 (FR_al spv ab pk)) by (unname_mems; solve_unch ltac:(unfold FR_al, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  assert (NS1 : forall y, FR_al spv ab pk y -> ~ (SB <= bv_unsigned y < HIMEM_BEG) /\ 12570624 <= bv_unsigned y).
  { destruct Hmab as [_ Hm]. destruct Hmr as [_ Hm2]. intros y Hy.
    unfold FR_al, inr, SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. }
  assert (Hsh1 : sh0 M1 pk 56) by (eapply sh0_unch; [exact HU1 | lia | unfold HIMEM_END; lia | intros y Hy; apply (NS1 y Hy) | exact Hsh]).
  assert (Hshab1 : sh0 M1 ab 8) by (eapply sh0_unch; [exact HU1 | lia | unfold HIMEM_END; lia | intros y Hy; apply (NS1 y Hy) | exact Hshab]).
  assert (Hrt1 : rt_ok M1) by (eapply rt_ok_unch; [exact HU1 | intros y Hy; unfold B_IMG_END; apply (NS1 y Hy) | exact Hrt]).
  eapply (reserve_cps rom Post M1 pk out wr mx sb (spv + -48) len ab eb);
    [ exact Hrt1 | exact HP1 | exact HW | exact Hpk8 | exact Hsh1
    | unfold B_IMG_END; repeat split; lia
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia] | exact Hlen
    | unfold B_IMG_END; split; [lia | split; [exact Hmab | split; [exact Hab1 | exact Hab8]]] | exact Hshab1
    | eapply wr_ok_grows; [exact HG1 | exact Hwab]
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) 0) with (Z_to_bv 64 0x2720ac) by reflexivity end.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (HU1' : unch M M' (FR_al spv ab pk)).
  { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_rb, FR_al, inr in *. lia. }
  assert (Cra : cell BSEGS M' (spv + -48 + 40) 8 ra).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs0 : cell BSEGS M' (spv + -48 + 32) 8 s0).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs1 : cell BSEGS M' (spv + -48 + 24) 8 s1).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs2 : cell BSEGS M' (spv + -48 + 16) 8 s2).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs3 : cell BSEGS M' (spv + -48 + 8) 8 s3).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (HG1' : mem_grows M M') by (eapply mem_grows_trans; eassumption).
  assert (Hwpk' : wr_ok BSEGS M' (pk + 16) 16) by (eapply wr_ok_grows; [exact HG1' | exact Hwpk]).
  assert (Hsh' : sh0 M' pk 56) by (eapply sh0_unch; [exact HU1' | lia | unfold HIMEM_END; lia | intros y Hy; apply (NS1 y Hy) | exact Hsh]).
  clearbody M1. clear C0 C8 C16 C24 C32 C40 C48 Hwpk Hfr Hwab.
  destruct HP' as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  assert (Hdec : rb_ok wr mx len \/ ~ rb_ok wr mx len) by (unfold rb_ok; lia).
  destruct Hdec as [Hy|Hn].
  - destruct (Hok Hy) as [Ea0 Cab]. match type of Ea0 with ?x = _ => subst x end. clear Hok Hno. destruct Hy as [Hln0 Hroom].
    wp_al [0x27211c; 0x272120; 0x272124]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
    split; intros Hbr; [exfalso; lia|]. clear Hbr.
    rewrite (Wu pk) by lia. split; intros Hbr; [exfalso; lia|]. clear Hbr.
    rewrite (andi7_W pk) by lia. rewrite Hpk8. change (bv_unsigned (W 0)) with 0.
    split; intros Hbr; [exfalso; apply Hbr; reflexivity|]. clear Hbr.
    chk0 Hsh'. mem_auto. rewrite ?add_W.
    match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ =>
      assert (Hsh3 : sh0 Mx pk 56) by (eapply (sh0_unch M' _ (fun x => inr x (pk + 24) 8)); [ | lia | unfold HIMEM_END; lia | | exact Hsh'];
        [apply unch_store; [apply unch_refl | lia | cbn; lia | intros x Hx; exact Hx]
        | intros y Hy; destruct Hmr as [_ Hm]; cbn in Hy; unfold inr, SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *; lia]) end.
    chk0 Hsh3. mem_auto. rewrite ?add_W. mem_auto.
    apply (K _ _ (wr + len)); [reflexivity | same_ex_lia | | | | | ].
    + intros _. split; [reflexivity|]. split; [reflexivity|]. solve_cell.
    + intros Hn. exfalso. apply Hn. split; lia.
    + unfold pkt_at; repeat split; solve_cell.
    + solve_unch ltac:(unfold FR_al, inr in *; lia).
    + eapply mem_grows_trans; [exact HG1'|]. solve_grows.
  - rewrite (Hno Hn) in *. clear Hok Hno.
    wp_al [0x27211c; 0x2720b0]. change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hbr; [clear Hbr | exfalso; lia].
    mem_auto.
    apply (K _ _ wr); [reflexivity | same_ex_lia | intros Hy; exfalso; apply Hn; exact Hy | intros _; split; reflexivity
                      | unfold pkt_at; repeat split; assumption | exact HU1' | exact HG1'].
Qed.
End Alloc.
