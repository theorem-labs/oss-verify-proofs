(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require Import PCode PMemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pkt_at (M : mem) (pk out wr mx sb : Z) (eb : word) : Prop :=
  cell PSEGS M pk 8 (W 0) /\ cell PSEGS M (pk + 8) 8 (W out) /\ cell PSEGS M (pk + 16) 8 (W wr)
  /\ cell PSEGS M (pk + 24) 8 (W wr) /\ cell PSEGS M (pk + 32) 8 (W mx) /\ cell PSEGS M (pk + 40) 8 (W sb)
  /\ cell PSEGS M (pk + 48) 1 eb.

Definition pkt_wf (pk out wr mx sb : Z) (eb : word) : Prop :=
  0 <= pk /\ pk + 56 < 2 ^ 63 /\ 0 < out /\ out + mx < 2 ^ 63 /\ 0 <= wr <= mx /\ 0 < sb < 2 ^ 64
  /\ (bv_unsigned eb mod 2 ^ 8) mod 2 = 0.

Ltac wp_gc stops := wp_go 0x119eb4 26%nat C_wp_get_curr_eq C_wp_get_curr stops.

(* [comment removed for export] *)
Section GetCurr.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 16 <= spv /\ spv <= pk.
Hypothesis Hfr : wr_ok PSEGS M (spv - 16) 16.

Definition KS_gc : list nat := [10; 11; 12]%nat.
Definition FR_gc (x : word) : Prop := inr x (spv - 16) 16.

Lemma get_curr_cps : forall l, length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W pk ->
  (forall l' M', length l' = 32%nat -> same_except KS_gc l l' -> rget l' 10 = W (out + wr) ->
                 unch M M' FR_gc -> mem_grows M M' ->
                 reach PSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x119eb4) l M Post.
Proof.
  intros l Hl H2 H10 K. destruct HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  destruct HW as (Hpk & Hpk2 & Hout & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0.
  wp_gc (@nil Z). mem_auto. rewrite Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb. mem_auto.
  assert (Hbit : bv_unsigned (v_andi (W (bv_unsigned eb mod 2 ^ (8 * Z.of_nat 1))) 1) = 0).
  { change 1 with (Z.ones 1). rewrite u_andi_ones by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned eb) (2 ^ 8) ltac:(lia)).
    rewrite Wu by (change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8); lia). exact Heb. }
  split; intros Hb; [exfalso; apply Hb; exact Hbit|]. clear Hb. mem_auto.
  rewrite ?add_W.
  replace (v_jalr ra 0) with (v_jalr (rget [x0; ra; Z_to_bv 64 spv; gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 pk; a1; a2; a3; a4;
       a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] 1) 0) by reflexivity.
  apply K; [reflexivity | | reflexivity | | solve_grows].
  - intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail | cbn [rget lget]; f_equal; lia]|]).
    rewrite !rget_beyond by (cbn [length]; lia). reflexivity.
  - solve_unch ltac:(unfold FR_gc, inr in *; lia).
Qed.
End GetCurr.

(* [comment removed for export] *)
Lemma pkt_at_unch : forall M M' (P : word -> Prop) pk out wr mx sb eb,
  unch M M' P -> 0 <= pk -> pk + 56 < 2 ^ 63 -> (forall x, inr x pk 56 -> ~ P x) ->
  pkt_at M pk out wr mx sb eb -> pkt_at M' pk out wr mx sb eb.
Proof.
  intros M M' P pk out wr mx sb eb HU Hpk Hpk2 HP (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  unfold pkt_at; repeat split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
    intros x Hx; apply HP; unfold inr in *; cbn in Hx; lia.
Qed.

Ltac wp_rb stops := wp_go 0x119d64 57%nat C_wp_reserve_eq C_wp_reserve stops.

(* [comment removed for export] *)
Section Reserve.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv len ab : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 64 <= spv /\ spv <= pk /\ spv <= ab.
Hypothesis Hfr : wr_ok PSEGS M (spv - 64) 64.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hab : 0 < ab /\ ab + 8 < 2 ^ 63 /\ (ab + 8 <= pk \/ pk + 56 <= ab).
Hypothesis Hwab : wr_ok PSEGS M ab 8.

Definition KS_rb : list nat := [10; 11; 12]%nat.
Definition FR_rb (x : word) : Prop := inr x (spv - 64) 64 \/ inr x ab 8.
Definition rb_ok : Prop := len <> 0 /\ len <= mx - wr.

Lemma reserve_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = W len -> rget l 12 = W ab ->
  (forall l' M', length l' = 32%nat -> same_except KS_rb l l' ->
                 (rb_ok -> rget l' 10 = W 1 /\ cell PSEGS M' ab 8 (W (out + wr))) ->
                 (~ rb_ok -> rget l' 10 = W 0) ->
                 pkt_at M' pk out wr mx sb eb ->
                 unch M M' FR_rb -> mem_grows M M' ->
                 reach PSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x119d64) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hout & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_rb [0x119dc0]. mem_auto. name_mem M1. rewrite Wu by lia.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_rb) by (unname_mems; solve_unch ltac:(unfold FR_rb, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  split; intros Hb.
  - (* [comment removed for export] *) mem_auto.
    apply K; [reflexivity | same_ex_lia | intros [H0 _]; exfalso; lia | reflexivity | exact HP1 | exact HU1 | exact HG1].
  - mem_auto. rewrite Wu by lia. split; intros Hb2; [exfalso; lia|]. clear Hb2. mem_auto.
    rewrite ?sub_W. rewrite !Wu by lia. split; intros Hb2.
    + (* [comment removed for export] *) mem_auto. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      split; intros Hb3; [clear Hb3 | exfalso; lia].
      split; intros Hb3; [exfalso; lia|]. clear Hb3.
      eapply (get_curr_cps rom Post M1 pk out wr mx sb (spv - 48) eb HP1 HW);
        [ lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia]
        | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity |].
      intros l' M' Hl' Hse' H10' HU' HG'. cbn [rget lget].
      replace (v_jalr (Z_to_bv 64 1154568) 0) with (Z_to_bv 64 0x119e08) by reflexivity.
      regs_open l' Hl'. se_subst Hse'. clear Hse'. subst.
      assert (HP' : pkt_at M' pk out wr mx sb eb).
      { eapply pkt_at_unch; [exact HU' | lia | lia | | exact HP1]. intros x Hx. unfold FR_gc, inr in *. lia. }
      destruct HP' as (C0' & C8' & C16' & C24' & C32' & C40' & C48').
      assert (Hw' : wr_ok PSEGS M' ab 8) by (eapply wr_ok_grows; [exact HG' | eapply wr_ok_grows; [exact HG1 | exact Hwab]]).
      assert (HU1' : unch M M' FR_rb).
      { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_gc, FR_rb, inr in *. lia. }
      assert (Cra : cell PSEGS M' (spv + -48 + 40) 8 ra).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs0 : cell PSEGS M' (spv + -48 + 32) 8 s0).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs1 : cell PSEGS M' (spv + -48 + 24) 8 s1).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs2 : cell PSEGS M' (spv + -48 + 16) 8 s2).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs3 : cell PSEGS M' (spv + -48 + 8) 8 s3).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs4 : cell PSEGS M' (spv + -48) 8 s4).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      clearbody M1.
      wp_rb (@nil Z). mem_auto.
      assert (Hbit : bv_unsigned (v_andi (W (bv_unsigned eb mod 2 ^ (8 * Z.of_nat 1))) 1) = 0).
      { change 1 with (Z.ones 1). rewrite u_andi_ones by lia.
        pose proof (Z.mod_pos_bound (bv_unsigned eb) (2 ^ 8) ltac:(lia)).
        rewrite Wu by (change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8); lia). exact Heb. }
      split; intros Hb3; [clear Hb3 | exfalso; apply Hb3; exact Hbit]. mem_auto.
      apply K; [reflexivity | same_ex_lia | | | | | ].
      * intros _. split; [reflexivity | apply cell_store_same; lia].
      * intros Hn. exfalso. apply Hn. split; lia.
      * unfold pkt_at; repeat split; solve_cell.
      * solve_unch ltac:(unfold FR_rb, inr in *; lia).
      * eapply mem_grows_trans; [exact HG1|]. eapply mem_grows_trans; [exact HG'|]. solve_grows.
    + (* [comment removed for export] *) mem_auto.
      apply K; [reflexivity | same_ex_lia | intros [_ H0]; exfalso; lia | reflexivity | exact HP1 | exact HU1 | exact HG1].
Qed.
End Reserve.

