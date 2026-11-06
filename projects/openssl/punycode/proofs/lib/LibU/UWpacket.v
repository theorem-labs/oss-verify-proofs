(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem ULib.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require Import UCode UMemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pkt_at (M : mem) (pk out wr mx sb : Z) (eb : word) : Prop :=
  cell USEGS M pk 8 (W 0) /\ cell USEGS M (pk + 8) 8 (W out) /\ cell USEGS M (pk + 16) 8 (W wr)
  /\ cell USEGS M (pk + 24) 8 (W wr) /\ cell USEGS M (pk + 32) 8 (W mx) /\ cell USEGS M (pk + 40) 8 (W sb)
  /\ cell USEGS M (pk + 48) 1 eb.

(* [comment removed for export] *)
Definition pkt_wf (pk out wr mx sb : Z) (eb : word) : Prop :=
  0 < pk /\ pk + 56 < 2 ^ 63 /\ pk mod 8 = 0 /\ 0 < out /\ out + mx < 2 ^ 63 /\ 0 <= wr <= mx /\ 0 < sb < 2 ^ 64
  /\ (bv_unsigned eb mod 2 ^ 8) mod 2 = 0.

Lemma pkt_at_unch : forall M M' (P : word -> Prop) pk out wr mx sb eb,
  unch M M' P -> 0 <= pk -> pk + 56 < 2 ^ 63 -> (forall x, inr x pk 56 -> ~ P x) ->
  pkt_at M pk out wr mx sb eb -> pkt_at M' pk out wr mx sb eb.
Proof.
  intros M M' P pk out wr mx sb eb HU Hpk Hpk2 HP (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  unfold pkt_at; repeat split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
    intros x Hx; apply HP; unfold inr in *; cbn in Hx; lia.
Qed.

Lemma eb_bit : forall eb : word, (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 ->
  bv_unsigned (v_andi (W (bv_unsigned eb mod 2 ^ (8 * Z.of_nat 1))) 1) = 0.
Proof.
  intros eb Heb. change 1 with (Z.ones 1). rewrite u_andi_ones by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned eb) (2 ^ 8) ltac:(lia)).
  rewrite Wu by (change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8); lia). exact Heb.
Qed.

Ltac wp_gc stops := wp_go 0x128aa0 37%nat C_wp_get_curr_eq C_wp_get_curr stops.

(* [comment removed for export] *)
Section GetCurr.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 16 <= spv /\ spv <= pk.
Hypothesis Hfr : wr_ok USEGS M (spv - 16) 16.

Definition KS_gc : list nat := [10; 11; 12]%nat.
Definition FR_gc (x : word) : Prop := inr x (spv - 16) 16.

Lemma get_curr_cps : forall l, length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W pk ->
  (forall l' M', length l' = 32%nat -> same_except KS_gc l l' -> rget l' 10 = W (out + wr) ->
                 unch M M' FR_gc -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x128aa0) l M Post.
Proof.
  intros l Hl H2 H10 K. destruct HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  destruct HW as (Hpk & Hpk2 & Hpk8 & Hout & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0.
  wp_gc [0x128b30; 0x128b04; 0x128ae4]. mem_auto.
  change 7 with (Z.ones 3). rewrite u_andi_ones_W by lia. rewrite !Wu by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; change (2 ^ 3) with 8 in Hbr; lia|]. clear Hbr. mem_auto. rewrite !Wu by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr. mem_auto.
  split; intros Hbr; [exfalso; apply Hbr; apply eb_bit; exact Heb|]. clear Hbr. mem_auto.
  rewrite u_not by lia. rewrite !Wu by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr. mem_auto. rewrite ?add_W.
  apply K; [reflexivity | same_ex_lia | reflexivity | unname_mems; solve_unch ltac:(unfold FR_gc, inr in *; lia) | solve_grows].
Qed.
End GetCurr.

Ltac wp_rb stops := wp_go 0x128914 66%nat C_wp_reserve_eq C_wp_reserve stops.

(* [comment removed for export] *)
Section Reserve.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv len ab : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 64 <= spv /\ spv <= pk /\ spv <= ab.
Hypothesis Hfr : wr_ok USEGS M (spv - 64) 64.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hab : 0 < ab /\ ab + 8 < 2 ^ 63 /\ ab mod 8 = 0 /\ (ab + 8 <= pk \/ pk + 56 <= ab).
Hypothesis Hwab : wr_ok USEGS M ab 8.

Definition KS_rb : list nat := [10; 11; 12]%nat.
Definition FR_rb (x : word) : Prop := inr x (spv - 64) 64 \/ inr x ab 8.
Definition rb_ok : Prop := len <> 0 /\ len <= mx - wr.

Lemma reserve_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = W len -> rget l 12 = W ab ->
  (forall l' M', length l' = 32%nat -> same_except KS_rb l l' ->
                 (rb_ok -> rget l' 10 = W 1 /\ cell USEGS M' ab 8 (W (out + wr))) ->
                 (~ rb_ok -> rget l' 10 = W 0) ->
                 pkt_at M' pk out wr mx sb eb ->
                 unch M M' FR_rb -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x128914) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hpk8 & Hout & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_rb [0x128a18; 0x12897c; 0x1289e4]. mem_auto. name_mem M1.
  change 7 with (Z.ones 3). rewrite u_andi_ones_W by lia. rewrite !Wu by lia.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_rb) by (unname_mems; solve_unch ltac:(unfold FR_rb, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; change (2 ^ 3) with 8 in Hbr; lia|]. clear Hbr.
  split; intros Hbr.
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
      replace (v_jalr (Z_to_bv 64 1214924) 0) with (Z_to_bv 64 0x1289cc) by reflexivity.
      regs_open l' Hl'. se_subst Hse'. clear Hse'. subst.
      assert (HP' : pkt_at M' pk out wr mx sb eb).
      { eapply pkt_at_unch; [exact HU' | lia | lia | | exact HP1]. intros x Hx. unfold FR_gc, inr in *. lia. }
      destruct HP' as (C0' & C8' & C16' & C24' & C32' & C40' & C48').
      assert (Hw' : wr_ok USEGS M' ab 8) by (eapply wr_ok_grows; [exact HG' | eapply wr_ok_grows; [exact HG1 | exact Hwab]]).
      assert (HU1' : unch M M' FR_rb).
      { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_gc, FR_rb, inr in *. lia. }
      assert (Cra : cell USEGS M' (spv + -48 + 40) 8 ra).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs0 : cell USEGS M' (spv + -48 + 32) 8 s0).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs1 : cell USEGS M' (spv + -48 + 24) 8 s1).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs2 : cell USEGS M' (spv + -48 + 16) 8 s2).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs3 : cell USEGS M' (spv + -48 + 8) 8 s3).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      assert (Cs4 : cell USEGS M' (spv + -48) 8 s4).
      { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_gc, inr in *; lia | unname_mems; solve_cell]. }
      clearbody M1.
      wp_rb [0x128a18; 0x1289e4]. change 7 with (Z.ones 3). rewrite u_andi_ones_W by lia.
      split; intros Hb3; [exfalso; change (2 ^ 3) with 8 in Hb3; lia|]. clear Hb3. mem_auto.
      split; intros Hb3; [clear Hb3 | exfalso; apply Hb3; apply eb_bit; exact Heb]. mem_auto.
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

Ltac wp_al stops := wp_go 0x1288a8 27%nat C_wp_alloc_eq C_wp_alloc stops.

(* [comment removed for export] *)
Section Alloc.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv len ab : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 96 <= spv /\ spv <= pk /\ spv <= ab.
Hypothesis Hfr : wr_ok USEGS M (spv - 96) 96.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hab : 0 < ab /\ ab + 8 < 2 ^ 63 /\ ab mod 8 = 0 /\ (ab + 8 <= pk \/ pk + 56 <= ab).
Hypothesis Hwab : wr_ok USEGS M ab 8.
Hypothesis Hwpk : wr_ok USEGS M (pk + 16) 16.

Definition KS_al : list nat := [10; 11; 12]%nat.
Definition FR_al (x : word) : Prop := inr x (spv - 96) 96 \/ inr x ab 8 \/ inr x (pk + 16) 16.

Lemma alloc_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = W len -> rget l 12 = W ab ->
  (forall l' M' wr', length l' = 32%nat -> same_except KS_al l l' ->
                 (rb_ok wr mx len -> rget l' 10 = W 1 /\ wr' = wr + len /\ cell USEGS M' ab 8 (W (out + wr))) ->
                 (~ rb_ok wr mx len -> rget l' 10 = W 0 /\ wr' = wr) ->
                 pkt_at M' pk out wr' mx sb eb ->
                 unch M M' FR_al -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x1288a8) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hpk8 & Hout & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_al [0x128910]. mem_auto. name_mem M1.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_al) by (unname_mems; solve_unch ltac:(unfold FR_al, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  replace (Z_to_bv 64 1214740) with (Z_to_bv 64 0x128914) by reflexivity.
  eapply (reserve_cps rom Post M1 pk out wr mx sb (spv - 32) len ab eb HP1 HW);
    [ lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia] | lia | lia
    | eapply wr_ok_grows; [exact HG1 | exact Hwab]
    | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | reflexivity |].
  intros l' M' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1214668) 0) with (Z_to_bv 64 0x1288cc) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (HU1' : unch M M' FR_al).
  { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_rb, FR_al, inr in *. lia. }
  assert (Cra : cell USEGS M' (spv + -32 + 24) 8 ra).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs0 : cell USEGS M' (spv + -32 + 16) 8 s0).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs1 : cell USEGS M' (spv + -32 + 8) 8 s1).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs2 : cell USEGS M' (spv + -32) 8 s2).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (HG1' : mem_grows M M') by (eapply mem_grows_trans; eassumption).
  assert (Hwpk' : wr_ok USEGS M' (pk + 16) 16) by (eapply wr_ok_grows; [exact HG1' | exact Hwpk]).
  clearbody M1. clear C0 C8 C16 C24 C32 C40 C48 Hwpk Hfr Hwab.
  destruct HP' as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  assert (Hdec : rb_ok wr mx len \/ ~ rb_ok wr mx len) by (unfold rb_ok; lia).
  destruct Hdec as [Hy|Hn].
  - destruct (Hok Hy) as [Ea0 Cab]. match type of Ea0 with ?x = _ => subst x end. clear Hok Hno. destruct Hy as [Hl0 Hroom].
    wp_al [0x128910]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
    split; intros Hbr; [exfalso; lia|]. clear Hbr.
    change 7 with (Z.ones 3). rewrite u_andi_ones_W by lia. rewrite !Wu by lia.
    split; intros Hbr; [exfalso; lia|]. clear Hbr.
    split; intros Hbr; [exfalso; change (2 ^ 3) with 8 in Hbr; lia|]. clear Hbr.
    mem_auto. rewrite ?add_W. mem_auto.
    apply (K _ _ (wr + len)); [reflexivity | same_ex_lia | | | | | ].
    + intros _. split; [reflexivity|]. split; [reflexivity|]. solve_cell.
    + intros Hn. exfalso. apply Hn. split; lia.
    + unfold pkt_at; repeat split; solve_cell.
    + solve_unch ltac:(unfold FR_al, inr in *; lia).
    + eapply mem_grows_trans; [exact HG1'|]. solve_grows.
  - rewrite (Hno Hn) in *. clear Hok Hno.
    wp_al [0x128910]. change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hbr; [clear Hbr | exfalso; lia].
    mem_auto.
    apply (K _ _ wr); [reflexivity | same_ex_lia | intros Hy; exfalso; apply Hn; exact Hy | intros _; split; reflexivity
                      | unfold pkt_at; repeat split; assumption | exact HU1' | exact HG1'].
Qed.
End Alloc.
