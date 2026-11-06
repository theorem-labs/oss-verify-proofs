(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem ULib.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require Import UCode UMemcpy UWpacket.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_pv stops := wp_go 0x12930c 26%nat C_put_value_eq C_put_value stops.

(* [comment removed for export] *)
Section PutValue.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (dt spv : Z) (val : word).
Hypothesis Hdt : 1 < dt /\ dt + 1 < 2 ^ 63.
Hypothesis Hsp : 16 <= spv /\ spv < 2 ^ 63.
Hypothesis Hfr : wr_ok USEGS M (spv - 16) 16.
Hypothesis Hwdt : wr_ok USEGS M dt 1.
Hypothesis Hdj : dt + 1 <= spv - 16 \/ spv <= dt.

Definition KS_pv : list nat := [10; 11; 12; 13; 14]%nat.
Definition FR_pv (x : word) : Prop := inr x (spv - 16) 16 \/ inr x dt 1.

Lemma put_value_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W dt -> rget l 11 = val -> rget l 12 = W 1 ->
  (forall l' M', length l' = 32%nat -> same_except KS_pv l l' -> unch M M' FR_pv -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x12930c) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. regs_open l Hl. subst sp a0 a1 a2.
  wp_pv [0x129370; 0x12933c]. mem_auto. rewrite u_not by lia. rewrite ?(Wu dt), ?(Wu (1 + -1)), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  rewrite ?add_W, ?sub_W. name_mem M1.
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  assert (HU1 : unch M M1 FR_pv) by (unname_mems; solve_unch ltac:(unfold FR_pv, inr in *; lia)).
  assert (Cra : cell USEGS M1 (spv + -16 + 8) 8 ra) by (unname_mems; solve_cell).
  assert (Cs0 : cell USEGS M1 (spv + -16) 8 s0) by (unname_mems; solve_cell).
  assert (Hw1 : wr_ok USEGS M1 dt 1) by (eapply wr_ok_grows; [exact HG1 | exact Hwdt]).
  clearbody M1.
  wp_pv [0x129370; 0x12933c].
  split; [eapply wr_ok_store; [exact Hw1 | lia | lia]|].
  rewrite ?addi_W. rewrite !Wu by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; apply Hbr; reflexivity|]. clear Hbr.
  mem_auto.
  apply K; [reflexivity | same_ex_lia | | eapply mem_grows_trans; [exact HG1|]; solve_grows].
  eapply unch_trans; [exact HU1|]. solve_unch ltac:(unfold FR_pv, inr in *; lia).
Qed.
End PutValue.

Ltac wp_pb stops := wp_go 0x1292a4 26%nat C_wp_put_bytes_eq C_wp_put_bytes stops.

(* [comment removed for export] *)
Section PutBytes.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv : Z) (eb val : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 144 <= spv /\ spv <= pk /\ spv mod 8 = 0.
Hypothesis Hfr : wr_ok USEGS M (spv - 144) 144.
Hypothesis Hwout : wr_ok USEGS M out mx.
Hypothesis Hwpk : wr_ok USEGS M (pk + 16) 16.
Hypothesis Hout : 1 < out /\ (out + mx <= spv - 144 \/ spv <= out) /\ (out + mx <= pk \/ pk + 56 <= out).

Definition KS_pb : list nat := [10; 11; 12; 13; 14]%nat.
Definition FR_pb (x : word) : Prop := inr x (spv - 144) 144 \/ inr x out mx \/ inr x (pk + 16) 16.
Definition pb_ok : Prop := 1 <= mx - wr.

Lemma put_byte_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = val -> rget l 12 = W 1 ->
  (forall l' M' wr', length l' = 32%nat -> same_except KS_pb l l' ->
                 (pb_ok -> wr' = wr + 1) -> (~ pb_ok -> wr' = wr) ->
                 pkt_at M' pk out wr' mx sb eb ->
                 unch M M' FR_pb -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x1292a4) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hpk8 & Hout0 & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_pb (@nil Z). mem_auto. name_mem M1. rewrite ?(Wu 8), ?(Wu 1) by lia.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_pb) by (unname_mems; solve_unch ltac:(unfold FR_pb, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  replace (Z_to_bv 64 1214632) with (Z_to_bv 64 0x1288a8) by reflexivity.
  eapply (alloc_cps rom Post M1 pk out wr mx sb (spv - 48) 1 (spv - 40) eb HP1 HW);
    [ lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia] | lia
    | split; [lia|]; split; [lia|]; split; [apply mod8_sub; [lia | reflexivity] | lia]
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia]
    | eapply wr_ok_grows; [exact HG1 | exact Hwpk]
    | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia |].
  intros l' M' wr' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1217240) 0) with (Z_to_bv 64 0x1292d8) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (HU1' : unch M M' FR_pb).
  { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_al, FR_pb, inr in *. lia. }
  assert (Cra : cell USEGS M' (spv + -48 + 40) 8 ra).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs0 : cell USEGS M' (spv + -48 + 32) 8 s0).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs1 : cell USEGS M' (spv + -48 + 24) 8 s1).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs2 : cell USEGS M' (spv + -48 + 16) 8 s2).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
  assert (HG1' : mem_grows M M') by (eapply mem_grows_trans; eassumption).
  clearbody M1. clear C0 C8 C16 C24 C32 C40 C48.
  assert (Hdec : rb_ok wr mx 1 \/ ~ rb_ok wr mx 1) by (unfold rb_ok; lia).
  destruct Hdec as [Hy|Hn].
  - destruct (Hok Hy) as (Ea0 & Ewr & Cab). match type of Ea0 with ?x = _ => subst x end. subst wr'.
    clear Hok Hno. destruct Hy as [_ Hroom].
    replace (spv - 40) with (spv + -48 + 48 + -40) in Cab by lia.
    wp_pb (@nil Z). change (bv_unsigned (Z_to_bv 64 1)) with 1. split; intros Hb2; [exfalso; lia|]. clear Hb2.
    mem_auto.
    replace (Z_to_bv 64 1217292) with (Z_to_bv 64 0x12930c) by reflexivity.
    eapply (put_value_cps rom Post M' (out + wr) (spv - 48) val);
      [ lia | lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1' | exact Hfr] | lia | lia]
      | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1' | exact Hwout] | lia | lia] | lia
      | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | reflexivity |].
    intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1217260) 0) with (Z_to_bv 64 0x1292ec) by reflexivity.
    regs_open l'' Hl''. se_subst Hse''. clear Hse''.
    assert (HP3 : pkt_at M'' pk out (wr + 1) mx sb eb).
    { eapply pkt_at_unch; [exact HU'' | lia | lia | | exact HP']. intros x Hx. unfold FR_pv, inr in *. lia. }
    assert (Cra3 : cell USEGS M'' (spv + -48 + 40) 8 ra).
    { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold FR_pv, inr in *; lia | exact Cra]. }
    assert (Cs03 : cell USEGS M'' (spv + -48 + 32) 8 s0).
    { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold FR_pv, inr in *; lia | exact Cs0]. }
    assert (Cs13 : cell USEGS M'' (spv + -48 + 24) 8 s1).
    { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold FR_pv, inr in *; lia | exact Cs1]. }
    assert (Cs23 : cell USEGS M'' (spv + -48 + 16) 8 s2).
    { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold FR_pv, inr in *; lia | exact Cs2]. }
    wp_pb (@nil Z). mem_auto.
    apply (K _ _ (wr + 1)); [reflexivity | same_ex_lia | reflexivity | intros Hn; exfalso; apply Hn; unfold pb_ok; lia | exact HP3 | | ].
    + eapply unch_trans; [exact HU1'|]. eapply unch_weaken; [exact HU''|]. intros x Hx. unfold FR_pv, FR_pb, inr in *. lia.
    + eapply mem_grows_trans; eassumption.
  - destruct (Hno Hn) as (Ea0 & Ewr). match type of Ea0 with ?x = _ => subst x end. subst wr'. clear Hok Hno.
    wp_pb (@nil Z). change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hb2; [clear Hb2 | exfalso; lia].
    mem_auto.
    apply (K _ _ wr); [reflexivity | same_ex_lia | intros Hy; exfalso; apply Hn; unfold rb_ok, pb_ok in *; lia | reflexivity
                      | exact HP' | exact HU1' | exact HG1'].
Qed.
End PutBytes.
