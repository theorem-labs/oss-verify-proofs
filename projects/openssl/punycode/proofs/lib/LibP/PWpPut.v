(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require Import PCode PMemcpy PWpacket.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_pb stops := wp_go 0x11a66c 43%nat C_wp_put_bytes_eq C_wp_put_bytes stops.

(* [comment removed for export] *)
Section PutBytes.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv : Z) (eb val : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hsp : 112 <= spv /\ spv <= pk.
Hypothesis Hfr : wr_ok PSEGS M (spv - 112) 112.
Hypothesis Hwout : wr_ok PSEGS M out mx.
Hypothesis Hwpk : wr_ok PSEGS M (pk + 16) 16.
Hypothesis Hout : (out + mx <= spv - 112 \/ spv <= out) /\ (out + mx <= pk \/ pk + 56 <= out).

Definition KS_pb : list nat := [10; 11; 12]%nat.
Definition FR_pb (x : word) : Prop := inr x (spv - 112) 112 \/ inr x out mx \/ inr x (pk + 16) 16.
Definition pb_ok : Prop := 1 <= mx - wr.

Lemma put_byte_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = val -> rget l 12 = W 1 ->
  (forall l' M' wr', length l' = 32%nat -> same_except KS_pb l l' ->
                 (pb_ok -> wr' = wr + 1) -> (~ pb_ok -> wr' = wr) ->
                 pkt_at M' pk out wr' mx sb eb ->
                 unch M M' FR_pb -> mem_grows M M' ->
                 reach PSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x11a66c) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hout0 & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_pb (@nil Z). mem_auto. name_mem M1. rewrite !Wu by lia.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_pb) by (unname_mems; solve_unch ltac:(unfold FR_pb, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  split; intros Hb; [exfalso; lia|]. clear Hb.
  eapply (reserve_cps rom Post M1 pk out wr mx sb (spv - 48) 1 (spv - 48) eb HP1 HW);
    [ lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia] | lia | lia
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia]
    | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia |].
  intros l' M' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1156776) 0) with (Z_to_bv 64 0x11a6a8) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (HU1' : unch M M' FR_pb).
  { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_rb, FR_pb, inr in *. lia. }
  assert (Cra : cell PSEGS M' (spv + -48 + 40) 8 ra).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs0 : cell PSEGS M' (spv + -48 + 32) 8 s0).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs1 : cell PSEGS M' (spv + -48 + 24) 8 s1).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs2 : cell PSEGS M' (spv + -48 + 16) 8 s2).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (Cs3 : cell PSEGS M' (spv + -48 + 8) 8 s3).
  { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
  assert (HG1' : mem_grows M M') by (eapply mem_grows_trans; eassumption).
  clearbody M1. clear C0 C8 C16 C24 C32 C40 C48.
  destruct HP' as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  assert (Hdec : rb_ok wr mx 1 \/ ~ rb_ok wr mx 1) by (unfold rb_ok; lia).
  destruct Hdec as [Hy|Hn].
  - destruct (Hok Hy) as [Ea0 Cab]. subst a0. clear Hok Hno. destruct Hy as [_ Hroom].
    replace (spv - 48) with (spv + -48 + 48 + -48) in Cab by lia.
    wp_pb [0x11a6d8]. rewrite Wu by lia. split; intros Hb2; [exfalso; lia|]. clear Hb2.
    mem_auto. rewrite ?add_W. mem_auto. name_mem M2. rewrite !Wu by lia.
    split; intros Hb2; [exfalso; lia|]. clear Hb2.
    split; intros Hb2; [exfalso; lia|]. clear Hb2. rewrite ?addi_W, ?add_W.
    assert (HP2 : pkt_at M2 pk out (wr + 1) mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
    assert (HG2 : mem_grows M M2) by (unname_mems; solve_grows).
    assert (HU2 : unch M M2 FR_pb) by (unname_mems; solve_unch ltac:(unfold FR_pb, inr in *; lia)).
    assert (Cra2 : cell PSEGS M2 (spv + -48 + 40) 8 ra) by (unname_mems; solve_cell).
    assert (Cs02 : cell PSEGS M2 (spv + -48 + 32) 8 s0) by (unname_mems; solve_cell).
    assert (Cs12 : cell PSEGS M2 (spv + -48 + 24) 8 s1) by (unname_mems; solve_cell).
    assert (Cs22 : cell PSEGS M2 (spv + -48 + 16) 8 s2) by (unname_mems; solve_cell).
    assert (Cs32 : cell PSEGS M2 (spv + -48 + 8) 8 s3) by (unname_mems; solve_cell).
    assert (Hw2 : wr_ok PSEGS M2 out mx) by (eapply wr_ok_grows; [exact HG2 | exact Hwout]).
    clearbody M2. clear Cra Cs0 Cs1 Cs2 Cs3 C0 C8 C16 C24 C32 C40 C48 Cab Hwout Hwpk Hfr.
    destruct HP2 as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
    wp_pb [0x11a6d8]. rewrite ?addi_W.
    split; [eapply wr_ok_store; [exact Hw2 | lia | lia]|].
    rewrite !Wu by lia. split; intros Hb2; [exfalso; lia|]. clear Hb2.
    mem_auto.
    apply (K _ _ (wr + 1)); [reflexivity | same_ex_lia | reflexivity | intros Hn; exfalso; apply Hn; unfold pb_ok; lia | | | ].
    + unfold pkt_at; repeat split; solve_cell.
    + solve_unch ltac:(unfold FR_pb, inr in *; lia).
    + eapply mem_grows_trans; [exact HG2|]. solve_grows.
  - rewrite (Hno Hn) in *. clear Hok Hno.
    wp_pb [0x11a6d8]. change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hb2; [clear Hb2 | exfalso; lia].
    mem_auto.
    apply (K _ _ wr); [reflexivity | same_ex_lia | intros Hy; exfalso; apply Hn; unfold rb_ok, pb_ok in *; lia | reflexivity
                      | unfold pkt_at; repeat split; assumption | exact HU1' | exact HG1'].
Qed.
End PutBytes.
