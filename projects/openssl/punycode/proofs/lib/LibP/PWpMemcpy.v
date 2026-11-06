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

Ltac wp_wm stops := wp_go 0x11a718 40%nat C_wp_memcpy_eq C_wp_memcpy stops.

(* [comment removed for export] *)
Section WMemcpy.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv src len : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hmx : mx < 32.
Hypothesis Hsp : 128 <= spv /\ spv <= pk.
Hypothesis Hfr : wr_ok PSEGS M (spv - 128) 128.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hsrc : 0 <= src /\ src + len < 2 ^ 63.
Hypothesis Hrd : rd_ok M src len.
Hypothesis Hwout : wr_ok PSEGS M out mx.
Hypothesis Hwpk : wr_ok PSEGS M (pk + 16) 16.
Hypothesis Hout : (out + mx <= spv - 128 \/ spv <= out) /\ (out + mx <= pk \/ pk + 56 <= out).

Definition KS_wm : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%nat.
Definition FR_wm (x : word) : Prop := inr x (spv - 128) 128 \/ inr x out mx \/ inr x (pk + 16) 16.
Definition wm_ok : Prop := len <> 0 /\ len <= mx - wr.

Lemma wmemcpy_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = W src -> rget l 12 = W len ->
  (forall l' M' wr', length l' = 32%nat -> same_except KS_wm l l' ->
                 (wm_ok -> wr' = wr + len) -> (~ wm_ok -> wr' = wr) ->
                 pkt_at M' pk out wr' mx sb eb ->
                 unch M M' FR_wm -> mem_grows M M' ->
                 reach PSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x11a718) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hout0 & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_wm (@nil Z). mem_auto. name_mem M1. rewrite Wu by lia.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_wm) by (unname_mems; solve_unch ltac:(unfold FR_wm, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  split; intros Hb.
  - (* [comment removed for export] *) mem_auto.
    apply (K _ _ wr); [reflexivity | same_ex_lia | intros [H0 _]; exfalso; lia | reflexivity | exact HP1 | exact HU1 | exact HG1].
  - eapply (reserve_cps rom Post M1 pk out wr mx sb (spv - 64) len (spv - 56) eb HP1 HW);
      [ lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia] | lia | lia
      | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia]
      | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia |].
    intros l' M' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1156952) 0) with (Z_to_bv 64 0x11a758) by reflexivity.
    regs_open l' Hl'. se_subst Hse'. clear Hse'.
    assert (HU1' : unch M M' FR_wm).
    { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_rb, FR_wm, inr in *. lia. }
    assert (Cra : cell PSEGS M' (spv + -64 + 56) 8 ra).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs0 : cell PSEGS M' (spv + -64 + 48) 8 s0).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs1 : cell PSEGS M' (spv + -64 + 40) 8 s1).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs2 : cell PSEGS M' (spv + -64 + 32) 8 s2).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs3 : cell PSEGS M' (spv + -64 + 24) 8 s3).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs4 : cell PSEGS M' (spv + -64 + 16) 8 s4).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_rb, inr in *; lia | unname_mems; solve_cell]. }
    assert (HG1' : mem_grows M M') by (eapply mem_grows_trans; eassumption).
    clearbody M1. clear C0 C8 C16 C24 C32 C40 C48.
    destruct HP' as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
    assert (Hdec : rb_ok wr mx len \/ ~ rb_ok wr mx len) by (unfold rb_ok; lia).
    destruct Hdec as [Hy|Hn].
    + destruct (Hok Hy) as [Ea0 Cab]. subst a0. clear Hok Hno. destruct Hy as [Hl0 Hroom].
      replace (spv - 56) with (spv + -64 + 64 + -56) in Cab by lia.
      wp_wm (@nil Z). rewrite Wu by lia. split; intros Hb2; [exfalso; lia|]. clear Hb2.
      mem_auto. rewrite ?add_W. mem_auto. name_mem M2. rewrite Wu by lia.
      split; intros Hb2; [exfalso; lia|]. clear Hb2.
      replace (v_jalr (Z_to_bv 64 2582392) (-820)) with (Z_to_bv 64 0x276444) by reflexivity.
      assert (HP2 : pkt_at M2 pk out (wr + len) mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
      assert (HG2 : mem_grows M M2) by (unname_mems; solve_grows).
      assert (HU2 : unch M M2 FR_wm) by (unname_mems; solve_unch ltac:(unfold FR_wm, inr in *; lia)).
      assert (Cra2 : cell PSEGS M2 (spv + -64 + 56) 8 ra) by (unname_mems; solve_cell).
      assert (Cs02 : cell PSEGS M2 (spv + -64 + 48) 8 s0) by (unname_mems; solve_cell).
      assert (Cs12 : cell PSEGS M2 (spv + -64 + 40) 8 s1) by (unname_mems; solve_cell).
      assert (Cs22 : cell PSEGS M2 (spv + -64 + 32) 8 s2) by (unname_mems; solve_cell).
      assert (Cs32 : cell PSEGS M2 (spv + -64 + 24) 8 s3) by (unname_mems; solve_cell).
      assert (Cs42 : cell PSEGS M2 (spv + -64 + 16) 8 s4) by (unname_mems; solve_cell).
      clearbody M2. clear Cra Cs0 Cs1 Cs2 Cs3 Cs4 C0 C8 C16 C24 C32 C40 C48 Cab.
      eapply (memcpy_cps rom Post M2 (out + wr) src len);
        [ lia | lia | lia | eapply rd_ok_grows; [exact HG2 | exact Hrd]
        | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG2 | exact Hwout] | lia | lia]
        | reflexivity | reflexivity | reflexivity | reflexivity |].
      intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
      replace (v_jalr (Z_to_bv 64 1157004) 0) with (Z_to_bv 64 0x11a78c) by reflexivity.
      regs_open l'' Hl''. se_subst Hse''. clear Hse''.
      assert (HP3 : pkt_at M'' pk out (wr + len) mx sb eb).
      { eapply pkt_at_unch; [exact HU'' | lia | lia | | exact HP2]. intros x Hx. unfold PMemcpy.FP, inr in *. lia. }
      assert (Cra3 : cell PSEGS M'' (spv + -64 + 56) 8 ra).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemcpy.FP, inr in *; lia | exact Cra2]. }
      assert (Cs03 : cell PSEGS M'' (spv + -64 + 48) 8 s0).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemcpy.FP, inr in *; lia | exact Cs02]. }
      assert (Cs13 : cell PSEGS M'' (spv + -64 + 40) 8 s1).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemcpy.FP, inr in *; lia | exact Cs12]. }
      assert (Cs23 : cell PSEGS M'' (spv + -64 + 32) 8 s2).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemcpy.FP, inr in *; lia | exact Cs22]. }
      assert (Cs33 : cell PSEGS M'' (spv + -64 + 24) 8 s3).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemcpy.FP, inr in *; lia | exact Cs32]. }
      assert (Cs43 : cell PSEGS M'' (spv + -64 + 16) 8 s4).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemcpy.FP, inr in *; lia | exact Cs42]. }
      wp_wm (@nil Z). mem_auto.
      apply (K _ _ (wr + len)); [reflexivity | same_ex_lia | reflexivity | intros Hn; exfalso; apply Hn; split; lia | exact HP3 | | ].
      * eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU''|]. intros x Hx. unfold PMemcpy.FP, FR_wm, inr in *. lia.
      * eapply mem_grows_trans; eassumption.
    + rewrite (Hno Hn) in *. clear Hok Hno.
      wp_wm (@nil Z). change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hb2; [clear Hb2 | exfalso; lia].
      mem_auto.
      apply (K _ _ wr); [reflexivity | same_ex_lia | intros Hy; exfalso; apply Hn; exact Hy | reflexivity
                        | unfold pkt_at; repeat split; assumption | exact HU1' | exact HG1'].
Qed.
End WMemcpy.

