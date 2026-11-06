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

Ltac wp_wm stops := wp_go 0x129374 31%nat C_wp_memcpy_eq C_wp_memcpy stops.

Section WMemcpy.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv src len : Z) (eb : word).
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hmx : mx < 32.
Hypothesis Hsp : 144 <= spv /\ spv <= pk /\ spv mod 8 = 0.
Hypothesis Hfr : wr_ok USEGS M (spv - 144) 144.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hsrc : 0 <= src /\ src + len < 2 ^ 63.
Hypothesis Hrd : rd_ok M src len.
Hypothesis Hwout : wr_ok USEGS M out mx.
Hypothesis Hwpk : wr_ok USEGS M (pk + 16) 16.
Hypothesis Hout : (out + mx <= spv - 144 \/ spv <= out) /\ (out + mx <= pk \/ pk + 56 <= out).

Definition KS_wm : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%nat.
Definition FR_wm (x : word) : Prop := inr x (spv - 144) 144 \/ inr x out mx \/ inr x (pk + 16) 16.
Definition wm_ok : Prop := len <> 0 /\ len <= mx - wr.

Lemma wmemcpy_cps : forall l, length l = 32%nat -> rget l 2 = W spv ->
  rget l 10 = W pk -> rget l 11 = W src -> rget l 12 = W len ->
  (forall l' M' wr', length l' = 32%nat -> same_except KS_wm l l' ->
                 (wm_ok -> wr' = wr + len) -> (~ wm_ok -> wr' = wr) ->
                 pkt_at M' pk out wr' mx sb eb ->
                 unch M M' FR_wm -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x129374) l M Post.
Proof.
  intros l Hl H2 H10 H11 H12 K. pose proof HP as (C0 & C8 & C16 & C24 & C32 & C40 & C48).
  pose proof HW as (Hpk & Hpk2 & Hpk8 & Hout0 & Hout2 & Hwr & Hsb & Heb).
  regs_open l Hl. subst sp a0 a1 a2.
  wp_wm (@nil Z). mem_auto. name_mem M1. rewrite Wu by lia.
  assert (HP1 : pkt_at M1 pk out wr mx sb eb) by (unname_mems; unfold pkt_at; repeat split; solve_cell).
  assert (HU1 : unch M M1 FR_wm) by (unname_mems; solve_unch ltac:(unfold FR_wm, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  split; intros Hbr.
  - (* [comment removed for export] *) mem_auto.
    apply (K _ _ wr); [reflexivity | same_ex_lia | intros [H0 _]; exfalso; lia | reflexivity | exact HP1 | exact HU1 | exact HG1].
  - replace (Z_to_bv 64 1214632) with (Z_to_bv 64 0x1288a8) by reflexivity.
    eapply (alloc_cps rom Post M1 pk out wr mx sb (spv - 48) len (spv - 48) eb HP1 HW);
      [ lia | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia] | lia
      | split; [lia|]; split; [lia|]; split; [apply mod8_sub; [lia | reflexivity] | lia] | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hfr] | lia | lia]
      | eapply wr_ok_grows; [exact HG1 | exact Hwpk]
      | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia |].
    intros l' M' wr' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1217452) 0) with (Z_to_bv 64 0x1293ac) by reflexivity.
    regs_open l' Hl'. se_subst Hse'. clear Hse'.
    assert (HU1' : unch M M' FR_wm).
    { eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR_al, FR_wm, inr in *. lia. }
    assert (Cra : cell USEGS M' (spv + -48 + 40) 8 ra).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs0 : cell USEGS M' (spv + -48 + 32) 8 s0).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs1 : cell USEGS M' (spv + -48 + 24) 8 s1).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs2 : cell USEGS M' (spv + -48 + 16) 8 s2).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
    assert (Cs3 : cell USEGS M' (spv + -48 + 8) 8 s3).
    { eapply cell_unch; [exact HU' | lia | lia | intros x Hx; unfold FR_al, inr in *; lia | unname_mems; solve_cell]. }
    assert (HG1' : mem_grows M M') by (eapply mem_grows_trans; eassumption).
    clearbody M1. clear C0 C8 C16 C24 C32 C40 C48.
    assert (Hdec : rb_ok wr mx len \/ ~ rb_ok wr mx len) by (unfold rb_ok; lia).
    destruct Hdec as [Hy|Hn].
    + destruct (Hok Hy) as (Ea0 & Ewr & Cab). match type of Ea0 with ?x = _ => subst x end. subst wr'.
      clear Hok Hno. destruct Hy as [Hl0 Hroom].
      replace (spv - 48) with (spv + -48 + 48 + -48) in Cab by lia.
      wp_wm (@nil Z). change (bv_unsigned (Z_to_bv 64 1)) with 1. split; intros Hb2; [exfalso; lia|]. clear Hb2.
      mem_auto. rewrite Wu by lia.
      split; intros Hb2; [exfalso; lia|]. clear Hb2.
      replace (v_jalr (Z_to_bv 64 2868148) 1336) with (Z_to_bv 64 0x2bc8ec) by reflexivity.
      eapply (memcpy_cps rom Post M' (out + wr) src len);
        [ lia | lia | lia | eapply rd_ok_grows; [exact HG1' | exact Hrd]
        | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1' | exact Hwout] | lia | lia]
        | reflexivity | reflexivity | reflexivity | reflexivity |].
      intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
      replace (v_jalr (Z_to_bv 64 1217480) 0) with (Z_to_bv 64 0x1293c8) by reflexivity.
      regs_open l'' Hl''. se_subst Hse''. clear Hse''.
      assert (HP3 : pkt_at M'' pk out (wr + len) mx sb eb).
      { eapply pkt_at_unch; [exact HU'' | lia | lia | | exact HP']. intros x Hx. unfold UMemcpy.FP, inr in *. lia. }
      assert (Cra3 : cell USEGS M'' (spv + -48 + 40) 8 ra).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemcpy.FP, inr in *; lia | exact Cra]. }
      assert (Cs03 : cell USEGS M'' (spv + -48 + 32) 8 s0).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemcpy.FP, inr in *; lia | exact Cs0]. }
      assert (Cs13 : cell USEGS M'' (spv + -48 + 24) 8 s1).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemcpy.FP, inr in *; lia | exact Cs1]. }
      assert (Cs23 : cell USEGS M'' (spv + -48 + 16) 8 s2).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemcpy.FP, inr in *; lia | exact Cs2]. }
      assert (Cs33 : cell USEGS M'' (spv + -48 + 8) 8 s3).
      { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemcpy.FP, inr in *; lia | exact Cs3]. }
      wp_wm (@nil Z). mem_auto.
      apply (K _ _ (wr + len)); [reflexivity | same_ex_lia | reflexivity | intros Hn; exfalso; apply Hn; split; lia | exact HP3 | | ].
      * eapply unch_trans; [exact HU1'|]. eapply unch_weaken; [exact HU''|]. intros x Hx. unfold UMemcpy.FP, FR_wm, inr in *. lia.
      * eapply mem_grows_trans; eassumption.
    + destruct (Hno Hn) as (Ea0 & Ewr). match type of Ea0 with ?x = _ => subst x end. subst wr'. clear Hok Hno.
      wp_wm (@nil Z). change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hb2; [clear Hb2 | exfalso; lia].
      mem_auto.
      apply (K _ _ wr); [reflexivity | same_ex_lia | intros Hy; exfalso; apply Hn; exact Hy | reflexivity
                        | exact HP' | exact HU1' | exact HG1'].
Qed.
End WMemcpy.
