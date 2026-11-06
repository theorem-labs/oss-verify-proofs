(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AMemIsZero AMemToShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_rp stops := wp_go 0x1c4f34 209%nat C_regpoisoned_eq C_regpoisoned stops.

Section RP.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (b n sp0 : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hmr : memrange b n.
Hypothesis Hnmax : n <= 2 ^ 43.
Hypothesis Hok : addr_ok M b n.
Hypothesis Hsp : A_IMG_END <= sp0 - 80 /\ sp0 < 2 ^ 63.
Hypothesis Hspz : sp0 <= SB \/ HIMEM_BEG <= sp0 - 80.
Hypothesis Hfr : wr_ok ASEGS M (sp0 - 80) 80.

Definition KS : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17]%nat.
Definition KSI : list nat := [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]%nat.
Definition FP (x : word) : Prop := inr x (sp0 - 80) 80.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W sp0.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' -> rget l' 10 = W 0 ->
  unch M M' FP -> mem_grows M M' ->
  reach ASEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition M1 : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (W (sp0 + -64 + 56)) (word_to_le_bytes 8 (rget l0 1)))
    (W (sp0 + -64 + 48)) (word_to_le_bytes 8 (rget l0 8)))
    (W (sp0 + -64 + 40)) (word_to_le_bytes 8 (rget l0 9)))
    (W (sp0 + -64 + 32)) (word_to_le_bytes 8 (rget l0 18)))
    (W (sp0 + -64 + 24)) (word_to_le_bytes 8 (rget l0 19)))
    (W (sp0 + -64 + 16)) (word_to_le_bytes 8 (rget l0 20)))
    (W (sp0 + -64 + 8)) (word_to_le_bytes 8 (rget l0 21)).

Definition SAVE_SLOTS : list (nat * Z) :=
  [(1%nat, 56); (8%nat, 48); (9%nat, 40); (18%nat, 32); (19%nat, 24); (20%nat, 16); (21%nat, 8)].

(* [comment removed for export] *)
Definition FPlow (x : word) : Prop := inr x (sp0 - 80) 16.
Definition MI (M' : mem) : Prop := unch M1 M' FPlow /\ mem_grows M1 M'.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1, A_IMG_END in *. solve_grows. Qed.

Lemma M1_unch : unch M M1 FP.
Proof. unfold M1, A_IMG_END in *. solve_unch ltac:(unfold FP, inr in *; lia). Qed.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma M1_saved : forall k off, In (k, off) SAVE_SLOTS -> cell ASEGS M1 (sp0 + -64 + off) 8 (rget l0 k).
Proof.
  intros k off Hin. unfold A_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Lemma MI_saved : forall M' k off, MI M' -> In (k, off) SAVE_SLOTS ->
  cell ASEGS M' (sp0 + -64 + off) 8 (rget l0 k).
Proof.
  intros M' k off [HU HG] Hin. unfold A_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply M1_saved; exact Hin];
    unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
    try lia; intros x Hx; unfold FPlow, inr in *; lia.
Qed.

Lemma FP_app : forall y, FP y -> A_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold FP, inr in Hy. lia. Qed.

Lemma FP_nosh : forall y, FP y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof. intros y Hy. unfold FP, inr in Hy. lia. Qed.

Lemma MI_final : forall M', MI M' -> unch M M' FP /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. split.
  - eapply unch_trans; [apply M1_unch|]. eapply unch_weaken; [exact HU|].
    intros x Hx. unfold FPlow, FP, inr in *. lia.
  - eapply mem_grows_trans; [apply M1_grows | exact HG].
Qed.

Lemma MI_rt : forall M', MI M' -> rt_ok M'.
Proof. intros M' HMI. destruct (MI_final _ HMI) as [HU _]. eapply rt_ok_unch; [exact HU | apply FP_app | exact Hrt]. Qed.

Lemma MI_ok : forall M', MI M' -> addr_ok M' b n.
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _]. destruct Hmr as [Hn0 Hr].
  eapply addr_ok_unch; [exact HU | unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *; lia
                       | unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *; lia | apply FP_nosh | exact Hok].
Qed.

Ltac pose_saved HMI :=
  pose proof (MI_saved _ 1%nat 56 HMI ltac:(cbv; tauto)) as Csv1;
  pose proof (MI_saved _ 8%nat 48 HMI ltac:(cbv; tauto)) as Csv8;
  pose proof (MI_saved _ 9%nat 40 HMI ltac:(cbv; tauto)) as Csv9;
  pose proof (MI_saved _ 18%nat 32 HMI ltac:(cbv; tauto)) as Csv18;
  pose proof (MI_saved _ 19%nat 24 HMI ltac:(cbv; tauto)) as Csv19;
  pose proof (MI_saved _ 20%nat 16 HMI ltac:(cbv; tauto)) as Csv20;
  pose proof (MI_saved _ 21%nat 8 HMI ltac:(cbv; tauto)) as Csv21.

(* [comment removed for export] *)
Lemma ret0 : forall l M', MI M' -> length l = 32%nat -> same_except KSI l0 l -> rget l 2 = W (sp0 - 64) ->
  reach ASEGS rom (Z_to_bv 64 0x1c50ac) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2. pose_saved HMI. destruct (MI_final _ HMI) as [HU HG].
  unfold A_IMG_END in *. regs_open l Hl. subst sp.
  wp_rp (@nil Z). mem_auto.
  apply K; [reflexivity | | reflexivity | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

Definition shb : Z := sha ((b + 7) / 8 * 8).
Definition she : Z := sha ((b + n) / 8 * 8).

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI l0 l /\ rget l 2 = W (sp0 - 64).

Ltac prove_stable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; reflexivity.

(* [comment removed for export] *)
Lemma after_miz : forall l M', MI M' -> stable l -> rget l 10 = W 1 ->
  reach ASEGS rom (Z_to_bv 64 0x1c50a8) l M' Post.
Proof.
  intros l M' HMI (Hl & Hse & H2) H10. regs_open l Hl. subst sp a0.
  wp_rp [0x1c5060; 0x1c50ac].
  split; intros Hb; [exfalso; rewrite Wu in Hb by lia; lia|].
  apply ret0; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].
Qed.

Lemma shb_val : shb = (b + 7) / 8 + SB.
Proof. unfold shb, sha. rewrite Z.div_mul by lia. reflexivity. Qed.
Lemma she_val : she = (b + n) / 8 + SB.
Proof. unfold she, sha. rewrite Z.div_mul by lia. reflexivity. Qed.

Lemma b_bounds : 0 <= b /\ b + n + 8 <= HIMEM_END.
Proof. destruct Hmr as [Hn0 Hr]. unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. Qed.

Lemma sh_bounds : SB <= shb /\ SB <= she < HIMEM_BEG /\ shb < HIMEM_BEG.
Proof.
  pose proof b_bounds as [Hb0 Hb1]. destruct Hmr as [Hn0 _]. rewrite shb_val, she_val.
  unfold SB, HIMEM_BEG, HIMEM_END in *.
  pose proof (Z.div_pos (b + 7) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (b + n) 8 ltac:(lia) ltac:(lia)).
  assert ((b + n) / 8 < 0x100000000000) by (apply Z.div_lt_upper_bound; lia).
  assert ((b + 7) / 8 < 0x100000000000) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* [comment removed for export] *)
Lemma chk3 : forall l M', MI M' -> stable l -> rget l 19 = W shb -> rget l 10 = W she ->
  reach ASEGS rom (Z_to_bv 64 0x1c5098) l M' Post.
Proof.
  intros l M' HMI (Hl & Hse & H2) H19 H10.
  pose proof sh_bounds as (Hs1 & Hs2 & Hs3). pose proof b_bounds as [Hb0 Hb1].
  unfold SB, HIMEM_BEG, HIMEM_END, A_IMG_END in *.
  regs_open l Hl. subst sp s3 a0.
  wp_rp [0x1c5060; 0x1c50ac].
  rewrite ?sub_W. rewrite !Wu by lia.
  split; intros Hb1'.
  - apply ret0; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].
  - replace (Z_to_bv 64 1922072) with (Z_to_bv 64 0x1d5418) by reflexivity.
    eapply (memiszero_cps rom Post M' shb (she - shb) (sp0 - 64)).
    + pose proof shb_val as Eb. pose proof she_val as Ee. destruct Hmr as [Hn0 _]. unfold SB in Eb, Ee. lia.
    + lia.
    + pose proof (addr_ok_zeros M' b n (MI_ok _ HMI) Hb0) as Hz. fold shb in Hz.
      replace (she - shb) with ((b + n) / 8 - (b + 7) / 8); [exact Hz|].
      pose proof shb_val as Eb. pose proof she_val as Ee. lia.
    + lia.
    + eapply wr_ok_sub; [eapply wr_ok_grows; [apply (proj2 (MI_final _ HMI)) | exact Hfr] | lia | lia].
    + lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + intros l' M'' Hl' Hse' H10' HU' HG'. cbn [rget lget].
      replace (v_jalr (Z_to_bv 64 1855656) 0) with (Z_to_bv 64 0x1c50a8) by reflexivity.
      apply after_miz; [| | exact H10'].
      * destruct HMI as [HU1 HG1]. split; [|eapply mem_grows_trans; eassumption]. eapply unch_trans; [exact HU1|].
        eapply unch_weaken; [exact HU'|].
        intros x Hx. unfold AMemIsZero.FP, FPlow, inr in *. lia.
      * split; [exact Hl'|]. split.
        -- eapply same_except_call; [ | exact Hse' | ];
             [ eapply same_except_trans; [exact Hse | same_ex]
             | intros k Hk; unfold AMemIsZero.KS, KSI in *; cbn [In] in *; intuition lia ].
        -- rewrite (Hse' 2%nat); [reflexivity|]. unfold AMemIsZero.KS. cbn [In]. intuition lia.
Qed.

(* [comment removed for export] *)
Lemma chk2 : forall l M', MI M' -> 0 < n -> stable l -> rget l 18 = W (b + n) -> rget l 11 = W SB ->
  rget l 19 = W shb -> rget l 10 = W she ->
  reach ASEGS rom (Z_to_bv 64 0x1c5044) l M' Post.
Proof.
  intros l M' HMI Hn0 (Hl & Hse & H2) H18 H11 H19 H10.
  pose proof b_bounds as [Hb0 Hb1]. pose proof (MI_ok _ HMI) as Hok1.
  destruct (sh_load ASEGS M' (b + n - 1) (Hok1 (b + n - 1) ltac:(lia)) ltac:(unfold HIMEM_END in *; lia)) as (u & Hu & Hc).
  unfold HIMEM_END in *.
  regs_open l Hl. subst sp s2 a1 s3 a0.
  wp_rp [0x1c5060; 0x1c5098].
  rewrite ?addi_W. replace (b + n + -1) with (b + n - 1) by lia.
  rewrite sha_addr_l by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  assert (Hst : forall r11 r12, stable [x0; ra; Z_to_bv 64 (sp0 - 64); gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 she; r11; r12;
             a3; a4; a5; a6; a7; Z_to_bv 64 (b + n - 1); Z_to_bv 64 shb; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6]).
  { intros r11 r12. prove_stable Hse. }
  split; intros Hb1'.
  - apply chk3; [exact HMI | apply Hst | reflexivity | reflexivity].
  - rewrite andi7_W by lia. rewrite !Ws by (pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)); lia).
    rewrite Wu in Hb1' by lia.
    split; intros Hb2.
    + apply chk3; [exact HMI | apply Hst | reflexivity | reflexivity].
    + exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma chk1 : forall l M', MI M' -> 0 < n -> stable l -> rget l 8 = W b -> rget l 18 = W (b + n) ->
  rget l 19 = W shb -> rget l 10 = W she -> rget l 21 = W C_SB ->
  reach ASEGS rom (Z_to_bv 64 0x1c5028) l M' Post.
Proof.
  intros l M' HMI Hn0 (Hl & Hse & H2) H8 H18 H19 H10 H21.
  pose proof (MI_rt _ HMI) as (_ & Hsb & _). pose proof (MI_ok _ HMI) as Hok1.
  pose proof b_bounds as [Hb0 Hb1].
  destruct (sh_load ASEGS M' b (Hok1 b ltac:(lia)) ltac:(unfold HIMEM_END in *; lia)) as (u & Hu & Hc).
  unfold C_SB, HIMEM_END in *.
  regs_open l Hl. subst sp s0 s2 s3 a0 s5.
  wp_rp [0x1c5060; 0x1c5044].
  mem_auto. rewrite sha_addr_l by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia.
  assert (Hst : forall r12 r13, stable [x0; ra; Z_to_bv 64 (sp0 - 64); gp; tp; t0; t1; t2; Z_to_bv 64 b; s1; Z_to_bv 64 she;
             Z_to_bv 64 SB; r12; r13; a4; a5; a6; a7; Z_to_bv 64 (b + n); Z_to_bv 64 shb; s4; Z_to_bv 64 6753080;
             s6; s7; s8; s9; s10; s11; t3; t4; t5; t6]).
  { intros r12 r13. prove_stable Hse. }
  split; intros Hb1'.
  - apply chk2; [exact HMI | exact Hn0 | apply Hst | reflexivity | reflexivity | reflexivity | reflexivity].
  - rewrite andi7_W by lia. rewrite !Ws by (pose proof (Z.mod_pos_bound b 8 ltac:(lia)); lia).
    rewrite Wu in Hb1' by lia.
    split; intros Hb2.
    + exfalso. lia.
    + apply chk2; [exact HMI | exact Hn0 | apply Hst | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Lemma inmem_ab : inmem ((b + 7) / 8 * 8).
Proof.
  pose proof (align_up_le b). eapply memrange_inmem; [exact Hmr|]. destruct Hmr as [Hn0 _]. lia.
Qed.
Lemma inmem_ae : inmem ((b + n) / 8 * 8).
Proof.
  pose proof (align_dn_le (b + n)). pose proof b_bounds as [Hb0 _]. destruct Hmr as [Hn0 Hr].
  assert (0 <= (b + n) / 8 * 8) by (pose proof (Z.div_pos (b + n) 8 ltac:(lia) ltac:(lia)); lia).
  unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END in *.
  destruct Hr as [Hr|Hr]; [left; lia|]. right.
  assert (HIMEM8 : 0x10007fff8000 mod 8 = 0) by reflexivity.
  assert (0x10007fff8000 <= (b + n) / 8 * 8); [|lia].
  replace 0x10007fff8000 with (0x10007fff8000 / 8 * 8) by reflexivity.
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.

(* [comment removed for export] *)
Lemma calls : forall l M', MI M' -> 0 < n -> stable l -> rget l 8 = W b -> rget l 18 = W (b + n) -> rget l 21 = W C_SB ->
  reach ASEGS rom (Z_to_bv 64 0x1c5008) l M' Post.
Proof.
  intros l M' HMI Hn0 (Hl & Hse & H2) H8 H18 H21.
  pose proof b_bounds as [Hb0 Hb1]. unfold HIMEM_END in *.
  regs_open l Hl. subst sp s0 s2 s5.
  wp_rp [0x1c5238].
  rewrite ?addi_W. rewrite !andi_m8_W by lia. rewrite !Wu by lia.
  split; intros Hb1'; [exfalso; lia|]. clear Hb1'.
  replace (Z_to_bv 64 1854120) with (Z_to_bv 64 0x1c4aa8) by reflexivity.
  eapply (memtoshadow_cps rom Post M' ((b + 7) / 8 * 8)); [apply (MI_rt _ HMI) | apply inmem_ab | reflexivity | reflexivity |].
  intros l' Hl' Hse' H10'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1855516) 0) with (Z_to_bv 64 0x1c501c) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  wp_rp [0x1c5238].
  replace (Z_to_bv 64 1854120) with (Z_to_bv 64 0x1c4aa8) by reflexivity.
  eapply (memtoshadow_cps rom Post M' ((b + n) / 8 * 8)); [apply (MI_rt _ HMI) | apply inmem_ae | reflexivity | reflexivity |].
  intros l'' Hl'' Hse'' H10''. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1855528) 0) with (Z_to_bv 64 0x1c5028) by reflexivity.
  regs_open l'' Hl''. se_subst Hse''. clear Hse''. cbn [rget lget] in H10''. match type of H10'' with ?x = _ => subst x end.
  apply chk1; [exact HMI | exact Hn0 | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex] | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma end_inmem : forall l M', MI M' -> 0 < n -> stable l -> rget l 8 = W b -> rget l 9 = W n -> rget l 21 = W C_SB ->
  rget l 11 = W SB -> rget l 12 = W (SB - 1) ->
  reach ASEGS rom (Z_to_bv 64 0x1c4fc0) l M' Post.
Proof.
  intros l M' HMI Hn0 (Hl & Hse & H2) H8 H9 H21 H11 H12.
  pose proof (MI_rt _ HMI) as (_ & _ & H3 & H4 & H5 & (v6 & H6) & H7 & H8' & _).
  pose proof b_bounds as [Hb0 Hb1]. destruct Hmr as [_ Hr].
  unfold G_MIDBEG, C_MIDBEG, G_MIDEND, C_MIDEND, G_HIEND, C_HIEND, C_SB in *.
  regs_open l Hl. subst sp s0 s1 s5 a1 a2.
  assert (Hgo : forall r10 r11 r12 r13 r14 r15 r16 r17,
    reach ASEGS rom (Z_to_bv 64 0x1c5008)
      [x0; ra; Z_to_bv 64 (sp0 - 64); gp; tp; t0; t1; t2; Z_to_bv 64 b; Z_to_bv 64 n; r10; r11; r12; r13; r14; r15; r16; r17;
       Z_to_bv 64 (n + b); s3; s4; Z_to_bv 64 6753080; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
  { intros. apply calls; [exact HMI | exact Hn0 | | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity].
    split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex] | reflexivity]. }
  wp_rp [0x1c5008; 0x1c5128].
  rewrite ?add_W.
  split; intros Hb1'; [apply Hgo|].
  mem_auto. rewrite midbeg_m1_val.
  split; intros Hb2.
  - mem_auto. rewrite hishadow_end_val.
    unfold SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *. rewrite !Wu in * by lia.
    split; intros Hb3; [exfalso; lia|].
    split; intros Hb4; [exfalso; lia|]. apply Hgo.
  - exfalso. unfold SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *. rewrite !Wu in Hb2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma beg_inmem : forall l M', MI M' -> stable l -> rget l 10 = W b -> rget l 11 = W n ->
  reach ASEGS rom (Z_to_bv 64 0x1c4f54) l M' Post.
Proof.
  intros l M' HMI (Hl & Hse & H2) H10 H11.
  pose proof (MI_rt _ HMI) as (H1 & Hsb & H3 & H4 & H5 & (v6 & H6) & H7 & H8' & _).
  pose proof b_bounds as [Hb0 Hb1]. destruct Hmr as [Hn0 Hr].
  unfold G_SB, G_MIDBEG, C_MIDBEG, G_MIDEND, C_MIDEND, G_HIEND, C_HIEND, C_SB in *.
  regs_open l Hl. subst sp a0 a1.
  assert (Hgo : 0 < n -> forall r10 r13 r14 r15 r16 r17 r5,
    reach ASEGS rom (Z_to_bv 64 0x1c4fc0)
      [x0; ra; Z_to_bv 64 (sp0 - 64); gp; tp; r5; t1; t2; Z_to_bv 64 b; Z_to_bv 64 n; r10; Z_to_bv 64 SB; Z_to_bv 64 (SB - 1);
       r13; r14; r15; r16; r17; s2; s3; s4; Z_to_bv 64 6753080; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] M' Post).
  { intros Hn1; intros. apply end_inmem; [exact HMI | exact Hn1 | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
    split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex] | reflexivity]. }
  wp_rp [0x1c4fc0; 0x1c50ac; 0x1c50d8].
  split; intros Hb0'.
  - apply ret0; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].
  - assert (Hn1 : 0 < n).
    { destruct (Z.eq_dec n 0) as [->|]; [exfalso; apply Hb0'; reflexivity | lia]. }
    mem_auto. rewrite lowmem_end_val.
    split; intros Hb1'; [apply Hgo; exact Hn1|].
    mem_auto. rewrite midbeg_m1_val.
    split; intros Hb2.
    + mem_auto. rewrite hishadow_end_val.
      unfold SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *. rewrite !Wu in * by lia.
      split; intros Hb3; [exfalso; lia|].
      split; intros Hb4; [exfalso; lia|]. apply Hgo; exact Hn1.
    + exfalso. unfold SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *. rewrite !Wu in Hb2 by lia. lia.
Qed.

Lemma rp_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W b -> rget l 11 = W n ->
  reach ASEGS rom (Z_to_bv 64 0x1c4f34) l M Post.
Proof.
  intros l Hl El H10 H11. assert (Hse : same_except KSI l0 l) by (subst l; apply same_except_refl).
  assert (E2 : rget l 2 = W sp0) by (rewrite El; exact H0sp).
  assert (E1 : rget l 1 = rget l0 1 /\ rget l 8 = rget l0 8 /\ rget l 9 = rget l0 9 /\ rget l 18 = rget l0 18
               /\ rget l 19 = rget l0 19 /\ rget l 20 = rget l0 20 /\ rget l 21 = rget l0 21) by (rewrite El; repeat split).
  clear El. unfold A_IMG_END in *. regs_open l Hl. cbn [rget lget] in E1, E2.
  destruct E1 as (? & ? & ? & ? & ? & ? & ?). subst a0 a1 sp ra s0 s1 s2 s3 s4 s5.
  wp_rp [0x1c4f54].
  rewrite ?addi_W.
  repeat (split; [solve_store|]).
  change (wbytes _ _ _) with M1.
  apply beg_inmem; [apply MI_M1 | | reflexivity | reflexivity].
  split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex] | cbn [rget lget]; f_equal; lia].
Qed.

End RP.

(* [comment removed for export] *)
Theorem regpoisoned_cps : forall rom Post M b n sp0 l,
  rt_ok M -> memrange b n -> n <= 2 ^ 43 -> addr_ok M b n ->
  A_IMG_END <= sp0 - 80 /\ sp0 < 2 ^ 63 -> (sp0 <= SB \/ HIMEM_BEG <= sp0 - 80) -> wr_ok ASEGS M (sp0 - 80) 80 ->
  length l = 32%nat -> rget l 2 = W sp0 -> rget l 10 = W b -> rget l 11 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> rget l' 10 = W 0 ->
                 unch M M' (FP sp0) -> mem_grows M M' ->
                 reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach ASEGS rom (Z_to_bv 64 0x1c4f34) l M Post.
Proof.
  intros rom Post M b n sp0 l; intros.
  eapply (rp_body rom Post M b n sp0) with (l0 := l); eauto.
Qed.
