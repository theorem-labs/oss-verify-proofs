(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem DecArith.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require Import PCode PImg PMemcpy PMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_dec stops := wp_go 0x1e0688 204%nat C_decode_eq C_decode stops.

(* [comment removed for export] *)
Definition KSdec : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition KSD : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition dec_FP (sp0 d q max : Z) (x : word) : Prop :=
  inr x (sp0 - 144) 144 \/ inr x d (4 * max) \/ inr x q 4.

Definition SAVE_SLOTS : list (nat * Z) :=
  [(1%nat, 136); (8%nat, 128); (9%nat, 120); (18%nat, 112); (19%nat, 104); (20%nat, 96); (21%nat, 88);
   (22%nat, 80); (23%nat, 72); (24%nat, 64); (25%nat, 56); (26%nat, 48); (27%nat, 40)].

Section Decode.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (sp0 p n d q max : Z).
Hypothesis Hn : 0 <= n < 2 ^ 31.
Hypothesis Hp : 0 <= p /\ p + n < 2 ^ 63.
Hypothesis Hrd : rd_ok M p n.
Hypothesis Hmax : 0 <= max <= 512.
Hypothesis Hqc : cell PSEGS M q 4 (W max).
Hypothesis Hsp : P_IMG_END <= sp0 - 144 /\ sp0 < 2 ^ 63.
Hypothesis Hfr : wr_ok PSEGS M (sp0 - 144) 144.
Hypothesis Hd : P_IMG_END <= d /\ d + 4 * max < 2 ^ 63.
Hypothesis Hwd : wr_ok PSEGS M d (4 * max).
Hypothesis Hq : P_IMG_END <= q /\ q + 4 < 2 ^ 63.
Hypothesis Hwq : wr_ok PSEGS M q 4.
Hypothesis Hdj1 : d + 4 * max <= sp0 - 144 \/ sp0 <= d.
Hypothesis Hdj2 : q + 4 <= sp0 - 144 \/ sp0 <= q.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W sp0.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSdec l0 l' ->
  (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
  (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell PSEGS M' q 4 (W w)) ->
  unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
  reach PSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

(* [comment removed for export] *)
Definition M1 : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (W (sp0 + -144 + 136)) (word_to_le_bytes 8 (rget l0 1)))
    (W (sp0 + -144 + 128)) (word_to_le_bytes 8 (rget l0 8)))
    (W (sp0 + -144 + 120)) (word_to_le_bytes 8 (rget l0 9)))
    (W (sp0 + -144 + 112)) (word_to_le_bytes 8 (rget l0 18)))
    (W (sp0 + -144 + 104)) (word_to_le_bytes 8 (rget l0 19)))
    (W (sp0 + -144 + 96)) (word_to_le_bytes 8 (rget l0 20)))
    (W (sp0 + -144 + 88)) (word_to_le_bytes 8 (rget l0 21)))
    (W (sp0 + -144 + 80)) (word_to_le_bytes 8 (rget l0 22)))
    (W (sp0 + -144 + 72)) (word_to_le_bytes 8 (rget l0 23)))
    (W (sp0 + -144 + 64)) (word_to_le_bytes 8 (rget l0 24)))
    (W (sp0 + -144 + 56)) (word_to_le_bytes 8 (rget l0 25)))
    (W (sp0 + -144 + 48)) (word_to_le_bytes 8 (rget l0 26)))
    (W (sp0 + -144 + 40)) (word_to_le_bytes 8 (rget l0 27)).

(* [comment removed for export] *)
Definition FPin (x : word) : Prop := inr x (sp0 - 144) 40 \/ inr x d (4 * max) \/ inr x q 4.

Definition MI (M' : mem) : Prop := unch M1 M' FPin /\ mem_grows M1 M'.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1, P_IMG_END in *. solve_grows. Qed.

Lemma M1_unch : unch M M1 (dec_FP sp0 d q max).
Proof. unfold M1, P_IMG_END in *. solve_unch ltac:(unfold dec_FP, inr in *; lia). Qed.

Lemma M1_saved : forall k off, In (k, off) SAVE_SLOTS ->
  cell PSEGS M1 (sp0 + -144 + off) 8 (rget l0 k).
Proof.
  intros k off Hin. unfold P_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Lemma MI_saved : forall M' k off, MI M' ->
  In (k, off) SAVE_SLOTS ->
  cell PSEGS M' (sp0 + -144 + off) 8 (rget l0 k).
Proof.
  intros M' k off [HU HG] Hin. unfold P_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply M1_saved; exact Hin];
    unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
    try lia; intros x Hx; unfold FPin, inr in *; lia.
Qed.

Lemma MI_rd : forall M', MI M' -> rd_ok M' p n.
Proof. intros M' [_ HG]. eapply rd_ok_grows; [exact HG|]. eapply rd_ok_grows; [apply M1_grows | exact Hrd]. Qed.

Lemma MI_wr_d : forall M', MI M' -> wr_ok PSEGS M' d (4 * max).
Proof. intros M' [_ HG]. eapply wr_ok_grows; [exact HG|]. eapply wr_ok_grows; [apply M1_grows | exact Hwd]. Qed.

Lemma MI_wr_q : forall M', MI M' -> wr_ok PSEGS M' q 4.
Proof. intros M' [_ HG]. eapply wr_ok_grows; [exact HG|]. eapply wr_ok_grows; [apply M1_grows | exact Hwq]. Qed.

Lemma MI_wr_sp : forall M', MI M' -> wr_ok PSEGS M' (sp0 - 144) 40.
Proof.
  intros M' [_ HG]. eapply wr_ok_grows; [exact HG|]. eapply wr_ok_grows; [apply M1_grows|].
  eapply wr_ok_sub; [exact Hfr | lia | lia].
Qed.

Lemma MI_final : forall M', MI M' -> unch M M' (dec_FP sp0 d q max) /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. split.
  - eapply unch_trans; [apply M1_unch|]. eapply unch_weaken; [exact HU|].
    intros x Hx. unfold FPin, dec_FP, inr in *. lia.
  - eapply mem_grows_trans; [apply M1_grows | exact HG].
Qed.

Ltac pose_saved HMI :=
  pose proof (MI_saved _ 1%nat 136 HMI ltac:(cbv; tauto)) as Csv1;
  pose proof (MI_saved _ 8%nat 128 HMI ltac:(cbv; tauto)) as Csv8;
  pose proof (MI_saved _ 9%nat 120 HMI ltac:(cbv; tauto)) as Csv9;
  pose proof (MI_saved _ 18%nat 112 HMI ltac:(cbv; tauto)) as Csv18;
  pose proof (MI_saved _ 19%nat 104 HMI ltac:(cbv; tauto)) as Csv19;
  pose proof (MI_saved _ 20%nat 96 HMI ltac:(cbv; tauto)) as Csv20;
  pose proof (MI_saved _ 21%nat 88 HMI ltac:(cbv; tauto)) as Csv21;
  pose proof (MI_saved _ 22%nat 80 HMI ltac:(cbv; tauto)) as Csv22;
  pose proof (MI_saved _ 23%nat 72 HMI ltac:(cbv; tauto)) as Csv23;
  pose proof (MI_saved _ 24%nat 64 HMI ltac:(cbv; tauto)) as Csv24;
  pose proof (MI_saved _ 25%nat 56 HMI ltac:(cbv; tauto)) as Csv25;
  pose proof (MI_saved _ 26%nat 48 HMI ltac:(cbv; tauto)) as Csv26;
  pose proof (MI_saved _ 27%nat 40 HMI ltac:(cbv; tauto)) as Csv27.

(* [comment removed for export] *)
Lemma epilogue : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 144) ->
  (rget l 10 = W 0 \/ rget l 10 = W 1) ->
  (rget l 10 = W 1 -> exists w, 0 <= w <= max /\ cell PSEGS M' q 4 (W w)) ->
  reach PSEGS rom (Z_to_bv 64 0x1e06dc) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2 Ha0 Hw. pose_saved HMI. destruct (MI_final _ HMI) as [HU HG].
  unfold P_IMG_END in *. regs_open l Hl. subst sp.
  wp_dec (@nil Z). mem_auto.
  apply K; [reflexivity | | exact Ha0 | exact Hw | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fail_exit : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 144) ->
  reach PSEGS rom (Z_to_bv 64 0x1e06d8) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2. regs_open l Hl. subst sp.
  wp_dec [0x1e06dc].
  apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E].
Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSD l0 l /\ rget l 2 = W (sp0 - 144) /\ rget l 8 = W sp0
  /\ rget l 9 = W q /\ rget l 18 = W d /\ rget l 19 = W n /\ rget l 20 = W p /\ rget l 7 = W max.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H9 & ?H18 & ?H19 & ?H20 & ?H7);
  regs_open l Hl.

Ltac prove_stable Hse :=
  unfold stable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
  cbn [rget lget]; repeat split; reflexivity.

Ltac pose_wr HMI :=
  pose proof (MI_rd _ HMI) as Hrd'; pose proof (MI_wr_d _ HMI) as Hwd';
  pose proof (MI_wr_q _ HMI) as Hwq'; pose proof (MI_wr_sp _ HMI) as Hwsp'.

Lemma MI_store : forall M' a bs, MI M' -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat (length bs)) -> FPin x) -> MI (wbytes M' (W a) bs).
Proof.
  intros M' a bs [HU HG] Ha Hnw HF. split.
  - apply unch_store; assumption.
  - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
Qed.

(* [comment removed for export] *)
Lemma success_exit : forall l M' wo, MI M' -> stable l -> rget l 23 = W wo -> 0 <= wo <= max ->
  reach PSEGS rom (Z_to_bv 64 0x1e09ac) l M' Post.
Proof.
  intros l M' wo HMI Hst H23 Hwo. pose_wr HMI. unfold P_IMG_END in *.
  open_stable Hst l. subst.
  wp_dec [0x1e06dc]. mem_auto.
  apply epilogue; [ | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | right; reflexivity | intros _; exists wo; split; [lia | apply cell_store_same; lia] ].
  apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia |].
  intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia.
Qed.

(* [comment removed for export] *)
Definition OI (pi wo : Z) (l : regfile) : Prop :=
  stable l /\ rget l 28 = W n /\ rget l 22 = W pi /\ rget l 11 = W wo /\ 0 <= pi < n /\ 0 <= wo <= max.

Section Tail.
Variables (pi' wo : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Kout : forall l M', MI M' -> OI pi' (wo + 1) l -> reach PSEGS rom (Z_to_bv 64 0x1e07f4) l M' Post.

(* [comment removed for export] *)
Lemma tail : forall l M', MI M' -> stable l -> rget l 28 = W n -> rget l 22 = W pi' ->
  rget l 11 = W wo -> rget l 23 = W (wo + 1) ->
  reach PSEGS rom (Z_to_bv 64 0x1e090c) l M' Post.
Proof.
  intros l M' HMI Hst H28 H22 H11 H23. pose_wr HMI. unfold P_IMG_END in *.
  open_stable Hst l. subst.
  destruct (rem_idx a2 (wo + 1) ltac:(lia)) as (r & Hr & Er).
  wp_dec [0x1e06dc]. rewrite !Wu by lia.
  split; intros Hb; [clear Hb|].
  { apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                    | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E]. }
  clear Hb. split; intros Hb.
  { apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                    | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E]. }
  mem_auto. rewrite Er. rewrite (subw_W wo r) by lia. rewrite !scale4_W by lia. rewrite ?add_W, ?addi_W.
  name_mem M2.
  assert (HMI2 : MI M2).
  { unname_mems. repeat (apply MI_store; [ | lia | rewrite length_N_to_le_bytes; lia
        | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]). exact HMI. }
  assert (Ct2 : cell PSEGS M2 (sp0 + -112) 8 (W max)) by (unname_mems; solve_cell).
  assert (Ct3 : cell PSEGS M2 (sp0 + -120) 8 (W n)) by (unname_mems; solve_cell).
  assert (Ct4 : cell PSEGS M2 (sp0 + -128) 8 (v_addw (v_divuw a2 (W (wo + 1))) t4)) by (unname_mems; solve_cell).
  assert (Cs11 : cell PSEGS M2 (sp0 + -136) 8 s11) by (unname_mems; solve_cell).
  assert (Cra : cell PSEGS M2 (sp0 + -144) 8 ra) by (unname_mems; solve_cell).
  clearbody M2. clear Hrd' Hwd' Hwq' Hwsp'. pose_wr HMI2.
  replace (Z_to_bv 64 2582600) with (Z_to_bv 64 0x276848) by reflexivity.
  eapply (memmove_cps rom Post M2 (d + 4 * r + 4) (d + 4 * r) (4 * (wo - r)));
    [ lia | lia | lia | replace (d + 4 * r + 4 - (d + 4 * r)) with 4 by lia; discriminate | lia
    | eapply rd_ok_sub; [apply (wr_ok_rd_ok M2 d (4 * max) Hwd'); unfold P_IMG_END; lia | lia | lia]
    | eapply wr_ok_sub; [exact Hwd' | lia | lia]
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1968508) 0) with (Z_to_bv 64 0x1e097c) by reflexivity.
  regs_open l'' Hl''. se_subst Hse''. clear Hse''.
  assert (HMI3 : MI M'').
  { destruct HMI2 as [HU2 HG2]. split; [|eapply mem_grows_trans; eassumption].
    eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU''|].
    intros x Hx. unfold PMemmove.FP, FPin, inr in *. lia. }
  assert (Ct2' : cell PSEGS M'' (sp0 + -112) 8 (W max)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemmove.FP, inr in *; lia | exact Ct2]. }
  assert (Ct3' : cell PSEGS M'' (sp0 + -120) 8 (W n)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemmove.FP, inr in *; lia | exact Ct3]. }
  assert (Ct4' : cell PSEGS M'' (sp0 + -128) 8 (v_addw (v_divuw a2 (W (wo + 1))) t4)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemmove.FP, inr in *; lia | exact Ct4]. }
  assert (Cs11' : cell PSEGS M'' (sp0 + -136) 8 s11).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemmove.FP, inr in *; lia | exact Cs11]. }
  assert (Cra' : cell PSEGS M'' (sp0 + -144) 8 ra).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold PMemmove.FP, inr in *; lia | exact Cra]. }
  clear Ct2 Ct3 Ct4 Cs11 Cra Hrd' Hwd' Hwq' Hwsp'. pose_wr HMI3.
  wp_dec [0x1e07f4; 0x1e09ac]. mem_auto. rewrite !Wu by lia.
  assert (HMI4 : MI (wbytes M'' (W (d + 4 * r)) (word_to_le_bytes 4 (v_addw (v_divuw a2 (W (wo + 1))) t4)))).
  { apply MI_store; [exact HMI3 | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia. }
  split; intros Hb2.
  - apply Kout; [exact HMI4|]. unfold OI. split; [prove_stable Hse|]. cbn [rget lget].
    repeat split; try reflexivity; lia.
  - eapply (success_exit _ _ (wo + 1)); [exact HMI4 | prove_stable Hse | reflexivity | lia].
Qed.
End Tail.

(* [comment removed for export] *)
Definition BI (s6v wo : Z) (l : regfile) : Prop :=
  stable l /\ rget l 28 = W n /\ rget l 11 = W wo /\ rget l 22 = W s6v.

Ltac open_BI H l :=
  let Hst := fresh "Hst" in
  destruct H as (Hst & ?H28 & ?H11 & ?H22); open_stable Hst l.

Ltac prove_BI Hse :=
  unfold BI; split; [prove_stable Hse|]; cbn [rget lget]; repeat split; try reflexivity.

Section Adapt.
Variables (pi' wo : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Ktail : forall l M', MI M' -> stable l -> rget l 28 = W n -> rget l 22 = W pi' ->
  rget l 11 = W wo -> rget l 23 = W (wo + 1) -> reach PSEGS rom (Z_to_bv 64 0x1e090c) l M' Post.

(* [comment removed for export] *)
Lemma adapt_loop : forall k l M', bv_unsigned (rget l 10) mod 2 ^ 32 = Z.of_nat k ->
  MI M' -> BI pi' wo l -> rget l 23 = W (wo + 1) ->
  reach PSEGS rom (Z_to_bv 64 0x1e08e0) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros l M' Hk HMI HBI H23.
  open_BI HBI l. subst. cbn [rget lget] in Hk.
  wp_dec [0x1e08e0; 0x1e090c]. split; intros Hb.
  - pose proof (adapt_decrease a0 s9 t6 Hb) as Hdec.
    eapply (IH (Z.to_nat (bv_unsigned (v_srliw (v_add (v_srliw (v_subw a0 (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 1)
                              (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 5) mod 2 ^ 32)));
      [ | | exact HMI | prove_BI Hse | reflexivity ].
    + pose proof (Z.mod_pos_bound (bv_unsigned (v_srliw (v_add (v_srliw (v_subw a0 (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 1)
                              (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 5)) (2 ^ 32) ltac:(lia)). lia.
    + cbn [rget lget].
      pose proof (Z.mod_pos_bound (bv_unsigned (v_srliw (v_add (v_srliw (v_subw a0 (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 1)
                              (v_srli (v_mulhu (v_slli a0 32) s9) 32)) 5)) (2 ^ 32) ltac:(lia)). lia.
  - clear Hb. apply Ktail; [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma brk : forall l M', MI M' -> BI pi' wo l -> reach PSEGS rom (Z_to_bv 64 0x1e08ac) l M' Post.
Proof.
  intros l M' HMI HBI. open_BI HBI l. subst.
  assert (Es7 : v_addiw (W wo) 1 = W (wo + 1)) by (apply addiw_W; lia).
  wp_dec [0x1e08e0; 0x1e090c]. rewrite ?Es7.
  split; intros Hb; clear Hb; (split; intros Hb; clear Hb);
    first [ apply Ktail; [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity]
          | eapply (adapt_loop (Z.to_nat (bv_unsigned _ mod 2 ^ 32)));
            [ cbn [rget lget]; rewrite Z2Nat.id; [reflexivity | apply Z.mod_pos_bound; lia]
            | exact HMI | prove_BI Hse | reflexivity ] ].
Qed.
End Adapt.

Section Digits.
Variables (wo lo : Z).
Hypothesis Hlo : 0 <= lo.
Hypothesis Kbrk : forall s6v l M', lo < s6v <= n -> MI M' -> BI s6v wo l ->
  reach PSEGS rom (Z_to_bv 64 0x1e08ac) l M' Post.

Section Iter.
Variable idx : Z.
Hypothesis Hidx : lo <= idx < n.
Hypothesis Kd1 : forall l M', idx + 1 < n -> MI M' -> BI (idx + 2) wo l -> rget l 17 = W (idx + 1) ->
  reach PSEGS rom (Z_to_bv 64 0x1e081c) l M' Post.

Ltac fail_leaf HMI Hse :=
  apply fail_exit; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].

(* [comment removed for export] *)
Lemma d3 : forall l M', MI M' -> BI (idx + 1) wo l -> reach PSEGS rom (Z_to_bv 64 0x1e086c) l M' Post.
Proof.
  intros l M' HMI HBI. open_BI HBI l. subst.
  wp_dec [0x1e06d8; 0x1e08ac; 0x1e081c]. rewrite zext32_W by lia. rewrite !Wu by lia.
  split; intros Hb; clear Hb.
  - apply (Kbrk (idx + 1)); [lia | exact HMI | prove_BI Hse].
  - split; intros Hb; clear Hb; [fail_leaf HMI Hse|].
    split; intros Hb; [fail_leaf HMI Hse|].
    rewrite addiw_W by lia.
    apply Kd1; [lia | exact HMI | prove_BI Hse; f_equal; lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma d2 : forall l M', MI M' -> BI (idx + 1) wo l -> reach PSEGS rom (Z_to_bv 64 0x1e0840) l M' Post.
Proof.
  intros l M' HMI HBI. open_BI HBI l. subst.
  wp_dec [0x1e06d8; 0x1e086c].
  repeat (split; intros ?Hb); first [ fail_leaf HMI Hse | apply d3; [exact HMI | prove_BI Hse] ].
Qed.

(* [comment removed for export] *)
Lemma d1 : forall l M', MI M' -> BI (idx + 1) wo l -> rget l 17 = W idx ->
  reach PSEGS rom (Z_to_bv 64 0x1e081c) l M' Post.
Proof.
  intros l M' HMI HBI H17. pose_wr HMI. open_BI HBI l. subst.
  wp_dec [0x1e06d8; 0x1e0840]. rewrite ?add_W.
  assert (exists v, load_ok PSEGS M' (W (p + idx)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  repeat (split; intros ?Hb); first [ fail_leaf HMI Hse | apply d2; [exact HMI | prove_BI Hse] ].
Qed.
End Iter.

Lemma digit_loop : forall k idx l M', n - idx = Z.of_nat k -> lo <= idx < n ->
  MI M' -> BI (idx + 1) wo l -> rget l 17 = W idx ->
  reach PSEGS rom (Z_to_bv 64 0x1e081c) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros idx l M' Hk Hidx HMI HBI H17.
  apply (d1 idx Hidx); [|exact HMI | exact HBI | exact H17].
  intros l2 M2 Hlt HMI2 HBI2 H17'.
  eapply (IH (Z.to_nat (n - (idx + 1)))) with (idx := idx + 1); [lia | lia | lia | exact HMI2 | | exact H17'].
  replace (idx + 1 + 1) with (idx + 2) by lia. exact HBI2.
Qed.
End Digits.

(* [comment removed for export] *)
Lemma outer_loop : forall k pi wo l M', n - pi = Z.of_nat k -> MI M' -> OI pi wo l ->
  reach PSEGS rom (Z_to_bv 64 0x1e07f4) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros pi wo l M' Hk HMI HOI.
  destruct HOI as (Hst & H28 & H22 & H11 & Hpi & Hwo).
  open_stable Hst l. subst.
  wp_dec [0x1e06d8; 0x1e081c]. rewrite zext32_W by lia. rewrite !Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb. rewrite addiw_W by lia.
  eapply digit_loop with (wo := wo) (lo := pi) (idx := pi) (k := Z.to_nat (n - pi));
    [ lia | | lia | lia | exact HMI | prove_BI Hse | reflexivity ].
  (* [comment removed for export] *)
  intros s6v l2 M2 Hs6 HMI2 HBI2.
  eapply brk with (pi' := s6v) (wo := wo); [lia | | exact HMI2 | exact HBI2].
  intros l3 M3 HMI3 Hst3 H28' H22' H11' H23'.
  eapply tail with (pi' := s6v) (wo := wo); try assumption; try lia.
  intros l4 M4 HMI4 HOI4.
  eapply (IH (Z.to_nat (n - s6v))); [lia | | exact HMI4 | exact HOI4]. lia.
Qed.

(* [comment removed for export] *)
Lemma pre_outer : forall pi wo l M', MI M' -> stable l -> rget l 22 = W pi -> rget l 23 = W wo ->
  0 <= pi <= n -> 0 <= wo <= max ->
  reach PSEGS rom (Z_to_bv 64 0x1e07ac) l M' Post.
Proof.
  intros pi wo l M' HMI Hst H22 H23 Hpi Hwo. open_stable Hst l. subst.
  wp_dec [0x1e07f4; 0x1e09ac]. rewrite addiw_W by lia. rewrite !Wu by lia.
  split; intros Hb.
  - eapply (success_exit _ _ wo); [exact HMI | prove_stable Hse | reflexivity | lia].
  - eapply (outer_loop (Z.to_nat (n - pi)) pi wo); [lia | exact HMI|].
    unfold OI. split; [prove_stable Hse|]. cbn [rget lget]. repeat split; try reflexivity; try lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_loop : forall k j bc l M', bc - j = Z.of_nat k -> 0 <= j < bc -> bc <= max -> bc < n ->
  MI M' -> stable l -> rget l 23 = W bc ->
  rget l 10 = W (bc - j) -> rget l 11 = W (d + 4 * j) -> rget l 12 = W (p + j) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0778) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros j bc l M' Hk Hj Hbm Hbn HMI Hst H23 H10 H11 H12.
  pose_wr HMI. unfold P_IMG_END in *. open_stable Hst l. subst.
  wp_dec [0x1e0778; 0x1e06d8; 0x1e07ac].
  assert (exists v, load_ok PSEGS M' (W (p + j)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  split; intros Hb; clear Hb.
  { apply fail_exit; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity]. }
  split; [eapply wr_ok_store; [exact Hwd' | lia | lia]|].
  rewrite ?addi_W. rewrite Wu by lia.
  assert (HMI2 : MI (wbytes M' (W (d + 4 * j)) (word_to_le_bytes 4 (v_lb (Z_to_bv 8 (bv_unsigned v)))))).
  { apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia. }
  split; intros Hb.
  - eapply (IH (Z.to_nat (bc - (j + 1)))) with (j := j + 1) (bc := bc);
      [lia | lia | lia | lia | lia | exact HMI2 | prove_stable Hse | reflexivity | ..]; cbn [rget lget]; f_equal; lia.
  - rewrite addiw_W by lia.
    eapply (pre_outer (bc + 1) bc); [exact HMI2 | prove_stable Hse | reflexivity | reflexivity | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma post_scan : forall bc l M', MI M' -> stable l -> rget l 23 = W bc -> bc = 0 \/ 0 < bc < n ->
  reach PSEGS rom (Z_to_bv 64 0x1e0760) l M' Post.
Proof.
  intros bc l M' HMI Hst H23 Hbc. open_stable Hst l. subst.
  wp_dec [0x1e0778; 0x1e06d8; 0x1e07ac]. rewrite !Wu by lia.
  split; intros Hb.
  - eapply (pre_outer 0 bc); [exact HMI | prove_stable Hse | reflexivity | reflexivity | lia | lia].
  - split; intros Hb2.
    + apply fail_exit; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].
    + rewrite zext32_W by lia.
      eapply (copy_loop (Z.to_nat (bc - 0)) 0 bc); [lia | lia | lia | lia | exact HMI | prove_stable Hse | reflexivity | ..];
        cbn [rget lget]; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma scan_loop : forall m k bc l M', n - k = Z.of_nat m -> 0 <= k < n -> bc = 0 \/ 0 < bc < k ->
  MI M' -> stable l ->
  rget l 10 = W k -> rget l 11 = W (p + n) -> rget l 13 = W (p + k) -> rget l 14 = W bc ->
  reach PSEGS rom (Z_to_bv 64 0x1e0740) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros k bc l M' Hm Hk Hbc HMI Hst H10 H11 H13 H14.
  pose_wr HMI. open_stable Hst l. subst.
  wp_dec [0x1e0740; 0x1e0760].
  assert (exists v, load_ok PSEGS M' (W (p + k)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  rewrite ?addi_W. rewrite addiw_W by lia. rewrite !Wu by lia.
  split; intros Hb; clear Hb; (split; intros Hb).
  - eapply (IH (Z.to_nat (n - (k + 1)))) with (k := k + 1) (bc := k);
      [lia | lia | lia | lia | exact HMI | prove_stable Hse | ..]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - eapply (post_scan k); [exact HMI | prove_stable Hse | reflexivity | lia].
  - eapply (IH (Z.to_nat (n - (k + 1)))) with (k := k + 1) (bc := bc);
      [lia | lia | lia | lia | exact HMI | prove_stable Hse | ..]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - eapply (post_scan bc); [exact HMI | prove_stable Hse | reflexivity | lia].
Qed.

Lemma M1_unch_fr : unch M M1 (fun x => inr x (sp0 - 144) 144).
Proof. unfold M1, P_IMG_END in *. solve_unch ltac:(unfold inr in *; lia). Qed.

Lemma M1_qcell : cell PSEGS M1 q 4 (W max).
Proof.
  unfold P_IMG_END in *.
  eapply cell_unch; [apply M1_unch_fr | lia | (cbn; lia) | | exact Hqc].
  intros x Hx. cbn in Hx. unfold inr in *. lia.
Qed.

(* [comment removed for export] *)
Lemma body_entry : forall l, length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 144) -> rget l 8 = W sp0 -> rget l 19 = W n ->
  rget l 10 = W p -> rget l 12 = W d -> rget l 13 = W q ->
  reach PSEGS rom (Z_to_bv 64 0x1e0718) l M1 Post.
Proof.
  intros l Hl Hse H2 H8 H19 H10 H12 H13.
  assert (HMI : MI M1) by (split; [apply unch_refl | apply mem_grows_refl]).
  pose proof M1_qcell as Cq. unfold P_IMG_END in *.
  regs_open l Hl. subst.
  wp_dec [0x1e0740; 0x1e07ac].
  eexists. split; [apply load_cell; [exact Cq | lia]|].
  rewrite (Wu max) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small max) by lia.
  rewrite lw_W by lia. rewrite ?add_W. rewrite !Wu by lia.
  split; intros Hb.
  - eapply (pre_outer 0 0); [exact HMI | prove_stable Hse | reflexivity | reflexivity | lia | lia].
  - eapply (scan_loop (Z.to_nat (n - 0)) 0 0); [lia | lia | lia | exact HMI | prove_stable Hse | ..];
      cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma decode_body : forall l, l = l0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  reach PSEGS rom (Z_to_bv 64 0x1e0688) l M Post.
Proof.
  intros l El H10 H11 H12 H13.
  assert (Hl : length l = 32%nat) by (rewrite El; exact Hl0).
  assert (Hse0 : same_except [] l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. clear El.
  pose proof Hfr as Hfr'. unfold P_IMG_END in *.
  regs_open l Hl. subst. se_subst Hse0.
  wp_dec [0x1e0718; 0x1e06d8]. mem_auto.
  rewrite slli_W by lia. rewrite ?addi_W. rewrite !Wu by lia.
  split; intros Hb; [clear Hb | exfalso; lia].
  match goal with |- reach _ _ _ _ ?Mx _ => change Mx with M1 end.
  apply body_entry; [reflexivity | | cbn [rget lget]; f_equal; lia | cbn [rget lget]; f_equal; lia
                    | reflexivity | reflexivity | reflexivity | reflexivity].
  eapply same_except_weaken with (ks := KSD); [|intros; assumption].
  intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail]|]).
  rewrite !rget_beyond by (cbn [length]; rewrite ?Hl0; lia). reflexivity.
Qed.

End Decode.

(* [comment removed for export] *)
Theorem decode_cps : forall rom Post M sp0 p n d q max l,
  0 <= n < 2 ^ 31 -> 0 <= p /\ p + n < 2 ^ 63 -> rd_ok M p n ->
  0 <= max <= 512 -> cell PSEGS M q 4 (W max) ->
  P_IMG_END <= sp0 - 144 /\ sp0 < 2 ^ 63 -> wr_ok PSEGS M (sp0 - 144) 144 ->
  P_IMG_END <= d /\ d + 4 * max < 2 ^ 63 -> wr_ok PSEGS M d (4 * max) ->
  P_IMG_END <= q /\ q + 4 < 2 ^ 63 -> wr_ok PSEGS M q 4 ->
  (d + 4 * max <= sp0 - 144 \/ sp0 <= d) -> (q + 4 <= sp0 - 144 \/ sp0 <= q) ->
  length l = 32%nat -> rget l 2 = W sp0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  (forall l' M', length l' = 32%nat -> same_except KSdec l l' ->
     (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
     (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell PSEGS M' q 4 (W w)) ->
     unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
     reach PSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0688) l M Post.
Proof.
  intros rom Post M sp0 p n d q max l; intros.
  eapply (decode_body rom Post M sp0 p n d q max) with (l0 := l); eauto.
Qed.
