(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem ULib DecArith UDecArith.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require Import UCode UImg UMemcpy UMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_dec stops := wp_go 0x215490 255%nat C_decode_eq C_decode stops.

(* [comment removed for export] *)
Definition KSdec : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition KSD : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition dec_FP (sp0 d q max : Z) (x : word) : Prop :=
  inr x (sp0 - 160) 160 \/ inr x d (4 * max) \/ inr x q 4.

Definition SAVE_SLOTS : list (nat * Z) :=
  [(1%nat, 152); (8%nat, 144); (9%nat, 136); (18%nat, 128); (19%nat, 120); (20%nat, 112); (21%nat, 104);
   (22%nat, 96); (23%nat, 88); (24%nat, 80); (25%nat, 72); (26%nat, 64); (27%nat, 56)].

Section Decode.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (sp0 p n d q max : Z).
Hypothesis Hn : 0 <= n < 2 ^ 31.
Hypothesis Hp : 0 <= p /\ p + n < 2 ^ 63.
Hypothesis Hrd : rd_ok M p n.
Hypothesis Hmax : 0 <= max <= 512.
Hypothesis Hqc : cell USEGS M q 4 (W max).
Hypothesis Hsp : U_IMG_END <= sp0 - 160 /\ sp0 < 2 ^ 63.
Hypothesis Hfr : wr_ok USEGS M (sp0 - 160) 160.
Hypothesis Hd : U_IMG_END <= d /\ d + 4 * max < 2 ^ 63.
Hypothesis Hwd : wr_ok USEGS M d (4 * max).
Hypothesis Hq : U_IMG_END <= q /\ q + 4 < 2 ^ 63.
Hypothesis Hwq : wr_ok USEGS M q 4.
Hypothesis Hdj1 : d + 4 * max <= sp0 - 160 \/ sp0 <= d.
Hypothesis Hdj2 : q + 4 <= sp0 - 160 \/ sp0 <= q.
(* [comment removed for export] *)
Hypothesis Hpnz : n = 0 \/ 0 < p.
Hypothesis Hdal : d mod 4 = 0.
Hypothesis Hqal : q mod 4 = 0.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W sp0.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSdec l0 l' ->
  (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
  (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell USEGS M' q 4 (W w)) ->
  unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
  reach USEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

(* [comment removed for export] *)
Definition M1 : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (W (sp0 + -160 + 152)) (word_to_le_bytes 8 (rget l0 1)))
    (W (sp0 + -160 + 144)) (word_to_le_bytes 8 (rget l0 8)))
    (W (sp0 + -160 + 136)) (word_to_le_bytes 8 (rget l0 9)))
    (W (sp0 + -160 + 128)) (word_to_le_bytes 8 (rget l0 18)))
    (W (sp0 + -160 + 120)) (word_to_le_bytes 8 (rget l0 19)))
    (W (sp0 + -160 + 112)) (word_to_le_bytes 8 (rget l0 20)))
    (W (sp0 + -160 + 104)) (word_to_le_bytes 8 (rget l0 21)))
    (W (sp0 + -160 + 96)) (word_to_le_bytes 8 (rget l0 22)))
    (W (sp0 + -160 + 88)) (word_to_le_bytes 8 (rget l0 23)))
    (W (sp0 + -160 + 80)) (word_to_le_bytes 8 (rget l0 24)))
    (W (sp0 + -160 + 72)) (word_to_le_bytes 8 (rget l0 25)))
    (W (sp0 + -160 + 64)) (word_to_le_bytes 8 (rget l0 26)))
    (W (sp0 + -160 + 56)) (word_to_le_bytes 8 (rget l0 27)).

(* [comment removed for export] *)
Definition FPin (x : word) : Prop := inr x (sp0 - 160) 56 \/ inr x d (4 * max) \/ inr x q 4.

Definition MI (M' : mem) : Prop := unch M1 M' FPin /\ mem_grows M1 M'.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1, U_IMG_END in *. solve_grows. Qed.

Lemma M1_unch : unch M M1 (dec_FP sp0 d q max).
Proof. unfold M1, U_IMG_END in *. solve_unch ltac:(unfold dec_FP, inr in *; lia). Qed.

Lemma M1_saved : forall k off, In (k, off) SAVE_SLOTS ->
  cell USEGS M1 (sp0 + -160 + off) 8 (rget l0 k).
Proof.
  intros k off Hin. unfold U_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Lemma MI_saved : forall M' k off, MI M' ->
  In (k, off) SAVE_SLOTS ->
  cell USEGS M' (sp0 + -160 + off) 8 (rget l0 k).
Proof.
  intros M' k off [HU HG] Hin. unfold U_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply M1_saved; exact Hin];
    unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
    try lia; intros x Hx; unfold FPin, inr in *; lia.
Qed.

Lemma MI_rd : forall M', MI M' -> rd_ok M' p n.
Proof. intros M' [_ HG]. eapply rd_ok_grows; [exact HG|]. eapply rd_ok_grows; [apply M1_grows | exact Hrd]. Qed.

Lemma MI_wr_d : forall M', MI M' -> wr_ok USEGS M' d (4 * max).
Proof. intros M' [_ HG]. eapply wr_ok_grows; [exact HG|]. eapply wr_ok_grows; [apply M1_grows | exact Hwd]. Qed.

Lemma MI_wr_q : forall M', MI M' -> wr_ok USEGS M' q 4.
Proof. intros M' [_ HG]. eapply wr_ok_grows; [exact HG|]. eapply wr_ok_grows; [apply M1_grows | exact Hwq]. Qed.

Lemma MI_wr_sp : forall M', MI M' -> wr_ok USEGS M' (sp0 - 160) 56.
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
  pose proof (MI_saved _ 1%nat 152 HMI ltac:(cbv; tauto)) as Csv1;
  pose proof (MI_saved _ 8%nat 144 HMI ltac:(cbv; tauto)) as Csv8;
  pose proof (MI_saved _ 9%nat 136 HMI ltac:(cbv; tauto)) as Csv9;
  pose proof (MI_saved _ 18%nat 128 HMI ltac:(cbv; tauto)) as Csv18;
  pose proof (MI_saved _ 19%nat 120 HMI ltac:(cbv; tauto)) as Csv19;
  pose proof (MI_saved _ 20%nat 112 HMI ltac:(cbv; tauto)) as Csv20;
  pose proof (MI_saved _ 21%nat 104 HMI ltac:(cbv; tauto)) as Csv21;
  pose proof (MI_saved _ 22%nat 96 HMI ltac:(cbv; tauto)) as Csv22;
  pose proof (MI_saved _ 23%nat 88 HMI ltac:(cbv; tauto)) as Csv23;
  pose proof (MI_saved _ 24%nat 80 HMI ltac:(cbv; tauto)) as Csv24;
  pose proof (MI_saved _ 25%nat 72 HMI ltac:(cbv; tauto)) as Csv25;
  pose proof (MI_saved _ 26%nat 64 HMI ltac:(cbv; tauto)) as Csv26;
  pose proof (MI_saved _ 27%nat 56 HMI ltac:(cbv; tauto)) as Csv27.

(* [comment removed for export] *)
Lemma epilogue : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 160) ->
  (rget l 10 = W 0 \/ rget l 10 = W 1) ->
  (rget l 10 = W 1 -> exists w, 0 <= w <= max /\ cell USEGS M' q 4 (W w)) ->
  reach USEGS rom (Z_to_bv 64 0x2154f8) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2 Ha0 Hw. pose_saved HMI. destruct (MI_final _ HMI) as [HU HG].
  unfold U_IMG_END in *. regs_open l Hl. subst sp.
  wp_dec (@nil Z). mem_auto.
  apply K; [reflexivity | | exact Ha0 | exact Hw | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fail_exit : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 160) ->
  reach USEGS rom (Z_to_bv 64 0x2154f4) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2. regs_open l Hl. subst sp.
  wp_dec [0x2154f8].
  apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E].
Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSD l0 l /\ rget l 2 = W (sp0 - 160) /\ rget l 8 = W sp0
  /\ rget l 9 = W q /\ rget l 18 = W d /\ rget l 19 = W n /\ rget l 20 = W p.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H9 & ?H18 & ?H19 & ?H20);
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

Ltac fail_leaf HMI Hse :=
  apply fail_exit; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].

(* [comment removed for export] *)
Lemma success_exit : forall l M' wo, MI M' -> stable l -> rget l 22 = W wo -> 0 <= wo <= max ->
  reach USEGS rom (Z_to_bv 64 0x21587c) l M' Post.
Proof.
  intros l M' wo HMI Hst H22 Hwo. pose_wr HMI. unfold U_IMG_END in *.
  open_stable Hst l. subst.
  wp_dec [0x2154f8]. mem_auto.
  apply epilogue; [ | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | right; reflexivity | intros _; exists wo; split; [lia | apply cell_store_same; lia] ].
  apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia |].
  intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia.
Qed.

(* [comment removed for export] *)
Definition lconst (l : regfile) : Prop :=
  rget l 7 = W n /\ rget l 28 = W max /\ rget l 24 = W 36 /\ rget l 26 = W 1 /\ rget l 1 = W (-5)
  /\ rget l 30 = W 456 /\ rget l 31 = W 1994.

(* [comment removed for export] *)
Definition Cmask (M' : mem) : Prop := cell USEGS M' (sp0 + -112) 8 (W 65535).

(* [comment removed for export] *)
Definition OI (pi wo bias : Z) (l : regfile) : Prop :=
  stable l /\ lconst l /\ rget l 23 = W pi /\ rget l 11 = W wo /\ rget l 25 = W bias
  /\ 0 <= pi < n /\ 0 <= wo <= max /\ 0 <= bias <= 300.

Ltac prove_lconst := unfold lconst; cbn [rget lget]; repeat split; reflexivity.

Section Tail.
Variables (pi' wo c df : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Hc : 0 <= c <= 7.
Hypothesis Hdf : 0 <= df <= 498.
Hypothesis Kout : forall l M' bias', MI M' -> Cmask M' -> OI pi' (wo + 1) bias' l ->
  reach USEGS rom (Z_to_bv 64 0x21567c) l M' Post.

(* [comment removed for export] *)
Lemma tail : forall l M', MI M' -> Cmask M' -> stable l -> lconst l -> rget l 23 = W pi' ->
  rget l 11 = W wo -> rget l 22 = W (wo + 1) -> rget l 13 = W (36 * c) -> rget l 14 = W df ->
  reach USEGS rom (Z_to_bv 64 0x2157bc) l M' Post.
Proof.
  intros l M' HMI HCm Hst Hlc H23 H11 H22 H13 H14. pose_wr HMI. unfold U_IMG_END, Cmask in *.
  destruct Hlc as (L7 & L28 & L24 & L26 & L1 & L30 & L31).
  open_stable Hst l. subst.
  destruct (rem_idx a2 (wo + 1) ltac:(lia)) as (r & Hr & Er).
  destruct (bias_val c df Hc Hdf) as (bv & Hbv & Ebv).
  assert (Hdr : (d + 4 * r) mod 4 = 0) by (replace (d + 4 * r) with (d + r * 4) by lia; rewrite Z_mod_plus_full; exact Hdal).
  assert (Hdr4 : (d + 4 * r + 4) mod 4 = 0) by (replace (d + 4 * r + 4) with (d + (r + 1) * 4) by lia; rewrite Z_mod_plus_full; exact Hdal).
  wp_dec [0x2154f4; 0x215888]. rewrite Er. rewrite (subw_W wo r) by lia. rewrite !scale4_W by lia.
  rewrite ?add_W, ?addi_W.
  rewrite (sltu0_W d), (sltiu1_W (d + 4 * r)) by lia.
  replace (Z.eqb d 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (d + 4 * r) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite (align_or (d + 4 * r + 4) (d + 4 * r)) by (try lia; assumption).
  change (bv_unsigned (Z_to_bv 64 (-5))) with (2 ^ 64 - 5).
  rewrite ?(Wu wo), ?(Wu max), ?(Wu d), ?(Wu (d + 4 * r)), ?(Wu 1) by lia.
  split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|]. clear Hbr.
  split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|].
  split; intros Hb2; [exfalso; lia|]. clear Hb2.
  split; intros Hb2; [exfalso; lia|]. clear Hb2.
  split; intros Hb2; [exfalso; lia|]. clear Hb2.
  split; intros Hb2; [exfalso; lia|]. clear Hb2.
  split; intros Hb2; [exfalso; lia|]. clear Hb2.
  mem_auto. rewrite Ebv.
  name_mem M2.
  assert (HMI2 : MI M2).
  { unname_mems. repeat (apply MI_store; [ | lia | rewrite length_N_to_le_bytes; lia
        | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]). exact HMI. }
  assert (HCm2 : cell USEGS M2 (sp0 + -112) 8 (W 65535)) by (unname_mems; solve_cell).
  assert (Ct2 : cell USEGS M2 (sp0 + -136) 8 (W n)) by (unname_mems; solve_cell).
  assert (Ct3 : cell USEGS M2 (sp0 + -144) 8 (W max)) by (unname_mems; solve_cell).
  assert (Ct4 : cell USEGS M2 (sp0 + -152) 8 (v_addw (v_divuw a2 (W (wo + 1))) t4)) by (unname_mems; solve_cell).
  assert (Cr : cell USEGS M2 (sp0 + -160) 8 (W r)) by (unname_mems; solve_cell).
  clearbody M2. clear Hrd' Hwd' Hwq' Hwsp' HCm. pose_wr HMI2.
  replace (Z_to_bv 64 2870512) with (Z_to_bv 64 0x2bccf0) by reflexivity.
  eapply (memmove_cps rom Post M2 (d + 4 * r + 4) (d + 4 * r) (4 * (wo - r)));
    [ lia | lia | lia | replace (d + 4 * r + 4 - (d + 4 * r)) with 4 by lia; discriminate | lia
    | eapply rd_ok_sub; [apply (wr_ok_rd_ok M2 d (4 * max) Hwd'); unfold U_IMG_END; lia | lia | lia]
    | eapply wr_ok_sub; [exact Hwd' | lia | lia]
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 2185296) 0) with (Z_to_bv 64 0x215850) by reflexivity.
  regs_open l'' Hl''. se_subst Hse''. clear Hse''.
  assert (HMI3 : MI M'').
  { destruct HMI2 as [HU2 HG2]. split; [|eapply mem_grows_trans; eassumption].
    eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU''|].
    intros x Hx. unfold UMemmove.FP, FPin, inr in *. lia. }
  assert (HCm3 : cell USEGS M'' (sp0 + -112) 8 (W 65535)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemmove.FP, inr in *; lia | exact HCm2]. }
  assert (Ct2' : cell USEGS M'' (sp0 + -136) 8 (W n)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemmove.FP, inr in *; lia | exact Ct2]. }
  assert (Ct3' : cell USEGS M'' (sp0 + -144) 8 (W max)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemmove.FP, inr in *; lia | exact Ct3]. }
  assert (Ct4' : cell USEGS M'' (sp0 + -152) 8 (v_addw (v_divuw a2 (W (wo + 1))) t4)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemmove.FP, inr in *; lia | exact Ct4]. }
  assert (Cr' : cell USEGS M'' (sp0 + -160) 8 (W r)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold UMemmove.FP, inr in *; lia | exact Cr]. }
  clear HCm2 Ct2 Ct3 Ct4 Cr Hrd' Hwd' Hwq' Hwsp'. pose_wr HMI3.
  wp_dec [0x21567c; 0x21587c]. mem_auto. rewrite ?(Wu pi'), ?(Wu n) by lia.
  assert (HMI4 : MI (wbytes M'' (W (d + 4 * r)) (word_to_le_bytes 4 (v_addw (v_divuw a2 (W (wo + 1))) t4)))).
  { apply MI_store; [exact HMI3 | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia. }
  split; intros Hb2.
  - apply (Kout _ _ bv); [exact HMI4 | unfold Cmask; solve_cell |].
    unfold OI. split; [prove_stable Hse|]. split; [prove_lconst|]. cbn [rget lget].
    repeat split; try reflexivity; lia.
  - eapply (success_exit _ _ (wo + 1)); [exact HMI4 | prove_stable Hse | reflexivity | lia].
Qed.
End Tail.

(* [comment removed for export] *)
Definition BI (s7v wo : Z) (l : regfile) : Prop :=
  stable l /\ lconst l /\ rget l 11 = W wo /\ rget l 23 = W s7v.

Ltac open_BI H l :=
  let Hst := fresh "Hst" in let Hlc := fresh "Hlc" in
  destruct H as (Hst & Hlc & ?H11 & ?H23);
  destruct Hlc as (?L7 & ?L28 & ?L24 & ?L26 & ?L1 & ?L30 & ?L31);
  open_stable Hst l.

Ltac prove_BI Hse :=
  unfold BI; split; [prove_stable Hse|]; split; [prove_lconst|]; cbn [rget lget]; repeat split; try reflexivity.

(* [comment removed for export] *)
Definition cap (c : nat) : Z :=
  match c with
  | 0%nat => 4294967296 | 1%nat => 134217728 | 2%nat => 4194304 | 3%nat => 131072 | 4%nat => 4096
  | 5%nat => 128 | 6%nat => 4 | _ => 1
  end.

Section Adapt.
Variables (pi' wo : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Ktail : forall c df l M', 0 <= c <= 7 -> 0 <= df <= 498 -> MI M' -> Cmask M' -> stable l -> lconst l ->
  rget l 23 = W pi' -> rget l 11 = W wo -> rget l 22 = W (wo + 1) -> rget l 13 = W (36 * c) -> rget l 14 = W df ->
  reach USEGS rom (Z_to_bv 64 0x2157bc) l M' Post.

Lemma spill_rd : forall M', MI M' -> rd_ok M' (sp0 - 160) 56.
Proof.
  intros M' HMI. apply (wr_ok_rd_ok M' (sp0 - 160) 56 (MI_wr_sp _ HMI)); unfold U_IMG_END in *; lia.
Qed.

(* [comment removed for export] *)
Lemma adapt_loop : forall k (cN : nat) l M', (7 - Z.of_nat cN = Z.of_nat k) -> (cN <= 6)%nat ->
  bv_unsigned (rget l 10) mod 2 ^ 32 < cap cN ->
  MI M' -> Cmask M' -> BI pi' wo l -> rget l 22 = W (wo + 1) -> rget l 13 = W (36 * Z.of_nat cN) ->
  reach USEGS rom (Z_to_bv 64 0x215790) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros cN l M' Hk HcN6 Hcap HMI HCm HBI H22 H13.
  open_BI HBI l. subst. cbn [rget lget] in Hcap.
  wp_dec [0x215790; 0x2157bc]. rewrite ?addi_W.
  destruct (adapt_bound a0 a6) as (nv & Hnv0 & Hnv & Env). rewrite Env.
  pose proof (Z.mod_pos_bound (bv_unsigned a0) (2 ^ 32) ltac:(lia)) as Hdlb.
  split; intros Hbr.
  - apply (adapt_continue a0 1994 ltac:(lia)) in Hbr.
    assert (HcN : (cN <= 5)%nat).
    { destruct cN as [|[|[|[|[|[|cN]]]]]]; try lia. exfalso. cbn [cap] in Hcap.
      destruct cN; cbn [cap] in Hcap; lia. }
    eapply (IH (Z.to_nat (7 - Z.of_nat (S cN)))) with (cN := S cN);
      [ lia | lia | lia | | exact HMI | exact HCm | prove_BI Hse | reflexivity | cbn [rget lget]; f_equal; lia ].
    cbn [rget lget]. rewrite Wu by lia. rewrite Z.mod_small by lia.
    destruct cN as [|[|[|[|[|[|cN]]]]]]; cbn [cap] in *; lia.
  - apply (adapt_stop a0 1994 ltac:(lia)) in Hbr.
    apply (Ktail (Z.of_nat cN + 1) nv); [lia | lia | exact HMI | exact HCm | prove_stable Hse | prove_lconst
      | reflexivity | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma brk : forall l M', MI M' -> Cmask M' -> BI pi' wo l -> reach USEGS rom (Z_to_bv 64 0x215750) l M' Post.
Proof.
  intros l M' HMI HCm HBI. pose proof (spill_rd _ HMI) as Hsr. unfold U_IMG_END in *.
  open_BI HBI l. subst.
  assert (Es6 : v_addiw (W wo) 1 = W (wo + 1)) by (apply addiw_W; lia).
  wp_dec [0x215790; 0x2157bc; 0x215888]. rewrite ?Es6, ?addi_W. rewrite ?(Wu (wo + 1)), ?(Wu 456) by lia.
  split; intros Hbr; clear Hbr.
  - (* [comment removed for export] *)
    assert (exists v, load_ok USEGS M' (W (sp0 + -128)) 8 v) as [v Hv] by (eapply load_rd; [exact Hsr | lia..]).
    exists v. split; [exact Hv|]. clear Hv.
    split; intros Hbr; [exfalso; lia|]. clear Hbr.
    split; intros Hbr.
    + match type of Hbr with bv_unsigned ?X < _ =>
        eapply (Ktail 0 (bv_unsigned X)); [lia | pose proof (u64_range X); lia
        | exact HMI | exact HCm | prove_stable Hse | prove_lconst | reflexivity | reflexivity | reflexivity | reflexivity
        | cbn [rget lget]; symmetry; apply W_u ] end.
    + clear Hbr.
      assert (exists v2, load_ok USEGS M' (W (sp0 + -120)) 8 v2) as [v2 Hv2] by (eapply load_rd; [exact Hsr | lia..]).
      exists v2. split; [exact Hv2|]. clear Hv2.
      eapply (adapt_loop 7 0%nat); [reflexivity | lia | | exact HMI | exact HCm | prove_BI Hse | reflexivity | reflexivity].
      cbn [rget lget cap]. apply Z.mod_pos_bound. lia.
  - split; intros Hbr; [exfalso; lia|]. clear Hbr.
    split; intros Hbr.
    + match type of Hbr with bv_unsigned ?X < _ =>
        eapply (Ktail 0 (bv_unsigned X)); [lia | pose proof (u64_range X); lia
        | exact HMI | exact HCm | prove_stable Hse | prove_lconst | reflexivity | reflexivity | reflexivity | reflexivity
        | cbn [rget lget]; symmetry; apply W_u ] end.
    + clear Hbr.
      assert (exists v2, load_ok USEGS M' (W (sp0 + -120)) 8 v2) as [v2 Hv2] by (eapply load_rd; [exact Hsr | lia..]).
      exists v2. split; [exact Hv2|]. clear Hv2.
      eapply (adapt_loop 7 0%nat); [reflexivity | lia | | exact HMI | exact HCm | prove_BI Hse | reflexivity | reflexivity].
      cbn [rget lget cap]. apply Z.mod_pos_bound. lia.
Qed.

End Adapt.

(* [comment removed for export] *)
Definition capw (j : nat) : Z :=
  match j with
  | 0%nat => 1 | 1%nat => 10 | 2%nat => 100 | 3%nat => 1000 | 4%nat => 10000 | 5%nat => 100000
  | 6%nat => 1000000 | 7%nat => 10000000 | 8%nat => 100000000 | 9%nat => 1000000000 | _ => 4294967296
  end.

Lemma capw_step : forall (j : nat) x w, (j <= 8)%nat -> 10 <= x -> capw j <= w -> capw (S j) <= x * w.
Proof.
  intros j x w Hj Hx Hw. do 9 (destruct j as [|j]; [cbn [capw] in *; nia|]). lia.
Qed.

Section Digits.
Variables (wo lo bias : Z).
Hypothesis Hlo : 0 <= lo.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Hbias : 0 <= bias <= 300.
Hypothesis Kbrk : forall s7v l M', lo < s7v <= n -> MI M' -> Cmask M' -> BI s7v wo l ->
  reach USEGS rom (Z_to_bv 64 0x215750) l M' Post.

(* [comment removed for export] *)
Definition DR (jN : nat) (wv : Z) (l : regfile) : Prop :=
  rget l 25 = W bias /\ rget l 13 = W (bias + 26) /\ rget l 14 = v_subw (W 0) (W bias)
  /\ rget l 16 = W (36 * (Z.of_nat jN + 1)) /\ bv_unsigned (rget l 15) mod 2 ^ 32 = wv
  /\ capw jN <= wv /\ (jN <= 9)%nat.

Section Iter.
Variables (idx : Z) (jN : nat) (wv : Z).
Hypothesis Hidx : lo <= idx < n.
Hypothesis Kd1 : forall wv' l M', idx + 1 < n -> MI M' -> Cmask M' -> BI (idx + 2) wo l -> DR (S jN) wv' l ->
  rget l 17 = W (idx + 1) -> reach USEGS rom (Z_to_bv 64 0x2156a0) l M' Post.

Lemma capw_pos : forall j, 1 <= capw j.
Proof. intros j. do 10 (destruct j as [|j]; [cbn; lia|]). cbn. lia. Qed.

(* [comment removed for export] *)
Lemma d3 : forall l M' t, MI M' -> Cmask M' -> BI (idx + 1) wo l -> DR jN wv l -> rget l 5 = W t -> 1 <= t <= 26 ->
  reach USEGS rom (Z_to_bv 64 0x21570c) l M' Post.
Proof.
  intros l M' t HMI HCm HBI HDR H5 Ht. destruct HDR as (D25 & D13 & D14 & D16 & D15 & Dcap & Dj).
  revert D15 Dcap. open_BI HBI l. subst. intros D15 Dcap. cbn [rget lget] in D15.
  wp_dec [0x2154f4; 0x215750; 0x2156a0; 0x215888].
  rewrite (subw_W 36 t) by lia. rewrite zext32_W by lia. rewrite ?(Wu t), ?(Wu 36), ?(Wu (idx + 1)), ?(Wu n) by lia.
  split; intros Hbr; clear Hbr.
  - apply (Kbrk (idx + 1)); [lia | exact HMI | exact HCm | prove_BI Hse].
  - split; intros Hbr; [exfalso; lia|]. clear Hbr.
    split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|].
    destruct (w_step a5 (36 - t) wv D15 ltac:(lia) Hbr) as [Ew Hlt]. clear Hbr.
    split; intros Hbr; [fail_leaf HMI Hse|].
    rewrite !addiw_W by lia.
    assert (Hj8 : (jN <= 8)%nat).
    { destruct (Nat.le_gt_cases jN 8) as [Hle|Hgt]; [exact Hle|]. exfalso.
      assert (jN = 9%nat) by lia. subst jN. cbn [capw] in Dcap. nia. }
    apply (Kd1 ((36 - t) * wv)); [lia | exact HMI | exact HCm | prove_BI Hse; f_equal; lia | | reflexivity].
    unfold DR. cbn [rget lget]. repeat split; try reflexivity.
    + f_equal. lia.
    + exact Ew.
    + apply capw_step; [exact Hj8 | lia | exact Dcap].
    + lia.
Qed.

(* [comment removed for export] *)
Lemma d2 : forall l M', MI M' -> Cmask M' -> BI (idx + 1) wo l -> DR jN wv l ->
  reach USEGS rom (Z_to_bv 64 0x2156dc) l M' Post.
Proof.
  intros l M' HMI HCm HBI HDR. pose proof HDR as (D25 & D13 & D14 & D16 & D15 & Dcap & Dj).
  pose proof (capw_pos jN) as Hcp.
  assert (HDR' : forall l', rget l' 25 = rget l 25 -> rget l' 13 = rget l 13 -> rget l' 14 = rget l 14 ->
             rget l' 16 = rget l 16 -> rget l' 15 = rget l 15 -> DR jN wv l').
  { intros l' E25 E13 E14 E16 E15. unfold DR. rewrite E25, E13, E14, E16, E15. exact HDR. }
  clear HDR. revert D15 Dcap HDR'. open_BI HBI l. subst. intros D15 Dcap HDR'. cbn [rget lget] in D15, HDR'.
  assert (Hkk : 0 <= 36 * (Z.of_nat jN + 1) <= 360) by lia.
  wp_dec [0x2154f4; 0x21570c; 0x215888].
  rewrite (t_mid bias (36 * (Z.of_nat jN + 1))) by lia.
  rewrite ?(Wu (36 * (Z.of_nat jN + 1))), ?(Wu (bias + 26)), ?(Wu bias) by lia.
  split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|]. clear Hbr.
  split; intros Hbr.
  { exfalso. rewrite Hbr in D15. change (0 mod 2 ^ 32) with 0 in D15. lia. }
  clear Hbr.
  split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|]. clear Hbr.
  split; intros Hb1.
  - split; intros Hb2.
    + eapply (d3 _ _ (36 * (Z.of_nat jN + 1) - bias)); [exact HMI | exact HCm | prove_BI Hse | apply HDR'; reflexivity | reflexivity | lia].
    + eapply (d3 _ _ 1); [exact HMI | exact HCm | prove_BI Hse | apply HDR'; reflexivity | reflexivity | lia].
  - split; intros Hb2.
    + eapply (d3 _ _ 1); [exact HMI | exact HCm | prove_BI Hse | apply HDR'; reflexivity | reflexivity | lia].
    + eapply (d3 _ _ 26); [exact HMI | exact HCm | prove_BI Hse | apply HDR'; reflexivity | reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma d1 : forall l M', MI M' -> Cmask M' -> BI (idx + 1) wo l -> DR jN wv l -> rget l 17 = W idx ->
  reach USEGS rom (Z_to_bv 64 0x2156a0) l M' Post.
Proof.
  intros l M' HMI HCm HBI HDR H17. pose_wr HMI.
  assert (HDR' : forall l', rget l' 25 = rget l 25 -> rget l' 13 = rget l 13 -> rget l' 14 = rget l 14 ->
             rget l' 16 = rget l 16 -> rget l' 15 = rget l 15 -> DR jN wv l').
  { intros l' E25 E13 E14 E16 E15. unfold DR. rewrite E25, E13, E14, E16, E15. exact HDR. }
  clear HDR. revert HDR'. open_BI HBI l. subst. intros HDR'. cbn [rget lget] in HDR'.
  assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
  wp_dec [0x2154f4; 0x2156dc; 0x215888]. rewrite ?add_W.
  rewrite (sltiu1_W (p + idx)) by lia.
  replace (Z.eqb (p + idx) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite ?(Wu (p + idx)), ?(Wu p), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  assert (exists v, load_ok USEGS M' (W (p + idx)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  repeat (split; intros ?Hbr);
    first [ fail_leaf HMI Hse | apply d2; [exact HMI | exact HCm | prove_BI Hse | apply HDR'; reflexivity] ].
Qed.
End Iter.

Lemma digit_loop : forall k idx jN wv l M', n - idx = Z.of_nat k -> lo <= idx < n ->
  MI M' -> Cmask M' -> BI (idx + 1) wo l -> DR jN wv l -> rget l 17 = W idx ->
  reach USEGS rom (Z_to_bv 64 0x2156a0) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros idx jN wv l M' Hk Hidx HMI HCm HBI HDR H17.
  apply (d1 idx jN wv Hidx); try assumption.
  intros wv' l2 M2 Hlt HMI2 HCm2 HBI2 HDR2 H17'.
  eapply (IH (Z.to_nat (n - (idx + 1)))) with (idx := idx + 1) (jN := S jN) (wv := wv'); try eassumption; try lia.
  replace (idx + 1 + 1) with (idx + 2) by lia. exact HBI2.
Qed.
End Digits.

(* [comment removed for export] *)
Lemma outer_loop : forall k pi wo bias l M', n - pi = Z.of_nat k -> MI M' -> Cmask M' -> OI pi wo bias l ->
  reach USEGS rom (Z_to_bv 64 0x21567c) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros pi wo bias l M' Hk HMI HCm HOI.
  destruct HOI as (Hst & Hlc & H23 & H11 & H25 & Hpi & Hwo & Hbias).
  destruct Hlc as (L7 & L28 & L24 & L26 & L1 & L30 & L31).
  open_stable Hst l. subst.
  wp_dec [0x2154f4; 0x2156a0]. rewrite zext32_W by lia. rewrite ?(Wu pi), ?(Wu n) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr. rewrite !addiw_W by lia.
  eapply digit_loop with (wo := wo) (lo := pi) (bias := bias) (idx := pi) (jN := 0%nat) (wv := 1) (k := Z.to_nat (n - pi));
    [ lia | lia | | lia | lia | exact HMI | exact HCm | prove_BI Hse | | reflexivity ].
  - (* [comment removed for export] *)
    intros s7v l2 M2 Hs7 HMI2 HCm2 HBI2.
    eapply brk with (pi' := s7v) (wo := wo); [lia | | exact HMI2 | exact HCm2 | exact HBI2].
    intros c df l3 M3 Hc Hdf HMI3 HCm3 Hst3 Hlc3 H23' H11' H22' H13' H14'.
    eapply tail with (pi' := s7v) (wo := wo) (c := c) (df := df); try assumption; try lia.
    intros l4 M4 bias4 HMI4 HCm4 HOI4.
    eapply (IH (Z.to_nat (n - s7v))); [lia | | exact HMI4 | exact HCm4 | exact HOI4]. lia.
  - unfold DR. cbn [rget lget]. repeat split; try reflexivity; cbn [capw]; lia.
Qed.

(* [comment removed for export] *)
Lemma pre_outer : forall pi wo l M', MI M' -> stable l -> rget l 23 = W pi -> rget l 22 = W wo ->
  rget l 10 = W max -> 0 <= pi <= n -> 0 <= wo <= max ->
  reach USEGS rom (Z_to_bv 64 0x215614) l M' Post.
Proof.
  intros pi wo l M' HMI Hst H23 H22 H10 Hpi Hwo. pose_wr HMI. unfold U_IMG_END in *.
  open_stable Hst l. subst.
  wp_dec [0x21567c; 0x21587c]. rewrite addiw_W by lia. replace (n + 0) with n by lia.
  rewrite ?(Wu pi), ?(Wu n), ?(Wu wo), ?(Wu max) by lia.
  split; intros Hbr.
  - eapply (success_exit _ _ wo); [exact HMI | prove_stable Hse | reflexivity | lia].
  - assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
    rewrite (sltu0_W p) by lia. replace (Z.eqb p 0) with false by (symmetry; apply Z.eqb_neq; lia).
    split; intros Hb2; [exfalso; lia|]. clear Hb2.
    mem_auto. rewrite ?slli_W by lia. mem_auto.
    eapply (outer_loop (Z.to_nat (n - pi)) pi wo 72); [lia | | | ].
    + repeat (apply MI_store; [ | lia | rewrite length_N_to_le_bytes; lia
        | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]). exact HMI.
    + unfold Cmask. solve_cell.
    + unfold OI. split; [prove_stable Hse|]. split; [prove_lconst|]. cbn [rget lget].
      repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma copy_loop : forall k j bc l M', bc - j = Z.of_nat k -> 0 <= j < bc -> bc <= max -> bc < n ->
  MI M' -> stable l -> rget l 22 = W bc -> rget l 10 = W max ->
  rget l 11 = W j -> rget l 13 = W bc -> rget l 14 = v_xori (W p) (-1) -> rget l 12 = W 1 -> rget l 15 = W 1 ->
  rget l 16 = W (d + 4 * j) -> rget l 17 = W (d + 4 * j) ->
  reach USEGS rom (Z_to_bv 64 0x2155c8) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros j bc l M' Hk Hj Hbm Hbn HMI Hst H22 H10 H11 H13 H14 H12 H15 H16 H17.
  pose_wr HMI. unfold U_IMG_END in *. open_stable Hst l. subst.
  wp_dec [0x2155c8; 0x2154f4; 0x215614; 0x215888]. rewrite ?add_W.
  rewrite (u_not p) by lia. rewrite (sltiu1_W (d + 4 * j)) by lia.
  replace (Z.eqb (d + 4 * j) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite ?(Wu j), ?(Wu (d + 4 * j)), ?(Wu d), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  assert (exists v, load_ok USEGS M' (W (p + j)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  split; intros Hbr; clear Hbr; [fail_leaf HMI Hse|].
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; [eapply wr_ok_store; [exact Hwd' | lia | lia]|].
  rewrite ?addi_W. rewrite ?(Wu bc), ?(Wu (j + 1)) by lia.
  match goal with |- context [wbytes M' ?a ?bs] => 
    assert (HMI2 : MI (wbytes M' a bs))
      by (apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia
                          | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]) end.
  split; intros Hbr.
  - eapply (IH (Z.to_nat (bc - (j + 1)))) with (j := j + 1) (bc := bc);
      [lia | lia | lia | lia | lia | exact HMI2 | prove_stable Hse | reflexivity | reflexivity | ..];
      cbn [rget lget]; try reflexivity; f_equal; lia.
  - rewrite addiw_W by lia.
    eapply (pre_outer (bc + 1) bc); [exact HMI2 | prove_stable Hse | reflexivity | reflexivity | reflexivity | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma post_scan : forall bc l M', MI M' -> stable l -> rget l 22 = W bc -> rget l 10 = W max ->
  bc = 0 \/ 0 < bc < n ->
  reach USEGS rom (Z_to_bv 64 0x215598) l M' Post.
Proof.
  intros bc l M' HMI Hst H22 H10 Hbc. unfold U_IMG_END in *. open_stable Hst l. subst.
  assert (Ean : v_andi (W d) 3 = W 0).
  { rewrite <- (W_u (v_andi (W d) 3)). f_equal. change 3 with (Z.ones 2). rewrite u_andi_ones_W by lia. exact Hdal. }
  wp_dec [0x2155c8; 0x2154f4; 0x215614]. rewrite Ean.
  rewrite (sltiu1_W 0), (sltu0_W d) by lia.
  replace (Z.eqb d 0) with false by (symmetry; apply Z.eqb_neq; lia). change (Z.eqb 0 0) with true. cbv beta iota.
  rewrite (and_W 1 1) by lia. change (Z.land 1 1) with 1.
  rewrite ?(Wu bc), ?(Wu max) by lia.
  split; intros Hbr.
  - eapply (pre_outer 0 bc); [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity | lia | lia].
  - split; intros Hb2; [fail_leaf HMI Hse|].
    rewrite zext32_W by lia.
    eapply (copy_loop (Z.to_nat (bc - 0)) 0 bc); [lia | lia | lia | lia | exact HMI | prove_stable Hse | reflexivity | reflexivity | ..];
      cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma scan_loop : forall m k bc l M', n - k = Z.of_nat m -> 0 <= k < n -> bc = 0 \/ 0 < bc < k ->
  MI M' -> stable l -> rget l 10 = W max ->
  rget l 11 = W k -> rget l 12 = W 1 -> rget l 14 = W (n - k) -> rget l 15 = W (p + k) -> rget l 16 = W (p + k) ->
  rget l 17 = W bc ->
  reach USEGS rom (Z_to_bv 64 0x21555c) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros k bc l M' Hm Hk Hbc HMI Hst H10 H11 H12 H14 H15 H16 H17.
  pose_wr HMI. open_stable Hst l. subst.
  assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
  wp_dec [0x21555c; 0x215598; 0x215888].
  rewrite (sltiu1_W (p + k)) by lia. replace (Z.eqb (p + k) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite ?(Wu (p + k)), ?(Wu p), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  assert (exists v, load_ok USEGS M' (W (p + k)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  rewrite ?addi_W. rewrite addiw_W by lia. rewrite ?(Wu (n - k + -1)) by lia.
  split; intros Hbr; clear Hbr; (split; intros Hbr).
  - eapply (IH (Z.to_nat (n - (k + 1)))) with (k := k + 1) (bc := k);
      [lia | lia | lia | lia | exact HMI | prove_stable Hse | reflexivity | ..]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - eapply (post_scan k); [exact HMI | prove_stable Hse | reflexivity | reflexivity | lia].
  - eapply (IH (Z.to_nat (n - (k + 1)))) with (k := k + 1) (bc := bc);
      [lia | lia | lia | lia | exact HMI | prove_stable Hse | reflexivity | ..]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - eapply (post_scan bc); [exact HMI | prove_stable Hse | reflexivity | reflexivity | lia].
Qed.

Lemma M1_unch_fr : unch M M1 (fun x => inr x (sp0 - 160) 160).
Proof. unfold M1, U_IMG_END in *. solve_unch ltac:(unfold inr in *; lia). Qed.

Lemma M1_qcell : cell USEGS M1 q 4 (W max).
Proof.
  unfold U_IMG_END in *.
  eapply cell_unch; [apply M1_unch_fr | lia | (cbn; lia) | | exact Hqc].
  intros x Hx. cbn in Hx. unfold inr in *. lia.
Qed.

(* [comment removed for export] *)
Lemma body_entry : forall l, length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 160) -> rget l 8 = W sp0 -> rget l 9 = W q -> rget l 19 = W n -> rget l 20 = W p ->
  rget l 12 = W d ->
  reach USEGS rom (Z_to_bv 64 0x215534) l M1 Post.
Proof.
  intros l Hl Hse H2 H8 H9 H19 H20 H12.
  assert (HMI : MI M1) by (split; [apply unch_refl | apply mem_grows_refl]).
  pose proof M1_qcell as Cq. unfold U_IMG_END in *.
  regs_open l Hl. subst.
  wp_dec [0x21555c; 0x215614].
  eexists. split; [apply load_cell; [exact Cq | lia]|].
  rewrite (Wu max) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small max) by lia.
  rewrite lw_W by lia. rewrite ?(Wu n) by lia.
  split; intros Hbr.
  - eapply (pre_outer 0 0); [exact HMI | prove_stable Hse | reflexivity | reflexivity | reflexivity | lia | lia].
  - assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
    rewrite (sltu0_W p) by lia. replace (Z.eqb p 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota.
    eapply (scan_loop (Z.to_nat (n - 0)) 0 0); [lia | lia | lia | exact HMI | prove_stable Hse | reflexivity | ..];
      cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma decode_body : forall l, l = l0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  reach USEGS rom (Z_to_bv 64 0x215490) l M Post.
Proof.
  intros l El H10 H11 H12 H13.
  assert (Hl : length l = 32%nat) by (rewrite El; exact Hl0).
  assert (Hse0 : same_except [] l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. clear El.
  pose proof Hfr as Hfr'. unfold U_IMG_END in *.
  regs_open l Hl. subst. se_subst Hse0.
  wp_dec [0x215534; 0x2154f4; 0x215888]. mem_auto.
  rewrite slli_W by lia. rewrite ?addi_W.
  change 3 with (Z.ones 2). rewrite u_andi_ones_W by lia. change (2 ^ 2) with 4. rewrite Hqal.
  rewrite ?(Wu q), ?(Wu n), ?(Wu (1 * 2 ^ 32 + -2)) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; apply Hbr; reflexivity|]. clear Hbr.
  split; intros Hbr; [clear Hbr | exfalso; lia].
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
  0 <= max <= 512 -> cell USEGS M q 4 (W max) ->
  U_IMG_END <= sp0 - 160 /\ sp0 < 2 ^ 63 -> wr_ok USEGS M (sp0 - 160) 160 ->
  U_IMG_END <= d /\ d + 4 * max < 2 ^ 63 -> wr_ok USEGS M d (4 * max) ->
  U_IMG_END <= q /\ q + 4 < 2 ^ 63 -> wr_ok USEGS M q 4 ->
  (d + 4 * max <= sp0 - 160 \/ sp0 <= d) -> (q + 4 <= sp0 - 160 \/ sp0 <= q) ->
  (n = 0 \/ 0 < p) -> d mod 4 = 0 -> q mod 4 = 0 ->
  length l = 32%nat -> rget l 2 = W sp0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  (forall l' M', length l' = 32%nat -> same_except KSdec l l' ->
     (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
     (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell USEGS M' q 4 (W w)) ->
     unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
     reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x215490) l M Post.
Proof.
  intros rom Post M sp0 p n d q max l; intros.
  eapply (decode_body rom Post M sp0 p n d q max) with (l0 := l); eauto.
Qed.
