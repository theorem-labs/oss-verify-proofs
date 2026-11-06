(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem DecArith ULib UDecArith.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ACheck ASaves.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BImg BAsanMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_dec stops := wp_go 0x430dbc 334%nat C_decode_eq C_decode stops.

(* [comment removed for export] *)
Definition KSdec : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition KSD : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition DEC_STK : Z := 2400.

Definition dec_FP (sp0 d q max : Z) (x : word) : Prop :=
  inr x (sp0 - 2400) 2400 \/ inr x d (4 * max) \/ inr x q 4.

Definition SAVE_SLOTS : list (nat * Z) :=
  [(1%nat, 168); (8%nat, 160); (9%nat, 152); (18%nat, 144); (19%nat, 136); (20%nat, 128); (21%nat, 120);
   (22%nat, 112); (23%nat, 104); (24%nat, 96); (25%nat, 88); (26%nat, 80); (27%nat, 72)].

Section Decode.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (sp0 p n d q max : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hn : 0 <= n < 2 ^ 31.
Hypothesis Hmp : memrange p n.
Hypothesis Hokp : addr_ok M p n.
Hypothesis Hrd : rd_ok M p n.
Hypothesis Hmax : 0 <= max <= 512.
Hypothesis Hqc : cell BSEGS M q 4 (W max).
Hypothesis Hsp : B_IMG_END <= sp0 - 2400 /\ sp0 < 2 ^ 63.
Hypothesis Hspz : sp0 <= SB \/ HIMEM_BEG <= sp0 - 2400.
Hypothesis Hfr : wr_ok BSEGS M (sp0 - 2400) 2400.
Hypothesis Hd : B_IMG_END <= d.
Hypothesis Hmd : memrange d (4 * max).
Hypothesis Hokd : addr_ok M d (4 * max).
Hypothesis Hshd : 0 < max -> shw_ok M d (4 * max).
Hypothesis Hwd : wr_ok BSEGS M d (4 * max).
Hypothesis Hq : B_IMG_END <= q.
Hypothesis Hmq : memrange q 4.
Hypothesis Hokq : addr_ok M q 4.
Hypothesis Hwq : wr_ok BSEGS M q 4.
Hypothesis Hdj1 : d + 4 * max <= sp0 - 2400 \/ sp0 <= d.
Hypothesis Hdj2 : q + 4 <= sp0 - 2400 \/ sp0 <= q.
(* [comment removed for export] *)
Hypothesis Hpnz : n = 0 \/ 0 < p.
Hypothesis Hdal : d mod 4 = 0.
Hypothesis Hqal : q mod 4 = 0.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W sp0.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSdec l0 l' ->
  (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
  (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell BSEGS M' q 4 (W w)) ->
  unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

(* [comment removed for export] *)
Definition M1 : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (W (sp0 + -176 + 168)) (word_to_le_bytes 8 (rget l0 1)))
    (W (sp0 + -176 + 160)) (word_to_le_bytes 8 (rget l0 8)))
    (W (sp0 + -176 + 152)) (word_to_le_bytes 8 (rget l0 9)))
    (W (sp0 + -176 + 144)) (word_to_le_bytes 8 (rget l0 18)))
    (W (sp0 + -176 + 136)) (word_to_le_bytes 8 (rget l0 19)))
    (W (sp0 + -176 + 128)) (word_to_le_bytes 8 (rget l0 20)))
    (W (sp0 + -176 + 120)) (word_to_le_bytes 8 (rget l0 21)))
    (W (sp0 + -176 + 112)) (word_to_le_bytes 8 (rget l0 22)))
    (W (sp0 + -176 + 104)) (word_to_le_bytes 8 (rget l0 23)))
    (W (sp0 + -176 + 96)) (word_to_le_bytes 8 (rget l0 24)))
    (W (sp0 + -176 + 88)) (word_to_le_bytes 8 (rget l0 25)))
    (W (sp0 + -176 + 80)) (word_to_le_bytes 8 (rget l0 26)))
    (W (sp0 + -176 + 72)) (word_to_le_bytes 8 (rget l0 27)).

(* [comment removed for export] *)
Definition FPin (x : word) : Prop := inr x (sp0 - 2400) 2296 \/ inr x d (4 * max) \/ inr x q 4.

Definition MI (M' : mem) : Prop := unch M1 M' FPin /\ mem_grows M1 M'.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1, B_IMG_END in *. solve_grows. Qed.

Lemma M1_unch : unch M M1 (dec_FP sp0 d q max).
Proof. unfold M1, B_IMG_END in *. solve_unch ltac:(unfold dec_FP, inr in *; lia). Qed.

Lemma M1_unch_fr : unch M M1 (fun x => inr x (sp0 - 104) 104).
Proof. unfold M1, B_IMG_END in *. solve_unch ltac:(unfold inr in *; lia). Qed.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma M1_saved : forall k off, In (k, off) SAVE_SLOTS ->
  cell BSEGS M1 (sp0 + -176 + off) 8 (rget l0 k).
Proof.
  intros k off Hin. unfold B_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Lemma MI_saved : forall M' k off, MI M' ->
  In (k, off) SAVE_SLOTS ->
  cell BSEGS M' (sp0 + -176 + off) 8 (rget l0 k).
Proof.
  intros M' k off [HU HG] Hin. unfold B_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply M1_saved; exact Hin];
    unfold SAVE_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]); try contradiction;
    try lia; intros x Hx; unfold FPin, inr in *; lia.
Qed.

(* [comment removed for export] *)
Lemma bounds : 0 <= p /\ p + n + 8 <= HIMEM_END /\ 0 <= d /\ d + 4 * max + 8 <= HIMEM_END /\ 0 <= q /\ q + 12 <= HIMEM_END.
Proof.
  destruct Hmp as [_ Hp']. destruct Hmd as [_ Hd']. destruct Hmq as [_ Hq'].
  unfold LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia.
Qed.

Lemma FP_app : forall y, dec_FP sp0 d q max y -> B_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold dec_FP, inr, B_IMG_END in *. lia. Qed.

Lemma FP_nosh : forall y, dec_FP sp0 d q max y -> ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof.
  intros y Hy. destruct Hmd as [_ Hd']. destruct Hmq as [_ Hq'].
  unfold dec_FP, inr, SB, LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia.
Qed.

Lemma MI_final : forall M', MI M' -> unch M M' (dec_FP sp0 d q max) /\ mem_grows M M'.
Proof.
  intros M' [HU HG]. split.
  - eapply unch_trans; [apply M1_unch|]. eapply unch_weaken; [exact HU|].
    intros x Hx. unfold FPin, dec_FP, inr in *. lia.
  - eapply mem_grows_trans; [apply M1_grows | exact HG].
Qed.

Lemma MI_rt : forall M', MI M' -> rt_ok M'.
Proof. intros M' HMI. destruct (MI_final _ HMI) as [HU _]. eapply rt_ok_unch; [exact HU | apply FP_app | exact Hrt]. Qed.

Lemma MI_okp : forall M', MI M' -> addr_ok M' p n.
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _]. pose proof bounds as B.
  eapply addr_ok_unch; [exact HU | lia | lia | apply FP_nosh | exact Hokp].
Qed.

Lemma MI_okd : forall M', MI M' -> addr_ok M' d (4 * max).
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _]. pose proof bounds as B.
  eapply addr_ok_unch; [exact HU | lia | lia | apply FP_nosh | exact Hokd].
Qed.

Lemma MI_okq : forall M', MI M' -> addr_ok M' q 4.
Proof.
  intros M' HMI. destruct (MI_final _ HMI) as [HU _]. pose proof bounds as B.
  eapply addr_ok_unch; [exact HU | lia | lia | apply FP_nosh | exact Hokq].
Qed.

Lemma MI_grows : forall M', MI M' -> mem_grows M M'.
Proof. intros M' HMI. apply (MI_final _ HMI). Qed.

Lemma MI_rd : forall M', MI M' -> rd_ok M' p n.
Proof. intros M' HMI. eapply rd_ok_grows; [apply (MI_grows _ HMI) | exact Hrd]. Qed.

Lemma MI_wr_d : forall M', MI M' -> wr_ok BSEGS M' d (4 * max).
Proof. intros M' HMI. eapply wr_ok_grows; [apply (MI_grows _ HMI) | exact Hwd]. Qed.

Lemma MI_wr_q : forall M', MI M' -> wr_ok BSEGS M' q 4.
Proof. intros M' HMI. eapply wr_ok_grows; [apply (MI_grows _ HMI) | exact Hwq]. Qed.

Lemma MI_wr_sp : forall M', MI M' -> wr_ok BSEGS M' (sp0 - 2400) 2296.
Proof.
  intros M' HMI. eapply wr_ok_grows; [apply (MI_grows _ HMI)|].
  eapply wr_ok_sub; [exact Hfr | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma MI_rd_sp : forall M', MI M' -> rd_ok M' (sp0 - 176) 72.
Proof.
  intros M' HMI. eapply rd_ok_sub; [apply (wr_ok_rd_ok M' (sp0 - 2400) 2296 (MI_wr_sp _ HMI)); lia | lia | lia].
Qed.

Lemma MI_shd : forall M', MI M' -> 0 < max -> shw_ok M' d (4 * max).
Proof. intros M' HMI Hm. unfold shw_ok. eapply rd_ok_grows; [apply (MI_grows _ HMI) | apply Hshd, Hm]. Qed.

Lemma MI_store : forall M' a bs, MI M' -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat (length bs)) -> FPin x) -> MI (wbytes M' (W a) bs).
Proof.
  intros M' a bs [HU HG] Ha Hnw HF. split.
  - apply unch_store; assumption.
  - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
Qed.

Ltac pose_saved HMI :=
  pose proof (MI_saved _ 1%nat 168 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv1;
  pose proof (MI_saved _ 8%nat 160 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv8;
  pose proof (MI_saved _ 9%nat 152 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv9;
  pose proof (MI_saved _ 18%nat 144 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv18;
  pose proof (MI_saved _ 19%nat 136 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv19;
  pose proof (MI_saved _ 20%nat 128 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv20;
  pose proof (MI_saved _ 21%nat 120 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv21;
  pose proof (MI_saved _ 22%nat 112 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv22;
  pose proof (MI_saved _ 23%nat 104 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv23;
  pose proof (MI_saved _ 24%nat 96 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv24;
  pose proof (MI_saved _ 25%nat 88 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv25;
  pose proof (MI_saved _ 26%nat 80 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv26;
  pose proof (MI_saved _ 27%nat 72 HMI ltac:(unfold SAVE_SLOTS; in_list)) as Csv27.

(* [comment removed for export] *)
Lemma epilogue : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 176) ->
  (rget l 10 = W 0 \/ rget l 10 = W 1) ->
  (rget l 10 = W 1 -> exists w, 0 <= w <= max /\ cell BSEGS M' q 4 (W w)) ->
  reach BSEGS rom (Z_to_bv 64 0x430e44) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2 Ha0 Hw. pose_saved HMI. destruct (MI_final _ HMI) as [HU HG].
  unfold B_IMG_END in *. regs_open l Hl. subst sp.
  wp_dec (@nil Z). mem_auto.
  apply K; [reflexivity | | exact Ha0 | exact Hw | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fail_exit : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 176) ->
  reach BSEGS rom (Z_to_bv 64 0x430e40) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2. regs_open l Hl. subst sp.
  wp_dec [0x430e44].
  apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E].
Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSD l0 l /\ rget l 2 = W (sp0 - 176) /\ rget l 8 = W sp0
  /\ rget l 9 = W q /\ rget l 18 = W d /\ rget l 19 = W n /\ rget l 20 = W p /\ rget l 23 = W SB.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H9 & ?H18 & ?H19 & ?H20 & ?H23);
  regs_open l Hl.

Ltac prove_stable Hse :=
  unfold stable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
  cbn [rget lget]; repeat split; reflexivity.

Ltac fail_leaf HMI Hse :=
  apply fail_exit; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].

(* [comment removed for export] *)
Lemma success_store : forall l M' wo, MI M' -> stable l -> rget l 24 = W wo -> 0 <= wo <= max ->
  reach BSEGS rom (Z_to_bv 64 0x431298) l M' Post.
Proof.
  intros l M' wo HMI Hst H24 Hwo. pose proof (MI_wr_q _ HMI) as Hwq'. pose proof bounds as B.
  unfold B_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x430e44]. mem_auto.
  apply epilogue; [ | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | right; reflexivity | intros _; exists wo; split; [lia | apply cell_store_same; lia] ].
  apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia |].
  intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia.
Qed.

(* [comment removed for export] *)
Lemma success_exit : forall l M' wo, MI M' -> stable l -> rget l 24 = W wo -> rget l 28 = W (sha q) -> 0 <= wo <= max ->
  reach BSEGS rom (Z_to_bv 64 0x431290) l M' Post.
Proof.
  intros l M' wo HMI Hst H24 H28 Hwo. pose proof bounds as B.
  destruct (sh_load_k BSEGS M' q 4 (MI_okq _ HMI) ltac:(lia) ltac:(lia) ltac:(lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Hm8.
  unfold B_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x430e44; 0x431298; 0x4312d4].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (eapply (success_store _ _ wo); [exact HMI | prove_stable Hse | reflexivity | lia]).
Qed.

(* [comment removed for export] *)
Ltac gload Hrd :=
  lazymatch type of Hrd with
  | rd_ok ?M0 _ _ =>
    lazymatch goal with
    | |- exists v, load_ok _ ?Mx (Z_to_bv 64 ?a) ?k v /\ _ =>
        let v := fresh "gv" in let Hv := fresh "Hgv" in
        assert (exists v, load_ok BSEGS Mx (W a) k v) as [v Hv]
          by (eapply load_rd; [eapply (rd_ok_grows M0); [solve_grows | exact Hrd] | lia..]);
        exists v; split; [exact Hv|]; clear Hv
    end
  end.

(* [comment removed for export] *)
Definition lconst (l : regfile) : Prop :=
  rget l 28 = W (sha q) /\ rget l 29 = W n /\ rget l 30 = W max /\ rget l 26 = W 1 /\ rget l 21 = W 25
  /\ rget l 22 = W 456 /\ rget l 1 = W 1994.

(* [comment removed for export] *)
Definition Cmask (M' : mem) : Prop := cell BSEGS M' (sp0 + -120) 8 (W 65535).

(* [comment removed for export] *)
Definition OI (pi wo bias : Z) (l : regfile) : Prop :=
  stable l /\ lconst l /\ rget l 25 = W pi /\ rget l 11 = W wo /\ rget l 14 = W bias
  /\ 0 <= pi < n /\ 0 <= wo <= max /\ 0 <= bias <= 300.

Ltac prove_lconst := unfold lconst; cbn [rget lget]; repeat split; reflexivity.

Section Tail.
Variables (pi' wo c df : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Hc : 0 <= c <= 7.
Hypothesis Hdf : 0 <= df <= 498.
Hypothesis Kout : forall l M' bias', MI M' -> Cmask M' -> OI pi' (wo + 1) bias' l ->
  reach BSEGS rom (Z_to_bv 64 0x43101c) l M' Post.

(* [comment removed for export] *)
Lemma tail2 : forall l M' r, MI M' -> Cmask M' -> stable l -> 0 <= r <= wo -> wo < max ->
  cell BSEGS M' (sp0 + -144) 8 (W (sha q)) -> cell BSEGS M' (sp0 + -152) 8 (W n) -> cell BSEGS M' (sp0 + -160) 8 (W max) ->
  rget l 25 = W pi' -> rget l 24 = W (wo + 1) -> rget l 21 = W (d + 4 * r) -> rget l 22 = W (36 * c) -> rget l 27 = W df ->
  rget l 26 = W 1 ->
  reach BSEGS rom (Z_to_bv 64 0x43121c) l M' Post.
Proof using All.
  intros l M' r HMI HCm Hst Hr Hwm Ct3 Ct4 Ct5 H25 H24 H21 H22 H27 H26.
  pose proof (MI_wr_d _ HMI) as Hwd'. pose proof (MI_rd_sp _ HMI) as Hrsp. pose proof bounds as B.
  destruct (bias_val c df Hc Hdf) as (bv & Hbv & Ebv).
  unfold B_IMG_END, HIMEM_END, Cmask in *.
  open_stable Hst l. subst.
  wp_dec [0x43101c; 0x431290]. rewrite ?addi_W.
  gload Hrsp. gload Hrsp.
  eexists. split; [apply load_cell8; exact HCm|].
  split; [eapply wr_ok_store; [exact Hwd' | lia | lia]|].
  rewrite Ebv.
  gload Hrsp.
  assert (Hdisj : d + 4 * max <= sp0 - 2400 \/ sp0 <= d) by exact Hdj1.
  eexists. split; [apply load_cell8; apply cell_store_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia | exact Ct3]|].
  eexists. split; [apply load_cell8; apply cell_store_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia | exact Ct4]|].
  eexists. split; [apply load_cell8; apply cell_store_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia | exact Ct5]|].
  rewrite !Wu by lia.
  match goal with |- context [wbytes M' ?a ?bs] =>
    assert (HMI2 : MI (wbytes M' a bs))
      by (apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia
                          | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]);
    assert (HCm2 : cell BSEGS (wbytes M' a bs) (sp0 + -120) 8 (W 65535))
      by (apply cell_store_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia | exact HCm]) end.
  split; intros Hb.
  - apply (Kout _ _ bv); [exact HMI2 | exact HCm2 |].
    unfold OI. split; [prove_stable Hse|]. split; [prove_lconst|]. cbn [rget lget].
    repeat split; try reflexivity; lia.
  - eapply (success_exit _ _ (wo + 1)); [exact HMI2 | prove_stable Hse | reflexivity | reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma tail : forall l M', MI M' -> Cmask M' -> stable l ->
  rget l 28 = W (sha q) -> rget l 29 = W n -> rget l 30 = W max ->
  rget l 25 = W pi' -> rget l 11 = W wo -> rget l 24 = W (wo + 1) -> rget l 22 = W (36 * c) -> rget l 27 = W df ->
  rget l 26 = W 1 ->
  reach BSEGS rom (Z_to_bv 64 0x431188) l M' Post.
Proof using All.
  intros l M' HMI HCm Hst H28 H29 H30 H25 H11 H24 H22 H27 H26.
  pose proof (MI_wr_sp _ HMI) as Hwsp'. pose proof bounds as B.
  unfold B_IMG_END, HIMEM_END, Cmask in *.
  open_stable Hst l. subst.
  destruct (rem_idx a3 (wo + 1) ltac:(lia)) as (r & Hr & Er).
  assert (Hdr : (d + 4 * r) mod 4 = 0) by (replace (d + 4 * r) with (d + r * 4) by lia; rewrite Z_mod_plus_full; exact Hdal).
  assert (Hdr4 : (d + 4 * r + 4) mod 4 = 0) by (replace (d + 4 * r + 4) with (d + (r + 1) * 4) by lia; rewrite Z_mod_plus_full; exact Hdal).
  wp_dec [0x430e40; 0x4312ac].
  rewrite Er. rewrite !scale4_W by lia. rewrite ?add_W, ?addi_W.
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
  split; [eapply wr_ok_store; [exact Hwsp' | lia | lia]|].
  split; intros Hb2; [exfalso; apply Hb2; reflexivity|]. clear Hb2.
  repeat (split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Hwsp']; solve_grows | lia | lia]|]).
  rewrite (subw_W wo r) by lia. rewrite !scale4_W by lia. rewrite ?add_W, ?addi_W.
  name_mem M2.
  assert (HMI2 : MI M2).
  { unname_mems. repeat (apply MI_store; [ | lia | rewrite length_N_to_le_bytes; lia
        | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]). exact HMI. }
  assert (HCm2 : cell BSEGS M2 (sp0 + -120) 8 (W 65535)) by (unname_mems; solve_cell).
  assert (Ct3 : cell BSEGS M2 (sp0 + -144) 8 (W (sha q))) by (unname_mems; solve_cell).
  assert (Ct4 : cell BSEGS M2 (sp0 + -152) 8 (W n)) by (unname_mems; solve_cell).
  assert (Ct5 : cell BSEGS M2 (sp0 + -160) 8 (W max)) by (unname_mems; solve_cell).
  clearbody M2. clear Hwsp' HCm.
  pose proof (MI_wr_d _ HMI2) as Hwd'. pose proof (MI_okd _ HMI2) as Hokd'.
  assert (Hmr1 : memrange (d + 4 * r) (4 * (wo - r))).
  { destruct Hmd as [_ Hd']. unfold memrange, LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. }
  assert (Hmr2 : memrange (d + 4 * r + 4) (4 * (wo - r))).
  { destruct Hmd as [_ Hd']. unfold memrange, LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. }
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) ?k) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) k) with (Z_to_bv 64 0x1bcf68) by reflexivity end.
  eapply (amemmove_cps rom Post M2 (d + 4 * r + 4) (d + 4 * r) (4 * (wo - r)) (sp0 - 176));
    [ apply (MI_rt _ HMI2) | lia | exact Hmr1 | exact Hmr2 | lia
    | eapply addr_ok_sub; [exact Hokd' | lia | lia]
    | eapply addr_ok_sub; [exact Hokd' | lia | lia]
    | intros Hpos; eapply shw_ok_sub; [apply (MI_shd _ HMI2); lia | lia | lia | lia]
    | intros Hpos; eapply shw_ok_sub; [apply (MI_shd _ HMI2); lia | lia | lia | lia]
    | eapply rd_ok_sub; [apply (wr_ok_rd_ok M2 d (4 * max) Hwd'); unfold B_IMG_END; lia | lia | lia]
    | eapply wr_ok_sub; [exact Hwd' | lia | lia]
    | unfold B_IMG_END; lia
    | unfold SB, HIMEM_BEG in *; lia
    | eapply wr_ok_sub; [apply (MI_wr_sp _ HMI2) | lia | lia]
    | lia
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) 0) with (Z_to_bv 64 0x43120c) by reflexivity end.
  regs_open l'' Hl''. se_subst Hse''. clear Hse''.
  assert (HMI3 : MI M'').
  { destruct HMI2 as [HU2 HG2]. split; [|eapply mem_grows_trans; eassumption].
    eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU''|].
    intros x Hx. unfold BAsanMemmove.FP, FPin, inr in *. lia. }
  assert (HCm3 : cell BSEGS M'' (sp0 + -120) 8 (W 65535)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold BAsanMemmove.FP, inr in *; lia | exact HCm2]. }
  assert (Ct3' : cell BSEGS M'' (sp0 + -144) 8 (W (sha q))).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold BAsanMemmove.FP, inr in *; lia | exact Ct3]. }
  assert (Ct4' : cell BSEGS M'' (sp0 + -152) 8 (W n)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold BAsanMemmove.FP, inr in *; lia | exact Ct4]. }
  assert (Ct5' : cell BSEGS M'' (sp0 + -160) 8 (W max)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold BAsanMemmove.FP, inr in *; lia | exact Ct5]. }
  clear HCm2 Ct3 Ct4 Ct5 Hwd' Hokd'.
  destruct (sh_load_k BSEGS M'' (d + 4 * r) 4 ltac:(eapply addr_ok_sub; [apply (MI_okd _ HMI3) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hcu).
  pose proof (Z.mod_pos_bound (d + 4 * r) 8 ltac:(lia)) as Hm8.
  wp_dec [0x43121c; 0x431284]. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (eapply (tail2 _ _ r); [exact HMI3 | exact HCm3 | prove_stable Hse | lia | lia | exact Ct3' | exact Ct4' | exact Ct5'
                           | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]).
Qed.
End Tail.

(* [comment removed for export] *)
Definition lconst0 (l : regfile) : Prop :=
  rget l 28 = W (sha q) /\ rget l 29 = W n /\ rget l 30 = W max /\ rget l 26 = W 1.
Definition BI (s9v wo : Z) (l : regfile) : Prop :=
  stable l /\ lconst0 l /\ rget l 11 = W wo /\ rget l 25 = W s9v.

Ltac open_BI H l :=
  let Hst := fresh "Hst" in let Hlc := fresh "Hlc" in
  destruct H as (Hst & Hlc & ?H11 & ?H25);
  destruct Hlc as (?L28 & ?L29 & ?L30 & ?L26); open_stable Hst l.

Ltac prove_BI Hse :=
  unfold BI; split; [prove_stable Hse|]; split; [unfold lconst0; cbn [rget lget]; repeat split; reflexivity|];
  cbn [rget lget]; split; reflexivity.

Definition cap (c : nat) : Z :=
  match c with
  | 0%nat => 4294967296 | 1%nat => 134217728 | 2%nat => 4194304 | 3%nat => 131072 | 4%nat => 4096
  | 5%nat => 128 | 6%nat => 4 | _ => 1
  end.

Section Adapt.
Variables (pi' wo : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Ktail : forall c df l M', 0 <= c <= 7 -> 0 <= df <= 498 -> MI M' -> Cmask M' -> stable l ->
  rget l 28 = W (sha q) -> rget l 29 = W n -> rget l 30 = W max ->
  rget l 25 = W pi' -> rget l 11 = W wo -> rget l 24 = W (wo + 1) -> rget l 22 = W (36 * c) -> rget l 27 = W df ->
  rget l 26 = W 1 ->
  reach BSEGS rom (Z_to_bv 64 0x431188) l M' Post.

(* [comment removed for export] *)
Lemma adapt_loop : forall k (cN : nat) l M', (7 - Z.of_nat cN = Z.of_nat k) -> (cN <= 6)%nat ->
  bv_unsigned (rget l 10) mod 2 ^ 32 < cap cN ->
  MI M' -> Cmask M' -> BI pi' wo l -> rget l 24 = W (wo + 1) -> rget l 22 = W (36 * Z.of_nat cN) -> rget l 1 = W 1994 ->
  reach BSEGS rom (Z_to_bv 64 0x431154) l M' Post.
Proof using All.
  induction k as [k IH] using lt_wf_ind; intros cN l M' Hk HcN6 Hcap HMI HCm HBI H24 H22 H1.
  open_BI HBI l. subst. cbn [rget lget] in Hcap.
  wp_dec [0x431154; 0x431188]. rewrite ?addi_W.
  destruct (adapt_bound a0 a5) as (nv & Hnv0 & Hnv & Env). rewrite Env.
  pose proof (Z.mod_pos_bound (bv_unsigned a0) (2 ^ 32) ltac:(lia)) as Hdlb.
  split; intros Hbr.
  - apply (adapt_continue a0 1994 ltac:(lia)) in Hbr.
    assert (HcN : (cN <= 5)%nat).
    { destruct cN as [|[|[|[|[|[|cN]]]]]]; try lia. exfalso. cbn [cap] in Hcap.
      destruct cN; cbn [cap] in Hcap; lia. }
    eapply (IH (Z.to_nat (7 - Z.of_nat (S cN)))) with (cN := S cN);
      [ lia | lia | lia | | exact HMI | exact HCm | prove_BI Hse | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity ].
    cbn [rget lget]. rewrite Wu by lia. rewrite Z.mod_small by lia.
    destruct cN as [|[|[|[|[|[|cN]]]]]]; cbn [cap] in *; lia.
  - apply (adapt_stop a0 1994 ltac:(lia)) in Hbr.
    apply (Ktail (Z.of_nat cN + 1) nv); [lia | lia | exact HMI | exact HCm | prove_stable Hse
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma brk : forall l M', MI M' -> Cmask M' -> BI pi' wo l -> rget l 22 = W 456 -> rget l 1 = W 1994 ->
  reach BSEGS rom (Z_to_bv 64 0x431114) l M' Post.
Proof using All.
  intros l M' HMI HCm HBI H22 H1. pose proof (MI_rd_sp _ HMI) as Hsr. unfold B_IMG_END in *.
  open_BI HBI l. subst.
  assert (Es8 : v_addiw (W wo) 1 = W (wo + 1)) by (apply addiw_W; lia).
  wp_dec [0x431154; 0x431188; 0x4312ac]. rewrite ?Es8, ?addi_W. rewrite ?(Wu (wo + 1)), ?(Wu 456) by lia.
  split; intros Hbr; clear Hbr; [gload Hsr; gload Hsr | gload Hsr];
  (split; intros Hbr2; [exfalso; lia|]; clear Hbr2; split; intros Hbr3;
   [ match type of Hbr3 with bv_unsigned ?X < _ =>
       eapply (Ktail 0 (bv_unsigned X)); [lia | pose proof (u64_range X); lia
       | exact HMI | exact HCm | prove_stable Hse | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
       | reflexivity | reflexivity | cbn [rget lget]; symmetry; apply W_u | reflexivity ] end
   | clear Hbr3;
     eapply (adapt_loop 7 0%nat); [reflexivity | lia | | exact HMI | exact HCm | prove_BI Hse | reflexivity | reflexivity | reflexivity];
     cbn [rget lget cap]; apply Z.mod_pos_bound; lia ]).
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

Lemma capw_pos : forall j, 1 <= capw j.
Proof. intros j. do 10 (destruct j as [|j]; [cbn; lia|]). cbn. lia. Qed.

(* [comment removed for export] *)
Definition DI (s9v wo : Z) (l : regfile) : Prop :=
  stable l /\ lconst l /\ rget l 11 = W wo /\ rget l 25 = W s9v.

Ltac open_DI H l :=
  let Hst := fresh "Hst" in let Hlc := fresh "Hlc" in
  destruct H as (Hst & Hlc & ?H11 & ?H25);
  destruct Hlc as (?L28 & ?L29 & ?L30 & ?L26 & ?L21 & ?L22 & ?L1); open_stable Hst l.

Ltac prove_DI Hse :=
  unfold DI; split; [prove_stable Hse|]; split; [prove_lconst|]; cbn [rget lget];
  split; first [reflexivity | f_equal; lia].

Section Digits.
Variables (wo lo bias : Z).
Hypothesis Hlo : 0 <= lo.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Hbias : 0 <= bias <= 300.
Hypothesis Kbrk : forall s9v l M', lo < s9v <= n -> MI M' -> Cmask M' -> BI s9v wo l ->
  rget l 22 = W 456 -> rget l 1 = W 1994 ->
  reach BSEGS rom (Z_to_bv 64 0x431114) l M' Post.

(* [comment removed for export] *)
Definition DR (jN : nat) (wv : Z) (l : regfile) : Prop :=
  rget l 14 = W bias /\ rget l 15 = W (bias + 26) /\ rget l 16 = v_subw (W 0) (W bias)
  /\ rget l 5 = W (36 * (Z.of_nat jN + 1)) /\ bv_unsigned (rget l 17) mod 2 ^ 32 = wv
  /\ capw jN <= wv /\ (jN <= 9)%nat.

Section Iter.
Variables (idx : Z) (jN : nat) (wv : Z).
Hypothesis Hidx : lo <= idx < n.
Hypothesis Kd1 : forall wv' l M', idx + 1 < n -> MI M' -> Cmask M' -> DI (idx + 2) wo l -> DR (S jN) wv' l ->
  rget l 10 = W (idx + 1) -> reach BSEGS rom (Z_to_bv 64 0x431040) l M' Post.

(* [comment removed for export] *)
Lemma d3 : forall l M' t, MI M' -> Cmask M' -> DI (idx + 1) wo l -> DR jN wv l -> rget l 6 = W t -> 1 <= t <= 26 ->
  reach BSEGS rom (Z_to_bv 64 0x4310bc) l M' Post.
Proof using All.
  intros l M' t HMI HCm HDI HDR H6 Ht. destruct HDR as (D14 & D15 & D16 & D5 & D17 & Dcap & Dj).
  revert D17 Dcap. open_DI HDI l. subst. intros D17 Dcap. cbn [rget lget] in D17.
  wp_dec [0x430e40; 0x431114; 0x431040; 0x4312ac].
  rewrite (subw_W 36 t) by lia. rewrite zext32_W by lia. rewrite ?(Wu t), ?(Wu 36), ?(Wu (idx + 1)), ?(Wu n) by lia.
  split; intros Hbr; clear Hbr.
  - apply (Kbrk (idx + 1)); [lia | exact HMI | exact HCm | prove_BI Hse | reflexivity | reflexivity].
  - split; intros Hbr; [exfalso; lia|]. clear Hbr.
    split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|].
    destruct (w_step a7 (36 - t) wv D17 ltac:(lia) Hbr) as [Ew Hlt]. clear Hbr.
    split; intros Hbr; [fail_leaf HMI Hse|].
    rewrite !addiw_W by lia.
    assert (Hj8 : (jN <= 8)%nat).
    { destruct (Nat.le_gt_cases jN 8) as [Hle|Hgt]; [exact Hle|]. exfalso.
      assert (jN = 9%nat) by lia. subst jN. cbn [capw] in Dcap. nia. }
    apply (Kd1 ((36 - t) * wv)); [lia | exact HMI | exact HCm | prove_DI Hse | | reflexivity].
    unfold DR. cbn [rget lget]. repeat split; try reflexivity.
    + f_equal. lia.
    + exact Ew.
    + apply capw_step; [exact Hj8 | lia | exact Dcap].
    + lia.
Qed.

(* [comment removed for export] *)
Lemma d2 : forall l M', MI M' -> Cmask M' -> DI (idx + 1) wo l -> DR jN wv l ->
  reach BSEGS rom (Z_to_bv 64 0x43108c) l M' Post.
Proof using All.
  intros l M' HMI HCm HDI HDR. pose proof HDR as (D14 & D15 & D16 & D5 & D17 & Dcap & Dj).
  pose proof (capw_pos jN) as Hcp.
  assert (HDR' : forall l', rget l' 14 = rget l 14 -> rget l' 15 = rget l 15 -> rget l' 16 = rget l 16 ->
             rget l' 5 = rget l 5 -> rget l' 17 = rget l 17 -> DR jN wv l').
  { intros l' E14 E15 E16 E5 E17. unfold DR. rewrite E14, E15, E16, E5, E17. exact HDR. }
  clear HDR. revert D17 Dcap HDR'. open_DI HDI l. subst. intros D17 Dcap HDR'. cbn [rget lget] in D17, HDR'.
  assert (Hkk : 0 <= 36 * (Z.of_nat jN + 1) <= 360) by lia.
  wp_dec [0x430e40; 0x4310bc; 0x4312ac].
  rewrite (t_mid bias (36 * (Z.of_nat jN + 1))) by lia.
  rewrite ?(Wu (36 * (Z.of_nat jN + 1))), ?(Wu (bias + 26)), ?(Wu bias) by lia.
  split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|]. clear Hbr.
  split; intros Hbr.
  { exfalso. rewrite Hbr in D17. change (0 mod 2 ^ 32) with 0 in D17. lia. }
  clear Hbr.
  split; intros Hbr; [clear Hbr; fail_leaf HMI Hse|]. clear Hbr.
  split; intros Hb1.
  - split; intros Hb2.
    + eapply (d3 _ _ (36 * (Z.of_nat jN + 1) - bias)); [exact HMI | exact HCm | prove_DI Hse | apply HDR'; reflexivity | reflexivity | lia].
    + eapply (d3 _ _ 1); [exact HMI | exact HCm | prove_DI Hse | apply HDR'; reflexivity | reflexivity | lia].
  - split; intros Hb2.
    + eapply (d3 _ _ 1); [exact HMI | exact HCm | prove_DI Hse | apply HDR'; reflexivity | reflexivity | lia].
    + eapply (d3 _ _ 26); [exact HMI | exact HCm | prove_DI Hse | apply HDR'; reflexivity | reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma d1 : forall l M', MI M' -> Cmask M' -> DI (idx + 1) wo l -> DR jN wv l -> rget l 10 = W (p + idx) ->
  reach BSEGS rom (Z_to_bv 64 0x431068) l M' Post.
Proof using All.
  intros l M' HMI HCm HDI HDR H10. pose proof (MI_rd _ HMI) as Hrd'. pose proof bounds as B. unfold HIMEM_END in *.
  assert (HDR' : forall l', rget l' 14 = rget l 14 -> rget l' 15 = rget l 15 -> rget l' 16 = rget l 16 ->
             rget l' 5 = rget l 5 -> rget l' 17 = rget l 17 -> DR jN wv l').
  { intros l' E14 E15 E16 E5 E17. unfold DR. rewrite E14, E15, E16, E5, E17. exact HDR. }
  clear HDR. revert HDR'. open_DI HDI l. subst. intros HDR'. cbn [rget lget] in HDR'.
  wp_dec [0x430e40; 0x43108c].
  assert (exists v, load_ok BSEGS M' (W (p + idx)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  repeat (split; intros ?Hb);
    first [ fail_leaf HMI Hse | apply d2; [exact HMI | exact HCm | prove_DI Hse | apply HDR'; reflexivity] ].
Qed.

(* [comment removed for export] *)
Lemma d0 : forall l M', MI M' -> Cmask M' -> DI (idx + 1) wo l -> DR jN wv l -> rget l 10 = W idx ->
  reach BSEGS rom (Z_to_bv 64 0x431040) l M' Post.
Proof using All.
  intros l M' HMI HCm HDI HDR H10. pose proof bounds as B. unfold HIMEM_END in B.
  assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
  destruct (sh_load_k BSEGS M' (p + idx) 1 ltac:(eapply addr_ok_sub; [apply (MI_okp _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (p + idx) 8 ltac:(lia)) as Hm8.
  assert (HDR' : forall l', rget l' 14 = rget l 14 -> rget l' 15 = rget l 15 -> rget l' 16 = rget l 16 ->
             rget l' 5 = rget l 5 -> rget l' 17 = rget l 17 -> DR jN wv l').
  { intros l' E14 E15 E16 E5 E17. unfold DR. rewrite E14, E15, E16, E5, E17. exact HDR. }
  clear HDR. revert HDR'. open_DI HDI l. subst. intros HDR'. cbn [rget lget] in HDR'.
  wp_dec [0x431068; 0x4312ac; 0x4312e0]. rewrite ?add_W.
  rewrite (sltiu1_W (p + idx)) by lia.
  replace (Z.eqb (p + idx) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite ?(Wu (p + idx)), ?(Wu p), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros Hbad; exfalso; lia | intros _] | intros _];
    (apply d1; [exact HMI | exact HCm | prove_DI Hse | apply HDR'; reflexivity | reflexivity]).
Qed.
End Iter.

Lemma digit_loop : forall k idx jN wv l M', n - idx = Z.of_nat k -> lo <= idx < n ->
  MI M' -> Cmask M' -> DI (idx + 1) wo l -> DR jN wv l -> rget l 10 = W idx ->
  reach BSEGS rom (Z_to_bv 64 0x431040) l M' Post.
Proof using All.
  induction k as [k IH] using lt_wf_ind; intros idx jN wv l M' Hk Hidx HMI HCm HDI HDR H10.
  apply (d0 idx jN wv Hidx); try assumption.
  intros wv' l2 M2 Hlt HMI2 HCm2 HDI2 HDR2 H10'.
  eapply (IH (Z.to_nat (n - (idx + 1)))) with (idx := idx + 1) (jN := S jN) (wv := wv'); try eassumption; try lia.
  replace (idx + 1 + 1) with (idx + 2) by lia. exact HDI2.
Qed.
End Digits.

(* [comment removed for export] *)
Lemma outer_loop : forall k pi wo bias l M', n - pi = Z.of_nat k -> MI M' -> Cmask M' -> OI pi wo bias l ->
  reach BSEGS rom (Z_to_bv 64 0x43101c) l M' Post.
Proof using All.
  induction k as [k IH] using lt_wf_ind; intros pi wo bias l M' Hk HMI HCm HOI.
  destruct HOI as (Hst & Hlc & H25 & H11 & H14 & Hpi & Hwo & Hbias).
  destruct Hlc as (L28 & L29 & L30 & L26 & L21 & L22 & L1).
  open_stable Hst l. subst.
  wp_dec [0x430e40; 0x431040]. rewrite zext32_W by lia. rewrite ?(Wu pi), ?(Wu n) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr. rewrite !addiw_W by lia.
  eapply digit_loop with (wo := wo) (lo := pi) (bias := bias) (idx := pi) (jN := 0%nat) (wv := 1) (k := Z.to_nat (n - pi));
    [ lia | lia | lia | | lia | lia | exact HMI | exact HCm | prove_DI Hse | | reflexivity ].
  - (* [comment removed for export] *)
    intros s9v l2 M2 Hs9 HMI2 HCm2 HBI2 H22' H1'.
    eapply brk with (pi' := s9v) (wo := wo); [lia | lia | | exact HMI2 | exact HCm2 | exact HBI2 | exact H22' | exact H1'].
    intros c df l3 M3 Hc Hdf HMI3 HCm3 Hst3 R28 R29 R30 R25 R11 R24 R22 R27 R26.
    eapply tail with (pi' := s9v) (wo := wo) (c := c) (df := df); try assumption; try lia.
    intros l4 M4 bias4 HMI4 HCm4 HOI4.
    assert (Hlt4 : 0 <= s9v < n) by (destruct HOI4 as (_ & _ & _ & _ & _ & Hx & _); exact Hx).
    eapply (IH (Z.to_nat (n - s9v))); [lia | | exact HMI4 | exact HCm4 | exact HOI4]. lia.
  - unfold DR. cbn [rget lget]. repeat split; try reflexivity; cbn [capw]; lia.
Qed.

(* [comment removed for export] *)
Definition stable2 (l : regfile) : Prop := stable l /\ rget l 28 = W (sha q) /\ rget l 12 = W max.

Ltac open_stable2 H l :=
  let Hst := fresh "Hst" in destruct H as (Hst & ?S28 & ?S12); open_stable Hst l.

Ltac prove_stable2 Hse :=
  unfold stable2; split; [prove_stable Hse|]; cbn [rget lget]; split; reflexivity.

(* [comment removed for export] *)
Lemma pre_outer : forall pi wo l M', MI M' -> stable2 l -> rget l 25 = W pi -> rget l 24 = W wo ->
  0 <= pi <= n -> 0 <= wo <= max ->
  reach BSEGS rom (Z_to_bv 64 0x430fbc) l M' Post.
Proof using All.
  intros pi wo l M' HMI Hst2 H25 H24 Hpi Hwo. pose proof (MI_wr_sp _ HMI) as Hwsp'. unfold B_IMG_END in *.
  open_stable2 Hst2 l. subst.
  wp_dec [0x43101c; 0x431290]. rewrite addiw_W by lia. replace (n + 0) with n by lia.
  rewrite ?(Wu pi), ?(Wu n), ?(Wu wo), ?(Wu max) by lia.
  split; intros Hbr.
  - eapply (success_exit _ _ wo); [exact HMI | prove_stable Hse | reflexivity | reflexivity | lia].
  - assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
    pose proof bounds as B. unfold HIMEM_END in B.
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
Definition CI (bc j : Z) (l : regfile) : Prop :=
  stable2 l /\ rget l 24 = W bc /\ rget l 13 = W j /\ rget l 14 = W 1 /\ rget l 15 = W bc
  /\ rget l 16 = v_xori (W p) (-1) /\ rget l 17 = W 1 /\ rget l 5 = W (d + 4 * j) /\ rget l 10 = W (d + 4 * j).

Ltac open_CI H l :=
  let Hst := fresh "Hst2" in
  destruct H as (Hst & ?H24 & ?H13 & ?H14 & ?H15 & ?H16 & ?H17 & ?H5 & ?H10); open_stable2 Hst l.

Ltac prove_CI Hse :=
  unfold CI; split; [prove_stable2 Hse|]; cbn [rget lget]; repeat split; try reflexivity; f_equal; lia.

Section Copy.
Variables (bc j : Z).
Hypothesis Hbc : bc <= max /\ bc < n.
Hypothesis Hj : 0 <= j < bc.
Hypothesis Kc : forall l M', j + 1 < bc -> MI M' -> CI bc (j + 1) l ->
  reach BSEGS rom (Z_to_bv 64 0x430f34) l M' Post.

(* [comment removed for export] *)
Lemma c2 : forall l M', MI M' -> CI bc j l -> reach BSEGS rom (Z_to_bv 64 0x430f78) l M' Post.
Proof using All.
  intros l M' HMI HCI. pose proof (MI_wr_d _ HMI) as Hwd'. pose proof bounds as B.
  unfold B_IMG_END, HIMEM_END in *.
  open_CI HCI l. subst.
  wp_dec [0x430f34; 0x430fbc]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Hwd' | lia | lia]|].
  match goal with |- context [wbytes M' ?a ?bs] =>
    assert (HMI2 : MI (wbytes M' a bs))
      by (apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia
                          | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]) end.
  rewrite ?(Wu bc), ?(Wu (j + 1)) by lia.
  split; intros Hb.
  - apply Kc; [lia | exact HMI2 | prove_CI Hse].
  - rewrite addiw_W by lia.
    eapply (pre_outer (bc + 1) bc); [exact HMI2 | prove_stable2 Hse | reflexivity | reflexivity | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma c1 : forall l M', MI M' -> CI bc j l -> rget l 11 = W (p + j) ->
  reach BSEGS rom (Z_to_bv 64 0x430f4c) l M' Post.
Proof using All.
  intros l M' HMI HCI H11. pose proof (MI_rd _ HMI) as Hrd'. pose proof bounds as B. unfold B_IMG_END, HIMEM_END in *.
  destruct (sh_load_k BSEGS M' (d + 4 * j) 4 ltac:(eapply addr_ok_sub; [apply (MI_okd _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (d + 4 * j) 8 ltac:(lia)) as Hm8.
  open_CI HCI l. subst.
  wp_dec [0x430e40; 0x430f78; 0x4312ac; 0x430fac].
  assert (exists v, load_ok BSEGS M' (W (p + j)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  split; intros Hb; clear Hb; [fail_leaf HMI Hse|].
  rewrite (sltiu1_W (d + 4 * j)) by lia.
  replace (Z.eqb (d + 4 * j) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite ?(Wu (d + 4 * j)), ?(Wu d), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (apply c2; [exact HMI | prove_CI Hse]).
Qed.

(* [comment removed for export] *)
Lemma c0 : forall l M', MI M' -> CI bc j l -> reach BSEGS rom (Z_to_bv 64 0x430f34) l M' Post.
Proof using All.
  intros l M' HMI HCI. pose proof bounds as B. unfold HIMEM_END in B.
  destruct (sh_load_k BSEGS M' (p + j) 1 ltac:(eapply addr_ok_sub; [apply (MI_okp _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (p + j) 8 ltac:(lia)) as Hm8.
  open_CI HCI l. subst.
  wp_dec [0x430f4c; 0x4312ac; 0x4312e8]. rewrite ?add_W.
  rewrite (u_not p) by lia. rewrite ?(Wu j) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros Hbad; exfalso; lia | intros _] | intros _];
    (apply c1; [exact HMI | prove_CI Hse | reflexivity]).
Qed.
End Copy.

Lemma copy_loop : forall k j bc l M', bc - j = Z.of_nat k -> 0 <= j < bc -> bc <= max /\ bc < n ->
  MI M' -> CI bc j l -> reach BSEGS rom (Z_to_bv 64 0x430f34) l M' Post.
Proof using All.
  induction k as [k IH] using lt_wf_ind; intros j bc l M' Hk Hj Hbc HMI HCI.
  apply (c0 bc j Hbc Hj); [|exact HMI | exact HCI].
  intros l2 M2 Hlt HMI2 HCI2.
  eapply (IH (Z.to_nat (bc - (j + 1)))) with (j := j + 1) (bc := bc); [lia | lia | lia | exact Hbc | exact HMI2 | exact HCI2].
Qed.

(* [comment removed for export] *)
Lemma post_scan : forall bc l M', MI M' -> stable2 l -> rget l 24 = W bc -> bc = 0 \/ 0 < bc < n ->
  reach BSEGS rom (Z_to_bv 64 0x430f04) l M' Post.
Proof using All.
  intros bc l M' HMI Hst2 H24 Hbc. pose proof bounds as B. unfold B_IMG_END, HIMEM_END in *.
  open_stable2 Hst2 l. subst.
  assert (Ean : v_andi (W d) 3 = W 0).
  { rewrite <- (W_u (v_andi (W d) 3)). f_equal. change 3 with (Z.ones 2). rewrite u_andi_ones_W by lia. exact Hdal. }
  wp_dec [0x430f34; 0x430e40; 0x430fbc]. rewrite Ean.
  rewrite (sltiu1_W 0), (sltu0_W d) by lia.
  replace (Z.eqb d 0) with false by (symmetry; apply Z.eqb_neq; lia). change (Z.eqb 0 0) with true. cbv beta iota.
  rewrite (and_W 1 1) by lia. change (Z.land 1 1) with 1.
  rewrite ?(Wu bc), ?(Wu max) by lia.
  split; intros Hb.
  - eapply (pre_outer 0 bc); [exact HMI | prove_stable2 Hse | reflexivity | reflexivity | lia | lia].
  - split; intros Hb2.
    + fail_leaf HMI Hse.
    + rewrite zext32_W by lia.
      eapply (copy_loop (Z.to_nat (bc - 0)) 0 bc); [lia | lia | lia | exact HMI | prove_CI Hse].
Qed.

(* [comment removed for export] *)
Definition SI (k bc : Z) (l : regfile) : Prop :=
  stable2 l /\ rget l 10 = W (p + k) /\ rget l 16 = W (p + k) /\ rget l 15 = W (n - k) /\ rget l 11 = W k
  /\ rget l 17 = W bc /\ rget l 13 = W 1 /\ rget l 14 = W 45.

Ltac open_SI H l :=
  let Hst := fresh "Hst2" in
  destruct H as (Hst & ?H10 & ?H16 & ?H15 & ?H11 & ?H17 & ?H13 & ?H14); open_stable2 Hst l.

Ltac prove_SI Hse :=
  unfold SI; split; [prove_stable2 Hse|]; cbn [rget lget]; repeat split; try reflexivity; f_equal; lia.

Section Scan.
Variables (k bc : Z).
Hypothesis Hk : 0 <= k < n.
Hypothesis Hbc : bc = 0 \/ 0 < bc < k.
Hypothesis Ks : forall bc' l M', k + 1 < n -> bc' = 0 \/ 0 < bc' < k + 1 -> MI M' -> SI (k + 1) bc' l ->
  reach BSEGS rom (Z_to_bv 64 0x430ea4) l M' Post.

(* [comment removed for export] *)
Lemma s1 : forall l M', MI M' -> SI k bc l -> reach BSEGS rom (Z_to_bv 64 0x430ec8) l M' Post.
Proof using All.
  intros l M' HMI HSI. pose proof (MI_rd _ HMI) as Hrd'. pose proof bounds as B. unfold HIMEM_END in B.
  open_SI HSI l. subst.
  wp_dec [0x430ea4; 0x430f04].
  assert (exists v, load_ok BSEGS M' (W (p + k)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  rewrite ?addi_W. rewrite addiw_W by lia. rewrite ?(Wu (n - k + -1)) by lia.
  split; intros Hb; clear Hb; (split; intros Hb).
  - apply (Ks k); [lia | lia | exact HMI | prove_SI Hse].
  - eapply (post_scan k); [exact HMI | prove_stable2 Hse | reflexivity | lia].
  - apply (Ks bc); [lia | lia | exact HMI | prove_SI Hse].
  - eapply (post_scan bc); [exact HMI | prove_stable2 Hse | reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma s0 : forall l M', MI M' -> SI k bc l -> reach BSEGS rom (Z_to_bv 64 0x430ea4) l M' Post.
Proof using All.
  intros l M' HMI HSI. pose proof bounds as B. unfold HIMEM_END in B.
  assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
  destruct (sh_load_k BSEGS M' (p + k) 1 ltac:(eapply addr_ok_sub; [apply (MI_okp _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (p + k) 8 ltac:(lia)) as Hm8.
  open_SI HSI l. subst.
  wp_dec [0x430ec8; 0x4312ac; 0x430efc].
  rewrite (sltiu1_W (p + k)) by lia. replace (Z.eqb (p + k) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (xor_W 1 0) by lia. change (Z.lxor 1 0) with 1.
  rewrite ?(Wu (p + k)), ?(Wu p), ?(Wu 1) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.

  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (apply s1; [exact HMI | prove_SI Hse]).
Qed.
End Scan.

Lemma scan_loop : forall m k bc l M', n - k = Z.of_nat m -> 0 <= k < n -> bc = 0 \/ 0 < bc < k ->
  MI M' -> SI k bc l -> reach BSEGS rom (Z_to_bv 64 0x430ea4) l M' Post.
Proof using All.
  induction m as [m IH] using lt_wf_ind; intros k bc l M' Hm Hk Hbc HMI HSI.
  apply (s0 k bc Hk Hbc); [|exact HMI | exact HSI].
  intros bc' l2 M2 Hlt Hbc' HMI2 HSI2.
  eapply (IH (Z.to_nat (n - (k + 1)))) with (k := k + 1) (bc := bc'); [lia | lia | lia | exact Hbc' | exact HMI2 | exact HSI2].
Qed.

(* [comment removed for export] *)
Lemma body_entry : forall l M', MI M' -> cell BSEGS M' q 4 (W max) -> stable l -> rget l 28 = W (sha q) ->
  reach BSEGS rom (Z_to_bv 64 0x430e80) l M' Post.
Proof using All.
  intros l M' HMI Cq Hst H28. pose proof bounds as B. unfold B_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x430ea4; 0x430fbc].
  eexists. split; [apply load_cell; [exact Cq | lia]|].
  rewrite (Wu max) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small max) by lia.
  rewrite lw_W by lia. rewrite ?(Wu n) by lia.
  split; intros Hb.
  - eapply (pre_outer 0 0); [exact HMI | prove_stable2 Hse | reflexivity | reflexivity | lia | lia].
  - assert (Hp0 : 0 < p) by (destruct Hpnz; lia).
    rewrite (sltu0_W p) by lia. replace (Z.eqb p 0) with false by (symmetry; apply Z.eqb_neq; lia).
    eapply (scan_loop (Z.to_nat (n - 0)) 0 0); [lia | lia | lia | exact HMI | prove_SI Hse].
Qed.

(* [comment removed for export] *)
Lemma entry_chk : forall l M', MI M' -> cell BSEGS M' q 4 (W max) -> stable l -> rget l 28 = W (sha q) ->
  reach BSEGS rom (Z_to_bv 64 0x430e30) l M' Post.
Proof using All.
  intros l M' HMI Cq Hst H28. open_stable Hst l. subst.
  wp_dec [0x430e80; 0x430e40]. rewrite slli_W by lia. rewrite ?addi_W. rewrite !Wu by lia.
  split; intros Hb; [clear Hb | exfalso; lia].
  apply body_entry; [exact HMI | exact Cq | prove_stable Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma prologue2 : forall l M', MI M' -> cell BSEGS M' q 4 (W max) -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 176) -> rget l 8 = W sp0 -> rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  reach BSEGS rom (Z_to_bv 64 0x430df8) l M' Post.
Proof using All.
  intros l M' HMI Cq Hl Hse H2 H8 H10 H11 H12 H13. pose proof bounds as B. unfold B_IMG_END, HIMEM_END in *.
  destruct (MI_rt _ HMI) as (G1 & G2 & _).
  destruct (sh_load_k BSEGS M' q 4 (MI_okq _ HMI) ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Hm8.
  assert (Ean : v_andi (W q) 3 = W 0).
  { rewrite <- (W_u (v_andi (W q) 3)). f_equal. change 3 with (Z.ones 2). rewrite u_andi_ones_W by lia. exact Hqal. }
  unfold G_SB, C_SB in *.
  regs_open l Hl. subst.
  wp_dec [0x430e30; 0x4312ac; 0x4312bc]. rewrite Ean. rewrite ?(Wu q), ?(Wu 0) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; intros Hbr; [exfalso; apply Hbr; reflexivity|]. clear Hbr.
  mem_auto. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (apply entry_chk; [exact HMI | exact Cq | | reflexivity];
     unfold stable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
     cbn [rget lget]; repeat split; try reflexivity; f_equal; lia).
Qed.

Lemma M1_qcell : cell BSEGS M1 q 4 (W max).
Proof using All.
  pose proof bounds as B. unfold B_IMG_END, HIMEM_END in *.
  eapply cell_unch; [apply M1_unch_fr | lia | (cbn; lia) | | exact Hqc].
  intros x Hx. cbn in Hx. unfold inr in *. lia.
Qed.

(* [comment removed for export] *)
Lemma decode_body : forall l, l = l0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  reach BSEGS rom (Z_to_bv 64 0x430dbc) l M Post.
Proof using All.
  intros l El H10 H11 H12 H13.
  assert (Hl : length l = 32%nat) by (rewrite El; exact Hl0).
  assert (Hse0 : same_except [] l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. clear El.
  pose proof Hfr as Hfr'. unfold B_IMG_END in *.
  regs_open l Hl. subst. se_subst Hse0.
  wp_dec [0x430df8]. mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ => change Mx with M1 end.
  apply prologue2; [apply MI_M1 | apply M1_qcell | reflexivity | | cbn [rget lget]; f_equal; lia
                   | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity].
  eapply same_except_weaken with (ks := KSD); [|intros; assumption].
  intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail]|]).
  rewrite !rget_beyond by (cbn [length]; rewrite ?Hl0; lia). reflexivity.
Qed.

End Decode.

(* [comment removed for export] *)
Theorem decode_cps : forall rom Post M sp0 p n d q max l,
  rt_ok M ->
  0 <= n < 2 ^ 31 -> memrange p n -> addr_ok M p n -> rd_ok M p n ->
  0 <= max <= 512 -> cell BSEGS M q 4 (W max) ->
  B_IMG_END <= sp0 - 2400 /\ sp0 < 2 ^ 63 -> (sp0 <= SB \/ HIMEM_BEG <= sp0 - 2400) ->
  wr_ok BSEGS M (sp0 - 2400) 2400 ->
  B_IMG_END <= d -> memrange d (4 * max) -> addr_ok M d (4 * max) -> (0 < max -> shw_ok M d (4 * max)) ->
  wr_ok BSEGS M d (4 * max) ->
  B_IMG_END <= q -> memrange q 4 -> addr_ok M q 4 -> wr_ok BSEGS M q 4 ->
  (d + 4 * max <= sp0 - 2400 \/ sp0 <= d) -> (q + 4 <= sp0 - 2400 \/ sp0 <= q) ->
  (n = 0 \/ 0 < p) -> d mod 4 = 0 -> q mod 4 = 0 ->
  length l = 32%nat -> rget l 2 = W sp0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  (forall l' M', length l' = 32%nat -> same_except KSdec l l' ->
     (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
     (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell BSEGS M' q 4 (W w)) ->
     unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x430dbc) l M Post.
Proof.
  intros rom Post M sp0 p n d q max l; intros.
  eapply (decode_body rom Post M sp0 p n d q max) with (l0 := l); eauto.
Qed.

