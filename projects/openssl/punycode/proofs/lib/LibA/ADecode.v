(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem DecArith.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AImg ACheck AAsanMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_dec stops := wp_go 0x407b38 291%nat C_decode_eq C_decode stops.

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
Hypothesis Hqc : cell ASEGS M q 4 (W max).
Hypothesis Hsp : A_IMG_END <= sp0 - 2400 /\ sp0 < 2 ^ 63.
Hypothesis Hspz : sp0 <= SB \/ HIMEM_BEG <= sp0 - 2400.
Hypothesis Hfr : wr_ok ASEGS M (sp0 - 2400) 2400.
Hypothesis Hd : A_IMG_END <= d.
Hypothesis Hmd : memrange d (4 * max).
Hypothesis Hokd : addr_ok M d (4 * max).
Hypothesis Hshd : 0 < max -> shw_ok M d (4 * max).
Hypothesis Hwd : wr_ok ASEGS M d (4 * max).
Hypothesis Hq : A_IMG_END <= q.
Hypothesis Hmq : memrange q 4.
Hypothesis Hokq : addr_ok M q 4.
Hypothesis Hwq : wr_ok ASEGS M q 4.
Hypothesis Hdj1 : d + 4 * max <= sp0 - 2400 \/ sp0 <= d.
Hypothesis Hdj2 : q + 4 <= sp0 - 2400 \/ sp0 <= q.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W sp0.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSdec l0 l' ->
  (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
  (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell ASEGS M' q 4 (W w)) ->
  unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
  reach ASEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

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
Proof. unfold M1, A_IMG_END in *. solve_grows. Qed.

Lemma M1_unch : unch M M1 (dec_FP sp0 d q max).
Proof. unfold M1, A_IMG_END in *. solve_unch ltac:(unfold dec_FP, inr in *; lia). Qed.

Lemma M1_unch_fr : unch M M1 (fun x => inr x (sp0 - 104) 104).
Proof. unfold M1, A_IMG_END in *. solve_unch ltac:(unfold inr in *; lia). Qed.

Lemma MI_M1 : MI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma M1_saved : forall k off, In (k, off) SAVE_SLOTS ->
  cell ASEGS M1 (sp0 + -176 + off) 8 (rget l0 k).
Proof.
  intros k off Hin. unfold A_IMG_END in *. unfold SAVE_SLOTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; unfold M1; solve_cell|]). contradiction.
Qed.

Lemma MI_saved : forall M' k off, MI M' ->
  In (k, off) SAVE_SLOTS ->
  cell ASEGS M' (sp0 + -176 + off) 8 (rget l0 k).
Proof.
  intros M' k off [HU HG] Hin. unfold A_IMG_END in *.
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

Lemma FP_app : forall y, dec_FP sp0 d q max y -> A_IMG_END <= bv_unsigned y.
Proof. intros y Hy. unfold dec_FP, inr, A_IMG_END in *. lia. Qed.

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

Lemma MI_wr_d : forall M', MI M' -> wr_ok ASEGS M' d (4 * max).
Proof. intros M' HMI. eapply wr_ok_grows; [apply (MI_grows _ HMI) | exact Hwd]. Qed.

Lemma MI_wr_q : forall M', MI M' -> wr_ok ASEGS M' q 4.
Proof. intros M' HMI. eapply wr_ok_grows; [apply (MI_grows _ HMI) | exact Hwq]. Qed.

Lemma MI_wr_sp : forall M', MI M' -> wr_ok ASEGS M' (sp0 - 2400) 2296.
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
  pose proof (MI_saved _ 1%nat 168 HMI ltac:(cbv; tauto)) as Csv1;
  pose proof (MI_saved _ 8%nat 160 HMI ltac:(cbv; tauto)) as Csv8;
  pose proof (MI_saved _ 9%nat 152 HMI ltac:(cbv; tauto)) as Csv9;
  pose proof (MI_saved _ 18%nat 144 HMI ltac:(cbv; tauto)) as Csv18;
  pose proof (MI_saved _ 19%nat 136 HMI ltac:(cbv; tauto)) as Csv19;
  pose proof (MI_saved _ 20%nat 128 HMI ltac:(cbv; tauto)) as Csv20;
  pose proof (MI_saved _ 21%nat 120 HMI ltac:(cbv; tauto)) as Csv21;
  pose proof (MI_saved _ 22%nat 112 HMI ltac:(cbv; tauto)) as Csv22;
  pose proof (MI_saved _ 23%nat 104 HMI ltac:(cbv; tauto)) as Csv23;
  pose proof (MI_saved _ 24%nat 96 HMI ltac:(cbv; tauto)) as Csv24;
  pose proof (MI_saved _ 25%nat 88 HMI ltac:(cbv; tauto)) as Csv25;
  pose proof (MI_saved _ 26%nat 80 HMI ltac:(cbv; tauto)) as Csv26;
  pose proof (MI_saved _ 27%nat 72 HMI ltac:(cbv; tauto)) as Csv27.

(* [comment removed for export] *)
Lemma epilogue : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 176) ->
  (rget l 10 = W 0 \/ rget l 10 = W 1) ->
  (rget l 10 = W 1 -> exists w, 0 <= w <= max /\ cell ASEGS M' q 4 (W w)) ->
  reach ASEGS rom (Z_to_bv 64 0x407bb0) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2 Ha0 Hw. pose_saved HMI. destruct (MI_final _ HMI) as [HU HG].
  unfold A_IMG_END in *. regs_open l Hl. subst sp.
  wp_dec (@nil Z). mem_auto.
  apply K; [reflexivity | | exact Ha0 | exact Hw | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fail_exit : forall l M', MI M' -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 176) ->
  reach ASEGS rom (Z_to_bv 64 0x407bac) l M' Post.
Proof.
  intros l M' HMI Hl Hse H2. regs_open l Hl. subst sp.
  wp_dec [0x407bb0].
  apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E].
Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSD l0 l /\ rget l 2 = W (sp0 - 176) /\ rget l 8 = W sp0
  /\ rget l 9 = W q /\ rget l 19 = W n /\ rget l 20 = W p /\ rget l 22 = W (sha q) /\ rget l 23 = W SB.

Ltac open_stable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H9 & ?H19 & ?H20 & ?H22 & ?H23);
  regs_open l Hl.

Ltac prove_stable Hse :=
  unfold stable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
  cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Ltac gload Hrd :=
  lazymatch type of Hrd with
  | rd_ok ?M0 _ _ =>
    lazymatch goal with
    | |- exists v, load_ok _ ?Mx (Z_to_bv 64 ?a) ?k v /\ _ =>
        let v := fresh "gv" in let Hv := fresh "Hgv" in
        assert (exists v, load_ok ASEGS Mx (W a) k v) as [v Hv]
          by (eapply load_rd; [eapply (rd_ok_grows M0); [solve_grows | exact Hrd] | lia..]);
        exists v; split; [exact Hv|]; clear Hv
    end
  end.

Ltac fold_call target :=
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) ?k) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) k) with (Z_to_bv 64 target) by reflexivity end.

Ltac epi_fail HMI Hse :=
  apply epilogue; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | left; reflexivity | intros E; cbn [rget lget] in E; discriminate E].

Ltac fail_leaf HMI Hse :=
  apply fail_exit; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].

(* [comment removed for export] *)
Lemma success_store : forall l M' wo, MI M' -> stable l -> rget l 25 = W wo -> 0 <= wo <= max ->
  reach ASEGS rom (Z_to_bv 64 0x407f74) l M' Post.
Proof.
  intros l M' wo HMI Hst H25 Hwo. pose proof (MI_wr_q _ HMI) as Hwq'. pose proof bounds as B.
  unfold A_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x407bb0]. mem_auto.
  apply epilogue; [ | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
                  | right; reflexivity | intros _; exists wo; split; [lia | apply cell_store_same; lia] ].
  apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia |].
  intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FPin, inr in *. lia.
Qed.

(* [comment removed for export] *)
Lemma success_exit : forall l M' wo, MI M' -> stable l -> rget l 25 = W wo -> 0 <= wo <= max ->
  reach ASEGS rom (Z_to_bv 64 0x407f6c) l M' Post.
Proof.
  intros l M' wo HMI Hst H25 Hwo. pose proof bounds as B.
  destruct (sh_load_k ASEGS M' q 4 (MI_okq _ HMI) ltac:(lia) ltac:(lia) ltac:(lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Hm8.
  unfold A_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x407bb0; 0x407f74].
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (eapply (success_store _ _ wo); [exact HMI | prove_stable Hse | reflexivity | lia]).
Qed.

(* [comment removed for export] *)
Definition stable2 (l : regfile) : Prop :=
  stable l /\ rget l 12 = W d /\ rget l 29 = W max.

Definition OI (pi wo : Z) (l : regfile) : Prop :=
  stable2 l /\ rget l 30 = W n /\ rget l 26 = W pi /\ rget l 11 = W wo /\ 0 <= pi < n /\ 0 <= wo <= max.

Ltac open_stable2 H l :=
  let Hst := fresh "Hst" in
  destruct H as (Hst & ?H12 & ?H29); open_stable Hst l.

Ltac prove_stable2 Hse :=
  unfold stable2; split; [prove_stable Hse|]; cbn [rget lget]; split; reflexivity.

(* [comment removed for export] *)
Definition BI (s10v wo' : Z) (l : regfile) : Prop :=
  stable2 l /\ rget l 30 = W n /\ rget l 11 = W wo' /\ rget l 26 = W s10v.

Ltac open_BI H l :=
  let Hst := fresh "Hst2" in
  destruct H as (Hst & ?H30 & ?H11 & ?H26); open_stable2 Hst l.

Ltac prove_BI Hse :=
  unfold BI; split; [prove_stable2 Hse|]; cbn [rget lget]; repeat split; try reflexivity.

Section Tail.
Variables (pi' wo : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Kout : forall l M', MI M' -> OI pi' (wo + 1) l -> reach ASEGS rom (Z_to_bv 64 0x407d48) l M' Post.

(* [comment removed for export] *)
Lemma tail2 : forall l M' r, MI M' -> stable l -> 0 <= r <= wo -> wo < max ->
  rget l 26 = W pi' -> rget l 25 = W (wo + 1) -> rget l 21 = W (d + 4 * r) ->
  cell ASEGS M' (sp0 + -136) 8 (W d) -> cell ASEGS M' (sp0 + -144) 8 (W max) -> cell ASEGS M' (sp0 + -152) 8 (W n) ->
  reach ASEGS rom (Z_to_bv 64 0x407efc) l M' Post.
Proof using All.
  intros l M' r HMI Hst Hr Hwm H26 H25 H21 Cd Cmax Cn.
  pose proof (MI_wr_d _ HMI) as Hwd'. pose proof (MI_rd_sp _ HMI) as Hrsp. pose proof bounds as B.
  unfold A_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x407d48; 0x407f6c]. rewrite ?addi_W.
  gload Hrsp. gload Hrsp. gload Hrsp.
  split; [eapply wr_ok_store; [exact Hwd' | lia | lia]|].
  gload Hrsp.
  mem_auto. rewrite !Wu by lia.
  match goal with |- context [wbytes M' ?a ?bs] =>
    assert (HMI2 : MI (wbytes M' a bs))
      by (apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia
                          | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]) end.
  split; intros Hb.
  - apply Kout; [exact HMI2|]. unfold OI. split; [prove_stable2 Hse|]. cbn [rget lget].
    repeat split; try reflexivity; lia.
  - eapply (success_exit _ _ (wo + 1)); [exact HMI2 | prove_stable Hse | reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma tail : forall l M', MI M' -> BI pi' wo l -> rget l 25 = W (wo + 1) ->
  reach ASEGS rom (Z_to_bv 64 0x407e90) l M' Post.
Proof using All.
  intros l M' HMI HBI H25.
  pose proof (MI_wr_sp _ HMI) as Hwsp'. pose proof bounds as B.
  unfold A_IMG_END, HIMEM_END in *.
  open_BI HBI l. subst.
  destruct (rem_idx t3 (wo + 1) ltac:(lia)) as (r & Hr & Er).
  wp_dec [0x407bb0]. rewrite !Wu by lia.
  split; intros Hb; [clear Hb|].
  { epi_fail HMI Hse. }
  clear Hb. split; intros Hb.
  { epi_fail HMI Hse. }
  mem_auto. rewrite Er. rewrite (subw_W wo r) by lia. rewrite !scale4_W by lia. rewrite ?add_W, ?addi_W.
  name_mem M2.
  assert (HMI2 : MI M2).
  { unname_mems. repeat (apply MI_store; [ | lia | rewrite length_N_to_le_bytes; lia
        | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]). exact HMI. }
  assert (Cd : cell ASEGS M2 (sp0 + -136) 8 (W d)) by (unname_mems; solve_cell).
  assert (Cmax : cell ASEGS M2 (sp0 + -144) 8 (W max)) by (unname_mems; solve_cell).
  assert (Cn : cell ASEGS M2 (sp0 + -152) 8 (W n)) by (unname_mems; solve_cell).
  clearbody M2. clear Hwsp'.
  pose proof (MI_wr_d _ HMI2) as Hwd'. pose proof (MI_okd _ HMI2) as Hokd'.
  assert (Hmr1 : memrange (d + 4 * r) (4 * (wo - r))).
  { destruct Hmd as [_ Hd']. unfold memrange, LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. }
  assert (Hmr2 : memrange (d + 4 * r + 4) (4 * (wo - r))).
  { destruct Hmd as [_ Hd']. unfold memrange, LOMEM_END, HIMEM_BEG, HIMEM_END in *. lia. }
  fold_call 0x1c2058.
  eapply (amemmove_cps rom Post M2 (d + 4 * r + 4) (d + 4 * r) (4 * (wo - r)) (sp0 - 176));
    [ apply (MI_rt _ HMI2) | lia | exact Hmr1 | exact Hmr2 | lia
    | eapply addr_ok_sub; [exact Hokd' | lia | lia]
    | eapply addr_ok_sub; [exact Hokd' | lia | lia]
    | intros Hpos; eapply shw_ok_sub; [apply (MI_shd _ HMI2); lia | lia | lia | lia]
    | intros Hpos; eapply shw_ok_sub; [apply (MI_shd _ HMI2); lia | lia | lia | lia]
    | eapply rd_ok_sub; [apply (wr_ok_rd_ok M2 d (4 * max) Hwd'); unfold A_IMG_END; lia | lia | lia]
    | eapply wr_ok_sub; [exact Hwd' | lia | lia]
    | unfold A_IMG_END; lia
    | unfold SB, HIMEM_BEG in *; lia
    | eapply wr_ok_sub; [apply (MI_wr_sp _ HMI2) | lia | lia]
    | lia
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l'' M'' Hl'' Hse'' HU'' HG''. cbn [rget lget].
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) 0) with (Z_to_bv 64 0x407eec) by reflexivity end.
  regs_open l'' Hl''. se_subst Hse''. clear Hse''.
  assert (HMI3 : MI M'').
  { destruct HMI2 as [HU2 HG2]. split; [|eapply mem_grows_trans; eassumption].
    eapply unch_trans; [exact HU2|]. eapply unch_weaken; [exact HU''|].
    intros x Hx. unfold AAsanMemmove.FP, FPin, inr in *. lia. }
  assert (Cd' : cell ASEGS M'' (sp0 + -136) 8 (W d)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold AAsanMemmove.FP, inr in *; lia | exact Cd]. }
  assert (Cmax' : cell ASEGS M'' (sp0 + -144) 8 (W max)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold AAsanMemmove.FP, inr in *; lia | exact Cmax]. }
  assert (Cn' : cell ASEGS M'' (sp0 + -152) 8 (W n)).
  { eapply cell_unch; [exact HU'' | lia | lia | intros x Hx; unfold AAsanMemmove.FP, inr in *; lia | exact Cn]. }
  clear Cd Cmax Cn Hwd' Hokd'.
  destruct (sh_load_k ASEGS M'' (d + 4 * r) 4 ltac:(eapply addr_ok_sub; [apply (MI_okd _ HMI3) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (d + 4 * r) 8 ltac:(lia)) as Hm8.
  wp_dec [0x407efc]. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (eapply (tail2 _ _ r); [exact HMI3 | prove_stable Hse | lia | lia | reflexivity | reflexivity | reflexivity
                           | exact Cd' | exact Cmax' | exact Cn']).
Qed.
End Tail.

Section Adapt.
Variables (pi' wo : Z).
Hypothesis Hpi' : 0 <= pi' <= n.
Hypothesis Hwo : 0 <= wo <= max.
Hypothesis Ktail : forall l M', MI M' -> BI pi' wo l -> rget l 25 = W (wo + 1) ->
  reach ASEGS rom (Z_to_bv 64 0x407e90) l M' Post.

(* [comment removed for export] *)
Lemma adapt_loop : forall k l M', bv_unsigned (rget l 10) mod 2 ^ 32 = Z.of_nat k ->
  MI M' -> BI pi' wo l -> rget l 25 = W (wo + 1) ->
  reach ASEGS rom (Z_to_bv 64 0x407e5c) l M' Post.
Proof using All.
  induction k as [k IH] using lt_wf_ind; intros l M' Hk HMI HBI H25.
  open_BI HBI l. subst. cbn [rget lget] in Hk.
  wp_dec [0x407e5c; 0x407e90]. split; intros Hb.
  - pose proof (adapt_decrease a0 a5 s5 Hb) as Hdec.
    match type of Hdec with ?e < _ =>
      assert (He : 0 <= e) by (apply Z.mod_pos_bound; lia);
      eapply (IH (Z.to_nat e)); [lia | cbn [rget lget]; lia | exact HMI | prove_BI Hse | reflexivity] end.
  - clear Hb. apply Ktail; [exact HMI | prove_BI Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma brk2 : forall l M', MI M' -> BI pi' wo l -> reach ASEGS rom (Z_to_bv 64 0x407e40) l M' Post.
Proof using All.
  intros l M' HMI HBI. pose proof (MI_rd_sp _ HMI) as Hrsp. unfold A_IMG_END in *.
  open_BI HBI l. subst.
  assert (Es9 : v_addiw (W wo) 1 = W (wo + 1)) by (apply addiw_W; lia).
  wp_dec [0x407e5c; 0x407e90]. rewrite ?addi_W. gload Hrsp. rewrite ?Es9.
  split; intros Hb; clear Hb.
  - apply Ktail; [exact HMI | prove_BI Hse | reflexivity].
  - match goal with |- reach _ _ _ ?l' _ _ =>
      eapply (adapt_loop (Z.to_nat (bv_unsigned (rget l' 10) mod 2 ^ 32))) end;
      [ cbn [rget lget]; rewrite Z2Nat.id; [reflexivity | apply Z.mod_pos_bound; lia]
      | exact HMI | prove_BI Hse | reflexivity ].
Qed.

(* [comment removed for export] *)
Lemma brk : forall l M', MI M' -> BI pi' wo l -> reach ASEGS rom (Z_to_bv 64 0x407e1c) l M' Post.
Proof using All.
  intros l M' HMI HBI. pose proof (MI_wr_sp _ HMI) as Hwsp'. pose proof (MI_rd_sp _ HMI) as Hrsp.
  unfold A_IMG_END in *.
  open_BI HBI l. subst.
  wp_dec [0x407e40]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Hwsp' | lia | lia]|].
  match goal with |- context [wbytes M' ?a ?bs] =>
    assert (HMI2 : MI (wbytes M' a bs))
      by (apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia
                          | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]) end.
  split; intros Hb; clear Hb.
  - gload Hrsp. apply brk2; [exact HMI2 | prove_BI Hse].
  - apply brk2; [exact HMI2 | prove_BI Hse].
Qed.
End Adapt.

Section Digits.
Variables (wo lo : Z).
Hypothesis Hlo : 0 <= lo.
Hypothesis Kbrk : forall s10v l M', lo < s10v <= n -> MI M' -> BI s10v wo l ->
  reach ASEGS rom (Z_to_bv 64 0x407e1c) l M' Post.

Section Iter.
Variable idx : Z.
Hypothesis Hidx : lo <= idx < n.
Hypothesis Kd1 : forall l M', idx + 1 < n -> MI M' -> BI (idx + 2) wo l -> rget l 10 = W (idx + 1) ->
  reach ASEGS rom (Z_to_bv 64 0x407d70) l M' Post.

(* [comment removed for export] *)
Lemma d3 : forall l M', MI M' -> BI (idx + 1) wo l -> reach ASEGS rom (Z_to_bv 64 0x407dd0) l M' Post.
Proof using All.
  intros l M' HMI HBI. open_BI HBI l. subst.
  wp_dec [0x407bac; 0x407e1c; 0x407d70]. rewrite zext32_W by lia. rewrite !Wu by lia.
  split; intros Hb; clear Hb.
  - apply (Kbrk (idx + 1)); [lia | exact HMI | prove_BI Hse].
  - split; intros Hb; clear Hb; [fail_leaf HMI Hse|].
    split; intros Hb; [fail_leaf HMI Hse|].
    rewrite addiw_W by lia.
    apply Kd1; [lia | exact HMI | prove_BI Hse; f_equal; lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma d2 : forall l M', MI M' -> BI (idx + 1) wo l -> reach ASEGS rom (Z_to_bv 64 0x407da4) l M' Post.
Proof using All.
  intros l M' HMI HBI. open_BI HBI l. subst.
  wp_dec [0x407bac; 0x407dd0].
  repeat (split; intros ?Hb); first [ fail_leaf HMI Hse | apply d3; [exact HMI | prove_BI Hse] ].
Qed.

(* [comment removed for export] *)
Lemma d1 : forall l M', MI M' -> BI (idx + 1) wo l -> rget l 10 = W (p + idx) ->
  reach ASEGS rom (Z_to_bv 64 0x407d84) l M' Post.
Proof using All.
  intros l M' HMI HBI H10. pose proof (MI_rd _ HMI) as Hrd'. pose proof bounds as B. unfold HIMEM_END in *.
  open_BI HBI l. subst.
  wp_dec [0x407bac; 0x407da4].
  assert (exists v, load_ok ASEGS M' (W (p + idx)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  repeat (split; intros ?Hb); first [ fail_leaf HMI Hse | apply d2; [exact HMI | prove_BI Hse] ].
Qed.

(* [comment removed for export] *)
Lemma d0 : forall l M', MI M' -> BI (idx + 1) wo l -> rget l 10 = W idx ->
  reach ASEGS rom (Z_to_bv 64 0x407d70) l M' Post.
Proof using All.
  intros l M' HMI HBI H10. pose proof bounds as B. unfold HIMEM_END in B.
  destruct (sh_load_k ASEGS M' (p + idx) 1 ltac:(eapply addr_ok_sub; [apply (MI_okp _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (p + idx) 8 ltac:(lia)) as Hm8.
  open_BI HBI l. subst.
  wp_dec [0x407d84]. rewrite ?add_W. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros Hbad; exfalso; lia | intros _] | intros _];
    (apply d1; [exact HMI | prove_BI Hse | reflexivity]).
Qed.
End Iter.

Lemma digit_loop : forall k idx l M', n - idx = Z.of_nat k -> lo <= idx < n ->
  MI M' -> BI (idx + 1) wo l -> rget l 10 = W idx ->
  reach ASEGS rom (Z_to_bv 64 0x407d70) l M' Post.
Proof using All.
  induction k as [k IH] using lt_wf_ind; intros idx l M' Hk Hidx HMI HBI H10.
  apply (d0 idx Hidx); [|exact HMI | exact HBI | exact H10].
  intros l2 M2 Hlt HMI2 HBI2 H10'.
  eapply (IH (Z.to_nat (n - (idx + 1)))) with (idx := idx + 1); [lia | lia | lia | exact HMI2 | | exact H10'].
  replace (idx + 1 + 1) with (idx + 2) by lia. exact HBI2.
Qed.
End Digits.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outer_loop : forall k pi wo l M', n - pi = Z.of_nat k -> MI M' -> OI pi wo l ->
  reach ASEGS rom (Z_to_bv 64 0x407d48) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros pi wo l M' Hk HMI HOI.
  destruct HOI as (Hst2 & H30 & H26 & H11 & Hpi & Hwo).
  open_stable2 Hst2 l. subst.
  wp_dec [0x407bac; 0x407d70]. rewrite zext32_W by lia. rewrite !Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb. rewrite addiw_W by lia.
  eapply digit_loop with (wo := wo) (lo := pi) (idx := pi) (k := Z.to_nat (n - pi));
    [ lia | | lia | lia | exact HMI | prove_BI Hse | reflexivity ].
  (* [comment removed for export] *)
  intros s10v l2 M2 Hs10 HMI2 HBI2.
  eapply brk with (pi' := s10v) (wo := wo); [lia | lia | | exact HMI2 | exact HBI2].
  intros l3 M3 HMI3 HBI3 H25'.
  eapply tail with (pi' := s10v) (wo := wo); try assumption; try lia.
  intros l4 M4 HMI4 HOI4.
  eapply (IH (Z.to_nat (n - s10v))); [lia | | exact HMI4 | exact HOI4]. lia.
Qed.

(* [comment removed for export] *)
Lemma pre_outer : forall pi wo l M', MI M' -> stable2 l -> rget l 26 = W pi -> rget l 25 = W wo ->
  0 <= pi <= n -> 0 <= wo <= max ->
  reach ASEGS rom (Z_to_bv 64 0x407cf8) l M' Post.
Proof.
  intros pi wo l M' HMI Hst2 H26 H25 Hpi Hwo. pose proof (MI_wr_sp _ HMI) as Hwsp'. unfold A_IMG_END in *.
  open_stable2 Hst2 l. subst.
  wp_dec [0x407d48; 0x407f6c]. rewrite addiw_W by lia. rewrite !Wu by lia.
  split; intros Hb.
  - eapply (success_exit _ _ wo); [exact HMI | prove_stable Hse | reflexivity | lia].
  - mem_auto.
    eapply (outer_loop (Z.to_nat (n - pi)) pi wo); [lia | |].
    + repeat (apply MI_store; [ | lia | rewrite length_N_to_le_bytes; lia
        | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]). exact HMI.
    + unfold OI. split; [prove_stable2 Hse|]. cbn [rget lget]. repeat split; try reflexivity; try lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition CI (bc j : Z) (l : regfile) : Prop :=
  stable2 l /\ rget l 25 = W bc /\ rget l 5 = W (bc - j) /\ rget l 10 = W (d + 4 * j) /\ rget l 13 = W (d + 4 * j)
  /\ rget l 11 = W (p + j) /\ rget l 14 = W (p + j).

Ltac open_CI H l :=
  let Hst := fresh "Hst2" in
  destruct H as (Hst & ?H25 & ?H5 & ?H10 & ?H13 & ?H11 & ?H14); open_stable2 Hst l.

Ltac prove_CI Hse :=
  unfold CI; split; [prove_stable2 Hse|]; cbn [rget lget]; repeat split; try reflexivity; f_equal; lia.

Section Copy.
Variables (bc j : Z).
Hypothesis Hbc : bc <= max /\ bc < n.
Hypothesis Hj : 0 <= j < bc.
Hypothesis Kc : forall l M', j + 1 < bc -> MI M' -> CI bc (j + 1) l ->
  reach ASEGS rom (Z_to_bv 64 0x407c78) l M' Post.

(* [comment removed for export] *)
Lemma c2 : forall l M', MI M' -> CI bc j l -> reach ASEGS rom (Z_to_bv 64 0x407ca0) l M' Post.
Proof using All.
  intros l M' HMI HCI. pose proof (MI_wr_d _ HMI) as Hwd'. pose proof bounds as B.
  unfold A_IMG_END, HIMEM_END in *.
  open_CI HCI l. subst.
  wp_dec [0x407c78; 0x407cf8]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Hwd' | lia | lia]|].
  match goal with |- context [wbytes M' ?a ?bs] =>
    assert (HMI2 : MI (wbytes M' a bs))
      by (apply MI_store; [exact HMI | lia | rewrite length_N_to_le_bytes; lia
                          | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FPin, inr in *; lia]) end.
  rewrite !Wu by lia.
  split; intros Hb.
  - apply Kc; [lia | exact HMI2 | prove_CI Hse].
  - rewrite addiw_W by lia.
    eapply (pre_outer (bc + 1) bc); [exact HMI2 | prove_stable2 Hse | reflexivity | reflexivity | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma c1 : forall l M', MI M' -> CI bc j l -> reach ASEGS rom (Z_to_bv 64 0x407c88) l M' Post.
Proof using All.
  intros l M' HMI HCI. pose proof (MI_rd _ HMI) as Hrd'. pose proof bounds as B. unfold HIMEM_END in B.
  destruct (sh_load_k ASEGS M' (d + 4 * j) 4 ltac:(eapply addr_ok_sub; [apply (MI_okd _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (d + 4 * j) 8 ltac:(lia)) as Hm8.
  open_CI HCI l. subst.
  wp_dec [0x407bac; 0x407ca0].
  assert (exists v, load_ok ASEGS M' (W (p + j)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  split; intros Hb; clear Hb; [fail_leaf HMI Hse|].
  rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (apply c2; [exact HMI | prove_CI Hse]).
Qed.

(* [comment removed for export] *)
Lemma c0 : forall l M', MI M' -> CI bc j l -> reach ASEGS rom (Z_to_bv 64 0x407c78) l M' Post.
Proof using All.
  intros l M' HMI HCI. pose proof bounds as B. unfold HIMEM_END in B.
  destruct (sh_load_k ASEGS M' (p + j) 1 ltac:(eapply addr_ok_sub; [apply (MI_okp _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (p + j) 8 ltac:(lia)) as Hm8.
  open_CI HCI l. subst.
  wp_dec [0x407c88]. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros Hbad; exfalso; lia | intros _] | intros _];
    (apply c1; [exact HMI | prove_CI Hse]).
Qed.
End Copy.

Lemma copy_loop : forall k j bc l M', bc - j = Z.of_nat k -> 0 <= j < bc -> bc <= max /\ bc < n ->
  MI M' -> CI bc j l -> reach ASEGS rom (Z_to_bv 64 0x407c78) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros j bc l M' Hk Hj Hbc HMI HCI.
  apply (c0 bc j Hbc Hj); [|exact HMI | exact HCI].
  intros l2 M2 Hlt HMI2 HCI2.
  eapply (IH (Z.to_nat (bc - (j + 1)))) with (j := j + 1) (bc := bc); [lia | lia | lia | exact Hbc | exact HMI2 | exact HCI2].
Qed.

(* [comment removed for export] *)
Lemma post_scan : forall bc l M', MI M' -> stable2 l -> rget l 25 = W bc -> bc = 0 \/ 0 < bc < n ->
  reach ASEGS rom (Z_to_bv 64 0x407c58) l M' Post.
Proof.
  intros bc l M' HMI Hst2 H25 Hbc. open_stable2 Hst2 l. subst.
  wp_dec [0x407c78; 0x407bac; 0x407cf8]. rewrite !Wu by lia.
  split; intros Hb.
  - eapply (pre_outer 0 bc); [exact HMI | prove_stable2 Hse | reflexivity | reflexivity | lia | lia].
  - split; intros Hb2.
    + fail_leaf HMI Hse.
    + rewrite zext32_W by lia.
      eapply (copy_loop (Z.to_nat (bc - 0)) 0 bc); [lia | lia | lia | exact HMI | prove_CI Hse].
Qed.

(* [comment removed for export] *)
Definition SI (k bc : Z) (l : regfile) : Prop :=
  stable2 l /\ rget l 10 = W (p + k) /\ rget l 14 = W (p + k) /\ rget l 13 = W (n - k) /\ rget l 11 = W k
  /\ rget l 15 = W bc.

Ltac open_SI H l :=
  let Hst := fresh "Hst2" in
  destruct H as (Hst & ?H10 & ?H14 & ?H13 & ?H11 & ?H15); open_stable2 Hst l.

Ltac prove_SI Hse :=
  unfold SI; split; [prove_stable2 Hse|]; cbn [rget lget]; repeat split; try reflexivity; f_equal; lia.

Section Scan.
Variables (k bc : Z).
Hypothesis Hk : 0 <= k < n.
Hypothesis Hbc : bc = 0 \/ 0 < bc < k.
Hypothesis Ks : forall bc' l M', k + 1 < n -> bc' = 0 \/ 0 < bc' < k + 1 -> MI M' -> SI (k + 1) bc' l ->
  reach ASEGS rom (Z_to_bv 64 0x407c0c) l M' Post.

(* [comment removed for export] *)
Lemma s1 : forall l M', MI M' -> SI k bc l -> reach ASEGS rom (Z_to_bv 64 0x407c1c) l M' Post.
Proof using All.
  intros l M' HMI HSI. pose proof (MI_rd _ HMI) as Hrd'. pose proof bounds as B. unfold HIMEM_END in B.
  open_SI HSI l. subst.
  wp_dec [0x407c0c; 0x407c58].
  assert (exists v, load_ok ASEGS M' (W (p + k)) 1 v) as [v Hv] by (eapply load_rd; [exact Hrd' | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  rewrite ?addi_W. rewrite addiw_W by lia. rewrite !Wu by lia.
  split; intros Hb; clear Hb; (split; intros Hb).
  - apply (Ks k); [lia | lia | exact HMI | prove_SI Hse].
  - eapply (post_scan k); [exact HMI | prove_stable2 Hse | reflexivity | lia].
  - apply (Ks bc); [lia | lia | exact HMI | prove_SI Hse].
  - eapply (post_scan bc); [exact HMI | prove_stable2 Hse | reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma s0 : forall l M', MI M' -> SI k bc l -> reach ASEGS rom (Z_to_bv 64 0x407c0c) l M' Post.
Proof using All.
  intros l M' HMI HSI. pose proof bounds as B. unfold HIMEM_END in B.
  destruct (sh_load_k ASEGS M' (p + k) 1 ltac:(eapply addr_ok_sub; [apply (MI_okp _ HMI) | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (p + k) 8 ltac:(lia)) as Hm8.
  open_SI HSI l. subst.
  wp_dec [0x407c1c]. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (apply s1; [exact HMI | prove_SI Hse]).
Qed.
End Scan.

Lemma scan_loop : forall m k bc l M', n - k = Z.of_nat m -> 0 <= k < n -> bc = 0 \/ 0 < bc < k ->
  MI M' -> SI k bc l -> reach ASEGS rom (Z_to_bv 64 0x407c0c) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros k bc l M' Hm Hk Hbc HMI HSI.
  apply (s0 k bc Hk Hbc); [|exact HMI | exact HSI].
  intros bc' l2 M2 Hlt Hbc' HMI2 HSI2.
  eapply (IH (Z.to_nat (n - (k + 1)))) with (k := k + 1) (bc := bc'); [lia | lia | lia | exact Hbc' | exact HMI2 | exact HSI2].
Qed.

(* [comment removed for export] *)
Lemma body_entry : forall l M', MI M' -> cell ASEGS M' q 4 (W max) -> stable l -> rget l 12 = W d ->
  reach ASEGS rom (Z_to_bv 64 0x407bec) l M' Post.
Proof.
  intros l M' HMI Cq Hst H12. pose proof bounds as B. unfold A_IMG_END, HIMEM_END in *.
  open_stable Hst l. subst.
  wp_dec [0x407c0c; 0x407cf8].
  eexists. split; [apply load_cell; [exact Cq | lia]|].
  rewrite (Wu max) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small max) by lia.
  rewrite lw_W by lia. rewrite !Wu by lia.
  split; intros Hb.
  - eapply (pre_outer 0 0); [exact HMI | prove_stable2 Hse | reflexivity | reflexivity | lia | lia].
  - eapply (scan_loop (Z.to_nat (n - 0)) 0 0); [lia | lia | lia | exact HMI | prove_SI Hse].
Qed.

(* [comment removed for export] *)
Lemma entry_chk : forall l M', MI M' -> cell ASEGS M' q 4 (W max) -> stable l -> rget l 12 = W d ->
  reach ASEGS rom (Z_to_bv 64 0x407b9c) l M' Post.
Proof.
  intros l M' HMI Cq Hst H12. open_stable Hst l. subst.
  wp_dec [0x407bec; 0x407bac]. rewrite slli_W by lia. rewrite ?addi_W. rewrite !Wu by lia.
  split; intros Hb; [clear Hb | exfalso; lia].
  apply body_entry; [exact HMI | exact Cq | prove_stable Hse | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma prologue2 : forall l M', MI M' -> cell ASEGS M' q 4 (W max) -> length l = 32%nat -> same_except KSD l0 l ->
  rget l 2 = W (sp0 - 176) -> rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  reach ASEGS rom (Z_to_bv 64 0x407b70) l M' Post.
Proof.
  intros l M' HMI Cq Hl Hse H2 H10 H11 H12 H13. pose proof bounds as B. unfold HIMEM_END in B.
  destruct (MI_rt _ HMI) as (G1 & G2 & _).
  destruct (sh_load_k ASEGS M' q 4 (MI_okq _ HMI) ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Hm8.
  unfold G_SB, C_SB in *.
  regs_open l Hl. subst.
  wp_dec [0x407b9c]. mem_auto. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
    (apply entry_chk; [exact HMI | exact Cq | | reflexivity];
     unfold stable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
     cbn [rget lget]; repeat split; try reflexivity; f_equal; lia).
Qed.

Lemma M1_qcell : cell ASEGS M1 q 4 (W max).
Proof.
  pose proof bounds as B. unfold A_IMG_END, HIMEM_END in *.
  eapply cell_unch; [apply M1_unch_fr | lia | (cbn; lia) | | exact Hqc].
  intros x Hx. cbn in Hx. unfold inr in *. lia.
Qed.

(* [comment removed for export] *)
Lemma decode_body : forall l, l = l0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  reach ASEGS rom (Z_to_bv 64 0x407b38) l M Post.
Proof.
  intros l El H10 H11 H12 H13.
  assert (Hl : length l = 32%nat) by (rewrite El; exact Hl0).
  assert (Hse0 : same_except [] l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. clear El.
  pose proof Hfr as Hfr'. unfold A_IMG_END in *.
  regs_open l Hl. subst. se_subst Hse0.
  wp_dec [0x407b70]. mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ => change Mx with M1 end.
  apply prologue2; [apply MI_M1 | apply M1_qcell | reflexivity | | cbn [rget lget]; f_equal; lia
                   | reflexivity | reflexivity | reflexivity | reflexivity].
  eapply same_except_weaken with (ks := KSD); [|intros; assumption].
  intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail]|]).
  rewrite !rget_beyond by (cbn [length]; rewrite ?Hl0; lia). reflexivity.
Qed.

End Decode.

(* [comment removed for export] *)
Theorem decode_cps : forall rom Post M sp0 p n d q max l,
  rt_ok M ->
  0 <= n < 2 ^ 31 -> memrange p n -> addr_ok M p n -> rd_ok M p n ->
  0 <= max <= 512 -> cell ASEGS M q 4 (W max) ->
  A_IMG_END <= sp0 - 2400 /\ sp0 < 2 ^ 63 -> (sp0 <= SB \/ HIMEM_BEG <= sp0 - 2400) ->
  wr_ok ASEGS M (sp0 - 2400) 2400 ->
  A_IMG_END <= d -> memrange d (4 * max) -> addr_ok M d (4 * max) -> (0 < max -> shw_ok M d (4 * max)) ->
  wr_ok ASEGS M d (4 * max) ->
  A_IMG_END <= q -> memrange q 4 -> addr_ok M q 4 -> wr_ok ASEGS M q 4 ->
  (d + 4 * max <= sp0 - 2400 \/ sp0 <= d) -> (q + 4 <= sp0 - 2400 \/ sp0 <= q) ->
  length l = 32%nat -> rget l 2 = W sp0 ->
  rget l 10 = W p -> rget l 11 = W n -> rget l 12 = W d -> rget l 13 = W q ->
  (forall l' M', length l' = 32%nat -> same_except KSdec l l' ->
     (rget l' 10 = W 0 \/ rget l' 10 = W 1) ->
     (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell ASEGS M' q 4 (W w)) ->
     unch M M' (dec_FP sp0 d q max) -> mem_grows M M' ->
     reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach ASEGS rom (Z_to_bv 64 0x407b38) l M Post.
Proof.
  intros rom Post M sp0 p n d q max l; intros.
  eapply (decode_body rom Post M sp0 p n d q max) with (l0 := l); eauto.
Qed.
