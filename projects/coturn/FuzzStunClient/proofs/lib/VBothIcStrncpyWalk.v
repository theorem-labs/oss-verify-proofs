(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothMemcpyBase BothMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothTls_code VBothIcStrlen_code VBothMusl_code VBothIcMemchr_code VBothIcMemset_code VBothIcStrncpy_code VBothMemsetWalk VBothTlsWalk VBothIcMemsetWalk VBothIcMemchrWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothMuslStrLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VBothMuslStrlen VBothMuslStrncpy.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_c0e7c : v_addi (0x49c00 : word) 4 = Z_to_bv 64 0x49c04. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_c0ea8 : v_addi (0x49c2c : word) 4 = (0x49c30 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_c0f80 : v_addi (0x49d04 : word) 4 = (0x49d08 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_c11a0 : v_addi (0x49f24 : word) 4 = (0x49f28 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_c1268 : v_addi (0x49fec : word) 4 = (0x49ff0 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_c0ea8 : ret_ok (0x49c30 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_c0f80 : ret_ok (0x49d08 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_c11a0 : ret_ok (0x49f28 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_c1268 : ret_ok (0x49ff0 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_c0e7c : v_jalr (Z_to_bv 64 0x49c04) 0 = (0x49c04 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Definition ISN_FRAME : Z := 4408.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition isn_cells (m : word -> option byte) : Prop :=
  cells m
  /\ rdn SEGS m (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xa94b0 0xaf3b8                                     (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0xaf3d5) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xab2d8 0xa3074                                     (* [comment removed for export] *)
  /\ cell m 0xab2f8 0xa2f3c                                     (* [comment removed for export] *)
  /\ cell m 0xab1f0 0xa26ec                                     (* [comment removed for export] *)
  /\ cell m 0xaa020 0xb2899 /\ rdn SEGS m (Z_to_bv 64 0xb2899) 1 = Some [Z_to_bv 8 1]   (* [comment removed for export] *)
  /\ cell m 0xab330 0xa2bec                                     (* [comment removed for export] *)
  /\ BothMemchr.rodata_clear m.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Record isnH (mem : word -> option byte) (d s n usp : Z) (buf : list byte) (K : Z) : Prop := {
  sn_n    : (0 <= n <= 2 ^ 40)%Z;
  sn_d    : (0 <= d)%Z;
  sn_dn   : (d + n < 2 ^ 64)%Z;
  sn_buf  : rdn SEGS mem (Z_to_bv 64 s) (length buf) = Some buf;
  sn_win  : ((s + K) / 8 * 8 + 8 <= s + Z.of_nat (length buf))%Z;
  sn_nw   : (s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  sn_s    : (0 < s)%Z;
  sn_K    : (0 <= K)%Z /\ (K < Z.of_nat (length buf))%Z /\ (K + 1 <= 2 ^ 40)%Z /\ (K + 8 <= n)%Z;
  sn_zero_K : bv_unsigned (VBothMuslStrlen.b_ buf K) = 0%Z;
  sn_disj : (d + n <= s \/ s + Z.of_nat (length buf) <= d)%Z;
  sn_rngs : (s + K + 1 <= kLowEnd)%Z \/ (kHighBeg <= s /\ s + K + 1 <= kHighEnd)%Z;
  sn_rngd : (d + n <= kLowEnd)%Z \/ (kHighBeg <= d /\ d + n <= kHighEnd)%Z;
  sn_sp   : (SB + ISN_FRAME + 8 <= usp < 2 ^ 64)%Z;
  sn_sap  : (usp <= s \/ s + Z.of_nat (length buf) <= usp - ISN_FRAME)%Z;
  sn_dst  : (usp <= d \/ d + n <= usp - ISN_FRAME)%Z;
  sn_shs  : (SB + (s + K) / 8 + 8 < usp - ISN_FRAME)%Z;
  sn_shd  : (SB + (d + n - 1) / 8 + 8 < usp - ISN_FRAME)%Z;
  (* [comment removed for export] *)
  sn_zgs  : forall g, (s / 8 <= g < (s + K) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  sn_lasts : exists b1 : byte, mem (Z_to_bv 64 (SB + (s + K) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((s + K) mod 8 < bv_unsigned b1 < 8)%Z);
  sn_wordss : forall a, ((SB + s / 8) / 8 * 8 <= a)%Z -> (a <= (SB + (s + K) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
                exists w : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w);
  (* [comment removed for export] *)
  sn_zgd  : forall g, (d / 8 <= g < (d + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  sn_lastd : exists b1 : byte, mem (Z_to_bv 64 (SB + (d + n - 1) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z);
  sn_wordsd : forall a, ((SB + d / 8) / 8 * 8 <= a)%Z -> (a <= (SB + (d + n - 1) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
                exists w : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w);
  sn_dok  : forall j, (0 <= j < n)%Z -> store_ok SEGS mem (Z_to_bv 64 (d + j)) 1 = true;
  sn_stk  : forall a, (usp - ISN_FRAME <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  sn_dcel : (d + n <= 0xa8000 \/ 0xb3340 <= d)%Z;
  sn_dro  : (0x10388 <= d \/ d + n <= 0x10360)%Z;
  sn_cel  : isn_cells mem
}.

(* [comment removed for export] *)
Definition isn_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.
(* [comment removed for export] *)
Definition ekeep (r : reg) : bool :=
  (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21
   || bv_eqb r 22 || bv_eqb r 23 || bv_eqb r 24)%bool.

Lemma strncpy_clob_isn : forall r : reg, isn_clob r = false -> ~ In r VBothMuslStrncpy.strncpy_clob.
Proof.
  intros r Hr Hin. unfold VBothMuslStrncpy.strncpy_clob in Hin. cbn in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn in Hr; discriminate Hr|]). exact Hin.
Qed.
Lemma rp_clob_isn : forall r : reg, isn_clob r = false -> rp_clob r = false.
Proof.
  intros r Hr. unfold isn_clob in Hr. unfold rp_clob.
  repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
  repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
Qed.
Lemma imc_clob_isn : forall r : reg, isn_clob r = false -> imc_clob r = false.
Proof. intros r Hr. exact Hr. Qed.

Section ISN.
  Variables (mem rom : word -> option byte) (d s n usp : Z) (buf : list byte) (K : Z).
  Hypothesis H : isnH mem d s n usp buf K.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 d.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 s.
  Hypothesis H012 : getr regs0 12 = Z_to_bv 64 n.

  Let Hn := sn_n _ _ _ _ _ _ _ H.
  Let Hd := sn_d _ _ _ _ _ _ _ H.
  Let HK := sn_K _ _ _ _ _ _ _ H.
  #[using="mem d s n buf K H"] Lemma Hsp : (0x7fff8000 + 4416 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (sn_sp _ _ _ _ _ _ _ H). unfold ISN_FRAME, SB in *. lia. Qed.
  #[using="mem d n usp K H HK"] Lemma Hs64 : (0 < s < 2 ^ 64)%Z /\ (s + Z.of_nat (length buf) < 2 ^ 64)%Z.
  Proof. pose proof (sn_nw _ _ _ _ _ _ _ H). pose proof (sn_s _ _ _ _ _ _ _ H). lia. Qed.
  #[using="mem s usp buf K H"] Lemma Hdn : (d + n < 2 ^ 64)%Z. Proof. exact (sn_dn _ _ _ _ _ _ _ H). Qed.
  #[using="mem usp buf H Hd HK"] Lemma HK64 : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z /\ (s + K + 1 < 2 ^ 47)%Z /\ (K + 8 <= n)%Z /\ (d + n < 2 ^ 47)%Z /\ (0 < n)%Z.
  Proof.
    pose proof (sn_K _ _ _ _ _ _ _ H). pose proof (sn_rngs _ _ _ _ _ _ _ H). pose proof (sn_rngd _ _ _ _ _ _ _ H). pose proof Hs64. pose proof Hd.
    unfold kLowEnd, kHighBeg, kHighEnd in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition I : Z := Z.of_nat (fz buf).
  #[using="mem d s n usp H HK"] Lemma I_facts : (0 <= I <= K)%Z /\ bv_unsigned (VBothMuslStrlen.b_ buf I) = 0%Z
                  /\ (forall j, (0 <= j < I)%Z -> bv_unsigned (VBothMuslStrlen.b_ buf j) <> 0%Z).
  Proof. pose proof HK as (K0 & KL & _). exact (fz_facts buf K ltac:(lia) (sn_zero_K _ _ _ _ _ _ _ H)). Qed.

  (* [comment removed for export] *)
  Definition p10 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 80%Z (getr regs0 24) (w 72%Z (getr regs0 23) (w 64%Z (getr regs0 22) (w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20)
      (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18) (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem))))))))).
  (* [comment removed for export] *)
  Definition p12 : word -> option byte :=
    wbytes (wbytes p10 (Z_to_bv 64 (usp - 2168)) (word_to_le_bytes 8 (Z_to_bv 64 0x49c04)))
           (Z_to_bv 64 (usp - 2176)) (word_to_le_bytes 8 (Z_to_bv 64 usp)).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.
  Ltac adr c := match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with c by lia end.

  #[using="d s n buf K H"] Lemma p10_out : forall x : word, (bv_unsigned x < usp - 80 \/ usp <= bv_unsigned x)%Z -> p10 x = mem x.
  Proof.
    intros x [Hx|Hx]; unfold p10; pose proof Hsp.
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  #[using="d s n buf K H"] Lemma p12_out : forall x : word,
    (bv_unsigned x < usp - 2176 \/ (usp - 2160 <= bv_unsigned x < usp - 80) \/ usp <= bv_unsigned x)%Z -> p12 x = mem x.
  Proof.
    intros x Hx. unfold p12. pose proof Hsp. rewrite <- (p10_out x) by lia.
    destruct Hx as [Hx|[Hx|Hx]].
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Definition sfr (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - ISN_FRAME \/ usp - 2160 <= bv_unsigned x)%Z -> m x = p12 x)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true)
    /\ (forall x, mem x <> None -> m x <> None).

  #[using="Type"] Lemma p12_sok : forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS p12 x 1 = true.
  Proof. intros x Hx. unfold p12, p10. repeat apply store_ok1_wbytes. exact Hx. Qed.
  #[using="Type"] Lemma p12_keep : forall x, mem x <> None -> p12 x <> None.
  Proof. intros x Hx. unfold p12, p10. repeat apply wbytes_keep. exact Hx. Qed.
  #[using="Type"] Lemma sfr_p12 : sfr p12.
  Proof. split; [intros; reflexivity|]. split; [exact p12_sok|exact p12_keep]. Qed.

  #[using="d s n buf K H"] Lemma sfr_below : forall m (x : word), sfr m -> (bv_unsigned x < usp - ISN_FRAME)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. rewrite (F1 x (or_introl Hx)). apply p12_out. unfold ISN_FRAME in Hx. lia. Qed.
  #[using="d s n buf K H"] Lemma sfr_out : forall m (x : word), sfr m -> (bv_unsigned x < usp - ISN_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. rewrite (F1 x) by lia. apply p12_out. unfold ISN_FRAME in Hx. lia. Qed.
  #[using="d s n buf K H"] Lemma rdn_sfr_below : forall m (a : Z) k, sfr m -> (0 <= a)%Z -> (a + Z.of_nat k <= usp - ISN_FRAME)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k F Ha Hk. pose proof Hsp. unfold ISN_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply (sfr_below m x F). unfold ISN_FRAME. lia.
  Qed.
  #[using="d s n buf K H"] Lemma rdn_sfr_out : forall m (a : Z) k, sfr m -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= usp - ISN_FRAME \/ usp <= a)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k F Ha Hk Hap. pose proof Hsp. unfold ISN_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply (sfr_out m x F). unfold ISN_FRAME. lia.
  Qed.
  #[using="d s n buf K H"] Lemma sfr_rp : forall m (rra s0 s1 s2 s3 s4 s5 : word), sfr m -> sfr (rp_frame m (usp - 2160) rra s0 s1 s2 s3 s4 s5).
  Proof.
    intros m rra s0 s1 s2 s3 s4 s5 (F1 & F2 & F3). pose proof Hsp. unfold sfr, ISN_FRAME in *. split; [|split].
    - intros x Hx. unfold rp_frame. rewrite <- (F1 x Hx). destruct Hx as [Hx|Hx].
      + rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
      + rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. unfold rp_frame. repeat apply store_ok1_wbytes. apply F2. exact Hx.
    - intros x Hx. unfold rp_frame. repeat apply wbytes_keep. apply F3. exact Hx.
  Qed.
  (* [comment removed for export] *)
  #[using="buf"] Lemma sfr_call : forall m m' (D : Z), sfr m -> (D <= 2248)%Z ->
    (forall x : word, (bv_unsigned x < usp - 2160 - D \/ usp - 2160 <= bv_unsigned x)%Z -> m' x = m x) ->
    (forall x, m x <> None -> m' x <> None) ->
    (forall x, store_ok SEGS m x 1 = true -> store_ok SEGS m' x 1 = true) ->
    sfr m'.
  Proof.
    intros m m' D (F1 & F2 & F3) HD A G S. split; [|split].
    - intros x Hx. unfold ISN_FRAME in *. rewrite A by lia. apply F1. exact Hx.
    - intros x Hx. apply S. apply F2. exact Hx.
    - intros x Hx. apply G. apply F3. exact Hx.
  Qed.
  #[using="d s n buf K H"] Lemma cells_sfr : forall m, sfr m -> isn_cells m.
  Proof.
    intros m F. pose proof (sn_cel _ _ _ _ _ _ _ H) as (C & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & RO).
    pose proof Hsp. pose proof SB_val. unfold ISN_FRAME in *.
    unfold isn_cells, cells, cell in *. rewrite !(rdn_sfr_below m) by (first [exact F | cbn; unfold ISN_FRAME; lia]).
    split; [exact C|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
    split; [exact C6|]. split; [exact C7|]. split; [exact C8|]. split; [exact C9|].
    intros i Hi. rewrite (sfr_below m); [exact (RO i Hi)|exact F|rewrite zbv_u by lia; unfold ISN_FRAME; lia].
  Qed.
  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp; unfold p12, p10;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
  #[using="d s n buf K H"] Lemma rd_ra : rdn SEGS p12 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).              Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s0 : rdn SEGS p12 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)).  Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s1 : rdn SEGS p12 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)).  Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s2 : rdn SEGS p12 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s3 : rdn SEGS p12 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s4 : rdn SEGS p12 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s5 : rdn SEGS p12 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s6 : rdn SEGS p12 (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 (getr regs0 22)). Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s7 : rdn SEGS p12 (Z_to_bv 64 (usp - 72)) 8 = Some (word_to_le_bytes 8 (getr regs0 23)). Proof. rd_slot. Qed.
  #[using="d s n buf K H"] Lemma rd_s8 : rdn SEGS p12 (Z_to_bv 64 (usp - 80)) 8 = Some (word_to_le_bytes 8 (getr regs0 24)). Proof. rd_slot. Qed.

  #[using="d s n buf K H"] Lemma stk8 : forall m a, sfr m -> (usp - ISN_FRAME <= a)%Z -> (a + 8 <= usp)%Z -> store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a (_ & F3 & _) H1 H2. unfold ISN_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F3. apply (sn_stk _ _ _ _ _ _ _ H). unfold ISN_FRAME. lia.
  Qed.

  Ltac msd F D a v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                 | apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold p12, p10; repeat apply store_ok1_wbytes;
                   apply (sn_stk _ _ _ _ _ _ _ H); unfold ISN_FRAME; lia ]).

  (* [comment removed for export] *)
  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r : reg, isn_clob r = false -> ekeep r = false -> getr regs r = getr regs0 r.
  Ltac keep_tac Hr He := repeat (rewrite getr_other by (intros ->; cbn in Hr, He; first [discriminate Hr | discriminate He])).

  (* [comment removed for export] *)
  Definition base (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (usp - 2160) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 9 = Z_to_bv 64 n
    /\ getr regs 18 = Z_to_bv 64 s /\ getr regs 19 = Z_to_bv 64 d /\ getr regs 23 = Z_to_bv 64 0xab2d8 /\ keep regs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="buf K H H01 H02 H010 H011 H012 Hn Hd HK"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x49bc0 : word) mem rom) (mkst regs (0x49c24 : word) p12 rom)
      /\ base regs /\ getr regs 12 = Z_to_bv 64 0xa3074.
  Proof.
    pose proof Hsp. pose proof Hs64. pose proof Hdn. pose proof Hd. pose proof Hn.
    assert (F12 : sfr p12) by exact sfr_p12.
    pose proof (cells_sfr p12 F12) as (_ & AI & GF & RS & RSL & _).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49bc0 eq_refl D_49bc0)). rewrite H02. zn.
      msd F_49bc4 D_49bc4 (usp - 8)%Z ra H02.
      msd F_49bc8 D_49bc8 (usp - 16)%Z (getr regs0 8) H02.
      msd F_49bcc D_49bcc (usp - 24)%Z (getr regs0 9) H02.
      msd F_49bd0 D_49bd0 (usp - 32)%Z (getr regs0 18) H02.
      msd F_49bd4 D_49bd4 (usp - 40)%Z (getr regs0 19) H02.
      msd F_49bd8 D_49bd8 (usp - 48)%Z (getr regs0 20) H02.
      msd F_49bdc D_49bdc (usp - 56)%Z (getr regs0 21) H02.
      msd F_49be0 D_49be0 (usp - 64)%Z (getr regs0 22) H02.
      msd F_49be4 D_49be4 (usp - 72)%Z (getr regs0 23) H02.
      msd F_49be8 D_49be8 (usp - 80)%Z (getr regs0 24) H02.
      change (wbytes _ _ _) with p10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49bec eq_refl D_49bec)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49bf0 eq_refl D_49bf0)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49bf4 eq_refl D_49bf4)). gr. rewrite H012. zn. rewrite ?Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49bf8 eq_refl D_49bf8)). gr. rewrite H011. zn. rewrite ?Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49bfc eq_refl D_49bfc)). gr. rewrite H010. zn. rewrite ?Z.add_0_r.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_49c00 eq_refl D_49c00)). rewrite lit_c0e7c.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5baec eq_refl D_5baec)). gr. zn.
      msd F_5baf0 D_5baf0 (usp - 2168)%Z (Z_to_bv 64 0x49c04) H02.
      msd F_5baf4 D_5baf4 (usp - 2176)%Z (Z_to_bv 64 usp) H02.
      change (wbytes _ _ _) with p12.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb2af8) F_5baf8 eq_refl D_5baf8);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5bafc eq_refl D_5bafc)). gr. zn.
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5bb00 eq_refl D_5bb00);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI).
      rewrite v_lb_1.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5bb04 eq_refl D_5bb04)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5bb08 eq_refl D_5bb08)).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5bb0c eq_refl D_5bb0c); gr; br_eq).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0x49c04) F_5bb10 eq_refl D_5bb10);
                   [ gr; imm_norm; zn; adr (usp - 2168)%Z;
                     unfold p12; rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia| len8; rewrite !zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia]
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 usp) F_5bb14 eq_refl D_5bb14);
                   [ gr; imm_norm; zn; adr (usp - 2176)%Z;
                     unfold p12; apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5bb18 eq_refl D_5bb18)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x49c04) F_5bb1c eq_refl D_5bb1c); gr; reflexivity |].
      imm_norm. rewrite ret_c0e7c. replace (usp - 2160 + -16 + 16)%Z with (usp - 2160)%Z by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9c04) F_49c04 eq_refl D_49c04);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_49c08 D_49c08 0xaf3b8%Z GF H02.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_49c0c eq_refl D_49c0c);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; first [exact RS | adr 0xaf3d5%Z; exact RS]).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaac10) F_49c10 eq_refl D_49c10);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c14 eq_refl D_49c14)). gr. zn.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_49c18 eq_refl D_49c18); gr; rewrite ?getr_zero; br_eq).
      mld F_49c1c D_49c1c 0xa3074%Z RSL H02.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_49c20 eq_refl D_49c20); gr; rewrite ?getr_zero; br_eq).
      apply mst_refl.
    - unfold base. gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr He. keep_tac Hr He. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d H Hn HK"] Lemma imcH_p12 : imcH SNL_FRAME p12 s n (usp - 2160) buf K.
  Proof.
    pose proof Hsp. pose proof Hs64 as [S1 S2]. pose proof HK as (K0 & KL & K40 & Kn). pose proof Hn. pose proof SB_val.
    pose proof (sn_sap _ _ _ _ _ _ _ H) as AP. pose proof (sn_shs _ _ _ _ _ _ _ H) as SH. unfold ISN_FRAME in *.
    assert (F12 : sfr p12) by exact sfr_p12.
    pose proof (cells_sfr p12 F12) as (C & AI & _ & _ & _ & _ & RM & _ & _ & _ & RO).
    constructor; unfold SNL_FRAME; try lia.
    - rewrite (rdn_sfr_out p12); [exact (sn_buf _ _ _ _ _ _ _ H)|exact F12|lia|lia|unfold ISN_FRAME; lia].
    - exact (sn_win _ _ _ _ _ _ _ H).
    - exact (sn_zero_K _ _ _ _ _ _ _ H).
    - exact (sn_rngs _ _ _ _ _ _ _ H).
    - intros g Hg. pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)).
      rewrite (sfr_below p12); [exact (sn_zgs _ _ _ _ _ _ _ H g Hg)|exact F12|rewrite zbv_u by lia; unfold ISN_FRAME; lia].
    - destruct (sn_lasts _ _ _ _ _ _ _ H) as (b1 & M & B). exists b1. split; [|exact B].
      pose proof (Z.div_pos (s + K) 8 ltac:(lia) ltac:(lia)).
      rewrite (sfr_below p12); [exact M|exact F12|rewrite zbv_u by lia; unfold ISN_FRAME; lia].
    - intros a Ha Hb Hm. pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_mod (SB + s / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + s / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SB + (s + K) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (s + K) / 8) 8 ltac:(lia)).
      rewrite (rdn_sfr_below p12); [exact (sn_wordss _ _ _ _ _ _ _ H a Ha Hb Hm)|exact F12|lia|cbn; unfold ISN_FRAME; lia].
    - intros a Ha. apply p12_sok. apply (sn_stk _ _ _ _ _ _ _ H). unfold ISN_FRAME. lia.
    - split; [exact C|]. split; [exact AI|]. split; [exact RM|exact RO].
  Qed.

  #[using="K H Hn HK"] Lemma blk_N : forall regs, base regs -> getr regs 12 = Z_to_bv 64 0xa3074 ->
    exists regs' m1,
      msteps SEGS (mkst regs (0x49c24 : word) p12 rom) (mkst regs' (0x49c30 : word) m1 rom)
      /\ sfr m1 /\ base regs' /\ getr regs' 10 = Z_to_bv 64 I.
  Proof.
    intros regs B H12. pose proof Hsp. pose proof Hs64 as [HS1 HS2]. pose proof Hn. pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    evar (rr : bvmap 5 word).
    edestruct (strnlen_run p12 rom s n (usp - 2160) buf K imcH_p12 rr (0x49c30 : word) ret_ok_c0ea8)
      as (r1 & m1 & M1 & R10 & R2 & R1 & K1 & M1o & M1g & M1s); cycle -1.
    { exists r1, m1. split; [|split; [|split; [|exact R10]]].
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c24 eq_refl D_49c24)). gr. rewrite B18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c28 eq_refl D_49c28)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa3074) F_49c2c eq_refl D_49c2c);
                     [reflexivity | gr; exact H12]).
        rewrite ?lit_c0ea8.
        match goal with |- msteps _ (mkst ?r ?pc ?mm ?ro) _ =>
          replace pc with (0xa3074 : word) by (apply bv_eq; vm_compute; reflexivity) end.
        subst rr. exact M1.
      - apply (sfr_call p12 m1 2232 sfr_p12 ltac:(lia)); [|exact M1g|exact M1s].
        intros x Hx. apply M1o. unfold SNL_FRAME. lia.
      - unfold base. rewrite (K1 8), (K1 9), (K1 18), (K1 19), (K1 23) by reflexivity. subst rr. gr.
        split; [exact R2|]. split; [exact B8|]. split; [exact B9|]. split; [exact B18|]. split; [exact B19|]. split; [exact B23|].
        intros r Hr He. destruct (bv_eq_dec _ r 1) as [->|N1]; [cbn in He; discriminate|].
        destruct (bv_eq_dec _ r 2) as [->|N2]; [cbn in He; discriminate|].
        rewrite (K1 r (imc_clob_isn r Hr)). keep_tac Hr He. apply BK; assumption. }
    all: subst rr; gr; try reflexivity; try assumption; zn; rewrite ?Z.add_0_r; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="mem K H Hn Hd HK"] Lemma blk_O : forall regs m, base regs -> getr regs 10 = Z_to_bv 64 I ->
    exists regs',
      msteps SEGS (mkst regs (0x49c30 : word) m rom) (mkst regs' (0x49c68 : word) m rom)
      /\ base regs' /\ getr regs' 20 = Z_to_bv 64 (I + 1) /\ getr regs' 21 = Z_to_bv 64 (s + (I + 1))
      /\ getr regs' 24 = Z_to_bv 64 (usp - 2152)
      /\ getr regs' 10 = Z_to_bv 64 (I + 1 - 65) /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 65).
  Proof.
    intros regs m B H10. pose proof Hsp. pose proof Hs64 as [S1 S2]. pose proof HK64 as (K0 & K40 & SK & Kn & DN & N0). pose proof Hd. pose proof Hdn.
    pose proof I_facts as (HI & _). pose proof (sn_disj _ _ _ _ _ _ _ H) as DJ. pose proof HK as (_ & KL & _).
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c30 eq_refl D_49c30)). gr. rewrite H10. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c34 eq_refl D_49c34)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_49c38 eq_refl D_49c38); gr; rewrite ?B9; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c3c eq_refl D_49c3c)). gr. zn. rewrite ?Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c40 eq_refl D_49c40)). gr. rewrite B8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c44 eq_refl D_49c44)). gr. zn.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49c48 eq_refl D_49c48)). gr. rewrite B19, v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49c4c eq_refl D_49c4c)). gr. rewrite B18, v_add_zbv by lia.
      destruct DJ as [DJ|DJ].
      + (* [comment removed for export] *)
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_49c50 eq_refl D_49c50); gr; rewrite ?B18; br_lt).
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49c58 eq_refl D_49c58)). gr. rewrite B18. rewrite v_not_zbv by lia.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_49c5c eq_refl D_49c5c); gr; br_lt).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c60 eq_refl D_49c60)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c64 eq_refl D_49c64)). rewrite getr_zero. zn.
        apply mst_refl.
      + (* [comment removed for export] *)
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_49c50 eq_refl D_49c50); gr; rewrite ?B18; br_lt).
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_49c54 eq_refl D_49c54); gr; rewrite ?B19; br_lt).
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49c58 eq_refl D_49c58)). gr. rewrite B18. rewrite v_not_zbv by lia.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_49c5c eq_refl D_49c5c); gr; br_lt).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c60 eq_refl D_49c60)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c64 eq_refl D_49c64)). rewrite getr_zero. zn.
        apply mst_refl.
    - assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
      { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
      destruct DJ as [DJ|DJ]; unfold base; gr; repeat split; try assumption; try (apply (f_equal (Z_to_bv 64)); lia);
        try (rewrite <- (zbv_wrap_add (-65)); apply (f_equal (Z_to_bv 64)); lia);
        apply KP; intros r Hr He; keep_tac Hr He; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d n usp K H HK"] Lemma last_s : exists b1 : byte, mem (Z_to_bv 64 (SB + (s + I) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((s + I) mod 8 < bv_unsigned b1 < 8)%Z).
  Proof.
    pose proof Hs64 as [S1 _]. pose proof I_facts as (Hi & _).
    pose proof (Z.div_le_mono (s + I) (s + K) 8 ltac:(lia) ltac:(lia)) as LE.
    destruct (Z.lt_ge_cases ((s + I) / 8) ((s + K) / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      apply (sn_zgs _ _ _ _ _ _ _ H). split; [apply Z.div_le_mono; lia|exact LT].
    - assert (E : ((s + I) / 8 = (s + K) / 8)%Z) by lia.
      destruct (sn_lasts _ _ _ _ _ _ _ H) as (b1 & M & B). exists b1. rewrite E. split; [exact M|].
      destruct B as [B|B]; [left; exact B|right].
      pose proof (Z.div_mod (s + I) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + I) 8 ltac:(lia)).
      pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). lia.
  Qed.
  #[using="d n usp K H HK"] Lemma zero_s : forall g, (s / 8 <= g < (s + I) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
  Proof.
    intros g Hg. pose proof Hs64 as [S1 _]. pose proof I_facts as (Hi & _).
    pose proof (Z.div_le_mono (s + I) (s + K) 8 ltac:(lia) ltac:(lia)). apply (sn_zgs _ _ _ _ _ _ _ H). lia.
  Qed.
  #[using="mem d n H Hd HK"] Lemma sfacts :
    (8 * (s / 8) <= s < 8 * (s / 8) + 8)%Z /\ (8 * ((s + I) / 8) <= s + I < 8 * ((s + I) / 8) + 8)%Z
    /\ ((s + I) mod 8 = s + I - 8 * ((s + I) / 8))%Z
    /\ (SB + (s + I) / 8 + 8 < usp - ISN_FRAME)%Z /\ (s / 8 <= (s + I) / 8 <= (s + K) / 8)%Z /\ SB = 0x7fff8000%Z
    /\ (s + K + 1 < 2 ^ 47)%Z /\ (0 <= I <= K)%Z.
  Proof.
    pose proof (sn_shs _ _ _ _ _ _ _ H) as Hshd. pose proof SB_val. pose proof Hs64 as [S1 _]. pose proof I_facts as (Hi & _).
    pose proof HK64 as (HK0 & HK1 & HK2 & _).
    pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
    pose proof (Z.div_mod (s + I) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + I) 8 ltac:(lia)).
    pose proof (Z.div_le_mono s (s + I) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (s + I) (s + K) 8 ltac:(lia) ltac:(lia)).
    lia.
  Qed.
  (* [comment removed for export] *)
  #[using="mem s buf K H Hn Hd HK"] Lemma dfacts :
    (8 * (d / 8) <= d < 8 * (d / 8) + 8)%Z /\ (8 * ((d + n - 1) / 8) <= d + n - 1 < 8 * ((d + n - 1) / 8) + 8)%Z
    /\ ((d + n - 1) mod 8 = d + n - 1 - 8 * ((d + n - 1) / 8))%Z
    /\ (SB + (d + n - 1) / 8 + 8 < usp - ISN_FRAME)%Z /\ (d / 8 <= (d + n - 1) / 8)%Z /\ SB = 0x7fff8000%Z
    /\ (d + n < 2 ^ 47)%Z /\ (8 <= n <= 2 ^ 40)%Z.
  Proof.
    pose proof (sn_shd _ _ _ _ _ _ _ H) as Hshd. pose proof SB_val. pose proof Hd. pose proof Hn. pose proof HK64 as (HK0 & _ & _ & Kn & DN & _).
    pose proof (Z.div_mod d 8 ltac:(lia)). pose proof (Z.mod_pos_bound d 8 ltac:(lia)).
    pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)).
    pose proof (Z.div_le_mono d (d + n - 1) 8 ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K H Hd HK"] Lemma blk_RQ1 : forall regs m, sfr m -> (I <= 63)%Z -> base regs ->
    getr regs 21 = Z_to_bv 64 (s + (I + 1)) -> getr regs 10 = Z_to_bv 64 (I + 1 - 65) -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x49c68 : word) m rom) (mkst regs' (0x49ca0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (SB + s / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (s + I) / 8)
      /\ getr regs' 21 = Z_to_bv 64 (s + I) /\ getr regs' 12 = w
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F Hi63 B H21 H10 H11. pose proof Hsp as HU. pose proof Hs64 as [S1 _].
    destruct sfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & Hi). unfold ISN_FRAME in Dshd.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
    pose proof (Z.div_mod (SB + s / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + s / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + (s + I) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (s + I) / 8) 8 ltac:(lia)).
    pose proof (Z.div_le_mono (SB + s / 8) (SB + (s + I) / 8) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (SB + (s + I) / 8) (SB + (s + K) / 8) 8 ltac:(lia) ltac:(lia)).
    destruct (sn_wordss _ _ _ _ _ _ _ H ((SB + s / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @Hi; @H4; @H5]); lia)) ltac:((ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @Hi; @H4; @H5]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w1 W1].
    destruct (sn_wordss _ _ _ _ _ _ _ H ((SB + (s + I) / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @Hi; @H4; @H5]); lia)) ltac:((ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @Hi; @H4; @H5]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w2 W2].
    assert (W1c : cell m ((SB + s / 8) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISN_FRAME; (ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @Hi; @H0; @H1; @Dshd]); lia)]). exact W1. }
    assert (W2c : cell m ((SB + (s + I) / 8) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISN_FRAME; (ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @Hi; @H2; @H3; @Dshd]); lia)]). exact W2. }
    replace (Z_to_bv 64 (I + 1 - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + (I + 1))) in H10
      by (rewrite <- (zbv_wrap_add (I + 1 - 65)); apply (f_equal (Z_to_bv 64)); lia).
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_49c68 eq_refl D_49c68); gr; rewrite ?H10, ?H11; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9c6c) F_49c6c eq_refl D_49c6c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_49c70 D_49c70 0xb1bb8%Z C1 B18.
      mld F_49c74 D_49c74 SB C2 B18.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49c78 eq_refl D_49c78)). gr. rewrite H21. zn.
      replace (s + (I + 1) + -1)%Z with (s + I)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_49c7c eq_refl D_49c7c)). gr. rewrite B18, (v_srli_3 s) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_49c80 eq_refl D_49c80)). gr. rewrite (v_srli_3 (s + I)) by (ltac2:(LK.k [@S1; @D0; @D1; @D01; @HSB; @HsK; @Hi]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49c84 eq_refl D_49c84)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@S1; @HSB; @HK; @D0; @HsK; @Hi]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49c88 eq_refl D_49c88)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@S1; @HSB; @D0; @D1; @DM; @D01; @HsK; @Hi]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49c8c eq_refl D_49c8c)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@HK; @S1; @D0; @D1; @D01; @HSB; @HsK; @Hi]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49c90 eq_refl D_49c90)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@S1; @D1; @DM; @D01; @HSB; @HsK; @Hi]); lia).
      mld F_49c94 D_49c94 (bv_unsigned w1) W1c B18.
      mld F_49c98 D_49c98 (bv_unsigned w2) W2c B18.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_49c9c eq_refl D_49c9c)). gr.
      apply mst_refl.
    - unfold base. gr. repeat split; try reflexivity; try assumption.
      intros r Hr He. keep_tac Hr He. apply BK; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="K H Hd HK"] Lemma blk_RQ2a : forall regs m, sfr m -> base regs ->
    getr regs 11 = Z_to_bv 64 (SB + (s + I) / 8) -> getr regs 21 = Z_to_bv 64 (s + I) ->
    exists regs',
      msteps SEGS (mkst regs (0x49ee8 : word) m rom) (mkst regs' (0x49f00 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = getr regs 11
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F B H11 H21. pose proof Hsp as HU. pose proof Hs64 as [S1 _].
    destruct sfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & Hi). unfold ISN_FRAME in Dshd.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    destruct last_s as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (s + I) / 8)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
    { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_49ee8 eq_refl D_49ee8);
                     gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49eec eq_refl D_49eec)). gr. rewrite H21, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_49ef0 eq_refl D_49ef0)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_49ef4 eq_refl D_49ef4)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49ef8 eq_refl D_49ef8)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_49efc eq_refl D_49efc)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
    - eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_49ee8 eq_refl D_49ee8);
                     gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49eec eq_refl D_49eec)). gr. rewrite H21, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_49ef0 eq_refl D_49ef0)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_49ef4 eq_refl D_49ef4)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49ef8 eq_refl D_49ef8)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_49efc eq_refl D_49efc)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="K H Hd HK"] Lemma rq_loop : forall (k : nat) regs m (g : Z), sfr m -> base regs ->
    getr regs 10 = Z_to_bv 64 (SB + g) -> getr regs 11 = Z_to_bv 64 (SB + (s + I) / 8) -> getr regs 12 = Z_to_bv 64 0 ->
    (s / 8 <= g < (s + I) / 8)%Z -> Z.of_nat k = ((s + I) / 8 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x49f04 : word) m rom) (mkst regs' (0x49f14 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    pose proof Hsp as HU. pose proof Hs64 as [S1 _].
    induction k as [|k IH]; intros regs m g F B H10 H11 H12 Hg Hk; [lia|].
    destruct sfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & Hi). unfold ISN_FRAME in Dshd.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
    { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). apply zero_s. lia. }
    destruct (Z.eq_dec (g + 1) ((s + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_49f04 eq_refl D_49f04);
                     gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49f08 eq_refl D_49f08)). gr. rewrite H10. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_49f0c eq_refl D_49f0c)). gr. rewrite H12, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_49f10 eq_refl D_49f10); gr; rewrite ?H11; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m (g + 1)%Z F) as (r2 & M2 & R12 & R20 & R24 & K2); cycle -1.
      { exists r2. split; [|split; [|split; [|split]]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_49f04 eq_refl D_49f04);
                       gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49f08 eq_refl D_49f08)). gr. rewrite H10. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_49f0c eq_refl D_49f0c)). gr. rewrite H12, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_49f10 eq_refl D_49f10); gr; rewrite ?H11; br_eq).
          subst rr. exact M2.
        + exact R12.
        + rewrite R20. subst rr. gr. reflexivity.
        + rewrite R24. subst rr. gr. reflexivity.
        + exact K2. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      all: try (apply (f_equal (Z_to_bv 64)); lia).
      all: unfold base; gr; repeat split; try assumption; apply KP; intros r Hr He; keep_tac Hr He; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="K H Hd HK"] Lemma blk_RQ2b : forall regs m, sfr m -> base regs ->
    getr regs 10 = Z_to_bv 64 (SB + s / 8) -> getr regs 11 = Z_to_bv 64 (SB + (s + I) / 8) -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x49f00 : word) m rom) (mkst regs' (0x49ca4 : word) m rom)
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F B H10 H11 H12. pose proof Hsp as HU. pose proof Hs64 as [S1 _].
    destruct sfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & Hi).
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
    { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec (s / 8) ((s + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split]].
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_49f00 eq_refl D_49f00); gr; rewrite ?H10, ?H11; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49f14 eq_refl D_49f14)). gr. rewrite H12, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_49f18 eq_refl D_49f18); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + gr. reflexivity. + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (rq_loop (Z.to_nat ((s + I) / 8 - s / 8)) rr m (s / 8) F) as (r2 & M2 & R12 & R20 & R24 & K2); cycle -1.
      { eexists. split; [|split; [|split]].
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_49f00 eq_refl D_49f00); gr; rewrite ?H10, ?H11; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49f14 eq_refl D_49f14)). rewrite R12, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_49f18 eq_refl D_49f18); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + gr. rewrite R20. subst rr. reflexivity.
        + gr. rewrite R24. subst rr. reflexivity.
        + pose proof K2 as (X2 & X8 & X9 & X18 & X19 & X23 & XK). unfold base. gr. repeat split; try assumption.
          intros r Hr He. keep_tac Hr He. apply XK; assumption. }
      all: subst rr; try assumption; try lia.
      all: unfold base; gr; repeat split; try assumption; apply KP; intros r Hr He; keep_tac Hr He; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d n K H Hn Hd HK"] Lemma rp_pre_s : forall m b1, sfr m -> (64 <= I)%Z ->
    mem (Z_to_bv 64 (SB + (s + I) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((s + I) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH m s (I + 1) (usp - 2160) b1.
  Proof.
    intros m b1 F Hi64 L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof Hs64 as [S1 _]. pose proof HK64 as (HK0 & HK1 & HK2 & _).
    destruct sfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & Hi). unfold ISN_FRAME in Dshd.
    pose proof F as (F1 & F2 & F3).
    constructor; rewrite ?Z.add_assoc; replace (s + I + 1 - 1)%Z with (s + I)%Z by lia.
    - lia.
    - lia.
    - pose proof (sn_rngs _ _ _ _ _ _ _ H). lia.
    - lia.
    - lia.
    - intros g Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). apply zero_s; lia.
    - rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). exact L1.
    - exact Hb1.
    - intros a Ha. apply F2. apply (sn_stk _ _ _ _ _ _ _ H). unfold ISN_FRAME. lia.
    - exact (proj1 (cells_sfr m F)).
  Qed.

  #[using="K H Hn Hd HK"] Lemma blk_RL : forall regs m, sfr m -> (64 <= I)%Z -> base regs ->
    getr regs 20 = Z_to_bv 64 (I + 1) -> getr regs 10 = Z_to_bv 64 (I + 1 - 65) -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) ->
    getr regs 24 = Z_to_bv 64 (usp - 2152) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x49c68 : word) m rom) (mkst regs' (0x49ca4 : word) m' rom)
      /\ sfr m' /\ getr regs' 20 = Z_to_bv 64 (I + 1) /\ getr regs' 24 = Z_to_bv 64 (usp - 2152) /\ base regs'.
  Proof.
    intros regs m F Hi64 B H20 H10 H11 H24. pose proof Hsp. pose proof Hs64 as [S1 _]. pose proof HK64 as (HK0 & HK1 & HK2 & _).
    pose proof I_facts as (Hi & _). pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    destruct last_s as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom s (I + 1) (usp - 2160) b1 (rp_pre_s m b1 F Hi64 L1 Hb1) rr (0x49f28 : word) ret_ok_c11a0)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split; [|split]]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_49c68 eq_refl D_49c68); gr; rewrite ?H10, ?H11; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_49e68 eq_refl D_49e68); gr; rewrite ?H20, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49f1c eq_refl D_49f1c)). gr. rewrite B18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49f20 eq_refl D_49f20)). gr. rewrite H20. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_49f24 eq_refl D_49f24)). rewrite lit_c11a0.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_49f28 eq_refl D_49f28); gr; rewrite ?R10, ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - rewrite (K1 20) by reflexivity. subst rr. gr. exact H20.
      - rewrite (K1 24) by reflexivity. subst rr. gr. exact H24.
      - unfold base. rewrite (K1 8), (K1 9), (K1 18), (K1 19), (K1 23) by reflexivity. subst rr. gr.
        split; [exact R2|]. split; [exact B8|]. split; [exact B9|]. split; [exact B18|]. split; [exact B19|]. split; [exact B23|].
        intros r Hr He. destruct (bv_eq_dec _ r 1) as [->|N1]; [cbn in He; discriminate|].
        destruct (bv_eq_dec _ r 2) as [->|N2]; [cbn in He; discriminate|].
        rewrite (K1 r (rp_clob_isn r Hr)). keep_tac Hr He. apply BK; assumption. }
    all: subst rr; gr; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
  Qed.

  (* [comment removed for export] *)
  #[using="K H Hn Hd HK"] Lemma blk_R : forall regs m, sfr m -> base regs ->
    getr regs 20 = Z_to_bv 64 (I + 1) -> getr regs 21 = Z_to_bv 64 (s + (I + 1)) -> getr regs 24 = Z_to_bv 64 (usp - 2152) ->
    getr regs 10 = Z_to_bv 64 (I + 1 - 65) -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x49c68 : word) m rom) (mkst regs' (0x49ca4 : word) m' rom)
      /\ sfr m' /\ getr regs' 24 = Z_to_bv 64 (usp - 2152) /\ base regs'.
  Proof.
    intros regs m F B H20 H21 H24 H10 H11. pose proof I_facts as (Hi & _).
    destruct (Z.lt_ge_cases I 64) as [Hsmall | Hbig].
    - destruct (blk_RQ1 regs m F ltac:(lia) B H21 H10 H11) as (q4 & w & M4 & A10 & A11 & A21 & A12 & A20 & A24 & AB).
      pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
      destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
      + exists q4, m. split; [|split; [exact F|split; [rewrite A24; exact H24|exact AB]]].
        eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_49ca0 eq_refl D_49ca0); gr; rewrite ?A12, ?getr_zero; br_eq).
        apply mst_refl.
      + assert (NZu : bv_unsigned w <> 0%Z).
        { intros E0. apply NZ. rewrite <- (zbv_self w), E0. reflexivity. }
        destruct (blk_RQ2a q4 m F AB A11 A21) as (q5 & M5 & B12 & B10 & B11 & B20 & B24 & BB).
        destruct (blk_RQ2b q5 m F BB) as (q6 & M6 & C20 & C24 & CB); [rewrite B10; exact A10 | rewrite B11; exact A11 | exact B12 |].
        exists q6, m. split; [|split; [exact F|split; [rewrite C24, B24, A24; exact H24|exact CB]]].
        eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_49ca0 eq_refl D_49ca0); gr; rewrite ?A12, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M5|]. exact M6.
    - destruct (blk_RL regs m F Hbig B H20 H10 H11 H24) as (q4 & m4 & M4 & F4 & L20 & L24 & LB).
      exists q4, m4. split; [exact M4|]. split; [exact F4|]. split; [exact L24|exact LB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="mem buf K H Hn Hd HK"] Lemma blk_WT : forall regs m, base regs ->
    exists regs',
      msteps SEGS (mkst regs (0x49ca4 : word) m rom) (mkst regs' (0x49cb4 : word) m rom)
      /\ base regs' /\ getr regs' 10 = Z_to_bv 64 (n - 65) /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 65)
      /\ getr regs' 24 = getr regs 24.
  Proof.
    intros regs m B. pose proof Hsp. pose proof Hd. pose proof Hdn. pose proof Hn.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    eexists. split.
    - mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49ca4 eq_refl D_49ca4)). gr. rewrite B19. rewrite v_not_zbv by lia.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_49ca8 eq_refl D_49ca8); gr; rewrite ?B9; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49cac eq_refl D_49cac)). gr. rewrite B9. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49cb0 eq_refl D_49cb0)). rewrite getr_zero. zn.
      apply mst_refl.
    - unfold base. gr. repeat split; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
      + intros r Hr He. keep_tac Hr He. apply BK; assumption.
      + rewrite <- (zbv_wrap_add (-65)). apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="buf K H Hn Hd HK"] Lemma blk_WQ1 : forall regs m, sfr m -> (n <= 64)%Z -> base regs ->
    getr regs 10 = Z_to_bv 64 (n - 65) -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x49cb4 : word) m rom) (mkst regs' (0x49cf0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (SB + d / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (d + n - 1) / 8)
      /\ getr regs' 12 = Z_to_bv 64 (d + n - 1) /\ getr regs' 13 = w
      /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F Hn64 B H10 H11. pose proof Hsp as HU. pose proof Hd. pose proof Hdn.
    destruct dfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HdK & Hn8). unfold ISN_FRAME in Dshd.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
    pose proof (Z.div_mod (SB + d / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + d / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + (d + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (d + n - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.div_le_mono (SB + d / 8) (SB + (d + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
    destruct (sn_wordsd _ _ _ _ _ _ _ H ((SB + d / 8) / 8 * 8)%Z ltac:(lia) ltac:(lia) ltac:(rewrite Z_mod_mult; reflexivity)) as [w1 W1].
    destruct (sn_wordsd _ _ _ _ _ _ _ H ((SB + (d + n - 1) / 8) / 8 * 8)%Z ltac:(lia) ltac:(lia) ltac:(rewrite Z_mod_mult; reflexivity)) as [w2 W2].
    assert (W1c : cell m ((SB + d / 8) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISN_FRAME; lia]). exact W1. }
    assert (W2c : cell m ((SB + (d + n - 1) / 8) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISN_FRAME; lia]). exact W2. }
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H10
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_49cb4 eq_refl D_49cb4); gr; rewrite ?H10, ?H11; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9cb8) F_49cb8 eq_refl D_49cb8);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_49cbc D_49cbc 0xb1bb8%Z C1 B18.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49cc0 eq_refl D_49cc0)). gr. rewrite B19, B9, v_add_zbv by lia.
      mld F_49cc4 D_49cc4 SB C2 B18.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_49cc8 eq_refl D_49cc8)). gr. rewrite B19, (v_srli_3 d) by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49ccc eq_refl D_49ccc)). gr. zn.
      replace (d + n + -1)%Z with (d + n - 1)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_49cd0 eq_refl D_49cd0)). gr. rewrite (v_srli_3 (d + n - 1)) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49cd4 eq_refl D_49cd4)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_49cd8 eq_refl D_49cd8)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49cdc eq_refl D_49cdc)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49ce0 eq_refl D_49ce0)). gr. rewrite v_andi_m8 by lia.
      mld F_49ce4 D_49ce4 (bv_unsigned w1) W1c B18.
      mld F_49ce8 D_49ce8 (bv_unsigned w2) W2c B18.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_49cec eq_refl D_49cec)). gr.
      apply mst_refl.
    - unfold base. gr. repeat split; try reflexivity; try assumption.
      intros r Hr He. keep_tac Hr He. apply BK; assumption.
  Qed.

  #[using="s usp buf K H"] Lemma last_d : exists b1 : byte, mem (Z_to_bv 64 (SB + (d + n - 1) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z).
  Proof. exact (sn_lastd _ _ _ _ _ _ _ H). Qed.

  (* [comment removed for export] *)
  #[using="buf K H Hn Hd HK"] Lemma blk_WQ2a : forall regs m, sfr m -> base regs ->
    getr regs 11 = Z_to_bv 64 (SB + (d + n - 1) / 8) -> getr regs 12 = Z_to_bv 64 (d + n - 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x49fb0 : word) m rom) (mkst regs' (0x49fc8 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = getr regs 11
      /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F B H11 H12. pose proof Hsp as HU. pose proof Hd. pose proof Hdn.
    destruct dfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HdK & Hn8). unfold ISN_FRAME in Dshd.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    destruct last_d as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (d + n - 1) / 8)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
    { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split; [|split]]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_49fb0 eq_refl D_49fb0);
                     gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49fb4 eq_refl D_49fb4)). gr. rewrite H12, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_49fb8 eq_refl D_49fb8)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_49fbc eq_refl D_49fbc)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49fc0 eq_refl D_49fc0)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_49fc4 eq_refl D_49fc4)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
    - eexists. split; [|split; [|split; [|split; [|split]]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_49fb0 eq_refl D_49fb0);
                     gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49fb4 eq_refl D_49fb4)). gr. rewrite H12, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_49fb8 eq_refl D_49fb8)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_49fbc eq_refl D_49fbc)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_49fc0 eq_refl D_49fc0)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_49fc4 eq_refl D_49fc4)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="buf K H Hn Hd HK"] Lemma wq_loop : forall (k : nat) regs m (g : Z), sfr m -> base regs ->
    getr regs 10 = Z_to_bv 64 (SB + g) -> getr regs 11 = Z_to_bv 64 (SB + (d + n - 1) / 8) -> getr regs 12 = Z_to_bv 64 0 ->
    (d / 8 <= g < (d + n - 1) / 8)%Z -> Z.of_nat k = ((d + n - 1) / 8 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x49fcc : word) m rom) (mkst regs' (0x49fdc : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    pose proof Hsp as HU. pose proof Hd. pose proof Hdn.
    induction k as [|k IH]; intros regs m g F B H10 H11 H12 Hg Hk; [lia|].
    destruct dfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HdK & Hn8). unfold ISN_FRAME in Dshd.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
    { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]).
      apply (sn_zgd _ _ _ _ _ _ _ H). lia. }
    destruct (Z.eq_dec (g + 1) ((d + n - 1) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_49fcc eq_refl D_49fcc);
                     gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49fd0 eq_refl D_49fd0)). gr. rewrite H10. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_49fd4 eq_refl D_49fd4)). gr. rewrite H12, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_49fd8 eq_refl D_49fd8); gr; rewrite ?H11; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m (g + 1)%Z F) as (r2 & M2 & R12 & R24 & K2); cycle -1.
      { exists r2. split; [|split; [|split]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_49fcc eq_refl D_49fcc);
                       gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49fd0 eq_refl D_49fd0)). gr. rewrite H10. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_49fd4 eq_refl D_49fd4)). gr. rewrite H12, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_49fd8 eq_refl D_49fd8); gr; rewrite ?H11; br_eq).
          subst rr. exact M2.
        + exact R12.
        + rewrite R24. subst rr. gr. reflexivity.
        + exact K2. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      all: try (apply (f_equal (Z_to_bv 64)); lia).
      all: unfold base; gr; repeat split; try assumption; apply KP; intros r Hr He; keep_tac Hr He; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="buf K H Hn Hd HK"] Lemma blk_WQ2b : forall regs m, sfr m -> base regs ->
    getr regs 10 = Z_to_bv 64 (SB + d / 8) -> getr regs 11 = Z_to_bv 64 (SB + (d + n - 1) / 8) -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x49fc8 : word) m rom) (mkst regs' (0x49cf4 : word) m rom)
      /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F B H10 H11 H12. pose proof Hsp as HU. pose proof Hd. pose proof Hdn.
    destruct dfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HdK & Hn8).
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    assert (KP : forall regs', (forall r, isn_clob r = false -> ekeep r = false -> getr regs' r = getr regs r) -> keep regs').
    { intros regs' X r Hr He. rewrite (X r Hr He). apply BK; assumption. }
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq | Hne].
    - eexists. split; [|split].
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_49fc8 eq_refl D_49fc8); gr; rewrite ?H10, ?H11; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49fdc eq_refl D_49fdc)). gr. rewrite H12, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_49fe0 eq_refl D_49fe0); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + unfold base. gr. repeat split; try assumption. apply KP. intros r Hr He. keep_tac Hr He. reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (wq_loop (Z.to_nat ((d + n - 1) / 8 - d / 8)) rr m (d / 8) F) as (r2 & M2 & R12 & R24 & K2); cycle -1.
      { eexists. split; [|split].
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_49fc8 eq_refl D_49fc8); gr; rewrite ?H10, ?H11; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_49fdc eq_refl D_49fdc)). rewrite R12, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_49fe0 eq_refl D_49fe0); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + gr. rewrite R24. subst rr. reflexivity.
        + pose proof K2 as (X2 & X8 & X9 & X18 & X19 & X23 & XK). unfold base. gr. repeat split; try assumption.
          intros r Hr He. keep_tac Hr He. apply XK; assumption. }
      all: subst rr; try assumption; try lia.
      all: unfold base; gr; repeat split; try assumption; apply KP; intros r Hr He; keep_tac Hr He; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="s buf K H Hn Hd HK"] Lemma rp_pre_d : forall m b1, sfr m -> (65 <= n)%Z ->
    mem (Z_to_bv 64 (SB + (d + n - 1) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH m d n (usp - 2160) b1.
  Proof.
    intros m b1 F Hn65 L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof Hd. pose proof Hdn. pose proof Hn.
    destruct dfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HdK & Hn8). unfold ISN_FRAME in Dshd.
    pose proof F as (F1 & F2 & F3).
    constructor.
    - lia.
    - lia.
    - exact (sn_rngd _ _ _ _ _ _ _ H).
    - lia.
    - lia.
    - intros g Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). apply (sn_zgd _ _ _ _ _ _ _ H). lia.
    - rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). exact L1.
    - exact Hb1.
    - intros a Ha. apply F2. apply (sn_stk _ _ _ _ _ _ _ H). unfold ISN_FRAME. lia.
    - exact (proj1 (cells_sfr m F)).
  Qed.

  #[using="buf K H Hn Hd HK"] Lemma blk_WL : forall regs m, sfr m -> (65 <= n)%Z -> base regs ->
    getr regs 10 = Z_to_bv 64 (n - 65) -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x49cb4 : word) m rom) (mkst regs' (0x49cf4 : word) m' rom)
      /\ sfr m' /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F Hn65 B H10 H11. pose proof Hsp. pose proof Hd. pose proof Hdn. pose proof Hn.
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK).
    destruct last_d as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom d n (usp - 2160) b1 (rp_pre_d m b1 F Hn65 L1 Hb1) rr (0x49ff0 : word) ret_ok_c1268)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_49cb4 eq_refl D_49cb4); gr; rewrite ?H10, ?H11; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_49ee0 eq_refl D_49ee0); gr; rewrite ?B9, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49fe4 eq_refl D_49fe4)). gr. rewrite B19. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49fe8 eq_refl D_49fe8)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_49fec eq_refl D_49fec)). rewrite lit_c1268.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_49ff0 eq_refl D_49ff0); gr; rewrite ?R10, ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - rewrite (K1 24) by reflexivity. subst rr. gr. reflexivity.
      - unfold base. rewrite (K1 8), (K1 9), (K1 18), (K1 19), (K1 23) by reflexivity. subst rr. gr.
        split; [exact R2|]. split; [exact B8|]. split; [exact B9|]. split; [exact B18|]. split; [exact B19|]. split; [exact B23|].
        intros r Hr He. destruct (bv_eq_dec _ r 1) as [->|N1]; [cbn in He; discriminate|].
        destruct (bv_eq_dec _ r 2) as [->|N2]; [cbn in He; discriminate|].
        rewrite (K1 r (rp_clob_isn r Hr)). keep_tac Hr He. apply BK; assumption. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="buf K H Hn Hd HK"] Lemma blk_W : forall regs m, sfr m -> base regs ->
    exists regs' m',
      msteps SEGS (mkst regs (0x49ca4 : word) m rom) (mkst regs' (0x49cf4 : word) m' rom)
      /\ sfr m' /\ getr regs' 24 = getr regs 24 /\ base regs'.
  Proof.
    intros regs m F B. pose proof Hn.
    destruct (blk_WT regs m B) as (q3 & MT & TB & T10 & T11 & T24).
    destruct (Z.lt_ge_cases n 65) as [Hsmall | Hbig].
    - destruct (blk_WQ1 q3 m F ltac:(lia) TB T10 T11) as (q4 & w & M4 & A10 & A11 & A12 & A13 & A24 & AB).
      pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
      destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
      + exists q4, m. split; [|split; [exact F|split; [rewrite A24; exact T24|exact AB]]].
        eapply msteps_trans; [exact MT|]. eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_49cf0 eq_refl D_49cf0); gr; rewrite ?A13, ?getr_zero; br_eq).
        apply mst_refl.
      + assert (NZu : bv_unsigned w <> 0%Z).
        { intros E0. apply NZ. rewrite <- (zbv_self w), E0. reflexivity. }
        destruct (blk_WQ2a q4 m F AB A11 A12) as (q5 & M5 & B12 & B10 & B11 & B24 & BB).
        destruct (blk_WQ2b q5 m F BB) as (q6 & M6 & C24 & CB); [rewrite B10; exact A10 | rewrite B11; exact A11 | exact B12 |].
        exists q6, m. split; [|split; [exact F|split; [rewrite C24, B24, A24; exact T24|exact CB]]].
        eapply msteps_trans; [exact MT|]. eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_49cf0 eq_refl D_49cf0); gr; rewrite ?A13, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M5|]. exact M6.
    - destruct (blk_WL q3 m F Hbig TB T10 T11) as (q4 & m4 & M4 & F4 & L24 & LB).
      exists q4, m4. split; [eapply msteps_trans; [exact MT|exact M4]|]. split; [exact F4|]. split; [rewrite L24; exact T24|exact LB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RES : list byte := firstn (Z.to_nat I) buf ++ zeros (Z.to_nat (n - I)).

  #[using="K H Hn Hd HK"] Lemma sncH_m : forall m, sfr m -> VBothMuslStrncpy.sncH m (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 (usp - 2160)) n buf.
  Proof.
    intros m F. pose proof Hsp. pose proof Hs64 as [S1 S2]. pose proof Hd. pose proof Hdn. pose proof Hn. pose proof HK as (K0 & KL & K40 & Kn).
    pose proof SB_val. pose proof (sn_sap _ _ _ _ _ _ _ H) as AP. pose proof (sn_dst _ _ _ _ _ _ _ H) as DP.
    pose proof (sn_shd _ _ _ _ _ _ _ H) as SHD. unfold ISN_FRAME in *.
    pose proof (cells_sfr m F) as (C & AI & GF & RS & RSL & RSC & RM & GI & BI & RMS & RO).
    pose proof F as (F1 & F2 & F3).
    destruct dfacts as (D0 & D1 & DM & Dshd & D01 & HSB & HdK & Hn8).
    constructor; rewrite ?zbv_u by lia; unfold VBothMuslStrncpy.SNC_FRAME.
    - rewrite (rdn_sfr_out m); [exact (sn_buf _ _ _ _ _ _ _ H)|exact F|lia|lia|unfold ISN_FRAME; lia].
    - right. exists K. split; [lia|]. split; [exact (sn_zero_K _ _ _ _ _ _ _ H)|].
      pose proof (sn_win _ _ _ _ _ _ _ H) as W. unfold VBothMuslStrlen.strlen_span.
      pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)).
      destruct (K <? VBothMuslStrlen.hd s)%Z; lia.
    - apply store_ok_bytes; [lia | rewrite Z2Nat.id by lia; lia |]. intros j Hj. rewrite Z2Nat.id in Hj by lia.
      apply F2. apply (sn_dok _ _ _ _ _ _ _ H). lia.
    - lia.
    - lia.
    - lia.
    - exact (sn_disj _ _ _ _ _ _ _ H).
    - exact RO.
    - exact (sn_dro _ _ _ _ _ _ _ H).
    - intros a Ha. apply F2. apply (sn_stk _ _ _ _ _ _ _ H). unfold ISN_FRAME. lia.
    - unfold BothRegionPoisoned.SB in *. lia.
    - lia.
    - lia.
    - intros _. exact (sn_rngd _ _ _ _ _ _ _ H).
    - intros _. lia.
    - intros g _ Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). exact (sn_zgd _ _ _ _ _ _ _ H g Hg).
    - intros _. destruct last_d as (b1 & L1 & B1). exists b1. split; [|exact B1].
      rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISN_FRAME; lia]). exact L1.
    - intros _ a Ha Hb Hm.
      pose proof (Z.div_mod (SB + d / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + d / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SB + (d + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (d + n - 1) / 8) 8 ltac:(lia)).
      rewrite (rdn_sfr_below m); [exact (sn_wordsd _ _ _ _ _ _ _ H a Ha Hb Hm)|exact F|(ltac2:(LK.k [@H1; @SHD; @D0; @D1; @HSB; @Hn8; @Ha; @H5; @H6; @H0; @Hb; @H7]); lia)|cbn; unfold ISN_FRAME; (ltac2:(LK.k [@H1; @SHD; @D0; @D1; @HSB; @Hn8; @Ha; @H5; @H6; @H0; @Hb; @H7]); lia)].
    - split; [exact C|]. split; [exact GI|]. split; [exact BI|exact RMS].
    - exact (sn_dcel _ _ _ _ _ _ _ H).
  Qed.

  #[using="K H Hn Hd HK"] Lemma blk_C : forall regs m, sfr m -> base regs ->
    exists regs' m',
      msteps SEGS (mkst regs (0x49cf4 : word) m rom) (mkst regs' (0x49d08 : word) m' rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 (usp - 2160) /\ keep regs'
      /\ (forall x : word, (bv_unsigned x < usp - ISN_FRAME \/ usp - 2160 <= bv_unsigned x)%Z -> m' x = wbytes m (Z_to_bv 64 d) RES x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    intros regs m F B. pose proof Hsp. pose proof Hn. pose proof Hd. pose proof Hdn. pose proof Hs64 as [HS1 HS2]. pose proof I_facts as (Hi & Zi & NZi). pose proof HK as (K0 & KL & K40 & Kn).
    pose proof B as (B2 & B8 & B9 & B18 & B19 & B23 & BK). pose proof F as (F1 & F2 & F3).
    pose proof (cells_sfr m F) as (_ & _ & _ & _ & _ & RSC & _).
    assert (RSC' : cell m (0xab2d8 + 32) 0xa2f3c) by exact RSC.
    evar (rr : bvmap 5 word).
    edestruct (VBothMuslStrncpy.ref_strncpy m (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 (usp - 2160)) n buf rom rr (0x49d08 : word)
                 (sncH_m m F) ret_ok_c0f80) as (r1 & m1 & mres & M1 & AG & SP & M1o & M1g); cycle -1.
    { (* [comment removed for export] *)
      assert (EM : mres = I).
      { destruct SP as (S1 & S2 & S3 & S4).
        destruct (Z.lt_trichotomy mres I) as [LT|[EQ|GT]]; [|exact EQ|].
        - exfalso. apply (NZi mres ltac:(lia)). unfold VBothMuslStrlen.b_. apply S4. lia.
        - exfalso. apply (S3 I ltac:(lia)). unfold VBothMuslStrlen.b_ in Zi. exact Zi. }
      subst mres.
      exists r1, m1. split; [|split; [|split; [|split; [|split]]]].
      - mld F_49cf4 D_49cf4 0xa2f3c%Z RSC' B23.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49cf8 eq_refl D_49cf8)). gr. rewrite B19. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49cfc eq_refl D_49cfc)). gr. rewrite B18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49d00 eq_refl D_49d00)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa2f3c) F_49d04 eq_refl D_49d04);
                     [reflexivity | gr; reflexivity]).
        rewrite ?lit_c0f80.
        match goal with |- msteps _ (mkst ?r ?pc ?mm ?ro) _ =>
          replace pc with (0xa2f3c : word) by (apply bv_eq; vm_compute; reflexivity) end.
        subst rr. exact M1.
      - rewrite (AG 10) by (unfold VBothMuslStrncpy.strncpy_clob; cbn; intuition discriminate). subst rr. gr. reflexivity.
      - rewrite (AG 2) by (unfold VBothMuslStrncpy.strncpy_clob; cbn; intuition discriminate). subst rr. gr. exact B2.
      - intros r Hr He. rewrite (AG r (strncpy_clob_isn r Hr)). subst rr. keep_tac Hr He. apply BK; assumption.
      - intros x Hx. unfold ISN_FRAME in Hx. rewrite M1o by (unfold VBothMuslStrncpy.SNC_FRAME; rewrite zbv_u by lia; lia).
        unfold RES. reflexivity.
      - intros x Hx. apply M1g. apply F3. exact Hx. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  #[using="d s n buf K H Hret"] Lemma blk_E : forall regs mF,
    getr regs 2 = Z_to_bv 64 (usp - 2160) ->
    (forall a, (usp - 80 <= a)%Z -> (a + 8 <= usp)%Z -> rdn SEGS mF (Z_to_bv 64 a) 8 = rdn SEGS p12 (Z_to_bv 64 a) 8) ->
    exists regs',
      msteps SEGS (mkst regs (0x49d08 : word) mF rom) (mkst regs' ra mF rom)
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23 /\ getr regs' 24 = getr regs0 24
      /\ getr regs' 10 = getr regs 10
      /\ (forall r, ekeep r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs mF H2 HF. pose proof Hsp.
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18.
    pose proof rd_s3 as RD19. pose proof rd_s4 as RD20. pose proof rd_s5 as RD21. pose proof rd_s6 as RD22.
    pose proof rd_s7 as RD23. pose proof rd_s8 as RD24.
    rewrite <- HF in RD1 by lia. rewrite <- HF in RD8 by lia. rewrite <- HF in RD9 by lia. rewrite <- HF in RD18 by lia.
    rewrite <- HF in RD19 by lia. rewrite <- HF in RD20 by lia. rewrite <- HF in RD21 by lia. rewrite <- HF in RD22 by lia.
    rewrite <- HF in RD23 by lia. rewrite <- HF in RD24 by lia.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49d08 eq_refl D_49d08)). rewrite H2. zn.
      mld2 F_49d0c D_49d0c ra RD1 H2.
      mld2 F_49d10 D_49d10 (getr regs0 8) RD8 H2.
      mld2 F_49d14 D_49d14 (getr regs0 9) RD9 H2.
      mld2 F_49d18 D_49d18 (getr regs0 18) RD18 H2.
      mld2 F_49d1c D_49d1c (getr regs0 19) RD19 H2.
      mld2 F_49d20 D_49d20 (getr regs0 20) RD20 H2.
      mld2 F_49d24 D_49d24 (getr regs0 21) RD21 H2.
      mld2 F_49d28 D_49d28 (getr regs0 22) RD22 H2.
      mld2 F_49d2c D_49d2c (getr regs0 23) RD23 H2.
      mld2 F_49d30 D_49d30 (getr regs0 24) RD24 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_49d34 eq_refl D_49d34)). gr. zn.
      replace (usp - 2160 + 128 + 2032)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_49d38 eq_refl D_49d38); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r He. unfold ekeep in He.
      repeat (rewrite getr_other by (intros ->; cbn in He; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="s K H Hret H01 H02 H010 H011 H012 Hn Hd HK"] Theorem isn_body :
    exists regs' m',
      msteps SEGS (mkst regs0 (0x49bc0 : word) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, isn_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - ISN_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = wbytes mem (Z_to_bv 64 d) RES x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    pose proof Hsp as HU. pose proof I_facts as (Hi & _). pose proof Hd. pose proof Hdn. pose proof Hn.
    destruct blk_P as (q1 & MP & PB & P12).
    destruct (blk_N q1 PB P12) as (q2 & m1 & MN & F1 & NB & N10).
    destruct (blk_O q2 m1 NB N10) as (q3 & MO & OB & O20 & O21 & O24 & O10 & O11).
    destruct (blk_R q3 m1 F1 OB O20 O21 O24 O10 O11) as (q4 & m4 & MR & F4 & R24 & RB).
    destruct (blk_W q4 m4 F4 RB) as (q5 & m5 & MW & F5 & W24 & WB).
    destruct (blk_C q5 m5 F5 WB) as (q6 & m6 & MC & C10 & C2 & CK & M6o & M6g).
    pose proof F5 as (F51 & F52 & F53).
    destruct (blk_E q6 m6 C2) as (q7 & M7 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E10 & EK).
    { intros a Ha1 Ha2.
      assert (LR : Z.of_nat (length RES) = n).
      { unfold RES. rewrite length_app, length_firstn, ZStores.length_zeros. pose proof HK as (_ & KL & _). lia. }
      pose proof (sn_dst _ _ _ _ _ _ _ H) as DP. unfold ISN_FRAME in DP.
      apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx.
      rewrite M6o by lia. rewrite MemSplit.wbytes_outside by (rewrite zbv_u by lia; lia). apply F51. lia. }
    exists q7, m6. split; [|split; [rewrite E10; exact C10|split; [exact E2|split; [exact E1|split; [|split; [|exact M6g]]]]]].
    - eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MN|]. eapply msteps_trans; [exact MO|].
      eapply msteps_trans; [exact MR|]. eapply msteps_trans; [exact MW|]. eapply msteps_trans; [exact MC|]. exact M7.
    - intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite E1; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite E2; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact E8|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact E9|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact E18|].
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact E19|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact E20|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact E21|].
      destruct (bv_eq_dec _ r 22) as [-> | N22]; [exact E22|].
      destruct (bv_eq_dec _ r 23) as [-> | N23]; [exact E23|].
      destruct (bv_eq_dec _ r 24) as [-> | N24]; [exact E24|].
      assert (He : ekeep r = false).
      { unfold ekeep. rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8), (bv_eqb_neq _ _ N9),
          (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N22),
          (bv_eqb_neq _ _ N23), (bv_eqb_neq _ _ N24). reflexivity. }
      rewrite (EK r He). apply CK; assumption.
    - intros x Hx. rewrite M6o by (unfold ISN_FRAME in *; lia). apply VBothMemsetWalk.wbytes_agree. apply (sfr_out m5 x F5). exact Hx.
  Qed.
End ISN.

(* [comment removed for export] *)
Theorem isn_run :
  forall (mem rom : word -> option byte) (d s n usp : Z) (buf : list byte) (K : Z),
  isnH mem d s n usp buf K ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
  getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
  let I := Z.of_nat (fz buf) in
  exists regs' m',
    msteps SEGS (mkst regs (0x442b0 : word) mem rom) (mkst regs' ra m' rom)
    /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, isn_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - ISN_FRAME \/ usp <= bv_unsigned x)%Z ->
          m' x = wbytes mem (Z_to_bv 64 d) (firstn (Z.to_nat I) buf ++ zeros (Z.to_nat (n - I))) x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (0 <= I <= K)%Z /\ bv_unsigned (VBothMuslStrlen.b_ buf I) = 0%Z
    /\ (forall j, (0 <= j < I)%Z -> bv_unsigned (VBothMuslStrlen.b_ buf j) <> 0%Z).
Proof.
  intros mem rom d s n usp buf K H regs ra Hret H1 H2 H10 H11 H12 I.
  destruct (isn_body mem rom d s n usp buf K H regs ra Hret H1 H2 H10 H11 H12) as (regs' & m' & M & A & B & C & D & E & F).
  pose proof (I_facts mem d s n usp buf K H) as (G1 & G2 & G3).
  exists regs', m'. split; [|split; [exact A|split; [exact B|split; [exact C|split; [exact D|split; [exact E|split; [exact F|]]]]]]].
  - mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_442b0 eq_refl D_442b0)). exact M.
  - split; [exact G1|]. split; [exact G2|exact G3].
Qed.
