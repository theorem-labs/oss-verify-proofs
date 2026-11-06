(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 GrayLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14_code_gmD.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section SBV.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables pix w h wpl data sp : Z.
  Variables left right top bot val : Z.
  Variables ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word.     (* [comment removed for export] *)

  Hypothesis Hpix : (1 <= pix /\ pix + 64 <= 2 ^ 64)%Z.
  Hypothesis ALpix : is_aligned pix 8.
  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hwpl : (w <= 4 * wpl /\ wpl <= 20000)%Z.
  Hypothesis Hsp : (112 <= sp /\ sp < 2 ^ 64)%Z.
  Hypothesis ALsp : is_aligned sp 16.
  Hypothesis Hra : ret_ok ra.
  Hypothesis Hl : (1 <= left < w)%Z.
  Hypothesis Hr : (1 <= right < w)%Z.
  Hypothesis Ht : (1 <= top)%Z.
  Hypothesis Hb : (1 <= bot)%Z.
  Hypothesis Htb : (top + bot < h)%Z.
  (* [comment removed for export] *)
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 8).
  Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
  Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
  #[local] Abbreviation RS := (4 * (wpl * h))%Z (only parsing).
  Hypothesis Hdata : (4 <= data /\ data + RS <= 2 ^ 64 /\ data mod 4 = 0)%Z.
  Hypothesis SOKr : store_ok SEGS M (Z_to_bv 64 data) (Z.to_nat RS) = true.
  Hypothesis FR : disj_apart data RS (sp - 112) 112.
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 112)) 112 = true.
  Hypothesis FP : disj_apart pix 64 (sp - 112) 112.

  (* [comment removed for export] *)
  Definition M1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 s5v))
      (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 s6v))
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 8 s7v))
      (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 s8v))
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 s9v).
  (* [comment removed for export] *)
  Definition M2 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (sp - 92)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 92)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (sp - 100)) (word_to_le_bytes 4 (Z_to_bv 64 8)).

  Lemma sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 112)%Z ->
    store_ok SEGS m (Z_to_bv 64 (sp - k)) n = true.
  Proof.
    intros m k n Hg Hk. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - 112)) _ 112%nat); [ | exact SOKf | | ];
      rewrite ?u_Z2bv by lia; lia.
  Qed.

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac sokf := apply sok_frame; [ unfold M1, M2; grows | cbn; lia ].
  Ltac peelf := unfold M2, M1; repeat (rewrite rdn_wbytes_out_Z by (zlen; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).

  Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
  Proof.
    intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
    rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
  Qed.
  Lemma lez4 : forall z, (0 <= z < 2 ^ 32)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
  Proof.
    intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sp_slot4 : forall k, (k mod 4 = 0)%Z -> ((sp - k) mod 4 = 0)%Z.
  Proof. intros k Hk. pose proof ALsp as AL. use_aligned AL. apply mod0_sub; [lia | apply mod16_mod4; exact AL | exact Hk]. Qed.
  Lemma pix_al8 : (pix mod 8 = 0)%Z.
  Proof. pose proof ALpix as AL. use_aligned AL. exact AL. Qed.

  Ltac stf F D k v := stepST F D (Z_to_bv 64 (sp - k)) v ltac:(sokf).
  Ltac ldpix F D z C :=
    stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z)
      ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelf; exact C)
      ltac:(apply lez4; lia);
    rewrite ?(v_lw_small z) by lia.
  Ltac ldf F D k z :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
      ltac:(unfold M2, M1; rdn_addr (sp - k)%Z; rdn_chain)
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite ?(v_lw_small z) by lia.
  Ltac andi_slot F D k :=
    stepiv F D (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; rewrite andi_3, u_Z2bv by lia; rewrite (sp_slot4 k) by reflexivity; reflexivity).
  Ltac andi_pix F D :=
    stepiv F D (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; rewrite andi_7, u_Z2bv by lia; rewrite pix_al8; reflexivity).
  (* [comment removed for export] *)
  Ltac zvw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?v_addi_0; rewrite ?zbv_addiw_small by lia;
                                       rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_A : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v ->
    getr regs 21 = s5v -> getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v -> getr regs 25 = s9v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
    getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x17afc : word) M rom) (mkst regs' (0x17cf0 : word) M2 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 112) /\ getr regs' 9 = Z_to_bv 64 data /\ getr regs' 18 = Z_to_bv 64 left
      /\ getr regs' 19 = Z_to_bv 64 top /\ getr regs' 20 = Z_to_bv 64 right /\ getr regs' 21 = Z_to_bv 64 bot
      /\ getr regs' 23 = Z_to_bv 64 w /\ getr regs' 24 = Z_to_bv 64 right /\ getr regs' 10 = Z_to_bv 64 wpl
      /\ regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H10 H11 H12 H13 H14 H15. use_apart FP.
    eexists. split.
    - zv F_17a00 D_17a00 (Z_to_bv 64 (sp - 112)).          (* [comment removed for export] *)
      stf F_17a04 D_17a04 8%Z ra.
      stf F_17a08 D_17a08 16%Z s0v.
      stf F_17a0c D_17a0c 24%Z s1v.
      stf F_17a10 D_17a10 32%Z s2v.
      stf F_17a14 D_17a14 40%Z s3v.
      stf F_17a18 D_17a18 48%Z s4v.
      stf F_17a1c D_17a1c 56%Z s5v.
      stf F_17a20 D_17a20 64%Z s6v.
      stf F_17a24 D_17a24 72%Z s7v.
      stf F_17a28 D_17a28 80%Z s8v.
      stf F_17a2c D_17a2c 88%Z s9v.
      fold M1.
      stepb_ft F_17a30 D_17a30 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17a34 D_17a34.                                   (* [comment removed for export] *)
      zv F_17a38 D_17a38 (Z_to_bv 64 bot).                  (* [comment removed for export] *)
      zv F_17a3c D_17a3c (Z_to_bv 64 top).                  (* [comment removed for export] *)
      zv F_17a40 D_17a40 (Z_to_bv 64 right).                (* [comment removed for export] *)
      zv F_17a44 D_17a44 (Z_to_bv 64 left).                 (* [comment removed for export] *)
      zv F_17a48 D_17a48 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      zv F_17a4c D_17a4c (Z_to_bv 64 (sp - 92)).            (* [comment removed for export] *)
      zv F_17a50 D_17a50 (Z_to_bv 64 (sp - 96)).            (* [comment removed for export] *)
      zv F_17a54 D_17a54 (Z_to_bv 64 (sp - 100)).           (* [comment removed for export] *)
      sn F_17a58 D_17a58.                                   (* [comment removed for export] *)
      andi_slot F_15f04 D_15f04 92%Z.                       (* [comment removed for export] *)
      stepb_ft F_15f08 D_15f08 ltac:(condZ).
      stepb_ft F_15f0c D_15f0c ltac:(condZ).                (* [comment removed for export] *)
      stf F_15f10 D_15f10 92%Z (Z_to_bv 64 0).
      andi_slot F_15f14 D_15f14 96%Z.
      stepb_ft F_15f18 D_15f18 ltac:(condZ).
      stepb_ft F_15f1c D_15f1c ltac:(condZ).                (* [comment removed for export] *)
      stf F_15f20 D_15f20 96%Z (Z_to_bv 64 0).
      andi_slot F_15f24 D_15f24 100%Z.
      stepb_ft F_15f28 D_15f28 ltac:(condZ).
      stepb_ft F_15f2c D_15f2c ltac:(condZ).                (* [comment removed for export] *)
      stf F_15f30 D_15f30 100%Z (Z_to_bv 64 0).
      stepb_ft F_15f34 D_15f34 ltac:(condZ).                (* [comment removed for export] *)
      andi_pix F_15f38 D_15f38.                             (* [comment removed for export] *)
      stepb_ft F_15f3c D_15f3c ltac:(condZ).
      sn F_15f40 D_15f40.                                   (* [comment removed for export] *)
      stepb_ft F_15f44 D_15f44 ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_15f48 D_15f48 w Cw.
      stf F_15f4c D_15f4c 92%Z (Z_to_bv 64 w).
      stepb_ft F_15f50 D_15f50 ltac:(condZ).
      sn F_15f54 D_15f54.                                   (* [comment removed for export] *)
      stepb_ft F_15f58 D_15f58 ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_15f5c D_15f5c h Ch.
      stf F_15f60 D_15f60 96%Z (Z_to_bv 64 h).
      stepb_ft F_15f64 D_15f64 ltac:(condZ).
      sn F_15f68 D_15f68.                                   (* [comment removed for export] *)
      stepb_ft F_15f6c D_15f6c ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_15f70 D_15f70 8%Z Cd.
      stf F_15f74 D_15f74 100%Z (Z_to_bv 64 8).
      sn F_15f78 D_15f78.                                   (* [comment removed for export] *)
      stepret F_15f7c D_15f7c (0x17b58 : word) ltac:(bveq).
      fold M2.
      (* [comment removed for export] *)
      ldf F_17a5c D_17a5c 100%Z 8%Z.                        (* [comment removed for export] *)
      sn F_17a60 D_17a60.                                   (* [comment removed for export] *)
      stepb_ft F_17a64 D_17a64 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17a68 D_17a68.                                   (* [comment removed for export] *)
      sn F_17a6c D_17a6c.                                   (* [comment removed for export] *)
      sn F_17a70 D_17a70.                                   (* [comment removed for export] *)
      sn F_17a74 D_17a74.                                   (* [comment removed for export] *)
      sn F_17a78 D_17a78. fixv (Z_to_bv 64 1) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_17a7c D_17a7c ltac:(condZ).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      ldf F_17a80 D_17a80 96%Z h.                           (* [comment removed for export] *)
      stepb_tk F_17a84 D_17a84 ltac:(condZ).                (* [comment removed for export] *)
      stepb_tk F_17aa8 D_17aa8 ltac:(condZ).                (* [comment removed for export] *)
      ldf F_17a90 D_17a90 92%Z w.                           (* [comment removed for export] *)
      stepb_tk F_17a94 D_17a94 ltac:(condZ).                (* [comment removed for export] *)
      zv F_17ab8 D_17ab8 (Z_to_bv 64 right).                (* [comment removed for export] *)
      stepb_tk F_17abc D_17abc ltac:(condZ).                (* [comment removed for export] *)
      zv F_17ac4 D_17ac4 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_17ac8 D_17ac8.                                   (* [comment removed for export] *)
      stepb_ft F_16d18 D_16d18 ltac:(condZ).
      andi_pix F_16d1c D_16d1c.                             (* [comment removed for export] *)
      stepb_ft F_16d20 D_16d20 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_16d24 D_16d24 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelf; exact Cdata)
        ltac:(apply lez8; lia).
      stepret F_16d28 D_16d28 (0x17bc8 : word) ltac:(bveq).
      zv F_17acc D_17acc (Z_to_bv 64 data).                 (* [comment removed for export] *)
      zv F_17ad0 D_17ad0 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_17ad4 D_17ad4.                                   (* [comment removed for export] *)
      stepb_ft F_15bac D_15bac ltac:(condZ).
      andi_pix F_15bb0 D_15bb0.
      stepb_ft F_15bb4 D_15bb4 ltac:(condR).                (* [comment removed for export] *)
      ldpix F_15bb8 D_15bb8 wpl Cwpl.
      stepret F_15bbc D_15bbc (0x17bd4 : word) ltac:(bveq).
      ldf F_17ad8 D_17ad8 100%Z 8%Z.                        (* [comment removed for export] *)
      sn F_17adc D_17adc.                                   (* [comment removed for export] *)
      stepb_tk F_17ae0 D_17ae0 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < data \/ data + RS <= bv_unsigned x)%Z -> Mi x = M2 x) /\ mem_grows M2 Mi.
  Lemma Inv_M2 : Inv M2.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
  Lemma M2_grows : mem_grows M M2.
  Proof. unfold M2, M1. grows. Qed.

  Lemma Inv_store : forall Mi (a : Z) (bs : list byte),
    Inv Mi -> (data <= a)%Z -> (a + Z.of_nat (length bs) <= data + RS)%Z -> Inv (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb'. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb'. split.
    - intros x Hx. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Lemma Inv_sok : forall Mi (a : Z) (n : nat), Inv Mi -> (data <= a)%Z -> (a + Z.of_nat n <= data + RS)%Z ->
    store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi a n [_ HG] Ha Hn. eapply store_ok_mono; [eapply mem_grows_trans; [exact M2_grows | exact HG]|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 data) _ (Z.to_nat RS)); [ | exact SOKr | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma Inv_rdn_frame : forall Mi (a : Z) (n : nat) bs, Inv Mi -> (sp - 112 <= a)%Z -> (a + Z.of_nat n <= sp)%Z ->
    rdn SEGS M2 (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros Mi a n bs [HI _] Ha Hn HM. use_apart FR. rewrite <- HM.
    assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_Z2bv; lia).
    apply rdn_ext; rewrite U; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  Lemma F_w : rdn SEGS M2 (Z_to_bv 64 (sp - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)).
  Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_h : rdn SEGS M2 (Z_to_bv 64 (sp - 96)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).
  Proof. unfold M2, M1. rdn_chain. Qed.

  Lemma row_bound : forall i, (0 <= i < h)%Z -> (4 * wpl * i + 4 * wpl <= RS)%Z.
  Proof.
    intros i Hi. assert (wpl * i <= wpl * (h - 1))%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.
  Lemma row_mod4 : forall i, ((data + 4 * wpl * i) mod 4 = 0)%Z.
  Proof.
    intros i. replace (data + 4 * wpl * i)%Z with (data + (wpl * i) * 4)%Z by lia.
    rewrite Z_mod_plus_full. exact (proj2 (proj2 Hdata)).
  Qed.
  Lemma line_ok : forall i, (0 <= i < h)%Z -> (data <= data + 4 * wpl * i /\ data + 4 * wpl * i + 4 * wpl <= data + RS)%Z.
  Proof. intros i Hi. pose proof (row_bound i Hi). assert (0 <= wpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia). lia. Qed.
  Lemma wi_bound : forall i, (0 <= i <= h)%Z -> (0 <= wpl * i <= 400000000)%Z.
  Proof. intros i Hi. split; [apply Z.mul_nonneg_nonneg; lia | change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia]. Qed.

  Ltac ldw F D HIv :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w)
      ltac:(rdn_addr (sp - 92)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact F_w])
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite ?(v_lw_small w) by lia.
  Ltac ldh F D HIv :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h)
      ltac:(rdn_addr (sp - 96)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact F_h])
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite ?(v_lw_small h) by lia.
  Ltac gsb F D aa HIv :=
    chain_step;
    [ reflexivity
    | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 aa);
      [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | reflexivity
      | apply (Inv_sok _ aa 1 HIv); [lia | cbn; lia] ]
    | step_simpl ].
  (* [comment removed for export] *)
  Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
  Ltac sltu0 F D := sn F D; fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
  Ltac slti0 F D := sn F D; fixv (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
  Ltac snez1 F D := sn F D; fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
  Ltac mulw_v F D v := sn F D; fixv v ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
  Ltac addw_v F D v := sn F D; fixv v ltac:(rewrite zbv_addw_small by lia; f_equal; lia).
  Ltac subw_v F D v := sn F D; fixv v ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section LINE.
  Variable L : Z.
  Hypothesis HL : (data <= L /\ L + 4 * wpl <= data + RS)%Z.
  Hypothesis HL4 : (L mod 4 = 0)%Z.

  (* [comment removed for export] *)
  Lemma sbv_T_byte : forall regs Mi j,
    (0 <= j < w)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 16 = Z_to_bv 64 L ->
    getr regs 17 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (L + j) -> getr regs 6 = Z_to_bv 64 (L + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17d60 : word) Mi rom) (mkst regs' (0x17d8c : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w /\ getr regs' 17 = Z_to_bv 64 (j + 1)
      /\ getr regs' 5 = Z_to_bv 64 (L + (j + 1)) /\ getr regs' 6 = Z_to_bv 64 (L + (j + 1))
      /\ regs_agree (fun r : reg => In r [5; 6; 12; 17]%list) regs regs'.
  Proof.
    intros regs Mi j Hj HIv H2 H14 H15 H16 H17 H5 H6.
    pose proof (xo_bound j wpl ltac:(lia)) as XB.
    assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))])).
    { apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]. }
    eexists. eexists. split; [|split; [exact HI'|]].
    - stepb_ft F_17c64 D_17c64 ltac:(condZ).                (* [comment removed for export] *)
      seqz0 F_17c68 D_17c68.                                (* [comment removed for export] *)
      sn F_17c6c D_17c6c.                                   (* [comment removed for export] *)
      stepb_ft F_17c70 D_17c70 ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_17c74 D_17c74 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_17c78 D_17c78 (Z_to_bv 64 (L + xo j))
        ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).   (* [comment removed for export] *)
      gsb F_17c7c D_17c7c (L + xo j)%Z HIv.                 (* [comment removed for export] *)
      ldw F_17c80 D_17c80 HI'.                              (* [comment removed for export] *)
      zv F_17c84 D_17c84 (Z_to_bv 64 (j + 1)).              (* [comment removed for export] *)
      zv F_17c88 D_17c88 (Z_to_bv 64 (L + (j + 1))).        (* [comment removed for export] *)
      zv F_17c8c D_17c8c (Z_to_bv 64 (L + (j + 1))).       (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_T_bytes : forall (k : nat) regs Mi j,
    (0 <= j)%Z -> (j + Z.of_nat k = w - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 16 = Z_to_bv 64 L ->
    getr regs 17 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (L + j) -> getr regs 6 = Z_to_bv 64 (L + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17d60 : word) Mi rom) (mkst regs' (0x17d08 : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [5; 6; 12; 17]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi j Hj Hk HIv H2 H14 H15 H16 H17 H5 H6;
      destruct (sbv_T_byte regs Mi j ltac:(lia) HIv H2 H14 H15 H16 H17 H5 H6) as (r1 & Ma & S1 & HI1 & A12 & A17 & A5 & A6 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact A12 | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_17c90 D_17c90 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17c94 D_17c94.                                   (* [comment removed for export] *)
      apply mst_refl.
    - pose proof (AG1 2 ltac:(notin_list)) as A2. rewrite H2 in A2.
      pose proof (AG1 14 ltac:(notin_list)) as A14. rewrite H14 in A14.
      pose proof (AG1 15 ltac:(notin_list)) as A15. rewrite H15 in A15.
      pose proof (AG1 16 ltac:(notin_list)) as A16. rewrite H16 in A16.
      destruct (IH r1 Ma (j + 1)%Z ltac:(lia) ltac:(lia) HI1 A2 A14 A15 A16 A17 A5 A6) as (r2 & Mb & S2 & HI2 & B12 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B12|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_17c90 D_17c90 ltac:(condZ).
        exact S2.
      + eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_byte : forall regs Mi j,
    (0 <= j < w)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 16 = Z_to_bv 64 L ->
    getr regs 17 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (L + j) -> getr regs 6 = Z_to_bv 64 (L + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x181d0 : word) Mi rom) (mkst regs' (0x181fc : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w /\ getr regs' 17 = Z_to_bv 64 (j + 1)
      /\ getr regs' 5 = Z_to_bv 64 (L + (j + 1)) /\ getr regs' 6 = Z_to_bv 64 (L + (j + 1))
      /\ regs_agree (fun r : reg => In r [5; 6; 12; 17]%list) regs regs'.
  Proof.
    intros regs Mi j Hj HIv H2 H14 H15 H16 H17 H5 H6.
    pose proof (xo_bound j wpl ltac:(lia)) as XB.
    assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))])).
    { apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]. }
    eexists. eexists. split; [|split; [exact HI'|]].
    - stepb_ft F_180d4 D_180d4 ltac:(condZ).                (* [comment removed for export] *)
      seqz0 F_180d8 D_180d8.                                (* [comment removed for export] *)
      sn F_180dc D_180dc.                                   (* [comment removed for export] *)
      stepb_ft F_180e0 D_180e0 ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_180e4 D_180e4 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_180e8 D_180e8 (Z_to_bv 64 (L + xo j))
        ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).   (* [comment removed for export] *)
      gsb F_180ec D_180ec (L + xo j)%Z HIv.                 (* [comment removed for export] *)
      ldw F_180f0 D_180f0 HI'.                              (* [comment removed for export] *)
      zv F_180f4 D_180f4 (Z_to_bv 64 (j + 1)).              (* [comment removed for export] *)
      zv F_180f8 D_180f8 (Z_to_bv 64 (L + (j + 1))).        (* [comment removed for export] *)
      zv F_180fc D_180fc (Z_to_bv 64 (L + (j + 1))).       (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_bytes : forall (k : nat) regs Mi j,
    (0 <= j)%Z -> (j + Z.of_nat k = w - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 -> getr regs 16 = Z_to_bv 64 L ->
    getr regs 17 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (L + j) -> getr regs 6 = Z_to_bv 64 (L + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x181d0 : word) Mi rom) (mkst regs' (0x18200 : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [5; 6; 12; 17]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi j Hj Hk HIv H2 H14 H15 H16 H17 H5 H6;
      destruct (sbv_B_byte regs Mi j ltac:(lia) HIv H2 H14 H15 H16 H17 H5 H6) as (r1 & Ma & S1 & HI1 & A12 & A17 & A5 & A6 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact A12 | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_18100 D_18100 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - pose proof (AG1 2 ltac:(notin_list)) as A2. rewrite H2 in A2.
      pose proof (AG1 14 ltac:(notin_list)) as A14. rewrite H14 in A14.
      pose proof (AG1 15 ltac:(notin_list)) as A15. rewrite H15 in A15.
      pose proof (AG1 16 ltac:(notin_list)) as A16. rewrite H16 in A16.
      destruct (IH r1 Ma (j + 1)%Z ltac:(lia) ltac:(lia) HI1 A2 A14 A15 A16 A17 A5 A6) as (r2 & Mb & S2 & HI2 & B12 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B12|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_18100 D_18100 ltac:(condZ).
        exact S2.
      + eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  End LINE.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_T_pre : forall regs Mi,
    getr regs 9 = Z_to_bv 64 data -> getr regs 19 = Z_to_bv 64 top ->
    exists regs',
      msteps SEGS (mkst regs (0x17cf0 : word) Mi rom) (mkst regs' (0x17d14 : word) Mi rom)
      /\ getr regs' 11 = Z_to_bv 64 (wpl * 0) /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 3
      /\ regs_agree (fun r : reg => In r [11; 13; 14; 15]%list) regs regs'.
  Proof.
    intros regs Mi H9 H19. eexists. split.
    - stepb_ft F_17bf4 D_17bf4 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17bf8 D_17bf8. fixv (Z_to_bv 64 (wpl * 0)) ltac:(f_equal; lia).   (* [comment removed for export] *)
      sn F_17bfc D_17bfc.                                   (* [comment removed for export] *)
      snez1 F_17c00 D_17c00.                                (* [comment removed for export] *)
      sn F_17c04 D_17c04.                                   (* [comment removed for export] *)
      sn F_17c08 D_17c08.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_T_head : forall regs Mi i, (0 <= i < h)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 11 = Z_to_bv 64 (wpl * i) -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x17d14 : word) Mi rom) (mkst regs' (0x17d60 : word) Mi rom)
      /\ getr regs' 16 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 17 = Z_to_bv 64 0
      /\ getr regs' 5 = Z_to_bv 64 (data + 4 * wpl * i + 0) /\ getr regs' 6 = Z_to_bv 64 (data + 4 * wpl * i + 0)
      /\ regs_agree (fun r : reg => In r [5; 6; 12; 16; 17]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv H2 H9 H10 H11 H13 H14.
    pose proof (wi_bound i ltac:(lia)) as WI. pose proof (line_ok i Hi) as LOK.
    eexists. split.
    - zv F_17c18 D_17c18 (Z_to_bv 64 (wpl * i)).            (* [comment removed for export] *)
      mulw_v F_17c1c D_17c1c (Z_to_bv 64 (wpl * i)).        (* [comment removed for export] *)
      stepb_ft F_17c20 D_17c20 ltac:(condR).                (* [comment removed for export] *)
      zvw F_17c24 D_17c24 (Z_to_bv 64 (wpl * i)).           (* [comment removed for export] *)
      zvs F_17c28 D_17c28 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_17c2c D_17c2c (Z_to_bv 64 (data + 4 * wpl * i)). (* [comment removed for export] *)
      seqz0 F_17c30 D_17c30.                                (* [comment removed for export] *)
      stepb_ft F_17c34 D_17c34 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_17c38 D_17c38.                                (* [comment removed for export] *)
      slti0 F_17c3c D_17c3c.                                (* [comment removed for export] *)
      sn F_17c40 D_17c40.                                   (* [comment removed for export] *)
      sn F_17c44 D_17c44.                                   (* [comment removed for export] *)
      stepb_ft F_17c48 D_17c48 ltac:(condR).                (* [comment removed for export] *)
      ldw F_17c4c D_17c4c HIv.                              (* [comment removed for export] *)
      stepb_ft F_17c50 D_17c50 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17c54 D_17c54.                                   (* [comment removed for export] *)
      zvs F_17c58 D_17c58 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_17c5c D_17c5c (Z_to_bv 64 (data + 4 * wpl * i + 0)).   (* [comment removed for export] *)
      zv F_17c60 D_17c60 (Z_to_bv 64 (data + 4 * wpl * i + 0)).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_T_rows : forall (k : nat) regs Mi i,
    (0 <= i)%Z -> (i + Z.of_nat k = top - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 11 = Z_to_bv 64 (wpl * i) -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 ->
    getr regs 19 = Z_to_bv 64 top ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17d14 : word) Mi rom) (mkst regs' (0x18050 : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [5; 6; 11; 12; 13; 16; 17]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv H2 H9 H10 H11 H13 H14 H15 H19.
    all: pose proof (wi_bound i ltac:(lia)) as WI; pose proof (wi_bound (i + 1) ltac:(lia)) as WI1.
    all: destruct (sbv_T_head regs Mi i ltac:(lia) HIv H2 H9 H10 H11 H13 H14) as (r0 & S0 & Z16 & Z17 & Z5 & Z6 & AG0).
    all: pose proof (AG0 2 ltac:(notin_list)) as Z2; rewrite H2 in Z2.
    all: pose proof (AG0 14 ltac:(notin_list)) as Z14; rewrite H14 in Z14.
    all: pose proof (AG0 15 ltac:(notin_list)) as Z15; rewrite H15 in Z15.
    all: destruct (sbv_T_bytes (data + 4 * wpl * i) (line_ok i ltac:(lia)) (row_mod4 i) (Z.to_nat (w - 1)) r0 Mi 0
                     ltac:(lia) ltac:(lia) HIv Z2 Z14 Z15 Z16 Z17 Z5 Z6) as (r1 & Ma & S1 & HI1 & A12 & AG1).
    all: assert (AG01 : regs_agree (fun r : reg => In r [5; 6; 12; 16; 17]%list) regs r1)
           by (eapply regs_agree_trans; [regs_agree_weaken AG0 | regs_agree_weaken AG1]).
    all: pose proof (AG01 10 ltac:(notin_list)) as A10; rewrite H10 in A10.
    all: pose proof (AG01 11 ltac:(notin_list)) as A11; rewrite H11 in A11.
    all: pose proof (AG01 13 ltac:(notin_list)) as A13; rewrite H13 in A13.
    all: pose proof (AG01 19 ltac:(notin_list)) as A19; rewrite H19 in A19.
    - eexists. exists Ma. split; [|split; [exact HI1 | split]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|].
        zvw F_17c0c D_17c0c (Z_to_bv 64 (i + 1)).           (* [comment removed for export] *)
        addw_v F_17c10 D_17c10 (Z_to_bv 64 (wpl * (i + 1))).   (* [comment removed for export] *)
        stepb_tk F_17c14 D_17c14 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact A12.
      + eapply regs_agree_trans; [regs_agree_weaken AG01|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x17d08 : word) Ma rom) (mkst r2 (0x17d14 : word) Ma rom)
                   /\ getr r2 13 = Z_to_bv 64 (i + 1) /\ getr r2 11 = Z_to_bv 64 (wpl * (i + 1))
                   /\ regs_agree (fun r : reg => In r [11; 13]%list) r1 r2).
      { eexists. split; [|split; [|split]].
        - zvw F_17c0c D_17c0c (Z_to_bv 64 (i + 1)).
          addw_v F_17c10 D_17c10 (Z_to_bv 64 (wpl * (i + 1))).
          stepb_ft F_17c14 D_17c14 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & B13 & B11 & AG2).
      pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite (AG01 2 ltac:(notin_list)), H2 in B2.
      pose proof (AG2 9 ltac:(notin_list)) as B9; rewrite (AG01 9 ltac:(notin_list)), H9 in B9.
      pose proof (AG2 10 ltac:(notin_list)) as B10; rewrite A10 in B10.
      pose proof (AG2 14 ltac:(notin_list)) as B14; rewrite (AG01 14 ltac:(notin_list)), H14 in B14.
      pose proof (AG2 15 ltac:(notin_list)) as B15; rewrite (AG01 15 ltac:(notin_list)), H15 in B15.
      pose proof (AG2 19 ltac:(notin_list)) as B19; rewrite A19 in B19.
      destruct (IH r2 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 B2 B9 B10 B11 B13 B14 B15 B19) as (r3 & Mb & S3 & HI3 & C12 & AG3).
      exists r3, Mb. split; [|split; [exact HI3 | split; [exact C12|]]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG01|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section LINE_M.
  Variable L : Z.
  Hypothesis HL : (data <= L /\ L + 4 * wpl <= data + RS)%Z.
  Hypothesis HL4 : (L mod 4 = 0)%Z.

  (* [comment removed for export] *)
  Lemma sbv_ML_bytes : forall (k : nat) regs Mi j,
    (0 <= j)%Z -> (j + Z.of_nat k = left - 1)%Z -> Inv Mi ->
    getr regs 5 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 3 -> getr regs 7 = Z_to_bv 64 L ->
    getr regs 29 = Z_to_bv 64 (L + j) -> getr regs 30 = Z_to_bv 64 (left - j) -> getr regs 31 = Z_to_bv 64 (L + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x180e4 : word) Mi rom) (mkst regs' (0x18110 : word) M' rom)
      /\ Inv M' /\ regs_agree (fun r : reg => In r [12; 29; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi j Hj Hk HIv H5 H6 H7 H29 H30 H31.
    all: pose proof (xo_bound j wpl ltac:(lia)) as XB.
    all: assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]))
           by (apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]).
    - eexists. eexists. split; [|split; [exact HI'|]].
      + stepb_ft F_17fe8 D_17fe8 ltac:(condZ).              (* [comment removed for export] *)
        seqz0 F_17fec D_17fec.                              (* [comment removed for export] *)
        sn F_17ff0 D_17ff0.                                 (* [comment removed for export] *)
        stepb_ft F_17ff4 D_17ff4 ltac:(condR).              (* [comment removed for export] *)
        stepb_ft F_17ff8 D_17ff8 ltac:(condZ).              (* [comment removed for export] *)
        stepiv F_17ffc D_17ffc (Z_to_bv 64 (L + xo j))
          ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).   (* [comment removed for export] *)
        zv F_18000 D_18000 (Z_to_bv 64 (L + (j + 1))).      (* [comment removed for export] *)
        zv F_18004 D_18004 (Z_to_bv 64 (left - (j + 1))).   (* [comment removed for export] *)
        gsb F_18008 D_18008 (L + xo j)%Z HIv.               (* [comment removed for export] *)
        zv F_1800c D_1800c (Z_to_bv 64 (L + (j + 1))).      (* [comment removed for export] *)
        stepb_ft F_18010 D_18010 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + solve_regs_agree.
    - assert (S1 : exists r1, msteps SEGS (mkst regs (0x180e4 : word) Mi rom)
                     (mkst r1 (0x180e4 : word) (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]) rom)
                   /\ getr r1 29 = Z_to_bv 64 (L + (j + 1)) /\ getr r1 30 = Z_to_bv 64 (left - (j + 1)) /\ getr r1 31 = Z_to_bv 64 (L + (j + 1))
                   /\ regs_agree (fun r : reg => In r [12; 29; 30; 31]%list) regs r1).
      { eexists. split; [|split; [|split; [|split]]].
        - stepb_ft F_17fe8 D_17fe8 ltac:(condZ).
          seqz0 F_17fec D_17fec.
          sn F_17ff0 D_17ff0.
          stepb_ft F_17ff4 D_17ff4 ltac:(condR).
          stepb_ft F_17ff8 D_17ff8 ltac:(condZ).
          stepiv F_17ffc D_17ffc (Z_to_bv 64 (L + xo j))
            ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).
          zv F_18000 D_18000 (Z_to_bv 64 (L + (j + 1))).
          zv F_18004 D_18004 (Z_to_bv 64 (left - (j + 1))).
          gsb F_18008 D_18008 (L + xo j)%Z HIv.
          zv F_1800c D_1800c (Z_to_bv 64 (L + (j + 1))).
          stepb_tk F_18010 D_18010 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & A29 & A30 & A31 & AG1).
      pose proof (AG1 5 ltac:(notin_list)) as A5; rewrite H5 in A5.
      pose proof (AG1 6 ltac:(notin_list)) as A6; rewrite H6 in A6.
      pose proof (AG1 7 ltac:(notin_list)) as A7; rewrite H7 in A7.
      destruct (IH r1 _ (j + 1)%Z ltac:(lia) ltac:(lia) HI' A5 A6 A7 A29 A30 A31) as (r2 & Mb & S2 & HI2 & AG2).
      exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2]|]. split; [exact HI2|].
      eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_MR_bytes : forall (k : nat) regs Mi j,
    (0 <= j)%Z -> (j + Z.of_nat k = w - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 5 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 3 -> getr regs 7 = Z_to_bv 64 L ->
    getr regs 28 = Z_to_bv 64 (L + j) -> getr regs 29 = Z_to_bv 64 (L + j) -> getr regs 30 = Z_to_bv 64 j ->
    exists regs' M',
      msteps SEGS (mkst regs (0x18124 : word) Mi rom) (mkst regs' (0x18160 : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [12; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi j Hj Hk HIv H2 H5 H6 H7 H28 H29 H30.
    all: pose proof (xo_bound j wpl ltac:(lia)) as XB.
    all: assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]))
           by (apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]).
    - eexists. eexists. split; [|split; [exact HI'|split]].
      + seqz0 F_18028 D_18028.                              (* [comment removed for export] *)
        stepb_ft F_1802c D_1802c ltac:(condR).              (* [comment removed for export] *)
        sltu0 F_18030 D_18030.                              (* [comment removed for export] *)
        slti0 F_18034 D_18034.                              (* [comment removed for export] *)
        sn F_18038 D_18038.                                 (* [comment removed for export] *)
        sn F_1803c D_1803c.                                 (* [comment removed for export] *)
        stepb_ft F_18040 D_18040 ltac:(condR).              (* [comment removed for export] *)
        stepb_ft F_18044 D_18044 ltac:(condZ).              (* [comment removed for export] *)
        stepiv F_18048 D_18048 (Z_to_bv 64 (L + xo j))
          ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).   (* [comment removed for export] *)
        gsb F_1804c D_1804c (L + xo j)%Z HIv.               (* [comment removed for export] *)
        ldw F_18050 D_18050 HI'.                            (* [comment removed for export] *)
        zv F_18054 D_18054 (Z_to_bv 64 (j + 1)).            (* [comment removed for export] *)
        zv F_18058 D_18058 (Z_to_bv 64 (L + (j + 1))).      (* [comment removed for export] *)
        zv F_1805c D_1805c (Z_to_bv 64 (L + (j + 1))).      (* [comment removed for export] *)
        stepb_ft F_18060 D_18060 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + gres; pin; reflexivity.
      + solve_regs_agree.
    - assert (S1 : exists r1, msteps SEGS (mkst regs (0x18124 : word) Mi rom)
                     (mkst r1 (0x18124 : word) (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]) rom)
                   /\ getr r1 28 = Z_to_bv 64 (L + (j + 1)) /\ getr r1 29 = Z_to_bv 64 (L + (j + 1)) /\ getr r1 30 = Z_to_bv 64 (j + 1)
                   /\ regs_agree (fun r : reg => In r [12; 28; 29; 30; 31]%list) regs r1).
      { eexists. split; [|split; [|split; [|split]]].
        - seqz0 F_18028 D_18028.
          stepb_ft F_1802c D_1802c ltac:(condR).
          sltu0 F_18030 D_18030.
          slti0 F_18034 D_18034.
          sn F_18038 D_18038.
          sn F_1803c D_1803c.
          stepb_ft F_18040 D_18040 ltac:(condR).
          stepb_ft F_18044 D_18044 ltac:(condZ).
          stepiv F_18048 D_18048 (Z_to_bv 64 (L + xo j))
            ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).
          gsb F_1804c D_1804c (L + xo j)%Z HIv.
          ldw F_18050 D_18050 HI'.
          zv F_18054 D_18054 (Z_to_bv 64 (j + 1)).
          zv F_18058 D_18058 (Z_to_bv 64 (L + (j + 1))).
          zv F_1805c D_1805c (Z_to_bv 64 (L + (j + 1))).
          stepb_tk F_18060 D_18060 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & A28 & A29 & A30 & AG1).
      pose proof (AG1 2 ltac:(notin_list)) as A2; rewrite H2 in A2.
      pose proof (AG1 5 ltac:(notin_list)) as A5; rewrite H5 in A5.
      pose proof (AG1 6 ltac:(notin_list)) as A6; rewrite H6 in A6.
      pose proof (AG1 7 ltac:(notin_list)) as A7; rewrite H7 in A7.
      destruct (IH r1 _ (j + 1)%Z ltac:(lia) ltac:(lia) HI' A2 A5 A6 A7 A28 A29 A30) as (r2 & Mb & S2 & HI2 & B12 & AG2).
      exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2]|]. split; [exact HI2|]. split; [exact B12|].
      eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.
  End LINE_M.

  (* [comment removed for export] *)
  Lemma sbv_M_pre : forall regs Mi, Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 12 = Z_to_bv 64 w -> getr regs 18 = Z_to_bv 64 left -> getr regs 19 = Z_to_bv 64 top ->
    getr regs 20 = Z_to_bv 64 right -> getr regs 21 = Z_to_bv 64 bot -> getr regs 23 = Z_to_bv 64 w -> getr regs 24 = Z_to_bv 64 right ->
    exists regs',
      msteps SEGS (mkst regs (0x18050 : word) Mi rom) (mkst regs' (0x1809c : word) Mi rom)
      /\ getr regs' 11 = Z_to_bv 64 (h - bot) /\ getr regs' 13 = Z_to_bv 64 (w - right) /\ getr regs' 14 = Z_to_bv 64 left
      /\ getr regs' 15 = Z_to_bv 64 (wpl * top) /\ getr regs' 16 = Z_to_bv 64 (data + (w - right))
      /\ getr regs' 17 = Z_to_bv 64 (data + (w - right)) /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 6 = Z_to_bv 64 3
      /\ regs_agree (fun r : reg => In r [5; 6; 11; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2 H9 H10 H12 H18 H19 H20 H21 H23 H24.
    pose proof (wi_bound top ltac:(lia)) as WT.
    eexists. split.
    - zv F_17f54 D_17f54 (Z_to_bv 64 (w - right)).          (* [comment removed for export] *)
      subw_v F_17f58 D_17f58 (Z_to_bv 64 (w - right)).      (* [comment removed for export] *)
      stepb_ft F_17f5c D_17f5c ltac:(condR).                (* [comment removed for export] *)
      ldh F_17f60 D_17f60 HIv.                              (* [comment removed for export] *)
      subw_v F_17f64 D_17f64 (Z_to_bv 64 (h - bot)).        (* [comment removed for export] *)
      zv F_17f68 D_17f68 (Z_to_bv 64 (h - bot)).            (* [comment removed for export] *)
      stepb_ft F_17f6c D_17f6c ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_17f70 D_17f70 ltac:(condZ).                (* [comment removed for export] *)
      zvw F_17f74 D_17f74 (Z_to_bv 64 (w - right)).         (* [comment removed for export] *)
      stepiv F_17f78 D_17f78 (Z_to_bv 64 (left * 2 ^ 32))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).             (* [comment removed for export] *)
      zv F_17f7c D_17f7c (Z_to_bv 64 (data + w)).           (* [comment removed for export] *)
      stepb_ft F_17f80 D_17f80 ltac:(condZ).                (* [comment removed for export] *)
      zv F_17f84 D_17f84 (Z_to_bv 64 right).                (* [comment removed for export] *)
      stepiv F_17f88 D_17f88 (Z_to_bv 64 left)
        ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; f_equal; apply Z.div_mul; lia).   (* [comment removed for export] *)
      mulw_v F_17f8c D_17f8c (Z_to_bv 64 (wpl * top)).      (* [comment removed for export] *)
      zv F_17f90 D_17f90 (Z_to_bv 64 (data + (w - right))). (* [comment removed for export] *)
      zv F_17f94 D_17f94 (Z_to_bv 64 (data + (w - right))). (* [comment removed for export] *)
      snez1 F_17f98 D_17f98.                                (* [comment removed for export] *)
      sn F_17f9c D_17f9c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_M_head : forall regs Mi i, (0 <= i < h)%Z ->
    getr regs 5 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 14 = Z_to_bv 64 left -> getr regs 15 = Z_to_bv 64 (wpl * i) -> getr regs 18 = Z_to_bv 64 left -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x1809c : word) Mi rom) (mkst regs' (0x180e4 : word) Mi rom)
      /\ getr regs' 7 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 28 = Z_to_bv 64 (4 * wpl * i)
      /\ getr regs' 29 = Z_to_bv 64 (data + 4 * wpl * i + 0) /\ getr regs' 30 = Z_to_bv 64 (left - 0)
      /\ getr regs' 31 = Z_to_bv 64 (data + 4 * wpl * i + 0)
      /\ regs_agree (fun r : reg => In r [7; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Mi i Hi H5 H9 H10 H14 H15 H18 H19.
    pose proof (wi_bound i ltac:(lia)) as WI. pose proof (line_ok i Hi) as LOK.
    eexists. split.
    - zv F_17fa0 D_17fa0 (Z_to_bv 64 (wpl * i)).            (* [comment removed for export] *)
      mulw_v F_17fa4 D_17fa4 (Z_to_bv 64 (wpl * i)).        (* [comment removed for export] *)
      stepb_ft F_17fa8 D_17fa8 ltac:(condR).                (* [comment removed for export] *)
      zvw F_17fac D_17fac (Z_to_bv 64 (wpl * i)).           (* [comment removed for export] *)
      zvs F_17fb0 D_17fb0 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_17fb4 D_17fb4 (Z_to_bv 64 (data + 4 * wpl * i)). (* [comment removed for export] *)
      seqz0 F_17fb8 D_17fb8.                                (* [comment removed for export] *)
      stepb_ft F_17fbc D_17fbc ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_17fc0 D_17fc0.                                (* [comment removed for export] *)
      slti0 F_17fc4 D_17fc4.                                (* [comment removed for export] *)
      sn F_17fc8 D_17fc8.                                   (* [comment removed for export] *)
      sn F_17fcc D_17fcc.                                   (* [comment removed for export] *)
      stepb_ft F_17fd0 D_17fd0 ltac:(condR).                (* [comment removed for export] *)
      zvs F_17fd4 D_17fd4 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_17fd8 D_17fd8 (Z_to_bv 64 (data + 4 * wpl * i + 0)).   (* [comment removed for export] *)
      zv F_17fdc D_17fdc (Z_to_bv 64 (left - 0)).           (* [comment removed for export] *)
      zv F_17fe0 D_17fe0 (Z_to_bv 64 (data + 4 * wpl * i + 0)).   (* [comment removed for export] *)
      stepb_ft F_17fe4 D_17fe4 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_M_rows : forall (k : nat) regs Mi i,
    (top <= i)%Z -> (i + Z.of_nat k = h - bot - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 5 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 3 ->
    getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl -> getr regs 11 = Z_to_bv 64 (h - bot) ->
    getr regs 13 = Z_to_bv 64 (w - right) -> getr regs 14 = Z_to_bv 64 left -> getr regs 15 = Z_to_bv 64 (wpl * i) ->
    getr regs 16 = Z_to_bv 64 (data + (w - right)) -> getr regs 17 = Z_to_bv 64 (data + (w - right)) ->
    getr regs 18 = Z_to_bv 64 left -> getr regs 19 = Z_to_bv 64 i ->
    exists regs' M',
      msteps SEGS (mkst regs (0x1809c : word) Mi rom) (mkst regs' (0x18174 : word) M' rom)
      /\ Inv M' /\ getr regs' 12 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [7; 12; 15; 19; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv H2 H5 H6 H9 H10 H11 H13 H14 H15 H16 H17 H18 H19.
    all: pose proof (wi_bound i ltac:(lia)) as WI; pose proof (wi_bound (i + 1) ltac:(lia)) as WI1.
    all: pose proof (line_ok i ltac:(lia)) as LOK; pose proof (row_mod4 i) as L4.
    all: destruct (sbv_M_head regs Mi i ltac:(lia) H5 H9 H10 H14 H15 H18 H19) as (r0 & S0 & Z7 & Z28 & Z29 & Z30 & Z31 & AG0).
    all: pose proof (AG0 5 ltac:(notin_list)) as Z5; rewrite H5 in Z5.
    all: pose proof (AG0 6 ltac:(notin_list)) as Z6; rewrite H6 in Z6.
    all: destruct (sbv_ML_bytes (data + 4 * wpl * i) LOK L4 (Z.to_nat (left - 1)) r0 Mi 0 ltac:(lia) ltac:(lia) HIv Z5 Z6 Z7 Z29 Z30 Z31)
           as (r1 & Ma & S1 & HI1 & AG1).
    all: assert (AG01 : regs_agree (fun r : reg => In r [7; 12; 28; 29; 30; 31]%list) regs r1)
           by (eapply regs_agree_trans; [regs_agree_weaken AG0 | regs_agree_weaken AG1]).
    all: pose proof (AG01 2 ltac:(notin_list)) as A2; rewrite H2 in A2.
    all: pose proof (AG01 13 ltac:(notin_list)) as A13; rewrite H13 in A13.
    all: pose proof (AG01 16 ltac:(notin_list)) as A16; rewrite H16 in A16.
    all: pose proof (AG01 17 ltac:(notin_list)) as A17; rewrite H17 in A17.
    all: pose proof (AG1 7 ltac:(notin_list)) as A7; rewrite Z7 in A7.
    all: pose proof (AG1 28 ltac:(notin_list)) as A28; rewrite Z28 in A28.
    (* [comment removed for export] *)
    all: assert (S2 : exists r2, msteps SEGS (mkst r1 (0x18110 : word) Ma rom) (mkst r2 (0x18124 : word) Ma rom)
                   /\ getr r2 28 = Z_to_bv 64 (data + 4 * wpl * i + (w - right)) /\ getr r2 29 = Z_to_bv 64 (data + 4 * wpl * i + (w - right))
                   /\ getr r2 30 = Z_to_bv 64 (w - right)
                   /\ regs_agree (fun r : reg => In r [12; 28; 29; 30]%list) r1 r2).
    1, 3: (eexists; split; [|split; [|split; [|split]]];
      [ ldw F_18014 D_18014 HI1;                            (* [comment removed for export] *)
        stepb_ft F_18018 D_18018 ltac:(condZ);              (* [comment removed for export] *)
        zv F_1801c D_1801c (Z_to_bv 64 (data + 4 * wpl * i + (w - right)));   (* [comment removed for export] *)
        zv F_18020 D_18020 (Z_to_bv 64 (data + 4 * wpl * i + (w - right)));   (* [comment removed for export] *)
        zv F_18024 D_18024 (Z_to_bv 64 (w - right));        (* [comment removed for export] *)
        apply mst_refl
      | gres; pin; reflexivity | gres; pin; reflexivity | gres; pin; reflexivity | solve_regs_agree ]).
    all: destruct S2 as (r2 & S2 & B28 & B29 & B30 & AG2).
    all: pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
    all: pose proof (AG2 5 ltac:(notin_list)) as B5; rewrite (AG01 5 ltac:(notin_list)), H5 in B5.
    all: pose proof (AG2 6 ltac:(notin_list)) as B6; rewrite (AG01 6 ltac:(notin_list)), H6 in B6.
    all: pose proof (AG2 7 ltac:(notin_list)) as B7; rewrite A7 in B7.
    all: destruct (sbv_MR_bytes (data + 4 * wpl * i) LOK L4 (Z.to_nat (right - 1)) r2 Ma (w - right) ltac:(lia) ltac:(lia) HI1 B2 B5 B6 B7 B28 B29 B30)
           as (r3 & Mb & S3 & HI3 & C12 & AG3).
    all: assert (AG03 : regs_agree (fun r : reg => In r [7; 12; 28; 29; 30; 31]%list) regs r3)
           by (eapply regs_agree_trans; [regs_agree_weaken AG01|]; eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
    all: pose proof (AG03 10 ltac:(notin_list)) as C10; rewrite H10 in C10.
    all: pose proof (AG03 11 ltac:(notin_list)) as C11; rewrite H11 in C11.
    all: pose proof (AG03 15 ltac:(notin_list)) as C15; rewrite H15 in C15.
    all: pose proof (AG03 19 ltac:(notin_list)) as C19; rewrite H19 in C19.
    - eexists. exists Mb. split; [|split; [exact HI3 | split]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        zvw F_18064 D_18064 (Z_to_bv 64 (i + 1)).           (* [comment removed for export] *)
        stepb_ft F_18068 D_18068 ltac:(condZ).              (* [comment removed for export] *)
        addw_v F_1806c D_1806c (Z_to_bv 64 (wpl * (i + 1))).   (* [comment removed for export] *)
        zv F_18070 D_18070 (Z_to_bv 64 (i + 1)).            (* [comment removed for export] *)
        stepb_ft F_18074 D_18074 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact C12.
      + eapply regs_agree_trans; [regs_agree_weaken AG03|]. solve_regs_agree.
    - assert (S4 : exists r4, msteps SEGS (mkst r3 (0x18160 : word) Mb rom) (mkst r4 (0x1809c : word) Mb rom)
                   /\ getr r4 15 = Z_to_bv 64 (wpl * (i + 1)) /\ getr r4 19 = Z_to_bv 64 (i + 1)
                   /\ regs_agree (fun r : reg => In r [7; 15; 19]%list) r3 r4).
      { eexists. split; [|split; [|split]].
        - zvw F_18064 D_18064 (Z_to_bv 64 (i + 1)).
          stepb_ft F_18068 D_18068 ltac:(condZ).
          addw_v F_1806c D_1806c (Z_to_bv 64 (wpl * (i + 1))).
          zv F_18070 D_18070 (Z_to_bv 64 (i + 1)).
          stepb_tk F_18074 D_18074 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S4 as (r4 & S4 & D15 & D19 & AG4).
      assert (AG04 : regs_agree (fun r : reg => In r [7; 12; 15; 19; 28; 29; 30; 31]%list) regs r4)
        by (eapply regs_agree_trans; [regs_agree_weaken AG03 | regs_agree_weaken AG4]).
      pose proof (AG04 2 ltac:(notin_list)) as D2; rewrite H2 in D2.
      pose proof (AG04 5 ltac:(notin_list)) as D5; rewrite H5 in D5.
      pose proof (AG04 6 ltac:(notin_list)) as D6; rewrite H6 in D6.
      pose proof (AG04 9 ltac:(notin_list)) as D9; rewrite H9 in D9.
      pose proof (AG04 10 ltac:(notin_list)) as D10; rewrite H10 in D10.
      pose proof (AG04 11 ltac:(notin_list)) as D11; rewrite H11 in D11.
      pose proof (AG04 13 ltac:(notin_list)) as D13; rewrite H13 in D13.
      pose proof (AG04 14 ltac:(notin_list)) as D14; rewrite H14 in D14.
      pose proof (AG04 16 ltac:(notin_list)) as D16; rewrite H16 in D16.
      pose proof (AG04 17 ltac:(notin_list)) as D17; rewrite H17 in D17.
      pose proof (AG04 18 ltac:(notin_list)) as D18; rewrite H18 in D18.
      destruct (IH r4 Mb (i + 1)%Z ltac:(lia) ltac:(lia) HI3 D2 D5 D6 D9 D10 D11 D13 D14 D15 D16 D17 D18 D19) as (r5 & Mc & S5 & HI5 & E12 & AG5).
      exists r5, Mc. split; [|split; [exact HI5 | split; [exact E12|]]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        eapply msteps_trans; [exact S3|]. eapply msteps_trans; [exact S4 | exact S5].
      + eapply regs_agree_trans; [exact AG04 | regs_agree_weaken AG5].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_B_pre : forall regs Mi, Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 11 = Z_to_bv 64 (h - bot) ->
    exists regs',
      msteps SEGS (mkst regs (0x18174 : word) Mi rom) (mkst regs' (0x18188 : word) Mi rom)
      /\ getr regs' 13 = Z_to_bv 64 (wpl * (h - bot)) /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 3
      /\ regs_agree (fun r : reg => In r [13; 14; 15]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2 H9 H10 H11.
    pose proof (wi_bound (h - bot) ltac:(lia)) as WB.
    eexists. split.
    - ldh F_18078 D_18078 HIv.                              (* [comment removed for export] *)
      stepb_ft F_1807c D_1807c ltac:(condZ).                (* [comment removed for export] *)
      mulw_v F_18080 D_18080 (Z_to_bv 64 (wpl * (h - bot))).   (* [comment removed for export] *)
      snez1 F_18084 D_18084.                                (* [comment removed for export] *)
      sn F_18088 D_18088.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_head : forall regs Mi i, (0 <= i < h)%Z ->
    getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 w ->
    getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 14 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x18188 : word) Mi rom) (mkst regs' (0x181d0 : word) Mi rom)
      /\ getr regs' 16 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 17 = Z_to_bv 64 0
      /\ getr regs' 5 = Z_to_bv 64 (data + 4 * wpl * i + 0) /\ getr regs' 6 = Z_to_bv 64 (data + 4 * wpl * i + 0)
      /\ regs_agree (fun r : reg => In r [5; 6; 16; 17]%list) regs regs'.
  Proof.
    intros regs Mi i Hi H9 H10 H11 H12 H13 H14.
    pose proof (wi_bound i ltac:(lia)) as WI. pose proof (line_ok i Hi) as LOK.
    eexists. split.
    - zv F_1808c D_1808c (Z_to_bv 64 (wpl * i)).            (* [comment removed for export] *)
      mulw_v F_18090 D_18090 (Z_to_bv 64 (wpl * i)).        (* [comment removed for export] *)
      stepb_ft F_18094 D_18094 ltac:(condR).                (* [comment removed for export] *)
      zvw F_18098 D_18098 (Z_to_bv 64 (wpl * i)).           (* [comment removed for export] *)
      zvs F_1809c D_1809c (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_180a0 D_180a0 (Z_to_bv 64 (data + 4 * wpl * i)). (* [comment removed for export] *)
      seqz0 F_180a4 D_180a4.                                (* [comment removed for export] *)
      stepb_ft F_180a8 D_180a8 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_180ac D_180ac.                                (* [comment removed for export] *)
      slti0 F_180b0 D_180b0.                                (* [comment removed for export] *)
      sn F_180b4 D_180b4.                                   (* [comment removed for export] *)
      sn F_180b8 D_180b8.                                   (* [comment removed for export] *)
      stepb_ft F_180bc D_180bc ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_180c0 D_180c0 ltac:(condZ).                (* [comment removed for export] *)
      sn F_180c4 D_180c4.                                   (* [comment removed for export] *)
      zvs F_180c8 D_180c8 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_180cc D_180cc (Z_to_bv 64 (data + 4 * wpl * i + 0)).   (* [comment removed for export] *)
      zv F_180d0 D_180d0 (Z_to_bv 64 (data + 4 * wpl * i + 0)).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_rows : forall (k : nat) regs Mi i,
    (0 <= i)%Z -> (i + Z.of_nat k = h - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 (wpl * i) ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 3 ->
    exists regs' M',
      msteps SEGS (mkst regs (0x18188 : word) Mi rom) (mkst regs' (0x183e8 : word) M' rom)
      /\ Inv M'
      /\ regs_agree (fun r : reg => In r [5; 6; 11; 12; 13; 16; 17]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv H2 H9 H10 H11 H12 H13 H14 H15.
    all: pose proof (wi_bound i ltac:(lia)) as WI; pose proof (wi_bound (i + 1) ltac:(lia)) as WI1.
    all: destruct (sbv_B_head regs Mi i ltac:(lia) H9 H10 H11 H12 H13 H14) as (r0 & S0 & Z16 & Z17 & Z5 & Z6 & AG0).
    all: pose proof (AG0 2 ltac:(notin_list)) as Z2; rewrite H2 in Z2.
    all: pose proof (AG0 14 ltac:(notin_list)) as Z14; rewrite H14 in Z14.
    all: pose proof (AG0 15 ltac:(notin_list)) as Z15; rewrite H15 in Z15.
    all: destruct (sbv_B_bytes (data + 4 * wpl * i) (line_ok i ltac:(lia)) (row_mod4 i) (Z.to_nat (w - 1)) r0 Mi 0
                     ltac:(lia) ltac:(lia) HIv Z2 Z14 Z15 Z16 Z17 Z5 Z6) as (r1 & Ma & S1 & HI1 & A12 & AG1).
    all: assert (AG01 : regs_agree (fun r : reg => In r [5; 6; 12; 16; 17]%list) regs r1)
           by (eapply regs_agree_trans; [regs_agree_weaken AG0 | regs_agree_weaken AG1]).
    all: pose proof (AG01 2 ltac:(notin_list)) as A2; rewrite H2 in A2.
    all: pose proof (AG01 10 ltac:(notin_list)) as A10; rewrite H10 in A10.
    all: pose proof (AG01 11 ltac:(notin_list)) as A11; rewrite H11 in A11.
    all: pose proof (AG01 13 ltac:(notin_list)) as A13; rewrite H13 in A13.
    - eexists. exists Ma. split; [|split; [exact HI1|]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|].
        zvw F_18104 D_18104 (Z_to_bv 64 (i + 1)).           (* [comment removed for export] *)
        stepb_ft F_18108 D_18108 ltac:(condZ).              (* [comment removed for export] *)
        ldh F_1810c D_1810c HI1.                            (* [comment removed for export] *)
        addw_v F_18110 D_18110 (Z_to_bv 64 (wpl * (i + 1))).   (* [comment removed for export] *)
        zv F_18114 D_18114 (Z_to_bv 64 (i + 1)).            (* [comment removed for export] *)
        stepb_ft F_18118 D_18118 ltac:(condZ).              (* [comment removed for export] *)
        sn F_1811c D_1811c.                                 (* [comment removed for export] *)
        apply mst_refl.
      + eapply regs_agree_trans; [regs_agree_weaken AG01|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x18200 : word) Ma rom) (mkst r2 (0x18188 : word) Ma rom)
                   /\ getr r2 11 = Z_to_bv 64 (i + 1) /\ getr r2 13 = Z_to_bv 64 (wpl * (i + 1))
                   /\ regs_agree (fun r : reg => In r [11; 13; 16; 17]%list) r1 r2).
      { eexists. split; [|split; [|split]].
        - zvw F_18104 D_18104 (Z_to_bv 64 (i + 1)).
          stepb_ft F_18108 D_18108 ltac:(condZ).
          ldh F_1810c D_1810c HI1.
          addw_v F_18110 D_18110 (Z_to_bv 64 (wpl * (i + 1))).
          zv F_18114 D_18114 (Z_to_bv 64 (i + 1)).
          stepb_tk F_18118 D_18118 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & B11 & B13 & AG2).
      assert (AG02 : regs_agree (fun r : reg => In r [5; 6; 11; 12; 13; 16; 17]%list) regs r2)
        by (eapply regs_agree_trans; [regs_agree_weaken AG01 | regs_agree_weaken AG2]).
      pose proof (AG02 2 ltac:(notin_list)) as B2; rewrite H2 in B2.
      pose proof (AG02 9 ltac:(notin_list)) as B9; rewrite H9 in B9.
      pose proof (AG02 10 ltac:(notin_list)) as B10; rewrite H10 in B10.
      pose proof (AG2 12 ltac:(notin_list)) as B12; rewrite A12 in B12.
      pose proof (AG02 14 ltac:(notin_list)) as B14; rewrite H14 in B14.
      pose proof (AG02 15 ltac:(notin_list)) as B15; rewrite H15 in B15.
      destruct (IH r2 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 B2 B9 B10 B11 B12 B13 B14 B15) as (r3 & Mb & S3 & HI3 & AG3).
      exists r3, Mb. split; [|split; [exact HI3|]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [exact AG02 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_ra : rdn SEGS M2 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 ra).   Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s0 : rdn SEGS M2 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 s0v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s1 : rdn SEGS M2 (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 s1v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s2 : rdn SEGS M2 (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 s2v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s3 : rdn SEGS M2 (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 s3v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s4 : rdn SEGS M2 (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 s4v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s5 : rdn SEGS M2 (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 s5v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s6 : rdn SEGS M2 (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 s6v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s7 : rdn SEGS M2 (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 s7v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s8 : rdn SEGS M2 (Z_to_bv 64 (sp - 80)) 8 = Some (word_to_le_bytes 8 s8v). Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_s9 : rdn SEGS M2 (Z_to_bv 64 (sp - 88)) 8 = Some (word_to_le_bytes 8 s9v). Proof. unfold M2, M1. rdn_chain. Qed.

  Ltac ldsv F D k v FL HIv :=
    stepLD F D (word_to_le_bytes 8 v) v
      ltac:(rdn_addr (sp - k)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact FL])
      ltac:(apply bytes_le_to_Z_8).

  (* [comment removed for export] *)
  Lemma sbv_E : forall regs Mi, Inv Mi -> getr regs 2 = Z_to_bv 64 (sp - 112) ->
    exists regs',
      msteps SEGS (mkst regs (0x183e8 : word) Mi rom) (mkst regs' ra Mi rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2.
    eexists. split.
    - sn F_182ec D_182ec.                                   (* [comment removed for export] *)
      ldsv F_182f0 D_182f0 8%Z ra F_ra HIv.
      ldsv F_182f4 D_182f4 16%Z s0v F_s0 HIv.
      ldsv F_182f8 D_182f8 24%Z s1v F_s1 HIv.
      ldsv F_182fc D_182fc 32%Z s2v F_s2 HIv.
      ldsv F_18300 D_18300 40%Z s3v F_s3 HIv.
      ldsv F_18304 D_18304 48%Z s4v F_s4 HIv.
      ldsv F_18308 D_18308 56%Z s5v F_s5 HIv.
      ldsv F_1830c D_1830c 64%Z s6v F_s6 HIv.
      ldsv F_18310 D_18310 72%Z s7v F_s7 HIv.
      ldsv F_18314 D_18314 80%Z s8v F_s8 HIv.
      ldsv F_18318 D_18318 88%Z s9v F_s9 HIv.
      zv F_1831c D_1831c (Z_to_bv 64 sp).                   (* [comment removed for export] *)
      stepret F_18320 D_18320 ra ltac:(reflexivity).        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma M2_outside : forall x : word, (bv_unsigned x < sp - 112 \/ sp <= bv_unsigned x)%Z -> M2 x = M x.
  Proof.
    intros x Hx. unfold M2, M1.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem sbv_run : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v ->
    getr regs 21 = s5v -> getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v -> getr regs 25 = s9v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
    getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17afc : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H10 H11 H12 H13 H14 H15.
    destruct (sbv_A regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H10 H11 H12 H13 H14 H15)
      as (r1 & S1 & A2 & A9 & A18 & A19 & A20 & A21 & A23 & A24 & A10 & AG1).
    destruct (sbv_T_pre r1 M2 A9 A19) as (r2 & S2 & B11 & B13 & B14 & B15 & AG2).
    pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
    pose proof (AG2 9 ltac:(notin_list)) as B9; rewrite A9 in B9.
    pose proof (AG2 10 ltac:(notin_list)) as B10; rewrite A10 in B10.
    pose proof (AG2 19 ltac:(notin_list)) as B19; rewrite A19 in B19.
    destruct (sbv_T_rows (Z.to_nat (top - 1)) r2 M2 0 ltac:(lia) ltac:(lia) Inv_M2 B2 B9 B10 B11 B13 B14 B15 B19) as (r3 & M3 & S3 & HI3 & C12 & AG3).
    assert (AG23 : regs_agree (fun r : reg => In r [5; 6; 11; 12; 13; 14; 15; 16; 17]%list) r1 r3)
      by (eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
    pose proof (AG23 2 ltac:(notin_list)) as C2; rewrite A2 in C2.
    pose proof (AG23 9 ltac:(notin_list)) as C9; rewrite A9 in C9.
    pose proof (AG23 10 ltac:(notin_list)) as C10; rewrite A10 in C10.
    pose proof (AG23 18 ltac:(notin_list)) as C18; rewrite A18 in C18.
    pose proof (AG23 19 ltac:(notin_list)) as C19; rewrite A19 in C19.
    pose proof (AG23 20 ltac:(notin_list)) as C20; rewrite A20 in C20.
    pose proof (AG23 21 ltac:(notin_list)) as C21; rewrite A21 in C21.
    pose proof (AG23 23 ltac:(notin_list)) as C23; rewrite A23 in C23.
    pose proof (AG23 24 ltac:(notin_list)) as C24; rewrite A24 in C24.
    destruct (sbv_M_pre r3 M3 HI3 C2 C9 C10 C12 C18 C19 C20 C21 C23 C24) as (r4 & S4 & D11 & D13 & D14 & D15 & D16 & D17 & D5 & D6 & AG4).
    pose proof (AG4 2 ltac:(notin_list)) as D2; rewrite C2 in D2.
    pose proof (AG4 9 ltac:(notin_list)) as D9; rewrite C9 in D9.
    pose proof (AG4 10 ltac:(notin_list)) as D10; rewrite C10 in D10.
    pose proof (AG4 18 ltac:(notin_list)) as D18; rewrite C18 in D18.
    pose proof (AG4 19 ltac:(notin_list)) as D19; rewrite C19 in D19.
    destruct (sbv_M_rows (Z.to_nat (h - bot - top - 1)) r4 M3 top ltac:(lia) ltac:(lia) HI3 D2 D5 D6 D9 D10 D11 D13 D14 D15 D16 D17 D18 D19)
      as (r5 & M5 & S5 & HI5 & E12 & AG5).
    pose proof (AG5 2 ltac:(notin_list)) as E2; rewrite D2 in E2.
    pose proof (AG5 9 ltac:(notin_list)) as E9; rewrite D9 in E9.
    pose proof (AG5 10 ltac:(notin_list)) as E10; rewrite D10 in E10.
    pose proof (AG5 11 ltac:(notin_list)) as E11; rewrite D11 in E11.
    destruct (sbv_B_pre r5 M5 HI5 E2 E9 E10 E11) as (r6 & S6 & G13 & G14 & G15 & AG6).
    pose proof (AG6 2 ltac:(notin_list)) as G2; rewrite E2 in G2.
    pose proof (AG6 9 ltac:(notin_list)) as G9; rewrite E9 in G9.
    pose proof (AG6 10 ltac:(notin_list)) as G10; rewrite E10 in G10.
    pose proof (AG6 11 ltac:(notin_list)) as G11; rewrite E11 in G11.
    pose proof (AG6 12 ltac:(notin_list)) as G12; rewrite E12 in G12.
    destruct (sbv_B_rows (Z.to_nat (bot - 1)) r6 M5 (h - bot) ltac:(lia) ltac:(lia) HI5 G2 G9 G10 G11 G12 G13 G14 G15) as (r7 & M7 & S7 & HI7 & AG7).
    pose proof (AG7 2 ltac:(notin_list)) as J2; rewrite G2 in J2.
    destruct (sbv_E r7 M7 HI7 J2) as (r8 & S8 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & AG8).
    exists r8, M7. split.
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
      eapply msteps_trans; [exact S4|]. eapply msteps_trans; [exact S5|]. eapply msteps_trans; [exact S6|].
      eapply msteps_trans; [exact S7 | exact S8].
    - split; [exact HI7|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG23|].
      eapply regs_agree_trans; [regs_agree_weaken AG4|]. eapply regs_agree_trans; [regs_agree_weaken AG5|].
      eapply regs_agree_trans; [regs_agree_weaken AG6|]. eapply regs_agree_trans; [regs_agree_weaken AG7 | regs_agree_weaken AG8].
  Qed.

End SBV.
