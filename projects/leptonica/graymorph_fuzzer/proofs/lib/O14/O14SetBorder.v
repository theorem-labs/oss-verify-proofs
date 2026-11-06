(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 GrayLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14_code_gmD.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.

Section SBV.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables pix w h wpl data sp : Z.
  Variables left right top bot val : Z.
  Variables ra s0v s1v s2v s3v s4v s5v s6v s7v s8v : word.     (* [comment removed for export] *)

  Hypothesis Hpix : (1 <= pix /\ pix + 64 <= 2 ^ 64)%Z.
  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hwpl : (w <= 4 * wpl /\ wpl <= 20000)%Z.
  Hypothesis Hsp : (96 <= sp /\ sp < 2 ^ 64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis Hl : (1 <= left < w)%Z.
  Hypothesis Hr : (1 <= right < w)%Z.
  Hypothesis Ht : (1 <= top)%Z.
  Hypothesis Hb : (1 <= bot)%Z.
  Hypothesis Htb : (top + bot < h)%Z.
  Hypothesis Hval : (0 <= val < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 8).
  Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
  Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
  #[local] Abbreviation RS := (4 * (wpl * h))%Z (only parsing).
  Hypothesis Hdata : (1 <= data /\ data + RS <= 2 ^ 64 /\ data mod 4 = 0)%Z.
  Hypothesis SOKr : store_ok SEGS M (Z_to_bv 64 data) (Z.to_nat RS) = true.
  Hypothesis FR : disj_apart data RS (sp - 96) 96.
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 96)) 96 = true.
  Hypothesis FP : disj_apart pix 64 (sp - 96) 96.

  (* [comment removed for export] *)
  Definition M1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 s5v))
      (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 s6v))
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 8 s7v))
      (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 s8v).
  (* [comment removed for export] *)
  Definition M2 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (sp - 84)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 92)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 84)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (sp - 92)) (word_to_le_bytes 4 (Z_to_bv 64 8)).

  Lemma sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 96)%Z ->
    store_ok SEGS m (Z_to_bv 64 (sp - k)) n = true.
  Proof.
    intros m k n Hg Hk. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - 96)) _ 96%nat); [ | exact SOKf | | ];
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

  Ltac stf F D k v := stepST F D (Z_to_bv 64 (sp - k)) v ltac:(sokf).
  Ltac ldpix F D z C :=
    stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z)
      ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelf; exact C)
      ltac:(apply lez4; lia);
    rewrite ?(v_lw_small z) by lia.
  (* [comment removed for export] *)
  Ltac ldf F D k z :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
      ltac:(unfold M2, M1; rdn_addr (sp - k)%Z; rdn_chain)
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite ?(v_lw_small z) by lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_A : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v ->
    getr regs 21 = s5v -> getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
    getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x17344 : word) M rom) (mkst regs' (0x175d8 : word) M2 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 96) /\ getr regs' 8 = Z_to_bv 64 val /\ getr regs' 9 = Z_to_bv 64 left
      /\ getr regs' 18 = Z_to_bv 64 data /\ getr regs' 19 = Z_to_bv 64 right /\ getr regs' 20 = Z_to_bv 64 bot
      /\ getr regs' 21 = Z_to_bv 64 top /\ getr regs' 23 = Z_to_bv 64 h /\ getr regs' 24 = Z_to_bv 64 top
      /\ getr regs' 10 = Z_to_bv 64 wpl /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H10 H11 H12 H13 H14 H15. use_apart FP.
    eexists. split.
    - zv F_17248 D_17248 (Z_to_bv 64 (sp - 96)).           (* [comment removed for export] *)
      stf F_1724c D_1724c 8%Z ra.
      stf F_17250 D_17250 16%Z s0v.
      stf F_17254 D_17254 24%Z s1v.
      stf F_17258 D_17258 32%Z s2v.
      stf F_1725c D_1725c 40%Z s3v.
      stf F_17260 D_17260 48%Z s4v.
      stf F_17264 D_17264 56%Z s5v.
      stf F_17268 D_17268 64%Z s6v.
      stf F_1726c D_1726c 72%Z s7v.
      stf F_17270 D_17270 80%Z s8v.
      fold M1.
      stepb_ft F_17274 D_17274 ltac:(condZ).                (* [comment removed for export] *)
      zv F_17278 D_17278 (Z_to_bv 64 val).                  (* [comment removed for export] *)
      zv F_1727c D_1727c (Z_to_bv 64 bot).                  (* [comment removed for export] *)
      zv F_17280 D_17280 (Z_to_bv 64 top).                  (* [comment removed for export] *)
      zv F_17284 D_17284 (Z_to_bv 64 right).                (* [comment removed for export] *)
      zv F_17288 D_17288 (Z_to_bv 64 left).                 (* [comment removed for export] *)
      zv F_1728c D_1728c (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      zv F_17290 D_17290 (Z_to_bv 64 (sp - 84)).            (* [comment removed for export] *)
      zv F_17294 D_17294 (Z_to_bv 64 (sp - 88)).            (* [comment removed for export] *)
      zv F_17298 D_17298 (Z_to_bv 64 (sp - 92)).            (* [comment removed for export] *)
      sn F_1729c D_1729c.                                   (* [comment removed for export] *)
      stepb_ft F_15d38 D_15d38 ltac:(condZ).
      stf F_15d3c D_15d3c 84%Z (Z_to_bv 64 0).
      stepb_ft F_15d40 D_15d40 ltac:(condZ).
      stf F_15d44 D_15d44 88%Z (Z_to_bv 64 0).
      stepb_ft F_15d48 D_15d48 ltac:(condZ).
      stf F_15d4c D_15d4c 92%Z (Z_to_bv 64 0).
      stepb_ft F_15d50 D_15d50 ltac:(condZ).
      stepb_ft F_15d54 D_15d54 ltac:(condZ).
      ldpix F_15d58 D_15d58 w Cw.
      stf F_15d5c D_15d5c 84%Z (Z_to_bv 64 w).
      stepb_ft F_15d60 D_15d60 ltac:(condZ).
      ldpix F_15d64 D_15d64 h Ch.
      stf F_15d68 D_15d68 88%Z (Z_to_bv 64 h).
      sn F_15d6c D_15d6c.
      stepb_ft F_15d70 D_15d70 ltac:(condZ).
      ldpix F_15d74 D_15d74 8%Z Cd.
      stf F_15d78 D_15d78 92%Z (Z_to_bv 64 8).
      sn F_15d7c D_15d7c.
      stepret F_15d80 D_15d80 (0x1739c : word) ltac:(bveq).
      fold M2.
      (* [comment removed for export] *)
      ldf F_172a0 D_172a0 92%Z 8%Z.                         (* [comment removed for export] *)
      sn F_172a4 D_172a4.                                   (* [comment removed for export] *)
      stepb_ft F_172a8 D_172a8 ltac:(condZ).                (* [comment removed for export] *)
      sn F_172ac D_172ac.                                   (* [comment removed for export] *)
      sn F_172b0 D_172b0.                                   (* [comment removed for export] *)
      sn F_172b4 D_172b4.                                   (* [comment removed for export] *)
      sn F_172b8 D_172b8.                                   (* [comment removed for export] *)
      sn F_172bc D_172bc. fixv (Z_to_bv 64 1) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_172c0 D_172c0 ltac:(condZ).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      ldf F_172c4 D_172c4 88%Z h.                           (* [comment removed for export] *)
      zv F_172c8 D_172c8 (Z_to_bv 64 top).                  (* [comment removed for export] *)
      stepb_tk F_172cc D_172cc ltac:(condZ).                (* [comment removed for export] *)
      stepb_tk F_172ec D_172ec ltac:(condZ).                (* [comment removed for export] *)
      ldf F_172d8 D_172d8 84%Z w.                           (* [comment removed for export] *)
      stepb_tk F_172dc D_172dc ltac:(condZ).                (* [comment removed for export] *)
      stepb_tk F_172fc D_172fc ltac:(condZ).                (* [comment removed for export] *)
      zv F_17304 D_17304 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_17308 D_17308.                                   (* [comment removed for export] *)
      stepb_ft F_16874 D_16874 ltac:(condZ).
      stepLD F_16878 D_16878 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelf; exact Cdata)
        ltac:(apply lez8; lia).
      stepret F_1687c D_1687c (0x17408 : word) ltac:(bveq).
      zv F_1730c D_1730c (Z_to_bv 64 data).                 (* [comment removed for export] *)
      zv F_17310 D_17310 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_17314 D_17314.                                   (* [comment removed for export] *)
      stepb_ft F_15a3c D_15a3c ltac:(condZ).
      ldpix F_15a40 D_15a40 wpl Cwpl.
      stepret F_15a44 D_15a44 (0x17414 : word) ltac:(bveq).
      ldf F_17318 D_17318 92%Z 8%Z.                         (* [comment removed for export] *)
      ldf F_1731c D_1731c 84%Z w.                           (* [comment removed for export] *)
      sn F_17320 D_17320.                                   (* [comment removed for export] *)
      sn F_17324 D_17324. fixv (Z_to_bv 64 w) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).   (* [comment removed for export] *)
      stepb_tk F_17328 D_17328 ltac:(condZ).                (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma Inv_rdn_frame : forall Mi (a : Z) (n : nat) bs, Inv Mi -> (sp - 96 <= a)%Z -> (a + Z.of_nat n <= sp)%Z ->
    rdn SEGS M2 (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros Mi a n bs [HI _] Ha Hn HM. use_apart FR. rewrite <- HM.
    assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_Z2bv; lia).
    apply rdn_ext; rewrite U; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  Lemma F_w : rdn SEGS M2 (Z_to_bv 64 (sp - 84)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)).
  Proof. unfold M2, M1. rdn_chain. Qed.
  Lemma F_h : rdn SEGS M2 (Z_to_bv 64 (sp - 88)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).
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

  (* [comment removed for export] *)
  Ltac ldw F D HIv :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w)
      ltac:(rdn_addr (sp - 84)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact F_w])
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite ?(v_lw_small w) by lia.
  Ltac ldh F D HIv :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h)
      ltac:(rdn_addr (sp - 88)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact F_h])
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite ?(v_lw_small h) by lia.
  (* [comment removed for export] *)
  Ltac gsb F D aa HIv :=
    chain_step;
    [ reflexivity
    | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 aa);
      [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | reflexivity
      | apply (Inv_sok _ aa 1 HIv); [lia | cbn; lia] ]
    | step_simpl ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_T_byte : forall regs Mi i j,
    (0 <= i < h)%Z -> (0 <= j < w)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) ->
    getr regs 15 = Z_to_bv 64 j -> getr regs 16 = Z_to_bv 64 (data + 4 * wpl * i + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17604 : word) Mi rom) (mkst regs' (0x17618 : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w /\ getr regs' 15 = Z_to_bv 64 (j + 1)
      /\ getr regs' 16 = Z_to_bv 64 (data + 4 * wpl * i + (j + 1))
      /\ regs_agree (fun r : reg => In r [11; 15; 16]%list) regs regs'.
  Proof.
    intros regs Mi i j Hi Hj HIv H2 H15 H16.
    pose proof (row_bound i Hi) as RB. pose proof (xo_bound j wpl ltac:(lia)) as XB. pose proof (row_mod4 i) as R4.
    assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (data + 4 * wpl * i + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))])).
    { apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]. }
    eexists. eexists. split; [|split; [exact HI'|]].
    - stepiv F_17508 D_17508 (Z_to_bv 64 (data + 4 * wpl * i + xo j))
        ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact R4 | lia | lia]).     (* [comment removed for export] *)
      gsb F_1750c D_1750c (data + 4 * wpl * i + xo j)%Z HIv.                          (* [comment removed for export] *)
      ldw F_17510 D_17510 HI'.                                                        (* [comment removed for export] *)
      zv F_17514 D_17514 (Z_to_bv 64 (j + 1)).                                        (* [comment removed for export] *)
      zv F_17518 D_17518 (Z_to_bv 64 (data + 4 * wpl * i + (j + 1))).                 (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_T_bytes : forall (k : nat) regs Mi i j,
    (0 <= i < h)%Z -> (0 <= j)%Z -> (j + Z.of_nat k = w - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) ->
    getr regs 15 = Z_to_bv 64 j -> getr regs 16 = Z_to_bv 64 (data + 4 * wpl * i + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17604 : word) Mi rom) (mkst regs' (0x175ec : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [11; 15; 16]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i j Hi Hj Hk HIv H2 H15 H16;
      destruct (sbv_T_byte regs Mi i j Hi ltac:(lia) HIv H2 H15 H16) as (r1 & Ma & S1 & HI1 & A11 & A15 & A16 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact A11 | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_1751c D_1751c ltac:(condZ).                (* [comment removed for export] *)
      sn F_17520 D_17520.                                   (* [comment removed for export] *)
      apply mst_refl.
    - pose proof (AG1 2 ltac:(notin_list)) as A2. rewrite H2 in A2.
      destruct (IH r1 Ma i (j + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 A2 A15 A16) as (r2 & Mb & S2 & HI2 & B11 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B11|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_1751c D_1751c ltac:(condZ).
        exact S2.
      + eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_T_rows : forall (k : nat) regs Mi i,
    (0 <= i)%Z -> (i + Z.of_nat k = top - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 11 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 i ->
    getr regs 13 = Z_to_bv 64 (4 * wpl) -> getr regs 14 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 24 = Z_to_bv 64 top ->
    exists regs' M',
      msteps SEGS (mkst regs (0x175f8 : word) Mi rom) (mkst regs' (0x17620 : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [11; 12; 14; 15; 16]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv H2 H11 H12 H13 H14 H24.
    all: assert (S0 : exists r0, msteps SEGS (mkst regs (0x175f8 : word) Mi rom) (mkst r0 (0x17604 : word) Mi rom)
                   /\ getr r0 15 = Z_to_bv 64 0 /\ getr r0 16 = Z_to_bv 64 (data + 4 * wpl * i + 0)
                   /\ regs_agree (fun r : reg => In r [15; 16]%list) regs r0).
    1, 3: (eexists; split; [|split; [|split]];
      [ stepb_ft F_174fc D_174fc ltac:(condZ);              (* [comment removed for export] *)
        sn F_17500 D_17500;                                 (* [comment removed for export] *)
        zv F_17504 D_17504 (Z_to_bv 64 (data + 4 * wpl * i + 0));   (* [comment removed for export] *)
        apply mst_refl
      | gres; pin; reflexivity | gres; pin; reflexivity | solve_regs_agree ]).
    all: destruct S0 as (r0 & S0 & Z15 & Z16 & AG0).
    all: pose proof (AG0 2 ltac:(notin_list)) as Z2; rewrite H2 in Z2.
    all: destruct (sbv_T_bytes (Z.to_nat (w - 1)) r0 Mi i 0 ltac:(lia) ltac:(lia) ltac:(lia) HIv Z2 Z15 Z16) as (r1 & Ma & S1 & HI1 & A11 & AG1).
    all: pose proof (AG1 12 ltac:(notin_list)) as A12; rewrite (AG0 12 ltac:(notin_list)), H12 in A12.
    all: pose proof (AG1 13 ltac:(notin_list)) as A13; rewrite (AG0 13 ltac:(notin_list)), H13 in A13.
    all: pose proof (AG1 14 ltac:(notin_list)) as A14; rewrite (AG0 14 ltac:(notin_list)), H14 in A14.
    all: pose proof (AG1 24 ltac:(notin_list)) as A24; rewrite (AG0 24 ltac:(notin_list)), H24 in A24.
    all: pose proof (AG1 2 ltac:(notin_list)) as A2; rewrite Z2 in A2.
    - eexists. exists Ma. split; [|split; [exact HI1 | split]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|].
        zv F_174f0 D_174f0 (Z_to_bv 64 (i + 1)).            (* [comment removed for export] *)
        zv F_174f4 D_174f4 (Z_to_bv 64 (data + 4 * wpl * (i + 1))).   (* [comment removed for export] *)
        stepb_tk F_174f8 D_174f8 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact A11.
      + eapply regs_agree_trans; [regs_agree_weaken AG0|]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x175ec : word) Ma rom) (mkst r2 (0x175f8 : word) Ma rom)
                   /\ getr r2 12 = Z_to_bv 64 (i + 1) /\ getr r2 14 = Z_to_bv 64 (data + 4 * wpl * (i + 1))
                   /\ regs_agree (fun r : reg => In r [12; 14]%list) r1 r2).
      { eexists. split; [|split; [|split]].
        - zv F_174f0 D_174f0 (Z_to_bv 64 (i + 1)).
          zv F_174f4 D_174f4 (Z_to_bv 64 (data + 4 * wpl * (i + 1))).
          stepb_ft F_174f8 D_174f8 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & B12 & B14 & AG2).
      pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
      pose proof (AG2 11 ltac:(notin_list)) as B11; rewrite A11 in B11.
      pose proof (AG2 13 ltac:(notin_list)) as B13; rewrite A13 in B13.
      pose proof (AG2 24 ltac:(notin_list)) as B24; rewrite A24 in B24.
      destruct (IH r2 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 B2 B11 B12 B13 B14 B24) as (r3 & Mb & S3 & HI3 & C11 & AG3).
      exists r3, Mb. split; [|split; [exact HI3 | split; [exact C11|]]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG0|]. eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section LINE.
  Variable L : Z.
  Hypothesis HL : (data <= L /\ L + 4 * wpl <= data + RS)%Z.
  Hypothesis HL4 : (L mod 4 = 0)%Z.

  (* [comment removed for export] *)
  Lemma sbv_ML_bytes : forall (k : nat) regs Mi j,
    (0 <= j)%Z -> (j + Z.of_nat k = left - 1)%Z -> Inv Mi ->
    getr regs 5 = Z_to_bv 64 (L + j) -> getr regs 11 = Z_to_bv 64 (L + left) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x1767c : word) Mi rom) (mkst regs' (0x1768c : word) M' rom)
      /\ Inv M' /\ regs_agree (fun r : reg => In r [5; 6]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi j Hj Hk HIv H5 H11.
    all: pose proof (xo_bound j wpl ltac:(lia)) as XB.
    all: assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]))
           by (apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]).
    - eexists. eexists. split; [|split; [exact HI'|]].
      + stepiv F_17580 D_17580 (Z_to_bv 64 (L + xo j))
          ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).   (* [comment removed for export] *)
        zv F_17584 D_17584 (Z_to_bv 64 (L + (j + 1))).                                 (* [comment removed for export] *)
        gsb F_17588 D_17588 (L + xo j)%Z HIv.                                          (* [comment removed for export] *)
        stepb_ft F_1758c D_1758c ltac:(condZ).                                        (* [comment removed for export] *)
        apply mst_refl.
      + solve_regs_agree.
    - assert (S1 : exists r1, msteps SEGS (mkst regs (0x1767c : word) Mi rom)
                     (mkst r1 (0x1767c : word) (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]) rom)
                   /\ getr r1 5 = Z_to_bv 64 (L + (j + 1)) /\ regs_agree (fun r : reg => In r [5; 6]%list) regs r1).
      { eexists. split; [|split].
        - stepiv F_17580 D_17580 (Z_to_bv 64 (L + xo j))
            ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).
          zv F_17584 D_17584 (Z_to_bv 64 (L + (j + 1))).
          gsb F_17588 D_17588 (L + xo j)%Z HIv.
          stepb_tk F_1758c D_1758c ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & A5 & AG1).
      pose proof (AG1 11 ltac:(notin_list)) as A11; rewrite H11 in A11.
      destruct (IH r1 _ (j + 1)%Z ltac:(lia) ltac:(lia) HI' A5 A11) as (r2 & Mb & S2 & HI2 & AG2).
      exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2]|]. split; [exact HI2|].
      eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_MR_bytes : forall (k : nat) regs Mi j,
    (0 <= j)%Z -> (j + Z.of_nat k = w - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 5 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 L ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17698 : word) Mi rom) (mkst regs' (0x176b0 : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [5; 11]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi j Hj Hk HIv H2 H5 H15.
    all: pose proof (xo_bound j wpl ltac:(lia)) as XB.
    all: assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]))
           by (apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]).
    - eexists. eexists. split; [|split; [exact HI'|split]].
      + zv F_1759c D_1759c (Z_to_bv 64 (L + j)).                                       (* [comment removed for export] *)
        stepiv F_175a0 D_175a0 (Z_to_bv 64 (L + xo j))
          ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).   (* [comment removed for export] *)
        gsb F_175a4 D_175a4 (L + xo j)%Z HIv.                                          (* [comment removed for export] *)
        ldw F_175a8 D_175a8 HI'.                                                       (* [comment removed for export] *)
        zv F_175ac D_175ac (Z_to_bv 64 (j + 1)).                                       (* [comment removed for export] *)
        stepb_ft F_175b0 D_175b0 ltac:(condZ).                                        (* [comment removed for export] *)
        apply mst_refl.
      + gres; pin; reflexivity.
      + solve_regs_agree.
    - assert (S1 : exists r1, msteps SEGS (mkst regs (0x17698 : word) Mi rom)
                     (mkst r1 (0x17698 : word) (wbytes Mi (Z_to_bv 64 (L + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))]) rom)
                   /\ getr r1 5 = Z_to_bv 64 (j + 1) /\ regs_agree (fun r : reg => In r [5; 11]%list) regs r1).
      { eexists. split; [|split].
        - zv F_1759c D_1759c (Z_to_bv 64 (L + j)).
          stepiv F_175a0 D_175a0 (Z_to_bv 64 (L + xo j))
            ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact HL4 | lia | lia]).
          gsb F_175a4 D_175a4 (L + xo j)%Z HIv.
          ldw F_175a8 D_175a8 HI'.
          zv F_175ac D_175ac (Z_to_bv 64 (j + 1)).
          stepb_tk F_175b0 D_175b0 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & A5 & AG1).
      pose proof (AG1 2 ltac:(notin_list)) as A2; rewrite H2 in A2.
      pose proof (AG1 15 ltac:(notin_list)) as A15; rewrite H15 in A15.
      destruct (IH r1 _ (j + 1)%Z ltac:(lia) ltac:(lia) HI' A2 A5 A15) as (r2 & Mb & S2 & HI2 & B11 & AG2).
      exists r2, Mb. split; [eapply msteps_trans; [exact S1 | exact S2]|]. split; [exact HI2|]. split; [exact B11|].
      eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.
  End LINE.

  Lemma line_ok : forall i, (0 <= i < h)%Z -> (data <= data + 4 * wpl * i /\ data + 4 * wpl * i + 4 * wpl <= data + RS)%Z.
  Proof. intros i Hi. pose proof (row_bound i Hi). assert (0 <= wpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia). lia. Qed.

  (* [comment removed for export] *)
  Lemma sbv_M_pre : forall regs Mi, Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 9 = Z_to_bv 64 left -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 11 = Z_to_bv 64 w -> getr regs 18 = Z_to_bv 64 data -> getr regs 19 = Z_to_bv 64 right ->
    getr regs 20 = Z_to_bv 64 bot -> getr regs 21 = Z_to_bv 64 top -> getr regs 23 = Z_to_bv 64 h -> getr regs 24 = Z_to_bv 64 top ->
    exists regs',
      msteps SEGS (mkst regs (0x17620 : word) Mi rom) (mkst regs' (0x1766c : word) Mi rom)
      /\ getr regs' 12 = Z_to_bv 64 (h - bot) /\ getr regs' 13 = Z_to_bv 64 (w - right) /\ getr regs' 14 = Z_to_bv 64 0
      /\ getr regs' 15 = Z_to_bv 64 (data + 4 * wpl * (top + 0)) /\ getr regs' 16 = Z_to_bv 64 (4 * wpl)
      /\ getr regs' 17 = Z_to_bv 64 (data + 4 * wpl * top + left) /\ getr regs' 23 = Z_to_bv 64 (top + 0)
      /\ regs_agree (fun r : reg => In r [12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2 H9 H10 H11 H18 H19 H20 H21 H23 H24.
    assert (Htw : (0 <= top * wpl <= 20000 * 20000)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
    eexists. split.
    - ldh F_17524 D_17524 HIv.                              (* [comment removed for export] *)
      sn F_17528 D_17528. fixv (Z_to_bv 64 (h - bot)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).    (* [comment removed for export] *)
      stepb_ft F_1752c D_1752c ltac:(condZ).                (* [comment removed for export] *)
      sn F_17530 D_17530. fixv (Z_to_bv 64 (w - right)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_17534 D_17534 ltac:(condZ).                (* [comment removed for export] *)
      zv F_17538 D_17538 (Z_to_bv 64 (top + 0)).            (* [comment removed for export] *)
      sn F_1753c D_1753c.                                   (* [comment removed for export] *)
      stepiv F_17540 D_17540 (Z_to_bv 64 (left * 2 ^ 32))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).             (* [comment removed for export] *)
      zv F_17544 D_17544 (Z_to_bv 64 (top * wpl)).          (* [comment removed for export] *)
      stepiv F_17548 D_17548 (Z_to_bv 64 left)
        ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; f_equal; apply Z.div_mul; lia).   (* [comment removed for export] *)
      stepiv F_1754c D_1754c (Z_to_bv 64 (4 * (top * wpl)))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).   (* [comment removed for export] *)
      zv F_17550 D_17550 (Z_to_bv 64 (data + 4 * wpl * (top + 0))).      (* [comment removed for export] *)
      stepiv F_17554 D_17554 (Z_to_bv 64 (4 * wpl))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).   (* [comment removed for export] *)
      zv F_17558 D_17558 (Z_to_bv 64 (data + 4 * wpl * top + left)).     (* [comment removed for export] *)
      sn F_1755c D_1755c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_M_rows : forall (k : nat) regs Mi kk,
    (0 <= kk)%Z -> (top + kk + Z.of_nat k = h - bot - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 9 = Z_to_bv 64 left ->
    getr regs 12 = Z_to_bv 64 (h - bot) -> getr regs 13 = Z_to_bv 64 (w - right) -> getr regs 14 = Z_to_bv 64 kk ->
    getr regs 15 = Z_to_bv 64 (data + 4 * wpl * (top + kk)) -> getr regs 16 = Z_to_bv 64 (4 * wpl) ->
    getr regs 17 = Z_to_bv 64 (data + 4 * wpl * top + left) -> getr regs 23 = Z_to_bv 64 (top + kk) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x1766c : word) Mi rom) (mkst regs' (0x177d0 : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [5; 6; 11; 14; 15; 23]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi kk Hkk Hk HIv H2 H9 H12 H13 H14 H15 H16 H17 H23.
    all: pose proof (line_ok (top + kk) ltac:(lia)) as LOK; pose proof (row_mod4 (top + kk)) as L4.
    all: assert (Hwk : (0 <= wpl * kk <= 20000 * 20000)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
    all: assert (Hwt : (0 <= wpl * top <= 20000 * 20000)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
    (* [comment removed for export] *)
    all: assert (S0 : exists r0, msteps SEGS (mkst regs (0x1766c : word) Mi rom) (mkst r0 (0x1767c : word) Mi rom)
                   /\ getr r0 5 = Z_to_bv 64 (data + 4 * wpl * (top + kk) + 0)
                   /\ getr r0 11 = Z_to_bv 64 (data + 4 * wpl * (top + kk) + left)
                   /\ regs_agree (fun r : reg => In r [5; 11]%list) regs r0).
    1, 3: (eexists; split; [|split; [|split]];
      [ stepb_ft F_17570 D_17570 ltac:(condZ);              (* [comment removed for export] *)
        zv F_17574 D_17574 (Z_to_bv 64 (4 * wpl * kk));     (* [comment removed for export] *)
        zv F_17578 D_17578 (Z_to_bv 64 (data + 4 * wpl * (top + kk) + left));   (* [comment removed for export] *)
        zv F_1757c D_1757c (Z_to_bv 64 (data + 4 * wpl * (top + kk) + 0));      (* [comment removed for export] *)
        apply mst_refl
      | gres; pin; reflexivity | gres; pin; reflexivity | solve_regs_agree ]).
    all: destruct S0 as (r0 & S0 & Z5 & Z11 & AG0).
    all: destruct (sbv_ML_bytes (data + 4 * wpl * (top + kk)) LOK L4 (Z.to_nat (left - 1)) r0 Mi 0 ltac:(lia) ltac:(lia) HIv Z5 Z11)
           as (r1 & Ma & S1 & HI1 & AG1).
    all: pose proof (AG1 2 ltac:(notin_list)) as A2; rewrite (AG0 2 ltac:(notin_list)), H2 in A2.
    all: pose proof (AG1 13 ltac:(notin_list)) as A13; rewrite (AG0 13 ltac:(notin_list)), H13 in A13.
    all: pose proof (AG1 15 ltac:(notin_list)) as A15; rewrite (AG0 15 ltac:(notin_list)), H15 in A15.
    (* [comment removed for export] *)
    all: assert (S2 : exists r2, msteps SEGS (mkst r1 (0x1768c : word) Ma rom) (mkst r2 (0x17698 : word) Ma rom)
                   /\ getr r2 5 = Z_to_bv 64 (w - right)
                   /\ regs_agree (fun r : reg => In r [5; 11]%list) r1 r2).
    1, 3: (eexists; split; [|split];
      [ ldw F_17590 D_17590 HI1;                            (* [comment removed for export] *)
        zv F_17594 D_17594 (Z_to_bv 64 (w - right));        (* [comment removed for export] *)
        stepb_ft F_17598 D_17598 ltac:(condZ);              (* [comment removed for export] *)
        apply mst_refl
      | gres; pin; reflexivity | solve_regs_agree ]).
    all: destruct S2 as (r2 & S2 & B5 & AG2).
    all: pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
    all: pose proof (AG2 15 ltac:(notin_list)) as B15; rewrite A15 in B15.
    all: destruct (sbv_MR_bytes (data + 4 * wpl * (top + kk)) LOK L4 (Z.to_nat (right - 1)) r2 Ma (w - right) ltac:(lia) ltac:(lia) HI1 B2 B5 B15)
           as (r3 & Mb & S3 & HI3 & C11 & AG3).
    all: assert (AG03 : regs_agree (fun r : reg => In r [5; 6; 11]%list) regs r3)
           by (eapply regs_agree_trans; [regs_agree_weaken AG0|]; eapply regs_agree_trans; [regs_agree_weaken AG1|];
               eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
    all: pose proof (AG03 12 ltac:(notin_list)) as C12; rewrite H12 in C12.
    all: pose proof (AG03 14 ltac:(notin_list)) as C14; rewrite H14 in C14.
    all: pose proof (AG03 15 ltac:(notin_list)) as C15; rewrite H15 in C15.
    all: pose proof (AG03 16 ltac:(notin_list)) as C16; rewrite H16 in C16.
    all: pose proof (AG03 23 ltac:(notin_list)) as C23; rewrite H23 in C23.
    - eexists. exists Mb. split; [|split; [exact HI3 | split]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        sn F_175b4 D_175b4.                                 (* [comment removed for export] *)
        zv F_17560 D_17560 (Z_to_bv 64 (top + (kk + 1))).   (* [comment removed for export] *)
        zv F_17564 D_17564 (Z_to_bv 64 (data + 4 * wpl * (top + (kk + 1)))).   (* [comment removed for export] *)
        zv F_17568 D_17568 (Z_to_bv 64 (kk + 1)).           (* [comment removed for export] *)
        stepb_tk F_1756c D_1756c ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact C11.
      + eapply regs_agree_trans; [regs_agree_weaken AG03|]. solve_regs_agree.
    - assert (S4 : exists r4, msteps SEGS (mkst r3 (0x176b0 : word) Mb rom) (mkst r4 (0x1766c : word) Mb rom)
                   /\ getr r4 23 = Z_to_bv 64 (top + (kk + 1)) /\ getr r4 15 = Z_to_bv 64 (data + 4 * wpl * (top + (kk + 1)))
                   /\ getr r4 14 = Z_to_bv 64 (kk + 1)
                   /\ regs_agree (fun r : reg => In r [14; 15; 23]%list) r3 r4).
      { eexists. split; [|split; [|split; [|split]]].
        - sn F_175b4 D_175b4.
          zv F_17560 D_17560 (Z_to_bv 64 (top + (kk + 1))).
          zv F_17564 D_17564 (Z_to_bv 64 (data + 4 * wpl * (top + (kk + 1)))).
          zv F_17568 D_17568 (Z_to_bv 64 (kk + 1)).
          stepb_ft F_1756c D_1756c ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S4 as (r4 & S4 & D23 & D15 & D14 & AG4).
      pose proof (AG4 2 ltac:(notin_list)) as D2; rewrite (AG03 2 ltac:(notin_list)), H2 in D2.
      pose proof (AG4 9 ltac:(notin_list)) as D9; rewrite (AG03 9 ltac:(notin_list)), H9 in D9.
      pose proof (AG4 12 ltac:(notin_list)) as D12; rewrite C12 in D12.
      pose proof (AG4 13 ltac:(notin_list)) as D13; rewrite (AG03 13 ltac:(notin_list)), H13 in D13.
      pose proof (AG4 16 ltac:(notin_list)) as D16; rewrite C16 in D16.
      pose proof (AG4 17 ltac:(notin_list)) as D17; rewrite (AG03 17 ltac:(notin_list)), H17 in D17.
      destruct (IH r4 Mb (kk + 1)%Z ltac:(lia) ltac:(lia) HI3 D2 D9 D12 D13 D14 D15 D16 D17 D23) as (r5 & Mc & S5 & HI5 & E11 & AG5).
      exists r5, Mc. split; [|split; [exact HI5 | split; [exact E11|]]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        eapply msteps_trans; [exact S3|]. eapply msteps_trans; [exact S4 | exact S5].
      + eapply regs_agree_trans; [regs_agree_weaken AG03|]. eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_B_pre : forall regs Mi, Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 10 = Z_to_bv 64 wpl -> getr regs 12 = Z_to_bv 64 (h - bot) ->
    getr regs 18 = Z_to_bv 64 data ->
    exists regs',
      msteps SEGS (mkst regs (0x177d0 : word) Mi rom) (mkst regs' (0x177f8 : word) Mi rom)
      /\ getr regs' 10 = Z_to_bv 64 (4 * wpl) /\ getr regs' 18 = Z_to_bv 64 (data + 4 * wpl * (h - bot))
      /\ regs_agree (fun r : reg => In r [10; 13; 14; 18]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2 H10 H12 H18.
    assert (Hbw : (0 <= (h - bot) * wpl <= 20000 * 20000)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
    eexists. split.
    - ldh F_176d4 D_176d4 HIv.                              (* [comment removed for export] *)
      stepb_ft F_176d8 D_176d8 ltac:(condZ).                (* [comment removed for export] *)
      zv F_176dc D_176dc (Z_to_bv 64 ((h - bot) * wpl)).    (* [comment removed for export] *)
      stepiv F_176e0 D_176e0 (Z_to_bv 64 (4 * ((h - bot) * wpl)))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).   (* [comment removed for export] *)
      zv F_176e4 D_176e4 (Z_to_bv 64 (data + 4 * wpl * (h - bot))).      (* [comment removed for export] *)
      stepiv F_176e8 D_176e8 (Z_to_bv 64 (4 * wpl))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).   (* [comment removed for export] *)
      sn F_176ec D_176ec.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_byte : forall regs Mi i j,
    (0 <= i < h)%Z -> (0 <= j < w)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) ->
    getr regs 13 = Z_to_bv 64 j -> getr regs 14 = Z_to_bv 64 (data + 4 * wpl * i + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17804 : word) Mi rom) (mkst regs' (0x17818 : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w /\ getr regs' 13 = Z_to_bv 64 (j + 1)
      /\ getr regs' 14 = Z_to_bv 64 (data + 4 * wpl * i + (j + 1))
      /\ regs_agree (fun r : reg => In r [11; 13; 14]%list) regs regs'.
  Proof.
    intros regs Mi i j Hi Hj HIv H2 H13 H14.
    pose proof (row_bound i Hi) as RB. pose proof (xo_bound j wpl ltac:(lia)) as XB. pose proof (row_mod4 i) as R4.
    assert (HI' : Inv (wbytes Mi (Z_to_bv 64 (data + 4 * wpl * i + xo j)) [Z_to_bv 8 (bv_unsigned (getr regs 8))])).
    { apply Inv_store; [exact HIv | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia]. }
    eexists. eexists. split; [|split; [exact HI'|]].
    - stepiv F_17708 D_17708 (Z_to_bv 64 (data + 4 * wpl * i + xo j))
        ltac:(gres; pin; imm_norm; apply xor3_xo; [lia | exact R4 | lia | lia]).     (* [comment removed for export] *)
      gsb F_1770c D_1770c (data + 4 * wpl * i + xo j)%Z HIv.                          (* [comment removed for export] *)
      ldw F_17710 D_17710 HI'.                                                        (* [comment removed for export] *)
      zv F_17714 D_17714 (Z_to_bv 64 (j + 1)).                                        (* [comment removed for export] *)
      zv F_17718 D_17718 (Z_to_bv 64 (data + 4 * wpl * i + (j + 1))).                 (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_bytes : forall (k : nat) regs Mi i j,
    (0 <= i < h)%Z -> (0 <= j)%Z -> (j + Z.of_nat k = w - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) ->
    getr regs 13 = Z_to_bv 64 j -> getr regs 14 = Z_to_bv 64 (data + 4 * wpl * i + j) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17804 : word) Mi rom) (mkst regs' (0x1781c : word) M' rom)
      /\ Inv M' /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [11; 13; 14]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i j Hi Hj Hk HIv H2 H13 H14;
      destruct (sbv_B_byte regs Mi i j Hi ltac:(lia) HIv H2 H13 H14) as (r1 & Ma & S1 & HI1 & A11 & A13 & A14 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact A11 | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_1771c D_1771c ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - pose proof (AG1 2 ltac:(notin_list)) as A2. rewrite H2 in A2.
      destruct (IH r1 Ma i (j + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 A2 A13 A14) as (r2 & Mb & S2 & HI2 & B11 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B11|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_1771c D_1771c ltac:(condZ).
        exact S2.
      + eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma sbv_B_rows : forall (k : nat) regs Mi i,
    (0 <= i)%Z -> (i + Z.of_nat k = h - 1)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 10 = Z_to_bv 64 (4 * wpl) -> getr regs 11 = Z_to_bv 64 w ->
    getr regs 12 = Z_to_bv 64 i -> getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x177f8 : word) Mi rom) (mkst regs' (0x17870 : word) M' rom)
      /\ Inv M'
      /\ regs_agree (fun r : reg => In r [11; 12; 13; 14; 18]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv H2 H10 H11 H12 H18.
    all: assert (S0 : exists r0, msteps SEGS (mkst regs (0x177f8 : word) Mi rom) (mkst r0 (0x17804 : word) Mi rom)
                   /\ getr r0 13 = Z_to_bv 64 0 /\ getr r0 14 = Z_to_bv 64 (data + 4 * wpl * i + 0)
                   /\ regs_agree (fun r : reg => In r [13; 14]%list) regs r0).
    1, 3: (eexists; split; [|split; [|split]];
      [ stepb_ft F_176fc D_176fc ltac:(condZ);              (* [comment removed for export] *)
        sn F_17700 D_17700;                                 (* [comment removed for export] *)
        zv F_17704 D_17704 (Z_to_bv 64 (data + 4 * wpl * i + 0));   (* [comment removed for export] *)
        apply mst_refl
      | gres; pin; reflexivity | gres; pin; reflexivity | solve_regs_agree ]).
    all: destruct S0 as (r0 & S0 & Z13 & Z14 & AG0).
    all: pose proof (AG0 2 ltac:(notin_list)) as Z2; rewrite H2 in Z2.
    all: destruct (sbv_B_bytes (Z.to_nat (w - 1)) r0 Mi i 0 ltac:(lia) ltac:(lia) ltac:(lia) HIv Z2 Z13 Z14) as (r1 & Ma & S1 & HI1 & A11 & AG1).
    all: pose proof (AG1 2 ltac:(notin_list)) as A2; rewrite Z2 in A2.
    all: pose proof (AG1 10 ltac:(notin_list)) as A10; rewrite (AG0 10 ltac:(notin_list)), H10 in A10.
    all: pose proof (AG1 12 ltac:(notin_list)) as A12; rewrite (AG0 12 ltac:(notin_list)), H12 in A12.
    all: pose proof (AG1 18 ltac:(notin_list)) as A18; rewrite (AG0 18 ltac:(notin_list)), H18 in A18.
    - eexists. exists Ma. split; [|split; [exact HI1|]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|].
        ldh F_17720 D_17720 HI1.                            (* [comment removed for export] *)
        sn F_17724 D_17724.                                 (* [comment removed for export] *)
        zv F_176f0 D_176f0 (Z_to_bv 64 (i + 1)).            (* [comment removed for export] *)
        zv F_176f4 D_176f4 (Z_to_bv 64 (data + 4 * wpl * (i + 1))).   (* [comment removed for export] *)
        stepb_tk F_176f8 D_176f8 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + eapply regs_agree_trans; [regs_agree_weaken AG0|]. eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (0x1781c : word) Ma rom) (mkst r2 (0x177f8 : word) Ma rom)
                   /\ getr r2 12 = Z_to_bv 64 (i + 1) /\ getr r2 18 = Z_to_bv 64 (data + 4 * wpl * (i + 1))
                   /\ regs_agree (fun r : reg => In r [12; 13; 18]%list) r1 r2).
      { eexists. split; [|split; [|split]].
        - ldh F_17720 D_17720 HI1.
          sn F_17724 D_17724.
          zv F_176f0 D_176f0 (Z_to_bv 64 (i + 1)).
          zv F_176f4 D_176f4 (Z_to_bv 64 (data + 4 * wpl * (i + 1))).
          stepb_ft F_176f8 D_176f8 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & B12 & B18 & AG2).
      pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
      pose proof (AG2 10 ltac:(notin_list)) as B10; rewrite A10 in B10.
      pose proof (AG2 11 ltac:(notin_list)) as B11; rewrite A11 in B11.
      destruct (IH r2 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 B2 B10 B11 B12 B18) as (r3 & Mb & S3 & HI3 & AG3).
      exists r3, Mb. split; [|split; [exact HI3|]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG0|]. eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sbv_T_pre : forall regs Mi,
    getr regs 10 = Z_to_bv 64 wpl -> getr regs 18 = Z_to_bv 64 data -> getr regs 24 = Z_to_bv 64 top ->
    exists regs',
      msteps SEGS (mkst regs (0x175d8 : word) Mi rom) (mkst regs' (0x175f8 : word) Mi rom)
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 (4 * wpl) /\ getr regs' 14 = Z_to_bv 64 (data + 4 * wpl * 0)
      /\ regs_agree (fun r : reg => In r [12; 13; 14]%list) regs regs'.
  Proof.
    intros regs Mi H10 H18 H24. eexists. split.
    - stepb_ft F_174dc D_174dc ltac:(condZ).                (* [comment removed for export] *)
      sn F_174e0 D_174e0.                                   (* [comment removed for export] *)
      stepiv F_174e4 D_174e4 (Z_to_bv 64 (4 * wpl))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).   (* [comment removed for export] *)
      zv F_174e8 D_174e8 (Z_to_bv 64 (data + 4 * wpl * 0)). (* [comment removed for export] *)
      sn F_174ec D_174ec.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

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

  Ltac ldsv F D k v FL HIv :=
    stepLD F D (word_to_le_bytes 8 v) v
      ltac:(rdn_addr (sp - k)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact FL])
      ltac:(apply bytes_le_to_Z_8).

  (* [comment removed for export] *)
  Lemma sbv_E : forall regs Mi, Inv Mi -> getr regs 2 = Z_to_bv 64 (sp - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x17870 : word) Mi rom) (mkst regs' ra Mi rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2.
    eexists. split.
    - sn F_17774 D_17774.                                   (* [comment removed for export] *)
      ldsv F_17778 D_17778 8%Z ra F_ra HIv.
      ldsv F_1777c D_1777c 16%Z s0v F_s0 HIv.
      ldsv F_17780 D_17780 24%Z s1v F_s1 HIv.
      ldsv F_17784 D_17784 32%Z s2v F_s2 HIv.
      ldsv F_17788 D_17788 40%Z s3v F_s3 HIv.
      ldsv F_1778c D_1778c 48%Z s4v F_s4 HIv.
      ldsv F_17790 D_17790 56%Z s5v F_s5 HIv.
      ldsv F_17794 D_17794 64%Z s6v F_s6 HIv.
      ldsv F_17798 D_17798 72%Z s7v F_s7 HIv.
      ldsv F_1779c D_1779c 80%Z s8v F_s8 HIv.
      zv F_177a0 D_177a0 (Z_to_bv 64 sp).                   (* [comment removed for export] *)
      stepret F_177a4 D_177a4 ra ltac:(reflexivity).        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma M2_outside : forall x : word, (bv_unsigned x < sp - 96 \/ sp <= bv_unsigned x)%Z -> M2 x = M x.
  Proof.
    intros x Hx. unfold M2, M1.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem sbv_run : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v ->
    getr regs 21 = s5v -> getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
    getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
    exists regs' M',
      msteps SEGS (mkst regs (0x17344 : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H10 H11 H12 H13 H14 H15.
    destruct (sbv_A regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H10 H11 H12 H13 H14 H15)
      as (r1 & S1 & A2 & A8 & A9 & A18 & A19 & A20 & A21 & A23 & A24 & A10 & A11 & AG1).
    destruct (sbv_T_pre r1 M2 A10 A18 A24) as (r2 & S2 & B12 & B13 & B14 & AG2).
    pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
    pose proof (AG2 11 ltac:(notin_list)) as B11; rewrite A11 in B11.
    pose proof (AG2 24 ltac:(notin_list)) as B24; rewrite A24 in B24.
    destruct (sbv_T_rows (Z.to_nat (top - 1)) r2 M2 0 ltac:(lia) ltac:(lia) Inv_M2 B2 B11 B12 B13 B14 B24) as (r3 & M3 & S3 & HI3 & C11 & AG3).
    assert (AG23 : regs_agree (fun r : reg => In r [11; 12; 13; 14; 15; 16]%list) r1 r3)
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
    destruct (sbv_M_pre r3 M3 HI3 C2 C9 C10 C11 C18 C19 C20 C21 C23 C24) as (r4 & S4 & D12 & D13 & D14 & D15 & D16 & D17 & D23 & AG4).
    pose proof (AG4 2 ltac:(notin_list)) as D2; rewrite C2 in D2.
    pose proof (AG4 9 ltac:(notin_list)) as D9; rewrite C9 in D9.
    destruct (sbv_M_rows (Z.to_nat (h - bot - top - 1)) r4 M3 0 ltac:(lia) ltac:(lia) HI3 D2 D9 D12 D13 D14 D15 D16 D17 D23)
      as (r5 & M5 & S5 & HI5 & E11 & AG5).
    assert (AG45 : regs_agree (fun r : reg => In r [5; 6; 11; 12; 13; 14; 15; 16; 17; 23]%list) r3 r5)
      by (eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5]).
    pose proof (AG45 2 ltac:(notin_list)) as E2; rewrite C2 in E2.
    pose proof (AG45 10 ltac:(notin_list)) as E10; rewrite C10 in E10.
    pose proof (AG45 18 ltac:(notin_list)) as E18; rewrite C18 in E18.
    pose proof (AG5 12 ltac:(notin_list)) as E12; rewrite D12 in E12.
    destruct (sbv_B_pre r5 M5 HI5 E2 E10 E12 E18) as (r6 & S6 & G10 & G18 & AG6).
    pose proof (AG6 2 ltac:(notin_list)) as G2; rewrite E2 in G2.
    pose proof (AG6 11 ltac:(notin_list)) as G11; rewrite E11 in G11.
    pose proof (AG6 12 ltac:(notin_list)) as G12; rewrite E12 in G12.
    destruct (sbv_B_rows (Z.to_nat (bot - 1)) r6 M5 (h - bot) ltac:(lia) ltac:(lia) HI5 G2 G10 G11 G12 G18) as (r7 & M7 & S7 & HI7 & AG7).
    pose proof (AG7 2 ltac:(notin_list)) as J2; rewrite G2 in J2.
    destruct (sbv_E r7 M7 HI7 J2) as (r8 & S8 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & AG8).
    exists r8, M7. split.
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
      eapply msteps_trans; [exact S4|]. eapply msteps_trans; [exact S5|]. eapply msteps_trans; [exact S6|].
      eapply msteps_trans; [exact S7 | exact S8].
    - split; [exact HI7|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG23|].
      eapply regs_agree_trans; [regs_agree_weaken AG45|]. eapply regs_agree_trans; [regs_agree_weaken AG6|].
      eapply regs_agree_trans; [regs_agree_weaken AG7 | regs_agree_weaken AG8].
  Qed.

End SBV.

