(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 LeptRop GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_7fc9c_80000 V23_code_rasteropLow_87000_875f4.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptRop_iface V23LeptRop.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition RGP_ENTRY : word := 0x7fc9c.
Definition RGP_A1 : word := 0x7fd18.
Definition RGP_P0 : word := 0x7ff84.
Definition RGP_E : word := 0x875b8.

Section RGP.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variables s datad dpixh dwpl dy dh datas spixh swpl sy : Z.
  Variables d dpixw dx dw spixw sx : Z.
  Variables DPW DX DW SPW SX : Z.
  Variable op : Z.
  Variables ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word.

  Hypothesis Hs : (240 <= s /\ s + 64 < 2 ^ 64)%Z.
  Hypothesis Hd : (d = 1 \/ d = 8)%Z.
  Hypothesis EDPW : (DPW = dpixw * d)%Z.  Hypothesis EDX : (DX = dx * d)%Z.  Hypothesis EDW : (DW = dw * d)%Z.
  Hypothesis ESPW : (SPW = spixw * d)%Z.  Hypothesis ESX : (SX = sx * d)%Z.
  Hypothesis Hpix : (1 <= dpixw <= 20000 /\ 1 <= dpixh <= 20000 /\ 1 <= spixw <= 20000 /\ 1 <= spixh <= 20000)%Z.
  Hypothesis Hrd : (0 <= dx /\ 0 <= dy /\ 1 <= dw /\ 1 <= dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh)%Z.
  Hypothesis Hrs : (0 <= sx /\ 0 <= sy /\ sx + dw <= spixw /\ sy + dh <= spixh)%Z.

  Hypothesis A_dh : rdn SEGS M (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Hypothesis A_op : rdn SEGS M (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)).
  Hypothesis A_datas : rdn SEGS M (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)).
  Hypothesis A_spixw : rdn SEGS M (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)).
  Hypothesis A_spixh : rdn SEGS M (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)).
  Hypothesis A_swpl : rdn SEGS M (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)).
  Hypothesis A_sx : rdn SEGS M (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)).
  Hypothesis A_sy : rdn SEGS M (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)).
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (s - 240)) 240 = true.

  Definition PM1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 s1v))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 s2v))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 s5v))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 s6v))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 s7v))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 s8v))
      (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 s9v))
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 s10v))
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 s11v).

  Definition PM1a : word -> option byte := wbytes PM1 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh)).

  Lemma rgp_sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 240)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - k)) n = true.
  Proof.
    intros m k n Hg Hk. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (s - 240)) _ 240%nat); [ | exact SOKf | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.
  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac sokf := apply rgp_sok_frame; [ unfold PM1; grows | cbn; lia ].
  Ltac stf F D k v := stepST F D (Z_to_bv 64 (s - k)) v ltac:(sokf).
  Ltac ldarg F D z A := stepLD F D (word_to_le_bytes 8 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; repeat rdn_peel1; rewrite ?Z.sub_0_r; exact A) ltac:(apply bytes_le_to_Z_8).
  Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
  Ltac zvw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?v_addi_0; rewrite ?zbv_addiw_small by lia;
                                       rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
  Ltac condS := pin; rewrite ?c_lts_Zs by lia; first [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
  Ltac mulw_v F D v := sn F D; fixv' v ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
  Ltac sextw F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
  Ltac addw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite addw_fit by lia; f_equal; lia).
  Ltac subw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite subw_fit by lia; f_equal; lia).

  Lemma rgp_bits : (1 <= DPW <= 160000 /\ 0 <= DX /\ 1 <= DW /\ DX + DW <= DPW /\ 1 <= SPW <= 160000 /\ 0 <= SX /\ SX + DW <= SPW)%Z.
  Proof. destruct Hd as [-> | ->]; lia. Qed.

  Lemma rg_A0 : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 s ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v -> getr regs 25 = s9v -> getr regs 26 = s10v -> getr regs 27 = s11v ->
    getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
    exists regs',
      msteps SEGS (mkst regs RGP_ENTRY M rom) (mkst regs' RGP_A1 PM1 rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 10 = Z_to_bv 64 datad /\ getr regs' 14 = Z_to_bv 64 dwpl /\ getr regs' 16 = Z_to_bv 64 dy
      /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 26 = Z_to_bv 64 sy /\ getr regs' 20 = Z_to_bv 64 SX /\ getr regs' 6 = Z_to_bv 64 swpl
      /\ getr regs' 28 = Z_to_bv 64 spixh /\ getr regs' 29 = Z_to_bv 64 SPW /\ getr regs' 19 = Z_to_bv 64 datas /\ getr regs' 11 = Z_to_bv 64 op
      /\ getr regs' 22 = Z_to_bv 64 dh /\ getr regs' 30 = Z_to_bv 64 DX /\ getr regs' 8 = Z_to_bv 64 DW /\ getr regs' 21 = Z_to_bv 64 DPW
      /\ regs_agree (fun r : reg => In r [2; 5; 6; 8; 11; 12; 13; 15; 19; 20; 21; 22; 23; 26; 28; 29; 30]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12 H13 H14 H15 H16 H17.
    unfold RGP_ENTRY, RGP_A1.
    pose proof rgp_bits as BB.
    assert (Hdd : (d = 1 \/ d = 8)%Z) by exact Hd.
    destruct Hdd as [D1 | D8]; subst d; rewrite ?Z.mul_1_r in *; eexists; (split; [
      zv F_7fc9c D_7fc9c (Z_to_bv 64 (s - 240));
      stf F_7fca0 D_7fca0 8%Z ra; stf F_7fca4 D_7fca4 16%Z s0v; stf F_7fca8 D_7fca8 24%Z s1v; stf F_7fcac D_7fcac 32%Z s2v;
      stf F_7fcb0 D_7fcb0 40%Z s3v; stf F_7fcb4 D_7fcb4 48%Z s4v; stf F_7fcb8 D_7fcb8 56%Z s5v; stf F_7fcbc D_7fcbc 64%Z s6v;
      stf F_7fcc0 D_7fcc0 72%Z s7v; stf F_7fcc4 D_7fcc4 80%Z s8v; stf F_7fcc8 D_7fcc8 88%Z s9v; stf F_7fccc D_7fccc 96%Z s10v;
      stf F_7fcd0 D_7fcd0 104%Z s11v;
      fold PM1;
      zv F_7fcd4 D_7fcd4 (Z_to_bv 64 dpixh);
      zv F_7fcd8 D_7fcd8 (Z_to_bv 64 dpixw);
      unfold PM1;
      ldarg F_7fcdc D_7fcdc sy A_sy;
      ldarg F_7fce0 D_7fce0 sx A_sx;
      ldarg F_7fce4 D_7fce4 swpl A_swpl;
      ldarg F_7fce8 D_7fce8 spixh A_spixh;
      ldarg F_7fcec D_7fcec spixw A_spixw;
      ldarg F_7fcf0 D_7fcf0 datas A_datas;
      ldarg F_7fcf4 D_7fcf4 op A_op;
      ldarg F_7fcf8 D_7fcf8 dh A_dh;
      fold PM1;
      sn F_7fcfc D_7fcfc |]).
    - stepb_ft F_7fd00 D_7fd00 ltac:(condZ).
      zv F_7fd04 D_7fd04 (Z_to_bv 64 DW).
      zv F_7fd08 D_7fd08 (Z_to_bv 64 DX).
      zv F_7fd0c D_7fd0c (Z_to_bv 64 DPW).
      zvw F_7fd10 D_7fd10 (Z_to_bv 64 dx).
      stepb_ft F_7fd14 D_7fd14 ltac:(condZ).
      apply mst_refl.
    - subst DPW DX DW SPW SX. repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - stepb_tk F_7fd00 D_7fd00 ltac:(condZ).
      zv F_7fd2c D_7fd2c (Z_to_bv 64 DPW). mulw_v F_7fd30 D_7fd30 (Z_to_bv 64 DPW). stepb_tk F_7fd34 D_7fd34 ltac:(condR).
      zv F_7fd3c D_7fd3c (Z_to_bv 64 DX). mulw_v F_7fd40 D_7fd40 (Z_to_bv 64 DX). stepb_tk F_7fd44 D_7fd44 ltac:(condR).
      zv F_7fd4c D_7fd4c (Z_to_bv 64 DW). mulw_v F_7fd50 D_7fd50 (Z_to_bv 64 DW). stepb_tk F_7fd54 D_7fd54 ltac:(condR).
      zv F_7fd5c D_7fd5c (Z_to_bv 64 SPW). mulw_v F_7fd60 D_7fd60 (Z_to_bv 64 SPW). stepb_tk F_7fd64 D_7fd64 ltac:(condR).
      zv F_7fd6c D_7fd6c (Z_to_bv 64 SX). mulw_v F_7fd70 D_7fd70 (Z_to_bv 64 SX). stepb_tk F_7fd74 D_7fd74 ltac:(condR).
      zv F_7fd7c D_7fd7c (Z_to_bv 64 SPW).
      zv F_7fd80 D_7fd80 (Z_to_bv 64 SX).
      zvw F_7fd84 D_7fd84 (Z_to_bv 64 DX).
      stepb_tk F_7fd88 D_7fd88 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma rg_A1 : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 16 = Z_to_bv 64 dy -> getr regs 23 = Z_to_bv 64 dpixh -> getr regs 26 = Z_to_bv 64 sy ->
    getr regs 20 = Z_to_bv 64 SX -> getr regs 28 = Z_to_bv 64 spixh -> getr regs 29 = Z_to_bv 64 SPW -> getr regs 22 = Z_to_bv 64 dh ->
    getr regs 30 = Z_to_bv 64 DX -> getr regs 8 = Z_to_bv 64 DW -> getr regs 21 = Z_to_bv 64 DPW ->
    exists regs',
      msteps SEGS (mkst regs RGP_A1 PM1 rom) (mkst regs' RGP_P0 PM1a rom)
      /\ getr regs' 31 = Z_to_bv 64 (DX + DW - DPW) /\ getr regs' 9 = Z_to_bv 64 DW /\ getr regs' 25 = Z_to_bv 64 DX /\ getr regs' 27 = Z_to_bv 64 SX
      /\ getr regs' 5 = Z_to_bv 64 sy /\ getr regs' 7 = Z_to_bv 64 dy
      /\ getr regs' 1 = Z_to_bv 64 sy /\ getr regs' 18 = Z_to_bv 64 (dy + dh - dpixh) /\ getr regs' 13 = Z_to_bv 64 DX /\ getr regs' 24 = Z_to_bv 64 SX
      /\ regs_agree (fun r : reg => In r [1; 5; 7; 9; 12; 13; 15; 17; 18; 22; 24; 25; 27; 31]%list) regs regs'.
  Proof.
    intros regs H2 H16 H23 H26 H20 H28 H29 H22 H30 H8 H21.
    unfold RGP_A1, RGP_P0.
    pose proof rgp_bits as BB.
    eexists. split.
    - zv F_7fd18 D_7fd18 (Z_to_bv 64 SX).
      zv F_7fd1c D_7fd1c (Z_to_bv 64 DX).
      sextw F_7fd20 D_7fd20 SX.
      stepb_tk F_7fd24 D_7fd24 ltac:(condZ).
      sextw F_7fdec D_7fdec DW. sextw F_7fdf0 D_7fdf0 DX.
      zv F_7fdf4 D_7fdf4 (Z_to_bv 64 (DX + DW)). addw_v F_7fdf8 D_7fdf8 (DX + DW)%Z.
      stepb_tk F_7fdfc D_7fdfc ltac:(condR).
      sextw F_7fe04 D_7fe04 (DX + DW)%Z. sextw F_7fe08 D_7fe08 DPW.
      subw_v F_7fe0c D_7fe0c (DX + DW - DPW)%Z. zv F_7fe10 D_7fe10 (Z_to_bv 64 (DX + DW - DPW)).
      stepb_tk F_7fe14 D_7fe14 ltac:(condR).
      stepb_tk F_7fe1c D_7fe1c ltac:(condS).
      sextw F_7fe30 D_7fe30 DW. sextw F_7fe34 D_7fe34 SX.
      zv F_7fe38 D_7fe38 (Z_to_bv 64 (SX + DW)). addw_v F_7fe3c D_7fe3c (SX + DW)%Z.
      stepb_tk F_7fe40 D_7fe40 ltac:(condR).
      sextw F_7fe48 D_7fe48 (SX + DW)%Z. sextw F_7fe4c D_7fe4c SPW.
      subw_v F_7fe50 D_7fe50 (SX + DW - SPW)%Z. zv F_7fe54 D_7fe54 (Z_to_bv 64 (SX + DW - SPW)).
      stepb_tk F_7fe58 D_7fe58 ltac:(condR).
      stepb_tk F_7fe60 D_7fe60 ltac:(condS).
      stepb_ft F_7fe74 D_7fe74 ltac:(condZ).
      zv F_7fe78 D_7fe78 (Z_to_bv 64 sy).
      zv F_7fe7c D_7fe7c (Z_to_bv 64 dy).
      sextw F_7fe80 D_7fe80 sy.
      stepb_ft F_7fe84 D_7fe84 ltac:(condZ).
      zv F_7fe88 D_7fe88 (Z_to_bv 64 dy).
      sn F_7fe8c D_7fe8c.
      sextw F_7fee8 D_7fee8 dh. sextw F_7feec D_7feec dy.
      zv F_7fef0 D_7fef0 (Z_to_bv 64 (dy + dh)). addw_v F_7fef4 D_7fef4 (dy + dh)%Z.
      stepb_tk F_7fef8 D_7fef8 ltac:(condR).
      sextw F_7ff00 D_7ff00 (dy + dh)%Z.
      subw_v F_7ff04 D_7ff04 (dy + dh - dpixh)%Z. zv F_7ff08 D_7ff08 (Z_to_bv 64 (dy + dh - dpixh)).
      stepb_tk F_7ff0c D_7ff0c ltac:(condR).
      stepb_tk F_7ff14 D_7ff14 ltac:(condS).
      sextw F_7ff28 D_7ff28 dh. sextw F_7ff2c D_7ff2c sy.
      zv F_7ff30 D_7ff30 (Z_to_bv 64 (sy + dh)). addw_v F_7ff34 D_7ff34 (sy + dh)%Z.
      stepb_tk F_7ff38 D_7ff38 ltac:(condR).
      sextw F_7ff40 D_7ff40 (sy + dh)%Z.
      subw_v F_7ff44 D_7ff44 (sy + dh - spixh)%Z. zv F_7ff48 D_7ff48 (Z_to_bv 64 (sy + dh - spixh)).
      stepb_tk F_7ff4c D_7ff4c ltac:(condR).
      stepb_tk F_7ff54 D_7ff54 ltac:(condS).
      sextw F_7ff68 D_7ff68 DW.
      stepb_tk F_7ff6c D_7ff6c ltac:(condZ).
      sextw F_7ff74 D_7ff74 dh.
      stepST F_7ff78 D_7ff78 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 dh) ltac:(sokf).
      fold PM1a.
      stepb_tk F_7ff7c D_7ff7c ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Theorem rgp_run : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 s ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v -> getr regs 25 = s9v -> getr regs 26 = s10v -> getr regs 27 = s11v ->
    getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
    exists regs',
      msteps SEGS (mkst regs RGP_ENTRY M rom) (mkst regs' RGP_P0 PM1a rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 1 = Z_to_bv 64 sy /\ getr regs' 5 = Z_to_bv 64 sy /\ getr regs' 6 = Z_to_bv 64 swpl
      /\ getr regs' 7 = Z_to_bv 64 dy /\ getr regs' 8 = Z_to_bv 64 DW /\ getr regs' 9 = Z_to_bv 64 DW /\ getr regs' 10 = Z_to_bv 64 datad
      /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 13 = Z_to_bv 64 DX /\ getr regs' 14 = Z_to_bv 64 dwpl /\ getr regs' 16 = Z_to_bv 64 dy
      /\ getr regs' 18 = Z_to_bv 64 (dy + dh - dpixh) /\ getr regs' 19 = Z_to_bv 64 datas /\ getr regs' 20 = Z_to_bv 64 SX
      /\ getr regs' 21 = Z_to_bv 64 DPW /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 24 = Z_to_bv 64 SX /\ getr regs' 25 = Z_to_bv 64 DX /\ getr regs' 26 = Z_to_bv 64 sy
      /\ getr regs' 27 = Z_to_bv 64 SX /\ getr regs' 28 = Z_to_bv 64 spixh /\ getr regs' 29 = Z_to_bv 64 SPW /\ getr regs' 30 = Z_to_bv 64 DX
      /\ getr regs' 31 = Z_to_bv 64 (DX + DW - DPW)
      /\ regs_agree (fun r : reg => In r [1; 2; 5; 6; 7; 8; 9; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
  Proof using All.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12 H13 H14 H15 H16 H17.
    destruct (rg_A0 regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12 H13 H14 H15 H16 H17)
      as (r1 & S1 & A2 & A10 & A14 & A16 & A23 & A26 & A20 & A6 & A28 & A29 & A19 & A11 & A22 & A30 & A8 & A21 & AG1).
    destruct (rg_A1 r1 A2 A16 A23 A26 A20 A28 A29 A22 A30 A8 A21) as (r2 & S2 & B31 & B9 & B25 & B27 & B5 & B7 & B1 & B18 & B13 & B24 & AG2).
    pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
    pose proof (AG2 6 ltac:(notin_list)) as B6; rewrite A6 in B6.
    pose proof (AG2 8 ltac:(notin_list)) as B8; rewrite A8 in B8.
    pose proof (AG2 10 ltac:(notin_list)) as B10; rewrite A10 in B10.
    pose proof (AG2 11 ltac:(notin_list)) as B11; rewrite A11 in B11.
    pose proof (AG2 14 ltac:(notin_list)) as B14; rewrite A14 in B14.
    pose proof (AG2 16 ltac:(notin_list)) as B16; rewrite A16 in B16.
    pose proof (AG2 19 ltac:(notin_list)) as B19; rewrite A19 in B19.
    pose proof (AG2 20 ltac:(notin_list)) as B20; rewrite A20 in B20.
    pose proof (AG2 21 ltac:(notin_list)) as B21; rewrite A21 in B21.
    pose proof (AG2 23 ltac:(notin_list)) as B23; rewrite A23 in B23.
    pose proof (AG2 26 ltac:(notin_list)) as B26; rewrite A26 in B26.
    pose proof (AG2 28 ltac:(notin_list)) as B28; rewrite A28 in B28.
    pose proof (AG2 29 ltac:(notin_list)) as B29; rewrite A29 in B29.
    pose proof (AG2 30 ltac:(notin_list)) as B30; rewrite A30 in B30.
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |].
    repeat (split; [assumption|]).
    eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

End RGP.

Section RGW.
Context {fx : FPState}.
Variable rom : word -> option byte.

Lemma rg_pro : forall regs m (s datad dpixw dpixh d dwpl dx dy dw dh op datas spixw spixh swpl sx sy : Z),
  (240 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  V23LeptRop_iface.rop_shape dpixw dpixh d dwpl -> V23LeptRop_iface.rop_shape spixw spixh d swpl ->
  V23LeptRop_iface.rop_rect dpixw dpixh dx dy dw dh -> V23LeptRop_iface.rop_rect spixw spixh sx sy dw dh ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs RGP_ENTRY m rom)
      (mkst regs' RGP_P0 (wbytes (V23LeptRop.RLF m s (getr regs 1) regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 1 = Z_to_bv 64 sy /\ getr regs' 5 = Z_to_bv 64 sy /\ getr regs' 6 = Z_to_bv 64 swpl
    /\ getr regs' 7 = Z_to_bv 64 dy /\ getr regs' 8 = Z_to_bv 64 (dw * d) /\ getr regs' 9 = Z_to_bv 64 (dw * d) /\ getr regs' 10 = Z_to_bv 64 datad
    /\ getr regs' 11 = Z_to_bv 64 op /\ getr regs' 13 = Z_to_bv 64 (dx * d) /\ getr regs' 14 = Z_to_bv 64 dwpl /\ getr regs' 16 = Z_to_bv 64 dy
    /\ getr regs' 18 = Z_to_bv 64 (dy + dh - dpixh) /\ getr regs' 19 = Z_to_bv 64 datas /\ getr regs' 20 = Z_to_bv 64 (sx * d)
    /\ getr regs' 21 = Z_to_bv 64 (dpixw * d) /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 24 = Z_to_bv 64 (sx * d) /\ getr regs' 25 = Z_to_bv 64 (dx * d) /\ getr regs' 26 = Z_to_bv 64 sy
    /\ getr regs' 27 = Z_to_bv 64 (sx * d) /\ getr regs' 28 = Z_to_bv 64 spixh /\ getr regs' 29 = Z_to_bv 64 (spixw * d) /\ getr regs' 30 = Z_to_bv 64 (dx * d)
    /\ getr regs' 31 = Z_to_bv 64 (dx * d + dw * d - dpixw * d)
    /\ regs_agree (fun r : reg => In r [1; 2; 5; 6; 7; 8; 9; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m s datad dpixw dpixh d dwpl dx dy dw dh op datas spixw spixh swpl sx sy Hs Hs64 SHd SHs RCd RCs
    Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy SOK H2 H10 H11 H12 H13 H14 H15 H16 H17.
  destruct SHd as (Hd & Hdpw & Hdph & _ & _). destruct SHs as (_ & Hspw & Hsph & _ & _).
  destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh). destruct RCs as (Hsx0 & Hsy0 & _ & _ & Hsxw & Hsyh).
  exact (rgp_run m rom s datad dpixh dwpl dy dh datas spixh swpl sy d dpixw dx dw spixw sx
           (dpixw * d) (dx * d) (dw * d) (spixw * d) (sx * d) op
           (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
           (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
           ltac:(lia) Hd eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
           Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy SOK
           regs eq_refl H2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           H10 H11 H12 H13 H14 H15 H16 H17).
Qed.

Lemma rg_E : forall regs m (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
  V23LeptRop.rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ->
  getr regs 2 = Z_to_bv 64 (s - 240) ->
  exists regs',
    msteps SEGS (mkst regs RGP_E m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hret
    (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) H2.
  unfold RGP_E.
  eexists. split.
  - stepLD F_875b8 D_875b8 (word_to_le_bytes 8 ret) ret ltac:(rdn_addr (s - 8)%Z; exact C) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875bc D_875bc (word_to_le_bytes 8 v0) v0 ltac:(rdn_addr (s - 16)%Z; exact C0) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875c0 D_875c0 (word_to_le_bytes 8 v1) v1 ltac:(rdn_addr (s - 24)%Z; exact C1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875c4 D_875c4 (word_to_le_bytes 8 v2) v2 ltac:(rdn_addr (s - 32)%Z; exact C2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875c8 D_875c8 (word_to_le_bytes 8 v3) v3 ltac:(rdn_addr (s - 40)%Z; exact C3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875cc D_875cc (word_to_le_bytes 8 v4) v4 ltac:(rdn_addr (s - 48)%Z; exact C4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875d0 D_875d0 (word_to_le_bytes 8 v5) v5 ltac:(rdn_addr (s - 56)%Z; exact C5) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875d4 D_875d4 (word_to_le_bytes 8 v6) v6 ltac:(rdn_addr (s - 64)%Z; exact C6) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875d8 D_875d8 (word_to_le_bytes 8 v7) v7 ltac:(rdn_addr (s - 72)%Z; exact C7) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875dc D_875dc (word_to_le_bytes 8 v8) v8 ltac:(rdn_addr (s - 80)%Z; exact C8) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875e0 D_875e0 (word_to_le_bytes 8 v9) v9 ltac:(rdn_addr (s - 88)%Z; exact C9) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875e4 D_875e4 (word_to_le_bytes 8 v10) v10 ltac:(rdn_addr (s - 96)%Z; exact C10) ltac:(apply bytes_le_to_Z_8).
    stepLD F_875e8 D_875e8 (word_to_le_bytes 8 v11) v11 ltac:(rdn_addr (s - 104)%Z; exact C11) ltac:(apply bytes_le_to_Z_8).
    zv F_875ec D_875ec (Z_to_bv 64 s).
    stepret F_875f0 D_875f0 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End RGW.
