(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 LeptRop GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_7fc9c_80000 V23_code_rasteropLow_80000_81000 V23_code_rasteropLow_81000_82000 V23_code_rasteropLow_82000_83000 V23_code_rasteropLow_83000_84000 V23_code_rasteropLow_84000_85000 V23_code_rasteropLow_85000_86000 V23_code_rasteropLow_86000_87000 V23_code_rasteropLow_87000_875f4.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma lmask_tbl : exists T, rdn SEGS (fun _ => None) (Z_to_bv 64 0x1f4c4) 132 = Some T.
Proof. img_exists. Qed.
Lemma lmask_read : forall m e, (0 <= e <= 32)%Z ->
  exists bs, rdn SEGS m (Z_to_bv 64 (0x1f4c4 + 4 * e)) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros m e He. destruct lmask_tbl as [T HT].
  pose proof (rdn_sub SEGS (fun _ => None) 132 (Z_to_bv 64 0x1f4c4) T (Z.to_nat (4 * e)) 4 HT ltac:(lia)) as HS.
  unfold at_ in HS. rewrite u_Z2bv in HS by lia. rewrite Z2Nat.id in HS by lia.
  exact (rdn_rom_any SEGS m 4 _ _ HS).
Qed.

Section RL.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables s datad dpixh dwpl dy dh datas spixh swpl sy : Z.
  Variables d dpixw dx dw spixw sx : Z.                       (* [comment removed for export] *)
  Variables DPW DX DW SPW SX cd cs nf lw : Z.                 (* [comment removed for export] *)
  Variables ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word.

  Hypothesis Hs : (250000 <= s /\ s + 64 < 2 ^ 64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis Hd : (d = 1 \/ d = 8)%Z.
  Hypothesis EDPW : (DPW = dpixw * d)%Z.  Hypothesis EDX : (DX = dx * d)%Z.  Hypothesis EDW : (DW = dw * d)%Z.
  Hypothesis ESPW : (SPW = spixw * d)%Z.  Hypothesis ESX : (SX = sx * d)%Z.
  Hypothesis Hpix : (1 <= dpixw <= 20000 /\ 1 <= dpixh <= 20000 /\ 1 <= spixw <= 20000 /\ 1 <= spixh <= 20000)%Z.
  Hypothesis Hwpl : (1 <= dwpl <= 20000 /\ DPW <= 32 * dwpl /\ 1 <= swpl <= 20000 /\ SPW <= 32 * swpl)%Z.
  Hypothesis Hrd : (0 <= dx /\ 0 <= dy /\ 1 <= dw /\ 1 <= dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh)%Z.
  Hypothesis Hrs : (0 <= sx /\ 0 <= sy /\ sx + dw <= spixw /\ sy + dh <= spixh)%Z.
  Hypothesis Hcol : (DX = 32 * cd /\ SX = 32 * cs /\ DW = 32 * nf + lw /\ 0 <= lw < 32)%Z.
  (* [comment removed for export] *)
  Hypothesis A_dh : rdn SEGS M (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Hypothesis A_op : rdn SEGS M (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 12)).
  Hypothesis A_datas : rdn SEGS M (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)).
  Hypothesis A_spixw : rdn SEGS M (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)).
  Hypothesis A_spixh : rdn SEGS M (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)).
  Hypothesis A_swpl : rdn SEGS M (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)).
  Hypothesis A_sx : rdn SEGS M (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)).
  Hypothesis A_sy : rdn SEGS M (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)).
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (s - 240)) 240 = true.

  (* [comment removed for export] *)
  Definition M1 : word -> option byte :=
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

  Lemma sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 240)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - k)) n = true.
  Proof.
    intros m k n Hg Hk. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (s - 240)) _ 240%nat); [ | exact SOKf | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.
  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac sokf := apply sok_frame; [ unfold M1; grows | cbn; lia ].
  Ltac stf F D k v := stepST F D (Z_to_bv 64 (s - k)) v ltac:(sokf).
  (* [comment removed for export] *)
  Ltac ldarg F D z A := stepLD F D (word_to_le_bytes 8 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; repeat rdn_peel1; rewrite ?Z.sub_0_r; exact A) ltac:(apply bytes_le_to_Z_8).
  (* [comment removed for export] *)
  Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
  Ltac zvw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?v_addi_0; rewrite ?zbv_addiw_small by lia;
                                       rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
  Ltac condS := pin; rewrite ?c_lts_Zs by lia; first [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
  Ltac mulw_v F D v := sn F D; fixv' v ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).

  Lemma bits_bounds : (1 <= DPW <= 160000 /\ 0 <= DX /\ 1 <= DW /\ DX + DW <= DPW /\ 1 <= SPW <= 160000 /\ 0 <= SX /\ SX + DW <= SPW)%Z.
  Proof. destruct Hd as [-> | ->]; lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rl_A0 : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 s ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v -> getr regs 25 = s9v -> getr regs 26 = s10v -> getr regs 27 = s11v ->
    getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
    exists regs',
      msteps SEGS (mkst regs (0x7fc9c : word) M rom) (mkst regs' (0x7fd18 : word) M1 rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 10 = Z_to_bv 64 datad /\ getr regs' 14 = Z_to_bv 64 dwpl /\ getr regs' 16 = Z_to_bv 64 dy
      /\ getr regs' 23 = Z_to_bv 64 dpixh /\ getr regs' 26 = Z_to_bv 64 sy /\ getr regs' 20 = Z_to_bv 64 SX /\ getr regs' 6 = Z_to_bv 64 swpl
      /\ getr regs' 28 = Z_to_bv 64 spixh /\ getr regs' 29 = Z_to_bv 64 SPW /\ getr regs' 19 = Z_to_bv 64 datas /\ getr regs' 11 = Z_to_bv 64 12
      /\ getr regs' 22 = Z_to_bv 64 dh /\ getr regs' 30 = Z_to_bv 64 DX /\ getr regs' 8 = Z_to_bv 64 DW /\ getr regs' 21 = Z_to_bv 64 DPW
      /\ regs_agree (fun r : reg => In r [2; 5; 6; 8; 11; 12; 13; 15; 19; 20; 21; 22; 23; 26; 28; 29; 30]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12 H13 H14 H15 H16 H17.
    pose proof bits_bounds as BB.
    assert (Hdd : (d = 1 \/ d = 8)%Z) by exact Hd.
    destruct Hdd as [D1 | D8]; subst d; rewrite ?Z.mul_1_r in *; eexists; (split; [
      zv F_7fc9c D_7fc9c (Z_to_bv 64 (s - 240));
      stf F_7fca0 D_7fca0 8%Z ra; stf F_7fca4 D_7fca4 16%Z s0v; stf F_7fca8 D_7fca8 24%Z s1v; stf F_7fcac D_7fcac 32%Z s2v;
      stf F_7fcb0 D_7fcb0 40%Z s3v; stf F_7fcb4 D_7fcb4 48%Z s4v; stf F_7fcb8 D_7fcb8 56%Z s5v; stf F_7fcbc D_7fcbc 64%Z s6v;
      stf F_7fcc0 D_7fcc0 72%Z s7v; stf F_7fcc4 D_7fcc4 80%Z s8v; stf F_7fcc8 D_7fcc8 88%Z s9v; stf F_7fccc D_7fccc 96%Z s10v;
      stf F_7fcd0 D_7fcd0 104%Z s11v;
      fold M1;
      zv F_7fcd4 D_7fcd4 (Z_to_bv 64 dpixh);                (* [comment removed for export] *)
      zv F_7fcd8 D_7fcd8 (Z_to_bv 64 dpixw);                (* [comment removed for export] *)
      unfold M1;
      ldarg F_7fcdc D_7fcdc sy A_sy;                        (* [comment removed for export] *)
      ldarg F_7fce0 D_7fce0 sx A_sx;                        (* [comment removed for export] *)
      ldarg F_7fce4 D_7fce4 swpl A_swpl;                    (* [comment removed for export] *)
      ldarg F_7fce8 D_7fce8 spixh A_spixh;                  (* [comment removed for export] *)
      ldarg F_7fcec D_7fcec spixw A_spixw;                  (* [comment removed for export] *)
      ldarg F_7fcf0 D_7fcf0 datas A_datas;                  (* [comment removed for export] *)
      ldarg F_7fcf4 D_7fcf4 12%Z A_op;                      (* [comment removed for export] *)
      ldarg F_7fcf8 D_7fcf8 dh A_dh;                        (* [comment removed for export] *)
      fold M1;
      sn F_7fcfc D_7fcfc |]).                               (* [comment removed for export] *)
    - (* [comment removed for export] *)
      stepb_ft F_7fd00 D_7fd00 ltac:(condZ).                (* [comment removed for export] *)
      zv F_7fd04 D_7fd04 (Z_to_bv 64 DW).                   (* [comment removed for export] *)
      zv F_7fd08 D_7fd08 (Z_to_bv 64 DX).                   (* [comment removed for export] *)
      zv F_7fd0c D_7fd0c (Z_to_bv 64 DPW).                  (* [comment removed for export] *)
      zvw F_7fd10 D_7fd10 (Z_to_bv 64 dx).                  (* [comment removed for export] *)
      stepb_ft F_7fd14 D_7fd14 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - subst DPW DX DW SPW SX. repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - (* [comment removed for export] *)
      stepb_tk F_7fd00 D_7fd00 ltac:(condZ).
      zv F_7fd2c D_7fd2c (Z_to_bv 64 DPW). mulw_v F_7fd30 D_7fd30 (Z_to_bv 64 DPW). stepb_tk F_7fd34 D_7fd34 ltac:(condR).
      zv F_7fd3c D_7fd3c (Z_to_bv 64 DX). mulw_v F_7fd40 D_7fd40 (Z_to_bv 64 DX). stepb_tk F_7fd44 D_7fd44 ltac:(condR).
      zv F_7fd4c D_7fd4c (Z_to_bv 64 DW). mulw_v F_7fd50 D_7fd50 (Z_to_bv 64 DW). stepb_tk F_7fd54 D_7fd54 ltac:(condR).
      zv F_7fd5c D_7fd5c (Z_to_bv 64 SPW). mulw_v F_7fd60 D_7fd60 (Z_to_bv 64 SPW). stepb_tk F_7fd64 D_7fd64 ltac:(condR).
      zv F_7fd6c D_7fd6c (Z_to_bv 64 SX). mulw_v F_7fd70 D_7fd70 (Z_to_bv 64 SX). stepb_tk F_7fd74 D_7fd74 ltac:(condR).
      zv F_7fd7c D_7fd7c (Z_to_bv 64 SPW).                  (* [comment removed for export] *)
      zv F_7fd80 D_7fd80 (Z_to_bv 64 SX).                   (* [comment removed for export] *)
      zvw F_7fd84 D_7fd84 (Z_to_bv 64 DX).                  (* [comment removed for export] *)
      stepb_tk F_7fd88 D_7fd88 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Definition M1a : word -> option byte := wbytes M1 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Definition M2 : word -> option byte := wbytes M1a (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 swpl)).
  Ltac sokf' := apply sok_frame; [ unfold M2, M1a, M1; grows | cbn; lia ].

  (* [comment removed for export] *)
  Ltac sextw F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
  Ltac addw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite addw_fit by lia; f_equal; lia).
  Ltac subw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite subw_fit by lia; f_equal; lia).

  (* [comment removed for export] *)
  Lemma rl_A1 : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 16 = Z_to_bv 64 dy -> getr regs 23 = Z_to_bv 64 dpixh -> getr regs 26 = Z_to_bv 64 sy ->
    getr regs 20 = Z_to_bv 64 SX -> getr regs 28 = Z_to_bv 64 spixh -> getr regs 29 = Z_to_bv 64 SPW -> getr regs 22 = Z_to_bv 64 dh ->
    getr regs 30 = Z_to_bv 64 DX -> getr regs 8 = Z_to_bv 64 DW -> getr regs 21 = Z_to_bv 64 DPW ->
    exists regs',
      msteps SEGS (mkst regs (0x7fd18 : word) M1 rom) (mkst regs' (0x7ff84 : word) M1a rom)
      /\ getr regs' 31 = Z_to_bv 64 (DX + DW - DPW) /\ getr regs' 9 = Z_to_bv 64 DW /\ getr regs' 25 = Z_to_bv 64 DX /\ getr regs' 27 = Z_to_bv 64 SX
      /\ getr regs' 5 = Z_to_bv 64 sy /\ getr regs' 7 = Z_to_bv 64 dy
      /\ regs_agree (fun r : reg => In r [1; 5; 7; 9; 12; 13; 15; 17; 18; 22; 24; 25; 27; 31]%list) regs regs'.
  Proof.
    intros regs H2 H16 H23 H26 H20 H28 H29 H22 H30 H8 H21.
    pose proof bits_bounds as BB.
    eexists. split.
    - zv F_7fd18 D_7fd18 (Z_to_bv 64 SX).                   (* [comment removed for export] *)
      zv F_7fd1c D_7fd1c (Z_to_bv 64 DX).                   (* [comment removed for export] *)
      sextw F_7fd20 D_7fd20 SX.                             (* [comment removed for export] *)
      stepb_tk F_7fd24 D_7fd24 ltac:(condZ).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_7fdec D_7fdec DW. sextw F_7fdf0 D_7fdf0 DX.
      zv F_7fdf4 D_7fdf4 (Z_to_bv 64 (DX + DW)). addw_v F_7fdf8 D_7fdf8 (DX + DW)%Z.
      stepb_tk F_7fdfc D_7fdfc ltac:(condR).
      sextw F_7fe04 D_7fe04 (DX + DW)%Z. sextw F_7fe08 D_7fe08 DPW.
      subw_v F_7fe0c D_7fe0c (DX + DW - DPW)%Z. zv F_7fe10 D_7fe10 (Z_to_bv 64 (DX + DW - DPW)).
      stepb_tk F_7fe14 D_7fe14 ltac:(condR).
      stepb_tk F_7fe1c D_7fe1c ltac:(condS).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_7fe30 D_7fe30 DW. sextw F_7fe34 D_7fe34 SX.
      zv F_7fe38 D_7fe38 (Z_to_bv 64 (SX + DW)). addw_v F_7fe3c D_7fe3c (SX + DW)%Z.
      stepb_tk F_7fe40 D_7fe40 ltac:(condR).
      sextw F_7fe48 D_7fe48 (SX + DW)%Z. sextw F_7fe4c D_7fe4c SPW.
      subw_v F_7fe50 D_7fe50 (SX + DW - SPW)%Z. zv F_7fe54 D_7fe54 (Z_to_bv 64 (SX + DW - SPW)).
      stepb_tk F_7fe58 D_7fe58 ltac:(condR).
      stepb_tk F_7fe60 D_7fe60 ltac:(condS).                (* [comment removed for export] *)
      stepb_ft F_7fe74 D_7fe74 ltac:(condZ).                (* [comment removed for export] *)
      zv F_7fe78 D_7fe78 (Z_to_bv 64 sy).                   (* [comment removed for export] *)
      zv F_7fe7c D_7fe7c (Z_to_bv 64 dy).                   (* [comment removed for export] *)
      sextw F_7fe80 D_7fe80 sy.                             (* [comment removed for export] *)
      stepb_ft F_7fe84 D_7fe84 ltac:(condZ).                (* [comment removed for export] *)
      zv F_7fe88 D_7fe88 (Z_to_bv 64 dy).                   (* [comment removed for export] *)
      sn F_7fe8c D_7fe8c.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_7fee8 D_7fee8 dh. sextw F_7feec D_7feec dy.
      zv F_7fef0 D_7fef0 (Z_to_bv 64 (dy + dh)). addw_v F_7fef4 D_7fef4 (dy + dh)%Z.
      stepb_tk F_7fef8 D_7fef8 ltac:(condR).
      sextw F_7ff00 D_7ff00 (dy + dh)%Z.
      subw_v F_7ff04 D_7ff04 (dy + dh - dpixh)%Z. zv F_7ff08 D_7ff08 (Z_to_bv 64 (dy + dh - dpixh)).
      stepb_tk F_7ff0c D_7ff0c ltac:(condR).
      stepb_tk F_7ff14 D_7ff14 ltac:(condS).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_7ff28 D_7ff28 dh. sextw F_7ff2c D_7ff2c sy.
      zv F_7ff30 D_7ff30 (Z_to_bv 64 (sy + dh)). addw_v F_7ff34 D_7ff34 (sy + dh)%Z.
      stepb_tk F_7ff38 D_7ff38 ltac:(condR).
      sextw F_7ff40 D_7ff40 (sy + dh)%Z.
      subw_v F_7ff44 D_7ff44 (sy + dh - spixh)%Z. zv F_7ff48 D_7ff48 (Z_to_bv 64 (sy + dh - spixh)).
      stepb_tk F_7ff4c D_7ff4c ltac:(condR).
      stepb_tk F_7ff54 D_7ff54 ltac:(condS).                (* [comment removed for export] *)
      sextw F_7ff68 D_7ff68 DW.                             (* [comment removed for export] *)
      stepb_tk F_7ff6c D_7ff6c ltac:(condZ).                (* [comment removed for export] *)
      sextw F_7ff74 D_7ff74 dh.                             (* [comment removed for export] *)
      stepST F_7ff78 D_7ff78 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 dh) ltac:(sokf).   (* [comment removed for export] *)
      fold M1a.
      stepb_tk F_7ff7c D_7ff7c ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma col_mods : (DX mod 32 = 0 /\ SX mod 32 = 0 /\ DW mod 32 = lw /\ DX / 32 = cd /\ SX / 32 = cs /\ DW / 32 = nf)%Z.
  Proof.
    destruct Hcol as (E1 & E2 & E3 & Hlw). rewrite E1, E2, E3.
    repeat split.
    - rewrite Z.mul_comm. apply Z_mod_mult.
    - rewrite Z.mul_comm. apply Z_mod_mult.
    - rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
    - rewrite Z.mul_comm. apply Z.div_mul. lia.
    - rewrite Z.mul_comm. apply Z.div_mul. lia.
    - rewrite Z.add_comm, Z.mul_comm, Z.div_add by lia. rewrite (Z.div_small lw 32) by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_A2 : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 25 = Z_to_bv 64 DX -> getr regs 27 = Z_to_bv 64 SX -> getr regs 6 = Z_to_bv 64 swpl ->
    getr regs 8 = Z_to_bv 64 DW ->
    exists regs',
      msteps SEGS (mkst regs (0x7ff84 : word) M1a rom) (mkst regs' (0x802fc : word) M2 rom)
      /\ getr regs' 12 = Z_to_bv 64 lw
      /\ regs_agree (fun r : reg => In r [12; 13; 15; 16; 28]%list) regs regs'.
  Proof.
    intros regs H2 H25 H27 H6 H8.
    pose proof bits_bounds as BB. pose proof col_mods as (MX & MS & MW & _).
    destruct (Z.eq_dec lw 0) as [E0 | NE0].
    - eexists. split.
      + sn F_7ff84 D_7ff84. sn F_7ff88 D_7ff88. fixv' (Z_to_bv 64 0) ltac:(apply or_andi31_0; lia).
        stepST F_7ff8c D_7ff8c (Z_to_bv 64 (s - 152)) (Z_to_bv 64 swpl) ltac:(apply sok_frame; [unfold M1a, M1; grows | cbn; lia]).
        fold M2.
        stepb_tk F_7ff90 D_7ff90 ltac:(condR).              (* [comment removed for export] *)
        sn F_80114 D_80114. fixv' (Z_to_bv 64 lw) ltac:(rewrite andi_31_Z by lia; rewrite MW; reflexivity).
        stepb_tk F_80118 D_80118 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; pin; reflexivity | solve_regs_agree].
    - destruct (lmask_read M2 lw ltac:(lia)) as (bs & Rbs & Lbs).
      eexists. split.
      + sn F_7ff84 D_7ff84. sn F_7ff88 D_7ff88. fixv' (Z_to_bv 64 0) ltac:(apply or_andi31_0; lia).
        stepST F_7ff8c D_7ff8c (Z_to_bv 64 (s - 152)) (Z_to_bv 64 swpl) ltac:(apply sok_frame; [unfold M1a, M1; grows | cbn; lia]).
        fold M2.
        stepb_tk F_7ff90 D_7ff90 ltac:(condR).
        sn F_80114 D_80114. fixv' (Z_to_bv 64 lw) ltac:(rewrite andi_31_Z by lia; rewrite MW; reflexivity).
        stepb_ft F_80118 D_80118 ltac:(condZ).
        sn F_8011c D_8011c. fixv' (Z_to_bv 64 (4 * lw)) ltac:(rewrite zbv_slli by lia; f_equal; lia).   (* [comment removed for export] *)
        sn F_80120 D_80120. sn F_80124 D_80124.             (* [comment removed for export] *)
        sn F_80128 D_80128.                                 (* [comment removed for export] *)
        stepb_tk F_8012c D_8012c ltac:(condZ).              (* [comment removed for export] *)
        sn F_80134 D_80134. fixv' (Z_to_bv 64 (0x1f4c4 + 4 * lw)) ltac:(rewrite zbv_add; reflexivity).   (* [comment removed for export] *)
        stepLD F_80138 D_80138 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
        sn F_8013c D_8013c.                                 (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; pin; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  #[local] Abbreviation RSd := (4 * (dwpl * dpixh))%Z (only parsing).
  #[local] Abbreviation RSs := (4 * (swpl * spixh))%Z (only parsing).
  Hypothesis Hdd : (4096 <= datad /\ datad + RSd + 8 <= 2 ^ 64 /\ datad mod 4 = 0)%Z.
  Hypothesis Hds : (4096 <= datas /\ datas + RSs + 8 <= 2 ^ 64 /\ datas mod 4 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis JT : rdn SEGS M (Z_to_bv 64 0x1f434) 4 = Some (Z_to_le_bytes 4 404972).

  #[local] Abbreviation PSF := (datas + 4 * (swpl * sy) + 4 * cs)%Z (only parsing).     (* [comment removed for export] *)
  #[local] Abbreviation PDF := (datad + 4 * (dwpl * dy) + 4 * cd)%Z (only parsing).     (* [comment removed for export] *)

  Lemma geom : (0 <= swpl * sy /\ swpl * sy + swpl <= swpl * spixh /\ swpl * spixh <= 400000000
               /\ 0 <= dwpl * dy /\ dwpl * dy + dwpl <= dwpl * dpixh /\ dwpl * dpixh <= 400000000
               /\ 0 <= cs /\ cs + nf + (if Z.eq_dec lw 0 then 0 else 1) <= swpl /\ 0 <= cd /\ cd + nf + (if Z.eq_dec lw 0 then 0 else 1) <= dwpl /\ 0 <= nf)%Z.
  Proof.
    pose proof bits_bounds as BB. destruct Hcol as (E1 & E2 & E3 & Hlw).
    assert (swpl * sy + swpl <= swpl * spixh)%Z by (replace (swpl * sy + swpl)%Z with (swpl * (sy + 1))%Z by lia; apply Z.mul_le_mono_nonneg_l; lia).
    assert (dwpl * dy + dwpl <= dwpl * dpixh)%Z by (replace (dwpl * dy + dwpl)%Z with (dwpl * (dy + 1))%Z by lia; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= swpl * sy)%Z by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= dwpl * dy)%Z by (apply Z.mul_nonneg_nonneg; lia).
    assert (swpl * spixh <= 400000000)%Z by (change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia).
    assert (dwpl * dpixh <= 400000000)%Z by (change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia).
    destruct (Z.eq_dec lw 0); lia.
  Qed.

  Lemma JT2 : rdn SEGS M2 (Z_to_bv 64 0x1f434) 4 = Some (Z_to_le_bytes 4 404972).
  Proof.
    unfold M2, M1a, M1. repeat (rewrite rdn_wbytes_out_Z by (zlen; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). exact JT.
  Qed.
  Lemma swpl_cell : rdn SEGS M2 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)).
  Proof. unfold M2. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.

  (* [comment removed for export] *)
  Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
  Ltac sltu0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
  Ltac slti0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
  Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
  Ltac slli2 F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  Ltac zand0 F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).

  (* [comment removed for export] *)
  Lemma rl_A3a : forall regs,
    getr regs 5 = Z_to_bv 64 sy -> getr regs 6 = Z_to_bv 64 swpl -> getr regs 7 = Z_to_bv 64 dy ->
    getr regs 10 = Z_to_bv 64 datad -> getr regs 14 = Z_to_bv 64 dwpl -> getr regs 19 = Z_to_bv 64 datas ->
    getr regs 25 = Z_to_bv 64 DX -> getr regs 27 = Z_to_bv 64 SX ->
    exists regs',
      msteps SEGS (mkst regs (0x802fc : word) M2 rom) (mkst regs' (0x803d8 : word) M2 rom)
      /\ getr regs' 17 = Z_to_bv 64 PSF /\ getr regs' 7 = Z_to_bv 64 PDF /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 5 = Z_to_bv 64 1
      /\ getr regs' 8 = Z_to_bv 64 (4 * (swpl * sy)) /\ getr regs' 18 = Z_to_bv 64 (4 * cs)
      /\ getr regs' 22 = Z_to_bv 64 (4 * (dwpl * dy)) /\ getr regs' 23 = Z_to_bv 64 (4 * cd)
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 8; 13; 15; 16; 17; 18; 22; 23]%list) regs regs'.
  Proof.
    intros regs H5 H6 H7 H10 H14 H19 H25 H27.
    pose proof bits_bounds as BB. pose proof col_mods as (MX & MS & MW & DXd & SXd & DWd). pose proof geom as G.
    assert (CC : (0 <= (if Z.eq_dec lw 0 then 0 else 1))%Z) by (destruct (Z.eq_dec lw 0); lia).
    eexists. split.
    - (* [comment removed for export] *)
      zv F_802fc D_802fc (Z_to_bv 64 (swpl * sy)).          (* [comment removed for export] *)
      mulw_v F_80300 D_80300 (Z_to_bv 64 (swpl * sy)).
      stepb_tk F_80304 D_80304 ltac:(condR).
      sextw F_8030c D_8030c (swpl * sy)%Z.
      slli2 F_80310 D_80310 (4 * (swpl * sy))%Z.            (* [comment removed for export] *)
      zv F_80314 D_80314 (Z_to_bv 64 (datas + 4 * (swpl * sy))).   (* [comment removed for export] *)
      snez1 F_80318 D_80318.                                (* [comment removed for export] *)
      seqz0 F_8031c D_8031c.                                (* [comment removed for export] *)
      stepb_tk F_80320 D_80320 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_80328 D_80328. slti0 F_8032c D_8032c. sn F_80330 D_80330. sn F_80334 D_80334.
      stepb_tk F_80338 D_80338 ltac:(condR).
      sn F_80340 D_80340. fixv' (Z_to_bv 64 cs) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite SXd; reflexivity).   (* [comment removed for export] *)
      slli2 F_80344 D_80344 (4 * cs)%Z.
      zv F_80348 D_80348 (Z_to_bv 64 PSF).                  (* [comment removed for export] *)
      stepb_tk F_8034c D_8034c ltac:(condZ).                (* [comment removed for export] *)
      seqz0 F_80354 D_80354. sn F_80358 D_80358.
      stepb_tk F_8035c D_8035c ltac:(condR).
      (* [comment removed for export] *)
      zv F_80364 D_80364 (Z_to_bv 64 (dwpl * dy)).          (* [comment removed for export] *)
      mulw_v F_80368 D_80368 (Z_to_bv 64 (dwpl * dy)).
      stepb_tk F_8036c D_8036c ltac:(condR).
      sextw F_80374 D_80374 (dwpl * dy)%Z.
      slli2 F_80378 D_80378 (4 * (dwpl * dy))%Z.            (* [comment removed for export] *)
      zv F_8037c D_8037c (Z_to_bv 64 (datad + 4 * (dwpl * dy))).   (* [comment removed for export] *)
      snez1 F_80380 D_80380.                                (* [comment removed for export] *)
      seqz0 F_80384 D_80384.
      stepb_tk F_80388 D_80388 ltac:(condR).
      sltu0 F_80390 D_80390. slti0 F_80394 D_80394. sn F_80398 D_80398. sn F_8039c D_8039c.
      stepb_tk F_803a0 D_803a0 ltac:(condR).
      sn F_803a8 D_803a8. fixv' (Z_to_bv 64 cd) ltac:(rewrite zbv_sraiw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite DXd; reflexivity).   (* [comment removed for export] *)
      slli2 F_803ac D_803ac (4 * cd)%Z.                     (* [comment removed for export] *)
      zv F_803b0 D_803b0 (Z_to_bv 64 PDF).                  (* [comment removed for export] *)
      seqz0 F_803b4 D_803b4.
      stepb_tk F_803b8 D_803b8 ltac:(condR).
      sltu0 F_803c0 D_803c0. slti0 F_803c4 D_803c4. sn F_803c8 D_803c8. sn F_803cc D_803cc.
      stepb_tk F_803d0 D_803d0 ltac:(condR).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_A3b : forall regs (mk : word),
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 17 = Z_to_bv 64 PSF -> getr regs 7 = Z_to_bv 64 PDF -> getr regs 16 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 (4 * (swpl * sy)) -> getr regs 18 = Z_to_bv 64 (4 * cs) ->
    getr regs 22 = Z_to_bv 64 (4 * (dwpl * dy)) -> getr regs 23 = Z_to_bv 64 (4 * cd) ->
    getr regs 9 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 12 -> getr regs 12 = Z_to_bv 64 lw ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 19 = Z_to_bv 64 datas -> getr regs 20 = Z_to_bv 64 SX -> getr regs 21 = Z_to_bv 64 DPW ->
    getr regs 27 = Z_to_bv 64 SX -> getr regs 28 = mk -> getr regs 29 = Z_to_bv 64 SPW ->
    getr regs 30 = Z_to_bv 64 DX -> getr regs 31 = Z_to_bv 64 (DX + DW - DPW) ->
    exists regs',
      msteps SEGS (mkst regs (0x803d8 : word) M2 rom) (mkst regs' (0x8228c : word) M2 rom)
      /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 (swpl * 0) /\ getr regs' 13 = Z_to_bv 64 (dwpl * 0)
      /\ getr regs' 27 = Z_to_bv 64 swpl /\ getr regs' 14 = Z_to_bv 64 dwpl /\ getr regs' 17 = Z_to_bv 64 PSF /\ getr regs' 7 = Z_to_bv 64 PDF
      /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 9 = Z_to_bv 64 DW /\ getr regs' 30 = Z_to_bv 64 32
      /\ getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 31 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 PDF /\ getr regs' 19 = Z_to_bv 64 PSF
      /\ getr regs' 29 = Z_to_bv 64 (- nf) /\ getr regs' 8 = Z_to_bv 64 18446744073709551611 /\ getr regs' 12 = Z_to_bv 64 lw
      /\ getr regs' 2 = Z_to_bv 64 (s - 240)
      /\ regs_agree (fun r : reg => In r [6; 8; 10; 11; 13; 15; 18; 19; 20; 21; 22; 25; 27; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs mk H2 H17 H7 H16 H5 H8 H18 H22 H23 H9 H10 H11 H12 H14 H19 H20 H21 H27 H28 H29 H30 H31.
    pose proof bits_bounds as BB. pose proof col_mods as (MX & MS & MW & DXd & SXd & DWd). pose proof geom as G.
    eexists. split.
    -
      (* [comment removed for export] *)
      sn F_803d8 D_803d8.
      zv F_803dc D_803dc (Z_to_bv 64 11).                   (* [comment removed for export] *)
      sn F_803e0 D_803e0. sn F_803e4 D_803e4.
      stepb_tk F_803e8 D_803e8 ltac:(condZ).                (* [comment removed for export] *)
      sn F_803f0 D_803f0. sn F_803f4 D_803f4. sn F_803f8 D_803f8.
      sn F_803fc D_803fc. fixv' (Z_to_bv 64 0x1f434) ltac:(apply bv_eq; reflexivity).
      stepLD F_80400 D_80400 (Z_to_le_bytes 4 404972) (Z_to_bv 64 404972) ltac:(addr_norm; rewrite ?Z.add_0_r; exact JT2) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 404972)) with (Z_to_bv 64 404972).
      sn F_80404 D_80404. fixv' (Z_to_bv 64 0x821f4) ltac:(apply bv_eq; reflexivity).
      stepret F_80408 D_80408 (0x821f4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_821f4 D_821f4. fixv' (Z_to_bv 64 (swpl * 0)) ltac:(f_equal; lia).     (* [comment removed for export] *)
      sn F_821f8 D_821f8. fixv' (Z_to_bv 64 (dwpl * 0)) ltac:(f_equal; lia).     (* [comment removed for export] *)
      sn F_821fc D_821fc.                                   (* [comment removed for export] *)
      zv F_82200 D_82200 (Z_to_bv 64 (SX + DPW)).           (* [comment removed for export] *)
      sn F_82204 D_82204.                                   (* [comment removed for export] *)
      zv F_82208 D_82208 (Z_to_bv 64 (4 * cd + 4 * (dwpl * dy))).   (* [comment removed for export] *)
      zand0 F_8220c D_8220c andi_3 (proj2 (proj2 Hds)).     (* [comment removed for export] *)
      zv F_82210 D_82210 (Z_to_bv 64 (4 * cs + 4 * (swpl * sy))).   (* [comment removed for export] *)
      sn F_82214 D_82214. sn F_82218 D_82218. fixv' (Z_to_bv 64 (DX + DW - DPW)) ltac:(apply and_srai63_np; lia).   (* [comment removed for export] *)
      zand0 F_8221c D_8221c andi_3 (proj2 (proj2 Hdd)).     (* [comment removed for export] *)
      subw_v F_82220 D_82220 (SPW - SX)%Z.                  (* [comment removed for export] *)
      subw_v F_82224 D_82224 (SX + DPW - DX)%Z.             (* [comment removed for export] *)
      sn F_82228 D_82228.                                   (* [comment removed for export] *)
      zv F_8222c D_8222c (Z_to_bv 64 PDF).                  (* [comment removed for export] *)
      zv F_82230 D_82230 (Z_to_bv 64 PSF).                  (* [comment removed for export] *)
      zv F_82234 D_82234 (Z_to_bv 64 (SX + DW)).            (* [comment removed for export] *)
      subw_v F_82238 D_82238 (SX + DW - SPW)%Z.             (* [comment removed for export] *)
      sn F_8223c D_8223c. sn F_82240 D_82240. fixv' (Z_to_bv 64 (SX + DW - SPW)) ltac:(apply and_srai63_np; lia).
      zv F_82244 D_82244 (Z_to_bv 64 DW).                   (* [comment removed for export] *)
      sn F_82248 D_82248. fixv' (Z_to_bv 64 nf) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite DWd; reflexivity).   (* [comment removed for export] *)
      zv F_8224c D_8224c (Z_to_bv 64 (- nf)).               (* [comment removed for export] *)
      sn F_82250 D_82250.                                   (* [comment removed for export] *)
      stepLD F_82254 D_82254 (word_to_le_bytes 8 (Z_to_bv 64 swpl)) (Z_to_bv 64 swpl) ltac:(rdn_addr (s - 152)%Z; exact swpl_cell) ltac:(apply bytes_le_to_Z_8).
      sn F_82258 D_82258.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SOKd : store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat RSd) = true.
  Hypothesis SOKs : store_ok SEGS M (Z_to_bv 64 datas) (Z.to_nat RSs) = true.
  Hypothesis FR : disj_apart datad RSd (s - 240) 240.

  Lemma wr_readable_v14 : wr_readable SEGS.
  Proof.
    intros seg Hin Hwr. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
  Qed.

  Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < datad \/ datad + RSd <= bv_unsigned x)%Z -> Mi x = M2 x) /\ mem_grows M2 Mi.
  Lemma Inv_M2 : Inv M2.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
  Lemma M2_grows : mem_grows M M2.
  Proof. unfold M2, M1a, M1. grows. Qed.

  Lemma Inv_store : forall Mi (a : Z) (bs : list byte),
    Inv Mi -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + RSd)%Z -> Inv (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Lemma Inv_sok : forall Mi (a : Z) (n : nat), Inv Mi -> (datad <= a)%Z -> (a + Z.of_nat n <= datad + RSd)%Z ->
    store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi a n [_ HG] Ha Hn. eapply store_ok_mono; [eapply mem_grows_trans; [exact M2_grows | exact HG]|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 datad) _ (Z.to_nat RSd)); [ | exact SOKd | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd4 : forall Mi base RS (a : Z), Inv Mi -> store_ok SEGS M (Z_to_bv 64 base) (Z.to_nat RS) = true ->
    (0 <= base /\ base + RS <= 2 ^ 64)%Z -> (base <= a)%Z -> (a + 4 <= base + RS)%Z ->
    exists bs, rdn SEGS Mi (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros Mi base RS a [_ HG] SOK Hb Ha H4.
    apply (store_ok_rdn SEGS Mi 4 (Z_to_bv 64 a) wr_readable_v14).
    eapply store_ok_mono; [eapply mem_grows_trans; [exact M2_grows | exact HG]|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma dh_cell : rdn SEGS M2 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Proof.
    unfold M2. rewrite rdn_wbytes_out_Z by (zlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    unfold M1a. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
  Qed.
  Lemma Inv_dh : forall Mi, Inv Mi -> rdn SEGS Mi (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Proof.
    intros Mi [HI _]. use_apart FR. rewrite <- dh_cell.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  #[local] Abbreviation SR i := (datas + 4 * (swpl * sy) + 4 * cs + 4 * (swpl * i))%Z (only parsing).   (* [comment removed for export] *)
  #[local] Abbreviation DR i := (datad + 4 * (dwpl * dy) + 4 * cd + 4 * (dwpl * i))%Z (only parsing).

  (* [comment removed for export] *)
  Lemma row_in : forall i, (0 <= i < dh)%Z ->
    (0 <= swpl * i <= 400000000 /\ 0 <= dwpl * i <= 400000000
     /\ swpl * sy + swpl * i + swpl <= swpl * spixh /\ dwpl * dy + dwpl * i + dwpl <= dwpl * dpixh)%Z.
  Proof.
    intros i Hi.
    assert (0 <= swpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= dwpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia).
    assert (swpl * i <= 400000000)%Z by (change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia).
    assert (dwpl * i <= 400000000)%Z by (change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia).
    assert (swpl * (sy + i + 1) <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (dwpl * (dy + i + 1) <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  Definition LInv (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 27 = Z_to_bv 64 swpl /\ getr regs 14 = Z_to_bv 64 dwpl /\
    getr regs 17 = Z_to_bv 64 PSF /\ getr regs 7 = Z_to_bv 64 PDF /\ getr regs 16 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 1 /\
    getr regs 9 = Z_to_bv 64 DW /\ getr regs 30 = Z_to_bv 64 32 /\ getr regs 21 = Z_to_bv 64 0 /\ getr regs 31 = Z_to_bv 64 0 /\
    getr regs 10 = Z_to_bv 64 PDF /\ getr regs 19 = Z_to_bv 64 PSF /\ getr regs 29 = Z_to_bv 64 (- nf) /\
    getr regs 8 = Z_to_bv 64 18446744073709551611 /\ getr regs 12 = Z_to_bv 64 lw.

  Lemma LInv_agree : forall regs regs',
    regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26]%list) regs regs' -> LInv regs -> LInv regs'.
  Proof.
    intros regs regs' AG (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12).
    unfold LInv. repeat split; match goal with |- getr regs' ?r = _ => rewrite (AG r ltac:(notin_list)); assumption end.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_H : forall regs Mi i, (0 <= i < dh)%Z -> LInv regs -> getr regs 25 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x8228c : word) Mi rom) (mkst regs' (0x822f4 : word) Mi rom)
      /\ getr regs' 15 = Z_to_bv 64 (SR i) /\ getr regs' 18 = Z_to_bv 64 (DR i)
      /\ regs_agree (fun r : reg => In r [6; 15; 18; 22]%list) regs regs'.
  Proof.
    intros regs Mi i Hi (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H25.
    pose proof (row_in i Hi) as RI. pose proof geom as G.
    assert (CC : (0 <= (if Z.eq_dec lw 0 then 0 else 1))%Z) by (destruct (Z.eq_dec lw 0); lia).
    eexists. split.
    - zv F_8228c D_8228c (Z_to_bv 64 (swpl * i)).           (* [comment removed for export] *)
      mulw_v F_82290 D_82290 (Z_to_bv 64 (swpl * i)).
      stepb_ft F_82294 D_82294 ltac:(condR).                (* [comment removed for export] *)
      sextw F_82298 D_82298 (swpl * i)%Z.
      slli2 F_8229c D_8229c (4 * (swpl * i))%Z.
      zv F_822a0 D_822a0 (Z_to_bv 64 (SR i)).               (* [comment removed for export] *)
      seqz0 F_822a4 D_822a4.
      stepb_ft F_822a8 D_822a8 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_822ac D_822ac. slti0 F_822b0 D_822b0. sn F_822b4 D_822b4. sn F_822b8 D_822b8.
      stepb_ft F_822bc D_822bc ltac:(condR).
      zv F_822c0 D_822c0 (Z_to_bv 64 (dwpl * i)).           (* [comment removed for export] *)
      mulw_v F_822c4 D_822c4 (Z_to_bv 64 (dwpl * i)).
      stepb_ft F_822c8 D_822c8 ltac:(condR).
      sextw F_822cc D_822cc (dwpl * i)%Z.
      slli2 F_822d0 D_822d0 (4 * (dwpl * i))%Z.
      zv F_822d4 D_822d4 (Z_to_bv 64 (DR i)).               (* [comment removed for export] *)
      seqz0 F_822d8 D_822d8.
      stepb_ft F_822dc D_822dc ltac:(condR).
      sltu0 F_822e0 D_822e0. slti0 F_822e4 D_822e4. sn F_822e8 D_822e8. sn F_822ec D_822ec.
      stepb_ft F_822f0 D_822f0 ltac:(condR).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ptr_mod4 : forall i k, ((DR i + 4 * k) mod 4 = 0 /\ (SR i + 4 * k) mod 4 = 0)%Z.
  Proof.
    intros i k. split.
    - replace (DR i + 4 * k)%Z with (datad + (dwpl * dy + cd + dwpl * i + k) * 4)%Z by lia. rewrite Z_mod_plus_full. exact (proj2 (proj2 Hdd)).
    - replace (SR i + 4 * k)%Z with (datas + (swpl * sy + cs + swpl * i + k) * 4)%Z by lia. rewrite Z_mod_plus_full. exact (proj2 (proj2 Hds)).
  Qed.

  (* [comment removed for export] *)
  Lemma rl_F0 : forall regs Mi i, (0 <= i < dh)%Z -> (32 <= DW)%Z -> LInv regs ->
    getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x822f4 : word) Mi rom) (mkst regs' (0x82314 : word) Mi rom)
      /\ getr regs' 15 = Z_to_bv 64 (4 * 0) /\ getr regs' 18 = Z_to_bv 64 (DR i) /\ getr regs' 22 = Z_to_bv 64 (SR i) /\ getr regs' 23 = Z_to_bv 64 (- (nf - 0))
      /\ regs_agree (fun r : reg => In r [15; 18; 22; 23]%list) regs regs'.
  Proof.
    intros regs Mi i Hi H32 (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H11 H13.
    pose proof (row_in i Hi) as RI. pose proof bits_bounds as BB.
    eexists. split.
    - stepb_ft F_822f4 D_822f4 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_822f8 D_822f8 ltac:(condR).                (* [comment removed for export] *)
      sn F_822fc D_822fc. fixv' (Z_to_bv 64 (4 * 0)) ltac:(reflexivity).   (* [comment removed for export] *)
      slli2 F_82300 D_82300 (4 * (dwpl * i))%Z.             (* [comment removed for export] *)
      slli2 F_82304 D_82304 (4 * (swpl * i))%Z.             (* [comment removed for export] *)
      zv F_82308 D_82308 (Z_to_bv 64 (DR i)).               (* [comment removed for export] *)
      zv F_8230c D_8230c (Z_to_bv 64 (SR i)).               (* [comment removed for export] *)
      zv F_82310 D_82310 (Z_to_bv 64 (- (nf - 0))).         (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_W : forall regs Mi i k, (0 <= i < dh)%Z -> (0 <= k < nf)%Z -> Inv Mi -> LInv regs ->
    getr regs 15 = Z_to_bv 64 (4 * k) -> getr regs 18 = Z_to_bv 64 (DR i) -> getr regs 22 = Z_to_bv 64 (SR i) -> getr regs 23 = Z_to_bv 64 (- (nf - k)) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x82314 : word) Mi rom) (mkst regs' (0x82340 : word) M' rom)
      /\ Inv M' /\ getr regs' 15 = Z_to_bv 64 (4 * (k + 1)) /\ getr regs' 23 = Z_to_bv 64 (- (nf - (k + 1)))
      /\ regs_agree (fun r : reg => In r [6; 15; 23; 24; 26]%list) regs regs'.
  Proof.
    intros regs Mi i k Hi Hk HIv (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H15 H18 H22 H23.
    pose proof (row_in i Hi) as RI. pose proof geom as G.
    assert (CC : (0 <= (if Z.eq_dec lw 0 then 0 else 1))%Z) by (destruct (Z.eq_dec lw 0); lia).
    destruct (rd4 Mi datas RSs (SR i + 4 * k) HIv SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Rbs & Lbs).
    eexists. eexists. split; [|split; [|split; [|split]]].
    - zv F_82314 D_82314 (Z_to_bv 64 (SR i + 4 * k)).       (* [comment removed for export] *)
      stepb_ft F_82318 D_82318 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_8231c D_8231c ltac:(condR).                (* [comment removed for export] *)
      zv F_82320 D_82320 (Z_to_bv 64 (DR i + 4 * k)).       (* [comment removed for export] *)
      stepb_ft F_82324 D_82324 ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_82328 D_82328 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
      stepST F_8232c D_8232c (Z_to_bv 64 (DR i + 4 * k)) (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) ltac:(apply (Inv_sok _ _ 4 HIv); [lia | cbn; lia]).
      stepb_ft F_82330 D_82330 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_82334 D_82334 ltac:(condZ).                (* [comment removed for export] *)
      sn F_82338 D_82338. fixv' (Z_to_bv 64 (- (nf - (k + 1)))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).   (* [comment removed for export] *)
      zv F_8233c D_8233c (Z_to_bv 64 (4 * (k + 1))).        (* [comment removed for export] *)
      apply mst_refl.
    - apply Inv_store; [exact HIv | lia | rewrite length_N_to_le_bytes; cbn; lia].
    - gres; pin; reflexivity.
    - gres; pin; reflexivity.
    - solve_regs_agree.
  Qed.

  Ltac condSe := pin; rewrite ?c_eq_Zs by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

  (* [comment removed for export] *)
  Lemma rl_words : forall (j : nat) regs Mi i k, (0 <= i < dh)%Z -> (0 <= k)%Z -> (k + Z.of_nat j = nf - 1)%Z -> Inv Mi -> LInv regs ->
    getr regs 15 = Z_to_bv 64 (4 * k) -> getr regs 18 = Z_to_bv 64 (DR i) -> getr regs 22 = Z_to_bv 64 (SR i) -> getr regs 23 = Z_to_bv 64 (- (nf - k)) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x82314 : word) Mi rom) (mkst regs' (0x8234c : word) M' rom)
      /\ Inv M' /\ getr regs' 15 = Z_to_bv 64 (SR i + 4 * nf) /\ getr regs' 18 = Z_to_bv 64 (DR i + 4 * nf)
      /\ regs_agree (fun r : reg => In r [6; 15; 18; 23; 24; 26]%list) regs regs'.
  Proof.
    induction j as [|j IH]; intros regs Mi i k Hi Hk Hj HIv LI H15 H18 H22 H23;
      destruct (rl_W regs Mi i k Hi ltac:(lia) HIv LI H15 H18 H22 H23) as (r1 & Ma & S1 & HI1 & A15 & A23 & AG1);
      pose proof (AG1 18 ltac:(notin_list)) as A18; rewrite H18 in A18;
      pose proof (AG1 22 ltac:(notin_list)) as A22; rewrite H22 in A22.
    - eexists. exists Ma. split; [|split; [exact HI1 | split; [|split]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_82340 D_82340 ltac:(condSe).             (* [comment removed for export] *)
        zv F_82344 D_82344 (Z_to_bv 64 (DR i + 4 * nf)).    (* [comment removed for export] *)
        zv F_82348 D_82348 (Z_to_bv 64 (SR i + 4 * nf)).    (* [comment removed for export] *)
        apply mst_refl.
      + gres; pin; reflexivity.
      + gres; pin; reflexivity.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (L1 : LInv r1) by (apply (LInv_agree regs); [regs_agree_weaken AG1 | exact LI]).
      destruct (IH r1 Ma i (k + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 L1 A15 A18 A22 A23) as (r2 & Mb & S2 & HI2 & B15 & B18 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B15 | split; [exact B18|]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_82340 D_82340 ltac:(condSe).
        exact S2.
      + eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma rl_P : forall regs Mi i n, (0 <= i < dh)%Z -> (n = nf)%Z -> Inv Mi -> LInv regs ->
    getr regs 15 = Z_to_bv 64 (SR i + 4 * n) -> getr regs 18 = Z_to_bv 64 (DR i + 4 * n) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x8234c : word) Mi rom) (mkst regs' (0x82274 : word) M' rom)
      /\ Inv M'
      /\ regs_agree (fun r : reg => In r [6; 15]%list) regs regs'.
  Proof.
    intros regs Mi i n Hi -> HIv (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H15 H18.
    pose proof (row_in i Hi) as RI. pose proof geom as G. pose proof (ptr_mod4 i nf) as (MD & MS).
    assert (Hlw : (0 <= lw < 32)%Z) by (destruct Hcol as (_ & _ & _ & X); exact X).
    destruct (Z.eq_dec lw 0) as [E0 | NE0].
    - exists regs, Mi. split; [|split; [exact HIv | apply regs_agree_refl]].
      stepb_tk F_8234c D_8234c ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - destruct (rd4 Mi datad RSd (DR i + 4 * nf) HIv SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rbd & Lbd).
      destruct (rd4 Mi datas RSs (SR i + 4 * nf) HIv SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Rbs & Lbs).
      eexists. eexists. split; [|split].
      + stepb_ft F_8234c D_8234c ltac:(condZ).
        stepb_ft F_82350 D_82350 ltac:(condZ).              (* [comment removed for export] *)
        zand0 F_82354 D_82354 andi_3 MD.                    (* [comment removed for export] *)
        stepb_ft F_82358 D_82358 ltac:(condR).              (* [comment removed for export] *)
        stepb_ft F_8235c D_8235c ltac:(condZ).              (* [comment removed for export] *)
        zand0 F_82360 D_82360 andi_3 MS.                    (* [comment removed for export] *)
        stepb_tk F_82364 D_82364 ltac:(condR).              (* [comment removed for export] *)
        stepLD F_8225c D_8225c bd (Z_to_bv 64 (bytes_le_to_Z bd)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbd) ltac:(symmetry; apply u_lez4; exact Lbd).
        stepLD F_82260 D_82260 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
        sn F_82264 D_82264. sn F_82268 D_82268. sn F_8226c D_8226c.
        chain_step; [ reflexivity
                    | eapply step_sw_at with (a := Z_to_bv 64 (DR i + 4 * nf));
                      [ exact F_82270 | reflexivity | exact D_82270 | gres; imm_norm; addr_tac | gres; reflexivity
                      | apply (Inv_sok _ _ 4 HIv); [lia | cbn; lia] ]
                    | step_simpl ].                         (* [comment removed for export] *)
        apply mst_refl.
      + apply Inv_store; [exact HIv | lia | rewrite length_N_to_le_bytes; cbn; lia].
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_N : forall regs Mi i, (0 <= i < dh)%Z -> Inv Mi -> LInv regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x82274 : word) Mi rom) (mkst regs' (0x82284 : word) Mi rom)
      /\ getr regs' 25 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (swpl * (i + 1)) /\ getr regs' 13 = Z_to_bv 64 (dwpl * (i + 1))
      /\ getr regs' 15 = Z_to_bv 64 dh
      /\ regs_agree (fun r : reg => In r [11; 13; 15; 25]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H25 H11 H13.
    pose proof (row_in i Hi) as RI.
    assert (swpl * (i + 1) <= 400020000 /\ dwpl * (i + 1) <= 400020000)%Z by lia.
    eexists. split.
    - sextw F_82274 D_82274 (i + 1)%Z.                      (* [comment removed for export] *)
      addw_v F_82278 D_82278 (dwpl * (i + 1))%Z.            (* [comment removed for export] *)
      addw_v F_8227c D_8227c (swpl * (i + 1))%Z.            (* [comment removed for export] *)
      stepLD F_82280 D_82280 (word_to_le_bytes 8 (Z_to_bv 64 dh)) (Z_to_bv 64 dh) ltac:(rdn_addr (s - 112)%Z; exact (Inv_dh Mi HIv)) ltac:(apply bytes_le_to_Z_8).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_row : forall regs Mi i, (0 <= i < dh)%Z -> Inv Mi -> LInv regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x8228c : word) Mi rom) (mkst regs' (0x82284 : word) M' rom)
      /\ Inv M' /\ LInv regs'
      /\ getr regs' 25 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (swpl * (i + 1)) /\ getr regs' 13 = Z_to_bv 64 (dwpl * (i + 1))
      /\ getr regs' 15 = Z_to_bv 64 dh
      /\ regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv LI H25 H11 H13.
    pose proof bits_bounds as BB. pose proof geom as G.
    assert (Hlw : (0 <= lw < 32)%Z) by (destruct Hcol as (_ & _ & _ & X); exact X).
    assert (EDW3 : (DW = 32 * nf + lw)%Z) by (destruct Hcol as (_ & _ & X & _); exact X).
    destruct (rl_H regs Mi i Hi LI H25) as (r1 & S1 & A15 & A18 & AG1).
    assert (L1 : LInv r1) by (apply (LInv_agree regs); [regs_agree_weaken AG1 | exact LI]).
    pose proof (AG1 11 ltac:(notin_list)) as A11; rewrite H11 in A11.
    pose proof (AG1 13 ltac:(notin_list)) as A13; rewrite H13 in A13.
    pose proof (AG1 25 ltac:(notin_list)) as A25; rewrite H25 in A25.
    (* [comment removed for export] *)
    assert (MID : exists r2 Ma, msteps SEGS (mkst r1 (0x822f4 : word) Mi rom) (mkst r2 (0x8234c : word) Ma rom)
                    /\ Inv Ma /\ getr r2 15 = Z_to_bv 64 (SR i + 4 * nf) /\ getr r2 18 = Z_to_bv 64 (DR i + 4 * nf)
                    /\ regs_agree (fun r : reg => In r [6; 15; 18; 22; 23; 24; 26]%list) r1 r2).
    { destruct (Z_lt_ge_dec DW 32) as [Hs32 | Hf32].
      - assert (Enf0 : (nf = 0)%Z) by lia.
        exists r1, Mi. split; [|split; [exact HIv | split; [|split; [|apply regs_agree_refl]]]].
        + destruct L1 as (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & _).
          stepb_tk F_822f4 D_822f4 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        + rewrite A15. f_equal. lia.
        + rewrite A18. f_equal. lia.
      - destruct (rl_F0 r1 Mi i Hi ltac:(lia) L1 A11 A13) as (r2 & S2 & B15 & B18 & B22 & B23 & AG2).
        assert (L2 : LInv r2) by (apply (LInv_agree r1); [regs_agree_weaken AG2 | exact L1]).
        destruct (rl_words (Z.to_nat (nf - 1)) r2 Mi i 0 Hi ltac:(lia) ltac:(lia) HIv L2 B15 B18 B22 B23) as (r3 & Ma & S3 & HI3 & C15 & C18 & AG3).
        exists r3, Ma. split; [eapply msteps_trans; [exact S2 | exact S3]|]. split; [exact HI3|]. split; [exact C15|]. split; [exact C18|].
        eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]. }
    destruct MID as (r2 & Ma & S2 & HI2 & B15 & B18 & AG2).
    assert (L2 : LInv r2) by (apply (LInv_agree r1); [regs_agree_weaken AG2 | exact L1]).
    destruct (rl_P r2 Ma i nf Hi eq_refl HI2 L2 B15 B18) as (r3 & Mb & S3 & HI3 & AG3).
    assert (L3 : LInv r3) by (apply (LInv_agree r2); [regs_agree_weaken AG3 | exact L2]).
    pose proof (AG3 25 ltac:(notin_list)) as C25; rewrite (AG2 25 ltac:(notin_list)), A25 in C25.
    pose proof (AG3 11 ltac:(notin_list)) as C11; rewrite (AG2 11 ltac:(notin_list)), A11 in C11.
    pose proof (AG3 13 ltac:(notin_list)) as C13; rewrite (AG2 13 ltac:(notin_list)), A13 in C13.
    destruct (rl_N r3 Mb i Hi HI3 L3 C25 C11 C13) as (r4 & S4 & D25 & D11 & D13 & D15 & AG4).
    assert (L4 : LInv r4) by (apply (LInv_agree r3); [regs_agree_weaken AG4 | exact L3]).
    exists r4, Mb. split; [|split; [exact HI3 | split; [exact L4 | split; [exact D25 | split; [exact D11 | split; [exact D13 | split; [exact D15|]]]]]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3 | exact S4].
    - eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|].
      eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4].
  Qed.

  (* [comment removed for export] *)
  Lemma rl_rows : forall (k : nat) regs Mi i, (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv Mi -> LInv regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x8228c : word) Mi rom) (mkst regs' (0x875b8 : word) M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 (s - 240)
      /\ regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv LI H25 H11 H13;
      destruct (rl_row regs Mi i ltac:(lia) HIv LI H25 H11 H13) as (r1 & Ma & S1 & HI1 & L1 & A25 & A11 & A13 & A15 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact (proj1 L1) | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_82284 D_82284 ltac:(condZ).                (* [comment removed for export] *)
      sn F_82288 D_82288.                                   (* [comment removed for export] *)
      apply mst_refl.
    - destruct (IH r1 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 L1 A25 A11 A13) as (r2 & Mb & S2 & HI2 & B2 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B2|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_82284 D_82284 ltac:(condZ).
        exact S2.
      + eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Inv_rdn_frame : forall Mi (a : Z) (n : nat) bs, Inv Mi -> (s - 240 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
    rdn SEGS M2 (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros Mi a n bs [HI _] Ha Hn HM. use_apart FR. rewrite <- HM.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
  Qed.
  Lemma F_ra : rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ra). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s0v : rdn SEGS M2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s1v : rdn SEGS M2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s2v : rdn SEGS M2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s3v : rdn SEGS M2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s4v : rdn SEGS M2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s5v : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s6v : rdn SEGS M2 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 s6v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s7v : rdn SEGS M2 (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 s7v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s8v : rdn SEGS M2 (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 s8v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s9v : rdn SEGS M2 (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 s9v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s10v : rdn SEGS M2 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 s10v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Lemma F_s11v : rdn SEGS M2 (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 s11v). Proof. unfold M2, M1a, M1. rdn_chain. Qed.
  Ltac ldsv F D k v FL HIv :=
    stepLD F D (word_to_le_bytes 8 v) v
      ltac:(rdn_addr (s - k)%Z; apply (Inv_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact FL])
      ltac:(apply bytes_le_to_Z_8).

  Lemma rl_E : forall regs Mi, Inv Mi -> getr regs 2 = Z_to_bv 64 (s - 240) ->
    exists regs',
      msteps SEGS (mkst regs (0x875b8 : word) Mi rom) (mkst regs' ra Mi rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2.
    eexists. split.
    -
      ldsv F_875b8 D_875b8 8%Z ra F_ra HIv.
      ldsv F_875bc D_875bc 16%Z s0v F_s0v HIv.
      ldsv F_875c0 D_875c0 24%Z s1v F_s1v HIv.
      ldsv F_875c4 D_875c4 32%Z s2v F_s2v HIv.
      ldsv F_875c8 D_875c8 40%Z s3v F_s3v HIv.
      ldsv F_875cc D_875cc 48%Z s4v F_s4v HIv.
      ldsv F_875d0 D_875d0 56%Z s5v F_s5v HIv.
      ldsv F_875d4 D_875d4 64%Z s6v F_s6v HIv.
      ldsv F_875d8 D_875d8 72%Z s7v F_s7v HIv.
      ldsv F_875dc D_875dc 80%Z s8v F_s8v HIv.
      ldsv F_875e0 D_875e0 88%Z s9v F_s9v HIv.
      ldsv F_875e4 D_875e4 96%Z s10v F_s10v HIv.
      ldsv F_875e8 D_875e8 104%Z s11v F_s11v HIv.
      zv F_875ec D_875ec (Z_to_bv 64 s).                    (* [comment removed for export] *)
      stepret F_875f0 D_875f0 ra ltac:(reflexivity).        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma M2_outside : forall x : word, (bv_unsigned x < s - 240 \/ s <= bv_unsigned x)%Z -> M2 x = M x.
  Proof.
    intros x Hx. unfold M2, M1a, M1.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem rl_run : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 s ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 22 = s6v -> getr regs 23 = s7v -> getr regs 24 = s8v -> getr regs 25 = s9v -> getr regs 26 = s10v -> getr regs 27 = s11v ->
    getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
    exists regs' M',
      msteps SEGS (mkst regs (0x7fc9c : word) M rom) (mkst regs' ra M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12 H13 H14 H15 H16 H17.
    destruct (rl_A0 regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12 H13 H14 H15 H16 H17)
      as (r1 & S1 & A2 & A10 & A14 & A16 & A23 & A26 & A20 & A6 & A28 & A29 & A19 & A11 & A22 & A30 & A8 & A21 & AG1).
    destruct (rl_A1 r1 A2 A16 A23 A26 A20 A28 A29 A22 A30 A8 A21) as (r2 & S2 & B31 & B9 & B25 & B27 & B5 & B7 & AG2).
    pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2.
    pose proof (AG2 6 ltac:(notin_list)) as B6; rewrite A6 in B6.
    pose proof (AG2 8 ltac:(notin_list)) as B8; rewrite A8 in B8.
    destruct (rl_A2 r2 B2 B25 B27 B6 B8) as (r3 & S3 & C12 & AG3).
    assert (AG23 : regs_agree (fun r : reg => In r [1; 5; 7; 9; 12; 13; 15; 16; 17; 18; 22; 24; 25; 27; 28; 31]%list) r1 r3)
      by (eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
    pose proof (AG3 2 ltac:(notin_list)) as C2; rewrite B2 in C2.
    pose proof (AG3 5 ltac:(notin_list)) as C5; rewrite B5 in C5.
    pose proof (AG3 6 ltac:(notin_list)) as C6; rewrite B6 in C6.
    pose proof (AG3 7 ltac:(notin_list)) as C7; rewrite B7 in C7.
    pose proof (AG3 9 ltac:(notin_list)) as C9; rewrite B9 in C9.
    pose proof (AG23 10 ltac:(notin_list)) as C10; rewrite A10 in C10.
    pose proof (AG23 11 ltac:(notin_list)) as C11; rewrite A11 in C11.
    pose proof (AG23 14 ltac:(notin_list)) as C14; rewrite A14 in C14.
    pose proof (AG23 19 ltac:(notin_list)) as C19; rewrite A19 in C19.
    pose proof (AG23 20 ltac:(notin_list)) as C20; rewrite A20 in C20.
    pose proof (AG23 21 ltac:(notin_list)) as C21; rewrite A21 in C21.
    pose proof (AG3 25 ltac:(notin_list)) as C25; rewrite B25 in C25.
    pose proof (AG3 27 ltac:(notin_list)) as C27; rewrite B27 in C27.
    pose proof (AG23 29 ltac:(notin_list)) as C29; rewrite A29 in C29.
    pose proof (AG23 30 ltac:(notin_list)) as C30; rewrite A30 in C30.
    pose proof (AG3 31 ltac:(notin_list)) as C31; rewrite B31 in C31.
    destruct (rl_A3a r3 C5 C6 C7 C10 C14 C19 C25 C27) as (r3a & S3a & Y17 & Y7 & Y16 & Y5 & Y8 & Y18 & Y22 & Y23 & AG3a).
    pose proof (AG3a 2 ltac:(notin_list)) as Y2; rewrite C2 in Y2.
    pose proof (AG3a 9 ltac:(notin_list)) as Y9; rewrite C9 in Y9.
    pose proof (AG3a 10 ltac:(notin_list)) as Y10; rewrite C10 in Y10.
    pose proof (AG3a 11 ltac:(notin_list)) as Y11; rewrite C11 in Y11.
    pose proof (AG3a 12 ltac:(notin_list)) as Y12; rewrite C12 in Y12.
    pose proof (AG3a 14 ltac:(notin_list)) as Y14; rewrite C14 in Y14.
    pose proof (AG3a 19 ltac:(notin_list)) as Y19; rewrite C19 in Y19.
    pose proof (AG3a 20 ltac:(notin_list)) as Y20; rewrite C20 in Y20.
    pose proof (AG3a 21 ltac:(notin_list)) as Y21; rewrite C21 in Y21.
    pose proof (AG3a 27 ltac:(notin_list)) as Y27; rewrite C27 in Y27.
    pose proof (AG3a 29 ltac:(notin_list)) as Y29; rewrite C29 in Y29.
    pose proof (AG3a 30 ltac:(notin_list)) as Y30; rewrite C30 in Y30.
    pose proof (AG3a 31 ltac:(notin_list)) as Y31; rewrite C31 in Y31.
    destruct (rl_A3b r3a (getr r3a 28) Y2 Y17 Y7 Y16 Y5 Y8 Y18 Y22 Y23 Y9 Y10 Y11 Y12 Y14 Y19 Y20 Y21 Y27 eq_refl Y29 Y30 Y31)
      as (r4 & S4b & D25 & D11 & D13 & D27 & D14 & D17 & D7 & D16 & D5 & D9 & D30 & D21 & D31 & D10 & D19 & D29 & D8 & D12 & D2 & AG4b).
    assert (S4 : msteps SEGS (mkst r3 (0x802fc : word) M2 rom) (mkst r4 (0x8228c : word) M2 rom)) by (eapply msteps_trans; [exact S3a | exact S4b]).
    assert (AG4 : regs_agree (fun r : reg => In r [5; 6; 7; 8; 10; 11; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 27; 29; 30; 31]%list) r3 r4)
      by (eapply regs_agree_trans; [regs_agree_weaken AG3a | regs_agree_weaken AG4b]).
    assert (L4 : LInv r4) by (unfold LInv; repeat split; assumption).
    destruct (rl_rows (Z.to_nat (dh - 1)) r4 M2 0 ltac:(lia) ltac:(lia) Inv_M2 L4 D25 D11 D13) as (r5 & M5 & S5 & HI5 & E2 & AG5).
    destruct (rl_E r5 M5 HI5 E2) as (r6 & S6 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & AG6).
    exists r6, M5. split.
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
      eapply msteps_trans; [exact S4|]. eapply msteps_trans; [exact S5 | exact S6].
    - split; [exact HI5|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG23|].
      eapply regs_agree_trans; [regs_agree_weaken AG4|]. eapply regs_agree_trans; [regs_agree_weaken AG5 | regs_agree_weaken AG6].
  Qed.

End RL.
