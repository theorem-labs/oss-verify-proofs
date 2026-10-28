(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 LeptRop GrayLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_rasteropLow_27f50_29000 V2_code_rasteropLow_29000_2a000 V2_code_rasteropLow_2a000_2b000 V2_code_rasteropLow_2b000_2c000 V2_code_rasteropLow_2c000_2d000 V2_code_rasteropLow_2d000_2e000 V2_code_rasteropLow_2e000_2f000 V2_code_rasteropLow_2f000_2f8a8.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma lmask_tbl : exists T, rdn SEGS (fun _ => None) (Z_to_bv 64 0x12970) 132 = Some T.
Proof. img_exists. Qed.
Lemma lmask_read : forall m e, (0 <= e <= 32)%Z ->
  exists bs, rdn SEGS m (Z_to_bv 64 (0x12970 + 4 * e)) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros m e He. destruct lmask_tbl as [T HT].
  pose proof (rdn_sub SEGS (fun _ => None) 132 (Z_to_bv 64 0x12970) T (Z.to_nat (4 * e)) 4 HT ltac:(lia)) as HS.
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
      msteps SEGS (mkst regs (0x27f50 : word) M rom) (mkst regs' (0x27fcc : word) M1 rom)
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
      zv F_27f50 D_27f50 (Z_to_bv 64 (s - 240));
      stf F_27f54 D_27f54 8%Z ra; stf F_27f58 D_27f58 16%Z s0v; stf F_27f5c D_27f5c 24%Z s1v; stf F_27f60 D_27f60 32%Z s2v;
      stf F_27f64 D_27f64 40%Z s3v; stf F_27f68 D_27f68 48%Z s4v; stf F_27f6c D_27f6c 56%Z s5v; stf F_27f70 D_27f70 64%Z s6v;
      stf F_27f74 D_27f74 72%Z s7v; stf F_27f78 D_27f78 80%Z s8v; stf F_27f7c D_27f7c 88%Z s9v; stf F_27f80 D_27f80 96%Z s10v;
      stf F_27f84 D_27f84 104%Z s11v;
      fold M1;
      zv F_27f88 D_27f88 (Z_to_bv 64 dpixh);                (* [comment removed for export] *)
      zv F_27f8c D_27f8c (Z_to_bv 64 dpixw);                (* [comment removed for export] *)
      unfold M1;
      ldarg F_27f90 D_27f90 sy A_sy;                        (* [comment removed for export] *)
      ldarg F_27f94 D_27f94 sx A_sx;                        (* [comment removed for export] *)
      ldarg F_27f98 D_27f98 swpl A_swpl;                    (* [comment removed for export] *)
      ldarg F_27f9c D_27f9c spixh A_spixh;                  (* [comment removed for export] *)
      ldarg F_27fa0 D_27fa0 spixw A_spixw;                  (* [comment removed for export] *)
      ldarg F_27fa4 D_27fa4 datas A_datas;                  (* [comment removed for export] *)
      ldarg F_27fa8 D_27fa8 12%Z A_op;                      (* [comment removed for export] *)
      ldarg F_27fac D_27fac dh A_dh;                        (* [comment removed for export] *)
      fold M1;
      sn F_27fb0 D_27fb0 |]).                               (* [comment removed for export] *)
    - (* [comment removed for export] *)
      stepb_ft F_27fb4 D_27fb4 ltac:(condZ).                (* [comment removed for export] *)
      zv F_27fb8 D_27fb8 (Z_to_bv 64 DW).                   (* [comment removed for export] *)
      zv F_27fbc D_27fbc (Z_to_bv 64 DX).                   (* [comment removed for export] *)
      zv F_27fc0 D_27fc0 (Z_to_bv 64 DPW).                  (* [comment removed for export] *)
      zvw F_27fc4 D_27fc4 (Z_to_bv 64 dx).                  (* [comment removed for export] *)
      stepb_ft F_27fc8 D_27fc8 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - subst DPW DX DW SPW SX. repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - (* [comment removed for export] *)
      stepb_tk F_27fb4 D_27fb4 ltac:(condZ).
      zv F_27fe0 D_27fe0 (Z_to_bv 64 DPW). mulw_v F_27fe4 D_27fe4 (Z_to_bv 64 DPW). stepb_tk F_27fe8 D_27fe8 ltac:(condR).
      zv F_27ff0 D_27ff0 (Z_to_bv 64 DX). mulw_v F_27ff4 D_27ff4 (Z_to_bv 64 DX). stepb_tk F_27ff8 D_27ff8 ltac:(condR).
      zv F_28000 D_28000 (Z_to_bv 64 DW). mulw_v F_28004 D_28004 (Z_to_bv 64 DW). stepb_tk F_28008 D_28008 ltac:(condR).
      zv F_28010 D_28010 (Z_to_bv 64 SPW). mulw_v F_28014 D_28014 (Z_to_bv 64 SPW). stepb_tk F_28018 D_28018 ltac:(condR).
      zv F_28020 D_28020 (Z_to_bv 64 SX). mulw_v F_28024 D_28024 (Z_to_bv 64 SX). stepb_tk F_28028 D_28028 ltac:(condR).
      zv F_28030 D_28030 (Z_to_bv 64 SPW).                  (* [comment removed for export] *)
      zv F_28034 D_28034 (Z_to_bv 64 SX).                   (* [comment removed for export] *)
      zvw F_28038 D_28038 (Z_to_bv 64 DX).                  (* [comment removed for export] *)
      stepb_tk F_2803c D_2803c ltac:(condZ).                (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x27fcc : word) M1 rom) (mkst regs' (0x28238 : word) M1a rom)
      /\ getr regs' 31 = Z_to_bv 64 (DX + DW - DPW) /\ getr regs' 9 = Z_to_bv 64 DW /\ getr regs' 25 = Z_to_bv 64 DX /\ getr regs' 27 = Z_to_bv 64 SX
      /\ getr regs' 5 = Z_to_bv 64 sy /\ getr regs' 7 = Z_to_bv 64 dy
      /\ regs_agree (fun r : reg => In r [1; 5; 7; 9; 12; 13; 15; 17; 18; 22; 24; 25; 27; 31]%list) regs regs'.
  Proof.
    intros regs H2 H16 H23 H26 H20 H28 H29 H22 H30 H8 H21.
    pose proof bits_bounds as BB.
    eexists. split.
    - zv F_27fcc D_27fcc (Z_to_bv 64 SX).                   (* [comment removed for export] *)
      zv F_27fd0 D_27fd0 (Z_to_bv 64 DX).                   (* [comment removed for export] *)
      sextw F_27fd4 D_27fd4 SX.                             (* [comment removed for export] *)
      stepb_tk F_27fd8 D_27fd8 ltac:(condZ).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_280a0 D_280a0 DW. sextw F_280a4 D_280a4 DX.
      zv F_280a8 D_280a8 (Z_to_bv 64 (DX + DW)). addw_v F_280ac D_280ac (DX + DW)%Z.
      stepb_tk F_280b0 D_280b0 ltac:(condR).
      sextw F_280b8 D_280b8 (DX + DW)%Z. sextw F_280bc D_280bc DPW.
      subw_v F_280c0 D_280c0 (DX + DW - DPW)%Z. zv F_280c4 D_280c4 (Z_to_bv 64 (DX + DW - DPW)).
      stepb_tk F_280c8 D_280c8 ltac:(condR).
      stepb_tk F_280d0 D_280d0 ltac:(condS).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_280e4 D_280e4 DW. sextw F_280e8 D_280e8 SX.
      zv F_280ec D_280ec (Z_to_bv 64 (SX + DW)). addw_v F_280f0 D_280f0 (SX + DW)%Z.
      stepb_tk F_280f4 D_280f4 ltac:(condR).
      sextw F_280fc D_280fc (SX + DW)%Z. sextw F_28100 D_28100 SPW.
      subw_v F_28104 D_28104 (SX + DW - SPW)%Z. zv F_28108 D_28108 (Z_to_bv 64 (SX + DW - SPW)).
      stepb_tk F_2810c D_2810c ltac:(condR).
      stepb_tk F_28114 D_28114 ltac:(condS).                (* [comment removed for export] *)
      stepb_ft F_28128 D_28128 ltac:(condZ).                (* [comment removed for export] *)
      zv F_2812c D_2812c (Z_to_bv 64 sy).                   (* [comment removed for export] *)
      zv F_28130 D_28130 (Z_to_bv 64 dy).                   (* [comment removed for export] *)
      sextw F_28134 D_28134 sy.                             (* [comment removed for export] *)
      stepb_ft F_28138 D_28138 ltac:(condZ).                (* [comment removed for export] *)
      zv F_2813c D_2813c (Z_to_bv 64 dy).                   (* [comment removed for export] *)
      sn F_28140 D_28140.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_2819c D_2819c dh. sextw F_281a0 D_281a0 dy.
      zv F_281a4 D_281a4 (Z_to_bv 64 (dy + dh)). addw_v F_281a8 D_281a8 (dy + dh)%Z.
      stepb_tk F_281ac D_281ac ltac:(condR).
      sextw F_281b4 D_281b4 (dy + dh)%Z.
      subw_v F_281b8 D_281b8 (dy + dh - dpixh)%Z. zv F_281bc D_281bc (Z_to_bv 64 (dy + dh - dpixh)).
      stepb_tk F_281c0 D_281c0 ltac:(condR).
      stepb_tk F_281c8 D_281c8 ltac:(condS).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      sextw F_281dc D_281dc dh. sextw F_281e0 D_281e0 sy.
      zv F_281e4 D_281e4 (Z_to_bv 64 (sy + dh)). addw_v F_281e8 D_281e8 (sy + dh)%Z.
      stepb_tk F_281ec D_281ec ltac:(condR).
      sextw F_281f4 D_281f4 (sy + dh)%Z.
      subw_v F_281f8 D_281f8 (sy + dh - spixh)%Z. zv F_281fc D_281fc (Z_to_bv 64 (sy + dh - spixh)).
      stepb_tk F_28200 D_28200 ltac:(condR).
      stepb_tk F_28208 D_28208 ltac:(condS).                (* [comment removed for export] *)
      sextw F_2821c D_2821c DW.                             (* [comment removed for export] *)
      stepb_tk F_28220 D_28220 ltac:(condZ).                (* [comment removed for export] *)
      sextw F_28228 D_28228 dh.                             (* [comment removed for export] *)
      stepST F_2822c D_2822c (Z_to_bv 64 (s - 112)) (Z_to_bv 64 dh) ltac:(sokf).   (* [comment removed for export] *)
      fold M1a.
      stepb_tk F_28230 D_28230 ltac:(condZ).                (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x28238 : word) M1a rom) (mkst regs' (0x285b0 : word) M2 rom)
      /\ getr regs' 12 = Z_to_bv 64 lw
      /\ regs_agree (fun r : reg => In r [12; 13; 15; 16; 28]%list) regs regs'.
  Proof.
    intros regs H2 H25 H27 H6 H8.
    pose proof bits_bounds as BB. pose proof col_mods as (MX & MS & MW & _).
    destruct (Z.eq_dec lw 0) as [E0 | NE0].
    - eexists. split.
      + sn F_28238 D_28238. sn F_2823c D_2823c. fixv' (Z_to_bv 64 0) ltac:(apply or_andi31_0; lia).
        stepST F_28240 D_28240 (Z_to_bv 64 (s - 152)) (Z_to_bv 64 swpl) ltac:(apply sok_frame; [unfold M1a, M1; grows | cbn; lia]).
        fold M2.
        stepb_tk F_28244 D_28244 ltac:(condR).              (* [comment removed for export] *)
        sn F_283c8 D_283c8. fixv' (Z_to_bv 64 lw) ltac:(rewrite andi_31_Z by lia; rewrite MW; reflexivity).
        stepb_tk F_283cc D_283cc ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; pin; reflexivity | solve_regs_agree].
    - destruct (lmask_read M2 lw ltac:(lia)) as (bs & Rbs & Lbs).
      eexists. split.
      + sn F_28238 D_28238. sn F_2823c D_2823c. fixv' (Z_to_bv 64 0) ltac:(apply or_andi31_0; lia).
        stepST F_28240 D_28240 (Z_to_bv 64 (s - 152)) (Z_to_bv 64 swpl) ltac:(apply sok_frame; [unfold M1a, M1; grows | cbn; lia]).
        fold M2.
        stepb_tk F_28244 D_28244 ltac:(condR).
        sn F_283c8 D_283c8. fixv' (Z_to_bv 64 lw) ltac:(rewrite andi_31_Z by lia; rewrite MW; reflexivity).
        stepb_ft F_283cc D_283cc ltac:(condZ).
        sn F_283d0 D_283d0. fixv' (Z_to_bv 64 (4 * lw)) ltac:(rewrite zbv_slli by lia; f_equal; lia).   (* [comment removed for export] *)
        sn F_283d4 D_283d4. sn F_283d8 D_283d8.             (* [comment removed for export] *)
        sn F_283dc D_283dc.                                 (* [comment removed for export] *)
        stepb_tk F_283e0 D_283e0 ltac:(condZ).              (* [comment removed for export] *)
        sn F_283e8 D_283e8. fixv' (Z_to_bv 64 (0x12970 + 4 * lw)) ltac:(rewrite zbv_add; reflexivity).   (* [comment removed for export] *)
        stepLD F_283ec D_283ec bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
        sn F_283f0 D_283f0.                                 (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; pin; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  #[local] Abbreviation RSd := (4 * (dwpl * dpixh))%Z (only parsing).
  #[local] Abbreviation RSs := (4 * (swpl * spixh))%Z (only parsing).
  Hypothesis Hdd : (4096 <= datad /\ datad + RSd + 8 <= 2 ^ 64 /\ datad mod 4 = 0)%Z.
  Hypothesis Hds : (4096 <= datas /\ datas + RSs + 8 <= 2 ^ 64 /\ datas mod 4 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis JT : rdn SEGS M (Z_to_bv 64 0x128e0) 4 = Some (Z_to_le_bytes 4 97268).

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

  Lemma JT2 : rdn SEGS M2 (Z_to_bv 64 0x128e0) 4 = Some (Z_to_le_bytes 4 97268).
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
      msteps SEGS (mkst regs (0x285b0 : word) M2 rom) (mkst regs' (0x2868c : word) M2 rom)
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
      zv F_285b0 D_285b0 (Z_to_bv 64 (swpl * sy)).          (* [comment removed for export] *)
      mulw_v F_285b4 D_285b4 (Z_to_bv 64 (swpl * sy)).
      stepb_tk F_285b8 D_285b8 ltac:(condR).
      sextw F_285c0 D_285c0 (swpl * sy)%Z.
      slli2 F_285c4 D_285c4 (4 * (swpl * sy))%Z.            (* [comment removed for export] *)
      zv F_285c8 D_285c8 (Z_to_bv 64 (datas + 4 * (swpl * sy))).   (* [comment removed for export] *)
      snez1 F_285cc D_285cc.                                (* [comment removed for export] *)
      seqz0 F_285d0 D_285d0.                                (* [comment removed for export] *)
      stepb_tk F_285d4 D_285d4 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_285dc D_285dc. slti0 F_285e0 D_285e0. sn F_285e4 D_285e4. sn F_285e8 D_285e8.
      stepb_tk F_285ec D_285ec ltac:(condR).
      sn F_285f4 D_285f4. fixv' (Z_to_bv 64 cs) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite SXd; reflexivity).   (* [comment removed for export] *)
      slli2 F_285f8 D_285f8 (4 * cs)%Z.
      zv F_285fc D_285fc (Z_to_bv 64 PSF).                  (* [comment removed for export] *)
      stepb_tk F_28600 D_28600 ltac:(condZ).                (* [comment removed for export] *)
      seqz0 F_28608 D_28608. sn F_2860c D_2860c.
      stepb_tk F_28610 D_28610 ltac:(condR).
      (* [comment removed for export] *)
      zv F_28618 D_28618 (Z_to_bv 64 (dwpl * dy)).          (* [comment removed for export] *)
      mulw_v F_2861c D_2861c (Z_to_bv 64 (dwpl * dy)).
      stepb_tk F_28620 D_28620 ltac:(condR).
      sextw F_28628 D_28628 (dwpl * dy)%Z.
      slli2 F_2862c D_2862c (4 * (dwpl * dy))%Z.            (* [comment removed for export] *)
      zv F_28630 D_28630 (Z_to_bv 64 (datad + 4 * (dwpl * dy))).   (* [comment removed for export] *)
      snez1 F_28634 D_28634.                                (* [comment removed for export] *)
      seqz0 F_28638 D_28638.
      stepb_tk F_2863c D_2863c ltac:(condR).
      sltu0 F_28644 D_28644. slti0 F_28648 D_28648. sn F_2864c D_2864c. sn F_28650 D_28650.
      stepb_tk F_28654 D_28654 ltac:(condR).
      sn F_2865c D_2865c. fixv' (Z_to_bv 64 cd) ltac:(rewrite zbv_sraiw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite DXd; reflexivity).   (* [comment removed for export] *)
      slli2 F_28660 D_28660 (4 * cd)%Z.                     (* [comment removed for export] *)
      zv F_28664 D_28664 (Z_to_bv 64 PDF).                  (* [comment removed for export] *)
      seqz0 F_28668 D_28668.
      stepb_tk F_2866c D_2866c ltac:(condR).
      sltu0 F_28674 D_28674. slti0 F_28678 D_28678. sn F_2867c D_2867c. sn F_28680 D_28680.
      stepb_tk F_28684 D_28684 ltac:(condR).
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
      msteps SEGS (mkst regs (0x2868c : word) M2 rom) (mkst regs' (0x2a540 : word) M2 rom)
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
      sn F_2868c D_2868c.
      zv F_28690 D_28690 (Z_to_bv 64 11).                   (* [comment removed for export] *)
      sn F_28694 D_28694. sn F_28698 D_28698.
      stepb_tk F_2869c D_2869c ltac:(condZ).                (* [comment removed for export] *)
      sn F_286a4 D_286a4. sn F_286a8 D_286a8. sn F_286ac D_286ac.
      sn F_286b0 D_286b0. fixv' (Z_to_bv 64 0x128e0) ltac:(apply bv_eq; reflexivity).
      stepLD F_286b4 D_286b4 (Z_to_le_bytes 4 97268) (Z_to_bv 64 97268) ltac:(addr_norm; rewrite ?Z.add_0_r; exact JT2) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 97268)) with (Z_to_bv 64 97268).
      sn F_286b8 D_286b8. fixv' (Z_to_bv 64 0x2a4a8) ltac:(apply bv_eq; reflexivity).
      stepret F_286bc D_286bc (0x2a4a8 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_2a4a8 D_2a4a8. fixv' (Z_to_bv 64 (swpl * 0)) ltac:(f_equal; lia).     (* [comment removed for export] *)
      sn F_2a4ac D_2a4ac. fixv' (Z_to_bv 64 (dwpl * 0)) ltac:(f_equal; lia).     (* [comment removed for export] *)
      sn F_2a4b0 D_2a4b0.                                   (* [comment removed for export] *)
      zv F_2a4b4 D_2a4b4 (Z_to_bv 64 (SX + DPW)).           (* [comment removed for export] *)
      sn F_2a4b8 D_2a4b8.                                   (* [comment removed for export] *)
      zv F_2a4bc D_2a4bc (Z_to_bv 64 (4 * cd + 4 * (dwpl * dy))).   (* [comment removed for export] *)
      zand0 F_2a4c0 D_2a4c0 andi_3 (proj2 (proj2 Hds)).     (* [comment removed for export] *)
      zv F_2a4c4 D_2a4c4 (Z_to_bv 64 (4 * cs + 4 * (swpl * sy))).   (* [comment removed for export] *)
      sn F_2a4c8 D_2a4c8. sn F_2a4cc D_2a4cc. fixv' (Z_to_bv 64 (DX + DW - DPW)) ltac:(apply and_srai63_np; lia).   (* [comment removed for export] *)
      zand0 F_2a4d0 D_2a4d0 andi_3 (proj2 (proj2 Hdd)).     (* [comment removed for export] *)
      subw_v F_2a4d4 D_2a4d4 (SPW - SX)%Z.                  (* [comment removed for export] *)
      subw_v F_2a4d8 D_2a4d8 (SX + DPW - DX)%Z.             (* [comment removed for export] *)
      sn F_2a4dc D_2a4dc.                                   (* [comment removed for export] *)
      zv F_2a4e0 D_2a4e0 (Z_to_bv 64 PDF).                  (* [comment removed for export] *)
      zv F_2a4e4 D_2a4e4 (Z_to_bv 64 PSF).                  (* [comment removed for export] *)
      zv F_2a4e8 D_2a4e8 (Z_to_bv 64 (SX + DW)).            (* [comment removed for export] *)
      subw_v F_2a4ec D_2a4ec (SX + DW - SPW)%Z.             (* [comment removed for export] *)
      sn F_2a4f0 D_2a4f0. sn F_2a4f4 D_2a4f4. fixv' (Z_to_bv 64 (SX + DW - SPW)) ltac:(apply and_srai63_np; lia).
      zv F_2a4f8 D_2a4f8 (Z_to_bv 64 DW).                   (* [comment removed for export] *)
      sn F_2a4fc D_2a4fc. fixv' (Z_to_bv 64 nf) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite DWd; reflexivity).   (* [comment removed for export] *)
      zv F_2a500 D_2a500 (Z_to_bv 64 (- nf)).               (* [comment removed for export] *)
      sn F_2a504 D_2a504.                                   (* [comment removed for export] *)
      stepLD F_2a508 D_2a508 (word_to_le_bytes 8 (Z_to_bv 64 swpl)) (Z_to_bv 64 swpl) ltac:(rdn_addr (s - 152)%Z; exact swpl_cell) ltac:(apply bytes_le_to_Z_8).
      sn F_2a50c D_2a50c.                                   (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x2a540 : word) Mi rom) (mkst regs' (0x2a5a8 : word) Mi rom)
      /\ getr regs' 15 = Z_to_bv 64 (SR i) /\ getr regs' 18 = Z_to_bv 64 (DR i)
      /\ regs_agree (fun r : reg => In r [6; 15; 18; 22]%list) regs regs'.
  Proof.
    intros regs Mi i Hi (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H25.
    pose proof (row_in i Hi) as RI. pose proof geom as G.
    assert (CC : (0 <= (if Z.eq_dec lw 0 then 0 else 1))%Z) by (destruct (Z.eq_dec lw 0); lia).
    eexists. split.
    - zv F_2a540 D_2a540 (Z_to_bv 64 (swpl * i)).           (* [comment removed for export] *)
      mulw_v F_2a544 D_2a544 (Z_to_bv 64 (swpl * i)).
      stepb_ft F_2a548 D_2a548 ltac:(condR).                (* [comment removed for export] *)
      sextw F_2a54c D_2a54c (swpl * i)%Z.
      slli2 F_2a550 D_2a550 (4 * (swpl * i))%Z.
      zv F_2a554 D_2a554 (Z_to_bv 64 (SR i)).               (* [comment removed for export] *)
      seqz0 F_2a558 D_2a558.
      stepb_ft F_2a55c D_2a55c ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_2a560 D_2a560. slti0 F_2a564 D_2a564. sn F_2a568 D_2a568. sn F_2a56c D_2a56c.
      stepb_ft F_2a570 D_2a570 ltac:(condR).
      zv F_2a574 D_2a574 (Z_to_bv 64 (dwpl * i)).           (* [comment removed for export] *)
      mulw_v F_2a578 D_2a578 (Z_to_bv 64 (dwpl * i)).
      stepb_ft F_2a57c D_2a57c ltac:(condR).
      sextw F_2a580 D_2a580 (dwpl * i)%Z.
      slli2 F_2a584 D_2a584 (4 * (dwpl * i))%Z.
      zv F_2a588 D_2a588 (Z_to_bv 64 (DR i)).               (* [comment removed for export] *)
      seqz0 F_2a58c D_2a58c.
      stepb_ft F_2a590 D_2a590 ltac:(condR).
      sltu0 F_2a594 D_2a594. slti0 F_2a598 D_2a598. sn F_2a59c D_2a59c. sn F_2a5a0 D_2a5a0.
      stepb_ft F_2a5a4 D_2a5a4 ltac:(condR).
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
      msteps SEGS (mkst regs (0x2a5a8 : word) Mi rom) (mkst regs' (0x2a5c8 : word) Mi rom)
      /\ getr regs' 15 = Z_to_bv 64 (4 * 0) /\ getr regs' 18 = Z_to_bv 64 (DR i) /\ getr regs' 22 = Z_to_bv 64 (SR i) /\ getr regs' 23 = Z_to_bv 64 (- (nf - 0))
      /\ regs_agree (fun r : reg => In r [15; 18; 22; 23]%list) regs regs'.
  Proof.
    intros regs Mi i Hi H32 (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H11 H13.
    pose proof (row_in i Hi) as RI. pose proof bits_bounds as BB.
    eexists. split.
    - stepb_ft F_2a5a8 D_2a5a8 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_2a5ac D_2a5ac ltac:(condR).                (* [comment removed for export] *)
      sn F_2a5b0 D_2a5b0. fixv' (Z_to_bv 64 (4 * 0)) ltac:(reflexivity).   (* [comment removed for export] *)
      slli2 F_2a5b4 D_2a5b4 (4 * (dwpl * i))%Z.             (* [comment removed for export] *)
      slli2 F_2a5b8 D_2a5b8 (4 * (swpl * i))%Z.             (* [comment removed for export] *)
      zv F_2a5bc D_2a5bc (Z_to_bv 64 (DR i)).               (* [comment removed for export] *)
      zv F_2a5c0 D_2a5c0 (Z_to_bv 64 (SR i)).               (* [comment removed for export] *)
      zv F_2a5c4 D_2a5c4 (Z_to_bv 64 (- (nf - 0))).         (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_W : forall regs Mi i k, (0 <= i < dh)%Z -> (0 <= k < nf)%Z -> Inv Mi -> LInv regs ->
    getr regs 15 = Z_to_bv 64 (4 * k) -> getr regs 18 = Z_to_bv 64 (DR i) -> getr regs 22 = Z_to_bv 64 (SR i) -> getr regs 23 = Z_to_bv 64 (- (nf - k)) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x2a5c8 : word) Mi rom) (mkst regs' (0x2a5f4 : word) M' rom)
      /\ Inv M' /\ getr regs' 15 = Z_to_bv 64 (4 * (k + 1)) /\ getr regs' 23 = Z_to_bv 64 (- (nf - (k + 1)))
      /\ regs_agree (fun r : reg => In r [6; 15; 23; 24; 26]%list) regs regs'.
  Proof.
    intros regs Mi i k Hi Hk HIv (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H15 H18 H22 H23.
    pose proof (row_in i Hi) as RI. pose proof geom as G.
    assert (CC : (0 <= (if Z.eq_dec lw 0 then 0 else 1))%Z) by (destruct (Z.eq_dec lw 0); lia).
    destruct (rd4 Mi datas RSs (SR i + 4 * k) HIv SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Rbs & Lbs).
    eexists. eexists. split; [|split; [|split; [|split]]].
    - zv F_2a5c8 D_2a5c8 (Z_to_bv 64 (SR i + 4 * k)).       (* [comment removed for export] *)
      stepb_ft F_2a5cc D_2a5cc ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_2a5d0 D_2a5d0 ltac:(condR).                (* [comment removed for export] *)
      zv F_2a5d4 D_2a5d4 (Z_to_bv 64 (DR i + 4 * k)).       (* [comment removed for export] *)
      stepb_ft F_2a5d8 D_2a5d8 ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_2a5dc D_2a5dc bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
      stepST F_2a5e0 D_2a5e0 (Z_to_bv 64 (DR i + 4 * k)) (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) ltac:(apply (Inv_sok _ _ 4 HIv); [lia | cbn; lia]).
      stepb_ft F_2a5e4 D_2a5e4 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_2a5e8 D_2a5e8 ltac:(condZ).                (* [comment removed for export] *)
      sn F_2a5ec D_2a5ec. fixv' (Z_to_bv 64 (- (nf - (k + 1)))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).   (* [comment removed for export] *)
      zv F_2a5f0 D_2a5f0 (Z_to_bv 64 (4 * (k + 1))).        (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x2a5c8 : word) Mi rom) (mkst regs' (0x2a600 : word) M' rom)
      /\ Inv M' /\ getr regs' 15 = Z_to_bv 64 (SR i + 4 * nf) /\ getr regs' 18 = Z_to_bv 64 (DR i + 4 * nf)
      /\ regs_agree (fun r : reg => In r [6; 15; 18; 23; 24; 26]%list) regs regs'.
  Proof.
    induction j as [|j IH]; intros regs Mi i k Hi Hk Hj HIv LI H15 H18 H22 H23;
      destruct (rl_W regs Mi i k Hi ltac:(lia) HIv LI H15 H18 H22 H23) as (r1 & Ma & S1 & HI1 & A15 & A23 & AG1);
      pose proof (AG1 18 ltac:(notin_list)) as A18; rewrite H18 in A18;
      pose proof (AG1 22 ltac:(notin_list)) as A22; rewrite H22 in A22.
    - eexists. exists Ma. split; [|split; [exact HI1 | split; [|split]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_2a5f4 D_2a5f4 ltac:(condSe).             (* [comment removed for export] *)
        zv F_2a5f8 D_2a5f8 (Z_to_bv 64 (DR i + 4 * nf)).    (* [comment removed for export] *)
        zv F_2a5fc D_2a5fc (Z_to_bv 64 (SR i + 4 * nf)).    (* [comment removed for export] *)
        apply mst_refl.
      + gres; pin; reflexivity.
      + gres; pin; reflexivity.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (L1 : LInv r1) by (apply (LInv_agree regs); [regs_agree_weaken AG1 | exact LI]).
      destruct (IH r1 Ma i (k + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 L1 A15 A18 A22 A23) as (r2 & Mb & S2 & HI2 & B15 & B18 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B15 | split; [exact B18|]]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_2a5f4 D_2a5f4 ltac:(condSe).
        exact S2.
      + eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma rl_P : forall regs Mi i n, (0 <= i < dh)%Z -> (n = nf)%Z -> Inv Mi -> LInv regs ->
    getr regs 15 = Z_to_bv 64 (SR i + 4 * n) -> getr regs 18 = Z_to_bv 64 (DR i + 4 * n) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x2a600 : word) Mi rom) (mkst regs' (0x2a528 : word) M' rom)
      /\ Inv M'
      /\ regs_agree (fun r : reg => In r [6; 15]%list) regs regs'.
  Proof.
    intros regs Mi i n Hi -> HIv (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H15 H18.
    pose proof (row_in i Hi) as RI. pose proof geom as G. pose proof (ptr_mod4 i nf) as (MD & MS).
    assert (Hlw : (0 <= lw < 32)%Z) by (destruct Hcol as (_ & _ & _ & X); exact X).
    destruct (Z.eq_dec lw 0) as [E0 | NE0].
    - exists regs, Mi. split; [|split; [exact HIv | apply regs_agree_refl]].
      stepb_tk F_2a600 D_2a600 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - destruct (rd4 Mi datad RSd (DR i + 4 * nf) HIv SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rbd & Lbd).
      destruct (rd4 Mi datas RSs (SR i + 4 * nf) HIv SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Rbs & Lbs).
      eexists. eexists. split; [|split].
      + stepb_ft F_2a600 D_2a600 ltac:(condZ).
        stepb_ft F_2a604 D_2a604 ltac:(condZ).              (* [comment removed for export] *)
        zand0 F_2a608 D_2a608 andi_3 MD.                    (* [comment removed for export] *)
        stepb_ft F_2a60c D_2a60c ltac:(condR).              (* [comment removed for export] *)
        stepb_ft F_2a610 D_2a610 ltac:(condZ).              (* [comment removed for export] *)
        zand0 F_2a614 D_2a614 andi_3 MS.                    (* [comment removed for export] *)
        stepb_tk F_2a618 D_2a618 ltac:(condR).              (* [comment removed for export] *)
        stepLD F_2a510 D_2a510 bd (Z_to_bv 64 (bytes_le_to_Z bd)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbd) ltac:(symmetry; apply u_lez4; exact Lbd).
        stepLD F_2a514 D_2a514 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
        sn F_2a518 D_2a518. sn F_2a51c D_2a51c. sn F_2a520 D_2a520.
        chain_step; [ reflexivity
                    | eapply step_sw_at with (a := Z_to_bv 64 (DR i + 4 * nf));
                      [ exact F_2a524 | reflexivity | exact D_2a524 | gres; imm_norm; addr_tac | gres; reflexivity
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
      msteps SEGS (mkst regs (0x2a528 : word) Mi rom) (mkst regs' (0x2a538 : word) Mi rom)
      /\ getr regs' 25 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (swpl * (i + 1)) /\ getr regs' 13 = Z_to_bv 64 (dwpl * (i + 1))
      /\ getr regs' 15 = Z_to_bv 64 dh
      /\ regs_agree (fun r : reg => In r [11; 13; 15; 25]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H25 H11 H13.
    pose proof (row_in i Hi) as RI.
    assert (swpl * (i + 1) <= 400020000 /\ dwpl * (i + 1) <= 400020000)%Z by lia.
    eexists. split.
    - sextw F_2a528 D_2a528 (i + 1)%Z.                      (* [comment removed for export] *)
      addw_v F_2a52c D_2a52c (dwpl * (i + 1))%Z.            (* [comment removed for export] *)
      addw_v F_2a530 D_2a530 (swpl * (i + 1))%Z.            (* [comment removed for export] *)
      stepLD F_2a534 D_2a534 (word_to_le_bytes 8 (Z_to_bv 64 dh)) (Z_to_bv 64 dh) ltac:(rdn_addr (s - 112)%Z; exact (Inv_dh Mi HIv)) ltac:(apply bytes_le_to_Z_8).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_row : forall regs Mi i, (0 <= i < dh)%Z -> Inv Mi -> LInv regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x2a540 : word) Mi rom) (mkst regs' (0x2a538 : word) M' rom)
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
    assert (MID : exists r2 Ma, msteps SEGS (mkst r1 (0x2a5a8 : word) Mi rom) (mkst r2 (0x2a600 : word) Ma rom)
                    /\ Inv Ma /\ getr r2 15 = Z_to_bv 64 (SR i + 4 * nf) /\ getr r2 18 = Z_to_bv 64 (DR i + 4 * nf)
                    /\ regs_agree (fun r : reg => In r [6; 15; 18; 22; 23; 24; 26]%list) r1 r2).
    { destruct (Z_lt_ge_dec DW 32) as [Hs32 | Hf32].
      - assert (Enf0 : (nf = 0)%Z) by lia.
        exists r1, Mi. split; [|split; [exact HIv | split; [|split; [|apply regs_agree_refl]]]].
        + destruct L1 as (I2 & I27 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & _).
          stepb_tk F_2a5a8 D_2a5a8 ltac:(condZ).            (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x2a540 : word) Mi rom) (mkst regs' (0x2f86c : word) M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 (s - 240)
      /\ regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv LI H25 H11 H13;
      destruct (rl_row regs Mi i ltac:(lia) HIv LI H25 H11 H13) as (r1 & Ma & S1 & HI1 & L1 & A25 & A11 & A13 & A15 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact (proj1 L1) | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_2a538 D_2a538 ltac:(condZ).                (* [comment removed for export] *)
      sn F_2a53c D_2a53c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - destruct (IH r1 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 L1 A25 A11 A13) as (r2 & Mb & S2 & HI2 & B2 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B2|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_2a538 D_2a538 ltac:(condZ).
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
      msteps SEGS (mkst regs (0x2f86c : word) Mi rom) (mkst regs' ra Mi rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2.
    eexists. split.
    -
      ldsv F_2f86c D_2f86c 8%Z ra F_ra HIv.
      ldsv F_2f870 D_2f870 16%Z s0v F_s0v HIv.
      ldsv F_2f874 D_2f874 24%Z s1v F_s1v HIv.
      ldsv F_2f878 D_2f878 32%Z s2v F_s2v HIv.
      ldsv F_2f87c D_2f87c 40%Z s3v F_s3v HIv.
      ldsv F_2f880 D_2f880 48%Z s4v F_s4v HIv.
      ldsv F_2f884 D_2f884 56%Z s5v F_s5v HIv.
      ldsv F_2f888 D_2f888 64%Z s6v F_s6v HIv.
      ldsv F_2f88c D_2f88c 72%Z s7v F_s7v HIv.
      ldsv F_2f890 D_2f890 80%Z s8v F_s8v HIv.
      ldsv F_2f894 D_2f894 88%Z s9v F_s9v HIv.
      ldsv F_2f898 D_2f898 96%Z s10v F_s10v HIv.
      ldsv F_2f89c D_2f89c 104%Z s11v F_s11v HIv.
      zv F_2f8a0 D_2f8a0 (Z_to_bv 64 s).                    (* [comment removed for export] *)
      stepret F_2f8a4 D_2f8a4 ra ltac:(reflexivity).        (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x27f50 : word) M rom) (mkst regs' ra M' rom)
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
    assert (S4 : msteps SEGS (mkst r3 (0x285b0 : word) M2 rom) (mkst r4 (0x2a540 : word) M2 rom)) by (eapply msteps_trans; [exact S3a | exact S4b]).
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
