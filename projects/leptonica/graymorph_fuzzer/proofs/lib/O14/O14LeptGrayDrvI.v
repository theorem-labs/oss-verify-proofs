(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoom14 GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptPixHdr O14LeptCmap2 O14LeptPixCopy O14LeptGrayD_iface O14LeptGrayA O14LeptGrayD O14_code_gmD_drv O14LeptGrayDrv.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section GrayDrvI.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mvli F D v := first [zv F D v | sn F D].

Lemma e_hd_null : hd_null_spec (0x1fe10 : word) 0x10298 0x1061e.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_1fd14 D_1fd14 (Z_to_bv 64 (s - 64)).
    stepST F_1fd18 D_1fd18 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_1fd1c D_1fd1c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1fd20 D_1fd20 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_1fd24 D_1fd24 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_1fd28 D_1fd28 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_1fd2c D_1fd2c ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fd7c D_1fd7c.
    stepLD F_1fd80 D_1fd80 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_1fd84 D_1fd84 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_1fd88 D_1fd88.
    stepb_ft F_1fd8c D_1fd8c ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fd90 D_1fd90. sn F_1fd94 D_1fd94. sn F_1fd98 D_1fd98. sn F_1fd9c D_1fd9c. sn F_1fda0 D_1fda0.
    sn F_1fdc8 D_1fdc8.
    stepLD8 F_1fdcc D_1fdcc ret.
    stepLD8 F_1fdd0 D_1fdd0 (getr regs 8).
    stepLD8 F_1fdd4 D_1fdd4 (getr regs 9).
    stepLD8 F_1fdd8 D_1fdd8 (getr regs 18).
    stepLD8 F_1fddc D_1fddc (getr regs 19).
    zv F_1fde0 D_1fde0 (Z_to_bv 64 s).
    sn F_1fde4 D_1fde4.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_hd_depth : hd_depth_spec (0x1fe10 : word) 0x10d0b 0x1061e.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_1fd14 D_1fd14 (Z_to_bv 64 (s - 64)).
    stepST F_1fd18 D_1fd18 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_1fd1c D_1fd1c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1fd20 D_1fd20 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_1fd24 D_1fd24 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_1fd28 D_1fd28 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_1fd2c D_1fd2c ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fd30 D_1fd30. sn F_1fd34 D_1fd34.               (* [comment removed for export] *)
    zv F_1fd38 D_1fd38 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_1fd3c D_1fd3c.                                   (* [comment removed for export] *)
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_167bc D_167bc (0x1fe3c : word) ltac:(bveq).
    sn F_1fd40 D_1fd40.                                   (* [comment removed for export] *)
    stepb_tk F_1fd44 D_1fd44 ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fda4 D_1fda4.
    stepLD F_1fda8 D_1fda8 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_1fdac D_1fdac (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_1fdb0 D_1fdb0.
    stepb_ft F_1fdb4 D_1fdb4 ltac:(condZ).
    sn F_1fdb8 D_1fdb8. sn F_1fdbc D_1fdbc. sn F_1fdc0 D_1fdc0. sn F_1fdc4 D_1fdc4.
    sn F_1fdc8 D_1fdc8.
    stepLD8 F_1fdcc D_1fdcc ret.
    stepLD8 F_1fdd0 D_1fdd0 (getr regs 8).
    stepLD8 F_1fdd4 D_1fdd4 (getr regs 9).
    stepLD8 F_1fdd8 D_1fdd8 (getr regs 18).
    stepLD8 F_1fddc D_1fddc (getr regs 19).
    zv F_1fde0 D_1fde0 (Z_to_bv 64 s).
    sn F_1fde4 D_1fde4.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_hd_cmap : hd_cmap_spec (0x1fe10 : word) 0x10803 0x1061e.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_1fd14 D_1fd14 (Z_to_bv 64 (s - 64)).
    stepST F_1fd18 D_1fd18 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_1fd1c D_1fd1c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1fd20 D_1fd20 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_1fd24 D_1fd24 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_1fd28 D_1fd28 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_1fd2c D_1fd2c ltac:(condZ).
    sn F_1fd30 D_1fd30. sn F_1fd34 D_1fd34.
    zv F_1fd38 D_1fd38 (Z_to_bv 64 pixs).
    sn F_1fd3c D_1fd3c.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x1fe3c : word) ltac:(bveq).
    sn F_1fd40 D_1fd40.
    stepb_ft F_1fd44 D_1fd44 ltac:(condZ).                (* [comment removed for export] *)
    zv F_1fd48 D_1fd48 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_1fd4c D_1fd4c.                                   (* [comment removed for export] *)
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x1fe4c : word) ltac:(bveq).
    stepb_ft F_1fd50 D_1fd50 ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fd54 D_1fd54.
    stepLD F_1fd58 D_1fd58 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_1fd5c D_1fd5c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_1fd60 D_1fd60.
    stepb_ft F_1fd64 D_1fd64 ltac:(condZ).
    sn F_1fd68 D_1fd68. sn F_1fd6c D_1fd6c. sn F_1fd70 D_1fd70. sn F_1fd74 D_1fd74. sn F_1fd78 D_1fd78.
    sn F_1fdc8 D_1fdc8.
    stepLD8 F_1fdcc D_1fdcc ret.
    stepLD8 F_1fdd0 D_1fdd0 (getr regs 8).
    stepLD8 F_1fdd4 D_1fdd4 (getr regs 9).
    stepLD8 F_1fdd8 D_1fdd8 (getr regs 18).
    stepLD8 F_1fddc D_1fddc (getr regs 19).
    zv F_1fde0 D_1fde0 (Z_to_bv 64 s).
    sn F_1fde4 D_1fde4.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_hd_ok : hd_ok_spec (0x1fe10 : word) (0x1ff8c : word) 255.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x178a4) with (0x178a4 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_1fd14 D_1fd14 (Z_to_bv 64 (s - 64)).
    stepST F_1fd18 D_1fd18 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_1fd1c D_1fd1c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1fd20 D_1fd20 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_1fd24 D_1fd24 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_1fd28 D_1fd28 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_1fd2c D_1fd2c ltac:(condZ).
    zv F_1fd30 D_1fd30 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_1fd34 D_1fd34 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_1fd38 D_1fd38 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_1fd3c D_1fd3c.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x1fe3c : word) ltac:(bveq).
    sn F_1fd40 D_1fd40.
    stepb_ft F_1fd44 D_1fd44 ltac:(condZ).
    zv F_1fd48 D_1fd48 (Z_to_bv 64 pixs).
    sn F_1fd4c D_1fd4c.
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x1fe4c : word) ltac:(bveq).
    stepb_tk F_1fd50 D_1fd50 ltac:(condZ).                (* [comment removed for export] *)
    zv F_1fde8 D_1fde8 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_1fdec D_1fdec.                                   (* [comment removed for export] *)
    stepb_ft F_1fdf0 D_1fdf0 ltac:(condZ).
    zv F_1fdf4 D_1fdf4 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_1fdf8 D_1fdf8 ltac:(condZ).
    sn F_1fdfc D_1fdfc.                                   (* [comment removed for export] *)
    stepb_tk F_1fe00 D_1fe00 ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fe74 D_1fe74. sn F_1fe78 D_1fe78. sn F_1fe7c D_1fe7c. sn F_1fe80 D_1fe80.
    mvli F_1fe84 D_1fe84 (Z_to_bv 64 pixs). mvli F_1fe88 D_1fe88 (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_1fe8c D_1fe8c.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segB : segB_spec (0x1ff8c : word) (0x1ff98 : word) PC_pixErodeGray3h.
Proof.
  unfold segB_spec, PC_pixErodeGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x20004) with (0x20004 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_1fe90 D_1fe90 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_1fe94 D_1fe94 ltac:(condZ).                (* [comment removed for export] *)
    sn F_1fe98 D_1fe98.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segC : segC_spec (0x1ff98 : word) (0x1ffe8 : word).
Proof.
  unfold segC_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x17b60) with (0x17b60 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_1fe9c D_1fe9c (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_1fea0 D_1fea0.                                   (* [comment removed for export] *)
    sn F_1fed8 D_1fed8. sn F_1fedc D_1fedc. sn F_1fee0 D_1fee0. sn F_1fee4 D_1fee4.
    sn F_1fee8 D_1fee8.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segD : segD_spec (0x1ffe8 : word) (0x1fff4 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_1feec D_1feec.                                   (* [comment removed for export] *)
    zv F_1fef0 D_1fef0 (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_1fef4 D_1fef4.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segE : segE_spec (0x1fff4 : word) (0x1fffc : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_1fef8 D_1fef8 (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_1fefc D_1fefc.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segF : segF_spec (0x1fffc : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_1ff00 D_1ff00.                                   (* [comment removed for export] *)
    sn F_1ff04 D_1ff04.                                   (* [comment removed for export] *)
    stepLD F_1fe58 D_1fe58 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1fe5c D_1fe5c (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1fe60 D_1fe60 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1fe64 D_1fe64 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_1fe68 D_1fe68 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_1fe6c D_1fe6c (Z_to_bv 64 s).
    stepret F_1fe70 D_1fe70 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma d_hd_null : hd_null_spec (0x20660 : word) 0x10298 0x104ae.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_20564 D_20564 (Z_to_bv 64 (s - 64)).
    stepST F_20568 D_20568 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_2056c D_2056c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20570 D_20570 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20574 D_20574 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20578 D_20578 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_2057c D_2057c ltac:(condZ).                (* [comment removed for export] *)
    sn F_205cc D_205cc.
    stepLD F_205d0 D_205d0 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_205d4 D_205d4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_205d8 D_205d8.
    stepb_ft F_205dc D_205dc ltac:(condZ).                (* [comment removed for export] *)
    sn F_205e0 D_205e0. sn F_205e4 D_205e4. sn F_205e8 D_205e8. sn F_205ec D_205ec. sn F_205f0 D_205f0.
    sn F_20618 D_20618.
    stepLD8 F_2061c D_2061c ret.
    stepLD8 F_20620 D_20620 (getr regs 8).
    stepLD8 F_20624 D_20624 (getr regs 9).
    stepLD8 F_20628 D_20628 (getr regs 18).
    stepLD8 F_2062c D_2062c (getr regs 19).
    zv F_20630 D_20630 (Z_to_bv 64 s).
    sn F_20634 D_20634.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_hd_depth : hd_depth_spec (0x20660 : word) 0x10d0b 0x104ae.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_20564 D_20564 (Z_to_bv 64 (s - 64)).
    stepST F_20568 D_20568 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_2056c D_2056c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20570 D_20570 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20574 D_20574 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20578 D_20578 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_2057c D_2057c ltac:(condZ).                (* [comment removed for export] *)
    sn F_20580 D_20580. sn F_20584 D_20584.               (* [comment removed for export] *)
    zv F_20588 D_20588 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_2058c D_2058c.                                   (* [comment removed for export] *)
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_167bc D_167bc (0x2068c : word) ltac:(bveq).
    sn F_20590 D_20590.                                   (* [comment removed for export] *)
    stepb_tk F_20594 D_20594 ltac:(condZ).                (* [comment removed for export] *)
    sn F_205f4 D_205f4.
    stepLD F_205f8 D_205f8 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_205fc D_205fc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_20600 D_20600.
    stepb_ft F_20604 D_20604 ltac:(condZ).
    sn F_20608 D_20608. sn F_2060c D_2060c. sn F_20610 D_20610. sn F_20614 D_20614.
    sn F_20618 D_20618.
    stepLD8 F_2061c D_2061c ret.
    stepLD8 F_20620 D_20620 (getr regs 8).
    stepLD8 F_20624 D_20624 (getr regs 9).
    stepLD8 F_20628 D_20628 (getr regs 18).
    stepLD8 F_2062c D_2062c (getr regs 19).
    zv F_20630 D_20630 (Z_to_bv 64 s).
    sn F_20634 D_20634.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_hd_cmap : hd_cmap_spec (0x20660 : word) 0x10803 0x104ae.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_20564 D_20564 (Z_to_bv 64 (s - 64)).
    stepST F_20568 D_20568 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_2056c D_2056c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20570 D_20570 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20574 D_20574 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20578 D_20578 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_2057c D_2057c ltac:(condZ).
    sn F_20580 D_20580. sn F_20584 D_20584.
    zv F_20588 D_20588 (Z_to_bv 64 pixs).
    sn F_2058c D_2058c.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x2068c : word) ltac:(bveq).
    sn F_20590 D_20590.
    stepb_ft F_20594 D_20594 ltac:(condZ).                (* [comment removed for export] *)
    zv F_20598 D_20598 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_2059c D_2059c.                                   (* [comment removed for export] *)
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x2069c : word) ltac:(bveq).
    stepb_ft F_205a0 D_205a0 ltac:(condZ).                (* [comment removed for export] *)
    sn F_205a4 D_205a4.
    stepLD F_205a8 D_205a8 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_205ac D_205ac (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_205b0 D_205b0.
    stepb_ft F_205b4 D_205b4 ltac:(condZ).
    sn F_205b8 D_205b8. sn F_205bc D_205bc. sn F_205c0 D_205c0. sn F_205c4 D_205c4. sn F_205c8 D_205c8.
    sn F_20618 D_20618.
    stepLD8 F_2061c D_2061c ret.
    stepLD8 F_20620 D_20620 (getr regs 8).
    stepLD8 F_20624 D_20624 (getr regs 9).
    stepLD8 F_20628 D_20628 (getr regs 18).
    stepLD8 F_2062c D_2062c (getr regs 19).
    zv F_20630 D_20630 (Z_to_bv 64 s).
    sn F_20634 D_20634.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_hd_ok : hd_ok_spec (0x20660 : word) (0x207dc : word) 0.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x178a4) with (0x178a4 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_20564 D_20564 (Z_to_bv 64 (s - 64)).
    stepST F_20568 D_20568 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_2056c D_2056c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20570 D_20570 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20574 D_20574 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20578 D_20578 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_2057c D_2057c ltac:(condZ).
    zv F_20580 D_20580 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_20584 D_20584 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_20588 D_20588 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_2058c D_2058c.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x2068c : word) ltac:(bveq).
    sn F_20590 D_20590.
    stepb_ft F_20594 D_20594 ltac:(condZ).
    zv F_20598 D_20598 (Z_to_bv 64 pixs).
    sn F_2059c D_2059c.
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x2069c : word) ltac:(bveq).
    stepb_tk F_205a0 D_205a0 ltac:(condZ).                (* [comment removed for export] *)
    zv F_20638 D_20638 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_2063c D_2063c.                                   (* [comment removed for export] *)
    stepb_ft F_20640 D_20640 ltac:(condZ).
    zv F_20644 D_20644 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_20648 D_20648 ltac:(condZ).
    sn F_2064c D_2064c.                                   (* [comment removed for export] *)
    stepb_tk F_20650 D_20650 ltac:(condZ).                (* [comment removed for export] *)
    sn F_206c4 D_206c4. sn F_206c8 D_206c8. sn F_206cc D_206cc. sn F_206d0 D_206d0.
    mvli F_206d4 D_206d4 (Z_to_bv 64 pixs). mvli F_206d8 D_206d8 (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_206dc D_206dc.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segB : segB_spec (0x207dc : word) (0x207e8 : word) PC_pixDilateGray3h.
Proof.
  unfold segB_spec, PC_pixDilateGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x20854) with (0x20854 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_206e0 D_206e0 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_206e4 D_206e4 ltac:(condZ).                (* [comment removed for export] *)
    sn F_206e8 D_206e8.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segC : segC_spec (0x207e8 : word) (0x20838 : word).
Proof.
  unfold segC_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x17b60) with (0x17b60 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_206ec D_206ec (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_206f0 D_206f0.                                   (* [comment removed for export] *)
    sn F_20728 D_20728. sn F_2072c D_2072c. sn F_20730 D_20730. sn F_20734 D_20734.
    sn F_20738 D_20738.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segD : segD_spec (0x20838 : word) (0x20844 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_2073c D_2073c.                                   (* [comment removed for export] *)
    zv F_20740 D_20740 (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_20744 D_20744.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segE : segE_spec (0x20844 : word) (0x2084c : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_20748 D_20748 (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_2074c D_2074c.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segF : segF_spec (0x2084c : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_20750 D_20750.                                   (* [comment removed for export] *)
    sn F_20754 D_20754.                                   (* [comment removed for export] *)
    stepLD F_206a8 D_206a8 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_206ac D_206ac (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_206b0 D_206b0 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_206b4 D_206b4 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_206b8 D_206b8 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_206bc D_206bc (Z_to_bv 64 s).
    stepret F_206c0 D_206c0 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma o_hd_null : hd_null_spec (0x20eb0 : word) 0x10298 0x11010.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_20db4 D_20db4 (Z_to_bv 64 (s - 64)).
    stepST F_20db8 D_20db8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_20dbc D_20dbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20dc0 D_20dc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20dc4 D_20dc4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20dc8 D_20dc8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_20dcc D_20dcc ltac:(condZ).                (* [comment removed for export] *)
    sn F_20e1c D_20e1c.
    stepLD F_20e20 D_20e20 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_20e24 D_20e24 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_20e28 D_20e28.
    stepb_ft F_20e2c D_20e2c ltac:(condZ).                (* [comment removed for export] *)
    sn F_20e30 D_20e30. sn F_20e34 D_20e34. sn F_20e38 D_20e38. sn F_20e3c D_20e3c. sn F_20e40 D_20e40.
    sn F_20e68 D_20e68.
    stepLD8 F_20e6c D_20e6c ret.
    stepLD8 F_20e70 D_20e70 (getr regs 8).
    stepLD8 F_20e74 D_20e74 (getr regs 9).
    stepLD8 F_20e78 D_20e78 (getr regs 18).
    stepLD8 F_20e7c D_20e7c (getr regs 19).
    zv F_20e80 D_20e80 (Z_to_bv 64 s).
    sn F_20e84 D_20e84.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_hd_depth : hd_depth_spec (0x20eb0 : word) 0x10d0b 0x11010.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_20db4 D_20db4 (Z_to_bv 64 (s - 64)).
    stepST F_20db8 D_20db8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_20dbc D_20dbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20dc0 D_20dc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20dc4 D_20dc4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20dc8 D_20dc8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_20dcc D_20dcc ltac:(condZ).                (* [comment removed for export] *)
    sn F_20dd0 D_20dd0. sn F_20dd4 D_20dd4.               (* [comment removed for export] *)
    zv F_20dd8 D_20dd8 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_20ddc D_20ddc.                                   (* [comment removed for export] *)
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_167bc D_167bc (0x20edc : word) ltac:(bveq).
    sn F_20de0 D_20de0.                                   (* [comment removed for export] *)
    stepb_tk F_20de4 D_20de4 ltac:(condZ).                (* [comment removed for export] *)
    sn F_20e44 D_20e44.
    stepLD F_20e48 D_20e48 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_20e4c D_20e4c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_20e50 D_20e50.
    stepb_ft F_20e54 D_20e54 ltac:(condZ).
    sn F_20e58 D_20e58. sn F_20e5c D_20e5c. sn F_20e60 D_20e60. sn F_20e64 D_20e64.
    sn F_20e68 D_20e68.
    stepLD8 F_20e6c D_20e6c ret.
    stepLD8 F_20e70 D_20e70 (getr regs 8).
    stepLD8 F_20e74 D_20e74 (getr regs 9).
    stepLD8 F_20e78 D_20e78 (getr regs 18).
    stepLD8 F_20e7c D_20e7c (getr regs 19).
    zv F_20e80 D_20e80 (Z_to_bv 64 s).
    sn F_20e84 D_20e84.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_hd_cmap : hd_cmap_spec (0x20eb0 : word) 0x10803 0x11010.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_20db4 D_20db4 (Z_to_bv 64 (s - 64)).
    stepST F_20db8 D_20db8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_20dbc D_20dbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20dc0 D_20dc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20dc4 D_20dc4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20dc8 D_20dc8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_20dcc D_20dcc ltac:(condZ).
    sn F_20dd0 D_20dd0. sn F_20dd4 D_20dd4.
    zv F_20dd8 D_20dd8 (Z_to_bv 64 pixs).
    sn F_20ddc D_20ddc.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x20edc : word) ltac:(bveq).
    sn F_20de0 D_20de0.
    stepb_ft F_20de4 D_20de4 ltac:(condZ).                (* [comment removed for export] *)
    zv F_20de8 D_20de8 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_20dec D_20dec.                                   (* [comment removed for export] *)
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x20eec : word) ltac:(bveq).
    stepb_ft F_20df0 D_20df0 ltac:(condZ).                (* [comment removed for export] *)
    sn F_20df4 D_20df4.
    stepLD F_20df8 D_20df8 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_20dfc D_20dfc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_20e00 D_20e00.
    stepb_ft F_20e04 D_20e04 ltac:(condZ).
    sn F_20e08 D_20e08. sn F_20e0c D_20e0c. sn F_20e10 D_20e10. sn F_20e14 D_20e14. sn F_20e18 D_20e18.
    sn F_20e68 D_20e68.
    stepLD8 F_20e6c D_20e6c ret.
    stepLD8 F_20e70 D_20e70 (getr regs 8).
    stepLD8 F_20e74 D_20e74 (getr regs 9).
    stepLD8 F_20e78 D_20e78 (getr regs 18).
    stepLD8 F_20e7c D_20e7c (getr regs 19).
    zv F_20e80 D_20e80 (Z_to_bv 64 s).
    sn F_20e84 D_20e84.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_hd_ok : hd_ok_spec (0x20eb0 : word) (0x2102c : word) 255.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x178a4) with (0x178a4 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_20db4 D_20db4 (Z_to_bv 64 (s - 64)).
    stepST F_20db8 D_20db8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_20dbc D_20dbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_20dc0 D_20dc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_20dc4 D_20dc4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_20dc8 D_20dc8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_20dcc D_20dcc ltac:(condZ).
    zv F_20dd0 D_20dd0 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_20dd4 D_20dd4 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_20dd8 D_20dd8 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_20ddc D_20ddc.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x20edc : word) ltac:(bveq).
    sn F_20de0 D_20de0.
    stepb_ft F_20de4 D_20de4 ltac:(condZ).
    zv F_20de8 D_20de8 (Z_to_bv 64 pixs).
    sn F_20dec D_20dec.
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x20eec : word) ltac:(bveq).
    stepb_tk F_20df0 D_20df0 ltac:(condZ).                (* [comment removed for export] *)
    zv F_20e88 D_20e88 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_20e8c D_20e8c.                                   (* [comment removed for export] *)
    stepb_ft F_20e90 D_20e90 ltac:(condZ).
    zv F_20e94 D_20e94 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_20e98 D_20e98 ltac:(condZ).
    sn F_20e9c D_20e9c.                                   (* [comment removed for export] *)
    stepb_tk F_20ea0 D_20ea0 ltac:(condZ).                (* [comment removed for export] *)
    sn F_20f14 D_20f14. sn F_20f18 D_20f18. sn F_20f1c D_20f1c. sn F_20f20 D_20f20.
    mvli F_20f24 D_20f24 (Z_to_bv 64 pixs). mvli F_20f28 D_20f28 (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_20f2c D_20f2c.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segB : segB_spec (0x2102c : word) (0x21038 : word) PC_pixErodeGray3h.
Proof.
  unfold segB_spec, PC_pixErodeGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x20004) with (0x20004 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_20f30 D_20f30 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_20f34 D_20f34 ltac:(condZ).                (* [comment removed for export] *)
    sn F_20f38 D_20f38.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segD : segD_spec (0x2110c : word) (0x21118 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_21010 D_21010.                                   (* [comment removed for export] *)
    zv F_21014 D_21014 (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_21018 D_21018.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segE : segE_spec (0x21118 : word) (0x21120 : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_2101c D_2101c (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_21020 D_21020.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segF : segF_spec (0x21120 : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_21024 D_21024.                                   (* [comment removed for export] *)
    sn F_21028 D_21028.                                   (* [comment removed for export] *)
    stepLD F_20ef8 D_20ef8 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_20efc D_20efc (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_20f00 D_20f00 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_20f04 D_20f04 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_20f08 D_20f08 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_20f0c D_20f0c (Z_to_bv 64 s).
    stepret F_20f10 D_20f10 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC1 : segC1_spec (0x21038 : word) (0x21058 : word) 0.
Proof.
  unfold segC1_spec, PC_pixSetBorderVal. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x17344) with (0x17344 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - zv F_20f3c D_20f3c (Z_to_bv 64 a0v).                  (* [comment removed for export] *)
    stepST F_20f40 D_20f40 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_20f44 D_20f44. sn F_20f48 D_20f48. sn F_20f4c D_20f4c. sn F_20f50 D_20f50. sn F_20f54 D_20f54.
    sn F_20f58 D_20f58.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC2 : segC2_spec (0x21058 : word) (0x21060 : word) PC_pixDilateGray3h.
Proof.
  unfold segC2_spec, PC_pixDilateGray3h. intros rom regs m s Hs Hs64 H2.
  replace (Z_to_bv 64 0x20854) with (0x20854 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - sn F_20f5c D_20f5c.                                   (* [comment removed for export] *)
    sn F_20f60 D_20f60.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC3 : segC3_spec (0x21060 : word) (0x210f4 : word).
Proof.
  unfold segC3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  eexists. split.
  - sn F_20f64 D_20f64.                                   (* [comment removed for export] *)
    stepST F_20fec D_20fec (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_20ff0 D_20ff0 (Z_to_bv 64 (s - 48)).             (* [comment removed for export] *)
    sn F_20ff4 D_20ff4.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC4 : segC4_spec (0x210f4 : word) (0x2110c : word).
Proof.
  unfold segC4_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha Rc H2.
  replace (Z_to_bv 64 0x17b60) with (0x17b60 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepLD F_20ff8 D_20ff8 (Z_to_le_bytes 8 a0v) (Z_to_bv 64 a0v) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rc) ltac:(apply W2Lib.lez8; lia).
    sn F_20ffc D_20ffc. sn F_21000 D_21000. sn F_21004 D_21004. sn F_21008 D_21008.
    sn F_2100c D_2100c.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_hd_null : hd_null_spec (0x21128 : word) 0x10298 0x10814.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_2102c D_2102c (Z_to_bv 64 (s - 64)).
    stepST F_21030 D_21030 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_21034 D_21034 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_21038 D_21038 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_2103c D_2103c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_21040 D_21040 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_21044 D_21044 ltac:(condZ).                (* [comment removed for export] *)
    sn F_21094 D_21094.
    stepLD F_21098 D_21098 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_2109c D_2109c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_210a0 D_210a0.
    stepb_ft F_210a4 D_210a4 ltac:(condZ).                (* [comment removed for export] *)
    sn F_210a8 D_210a8. sn F_210ac D_210ac. sn F_210b0 D_210b0. sn F_210b4 D_210b4. sn F_210b8 D_210b8.
    sn F_210e0 D_210e0.
    stepLD8 F_210e4 D_210e4 ret.
    stepLD8 F_210e8 D_210e8 (getr regs 8).
    stepLD8 F_210ec D_210ec (getr regs 9).
    stepLD8 F_210f0 D_210f0 (getr regs 18).
    stepLD8 F_210f4 D_210f4 (getr regs 19).
    zv F_210f8 D_210f8 (Z_to_bv 64 s).
    sn F_210fc D_210fc.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_hd_depth : hd_depth_spec (0x21128 : word) 0x10d0b 0x10814.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_2102c D_2102c (Z_to_bv 64 (s - 64)).
    stepST F_21030 D_21030 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_21034 D_21034 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_21038 D_21038 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_2103c D_2103c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_21040 D_21040 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_21044 D_21044 ltac:(condZ).                (* [comment removed for export] *)
    sn F_21048 D_21048. sn F_2104c D_2104c.               (* [comment removed for export] *)
    zv F_21050 D_21050 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_21054 D_21054.                                   (* [comment removed for export] *)
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_167bc D_167bc (0x21154 : word) ltac:(bveq).
    sn F_21058 D_21058.                                   (* [comment removed for export] *)
    stepb_tk F_2105c D_2105c ltac:(condZ).                (* [comment removed for export] *)
    sn F_210bc D_210bc.
    stepLD F_210c0 D_210c0 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_210c4 D_210c4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_210c8 D_210c8.
    stepb_ft F_210cc D_210cc ltac:(condZ).
    sn F_210d0 D_210d0. sn F_210d4 D_210d4. sn F_210d8 D_210d8. sn F_210dc D_210dc.
    sn F_210e0 D_210e0.
    stepLD8 F_210e4 D_210e4 ret.
    stepLD8 F_210e8 D_210e8 (getr regs 8).
    stepLD8 F_210ec D_210ec (getr regs 9).
    stepLD8 F_210f0 D_210f0 (getr regs 18).
    stepLD8 F_210f4 D_210f4 (getr regs 19).
    zv F_210f8 D_210f8 (Z_to_bv 64 s).
    sn F_210fc D_210fc.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_hd_cmap : hd_cmap_spec (0x21128 : word) 0x10803 0x10814.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_2102c D_2102c (Z_to_bv 64 (s - 64)).
    stepST F_21030 D_21030 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_21034 D_21034 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_21038 D_21038 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_2103c D_2103c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_21040 D_21040 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_21044 D_21044 ltac:(condZ).
    sn F_21048 D_21048. sn F_2104c D_2104c.
    zv F_21050 D_21050 (Z_to_bv 64 pixs).
    sn F_21054 D_21054.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x21154 : word) ltac:(bveq).
    sn F_21058 D_21058.
    stepb_ft F_2105c D_2105c ltac:(condZ).                (* [comment removed for export] *)
    zv F_21060 D_21060 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_21064 D_21064.                                   (* [comment removed for export] *)
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x21164 : word) ltac:(bveq).
    stepb_ft F_21068 D_21068 ltac:(condZ).                (* [comment removed for export] *)
    sn F_2106c D_2106c.
    stepLD F_21070 D_21070 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_21074 D_21074 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_21078 D_21078.
    stepb_ft F_2107c D_2107c ltac:(condZ).
    sn F_21080 D_21080. sn F_21084 D_21084. sn F_21088 D_21088. sn F_2108c D_2108c. sn F_21090 D_21090.
    sn F_210e0 D_210e0.
    stepLD8 F_210e4 D_210e4 ret.
    stepLD8 F_210e8 D_210e8 (getr regs 8).
    stepLD8 F_210ec D_210ec (getr regs 9).
    stepLD8 F_210f0 D_210f0 (getr regs 18).
    stepLD8 F_210f4 D_210f4 (getr regs 19).
    zv F_210f8 D_210f8 (Z_to_bv 64 s).
    sn F_210fc D_210fc.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_hd_ok : hd_ok_spec (0x21128 : word) (0x212a4 : word) 0.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x178a4) with (0x178a4 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_2102c D_2102c (Z_to_bv 64 (s - 64)).
    stepST F_21030 D_21030 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_21034 D_21034 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_21038 D_21038 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_2103c D_2103c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_21040 D_21040 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_21044 D_21044 ltac:(condZ).
    zv F_21048 D_21048 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_2104c D_2104c (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_21050 D_21050 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_21054 D_21054.
    stepb_ft F_167b4 D_167b4 ltac:(condZ).
    stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_167bc D_167bc (0x21154 : word) ltac:(bveq).
    sn F_21058 D_21058.
    stepb_ft F_2105c D_2105c ltac:(condZ).
    zv F_21060 D_21060 (Z_to_bv 64 pixs).
    sn F_21064 D_21064.
    stepb_ft F_168b4 D_168b4 ltac:(condZ).
    stepLD F_168b8 D_168b8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_168bc D_168bc (0x21164 : word) ltac:(bveq).
    stepb_tk F_21068 D_21068 ltac:(condZ).                (* [comment removed for export] *)
    zv F_21100 D_21100 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_21104 D_21104.                                   (* [comment removed for export] *)
    stepb_ft F_21108 D_21108 ltac:(condZ).
    zv F_2110c D_2110c (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_21110 D_21110 ltac:(condZ).
    sn F_21114 D_21114.                                   (* [comment removed for export] *)
    stepb_tk F_21118 D_21118 ltac:(condZ).                (* [comment removed for export] *)
    sn F_2118c D_2118c. sn F_21190 D_21190. sn F_21194 D_21194. sn F_21198 D_21198.
    mvli F_2119c D_2119c (Z_to_bv 64 pixs). mvli F_211a0 D_211a0 (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_211a4 D_211a4.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segB : segB_spec (0x212a4 : word) (0x212b0 : word) PC_pixDilateGray3h.
Proof.
  unfold segB_spec, PC_pixDilateGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x20854) with (0x20854 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_211a8 D_211a8 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_211ac D_211ac ltac:(condZ).                (* [comment removed for export] *)
    sn F_211b0 D_211b0.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segD : segD_spec (0x21384 : word) (0x21390 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_21288 D_21288.                                   (* [comment removed for export] *)
    zv F_2128c D_2128c (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_21290 D_21290.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segE : segE_spec (0x21390 : word) (0x21398 : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_21294 D_21294 (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_21298 D_21298.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segF : segF_spec (0x21398 : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_2129c D_2129c.                                   (* [comment removed for export] *)
    sn F_212a0 D_212a0.                                   (* [comment removed for export] *)
    stepLD F_21170 D_21170 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_21174 D_21174 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_21178 D_21178 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_2117c D_2117c (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_21180 D_21180 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_21184 D_21184 (Z_to_bv 64 s).
    stepret F_21188 D_21188 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC1 : segC1_spec (0x212b0 : word) (0x212d0 : word) 255.
Proof.
  unfold segC1_spec, PC_pixSetBorderVal. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x17344) with (0x17344 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - zv F_211b4 D_211b4 (Z_to_bv 64 a0v).                  (* [comment removed for export] *)
    stepST F_211b8 D_211b8 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_211bc D_211bc. sn F_211c0 D_211c0. sn F_211c4 D_211c4. sn F_211c8 D_211c8. sn F_211cc D_211cc.
    sn F_211d0 D_211d0.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC2 : segC2_spec (0x212d0 : word) (0x212d8 : word) PC_pixErodeGray3h.
Proof.
  unfold segC2_spec, PC_pixErodeGray3h. intros rom regs m s Hs Hs64 H2.
  replace (Z_to_bv 64 0x20004) with (0x20004 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - sn F_211d4 D_211d4.                                   (* [comment removed for export] *)
    sn F_211d8 D_211d8.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC3 : segC3_spec (0x212d8 : word) (0x2136c : word).
Proof.
  unfold segC3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  eexists. split.
  - sn F_211dc D_211dc.                                   (* [comment removed for export] *)
    stepST F_21264 D_21264 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_21268 D_21268 (Z_to_bv 64 (s - 48)).             (* [comment removed for export] *)
    sn F_2126c D_2126c.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC4 : segC4_spec (0x2136c : word) (0x21384 : word).
Proof.
  unfold segC4_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha Rc H2.
  replace (Z_to_bv 64 0x17b60) with (0x17b60 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepLD F_21270 D_21270 (Z_to_le_bytes 8 a0v) (Z_to_bv 64 a0v) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rc) ltac:(apply W2Lib.lez8; lia).
    sn F_21274 D_21274. sn F_21278 D_21278. sn F_2127c D_2127c. sn F_21280 D_21280.
    sn F_21284 D_21284.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str_pixs_nd : str16 0x10298 16. Proof. str16_tac. Qed.
Lemma str_not8 : str16 0x10d0b 14. Proof. str16_tac. Qed.
Lemma str_hascmap : str16 0x10803 16. Proof. str16_tac. Qed.
Lemma str_pixErodeGray3 : str16 0x1061e 13. Proof. str16_tac. Qed.
Lemma str_pixDilateGray3 : str16 0x104ae 14. Proof. str16_tac. Qed.
Lemma str_pixOpenGray3 : str16 0x11010 12. Proof. str16_tac. Qed.
Lemma str_pixCloseGray3 : str16 0x10814 13. Proof. str16_tac. Qed.

Lemma G3E_W : gray3h_contract PC_pixErodeGray3h RK_pixcopy RB_pixcopy14.
Proof. exact (G3E.gray3h_W RK_pixcopy RB_pixcopy14 pixCreateTemplate_sure_W). Qed.
Lemma G3D_W : gray3h_contract PC_pixDilateGray3h RK_pixcopy RB_pixcopy14.
Proof. exact (G3D.gray3h_W RK_pixcopy RB_pixcopy14 pixCreateTemplate_sure_W). Qed.

Ltac rok := red; apply bv_eq; reflexivity.

Section Final.
Hypothesis ABG : pixAddBorderGeneral_contract.
Hypothesis RBG : pixRemoveBorderGeneral_contract.
Hypothesis RBGn : pixRemoveBorderGeneral_null_contract.

Theorem pixErodeGray3_W : gray3_contract PC_pixErodeGray3 RK_gm3 RB_gm3.
Proof.
  apply (drv_W (0x1fe10 : word) (0x1ff8c : word) 255 0x10d0b 0x10803 0x1061e 14 16 13 e_hd_depth e_hd_cmap e_hd_ok ltac:(rok) str_not8 str_hascmap str_pixErodeGray3
           (or_intror eq_refl) ABG PC_pixErodeGray3 RK_gm3 RB_gm3 ltac:(apply bv_eq; reflexivity)).
  - assert (0 <= RK_pixcopy)%Z by (clear; room_consts; lia). unfold RK_gm3. lia.
  - assert (0 <= RB_pixcopy14)%Z by (clear; room_consts; lia). unfold RB_gm3. lia.
  - intros C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8. split.
    + eapply mid3_ok; first [exact e_segB | exact e_segC | exact e_segD | exact e_segE | exact e_segF | exact RBG | exact G3E_W | exact HK8 | eassumption | reflexivity | rok].
    + eapply mid3_null; first [exact e_segB | exact e_segC | exact e_segD | exact e_segE | exact e_segF | exact RBGn | exact G3E.gray3h_null_W | exact HK8 | eassumption | reflexivity | rok].
Qed.
Theorem pixDilateGray3_W : gray3_contract PC_pixDilateGray3 RK_gm3 RB_gm3.
Proof.
  apply (drv_W (0x20660 : word) (0x207dc : word) 0 0x10d0b 0x10803 0x104ae 14 16 14 d_hd_depth d_hd_cmap d_hd_ok ltac:(rok) str_not8 str_hascmap str_pixDilateGray3
           (or_introl eq_refl) ABG PC_pixDilateGray3 RK_gm3 RB_gm3 ltac:(apply bv_eq; reflexivity)).
  - assert (0 <= RK_pixcopy)%Z by (clear; room_consts; lia). unfold RK_gm3. lia.
  - assert (0 <= RB_pixcopy14)%Z by (clear; room_consts; lia). unfold RB_gm3. lia.
  - intros C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8. split.
    + eapply mid3_ok; first [exact d_segB | exact d_segC | exact d_segD | exact d_segE | exact d_segF | exact RBG | exact G3D_W | exact HK8 | eassumption | reflexivity | rok].
    + eapply mid3_null; first [exact d_segB | exact d_segC | exact d_segD | exact d_segE | exact d_segF | exact RBGn | exact G3D.gray3h_null_W | exact HK8 | eassumption | reflexivity | rok].
Qed.

Theorem pixOpenGray3_W : gray3_contract PC_pixOpenGray3 RK_gm4 RB_gm4.
Proof.
  apply (drv_W (0x20eb0 : word) (0x2102c : word) 255 0x10d0b 0x10803 0x11010 14 16 12 o_hd_depth o_hd_cmap o_hd_ok ltac:(rok) str_not8 str_hascmap str_pixOpenGray3
           (or_intror eq_refl) ABG PC_pixOpenGray3 RK_gm4 RB_gm4 ltac:(apply bv_eq; reflexivity)).
  - assert (0 <= RK_pixcopy)%Z by (clear; room_consts; lia). unfold RK_gm4. lia.
  - assert (0 <= RB_pixcopy14)%Z by (clear; room_consts; lia). unfold RB_gm4. lia.
  - intros C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8. split.
    + eapply mid4_ok; first [exact o_segB | exact o_segC1 | exact o_segC2 | exact o_segC3 | exact o_segC4 | exact o_segD | exact o_segE | exact o_segF
                             | exact RBG | exact G3E_W | exact G3D_W | exact HK8 | eassumption | reflexivity | rok | lia].
    + eapply mid4_null; first [exact o_segB | exact o_segC1 | exact o_segC2 | exact o_segC3 | exact o_segC4 | exact o_segD | exact o_segE | exact o_segF
                               | exact RBGn | exact G3E.gray3h_null_W | exact G3D.gray3h_null_W | exact HK8 | eassumption | reflexivity | rok | lia].
Qed.

Theorem pixCloseGray3_W : gray3_contract PC_pixCloseGray3 RK_gm4 RB_gm4.
Proof.
  apply (drv_W (0x21128 : word) (0x212a4 : word) 0 0x10d0b 0x10803 0x10814 14 16 13 c_hd_depth c_hd_cmap c_hd_ok ltac:(rok) str_not8 str_hascmap str_pixCloseGray3
           (or_introl eq_refl) ABG PC_pixCloseGray3 RK_gm4 RB_gm4 ltac:(apply bv_eq; reflexivity)).
  - assert (0 <= RK_pixcopy)%Z by (clear; room_consts; lia). unfold RK_gm4. lia.
  - assert (0 <= RB_pixcopy14)%Z by (clear; room_consts; lia). unfold RB_gm4. lia.
  - intros C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8. split.
    + eapply mid4_ok; first [exact c_segB | exact c_segC1 | exact c_segC2 | exact c_segC3 | exact c_segC4 | exact c_segD | exact c_segE | exact c_segF
                             | exact RBG | exact G3D_W | exact G3E_W | exact HK8 | eassumption | reflexivity | rok | lia].
    + eapply mid4_null; first [exact c_segB | exact c_segC1 | exact c_segC2 | exact c_segC3 | exact c_segC4 | exact c_segD | exact c_segE | exact c_segF
                               | exact RBGn | exact G3D.gray3h_null_W | exact G3E.gray3h_null_W | exact HK8 | eassumption | reflexivity | rok | lia].
Qed.
End Final.

(* [comment removed for export] *)
Theorem pixErodeGray3_null_W : gray3_null_contract PC_pixErodeGray3.
Proof. exact (drv_null_W (0x1fe10 : word) 0x10298 0x1061e 16 13 e_hd_null str_pixs_nd str_pixErodeGray3 PC_pixErodeGray3 ltac:(apply bv_eq; reflexivity)). Qed.
Theorem pixDilateGray3_null_W : gray3_null_contract PC_pixDilateGray3.
Proof. exact (drv_null_W (0x20660 : word) 0x10298 0x104ae 16 14 d_hd_null str_pixs_nd str_pixDilateGray3 PC_pixDilateGray3 ltac:(apply bv_eq; reflexivity)). Qed.
Theorem pixOpenGray3_null_W : gray3_null_contract PC_pixOpenGray3.
Proof. exact (drv_null_W (0x20eb0 : word) 0x10298 0x11010 16 12 o_hd_null str_pixs_nd str_pixOpenGray3 PC_pixOpenGray3 ltac:(apply bv_eq; reflexivity)). Qed.
Theorem pixCloseGray3_null_W : gray3_null_contract PC_pixCloseGray3.
Proof. exact (drv_null_W (0x21128 : word) 0x10298 0x10814 16 13 c_hd_null str_pixs_nd str_pixCloseGray3 PC_pixCloseGray3 ltac:(apply bv_eq; reflexivity)). Qed.

End GrayDrvI.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
