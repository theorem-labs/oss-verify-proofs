(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoom14 GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptStderr V14LeptBase V14LeptUb.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14CL7a.
Import V14CL7a.V14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptPixHdr V14LeptCmap2 V14LeptPixCopy V14LeptGrayD_iface V14LeptGrayA V14LeptGrayD V14_code_gmD_drv V14LeptGrayDrv.
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
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mvli F D v := first [zv F D v | sn F D].

Lemma e_hd_null : hd_null_spec (0x2724c : word) 0x10298 0x1061e.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_27150 D_27150 (Z_to_bv 64 (s - 64)).
    stepST F_27154 D_27154 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_27158 D_27158 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_2715c D_2715c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_27160 D_27160 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_27164 D_27164 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_27168 D_27168 ltac:(condZ).                (* [comment removed for export] *)
    sn F_271b8 D_271b8.
    stepLD F_271bc D_271bc (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_271c0 D_271c0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_271c4 D_271c4.
    stepb_ft F_271c8 D_271c8 ltac:(condZ).                (* [comment removed for export] *)
    sn F_271cc D_271cc. sn F_271d0 D_271d0. sn F_271d4 D_271d4. sn F_271d8 D_271d8. sn F_271dc D_271dc.
    sn F_27204 D_27204.
    stepLD8 F_27208 D_27208 ret.
    stepLD8 F_2720c D_2720c (getr regs 8).
    stepLD8 F_27210 D_27210 (getr regs 9).
    stepLD8 F_27214 D_27214 (getr regs 18).
    stepLD8 F_27218 D_27218 (getr regs 19).
    zv F_2721c D_2721c (Z_to_bv 64 s).
    sn F_27220 D_27220.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_hd_depth : hd_depth_spec (0x2724c : word) 0x10d0b 0x1061e.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_27150 D_27150 (Z_to_bv 64 (s - 64)).
    stepST F_27154 D_27154 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_27158 D_27158 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_2715c D_2715c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_27160 D_27160 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_27164 D_27164 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_27168 D_27168 ltac:(condZ).                (* [comment removed for export] *)
    sn F_2716c D_2716c. sn F_27170 D_27170.               (* [comment removed for export] *)
    zv F_27174 D_27174 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_27178 D_27178.                                   (* [comment removed for export] *)
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_16c50 D_16c50 (0x27278 : word) ltac:(bveq).
    sn F_2717c D_2717c.                                   (* [comment removed for export] *)
    stepb_tk F_27180 D_27180 ltac:(condZ).                (* [comment removed for export] *)
    sn F_271e0 D_271e0.
    stepLD F_271e4 D_271e4 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_271e8 D_271e8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_271ec D_271ec.
    stepb_ft F_271f0 D_271f0 ltac:(condZ).
    sn F_271f4 D_271f4. sn F_271f8 D_271f8. sn F_271fc D_271fc. sn F_27200 D_27200.
    sn F_27204 D_27204.
    stepLD8 F_27208 D_27208 ret.
    stepLD8 F_2720c D_2720c (getr regs 8).
    stepLD8 F_27210 D_27210 (getr regs 9).
    stepLD8 F_27214 D_27214 (getr regs 18).
    stepLD8 F_27218 D_27218 (getr regs 19).
    zv F_2721c D_2721c (Z_to_bv 64 s).
    sn F_27220 D_27220.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_hd_cmap : hd_cmap_spec (0x2724c : word) 0x10803 0x1061e.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_27150 D_27150 (Z_to_bv 64 (s - 64)).
    stepST F_27154 D_27154 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_27158 D_27158 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_2715c D_2715c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_27160 D_27160 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_27164 D_27164 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_27168 D_27168 ltac:(condZ).
    sn F_2716c D_2716c. sn F_27170 D_27170.
    zv F_27174 D_27174 (Z_to_bv 64 pixs).
    sn F_27178 D_27178.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x27278 : word) ltac:(bveq).
    sn F_2717c D_2717c.
    stepb_ft F_27180 D_27180 ltac:(condZ).                (* [comment removed for export] *)
    zv F_27184 D_27184 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_27188 D_27188.                                   (* [comment removed for export] *)
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x27288 : word) ltac:(bveq).
    stepb_ft F_2718c D_2718c ltac:(condZ).                (* [comment removed for export] *)
    sn F_27190 D_27190.
    stepLD F_27194 D_27194 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_27198 D_27198 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_2719c D_2719c.
    stepb_ft F_271a0 D_271a0 ltac:(condZ).
    sn F_271a4 D_271a4. sn F_271a8 D_271a8. sn F_271ac D_271ac. sn F_271b0 D_271b0. sn F_271b4 D_271b4.
    sn F_27204 D_27204.
    stepLD8 F_27208 D_27208 ret.
    stepLD8 F_2720c D_2720c (getr regs 8).
    stepLD8 F_27210 D_27210 (getr regs 9).
    stepLD8 F_27214 D_27214 (getr regs 18).
    stepLD8 F_27218 D_27218 (getr regs 19).
    zv F_2721c D_2721c (Z_to_bv 64 s).
    sn F_27220 D_27220.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_hd_ok : hd_ok_spec (0x2724c : word) (0x273c8 : word) 255.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x18424) with (0x18424 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_27150 D_27150 (Z_to_bv 64 (s - 64)).
    stepST F_27154 D_27154 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_27158 D_27158 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_2715c D_2715c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_27160 D_27160 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_27164 D_27164 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_27168 D_27168 ltac:(condZ).
    zv F_2716c D_2716c (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_27170 D_27170 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_27174 D_27174 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_27178 D_27178.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x27278 : word) ltac:(bveq).
    sn F_2717c D_2717c.
    stepb_ft F_27180 D_27180 ltac:(condZ).
    zv F_27184 D_27184 (Z_to_bv 64 pixs).
    sn F_27188 D_27188.
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x27288 : word) ltac:(bveq).
    stepb_tk F_2718c D_2718c ltac:(condZ).                (* [comment removed for export] *)
    zv F_27224 D_27224 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_27228 D_27228.                                   (* [comment removed for export] *)
    stepb_ft F_2722c D_2722c ltac:(condZ).
    zv F_27230 D_27230 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_27234 D_27234 ltac:(condZ).
    sn F_27238 D_27238.                                   (* [comment removed for export] *)
    stepb_tk F_2723c D_2723c ltac:(condZ).                (* [comment removed for export] *)
    sn F_272b0 D_272b0. sn F_272b4 D_272b4. sn F_272b8 D_272b8. sn F_272bc D_272bc.
    mvli F_272c0 D_272c0 (Z_to_bv 64 pixs). mvli F_272c4 D_272c4 (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_272c8 D_272c8.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segB : segB_spec (0x273c8 : word) (0x273d4 : word) PC_pixErodeGray3h.
Proof.
  unfold segB_spec, PC_pixErodeGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x27440) with (0x27440 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_272cc D_272cc (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_272d0 D_272d0 ltac:(condZ).                (* [comment removed for export] *)
    sn F_272d4 D_272d4.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segC : segC_spec (0x273d4 : word) (0x27424 : word).
Proof.
  unfold segC_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x18720) with (0x18720 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_272d8 D_272d8 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_272dc D_272dc.                                   (* [comment removed for export] *)
    sn F_27314 D_27314. sn F_27318 D_27318. sn F_2731c D_2731c. sn F_27320 D_27320.
    sn F_27324 D_27324.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segD : segD_spec (0x27424 : word) (0x27430 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_27328 D_27328.                                   (* [comment removed for export] *)
    zv F_2732c D_2732c (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_27330 D_27330.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segE : segE_spec (0x27430 : word) (0x27438 : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_27334 D_27334 (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_27338 D_27338.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma e_segF : segF_spec (0x27438 : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_2733c D_2733c.                                   (* [comment removed for export] *)
    sn F_27340 D_27340.                                   (* [comment removed for export] *)
    stepLD F_27294 D_27294 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_27298 D_27298 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_2729c D_2729c (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_272a0 D_272a0 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_272a4 D_272a4 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_272a8 D_272a8 (Z_to_bv 64 s).
    stepret F_272ac D_272ac ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma d_hd_null : hd_null_spec (0x28214 : word) 0x10298 0x104ae.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_28118 D_28118 (Z_to_bv 64 (s - 64)).
    stepST F_2811c D_2811c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_28120 D_28120 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_28124 D_28124 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_28128 D_28128 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2812c D_2812c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_28130 D_28130 ltac:(condZ).                (* [comment removed for export] *)
    sn F_28180 D_28180.
    stepLD F_28184 D_28184 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_28188 D_28188 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_2818c D_2818c.
    stepb_ft F_28190 D_28190 ltac:(condZ).                (* [comment removed for export] *)
    sn F_28194 D_28194. sn F_28198 D_28198. sn F_2819c D_2819c. sn F_281a0 D_281a0. sn F_281a4 D_281a4.
    sn F_281cc D_281cc.
    stepLD8 F_281d0 D_281d0 ret.
    stepLD8 F_281d4 D_281d4 (getr regs 8).
    stepLD8 F_281d8 D_281d8 (getr regs 9).
    stepLD8 F_281dc D_281dc (getr regs 18).
    stepLD8 F_281e0 D_281e0 (getr regs 19).
    zv F_281e4 D_281e4 (Z_to_bv 64 s).
    sn F_281e8 D_281e8.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_hd_depth : hd_depth_spec (0x28214 : word) 0x10d0b 0x104ae.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_28118 D_28118 (Z_to_bv 64 (s - 64)).
    stepST F_2811c D_2811c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_28120 D_28120 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_28124 D_28124 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_28128 D_28128 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2812c D_2812c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_28130 D_28130 ltac:(condZ).                (* [comment removed for export] *)
    sn F_28134 D_28134. sn F_28138 D_28138.               (* [comment removed for export] *)
    zv F_2813c D_2813c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_28140 D_28140.                                   (* [comment removed for export] *)
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_16c50 D_16c50 (0x28240 : word) ltac:(bveq).
    sn F_28144 D_28144.                                   (* [comment removed for export] *)
    stepb_tk F_28148 D_28148 ltac:(condZ).                (* [comment removed for export] *)
    sn F_281a8 D_281a8.
    stepLD F_281ac D_281ac (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_281b0 D_281b0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_281b4 D_281b4.
    stepb_ft F_281b8 D_281b8 ltac:(condZ).
    sn F_281bc D_281bc. sn F_281c0 D_281c0. sn F_281c4 D_281c4. sn F_281c8 D_281c8.
    sn F_281cc D_281cc.
    stepLD8 F_281d0 D_281d0 ret.
    stepLD8 F_281d4 D_281d4 (getr regs 8).
    stepLD8 F_281d8 D_281d8 (getr regs 9).
    stepLD8 F_281dc D_281dc (getr regs 18).
    stepLD8 F_281e0 D_281e0 (getr regs 19).
    zv F_281e4 D_281e4 (Z_to_bv 64 s).
    sn F_281e8 D_281e8.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_hd_cmap : hd_cmap_spec (0x28214 : word) 0x10803 0x104ae.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_28118 D_28118 (Z_to_bv 64 (s - 64)).
    stepST F_2811c D_2811c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_28120 D_28120 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_28124 D_28124 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_28128 D_28128 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2812c D_2812c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_28130 D_28130 ltac:(condZ).
    sn F_28134 D_28134. sn F_28138 D_28138.
    zv F_2813c D_2813c (Z_to_bv 64 pixs).
    sn F_28140 D_28140.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x28240 : word) ltac:(bveq).
    sn F_28144 D_28144.
    stepb_ft F_28148 D_28148 ltac:(condZ).                (* [comment removed for export] *)
    zv F_2814c D_2814c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_28150 D_28150.                                   (* [comment removed for export] *)
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x28250 : word) ltac:(bveq).
    stepb_ft F_28154 D_28154 ltac:(condZ).                (* [comment removed for export] *)
    sn F_28158 D_28158.
    stepLD F_2815c D_2815c (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_28160 D_28160 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_28164 D_28164.
    stepb_ft F_28168 D_28168 ltac:(condZ).
    sn F_2816c D_2816c. sn F_28170 D_28170. sn F_28174 D_28174. sn F_28178 D_28178. sn F_2817c D_2817c.
    sn F_281cc D_281cc.
    stepLD8 F_281d0 D_281d0 ret.
    stepLD8 F_281d4 D_281d4 (getr regs 8).
    stepLD8 F_281d8 D_281d8 (getr regs 9).
    stepLD8 F_281dc D_281dc (getr regs 18).
    stepLD8 F_281e0 D_281e0 (getr regs 19).
    zv F_281e4 D_281e4 (Z_to_bv 64 s).
    sn F_281e8 D_281e8.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_hd_ok : hd_ok_spec (0x28214 : word) (0x28390 : word) 0.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x18424) with (0x18424 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_28118 D_28118 (Z_to_bv 64 (s - 64)).
    stepST F_2811c D_2811c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_28120 D_28120 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_28124 D_28124 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_28128 D_28128 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2812c D_2812c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_28130 D_28130 ltac:(condZ).
    zv F_28134 D_28134 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_28138 D_28138 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_2813c D_2813c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_28140 D_28140.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x28240 : word) ltac:(bveq).
    sn F_28144 D_28144.
    stepb_ft F_28148 D_28148 ltac:(condZ).
    zv F_2814c D_2814c (Z_to_bv 64 pixs).
    sn F_28150 D_28150.
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x28250 : word) ltac:(bveq).
    stepb_tk F_28154 D_28154 ltac:(condZ).                (* [comment removed for export] *)
    zv F_281ec D_281ec (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_281f0 D_281f0.                                   (* [comment removed for export] *)
    stepb_ft F_281f4 D_281f4 ltac:(condZ).
    zv F_281f8 D_281f8 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_281fc D_281fc ltac:(condZ).
    sn F_28200 D_28200.                                   (* [comment removed for export] *)
    stepb_tk F_28204 D_28204 ltac:(condZ).                (* [comment removed for export] *)
    sn F_28278 D_28278. sn F_2827c D_2827c. sn F_28280 D_28280. sn F_28284 D_28284.
    mvli F_28288 D_28288 (Z_to_bv 64 pixs). mvli F_2828c D_2828c (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_28290 D_28290.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segB : segB_spec (0x28390 : word) (0x2839c : word) PC_pixDilateGray3h.
Proof.
  unfold segB_spec, PC_pixDilateGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x28408) with (0x28408 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_28294 D_28294 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_28298 D_28298 ltac:(condZ).                (* [comment removed for export] *)
    sn F_2829c D_2829c.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segC : segC_spec (0x2839c : word) (0x283ec : word).
Proof.
  unfold segC_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x18720) with (0x18720 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_282a0 D_282a0 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_282a4 D_282a4.                                   (* [comment removed for export] *)
    sn F_282dc D_282dc. sn F_282e0 D_282e0. sn F_282e4 D_282e4. sn F_282e8 D_282e8.
    sn F_282ec D_282ec.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segD : segD_spec (0x283ec : word) (0x283f8 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_282f0 D_282f0.                                   (* [comment removed for export] *)
    zv F_282f4 D_282f4 (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_282f8 D_282f8.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segE : segE_spec (0x283f8 : word) (0x28400 : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_282fc D_282fc (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_28300 D_28300.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma d_segF : segF_spec (0x28400 : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_28304 D_28304.                                   (* [comment removed for export] *)
    sn F_28308 D_28308.                                   (* [comment removed for export] *)
    stepLD F_2825c D_2825c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_28260 D_28260 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_28264 D_28264 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_28268 D_28268 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_2826c D_2826c (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_28270 D_28270 (Z_to_bv 64 s).
    stepret F_28274 D_28274 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma o_hd_null : hd_null_spec (0x291dc : word) 0x10298 0x11010.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_290e0 D_290e0 (Z_to_bv 64 (s - 64)).
    stepST F_290e4 D_290e4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_290e8 D_290e8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_290ec D_290ec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_290f0 D_290f0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_290f4 D_290f4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_290f8 D_290f8 ltac:(condZ).                (* [comment removed for export] *)
    sn F_29148 D_29148.
    stepLD F_2914c D_2914c (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_29150 D_29150 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_29154 D_29154.
    stepb_ft F_29158 D_29158 ltac:(condZ).                (* [comment removed for export] *)
    sn F_2915c D_2915c. sn F_29160 D_29160. sn F_29164 D_29164. sn F_29168 D_29168. sn F_2916c D_2916c.
    sn F_29194 D_29194.
    stepLD8 F_29198 D_29198 ret.
    stepLD8 F_2919c D_2919c (getr regs 8).
    stepLD8 F_291a0 D_291a0 (getr regs 9).
    stepLD8 F_291a4 D_291a4 (getr regs 18).
    stepLD8 F_291a8 D_291a8 (getr regs 19).
    zv F_291ac D_291ac (Z_to_bv 64 s).
    sn F_291b0 D_291b0.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_hd_depth : hd_depth_spec (0x291dc : word) 0x10d0b 0x11010.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_290e0 D_290e0 (Z_to_bv 64 (s - 64)).
    stepST F_290e4 D_290e4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_290e8 D_290e8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_290ec D_290ec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_290f0 D_290f0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_290f4 D_290f4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_290f8 D_290f8 ltac:(condZ).                (* [comment removed for export] *)
    sn F_290fc D_290fc. sn F_29100 D_29100.               (* [comment removed for export] *)
    zv F_29104 D_29104 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_29108 D_29108.                                   (* [comment removed for export] *)
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_16c50 D_16c50 (0x29208 : word) ltac:(bveq).
    sn F_2910c D_2910c.                                   (* [comment removed for export] *)
    stepb_tk F_29110 D_29110 ltac:(condZ).                (* [comment removed for export] *)
    sn F_29170 D_29170.
    stepLD F_29174 D_29174 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_29178 D_29178 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_2917c D_2917c.
    stepb_ft F_29180 D_29180 ltac:(condZ).
    sn F_29184 D_29184. sn F_29188 D_29188. sn F_2918c D_2918c. sn F_29190 D_29190.
    sn F_29194 D_29194.
    stepLD8 F_29198 D_29198 ret.
    stepLD8 F_2919c D_2919c (getr regs 8).
    stepLD8 F_291a0 D_291a0 (getr regs 9).
    stepLD8 F_291a4 D_291a4 (getr regs 18).
    stepLD8 F_291a8 D_291a8 (getr regs 19).
    zv F_291ac D_291ac (Z_to_bv 64 s).
    sn F_291b0 D_291b0.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_hd_cmap : hd_cmap_spec (0x291dc : word) 0x10803 0x11010.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_290e0 D_290e0 (Z_to_bv 64 (s - 64)).
    stepST F_290e4 D_290e4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_290e8 D_290e8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_290ec D_290ec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_290f0 D_290f0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_290f4 D_290f4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_290f8 D_290f8 ltac:(condZ).
    sn F_290fc D_290fc. sn F_29100 D_29100.
    zv F_29104 D_29104 (Z_to_bv 64 pixs).
    sn F_29108 D_29108.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x29208 : word) ltac:(bveq).
    sn F_2910c D_2910c.
    stepb_ft F_29110 D_29110 ltac:(condZ).                (* [comment removed for export] *)
    zv F_29114 D_29114 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_29118 D_29118.                                   (* [comment removed for export] *)
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x29218 : word) ltac:(bveq).
    stepb_ft F_2911c D_2911c ltac:(condZ).                (* [comment removed for export] *)
    sn F_29120 D_29120.
    stepLD F_29124 D_29124 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_29128 D_29128 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_2912c D_2912c.
    stepb_ft F_29130 D_29130 ltac:(condZ).
    sn F_29134 D_29134. sn F_29138 D_29138. sn F_2913c D_2913c. sn F_29140 D_29140. sn F_29144 D_29144.
    sn F_29194 D_29194.
    stepLD8 F_29198 D_29198 ret.
    stepLD8 F_2919c D_2919c (getr regs 8).
    stepLD8 F_291a0 D_291a0 (getr regs 9).
    stepLD8 F_291a4 D_291a4 (getr regs 18).
    stepLD8 F_291a8 D_291a8 (getr regs 19).
    zv F_291ac D_291ac (Z_to_bv 64 s).
    sn F_291b0 D_291b0.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_hd_ok : hd_ok_spec (0x291dc : word) (0x29358 : word) 255.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x18424) with (0x18424 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_290e0 D_290e0 (Z_to_bv 64 (s - 64)).
    stepST F_290e4 D_290e4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_290e8 D_290e8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_290ec D_290ec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_290f0 D_290f0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_290f4 D_290f4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_290f8 D_290f8 ltac:(condZ).
    zv F_290fc D_290fc (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_29100 D_29100 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_29104 D_29104 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_29108 D_29108.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x29208 : word) ltac:(bveq).
    sn F_2910c D_2910c.
    stepb_ft F_29110 D_29110 ltac:(condZ).
    zv F_29114 D_29114 (Z_to_bv 64 pixs).
    sn F_29118 D_29118.
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x29218 : word) ltac:(bveq).
    stepb_tk F_2911c D_2911c ltac:(condZ).                (* [comment removed for export] *)
    zv F_291b4 D_291b4 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_291b8 D_291b8.                                   (* [comment removed for export] *)
    stepb_ft F_291bc D_291bc ltac:(condZ).
    zv F_291c0 D_291c0 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_291c4 D_291c4 ltac:(condZ).
    sn F_291c8 D_291c8.                                   (* [comment removed for export] *)
    stepb_tk F_291cc D_291cc ltac:(condZ).                (* [comment removed for export] *)
    sn F_29240 D_29240. sn F_29244 D_29244. sn F_29248 D_29248. sn F_2924c D_2924c.
    mvli F_29250 D_29250 (Z_to_bv 64 pixs). mvli F_29254 D_29254 (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_29258 D_29258.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segB : segB_spec (0x29358 : word) (0x29364 : word) PC_pixErodeGray3h.
Proof.
  unfold segB_spec, PC_pixErodeGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x27440) with (0x27440 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_2925c D_2925c (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_29260 D_29260 ltac:(condZ).                (* [comment removed for export] *)
    sn F_29264 D_29264.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segD : segD_spec (0x29438 : word) (0x29444 : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_2933c D_2933c.                                   (* [comment removed for export] *)
    zv F_29340 D_29340 (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_29344 D_29344.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segE : segE_spec (0x29444 : word) (0x2944c : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_29348 D_29348 (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_2934c D_2934c.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segF : segF_spec (0x2944c : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_29350 D_29350.                                   (* [comment removed for export] *)
    sn F_29354 D_29354.                                   (* [comment removed for export] *)
    stepLD F_29224 D_29224 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_29228 D_29228 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_2922c D_2922c (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_29230 D_29230 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_29234 D_29234 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_29238 D_29238 (Z_to_bv 64 s).
    stepret F_2923c D_2923c ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC1 : segC1_spec (0x29364 : word) (0x29384 : word) 0.
Proof.
  unfold segC1_spec, PC_pixSetBorderVal. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x17afc) with (0x17afc : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - zv F_29268 D_29268 (Z_to_bv 64 a0v).                  (* [comment removed for export] *)
    stepST F_2926c D_2926c (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_29270 D_29270. sn F_29274 D_29274. sn F_29278 D_29278. sn F_2927c D_2927c. sn F_29280 D_29280.
    sn F_29284 D_29284.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC2 : segC2_spec (0x29384 : word) (0x2938c : word) PC_pixDilateGray3h.
Proof.
  unfold segC2_spec, PC_pixDilateGray3h. intros rom regs m s Hs Hs64 H2.
  replace (Z_to_bv 64 0x28408) with (0x28408 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - sn F_29288 D_29288.                                   (* [comment removed for export] *)
    sn F_2928c D_2928c.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC3 : segC3_spec (0x2938c : word) (0x29420 : word).
Proof.
  unfold segC3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  eexists. split.
  - sn F_29290 D_29290.                                   (* [comment removed for export] *)
    stepST F_29318 D_29318 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_2931c D_2931c (Z_to_bv 64 (s - 48)).             (* [comment removed for export] *)
    sn F_29320 D_29320.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma o_segC4 : segC4_spec (0x29420 : word) (0x29438 : word).
Proof.
  unfold segC4_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha Rc H2.
  replace (Z_to_bv 64 0x18720) with (0x18720 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepLD F_29324 D_29324 (Z_to_le_bytes 8 a0v) (Z_to_bv 64 a0v) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rc) ltac:(apply W2Lib.lez8; lia).
    sn F_29328 D_29328. sn F_2932c D_2932c. sn F_29330 D_29330. sn F_29334 D_29334.
    sn F_29338 D_29338.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_hd_null : hd_null_spec (0x29454 : word) 0x10298 0x10814.
Proof.
  unfold hd_null_spec, err_exit. intros rom regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRd.
  eexists. split.
  - zv F_29358 D_29358 (Z_to_bv 64 (s - 64)).
    stepST F_2935c D_2935c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_29360 D_29360 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_29364 D_29364 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_29368 D_29368 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2936c D_2936c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_tk F_29370 D_29370 ltac:(condZ).                (* [comment removed for export] *)
    sn F_293c0 D_293c0.
    stepLD F_293c4 D_293c4 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_293c8 D_293c8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_293cc D_293cc.
    stepb_ft F_293d0 D_293d0 ltac:(condZ).                (* [comment removed for export] *)
    sn F_293d4 D_293d4. sn F_293d8 D_293d8. sn F_293dc D_293dc. sn F_293e0 D_293e0. sn F_293e4 D_293e4.
    sn F_2940c D_2940c.
    stepLD8 F_29410 D_29410 ret.
    stepLD8 F_29414 D_29414 (getr regs 8).
    stepLD8 F_29418 D_29418 (getr regs 9).
    stepLD8 F_2941c D_2941c (getr regs 18).
    stepLD8 F_29420 D_29420 (getr regs 19).
    zv F_29424 D_29424 (Z_to_bv 64 s).
    sn F_29428 D_29428.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_hd_depth : hd_depth_spec (0x29454 : word) 0x10d0b 0x10814.
Proof.
  unfold hd_depth_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
  unfold FRd in *. eexists. split.
  - zv F_29358 D_29358 (Z_to_bv 64 (s - 64)).
    stepST F_2935c D_2935c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_29360 D_29360 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_29364 D_29364 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_29368 D_29368 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2936c D_2936c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_29370 D_29370 ltac:(condZ).                (* [comment removed for export] *)
    sn F_29374 D_29374. sn F_29378 D_29378.               (* [comment removed for export] *)
    zv F_2937c D_2937c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_29380 D_29380.                                   (* [comment removed for export] *)
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepret F_16c50 D_16c50 (0x29480 : word) ltac:(bveq).
    sn F_29384 D_29384.                                   (* [comment removed for export] *)
    stepb_tk F_29388 D_29388 ltac:(condZ).                (* [comment removed for export] *)
    sn F_293e8 D_293e8.
    stepLD F_293ec D_293ec (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_293f0 D_293f0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_293f4 D_293f4.
    stepb_ft F_293f8 D_293f8 ltac:(condZ).
    sn F_293fc D_293fc. sn F_29400 D_29400. sn F_29404 D_29404. sn F_29408 D_29408.
    sn F_2940c D_2940c.
    stepLD8 F_29410 D_29410 ret.
    stepLD8 F_29414 D_29414 (getr regs 8).
    stepLD8 F_29418 D_29418 (getr regs 9).
    stepLD8 F_2941c D_2941c (getr regs 18).
    stepLD8 F_29420 D_29420 (getr regs 19).
    zv F_29424 D_29424 (Z_to_bv 64 s).
    sn F_29428 D_29428.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_hd_cmap : hd_cmap_spec (0x29454 : word) 0x10803 0x10814.
Proof.
  unfold hd_cmap_spec, err_exit. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK Rg Rs H2 H1 H10.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rcm.
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm.
  unfold FRd in *. eexists. split.
  - zv F_29358 D_29358 (Z_to_bv 64 (s - 64)).
    stepST F_2935c D_2935c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_29360 D_29360 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_29364 D_29364 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_29368 D_29368 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2936c D_2936c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_29370 D_29370 ltac:(condZ).
    sn F_29374 D_29374. sn F_29378 D_29378.
    zv F_2937c D_2937c (Z_to_bv 64 pixs).
    sn F_29380 D_29380.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x29480 : word) ltac:(bveq).
    sn F_29384 D_29384.
    stepb_ft F_29388 D_29388 ltac:(condZ).                (* [comment removed for export] *)
    zv F_2938c D_2938c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_29390 D_29390.                                   (* [comment removed for export] *)
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x29490 : word) ltac:(bveq).
    stepb_ft F_29394 D_29394 ltac:(condZ).                (* [comment removed for export] *)
    sn F_29398 D_29398.
    stepLD F_2939c D_2939c (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
    stepLD F_293a0 D_293a0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
    sn F_293a4 D_293a4.
    stepb_ft F_293a8 D_293a8 ltac:(condZ).
    sn F_293ac D_293ac. sn F_293b0 D_293b0. sn F_293b4 D_293b4. sn F_293b8 D_293b8. sn F_293bc D_293bc.
    sn F_2940c D_2940c.
    stepLD8 F_29410 D_29410 ret.
    stepLD8 F_29414 D_29414 (getr regs 8).
    stepLD8 F_29418 D_29418 (getr regs 9).
    stepLD8 F_2941c D_2941c (getr regs 18).
    stepLD8 F_29420 D_29420 (getr regs 19).
    zv F_29424 D_29424 (Z_to_bv 64 s).
    sn F_29428 D_29428.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_hd_ok : hd_ok_spec (0x29454 : word) (0x295d0 : word) 0.
Proof.
  unfold hd_ok_spec, PC_pixAddBorderGeneral. intros rom regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd Hcm DJ SOK H2 H1 H10 H11 H12.
  replace (Z_to_bv 64 0x18424) with (0x18424 : word) by (apply bv_eq; reflexivity).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (PX1 : PIXat (FRd m s ret regs) pixs vs).
  { unfold FRd. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd. pose proof (PIX_rd_cmap SEGS _ _ _ PX1) as Ccm. rewrite Hcm in Ccm.
  unfold FRd in *. eexists. split.
  - zv F_29358 D_29358 (Z_to_bv 64 (s - 64)).
    stepST F_2935c D_2935c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_29360 D_29360 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_29364 D_29364 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_29368 D_29368 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_2936c D_2936c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_29370 D_29370 ltac:(condZ).
    zv F_29374 D_29374 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    zv F_29378 D_29378 (Z_to_bv 64 3).                    (* [comment removed for export] *)
    zv F_2937c D_2937c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
    sn F_29380 D_29380.
    stepb_ft F_16c40 D_16c40 ltac:(condZ).
    guard8 F_16c44 D_16c44 AL8. stepb_ft F_16c48 D_16c48 ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
    stepret F_16c50 D_16c50 (0x29480 : word) ltac:(bveq).
    sn F_29384 D_29384.
    stepb_ft F_29388 D_29388 ltac:(condZ).
    zv F_2938c D_2938c (Z_to_bv 64 pixs).
    sn F_29390 D_29390.
    stepb_ft F_16d64 D_16d64 ltac:(condZ).
    guard8 F_16d68 D_16d68 AL8. stepb_ft F_16d6c D_16d6c ltac:(condZ).   (* [comment removed for export] *)
    stepLD F_16d70 D_16d70 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccm) ltac:(apply W2Lib.lez8; lia).
    stepret F_16d74 D_16d74 (0x29490 : word) ltac:(bveq).
    stepb_tk F_29394 D_29394 ltac:(condZ).                (* [comment removed for export] *)
    zv F_2942c D_2942c (Z_to_bv 64 1).                    (* [comment removed for export] *)
    sn F_29430 D_29430.                                   (* [comment removed for export] *)
    stepb_ft F_29434 D_29434 ltac:(condZ).
    zv F_29438 D_29438 (Z_to_bv 64 1).                    (* [comment removed for export] *)
    stepb_ft F_2943c D_2943c ltac:(condZ).
    sn F_29440 D_29440.                                   (* [comment removed for export] *)
    stepb_tk F_29444 D_29444 ltac:(condZ).                (* [comment removed for export] *)
    sn F_294b8 D_294b8. sn F_294bc D_294bc. sn F_294c0 D_294c0. sn F_294c4 D_294c4.
    mvli F_294c8 D_294c8 (Z_to_bv 64 pixs). mvli F_294cc D_294cc (Z_to_bv 64 pixs).   (* [comment removed for export] *)
    sn F_294d0 D_294d0.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segB : segB_spec (0x295d0 : word) (0x295dc : word) PC_pixDilateGray3h.
Proof.
  unfold segB_spec, PC_pixDilateGray3h. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10 H9 H19.
  replace (Z_to_bv 64 0x28408) with (0x28408 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_294d4 D_294d4 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    stepb_ft F_294d8 D_294d8 ltac:(condZ).                (* [comment removed for export] *)
    sn F_294dc D_294dc.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segD : segD_spec (0x296b0 : word) (0x296bc : word).
Proof.
  unfold segD_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - sn F_295b4 D_295b4.                                   (* [comment removed for export] *)
    zv F_295b8 D_295b8 (Z_to_bv 64 (s - 56)).             (* [comment removed for export] *)
    sn F_295bc D_295bc.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segE : segE_spec (0x296bc : word) (0x296c4 : word).
Proof.
  unfold segE_spec. intros rom regs m s Hs Hs64 H2.
  eexists. split.
  - zv F_295c0 D_295c0 (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
    sn F_295c4 D_295c4.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segF : segF_spec (0x296c4 : word).
Proof.
  unfold segF_spec. intros rom regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
  eexists. split.
  - sn F_295c8 D_295c8.                                   (* [comment removed for export] *)
    sn F_295cc D_295cc.                                   (* [comment removed for export] *)
    stepLD F_2949c D_2949c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
    stepLD F_294a0 D_294a0 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
    stepLD F_294a4 D_294a4 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
    stepLD F_294a8 D_294a8 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
    stepLD F_294ac D_294ac (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
    zv F_294b0 D_294b0 (Z_to_bv 64 s).
    stepret F_294b4 D_294b4 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC1 : segC1_spec (0x295dc : word) (0x295fc : word) 255.
Proof.
  unfold segC1_spec, PC_pixSetBorderVal. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x17afc) with (0x17afc : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - zv F_294e0 D_294e0 (Z_to_bv 64 a0v).                  (* [comment removed for export] *)
    stepST F_294e4 D_294e4 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_294e8 D_294e8. sn F_294ec D_294ec. sn F_294f0 D_294f0. sn F_294f4 D_294f4. sn F_294f8 D_294f8.
    sn F_294fc D_294fc.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC2 : segC2_spec (0x295fc : word) (0x29604 : word) PC_pixErodeGray3h.
Proof.
  unfold segC2_spec, PC_pixErodeGray3h. intros rom regs m s Hs Hs64 H2.
  replace (Z_to_bv 64 0x27440) with (0x27440 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - sn F_29500 D_29500.                                   (* [comment removed for export] *)
    sn F_29504 D_29504.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC3 : segC3_spec (0x29604 : word) (0x29698 : word).
Proof.
  unfold segC3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  eexists. split.
  - sn F_29508 D_29508.                                   (* [comment removed for export] *)
    stepST F_29590 D_29590 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_29594 D_29594 (Z_to_bv 64 (s - 48)).             (* [comment removed for export] *)
    sn F_29598 D_29598.                                   (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma c_segC4 : segC4_spec (0x29698 : word) (0x296b0 : word).
Proof.
  unfold segC4_spec, PC_pixRemoveBorderGeneral. intros rom regs m s a0v Hs Hs64 Ha Rc H2.
  replace (Z_to_bv 64 0x18720) with (0x18720 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepLD F_2959c D_2959c (Z_to_le_bytes 8 a0v) (Z_to_bv 64 a0v) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rc) ltac:(apply W2Lib.lez8; lia).
    sn F_295a0 D_295a0. sn F_295a4 D_295a4. sn F_295a8 D_295a8. sn F_295ac D_295ac.
    sn F_295b0 D_295b0.                                   (* [comment removed for export] *)
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
  apply (drv_W (0x2724c : word) (0x273c8 : word) 255 0x10d0b 0x10803 0x1061e 14 16 13 e_hd_depth e_hd_cmap e_hd_ok ltac:(rok) str_not8 str_hascmap str_pixErodeGray3
           (or_intror eq_refl) ABG PC_pixErodeGray3 RK_gm3 RB_gm3 ltac:(apply bv_eq; reflexivity)).
  - assert (0 <= RK_pixcopy)%Z by (clear; room_consts; lia). unfold RK_gm3. lia.
  - assert (0 <= RB_pixcopy14)%Z by (clear; room_consts; lia). unfold RB_gm3. lia.
  - intros C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8. split.
    + eapply mid3_ok; first [exact e_segB | exact e_segC | exact e_segD | exact e_segE | exact e_segF | exact RBG | exact G3E_W | exact HK8 | eassumption | reflexivity | rok].
    + eapply mid3_null; first [exact e_segB | exact e_segC | exact e_segD | exact e_segE | exact e_segF | exact RBGn | exact G3E.gray3h_null_W | exact HK8 | eassumption | reflexivity | rok].
Qed.
Theorem pixDilateGray3_W : gray3_contract PC_pixDilateGray3 RK_gm3 RB_gm3.
Proof.
  apply (drv_W (0x28214 : word) (0x28390 : word) 0 0x10d0b 0x10803 0x104ae 14 16 14 d_hd_depth d_hd_cmap d_hd_ok ltac:(rok) str_not8 str_hascmap str_pixDilateGray3
           (or_introl eq_refl) ABG PC_pixDilateGray3 RK_gm3 RB_gm3 ltac:(apply bv_eq; reflexivity)).
  - assert (0 <= RK_pixcopy)%Z by (clear; room_consts; lia). unfold RK_gm3. lia.
  - assert (0 <= RB_pixcopy14)%Z by (clear; room_consts; lia). unfold RB_gm3. lia.
  - intros C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8. split.
    + eapply mid3_ok; first [exact d_segB | exact d_segC | exact d_segD | exact d_segE | exact d_segF | exact RBG | exact G3D_W | exact HK8 | eassumption | reflexivity | rok].
    + eapply mid3_null; first [exact d_segB | exact d_segC | exact d_segD | exact d_segE | exact d_segF | exact RBGn | exact G3D.gray3h_null_W | exact HK8 | eassumption | reflexivity | rok].
Qed.

Theorem pixOpenGray3_W : gray3_contract PC_pixOpenGray3 RK_gm4 RB_gm4.
Proof.
  apply (drv_W (0x291dc : word) (0x29358 : word) 255 0x10d0b 0x10803 0x11010 14 16 12 o_hd_depth o_hd_cmap o_hd_ok ltac:(rok) str_not8 str_hascmap str_pixOpenGray3
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
  apply (drv_W (0x29454 : word) (0x295d0 : word) 0 0x10d0b 0x10803 0x10814 14 16 13 c_hd_depth c_hd_cmap c_hd_ok ltac:(rok) str_not8 str_hascmap str_pixCloseGray3
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
Proof. exact (drv_null_W (0x2724c : word) 0x10298 0x1061e 16 13 e_hd_null str_pixs_nd str_pixErodeGray3 PC_pixErodeGray3 ltac:(apply bv_eq; reflexivity)). Qed.
Theorem pixDilateGray3_null_W : gray3_null_contract PC_pixDilateGray3.
Proof. exact (drv_null_W (0x28214 : word) 0x10298 0x104ae 16 14 d_hd_null str_pixs_nd str_pixDilateGray3 PC_pixDilateGray3 ltac:(apply bv_eq; reflexivity)). Qed.
Theorem pixOpenGray3_null_W : gray3_null_contract PC_pixOpenGray3.
Proof. exact (drv_null_W (0x291dc : word) 0x10298 0x11010 16 12 o_hd_null str_pixs_nd str_pixOpenGray3 PC_pixOpenGray3 ltac:(apply bv_eq; reflexivity)). Qed.
Theorem pixCloseGray3_null_W : gray3_null_contract PC_pixCloseGray3.
Proof. exact (drv_null_W (0x29454 : word) 0x10298 0x10814 16 13 c_hd_null str_pixs_nd str_pixCloseGray3 PC_pixCloseGray3 ltac:(apply bv_eq; reflexivity)). Qed.

End GrayDrvI.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
