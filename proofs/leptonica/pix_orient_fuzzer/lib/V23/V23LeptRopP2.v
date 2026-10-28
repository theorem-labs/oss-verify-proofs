(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptRop_iface V23LeptRop V23_code_pixRasterop V23LeptRop2C V23LeptRopOp2W V23LeptRopG2WC V23LeptRopClose.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PRSegs2.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Notation w4 x := (word_to_le_bytes 4 x) (only parsing).

Definition PSM2 (m : word -> option byte) (s : Z) (vd vs : pixv) (dh sx sy : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 120)) (w4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 124)) (w4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 128)) (w4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 120)) (w4 (Z_to_bv 64 (p_w vs)))) (Z_to_bv 64 (s - 124)) (w4 (Z_to_bv 64 (p_h vs)))) (Z_to_bv 64 (s - 128)) (w4 (Z_to_bv 64 (p_d vs))))
    (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 (p_w vd)))) (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 (p_h vd))))
    (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 (p_d vd)))) (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 (p_data vd))))
    (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 (p_h vs)))) (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 (p_wpl vs))))
    (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 sx))) (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 sy)))
    (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 2)))
    (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 (p_data vs)))) (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 (p_w vs))).

Lemma pr_Bs2 : forall regs m (s pixd pixs dx dy dw dh sx sy : Z) (vd vs : pixv),
  (224 <= s)%Z -> (s mod 16 = 0)%Z -> (pixd mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z -> (s + 8 < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd + 64 <= s - 224 \/ s + 8 <= pixd)%Z -> PIXat m pixd vd ->
  (1 <= pixs)%Z -> (pixs + 64 <= s - 224 \/ s + 8 <= pixs)%Z -> PIXat m pixs vs -> p_d vs = p_d vd ->
  (0 <= p_w vd < 2 ^ 31)%Z -> (0 <= p_h vd < 2 ^ 31)%Z -> (0 <= p_d vd < 2 ^ 31)%Z -> (0 <= p_wpl vd < 2 ^ 31)%Z -> (0 <= p_data vd < 2 ^ 64)%Z ->
  (0 <= p_w vs < 2 ^ 31)%Z -> (0 <= p_h vs < 2 ^ 31)%Z -> (0 <= p_wpl vs < 2 ^ 31)%Z -> (0 <= p_data vs < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 224)) 108 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))) ->
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))) ->
  getr regs 2 = Z_to_bv 64 (s - 224) -> getr regs 19 = Z_to_bv 64 2 -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 25 = Z_to_bv 64 pixs ->
  getr regs 27 = Z_to_bv 64 dh -> getr regs 18 = Z_to_bv 64 dx -> getr regs 9 = Z_to_bv 64 dy -> getr regs 8 = Z_to_bv 64 dw ->
  getr regs 22 = Z_to_bv 64 sx -> getr regs 21 = Z_to_bv 64 sy ->
  exists regs',
    msteps SEGS (mkst regs (0x7f1b4 : word) m rom) (mkst regs' (0x7fc9c : word) (PSM2 m s vd vs dh sx sy) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 224) /\ getr regs' 1 = Z_to_bv 64 0x7f33c
    /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 (p_w vd) /\ getr regs' 12 = Z_to_bv 64 (p_h vd) /\ getr regs' 13 = Z_to_bv 64 (p_d vd)
    /\ getr regs' 14 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 15 = Z_to_bv 64 dx /\ getr regs' 16 = Z_to_bv 64 dy /\ getr regs' 17 = Z_to_bv 64 dw
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 24; 26]%list) regs regs'.
Proof.
  intros regs m s pixd pixs dx dy dw dh sx sy vd vs Hs Hs16 ALd8 ALs8 Hs64 Hp DJ PX Hps DJs PXs Edd Hw Hh Hd Hwpl Hdata Hsw Hsh Hswpl Hsdata SOK Rw Rh Rd
    R2 R19 R20 R25 R27 R18 R9 R8 R22 R21.
  assert (SL120 : ((s - 120) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  assert (SL124 : ((s - 124) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  assert (SL128 : ((s - 128) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  pose proof PX as (Hp0 & Hp64 & _). pose proof PXs as (Hps0 & Hps64 & _).
  assert (Hsd : (0 <= p_d vs < 2 ^ 31)%Z) by (rewrite Edd; exact Hd).
  eexists. split.
  - sn F_7f1b4 D_7f1b4.
    stepb_ft F_7f1b8 D_7f1b8 ltac:(condZ).
    sn F_7f1bc D_7f1bc. sn F_7f1c0 D_7f1c0. sn F_7f1c4 D_7f1c4.
    stepiv F_7f1c8 D_7f1c8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
    stepb_tk F_7f1cc D_7f1cc ltac:(condZ).
    stepb_ft F_7f288 D_7f288 ltac:(condZ).
    sn F_7f28c D_7f28c.
    zv F_7f290 D_7f290 (Z_to_bv 64 (s - 120)). zv F_7f294 D_7f294 (Z_to_bv 64 (s - 124)). zv F_7f298 D_7f298 (Z_to_bv 64 (s - 128)).
    sn F_7f29c D_7f29c.
    zand F_6e2a4 D_6e2a4 andi_3 SL120.
    stepb_ft F_6e2a8 D_6e2a8 ltac:(condZ).
    stepb_ft F_6e2ac D_6e2ac ltac:(condR).
    stepST F_6e2b0 D_6e2b0 (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zand F_6e2b4 D_6e2b4 andi_3 SL124.
    stepb_ft F_6e2b8 D_6e2b8 ltac:(condZ).
    stepb_ft F_6e2bc D_6e2bc ltac:(condR).
    stepST F_6e2c0 D_6e2c0 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zand F_6e2c4 D_6e2c4 andi_3 SL128.
    stepb_ft F_6e2c8 D_6e2c8 ltac:(condZ).
    stepb_ft F_6e2cc D_6e2cc ltac:(condR).
    stepST F_6e2d0 D_6e2d0 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepb_ft F_6e2d4 D_6e2d4 ltac:(condZ).
    zand F_6e2d8 D_6e2d8 andi_7 ALs8.
    stepb_ft F_6e2dc D_6e2dc ltac:(condZ).
    sn F_6e2e0 D_6e2e0.
    stepb_ft F_6e2e4 D_6e2e4 ltac:(condR).
    stepLD F_6e2e8 D_6e2e8 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_w vs)) by lia.
    stepST F_6e2ec D_6e2ec (Z_to_bv 64 (s - 120)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
    stepb_ft F_6e2f0 D_6e2f0 ltac:(condZ).
    sn F_6e2f4 D_6e2f4.
    stepb_ft F_6e2f8 D_6e2f8 ltac:(condR).
    stepLD F_6e2fc D_6e2fc (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_h vs)) by lia.
    stepST F_6e300 D_6e300 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
    stepb_ft F_6e304 D_6e304 ltac:(condZ).
    sn F_6e308 D_6e308.
    stepb_ft F_6e30c D_6e30c ltac:(condR).
    stepLD F_6e310 D_6e310 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepST F_6e314 D_6e314 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
    sn F_6e318 D_6e318.
    stepret F_6e31c D_6e31c (0x7f2a0 : word) ltac:(bveq).
    stepLD F_7f2a0 D_7f2a0 (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rd) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_d vd)) by lia.
    stepLD F_7f2a4 D_7f2a4 (word_to_le_bytes 4 (Z_to_bv 64 (p_d vs))) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d vs)))); zlen; unorm; lia) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepb_ft F_7f2a8 D_7f2a8 ltac:(rewrite Edd; condZ).
    sn F_7f2ac D_7f2ac. sn F_7f2b0 D_7f2b0.
    stepb_ft F_6f1ec D_6f1ec ltac:(condZ).
    zand F_6f1f0 D_6f1f0 andi_7 ALd8.
    stepb_ft F_6f1f4 D_6f1f4 ltac:(condR).
    stepLD F_6f1f8 D_6f1f8 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
    stepret F_6f1fc D_6f1fc (0x7f2b4 : word) ltac:(bveq).
    stepLD F_7f2b4 D_7f2b4 (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))) (Z_to_bv 64 (p_w vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rw) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_w vd)) by lia.
    stepST F_7f2b8 D_7f2b8 (Z_to_bv 64 (s - 136)) (Z_to_bv 64 (p_w vd)) ltac:(sok_in SOK).
    stepLD F_7f2bc D_7f2bc (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rh) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_h vd)) by lia.
    stepST F_7f2c0 D_7f2c0 (Z_to_bv 64 (s - 144)) (Z_to_bv 64 (p_h vd)) ltac:(sok_in SOK).
    stepLD F_7f2c4 D_7f2c4 (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rd) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_d vd)) by lia.
    stepST F_7f2c8 D_7f2c8 (Z_to_bv 64 (s - 152)) (Z_to_bv 64 (p_d vd)) ltac:(sok_in SOK).
    stepST F_7f2cc D_7f2cc (Z_to_bv 64 (s - 160)) (Z_to_bv 64 (p_data vd)) ltac:(sok_in SOK).
    sn F_7f2d0 D_7f2d0. sn F_7f2d4 D_7f2d4.
    stepb_ft F_6df4c D_6df4c ltac:(condZ).
    zand F_6df50 D_6df50 andi_7 ALd8.
    stepb_ft F_6df54 D_6df54 ltac:(condR).
    stepLD F_6df58 D_6df58 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_wpl vd)) by lia.
    stepret F_6df5c D_6df5c (0x7f2d8 : word) ltac:(bveq).
    sn F_7f2d8 D_7f2d8. sn F_7f2dc D_7f2dc. sn F_7f2e0 D_7f2e0.
    stepb_ft F_6f1ec D_6f1ec ltac:(condZ).
    zand F_6f1f0 D_6f1f0 andi_7 ALs8.
    stepb_ft F_6f1f4 D_6f1f4 ltac:(condR).
    stepLD F_6f1f8 D_6f1f8 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PXs)) ltac:(apply lez8; lia).
    stepret F_6f1fc D_6f1fc (0x7f2e4 : word) ltac:(bveq).
    stepLD F_7f2e4 D_7f2e4 (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs))) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs)))); zlen; unorm; lia) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_w vs)) by lia.
    stepLD F_7f2e8 D_7f2e8 (word_to_le_bytes 4 (Z_to_bv 64 (p_h vs))) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h vs)))); zlen; unorm; lia) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_h vs)) by lia.
    sn F_7f2ec D_7f2ec. sn F_7f2f0 D_7f2f0. sn F_7f2f4 D_7f2f4.
    stepb_ft F_6df4c D_6df4c ltac:(condZ).
    zand F_6df50 D_6df50 andi_7 ALs8.
    stepb_ft F_6df54 D_6df54 ltac:(condR).
    stepLD F_6df58 D_6df58 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_wpl vs)) by lia.
    stepret F_6df5c D_6df5c (0x7f2f8 : word) ltac:(bveq).
    stepST F_7f2f8 D_7f2f8 (Z_to_bv 64 (s - 192)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
    stepST F_7f2fc D_7f2fc (Z_to_bv 64 (s - 184)) (Z_to_bv 64 (p_wpl vs)) ltac:(sok_in SOK).
    stepST F_7f300 D_7f300 (Z_to_bv 64 (s - 176)) (Z_to_bv 64 sx) ltac:(sok_in SOK).
    stepST F_7f304 D_7f304 (Z_to_bv 64 (s - 168)) (Z_to_bv 64 sy) ltac:(sok_in SOK).
    stepST F_7f308 D_7f308 (Z_to_bv 64 (s - 224)) (Z_to_bv 64 dh) ltac:(sok_in SOK).
    stepST F_7f30c D_7f30c (Z_to_bv 64 (s - 216)) (Z_to_bv 64 2) ltac:(sok_in SOK).
    stepST F_7f310 D_7f310 (Z_to_bv 64 (s - 208)) (Z_to_bv 64 (p_data vs)) ltac:(sok_in SOK).
    stepST F_7f314 D_7f314 (Z_to_bv 64 (s - 200)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
    stepLD8 F_7f318 D_7f318 (Z_to_bv 64 (p_data vd)). stepLD8 F_7f31c D_7f31c (Z_to_bv 64 (p_w vd)).
    stepLD8 F_7f320 D_7f320 (Z_to_bv 64 (p_h vd)). stepLD8 F_7f324 D_7f324 (Z_to_bv 64 (p_d vd)).
    sn F_7f328 D_7f328. sn F_7f32c D_7f32c. sn F_7f330 D_7f330. sn F_7f334 D_7f334.
    sn F_7f338 D_7f338.
    unfold PSM2. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End PRSegs2.

Lemma PSM2_outside : forall m s vd vs dh sx sy (a : word), (224 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 224 <= bv_unsigned a < s)%Z -> PSM2 m s vd vs dh sx sy a = m a.
Proof.
  intros m s vd vs dh sx sy a Hs Hs64 Ha. unfold PSM2. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.
Lemma PSM2_above : forall m s vd vs dh sx sy (a : word), (224 <= s)%Z -> (s < 2 ^ 64)%Z -> (s - 104 <= bv_unsigned a)%Z -> PSM2 m s vd vs dh sx sy a = m a.
Proof.
  intros m s vd vs dh sx sy a Hs Hs64 Ha. unfold PSM2. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

Section Rop2C.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.

Definition rasteropLow2_clip_contract : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  rop2_clip_arm dx sx dw dpixw spixw dy sy dh dpixh spixh swpl ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

Theorem rasteropLow2_clip_W : rasteropLow2_clip_contract.
Proof.
  unfold rasteropLow2_clip_contract.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh ARM Ld Ld0 Ld00 Ls NEsd HK.
  destruct ARM as [[A1 A2] | ARM].
  - exact (rasteropLow_wa2_clip_closed C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
      CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
      Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh A1 A2 Ld Ld0 Ld00 Ls NEsd HK).
  - exact (rasteropLow_gen2_clip_W C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
      CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
      Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh ARM Ld Ld0 Ld00 Ls HK).
Qed.

(* [comment removed for export] *)
Definition pixRasterop_op2clip_contract : Prop :=
  forall C Ar A m md regs (s pixd dx dy dw dh pixs sx sy : Z) (vd vs : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s)%Z -> (s + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 dx -> getr regs 12 = Z_to_bv 64 dy -> getr regs 13 = Z_to_bv 64 dw ->
  getr regs 14 = Z_to_bv 64 dh -> getr regs 15 = Z_to_bv 64 2 -> getr regs 16 = Z_to_bv 64 pixs -> getr regs 17 = Z_to_bv 64 sx ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vs = p_d vd -> p_d vd = 1%Z ->
  rop_shape (p_w vd) (p_h vd) (p_d vd) (p_wpl vd) -> rop_shape (p_w vs) (p_h vs) (p_d vs) (p_wpl vs) ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  rop2_clip_arm dx sx dw (p_w vd) (p_w vs) dy sy dh (p_h vd) (p_h vs) (p_wpl vs) ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd) -> Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd) ->
  live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z -> live Ar (Z_to_bv 64 (p_data vd)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None ->
  live A (Z_to_bv 64 (p_data vs)) = Some (4 * (p_wpl vs * p_h vs))%Z -> Z_to_bv 64 (p_data vs) <> Z_to_bv 64 (p_data vd) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd vd -> PIXat m' pixs vs ->
      (forall a : word, ~ scratch C s a -> ~ (p_data vd <= bv_unsigned a < p_data vd + 4 * (p_wpl vd * p_h vd))%Z -> m' a = m a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.

Theorem pixRasterop_op2clip_W : pixRasterop_op2clip_contract.
Proof.
  unfold pixRasterop_op2clip_contract.
  intros C Ar A m md regs s pixd dx dy dw dh pixs sx sy vd vs ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rsy
    PXd PXs Edd Ed1 SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh ARM Lpd Lps NEpd NEps Ld Ld0 Ld00 Ls NEsd HK.
  unfold PC_pixRasterop. replace (Z_to_bv 64 0x7f13c) with (0x7f13c : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ROP_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (pix_facts C A m md pixd vd CK HW PXd SHd Lpd) as (Gpd & TOPpd & Hdatad & Hwpld).
  destruct (pix_facts C A m md pixs vs CK HW PXs SHs Lps) as (Gps & TOPps & Hdatas & Hwpls).
  assert (ALd8 : (pixd mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  assert (ALs8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  pose proof SHd as (Hdd & Hwd & Hhd & _ & Hszd). pose proof SHs as (_ & Hws & Hhs & _ & _).
  set (nd := (4 * (p_wpl vd * p_h vd))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; clear - Hwpld Hhd; nia).
  destruct (pr_A al_rom regs m s pixd 2 vd ret (Z_to_bv 64 sy) ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PXd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 224) 224 CK HW ltac:(lia) ltac:(cbn; lia)) Rsy H2 H1 H10 H15)
    as (r1 & RUN1 & Q2 & Q19 & Q20 & Q21 & Q25 & Q22 & Q27 & Q18 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := PRM m s ret regs (p_w vd) (p_h vd) (p_d vd)).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1)
    by (apply (WP_range C Ar A m m M1 md s (s - 224) CK HW (POSTM_refl _ _ _ _) SUB); [lia | lia | intros a Ha; subst M1; apply PRM_outside; lia | subst M1; unfold PRM, RLF; grows_chain]).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M1 a = m a) by (intros a Ha; subst M1; apply PRM_outside; lia).
  assert (PXd1 : PIXat M1 pixd vd) by (apply (PIXat_frame m); [exact PXd | intros x Hx; apply OUT1; lia]).
  assert (PXs1 : PIXat M1 pixs vs) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd)))); zlen; unorm; lia).
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd)))); zlen; unorm; lia).
  assert (Rd1 : rdn SEGS M1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd)))); zlen; unorm; lia).
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE0.
  assert (CE1 : rlcells M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame (RLF m s ret regs) M1 s); [lia | lia | exact CE0 |]. intros x Hx. subst M1. apply PRM_above; lia. }
  destruct (pr_Bs2 al_rom r1 M1 s pixd pixs dx dy dw dh sx sy vd vs ltac:(lia) Hs16 ALd8 ALs8 ltac:(lia) ltac:(lia) ltac:(lia) PXd1 ltac:(lia) ltac:(lia) PXs1 Edd
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdatad ltac:(lia) ltac:(lia) ltac:(lia) Hdatas
              (W_sok_win C A M1 md (s - 224) 108 CK HW1 ltac:(lia) ltac:(cbn; lia)) Rw1 Rh1 Rd1
              Q2 Q19 Q20 ltac:(rewrite Q25; exact H16) ltac:(rewrite Q27; exact H14) ltac:(rewrite Q18; exact H11) ltac:(rewrite Q9; exact H12)
              ltac:(rewrite Q8; exact H13) ltac:(rewrite Q22; exact H17) Q21)
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & P16' & P17 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := PSM2 M1 s vd vs dh sx sy).
  assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2)
    by (apply (WP_range C Ar A m M1 M2 md s (s - 224) CK HW1 PM1 SUB); [lia | lia | intros a Ha; subst M2; apply PSM2_outside; lia | subst M2; unfold PSM2; clearbody M1; grows_chain]).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M2 a = m a) by (intros a Ha; subst M2; rewrite PSM2_outside by lia; apply OUT1; exact Ha).
  assert (CE2 : rlcells M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame M1 M2 s); [lia | lia | exact CE1 |]. intros x Hx. subst M2. apply PSM2_above; lia. }
  replace (0x7fc9c : word) with (Z_to_bv 64 PC_rasteropLow) by (apply bv_eq; reflexivity).
  apply (rasteropLow2_clip_W C Ar A M2 md r2 (s - 224)%Z (p_data vd) (p_w vd) (p_h vd) (p_wpl vd) dx dy dw dh (p_data vs) (p_w vs) (p_h vs) (p_wpl vs) sx sy
           (Z_to_bv 64 0x7f33c) S CK HW2 SUB P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROPLOW_STACK; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 ltac:(rewrite P13, Ed1; reflexivity) P14 P15 P16' P17).
  1-8: repeat match goal with |- context [Z_to_bv 64 (?b - 224 + ?k)%Z] => let c := eval cbv in (224 - k)%Z in replace (b - 224 + k)%Z with (b - c)%Z by lia end;
       subst M2; unfold PSM2; rdn_chain.
  - exact Hdatad. - exact Hdatas. - rewrite <- Ed1. exact SHd. - rewrite <- Ed1, <- Edd. exact SHs.
  - exact Bdx. - exact Bsx. - exact Bdy. - exact Bsy. - exact Bdw. - exact Bdh. - exact ARM.
  - exact Ld. - exact Ld0. - exact Ld00. - exact Ls. - exact NEsd.
  - intros m3 r3 HW3 CS3 PM3 FT3.
    replace (Z_to_bv 64 0x7f33c) with (0x7f33c : word) by (apply bv_eq; reflexivity).
    destruct (pr_J al_rom r3 m3) as (r4 & RUN4 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    destruct (blk_range C A m md (Z_to_bv 64 (p_data vd)) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    assert (CE3 : rlcells m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
    { apply (rlcells_frame M2 m3 s); [lia | lia | exact CE2 |]. intros x Hx. apply FT3; [unfold scratch; lia | lia]. }
    destruct (pr_C al_rom r4 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) Hret CE3 ltac:(csr; reflexivity))
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK m3 r5 HW3).
    + apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption | csr; reflexivity ].
    + eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [| exact PM3]; lia].
    + apply (PIXat_frame m); [exact PXd|].
      apply (hdr_kept C A m md (s - 224) pixd (p_data vd) nd M2 m3 CK HW Lpd Ld NEpd ltac:(lia) Hdatad Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + apply (PIXat_frame m); [exact PXs|].
      apply (hdr_kept C A m md (s - 224) pixs (p_data vd) nd M2 m3 CK HW Lps Ld NEps ltac:(lia) Hdatad Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + intros a Ha Hb. unfold scratch in Ha. rewrite (FT3 a) by (unfold scratch; lia). apply OUT2. lia.
    + exact Z10.
Qed.

End Rop2C.
