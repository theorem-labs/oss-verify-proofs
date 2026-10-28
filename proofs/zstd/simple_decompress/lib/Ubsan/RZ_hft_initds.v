(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_fse_small_kit.
Import ListNotations. Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac ids_trap := lazymatch goal with |- context [Z_to_bv 64 0x2c1b0] => kx_trap_fast | _ => idtac end.

Ltac ids_post :=
  apply evt_done; unfold fse_initds_post, bitd_cells; repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [match goal with H : rw_cells _ _ _ (C8 _ :: C8 _ :: nil) |- _ => exact H end|];
  lazymatch goal with |- context [Z.land ?x ((2 ^ ?k + -1) mod 2 ^ 64)] =>
    let FB := fresh "FB" in pose proof (sk_land_mask x k ltac:(lia)) as FB end;
  split; [lia|];
  split; [match goal with H : rw_cells _ _ _ (C8 _ :: C4 _ :: _) |- _ => exact H end|];
  unfold fbit_ok; split; [split; [lia | intros; first [left; lia | right; lia]] | lia].

Theorem fse_initds_proof : fse_initds_stmt.
Proof.
  unfold fse_initds_stmt, PFSE_INITDS. intros until junk.
  intros MI STC BDC (BCR & BOK) BC2 SRCB SRCL DTB TLR R1 R2 R3 R4 R5 R6 R7 R8 A1 A2 A3 D1 D2 D3 D4 D5.
  unfold bitd_cells in BDC.
  assert (MU : munch [(ST, ST + 16); (BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  destruct (sk_cb16 usegs m ST junk STC) as (w0 & w1 & HST). clear STC.
  pose proof (sk_hdr_ro usegs m DT _ DTB) as DTC. clear DTB.
  pose proof (sk_mask_ro m tl MI ltac:(lia)) as MASK. unfold FBITMASK in MASK.
  assert (P2 : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  assert (N0 : 0 <= n) by (rewrite <- SRCL; apply Zle_0_nat).
  destruct (Z_le_gt_dec 65 (bc + tl)) as [K|K].
  - (* [comment removed for export] *)
    clear BOK.
    kx_auto [] 200%nat
      [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZRange n 0 (2^47); KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange bc 0 2048; KZRange (bc + tl) 65 2060;
       KZAlign ST 8; KZAlign BD 8; KZAlign DT 2; KZWr ST 16; KZWr BD 40;
       KZDisj ST 16 BD 40; KZDisj BD 40 SRC n; KZDisj ST 16 SRC n; KZDisj BD 40 DT 2; KZDisj ST 16 DT 2; KZImg 0x10000 0x14000]
      [(SRC, n)].
    all: ids_trap. all: kx_mem. all: zstep. all: ids_post.
  - specialize (BOK ltac:(lia)).
    destruct (Z_le_gt_dec (SRC + 8) ptr) as [K2|K2].
    + (* [comment removed for export] *)
      assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SRC + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
        by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SRC); clear - BOK K K2 BCR TLR; Z.div_mod_to_equations; lia).
      destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4).
      assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc. clear BOK.
      kx_auto [] 200%nat
        [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
         KZRange n 16 (2^47); KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64;
         KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
         KZAlign ST 8; KZAlign BD 8; KZAlign DT 2; KZWr ST 16; KZWr BD 40;
         KZDisj ST 16 BD 40; KZDisj BD 40 SRC n; KZDisj ST 16 SRC n; KZDisj BD 40 DT 2; KZDisj ST 16 DT 2; KZImg 0x10000 0x14000]
        [(SRC, n)].
      all: ids_trap. all: kx_mem. all: zstep. all: ids_post.
    + destruct (Z.eq_dec ptr SRC) as [K3|K3].
      * (* [comment removed for export] *)
        subst ptr. clear BOK.
        kx_auto [] 200%nat
          [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
           KZRange n 0 (2^47); KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange bc 0 64; KZRange (bc + tl) 0 64;
           KZAlign ST 8; KZAlign BD 8; KZAlign DT 2; KZWr ST 16; KZWr BD 40;
           KZDisj ST 16 BD 40; KZDisj BD 40 SRC n; KZDisj ST 16 SRC n; KZDisj BD 40 DT 2; KZDisj ST 16 DT 2; KZImg 0x10000 0x14000]
          [(SRC, n)].
        all: ids_trap. all: kx_mem. all: zstep. all: ids_post.
      * (* [comment removed for export] *)
        destruct (Z_le_gt_dec ((bc + tl) / 8) (ptr - SRC)) as [K4|K4].
        -- assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SRC + d /\ 0 <= q <= d /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n)
             by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SRC); clear - BOK K K2 K3 K4 BCR TLR; Z.div_mod_to_equations; lia).
           destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4).
           assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc. clear BOK.
           kx_auto [] 200%nat
             [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
              KZRange n 9 (2^47); KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange q 0 7; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64;
              KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
              KZAlign ST 8; KZAlign BD 8; KZAlign DT 2; KZWr ST 16; KZWr BD 40;
              KZDisj ST 16 BD 40; KZDisj BD 40 SRC n; KZDisj ST 16 SRC n; KZDisj BD 40 DT 2; KZDisj ST 16 DT 2; KZImg 0x10000 0x14000]
             [(SRC, n)].
           all: ids_trap. all: kx_mem. all: zstep. all: ids_post.
        -- (* [comment removed for export] *)
           assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SRC + d /\ 1 <= d < q /\ q <= 8 /\ 0 <= r <= 7 /\ d <= 7 /\ d + 8 <= n)
             by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SRC); clear - BOK K K2 K3 K4 BCR TLR; Z.div_mod_to_equations; lia).
           destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & Q5).
           assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc. clear BOK.
           kx_auto [] 200%nat
             [KZRange ST 4096 (2^47 - 17); KZRange BD 4096 (2^47 - 41); KZRange DT 4096 (2^47 - 5); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
              KZRange n 9 (2^47); KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange q 2 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64;
              KZRange d 1 7; KZRange (q - d) 1 7; KZRange (n - d) 8 (2^47); KZRange (8 * q + r - 8 * d) 8 64;
              KZAlign ST 8; KZAlign BD 8; KZAlign DT 2; KZWr ST 16; KZWr BD 40;
              KZDisj ST 16 BD 40; KZDisj BD 40 SRC n; KZDisj ST 16 SRC n; KZDisj BD 40 DT 2; KZDisj ST 16 DT 2; KZImg 0x10000 0x14000]
             [(SRC, n)].
           all: ids_trap. all: kx_mem. all: zstep. all: ids_post.
Qed.
