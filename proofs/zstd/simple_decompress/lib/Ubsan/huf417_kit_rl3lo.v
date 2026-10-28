(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41RL3LO.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation WR0 := [(SPV - 512, SPV - 376)].
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_rl3_lo_w : forall mm S3 o3 S4 o4
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : word),
    0 <= o3 < 8 -> 4096 <= S3 -> S3 < 2^47 -> 4096 <= S4 -> 0 <= o4 -> S4 + o4 < 2^47 ->
    mem_inv usegs mm ->
    FRA mm w0 w1 w2 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S4 + o4)) ->
    (8 <= o4 ->
        evt usegs POST (ST 0x23450 mm x1 x5 (Z_to_bv 64 (S3 + o3)) x7 x8 (Z_to_bv 64 3) x10 x11 (Z_to_bv 64 (S4 + 8)) x13 x14 x15
                         x16 x17 x18 x19 (Z_to_bv 64 (S4 + o4)) x21 (Z_to_bv 64 3) x20 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    (o4 < 8 ->
        evt usegs POST (ST 0x23520 mm x1 x5 (Z_to_bv 64 (S3 + o3)) x7 x8 (Z_to_bv 64 3) x10 x11 (Z_to_bv 64 (S4 + 8)) x13 x14 x15
                         x16 x17 x18 x19 (Z_to_bv 64 (S4 + o4)) x21 (Z_to_bv 64 3) x20 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x23394 mm x1 x5 (Z_to_bv 64 (S3 + o3)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm S3 o3 S4 o4 x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 O3 RS3 RS3E RS4 RO4 RS4O MI FA KA KB.
    assert (MU : munch WR0 mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    kx_autoLx [0x23450; 0x23520] 30%nat
      [KZRange o3 0 7; KZRange S3 4096 (2^47); KZRange (S3 + 8) 4096 (2^48); KZRange S4 4096 (2^47); KZRange o4 0 (2^47);
       KZRange (S4 + o4) 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 512) 136]
      [(SPV - 512, 136)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23450) _ _ _ _) => eapply KA
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23520) _ _ _ _) => eapply KB
         end.
    all: try first [ eassumption | lia ].
  Qed.
End DX41RL3LO.
