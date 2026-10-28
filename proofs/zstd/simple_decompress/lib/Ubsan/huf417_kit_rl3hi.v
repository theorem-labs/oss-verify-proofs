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

Section DX41RL3HI.
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
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation WR3 := [(SPV - 184, SPV - 144)].
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_rl3_hi_w : forall mm S3 n3 b3 o3 p3 S4 o4 (k3 : word) pad3
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : word),
    8 <= o3 -> o3 + 8 <= n3 -> 0 <= p3 <= 56 -> 4096 <= S4 -> 0 <= o4 -> S4 + o4 < 2^47 ->
    mem_inv usegs mm ->
    FRA mm w0 w1 w2 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S4 + o4)) ->
    BD3 mm k3 (Z_to_bv 64 p3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    SBUF mm S3 n3 b3 ->
    (forall mm' (c y7 y8 y27 : word),
        8 <= o4 -> munch WR3 mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
        FRA mm' w0 w1 w2 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S4 + o4)) ->
        BD3 mm' c (Z_to_bv 64 (Z.land p3 7)) pad3 (Z_to_bv 64 (S3 + (o3 - p3 / 8))) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
        evt usegs POST (ST 0x23450 mm' x1 x5 (Z_to_bv 64 (S3 + (o3 - p3 / 8))) y7 y8 (Z_to_bv 64 3) x10 x11 (Z_to_bv 64 (S4 + 8))
                         x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (Z.land p3 7)) (Z_to_bv 64 (S4 + o4)) x21 (Z_to_bv 64 0) x20
                         x24 x25 x26 y27 x28 x29 x30 c)) ->
    (forall mm' (c y7 y8 y27 : word),
        o4 < 8 -> munch WR3 mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
        FRA mm' w0 w1 w2 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S4 + o4)) ->
        BD3 mm' c (Z_to_bv 64 (Z.land p3 7)) pad3 (Z_to_bv 64 (S3 + (o3 - p3 / 8))) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
        evt usegs POST (ST 0x23520 mm' x1 x5 (Z_to_bv 64 (S3 + (o3 - p3 / 8))) y7 y8 (Z_to_bv 64 3) x10 x11 (Z_to_bv 64 (S4 + 8))
                         x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (Z.land p3 7)) (Z_to_bv 64 (S4 + o4)) x21 (Z_to_bv 64 0) x20
                         x24 x25 x26 y27 x28 x29 x30 c)) ->
    evt usegs POST (ST 0x23394 mm x1 x5 (Z_to_bv 64 (S3 + o3)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 p3)
                     x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm S3 n3 b3 o3 p3 S4 o4 k3 pad3 x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 O3 N3 HP3 RS4 RO4 RS4O MI FA BD SB KA KB.
    destruct SB as (B3 & L3 & R30 & R31 & R32 & D31 & D32).
    assert (K3 : S3 + n3 <= SPV - 912 \/ SPV <= S3) by (clear - D32 LO; lia).
    clear D31 D32.
    assert (MU : munch WR3 mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    kx_autoLx [0x23450; 0x23520] 80%nat
      [KZRange o3 8 (2^32); KZRange (n3 - o3) 8 (2^32); KZRange p3 0 56; KZRange n3 0 (2^32);
       KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange o4 0 (2^47); KZRange (S4 + o4) 4096 (2^47);
       KZRange SPV 4096 (2^47); KZWr (SPV - 512) 136; KZWr (SPV - 184) 40;
       KZDisj (SPV - 512) 136 S3 n3; KZDisj (SPV - 184) 40 S3 n3; KZDisj (SPV - 512) 136 (SPV - 184) 40]
      [(S3, n3); (SPV - 512, 136); (SPV - 184, 40)].
    all: x41_ck.
    all: kx_mem.
    all: replace (p3 mod 2 ^ 64) with p3 in * by (rewrite Z.mod_small; lia).
    all: replace (S3 + (o3 + -1 * (p3 / 8))) with (S3 + (o3 - p3 / 8)) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23450) _ _ _ _) => eapply KA
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23520) _ _ _ _) => eapply KB
         end.
    all: try first [ eassumption | lia ].
  Qed.
End DX41RL3HI.
