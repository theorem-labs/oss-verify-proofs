(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41RC.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

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
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Lemma x41_r_c : forall mm rest j e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x1 x5 x6 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x30 x31 : word)
      (w0 w3 w4 w5 w12 w15 w16 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 dl) w3 w4 w5
      (Z_to_bv 64 (3 * e1)) (Z_to_bv 64 (2 * e1)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + dcap - 3))
      (Z_to_bv 64 (DST + 2 * e1)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    SINV o1 n1 c1 -> SINV o2 n2 c2 -> SINV o3 n3 c3 -> SINV o4 n4 c4 ->
    0 <= c1 < 2^31 -> 0 <= c2 < 2^31 -> 0 <= c3 < 2^31 -> 0 <= c4 < 2^31 ->
    0 <= j -> 0 <= e1 -> j + 3 * e1 + 4 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt usegs POST (ST 0x24000 mm x1 x5 x6 (Z_to_bv 64 DST) x8 x9 (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) (Z_to_bv 64 (DST + dcap)) x28 (Z_to_bv 64 (DST + j)) x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x1 x5 x6 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x30 x31 w0 w3 w4 w5 w12 w15 w16
      PV MI OUT DTB FA B1 B2 B3 B4 SB1 SB2 SB3 SB4 SI1 SI2 SI3 SI4 C1 C2 C3 C4 HJ HE HROOM HDL HTL HRSV.
    kx_autoLx [0x24024] 20%nat
      [KZRange j 0 (2^32); KZRange e1 0 (2^32); KZRange dcap 0 (2^32); KZRange (dcap - 3 * e1 - j) 4 (2^32);
       KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SPV - 512, 136)].
    kx_ev_ranges. kx_mem.
    replace (DST + j + 4) with (DST + (j + 4)) by lia.
    replace (DST + (e1 + j) + 4) with (DST + (j + 4 + e1)) by lia.
    replace (DST + (2 * e1 + j) + 4) with (DST + (j + 4 + 2 * e1)) by lia.
    replace (DST + (3 * e1 + j) + 4) with (DST + (j + 4 + 3 * e1)) by lia.
    eapply (x41_c0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 mm rest
              (j + 4) (j + 4 + e1) (j + 4 + 2 * e1) (j + 4 + 3 * e1) e1 (2 * e1) (3 * e1)
              S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv k1 k2 k3 k4 pad1 pad2 pad3 pad4).
    all: first [ eassumption | lia | exact (rsk_al_e _ _ SPVA) | exact (rsk_al_e _ _ DTA) ].
  Qed.

End DX41RC.
