(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf417_kit_rlk.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Section RLD.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation FRK mm j e1 dl S2 S3 S4 w0 w12 w15 w16 :=
    (rw_cells usegs mm (SPV + -512)
       [C8 w0; C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 (S4 + 8)); C8 (Z_to_bv 64 (S3 + 8));
        C8 (Z_to_bv 64 (S2 + 8)); C8 (Z_to_bv 64 (3 * e1)); C8 (Z_to_bv 64 (2 * e1)); C8 (Z_to_bv 64 (DST + dcap));
        C8 (Z_to_bv 64 (DST + e1)); C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 w12;
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 w15; C8 w16]).
  Notation KBASE mm rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 :=
    (X41P mm rest /\ mem_inv usegs mm /\ stk usegs mm DST (DST + dcap) /\ bytes_at usegs mm DT dtb /\ huf_nb_ok false dtb tl /\
     SBUF mm S1 n1 b1 /\ SBUF mm S2 n2 b2 /\ SBUF mm S3 n3 b3 /\ SBUF mm S4 n4 b4 /\
     0 <= j /\ 0 <= e1 /\ j + 3 * e1 + 4 <= dcap /\ dl = tl + 256 * rsv /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255).

  Definition KH (rest : list byte) (j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 : Z) (b1 b2 b3 b4 pad1 pad2 pad3 pad4 : list byte)
      (w0 : word) : Prop :=
    forall mm (k1 k2 k3 k4 : word) c1 o1 c2 o2 c3 o3 c4 o4 (x7 x8 x9 x12 x14 x21 x22 x27 x29 w12 w15 : word),
      KBASE mm rest (j + 4) e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 ->
      FRK mm (j + 4) e1 dl S2 S3 S4 w0 w12 w15 (Z_to_bv 64 (S4 + o4)) ->
      BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
      BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
      BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
      BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
      x41_hinv o1 n1 c1 -> x41_hinv o2 n2 c2 -> x41_hinv o3 n3 c3 -> x41_hinv o4 n4 c4 ->
      evt usegs POST (ST 0x22df8 mm (Z_to_bv 64 c2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x7 x8 x9
                       (Z_to_bv 64 (-20)) (Z_to_bv 64 (-1 * DT + -5)) x12 (Z_to_bv 64 c1) x14
                       (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 c4) (Z_to_bv 64 c3)
                       k2 x21 x22 k4 (Z_to_bv 64 (DST + (j + 4))) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x27
                       k1 x29 (Z_to_bv 64 (S1 + o1)) k3).

  Definition K4264 (rest : list byte) (j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 : Z) (b1 b2 b3 b4 pad1 pad2 pad3 pad4 : list byte)
      (w0 : word) : Prop :=
    forall mm (k1 k2 k3 k4 : word) p1 o1 p2 o2 p3 o3 p4 o4 (x7 x8 x9 x21 x22 x27 w12 w15 : word),
      KBASE mm rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 ->
      FRK mm j e1 dl S2 S3 S4 w0 w12 w15 (Z_to_bv 64 (S4 + o4)) ->
      BD1 mm k1 (Z_to_bv 64 p1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
      BD2 mm k2 (Z_to_bv 64 p2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
      BD3 mm k3 (Z_to_bv 64 p3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
      BD4 mm k4 (Z_to_bv 64 p4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
      x41_dinv o1 n1 p1 -> x41_dinv o2 n2 p2 -> x41_dinv o3 n3 p3 -> x41_dinv o4 n4 p4 ->
      evt usegs POST (ST 0x2323c mm (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x7 x8 x9
                       (Z_to_bv 64 (-20)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 p1) (Z_to_bv 64 (DST + (j + 3 * e1 + 3)))
                       (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 p4) (Z_to_bv 64 p3)
                       k2 x21 x22 k4 (Z_to_bv 64 (DST + (j + 3))) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x27
                       k1 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (S1 + o1)) k3).

End RLD.
