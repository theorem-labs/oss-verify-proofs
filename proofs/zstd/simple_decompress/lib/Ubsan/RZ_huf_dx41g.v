(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf417_kit_rlk huf417_kit_rlo.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41G.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Definition DINV1 (o n p : Z) : Prop := 0 <= p <= 112 /\ 0 <= o /\ (o = 0 \/ (o + 8 <= n /\ p <= 56)).
  Definition DINV2 (o n p q : Z) : Prop := 0 <= p <= 100 /\ 0 <= q <= 12 /\ 0 <= o /\ (o = 0 \/ (o + 8 <= n /\ p <= 44)).
  Definition HINV (o n c : Z) : Prop := 0 <= c <= 64 /\ 0 <= o /\ (o = 0 \/ (o + 8 <= n /\ c <= 8)).
  Definition x41_hide (P : Prop) : Prop := P.          (* [comment removed for export] *)
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation K4448 := (huf417_kit_rlk.K4448 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation K4608 := (huf417_kit_rlk.K4608 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
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

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].   (* [comment removed for export] *)

  Lemma x41_r_lo : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    K4448 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4608 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    forall mm (k1 k2 k3 k4 : word) p1 o1 p2 o2 p3 o3 p4 o4 (x7 x8 x9 x21 x22 x27 w12 w15 : word),
      KBASE mm rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 ->
      FRK mm j e1 dl S2 S3 S4 w0 w12 w15 (Z_to_bv 64 (S4 + o4)) ->
      BD1 mm k1 (Z_to_bv 64 p1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
      BD2 mm k2 (Z_to_bv 64 p2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
      BD3 mm k3 (Z_to_bv 64 p3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
      BD4 mm k4 (Z_to_bv 64 p4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
      x41_dinv o1 n1 p1 -> x41_dinv o2 n2 p2 -> x41_dinv o3 n3 p3 -> x41_dinv o4 n4 p4 -> o1 < 8 ->
      evt usegs POST (ST 0x2323c mm (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x7 x8 x9
                       (Z_to_bv 64 (-20)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 p1) (Z_to_bv 64 (DST + (j + 3 * e1 + 3)))
                       (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 p4) (Z_to_bv 64 p3)
                       k2 x21 x22 k4 (Z_to_bv 64 (DST + (j + 3))) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x27
                       k1 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (S1 + o1)) k3).
  Proof using CTX DJ3.
    exact (huf417_kit_rlo.x41_rlo_k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3).
  Qed.
End DX41G.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
