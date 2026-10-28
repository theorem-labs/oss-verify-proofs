(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi AF_huf_z4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s31k AF_huf_z4s31b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

Definition K32S3 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v4 v5 v7 v8 v9 v10 v11 : word)
         (z1 z5 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z19 z20 z22 z23 z24 z25 z27 z28 z29 z31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
           (SPD v0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) v4 v5 (Z_to_bv 64 (DST + dcap)) v7 v8 v9 v10 v11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c' b' jp' p' s' l') bd1 ->
    evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 (Z_to_bv 64 (DST + dcap)) z7 z8 x9 z10 z11 z12 z13 z14 z15 z16 z17 x18 z19 z20 (Z_to_bv 64 AZ4_SB) z22 z23 z24 z25 (Z_to_bv 64 (2^61)) z27 z28 z29 (Z_to_bv 64 (DT + 4)) z31)
                           FR (Z_to_bv 64 AZ4_S3) fc None mm' (seg_rom bsegs)).

Definition C32J (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) mm (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe ->
    ((exists pt, p = (Z_to_bv 64 (SS + O + pt)) /\ 0 <= pt /\ (pt = 0 \/ pt + 8 <= Lk)) /\ 0 <= b <= 64 \/ 64 < b < 2^31) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs)).

Definition C32H5 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) mm (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> tl < 12 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x90f24) fc None mm (seg_rom bsegs)).

Definition C32H4 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) mm (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q -> q + 8 <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b < 2^31 -> 12 <= tl ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x9168c) fc None mm (seg_rom bsegs)).

Definition C32R (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 x9 x18 : word) (bd4 bd3 bd1 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w11 : word) mm (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 w9 (Z_to_bv 64 (DST + Qe)) w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> Qe < q + 8 -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b < 2^31 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (DST + q)) x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x9156c) fc None mm (seg_rom bsegs)).

End CANSEC1.

Notation Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT :=
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] (only parsing).

Lemma z4s32_E : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O -> 1 <= L < 2^26 -> 0 <= pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> tl <= mtl -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> O <= 2^26 ->
  (Qe - q < 8 -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (- q + Qe)) (Z_to_bv 64 8) x12 x13 x14 x15 x16 x17
               x27 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 (Z_to_bv 64 (2^61)) x24 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x9156c) fc None mm' (seg_rom bsegs))) ->
  (8 <= Qe - q -> 12 <= tl -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 12) (Z_to_bv 64 tl) x12 x13 x14 x15 x16 x17
               x27 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 (Z_to_bv 64 (2^61)) x24 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x9168c) fc None mm' (seg_rom bsegs))) ->
  (8 <= Qe - q -> tl < 12 -> b <= 64 -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (- tl + -256 * mtl)) (Z_to_bv 64 b) (Z_to_bv 64 (DST + Qe)) x13 x14 x15 x16 x17
               x27 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) (Z_to_bv 64 (- DT + -5)) x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x90f24) fc None mm' (seg_rom bsegs))) ->
  (8 <= Qe - q -> tl < 12 -> 64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) (Z_to_bv 64 (DST + Qe)) x13 x14 x15 x16 x17
               x27 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 (Z_to_bv 64 (2^61)) x24 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x27 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 (Z_to_bv 64 (2^61)) x24 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 AZ4_S2) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp SP DST dcap SS DT q Qe O L pt b cz tl mtl
    SPL BD MI RS HD HDE HDC HQ HQE HS HSE HO HL HPT HB HCZ HTL HMT HTM HDT HSP HO2 K1 K2 K3 K4.
  unfold AZ4_S2, AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec (Qe - q) 8) as [C1|C1]; [|destruct (Z_lt_ge_dec tl 12) as [C2|C2]; [destruct (Z_le_gt_dec b 64) as [C3|C3]|]].
  4: kx_runFmd [0x90f24; 0x9156c; 0x9168c; 0x91c20; 0x8fbec] 60%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  3: kx_runFmd [0x90f24; 0x9156c; 0x9168c; 0x91c20; 0x8fbec] 60%nat [false; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [0x90f24; 0x9156c; 0x9168c; 0x91c20; 0x8fbec] 60%nat [false; false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x90f24; 0x9156c; 0x9168c; 0x91c20; 0x8fbec] 60%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: rewrite ?z4_eext in *.
  all: repeat (lazymatch goal with |- context [edenot ?E ?e] =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
         cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end).
  all: rewrite ?z4_dl_b0 in * by lia.
  all: rewrite ?Z_to_bv_bv_unsigned in *.
  all: repeat match goal with H : rw_cells _ _ _ [C8 (ext_val false 0 1 (edenot ?E ?e))] |- _ =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite (ez_ok zv E (kE_atoms zv xs) e) in H; let na := eval vm_compute in (length zv) in
         cbv [ez] in H; change (length zv) with na in H; cbv [nth Nat.ltb Nat.leb] in H; rewrite z4_dl_b0 in H by lia end end.
  4: (eapply K2; [lia | lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  3: (eapply K4; [lia | lia | lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  2: z4_m64.
  2: (eapply K3; [lia | lia | lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  1: (eapply K1; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_R5A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91044) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90f3c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91044] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + (p2 + qb)); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_R5B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91044) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90f3c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91044] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_H5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x9103c) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -184))
               (Z_to_bv 64 b) z12 x13 x14 x15 x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z13 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) z12 z13 x14 x15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91044) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91044) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x90f24) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x90f3c] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x90f3c] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x90f3c] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s32_R5A with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s32_R5B with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s32_J : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap -> 0 <= b < 2^31 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (Qe - q < 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe)) x9 (Z_to_bv 64 (- q + Qe)) (Z_to_bv 64 2) x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x91ec8) fc None mm (seg_rom bsegs))) ->
  (2 <= Qe - q -> b <= 64 -> forall z10 : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x91c60) fc None mm (seg_rom bsegs))) ->
  (2 <= Qe - q -> 64 < b -> forall z10 : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x91eb8) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
           (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 c p s l jp SP DST dcap DT q Qe b tl mtl
    SPL BD2 MI RS HD HDE HDC HQ HQE HB HTL HMT HDT HSP K1 K2 K3.
  unfold AZ4_SB in *.
  destruct (Z_lt_ge_dec (Qe - q) 2) as [C1|C1]; [|destruct (Z_le_gt_dec b 64) as [C2|C2]].
  3: kx_runFmd [0x91c60; 0x91ec8; 0x91eb8; 0x8fbec] 40%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
     KZWord (SP + -176) 4 b; KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [0x91c60; 0x91ec8; 0x91eb8; 0x8fbec] 40%nat [false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
     KZWord (SP + -176) 4 b; KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x91c60; 0x91ec8; 0x91eb8; 0x8fbec] 40%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
     KZWord (SP + -176) 4 b; KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: z4_m64.
  3: (eapply K3; lia).
  2: z4_m64.
  2: (eapply K2; lia).
  1: (apply K1; lia).
Qed.

Lemma z4s32_R2A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91d84) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x25 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91c78) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91d84] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + (p2 + qb)); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_R2B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91d84) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x25 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91c78) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91d84] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_H2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x91d78) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -184))
               (Z_to_bv 64 b) z12 x13 x14 x15 x16 x17 x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z13 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) z12 z13 x14 x15 x16 x17
               x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91ec4) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91d84) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91d84) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x25 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91c60) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x91ec4; 0x91c78] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x91ec4; 0x91c78] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x91ec4; 0x91c78] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s32_R2A with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s32_R2B with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s32_B2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 2 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b <= 64 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (z10 y12 y13 y14 y15 y16 y17 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (b + nb)); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 (Z_to_bv 64 (b + nb)) y12 y13
              y14 y15 y16 y17 x25 (Z_to_bv 64 (DST + (q + bv_unsigned z10))) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91e50) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 (Z_to_bv 64 1) x11 x12 x13
           x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91d84) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3
    SPL BD2 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 2 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x91e50] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 2 (2^32); KZRange (Qe - q) 2 (2^32); KZRange (dcap - q) 2 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 64; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: let R40 := fresh "R40" in kx_range (EVar 40) R40.
  all: let R42 := fresh "R42" in kx_range (EVar 42) R42.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s32_C2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap -> 0 <= b < 2^31 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (b <= 64 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x91c60) fc None mm (seg_rom bsegs))) ->
  (64 < b ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x91eb8) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91e50) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 c p s l jp SP DST dcap DT q Qe b tl mtl
    SPL BD2 MI RS HD HDE HDC HQ HQE HB HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec b 64) as [C|C].
  2: kx_runFmd [0x91c60; 0x91eb8] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 65 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -176) 4 b; KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x91c60; 0x91eb8] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 64;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -176) 4 b; KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: kx_post_regs_keep.
  all: z4post_ez.
  1: apply K1; lia.
  1: apply K2; lia.
Qed.

Lemma z4s32_RT : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (bd3 : list cell)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x91d78) (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91d84) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x91d78) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            x30 x31)
       F (Z_to_bv 64 0x91d78) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 bd3 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP K.
  unfold AZ4_SB in *.
  kx_runFmd [0x91d84] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s32_X2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (Qe - q < 2 \/ x10 = Z_to_bv 64 0) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91ec4) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91d84) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP HC K.
  unfold AZ4_SB in *.
  destruct (Z_lt_ge_dec (Qe - q) 2) as [C|C].
  - kx_runFmd [0x91e50; 0x91ec4] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
  - destruct HC as [HC|HC]; [lia|]. subst x10.
    kx_runFmd [0x91e50; 0x91ec4] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
Qed.


Lemma z4s32_R4A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x917e4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x916dc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x917e4] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + (p2 + qb)); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_R4B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x917e4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x916dc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x917e4] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_H4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x917dc) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -184))
               (Z_to_bv 64 b) z12 x13 x14 x15 x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z13 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) z12 z13 x14 x15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x917e4) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x917e4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x916c4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x916dc] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x916dc] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x916dc] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s32_R4A with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s32_R4B with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s32_L5R : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91044) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9103c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT Qe tl mtl SPL MI RS HD HDE HDC HQE HTL HMT HDT HSP K.
  kx_runFmd [0x91044] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s32_L4R : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x917e4) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x917dc) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT Qe tl mtl SPL MI RS HD HDE HDC HQE HTL HMT HDT HSP K.
  kx_runFmd [0x917e4] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s32_X5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (Qe < q + 10 \/ x10 = Z_to_bv 64 0) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 (DST + q)) x20 x21 x22 (Z_to_bv 64 (DST + Qe + -9)) x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 (DST + q)) x20 x21 x22 (Z_to_bv 64 (DST + Qe + -9)) x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91044) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP HX K.
  destruct (Z_lt_ge_dec Qe (q + 10)) as [C1|C1].
  - kx_runFmd [0x91c20] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: try lia.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
  - destruct HX as [HX|HX]; [lia|]. subst x10.
    kx_runFmd [0x91c20] 10%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: try lia.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
Qed.

Lemma z4s32_X4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (Qe < q + 8 \/ x10 = Z_to_bv 64 0) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 (DST + q)) x20 x21 x22 (Z_to_bv 64 (DST + Qe + -7)) x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 (DST + q)) x20 x21 x22 (Z_to_bv 64 (DST + Qe + -7)) x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x917e4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP HX K.
  destruct (Z_lt_ge_dec Qe (q + 8)) as [C1|C1].
  - kx_runFmd [0x91c20] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: try lia.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
  - destruct HX as [HX|HX]; [lia|]. subst x10.
    kx_runFmd [0x91c20] 10%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: try lia.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
Qed.

Lemma z4s32_N4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O -> 1 <= L < 2^26 -> 0 <= pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> tl <= mtl -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> O <= 2^26 ->
  (b <= 64 -> forall mm',
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (- tl + -256 * mtl)) (Z_to_bv 64 b) (Z_to_bv 64 (DST + Qe)) x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (DST + Qe + -7)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x916c4) fc None mm' (seg_rom bsegs))) ->
  (64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) (Z_to_bv 64 (DST + Qe)) x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (DST + q)) x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x9168c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp SP DST dcap SS DT q Qe O L pt b cz tl mtl
    SPL BD MI RS HD HDE HDC HQ HQE HS HSE HO HL HPT HB HCZ HTL HMT HTM HDT HSP HO2 K1 K2.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_le_gt_dec b 64) as [C3|C3].
  2: kx_runFmd [0x916c4; 0x91c20; 0x8fbec] 40%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x916c4; 0x91c20; 0x8fbec] 40%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: rewrite ?z4_eext in *.
  all: repeat (lazymatch goal with |- context [edenot ?E ?e] =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
         cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end).
  all: rewrite ?z4_dl_b0 in * by lia.
  all: rewrite ?Z_to_bv_bv_unsigned in *.
  all: repeat match goal with H : rw_cells _ _ _ [C8 (ext_val false 0 1 (edenot ?E ?e))] |- _ =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite (ez_ok zv E (kE_atoms zv xs) e) in H; let na := eval vm_compute in (length zv) in
         cbv [ez] in H; change (length zv) with na in H; cbv [nth Nat.ltb Nat.leb] in H; rewrite z4_dl_b0 in H by lia end end.
  2: (eapply K2; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  1: z4_m64.
  1: (eapply K1; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_RH0 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (b <= 64 ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 65) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9157c) fc None mm (seg_rom bsegs))) ->
  (64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9156c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp SP DST dcap SS DT q Qe O L pt b cz tl mtl
    SPL BD MI RS HD HDE HDC HQ HQE HS HSE HO HL HPT HB HCZ HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_le_gt_dec b 64) as [C3|C3].
  2: kx_runFmd [0x9157c; 0x91c20] 30%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x9157c; 0x91c20] 30%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: rewrite ?z4_eext in *.
  all: repeat (lazymatch goal with |- context [edenot ?E ?e] =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
         cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end).
  all: rewrite ?z4_dl_b0 in * by lia.
  all: rewrite ?Z_to_bv_bv_unsigned in *.
  2: (eapply K2; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  1: (apply K1; lia).
Qed.

Lemma z4s32_LR : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91c18) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT Qe tl mtl SPL MI RS HD HDE HDC HQE HTL HMT HDT HSP K.
  kx_runFmd [0x91c20] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange Qe 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s32_RA : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 z11 z12 z13 z14 z15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 qb) (Z_to_bv 64 (SS + O)) x15 x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91594) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91c20] 80%nat [true; true; true; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + (p2 + qb)); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_RB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 z11 z12 z13 z14 z15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 qb) (Z_to_bv 64 (SS + O)) x15 x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB)
           x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x91594) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt qb b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91c20] 80%nat [true; true; true; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -304) 8 (DST + Qe); KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s32_RH : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x91c18) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -184))
               (Z_to_bv 64 b) z12 x13 x14 x15 x16 x17 x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z14 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) z12 x13 z14 x15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 z11 z12 z13 z14 z15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z10 z11 z12 z13 z14 z15 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
      rw_cells bsegs mm' (SP + -184) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 z11 z12 z13 z14 z15 x16 x17
               x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
           F (Z_to_bv 64 0x91c20) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x27 x18 x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x25 x26 x24 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9157c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w11 jp sb SP DST dcap SS DT q Qe O L pt b cz tl mtl A1 L1
    SPL BD2 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HQE HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x91594] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x91594] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x91c20; 0x91594] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -184) 8 cz; KZWord (SP + -176) 4 b; KZWord (SP + -168) 8 (SS + O + pt); KZWord (SP + -160) 8 (SS + O);
     KZWord (SP + -152) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s32_RA with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s32_RB with (qb := b / 8) (DST := DST) (dcap := dcap) (Qe := Qe) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s32_c4mod : forall m A (c : word) (V : Z) (jp : list byte) (p s l : word),
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 V); CB 4 jp; C8 p; C8 s; C8 l] ->
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 (V mod 2^32)); CB 4 jp; C8 p; C8 s; C8 l].
Proof.
  intros m A c V jp p s l RW.
  assert (E : le4 (Z_to_bv 64 V) = le4 (Z_to_bv 64 (V mod 2^32))).
  { unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite !Z_to_le_bytes_mod by (cbn; lia). reflexivity. }
  unfold rw_cells, cells_at in *. destruct RW as [[WF BA] WR].
  split; [split|].
  - exact WF.
  - cbn [cells_bytes cbytes] in BA |- *. rewrite <- E. exact BA.
  - exact WR.
Qed.

Lemma z4s32_NB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 2 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (z10 y11 y12 y13 y14 y15 y16 y17 : word) (b' : Z), 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 y11 y12 y13
              y14 y15 y16 y17 x25 (Z_to_bv 64 (DST + (q + bv_unsigned z10))) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x9204c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13
           x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91f8c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3
    SPL BD2 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 2 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x9204c] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 2 (2^32); KZRange (Qe - q) 2 (2^32); KZRange (dcap - q) 2 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: let R43 := fresh "R43" in kx_range (EVar 43) R43.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s32_LA : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b c tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= q + 1 -> Qe <= dcap ->
  0 <= b < 2^32 -> 0 <= c < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q = Qe ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + Qe)) x11 x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x920e0) fc None mm (seg_rom bsegs))) ->
  (q + 1 = Qe -> forall (i : Z) (y10 y12 : word), 0 <= i < 2^tl ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 (Z_to_bv 64 i) y12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91ee8) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
            x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22 x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91ec8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 p s l jp SP DST dcap DT q Qe b c tl mtl
    SPL BD2 MI RS HD HDE HDC HQ HQ1 HQE HB HC HTL HMT HDT HSP K0 K1.
  unfold AZ4_SB in *.
  destruct (Z.eq_dec q Qe) as [E|E].
  - kx_runFmd [0x920e0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 0 0;
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -304) 8 (DST + Qe);
      KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K0; lia.
  - kx_runFmd [0x91ee8] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 1 1;
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b; KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -304) 8 (DST + Qe);
      KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: kx_post_regs_keep.
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r25 ?r18 ?r19 ?r21 ?r22 ?r20 ?r23 ?r24 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) _ _ _ _ _ _) =>
      rewrite <- (Z_to_bv_bv_unsigned r11); eapply (K1 ltac:(lia) (bv_unsigned r11) r10 r12) end.
    all: lazymatch goal with
         | |- evtF _ _ _ _ => z4post_ez
         | |- 0 <= bv_unsigned (edenot ?E (EAlu ALU_SRL ?x ?s)) < 2^?t => apply (z4_srl_ltt E x s t); [lia | z4uzm]
         end.
Qed.

Lemma z4s32_br_shi : forall E X K,
  bv_unsigned (edenot E K) = 2^61 -> bv_unsigned (edenot E X) < 2^61 ->
  branch_taken BC_EQ (edenot E (EAlu ALU_SRL (EAlu ALU_ADD X K) (ELit 62))) (edenot E (ELit 0)) = true.
Proof.
  intros E X K HK HX.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [HX0 _].
  cbn [edenot branch_taken] in *.
  rewrite bv_eqb_Z, u_srl64, u_add64, HK.
  change (bv_unsigned (Z_to_bv 64 62)) with 62. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (62 mod 64) with 62.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma z4s32_LB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y13 : word), bv_unsigned y10 = DT + 4 + 4 * i -> 1 <= bv_unsigned y11 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 1) y13
              x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22
              x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91f5c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 i) x12 x13
           x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22
           x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91ee8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i
    SPL BD2 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HI HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x91f5c] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EAlu ALU_SRL (EAlu ALU_ADD ?X ?K) (ELit 62))) _ = true => apply (z4s32_br_shi E X K); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: kx_post_regs_keep.
  all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (ev _ ?n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => let R := fresh "R" in kx_range (EVar n) R end.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s32_br_sx63 : forall E X, 64 <= bv_unsigned (edenot E X) < 2^32 ->
  branch_taken BC_LTU (edenot E (ELit 63)) (edenot E (EExt true 0 4 X)) = true.
Proof.
  intros E X HX. cbn [edenot branch_taken] in *.
  rewrite bv_ltu_Z. change (bv_unsigned (Z_to_bv 64 63)) with 63.
  destruct (Z_lt_le_dec (bv_unsigned (edenot E X)) (2^31)) as [HS|HS].
  - rewrite u_ext_sx0_small by (cbn; lia). apply Z.ltb_lt. lia.
  - rewrite u_ext_sx0_high by (cbn; lia). apply Z.ltb_lt. lia.
Qed.

Lemma z4s32_LC : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i len : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> 1 <= len <= 2 -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y12 y13 : word) (b' : Z),
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13
              x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q + 1)) x19 (Z_to_bv 64 AZ4_SB) x22
              x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x920e0) fc None mm' (seg_rom bsegs))) ->
  (forall (mm' : amem) (y12 y13 : word) (v : Z), 0 <= v < 128 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) (Z_to_bv 64 64) y12 y13
              x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22
              x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x920c4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 len) (Z_to_bv 64 1) x13
           x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22
           x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91f5c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i len
    SPL BD2 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HI HLN HQD HTL HMT HDT HSP HB HC HTE HT2 K K2.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  destruct (Z.eq_dec len 1) as [LN1 | LN2]; [| assert (LN2' : len = 2) by lia; destruct (Z_le_gt_dec b 63) as [B63 | B64]].
  3: kx_runFmd [0x920e0] 200%nat [true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 64 (2^32 - 1); KZRange len 2 2; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  2: kx_runFmd [0x920e0] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 63; KZRange len 2 2; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  1: kx_runFmd [0x920e0] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange len 1 1; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_LTU (edenot ?E (ELit 63)) (edenot ?E (EExt true 0 4 ?X)) = true => apply (z4s32_br_sx63 E X); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: kx_post_regs_keep.
  2: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + bv_unsigned (ev _ ?n))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => let R := fresh "R" in kx_range (EVar n) R end.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: first [eapply K | eapply K2].
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s32_LD : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 v : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = Qe -> 0 <= v < 128 -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y12 y13 : word) (b' : Z),
     rw_cells bsegs mm' (SP + -384) (Z4SPL2 w0 w1 w4 w5 w7 w8 w9 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13
              x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q + 1)) x19 (Z_to_bv 64 AZ4_SB) x22
              x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x920e0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) (Z_to_bv 64 64) x12 x13
           x14 x15 x16 x17 x25 (Z_to_bv 64 (DST + q)) x19 (Z_to_bv 64 AZ4_SB) x22
           x20 x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x920c4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 v
    SPL BD2 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HV HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  destruct (Z_lt_le_dec v 64) as [V64 | V64].
  2: kx_runFmd [0x920e0] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange v 64 127; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  1: kx_runFmd [0x920e0] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange v 0 63; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -184) 8 c; KZWord (SP + -176) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -184) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_LTU (edenot ?E (ELit 63)) (edenot ?E (EExt true 0 4 ?X)) = true => apply (z4s32_br_sx63 E X); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s32_BR1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384)
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q + 2 <= Qe ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91f8c) fc None mm (seg_rom bsegs))) ->
  (Qe < q + 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91ec8) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91ec4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec (q + 2) Qe) as [C|C].
  - kx_runFmd [0x91f8c; 0x91ec8] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact (K1 C).
  - kx_runFmd [0x91f8c; 0x91ec8] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (q + 2 - Qe) 1 2;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K2; lia.
Qed.

Lemma z4s32_BR2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384)
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q + 2 <= Qe ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91f8c) fc None mm (seg_rom bsegs))) ->
  (Qe < q + 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91ec8) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9204c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec (q + 2) Qe) as [C|C].
  - kx_runFmd [0x91f8c; 0x91ec8] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact (K1 C).
  - kx_runFmd [0x91f8c; 0x91ec8] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (q + 2 - Qe) 1 2;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K2; lia.
Qed.

Lemma z4s32_TN : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b tl mtl : Z),
  rw_cells bsegs mm (SP + -384)
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
  rw_cells bsegs mm (SP + -184) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap -> 0 <= b < 2^32 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (forall mm' : amem,
     rw_cells bsegs mm' (SP + -384)
     [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 (DST + Qe)); C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
     rw_cells bsegs mm' (SP + -184) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00); C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm mm' -> wmono bsegs mm mm' ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 (Z_to_bv 64 0x20e00) x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x91ec4) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x25 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x23 x24 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x91eb8) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w11 c p s l jp SP DST dcap DT q Qe b tl mtl SPL BD2 MI RS HD HDE HDC HQ HQE HB HTL HMT HDT HSP K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -184, SP + -144)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x91ec4] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^32 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWr (SP + -384) 120; KZWr (SP + -184) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD2; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge ].
Qed.


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
(* [comment removed for export] *)
(* [comment removed for export] *)
