(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AZ4_C0 : Z := 0x8fc5c.
Definition AZ4_S1 : Z := 0x8fc74.
Definition AZ4_S2 : Z := 0x90ec8.
Definition AZ4_S3 : Z := 0x920e0.
Definition AZ4_S4 : Z := 0x932ec.
Definition AZ4_END : Z := 0x9448c.
Definition AZ4_DEPI : Z := 0x8fbec.
Definition AZ4_SB : Z := 0x7fff8000.

(* [comment removed for export] *)
Definition SPD (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word) : list cell :=
  [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14].

(* [comment removed for export] *)
Definition BD4A (c b : word) (jp : list byte) (p s l : word) : list cell := [C8 c; C4 b; CB 4 jp; C8 p; C8 s; C8 l].

Lemma SPD_size : forall w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14,
  cells_size (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14) = 120%nat.
Proof. reflexivity. Qed.
Lemma BD4A_size : forall c b jp p s l, cells_size (BD4A c b jp p s l) = 40%nat.
Proof. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Z4SF.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation W z := (Z_to_bv 64 z) (only parsing).
  Notation DL := (W (tl + 256 * mtl)) (only parsing).
  Notation D7 := (W (DST + dcap - 7)) (only parsing).
  Notation DE := (W (DST + dcap)) (only parsing).
  Notation DT4 := (W (DT + 4)) (only parsing).
  Notation DC := (W dcap) (only parsing).
  Notation SB := (W AZ4_SB) (only parsing).
  Notation M61 := (W (2^61)) (only parsing).

  (* [comment removed for export] *)
  Definition Z4SF (mm : amem) (spl bd4 bd3 bd2 bd1 : list cell) : Prop :=
    (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ bytes_at bsegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk bsegs mm lo (SP + -384)
    /\ rw_cells bsegs mm (SP + -384) spl /\ cells_size spl = 120%nat
    /\ rw_cells bsegs mm (SP + -264) bd4 /\ cells_size bd4 = 40%nat
    /\ rw_cells bsegs mm (SP + -224) bd3 /\ cells_size bd3 = 40%nat
    /\ rw_cells bsegs mm (SP + -184) bd2 /\ cells_size bd2 = 40%nat
    /\ rw_cells bsegs mm (SP + -144) bd1 /\ cells_size bd1 = 40%nat
    /\ rw_cells bsegs mm (SP + -104) FRS
    /\ mem_inv bsegs mm /\ munch DW m0 mm /\ wmono bsegs m0 mm.

  (* [comment removed for export] *)
  Notation ZS pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)) (only parsing).

  (* [comment removed for export] *)
  Definition z4s31_goal (Q : machine_state -> Prop) (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (c : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w10 w11 w12 : word) (bd4 bd3 bd2 : list cell) mm
           (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word),
    Z4SF mm (SPD w0 w1 DL D7 w4 w5 DE w7 w8 (W (DST + Qe)) w10 w11 w12 DT4 DC) bd4 bd3 bd2
         (BD4A c (W b) jp (W (SS + O + pt)) (W (SS + O)) (W (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v4 v5 v7 v8 v9 v11 : word)
            (z1 z5 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z20 z22 z23 z24 z25 z27 z28 z29 z31 : word),
       Z4SF mm' (SPD v0 w1 DL D7 v4 v5 DE v7 v8 v9 w10 v11 (W tl) DT4 DC) bd4 bd3 bd2 (BD4A c' b' jp' p' s' l') ->
       evtF bsegs RNG Q (ZS AZ4_S2 mm' z1 z5 DE z7 z8 x9 z10 z11 z12 z13 z14 z15 z16 z17 x18 x19 z20 SB z22 z23 z24 z25
                            M61 z27 z28 z29 DT4 z31)) ->
    evtF bsegs RNG Q (ZS AZ4_S1 mm x1 x5 x6 x7 x8 x9 x10 x11 (W (DST + q)) x13 x14 x15 x16 (W (DST + Qe)) x18 x19 x20 SB
                         x22 x23 x24 x25 x26 x27 x28 x29 DT4 x31).

  (* [comment removed for export] *)
  Definition z4s32_goal (Q : machine_state -> Prop) (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (c : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w11 : word) (bd4 bd3 bd1 : list cell) mm
           (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF mm (SPD w0 w1 DL D7 w4 w5 DE w7 w8 w9 (W (DST + Qe)) w11 (W tl) DT4 DC) bd4 bd3
         (BD4A c (W b) jp (W (SS + O + pt)) (W (SS + O)) (W (SS + O + 8))) bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v4 v5 v7 v8 v9 v10 v11 : word)
            (z1 z5 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z19 z20 z22 z23 z24 z25 z27 z28 z29 z31 : word),
       Z4SF mm' (SPD v0 w1 DL D7 v4 v5 DE v7 v8 v9 v10 v11 (W tl) DT4 DC) bd4 bd3 (BD4A c' b' jp' p' s' l') bd1 ->
       evtF bsegs RNG Q (ZS AZ4_S3 mm' z1 z5 DE z7 z8 x9 z10 z11 z12 z13 z14 z15 z16 z17 x18 z19 z20 SB z22 z23 z24 z25
                            M61 z27 z28 z29 DT4 z31)) ->
    evtF bsegs RNG Q (ZS AZ4_S2 mm x1 x5 DE x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (W (DST + q)) x20 SB
                         x22 x23 x24 x25 M61 x27 x28 x29 DT4 x31).

  (* [comment removed for export] *)
  Definition z4s33_goal (Q : machine_state -> Prop) (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w9 w10 w11 : word) (bd4 bd2 bd1 : list cell) mm
           (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF mm (SPD w0 (W (DST + Qe)) DL D7 w4 w5 DE w7 w8 w9 w10 w11 (W tl) DT4 DC) bd4
         (BD4A c (W b) jp (W (SS + O + pt)) (W (SS + O)) (W (SS + O + 8))) bd2 bd1 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v1 v4 v5 v7 v8 v9 v10 v11 : word)
            (z1 z5 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z22 z23 z24 z25 z27 z28 z29 z31 : word),
       Z4SF mm' (SPD v0 v1 DL D7 v4 v5 DE v7 v8 v9 v10 v11 (W tl) DT4 DC) bd4 (BD4A c' b' jp' p' s' l') bd2 bd1 ->
       evtF bsegs RNG Q (ZS AZ4_S4 mm' z1 z5 DE z7 z8 x9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 SB z22 z23 z24 z25
                            M61 z27 z28 z29 DT4 z31)) ->
    evtF bsegs RNG Q (ZS AZ4_S3 mm x1 x5 DE x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (W (DST + q)) x19 x20 SB
                         x22 x23 x24 x25 M61 x27 x28 x29 DT4 x31).

  (* [comment removed for export] *)
  Definition z4s34_goal (Q : machine_state -> Prop) (O L : Z) : Prop :=
    forall (q pt b : Z) (c : word) (jp : list byte) (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (bd3 bd2 bd1 : list cell) mm
           (x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF mm (SPD w0 w1 DL D7 w4 w5 DE w7 w8 w9 w10 w11 (W tl) DT4 DC)
         (BD4A c (W b) jp (W (SS + O + pt)) (W (SS + O)) (W (SS + O + 8))) bd3 bd2 bd1 ->
    0 <= q <= dcap -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : word)
            (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       Z4SF mm' (SPD v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 DC) (BD4A c' b' jp' p' s' l') bd3 bd2 bd1 ->
       evtF bsegs RNG Q (ZS AZ4_END mm' z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25
                            z26 z27 z28 z29 z30 z31)) ->
    evtF bsegs RNG Q (ZS AZ4_S4 mm x1 x5 DE x7 x8 (W (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 SB
                         x22 x23 x24 x25 M61 x27 x28 x29 DT4 x31).

  Definition z4end_goal (Q : machine_state -> Prop) : Prop :=
    forall (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word)
           (c1 b1 p1 s1' l1 c2 b2 p2 s2' l2 c3 b3 p3 s3' l3 c4 b4 p4 s4' l4 : word) (jp1 jp2 jp3 jp4 : list byte) mm
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    Z4SF mm (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 DC)
         (BD4A c4 b4 jp4 p4 s4' l4) (BD4A c3 b3 jp3 p3 s3' l3) (BD4A c2 b2 jp2 p2 s2' l2) (BD4A c1 b1 jp1 p1 s1' l1) ->
    (forall mm' (spl : list cell) (r : Z) (z1 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       Z4SF mm' spl
         (BD4A c4 b4 jp4 p4 s4' l4) (BD4A c3 b3 jp3 p3 s3' l3) (BD4A c2 b2 jp2 p2 s2' l2) (BD4A c1 b1 jp1 p1 s1' l1) ->
       r = dcap \/ r = 2^64 - 20 ->
       evtF bsegs RNG Q (ZS AZ4_DEPI mm' z1 (W r) z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25
                            z26 z27 z28 z29 z30 z31)) ->
    evtF bsegs RNG Q (ZS AZ4_END mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                         x26 x27 x28 x29 x30 x31).

End Z4SF.

(* [comment removed for export] *)
Definition z4ctx (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (rng_fs : alayout -> footprint -> Prop) (sp tp : word) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z)
    (cells : list deltX2) (cbs : list byte) (pdt : aptr) (SBL SBH : Z) (rstk : region) : Prop :=
  AHEAP AI L RNG st LB m0
  /\ (forall F k, ~ In (mkABlock (ABFake 0) F k) LB)
  /\ (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b))
  /\ 1 <= mtl <= 12 /\ tl <= mtl /\ In (HB pdt DT (DTABLE_BYTES mtl)) LB
  /\ x2_table_ok cells tl /\ cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells) /\ zlen cbs = 4 * 2^tl
  /\ ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) /\ 0 <= dcap < 2^32
  /\ Forall (fun c => 0 <= c < 256) src /\ zlen src < 2^26 /\ 16 <= SS
  /\ (0 < zlen src -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + zlen src <= SBH)
  /\ (DT + DTABLE_BYTES mtl <= SS \/ SS + zlen src <= DT) /\ (DST + dcap <= SS \/ SS + zlen src <= DST)
  /\ (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT)
  /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned sp - 4096 /\ bv_unsigned sp + 16 < al_top L
  /\ bv_unsigned sp mod 16 = 0 /\ tp = Z_to_bv 64 ATP /\ harness_invA m0
  /\ rclean m0 rstk /\ r_lo rstk <= lo /\ bv_unsigned sp <= r_hi rstk /\ ATOP <= r_rlo rstk /\ rrng RNG rstk
  /\ rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG.

(* [comment removed for export] *)
Definition z4s31_stmtA : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s31_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe.

Definition z4s32_stmtA : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s32_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe.

Definition z4s33_stmtA : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s33_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe.

Definition z4s34_stmtA : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src ->
  z4s34_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk.

Definition z4end_stmtA : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap ->
  z4end_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.

End CANSEC1.
