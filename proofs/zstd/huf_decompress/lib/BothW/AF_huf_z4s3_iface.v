(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  Notation W v := (Z_to_bv 64 v) (only parsing).
  Notation DL := (W (tl + 256 * mtl)) (only parsing).
  Notation D7 := (W (DST + dcap - 7)) (only parsing).
  Notation DE := (W (DST + dcap)) (only parsing).
  Notation DT4 := (W (DT + 4)) (only parsing).
  Notation DC := (W dcap) (only parsing).
  Notation SB := (W AZ4_SB) (only parsing).
  Notation M61 := (W (2^61)) (only parsing).

  (* [comment removed for export] *)
  Definition Z4SF (mm : amem) (spl bd4 bd3 bd2 bd1 : list cell) : Prop :=
    (exists out : list Z, u8arr bsegs mm DST (map (Z_to_bv 8) out) /\ zlen out = dcap)
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
    /\ mem_inv bsegs mm
    /\ munch DW m0 mm
    /\ wmono bsegs m0 mm.

  (* [comment removed for export] *)
  Notation ZS ip mem v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
             v28 v29 v30 v31 :=
    (MS (mkR v1 (W (SP + -384)) gp tp v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
             v24 v25 v26 v27 v28 v29 v30 v31) FR (W ip) fc None mem (seg_rom bsegs)) (only parsing).

  (* [comment removed for export] *)
  Definition z4s31_goal (Q : machine_state -> Prop) (O L Qe : Z) : Prop :=
    forall (op ip nb : Z) (cont : word) (pad : list byte)
           (f0 f1 f4 f5 f7 f8 f10 f11 f12 : word) (d4 d3 d2 : list cell) (mem : amem)
           (r1 r5 r6 r7 r8 r9 r10 r11 r13 r14 r15 r16 r18 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r31 : word),
      Z4SF mem (SPD f0 f1 DL D7 f4 f5 DE f7 f8 (W (DST + Qe)) f10 f11 f12 DT4 DC) d4 d3 d2
        (BD4A cont (W nb) pad (W (SS + O + ip)) (W (SS + O)) (W (SS + O + 8))) ->
      0 <= op <= Qe -> 0 <= ip -> ip = 0 \/ ip + 8 <= L -> 0 <= nb < 2^31 ->
      (forall (mem' : amem) (bc bn bp bs bl : word) (pad' : list byte) (g0 g4 g5 g7 g8 g9 g11 : word)
              (t1 t5 t7 t8 t10 t11 t12 t13 t14 t15 t16 t17 t20 t22 t23 t24 t25 t27 t28 t29 t31 : word),
         Z4SF mem' (SPD g0 f1 DL D7 g4 g5 DE g7 g8 g9 f10 g11 (W tl) DT4 DC) d4 d3 d2 (BD4A bc bn pad' bp bs bl) ->
         evtF bsegs RNG Q (ZS AZ4_S2 mem' t1 t5 DE t7 t8 r9 t10 t11 t12 t13 t14 t15 t16 t17 r18 r19 t20 SB t22 t23
                             t24 t25 M61 t27 t28 t29 DT4 t31)) ->
      evtF bsegs RNG Q (ZS AZ4_S1 mem r1 r5 r6 r7 r8 r9 r10 r11 (W (DST + op)) r13 r14 r15 r16 (W (DST + Qe)) r18 r19
                          r20 SB r22 r23 r24 r25 r26 r27 r28 r29 DT4 r31).

  (* [comment removed for export] *)
  Definition z4s32_goal (Q : machine_state -> Prop) (O L Qe : Z) : Prop :=
    forall (op ip nb : Z) (cont : word) (pad : list byte)
           (f0 f1 f4 f5 f7 f8 f9 f11 : word) (d4 d3 d1 : list cell) (mem : amem)
           (r1 r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r20 r22 r23 r24 r25 r27 r28 r29 r31 : word),
      Z4SF mem (SPD f0 f1 DL D7 f4 f5 DE f7 f8 f9 (W (DST + Qe)) f11 (W tl) DT4 DC) d4 d3
        (BD4A cont (W nb) pad (W (SS + O + ip)) (W (SS + O)) (W (SS + O + 8))) d1 ->
      0 <= op <= Qe -> 0 <= ip -> ip = 0 \/ ip + 8 <= L -> 0 <= nb < 2^31 ->
      (forall (mem' : amem) (bc bn bp bs bl : word) (pad' : list byte) (g0 g4 g5 g7 g8 g9 g10 g11 : word)
              (t1 t5 t7 t8 t10 t11 t12 t13 t14 t15 t16 t17 t19 t20 t22 t23 t24 t25 t27 t28 t29 t31 : word),
         Z4SF mem' (SPD g0 f1 DL D7 g4 g5 DE g7 g8 g9 g10 g11 (W tl) DT4 DC) d4 d3 (BD4A bc bn pad' bp bs bl) d1 ->
         evtF bsegs RNG Q (ZS AZ4_S3 mem' t1 t5 DE t7 t8 r9 t10 t11 t12 t13 t14 t15 t16 t17 r18 t19 t20 SB t22 t23
                             t24 t25 M61 t27 t28 t29 DT4 t31)) ->
      evtF bsegs RNG Q (ZS AZ4_S2 mem r1 r5 DE r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 (W (DST + op)) r20 SB
                          r22 r23 r24 r25 M61 r27 r28 r29 DT4 r31).

  (* [comment removed for export] *)
  Definition z4s33_goal (Q : machine_state -> Prop) (O L Qe : Z) : Prop :=
    forall (op ip nb : Z) (cont : word) (pad : list byte)
           (f0 f4 f5 f7 f8 f9 f10 f11 : word) (d4 d2 d1 : list cell) (mem : amem)
           (r1 r5 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r27 r28 r29 r31 : word),
      Z4SF mem (SPD f0 (W (DST + Qe)) DL D7 f4 f5 DE f7 f8 f9 f10 f11 (W tl) DT4 DC) d4
        (BD4A cont (W nb) pad (W (SS + O + ip)) (W (SS + O)) (W (SS + O + 8))) d2 d1 ->
      0 <= op <= Qe -> 0 <= ip -> ip = 0 \/ ip + 8 <= L -> 0 <= nb < 2^31 ->
      (forall (mem' : amem) (bc bn bp bs bl : word) (pad' : list byte) (g0 g1 g4 g5 g7 g8 g9 g10 g11 : word)
              (t1 t5 t7 t8 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t22 t23 t24 t25 t27 t28 t29 t31 : word),
         Z4SF mem' (SPD g0 g1 DL D7 g4 g5 DE g7 g8 g9 g10 g11 (W tl) DT4 DC) d4 (BD4A bc bn pad' bp bs bl) d2 d1 ->
         evtF bsegs RNG Q (ZS AZ4_S4 mem' t1 t5 DE t7 t8 r9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 SB t22 t23
                             t24 t25 M61 t27 t28 t29 DT4 t31)) ->
      evtF bsegs RNG Q (ZS AZ4_S3 mem r1 r5 DE r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 (W (DST + op)) r19 r20 SB
                          r22 r23 r24 r25 M61 r27 r28 r29 DT4 r31).

  (* [comment removed for export] *)
  Definition z4s34_goal (Q : machine_state -> Prop) (O L : Z) : Prop :=
    forall (op ip nb : Z) (cont : word) (pad : list byte)
           (f0 f1 f4 f5 f7 f8 f9 f10 f11 : word) (d3 d2 d1 : list cell) (mem : amem)
           (r1 r5 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r22 r23 r24 r25 r27 r28 r29 r31 : word),
      Z4SF mem (SPD f0 f1 DL D7 f4 f5 DE f7 f8 f9 f10 f11 (W tl) DT4 DC)
        (BD4A cont (W nb) pad (W (SS + O + ip)) (W (SS + O)) (W (SS + O + 8))) d3 d2 d1 ->
      0 <= op <= dcap -> 0 <= ip -> ip = 0 \/ ip + 8 <= L -> 0 <= nb < 2^31 ->
      (forall (mem' : amem) (bc bn bp bs bl : word) (pad' : list byte)
              (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 : word)
              (t1 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29
               t30 t31 : word),
         Z4SF mem' (SPD g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 DC) (BD4A bc bn pad' bp bs bl) d3 d2 d1 ->
         evtF bsegs RNG Q (ZS AZ4_END mem' t1 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23
                             t24 t25 t26 t27 t28 t29 t30 t31)) ->
      evtF bsegs RNG Q (ZS AZ4_S4 mem r1 r5 DE r7 r8 (W (DST + op)) r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 SB
                          r22 r23 r24 r25 M61 r27 r28 r29 DT4 r31).

  Definition z4end_goal (Q : machine_state -> Prop) : Prop :=
    forall (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : word)
           (bc1 bn1 bp1 bs1 bl1 bc2 bn2 bp2 bs2 bl2 bc3 bn3 bp3 bs3 bl3 bc4 bn4 bp4 bs4 bl4 : word)
           (pad1 pad2 pad3 pad4 : list byte) (mem : amem)
           (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30
            r31 : word),
      Z4SF mem (SPD f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 DC)
        (BD4A bc4 bn4 pad4 bp4 bs4 bl4) (BD4A bc3 bn3 pad3 bp3 bs3 bl3)
        (BD4A bc2 bn2 pad2 bp2 bs2 bl2) (BD4A bc1 bn1 pad1 bp1 bs1 bl1) ->
      (forall (mem' : amem) (frame : list cell) (rv : Z)
              (u1 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30
               u31 : word),
         Z4SF mem' frame (BD4A bc4 bn4 pad4 bp4 bs4 bl4) (BD4A bc3 bn3 pad3 bp3 bs3 bl3)
           (BD4A bc2 bn2 pad2 bp2 bs2 bl2) (BD4A bc1 bn1 pad1 bp1 bs1 bl1) ->
         rv = dcap \/ rv = 2^64 - 20 ->
         evtF bsegs RNG Q (ZS AZ4_DEPI mem' u1 (W rv) u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21
                             u22 u23 u24 u25 u26 u27 u28 u29 u30 u31)) ->
      evtF bsegs RNG Q (ZS AZ4_END mem r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24
                          r25 r26 r27 r28 r29 r30 r31).

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
