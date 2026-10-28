(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s3_iface AF_huf_z4s2_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

Definition AZ4_D : Z := 0x8e4e4.
Definition AZ4_DRET : Z := 0x8776c.
Definition AZ4_I1 : Z := 0x8e740.
Definition Z4D_STACK : Z := 7664.

Section CANSEC1. Context {rc : runConstT}.

Definition z4d_postA (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
    (fc : bv 32) (DST dcap lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m m' /\ wmono bsegs m m'.

Section Z4D.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation W z := (Z_to_bv 64 z) (only parsing).
  Notation POSTD := (z4d_postA RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc DST dcap lo m0).
  Notation Z4SF := (AF_huf_z4s3_iface.Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation ZS pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)) (only parsing).

  Definition z4d_goal : Prop :=
    forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    ((DST = 0 /\ dcap = 0) \/ exists buf, u8arr bsegs m0 DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap) ->
    bytes_at bsegs m0 SS (map (Z_to_bv 8) src) ->
    bytes_at bsegs m0 (DT + 4) cbs ->
    bytes_at bsegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    stk bsegs m0 lo SP -> mem_inv bsegs m0 ->
    evtF bsegs RNG POSTD
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W DST) (W dcap) (W SS) (W n) (W DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          FR (W AZ4_D) fc None m0 (seg_rom bsegs)).

  Definition z4epi_hyp (Q : machine_state -> Prop) : Prop :=
    forall mm (spl bd4 bd3 bd2 bd1 : list cell)
           (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
    Z4SF mm spl bd4 bd3 bd2 bd1 ->
    evtF bsegs RNG Q (ZS AZ4_DEPI mm z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26
                         z27 z28 z29 z30 z31).

  Definition z4i1_goal (Q : machine_state -> Prop) : Prop :=
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4epi_hyp Q ->
    forall mm (l1 l2 l3 : Z) (w0 w1 w2 w3 w4 w5 w7 w8 w11 w12 : word) (j4 j3 j2 j1 : list byte)
           (x1 x5 x6 x7 x10 x12 x13 x14 x16 x17 x24 x27 x28 x29 x30 x31 : word),
    Z4SF mm (SPD w0 w1 w2 w3 w4 w5 (W (DST + dcap)) w7 w8 (W (DST + seg)) (W (DST + 2 * seg)) w11 w12 (W (DT + 4)) (W dcap))
      [CB 40 j4] [CB 40 j3] [CB 40 j2] [CB 40 j1] ->
    0 <= l1 < 65536 -> 0 <= l2 < 65536 -> 0 <= l3 < 65536 -> 6 + l1 + l2 + l3 <= n -> 6 <= dcap -> 10 <= n ->
    evtF bsegs RNG Q (ZS AZ4_I1 mm x1 x5 x6 x7 (W DST) (W (SS + 6 + l1 + l2)) x10 (W (SS + 6)) x12 x13 x14 (W l1) x16 x17
                         (W l3) (W l2) (W (SS + 6 + l1)) (W AZ4_SB) (W (6 + l1 + l2 + l3)) (W n) x24 (W (tl + 256 * mtl))
                         (W (DST + 3 * seg)) x27 x28 x29 x30 x31).
End Z4D.

Definition z4i1_stmtA : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  z4i1_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.

Definition z4d_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  AHEAP AI L RNG st LB m0 ->
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  1 <= mtl <= 12 -> tl <= mtl -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  x2_table_ok cells tl -> cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells) -> zlen cbs = 4 * 2^tl ->
  ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) -> 0 <= dcap < 2^32 ->
  Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 -> 16 <= SS ->
  (0 < zlen src -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + zlen src <= SBH) ->
  (DT + DTABLE_BYTES mtl <= SS \/ SS + zlen src <= DT) -> (DST + dcap <= SS \/ SS + zlen src <= DST) ->
  (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
  ATOP + 4096 <= lo -> lo <= bv_unsigned sp - Z4D_STACK -> bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP -> harness_invA m0 ->
  rclean m0 rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  z4d_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs.
End CANSEC1.
