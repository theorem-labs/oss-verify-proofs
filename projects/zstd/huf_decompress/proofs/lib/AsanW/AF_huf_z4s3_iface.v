(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4s3_iface () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition SPA (w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 : word) (j0 j1 : list byte) : list cell :=
  [CB 40 j0; C8 w40; CB 120 j1; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200;
   C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264;
   C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312].

(* [comment removed for export] *)
Definition BD4A (c b : word) (jp : list byte) (p s l : word) : list cell := [C8 c; C4 b; CB 4 jp; C8 p; C8 s; C8 l].

Lemma SPA_size : forall w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 j0 j1, cells_size (SPA w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 j0 j1) = 320%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s3_iface ()) [] "h02j0h12j1h24w168h34w176h44w184h54w192h64w200h74w208h84w216h94w224h:4w232h;4w240h<4w248h=4w256h>4w264h?4w272h@4w280hA4w288hB4w296hC4w304hD4w312hE3w40p;1p;2p-1p10000p4p710p8g000Gj12Tg000lj14Tg001Jj13Tg001mj15Tg002Mj26Tg002gj10Tf0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g003F#2#2#2R0#2#2#2#4#3R1%40#3#5R0g003kg004J#1#1#1#1#1#1#1#1#1#1'6X10W0XD1XC1XB1XA1X@1X?1X>1X=1X<1X;1X:1X91X81X71X61X51X41X31X21WEo"). Qed.
Lemma BD4A_size : forall c b jp p s l, cells_size (BD4A c b jp p s l) = 40%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4s3_iface ()) [] "h01bh11ch22jph31lh41ph51sp;1p;2g000Gj11Tg000lj14Tg001Jj13Tg001mj15Tg002Mj26Tg002gj10Tf0#0#0#0#0#0#0#0#0p=2g003F#1#1#1R0#1#1#1#4#3R1%40#3#5g003kg004J#2#2#2#2#2'6X31X51X41W2X01W1o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Z4SF.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition Z4SF (mm : amem) (spl bd4 : list cell) : Prop :=
    (exists buf, u8arr asegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at asegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at asegs mm (DT + 4) cbs
    /\ bytes_at asegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk asegs mm lo (SP + -576)
    /\ rw_cells asegs mm (SP + -576) spl /\ cells_size spl = 320%nat
    /\ rw_cells asegs mm (SP + -256) bd4 /\ cells_size bd4 = 40%nat
    /\ (exists jj, rw_cells asegs mm (SP + -216) [CB 112 jj])
    /\ rw_cells asegs mm (SP + -104) FRS
    /\ mem_inv asegs mm /\ munch DW m0 mm /\ wmono asegs m0 mm.

  (* [comment removed for export] *)
  Notation ZS pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SP + -576)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Z_to_bv 64 pc) fc None mm (seg_rom asegs)) (only parsing).

  (* [comment removed for export] *)
  Definition z4s31_goal (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (c : word) (y1 y6 y10 y13 y14 y15 y16 y18 y19 y22 : word)
           (w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w256 w264 w272 w280 w288 w296 : word) (j0 j1 : list byte)
           (bd4 : list cell)
           mm (x5 x7 x8 x11 x20 x21 x23 x25 x30 x31 : word),
    Z4SF mm (SPA w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 (Z_to_bv 64 (SS + O + 8)) w256 w264 w272 w280 w288 w296 c (Z_to_bv 64 (DT + 4)) j0 j1)
         bd4 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (z5 z7 z8 z9 z11 z12 z14 z16 z17 z21 z25 z26 z30 z31 z304 : word),
       Z4SF mm' (SPA w40 w168 y16 w184 w192 w200 w208 w216 w224 w232 w240 (Z_to_bv 64 (SS + O + 8)) w256 w264 w272 w280 w288 (Z_to_bv 64 tl) z304 (Z_to_bv 64 (DT + 4)) j0 j1)
            bd4 ->
       evtF asegs RNG POST (ZS 0x8a804 mm' y1 z5 y6 z7 z8 z9 y10 z11 z12 y13 z14 y15 z16 z17 y18 y19 y14 z21 y22 (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (tl + 256 * mtl)) z25 z26 (Z_to_bv 64 2147450880) w200 y6 z30 z31)) ->
    evtF asegs RNG POST (ZS 0x898c0 mm y1 x5 y6 x7 x8 (Z_to_bv 64 (b)) y10 x11 (Z_to_bv 64 (SS + O)) y13 y14 y15 y16 (Z_to_bv 64 (DST + Qe)) y18 y19 x20 x21 y22 x23 (Z_to_bv 64 (DST + q)) x25 (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 2147450880) w200 (Z_to_bv 64 (tl + 256 * mtl)) x30 x31).

  (* [comment removed for export] *)
  Definition z4s32_goal (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (c : word) (y9 y10 y12 y13 y18 y19 y23 : word)
           (w40 w168 w176 w184 w192 w200 w208 w224 w232 w240 w248 w264 w272 w280 w288 w304 : word) (j0 j1 : list byte)
           (bd4 : list cell)
           mm (x5 x7 x8 x11 x14 x16 x17 x21 x25 x26 x30 x31 : word),
    Z4SF mm (SPA w40 w168 w176 w184 w192 w200 w208 (Z_to_bv 64 (DST + Qe)) w224 w232 w240 w248 (Z_to_bv 64 (SS + O + 8)) w264 w272 w280 w288 (Z_to_bv 64 tl) w304 (Z_to_bv 64 (DT + 4)) j0 j1)
         bd4 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (z1 z5 z7 z8 z11 z14 z15 z16 z17 z25 z29 z30 z31 : word),
       Z4SF mm' (SPA w40 w168 w176 w184 w192 w200 w208 (Z_to_bv 64 (DST + Qe)) w224 w232 w240 w248 (Z_to_bv 64 (SS + O + 8)) w264 w272 w280 w288 (Z_to_bv 64 tl) w304 (Z_to_bv 64 (DT + 4)) j0 j1)
            bd4 ->
       evtF asegs RNG POST (ZS 0x8b714 mm' z1 z5 (Z_to_bv 64 tl) z7 z8 y9 y10 z11 y12 y13 z14 z15 z16 z17 y18 w224 (Z_to_bv 64 (SS + O)) y9 w240 y23 (Z_to_bv 64 (tl + 256 * mtl)) z25 y19 (Z_to_bv 64 2147450880) w200 z29 z30 z31)) ->
    evtF asegs RNG POST (ZS 0x8a804 mm (Z_to_bv 64 (b)) x5 c x7 x8 y9 y10 x11 y12 y13 x14 (Z_to_bv 64 (DST + q)) x16 x17 y18 y19 (Z_to_bv 64 (SS + O)) x21 (Z_to_bv 64 (SS + O + pt)) y23 (Z_to_bv 64 (tl + 256 * mtl)) x25 x26 (Z_to_bv 64 2147450880) w200 c x30 x31).

  (* [comment removed for export] *)
  Definition z4s33_goal (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (c : word) (y1 y9 y10 y12 y14 y20 y22 y23 : word)
           (w40 w168 w176 w184 w192 w208 w216 w224 w232 w240 w248 w256 w272 w280 w296 w304 : word) (j0 j1 : list byte)
           (bd4 : list cell)
           mm (x5 x7 x8 x11 x15 x16 x17 x25 x29 x30 x31 : word),
    Z4SF mm (SPA w40 w168 w176 w184 w192 (Z_to_bv 64 (DST + Qe)) w208 w216 w224 w232 w240 w248 w256 (Z_to_bv 64 (SS + O + 8)) w272 w280 (Z_to_bv 64 (SS + O + pt)) w296 w304 (Z_to_bv 64 (DT + 4)) j0 j1)
         bd4 ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (z5 z7 z8 z11 z13 z15 z16 z17 z18 z21 z26 z28 z29 z30 z31 z288 : word),
       Z4SF mm' (SPA w40 w168 w176 w184 w192 (Z_to_bv 64 (DST + Qe)) w208 w216 w224 w232 w240 w248 w256 (Z_to_bv 64 (SS + O + 8)) w272 w280 z288 w296 w304 (Z_to_bv 64 (DT + 4)) j0 j1)
            bd4 ->
       evtF asegs RNG POST (ZS 0x8c638 mm' y1 z5 (Z_to_bv 64 tl) z7 z8 y9 y10 z11 y12 z13 y14 z15 z16 z17 z18 (Z_to_bv 64 (SS + O)) y20 z21 y22 y23 (Z_to_bv 64 (tl + 256 * mtl)) w176 z26 (Z_to_bv 64 2147450880) z28 z29 z30 z31)) ->
    evtF asegs RNG POST (ZS 0x8b714 mm y1 x5 (Z_to_bv 64 tl) x7 x8 y9 y10 x11 y12 (Z_to_bv 64 (DST + q)) y14 x15 x16 x17 (Z_to_bv 64 (b)) (Z_to_bv 64 (SS + O)) y20 y9 y22 y23 (Z_to_bv 64 (tl + 256 * mtl)) x25 c (Z_to_bv 64 2147450880) (Z_to_bv 64 (DST + Qe)) x29 x30 x31).

  (* [comment removed for export] *)
  Definition z4s34_goal (O L Qe : Z) : Prop :=
    forall (q pt b : Z) (y1 y9 y12 y14 y15 y18 y19 y20 y23 : word)
           (w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 : word) (j0 j1 : list byte)
           (c : word) (jp : list byte)
           mm (x5 x7 x8 x11 x13 x16 x17 x21 x26 x28 x29 x30 x31 : word),
    Z4SF mm (SPA w40 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 (Z_to_bv 64 (DT + 4)) j0 j1)
         (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b < 2^31 ->
    (forall mm' (spl : list cell) (cx bx px sx lx : word) (jx : list byte) (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       Z4SF mm' spl (BD4A cx bx jx px sx lx) -> cells_size spl = 320%nat ->
       evtF asegs RNG POST (ZS 0x8d554 mm' z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)) ->
    evtF asegs RNG POST (ZS 0x8c638 mm y1 x5 (Z_to_bv 64 tl) x7 x8 y9 (Z_to_bv 64 (DST + q)) x11 y12 x13 y14 y15 x16 x17 y18 y19 y20 x21 (Z_to_bv 64 (DST + Qe - 7)) y23 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + Qe)) x26 (Z_to_bv 64 2147450880) x28 x29 x30 x31).

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
  /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned sp - HUF_DEC_STACK_A /\ bv_unsigned sp + 16 < al_top L
  /\ bv_unsigned sp mod 16 = 0 /\ tp = Z_to_bv 64 ATP /\ harness_invA m0
  /\ rclean m0 rstk /\ r_lo rstk <= lo /\ bv_unsigned sp <= r_hi rstk /\ ATOP <= r_rlo rstk /\ rrng RNG rstk
  /\ rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG.

(* [comment removed for export] *)
Definition z4s31_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s31_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs O Lk Qe.

Definition z4s32_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s32_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs O Lk Qe.

Definition z4s33_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s33_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs O Lk Qe.

Definition z4s34_stmtA : Prop :=
  forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region) (O Lk Qe : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  z4s34_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs O Lk Qe.

End CANSEC1.
