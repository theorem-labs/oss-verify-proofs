(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0, listing offset AF_sb_dec = 0x2e5c), segment B: the /10 digit
   loop, the min-digits pad and the emit loop, BASE + 0x2f80 (0x836f4) to BASE + 0x301c (0x83790), in the
   continuation-passing form sbd_at1 -> sbd_at2.  Segment A produces sbd_at1; segment C
   (lib/B/Prog/SbDecSegC.v) consumes sbd_at2 and ends in tsb_dec_post.
   The code of this segment, from the neutral listing:
   - 0x836f4..0x83734 the digit loop: a7 := s5, a6 := a0, a0 := a0 + 1, t0 := s9 + a6, the magic multiply
     (mul t1,s5,a4 with a4 = 1717986919, srli t2,t1,0x3f, srai t1,t1,0x22, addw s5,t1,t2 = s5 / 10), the
     remainder (mul t1,s5,a2 with a2 = 10, subw t1,a7,t1, addi t1,t1,48), sb t1,0(t0), addiw a1,a1,1,
     bltu a3,a7 (a3 = -20: the loop exit, s5 < 10) and bltu a6,a5 (a5 = 2: at most three digits);
   - 0x83734..0x8374c the pad: bgeu a1,s4 (s4 = md), beq s9,a0 (a0 = -1: the UBSan null check, never equal),
     sb a0,1(s9) with a0 = 48 and a0 := 2;
   - 0x8374c..0x8378c the emit loop: s4 := a0 - 1, s5 := -1, bltu s10,s4 (s10 = ~(s9): the UBSan
     pointer-overflow check, never taken), the shadow check of d[i] (srli/add/lb/bnez, then andi a2,a0,7 and
     blt a2,a1 at 0x83784), lbu a1,0(a0), mv a0,s3 and the call of sb_ch at 0x83774, addi s4,s4,-1,
     bne s4,s5 and j 0x83790.
   The segment calls sb_ch once per emitted digit (at most three times) and nothing else; it allocates no
   block and no frame, so the journal's state, world and event count do not change. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ IdentBProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC1g YC1h YC45 IdentBFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC81 YC4b.
(* the callee's contract and the function's own contract (statement file) *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
(* The plain model and its released Z-level lemmas (lib/Prog/sb_dec.v: sbd_q, sbd_r, sbd_lt10, ...) *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import sb_dec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- the machine arithmetic of the loop (section 4 of the lane's brief) ----------------------------
   The released Z-level facts are lib/Prog/sb_dec.v's sbd_q (the magic multiply) and sbd_r (the
   remainder); they are stated for the plain build's machine words.  The walk needs them in the engine's
   sv_denot / U form, one step at a time: the engine sees the 64-bit shift of the product (srai), the
   64-bit sign bit (srli) and the 64-bit difference (subw's argument), and folds the 32-bit wrap of the
   sum itself (addw) once the operands' ranges are known. *)
Lemma sbd_prod_range : forall x, 0 <= x < 2 ^ 31 -> 0 <= x * 1717986919 < 2 ^ 62.
Proof. intros x Hx. split; [lia|]. apply (Z.le_lt_trans _ ((2 ^ 31 - 1) * 1717986919)); [nia | lia]. Qed.
(* The quotient: the high 64-bit half of the magic multiply, shifted right by 34, is x / 10.  Derived from
   the released sbd_q (lib/Prog/sb_dec.v:33), whose statement adds the sign-bit term of the same product. *)
Lemma sbd_qdiv : forall x, 0 <= x < 2 ^ 31 -> Z.shiftr (x * 1717986919) 34 = x / 10.
Proof.
intros x Hx. pose proof (sbd_prod_range x Hx) as Hp.
pose proof (sbd_q x Hx) as Hq.
rewrite signed_lit, (zcanon_id (x * 1717986919)) in Hq by (unfold M64; lia).
rewrite (swrap64_id (x * 1717986919)) in Hq by (unfold half64; lia).
rewrite !Z.shiftr_div_pow2 in Hq by lia.
rewrite (Z.div_small (x * 1717986919) (2 ^ 63)) in Hq by lia.
rewrite Z.add_0_r in Hq.
assert (Hd : 0 <= x * 1717986919 / 2 ^ 34 < 2 ^ 28).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
rewrite (Z.mod_small (x * 1717986919 / 2 ^ 34) 18446744073709551616) in Hq by lia.
rewrite sbd_swrap in Hq by lia.
rewrite Z.shiftr_div_pow2 by lia. exact Hq.
Qed.
(* The sign bit of the same product is 0. *)
Lemma sbd_qsign : forall x, 0 <= x < 2 ^ 31 -> Z.shiftr (x * 1717986919) 63 = 0.
Proof.
intros x Hx. pose proof (sbd_prod_range x Hx) as Hp.
rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.
(* The remainder: x - 10 * (x / 10) = x mod 10 (lib/Prog/sb_dec.v:49 states the same step for the plain
   build's 32-bit wrap; the engine needs the 64-bit difference, which does not wrap). *)
Lemma sbd_rsub : forall x, 0 <= x -> x - x / 10 * 10 = x mod 10.
Proof. intros x Hx. pose proof (Z.div_mod x 10 ltac:(lia)). lia. Qed.
Lemma sbd_div10_range : forall x, 0 <= x < 2 ^ 31 -> 0 <= x / 10 <= 214748364.
Proof.
intros x Hx. split; [apply Z.div_pos; lia|].
assert (H : x / 10 < 214748365) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
(* ---- the two cut predicates ------------------------------------------------------------------------
   sbd_at2 is segment C's text (frozen): segment B proves it, segment C assumes it.
   sbd_at1 has the same parameter prefix and adds (s1v regs1 mem1 md1): s1v is sb_dec's realigned stack
   pointer (0x8360c andi sp,sp,-32), regs1 / mem1 / md1 the machine state at 0x836f4. *)
Definition sbd_at2 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b v md p cap n ov : Z)
  (fpos : Z) (S2 : astate) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  (* the caller's journal, sb_dec's frame owned *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mem2 md2 k /\
  frames S2 = (0, fpos) :: frames Sc /\ ablocks B lyc S2 = ablocks B lyc Sc /\
  (* sb_dec's entry: the return address and the stack window (tsb_dec_spec's premises) *)
  YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SB_DEC_STK /\ spZ regs <= sp0 /\
  (* the frame's last word holds the flag address (aj_stack_malloc_atS) *)
  rdword (aview SEGS (w_H W) mem2) (frame_addr lyc 0 fpos + 64 - 8) = Some (flag_addr lyc 0 fpos) /\
  (* the registers the release and the epilogue read, and the callee-saved registers they do not reload *)
  getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  getr regs2 8 = getr regs 2 /\
  getr regs2 18 = w64 (frame_addr lyc 0 fpos) /\ getr regs2 23 = w64 (frame_addr lyc 0 fpos) /\
  getr regs2 24 = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8) /\ getr regs2 27 = getr regs 27 /\
  (* the caller's ra, s0 .. s10, saved by the prologue at sp - 8 .. sp - 96 (sp = sb_dec's entry sp) *)
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) /\
  (* the struct sb and the digits, as tsb_dec_post states them *)
  tsb_dec_rec_at lyc b /\
  val_mem SEGS (mrestrict (w_H W) mem2) b 8 p /\
  val_mem SEGS (mrestrict (w_H W) mem2) (b + 8) 8 cap /\
  val_mem SEGS (mrestrict (w_H W) mem2) (b + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (b + 24) 4
    (if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else ov) /\
  garr8 SEGS (mrestrict (w_H W) mem2) (p + n)
    (firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md)) /\
  (0 < sb_dec_c.sb_dec_room cap n -> tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n)) /\
  (* what the call kept so far: tcj_kept with the frame's bytes and its shadow also excluded *)
  tcj_kept B SB_DEC_STK lyc Sc W memc W mem2 (spZ regs)
    (fun a => tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a \/ in_frames lyc [(0, fpos)] a).
(* The state at 0x836f4 (BASE + 0x2f80): segment A's exit, segment B's entry.  Everything but the last
   four clauses is carried unchanged to sbd_at2; the last four are what the loop reads and writes. *)
Definition sbd_at1 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b v md p cap n ov : Z)
  (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  (* the caller's journal, sb_dec's frame owned *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mem1 md1 k /\
  frames S2 = (0, fpos) :: frames Sc /\ ablocks B lyc S2 = ablocks B lyc Sc /\
  (* sb_dec's entry premises (tsb_dec_spec), carried *)
  YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SB_DEC_STK /\ spZ regs <= sp0 /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ 4096 <= raZ regs /\
  0 <= v < 2 ^ 31 /\ (md = 1 \/ md = 2) /\
  b mod 8 = 0 /\ 0 <= b /\ b + 28 <= 2 ^ 63 /\ (spZ regs <= b \/ b + 28 <= spZ regs - SB_DEC_STK) /\
  tsb_dec_rec_at lyc b /\
  0 <= p < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\ 0 <= n /\ n + 4 < 2 ^ 64 /\ 0 <= ov < 2 ^ 32 /\
  (* the realigned stack pointer of sb_dec (0x8360c andi sp,sp,-32) *)
  spZ regs - 144 <= s1v /\ s1v <= spZ regs - 128 /\ s1v mod 32 = 0 /\
  (* the frame's last word holds the flag address (aj_stack_malloc_atS) *)
  rdword (aview SEGS (w_H W) mem1) (frame_addr lyc 0 fpos + 64 - 8) = Some (flag_addr lyc 0 fpos) /\
  (* the registers at 0x836f4 *)
  getr regs1 2 = w64 s1v /\ getr regs1 3 = getr regs 3 /\
  getr regs1 4 = getr regs 4 /\ getr regs1 5 = w64 4 /\ getr regs1 8 = getr regs 2 /\
  getr regs1 9 = w64 s1v /\ getr regs1 10 = w64 0 /\ getr regs1 11 = w64 0 /\ getr regs1 12 = w64 10 /\
  getr regs1 13 = w64 (2 ^ 64 - 20) /\ getr regs1 14 = w64 1717986919 /\ getr regs1 15 = w64 2 /\
  getr regs1 18 = w64 (frame_addr lyc 0 fpos) /\ getr regs1 19 = w64 b /\ getr regs1 20 = w64 md /\
  getr regs1 21 = w64 v /\ getr regs1 22 = w64 SHADOW_OFF /\
  getr regs1 23 = w64 (frame_addr lyc 0 fpos) /\
  getr regs1 24 = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8) /\
  getr regs1 25 = w64 (frame_addr lyc 0 fpos + 32) /\
  getr regs1 26 = w64 (2 ^ 64 - (frame_addr lyc 0 fpos + 32) - 1) /\ getr regs1 27 = getr regs 27 /\
  (* the caller's ra, s0 .. s10, saved by the prologue at sp - 8 .. sp - 96 *)
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) /\
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) /\
  (* the frame's shadow at the digit slot: byte 4 of the frame's shadow is 04, so the four bytes
     [F + 32, F + 36) are addressable and the loop's shadow check (0x83758..0x83788) passes *)
  aview SEGS (w_H W) mem1 (SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4) = Some 4 /\
  (* the struct sb at mem1, as sb_dec's caller passed it *)
  val_mem SEGS (mrestrict (w_H W) mem1) b 8 p /\
  val_mem SEGS (mrestrict (w_H W) mem1) (b + 8) 8 cap /\
  val_mem SEGS (mrestrict (w_H W) mem1) (b + 16) 8 n /\
  val_mem SEGS (mrestrict (w_H W) mem1) (b + 24) 4 ov /\
  twr_ok B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W mem1 (spZ regs) (b + 16) 12 /\
  (* the buffer p[n ..], written through sb_ch when there is room *)
  (0 < sb_dec_c.sb_dec_room cap n ->
     0 < p /\ p + cap <= 2 ^ 63 /\
     tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     range_addressable (aview SEGS (w_H W) mem1) SHADOW_OFF (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     twr_ok B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W mem1 (spZ regs) (p + n)
       (sb_dec_c.sb_dec_acc v md cap n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= b \/ b + 28 <= p + n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= spZ regs - SB_DEC_STK \/ spZ regs <= p + n)) /\
  (* what segment A kept: only sb_dec's own stack window and its own frame changed *)
  tcj_kept B SB_DEC_STK lyc Sc W memc W mem1 (spZ regs) (fun a => in_frames lyc [(0, fpos)] a).
Definition sbd_segB_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word) (b v md p cap n ov : Z)
    (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1 (Q : world SEGS -> config -> Prop),
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regs2 : bvmap 5 word) mem2 md2,
     sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2f80) regs1 mem1 md1) Q.
(* The three parts of sbd_segB_spec, split on the value: v < 10 (one digit, this file's sbd_segB_lt10),
   10 <= v < 100 (two digits) and 100 <= v (three digits).  lib/B/Prog/SbDecWalk.v proves sbd_segB_spec
   from the three. *)
Definition sbd_segB_lt10_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word) (b v md p cap n ov : Z)
    (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1 (Q : world SEGS -> config -> Prop),
  v < 10 ->
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regs2 : bvmap 5 word) mem2 md2,
     sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2f80) regs1 mem1 md1) Q.
Definition sbd_segB_v10a_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word) (b v md p cap n ov : Z)
    (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1 (Q : world SEGS -> config -> Prop),
  10 <= v < 100 ->
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regs2 : bvmap 5 word) mem2 md2,
     sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2f80) regs1 mem1 md1) Q.
Definition sbd_segB_v10b_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word) (b v md p cap n ov : Z)
    (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1 (Q : world SEGS -> config -> Prop),
  100 <= v ->
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regs2 : bvmap 5 word) mem2 md2,
     sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2f80) regs1 mem1 md1) Q.
(* ---- the walk ---------------------------------------------------------------------------------- *)
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
(* the callee at BASE + AF_sb_ch (lib/B/Prog/sb_ch.v) and the program functions' starts *)
Hypothesis HSC : tsb_ch_spec B.
Hypothesis PSIG : identb_prog_sig_ok.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The symbolic state at 0x836f4.  Atoms 0..31 are the registers; the seven extra atoms are
   32 = v / 10, 33 = v / 100, 34 = v / 1000 (the quotients the loop computes), 35 = v mod 10,
   36 = v / 10 mod 10, 37 = v / 100 mod 10 (the digits it stores) and 38 = the shadow byte of the
   digit slot.  Registers t0, a0 .. a5 hold the constants segment A left in them, so the engine sees
   the multiplier 1717986919, the divisor 10 and the loop bounds as literals. *)
Definition sbd_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (5%bv : bv 5) (SLit 4)) (10%bv : bv 5) (SLit 0)) (11%bv : bv 5) (SLit 0)) (12%bv : bv 5) (SLit 10))
    (13%bv : bv 5) (SLit (-20))) (14%bv : bv 5) (SLit 1717986919)) (15%bv : bv 5) (SLit 2).
(* The four bytes of sb_dec's own frame the loop writes and reads back (d[0 .. 3] at F + 32), and the
   shadow byte that covers them (04: the first four bytes of the granule are addressable). *)
Definition sbd_rF : YP09.region := YP09.mkRegion (Some 25%nat) 0 4 0 4 [].
Definition sbd_rS : YP09.region :=
  YP09.mkRegion (Some 38%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 4))].
Definition sbd_rs : smem := [sbd_rF; sbd_rS].
Definition sbd_SH : list shent := [mkSHE 25 0 4].
Definition sbd_Bx : sv := SOff 22 0.
Definition sbd_extra (v F : Z) : list word :=
  map (Z_to_bv 64) [v / 10; v / 10 / 10; v / 10 / 10 / 10;
                    v mod 10; v / 10 mod 10; v / 10 / 10 mod 10; SHADOW_OFF + (F + 32) / 8].
Definition sbd_env (regs1 : bvmap 5 word) (v F : Z) : env := Eimg (Ereg regs1 (sbd_extra v F)).
Definition sbd_atoms : list (nat * afact) :=
  [(20%nat, mkAF 1 2 0); (21%nat, mkAF 0 2147483647 0); (22%nat, mkAF SB SB 0);
   (25%nat, mkAF 4096 (2 ^ 47 - 4) 3); (26%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0);
   (32%nat, mkAF 0 214748364 0); (33%nat, mkAF 0 21474836 0); (34%nat, mkAF 0 2147483 0);
   (35%nat, mkAF 0 9 0); (36%nat, mkAF 0 9 0); (37%nat, mkAF 0 9 0)].
(* What the engine cannot compute: the magic multiply's quotient and sign bit and the remainder, for
   each of the three turns of the loop, and the shadow address of the digit slot. *)
Definition sbd_mul (m : nat) : sv := SMd M_MUL (SOff m 0) (SLit 1717986919).
Definition sbd_alias : list (sv * sv) :=
  [ (SAlu ALU_SRL (sbd_mul 21) (SLit 63), SLit 0);
    (SAlu ALU_SRA (sbd_mul 21) (SLit 34), SOff 32 0);
    (SAlu ALU_SUB (SOff 21 0) (SMd M_MUL (SOff 32 0) (SLit 10)), SOff 35 0);
    (SAlu ALU_SRL (sbd_mul 32) (SLit 63), SLit 0);
    (SAlu ALU_SRA (sbd_mul 32) (SLit 34), SOff 33 0);
    (SAlu ALU_SUB (SOff 32 0) (SMd M_MUL (SOff 33 0) (SLit 10)), SOff 36 0);
    (SAlu ALU_SRL (sbd_mul 33) (SLit 63), SLit 0);
    (SAlu ALU_SRA (sbd_mul 33) (SLit 34), SOff 34 0);
    (SAlu ALU_SUB (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit 10)), SOff 37 0);
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 22 0), SOff 38 0) ].
(* The loop's exit test at 0x8372c (bltu a3,a7 with a3 = -20 and a7 = the turn's value - 10). *)
Definition sbd_lt (m : nat) : acond := mkAC BC_LTU (SLit (-20)) (SOff m (-10)).
Definition sbd_ge (m : nat) : acond := mkAC BC_GEU (SLit (-20)) (SOff m (-10)).
Definition sbd_ss (cnds : list acond) : sstate :=
  mkSS 0x2f80 sbd_sr sbd_rs None (mkFacts sbd_atoms cnds sbd_alias).
(* ---- the three facts the engine cannot compute, in its own form ---------------------------------- *)
Lemma sbd_u_atom : forall E (m : nat) x, ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff m 0) = x.
Proof.
intros E m x Hm Hx. rewrite U_SOff, Hm, unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id.
unfold M64. lia.
Qed.
Lemma sbd_u_mul : forall E (m : nat) x, ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 31 ->
  U E (sbd_mul m) = x * 1717986919.
Proof.
intros E m x Hm Hx. pose proof (sbd_prod_range x Hx) as Hp.
unfold sbd_mul. rewrite U_SMd. cbn [zmd_raw].
rewrite (sbd_u_atom E m x Hm ltac:(lia)), U_SLit, (zcanon_id 1717986919) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.
(* The quotient (srai by 34), the sign bit (srli by 63) and the remainder (subw) of one turn. *)
Lemma sbd_alias_step : forall E (m q d : nat) x,
  0 <= x < 2 ^ 31 -> ew E m = Z_to_bv 64 x -> ew E q = Z_to_bv 64 (x / 10) ->
  ew E d = Z_to_bv 64 (x mod 10) ->
  sv_denot E (SAlu ALU_SRL (sbd_mul m) (SLit 63)) = sv_denot E (SLit 0) /\
  sv_denot E (SAlu ALU_SRA (sbd_mul m) (SLit 34)) = sv_denot E (SOff q 0) /\
  sv_denot E (SAlu ALU_SUB (SOff m 0) (SMd M_MUL (SOff q 0) (SLit 10))) = sv_denot E (SOff d 0).
Proof.
intros E m q d x Hx Hm Hq Hd.
pose proof (sbd_prod_range x Hx) as Hp.
pose proof (sbd_div10_range x Hx) as Hqr.
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hdr.
pose proof (sbd_u_mul E m x Hm Hx) as HU.
split; [|split]; apply U_inj; rewrite U_SAlu; cbn [zalu_raw]; rewrite ?HU, ?U_SLit.
- change (Z.land (zcanon 63) 63) with 63. rewrite (sbd_qsign x Hx). reflexivity.
- change (Z.land (zcanon 34) 63) with 34.
  rewrite (swrap64_id (x * 1717986919)) by (unfold half64; lia).
  rewrite (sbd_qdiv x Hx), (sbd_u_atom E q (x / 10) Hq ltac:(lia)).
  apply zcanon_id. unfold M64. lia.
- rewrite (sbd_u_atom E m x Hm ltac:(lia)), (sbd_u_atom E d (x mod 10) Hd ltac:(lia)).
  rewrite U_SMd. cbn [zmd_raw].
  rewrite (sbd_u_atom E q (x / 10) Hq ltac:(lia)), U_SLit, (zcanon_id 10) by (unfold M64; lia).
  rewrite (zcanon_id (x / 10 * 10)) by (unfold M64; lia).
  rewrite (sbd_rsub x ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
(* The loop's exit test, from the released lib/Prog/sb_dec.v:sbd_lt10. *)
Lemma sbd_cond_lt : forall E (m : nat) x, 0 <= x < 2 ^ 31 -> ew E m = Z_to_bv 64 x -> x < 10 ->
  acond_ok E (sbd_lt m).
Proof.
intros E m x Hx Hm Hlt. unfold acond_ok, sbd_lt. cbn [ac_c ac_a ac_b branch_taken].
cbn [sv_denot]. rewrite Hm, unsigned_lit_small by lia.
rewrite (sbd_lt10 x Hx). apply Z.ltb_lt. exact Hlt.
Qed.
Lemma sbd_cond_ge : forall E (m : nat) x, 0 <= x < 2 ^ 31 -> ew E m = Z_to_bv 64 x -> 10 <= x ->
  acond_ok E (sbd_ge m).
Proof.
intros E m x Hx Hm Hge. unfold acond_ok, sbd_ge. cbn [ac_c ac_a ac_b branch_taken].
cbn [sv_denot]. rewrite Hm, unsigned_lit_small by lia.
rewrite (sbd_lt10 x Hx), (proj2 (Z.ltb_ge x 10) Hge). reflexivity.
Qed.
(* One byte of memory, from the state's view of it. *)
Lemma sbd_val_mem1 : forall (W : world SEGS) mem a v,
  aview SEGS (w_H W) mem a = Some v -> val_mem SEGS (mrestrict (w_H W) mem) a 1 v.
Proof.
intros W mem a v Hv kk Hk. assert (kk = 0)%nat by lia. subst kk.
destruct (aview_byte SEGS (w_H W) mem a v Hv) as (bb & Hbb & Hvv & Hr).
rewrite Z.add_0_r, Hbb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite !Z.mod_mod by lia. rewrite <- Hvv.
rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.
(* The symbolic state at 0x836f4 holds of the machine state sbd_at1 describes. *)
Lemma sbd_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
  (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1 cnds,
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  conds_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) cnds ->
  st_ok_pi SEGS VAL (sbd_env regs1 v (frame_addr lyc 0 fpos)) (sbd_ss cnds)
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + 0x2f80)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS sbd_Bx sbd_SH (sbd_env regs1 v (frame_addr lyc 0 fpos)) (mrestrict (w_H W) mem1).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 cnds
  HAT HC.
destruct HAT as (HJ & Hfrs & Habl & Hra & Hal16 & Hwlo & Hwhi & Hgp & Htp & Hra4 & Hv & Hmd &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov &
  Hs1lo & Hs1hi & Hs1al & Hflag &
  R2 & R3 & R4 & R5 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R18 & R19 & R20 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 &
  HSHB & VP & VCAP & VN & VOV & HWR & HROOM & HKEEP).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem1 md1 0 fpos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B lyc S2 W mem1 md1 0 fpos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS lyc S2 W mem1 md1 0 fpos HAR Hin) as (_ & _ & HFpres & HFSpres).
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
set (F := frame_addr lyc 0 fpos) in *.
(* the frame's digit slot and the shadow byte that covers it *)
assert (HFq : F mod 8 = 0) by (pose proof (Z.div_mod F 64 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia));
  rewrite HF64 in *; clear - HF64; apply Znumtheory.Zdivide_mod; apply (Z.divide_trans _ 64);
  [exists 8; reflexivity | apply Znumtheory.Zmod_divide; [lia | exact HF64]]).
assert (HD8 : (F + 32) / 8 = F / 8 + 4).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HFq, Z.add_0_r in D.
  rewrite D at 1. replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (HS8 : 0 <= (F + 32) / 8) by (apply Z.div_pos; lia).
assert (HS8h : (F + 32) / 8 <= F) by (apply Z.div_le_upper_bound; lia).
assert (HSHB' : aview SEGS (w_H W) mem1 (SHADOW_OFF + (F + 32) / 8) = Some 4)
  by (rewrite HD8, Z.add_assoc; exact HSHB).
(* the environment *)
set (E := sbd_env regs1 v F).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sbd_env; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs1 (sbd_extra v F)) i)
  by (intros i Hi; subst E; unfold sbd_env; apply Eimg_low; exact Hi).
assert (E20 : ew E 20 = w64 md)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = w64 (F + 32))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (2 ^ 64 - (F + 32) - 1))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 (v / 10))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (v / 10 / 10))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (v / 10 / 10 / 10))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (v mod 10))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (v / 10 mod 10))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (v / 10 / 10 mod 10))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (SHADOW_OFF + (F + 32) / 8))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
(* the quotients' ranges *)
pose proof (sbd_div10_range v ltac:(lia)) as Q1.
pose proof (sbd_div10_range (v / 10) ltac:(lia)) as Q2.
pose proof (sbd_div10_range (v / 10 / 10) ltac:(lia)) as Q3.
pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as M1.
pose proof (Z.mod_pos_bound (v / 10) 10 ltac:(lia)) as M2.
pose proof (Z.mod_pos_bound (v / 10 / 10) 10 ltac:(lia)) as M3.
assert (Q2' : 0 <= v / 10 / 10 <= 21474836)
  by (split; [lia|]; assert (v / 10 / 10 < 21474837) by (apply Z.div_lt_upper_bound; lia); lia).
assert (Q3' : 0 <= v / 10 / 10 / 10 <= 2147483)
  by (split; [lia|]; assert (v / 10 / 10 / 10 < 2147484) by (apply Z.div_lt_upper_bound; lia); lia).
(* the unsigned values of the atoms the state's facts speak about *)
assert (U20 : bv_unsigned (ew E 20) = md) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = v) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25) = F + 32) by (rewrite E25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = 2 ^ 64 - (F + 32) - 1)
  by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = v / 10) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = v / 10 / 10) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v / 10 / 10 / 10) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = v mod 10) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = v / 10 mod 10) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = v / 10 / 10 mod 10) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = SHADOW_OFF + (F + 32) / 8)
  by (rewrite E38; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx.
  (* the state with the engine's default registers, then the seven constants segment A left in place *)
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS 0x2f80 sr_atoms sbd_rs None (mkFacts sbd_atoms cnds sbd_alias))
    (mkst regs1 (Z_to_bv 64 (BASE + 0x2f80)) (mrestrict (w_H W) mem1) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. unfold sbd_env. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold sbd_rs, sbd_rF, sbd_rS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + 32 + o) ltac:(lia))).
      + rewrite U38. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (SHADOW_OFF + (F + 32) / 8) 0 1 (SLit 4) 4);
        [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (sbd_val_mem1 W mem1 _ 4 HSHB').
    - apply pairwise_disjoint_of_extents.
      unfold sbd_rs, sbd_rF, sbd_rS, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U25, U38. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as DF8.
      pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)) as MF8.
      repeat split; try exact I; unfold SHADOW_OFF; lia.
    - split; [|split].
      + unfold sbd_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U20, U21, U22, U25, U26, U32, U33, U34, U35, U36, U37.
        change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
        pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as DF8.
        assert (HA8 : (F + 32) mod 8 = 0) by (rewrite Zplus_mod, HFq; reflexivity).
        unfold SB, SHADOW_OFF in *.
        repeat match goal with |- _ /\ _ => split end; try exact I; lia.
      + cbn [f_conds]. exact HC.
      + cbn [f_alias]. unfold sbd_alias, alias_ok.
        destruct (sbd_alias_step E 21 32 35 v ltac:(lia) E21 E32 E35) as (A1 & A2 & A3).
        destruct (sbd_alias_step E 32 33 36 (v / 10) ltac:(lia) E32 E33 E36) as (A4 & A5 & A6).
        destruct (sbd_alias_step E 33 34 37 (v / 10 / 10) ltac:(lia) E33 E34 E37) as (A7 & A8 & A9).
        repeat match goal with |- _ /\ _ => split end; try exact I;
        try first [exact A1 | exact A2 | exact A3 | exact A4 | exact A5 | exact A6
                  | exact A7 | exact A8 | exact A9].
        exact (shadow_decl_ok E 25 22 38 (F + 32) SHADOW_OFF E25 ltac:(lia) E22 E38). }
  (* pin the seven constants *)
  unfold sbd_ss, sbd_sr.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (5%bv : bv 5) (SLit 4) HS0 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R5; reflexivity)) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SLit 0) HS1 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R10; reflexivity)) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (11%bv : bv 5) (SLit 0) HS2 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R11; reflexivity)) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (12%bv : bv 5) (SLit 10) HS3 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R12; reflexivity)) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (13%bv : bv 5) (SLit (-20)) HS4 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R13; unfold w64; apply Z_to_bv64_eq_mod;
          vm_compute; reflexivity)) as HS5.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (14%bv : bv 5) (SLit 1717986919) HS5
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R14; reflexivity)) as HS6.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (15%bv : bv 5) (SLit 2) HS6 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R15; reflexivity)) as HS7.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS7.
  exact HS7.
- (* the shadow entry: the four bytes [F + 32, F + 36) are addressable *)
  unfold sh_ok, sbd_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H W) mem1 E sbd_Bx 25 (F + 32) 4 (F + 32) 0 4).
  + apply (range_addressable_partial (aview SEGS (w_H W) mem1) SHADOW_OFF (F + 32) 4).
    * unfold shadow_of_addr. exact HSHB'.
    * rewrite Zplus_mod, HFq. reflexivity.
    * lia.
  + unfold sbd_Bx. rewrite U_SOff, U22, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  + rewrite U_SOff, U25, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
    pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as DF8.
    pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)) as MF8. lia.
Qed.
(* ---- what the segment keeps -------------------------------------------------------------------- *)
(* tcj_kept composes: the first five clauses chain, the last one speaks of the final state only. *)
Lemma sbd_kept_trans : forall STK' lyc0 Sc0 (W : world SEGS) m0 m1 m2 sp (E1 E2 : Z -> Prop),
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E1 -> tcj_kept B STK' lyc0 Sc0 W m1 W m2 sp E2 ->
  tcj_kept B STK' lyc0 Sc0 W m0 W m2 sp (fun a => E1 a \/ E2 a).
Proof.
intros STK' lyc0 Sc0 W m0 m1 m2 sp E1 E2 (A1 & A2 & A3 & A4 & A5 & _) (D1 & D2 & D3 & D4 & D5 & D6).
split; [intros a Ha Hw He; rewrite (D1 a Ha Hw ltac:(tauto)); exact (A1 a Ha Hw ltac:(tauto))|].
split; [intros bb m i Hin Hi He; rewrite (D2 bb m i Hin Hi ltac:(tauto)); exact (A2 bb m i Hin Hi ltac:(tauto))|].
split; [intros a Hi Hs He; rewrite (D3 a Hi Hs He); exact (A3 a Hi Hs He)|].
split; [intros cid pos a Hin Hr He; rewrite (D4 cid pos a Hin Hr ltac:(tauto));
        exact (A4 cid pos a Hin Hr ltac:(tauto))|].
split; [intros a Ha Hw Hp; exact (D5 a Ha Hw (A5 a Ha Hw Hp)) | exact D6].
Qed.
Lemma sbd_kept_mono : forall STK' lyc0 Sc0 (W : world SEGS) m0 m1 sp (E E' : Z -> Prop),
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E -> (forall a, E a -> E' a) ->
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E'.
Proof.
intros STK' lyc0 Sc0 W m0 m1 sp E E' (A1 & A2 & A3 & A4 & A5 & A6) HE.
split; [intros a Ha Hw He; apply A1; auto|].
split; [intros bb m i Hin Hi He; apply (A2 bb m i Hin Hi); auto|].
split; [exact A3|].
split; [intros cid pos a Hin Hr He; apply (A4 cid pos a Hin Hr); auto|].
split; [exact A5 | exact A6].
Qed.
(* A byte the current state keeps, read through a window the run did not touch. *)
Lemma sbd_aview_frame : forall (W : world SEGS) m0 m1 (P : Z -> Prop) a, 0 <= a < 2 ^ 64 -> ~ P a ->
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) m1 x = mrestrict (w_H W) m0 x) ->
  aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Proof.
intros W m0 m1 P a Ha HP HK. unfold aview, mbyte. rewrite HK; [reflexivity|].
rewrite unsigned_lit_small by lia. exact HP.
Qed.
(* The caller's struct sits in the machine stack, whose shadow the allocator keeps zero: its bytes are
   addressable in every state of the walk (re-derived from that state's AR, never carried over a call). *)
Lemma sbd_stk_shadow : forall ly1 S1 (W1 : world SEGS) m1 md1' q len,
  AR SEGS B ly1 S1 W1 m1 md1' -> ly_stk_lo ly1 <= q -> q + len <= ly_stk_hi ly1 -> 0 <= len ->
  range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF q len.
Proof.
intros ly1 S1 W1 m1 md1' q len HAR1 Hlo Hhi Hlen.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR1))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS ly1 S1 W1 m1 md1' (ly_stk_lo ly1, ly_stk_hi ly1 - ly_stk_lo ly1)
  HAR1 ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
assert (H8lo : ly_stk_lo ly1 mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_lo ly1) 4096 ltac:(lia)) as D. rewrite Hpal, Z.add_0_r in D.
  rewrite D. replace (4096 * (ly_stk_lo ly1 / 4096)) with ((512 * (ly_stk_lo ly1 / 4096)) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (H8hi : ly_stk_hi ly1 mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_hi ly1) 4096 ltac:(lia)) as D. rewrite Hpah, Z.add_0_r in D.
  rewrite D. replace (4096 * (ly_stk_hi ly1 / 4096)) with ((512 * (ly_stk_hi ly1 / 4096)) * 8) by lia.
  apply Z.mod_mul. lia. }
eapply (range_addressable_sub (aview SEGS (w_H W1) m1) SHADOW_OFF (ly_stk_lo ly1)
          (ly_stk_hi ly1 - ly_stk_lo ly1) q len);
  [ apply zero_shadow_range;
    [ exact H8lo
    | rewrite Zminus_mod, H8lo, H8hi; reflexivity
    | exact Hz ]
  | lia | lia ].
Qed.
(* A run of the segment keeps everything but sb_dec's own frame: its only write window is the digit slot. *)
Lemma sbd_kept_of_run : forall (W : world SEGS) E0 rs m0 m1 lyc0 Sc0 S20 md' (Ew : Z -> Prop) sp STK',
  AR SEGS B lyc0 S20 W m1 md' ->
  ablocks B lyc0 S20 = ablocks B lyc0 Sc0 ->
  (forall cid pos, In (cid, pos) (frames Sc0) -> In (cid, pos) (frames S20)) ->
  frame_of E0 rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall a, in_wrange E0 rs a -> Ew a) ->
  (forall a, in_img SEGS a -> ~ in_wrange E0 rs a) ->
  (forall a, sp - STK' <= a < sp -> apresent (w_H W) m1 a) ->
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp Ew.
Proof.
intros W E0 rs m0 m1 lyc0 Sc0 S20 md' Ew sp STK' HAR1 Hbl Hfr HFr HG Hsub Himg Hpres.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ Ew a ->
  aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a).
{ intros a Ha He. apply (sbd_aview_frame W m0 m1 (in_wrange E0 rs) a Ha);
  [intros Hw; exact (He (Hsub a Hw)) | exact HFr]. }
assert (KP : forall a, apresent (w_H W) m0 a -> apresent (w_H W) m1 a).
{ intros a (Hh & bb & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
  rewrite Hh, Hb in HG. destruct (m1 (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity]. }
split; [intros a Ha Hw He; apply KV; [lia | exact He]|].
split.
{ intros bb m i Hin Hi He. apply KV; [| exact He].
  pose proof (al_blocks _ _ LAWS lyc0 S20 W m1 md' bb m HAR1 ltac:(rewrite Hbl; exact Hin))
    as (_ & X1 & X2 & _). lia. }
split.
{ intros a Hi Hns He. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  apply (sbd_aview_frame W m0 m1 (in_wrange E0 rs) a ltac:(lia) (Himg a Hi) HFr). }
split.
{ intros cid pos a Hin Hr He.
  destruct (frame_zone SEGS B LAWS lyc0 S20 W m1 md' cid pos a HAR1 (Hfr cid pos Hin) Hr)
    as (Hz & [(Hr1 & Happ1) | Hr2]).
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ1. apply KV; [lia | exact He].
  - unfold kLowMemEnd, kHighShadowEnd in Hr2. apply KV; [lia | exact He]. }
split; [intros a Ha Hw Hp; exact (KP a Hp) | exact Hpres].
Qed.
(* Bytes a kept range keeps: in the machine stack (above the allocation ceiling, clause 1) and in the
   caller's buffer (a heap block or one of the caller's frames, clauses 2 and 4). *)
Lemma sbd_keep_val_mem : forall STK' lyc0 Sc0 (W : world SEGS) m0 m1 sp (E : Z -> Prop) a len val,
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E ->
  (forall i, 0 <= i < Z.of_nat len ->
     alloc_ceiling <= a + i < 2 ^ 64 /\ ~ (sp - STK' <= a + i < sp) /\ ~ E (a + i)) ->
  val_mem SEGS (mrestrict (w_H W) m0) a len val ->
  val_mem SEGS (mrestrict (w_H W) m1) a len val.
Proof.
intros STK' lyc0 Sc0 W m0 m1 sp E a len val (K1 & _) Hout Hv kk Hk.
rewrite <- (Hv kk Hk). apply (mbyte_of_aview SEGS (w_H W) (w_H W) m0 m1).
destruct (Hout (Z.of_nat kk) ltac:(lia)) as (H1 & H2 & H3). apply K1; assumption.
Qed.
Lemma sbd_keep_byte : forall STK' lyc0 Sc0 (W : world SEGS) m0 m1 sp (E : Z -> Prop) q len a,
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E -> tdst_ok B lyc0 Sc0 q len -> q <= a < q + len -> ~ E a ->
  aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Proof.
intros STK' lyc0 Sc0 W m0 m1 sp E q len a (_ & K2 & _ & K4 & _) HD Ha He.
destruct (HD a Ha) as [(bb & m & Hinb & Hr) | (cid & pos & Hinf & Hr)].
- replace a with (bb + (a - bb)) by lia. apply (K2 bb m (a - bb) Hinb); [lia|].
  replace (bb + (a - bb)) with a by lia. exact He.
- apply (K4 cid pos a Hinf); [left; exact Hr | exact He].
Qed.
Lemma sbd_keep_garr8 : forall STK' lyc0 Sc0 (W : world SEGS) m0 m1 sp (E : Z -> Prop) q len base l,
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E -> tdst_ok B lyc0 Sc0 q len ->
  q <= base -> base + Z.of_nat (length l) <= q + len ->
  (forall i, base <= i < base + Z.of_nat (length l) -> ~ E i) ->
  garr8 SEGS (mrestrict (w_H W) m0) base l ->
  garr8 SEGS (mrestrict (w_H W) m1) base l.
Proof.
intros STK' lyc0 Sc0 W m0 m1 sp E q len base l HK HD Hq1 Hq2 HE HG j Hj.
destruct (HG j Hj) as (HV & HR). split; [|exact HR].
intros kk Hkk. assert (kk = 0)%nat by (cbn in Hkk; lia). subst kk.
rewrite <- (HV 0%nat ltac:(lia)). apply (mbyte_of_aview SEGS (w_H W) (w_H W) m0 m1).
apply (sbd_keep_byte STK' lyc0 Sc0 W m0 m1 sp E q len (base + Z.of_nat j + Z.of_nat 0) HK HD);
  [lia | apply HE; lia].
Qed.
(* The caller's buffer lies in the same blocks and frames after sb_dec took its own frame. *)
Lemma sbd_tdst_S2 : forall lyc0 Sc0 S20 q len,
  ablocks B lyc0 S20 = ablocks B lyc0 Sc0 ->
  (forall cid pos, In (cid, pos) (frames Sc0) -> In (cid, pos) (frames S20)) ->
  tdst_ok B lyc0 Sc0 q len -> tdst_ok B lyc0 S20 q len.
Proof.
intros lyc0 Sc0 S20 q len Hbl Hfr HD a Ha.
destruct (HD a Ha) as [(bb & m & Hinb & Hr) | (cid & pos & Hinf & Hr)].
- left. exists bb, m. split; [rewrite Hbl; exact Hinb | exact Hr].
- right. exists cid, pos. split; [exact (Hfr cid pos Hinf) | exact Hr].
Qed.
(* The buffer's shadow in a later state: for a heap block from that state's allocator invariant, for a
   frame of the caller from what the call kept.  (Never carried across a call unproved.) *)
Lemma sbd_ra_keep : forall STK' lyc0 Sc0 S20 (W : world SEGS) m0 m1 md' sp (E : Z -> Prop) q len,
  AR SEGS B lyc0 S20 W m1 md' ->
  ablocks B lyc0 S20 = ablocks B lyc0 Sc0 ->
  (forall cid pos, In (cid, pos) (frames Sc0) -> In (cid, pos) (frames S20)) ->
  tcj_kept B STK' lyc0 Sc0 W m0 W m1 sp E ->
  tdst_ok B lyc0 Sc0 q len ->
  (forall x, q <= x < q + len -> ~ E (shadow_addr x)) ->
  range_addressable (aview SEGS (w_H W) m0) SHADOW_OFF q len ->
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF q len.
Proof.
intros STK' lyc0 Sc0 S20 W m0 m1 md' sp E q len HAR1 Hbl Hfr HK HD HnE HRA x Hx.
destruct HK as (_ & _ & _ & K4 & _).
destruct (HD x Hx) as [(bb & m & Hinb & Hr) | (cid & pos & Hinf & Hr)].
- apply (range_addressable_of_block SEGS B LAWS lyc0 S20 W m1 md' bb m x 1 HAR1
    ltac:(rewrite Hbl; exact Hinb) ltac:(lia) ltac:(lia)). lia.
- destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr. fold (shadow_addr x).
  apply (K4 cid pos (shadow_addr x) Hinf); [| exact (HnE x Hx)].
  right. unfold in_zr, frame_rng, shadow_addr in *. cbn [fst snd] in *.
  destruct (frame_al64 SEGS B lyc0 S20 W m1 md' cid pos HAR1 (Hfr cid pos Hinf)) as (HA1 & HA2 & HA3).
  pose proof (Z.div_mod (frame_addr lyc0 cid pos) 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod (frame_addr lyc0 cid pos) 64 ltac:(lia)) as D1b.
  pose proof (Z.mod_pos_bound (frame_addr lyc0 cid pos) 8 ltac:(lia)) as D1c.
  pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D2a.
  pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as D2b.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
  clear - HA1 HA2 HA3 D1 D1b D1c D2 D2a D2b D3 D4 Hr. lia.
Qed.
(* The frame's own words (the released-frame magic and the flag slot) survive a step that keeps them. *)
Lemma sbd_rdword_keep : forall (W : world SEGS) m0 m1 a w,
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W) m1 (a + i) = aview SEGS (w_H W) m0 (a + i)) ->
  rdword (aview SEGS (w_H W) m0) a = Some w -> rdword (aview SEGS (w_H W) m1) a = Some w.
Proof.
intros W m0 m1 a w HK Hw. unfold rdword in *.
pose proof (HK 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
rewrite K0, (HK 1 ltac:(lia)), (HK 2 ltac:(lia)), (HK 3 ltac:(lia)), (HK 4 ltac:(lia)),
        (HK 5 ltac:(lia)), (HK 6 ltac:(lia)), (HK 7 ltac:(lia)).
exact Hw.
Qed.
(* sb_dec's own frame and the caller's buffer are disjoint: the frame is not one of the caller's. *)
Lemma sbd_frame_buf_apart : forall lyc0 Sc0 S20 (W : world SEGS) m md' fpos0 q len a,
  AR SEGS B lyc0 S20 W m md' ->
  frames S20 = (0, fpos0) :: frames Sc0 ->
  ablocks B lyc0 S20 = ablocks B lyc0 Sc0 ->
  tdst_ok B lyc0 Sc0 q len -> q <= a < q + len ->
  ~ (frame_addr lyc0 0 fpos0 <= a < frame_addr lyc0 0 fpos0 + fs_frame_bytes 0).
Proof.
intros lyc0 Sc0 S20 W m md' fpos0 q len a HAR1 Hfrs0 Hbl HD Ha Hinf0.
assert (Hour : In (0, fpos0) (frames S20)) by (rewrite Hfrs0; left; reflexivity).
destruct (HD a Ha) as [(bb & m' & Hinb & Hr) | (cid & pos & Hinf & Hr)].
- pose proof (sep_block_frame SEGS B LAWS lyc0 S20 W m md' bb m' 0 fpos0 HAR1
    ltac:(rewrite Hbl; exact Hinb) Hour) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply in_split in Hinf as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS lyc0 S20 W m md' (0, fpos0) (cid, pos) [] l1 l2 HAR1
    ltac:(rewrite Hfrs0, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. lia.
Qed.
(* Where a byte of the caller's buffer lies, and that it is present, in any state that holds it. *)
Lemma sbd_dst_facts : forall lyc0 S20 (W : world SEGS) m md' q len a,
  AR SEGS B lyc0 S20 W m md' -> tdst_ok B lyc0 S20 q len -> q <= a < q + len ->
  4096 <= a < alloc_ceiling /\ apresent (w_H W) m a.
Proof.
intros lyc0 S20 W m md' q len a HAR1 HD Ha.
destruct (HD a Ha) as [(bb & mm & Hinb & Hr) | (cid & pos & Hinf & Hr)].
- destruct (al_blocks _ _ LAWS lyc0 S20 W m md' bb mm HAR1 Hinb) as (_ & H4 & Hce & _ & Hb & _).
  split; [lia | exact (proj1 (Hb a ltac:(lia)))].
- destruct (frames_bounds SEGS B LAWS lyc0 S20 W m md' cid pos HAR1 Hinf) as (Hf0 & Hfc & _).
  destruct (al_frames _ _ LAWS lyc0 S20 W m md' cid pos HAR1 Hinf) as (_ & _ & Hb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  split; [lia | exact (proj1 (Hb a ltac:(lia)))].
Qed.
(* What sb_ch kept, in sb_dec's own window and against the caller's state. *)
Lemma sbd_kept_of_call : forall (W : world SEGS) m0 m1 lyc0 Sc0 S20 (Ec : Z -> Prop) sp1 sp2 STK1 STK2,
  tcj_kept B STK1 lyc0 S20 W m0 W m1 sp1 Ec ->
  ablocks B lyc0 S20 = ablocks B lyc0 Sc0 ->
  (forall cid pos, In (cid, pos) (frames Sc0) -> In (cid, pos) (frames S20)) ->
  sp2 - STK2 <= sp1 - STK1 -> sp1 <= sp2 ->
  (forall a, sp2 - STK2 <= a < sp2 -> apresent (w_H W) m1 a) ->
  tcj_kept B STK2 lyc0 Sc0 W m0 W m1 sp2 Ec.
Proof.
intros W m0 m1 lyc0 Sc0 S20 Ec sp1 sp2 STK1 STK2 (A1 & A2 & A3 & A4 & A5 & _) Hbl Hfr Hlo Hhi Hpres.
split; [intros a Ha Hw He; apply A1; [exact Ha | lia | exact He]|].
split; [intros bb m i Hinb Hi He; apply (A2 bb m i); [rewrite Hbl; exact Hinb | exact Hi | exact He]|].
split; [exact A3|].
split; [intros cid pos a Hinf Hr He; apply (A4 cid pos a); [exact (Hfr cid pos Hinf) | exact Hr | exact He]|].
split; [intros a Ha Hw Hp; apply A5; [exact Ha | lia | exact Hp] | exact Hpres].
Qed.
(* A byte of the caller's buffer is app memory: it is never one of the shadow bytes. *)
Lemma sbd_dst_app : forall lyc0 S20 (W : world SEGS) m md' q len a,
  AR SEGS B lyc0 S20 W m md' -> tdst_ok B lyc0 S20 q len -> q <= a < q + len ->
  ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros lyc0 S20 W m md' q len a HAR1 HD Ha.
destruct (HD a Ha) as [(bb & mm & Hinb & Hr) | (cid & pos & Hinf & Hr)].
- destruct (al_blocks _ _ LAWS lyc0 S20 W m md' bb mm HAR1 Hinb) as (_ & _ & _ & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- destruct (frames_bounds SEGS B LAWS lyc0 S20 W m md' cid pos HAR1 Hinf) as (_ & _ & Happ).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
(* ---- the emit loop's bookkeeping ------------------------------------------------------------------
   After j of the emitted digits D, the struct holds nj = n + min(j, room) and over = 1 once a call found no
   room, and the buffer holds the first min(j, room) digits at p + n (template: the cold lane's sbc_post /
   sbc_tr_st / sbc_tr_ov in an unreleased draft sbdec_mid.v, here stated forward). *)
Definition sbd_inv (W : world SEGS) (m : word -> option byte) (b p cap n ov : Z) (D : list Z) (j : nat)
  (nj ovj : Z) : Prop :=
  nj = n + Z.min (Z.of_nat j) (sb_dec_c.sb_dec_room cap n) /\
  ovj = (if sb_dec_c.sb_dec_room cap n <? Z.of_nat j then 1 else ov) /\
  val_mem SEGS (mrestrict (w_H W) m) b 8 p /\
  val_mem SEGS (mrestrict (w_H W) m) (b + 8) 8 cap /\
  val_mem SEGS (mrestrict (w_H W) m) (b + 16) 8 nj /\
  val_mem SEGS (mrestrict (w_H W) m) (b + 24) 4 ovj /\
  garr8 SEGS (mrestrict (w_H W) m) (p + n)
    (firstn (Z.to_nat (Z.min (Z.of_nat j) (sb_dec_c.sb_dec_room cap n))) D).
Lemma sbd_room_nn : forall cap n, 0 <= sb_dec_c.sb_dec_room cap n.
Proof. intros cap n. unfold sb_dec_c.sb_dec_room. destruct (Z.leb_spec (n + 1) cap); lia. Qed.
Lemma sbd_garr8_snoc : forall m base l c,
  garr8 SEGS m base l -> garr8 SEGS m (base + Z.of_nat (length l)) [c] -> garr8 SEGS m base (l ++ [c]).
Proof.
intros m base l c H1 H2 j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hl | Hl].
- rewrite app_nth1 by lia. apply H1. lia.
- assert (j = length l) by lia. subst j. rewrite app_nth2, Nat.sub_diag by lia.
  destruct (H2 0%nat ltac:(cbn; lia)) as (HV & HR). rewrite Z.add_0_r in HV. split; [exact HV | exact HR].
Qed.
Lemma sbd_firstn_snoc : forall (D : list Z) j, (j < length D)%nat -> firstn (S j) D = firstn j D ++ [nth j D 0].
Proof.
induction D as [|x D IH]; intros j Hj; [cbn in Hj; lia|].
destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. cbn in Hj. lia.
Qed.
(* The invariant at the start of the emit loop. *)
Lemma sbd_inv_init : forall W m b p cap n ov D,
  val_mem SEGS (mrestrict (w_H W) m) b 8 p -> val_mem SEGS (mrestrict (w_H W) m) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) m) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) m) (b + 24) 4 ov ->
  sbd_inv W m b p cap n ov D 0 n ov.
Proof.
intros W m b p cap n ov D H1 H2 H3 H4. pose proof (sbd_room_nn cap n) as Hr.
unfold sbd_inv. change (Z.of_nat 0) with 0. rewrite Z.min_l by lia. rewrite Z.add_0_r.
replace (sb_dec_c.sb_dec_room cap n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
split; [reflexivity|]. split; [reflexivity|].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
unfold garr8. intros jj Hjj. rewrite length_firstn in Hjj. cbn in Hjj. lia.
Qed.
(* The invariant through a step that keeps the struct and the digits written so far. *)
Lemma sbd_inv_keep : forall STK' lyc0 Sc0 W m m' sp (E : Z -> Prop) b p cap n ov D j nj ovj,
  tcj_kept B STK' lyc0 Sc0 W m W m' sp E ->
  (forall i, 0 <= i < 28 ->
     alloc_ceiling <= b + i < 2 ^ 64 /\ ~ (sp - STK' <= b + i < sp) /\ ~ E (b + i)) ->
  (0 < sb_dec_c.sb_dec_room cap n ->
     tdst_ok B lyc0 Sc0 (p + n) (Z.min (Z.of_nat (length D)) (sb_dec_c.sb_dec_room cap n)) /\
     (forall a, p + n <= a < p + n + Z.min (Z.of_nat (length D)) (sb_dec_c.sb_dec_room cap n) -> ~ E a)) ->
  (j <= length D)%nat ->
  sbd_inv W m b p cap n ov D j nj ovj -> sbd_inv W m' b p cap n ov D j nj ovj.
Proof.
intros STK' lyc0 Sc0 W m m' sp E b p cap n ov D j nj ovj HK Hout Hbuf Hj (I1 & I2 & I3 & I4 & I5 & I6 & I7).
pose proof (sbd_room_nn cap n) as Hr.
split; [exact I1|]. split; [exact I2|].
split; [apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ b 8 p HK); [intros i Hi; apply Hout; lia | exact I3]|].
split; [apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (b + 8) 8 cap HK);
        [intros i Hi; replace (b + 8 + i) with (b + (8 + i)) by lia; apply Hout; lia | exact I4]|].
split; [apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (b + 16) 8 nj HK);
        [intros i Hi; replace (b + 16 + i) with (b + (16 + i)) by lia; apply Hout; lia | exact I5]|].
split; [apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (b + 24) 4 ovj HK);
        [intros i Hi; replace (b + 24 + i) with (b + (24 + i)) by lia; apply Hout; lia | exact I6]|].
set (w := Z.min (Z.of_nat j) (sb_dec_c.sb_dec_room cap n)) in *.
assert (Hlen : Z.of_nat (length (firstn (Z.to_nat w) D)) = w).
{ rewrite length_firstn. subst w. lia. }
destruct (Z.eq_dec w 0) as [Hw0 | Hw0].
- intros jj Hjj. rewrite length_firstn, Hw0 in Hjj. cbn in Hjj. lia.
- assert (Hpos : 0 < sb_dec_c.sb_dec_room cap n) by (subst w; lia).
  destruct (Hbuf Hpos) as (HD & HE).
  apply (sbd_keep_garr8 _ _ _ _ _ _ _ _ (p + n) (Z.min (Z.of_nat (length D)) (sb_dec_c.sb_dec_room cap n))
           (p + n) _ HK HD); [lia | rewrite Hlen; subst w; lia | | exact I7].
  intros a Ha. apply HE. rewrite Hlen in Ha. subst w. lia.
Qed.
(* The invariant through one call of sb_ch with the j-th digit (template: sbc_tr_st / sbc_tr_ov). *)
Lemma sbd_inv_call : forall STK' lyc0 Sc0 W m m' sp b p cap n ov D j nj ovj,
  tcj_kept B STK' lyc0 Sc0 W m W m' sp (tsb_ch_wr b p nj cap) ->
  (forall i, 0 <= i < 28 -> alloc_ceiling <= b + i < 2 ^ 64 /\ ~ (sp - STK' <= b + i < sp)) ->
  (0 < sb_dec_c.sb_dec_room cap n ->
     tdst_ok B lyc0 Sc0 (p + n) (Z.min (Z.of_nat (length D)) (sb_dec_c.sb_dec_room cap n)) /\
     (p + n + Z.min (Z.of_nat (length D)) (sb_dec_c.sb_dec_room cap n) <= b \/ b + 28 <= p + n)) ->
  0 <= n -> (j < length D)%nat ->
  sbd_inv W m b p cap n ov D j nj ovj ->
  val_mem SEGS (mrestrict (w_H W) m') b 8 p -> val_mem SEGS (mrestrict (w_H W) m') (b + 8) 8 cap ->
  (if nj + 1 <? cap
   then val_mem SEGS (mrestrict (w_H W) m') (b + 16) 8 (nj + 1) /\
        val_mem SEGS (mrestrict (w_H W) m') (b + 24) 4 ovj /\
        garr8 SEGS (mrestrict (w_H W) m') (p + nj) [nth j D 0]
   else val_mem SEGS (mrestrict (w_H W) m') (b + 16) 8 nj /\
        val_mem SEGS (mrestrict (w_H W) m') (b + 24) 4 1) ->
  sbd_inv W m' b p cap n ov D (S j) (if nj + 1 <? cap then nj + 1 else nj) (if nj + 1 <? cap then ovj else 1).
Proof.
intros STK' lyc0 Sc0 W m m' sp b p cap n ov D j nj ovj HK Hout Hbuf Hn Hj I Vp Vcap Hif.
unfold sbd_inv in *. destruct I as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
pose proof (sbd_room_nn cap n) as Hr.
set (room := sb_dec_c.sb_dec_room cap n) in *.
assert (Hroom : room = sb_dec_c.sb_dec_room cap n) by reflexivity.
clearbody room.
(* the digits written so far survive the call: it writes only b + 16 .. b + 28 and p + nj *)
assert (HG : garr8 SEGS (mrestrict (w_H W) m') (p + n) (firstn (Z.to_nat (Z.min (Z.of_nat j) room)) D)).
{ assert (Hlen : Z.of_nat (length (firstn (Z.to_nat (Z.min (Z.of_nat j) room)) D))
                 = Z.min (Z.of_nat j) room) by (rewrite length_firstn; lia).
  destruct (Z.eq_dec (Z.min (Z.of_nat j) room) 0) as [Hw0 | Hw0].
  - intros jj Hjj. rewrite length_firstn, Hw0 in Hjj. cbn in Hjj. lia.
  - assert (Hpos : 0 < room) by lia.
    destruct (Hbuf Hpos) as (HD & Hd).
    apply (sbd_keep_garr8 _ _ _ _ _ _ _ _ (p + n) (Z.min (Z.of_nat (length D)) room) (p + n) _ HK HD);
      [lia | rewrite Hlen; lia | | exact I7].
    intros a Ha [Hw | (Hlt & Hw)]; rewrite Hlen in Ha; lia. }
destruct (Z.ltb_spec (nj + 1) cap) as [Hlt | Hge].
- (* room: the call wrote the digit at p + nj *)
  destruct Hif as (Hn' & Hov' & Hc).
  assert (Hrm : room = cap - 1 - n).
  { rewrite Hroom. unfold sb_dec_c.sb_dec_room. destruct (Z.leb_spec (n + 1) cap); lia. }
  assert (Hjr : Z.of_nat j < room) by lia.
  rewrite Nat2Z.inj_succ.
  rewrite (Z.min_l (Z.succ (Z.of_nat j)) room) by lia.
  rewrite (Z.min_l (Z.of_nat j) room) in I1, HG by lia.
  split; [lia|].
  split.
  { replace (room <? Z.succ (Z.of_nat j)) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (room <? Z.of_nat j) with false in I2 by (symmetry; apply Z.ltb_ge; lia). exact I2. }
  split; [exact Vp|]. split; [exact Vcap|]. split; [exact Hn'|]. split; [exact Hov'|].
  rewrite Z2Nat.inj_succ by lia. rewrite Nat2Z.id in HG |- *.
  rewrite (sbd_firstn_snoc D j Hj).
  apply sbd_garr8_snoc; [exact HG|].
  rewrite length_firstn, Nat.min_l by lia. replace (p + n + Z.of_nat j) with (p + nj) by lia. exact Hc.
- (* no room: n stays and over becomes 1 *)
  destruct Hif as (Hn' & Hov').
  assert (Hrj : room <= Z.of_nat j).
  { rewrite Hroom in *. unfold sb_dec_c.sb_dec_room in *. destruct (Z.leb_spec (n + 1) cap); lia. }
  rewrite Nat2Z.inj_succ.
  rewrite (Z.min_r (Z.succ (Z.of_nat j)) room) by lia.
  rewrite (Z.min_r (Z.of_nat j) room) in I1, HG by lia.
  split; [lia|].
  split; [replace (room <? Z.succ (Z.of_nat j)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
  split; [exact Vp|]. split; [exact Vcap|]. split; [exact Hn'|]. split; [exact Hov'|].
  exact HG.
Qed.
(* The write right of the walk's own regions, and the side conditions of sbd_kept_of_run: the only
   window the segment's own code writes is the digit slot [F + 32, F + 36) of sb_dec's frame. *)
Ltac sbd_wrange Ha :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  destruct Ha as (r & Hr & Ha); vm_compute in Hr;
  destruct Hr as [Hr | [Hr | Hr]]; [ | | exfalso; exact Hr ];
  subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Ha end.
Ltac sbd_frame_pos fp :=
  exists 0, fp;
  split; first [ left; reflexivity
               | left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia ].
Ltac sbd_awr fp :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_wrange Ha; right; right; right; sbd_frame_pos fp.
(* the run's write window is the digit slot [F + 32, F + 36) *)
Ltac sbd_wr_slot :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_wrange Ha; lia.
(* the digit slot is in sb_dec's frame, which is not part of the image *)
Ltac sbd_wr_img Hfi0 :=
  let a := fresh "a" in let Hi := fresh "Hi" in let Ha := fresh "Ha" in
  let Hi2 := fresh "Hi2" in let Hfi := fresh "Hfi" in
  intros a Hi Ha; pose proof (pa_img_range a Hi) as Hi2; pose proof Hfi0 as Hfi;
  change (fs_frame_bytes 0) with 64 in Hfi; sbd_wrange Ha; lia.
(* the stack window of sb_dec is present in every state of its journal *)
Ltac sbd_pres_win HJx :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _);
  apply Hpr; lia.
(* ---- the emit loop, one turn at a time ------------------------------------------------------------
   The emit loop (0x83754 .. 0x8378c) runs once per digit and calls sb_ch each time.  It is walked once, as
   the lemma sbd_emit_loop below: its state at the loop head 0x83754 (BASE + 0x2fe0) is the machine-fact predicate
   sbd_lh (turn index i, digits already emitted j), and one turn is the symbolic state sbd_lss with the
   index i an atom.  Each path of the digit loop ends at the loop head and hands sbd_lh to sbd_emit_loop. *)
Lemma sbd_lsd_byte : forall k x, 0 <= x -> Forall (fun c => 48 <= c <= 57) (sb_dec_c.sb_dec_lsd x k).
Proof.
induction k as [|k IH]; intros x Hx; cbn [sb_dec_c.sb_dec_lsd]; [constructor|].
pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
constructor; [lia|]. destruct (x <? 10); [constructor | apply IH; apply Z.div_pos; lia].
Qed.
Lemma sbd_D_byte : forall x md t, 0 <= x -> 0 <= nth t (sb_dec_c.sb_dec_D x md) 0 < 256.
Proof.
intros x md t Hx.
assert (HF : Forall (fun c => 48 <= c <= 57) (sb_dec_c.sb_dec_D x md)).
{ unfold sb_dec_c.sb_dec_D. cbv zeta. apply Forall_rev.
  destruct (Z.of_nat (length (sb_dec_c.sb_dec_lsd x 3)) <? md).
  - apply Forall_app. split; [apply sbd_lsd_byte; exact Hx | constructor; [lia | constructor]].
  - apply sbd_lsd_byte. exact Hx. }
destruct (Nat.lt_ge_cases t (length (sb_dec_c.sb_dec_D x md))) as [Ht | Ht].
- rewrite Forall_forall in HF. pose proof (HF _ (nth_In _ 0 Ht)). lia.
- rewrite nth_overflow by exact Ht. lia.
Qed.
(* A byte a symbolic chunk holds, read through the state's view. *)
Lemma sbd_aview_chunk : forall (W : world SEGS) m E base off e x,
  YP09.chunk_ok SEGS E (mrestrict (w_H W) m) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 x -> 0 <= x < 256 ->
  aview SEGS (w_H W) m (base + off) = Some x.
Proof.
intros W m E base off e x Hc He Hx.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
rewrite Z.add_0_r in Hb2. unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite He. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
rewrite unsigned_lit_small by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* The symbolic state at the loop head.  Atoms 0..31 are the registers (s4 = 20 is the index i of the
   digit this turn emits, s5 = 21 is pinned to -1); the three extra atoms are 32 = F + 32 + i (the digit's
   address), 33 = the digit and 34 = the address of the shadow byte of the digit slot.  The two regions are
   that digit and that shadow byte (04: the four bytes [F + 32, F + 36) are addressable). *)
Definition sbd_lsr : list sv := sr_set sr_atoms (21%bv : bv 5) (SLit 18446744073709551615).
Definition sbd_lrD : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition sbd_lrS : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 4))].
Definition sbd_lrs : smem := [sbd_lrD; sbd_lrS].
Definition sbd_lSH : list shent := [mkSHE 32 0 1].
Definition sbd_latoms : list (nat * afact) :=
  [(20%nat, mkAF 0 2 0); (22%nat, mkAF SB SB 0);
   (25%nat, mkAF 4096 (2 ^ 47 - 4) 3); (26%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0);
   (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 0 255 0)].
(* a0 = s9 + s4 is the digit's address, its shadow address is a0 >> 3 + s6, and a0 & 7 is the index *)
Definition sbd_lalias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 25 0) (SOff 20 0), SOff 32 0);
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0), SOff 34 0);
    (SAlu ALU_AND (SOff 32 0) (SLit 7), SOff 20 0) ].
Definition sbd_lss : sstate := mkSS 0x2fe0 sbd_lsr sbd_lrs None (mkFacts sbd_latoms [] sbd_lalias).
Definition sbd_lenv (regsL : bvmap 5 word) (F : Z) (i : nat) (d : Z) : env :=
  Eimg (Ereg regsL (map (Z_to_bv 64) [F + 32 + Z.of_nat i; d; SHADOW_OFF + (F + 32 + Z.of_nat i) / 8])).
(* The symbolic state at the loop head holds of a machine state with these facts. *)
Lemma sbd_lentry : forall ly2 S20 (W : world SEGS) memL mdL fpos0 (regsL : bvmap 5 word) (i : nat) d,
  AR SEGS B ly2 S20 W memL mdL -> In (0, fpos0) (frames S20) ->
  (i < 3)%nat -> 0 <= d < 256 ->
  getr regsL 20 = w64 (Z.of_nat i) -> getr regsL 21 = w64 (2 ^ 64 - 1) -> getr regsL 22 = w64 SHADOW_OFF ->
  getr regsL 25 = w64 (frame_addr ly2 0 fpos0 + 32) ->
  getr regsL 26 = w64 (2 ^ 64 - (frame_addr ly2 0 fpos0 + 32) - 1) ->
  aview SEGS (w_H W) memL (frame_addr ly2 0 fpos0 + 32 + Z.of_nat i) = Some d ->
  aview SEGS (w_H W) memL (SHADOW_OFF + frame_addr ly2 0 fpos0 / 8 + 4) = Some 4 ->
  st_ok_pi SEGS VAL (sbd_lenv regsL (frame_addr ly2 0 fpos0) i d) sbd_lss
    (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + 0x2fe0)) memL (seg_rom SEGS)))
  /\ sh_ok SEGS sbd_Bx sbd_lSH (sbd_lenv regsL (frame_addr ly2 0 fpos0) i d) (mrestrict (w_H W) memL).
Proof.
intros ly2 S20 W memL mdL fpos0 regsL i d HAR Hin Hi Hd R20 R21 R22 R25 R26 HDG HSHB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly2 S20 W memL mdL 0 fpos0 HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B ly2 S20 W memL mdL 0 fpos0 HAR Hin) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
set (F := frame_addr ly2 0 fpos0) in *.
assert (HFq : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hi2 : 0 <= Z.of_nat i <= 2) by lia.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HFq, Z.add_0_r in DF.
assert (HD8 : (F + 32) / 8 = F / 8 + 4).
{ rewrite DF at 1. replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (HA8 : (F + 32 + Z.of_nat i) / 8 = F / 8 + 4).
{ rewrite DF at 1. replace (8 * (F / 8) + 32 + Z.of_nat i) with (Z.of_nat i + (F / 8 + 4) * 8) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small (Z.of_nat i) 8) by lia. lia. }
assert (HAm : Z.land (F + 32 + Z.of_nat i) 7 = Z.of_nat i).
{ change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  rewrite DF at 1. replace (8 * (F / 8) + 32 + Z.of_nat i) with (Z.of_nat i + (F / 8 + 4) * 8) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HSHB' : aview SEGS (w_H W) memL (SHADOW_OFF + (F + 32 + Z.of_nat i) / 8) = Some 4)
  by (rewrite HA8, Z.add_assoc; exact HSHB).
set (E := sbd_lenv regsL F i d).
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew E n = ew (Ereg regsL (map (Z_to_bv 64) [F + 32 + Z.of_nat i; d; SHADOW_OFF + (F + 32 + Z.of_nat i) / 8])) n)
  by (intros n Hn; subst E; unfold sbd_lenv; apply Eimg_low; exact Hn).
assert (E20 : ew E 20 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 20 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = w64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 22 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = w64 (F + 32))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (2 ^ 64 - (F + 32) - 1))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 32 + Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SHADOW_OFF + (F + 32 + Z.of_nat i) / 8))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (U20 : bv_unsigned (ew E 20) = Z.of_nat i) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25) = F + 32) by (rewrite E25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = 2 ^ 64 - (F + 32) - 1)
  by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = F + 32 + Z.of_nat i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = d) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = SHADOW_OFF + (F + 32 + Z.of_nat i) / 8)
  by (rewrite E34; apply unsigned_lit_small; rewrite HA8; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS 0x2fe0 sr_atoms sbd_lrs None (mkFacts sbd_latoms [] sbd_lalias))
    (mkst regsL (Z_to_bv 64 (BASE + 0x2fe0)) (mrestrict (w_H W) memL) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. unfold sbd_lenv. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold sbd_lrs, sbd_lrD, sbd_lrS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (F + 32 + Z.of_nat i) 0 1 (SOff 33 0) d);
        [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E33 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (sbd_val_mem1 W memL _ d HDG).
      + rewrite U34. split; [unfold SHADOW_OFF; lia|]. split; [rewrite HA8; unfold SHADOW_OFF; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (SHADOW_OFF + (F + 32 + Z.of_nat i) / 8) 0 1 (SLit 4) 4);
        [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (sbd_val_mem1 W memL _ 4 HSHB').
    - apply pairwise_disjoint_of_extents.
      unfold sbd_lrs, sbd_lrD, sbd_lrS, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U32, U34, HA8. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; try exact I; unfold SHADOW_OFF; lia.
    - split; [|split].
      + unfold sbd_latoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U20, U22, U25, U26, U32, U33.
        change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
        assert (HA8' : (F + 32) mod 8 = 0) by (rewrite Zplus_mod, HFq; reflexivity).
        unfold SB, SHADOW_OFF in *.
        repeat match goal with |- _ /\ _ => split end; try exact I; lia.
      + cbn [f_conds]. exact I.
      + cbn [f_alias]. unfold sbd_lalias, alias_ok.
        split; [|split; [|split; [|exact I]]].
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U25, U20, U32, !Z.add_0_r.
          rewrite (zcanon_id (F + 32)), (zcanon_id (Z.of_nat i)) by (unfold M64; lia). reflexivity.
        * exact (shadow_decl_ok E 32 22 34 (F + 32 + Z.of_nat i) SHADOW_OFF E32 ltac:(lia) E22 E34).
        * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U32, U_SLit, U20, !Z.add_0_r.
          rewrite (zcanon_id (F + 32 + Z.of_nat i)), (zcanon_id 7) by (unfold M64; lia).
          rewrite HAm. reflexivity. }
  unfold sbd_lss, sbd_lsr.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (21%bv : bv 5) (SLit 18446744073709551615) HS0
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R21; reflexivity)) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  exact HS1.
- unfold sh_ok, sbd_lSH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H W) memL E sbd_Bx 32 (F + 32) 4 (F + 32 + Z.of_nat i) 0 1).
  + apply (range_addressable_partial (aview SEGS (w_H W) memL) SHADOW_OFF (F + 32) 4).
    * unfold shadow_of_addr. rewrite HD8, Z.add_assoc. exact HSHB.
    * rewrite Zplus_mod, HFq. reflexivity.
    * lia.
  + unfold sbd_Bx. rewrite U_SOff, U22, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  + rewrite U_SOff, U32, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
(* The machine state at the loop head 0x83754 (BASE + 0x2fe0) before the turn that emits digit j of D:
   the turn's index i = length D - 1 - j in s4, the digits not yet emitted at F + 32 .. F + 32 + i, the rest
   of sb_dec's frame as segment A left it, the struct after j calls (sbd_inv), and what the segment kept. *)
Definition sbd_lh (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (k : Z)
  (regs : bvmap 5 word) (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z)
  (mem1 : word -> option byte) (i j : nat) (nj ovj : Z)
  (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  (i < 3)%nat /\ (j + i + 1 = length (sb_dec_c.sb_dec_D v md))%nat /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W memL mdL k /\
  getr regsL 2 = w64 s1v /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4 /\
  getr regsL 8 = getr regs 2 /\ getr regsL 18 = w64 (frame_addr lyc 0 fpos) /\ getr regsL 19 = w64 b /\
  getr regsL 20 = w64 (Z.of_nat i) /\ getr regsL 21 = w64 (2 ^ 64 - 1) /\ getr regsL 22 = w64 SHADOW_OFF /\
  getr regsL 23 = w64 (frame_addr lyc 0 fpos) /\
  getr regsL 24 = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8) /\
  getr regsL 25 = w64 (frame_addr lyc 0 fpos + 32) /\
  getr regsL 26 = w64 (2 ^ 64 - (frame_addr lyc 0 fpos + 32) - 1) /\ getr regsL 27 = getr regs 27 /\
  (forall t, (t <= i)%nat -> aview SEGS (w_H W) memL (frame_addr lyc 0 fpos + 32 + Z.of_nat t)
                            = Some (nth (j + (i - t)) (sb_dec_c.sb_dec_D v md) 0)) /\
  (forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 ->
     ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem1 a) /\
  aview SEGS (w_H W) memL (SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4) = Some 4 /\
  sbd_inv W memL b p cap n ov (sb_dec_c.sb_dec_D v md) j nj ovj /\
  tcj_kept B SB_CH_STK lyc Sc W mem1 W memL s1v
    (fun a => (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) \/
              tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a).
(* Where the caller's struct lies: in the machine stack, above the allocation ceiling. *)
Lemma sbd_b_range : forall STK sp0 FP ly S W0 mem0 md0 own lyc S2 (W : world SEGS) m md k b,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc S2 W m md k -> tsb_dec_rec_at lyc b ->
  alloc_ceiling <= b /\ b + 32 <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc S2 W m md k b HJ Hrec.
pose proof HJ as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & Hstkz & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
destruct Hrec as (Hrl0 & Hrh0). rewrite Elo in Hrl0. rewrite Ehi in Hrh0. split; lia.
Qed.
(* One call of sb_ch from sb_dec's frame, with its contract's premises re-derived in the call state. *)
Lemma sbd_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1
    (mi : word -> option byte) (mdi : Model) (regsC : bvmap 5 word) (retk c nj ovj : Z)
    (Qc : world SEGS -> config -> Prop),
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mi mdi k ->
  getr regsC 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsC 2 = w64 s1v -> getr regsC 3 = getr regs 3 -> getr regsC 4 = getr regs 4 ->
  getr regsC 10 = w64 b -> getr regsC 11 = w64 c -> 0 <= c < 256 ->
  val_mem SEGS (mrestrict (w_H W) mi) b 8 p -> val_mem SEGS (mrestrict (w_H W) mi) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) mi) (b + 16) 8 nj -> val_mem SEGS (mrestrict (w_H W) mi) (b + 24) 4 ovj ->
  0 <= nj -> nj + 1 < 2 ^ 64 -> 0 <= ovj < 2 ^ 32 ->
  twr_ok B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W mi s1v (b + 16) 12 ->
  (nj + 1 < cap -> 0 < p /\ p + cap <= 2 ^ 63 /\ tdst_ok B lyc S2 (p + nj) 1 /\
     range_addressable (aview SEGS (w_H W) mi) SHADOW_OFF (p + nj) 1 /\
     twr_ok B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W mi s1v (p + nj) 1 /\
     (p + nj + 1 <= b \/ b + 28 <= p + nj) /\ (p + nj + 1 <= s1v - SB_CH_STK \/ s1v <= p + nj)) ->
  (forall W2 c2, tsb_ch_post B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mi k regsC
                   b c p cap nj ovj W2 c2 -> SRr SEGS W2 c2 Qc) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_sb_ch) regsC mi mdi) Qc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1
  mi mdi regsC retk c nj ovj Qc HAT HJi Rra Hrk Hrk2 Rsp Rgp Rtp Ra0 Ra1 Hc
  Vp' Vcap' Vn' Vov' Hnj0 Hnj1 Hovj HWRi HROOMi HK.
destruct HAT as (_ & _ & _ & _ & _ & Hwlo & Hwhi & Hgp & Htp & _ & _ & _ &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov & Hs1lo & Hs1hi & Hs1al & _).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof (proj1 HJi) as HARi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstki & _).
pose proof Hstki as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct Hrec as (Hrlo & Hrhi).
assert (Qsp : spZ regsC = s1v) by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; lia).
eapply SRr_bind;
[ apply (HSC STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mi mdi k regsC b c p cap nj ovj HJi)
| intros W2 c2 _ HP; exact (HK W2 c2 HP) ].
- rewrite Rra. apply ret_ok_codeptr_v; lia.
- unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
- rewrite Rgp. exact Hgp.
- rewrite Rtp. exact Htp.
- rewrite Qsp. pose proof (Z.div_mod s1v 32 ltac:(lia)) as D. rewrite Hs1al, Z.add_0_r in D.
  rewrite D. replace (32 * (s1v / 32)) with ((2 * (s1v / 32)) * 16) by lia. apply Z.mod_mul. lia.
- rewrite Qsp. lia.
- rewrite Qsp. lia.
- exact Ra0.
- exact Ra1.
- exact Hc.
- exact Hb8.
- exact Hb0.
- exact Hb63.
- rewrite Qsp. lia.
- right. split; lia.
- exact Vp'.
- exact Vcap'.
- exact Vn'.
- exact Vov'.
- lia.
- lia.
- exact Hnj0.
- exact Hnj1.
- exact Hovj.
- exact (sbd_stk_shadow lyc S2 W mi mdi b 28 HARi ltac:(lia) ltac:(lia) ltac:(lia)).
- rewrite Qsp. exact HWRi.
- intros Hroom. destruct (HROOMi Hroom) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
  split; [rewrite Qsp; exact X5|]. split; [exact X6 | rewrite Qsp; exact X7].
Qed.
(* The call's premises on the struct and on the byte p[nj] it writes, in a state that kept everything but
   the digit slot and the segment's own writes since sb_dec's entry state mem1. *)
Lemma sbd_call_pre : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1
    m' md' (Ew : Z -> Prop) (j : nat) nj,
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W m' md' k ->
  tcj_kept B SB_CH_STK lyc Sc W mem1 W m' s1v Ew ->
  (forall a, Ew a -> (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) \/
                     tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a) ->
  nj = n + Z.min (Z.of_nat j) (sb_dec_c.sb_dec_room cap n) ->
  (j < length (sb_dec_c.sb_dec_D v md))%nat ->
  twr_ok B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W m' s1v (b + 16) 12 /\
  (nj + 1 < cap -> 0 < p /\ p + cap <= 2 ^ 63 /\ tdst_ok B lyc S2 (p + nj) 1 /\
     range_addressable (aview SEGS (w_H W) m') SHADOW_OFF (p + nj) 1 /\
     twr_ok B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W m' s1v (p + nj) 1 /\
     (p + nj + 1 <= b \/ b + 28 <= p + nj) /\ (p + nj + 1 <= s1v - SB_CH_STK \/ s1v <= p + nj)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1
  m' md' Ew j nj HAT HJ' K HEw Hnj Hj.
destruct HAT as (_ & Hfrs & Habl & _ & _ & Hwlo & Hwhi & _ & _ & _ & Hv & Hmd &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov & Hs1lo & Hs1hi & Hs1al & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & HWR & HROOM & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
pose proof (proj1 HJ') as HAR'.
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HSUBF : forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2))
  by (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0).
destruct (frames_bounds SEGS B LAWS lyc S2 W m' md' 0 fpos HAR' Hin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (sbd_room_nn cap n) as Hrnn.
pose proof (sbd_D_len v md ltac:(lia)) as HL.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (sbd_b_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ k b HJ' Hrec) as (Hblo & Hbhi).
split.
- intros a Ha. destruct (HWR a ltac:(lia)) as (Hw & Hpr & Hown & _).
  split; [exact Hw|]. split; [|split; [exact Hown | lia]].
  destruct K as (_ & _ & _ & _ & K5 & _). apply K5; [lia | lia | exact Hpr].
- intros Hlt.
  assert (Hroom : 0 < sb_dec_c.sb_dec_room cap n)
    by (unfold sb_dec_c.sb_dec_room in *; destruct (Z.leb_spec (n + 1) cap); lia).
  destruct (HROOM Hroom) as (Hp0 & Hpcap & HDST & HRAp & HWRp & Hpb & Hpsp).
  assert (Hrm : sb_dec_c.sb_dec_room cap n = cap - 1 - n)
    by (unfold sb_dec_c.sb_dec_room; destruct (Z.leb_spec (n + 1) cap); lia).
  assert (Hjr : Z.of_nat j < sb_dec_c.sb_dec_room cap n /\ nj = n + Z.of_nat j) by lia.
  assert (Hja : Z.of_nat j < sb_dec_c.sb_dec_acc v md cap n) by (unfold sb_dec_c.sb_dec_acc; lia).
  assert (HDST1 : tdst_ok B lyc Sc (p + nj) 1) by (intros a Ha; apply HDST; lia).
  assert (HDST2 : tdst_ok B lyc S2 (p + nj) 1) by exact (sbd_tdst_S2 lyc Sc S2 (p + nj) 1 Habl HSUBF HDST1).
  split; [exact Hp0|]. split; [exact Hpcap|]. split; [exact HDST2|].
  split.
  { apply (sbd_ra_keep SB_CH_STK lyc Sc S2 W mem1 m' md' s1v Ew (p + nj) 1 HAR' Habl HSUBF K HDST1).
    - intros x Hx Hbad.
      destruct (sbd_dst_facts lyc S2 W m' md' (p + nj) 1 x HAR' HDST2 Hx) as (Hx1 & _).
      pose proof (YCbq.shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as Hsb.
      unfold kLowMemEnd, kHighShadowEnd in Hsb.
      destruct (HEw _ Hbad) as [Hs | [Hb | Hbuf]].
      + unfold shadow_addr in Hs, Hsb. lia.
      + unfold shadow_addr in Hb, Hsb. lia.
      + apply (sbd_dst_app lyc S2 W m' md' (p + n) (sb_dec_c.sb_dec_acc v md cap n) (shadow_addr x) HAR'
                 (sbd_tdst_S2 lyc Sc S2 _ _ Habl HSUBF HDST) Hbuf).
        unfold kLowShadowBeg, kHighMemBeg, shadow_addr in *. lia.
    - intros a Ha. apply HRAp. lia. }
  split.
  { intros a Ha. destruct (HWRp a ltac:(lia)) as (Hw & Hpr & Hown & _).
    split; [exact Hw|]. split;
    [ exact (proj2 (sbd_dst_facts lyc S2 W m' md' (p + nj) 1 a HAR' HDST2 Ha))
    | split; [exact Hown | lia] ]. }
  split; lia.
Qed.
(* What a call of sb_ch keeps of sb_dec's own frame and of the frame's shadow: all of it (it writes only the
   struct's n / over and p[nj]). *)
Lemma sbd_call_frame : forall lyc Sc S2 (W : world SEGS) m mA md' fpos b p nj cap sp' STK',
  AR SEGS B lyc S2 W m md' -> frames S2 = (0, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  tcj_kept B STK' lyc S2 W m W mA sp' (tsb_ch_wr b p nj cap) ->
  alloc_ceiling <= b ->
  (nj + 1 < cap -> tdst_ok B lyc Sc (p + nj) 1) ->
  (forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 ->
     aview SEGS (w_H W) mA a = aview SEGS (w_H W) m a) /\
  aview SEGS (w_H W) mA (SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4)
    = aview SEGS (w_H W) m (SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4).
Proof.
intros lyc Sc S2 W m mA md' fpos b p nj cap sp' STK' HAR Hfrs Habl HK Hblo HDST.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HSUBF : forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2))
  by (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0).
destruct (frames_bounds SEGS B LAWS lyc S2 W m md' 0 fpos HAR Hin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct HK as (_ & _ & _ & KC4 & _).
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc 0 fpos) ltac:(unfold kHighMemEnd; lia)) as Hsb.
unfold kLowMemEnd, kHighShadowEnd, shadow_addr in Hsb.
split.
- intros a Ha. apply (KC4 0 fpos a Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia.
  + intros [Hw | (Hlt & Hw)]; [lia|].
    apply (sbd_frame_buf_apart lyc Sc S2 W m md' fpos (p + nj) 1 a HAR Hfrs Habl (HDST Hlt) ltac:(lia)).
    change (fs_frame_bytes 0) with 64. lia.
- apply (KC4 0 fpos _ Hin).
  + right. unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0) with 64.
    change (64 / 8) with 8. lia.
  + intros [Hw | (Hlt & Hw)]; [lia|].
    apply (sbd_dst_app lyc S2 W m md' (p + nj) 1 (p + nj) HAR (sbd_tdst_S2 lyc Sc S2 _ _ Habl HSUBF (HDST Hlt))
             ltac:(lia)).
    pose proof (Z.div_mod (frame_addr lyc 0 fpos) 8 ltac:(lia)) as DF8.
    pose proof (Z.mod_pos_bound (frame_addr lyc 0 fpos) 8 ltac:(lia)) as MF8.
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* The struct at the start of the emit loop: a state that kept everything but the digit slot. *)
Lemma sbd_inv0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1 m' md',
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W m' md' k ->
  tcj_kept B SB_CH_STK lyc Sc W mem1 W m' s1v
    (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
  sbd_inv W m' b p cap n ov (sb_dec_c.sb_dec_D v md) 0 n ov.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1
  m' md' HAT HJ' K.
destruct HAT as (_ & Hfrs & Habl & _ & _ & Hwlo & Hwhi & _ & _ & _ & Hv & Hmd &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov & Hs1lo & Hs1hi & Hs1al & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & VP & VCAP & VN & VOV & _ & _ & _).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
pose proof (proj1 HJ') as HAR'.
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W m' md' 0 fpos HAR' Hin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil.
destruct (sbd_b_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ k b HJ' Hrec) as (Hblo & Hbhi).
assert (HOUT : forall i, 0 <= i < 28 ->
  alloc_ceiling <= b + i < 2 ^ 64 /\ ~ (s1v - SB_CH_STK <= b + i < s1v) /\
  ~ (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) (b + i))
  by (intros i Hi; cbv beta; lia).
apply sbd_inv_init.
- apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ b 8 p K); [intros i Hi; apply HOUT; lia | exact VP].
- apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (b + 8) 8 cap K);
  [intros i Hi; replace (b + 8 + i) with (b + (8 + i)) by lia; apply HOUT; lia | exact VCAP].
- apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (b + 16) 8 n K);
  [intros i Hi; replace (b + 16 + i) with (b + (16 + i)) by lia; apply HOUT; lia | exact VN].
- apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (b + 24) 4 ov K);
  [intros i Hi; replace (b + 24 + i) with (b + (24 + i)) by lia; apply HOUT; lia | exact VOV].
Qed.
(* The exit state at 0x83790 (BASE + 0x301c) in sbd_at2's shape, once every digit is emitted. *)
Lemma sbd_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1
    (regs2 : bvmap 5 word) mem2 md2 nj ovj,
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mem2 md2 k ->
  getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 -> getr regs2 8 = getr regs 2 ->
  getr regs2 18 = w64 (frame_addr lyc 0 fpos) -> getr regs2 23 = w64 (frame_addr lyc 0 fpos) ->
  getr regs2 24 = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8) -> getr regs2 27 = getr regs 27 ->
  (forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 ->
     ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) ->
  sbd_inv W mem2 b p cap n ov (sb_dec_c.sb_dec_D v md) (length (sb_dec_c.sb_dec_D v md)) nj ovj ->
  tcj_kept B SB_CH_STK lyc Sc W mem1 W mem2 s1v
    (fun a => (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) \/
              tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a) ->
  sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1
  regs2 mem2 md2 nj ovj HAT HJ2 RF3 RF4 RF8 RF18 RF23 RF24 RF27 KF INV KFIN.
destruct HAT as (HJ & Hfrs & Habl & Hra & Hal16 & Hwlo & Hwhi & Hgp & Htp & Hra4 & Hv & Hmd &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov &
  Hs1lo & Hs1hi & Hs1al & Hflag &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 &
  _ & _ & _ & _ & _ & _ & HROOM & HKEEP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & Hstkz & Hceil & Hslo & Hshi & H47 & _).
destruct (sbd_b_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ k b HJ2 Hrec) as (Hblo & Hbhi).
pose proof (proj1 HJ2) as HAR2.
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
(* what the whole of sb_dec kept so far *)
eassert (KWIDE : tcj_kept B SB_DEC_STK lyc Sc W mem1 W mem2 (spZ regs) _);
[ eapply (sbd_kept_of_call W mem1 mem2 lyc Sc Sc _ s1v (spZ regs) SB_CH_STK SB_DEC_STK
            KFIN eq_refl ltac:(intros cid0 pos0 H0; exact H0) ltac:(lia) ltac:(lia));
  intros a0 Ha0; apply Hpr0; lia | ].
pose proof (sbd_kept_trans SB_DEC_STK lyc Sc W memc mem1 mem2 (spZ regs) _ _ HKEEP KWIDE) as KALL.
destruct INV as (N1 & O1 & VPF & VCAPF & VNF & VOVF & GARRF).
(* the frame's flag slot, which the segment never writes *)
assert (HflagF : rdword (aview SEGS (w_H W) mem2) (frame_addr lyc 0 fpos + 64 - 8)
                 = Some (flag_addr lyc 0 fpos)).
{ apply (sbd_rdword_keep W mem1 mem2 (frame_addr lyc 0 fpos + 64 - 8) (flag_addr lyc 0 fpos)
           ltac:(intros i Hi; apply KF; lia)). exact Hflag. }
(* the twelve words the prologue saved, which lie above sb_ch's window *)
assert (SAVEOUT : forall a, spZ regs - 96 <= a -> a + 8 <= spZ regs -> forall i, 0 <= i < 8 ->
  alloc_ceiling <= a + i < 2 ^ 64 /\ ~ (s1v - SB_CH_STK <= a + i < s1v) /\
  ~ ((fun a1 => (frame_addr lyc 0 fpos + 32 <= a1 < frame_addr lyc 0 fpos + 36) \/
                tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a1) (a + i))).
{ intros a Ha1 Ha2 i Hi. split; [lia|]. split; [lia|].
  cbv beta. intros [Hs | [Hb | Hbuf]]; [lia | lia |].
  assert (Hpos : 0 < sb_dec_c.sb_dec_room cap n).
  { destruct (Z.lt_ge_cases 0 (sb_dec_c.sb_dec_room cap n)) as [H|H]; [exact H|].
    exfalso. unfold sb_dec_c.sb_dec_acc in Hbuf. pose proof (sbd_room_nn cap n). lia. }
  destruct (HROOM Hpos) as (_ & _ & _ & _ & _ & _ & Hpsp). lia. }
assert (VF1 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 8) 8 _ KFIN); [ apply SAVEOUT; lia | exact V1 ]).
assert (VF8 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 16) 8 _ KFIN); [ apply SAVEOUT; lia | exact V8 ]).
assert (VF9 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 24) 8 _ KFIN); [ apply SAVEOUT; lia | exact V9 ]).
assert (VF18 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 32) 8 _ KFIN); [ apply SAVEOUT; lia | exact V18 ]).
assert (VF19 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 40) 8 _ KFIN); [ apply SAVEOUT; lia | exact V19 ]).
assert (VF20 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 48) 8 _ KFIN); [ apply SAVEOUT; lia | exact V20 ]).
assert (VF21 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 56) 8 _ KFIN); [ apply SAVEOUT; lia | exact V21 ]).
assert (VF22 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 64) 8 _ KFIN); [ apply SAVEOUT; lia | exact V22 ]).
assert (VF23 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 72) 8 _ KFIN); [ apply SAVEOUT; lia | exact V23 ]).
assert (VF24 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 80) 8 _ KFIN); [ apply SAVEOUT; lia | exact V24 ]).
assert (VF25 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 88) 8 _ KFIN); [ apply SAVEOUT; lia | exact V25 ]).
assert (VF26 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)))
  by (apply (sbd_keep_val_mem _ _ _ _ _ _ _ _ (spZ regs - 96) 8 _ KFIN); [ apply SAVEOUT; lia | exact V26 ]).
(* what the whole of sb_dec kept so far, in the shape tsb_dec_post wants *)
assert (KAT2 : tcj_kept B SB_DEC_STK lyc Sc W memc W mem2 (spZ regs)
  (fun a => tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a \/ in_frames lyc [(0, fpos)] a)).
{ apply (sbd_kept_mono _ _ _ _ _ _ _ _ _ KALL). intros a0 Ha0. cbv beta in Ha0 |- *.
  destruct Ha0 as [Hf | [Hs | Hw]].
  - right. exact Hf.
  - right. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia.
  - left. exact Hw. }
assert (HDSTF : 0 < sb_dec_c.sb_dec_room cap n ->
  tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n))
  by (intros Hpos; exact (proj1 (proj2 (proj2 (HROOM Hpos))))).
change (Z.min (Z.of_nat (length (sb_dec_c.sb_dec_D v md))) (sb_dec_c.sb_dec_room cap n))
  with (sb_dec_c.sb_dec_acc v md cap n) in N1, GARRF.
rewrite N1 in VNF. rewrite O1 in VOVF.
unfold sbd_at2.
repeat first [ exact HJ2 | assumption | match goal with |- _ /\ _ => split end ].
Qed.
(* The emit loop's test bne s4,s5 after addi s4,s4,-1 (s5 = -1): taken while the index was not 0. *)
Lemma sbd_bne : forall E x, bv_unsigned (ew E 20) = x -> 0 <= x <= 2 ->
  branch_taken BC_NE (sv_denot E (SOff 20 (-1))) (sv_denot E (SLit 18446744073709551615)) = negb (x =? 0).
Proof.
intros E x Hx Hr. rewrite branch_ne_U, U_SOff, U_SLit, Hx.
rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
destruct (Z.eqb_spec x 0) as [H0 | H0].
- rewrite H0. reflexivity.
- rewrite (zcanon_id (x + -1)) by (unfold M64; lia).
  replace (x + -1 =? 18446744073709551615) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
(* The variants of the run tactics' side goals for a run that writes nothing outside its regions'
   (empty) windows; each lia sees only the window hypothesis. *)
Ltac sbd_nowr :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_wrange Ha; exfalso; clear - Ha; lia.
Ltac sbd_kv HFr :=
  lazymatch type of HFr with
  | frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
    intros a Ha; apply (sbd_aview_frame _ m0 m1 (in_wrange E0 rs) a Ha);
    [ intros Hw; sbd_wrange Hw; clear - Hw; lia | exact HFr ]
  end.
Ltac sbd_kv0 HFr :=
  lazymatch type of HFr with
  | frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) =>
    let a := fresh "a" in let Ha := fresh "Ha" in let r0 := fresh "r0" in let Hr0 := fresh "Hr0" in
    intros a Ha; apply (sbd_aview_frame _ m0 m1 (in_wrange E0 rs) a Ha);
    [ intros (r0 & Hr0 & _); exact Hr0 | exact HFr ]
  end.
Ltac sbd_kvs HFr :=
  lazymatch type of HFr with
  | frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in let Hw := fresh "Hw" in
    intros a Ha Hn; apply (sbd_aview_frame _ m0 m1 (in_wrange E0 rs) a Ha);
    [ intros Hw; sbd_wrange Hw; apply Hn; clear - Hw; lia | exact HFr ]
  end.
Ltac sbd_lew R n r :=
  unfold sbd_lenv; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ n r eq_refl); exact R.
(* One turn of the emit loop: the call of sb_ch for digit j, then back to the loop head for digit j + 1, or,
   after the last digit, on to 0x83790. *)
Lemma sbd_emit_turn : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1
    (Q : world SEGS -> config -> Prop),
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regs2 : bvmap 5 word) mem2 md2,
     sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2) Q) ->
  forall i : nat,
  (forall i', (i' < i)%nat -> forall (j : nat) nj ovj (regsL : bvmap 5 word) memL mdL,
     sbd_lh STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs b v md p cap n ov fpos S2 s1v mem1 i' j nj ovj
       regsL memL mdL ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) regsL memL mdL) Q) ->
  forall (j : nat) nj ovj (regsL : bvmap 5 word) memL mdL,
  sbd_lh STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs b v md p cap n ov fpos S2 s1v mem1 i j nj ovj
    regsL memL mdL ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) regsL memL mdL) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 Q
  HAT HQ i IH j nj ovj regsL memL mdL HL.
pose proof HAT as HAT0.
destruct HAT0 as (_ & Hfrs & Habl & _ & _ & Hwlo & Hwhi & _ & _ & _ & Hv & Hmd &
  _ & _ & _ & Hbwin & Hrec & _ & _ & Hn0 & Hn1 & Hov & Hs1lo & Hs1hi & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & HROOM & _).
destruct HL as (Hi3 & Hj & HJL & L2 & L3 & L4 & L8 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 &
  L27 & HDIG & HFRM & HSHL & INV & KL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HSUBF : forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2))
  by (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0).
destruct (sbd_b_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ k b HJL Hrec) as (Hblo & Hbhi).
pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & Hstkz & Hceil & Hslo & Hshi & H47 & _).
pose proof (sbd_room_nn cap n) as Hrnn.
pose proof (sbd_D_len v md ltac:(lia)) as HLD.
assert (HWIN : forall a, s1v - SB_CH_STK <= a < s1v -> sp0 - STK <= a < sp0) by (intros a Ha; lia).
assert (Hs1r : 0 <= s1v < 2 ^ 47) by lia.
(* the struct's counters after j calls *)
pose proof INV as (I1 & I2 & _).
assert (Hj3 : (j < length (sb_dec_c.sb_dec_D v md))%nat) by lia.
assert (Hnj0 : 0 <= nj) by lia.
assert (Hnj1 : nj + 1 < 2 ^ 64) by lia.
assert (Hovj : 0 <= ovj < 2 ^ 32) by (rewrite I2; destruct (_ <? _); lia).
assert (HNJW : nj + 1 < cap ->
  p + n <= p + nj < p + n + sb_dec_c.sb_dec_acc v md cap n /\ nj = n + Z.of_nat j).
{ intros Hlt. unfold sb_dec_c.sb_dec_acc.
  assert (Hrm : sb_dec_c.sb_dec_room cap n = cap - 1 - n)
    by (unfold sb_dec_c.sb_dec_room; destruct (Z.leb_spec (n + 1) cap); lia).
  lia. }
assert (HNJD : nj + 1 < cap -> tdst_ok B lyc Sc (p + nj) 1).
{ intros Hlt. destruct (HNJW Hlt) as (Hw & _).
  assert (Hpos : 0 < sb_dec_c.sb_dec_room cap n) by (unfold sb_dec_c.sb_dec_acc in Hw; lia).
  destruct (HROOM Hpos) as (_ & _ & HDST & _). intros a Ha. apply HDST. lia. }
assert (HBUF : 0 < sb_dec_c.sb_dec_room cap n ->
  tdst_ok B lyc Sc (p + n) (Z.min (Z.of_nat (length (sb_dec_c.sb_dec_D v md))) (sb_dec_c.sb_dec_room cap n)) /\
  (p + n + Z.min (Z.of_nat (length (sb_dec_c.sb_dec_D v md))) (sb_dec_c.sb_dec_room cap n) <= b \/
   b + 28 <= p + n)).
{ intros Hpos. destruct (HROOM Hpos) as (_ & _ & HD0 & _ & _ & Hpb & _).
  unfold sb_dec_c.sb_dec_acc in HD0, Hpb. split; [exact HD0 | exact Hpb]. }
assert (HOUTB : forall t, 0 <= t < 28 ->
  alloc_ceiling <= b + t < 2 ^ 64 /\ ~ (s1v - SB_CH_STK <= b + t < s1v)) by (intros t Ht; lia).
destruct (frames_bounds SEGS B LAWS lyc S2 W memL mdL 0 fpos (proj1 HJL) Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in HFceil.
assert (HFR : forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; lia).
assert (HSHR : 0 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < 2 ^ 64).
{ pose proof (Z.div_pos (frame_addr lyc 0 fpos) 8 ltac:(lia) ltac:(lia)).
  assert (frame_addr lyc 0 fpos / 8 <= frame_addr lyc 0 fpos) by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF; lia. }
(* the digit this turn emits, and the symbolic state at the loop head *)
set (c := nth j (sb_dec_c.sb_dec_D v md) 0).
pose proof (HDIG i (le_n i)) as HD0. rewrite Nat.sub_diag, Nat.add_0_r in HD0. fold c in HD0.
assert (Hc256 : 0 <= c < 256) by (apply sbd_D_byte; lia).
destruct (sbd_lentry lyc S2 W memL mdL fpos regsL i c (proj1 HJL) Hin Hi3 Hc256 L20 L21 L22 L25 L26 HD0 HSHL)
  as [HS SHOK].
assert (EE2 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 2 = w64 s1v) by sbd_lew L2 2%nat (2%bv : bv 5).
assert (EE3 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 3 = getr regs 3) by sbd_lew L3 3%nat (3%bv : bv 5).
assert (EE4 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 4 = getr regs 4) by sbd_lew L4 4%nat (4%bv : bv 5).
assert (EE8 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 8 = getr regs 2) by sbd_lew L8 8%nat (8%bv : bv 5).
assert (EE18 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 18 = w64 (frame_addr lyc 0 fpos))
  by sbd_lew L18 18%nat (18%bv : bv 5).
assert (EE19 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 19 = w64 b) by sbd_lew L19 19%nat (19%bv : bv 5).
assert (EE20 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 20 = w64 (Z.of_nat i)) by sbd_lew L20 20%nat (20%bv : bv 5).
assert (EE21 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 21 = w64 (2 ^ 64 - 1)) by sbd_lew L21 21%nat (21%bv : bv 5).
assert (EE22 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 22 = w64 SHADOW_OFF) by sbd_lew L22 22%nat (22%bv : bv 5).
assert (EE23 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 23 = w64 (frame_addr lyc 0 fpos))
  by sbd_lew L23 23%nat (23%bv : bv 5).
assert (EE24 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 24 = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8))
  by sbd_lew L24 24%nat (24%bv : bv 5).
assert (EE25 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 25 = w64 (frame_addr lyc 0 fpos + 32))
  by sbd_lew L25 25%nat (25%bv : bv 5).
assert (EE26 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 26
               = w64 (2 ^ 64 - (frame_addr lyc 0 fpos + 32) - 1)) by sbd_lew L26 26%nat (26%bv : bv 5).
assert (EE27 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 27 = getr regs 27) by sbd_lew L27 27%nat (27%bv : bv 5).
assert (EE33 : ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 33 = Z_to_bv 64 c)
  by (unfold sbd_lenv; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (U20 : bv_unsigned (ew (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) 20) = Z.of_nat i)
  by (rewrite EE20; apply unsigned_lit_small; lia).
remember (sbd_lenv regsL (frame_addr lyc 0 fpos) i c) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sbd_lenv; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + 0x2fe0)) with (Z_to_bv 64 (BASE + 0x2fe0)).
change memL with (ms_mem (mkst regsL (Z_to_bv 64 (BASE + 0x2fe0)) memL (seg_rom SEGS))) in HJL.
(* the run from the loop head to the call of sb_ch at 0x83774: the shadow check passes, nothing is written *)
paj_run_tok RUN HS HJL SHOK Bspan; [sbd_nowr | ].
rename ms into msC. rename HFr into HFrC. rename HG into HGC. clear HF.
assert (KVC : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) memL a)
  by sbd_kv HFrC.
assert (KR : tcj_kept B SB_CH_STK lyc Sc W memL W (ms_mem msC) s1v (fun _ => False)).
{ eapply (sbd_kept_of_run W _ _ memL (ms_mem msC) lyc Sc S2 _ _ s1v SB_CH_STK);
  [ exact (proj1 HJL) | exact Habl | exact HSUBF | exact HFrC | exact HGC
  | intros a Ha; sbd_wrange Ha; clear - Ha; lia
  | intros a Hi Ha; sbd_wrange Ha; clear - Ha; lia
  | intros a Ha; pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _);
    apply Hpr; apply HWIN; exact Ha ]. }
pose proof (sbd_inv_keep SB_CH_STK lyc Sc W memL (ms_mem msC) s1v (fun _ => False) b p cap n ov
  (sb_dec_c.sb_dec_D v md) j nj ovj KR
  ltac:(intros t Ht; destruct (HOUTB t Ht) as (X1 & X2); split; [exact X1 | split; [exact X2 | intros X3; exact X3]])
  ltac:(intros Hpos; split; [exact (proj1 (HBUF Hpos)) | intros a Ha X; exact X])
  ltac:(clear - Hj3; lia) INV) as INVC.
pose proof INVC as (_ & _ & VP2 & VCAP2 & VN2 & VOV2 & _).
pose proof (sbd_kept_trans SB_CH_STK lyc Sc W mem1 memL (ms_mem msC) s1v _ _ KL KR) as K1C.
destruct (sbd_call_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
  regs1 mem1 md1 (ms_mem msC) _ _ j nj HAT HJL K1C ltac:(intros a [Ha | []]; exact Ha) I1 Hj3)
  as (HWR2 & HROOM2).
(* the call *)
pmkst HS.
rewrite (PSIG IB_sb_ch AF_sb_ch eq_refl).
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp;
prreg HS (4%bv : bv 5) Rtp; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Qg =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_sb_ch) rg mm mdx) Qg) end.
eapply (sbd_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1
          (ms_mem msC) _ (ms_regs msC) 12292 c nj ovj _ HAT HJL);
  [ exact Rra | clear; lia | reflexivity
  | rewrite Rsp, EE2; reflexivity | rewrite Rgp, EE3; reflexivity | rewrite Rtp, EE4; reflexivity
  | rewrite Ra0, EE19; reflexivity | rewrite Ra1, EE33; reflexivity
  | exact Hc256 | exact VP2 | exact VCAP2 | exact VN2 | exact VOV2
  | exact Hnj0 | exact Hnj1 | exact Hovj | exact HWR2 | exact HROOM2 | ].
(* ---- after the call: the state at the return point 0x83778 ---- *)
intros W2 c2 HP.
destruct HP as (HW2 & regsA & memA & mdA & Hc2 & HJA & HPA & HtcjA & VpA & VcapA & Hif).
replace (k + EV_SB_CH) with k in HJA by (unfold EV_SB_CH; clear; lia).
subst W2; rewrite Hc2; rewrite Rra.
assert (Qsp2 : spZ (ms_regs msC) = s1v)
  by (unfold spZ; rewrite Rsp, EE2; apply unsigned_lit_small; clear - Hs1r; lia).
rewrite Qsp2 in HtcjA.
assert (KA : tcj_kept B SB_CH_STK lyc Sc W (ms_mem msC) W memA s1v (tsb_ch_wr b p nj cap)).
{ eapply (sbd_kept_of_call W (ms_mem msC) memA lyc Sc S2 _ s1v s1v SB_CH_STK SB_CH_STK
            HtcjA Habl HSUBF (Z.le_refl _) (Z.le_refl _)).
  intros a Ha. pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
  apply Hpr. apply HWIN. exact Ha. }
pose proof (sbd_inv_call SB_CH_STK lyc Sc W (ms_mem msC) memA s1v b p cap n ov
  (sb_dec_c.sb_dec_D v md) j nj ovj KA HOUTB HBUF Hn0 Hj3 INVC VpA VcapA Hif) as INVA.
assert (KLA : tcj_kept B SB_CH_STK lyc Sc W mem1 W memA s1v
  (fun a => (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) \/
            tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a)).
{ apply (sbd_kept_mono _ _ _ _ _ _ _ _ _ (sbd_kept_trans _ _ _ _ _ _ _ _ _ _ K1C KA)).
  intros a [[Ha | []] | [Hw | (Hlt & Hw)]]; [exact Ha | right; left; exact Hw | ].
  right; right. destruct (HNJW Hlt) as (X & _). subst a. exact X. }
destruct (sbd_call_frame lyc Sc S2 W (ms_mem msC) memA _ fpos b p nj cap s1v SB_CH_STK (proj1 HJL) Hfrs Habl
  HtcjA Hblo HNJD) as (KFA & KSA).
(* the symbolic state after the call: no region kept, the callee-saved registers as they were *)
jafter_call_keep_pi HS 40%nat regsA (mrestrict (w_H W) memA) HPA (@nil nat) HS3.
specialize (HS3 (Forall_nil _)).
clear HS SHOK. rewrite <- restrict_mkst_fx in HS3.
lazymatch type of HS3 with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEI3 : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (SHOK3 : sh_ok SEGS sbd_Bx [] E2 (mrestrict (w_H W) memA)) by apply Forall_nil end.
lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ =>
  let vv := eval vm_compute in ss in change ss with vv in HS3 end.
change memA with (ms_mem (mkst regsA (Z_to_bv 64 (BASE + 12292)) memA (seg_rom SEGS))) in HJA.
(* addi s4,s4,-1 and the loop's test bne s4,s5 *)
paj_run_tok RUN HS3 HJA SHOK3 Bspan; [apply awr_ok_nil | ].
rename ms into msR. rename HFr into HFrR. rename HG into HGR. clear HF.
assert (KVR : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msR) a = aview SEGS (w_H W) memA a)
  by sbd_kv0 HFrR.
assert (KRR : tcj_kept B SB_CH_STK lyc Sc W memA W (ms_mem msR) s1v (fun _ => False)).
{ eapply (sbd_kept_of_run W _ _ memA (ms_mem msR) lyc Sc S2 _ _ s1v SB_CH_STK);
  [ exact (proj1 HJA) | exact Habl | exact HSUBF | exact HFrR | exact HGR
  | intros a0 (r0 & Hr0 & _); destruct Hr0
  | intros a0 Hi0 (r0 & Hr0 & _); destruct Hr0
  | intros a Ha; pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _);
    apply Hpr; apply HWIN; exact Ha ]. }
pose proof (sbd_inv_keep SB_CH_STK lyc Sc W memA (ms_mem msR) s1v (fun _ => False) b p cap n ov
  (sb_dec_c.sb_dec_D v md) (Datatypes.S j) _ _ KRR
  ltac:(intros t Ht; destruct (HOUTB t Ht) as (X1 & X2); split; [exact X1 | split; [exact X2 | intros X3; exact X3]])
  ltac:(intros Hpos; split; [exact (proj1 (HBUF Hpos)) | intros a Ha X; exact X])
  ltac:(clear - Hj3; lia) INVA) as INVR.
assert (KLR : tcj_kept B SB_CH_STK lyc Sc W mem1 W (ms_mem msR) s1v
  (fun a => (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) \/
            tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a))
  by (apply (sbd_kept_mono _ _ _ _ _ _ _ _ _ (sbd_kept_trans _ _ _ _ _ _ _ _ _ _ KLA KRR));
      intros a [Ha | []]; exact Ha).
(* the loop's test: back to the loop head while digits remain (i <> 0), else on to 0x83790 *)
psrr_branch_tok RUN BR HS3 SHOK3 Bspan.
all: lazymatch goal with Hc : branch_taken _ (sv_denot ?E3 _) _ = _ |- _ =>
       rewrite (sbd_bne E3 (Z.of_nat i) ltac:(rewrite ew_havoc_old by (cbv; lia); exact U20)
                  ltac:(clear - Hi3; lia)) in Hc end.
1: assert (Hi0 : i <> 0%nat) by (intros Hi0; rewrite Hi0 in Hc; discriminate Hc).
2: assert (Hi0 : i = 0%nat)
     by (destruct i as [|i']; [reflexivity | exfalso; clear - Hc; cbn in Hc; discriminate Hc]).
1: paj_run_to_tok RUNTO HS3 HJA SHOK3 Bspan 0x2fe0; [apply awr_ok_nil | ].
2: paj_run_to_tok RUNTO HS3 HJA SHOK3 Bspan 0x301c; [apply awr_ok_nil | ].
all: rename ms into msB; rename HFr into HFrB; rename HG into HGB; clear HF.
all: assert (KVB : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) memA a);
  [ intros a Ha; rewrite <- (KVR a Ha); revert a Ha; sbd_kv0 HFrB | ].
all: assert (KRB : tcj_kept B SB_CH_STK lyc Sc W (ms_mem msR) W (ms_mem msB) s1v (fun _ => False));
  [ eapply (sbd_kept_of_run W _ _ (ms_mem msR) (ms_mem msB) lyc Sc S2 _ _ s1v SB_CH_STK);
    [ exact (proj1 HJA) | exact Habl | exact HSUBF | exact HFrB | exact HGB
    | intros a0 (r0 & Hr0 & _); destruct Hr0
    | intros a0 Hi1 (r0 & Hr0 & _); destruct Hr0
    | intros a Ha; pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _);
      apply Hpr; apply HWIN; exact Ha ]
  | ].
all: pose proof (sbd_inv_keep SB_CH_STK lyc Sc W (ms_mem msR) (ms_mem msB) s1v (fun _ => False) b p cap n ov
  (sb_dec_c.sb_dec_D v md) (Datatypes.S j) _ _ KRB
  ltac:(intros t Ht; destruct (HOUTB t Ht) as (X1 & X2); split; [exact X1 | split; [exact X2 | intros X3; exact X3]])
  ltac:(intros Hpos; split; [exact (proj1 (HBUF Hpos)) | intros a Ha X; exact X])
  ltac:(clear - Hj3; lia) INVR) as INVB.
all: assert (KLB : tcj_kept B SB_CH_STK lyc Sc W mem1 W (ms_mem msB) s1v
  (fun a => (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) \/
            tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a));
  [ apply (sbd_kept_mono _ _ _ _ _ _ _ _ _ (sbd_kept_trans _ _ _ _ _ _ _ _ _ _ KLR KRB));
    intros a [Ha | []]; exact Ha | ].
(* sb_dec's frame outside the digit slot, and the slot's shadow byte, as at the loop head *)
all: assert (KFB : forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 ->
                aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) memL a);
  [ intros a Ha; rewrite (KVB a (HFR a Ha)), (KFA a Ha), (KVC a (HFR a Ha)); reflexivity | ].
all: pmkst HS3.
(* ---- back at the loop head: the next turn, by the induction hypothesis ---- *)
1: { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Qg =>
       change (SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) rg mm mdx) Qg) end.
     prreg HS3 (2%bv : bv 5) Q2; prreg HS3 (3%bv : bv 5) Q3; prreg HS3 (4%bv : bv 5) Q4;
     prreg HS3 (8%bv : bv 5) Q8; prreg HS3 (18%bv : bv 5) Q18; prreg HS3 (19%bv : bv 5) Q19;
     prreg HS3 (20%bv : bv 5) Q20; prreg HS3 (21%bv : bv 5) Q21; prreg HS3 (22%bv : bv 5) Q22;
     prreg HS3 (23%bv : bv 5) Q23; prreg HS3 (24%bv : bv 5) Q24; prreg HS3 (25%bv : bv 5) Q25;
     prreg HS3 (26%bv : bv 5) Q26; prreg HS3 (27%bv : bv 5) Q27.
     eapply (IH (i - 1)%nat ltac:(clear - Hi0; lia) (Datatypes.S j) _ _ (ms_regs msB) (ms_mem msB) _).
     unfold sbd_lh.
     split; [clear - Hi3; lia|].
     split; [clear - Hj Hi0; lia|].
     split; [exact HJA|].
     split; [rewrite Q2, EE2; reflexivity|].
     split; [rewrite Q3, EE3; reflexivity|].
     split; [rewrite Q4, EE4; reflexivity|].
     split; [rewrite Q8, EE8; reflexivity|].
     split; [rewrite Q18, EE18; reflexivity|].
     split; [rewrite Q19, EE19; reflexivity|].
     split; [rewrite Q20, U20; unfold w64; f_equal; clear - Hi0; lia|].
     split; [rewrite Q21; reflexivity|].
     split; [rewrite Q22, EE22; reflexivity|].
     split; [rewrite Q23, EE23; reflexivity|].
     split; [rewrite Q24, EE24; reflexivity|].
     split; [rewrite Q25, EE25; reflexivity|].
     split; [rewrite Q26, EE26; reflexivity|].
     split; [rewrite Q27, EE27; reflexivity|].
     split.
     { intros t Ht.
       rewrite (KFB (frame_addr lyc 0 fpos + 32 + Z.of_nat t) ltac:(clear - Ht Hi3 Hi0; lia)),
         (HDIG t ltac:(clear - Ht Hi0; lia)).
       replace (Datatypes.S j + (i - 1 - t))%nat with (j + (i - t))%nat by (clear - Ht Hi0; lia).
       reflexivity. }
     split.
     { intros a Ha Hn. rewrite (KFB a Ha). exact (HFRM a Ha Hn). }
     split.
     { rewrite (KVB _ HSHR), KSA, (KVC _ HSHR). exact HSHL. }
     split; [exact INVB | exact KLB]. }
(* ---- the last digit is emitted: on to 0x83790 with sbd_at2 ---- *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Qg =>
  change (SRr SEGS W (cfg_at SEGS (BASE + 0x301c) rg mm mdx) Qg) end.
prreg HS3 (3%bv : bv 5) Q3; prreg HS3 (4%bv : bv 5) Q4; prreg HS3 (8%bv : bv 5) Q8;
prreg HS3 (18%bv : bv 5) Q18; prreg HS3 (23%bv : bv 5) Q23; prreg HS3 (24%bv : bv 5) Q24;
prreg HS3 (27%bv : bv 5) Q27.
apply HQ.
eapply (sbd_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1
          (ms_regs msB) (ms_mem msB) _ _ _ HAT HJA);
  [ rewrite Q3, EE3; reflexivity | rewrite Q4, EE4; reflexivity | rewrite Q8, EE8; reflexivity
  | rewrite Q18, EE18; reflexivity | rewrite Q23, EE23; reflexivity | rewrite Q24, EE24; reflexivity
  | rewrite Q27, EE27; reflexivity
  | intros a Ha Hn; rewrite (KFB a Ha); exact (HFRM a Ha Hn)
  | replace (length (sb_dec_c.sb_dec_D v md)) with (Datatypes.S j) by (clear - Hj Hi0; lia); exact INVB
  | exact KLB ].
Qed.
(* The whole emit loop, from any turn: one turn at a time, by induction on the turn's index. *)
Lemma sbd_emit_loop : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1
    (Q : world SEGS -> config -> Prop),
  sbd_at1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regs2 : bvmap 5 word) mem2 md2,
     sbd_at2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 regs2 mem2 md2 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x301c) regs2 mem2 md2) Q) ->
  forall (i j : nat) nj ovj (regsL : bvmap 5 word) memL mdL,
  sbd_lh STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs b v md p cap n ov fpos S2 s1v mem1 i j nj ovj
    regsL memL mdL ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) regsL memL mdL) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 Q
  HAT HQ.
assert (G : forall (m i : nat), (i <= m)%nat -> forall (j : nat) nj ovj (regsL : bvmap 5 word) memL mdL,
  sbd_lh STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs b v md p cap n ov fpos S2 s1v mem1 i j nj ovj
    regsL memL mdL ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) regsL memL mdL) Q).
{ induction m as [|m IHm]; intros i Hi;
  apply (sbd_emit_turn STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
           regs1 mem1 md1 Q HAT HQ i);
  intros i' Hi'; [exfalso; lia | apply IHm; lia]. }
intros i. exact (G i i (le_n i)).
Qed.
Theorem sbd_segB_lt10 : sbd_segB_lt10_spec.
Proof.
unfold sbd_segB_lt10_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 Q
  Hvlt HAT HQ.
pose proof HAT as HAT0.
destruct HAT0 as (HJ & Hfrs & Habl & Hra & Hal16 & Hwlo & Hwhi & Hgp & Htp & Hra4 & Hv & Hmd &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov &
  Hs1lo & Hs1hi & Hs1al & Hflag &
  R2 & R3 & R4 & R5 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R18 & R19 & R20 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 &
  HSHB & VP & VCAP & VN & VOV & HWR & HROOM & HKEEP).
pose proof (proj1 HJ) as HAR.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HDS0 : SB_DEC_STK = 4256) by reflexivity.
assert (HCS0 : SB_CH_STK = 4112) by reflexivity.
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof pa_base_lo as HBLO.
destruct (frames_bounds SEGS B LAWS lyc S2 W mem1 md1 0 fpos HAR Hin) as (HF4096 & HFceil & HFapp).
(* where the caller's struct and sb_dec's stack window lie *)
pose proof HJ as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & Hstkz & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof Hrec as (Hrl0 & Hrh0).
assert (Hblo : alloc_ceiling <= b) by (rewrite Elo in Hrl0; lia).
assert (Hbhi : b + 32 <= 2 ^ 47) by (rewrite Ehi in Hrh0; lia).
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* One digit: v < 10 (the premise of this half), so the loop's exit test at 0x8372c is taken on the first
   turn; it is decided as a condition of the entry state. *)
destruct (Z.lt_ge_cases v 10) as [Hv10 | Hv10]; [ | exfalso; clear - Hvlt Hv10; lia ].
assert (HC : conds_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) [sbd_lt 21]).
{ split; [|exact I]. apply (sbd_cond_lt _ 21 v ltac:(lia)); [| exact Hv10].
  unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl). exact R21. }
destruct (sbd_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
  regs1 mem1 md1 [sbd_lt 21] HAT HC) as [HS SHOK].
(* the two atoms the write-window side conditions speak about: the digit slot and its shadow byte *)
assert (U25 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 25) = frame_addr lyc 0 fpos + 32).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl), R25. apply unsigned_lit_small. lia. }
assert (U38 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 38)
  = SHADOW_OFF + (frame_addr lyc 0 fpos + 32) / 8).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs1 _ 6). apply unsigned_lit_small.
  assert (HS8 : 0 <= (frame_addr lyc 0 fpos + 32) / 8) by (apply Z.div_pos; lia).
  assert (HS8h : (frame_addr lyc 0 fpos + 32) / 8 <= frame_addr lyc 0 fpos)
    by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF. lia. }
assert (EE2 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 2 = w64 s1v).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). exact R2. }
assert (EE3 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 3 = getr regs 3).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 3 3%bv eq_refl). exact R3. }
assert (EE4 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 4 = getr regs 4).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 4 4%bv eq_refl). exact R4. }
assert (EE8 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 8 = getr regs 2).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl). exact R8. }
assert (EE18 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 18 = w64 (frame_addr lyc 0 fpos)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl). exact R18. }
assert (EE23 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 23 = w64 (frame_addr lyc 0 fpos)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl). exact R23. }
assert (EE24 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 24
  = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 24 24%bv eq_refl). exact R24. }
assert (EE27 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 27 = getr regs 27).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl). exact R27. }
assert (U20 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 20) = md).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 20 20%bv eq_refl), R20. apply unsigned_lit_small. lia. }
assert (EE20 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 20 = w64 md).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 20 20%bv eq_refl). exact R20. }
assert (EE19 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 19 = w64 b).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl). exact R19. }
assert (U35 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 35) = v mod 10).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 3).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound v 10 ltac:(lia)). lia. }
assert (U36 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 36) = v / 10 mod 10).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 4).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound (v / 10) 10 ltac:(lia)). lia. }
assert (U37 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 37) = v / 10 / 10 mod 10).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 5).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound (v / 10 / 10) 10 ltac:(lia)). lia. }
assert (EE22 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 22 = w64 SHADOW_OFF).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl). exact R22. }
assert (EE25 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 25 = w64 (frame_addr lyc 0 fpos + 32)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl). exact R25. }
assert (EE26 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 26
  = w64 (2 ^ 64 - (frame_addr lyc 0 fpos + 32) - 1)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 26 26%bv eq_refl). exact R26. }
(* the shadow byte of the digit slot lies outside the slot, and the frame inside the address space *)
assert (HSHNS : 0 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < 2 ^ 64 /\
  ~ (frame_addr lyc 0 fpos + 32 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < frame_addr lyc 0 fpos + 36)).
{ pose proof (Z.div_mod (frame_addr lyc 0 fpos) 8 ltac:(lia)) as DF8.
  pose proof (Z.mod_pos_bound (frame_addr lyc 0 fpos) 8 ltac:(lia)) as MF8.
  unfold SHADOW_OFF. lia. }
assert (HFR : forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; lia).
remember (sbd_env regs1 v (frame_addr lyc 0 fpos)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sbd_env; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + 0x2f80)) with (Z_to_bv 64 (BASE + 0x2f80)).
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (BASE + 0x2f80)) mem1 (seg_rom SEGS))) in HJ.
(* the run from 0x836f4: the whole digit loop, stopping at the pad's branch on md (0x83734) *)
paj_run_tok RUN HS HJ SHOK Bspan; [sbd_awr fpos | ].
rename ms into ms1. rename HFr into HFr1. rename HG into HG1. clear HF.
assert (K1 : tcj_kept B SB_CH_STK lyc Sc W mem1 W (ms_mem ms1) s1v
  (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36)).
{ eapply (sbd_kept_of_run W E sbd_rs mem1 (ms_mem ms1) lyc Sc S2 _ _ s1v SB_CH_STK);
  [ exact (proj1 HJ) | exact Habl | (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0)
  | exact HFr1 | exact HG1 | sbd_wr_slot
  | sbd_wr_img (frm_off_imgP B lyc S2 W mem1 md1 0 fpos HAR Hin) | sbd_pres_win HJ ]. }
assert (KF1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem1 a) by sbd_kvs HFr1.
(* the branch on md at 0x83734: md = 1 goes straight to the emit loop, md = 2 first pads a '0' *)
psrr_branch_tok RUN BR HS SHOK Bspan.
1: assert (Hmd1 : md = 1).
1: { revert Hc. rewrite branch_geu_U, U_SLit, U_SOff, U20, Z.add_0_r.
     rewrite !zcanon_id by (unfold M64; lia).
     destruct (Z.ltb_spec 1 md); [discriminate | intros _; lia]. }
2: assert (Hmd2 : md = 2).
2: { revert Hc. rewrite branch_geu_U, U_SLit, U_SOff, U20, Z.add_0_r.
     rewrite !zcanon_id by (unfold M64; lia).
     destruct (Z.ltb_spec 1 md); [intros _; lia | discriminate]. }
(* the digits of each path: the model's sb_dec_D *)
all: assert (Hlsd : sb_dec_c.sb_dec_lsd v 3 = [48 + v mod 10]);
  [ cbn [sb_dec_c.sb_dec_lsd]; replace (v <? 10) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity | ].
1: assert (HDl : sb_dec_c.sb_dec_D v md = [48 + v mod 10]).
1: { unfold sb_dec_c.sb_dec_D. rewrite Hlsd. cbn [length]. change (Z.of_nat 1) with 1.
     replace (1 <? md) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
2: assert (HDl : sb_dec_c.sb_dec_D v md = [48; 48 + v mod 10]).
2: { unfold sb_dec_c.sb_dec_D. rewrite Hlsd. cbn [length]. change (Z.of_nat 1) with 1.
     replace (1 <? md) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
(* on to the emit loop's head 0x83754 (BASE + 0x2fe0) *)
all: paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2fe0; [sbd_awr fpos | ].
all: rename ms into ms2; rename HFr into HFr2; rename HG into HG2; clear HF.
all: assert (K2 : tcj_kept B SB_CH_STK lyc Sc W (ms_mem ms1) W (ms_mem ms2) s1v
  (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36));
  [ eapply (sbd_kept_of_run W _ _ (ms_mem ms1) (ms_mem ms2) lyc Sc S2 _ _ s1v SB_CH_STK);
    [ exact (proj1 HJ) | exact Habl | (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0)
    | exact HFr2 | exact HG2 | sbd_wr_slot
    | sbd_wr_img (frm_off_imgP B lyc S2 W mem1 md1 0 fpos HAR Hin) | sbd_pres_win HJ ]
  | ].
all: assert (KF2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
  aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) (ms_mem ms1) a); [ sbd_kvs HFr2 | ].
all: assert (K : tcj_kept B SB_CH_STK lyc Sc W mem1 W (ms_mem ms2) s1v
  (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36));
  [ apply (sbd_kept_mono _ _ _ _ _ _ _ _ _ (sbd_kept_trans _ _ _ _ _ _ _ _ _ _ K1 K2));
    intros a [Ha | Ha]; exact Ha | ].
all: assert (KF : forall a, 0 <= a < 2 ^ 64 ->
  ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
  aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem1 a);
  [ intros a Ha Hn; rewrite (KF2 a Ha Hn); exact (KF1 a Ha Hn) | ].
(* the digits the loop left in the slot, read back from the symbolic state *)
all: pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0.
all: destruct HR0 as (_ & _ & _ & HCH).
all: cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HCH.
all: rewrite U25 in HCH.
all: repeat (let Hk := fresh "HCk" in apply Forall_cons_iff in HCH; destruct HCH as [Hk HCH]).
all: repeat match goal with
     | H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff 35 48))) |- _ =>
         let Hd := fresh "HDG" in
         pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SOff 35 48) (48 + v mod 10) H
           ltac:(cbn [sv_denot]; rewrite U35; f_equal; apply Z.add_comm)
           ltac:(pose proof (Z.mod_pos_bound v 10 ltac:(lia)); lia)) as Hd; clear H
     | H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SLit 48))) |- _ =>
         let Hd := fresh "HDG" in
         pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SLit 48) 48 H
           ltac:(reflexivity) ltac:(lia)) as Hd; clear H
     end.
all: pmkst HS.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Qg =>
       change (SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) rg mm mdx) Qg) end.
all: prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
     prreg HS (8%bv : bv 5) P8; prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19;
     prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22;
     prreg HS (23%bv : bv 5) P23; prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25;
     prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27.
(* the emit loop, one sb_ch call per digit (sbd_emit_loop) *)
1: eapply (sbd_emit_loop STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
             regs1 mem1 md1 Q HAT HQ 0%nat 0%nat n ov (ms_regs ms2) (ms_mem ms2) _).
2: eapply (sbd_emit_loop STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
             regs1 mem1 md1 Q HAT HQ 1%nat 0%nat n ov (ms_regs ms2) (ms_mem ms2) _).
all: unfold sbd_lh.
all: split; [lia|].
all: split; [rewrite HDl; reflexivity|].
all: split; [exact HJ|].
all: split; [rewrite P2, EE2; reflexivity|].
all: split; [rewrite P3, EE3; reflexivity|].
all: split; [rewrite P4, EE4; reflexivity|].
all: split; [rewrite P8, EE8; reflexivity|].
all: split; [rewrite P18, EE18; reflexivity|].
all: split; [rewrite P19, EE19; reflexivity|].
all: split; [rewrite P20; reflexivity|].
all: split; [rewrite P21; reflexivity|].
all: split; [rewrite P22, EE22; reflexivity|].
all: split; [rewrite P23, EE23; reflexivity|].
all: split; [rewrite P24, EE24; reflexivity|].
all: split; [rewrite P25, EE25; reflexivity|].
all: split; [rewrite P26, EE26; reflexivity|].
all: split; [rewrite P27, EE27; reflexivity|].
all: split;
  [ intros t Ht; rewrite HDl; destruct t as [|[|t]]; try (exfalso; clear - Ht; lia);
    cbn [nth Nat.add Nat.sub Z.of_nat Pos.of_succ_nat]; assumption | ].
all: split; [ intros a Ha Hn; exact (KF a (HFR a Ha) Hn) | ].
all: split; [ rewrite (KF _ (proj1 HSHNS) (proj2 HSHNS)); exact HSHB | ].
all: split;
  [ exact (sbd_inv0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
             regs1 mem1 md1 (ms_mem ms2) _ HAT HJ K)
  | apply (sbd_kept_mono _ _ _ _ _ _ _ _ _ K); intros a Ha; left; exact Ha ].
Qed.
End walk.
End h.
End f.
End d.
