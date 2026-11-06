(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0, 0x268 bytes, listing offset AF_sb_dec = 0x2e5c): its
   ASan+UBSan-build contract tsb_dec_spec, in cgif's caller-journal form (CONVENTIONS.md §2; cgif
   lib/YC20.v:311-365, tlzw_kept / tlzw_post / tlzw_spec): sb_dec writes its caller's struct sb (on the
   caller's machine stack) and the caller's buffer (in the caller's side-stack frame).
   The B twin of lib/A/Prog/sb_dec.v: the same
   names, argument order, premises and post. What image B changes:
   - the B listing layer (PAImg identb_listing, AF_sb_dec = 0x2e5c) and the B frame helpers (IdentBFrame.v);
   - the stack SB_DEC_STK: frame 128 (0x835d0 addi sp,sp,-128) and sb_ch's SB_CH_STK below the aligned sp;
   - sb_dec does not touch the struct itself: it calls sb_ch once per digit (0x83774), so b's 28 bytes and
     p[n ..] are read and written by sb_ch under its contract tsb_ch_spec (lib/B/Prog/sb_ch.v);
   - the listing's UBSan null-pointer check of p in sb_ch (0x838b4..0x838c4, trap at 0x83908): 0 < p
     in place of the A text's 0 <= p.
   THE WALK: Theorem pb_sb_dec : tsb_dec_spec B is in lib/B/Prog/SbDecWalk.v, chained from the segment lemmas
   of SbDecSegA.v (0x835d0 .. 0x836f4), SbDecSegB.v / SbDecSegBv10a.v / SbDecSegBv10b.v (0x836f4 .. 0x83790,
   split on v) and SbDecSegC.v (0x83790 .. 0x83830). Those files Require this one, so the walk cannot sit
   here; its Section hypotheses are listed in SbDecWalk.v. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib.
(* The side-stack frame helpers of image B. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBFrame YC85.
(* The shared caller-journal shapes tcj_kept / twr_ok / tdst_ok of image B.
   *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBCJ.
(* The callee's contract: tsb_ch_spec,
   SB_CH_STK, EV_SB_CH. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch.
(* The plain model of sb_dec (released, origin/ossv/recipes c8557374ad2e), used as it is (the A text's
   choice; lib/U/Prog/sb_dec_c.v defines sb_dec_lsd / sb_dec_D / sb_dec_room / sb_dec_acc with the same text). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_sb_dec : Z := BASE + AF_sb_dec.
(* The stack the call needs, measured from the listing: the 128-byte frame (0x835d0 addi sp,sp,-128;
   probe 0x835d4 at sp0-128; ra, s0..s10 at sp0-8 .. sp0-96), the 32-byte alignment of sp (0x8360c andi
   sp,sp,-32: up to 16 more bytes, sp0 is 16-aligned), so s1 = sp >= sp0 - 144 at both calls. Below s1:
   ESTACK for the class-0 side-stack frame allocation at 0x83640 and SB_CH_STK = 16 + ESTACK
   (lib/B/Prog/sb_ch.v) for the sb_ch call at 0x83774; the larger is SB_CH_STK, so 144 + 16 + ESTACK.
   The real-stack fallback (0x83658..0x83670: frame at s1-64, one probe store at s1-4096, sb_ch then called
   from s1-64) is not reached: the use-after-return flag cell holds 1 (AR_const_law) and the class-0
   allocation returns a frame (0x83654 bnez taken). *)
Definition SB_DEC_STK : Z := 160 + ESTACK.
(* Allocator events and live heap bytes of one call: none. The ASan+UBSan listing calls no allocator; the
   class-0 side-stack frame allocation counts no event (YG00.v:570-579 stack_malloc has no tick) and adds no
   heap block; sb_ch (at most 3 calls, one per digit) has EV_SB_CH = 0 (lib/B/Prog/sb_ch.v). Both must fit
   under the shared EV_MAX / LIVE_MAX. *)
Definition EV_SB_DEC : Z := 0.
Definition LIVE_SB_DEC : Z := 0.
Section h.
Variable B : asyms.
(* The bytes sb_dec writes outside its own stack window and its own side-stack frame (through sb_ch):
   b->n and b->over (b+16 .. b+28) and the emitted digits p[n .. n + acc). *)
Definition tsb_dec_wr (b p n acc : Z) (a : Z) : Prop :=
  (b + 16 <= a < b + 28) \/ (p + n <= a < p + n + acc).
(* Where the caller's struct sb lies: in the caller's machine stack, with the whole 32-byte slot
   [b, b+32) inside it (AR_zshadow_law then gives zero shadow for the four granules). The A text's reason
   (A's hoisted andi of the b->over check) is not in B's sb_dec: B's b->over check is in sb_ch
   (0x838e0..0x83918), whose contract takes b in a frame or the machine stack (tsb_ch_rec_at) and
   range_addressable b 28; both follow from this premise at every call, and it keeps b's bytes and shadow
   across the frame allocation at 0x83640. In fuzz_identity b is reac_box_name's machine stack. *)
Definition tsb_dec_rec_at (lyc : alayout) (b : Z) : Prop :=
  ly_stk_lo lyc <= b /\ b + 32 <= ly_stk_hi lyc.
(* The post: cgif tlzw_post, YC20.v:328-346, with sb_dec's result (the plain sb_dec_c model: the struct
   sb record sb_rec p cap n' over' and the digits firstn acc (sb_dec_D v md) at p + n). *)
Definition tsb_dec_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b v md p cap n ov : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_SB_DEC) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    tcj_kept B SB_DEC_STK lyc Sc W memc W2 mem2 (spZ regs) (tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n)) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) b 8 p /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 8) 8 cap /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 16) 8 (n + sb_dec_c.sb_dec_acc v md cap n) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) (b + 24) 4
      (if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else ov) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (p + n)
      (firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md)).
(* The pre-condition: cgif tlzw_spec, YC20.v:347-365. a0 = b (struct sb { char *p; size_t cap, n;
   int over; }, 28 bytes), a1 = v, a2 = md (min_digits). *)
Definition tsb_dec_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b v md p cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 b -> getr regs 11 = w64 v -> getr regs 12 = w64 md ->
  0 <= v < 2 ^ 31 -> (md = 1 \/ md = 2) ->
  (* the struct sb: read (p, cap, n), written (n, over) *)
  b mod 8 = 0 -> 0 <= b -> b + 28 <= 2 ^ 63 -> (spZ regs <= b \/ b + 28 <= spZ regs - SB_DEC_STK) ->
  tsb_dec_rec_at lyc b ->
  val_mem SEGS (mrestrict (w_H W) memc) b 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (b + 24) 4 ov ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 4 < 2 ^ 64 -> 0 <= ov < 2 ^ 32 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + 16) 12 ->
  (* the buffer: written p[n .. n + acc) when there is room *)
  (0 < sb_dec_c.sb_dec_room cap n ->
     0 < p /\ p + cap <= 2 ^ 63 /\
     tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= b \/ b + 28 <= p + n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= spZ regs - SB_DEC_STK \/ spZ regs <= p + n)) ->
  (* room for sb_dec's own class-0 side-stack frame; the allocator budget (both increments are 0) *)
  Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV_SB_DEC <= EV_MAX -> blocks_bytes Sc + LIVE_SB_DEC <= LIVE_MAX ->
  SRr SEGS W (cfg_at SEGS A_sb_dec regs memc mdc)
    (tsb_dec_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov).
End h.
End f.
End d.
