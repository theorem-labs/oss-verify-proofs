(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:358-361
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/IngestWalk.v, with its module paths and module names changed; 125 of its 161 lines of code are new or changed and 331 lines of the source are left out. *)
(* The boundary layer of sb_dec's ASan walk (fuzz_identity.asan 0x83494, AF_sb_dec 0x2d88): the state at each
   phase boundary of the listing, the statement of each segment lemma, and their composition into tsb_dec_spec
   (proved here). The segments are proved against these statements (lanes), not here.

   Segments (addresses from (internal path); offsets from 0x83494):
   A 0x83494..0x835f4 (+0x000..+0x160), 88 slots, plain runs: the prologue (frame 96, saves, realign
     andi sp,sp,-32), the use-after-return flag load (GOT 0x9c408), __asan_stack_malloc_0 (a0 = 64, 0x834f8),
     the frame header and the frame's shadow f1 f1 f1 f1 04 f3 f3 f3, the digit loop (0x835a4..0x835e0, up to
     three digits into d[0..3) at frame+32) and the min_digits pad (0x835e4..0x835f0).
   B 0x835f4..0x836e8 (+0x160..+0x254), 61 slots, token runs: the emit loop (0x8363c..0x836bc, kd turns, each
     with the shadow checks of b, b+8, b+16, b+24, d[j] and p+n), writing b->n, b->over and p[n..n+acc).
   C 0x836e8..ret (+0x254..+0x2ec), 38 slots, plain runs: the release (shadow +4 := f8, magic 0x45e0360e,
     shadow := f5 x 8, the flag byte through the word at frame+56), the epilogue, ret; then the post.

   The walk's journal is the caller's (tsb_dec_spec's premise), extended: own frames (0, pos) :: own, events
   k. Every write of the call has its right there (twr_ok for b+16..b+28 and p+n..p+n+acc; the window of the
   caller for sb_dec's stack; the own list for sb_dec's frame), as YC85 aj_stack_malloc_atS (seg A) and
   IdentFrame aj_flag_store_pi (seg C, own' = own) state it. Beside it each boundary carries tcj_kept against
   the call's entry state (window SB_DEC_STK below the entry sp, write set tsb_dec_wr), which tsb_dec_post
   asks for. (The call's own journal, based at the entry state, cannot hold: b lies on the caller's machine
   stack outside the call's window, and YCbq.v ajournal has no write-token exception there.) *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 YC81 YC4b YC45 YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The boundaries' slots, as offsets from sb_dec's first slot. *)
Definition SBD_A_END : Z := 0x160.   (* 0x835f4 addi a1,s2,16 *)
Definition SBD_B_END : Z := 0x254.   (* 0x836e8 li a1,-8 *)
(* The frame's shadow after the prologue (0x83578..0x8359c): d[0..4) at frame+32 is the one variable. *)
Definition SBD_FRAME_SHADOW : list Z := [241; 241; 241; 241; 4; 243; 243; 243].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.

(* ---- the call: tsb_dec_spec's variables -------------------------------------------------------------------- *)
Record sbd_ctx : Type := mkSbd {
  sq_STK : Z; sq_sp0 : Z; sq_FP : list (Z * Z); sq_ly : alayout; sq_S : astate; sq_W0 : world SEGS;
  sq_mem0 : word -> option byte; sq_md0 : Model; sq_own : list (Z * Z);
  sq_lyc : alayout; sq_Sc : astate; sq_W : world SEGS; sq_memc : word -> option byte; sq_mdc : Model; sq_k : Z;
  sq_regs : bvmap 5 word; sq_b : Z; sq_v : Z; sq_md : Z; sq_p : Z; sq_cap : Z; sq_n : Z; sq_ov : Z }.
(* sb_dec's entry sp, and the plain model of the result (lib/Prog/sb_dec_c.v). *)
Definition sq_sp (g : sbd_ctx) : Z := spZ (sq_regs g).
Definition sq_D (g : sbd_ctx) : list Z := sb_dec_c.sb_dec_D (sq_v g) (sq_md g).
Definition sq_kd (g : sbd_ctx) : Z := Z.of_nat (length (sq_D g)).
Definition sq_acc (g : sbd_ctx) : Z := sb_dec_c.sb_dec_acc (sq_v g) (sq_md g) (sq_cap g) (sq_n g).
Definition sq_over (g : sbd_ctx) : Z :=
  if sb_dec_c.sb_dec_room (sq_cap g) (sq_n g) <? sq_kd g then 1 else sq_ov g.
(* sb_dec's class-0 side-stack frame. *)
Definition sq_F (g : sbd_ctx) (pos : Z) : Z := frame_addr (sq_lyc g) 0 pos.

(* tsb_dec_spec's premises, in its order. *)
Definition sbd_pre (g : sbd_ctx) : Prop :=
  ajournal SEGS B (sq_STK g) (sq_sp0 g) (sq_FP g) (sq_ly g) (sq_S g) (sq_W0 g) (sq_mem0 g) (sq_md0 g) (sq_own g)
    (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) (sq_mdc g) (sq_k g) /\
  YK0s.ret_ok (getr (sq_regs g) 1) /\ 4096 <= raZ (sq_regs g) /\
  getr (sq_regs g) 3 = w64 (as_gp B) /\ getr (sq_regs g) 4 = w64 (as_tp B) /\
  spZ (sq_regs g) mod 16 = 0 /\ sq_sp0 g - sq_STK g <= spZ (sq_regs g) - SB_DEC_STK /\ spZ (sq_regs g) <= sq_sp0 g /\
  getr (sq_regs g) 10 = w64 (sq_b g) /\ getr (sq_regs g) 11 = w64 (sq_v g) /\ getr (sq_regs g) 12 = w64 (sq_md g) /\
  0 <= sq_v g < 2 ^ 31 /\ (sq_md g = 1 \/ sq_md g = 2) /\
  sq_b g mod 8 = 0 /\ 0 <= sq_b g /\ sq_b g + 28 <= 2 ^ 63 /\
  (spZ (sq_regs g) <= sq_b g \/ sq_b g + 28 <= spZ (sq_regs g) - SB_DEC_STK) /\
  tsb_dec_rec_at (sq_lyc g) (sq_b g) /\
  val_mem SEGS (rd (sq_W g) (sq_memc g)) (sq_b g) 8 (sq_p g) /\
  val_mem SEGS (rd (sq_W g) (sq_memc g)) (sq_b g + 8) 8 (sq_cap g) /\
  val_mem SEGS (rd (sq_W g) (sq_memc g)) (sq_b g + 16) 8 (sq_n g) /\
  val_mem SEGS (rd (sq_W g) (sq_memc g)) (sq_b g + 24) 4 (sq_ov g) /\
  0 <= sq_p g < 2 ^ 64 /\ 0 <= sq_cap g < 2 ^ 64 /\ 0 <= sq_n g /\ sq_n g + 4 < 2 ^ 64 /\ 0 <= sq_ov g < 2 ^ 32 /\
  twr_ok B (sq_STK g) (sq_sp0 g) (sq_FP g) (sq_ly g) (sq_S g) (sq_lyc g) (sq_Sc g) (sq_own g) (sq_W g) (sq_memc g)
    (spZ (sq_regs g)) (sq_b g + 16) 12 /\
  (0 < sb_dec_c.sb_dec_room (sq_cap g) (sq_n g) ->
     0 <= sq_p g /\ sq_p g + sq_cap g <= 2 ^ 63 /\
     tdst_ok B (sq_lyc g) (sq_Sc g) (sq_p g + sq_n g) (sb_dec_c.sb_dec_acc (sq_v g) (sq_md g) (sq_cap g) (sq_n g)) /\
     range_addressable (aview SEGS (w_H (sq_W g)) (sq_memc g)) SHADOW_OFF (sq_p g + sq_n g)
       (sb_dec_c.sb_dec_acc (sq_v g) (sq_md g) (sq_cap g) (sq_n g)) /\
     twr_ok B (sq_STK g) (sq_sp0 g) (sq_FP g) (sq_ly g) (sq_S g) (sq_lyc g) (sq_Sc g) (sq_own g) (sq_W g) (sq_memc g)
       (spZ (sq_regs g)) (sq_p g + sq_n g) (sb_dec_c.sb_dec_acc (sq_v g) (sq_md g) (sq_cap g) (sq_n g)) /\
     (sq_p g + sq_n g + sb_dec_c.sb_dec_acc (sq_v g) (sq_md g) (sq_cap g) (sq_n g) <= sq_b g \/
      sq_b g + 28 <= sq_p g + sq_n g) /\
     (sq_p g + sq_n g + sb_dec_c.sb_dec_acc (sq_v g) (sq_md g) (sq_cap g) (sq_n g) <= spZ (sq_regs g) - SB_DEC_STK \/
      spZ (sq_regs g) <= sq_p g + sq_n g)) /\
  Z.of_nat (length (frames (sq_Sc g))) <= 8 /\
  st_nev (sq_Sc g) + EV_SB_DEC <= EV_MAX /\ blocks_bytes (sq_Sc g) + LIVE_SB_DEC <= LIVE_MAX.

(* ---- the boundaries ---------------------------------------------------------------------------------------- *)
(* What every boundary after the frame allocation carries (all slots measured on the listing):
   0x834c0 addi s0,sp,96 (s0 = entry sp); 0x834c4 andi sp,sp,-32 / 0x834c8 mv s1,sp (sp = s1, 32-aligned,
   96..112 below the entry sp); x3, x4, x24..x27 never written; 0x834f8 the allocation returns the frame in a0,
   0x83504 mv a6,a0, 0x83574 add a7,t0,s5 (a7 = shadow of the frame; t0 = frame >> 3 at 0x83544),
   0x834ec mv s2,a0 (s2 = b), 0x834e8 ld s5,0(a1) (s5 = the shadow base); the nine saves at entry sp - 8 ..
   entry sp - 72 (0x8349c..0x834bc), read back by the epilogue (0x83754..0x83774); the frame's flag word at
   frame + 64 - 8, read by the release (0x83724 ld a0,56(a0)). *)
Definition sbd_common (g : sbd_ctx) (pos : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
  getr regs2 8 = w64 (sq_sp g) /\
  (exists sp1, getr regs2 2 = w64 sp1 /\ getr regs2 9 = w64 sp1 /\
     sq_sp g - 112 <= sp1 <= sq_sp g - 96 /\ sp1 mod 32 = 0) /\
  getr regs2 3 = getr (sq_regs g) 3 /\ getr regs2 4 = getr (sq_regs g) 4 /\
  getr regs2 24 = getr (sq_regs g) 24 /\ getr regs2 25 = getr (sq_regs g) 25 /\
  getr regs2 26 = getr (sq_regs g) 26 /\ getr regs2 27 = getr (sq_regs g) 27 /\
  getr regs2 10 = w64 (sq_F g pos) /\ getr regs2 16 = w64 (sq_F g pos) /\
  getr regs2 17 = w64 (SB + sq_F g pos / 8) /\
  getr regs2 18 = w64 (sq_b g) /\ getr regs2 21 = w64 SB /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 8) 8 (raZ (sq_regs g)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 16) 8 (bv_unsigned (getr (sq_regs g) 8)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 24) 8 (bv_unsigned (getr (sq_regs g) 9)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 32) 8 (bv_unsigned (getr (sq_regs g) 18)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 40) 8 (bv_unsigned (getr (sq_regs g) 19)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 48) 8 (bv_unsigned (getr (sq_regs g) 20)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 56) 8 (bv_unsigned (getr (sq_regs g) 21)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 64) 8 (bv_unsigned (getr (sq_regs g) 22)) /\
  val_mem SEGS (rd (sq_W g) mem2) (sq_sp g - 72) 8 (bv_unsigned (getr (sq_regs g) 23)) /\
  rdword (aview SEGS (w_H (sq_W g)) mem2) (sq_F g pos + fs_frame_bytes 0 - 8) = Some (flag_addr (sq_lyc g) 0 pos).

(* A boundary: at slot BASE + AF_sb_dec + off, the caller's journal with own (0, pos) :: own and k events,
   the heap blocks unchanged, what the call has kept of its entry state (tcj_kept), the common part, and P.
   frames = (0, pos) :: own ++ ... is part of the journal. *)
Definition sbd_cut (g : sbd_ctx) (pos off : Z)
  (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = sq_W g /\ exists ly2 S2 regs2 mem2 md2,
    c2 = cfg_at SEGS (A_sb_dec + off) regs2 mem2 md2 /\
    ajournal SEGS B (sq_STK g) (sq_sp0 g) (sq_FP g) (sq_ly g) (sq_S g) (sq_W0 g) (sq_mem0 g) (sq_md0 g)
      ((0, pos) :: sq_own g) ly2 S2 (sq_W g) mem2 md2 (sq_k g) /\
    tcj_kept B SB_DEC_STK (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) (sq_W g) mem2 (sq_sp g)
      (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) (sq_acc g)) /\
    ablocks B ly2 S2 = ablocks B (sq_lyc g) (sq_Sc g) /\ ~ In (0, pos) (frames (sq_Sc g)) /\
    sbd_common g pos regs2 mem2 /\
    P ly2 S2 regs2 mem2 md2.

(* End of A (0x835f4): s6, s7 not yet written; a4 = d's address (0x83534 addi a4,a6,32), a5 = the digit count
   after the pad (0x835b0 / 0x835f0); d[0..kd) holds the digits least significant first (0x835d4, 0x835ec), i.e.
   rev (sb_dec_D v md); the frame's shadow as poisoned; the struct sb as at entry; the buffer's shadow as at
   entry (re-read by B's checks at 0x83694). *)
Definition sbd_A_end (g : sbd_ctx) (pos : Z) : world SEGS -> config -> Prop :=
  sbd_cut g pos SBD_A_END (fun ly2 S2 regs2 mem2 md2 =>
    getr regs2 22 = getr (sq_regs g) 22 /\ getr regs2 23 = getr (sq_regs g) 23 /\
    getr regs2 14 = w64 (sq_F g pos + 32) /\ getr regs2 15 = w64 (sq_kd g) /\
    garr8 SEGS (rd (sq_W g) mem2) (sq_F g pos + 32) (rev (sq_D g)) /\
    garr8 SEGS (rd (sq_W g) mem2) (SB + sq_F g pos / 8) SBD_FRAME_SHADOW /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g) 8 (sq_p g) /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 8) 8 (sq_cap g) /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 16) 8 (sq_n g) /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 24) 4 (sq_ov g) /\
    (0 < sq_acc g -> range_addressable (aview SEGS (w_H (sq_W g)) mem2) SHADOW_OFF (sq_p g + sq_n g) (sq_acc g))).

(* End of B (0x836e8): the struct sb and the digits as the post states them. *)
Definition sbd_B_end (g : sbd_ctx) (pos : Z) : world SEGS -> config -> Prop :=
  sbd_cut g pos SBD_B_END (fun ly2 S2 regs2 mem2 md2 =>
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g) 8 (sq_p g) /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 8) 8 (sq_cap g) /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 16) 8 (sq_n g + sq_acc g) /\
    val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 24) 4 (sq_over g) /\
    garr8 SEGS (rd (sq_W g) mem2) (sq_p g + sq_n g) (firstn (Z.to_nat (sq_acc g)) (sq_D g))).

(* ---- the segments ------------------------------------------------------------------------------------------ *)
(* A: entry -> 0x835f4. Proved under the walk's hypotheses (sb_dec.v Section walk): ASM0, SMP, TLF via
   YC85 aj_stack_malloc_atS for the allocation, plain runs (paj_run_sh) before and after it. *)
Definition seg_sbd_A : Prop :=
  forall g, sbd_pre g ->
  SRr SEGS (sq_W g) (cfg_at SEGS A_sb_dec (sq_regs g) (sq_memc g) (sq_mdc g))
    (fun W2 c2 => exists pos, sbd_A_end g pos W2 c2).
(* B: 0x835f4 -> 0x836e8, the checked emit loop (token runs, kd turns). *)
Definition seg_sbd_B : Prop :=
  forall g pos W2 c2, sbd_pre g -> sbd_A_end g pos W2 c2 -> SRr SEGS W2 c2 (sbd_B_end g pos).
(* C: 0x836e8 -> ret, the release (aj_flag_store_pi), the epilogue, and the post. *)
Definition seg_sbd_C : Prop :=
  forall g pos W2 c2, sbd_pre g -> sbd_B_end g pos W2 c2 ->
  SRr SEGS W2 c2 (tsb_dec_post B (sq_STK g) (sq_sp0 g) (sq_FP g) (sq_ly g) (sq_S g) (sq_W0 g) (sq_mem0 g)
    (sq_md0 g) (sq_own g) (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) (sq_k g) (sq_regs g)
    (sq_b g) (sq_v g) (sq_md g) (sq_p g) (sq_cap g) (sq_n g) (sq_ov g)).

(* ---- the composition --------------------------------------------------------------------------------------- *)
Lemma pb_sb_dec_of_segs : seg_sbd_A -> seg_sbd_B -> seg_sbd_C -> tsb_dec_spec B.
Proof.
intros HA HB HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30
  H31 H32.
pose (g := mkSbd STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov).
assert (Hpre : sbd_pre g)
  by (unfold sbd_pre, g; cbn [sq_STK sq_sp0 sq_FP sq_ly sq_S sq_W0 sq_mem0 sq_md0 sq_own sq_lyc sq_Sc sq_W
        sq_memc sq_mdc sq_k sq_regs sq_b sq_v sq_md sq_p sq_cap sq_n sq_ov];
      repeat (split; [assumption|]); assumption).
apply (SRr_bind SEGS _ _ _ _ (HA g Hpre)). intros W2 c2 _ (pos & HAe).
apply (SRr_bind SEGS _ _ _ _ (HB g pos W2 c2 Hpre HAe)). intros W3 c3 _ HBe.
exact (HC g pos W3 c3 Hpre HBe).
Qed.
End h.
End f.
End d.
