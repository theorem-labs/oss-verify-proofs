(* check_text_counter (fuzz_codec.c:468-490; image A 0x83b5c, 167 instructions): the boundary layer of its
   image-A walk against lib/A/Prog/CPgChkC.v's cdc_check_text_counter_specX. The walk is cut once, at 0x83ce0,
   where both result paths meet; the cut is a concrete state (registers and the bytes the rest of the walk reads),
   so the last segment (check_text_counter_A_E.v) starts from a fresh symbolic state.

   The code (from the neutral listing of the pinned image):
     0x83b5c..0x83ba0  the real frame of 160 bytes, the twelve saves at entry sp - 8 .. entry sp - 104, s0 = entry
                       sp, sp = s1 = sp1 = (entry sp - 160) & -32; s3 = dots, s4 = seg, s5 = text
     0x83bac..0x83bc8  the .got loads of the use-after-return cell and of the shadow offset (s8 = SB); the cell
                       holds 1, so the frame request at 0x83bd0 (class 0, 64 bytes) is taken
     0x83bd4..0x83c6c  s2 = s9 = F (the frame; F is at least 4096, so the real-stack fallback 0x83be8 is not
                       reached), sd F at sp1 + 40, the frame header F[0..24), s10 = SB + F / 8, the frame's shadow
                       f1 f1 f1 f1 00 f3 f3 f3, the want dots byte sp1 + 55 := 0, sd F + 32 at sp1 + 24
     0x83c70           owed_counter_text(text, F + 32, sp1 + 55)
     0x83c74..0x83c88  s7 = its rc, s6 = 0xa5, __asan_memset(seg, 0xa5, 24)
     0x83c8c..0x83cac  s11 = SB + dots / 8, the checked store dots := 0xa5,
                       diginet_counter_text(text, seg, dots)
     0x83cb0..0x83cdc  rc against s7 (abort when they differ); when both are 0, the bcmp wrapper on seg and
                       F + 32 over 8 bytes and the checked load of dots against sp1 + 55 (abort on a difference)
                                                                                     -> cut C5 at 0x83ce0
     0x83ce0..0x83d24  the checked loop over seg + 8 .. seg + 24 (abort on a byte other than 0xa5)
     0x83d28..0x83dcc  the frame's shadow byte 4 := f8, F[0] := 0x45e0360e, the shadow := f5 x 8, the flag byte
                       through the word at F + 56 := 0 (the release), the epilogue, ret.
   The cut carries the caller's journal with own (0, pos) :: own, what the call has kept of its entry state
   (tcj_kept, window T_check_text_counter below the entry sp, write set seg[0..24) and the dots byte), the
   blocks of the entry state, the meter, the input, and the registers and saves below (ctc_common). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition CTC_A : Z := 0x83b5c.
Definition CTC_C5 : Z := 0x83ce0.
(* The realigned sp: 0x83b5c addi sp,sp,-160 then 0x83b9c andi sp,sp,-32. *)
Definition ctc_sp1 (sp : Z) : Z := 32 * ((sp - 160) / 32).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* the contract's variables *)
Record ctc_ctx : Type := mkCtc {
  x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z); x_ly : alayout; x_S : astate; x_W0 : world tfibsegs;
  x_mem0 : word -> option byte; x_md0 : Model; x_own : list (Z * Z);
  x_lyc : alayout; x_Sc : astate; x_W : world tfibsegs; x_memc : word -> option byte; x_mdc : Model; x_k : Z;
  x_regs : bvmap 5 word; x_q : Z; x_sg : Z; x_dt : Z; x_tb : list Z; x_sj : list Z; x_dj : Z }.
Definition x_sp (g : ctc_ctx) : Z := spZ (x_regs g).
Definition x_F (g : ctc_ctx) (pos : Z) : Z := frame_addr (x_lyc g) 0 pos.
Definition x_FL (g : ctc_ctx) (pos : Z) : Z := flag_addr (x_lyc g) 0 pos.
(* the bytes the call may write, and its result *)
Definition ctc_E (g : ctc_ctx) : Z -> Prop := fun x => x_sg g <= x < x_sg g + 24 \/ x_dt g <= x < x_dt g + 1.
Definition ctc_R (g : ctc_ctx) : world tfibsegs -> (word -> option byte) -> bvmap 5 word -> Prop :=
  fun W2 mem2 regs2 =>
    exists s' d', garr8 tfibsegs (rd W2 mem2) (x_sg g) (s' ++ repeat 0xa5 16) /\ length s' = 8%nat /\
                  val_mem tfibsegs (rd W2 mem2) (x_dt g) 1 d'.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA PERSA : Z.
Variable ROSTRS : list (Z * Z).

(* cdc_check_text_counter_specX's premises, in its order, at image A's read window *)
Definition ctc_pre (g : ctc_ctx) : Prop :=
  cdc_entry tfibsegs B (x_STK g) (x_sp0 g) (x_FP g) (x_ly g) (x_S g) (x_W0 g) (x_mem0 g) (x_md0 g) (x_own g)
    (x_lyc g) (x_Sc g) (x_W g) (x_memc g) (x_mdc g) (x_k g) (x_regs g) T_check_text_counter /\
  getr (x_regs g) 10 = w64 (x_q g) /\
  cstr_rd tfibsegs (x_W g) (x_memc g) (x_sp g) T_check_text_counter (x_q g) (x_tb g) /\
  cobj_ok B (x_lyc g) (x_Sc g) (x_q g) (Z.of_nat (length (x_tb g))) /\
  cobj_ok B (x_lyc g) (x_Sc g) (x_sg g) 24 /\ cobj_ok B (x_lyc g) (x_Sc g) (x_dt g) 1 /\
  getr (x_regs g) 11 = w64 (x_sg g) /\
  cdst_ok tfibsegs B (x_STK g) (x_sp0 g) (x_FP g) (x_ly g) (x_S g) (x_lyc g) (x_Sc g) (x_own g) (x_W g) (x_memc g)
    (x_sp g) T_check_text_counter (x_sg g) 24 /\
  garr8 tfibsegs (rd (x_W g) (x_memc g)) (x_sg g) (x_sj g) /\ length (x_sj g) = 24%nat /\
  getr (x_regs g) 12 = w64 (x_dt g) /\
  cdst_ok tfibsegs B (x_STK g) (x_sp0 g) (x_FP g) (x_ly g) (x_S g) (x_lyc g) (x_Sc g) (x_own g) (x_W g) (x_memc g)
    (x_sp g) T_check_text_counter (x_dt g) 1 /\
  val_mem tfibsegs (rd (x_W g) (x_memc g)) (x_dt g) 1 (x_dj g) /\
  (x_sg g + 24 <= x_dt g \/ x_dt g + 1 <= x_sg g) /\
  (x_q g + Z.of_nat (length (x_tb g)) <= x_sg g \/ x_sg g + 24 <= x_q g) /\
  (x_q g + Z.of_nat (length (x_tb g)) <= x_dt g \/ x_dt g + 1 <= x_q g) /\
  cimg_rd tfibsegs B CA_RLO CA_RHI (x_W g) (x_memc g) (x_sp g) T_check_text_counter
    ((SEG7TBL, 364) :: (GLYPHA, 464) :: ROSTRS) /\
  (let '(r1, s1, d1) := counter_text_spec (x_tb g) in
   let '(r2, s2, d2) := owed_counter_text_spec (x_tb g) in
   r1 = r2 /\ (r1 = 0 -> s1 = s2 /\ d1 = d2)) /\
  Z.of_nat (length (frames (x_Sc g))) <= 6.
Definition ctc_post (g : ctc_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (x_STK g) (x_sp0 g) (x_FP g) (x_ly g) (x_S g) (x_W0 g) (x_mem0 g) (x_md0 g) (x_own g)
    (x_k g) (x_regs g) T_check_text_counter (ctc_E g) (x_lyc g) (x_Sc g) (x_W g) (x_memc g) (x_mdc g) (ctc_R g).

(* What every cut after the frame request carries: sp = s1 = sp1, s0 = the entry sp, s2 = s9 = F,
   s10 = SB + F / 8, s8 = SB, s3 = dots, s4 = seg, s5 = text, gp and tp untouched; the twelve saves (0x83b64..
   0x83b94) the epilogue (0x83d94..0x83dc4) reads back; the flag word at F + 56 (0x83d64 reads it). *)
Definition ctc_common (g : ctc_ctx) (pos : Z) (W2 : world tfibsegs) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) : Prop :=
  getr regs2 2 = w64 (ctc_sp1 (x_sp g)) /\ getr regs2 9 = w64 (ctc_sp1 (x_sp g)) /\ getr regs2 8 = w64 (x_sp g) /\
  getr regs2 3 = getr (x_regs g) 3 /\ getr regs2 4 = getr (x_regs g) 4 /\
  getr regs2 18 = w64 (x_F g pos) /\ getr regs2 19 = w64 (x_dt g) /\ getr regs2 20 = w64 (x_sg g) /\
  getr regs2 21 = w64 (x_q g) /\ getr regs2 24 = w64 SB /\ getr regs2 25 = w64 (x_F g pos) /\
  getr regs2 26 = w64 (SB + x_F g pos / 8) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 8) 8 (raZ (x_regs g)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 16) 8 (bv_unsigned (getr (x_regs g) 8)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 24) 8 (bv_unsigned (getr (x_regs g) 9)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 32) 8 (bv_unsigned (getr (x_regs g) 18)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 40) 8 (bv_unsigned (getr (x_regs g) 19)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 48) 8 (bv_unsigned (getr (x_regs g) 20)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 56) 8 (bv_unsigned (getr (x_regs g) 21)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 64) 8 (bv_unsigned (getr (x_regs g) 22)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 72) 8 (bv_unsigned (getr (x_regs g) 23)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 80) 8 (bv_unsigned (getr (x_regs g) 24)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 88) 8 (bv_unsigned (getr (x_regs g) 25)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 96) 8 (bv_unsigned (getr (x_regs g) 26)) /\
  val_mem tfibsegs (rd W2 mem2) (x_sp g - 104) 8 (bv_unsigned (getr (x_regs g) 27)) /\
  rdword (aview tfibsegs (w_H W2) mem2) (x_F g pos + fs_frame_bytes 0 - 8) = Some (x_FL g pos).

(* A cut at pc: the caller's journal with own (0, pos) :: own and k events, what the call has kept of its entry
   state, the blocks of the entry state, the frame fresh at entry, the meter and the input, the common part,
   and P. *)
Definition ctc_cut (g : ctc_ctx) (pos pc : Z)
  (P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
    ajournal tfibsegs B (x_STK g) (x_sp0 g) (x_FP g) (x_ly g) (x_S g) (x_W0 g) (x_mem0 g) (x_md0 g)
      ((0, pos) :: x_own g) ly2 S2 W2 mem2 md2 (x_k g) /\
    tcj_kept tfibsegs B T_check_text_counter (x_lyc g) (x_Sc g) (x_W g) (x_memc g) W2 mem2 (x_sp g) (ctc_E g) /\
    Permutation (ablocks B ly2 S2) (ablocks B (x_lyc g) (x_Sc g)) /\ ~ In (0, pos) (frames (x_Sc g)) /\
    mo_le MT (x_Sc g) S2 0 /\ same_io (x_mdc g) md2 /\
    ctc_common g pos W2 regs2 mem2 /\
    P ly2 S2 W2 regs2 mem2 md2.

(* C5 (0x83ce0, the loop head reached from both rc paths): seg's first eight bytes are the library's digits (or
   what a failed call left there), the sixteen after them hold the 0xa5 of the memset, dots holds a byte, and the
   sixteen bytes the loop reads are marked usable. *)
Definition ctc_P5 (g : ctc_ctx) : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly2 S2 W2 regs2 mem2 md2 =>
    exists s' d', garr8 tfibsegs (rd W2 mem2) (x_sg g) s' /\ length s' = 8%nat /\
      garr8 tfibsegs (rd W2 mem2) (x_sg g + 8) (repeat 0xa5 16) /\
      val_mem tfibsegs (rd W2 mem2) (x_dt g) 1 d' /\
      range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (x_sg g + 8) 16.

(* E: C5 -> ret, the loop, the release and the post. *)
Definition seg_ctc_E : Prop :=
  forall g pos W2 c2, ctc_pre g -> ctc_cut g pos CTC_C5 (ctc_P5 g) W2 c2 -> SRr tfibsegs W2 c2 (ctc_post g).
End d.
End b.
