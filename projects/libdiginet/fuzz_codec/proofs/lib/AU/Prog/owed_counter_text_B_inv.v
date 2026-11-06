(* The boundary layer of owed_counter_text's walk in image B (fuzz_codec.asan-ubsan 0x84474, 320 instructions): the
   state at each segment boundary, the statement of each segment lemma, and their composition into
   cdcU_owed_counter_text_specX (proved here, by induction over the two loops). The segments are proved against these
   statements in owed_counter_text_B_<seg>.v. The form is lib/A/Prog/diginet_counter_text_A_inv.v's.

   The code (listing nd/B/owed_counter_text.fuzz_codec.asan-ubsan.s):
   S0  0x84474 .. 0x845d4: real frame 192 (13 saves at entry sp - 8 .. - 104, `sd zero,0(sp)`), s0 = entry sp,
       sp = s1 = 32 * ((sp - 192) / 32); 48(s1) := sg; the cell 0x9e488 (it holds 1) and the shadow offset through
       0x9e430 into s7; the class-1 side-stack frame request (a0 = 128, jal 0x3d3c0 at 0x844e8); a0 = F is not 0, so
       the machine-stack fallback 0x844fc .. 0x84514 is not reached; 40(s1) := dt, 32(s1) := F, 80(s1) := F,
       24(s1) := F; the frame header F[0..24); the frame's 16 shadow bytes f1 f1 f1 f1 00 f2 f2 f2 00 00 00 00
       f3 f3 f3 f3; __asan_memset (F + 64, 0, 32) at 0x845b4; s3 = 0, s11 = ~(F + 64), s2 = F + 32,
       56(s1) := ~(F + 32), s6 = q - 1, s8 = 46; to the loop-1 head 0x845d4.
   L1  0x845d4 .. : the byte t[i] at s4 (its check); 0 leaves the loop (0x84728); a dot after a digit whose dot is
       clear sets dot[n - 1] (0x845f4 .. 0x84624, 0x846bc .. 0x846cc); else owed_seg7 (0x84630) of the byte (a dot
       draws as ' '), E_RANGE (to 0x84840, a0 = -11) on a negative pattern or a ninth digit, else dot[n] := (byte is
       '.'), s[n] := pattern, n := n + 1; s4, s6 advance (0x846a8 .. 0x846b4) and back to 0x845d4. The text end
       0x84728 .. 0x84760: the check of dt, *dt := 0, a3 = a4 = 0, a5 = 8, a6 = ~sg, a7 = 7, t0 = 8 - n, t1 = 1; to
       the loop-2 head 0x84764.
   L2  0x84764 .. : digit i of 8: seg[i] := s[i - (8 - n)] or 0; a dot on digit 7 is E_RANGE (0x8483c, to 0x84840);
       a dot on digit i < 7 sets bit i of *dt (0x847e0 .. 0x847f8); after digit 7, a0 := 0 (0x84834, to 0x84840).
   X   0x84840 .. ret: the frame's variables' shadow := f8, F[0] := 0x45e0360e, 32(s1) = F is not 0 so the frame's
       shadow := f5 (x16) and the flag byte (through the word at F + 120) := 0: the release; the epilogue, ret; then
       the contract's post.
   The UBSan checks on the way (every branch to the trap at 0x84940) are shown not taken by each segment.

   Each boundary is a predicate on the configuration: the caller's journal extended by the frame
   (own (1, pos) :: own), what the call has kept of its entry state (tcj_kept against the entry state, window
   TB_owed_counter_text below the entry sp, write set seg[0..8) and dt), the heap blocks as at entry, the registers
   and memory every boundary carries (oc_common), and the boundary's own facts. A segment builds its own symbolic
   state from these facts. The text, seg, dt and the image tables are read after the frame request; their facts at
   a boundary state are oc_now, a premise of every segment, which the closing theorem derives from the contract's
   premises. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The boundaries' addresses. *)
Definition B_OCT : Z := 0x84474.    (* owed_counter_text *)
Definition B_OSEG7 : Z := 0x84a54.  (* owed_seg7 *)
Definition PC_L1 : Z := 0x845d4.    (* srli s9,s4,0x3: the loop-1 head *)
Definition PC_L2 : Z := 0x84764.    (* subw t2,a3,t0: the loop-2 head *)
Definition PC_X : Z := 0x84840.     (* li a1,-8: the exit *)
(* The frame's 16 shadow bytes after 0x84560 .. 0x845a4 (s[8] at F + 32 and dot[8] at F + 64 are its variables). *)
Definition OC_FRAME_SHADOW : list Z := [241; 241; 241; 241; 0; 242; 242; 242; 0; 0; 0; 0; 243; 243; 243; 243].

(* The first loop's facts over its Gallina state: n digits placed, s their patterns, dot the 8 flags. *)
Definition oc_l1 (n : Z) (s dot : list Z) : Prop :=
  ct_inv n dot /\ Forall (fun x => 0 <= x <= 1) dot /\ length s = Z.to_nat n /\ Forall (fun v => 0 <= v < 128) s.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).

(* ---- the call: cdcU_owed_counter_text_specX's variables -------------------------------------------------------- *)
Record oc_ctx : Type := mkOc {
  og_STK : Z; og_sp0 : Z; og_FP : list (Z * Z); og_ly : alayout; og_S : astate; og_W0 : world tfibsegs;
  og_mem0 : word -> option byte; og_md0 : Model; og_own : list (Z * Z);
  og_lyc : alayout; og_Sc : astate; og_W : world tfibsegs; og_memc : word -> option byte; og_mdc : Model; og_k : Z;
  og_regs : bvmap 5 word; og_q : Z; og_sg : Z; og_dt : Z; og_tb : list Z; og_sj : list Z; og_dj : Z }.
(* The entry sp, the realigned sp of 0x844b4, the text's length, the class-1 frame and its flag byte, the write set. *)
Definition og_sp (g : oc_ctx) : Z := spZ (og_regs g).
Definition og_sp1 (g : oc_ctx) : Z := 32 * ((og_sp g - 192) / 32).
Definition og_len (g : oc_ctx) : Z := Z.of_nat (length (og_tb g)).
Definition og_F (g : oc_ctx) (pos : Z) : Z := frame_addr (og_lyc g) 1 pos.
Definition og_FL (g : oc_ctx) (pos : Z) : Z := flag_addr (og_lyc g) 1 pos.
Definition oc_wr (g : oc_ctx) : Z -> Prop := fun x => og_sg g <= x < og_sg g + 8 \/ og_dt g <= x < og_dt g + 1.
(* the 64-bit complement ~x of an address (s11, 56(s1) and a6 hold them for the UBSan checks of an index) *)
Definition onot (x : Z) : Z := 2 ^ 64 - 1 - x.

(* The contract's premises the walk takes as they are, in the contract's order (the one-object premises of the text
   and seg and the image tables are oc_pre2; the facts of the text, seg, dt and the tables after the frame request
   are oc_now). *)
Definition oc_pre (g : oc_ctx) : Prop :=
  cdc_entry tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    (og_own g) (og_lyc g) (og_Sc g) (og_W g) (og_memc g) (og_mdc g) (og_k g) (og_regs g) TB_owed_counter_text /\
  getr (og_regs g) 10 = w64 (og_q g) /\
  cstr_rd tfibsegs (og_W g) (og_memc g) (og_sp g) TB_owed_counter_text (og_q g) (og_tb g) /\
  getr (og_regs g) 11 = w64 (og_sg g) /\
  cdst_ok tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_lyc g) (og_Sc g) (og_own g)
    (og_W g) (og_memc g) (og_sp g) TB_owed_counter_text (og_sg g) 8 /\
  garr8 tfibsegs (rd (og_W g) (og_memc g)) (og_sg g) (og_sj g) /\ length (og_sj g) = 8%nat /\
  getr (og_regs g) 12 = w64 (og_dt g) /\
  ((cdst_ok tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_lyc g) (og_Sc g) (og_own g)
      (og_W g) (og_memc g) (og_sp g) TB_owed_counter_text (og_dt g) 1 /\ cobj_ok B (og_lyc g) (og_Sc g) (og_dt g) 1) \/
   cdstk_ok tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_lyc g) (og_Sc g) (og_own g)
      (og_W g) (og_memc g) (og_sp g) TB_owed_counter_text (og_dt g) 1) /\
  val_mem tfibsegs (rd (og_W g) (og_memc g)) (og_dt g) 1 (og_dj g) /\
  (og_sg g + 8 <= og_dt g \/ og_dt g + 1 <= og_sg g) /\
  (og_q g + og_len g <= og_sg g \/ og_sg g + 8 <= og_q g) /\
  (og_q g + og_len g <= og_dt g \/ og_dt g + 1 <= og_q g) /\
  Z.of_nat (length (frames (og_Sc g))) <= 8.

(* The facts of the text, seg, dt and the image tables at a state the walk reaches after its frame request: the
   caller's journal with the frame, what the call kept, the blocks as at entry. *)
Definition oc_now (g : oc_ctx) : Prop :=
  forall pos ly2 S2 (W2 : world tfibsegs) mem2 md2,
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) -> ~ In (1, pos) (frames (og_Sc g)) ->
  (garr8 tfibsegs (rd W2 mem2) (og_q g) (og_tb g) /\
   range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (og_q g) (og_len g)) /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (og_sg g) 8 /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (og_dt g) 1 /\
  cimg_rd tfibsegs B RLO RHI W2 mem2 (og_sp1 g) TB_owed_seg7 ((GLYPHA, 464) :: ROSTRS).

(* The contract's premises from which oc_now is derived: the text and seg each in one object of the entry state,
   and the image tables. *)
Definition oc_pre2 (g : oc_ctx) : Prop :=
  cobj_ok B (og_lyc g) (og_Sc g) (og_q g) (og_len g) /\ cobj_ok B (og_lyc g) (og_Sc g) (og_sg g) 8 /\
  cimg_rd tfibsegs B RLO RHI (og_W g) (og_memc g) (og_sp g) TB_owed_counter_text ((GLYPHA, 464) :: ROSTRS).

(* ---- what every boundary carries --------------------------------------------------------------------------------
   0x844b0 addi s0,sp,192 (s0 = entry sp); 0x844b4 andi sp,sp,-32 / 0x844b8 mv s1,sp (sp = s1 = sp1); x3, x4 never
   written; s7 = SB (0x844d8); s10 = SB + F / 8 (0x8455c); s2 = F + 32, s5 = F + 64, s8 = 46, s11 = ~(F + 64)
   (0x845bc .. 0x845d0, none written after); the thirteen saves at entry sp - 8 .. entry sp - 104 (0x8447c ..
   0x844ac), read back by the epilogue (0x84904 .. 0x84934); the spills 24(s1) = 32(s1) = 80(s1) = F, 40(s1) = dt,
   48(s1) = sg, 56(s1) = ~(F + 32); the frame's flag word at F + 120 (read at 0x848b4); the frame's shadow as
   0x84560 .. 0x845a4 write it. *)
Definition oc_common (g : oc_ctx) (pos : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (W2 : world tfibsegs)
  : Prop :=
  getr regs2 8 = w64 (og_sp g) /\ getr regs2 2 = w64 (og_sp1 g) /\ getr regs2 9 = w64 (og_sp1 g) /\
  getr regs2 3 = getr (og_regs g) 3 /\ getr regs2 4 = getr (og_regs g) 4 /\
  getr regs2 23 = w64 SB /\ getr regs2 26 = w64 (SB + og_F g pos / 8) /\
  getr regs2 18 = w64 (og_F g pos + 32) /\ getr regs2 21 = w64 (og_F g pos + 64) /\
  getr regs2 24 = w64 46 /\ getr regs2 27 = w64 (onot (og_F g pos + 64)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 8) 8 (raZ (og_regs g)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 16) 8 (bv_unsigned (getr (og_regs g) 8)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 24) 8 (bv_unsigned (getr (og_regs g) 9)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 32) 8 (bv_unsigned (getr (og_regs g) 18)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 40) 8 (bv_unsigned (getr (og_regs g) 19)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 48) 8 (bv_unsigned (getr (og_regs g) 20)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 56) 8 (bv_unsigned (getr (og_regs g) 21)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 64) 8 (bv_unsigned (getr (og_regs g) 22)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 72) 8 (bv_unsigned (getr (og_regs g) 23)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 80) 8 (bv_unsigned (getr (og_regs g) 24)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 88) 8 (bv_unsigned (getr (og_regs g) 25)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 96) 8 (bv_unsigned (getr (og_regs g) 26)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp g - 104) 8 (bv_unsigned (getr (og_regs g) 27)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp1 g + 24) 8 (og_F g pos) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp1 g + 32) 8 (og_F g pos) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp1 g + 40) 8 (og_dt g) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp1 g + 48) 8 (og_sg g) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp1 g + 56) 8 (onot (og_F g pos + 32)) /\
  val_mem tfibsegs (rd W2 mem2) (og_sp1 g + 80) 8 (og_F g pos) /\
  rdword (aview tfibsegs (w_H W2) mem2) (og_F g pos + 120) = Some (og_FL g pos) /\
  garr8 tfibsegs (rd W2 mem2) (SB + og_F g pos / 8) OC_FRAME_SHADOW.

(* s[0..n) at F + 32 (bytes) and dot[0..8) at F + 64 (4-byte words). *)
Definition oc_arrays (g : oc_ctx) (pos : Z) (W2 : world tfibsegs) (mem2 : word -> option byte) (n : Z) (s dot : list Z)
  : Prop :=
  (forall i, 0 <= i < 8 -> val_mem tfibsegs (rd W2 mem2) (og_F g pos + 64 + 4 * i) 4 (nth (Z.to_nat i) dot 0)) /\
  (forall i, 0 <= i < n -> val_mem tfibsegs (rd W2 mem2) (og_F g pos + 32 + i) 1 (nth (Z.to_nat i) s 0)).

(* A boundary: at pc, the caller's journal with own (1, pos) :: own and k events, what the call has kept of its
   entry state, the heap blocks as at entry, the frame new, the model's input and the meter, the common part,
   and P. *)
Definition oc_cut (g : oc_ctx) (pos pc : Z)
  (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> world tfibsegs -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
    ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
      ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) /\
    tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) /\
    Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) /\ ~ In (1, pos) (frames (og_Sc g)) /\
    same_io (og_mdc g) md2 /\ mo_le MT (og_Sc g) S2 0 /\
    oc_common g pos regs2 mem2 W2 /\
    P ly2 S2 regs2 mem2 md2 W2.

(* The loop-1 head 0x845d4: n digits so far (s3), s4 = q + i (the next byte's address), s6 = q + i - 1. The bytes
   tb[0..i) are not 0; the first loop over the bytes from i on, from (n, s, dot), gives the result of the whole first
   loop. seg and dt are as at entry. fuel bounds the bytes left. *)
Definition P_L1 (g : oc_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i n : Z) (s dot : list Z),
    getr regs2 19 = w64 n /\ getr regs2 20 = w64 (og_q g + i) /\ getr regs2 22 = w64 (og_q g + i - 1) /\
    0 <= i /\ (Z.to_nat (og_len g - i) <= fuel)%nat /\
    Forall (fun x => x <> 0) (firstn (Z.to_nat i) (og_tb g)) /\
    ct1_owe (skipn (Z.to_nat i) (og_tb g)) n s dot = ct1_owe (og_tb g) 0 [] (repeat 0 8) /\
    oc_l1 n s dot /\ oc_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (og_sg g) (og_sj g) /\ val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 (og_dj g).

(* The loop-2 head 0x84764, digit i (kk = 8 - i digits left): a3 = a4 = i, a5 = 8, a6 = ~sg, a7 = 7, t0 = 8 - n,
   t1 = 1, a1 = the shadow byte address of dt, a2 = dt mod 8, s3 = n. The second loop from digit i gives the
   result; seg[0..i) holds the digits so far, seg[i..8) is as at entry, dt holds the dots so far. *)
Definition P_L2 (g : oc_ctx) (pos : Z) (kk : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i n d : Z) (s dot sacc : list Z),
    getr regs2 13 = w64 i /\ getr regs2 14 = w64 i /\ getr regs2 15 = w64 8 /\
    getr regs2 16 = w64 (onot (og_sg g)) /\ getr regs2 17 = w64 7 /\ getr regs2 5 = w64 (8 - n) /\
    getr regs2 6 = w64 1 /\ getr regs2 11 = w64 (SB + og_dt g / 8) /\ getr regs2 12 = w64 (og_dt g mod 8) /\
    getr regs2 19 = w64 n /\
    Z.of_nat kk = 8 - i /\ 0 <= i < 8 /\
    owed_counter_text_spec (og_tb g) = ct2_go n s dot i kk sacc d /\
    oc_l1 n s dot /\ length sacc = Z.to_nat i /\ Forall (fun v => 0 <= v < 128) sacc /\ 0 <= d < 128 /\
    oc_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (og_sg g) (sacc ++ skipn (Z.to_nat i) (og_sj g)) /\
    val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 d.

(* What the contract's post asks of the result, at a memory. *)
Definition oc_res (g : oc_ctx) (W2 : world tfibsegs) (mem2 : word -> option byte) (regs2 : bvmap 5 word) : Prop :=
  let '(r, s, d) := owed_counter_text_spec (og_tb g) in
  getr regs2 10 = w64 r /\
  (r = 0 -> garr8 tfibsegs (rd W2 mem2) (og_sg g) s /\ val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 d) /\
  (r <> 0 -> exists s' d', garr8 tfibsegs (rd W2 mem2) (og_sg g) s' /\ length s' = 8%nat /\
                           val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 d').

(* The exit 0x84840: a0 is the spec's code, seg and dt as the post states them. *)
Definition P_X (g : oc_ctx) : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => oc_res g W2 mem2 regs2.

(* The contract's post. *)
Definition oc_post (g : oc_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    (og_own g) (og_k g) (og_regs g) TB_owed_counter_text (oc_wr g) (og_lyc g) (og_Sc g) (og_W g) (og_memc g) (og_mdc g)
    (fun W2 mem2 regs2 => oc_res g W2 mem2 regs2).

(* ---- the segments ------------------------------------------------------------------------------------------------ *)
(* S0: entry -> the loop-1 head with no byte read. *)
Definition oc_seg_S0 : Prop :=
  forall g, oc_pre g -> oc_now g ->
  SRr tfibsegs (og_W g) (cfg_at tfibsegs B_OCT (og_regs g) (og_memc g) (og_mdc g))
    (fun W2 c2 => exists pos, oc_cut g pos PC_L1 (P_L1 g pos (length (og_tb g))) W2 c2).
(* L1: one pass of the first loop. *)
Definition oc_seg_L1 : Prop :=
  forall g pos fuel W2 c2, oc_pre g -> oc_now g -> oc_cut g pos PC_L1 (P_L1 g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => oc_cut g pos PC_L1 (P_L1 g pos fuel) W3 c3 \/
                                   oc_cut g pos PC_L2 (P_L2 g pos 8) W3 c3 \/ oc_cut g pos PC_X (P_X g) W3 c3).
(* L2: one digit of the second loop. *)
Definition oc_seg_L2 : Prop :=
  forall g pos kk W2 c2, oc_pre g -> oc_now g -> oc_cut g pos PC_L2 (P_L2 g pos (S kk)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => oc_cut g pos PC_L2 (P_L2 g pos kk) W3 c3 \/ oc_cut g pos PC_X (P_X g) W3 c3).
(* X: the release, the epilogue, the post. *)
Definition oc_seg_X : Prop :=
  forall g pos W2 c2, oc_pre g -> oc_now g -> oc_cut g pos PC_X (P_X g) W2 c2 -> SRr tfibsegs W2 c2 (oc_post g).

(* ---- the composition --------------------------------------------------------------------------------------------- *)
Lemma P_L2_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_L2 g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2
  (i & n & d & s & dot & sacc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & Hi & _).
cbn in Hk. lia.
Qed.
Lemma P_L1_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, oc_pre g -> P_L1 g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 Hpre (i & n & s & dot & _ & _ & _ & Hi & Hf & Hnz & _).
destruct Hpre as (_ & _ & (_ & _ & Hin0 & _) & _).
unfold og_len in Hf.
assert (Hge : (length (og_tb g) <= Z.to_nat i)%nat) by lia.
rewrite firstn_all2 in Hnz by exact Hge.
rewrite Forall_forall in Hnz. exact (Hnz 0 Hin0 eq_refl).
Qed.
Lemma oc_cut_mono : forall g pos pc (P Q : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
  world tfibsegs -> Prop) W2 c2,
  (forall ly2 S2 regs2 mem2 md2 W2, P ly2 S2 regs2 mem2 md2 W2 -> Q ly2 S2 regs2 mem2 md2 W2) ->
  oc_cut g pos pc P W2 c2 -> oc_cut g pos pc Q W2 c2.
Proof.
intros g pos pc P Q W2 c2 HPQ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). apply HPQ. exact H9.
Qed.

Section comp.
Hypothesis HS0 : oc_seg_S0.
Hypothesis HL1 : oc_seg_L1.
Hypothesis HL2 : oc_seg_L2.
Hypothesis HX : oc_seg_X.
Lemma oc_L2_closed : forall kk g pos W2 c2, oc_pre g -> oc_now g -> oc_cut g pos PC_L2 (P_L2 g pos kk) W2 c2 ->
  SRr tfibsegs W2 c2 (oc_post g).
Proof.
induction kk as [|kk IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HP).
  exact (P_L2_zero g pos ly2 S2 regs2 mem2 md2 W2 HP).
- apply (SRr_bind tfibsegs _ _ _ _ (HL2 g pos kk W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (HX g pos W3 c3 Hpre Hnow H).
Qed.
Lemma oc_L1_closed : forall fuel g pos W2 c2, oc_pre g -> oc_now g -> oc_cut g pos PC_L1 (P_L1 g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (oc_post g).
Proof.
induction fuel as [|fuel IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HP).
  exact (P_L1_zero g pos ly2 S2 regs2 mem2 md2 W2 Hpre HP).
- apply (SRr_bind tfibsegs _ _ _ _ (HL1 g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | [H | H]].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (oc_L2_closed 8 g pos W3 c3 Hpre Hnow H).
  + exact (HX g pos W3 c3 Hpre Hnow H).
Qed.
Theorem oc_of_segs : forall g, oc_pre g -> oc_now g ->
  SRr tfibsegs (og_W g) (cfg_at tfibsegs B_OCT (og_regs g) (og_memc g) (og_mdc g)) (oc_post g).
Proof.
intros g Hpre Hnow.
apply (SRr_bind tfibsegs _ _ _ _ (HS0 g Hpre Hnow)). intros W2 c2 _ (pos & H).
exact (oc_L1_closed _ g pos W2 c2 Hpre Hnow H).
Qed.
End comp.

(* The contract from the four segments and oc_now at every call. *)
Theorem oc_spec_of_segs : oc_seg_S0 -> oc_seg_L1 -> oc_seg_L2 -> oc_seg_X ->
  (forall g, oc_pre g -> oc_pre2 g -> oc_now g) ->
  cdcU_owed_counter_text_specX tfibsegs B MT RLO RHI GLYPHA ROSTRS B_OCT.
Proof.
intros HS0 HL1 HL2 HX HNOW.
unfold cdcU_owed_counter_text_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj
  H1 H2 H3 Hoq Hosg H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 Himg H16.
pose (g := mkOc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj).
assert (Hpre : oc_pre g)
  by (unfold oc_pre, g, og_sp, og_len; cbn [og_STK og_sp0 og_FP og_ly og_S og_W0 og_mem0 og_md0 og_own og_lyc og_Sc
        og_W og_memc og_mdc og_k og_regs og_q og_sg og_dt og_tb og_sj og_dj];
      repeat (split; [assumption|]); assumption).
assert (Hpre2 : oc_pre2 g)
  by (unfold oc_pre2, g, og_sp, og_len; cbn [og_STK og_sp0 og_FP og_ly og_S og_W0 og_mem0 og_md0 og_own og_lyc og_Sc
        og_W og_memc og_mdc og_k og_regs og_q og_sg og_dt og_tb og_sj og_dj];
      repeat (split; [assumption|]); assumption).
exact (oc_of_segs HS0 HL1 HL2 HX g Hpre (HNOW g Hpre Hpre2)).
Qed.
End h.
End d.
