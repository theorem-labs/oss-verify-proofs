(* The boundary layer of diginet_counter_text's walk in image A (fuzz_codec.asan 0x86120, 314 instructions): the
   state at each segment boundary, the statement of each segment lemma, and their composition into
   cdc_counter_text_specX (proved here, by induction over the two loops). The segments are proved against these
   statements in diginet_counter_text_A_<seg>.v.

   The code (listing nd/A/diginet_counter_text.fuzz_codec.asan.s):
   S0  0x86120 .. 0x862a4 / 0x863d8: real frame 160 (13 saves, `sd zero,0(sp)`), s0 = entry sp, sp = s1 =
       32 * ((sp - 160) / 32); the cell 0x9db68 (it holds 1) and the shadow offset through 0x9db10; the class-1
       side-stack frame request (a0 = 128, jal 0x3d270 at 0x86194); the spills 48(s1), 16(s1), 24(s1) = F; the frame
       header F[0..24); the frame's 16 shadow bytes f1 f1 f1 f1 00 f2 f2 f2 00 00 00 00 f3 f3 f3 f3; __asan_memset
       (F + 64, 0, 32) at 0x86254; 8(s1) = dt; the null tests of q, sg, dt (not taken); the first text byte; to the
       loop-1 head 0x862a4, or (empty text) to the loop-2 head 0x863d8 with n = 0.
   L1  0x862a4 .. : one text byte per pass: a dot after a digit sets dot[n - 1]; else diginet_seg7 (0x862e0) of the
       byte (a dot draws as ' '), E_RANGE (to 0x864c0, a0 = -11) on a negative pattern or a ninth digit, else s[n]
       := pattern (and dot[n] := 1 for a dot), n := n + 1; then the next text byte: 0 leaves the loop with
       s11 := n - 8 (to 0x863d8), else back to 0x862a4.
   L2  0x863d8 .. : digit i of 8 (k = 8 - i left): seg[i] := s[n - 8 + i] or 0; a dot on digit 7 is E_RANGE (0x864bc,
       to 0x864c0); a dot on digit i < 7 sets bit i of the dots; after digit 7 *dt := dots, a0 := 0 (0x8649c .. 0x864b8,
       to 0x864c0).
   X   0x864c0 .. ret: the frame's variables' shadow := f8, F[0] := 0x45e0360e, the frame's shadow := f5 (x16), the
       flag byte (through the word at F + 120) := 0: the release; the epilogue, ret; then the contract's post.

   Each boundary is a predicate on the configuration (sb_dec_inv.v's form in the released fuzz_identity tree): the
   caller's journal extended by the frame (own (1, pos) :: own), what the call has kept of its entry state
   (tcj_kept against the entry state, window T_counter_text below the entry sp, write set seg[0..8) and dt), the
   heap blocks as at entry, the registers and memory every boundary carries (ct_common), and the boundary's own
   facts. A segment builds its own symbolic state from these facts.

   The text, seg, dt and the seg7 table are read after the frame request. Their facts at a boundary state are
   ct_now, a premise of every segment: the closing theorem derives it from the contract's premises, so a change of
   those premises touches only that derivation. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgChkC CPgWalk CPgWalkKept.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The boundaries' addresses. *)
Definition A_CT : Z := 0x86120.     (* diginet_counter_text *)
Definition A_SEG7 : Z := 0x860b4.   (* diginet_seg7 *)
Definition PC_L1 : Z := 0x862a4.    (* zext.b s8,a1: the loop-1 head *)
Definition PC_L2 : Z := 0x863d8.    (* addw a6,s11,a3: the loop-2 head *)
Definition PC_X : Z := 0x864c0.     (* li a1,-8: the exit *)
(* The frame's 16 shadow bytes after 0x86200 .. 0x86244 (s[8] at F + 32 and dot[8] at F + 64 are its variables). *)
Definition CT_FRAME_SHADOW : list Z := [241; 241; 241; 241; 0; 242; 242; 242; 0; 0; 0; 0; 243; 243; 243; 243].

(* The first loop's facts over its Gallina state: n digits placed, s their patterns, dot the 8 flags. *)
Definition ct_l1 (n : Z) (s dot : list Z) : Prop :=
  ct_inv n dot /\ Forall (fun x => 0 <= x <= 1) dot /\ length s = Z.to_nat n /\ Forall (fun v => 0 <= v < 128) s.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.

(* ---- the call: cdc_counter_text_specX's variables ------------------------------------------------------------ *)
Record ct_ctx : Type := mkCt {
  cg_STK : Z; cg_sp0 : Z; cg_FP : list (Z * Z); cg_ly : alayout; cg_S : astate; cg_W0 : world tfibsegs;
  cg_mem0 : word -> option byte; cg_md0 : Model; cg_own : list (Z * Z);
  cg_lyc : alayout; cg_Sc : astate; cg_W : world tfibsegs; cg_memc : word -> option byte; cg_mdc : Model; cg_k : Z;
  cg_regs : bvmap 5 word; cg_q : Z; cg_sg : Z; cg_dt : Z; cg_tb : list Z; cg_sj : list Z; cg_dj : Z }.
(* The entry sp, the realigned sp of 0x86160, the text's length, the class-1 frame and its flag byte, the write set. *)
Definition cg_sp (g : ct_ctx) : Z := spZ (cg_regs g).
Definition cg_sp1 (g : ct_ctx) : Z := 32 * ((cg_sp g - 160) / 32).
Definition cg_len (g : ct_ctx) : Z := Z.of_nat (length (cg_tb g)).
Definition cg_F (g : ct_ctx) (pos : Z) : Z := frame_addr (cg_lyc g) 1 pos.
Definition cg_FL (g : ct_ctx) (pos : Z) : Z := flag_addr (cg_lyc g) 1 pos.
Definition ct_wr (g : ct_ctx) : Z -> Prop := fun x => cg_sg g <= x < cg_sg g + 8 \/ cg_dt g <= x < cg_dt g + 1.

(* The contract's premises the walk takes as they are, in the contract's order (the text's, seg's, dt's and the
   seg7 table's facts after the frame request are ct_now). *)
Definition ct_pre (g : ct_ctx) : Prop :=
  cdc_entry tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    (cg_own g) (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g) (cg_k g) (cg_regs g) T_counter_text /\
  getr (cg_regs g) 10 = w64 (cg_q g) /\
  cstr_rd tfibsegs (cg_W g) (cg_memc g) (cg_sp g) T_counter_text (cg_q g) (cg_tb g) /\
  getr (cg_regs g) 11 = w64 (cg_sg g) /\
  cdst_ok tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_lyc g) (cg_Sc g) (cg_own g)
    (cg_W g) (cg_memc g) (cg_sp g) T_counter_text (cg_sg g) 8 /\
  garr8 tfibsegs (rd (cg_W g) (cg_memc g)) (cg_sg g) (cg_sj g) /\ length (cg_sj g) = 8%nat /\
  getr (cg_regs g) 12 = w64 (cg_dt g) /\
  cdst_ok tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_lyc g) (cg_Sc g) (cg_own g)
    (cg_W g) (cg_memc g) (cg_sp g) T_counter_text (cg_dt g) 1 /\
  val_mem tfibsegs (rd (cg_W g) (cg_memc g)) (cg_dt g) 1 (cg_dj g) /\
  (cg_sg g + 8 <= cg_dt g \/ cg_dt g + 1 <= cg_sg g) /\
  (cg_q g + cg_len g <= cg_sg g \/ cg_sg g + 8 <= cg_q g) /\
  (cg_q g + cg_len g <= cg_dt g \/ cg_dt g + 1 <= cg_q g) /\
  Z.of_nat (length (frames (cg_Sc g))) <= 8.

(* The facts of the text, seg, dt and the seg7 table at a state the walk reaches after its frame request: the
   caller's journal with the frame, what the call kept, the blocks as at entry. *)
Definition ct_now (g : ct_ctx) : Prop :=
  forall pos ly2 S2 (W2 : world tfibsegs) mem2 md2,
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  tcj_kept tfibsegs B T_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ~ In (1, pos) (frames (cg_Sc g)) ->
  (garr8 tfibsegs (rd W2 mem2) (cg_q g) (cg_tb g) /\
   range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_q g) (cg_len g)) /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_sg g) 8 /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_dt g) 1 /\
  (arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W2) mem2) /\
   (forall i, 0 <= i < 364 -> in_roP tfibsegs RLO RHI (SEG7TBL + i)) /\
   crd_ok tfibsegs W2 mem2 (cg_sp1 g) T_seg7 SEG7TBL 364).

(* The contract's premises from which ct_now is derived: the text, seg and dt each in one object of the entry
   state, and the seg7 table's range of the image. *)
Definition ct_pre2 (g : ct_ctx) : Prop :=
  cobj_ok B (cg_lyc g) (cg_Sc g) (cg_q g) (cg_len g) /\ cobj_ok B (cg_lyc g) (cg_Sc g) (cg_sg g) 8 /\
  cobj_ok B (cg_lyc g) (cg_Sc g) (cg_dt g) 1 /\
  cimg_rd tfibsegs B RLO RHI (cg_W g) (cg_memc g) (cg_sp g) T_counter_text [(SEG7TBL, 364)].

(* ---- what every boundary carries --------------------------------------------------------------------------------
   0x8615c addi s0,sp,160 (s0 = entry sp); 0x86160 andi sp,sp,-32 / 0x86164 mv s1,sp (sp = s1 = sp1); x3, x4 never
   written; 0x861dc / 0x861fc s7 = SB + F / 8 (F >> 3 plus the shadow offset); 0x86184 s9 = SB; the thirteen saves
   at entry sp - 8 .. entry sp - 104 (0x86128 .. 0x86158), read back by the epilogue (0x86584 .. 0x865b4); the spills
   8(s1) = dt (0x8626c, read at 0x8649c), 16(s1) = 24(s1) = F (0x8625c / 0x86260, read at 0x864e8 / 0x864e0); the
   frame's flag word at F + 120 (read at 0x86534); the frame's shadow as 0x86200 .. 0x86244 write it. *)
Definition ct_common (g : ct_ctx) (pos : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (W2 : world tfibsegs)
  : Prop :=
  getr regs2 8 = w64 (cg_sp g) /\ getr regs2 2 = w64 (cg_sp1 g) /\ getr regs2 9 = w64 (cg_sp1 g) /\
  getr regs2 3 = getr (cg_regs g) 3 /\ getr regs2 4 = getr (cg_regs g) 4 /\
  getr regs2 23 = w64 (SB + cg_F g pos / 8) /\ getr regs2 25 = w64 SB /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 8) 8 (raZ (cg_regs g)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 16) 8 (bv_unsigned (getr (cg_regs g) 8)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 24) 8 (bv_unsigned (getr (cg_regs g) 9)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 32) 8 (bv_unsigned (getr (cg_regs g) 18)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 40) 8 (bv_unsigned (getr (cg_regs g) 19)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 48) 8 (bv_unsigned (getr (cg_regs g) 20)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 56) 8 (bv_unsigned (getr (cg_regs g) 21)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 64) 8 (bv_unsigned (getr (cg_regs g) 22)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 72) 8 (bv_unsigned (getr (cg_regs g) 23)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 80) 8 (bv_unsigned (getr (cg_regs g) 24)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 88) 8 (bv_unsigned (getr (cg_regs g) 25)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 96) 8 (bv_unsigned (getr (cg_regs g) 26)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp g - 104) 8 (bv_unsigned (getr (cg_regs g) 27)) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp1 g + 8) 8 (cg_dt g) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp1 g + 16) 8 (cg_F g pos) /\
  val_mem tfibsegs (rd W2 mem2) (cg_sp1 g + 24) 8 (cg_F g pos) /\
  rdword (aview tfibsegs (w_H W2) mem2) (cg_F g pos + 120) = Some (cg_FL g pos) /\
  garr8 tfibsegs (rd W2 mem2) (SB + cg_F g pos / 8) CT_FRAME_SHADOW.

(* s[0..n) at F + 32 (bytes) and dot[0..8) at F + 64 (4-byte words). *)
Definition ct_arrays (g : ct_ctx) (pos : Z) (W2 : world tfibsegs) (mem2 : word -> option byte) (n : Z) (s dot : list Z)
  : Prop :=
  (forall i, 0 <= i < 8 -> val_mem tfibsegs (rd W2 mem2) (cg_F g pos + 64 + 4 * i) 4 (nth (Z.to_nat i) dot 0)) /\
  (forall i, 0 <= i < n -> val_mem tfibsegs (rd W2 mem2) (cg_F g pos + 32 + i) 1 (nth (Z.to_nat i) s 0)).

(* A boundary: at pc, the caller's journal with own (1, pos) :: own and k events, what the call has kept of its
   entry state, the heap blocks as at entry, the frame new, the model's input and the meter, the common part,
   and P. *)
Definition ct_cut (g : ct_ctx) (pos pc : Z)
  (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> world tfibsegs -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
    ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
      ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) /\
    tcj_kept tfibsegs B T_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) /\
    Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) /\ ~ In (1, pos) (frames (cg_Sc g)) /\
    same_io (cg_mdc g) md2 /\ mo_le MT (cg_Sc g) S2 0 /\
    ct_common g pos regs2 mem2 W2 /\
    P ly2 S2 regs2 mem2 md2 W2.

(* The loop-1 head 0x862a4: a1 = ch = tb[j] (the byte read last, not 0), s3 = s6 = q + j + 1 (the next byte's
   address), s2 = 46, s4 = sg, s5 = F + 64 (dot), s10 = F + 32 (s), s11 = n. The bytes tb[0..j] are not 0; the
   first loop over the bytes from j on, from (n, s, dot), gives the result of the whole first loop. seg and dt are
   as at entry. fuel bounds the bytes left. *)
Definition P_L1 (g : ct_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (j n ch : Z) (s dot : list Z),
    getr regs2 11 = w64 ch /\ getr regs2 18 = w64 46 /\
    getr regs2 19 = w64 (cg_q g + j + 1) /\ getr regs2 22 = w64 (cg_q g + j + 1) /\
    getr regs2 20 = w64 (cg_sg g) /\ getr regs2 21 = w64 (cg_F g pos + 64) /\
    getr regs2 26 = w64 (cg_F g pos + 32) /\ getr regs2 27 = w64 n /\
    0 <= j /\ (Z.to_nat (cg_len g - j) <= fuel)%nat /\
    nth (Z.to_nat j) (cg_tb g) 0 = ch /\ ch <> 0 /\ Forall (fun x => x <> 0) (firstn (S (Z.to_nat j)) (cg_tb g)) /\
    ct1_lib (skipn (Z.to_nat j) (cg_tb g)) n s dot = ct1_lib (cg_tb g) 0 [] (repeat 0 8) /\
    ct_l1 n s dot /\ ct_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (cg_sg g) (cg_sj g) /\ val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g).

(* The loop-2 head 0x863d8, digit i (kk = 8 - i digits left): a0 = s4 = sg + i, a2 = the dots so far, a3 = i,
   a4 = 8 - i, a5 = 1, s5 = F + 64, s10 = F + 32, s11 = n - 8. The second loop from digit i gives the result;
   seg[0..i) holds the digits so far, seg[i..8) and dt are as at entry. *)
Definition P_L2 (g : ct_ctx) (pos : Z) (kk : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i n d : Z) (s dot sacc : list Z),
    getr regs2 10 = w64 (cg_sg g + i) /\ getr regs2 20 = w64 (cg_sg g + i) /\
    getr regs2 12 = w64 d /\ getr regs2 13 = w64 i /\ getr regs2 14 = w64 (8 - i) /\ getr regs2 15 = w64 1 /\
    getr regs2 21 = w64 (cg_F g pos + 64) /\ getr regs2 26 = w64 (cg_F g pos + 32) /\
    getr regs2 27 = w64 (n - 8) /\
    Z.of_nat kk = 8 - i /\ 0 <= i < 8 /\
    counter_text_spec (cg_tb g) = ct2_go n s dot i kk sacc d /\
    ct_l1 n s dot /\ length sacc = Z.to_nat i /\ Forall (fun v => 0 <= v < 128) sacc /\ 0 <= d < 128 /\
    ct_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (cg_sg g) (sacc ++ skipn (Z.to_nat i) (cg_sj g)) /\
    val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g).

(* What the contract's post asks of the result, at a memory. *)
Definition ct_res (g : ct_ctx) (W2 : world tfibsegs) (mem2 : word -> option byte) (regs2 : bvmap 5 word) : Prop :=
  let '(r, s, d) := counter_text_spec (cg_tb g) in
  getr regs2 10 = w64 r /\
  (r = 0 -> garr8 tfibsegs (rd W2 mem2) (cg_sg g) s /\ val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 d) /\
  (r <> 0 -> exists s' d', garr8 tfibsegs (rd W2 mem2) (cg_sg g) s' /\ length s' = 8%nat /\
                           val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 d').

(* The exit 0x864c0: a0 is the spec's code, seg and dt as the post states them. *)
Definition P_X (g : ct_ctx) : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => ct_res g W2 mem2 regs2.

(* The contract's post. *)
Definition ct_post (g : ct_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    (cg_own g) (cg_k g) (cg_regs g) T_counter_text (ct_wr g) (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g)
    (fun W2 mem2 regs2 => ct_res g W2 mem2 regs2).

(* ---- the segments ------------------------------------------------------------------------------------------------ *)
(* S0: entry -> the loop-1 head (first byte not 0) or the loop-2 head (empty text). *)
Definition ct_seg_S0 : Prop :=
  forall g, ct_pre g -> ct_now g ->
  SRr tfibsegs (cg_W g) (cfg_at tfibsegs A_CT (cg_regs g) (cg_memc g) (cg_mdc g))
    (fun W2 c2 => exists pos, ct_cut g pos PC_L1 (P_L1 g pos (length (cg_tb g))) W2 c2 \/
                              ct_cut g pos PC_L2 (P_L2 g pos 8) W2 c2).
(* L1: one pass of the first loop. *)
Definition ct_seg_L1 : Prop :=
  forall g pos fuel W2 c2, ct_pre g -> ct_now g -> ct_cut g pos PC_L1 (P_L1 g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => ct_cut g pos PC_L1 (P_L1 g pos fuel) W3 c3 \/
                                   ct_cut g pos PC_L2 (P_L2 g pos 8) W3 c3 \/ ct_cut g pos PC_X (P_X g) W3 c3).
(* L2: one digit of the second loop. *)
Definition ct_seg_L2 : Prop :=
  forall g pos kk W2 c2, ct_pre g -> ct_now g -> ct_cut g pos PC_L2 (P_L2 g pos (S kk)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => ct_cut g pos PC_L2 (P_L2 g pos kk) W3 c3 \/ ct_cut g pos PC_X (P_X g) W3 c3).
(* X: the release, the epilogue, the post. *)
Definition ct_seg_X : Prop :=
  forall g pos W2 c2, ct_pre g -> ct_now g -> ct_cut g pos PC_X (P_X g) W2 c2 -> SRr tfibsegs W2 c2 (ct_post g).

(* ---- the composition --------------------------------------------------------------------------------------------- *)
Lemma P_L2_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_L2 g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 (i & n & d & s & dot & sacc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & Hi & _).
cbn in Hk. lia.
Qed.
Lemma P_L1_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_L1 g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2
  (j & n & ch & s & dot & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hf & Hch & Hnz & _).
assert (Hlt : (Z.to_nat j < length (cg_tb g))%nat).
{ destruct (Nat.lt_ge_cases (Z.to_nat j) (length (cg_tb g))) as [H | H]; [exact H|].
  exfalso. apply Hnz. rewrite <- Hch. apply nth_overflow. exact H. }
unfold cg_len in Hf. lia.
Qed.
Lemma ct_cut_mono : forall g pos pc (P Q : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
  world tfibsegs -> Prop) W2 c2,
  (forall ly2 S2 regs2 mem2 md2 W2, P ly2 S2 regs2 mem2 md2 W2 -> Q ly2 S2 regs2 mem2 md2 W2) ->
  ct_cut g pos pc P W2 c2 -> ct_cut g pos pc Q W2 c2.
Proof.
intros g pos pc P Q W2 c2 HPQ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). apply HPQ. exact H9.
Qed.

Section comp.
Hypothesis HS0 : ct_seg_S0.
Hypothesis HL1 : ct_seg_L1.
Hypothesis HL2 : ct_seg_L2.
Hypothesis HX : ct_seg_X.
Lemma ct_L2_closed : forall kk g pos W2 c2, ct_pre g -> ct_now g -> ct_cut g pos PC_L2 (P_L2 g pos kk) W2 c2 ->
  SRr tfibsegs W2 c2 (ct_post g).
Proof.
induction kk as [|kk IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HP).
  exact (P_L2_zero g pos ly2 S2 regs2 mem2 md2 W2 HP).
- apply (SRr_bind tfibsegs _ _ _ _ (HL2 g pos kk W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (HX g pos W3 c3 Hpre Hnow H).
Qed.
Lemma ct_L1_closed : forall fuel g pos W2 c2, ct_pre g -> ct_now g -> ct_cut g pos PC_L1 (P_L1 g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (ct_post g).
Proof.
induction fuel as [|fuel IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HP).
  exact (P_L1_zero g pos ly2 S2 regs2 mem2 md2 W2 HP).
- apply (SRr_bind tfibsegs _ _ _ _ (HL1 g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | [H | H]].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (ct_L2_closed 8 g pos W3 c3 Hpre Hnow H).
  + exact (HX g pos W3 c3 Hpre Hnow H).
Qed.
Theorem ct_of_segs : forall g, ct_pre g -> ct_now g ->
  SRr tfibsegs (cg_W g) (cfg_at tfibsegs A_CT (cg_regs g) (cg_memc g) (cg_mdc g)) (ct_post g).
Proof.
intros g Hpre Hnow.
apply (SRr_bind tfibsegs _ _ _ _ (HS0 g Hpre Hnow)). intros W2 c2 _ (pos & [H | H]).
- exact (ct_L1_closed _ g pos W2 c2 Hpre Hnow H).
- exact (ct_L2_closed 8 g pos W2 c2 Hpre Hnow H).
Qed.
End comp.

(* The contract from the four segments and ct_now at every call. *)
Theorem ct_spec_of_segs : ct_seg_S0 -> ct_seg_L1 -> ct_seg_L2 -> ct_seg_X ->
  (forall g, ct_pre g -> ct_pre2 g -> ct_now g) ->
  cdc_counter_text_specX tfibsegs B MT RLO RHI SEG7TBL A_CT.
Proof.
intros HS0 HL1 HL2 HX HNOW.
unfold cdc_counter_text_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj
  H1 H2 H3 Hoq Hosg Hodt H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 Himg H16.
pose (g := mkCt STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj).
assert (Hpre : ct_pre g)
  by (unfold ct_pre, g, cg_sp, cg_len; cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc
        cg_W cg_memc cg_mdc cg_k cg_regs cg_q cg_sg cg_dt cg_tb cg_sj cg_dj];
      repeat (split; [assumption|]); assumption).
assert (Hpre2 : ct_pre2 g)
  by (unfold ct_pre2, g, cg_sp, cg_len; cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc
        cg_W cg_memc cg_mdc cg_k cg_regs cg_q cg_sg cg_dt cg_tb cg_sj cg_dj];
      repeat (split; [assumption|]); assumption).
exact (ct_of_segs HS0 HL1 HL2 HX g Hpre (HNOW g Hpre Hpre2)).
Qed.
End h.
End d.
