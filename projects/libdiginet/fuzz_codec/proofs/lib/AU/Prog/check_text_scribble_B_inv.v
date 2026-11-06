(* The boundary layer of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc, 227 instructions,
   real frame 128, a side-stack frame of class 0): the state at each segment boundary, the statement of each segment
   lemma, and their composition into lib/AU/Prog/CPgChkU.v's cdcU_check_text_scribble_specX (by induction over the
   three loops). The segments are proved against these statements in check_text_scribble_B_<seg>.v.

   The code (neutral listing of image B):
   S0  0x83dbc .. 0x83ed0: the frame (`sd zero,0(sp)`, twelve saves at entry sp - 8 .. entry sp - 96), s0 = entry
       sp, sp = s1 = 32 * ((sp - 128) / 32); s3 = n, s4 = ch, s5 = q; the use-after-return cell (it holds 1) and the
       shadow offset s7 = SB through the .got; the class-0 side-stack frame request (a0 = 64, jal 0x3d24c at
       0x83e2c), s2 = s8 = F; the real-stack fallback 0x83e44 .. 0x83e5c is not reached (F <> 0); 24(s1) = F; the
       frame header F[0..24); s6 = F + 32 (want); s9 = SB + F / 8; the frame's eight shadow bytes f1 x4 | 00 | f3 x3;
       a1 = o = 0, s10 = i = 0, a2 = ~(F + 32), a3 = ~q, a4 = 46, a5 = 8.
   L   0x83ed4: one output byte of the inlined owed_scribble_text: the text byte x = q[i] (an instrumented check);
       x = 0 or o >= n leaves to E; a dot followed by a digit y stores y - 26 and takes two text bytes, any other
       byte stores x (or 0x3f for x >= 0x80) and takes one; want[o] is stored after an instrumented check; o += 1;
       the UBSan checks of q + i + 1 (0x83efc), want + o (0x83f24 / 0x83f4c) and q + i (0x83f80, else the
       unconditional jump 0x83f84 to the trap) are not taken.
   E   0x83fb8: o >= n to M, else a3 = 32 and on to the pad loop.
   P   0x83fc0: want[o] := ' ' (the UBSan check of want + o at 0x83fc0, an instrumented check), o += 1, back
       while o <> n, else to M.
   M   0x83ff4 .. 0x84094: __asan_memset (ch, 0xa5, 24) at 0x84000, diginet_scribble_text (q, ch, n) at 0x84010, the
       used count against s10 (abort if they differ), the compare wrapper (ch, want, n) at 0x84024 (abort if not
       equal), the UBSan check of ch + n (0x84030), n <> 24, then s4 = ch + n, a1 = j = 0, a2 = 24 - n,
       a3 = ~(ch + n), a4 = 0xa5.
   F   0x84098: the inlined fuzz_all over the record's bytes [n, 24): the UBSan check of s4 + j, an instrumented
       check, the byte against 0xa5 (abort if it differs), j += 1, back while j <> 24 - n, else to R.
   R   0x8403c .. ret: want's shadow byte := f8, F[0] := 0x45e0360e, s2 <> 0 so the frame's shadow := f5 (x8) and
       the flag byte (through the word at F + 56) := 0, the release; the epilogue, ret; the contract's post.

   Each boundary is a predicate on the configuration (lib/A/Prog/diginet_counter_text_A_inv.v's form): the caller's
   journal extended by the frame (own (0, pos) :: own), what the call has kept of its entry state (tcj_kept against
   the entry state, window TB_check_text_scribble below the entry sp, write set the record's 24 bytes), the heap
   blocks as at entry, the registers and memory every boundary carries (bs_common), and the boundary's own facts.
   The facts of the text and of the record at a boundary state are bs_now, derived from the contract's premises
   in check_text_scribble_B.v. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The boundaries' addresses, and the callees'. *)
Definition B_CTS : Z := 0x83dbc.     (* check_text_scribble *)
Definition PC_L : Z := 0x83ed4.      (* add a0,s5,s10: the text loop's head *)
Definition PC_E : Z := 0x83fb8.      (* bgeu a1,s3: the text loop's exit *)
Definition PC_P : Z := 0x83fc0.      (* bltu a2,a1: the pad loop's head *)
Definition PC_M : Z := 0x83ff4.      (* li a1,165: the record's memset *)
Definition PC_F : Z := 0x84098.      (* bltu a3,a1: the fuzz_all loop's head *)
Definition PC_R : Z := 0x8403c.      (* li a0,-8: the release *)
Definition B_SCRT : Z := 0x86500.    (* diginet_scribble_text *)
(* The frame's eight shadow bytes after 0x83eac .. 0x83ecc (want[8] at F + 32 is its one variable). *)
Definition BS_FRAME_SHADOW : list Z := [241; 241; 241; 241; 0; 243; 243; 243].
(* The complement of a 64-bit value (`not`), as the walk's registers hold it. *)
Definition bnot (x : Z) : Z := 2 ^ 64 - 1 - x.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the call: cdcU_check_text_scribble_specX's variables ------------------------------------------------------ *)
Record bs_ctx : Type := mkBs {
  bs_STK : Z; bs_sp0 : Z; bs_FP : list (Z * Z); bs_ly : alayout; bs_S : astate; bs_W0 : world tfibsegs;
  bs_mem0 : word -> option byte; bs_md0 : Model; bs_own : list (Z * Z);
  bs_lyc : alayout; bs_Sc : astate; bs_W : world tfibsegs; bs_memc : word -> option byte; bs_mdc : Model; bs_k : Z;
  bs_regs : bvmap 5 word; bs_q : Z; bs_ch : Z; bs_n : Z; bs_tb : list Z; bs_cj : list Z }.
(* The entry sp, the realigned sp of 0x83df8, the text's length, the class-0 frame and its flag byte, the write set,
   the owed result. *)
Definition bs_sp (g : bs_ctx) : Z := spZ (bs_regs g).
Definition bs_sp1 (g : bs_ctx) : Z := 32 * ((bs_sp g - 128) / 32).
Definition bs_len (g : bs_ctx) : Z := Z.of_nat (length (bs_tb g)).
Definition bs_F (g : bs_ctx) (pos : Z) : Z := frame_addr (bs_lyc g) 0 pos.
Definition bs_FL (g : bs_ctx) (pos : Z) : Z := flag_addr (bs_lyc g) 0 pos.
Definition bs_wr (g : bs_ctx) : Z -> Prop := fun x => bs_ch g <= x < bs_ch g + 24.
Definition bs_owe (g : bs_ctx) : list Z * Z := owed_scribble_text_spec (bs_tb g) (bs_n g).
(* The rest of the owed text from byte i with k output slots left. *)
Definition bs_rest (g : bs_ctx) (i : Z) (k : Z) : list Z * Z := scr_owe (skipn (Z.to_nat i) (bs_tb g)) (Z.to_nat k).

(* The contract's premises, in the contract's order. *)
Definition bs_pre (g : bs_ctx) : Prop :=
  cdc_entry tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    (bs_own g) (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) (bs_k g) (bs_regs g) TB_check_text_scribble /\
  getr (bs_regs g) 10 = w64 (bs_q g) /\
  cstr_rd tfibsegs (bs_W g) (bs_memc g) (bs_sp g) TB_check_text_scribble (bs_q g) (bs_tb g) /\
  cobj_ok B (bs_lyc g) (bs_Sc g) (bs_q g) (bs_len g) /\ cobj_ok B (bs_lyc g) (bs_Sc g) (bs_ch g) 24 /\
  getr (bs_regs g) 11 = w64 (bs_ch g) /\
  cdst_ok tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_lyc g) (bs_Sc g) (bs_own g)
    (bs_W g) (bs_memc g) (bs_sp g) TB_check_text_scribble (bs_ch g) 24 /\
  garr8 tfibsegs (rd (bs_W g) (bs_memc g)) (bs_ch g) (bs_cj g) /\ length (bs_cj g) = 24%nat /\
  getr (bs_regs g) 12 = w64 (bs_n g) /\ 0 <= bs_n g <= 8 /\
  (bs_q g + bs_len g <= bs_ch g \/ bs_ch g + 24 <= bs_q g) /\
  owed_scribble_text_spec (bs_tb g) (bs_n g) = scribble_text_spec (bs_tb g) (bs_n g) /\
  Z.of_nat (length (frames (bs_Sc g))) <= 8.

(* The facts of the text and of the record at a state the walk reaches after its frame request: the caller's
   journal with the frame, what the call kept, the blocks as at entry. *)
Definition bs_now (g : bs_ctx) : Prop :=
  forall pos ly2 S2 (W2 : world tfibsegs) mem2 md2,
  ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    ((0, pos) :: bs_own g) ly2 S2 W2 mem2 md2 (bs_k g) ->
  tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 mem2 (bs_sp g) (bs_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (bs_lyc g) (bs_Sc g)) -> ~ In (0, pos) (frames (bs_Sc g)) ->
  (garr8 tfibsegs (rd W2 mem2) (bs_q g) (bs_tb g) /\
   range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (bs_q g) (bs_len g)) /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (bs_ch g) 24 /\
  shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (bs_ch g) 24 /\
  shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (bs_q g) (bs_len g).

(* ---- what every boundary carries --------------------------------------------------------------------------------
   0x83df4 addi s0,sp,128 (s0 = entry sp); 0x83df8 andi sp,sp,-32 / 0x83dfc mv s1,sp (sp = s1 = sp1); x3, x4, s11 never
   written; s2 = s8 = F (0x83e30, 0x83e3c); s6 = F + 32 (0x83e6c); s7 = SB (0x83e1c); s9 = SB + F / 8 (0x83e7c,
   0x83ea8); s3 = n, s5 = q (0x83e00, 0x83e20); the twelve saves at entry sp - 8 .. entry sp - 96 (0x83dc4 ..
   0x83df0), read back by the epilogue (0x840f4 .. 0x84120); the frame's flag word at F + 56 (read at 0x84078);
   the frame's shadow as 0x83eac .. 0x83ecc write it. s4 is ch up to M and ch + n after it (the boundary's own). *)
Definition bs_common (g : bs_ctx) (pos : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (W2 : world tfibsegs)
  : Prop :=
  getr regs2 8 = w64 (bs_sp g) /\ getr regs2 2 = w64 (bs_sp1 g) /\ getr regs2 9 = w64 (bs_sp1 g) /\
  getr regs2 3 = getr (bs_regs g) 3 /\ getr regs2 4 = getr (bs_regs g) 4 /\
  getr regs2 18 = w64 (bs_F g pos) /\ getr regs2 24 = w64 (bs_F g pos) /\
  getr regs2 22 = w64 (bs_F g pos + 32) /\ getr regs2 23 = w64 SB /\
  getr regs2 25 = w64 (SB + bs_F g pos / 8) /\
  getr regs2 19 = w64 (bs_n g) /\ getr regs2 21 = w64 (bs_q g) /\ getr regs2 27 = getr (bs_regs g) 27 /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 8) 8 (raZ (bs_regs g)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 16) 8 (bv_unsigned (getr (bs_regs g) 8)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 24) 8 (bv_unsigned (getr (bs_regs g) 9)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 32) 8 (bv_unsigned (getr (bs_regs g) 18)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 40) 8 (bv_unsigned (getr (bs_regs g) 19)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 48) 8 (bv_unsigned (getr (bs_regs g) 20)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 56) 8 (bv_unsigned (getr (bs_regs g) 21)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 64) 8 (bv_unsigned (getr (bs_regs g) 22)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 72) 8 (bv_unsigned (getr (bs_regs g) 23)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 80) 8 (bv_unsigned (getr (bs_regs g) 24)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 88) 8 (bv_unsigned (getr (bs_regs g) 25)) /\
  val_mem tfibsegs (rd W2 mem2) (bs_sp g - 96) 8 (bv_unsigned (getr (bs_regs g) 26)) /\
  rdword (aview tfibsegs (w_H W2) mem2) (bs_F g pos + 56) = Some (bs_FL g pos) /\
  garr8 tfibsegs (rd W2 mem2) (SB + bs_F g pos / 8) BS_FRAME_SHADOW.

(* A boundary: at pc, the caller's journal with own (0, pos) :: own and k events, what the call has kept of its
   entry state, the heap blocks as at entry, the frame new, the model's input and the meter, the common part,
   and P. *)
Definition bs_cut (g : bs_ctx) (pos pc : Z)
  (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> world tfibsegs -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
    ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
      ((0, pos) :: bs_own g) ly2 S2 W2 mem2 md2 (bs_k g) /\
    tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 mem2 (bs_sp g) (bs_wr g) /\
    Permutation (ablocks B ly2 S2) (ablocks B (bs_lyc g) (bs_Sc g)) /\ ~ In (0, pos) (frames (bs_Sc g)) /\
    same_io (bs_mdc g) md2 /\ mo_le MT (bs_Sc g) S2 0 /\
    bs_common g pos regs2 mem2 W2 /\
    P ly2 S2 regs2 mem2 md2 W2.

(* The text loop's head 0x83ed4 after o output bytes from the first i text bytes: a1 = o, s10 = i, a2 = ~(F + 32),
   a3 = ~q, a4 = 46, a5 = 8, s4 = ch; the bytes q[0..i) are not 0; want[0..o) = w, and w followed by the owed text
   from byte i with n - o slots left is the whole owed text. fuel bounds the slots left. *)
Definition P_L (g : bs_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i o : Z) (w : list Z),
    getr regs2 11 = w64 o /\ getr regs2 26 = w64 i /\
    getr regs2 12 = w64 (bnot (bs_F g pos + 32)) /\ getr regs2 13 = w64 (bnot (bs_q g)) /\
    getr regs2 14 = w64 46 /\ getr regs2 15 = w64 8 /\ getr regs2 20 = w64 (bs_ch g) /\
    0 <= i /\ 0 <= o <= bs_n g /\ (Z.to_nat (bs_n g - o) < fuel)%nat /\
    Forall (fun x => x <> 0) (firstn (Z.to_nat i) (bs_tb g)) /\
    length w = Z.to_nat o /\
    fst (bs_owe g) = w ++ fst (bs_rest g i (bs_n g - o)) /\
    snd (bs_owe g) = i + snd (bs_rest g i (bs_n g - o)) /\
    garr8 tfibsegs (rd W2 mem2) (bs_F g pos + 32) w.

(* The text loop's exit 0x83fb8: the rest of the owed text is n - o spaces and the bytes used are i. *)
Definition P_E (g : bs_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i o : Z) (w : list Z),
    getr regs2 11 = w64 o /\ getr regs2 26 = w64 i /\
    getr regs2 12 = w64 (bnot (bs_F g pos + 32)) /\ getr regs2 20 = w64 (bs_ch g) /\
    0 <= i /\ 0 <= o <= bs_n g /\
    length w = Z.to_nat o /\
    fst (bs_owe g) = w ++ repeat 32 (Z.to_nat (bs_n g - o)) /\ snd (bs_owe g) = i /\
    garr8 tfibsegs (rd W2 mem2) (bs_F g pos + 32) w.

(* The pad loop's head 0x83fc0: as E with o < n and a3 = ' '. *)
Definition P_P (g : bs_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i o : Z) (w : list Z),
    getr regs2 11 = w64 o /\ getr regs2 26 = w64 i /\
    getr regs2 12 = w64 (bnot (bs_F g pos + 32)) /\ getr regs2 13 = w64 32 /\ getr regs2 20 = w64 (bs_ch g) /\
    0 <= i /\ 0 <= o < bs_n g /\ (Z.to_nat (bs_n g - o) <= fuel)%nat /\
    length w = Z.to_nat o /\
    fst (bs_owe g) = w ++ repeat 32 (Z.to_nat (bs_n g - o)) /\ snd (bs_owe g) = i /\
    garr8 tfibsegs (rd W2 mem2) (bs_F g pos + 32) w.

(* The memset 0x83ff4: want holds the owed text, s10 its bytes used, s4 = ch. *)
Definition P_M (g : bs_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 26 = w64 (snd (bs_owe g)) /\ getr regs2 20 = w64 (bs_ch g) /\
    garr8 tfibsegs (rd W2 mem2) (bs_F g pos + 32) (fst (bs_owe g)).

(* The fuzz_all loop's head 0x84098 at byte n + j of the record: a1 = j, s4 = ch + n, a2 = 24 - n,
   a3 = ~(ch + n), a4 = 0xa5; the record holds scribble_bytes. *)
Definition P_F (g : bs_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (j : Z),
    getr regs2 11 = w64 j /\ getr regs2 20 = w64 (bs_ch g + bs_n g) /\ getr regs2 12 = w64 (24 - bs_n g) /\
    getr regs2 13 = w64 (bnot (bs_ch g + bs_n g)) /\ getr regs2 14 = w64 165 /\
    0 <= j < 24 - bs_n g /\ (Z.to_nat (24 - bs_n g - j) <= fuel)%nat /\
    garr8 tfibsegs (rd W2 mem2) (bs_ch g) (scribble_bytes (bs_tb g) (bs_n g)).

(* The release 0x8403c: the record holds scribble_bytes. *)
Definition P_R (g : bs_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => garr8 tfibsegs (rd W2 mem2) (bs_ch g) (scribble_bytes (bs_tb g) (bs_n g)).

(* The contract's post. *)
Definition bs_post (g : bs_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    (bs_own g) (bs_k g) (bs_regs g) TB_check_text_scribble (bs_wr g) (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g)
    (bs_mdc g)
    (fun W2 mem2 regs2 => garr8 tfibsegs (rd W2 mem2) (bs_ch g) (scribble_bytes (bs_tb g) (bs_n g))).

(* ---- the segments ------------------------------------------------------------------------------------------------ *)
(* S0: entry -> the text loop's head with i = o = 0. *)
Definition bs_seg_S0 : Prop :=
  forall g, bs_pre g -> bs_now g ->
  SRr tfibsegs (bs_W g) (cfg_at tfibsegs B_CTS (bs_regs g) (bs_memc g) (bs_mdc g))
    (fun W2 c2 => exists pos, bs_cut g pos PC_L (P_L g pos (S (Z.to_nat (bs_n g)))) W2 c2).
(* L: one output byte of the text loop. *)
Definition bs_seg_L : Prop :=
  forall g pos fuel W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_L (P_L g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => bs_cut g pos PC_L (P_L g pos fuel) W3 c3 \/ bs_cut g pos PC_E (P_E g pos) W3 c3).
(* E: the text loop's exit, to the pad loop or the memset. *)
Definition bs_seg_E : Prop :=
  forall g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_E (P_E g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => bs_cut g pos PC_P (P_P g pos 8) W3 c3 \/ bs_cut g pos PC_M (P_M g pos) W3 c3).
(* P: one byte of the pad loop. *)
Definition bs_seg_P : Prop :=
  forall g pos fuel W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_P (P_P g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => bs_cut g pos PC_P (P_P g pos fuel) W3 c3 \/ bs_cut g pos PC_M (P_M g pos) W3 c3).
(* M: the memset, diginet_scribble_text, the compare, to the fuzz_all loop's head with j = 0. *)
Definition bs_seg_M : Prop :=
  forall g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_M (P_M g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => bs_cut g pos PC_F (P_F g pos 24) W3 c3).
(* F: one byte of the fuzz_all loop. *)
Definition bs_seg_F : Prop :=
  forall g pos fuel W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_F (P_F g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => bs_cut g pos PC_F (P_F g pos fuel) W3 c3 \/ bs_cut g pos PC_R (P_R g pos) W3 c3).
(* R: the release, the epilogue, the post. *)
Definition bs_seg_R : Prop :=
  forall g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_R (P_R g pos) W2 c2 -> SRr tfibsegs W2 c2 (bs_post g).

(* ---- the composition --------------------------------------------------------------------------------------------- *)
Lemma P_L_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_L g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 (i & o & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). lia.
Qed.
Lemma P_P_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_P g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 (i & o & w & _ & _ & _ & _ & _ & _ & Ho & Hf & _). lia.
Qed.
Lemma P_F_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_F g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 (j & _ & _ & _ & _ & _ & Hj & Hf & _). lia.
Qed.
Lemma bs_cut_mono : forall g pos pc (P Q : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
  world tfibsegs -> Prop) W2 c2,
  (forall ly2 S2 regs2 mem2 md2 W2, P ly2 S2 regs2 mem2 md2 W2 -> Q ly2 S2 regs2 mem2 md2 W2) ->
  bs_cut g pos pc P W2 c2 -> bs_cut g pos pc Q W2 c2.
Proof.
intros g pos pc P Q W2 c2 HPQ (ly2 & S2 & regs2 & mem2 & md2 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
exists ly2, S2, regs2, mem2, md2. repeat (split; [assumption|]). apply HPQ. exact H9.
Qed.

Section comp.
Hypothesis HS0 : bs_seg_S0.
Hypothesis HL : bs_seg_L.
Hypothesis HE : bs_seg_E.
Hypothesis HP : bs_seg_P.
Hypothesis HM : bs_seg_M.
Hypothesis HF : bs_seg_F.
Hypothesis HR : bs_seg_R.
Lemma bs_F_closed : forall fuel g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_F (P_F g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_post g).
Proof.
induction fuel as [|fuel IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HPc).
  exact (P_F_zero g pos ly2 S2 regs2 mem2 md2 W2 HPc).
- apply (SRr_bind tfibsegs _ _ _ _ (HF g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (HR g pos W3 c3 Hpre Hnow H).
Qed.
Lemma bs_M_closed : forall g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_M (P_M g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_post g).
Proof.
intros g pos W2 c2 Hpre Hnow Hc.
apply (SRr_bind tfibsegs _ _ _ _ (HM g pos W2 c2 Hpre Hnow Hc)). intros W3 c3 _ H.
exact (bs_F_closed 24 g pos W3 c3 Hpre Hnow H).
Qed.
Lemma bs_P_closed : forall fuel g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_P (P_P g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_post g).
Proof.
induction fuel as [|fuel IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HPc).
  exact (P_P_zero g pos ly2 S2 regs2 mem2 md2 W2 HPc).
- apply (SRr_bind tfibsegs _ _ _ _ (HP g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (bs_M_closed g pos W3 c3 Hpre Hnow H).
Qed.
Lemma bs_E_closed : forall g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_E (P_E g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_post g).
Proof.
intros g pos W2 c2 Hpre Hnow Hc.
apply (SRr_bind tfibsegs _ _ _ _ (HE g pos W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
- exact (bs_P_closed 8 g pos W3 c3 Hpre Hnow H).
- exact (bs_M_closed g pos W3 c3 Hpre Hnow H).
Qed.
Lemma bs_L_closed : forall fuel g pos W2 c2, bs_pre g -> bs_now g -> bs_cut g pos PC_L (P_L g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_post g).
Proof.
induction fuel as [|fuel IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HPc).
  exact (P_L_zero g pos ly2 S2 regs2 mem2 md2 W2 HPc).
- apply (SRr_bind tfibsegs _ _ _ _ (HL g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (bs_E_closed g pos W3 c3 Hpre Hnow H).
Qed.
Theorem bs_of_segs : forall g, bs_pre g -> bs_now g ->
  SRr tfibsegs (bs_W g) (cfg_at tfibsegs B_CTS (bs_regs g) (bs_memc g) (bs_mdc g)) (bs_post g).
Proof.
intros g Hpre Hnow.
apply (SRr_bind tfibsegs _ _ _ _ (HS0 g Hpre Hnow)). intros W2 c2 _ (pos & H).
exact (bs_L_closed _ g pos W2 c2 Hpre Hnow H).
Qed.
End comp.

(* The contract from the seven segments and bs_now at every call. *)
Theorem bs_spec_of_segs : bs_seg_S0 -> bs_seg_L -> bs_seg_E -> bs_seg_P -> bs_seg_M -> bs_seg_F -> bs_seg_R ->
  (forall g, bs_pre g -> bs_now g) ->
  cdcU_check_text_scribble_specX tfibsegs B MT B_CTS.
Proof.
intros HS0 HL HE HP HM HF HR HNOW.
unfold cdcU_check_text_scribble_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
  H1 H2 H3 Hoq Hoch H4 H5 H6 H7 H8 H9 H10 H11 H12.
pose (g := mkBs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj).
assert (Hpre : bs_pre g)
  by (unfold bs_pre, g, bs_sp, bs_len; cbn [bs_STK bs_sp0 bs_FP bs_ly bs_S bs_W0 bs_mem0 bs_md0 bs_own bs_lyc bs_Sc
        bs_W bs_memc bs_mdc bs_k bs_regs bs_q bs_ch bs_n bs_tb bs_cj];
      repeat (split; [assumption|]); assumption).
exact (bs_of_segs HS0 HL HE HP HM HF HR g Hpre (HNOW g Hpre)).
Qed.
End h.
End d.
