(* The boundary layer of check_text_counter's walk in image B (fuzz_codec.asan-ubsan 0x841c4, 172 instructions, real
   frame 160, a side-stack frame of class 0): the state at each segment boundary, the statement of each segment, and
   their composition into lib/AU/Prog/CPgChkU.v's cdcU_check_text_counter_specX. The segments are proved against these
   statements in check_text_counter_B_<seg>.v.

   The code (neutral listing of image B):
   S0  0x841c4 .. 0x842d8: the frame (`sd zero,0(sp)`, thirteen saves at entry sp - 8 .. entry sp - 104), s0 = entry
       sp, sp = s1 = 32 * ((sp - 160) / 32); s4 = dt, s3 = sg, s5 = q; the use-after-return cell (it holds 1) and the
       shadow offset s8 = SB through the .got; the class-0 side-stack frame request (a0 = 64, jal 0x3d24c at
       0x84238), s9 = F; the real-stack fallback 0x8424c .. 0x84264 is not reached (F <> 0); 24(s1) = 40(s1) = F;
       s6 = F + 32 (want[8]); the frame header F[0..24); s10 = SB + F / 8; the frame's eight shadow bytes
       f1 x4 | 00 | f3 x3; the want dots byte 55(s1) := 0; a0 = q, a1 = F + 32, a2 = s1 + 55, jal owed_counter_text.
   N1a 0x84474 owed_counter_text through its contract; s7 = its rc, a0 = sg, a1 = 0xa5, a2 = 24, s2 = 0xa5, jal
       __asan_memset at 0x842f0.
   N1b 0x51f84 __asan_memset through the runtime's contract; s11 = SB + dt / 8; the instrumented check of the store
       to dt; dt := 0xa5; a0 = q, a1 = sg, a2 = dt, jal diginet_counter_text at 0x84314.
   N2  0x869e4 diginet_counter_text through its contract; 0x84318 bne a0,s7 (not taken: the two results agree);
       0x8431c bnez s7: a result other than 0 goes to 0x84348, a result 0 to the compare wrapper (a0 = sg,
       a1 = want, a2 = 8, jal at 0x8432c).
   N3  0x42430 the compare wrapper through its contract (equal); 0x84330 bnez a0 (not taken); the instrumented check
       of the load of dt; dt against the want dots byte 55(s1) (equal).
       From 0x84348 (N2 and N3): the UBSan check of sg + 8 (0x8434c, not taken), s3 = sg + 8, a1 = j = 0,
       a2 = 0xa5, a3 = ~(sg + 8), a4 = 16.
   F   0x84364: the inlined fuzz_all over the record's bytes [8, 24): the UBSan check of s3 + j, the instrumented
       check, the byte against 0xa5 (abort if it differs), j += 1, back while j <> 16, else to R.
   R   0x8439c .. ret: want's shadow byte := f8, F[0] := 0x45e0360e, 24(s1) = F <> 0 so the frame's shadow := f5 (x8)
       and the flag byte (through the word at F + 56) := 0, the release; the epilogue, ret; the contract's post.

   Each boundary is a predicate on the configuration: the caller's journal extended by the frame
   (own (0, pos) :: own), what the call has kept of its entry state (tcj_kept against the entry state, window
   TB_check_text_counter below the entry sp, write set the record's 24 bytes and dt), the heap blocks as at entry,
   the registers and memory every boundary carries (cc_common), and the boundary's own facts. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The boundaries' addresses, and the callees'. *)
Definition B_CTC : Z := 0x841c4.          (* check_text_counter *)
Definition B_OWED_CT : Z := 0x84474.      (* owed_counter_text, called from 0x842d8 *)
Definition B_COUNTER_TEXT : Z := 0x869e4. (* diginet_counter_text, called from 0x84314 *)
Definition CC_CM : Z := 0x51f84.          (* __asan_memset, called from 0x842f0 *)
Definition CC_CB : Z := 0x42430.          (* the compare wrapper, called from 0x8432c *)
Definition CC_FL : Z := 0x84364.          (* bltu a3,a1: the fuzz_all loop's head *)
Definition CC_R : Z := 0x8439c.           (* li a0,-8: the release *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).

(* ---- the call: cdcU_check_text_counter_specX's variables --------------------------------------------------------- *)
Record cc_ctx : Type := mkCc {
  cc_STK : Z; cc_sp0 : Z; cc_FP : list (Z * Z); cc_ly : alayout; cc_S : astate; cc_W0 : world tfibsegs;
  cc_mem0 : word -> option byte; cc_md0 : Model; cc_own : list (Z * Z);
  cc_lyc : alayout; cc_Sc : astate; cc_W : world tfibsegs; cc_memc : word -> option byte; cc_mdc : Model; cc_k : Z;
  cc_regs : bvmap 5 word; cc_q : Z; cc_sg : Z; cc_dt : Z; cc_tb : list Z; cc_sj : list Z; cc_dj : Z }.
Definition cc_sp (g : cc_ctx) : Z := spZ (cc_regs g).
Definition cc_sp1 (g : cc_ctx) : Z := 32 * ((cc_sp g - 160) / 32).
Definition cc_len (g : cc_ctx) : Z := Z.of_nat (length (cc_tb g)).
Definition cc_F (g : cc_ctx) (pos : Z) : Z := frame_addr (cc_lyc g) 0 pos.
Definition cc_FL (g : cc_ctx) (pos : Z) : Z := flag_addr (cc_lyc g) 0 pos.
Definition cc_wr (g : cc_ctx) : Z -> Prop := fun x => cc_sg g <= x < cc_sg g + 24 \/ cc_dt g <= x < cc_dt g + 1.
(* the owed result (rc, digits, dots) and the library's *)
Definition cc_ro (g : cc_ctx) : Z := fst (fst (owed_counter_text_spec (cc_tb g))).
Definition cc_so (g : cc_ctx) : list Z := snd (fst (owed_counter_text_spec (cc_tb g))).
Definition cc_do (g : cc_ctx) : Z := snd (owed_counter_text_spec (cc_tb g)).

(* The contract's premises, in the contract's order. *)
Definition cc_pre (g : cc_ctx) : Prop :=
  cdc_entry tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    (cc_own g) (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_mdc g) (cc_k g) (cc_regs g) TB_check_text_counter /\
  getr (cc_regs g) 10 = w64 (cc_q g) /\
  cstr_rd tfibsegs (cc_W g) (cc_memc g) (cc_sp g) TB_check_text_counter (cc_q g) (cc_tb g) /\
  cobj_ok B (cc_lyc g) (cc_Sc g) (cc_q g) (cc_len g) /\ cobj_ok B (cc_lyc g) (cc_Sc g) (cc_sg g) 24 /\
  cobj_ok B (cc_lyc g) (cc_Sc g) (cc_dt g) 1 /\
  getr (cc_regs g) 11 = w64 (cc_sg g) /\
  cdst_ok tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_lyc g) (cc_Sc g) (cc_own g)
    (cc_W g) (cc_memc g) (cc_sp g) TB_check_text_counter (cc_sg g) 24 /\
  garr8 tfibsegs (rd (cc_W g) (cc_memc g)) (cc_sg g) (cc_sj g) /\ length (cc_sj g) = 24%nat /\
  getr (cc_regs g) 12 = w64 (cc_dt g) /\
  cdst_ok tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_lyc g) (cc_Sc g) (cc_own g)
    (cc_W g) (cc_memc g) (cc_sp g) TB_check_text_counter (cc_dt g) 1 /\
  val_mem tfibsegs (rd (cc_W g) (cc_memc g)) (cc_dt g) 1 (cc_dj g) /\
  (cc_sg g + 24 <= cc_dt g \/ cc_dt g + 1 <= cc_sg g) /\
  (cc_q g + cc_len g <= cc_sg g \/ cc_sg g + 24 <= cc_q g) /\
  (cc_q g + cc_len g <= cc_dt g \/ cc_dt g + 1 <= cc_q g) /\
  cimg_rd tfibsegs B CB_RLO CB_RHI (cc_W g) (cc_memc g) (cc_sp g) TB_check_text_counter
    ((SEG7TBL, 364) :: (GLYPHA, 464) :: ROSTRS) /\
  (let '(r1, s1, d1) := counter_text_spec (cc_tb g) in
   let '(r2, s2, d2) := owed_counter_text_spec (cc_tb g) in
   r1 = r2 /\ (r1 = 0 -> s1 = s2 /\ d1 = d2)) /\
  Z.of_nat (length (frames (cc_Sc g))) <= 6.

(* The facts of the text, the record and dt at a state the walk reaches after its frame request. *)
Definition cc_now (g : cc_ctx) : Prop :=
  forall pos ly2 S2 (W2 : world tfibsegs) mem2 md2,
  ajournal tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g) ->
  tcj_kept tfibsegs B TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) W2 mem2 (cc_sp g) (cc_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cc_lyc g) (cc_Sc g)) -> ~ In (0, pos) (frames (cc_Sc g)) ->
  (garr8 tfibsegs (rd W2 mem2) (cc_q g) (cc_tb g) /\
   range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cc_q g) (cc_len g) /\
   shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (cc_q g) (cc_len g)) /\
  (range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cc_sg g) 24 /\
   shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (cc_sg g) 24) /\
  (range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cc_dt g) 1 /\
   shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (cc_dt g) 1).

(* ---- what every boundary carries --------------------------------------------------------------------------------
   0x84200 addi s0,sp,160 (s0 = entry sp); 0x84204 andi sp,sp,-32 / 0x84208 mv s1,sp (sp = s1 = sp1); x3, x4 never
   written; s9 = F (0x84244); s6 = F + 32 (0x84270); s10 = SB + F / 8 (0x84280, 0x842a0); s8 = SB (0x84228);
   s5 = q (0x8422c), s4 = dt (0x8420c); the thirteen saves at entry sp - 8 .. entry sp - 104 (0x841cc .. 0x841fc),
   read back by the epilogue (0x8440c .. 0x8443c); the frame's flag word at F + 56 (read at 0x843dc); the frame's
   shadow as 0x842a4 .. 0x842c4 write it; F at 24(s1) (0x84268, read at 0x843b0). s2, s3, s7 and s11 are the
   boundary's own. *)
Definition cc_common (g : cc_ctx) (pos : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (W2 : world tfibsegs)
  : Prop :=
  getr regs2 8 = w64 (cc_sp g) /\ getr regs2 2 = w64 (cc_sp1 g) /\ getr regs2 9 = w64 (cc_sp1 g) /\
  getr regs2 3 = getr (cc_regs g) 3 /\ getr regs2 4 = getr (cc_regs g) 4 /\
  getr regs2 25 = w64 (cc_F g pos) /\ getr regs2 22 = w64 (cc_F g pos + 32) /\
  getr regs2 26 = w64 (SB + cc_F g pos / 8) /\ getr regs2 24 = w64 SB /\
  getr regs2 21 = w64 (cc_q g) /\ getr regs2 20 = w64 (cc_dt g) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 8) 8 (raZ (cc_regs g)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 16) 8 (bv_unsigned (getr (cc_regs g) 8)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 24) 8 (bv_unsigned (getr (cc_regs g) 9)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 32) 8 (bv_unsigned (getr (cc_regs g) 18)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 40) 8 (bv_unsigned (getr (cc_regs g) 19)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 48) 8 (bv_unsigned (getr (cc_regs g) 20)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 56) 8 (bv_unsigned (getr (cc_regs g) 21)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 64) 8 (bv_unsigned (getr (cc_regs g) 22)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 72) 8 (bv_unsigned (getr (cc_regs g) 23)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 80) 8 (bv_unsigned (getr (cc_regs g) 24)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 88) 8 (bv_unsigned (getr (cc_regs g) 25)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 96) 8 (bv_unsigned (getr (cc_regs g) 26)) /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp g - 104) 8 (bv_unsigned (getr (cc_regs g) 27)) /\
  rdword (aview tfibsegs (w_H W2) mem2) (cc_F g pos + 56) = Some (cc_FL g pos) /\
  garr8 tfibsegs (rd W2 mem2) (SB + cc_F g pos / 8) BS_FRAME_SHADOW /\
  val_mem tfibsegs (rd W2 mem2) (cc_sp1 g + 24) 8 (cc_F g pos).

(* A boundary: at pc, the caller's journal with own (0, pos) :: own and k events, what the call has kept of its
   entry state, the heap blocks as at entry, the frame new, the model's input and the meter, the common part,
   and P. *)
Definition cc_cut (g : cc_ctx) (pos pc : Z)
  (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> world tfibsegs -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
    ajournal tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
      ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g) /\
    tcj_kept tfibsegs B TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) W2 mem2 (cc_sp g) (cc_wr g) /\
    Permutation (ablocks B ly2 S2) (ablocks B (cc_lyc g) (cc_Sc g)) /\ ~ In (0, pos) (frames (cc_Sc g)) /\
    same_io (cc_mdc g) md2 /\ mo_le MT (cc_Sc g) S2 0 /\
    cc_common g pos regs2 mem2 W2 /\
    P ly2 S2 regs2 mem2 md2 W2.

(* what owed_counter_text left: the digits at want[8] and the want dots byte at 55(s1), the owed ones when its
   result is 0 *)
Definition cc_owres (g : cc_ctx) (pos : Z) (mem2 : word -> option byte) (W2 : world tfibsegs) : Prop :=
  exists sw v2, garr8 tfibsegs (rd W2 mem2) (cc_F g pos + 32) sw /\ length sw = 8%nat /\
    val_mem tfibsegs (rd W2 mem2) (cc_sp1 g + 55) 1 v2 /\ (cc_ro g = 0 -> sw = cc_so g /\ v2 = cc_do g).
(* the record with eight digits in front of sixteen 0xa5 bytes, and dt *)
Definition cc_recok (g : cc_ctx) (mem2 : word -> option byte) (W2 : world tfibsegs) : Prop :=
  exists s d, length s = 8%nat /\ garr8 tfibsegs (rd W2 mem2) (cc_sg g) (s ++ repeat 165 16) /\
    val_mem tfibsegs (rd W2 mem2) (cc_dt g) 1 d.

(* owed_counter_text's entry 0x84474: ra = 0x842dc, a0 = q, a1 = F + 32, a2 = s1 + 55, s3 = sg; the want dots byte
   is 0 *)
Definition P_C0 (g : cc_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 1 = w64 0x842dc /\ getr regs2 10 = w64 (cc_q g) /\ getr regs2 11 = w64 (cc_F g pos + 32) /\
    getr regs2 12 = w64 (cc_sp1 g + 55) /\ getr regs2 19 = w64 (cc_sg g) /\
    val_mem tfibsegs (rd W2 mem2) (cc_sp1 g + 55) 1 0.
(* __asan_memset's entry 0x51f84: ra = 0x842f4, a0 = sg, a1 = 0xa5, a2 = 24, s2 = 0xa5, s3 = sg, s7 = the owed rc *)
Definition P_CM (g : cc_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 1 = w64 0x842f4 /\ getr regs2 10 = w64 (cc_sg g) /\ getr regs2 11 = w64 165 /\
    getr regs2 12 = w64 24 /\ getr regs2 18 = w64 165 /\ getr regs2 19 = w64 (cc_sg g) /\
    getr regs2 23 = w64 (cc_ro g) /\ cc_owres g pos mem2 W2.
(* diginet_counter_text's entry 0x869e4: ra = 0x84318, a0 = q, a1 = sg, a2 = dt, s3 = sg, s7 = the owed rc,
   s11 = SB + dt / 8; the record's 24 bytes and dt hold 0xa5 *)
Definition P_C1 (g : cc_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 1 = w64 0x84318 /\ getr regs2 10 = w64 (cc_q g) /\ getr regs2 11 = w64 (cc_sg g) /\
    getr regs2 12 = w64 (cc_dt g) /\ getr regs2 19 = w64 (cc_sg g) /\ getr regs2 23 = w64 (cc_ro g) /\
    getr regs2 27 = w64 (SB + cc_dt g / 8) /\
    garr8 tfibsegs (rd W2 mem2) (cc_sg g) (repeat 165 24) /\ val_mem tfibsegs (rd W2 mem2) (cc_dt g) 1 165 /\
    cc_owres g pos mem2 W2.
(* the compare wrapper's entry 0x42430 (both results 0): ra = 0x84330, a0 = sg, a1 = want, a2 = 8, s3 = sg,
   s11 = SB + dt / 8; the record holds the digits s, want too, dt and the want dots byte d *)
Definition P_CB (g : cc_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 =>
    getr regs2 1 = w64 0x84330 /\ getr regs2 10 = w64 (cc_sg g) /\ getr regs2 11 = w64 (cc_F g pos + 32) /\
    getr regs2 12 = w64 8 /\ getr regs2 19 = w64 (cc_sg g) /\ getr regs2 27 = w64 (SB + cc_dt g / 8) /\
    exists s d, length s = 8%nat /\ garr8 tfibsegs (rd W2 mem2) (cc_sg g) (s ++ repeat 165 16) /\
      garr8 tfibsegs (rd W2 mem2) (cc_F g pos + 32) s /\
      val_mem tfibsegs (rd W2 mem2) (cc_dt g) 1 d /\ val_mem tfibsegs (rd W2 mem2) (cc_sp1 g + 55) 1 d.
(* the fuzz_all loop's head 0x84364 at byte 8 + j of the record: a1 = j, s3 = sg + 8, a2 = 0xa5, a3 = ~(sg + 8),
   a4 = 16 *)
Definition P_FL (g : cc_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (j : Z),
    getr regs2 11 = w64 j /\ getr regs2 19 = w64 (cc_sg g + 8) /\ getr regs2 12 = w64 165 /\
    getr regs2 13 = w64 (bnot (cc_sg g + 8)) /\ getr regs2 14 = w64 16 /\
    0 <= j < 16 /\ (Z.to_nat (16 - j) <= fuel)%nat /\ cc_recok g mem2 W2.
(* the release 0x8439c *)
Definition P_R (g : cc_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => cc_recok g mem2 W2.

(* The contract's post. *)
Definition cc_post (g : cc_ctx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    (cc_own g) (cc_k g) (cc_regs g) TB_check_text_counter (cc_wr g) (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g)
    (cc_mdc g)
    (fun W2 mem2 regs2 => exists s' d', garr8 tfibsegs (rd W2 mem2) (cc_sg g) (s' ++ repeat 0xa5 16) /\
       length s' = 8%nat /\ val_mem tfibsegs (rd W2 mem2) (cc_dt g) 1 d').

(* ---- the segments ------------------------------------------------------------------------------------------------ *)
Definition cc_seg_S0 : Prop :=
  forall g, cc_pre g -> cc_now g ->
  SRr tfibsegs (cc_W g) (cfg_at tfibsegs B_CTC (cc_regs g) (cc_memc g) (cc_mdc g))
    (fun W2 c2 => exists pos, cc_cut g pos B_OWED_CT (P_C0 g pos) W2 c2).
Definition cc_seg_N1a : Prop :=
  forall g pos W2 c2, cc_pre g -> cc_now g -> cc_cut g pos B_OWED_CT (P_C0 g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (cc_cut g pos CC_CM (P_CM g pos)).
Definition cc_seg_N1b : Prop :=
  forall g pos W2 c2, cc_pre g -> cc_now g -> cc_cut g pos CC_CM (P_CM g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (cc_cut g pos B_COUNTER_TEXT (P_C1 g pos)).
Definition cc_seg_N2 : Prop :=
  forall g pos W2 c2, cc_pre g -> cc_now g -> cc_cut g pos B_COUNTER_TEXT (P_C1 g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => cc_cut g pos CC_CB (P_CB g pos) W3 c3 \/ cc_cut g pos CC_FL (P_FL g pos 16) W3 c3).
Definition cc_seg_N3 : Prop :=
  forall g pos W2 c2, cc_pre g -> cc_now g -> cc_cut g pos CC_CB (P_CB g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (cc_cut g pos CC_FL (P_FL g pos 16)).
Definition cc_seg_F : Prop :=
  forall g pos fuel W2 c2, cc_pre g -> cc_now g -> cc_cut g pos CC_FL (P_FL g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => cc_cut g pos CC_FL (P_FL g pos fuel) W3 c3 \/ cc_cut g pos CC_R (P_R g pos) W3 c3).
Definition cc_seg_R : Prop :=
  forall g pos W2 c2, cc_pre g -> cc_now g -> cc_cut g pos CC_R (P_R g pos) W2 c2 -> SRr tfibsegs W2 c2 (cc_post g).

(* ---- the composition --------------------------------------------------------------------------------------------- *)
Lemma P_FL_zero : forall g pos ly2 S2 regs2 mem2 md2 W2, P_FL g pos 0 ly2 S2 regs2 mem2 md2 W2 -> False.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 (j & _ & _ & _ & _ & _ & Hj & Hf & _). lia.
Qed.

Section comp.
Hypothesis HS0 : cc_seg_S0.
Hypothesis HN1a : cc_seg_N1a.
Hypothesis HN1b : cc_seg_N1b.
Hypothesis HN2 : cc_seg_N2.
Hypothesis HN3 : cc_seg_N3.
Hypothesis HF : cc_seg_F.
Hypothesis HR : cc_seg_R.
Lemma cc_F_closed : forall fuel g pos W2 c2, cc_pre g -> cc_now g -> cc_cut g pos CC_FL (P_FL g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (cc_post g).
Proof.
induction fuel as [|fuel IH]; intros g pos W2 c2 Hpre Hnow Hc.
- exfalso. destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & _ & HPc).
  exact (P_FL_zero g pos ly2 S2 regs2 mem2 md2 W2 HPc).
- apply (SRr_bind tfibsegs _ _ _ _ (HF g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H | H].
  + exact (IH g pos W3 c3 Hpre Hnow H).
  + exact (HR g pos W3 c3 Hpre Hnow H).
Qed.
Theorem cc_of_segs : forall g, cc_pre g -> cc_now g ->
  SRr tfibsegs (cc_W g) (cfg_at tfibsegs B_CTC (cc_regs g) (cc_memc g) (cc_mdc g)) (cc_post g).
Proof.
intros g Hpre Hnow.
apply (SRr_bind tfibsegs _ _ _ _ (HS0 g Hpre Hnow)). intros W2 c2 _ (pos & H2).
apply (SRr_bind tfibsegs _ _ _ _ (HN1a g pos W2 c2 Hpre Hnow H2)). intros W3 c3 _ H3.
apply (SRr_bind tfibsegs _ _ _ _ (HN1b g pos W3 c3 Hpre Hnow H3)). intros W4 c4 _ H4.
apply (SRr_bind tfibsegs _ _ _ _ (HN2 g pos W4 c4 Hpre Hnow H4)). intros W5 c5 _ [H5 | H5].
- apply (SRr_bind tfibsegs _ _ _ _ (HN3 g pos W5 c5 Hpre Hnow H5)). intros W6 c6 _ H6.
  exact (cc_F_closed 16 g pos W6 c6 Hpre Hnow H6).
- exact (cc_F_closed 16 g pos W5 c5 Hpre Hnow H5).
Qed.
End comp.

(* The contract from the seven segments and cc_now at every call. *)
Theorem cc_spec_of_segs : cc_seg_S0 -> cc_seg_N1a -> cc_seg_N1b -> cc_seg_N2 -> cc_seg_N3 -> cc_seg_F -> cc_seg_R ->
  (forall g, cc_pre g -> cc_now g) ->
  cdcU_check_text_counter_specX tfibsegs B MT CB_RLO CB_RHI SEG7TBL GLYPHA ROSTRS B_CTC.
Proof.
intros HS0 HN1a HN1b HN2 HN3 HF HR HNOW.
unfold cdcU_check_text_counter_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj
  H1 H2 H3 Hoq Hosg Hodt H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
pose (g := mkCc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj).
assert (Hpre : cc_pre g)
  by (unfold cc_pre, g, cc_sp, cc_len; cbn [cc_STK cc_sp0 cc_FP cc_ly cc_S cc_W0 cc_mem0 cc_md0 cc_own cc_lyc cc_Sc
        cc_W cc_memc cc_mdc cc_k cc_regs cc_q cc_sg cc_dt cc_tb cc_sj cc_dj];
      repeat (split; [assumption|]); assumption).
exact (cc_of_segs HS0 HN1a HN1b HN2 HN3 HF HR g Hpre (HNOW g Hpre)).
Qed.
End h.
End d.
