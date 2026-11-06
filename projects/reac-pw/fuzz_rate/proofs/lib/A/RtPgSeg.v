(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSeg.v at 256ddb9487c and
   proofs/reac-pw/fuzz_role/lib/A/RPgHarn.v at 680a13dcf7c for reac-pw/fuzz_rate image A: role's pcs, registers and
   real-frame cells are replaced by the ones measured on fuzz_rate.asan and its contract file and image record by
   rate's (lib/A/RtPgCSpec.v, lib/A/RtPgImgA.v; the rl_ vocabulary becomes rt_); the build's latch gains a third
   entry; the checks' tail becomes the asked[] set-up, the decide loop and its tail; the third segment (the list), the
   two malloc steps and the five segment statements S_E01 .. S_X01 in the plain walk's continuation form are new. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): THE CUT STATES of the walk
   of LLVMFuzzerTestOneInput (0x80714, 12156 bytes, 3039 instructions), the five segment statements and the statement
   of every piece the walk is split into. Statement text only: proves no function (kind: statement text).

   WHAT THIS FILE IS FOR. The walk is cut at the points the plain walk of the same function is cut at
   (lib/Prog/LLVMFuzzerTestOneInput_c.v): ENTRY, C1 = 0x809e0 (malloc(pp) returned), C3 = 0x828b8 (malloc(pod)
   returned), C4 = 0x82e84 (check_code(reac_rate_refuse_code(4), 4) returned), C6 = 0x82e98 (malloc(buf) returned),
   C7 = 0x82ed4 (check_csv returned) and RET. The five segments keep the plain walk's names S_E01 / S_M01 / S_M02 /
   S_M03 / S_X01 and its continuation form ("the H of the exit cut -> the H of the entry cut"). The three middle
   bodies are the fixed contracts rate_build_contract (C1 -> C2 = the malloc(pod) `jal` 0x828b4),
   rate_check_contract (C3 -> C4) and rate_csv_contract (C6 -> C7) of lib/A/RtPgCSpec.v at image A's record
   RtPgImgA.rate_himg_A; S_M01 adds the malloc(pod) step C2 -> C3 and S_M03 the malloc(buf) step C4 -> C6 (through
   the `jal` C5 = 0x82e94). The first two contracts' walks are cut again at the heads and joins of their loops and at
   the boundaries of their pieces, and every piece is stated here, so that the pieces are proved in parallel and each
   proof sees only the STATEMENTS of the pieces its continuation goes to.

   HOW A CUT IS STATED, AND WHY NOT AS A SYMBOLIC STATE. A cut is a SEMANTIC predicate over
   (ly, S, W, regs, mem, md) at the cut's pc: the caller's journal from the segment's start, the frame's shadow
   bytes, the first block's image, the input bytes left, and a list of (location, value) facts over the run's
   quantities (RtPgBase.rt_at: a register, or the 8-byte cell at an offset of a base). A symbolic state can only be
   written down after the piece before it has been run, which would serialise the pieces; a semantic cut lets each
   piece rebuild its own symbolic state from the cut, as the released walks rebuild the entry one.
   A cut states only POSITIVE facts. What a call leaves alone is not restated: the journal's own clauses and each
   callee's write-set post carry it between cuts.

   WHERE A VALUE LIVES. Image A keeps the harness's values in registers and in 8-byte cells of the real frame at
   R + off, R = 32 * floor((S - 0x1e0) / 32) being the 32-aligned base the prologue puts in s1 and sp (0x80754,
   0x80758) and S the entry sp (s0, 0x80750). The locals whose address is taken live in the frame for locals F, a
   side-stack frame of class 3 that the prologue takes (0x80780 `addi a0,zero,0x1c0`, 0x80784 the call, s8 = s10 = F):
   t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at F+0xf0, hz at F+0x180, asked[0] at F+0x190 and
   asked[1] at F+0x1a0 (two objects of 4 bytes each). s4 = (F >> 3) + K is the frame's shadow base and s2 = K the
   runtime's shadow offset (until 0x82eac). sp = R from 0x80758 to the epilogue. The seven header values (flags, mask,
   buflen = byte 2 mod 24, bytes 3 .. 6) are spilled to R-relative cells in the build and read back in the checks.

   THE MODEL. The quantities a cut names are the shared model's (lib/Pod): the record built so far is a
   Model.pb_cut (the shape, the properties written and, inside a params Struct, the pods written), the first block
   holds Layout.pc_image of it, what is left of the input is a suffix of the bytes after the 7-byte header, and the
   cursor that names it is src + |rest| - |r|. At the end of the build the block holds Layout.pp_bytes of the record
   Model.pod_build makes; the checking segment reads it back, its scan computes Rate.expect_model step by step, and its
   decide loop runs the library's answers (Pod/RateCfg.v) on asked[0] and asked[1]. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the pcs of the cuts ============================================
   Each is the address of the first instruction of the piece that starts there; the seven segment cuts are
   RtPgImgA.rate_himg_A's hi_c1 .. hi_c7 (rs_pcs_himg). *)
Definition RS_ENTRY : Z := 0x80714.      (* `addi sp,sp,-0x1e0` *)
Definition RS_RET : Z := 0x8304c.        (* `ret` *)
Definition RS_C1 : Z := 0x809e0.         (* `bnez a0` after malloc(pp) (`jal` 0x809dc) *)
Definition RS_C2 : Z := 0x828b4.         (* the `jal` of malloc(pod), a0 = len + (len == 0) *)
Definition RS_C3 : Z := 0x828b8.         (* `beqz a0` after it returns *)
Definition RS_C4 : Z := 0x82e84.         (* after check_code(reac_rate_refuse_code(4), 4) returns (`jal` 0x82e80) *)
Definition RS_C5 : Z := 0x82e94.         (* the `jal` of malloc(buf), a0 = buflen + (buflen == 0) *)
Definition RS_C6 : Z := 0x82e98.         (* `beqz a0` after it returns *)
Definition RS_C7 : Z := 0x82ed4.         (* `mv a0,s5` after check_csv returns (`jal` 0x82ed0), before free(buf) *)
Definition RS_J82f04 : Z := 0x82f04.     (* `lui a0,0x45e03`: the frame's retirement word, after the three releases *)
(* inside the build (M01) *)
Definition RS_B7 : Z := 0x80b28.         (* the shape-7 object header *)
Definition RS_BO : Z := 0x80b94.         (* the Object header (shape <> 7) *)
Definition RS_PH : Z := 0x80d38.         (* the property loop's preheader *)
Definition RS_N : Z := 0x80e10.          (* `sd a6,0xf8(s1)`: the property loop's head *)
Definition RS_SEL7 : Z := 0x80e6c.       (* the shape-7 Int pod of one property *)
Definition RS_SELK : Z := 0x81018.       (* a property's key, its flags and the `first` test *)
Definition RS_SELI : Z := 0x82280.       (* the Int-7 value pod *)
Definition RS_SELS : Z := 0x81150.       (* the params Struct's header and its pod count *)
Definition RS_C : Z := 0x8127c.          (* the pod loop's head *)
Definition RS_D0 : Z := 0x81334.         (* ent_build case 0 (the head-amp key), with input left *)
Definition RS_D0E : Z := 0x813a0.        (* ent_build case 0 with no input left *)
Definition RS_D1 : Z := 0x817c4.
Definition RS_D2 : Z := 0x816ac.
Definition RS_D3 : Z := 0x81710.
Definition RS_D4 : Z := 0x81668.
Definition RS_D5 : Z := 0x81804.
Definition RS_D6 : Z := 0x81880.
Definition RS_D7 : Z := 0x81754.
Definition RS_D8 : Z := 0x818d0.
Definition RS_D9 : Z := 0x81954.
Definition RS_G : Z := 0x8150c.          (* case 0 after the digits, the reverse and the odd_ch part *)
Definition RS_J : Z := 0x81e00.          (* the pod is built: the inlined pod_write_ent begins *)
Definition RS_CL : Z := 0x82484.         (* the params Struct's size word is about to be patched *)
Definition RS_LATCH : Z := 0x82528.      (* the property loop's latch, from the Struct's close *)
Definition RS_LATCHI : Z := 0x8252c.     (* its second entry, from the Int-7 piece after its reload (`j` 0x82448) *)
Definition RS_LATCH7 : Z := 0x82530.     (* its third entry, from the shape-7 piece *)
Definition RS_P : Z := 0x826d0.          (* the builder's end, entered with no property *)
Definition RS_P1 : Z := 0x826d4.         (* its second entry, from the latch *)
Definition RS_R : Z := 0x82808.          (* the corruption loop's head *)
Definition RS_RT : Z := 0x82888.         (* after the corruption: corrupt := 1, then the second request *)
(* inside the checks (M02) *)
Definition RS_E : Z := 0x82930.          (* the inlined expect_rate begins *)
Definition RS_O : Z := 0x829c0.          (* its outer scan head *)
Definition RS_I : Z := 0x829e4.          (* its inner scan head *)
Definition RS_KM : Z := 0x82aac.         (* a key was found: the compare and then the value *)
Definition RS_ABS : Z := 0x82b7c.        (* no pair matched: the absent check *)
Definition RS_MAL : Z := 0x82c9c.        (* the malformed check *)
Definition RS_A : Z := 0x82ca8.          (* the check is done: asked[] is set up *)
Definition RS_DEC : Z := 0x82d14.        (* the decide loop's head (one turn per asked value) *)
Definition RS_T2 : Z := 0x82e74.         (* after the loop: check_code(reac_rate_refuse_code(4), 4) *)

(* the 13 callee-saved words the prologue writes at [S - 0x68, S) (0x8071c .. 0x8074c) and the epilogue reads back
   (0x83014 .. 0x83044), in the order of their offsets -8, -0x10, ..., -0x68 *)
Definition rs_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the frame for locals is a side-stack frame of class 3 (RtPgImgA: hi_cid rate_himg_A) *)
Definition RS_CID : Z := 3.
(* the real frame below S (`addi sp,sp,-0x1e0`) *)
Definition RS_RSZ : Z := 0x1e0.
(* the events the whole run's journal records: three allocations and three releases *)
Definition RS_EV : Z := 6.

Lemma rs_pcs_himg : hi_c1 rate_himg_A = RS_C1 /\ hi_c2 rate_himg_A = RS_C2 /\ hi_c3 rate_himg_A = RS_C3 /\
  hi_c4 rate_himg_A = RS_C4 /\ hi_c5 rate_himg_A = RS_C5 /\ hi_c6 rate_himg_A = RS_C6 /\
  hi_c7 rate_himg_A = RS_C7 /\ hi_cid rate_himg_A = RS_CID /\ hi_rsz rate_himg_A = RS_RSZ.
Proof. repeat split; reflexivity. Qed.

(* The byte values of the frame's shadow at the states the walk passes through (one byte per 8-byte granule of F,
   56 granules). P0 is the prologue's pattern (RtPgImgA.rate_A_shA, the stores 0x807f4 .. 0x808d8); rs_open opens k
   granules from j (each := 0x00). PJ opens e's 13 granules 0x1e .. 0x2a (the pod loop's stores 0x81280 .. 0x812b0;
   closed again at 0x82000 .. 0x82034 / 0x82450 .. 0x82480); PG has t (0x04 .. 0x0f) and ch (0x14 .. 0x16) open as
   well, with r (0x1c) back out of scope (0x81508); PZ opens hz's granule 0x30 to its 4 bytes (0x828e4); PB opens
   asked[0]'s and asked[1]'s granules 0x32 and 0x34 too (0x82cc8, 0x82ccc) and is RtPgImgA.rate_A_shB. *)
Definition rs_P0 : list Z := rate_A_shA.
Definition rs_open (pat : list Z) (j k : nat) : list Z := firstn j pat ++ repeat 0 k ++ skipn (j + k) pat.
Definition rs_PJ : list Z := rs_open rs_P0 30 13.
Definition rs_PG : list Z := rs_open (rs_open rs_PJ 4 12) 20 3.
Definition rs_PZ : list Z := firstn 48 rs_P0 ++ [0x04] ++ skipn 49 rs_P0.
Definition rs_PB : list Z := rate_A_shB.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

Definition rs_u8s (l : list byte) : list Z := map (fun x : byte => bv_unsigned x) l.

(* a list of (location, value) facts, through RtPgBase.rt_at: a register holds the 64-bit word of v, a cell holds
   its 8 little-endian bytes *)
Definition rs_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rt_renv)
(L : list (rt_loc * Z)) : Prop :=
Forall (fun f => rt_at segs H mem regs e (fst f) (snd f)) L.

(* ========================= what every cut INSIDE a segment carries =========================
   The segment's own journal from its start (with the segment's event count: no middle segment allocates), sp / gp /
   tp as at the start, the frames, the blocks, the I/O state and the meter as at the start, and every byte outside
   the callees' stack [R - T_SEG_STK, R) and outside the ranges the segment writes as at the start. These are exactly
   the clauses of RtPgCSpec.rt_seg_post without its pc and its result, so the cut at a segment's last pc IS that
   segment's post. *)
Definition rs_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).

(* ================== the fixed data of a segment's walk ==================
   One record for everything a segment's contract fixes before its first instruction: the harness's journal so far
   (its start state and the journal's parameters), the registers at the segment's first pc, the run's quantities e
   (RtPgBase.rt_renv: S, R, F, the three blocks, len, the seven header values, the input cursor and what is left of
   it), the position of the frame for locals among the side stack's frames of its class, and the read-only range. A
   cut inside the segment is a predicate over this record and the state at the cut. *)
Record rs_scx := RSCx {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z);
x_ly : alayout; x_S : astate; x_W0 : world segs; x_mem0 : word -> option byte; x_md0 : Model;
x_own : list (Z * Z); x_k : Z; x_regs : bvmap 5 word;
x_lyc : alayout; x_Sc : astate; x_W : world segs; x_memc : word -> option byte; x_mdc : Model;
x_RLO : Z; x_RHI : Z; x_e : rt_renv; x_pos : Z }.

(* what every segment's contract asks at its start (RtPgCSpec.rt_seg_pre at image A's record) *)
Definition rs_pre (cx : rs_scx) : Prop :=
rt_seg_pre segs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
(x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)
rate_himg_A (x_RLO cx) (x_RHI cx) (x_e cx) (x_pos cx).

(* the journal-and-frame part of a cut inside the segment, with the segment's write set E *)
Definition rs_core (cx : rs_scx) (E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rs_mid (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
(x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) E ly2 S2 W2 regs2 mem2 md2.

(* the three segments' write sets, as their contracts state them: the image's ranges (RtPgImgA: hi_w1 / hi_w2 /
   hi_w3) and the block the segment fills; the list's also lets runtime-owned bytes change (its two callees take and
   release side-stack frames of their own) *)
Definition rs_E1 (cx : rs_scx) : Z -> Prop :=
fun a => rt_inw (x_e cx) (hi_w1 rate_himg_A) a \/
q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE.
Definition rs_E2 (cx : rs_scx) : Z -> Prop :=
fun a => rt_inw (x_e cx) (hi_w2 rate_himg_A) a \/
q_pod (x_e cx) <= a < q_pod (x_e cx) + q_len (x_e cx).
Definition rs_E3 (cx : rs_scx) : Z -> Prop :=
fun a => rt_inw (x_e cx) (hi_w3 rate_himg_A) a \/
q_buf (x_e cx) <= a < q_buf (x_e cx) + rt_bl (q_buflen (x_e cx)) \/ aowned B (x_lyc cx) (x_Sc cx) a.

(* the first block's bytes at a cut *)
Definition rs_pp_at (cx : rs_scx) (W2 : world segs) (mem2 : word -> option byte) (l : list byte) : Prop :=
garr8 segs (mrestrict (w_H W2) mem2) (q_pp (x_e cx)) (rs_u8s l).
(* the frame's shadow bytes at a cut *)
Definition rs_fsh_at (cx : rs_scx) (W2 : world segs) (mem2 : word -> option byte) (pat : list Z) : Prop :=
rt_fsh segs (w_H W2) mem2 (q_F (x_e cx)) pat.
(* the values at a cut's locations *)
Definition rs_at_cx (cx : rs_scx) (W2 : world segs) (mem2 : word -> option byte) (regs2 : bvmap 5 word)
(L : list (rt_loc * Z)) : Prop :=
rs_at (w_H W2) mem2 regs2 (x_e cx) L.

(* What is left of the input the build reads: a suffix of the bytes after the 7-byte header, and the cursor that
   names it. q_src is where those bytes lie and q_left how many there are. *)
Definition rs_suffix (rest r : list byte) : Prop := exists j, (j <= length rest)%nat /\ r = skipn j rest.
Definition rs_cur (cx : rs_scx) (rest r : list byte) : Z :=
q_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r).
(* the input bytes, as rate_build_contract gives them: at q_src, outside the callees' stack, the ranges the
   segment writes and the first block *)
Definition rs_in (cx : rs_scx) (rest : list byte) : Prop :=
q_left (x_e cx) = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_src (x_e cx)) (rs_u8s rest) /\
range_addressable (aview segs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (q_src (x_e cx)) (q_left (x_e cx)) /\
(0 < q_left (x_e cx) -> shadow_hull_vis (aview segs (w_H (x_W cx)) (x_memc cx)) (q_src (x_e cx)) (q_left (x_e cx))) /\
amem_range (q_src (x_e cx)) (q_left (x_e cx)) /\
0 < q_src (x_e cx) /\ q_src (x_e cx) + q_left (x_e cx) <= 2 ^ 63 /\
(forall a, q_src (x_e cx) <= a < q_src (x_e cx) + q_left (x_e cx) ->
 ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) /\ ~ rt_inw (x_e cx) (hi_w1 rate_himg_A) a /\
 ~ (q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE)).

(* ===================================================================================================
   THE BUILD (M01): the cuts of rate_build_contract's walk, from C1 = 0x809e0 to C2 = 0x828b4
   ===================================================================================================
   The builder writes one object into the first block. Its state at a cut is the record so far (a Model.pb_cut: the
   shape sh, the properties ps written and, inside a params Struct, the pods es written), what is left of the input,
   and the loop counters; the block holds Layout.pc_image of that state and the R-relative cells hold the loop's
   constants and counters. Every list below was measured on rate's code: each value is set on every path into its
   cut and read after it. *)

(* The constants the preheader (0x80d38 .. 0x80e0c) puts in R-relative cells and no piece writes again:
   0x15555556 is the `% 12u` multiplier (pod.h:354, 0x80dc4), 0x10003 is SPA_PROP_VOLUME (0x80dcc), 0x80001 is
   SPA_PROP_params (0x80dd4), -0x4001 and -0x3ffd are the two capacity bounds (0x80e0c, 0x80a9c), R+0x28 and R+0x30
   are the top size word's offset (0: the block's length before the header) and its address, and R+0x90 holds the
   `v / 10` multiplier of the digit loop (pod.h:240-241, 0x80de4; read at 0x8137c). The flags byte is in R+0x58 from
   E01 on. *)
Definition RS_MULT10 : Z := 0xcccccccd * 2 ^ 32.
Definition rs_Kc (cx : rs_scx) (sh np : Z) : list (rt_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x10, 0x15555556); (LCell XR 0x18, q_F e); (LCell XR 0x28, 0); (LCell XR 0x30, q_pp e);
 (LCell XR 0x60, q_F e + 0x100); (LCell XR 0x78, q_F e); (LCell XR 0x58, q_fl e); (LCell XR 0x68, 0x10003);
 (LCell XR 0x70, q_pp e + 0x4010); (LCell XR 0x80, 0x80001); (LCell XR 0x88, q_pp e + 0x400c);
 (LCell XR 0x98, q_F e + 0xa0); (LCell XR 0xa0, q_pp e + 0x4014);
 (LCell XR 0xa8, Z.shiftr (q_pp e + 0x4d14) 3); (LCell XR 0xb0, q_pp e + 0x4000);
 (LCell XR 0xb8, q_pp e + 0x4d14); (LCell XR 0xc0, q_pp e); (LCell XR 0xd0, np); (LCell XR 0xd8, sh);
 (LCell XR 0xe8, shadow_addr (q_pp e + 0x4000)); (LCell XR 0x108, q_F e + 0xf8); (LCell XR 0x118, -0x4001);
 (LCell XR 0x130, -0x3ffd); (LCell XR 0x138, q_F e + 0xf0); (LCell XR 0x90, RS_MULT10)].

(* The six header values E01 spilled (fuzz_rate.c:236-239) that M01 never writes again, from B7 on (b3 moves from s7
   to R+0x20 at 0x809f8; b4 and b6 are kept shifted left by 8); the checks read them back. *)
Definition rs_Hc (cx : rs_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x20, q_b3 e); (LCell XR 0x38, Z.shiftl (q_b6 e) 8); (LCell XR 0x40, q_b5 e);
 (LCell XR 0x48, Z.shiftl (q_b4 e) 8); (LCell XR 0x50, q_buflen e); (LCell XR 0x120, q_mask e)].

(* the registers the property loop keeps: s0 = S, s1 = R, s4 = the frame's shadow base, s2 = the runtime's shadow
   offset, s3 = &r, s5 = &t, s7 = &pp->len, s11 = the block. Most of its cuts also have s10 = -0x4001 (the capacity
   bound, reloaded from R+0x118); G and P have another value there, so it is listed per cut. *)
Definition rs_Rc0 (cx : rs_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 20, shadow_addr (q_F e)); (LReg 18, SHADOW_OFF);
 (LReg 19, q_F e + 0xe0); (LReg 21, q_F e + 0x20); (LReg 23, q_pp e + 0x4000)].
Definition rs_Rc (cx : rs_scx) : list (rt_loc * Z) := rs_Rc0 cx ++ [(LReg 27, q_pp (x_e cx))].

(* the cursor: in the header cuts in.p is in s9 and in.n in t0; from the preheader on in.p is the cell R+0x100
   (0x80d40) and in.n the register s8 (0x80e08); in the pod loop both are registers (s9, s8) *)
Definition rs_cur2h (cx : rs_scx) (rest r : list byte) : list (rt_loc * Z) :=
[(LReg 25, rs_cur cx rest r); (LReg 5, Z.of_nat (length r))].
Definition rs_cur2 (cx : rs_scx) (rest r : list byte) : list (rt_loc * Z) :=
[(LCell XR 0x100, rs_cur cx rest r); (LReg 24, Z.of_nat (length r))].

(* the two header reads of pod_build (pod.h:385-386): the shape and the property count *)
Definition rs_sh (rest : list byte) : Z := fst (Cursor.fuzz_u8 rest) mod 8.
Definition rs_np (rest : list byte) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))) mod 4.
Definition rs_r0 (rest : list byte) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))).
(* the record the loop may have built: what Model.pod_rec_wf asks of its parts *)
Definition rs_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2 ^ 32 /\ pval_wf (snd kv)) ps /\
Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.
Definition rs_plen (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))).
Definition rs_seen (ps : list (Z * pval)) : Z := Z.b2z (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps).
Definition rs_first (ps : list (Z * pval)) : Z :=
Z.b2z (negb (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps)).
(* the offset of an open params Struct's size word: the property's key and flags are already written *)
Definition rs_at_of (sh : Z) (ps : list (Z * pval)) : Z := rs_plen sh ps + 8.

(* ---------------- the build's first own cuts: 0x80b28 (shape 7) and 0x80b94 (any other shape) ----------
   The block was filled with zeros (0x809f4), the two header bytes were read, and the top size word was written as
   four zero bytes with len := 4 (0x80ab0 .. 0x80b00). a0 is that length, a1 = len - 0x3ffd is the capacity test's
   left side, a5 = pp + 0 and a6 = 0 are the top word's address and offset, s3 = 0x5000 is the constant the
   preheader turns into &pp->n_ent, s6 is the shadow address of &pp->len, and s8 = s10 = F. *)
Definition rs_L_hdr (cx : rs_scx) (sh np : Z) (rest r : list byte) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 10, 4); (LReg 11, 4 - 0x3ffd); (LReg 15, q_pp e); (LReg 16, 0); (LReg 19, 0x5000); (LReg 8, q_S e);
 (LReg 9, q_R e); (LReg 20, shadow_addr (q_F e)); (LReg 18, SHADOW_OFF); (LReg 23, q_pp e + 0x4000);
 (LReg 24, q_F e); (LReg 26, q_F e); (LReg 27, q_pp e); (LCell XR 0x58, q_fl e); (LCell XR 0xd0, np);
 (LCell XR 0xd8, sh); (LReg 22, shadow_addr (q_pp e + 0x4000)); (LCell XR 0x130, -0x3ffd)]
++ rs_Hc cx ++ rs_cur2h cx rest r.
(* the block's bytes before the object's header: the top size word only *)
Definition rs_img_hdr : list byte := pp_image (le32 0) false false false [] false.
Definition rs_cut_hdr (cx : rs_scx) (rest r : list byte) (sh np : Z)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_hdr cx sh np rest r) /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_pp_at cx W2 mem2 rs_img_hdr /\
rs_in cx rest /\ rs_suffix rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ r = rs_r0 rest.
Definition rs_cut_B7 (cx : rs_scx) (rest r : list byte) (np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_cut_hdr cx rest r 7 np ly2 S2 W2 regs2 mem2 md2.
Definition rs_cut_BO (cx : rs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_cut_hdr cx rest r sh np ly2 S2 W2 regs2 mem2 md2 /\ sh <> 7.

(* ---------------- PH = 0x80d38: the header is written, the preheader is about to run ----------------
   The block holds the image of the empty record of this shape (its header bytes and, for an Object, is_props); a6
   and a5 still hold the top word's offset and address, which the preheader spills (0x80d38, 0x80d3c). *)
Definition rs_L_PH (cx : rs_scx) (sh np : Z) (rest r : list byte) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 15, q_pp e); (LReg 16, 0); (LReg 19, 0x5000); (LReg 8, q_S e); (LReg 9, q_R e);
 (LReg 20, shadow_addr (q_F e)); (LReg 18, SHADOW_OFF); (LReg 23, q_pp e + 0x4000); (LReg 24, q_F e);
 (LReg 26, q_F e); (LReg 27, q_pp e); (LCell XR 0x58, q_fl e); (LCell XR 0xd0, np); (LCell XR 0xd8, sh);
 (LReg 22, shadow_addr (q_pp e + 0x4000)); (LCell XR 0x130, -0x3ffd)]
++ rs_Hc cx ++ rs_cur2h cx rest r.
Definition rs_cut_PH (cx : rs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_PH cx sh np rest r) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh [] None)) /\
rs_in cx rest /\ rs_suffix rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ r = rs_r0 rest.

(* ---------------- N = 0x80e10: the property loop's head, |ps| properties written ----------------
   The property index is in a6 and `seen` in s9; s6 is the shadow address of &pp->len (0x80a80, or reloaded from
   R+0xe8). R+0xf8 is NOT part of the state: the pc writes it. *)
Definition rs_L_N (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rs_Rc cx ++ [(LReg 26, -0x4001); (LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000));
             (LReg 16, Z.of_nat (length ps)); (LReg 25, rs_seen ps)]
++ rs_Kc cx sh np ++ rs_Hc cx ++ rs_cur2 cx rest r.
Definition rs_cut_N (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_N cx sh np ps rest r) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (rs_r0 rest).

(* ---------------- the two ends of one property's selector (pod.h:399-423) ----------------
   SEL7 0x80e6c (shape 7: the property is an Int pod with no key) and SELK 0x81018 (any other shape: the key, its
   flags and the `first` test). a0 is pp->len at the cut and a2 = len - 0x3ffd its capacity test's left side; a1 is
   the selector byte at SELK. *)
Definition rs_L_SEL (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rs_Rc cx ++ [(LReg 26, -0x4001); (LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000));
             (LReg 10, rs_plen sh ps); (LReg 12, rs_plen sh ps - 0x3ffd); (LReg 25, rs_seen ps)]
++ rs_Kc cx sh np ++ rs_Hc cx ++ [(LCell XR 0xf8, Z.of_nat (length ps))] ++ rs_cur2 cx rest r.
(* what every cut of one property's body shares with N, with the tie of ps to the input: the properties written are
   the ones Model.props_loop makes of the bytes after the two header reads *)
Definition rs_prop_base (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
ps = fst (props_loop sh (length ps) (rs_r0 rest)) /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3.
Definition rs_cut_SEL7 (cx : rs_scx) (np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_prop_base cx 7 np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_SEL cx 7 np ps rest r) /\
rs_pp_at cx W2 mem2 (pc_image (PbCut 7 ps None)) /\
r = snd (Cursor.fuzz_u8 (snd (props_loop 7 (length ps) (rs_r0 rest)))).
Definition rs_cut_SELK (cx : rs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_SEL cx sh np ps rest r ++ [(LReg 11, sel)]) /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
sh <> 7 /\ 0 <= sel < 256 /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))).

(* ---------------- the two ends of the key piece (pod.h:407-423) ----------------
   SELI 0x82280 writes the Int value pod of a property whose value is an Int (the volume property, and a params
   property whose selector has bit 4 set), SELS 0x81150 opens a params Struct. On both, the key word and the flags
   word are already written, so the block's bytes are the record's image with those eight bytes appended; `at`
   (R+0xe0) is the open Struct's size word offset and a0 = at - 0x3ffd is the capacity test's left side (0x8113c ..
   0x81144); s6 is the shadow address of &pp->len (read at 0x8119c / 0x822c8). The cells R+0xc8 (seen') and R+0x110
   (first) are written on both arms (0x8110c, 0x8112c, before the arm test 0x81148), with the volume arm's values
   (seen, 0) when sel mod 4 = 0. *)
Definition rs_img_key (sh : Z) (ps : list (Z * pval)) (kk : Z) : list byte :=
pp_image (pc_buf (PbCut sh ps None) ++ le32 kk ++ le32 0)
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
(* the key the selector chooses (Model.prop_step): the volume property, else the params property *)
Definition rs_key_of (sel : Z) : Z := if sel mod 4 =? 0 then 0x10003 else 0x80001.
Definition rs_L_KEY (cx : rs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rs_Rc cx ++ [(LReg 26, -0x4001); (LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000));
             (LReg 10, rs_at_of sh ps - 0x3ffd)]
++ rs_Kc cx sh np ++ rs_Hc cx
++ [(LCell XR 0xf8, Z.of_nat (length ps)); (LCell XR 0xe0, rs_at_of sh ps);
    (LCell XR 0xc8, if sel mod 4 =? 0 then rs_seen ps else 1);
    (LCell XR 0x110, if sel mod 4 =? 0 then 0 else rs_first ps)]
++ rs_cur2 cx rest r.
Definition rs_cut_SELI (cx : rs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_KEY cx sh np sel ps rest r) /\
rs_pp_at cx W2 mem2 (rs_img_key sh ps (rs_key_of sel)) /\ sh <> 7 /\ 0 <= sel < 256 /\
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))).
Definition rs_cut_SELS (cx : rs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_KEY cx sh np sel ps rest r) /\
rs_pp_at cx W2 mem2 (rs_img_key sh ps 0x80001) /\ sh <> 7 /\ 0 <= sel < 256 /\
sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))).

(* ---------------- C = 0x8127c: the pod loop's head, |es| pods written ----------------
   The cursor is in s9 / s8 here and R+0x100 is dead (the pod loop uses it as scratch; CL rewrites it from s9); the
   pod index is in a1 (the pc spills it to R+0x128), the count in R+0xf0, `at` in R+0xe0, `first` in R+0x110 and
   seen' = 1 in R+0xc8. The frame's shadow is still the prologue's: the pc at 0x81280 opens e's granules. *)
Definition rs_L_pod (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (rest r : list byte)
: list (rt_loc * Z) :=
rs_Rc cx ++ [(LReg 26, -0x4001)] ++ rs_Kc cx sh np ++ rs_Hc cx
++ [(LCell XR 0xf8, Z.of_nat (length ps)); (LCell XR 0xe0, rs_at_of sh ps);
    (LCell XR 0xf0, cnt); (LCell XR 0xc8, 1); (LCell XR 0x110, rs_first ps);
    (LReg 24, Z.of_nat (length r)); (LReg 25, rs_cur cx rest r)].
(* What every cut inside the pod loop shares, with the tie of the count and the pods to the input: the selector
   picked the params Struct, the count byte gave cnt = c mod 33 (pod.h:425) and the pods written are the ones
   Model.ents_loop makes of what follows it, leaving rr at the turn's start. *)
Definition rs_pod_tie (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent) (rest rr : list byte)
: Prop :=
exists sel c r1 r2,
(sel, r1) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))) /\
(c, r2) = Cursor.fuzz_u8 r1 /\ cnt = c mod 33 /\ sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
ents_loop (length es) r2 = (es, rr).
Definition rs_pod_base (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_in cx rest /\ rs_suffix rest r /\ rs_suffix rest rr /\ rs_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
ps = fst (props_loop sh (length ps) (rs_r0 rest)) /\
rs_pod_tie sh ps cnt es rest rr /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ (length es < 32)%nat /\ Z.of_nat (length es) < cnt.
Definition rs_cut_C (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest r r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_pod cx sh np ps cnt rest r ++ [(LReg 11, Z.of_nat (length es))]) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))).

(* ---------------- the eleven entries of ent_build's switch (pod.h:265-379) ----------------
   The dispatch (0x81280 .. 0x81330) opens e's granules, fills e with zeros (0x812c0), reads the kind byte and jumps
   through the nine relative entries at .rodata 0x20f64; `bltu a2,a1` 0x8130c takes case 9 and `beqz s8` 0x812c4
   takes case 0 with no input left. At every entry a4 is the kind byte's address, s9 the cursor after it, s8 what is
   left after it, a5 what was left before it, s6 the sign-extended kind byte and a0 that byte shifted left by 56;
   a7 = 10 and a2 = 8 are the two constants of the `% 10` and of the table's bound; s10 = -0x4001. The pod loop's
   cells (rs_podc) hold the property index, `at`, the count, seen' = 1, `first` and the pod index. *)
Definition rs_pc_D (kd : Z) : Z :=
if kd mod 10 =? 0 then RS_D0 else if kd mod 10 =? 1 then RS_D1 else if kd mod 10 =? 2 then RS_D2
else if kd mod 10 =? 3 then RS_D3 else if kd mod 10 =? 4 then RS_D4 else if kd mod 10 =? 5 then RS_D5
else if kd mod 10 =? 6 then RS_D6 else if kd mod 10 =? 7 then RS_D7 else if kd mod 10 =? 8 then RS_D8
else RS_D9.
Definition rs_podc (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent) : list (rt_loc * Z) :=
[(LCell XR 0xf8, Z.of_nat (length ps)); (LCell XR 0xe0, rs_at_of sh ps); (LCell XR 0xf0, cnt);
 (LCell XR 0xc8, 1); (LCell XR 0x110, rs_first ps); (LCell XR 0x128, Z.of_nat (length es))].
Definition rs_L_Dc0 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rt_loc * Z) :=
rs_Rc0 cx ++ rs_Kc cx sh np ++ rs_Hc cx ++ rs_podc sh ps cnt es.
Definition rs_L_Dc (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rt_loc * Z) :=
rs_L_Dc0 cx sh np ps cnt es ++ [(LReg 27, q_pp (x_e cx))].
(* Case 9 is reached by `bltu a2,a1` 0x8130c, before the instructions 0x81314 .. 0x8132c that form the table's
   address and shift and sign-extend the kind byte, so a2 holds the table's address and a0 and s6 the kind byte's two
   forms only on the nine table entries; on case 9 a2 is still the bound 8. *)
Definition rs_L_D (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (kd : Z) : list (rt_loc * Z) :=
rs_L_Dc cx sh np ps cnt es
++ [(LReg 26, -0x4001); (LReg 15, Z.of_nat (length r) + 1);
    (LReg 14, rs_cur cx rest r - 1); (LReg 25, rs_cur cx rest r); (LReg 24, Z.of_nat (length r));
    (LReg 17, 10)]
++ (if kd mod 10 =? 9 then [(LReg 12, 8)]
    else [(LReg 12, 0x20f64); (LReg 22, kd - 256 * (kd / 128)); (LReg 10, kd * 2 ^ 56)]).
(* rr is what is left of the input when the turn begins (at C); the kind byte is the first of it and r what is left
   after it, so the pod the turn builds is Model.ent_build rr. *)
Definition rs_cut_D (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (kd : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_D cx sh np ps cnt es rest r kd) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0xf0) (rs_u8s (zeros 104)) /\
rs_suffix rest rr /\ (kd, r) = Cursor.fuzz_u8 rr /\ 0 <= kd < 256 /\ rr <> [].
(* the same with no input left: the kind byte reads as 0 and the cursor does not move (fuzz.h:37-43) *)
Definition rs_cut_D0E (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_Dc cx sh np ps cnt es ++ [(LReg 26, -0x4001); (LReg 24, 0); (LReg 25, rs_cur cx rest [])]) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0xf0) (rs_u8s (zeros 104)).

(* ---------------- G = 0x8150c: case 0 after the digits, the reverse and the odd_ch part ----------------
   t and ch are in scope and r is out of scope again (0x81508; the odd_ch path never opens it), so the frame's shadow
   is neither the prologue's nor the pod loop's: rs_PG is that state. s6 = &ch, s11 = the second input byte of the
   head-amp key, s9 the cursor and s10 what is left; ch holds the key's first part with its NUL. *)
(* what case 0 reads of the turn's input before G: the kind byte, then c and p (pod.h:224-262); chs is the key's
   first part, the decimal text of c mod 64 or the odd_ch string of c mod 14. *)
Definition rs_g_of (rr : list byte) : list byte * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Definition rs_cut_G (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (pb : Z) (chs : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_Dc0 cx sh np ps cnt es
 ++ [(LReg 26, Z.of_nat (length r)); (LReg 22, q_F (x_e cx) + 0xa0); (LReg 27, pb);
     (LReg 25, rs_cur cx rest r)]) /\
rs_fsh_at cx W2 mem2 rs_PG /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0xa0) (rs_u8s (chs ++ [NUL])) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0xf0) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (chs, pb, r) = rs_g_of rr /\
(length chs <= 21)%nat /\ 0 <= pb < 256.

(* ---------------- J = 0x81e00: the pod is built; the inlined pod_write_ent begins ----------------
   e holds Layout.ent_mem of the pod ent_build made of the turn's input, the cursor is in s9 and what is left in s8,
   and s6, s7 and s11 hold the three values the cases reload from R+0xe8, R+0xb0, R+0xc0. *)
Definition rs_cut_J (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (ed : ent) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_Dc cx sh np ps cnt es
 ++ [(LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000)); (LReg 25, rs_cur cx rest r);
     (LReg 24, Z.of_nat (length r)); (LReg 26, -0x4001)]) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0xf0) (rs_u8s (ent_mem ed)) /\
(ed, r) = ent_build rr /\ ent_wf ed.

(* ---------------- CL = 0x82484: the count is reached; the Struct's size word is patched ----------------
   The pod loop wrote cnt pods and e is out of scope again (0x82000 .. 0x82034, or never opened when the count is
   0). *)
Definition rs_cut_CL (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_Kc cx sh np ++ rs_Hc cx
 ++ [(LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000)); (LReg 26, -0x4001); (LReg 25, rs_cur cx rest r);
     (LReg 24, Z.of_nat (length r));
     (LCell XR 0xf8, Z.of_nat (length ps)); (LCell XR 0xe0, rs_at_of sh ps);
     (LCell XR 0xc8, 1); (LCell XR 0x110, rs_first ps)]) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
ps = fst (props_loop sh (length ps) (rs_r0 rest)) /\
rs_pod_tie sh ps cnt es rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ Z.of_nat (length es) = cnt.

(* ---------------- the latch 0x82528 / 0x8252c / 0x82530: one property is written ----------------
   At 0x82528 (from the Struct's close) the property index and `seen` are still in cells (the pc and the next one load
   them); at 0x8252c (from the Int-7 piece, after its own reload of the index) the index is in a6 and `seen` in its
   cell; at 0x82530 (from the shape-7 piece) both are in a6 and s9. *)
Definition rs_latch_body (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
sh = rs_sh rest /\ np = rs_np rest /\ 1 <= Z.of_nat (length ps) <= np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (rs_r0 rest).
Definition rs_L_LATCH (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rs_Rc cx ++ rs_Kc cx sh np ++ rs_Hc cx
++ [(LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000)); (LReg 26, -0x4001);
    (LCell XR 0xf8, Z.of_nat (length ps) - 1); (LCell XR 0xc8, rs_seen ps)]
++ rs_cur2 cx rest r.
Definition rs_cut_LATCH (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_LATCH cx sh np ps rest r).
Definition rs_cut_LATCHI (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_LATCH cx sh np ps rest r ++ [(LReg 16, Z.of_nat (length ps) - 1)]).
Definition rs_cut_LATCH7 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_Kc cx sh np ++ rs_Hc cx
 ++ [(LReg 22, shadow_addr (q_pp (x_e cx) + 0x4000)); (LReg 26, -0x4001);
     (LReg 16, Z.of_nat (length ps) - 1); (LReg 25, rs_seen ps)]
 ++ rs_cur2 cx rest r).

(* ---------------- P = 0x826d0 / P1 = 0x826d4: every property is written ----------------
   0x826d0 is entered only when the object has no property (0x80d6c, before the preheader writes its constant
   cells), with what is left in t0; 0x826d4 is the latch's exit, where `mv s8,t0` 0x826d0 has moved it into s8. *)
Definition rs_L_P (cx : rs_scx) (rest r : list byte) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 20, shadow_addr (q_F e)); (LReg 18, SHADOW_OFF);
 (LReg 23, q_pp e + 0x4000); (LReg 27, q_pp e); (LReg 22, shadow_addr (q_pp e + 0x4000));
 (LCell XR 0x18, q_F e); (LCell XR 0x28, 0); (LCell XR 0x30, q_pp e); (LCell XR 0x78, q_F e);
 (LCell XR 0x58, q_fl e); (LCell XR 0xa8, Z.shiftr (q_pp e + 0x4d14) 3);
 (LCell XR 0xb8, q_pp e + 0x4d14); (LCell XR 0xc0, q_pp e);
 (LCell XR 0x100, rs_cur cx rest r)] ++ rs_Hc cx.
Definition rs_Pbody (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) = np /\
(ps, r) = props_loop sh (length ps) (rs_r0 rest).
Definition rs_cut_P (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_P cx rest r ++ [(LReg 5, Z.of_nat (length r))]).
Definition rs_cut_P1 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_P cx rest r ++ [(LReg 24, Z.of_nat (length r))]).

(* ---------------- R = 0x82808 and RT = 0x82888: the corruption (pod.h:441-448) ----------------
   The object is complete (its top size word was patched), so the block holds the image of the record with no
   corruption yet. The loop writes one byte a turn: a3 = kk is the index, a2 = cnt - kk what is left of the count the
   input byte gave (`andi a2,a2,7` 0x827dc, decremented at 0x82860), a4 = off, a0 is the cursor of the byte reads and
   a5 what is left of the input. It also leaves through `bgeu a1,a6` 0x8281c when off + kk reaches the length, so the
   bytes written, bs, are the first min(cnt, len - off) of the input's. At RT the corruption is done but the corrupt
   word is NOT yet written (`sw a0,0(s9)` 0x8289c is after the cut), so the block still holds the image with corrupt
   false and the record's own bytes. s9 = &pp->corrupt (0x82734 .. 0x82738). *)
Definition rs_L_post (cx : rs_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 20, shadow_addr (q_F e)); (LReg 18, SHADOW_OFF);
 (LReg 23, q_pp e + 0x4000); (LReg 27, q_pp e); (LReg 22, shadow_addr (q_pp e + 0x4000));
 (LReg 25, q_pp e + 0x4d18);
 (LCell XR 0x18, q_F e); (LCell XR 0x78, q_F e); (LCell XR 0x58, q_fl e);
 (LCell XR 0xa8, Z.shiftr (q_pp e + 0x4d14) 3); (LCell XR 0xb8, q_pp e + 0x4d14);
 (LCell XR 0xc0, q_pp e)] ++ rs_Hc cx.
(* the block's bytes with the first kk corruption bytes written at off *)
Definition rs_img_corr (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (kk : Z) : list byte :=
pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn (Z.to_nat kk) bs))
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Definition rs_corr_wf (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (cnt : Z) : Prop :=
8 <= off /\ off + Z.of_nat (length bs) <= rs_plen sh ps /\ (length bs <= 7)%nat /\
0 < cnt <= 7 /\ Z.of_nat (length bs) = Z.min cnt (rs_plen sh ps - off).
Definition rs_cut_R (cx : rs_scx) (sh : Z) (ps : list (Z * pval)) (rest r : list byte)
(off : Z) (bs : list byte) (cnt kk : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_post cx ++ [(LReg 13, kk); (LReg 12, cnt - kk); (LReg 14, off);
                  (LReg 10, rs_cur cx rest r); (LReg 15, Z.of_nat (length r))]) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (rs_img_corr sh ps off bs kk) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
rs_corr_wf sh ps off bs cnt /\ 0 <= kk < cnt /\ kk <= Z.of_nat (length bs) /\
skipn (Z.to_nat kk) bs = fst (fuzz_u8s (length bs - Z.to_nat kk) r).
Definition rs_cut_RT (cx : rs_scx) (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_post cx) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (rs_img_corr sh ps off bs (Z.of_nat (length bs))) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
8 <= off /\ off + Z.of_nat (length bs) <= rs_plen sh ps /\ (length bs <= 7)%nat.

(* ---------------- C2 = 0x828b4: the build is done; the second request is in a0 ----------------
   This cut IS rate_build_contract's post, at the pc its contract names (hi_c2 rate_himg_A): the C2 value list, the
   frame's shadow back to the prologue's, and the block holding Layout.pp_bytes of the record. *)
Definition rs_cut_C2 (cx : rs_scx) (rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L2 rate_himg_A) /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_pp_at cx W2 mem2 (pp_bytes (fst (pod_build rest))) /\
q_len (x_e cx) = rt_len rest.

(* ===================================================================================================
   THE CHECKS (M02): the cuts of rate_check_contract's walk, from C3 = 0x828b8 to C4 = 0x82e84
   ===================================================================================================
   The first block holds Layout.pp_bytes of the record some input made; the segment copies its first len bytes into
   the second block, puts 0x5a5a5a5a into hz (F+0x180, its granule in scope from 0x828e4 on: rs_PZ), runs the parse on
   the copy (or on NULL, by bit 0 of the flags byte), scans the record's entries for the rate key when the record is
   uncorrupted and runs the check its answer selects, sets up asked[0] and asked[1] in the frame (their granules in
   scope from 0x82cc8 / 0x82ccc on: rs_PB), runs the decide turn twice and then check_code(refuse_code(4), 4). From
   the parse on, the float state is some fx2 that keeps every float register outside fa0, fa3, fa4 and fa5 and has a
   zero rounding mode. *)
(* the parse's answer on the block's bytes (NULL by bit 0 of the flags byte), the expectation the inlined scan
   computes, and hz after the parse: the value the parse wrote, else the 0x5a5a5a5a the harness put there *)
Definition rs_PA (cx : rs_scx) (rec : pod_rec) : option Z * Z :=
Rate.harness_parse (Z.testbit (q_fl (x_e cx)) 0) (buf rec).
Definition rs_E0 (rec : pod_rec) : option Z * Z := Rate.expect_model false rec.
Definition rs_hz (cx : rs_scx) (rec : pod_rec) : Z := Rate.written_or 0x5a5a5a5a (rs_PA cx rec).
(* the two asked values (fuzz_rate.c:262): rc == 1 ? hz : 48000, and the u32 `other` of header bytes 3 .. 6 in the
   form 0x82ca8 .. 0x82cd8 computes it from the cells, (b4 << 8 | b3) | (b6 << 8 | b5) << 16 (its 4 bytes are what
   asked[1] holds; the code reads it back with a sign-extending `lw`) *)
Definition rs_ask0 (cx : rs_scx) (rec : pod_rec) : Z :=
if snd (rs_PA cx rec) =? 1 then rs_hz cx rec else 48000.
Definition rs_other (e : rt_renv) : Z :=
Z.lor (Z.lor (Z.shiftl (q_b4 e) 8) (q_b3 e)) (Z.shiftl (Z.lor (Z.shiftl (q_b6 e) 8) (q_b5 e)) 16).
(* what every cut of the checks carries, with the frame's shadow pattern pat (rs_PZ until the asked set-up, rs_PB
   from the decide loop on) *)
Definition rs_chk_base (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (pat : list Z)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_fxk [10; 13; 14; 15] fx fx2 /\
rs_fsh_at cx W2 mem2 pat /\ rom_view segs W2 mem2 /\
rs_pp_at cx W2 mem2 (pp_bytes rec) /\
pod_rec_wf rec /\ q_len (x_e cx) = Z.of_nat (length (buf rec)) /\
q_pod (x_e cx) <> 0 /\ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)).
(* the hz cell, at every cut after the parse *)
Definition rs_hz_at (cx : rs_scx) (rec : pod_rec) (W2 : world segs) (mem2 : word -> option byte) : Prop :=
val_mem segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x180) 4 (rs_hz cx rec mod 2 ^ 32).
(* the two asked cells, from the asked set-up on *)
Definition rs_ask_at (cx : rs_scx) (rec : pod_rec) (W2 : world segs) (mem2 : word -> option byte) : Prop :=
val_mem segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x190) 4 (rs_ask0 cx rec mod 2 ^ 32) /\
val_mem segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x1a0) 4 (rs_other (x_e cx)).
(* the values every cut of the checks carries up to the asked set-up: s0 = S, s1 = R, s4 = the frame's shadow base,
   s2 = the runtime's shadow offset, s5 = &hz (0x828c4), pod in R+0x138 (0x828fc), F in R+0x18, the flags byte in
   R+0x58 and the six header cells *)
Definition rs_L_chk (cx : rs_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 20, shadow_addr (q_F e)); (LReg 18, SHADOW_OFF);
 (LCell XR 0x138, q_pod e); (LReg 21, q_F e + 0x180);
 (LCell XR 0x18, q_F e); (LCell XR 0x58, q_fl e)] ++ rs_Hc cx.

(* ---------------- E = 0x82930: the inlined expect_rate begins ----------------
   Reached when the record is uncorrupted (`bnez a0` 0x82928 not taken) and bit 0 of the flags byte is clear
   (`bnez s3` 0x8292c not taken); s8 = rc (0x82918), s6 = F (0x82924), s10 = the flags byte (0x828e8). *)
Definition rs_cut_E (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 23, q_pp (x_e cx) + 0x4000); (LReg 24, snd (rs_PA cx rec));
                 (LReg 22, q_F (x_e cx)); (LReg 27, q_pp (x_e cx));
                 (LCell XR 0x78, q_F (x_e cx));
                 (LCell XR 0xa8, Z.shiftr (q_pp (x_e cx) + 0x4d14) 3);
                 (LCell XR 0xb8, q_pp (x_e cx) + 0x4d14); (LCell XR 0xc0, q_pp (x_e cx));
                 (LReg 26, q_fl (x_e cx))]) /\
rs_hz_at cx rec W2 mem2 /\
Z.testbit (q_fl (x_e cx)) 0 = false /\ corrupt rec = false /\
Rate.parse_model (buf rec) = rs_E0 rec.

(* ---------------- O = 0x829c0: the outer scan's head ----------------
   t3 = n_ent, s3 = n_ent - 1, a1 = at, and the five fixed operands of the scan: t2 and s10 = &ent[0],
   t6 = &ent[0] + 4, t4 and t5 = &ent[0] + 8; s11 = -1 and s9 = 8 (POD_STRING) are the scan's two constants. *)
Definition rs_L_scan (cx : rs_scx) (rec : pod_rec) : list (rt_loc * Z) :=
let e := x_e cx in
rs_L_chk cx ++
[(LReg 24, snd (rs_PA cx rec)); (LReg 27, -1); (LReg 25, 8);
 (LReg 28, Z.of_nat (length (ents rec))); (LReg 19, Z.of_nat (length (ents rec)) - 1);
 (LReg 7, q_pp e + 0x4014); (LReg 26, q_pp e + 0x4014);
 (LReg 31, q_pp e + 0x4018); (LReg 29, q_pp e + 0x401c); (LReg 30, q_pp e + 0x401c);
 (LCell XR 0x78, q_F e); (LCell XR 0xc0, q_pp e)].
Definition rs_scan_inv (rec : pod_rec) (j : nat) : Prop :=
(j <= length (ents rec))%nat /\
rs_E0 rec = Rate.rate_of_pairs Rate.expect_value (pairs_by key_of (skipn j (ents rec)) None).
Definition rs_chk_rec (cx : rs_scx) (rec : pod_rec) : Prop :=
corrupt rec = false /\ is_props rec = true /\ params_struct rec = true /\
snd (rs_PA cx rec) = snd (rs_E0 rec) /\ fst (rs_PA cx rec) = fst (rs_E0 rec).
Definition rs_cut_O (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (j : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_scan cx rec ++ [(LReg 11, Z.of_nat j); (LReg 14, 104)]) /\
rs_hz_at cx rec W2 mem2 /\ rs_scan_inv rec j /\ rs_chk_rec cx rec.

(* ---------------- I = 0x829e4: pod_next_pair's inner head, scanning from at0 for a key ----------
   a4 = 104 * at0 is fixed, s6 = m and s7 = m + 1, and the five operand registers advance by 104 a turn, so the entry
   the turn reads is &ent[m] with m the inner index. *)
Definition rs_cut_I (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_scan cx rec ++
 [(LReg 14, 104 * Z.of_nat at0); (LReg 22, Z.of_nat m); (LReg 23, Z.of_nat m + 1);
  (LReg 16, q_pp (x_e cx) + 0x4014 + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 15, q_pp (x_e cx) + 0x4014 + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 12, q_pp (x_e cx) + 0x4018 + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 13, q_pp (x_e cx) + 0x401c + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 17, q_pp (x_e cx) + 0x401c + 104 * (Z.of_nat m - Z.of_nat at0))]) /\
rs_hz_at cx rec W2 mem2 /\ rs_scan_inv rec at0 /\ rs_chk_rec cx rec /\
(at0 <= m < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None).

(* ---------------- KM = 0x82aac: entry m is a key and entry m + 1 is its value ----------
   a0 is the key's body address, s6 = m + 1 the value's index and s7 = m + 2 the next `at`; the five operands are
   spilled around the string compare (0x82ac0 .. 0x82ad0) and reloaded after it. *)
Definition rs_cut_KM (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat) (kb : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_scan cx rec ++
 [(LReg 10, q_pp (x_e cx) + 0x401c + 104 * Z.of_nat m); (LReg 22, Z.of_nat m + 1);
  (LReg 23, Z.of_nat m + 2)]) /\
rs_hz_at cx rec W2 mem2 /\ rs_scan_inv rec at0 /\ rs_chk_rec cx rec /\
(at0 <= m)%nat /\ (m + 1 < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None) /\
key_of (nth m (ents rec) (Ent 0 0 [])) = Some kb.

(* ---------------- the two checks the answer selects, and the join after them ----------------
   ABS 0x82b7c: no pair of the record has the rate key (or there is no params Struct), so the answer is (None, 0) and
   check_absent runs. MAL 0x82c9c: the answer is (None, -1) (the NULL flag, no Props object, or a value no reader
   takes) and check_malformed runs. A 0x82ca8: the check is done (or skipped, for a corrupted record) and the asked
   set-up begins; s10 is the flags byte again (0x828e8, or reloaded at 0x82b30 / 0x82b8c), whose bit 1 is the role;
   pp is only in R+0xc0 (s11 is -1 after the scan). *)
Definition rs_cut_ABS (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 24, 0); (LCell XR 0x78, q_F (x_e cx)); (LCell XR 0xc0, q_pp (x_e cx))]) /\
rs_hz_at cx rec W2 mem2 /\ fst (rs_PA cx rec) = None /\ snd (rs_PA cx rec) = 0.
Definition rs_cut_MAL (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 24, -1); (LReg 22, q_F (x_e cx)); (LReg 26, q_fl (x_e cx));
                 (LCell XR 0x78, q_F (x_e cx)); (LCell XR 0xc0, q_pp (x_e cx))]) /\
rs_hz_at cx rec W2 mem2 /\ fst (rs_PA cx rec) = None /\ snd (rs_PA cx rec) = -1.
Definition rs_cut_A (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 24, snd (rs_PA cx rec)); (LReg 22, q_F (x_e cx)); (LReg 26, q_fl (x_e cx));
                 (LCell XR 0x78, q_F (x_e cx)); (LCell XR 0xc0, q_pp (x_e cx))]) /\
rs_hz_at cx rec W2 mem2.

(* ---------------- DEC = 0x82d14, the decide loop's head, and T2 = 0x82e74 after it ----------------
   Both turns enter with asked[0] and asked[1] in their cells and in scope (rs_PB). Turn t (0 or 1) has a0 =
   &asked[t] (F+0x190 from 0x82cc0, then F+0x1a0 from the latch's `mv a0,s6` 0x82e54) and the turn flag s3 = 1 - t
   (0x82d0c, then 0x82e58); s5 = the role (flags bit 1, 0x82cf8), s6 = F+0x1a0 (0x82cd0), s10 = mask (0x82d10),
   s11 = &closed_list (0x82d04 .. 0x82d08: RS_CLOSED). What D, T2 and C4 all carry is rs_L_dec, the values of
   RtPgImgA's hi_L4. *)
Definition RS_CLOSED : Z := 0x21520.
Lemma rs_closed_himg : In (RS_CLOSED, RateCfg.closed_list) (hi_i32 rate_himg_A).
Proof. exact (or_introl eq_refl). Qed.
Definition rs_L_dec (cx : rs_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 20, shadow_addr (q_F e));
 (LCell XR 0x18, q_F e); (LCell XR 0x50, q_buflen e); (LCell XR 0x78, q_F e);
 (LCell XR 0xc0, q_pp e); (LCell XR 0x120, q_mask e); (LCell XR 0x138, q_pod e)].
Definition rs_L_DEC (cx : rs_scx) (t : Z) : list (rt_loc * Z) :=
let e := x_e cx in
rs_L_dec cx ++
[(LReg 18, SHADOW_OFF); (LReg 10, q_F e + 0x190 + 0x10 * t); (LReg 19, 1 - t);
 (LReg 21, Z.b2z (Z.testbit (q_fl e) 1)); (LReg 22, q_F e + 0x1a0); (LReg 26, q_mask e);
 (LReg 27, RS_CLOSED)].
Definition rs_cut_DEC (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (t : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PB ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_DEC cx (Z.of_nat t)) /\
rs_ask_at cx rec W2 mem2 /\ (t < 2)%nat.
Definition rs_cut_T2 (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec rs_PB ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_dec cx).

(* ---------------- C4 = 0x82e84: the checks are done ----------------
   This cut IS rate_check_contract's post, at the pc its contract names (hi_c4 rate_himg_A). *)
Definition rs_cut_C4 (cx : rs_scx) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_fxk [10; 13; 14; 15] fx fx2 /\
rt_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L4 rate_himg_A) /\
rs_fsh_at cx W2 mem2 rs_PB.

(* ===================================================================================================
   THE LIST (M03): rate_csv_contract's walk, from C6 = 0x82e98 to C7 = 0x82ed4 (15 instructions, no internal cut)
   ===================================================================================================
   C7 IS rate_csv_contract's post, at the pc its contract names (hi_c7 rate_himg_A). *)
Definition rs_cut_C7 (cx : rs_scx) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E3 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_fxk [10] fx fx2 /\
rt_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L7 rate_himg_A) /\
rs_fsh_at cx W2 mem2 rs_PB.

(* ===================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   ===================================================================================================
   One per cut, with the LOOP INDEX as an argument (and never under the inner quantifier), so that the latch of a
   loop can hand the head its next index and the closure is an induction on the index, not a circular hypothesis:
   rs_from_N .. (S i) is what the property loop's latch gives, rs_from_C .. i (S k) what the pod loop's latch gives,
   rs_from_DEC .. (S t) what the decide loop's latch gives. A piece lemma is `<its start premises> -> <the
   continuations of its end cuts> -> <the continuation of its start cut>`, so a lane proving one piece takes the other
   lanes' continuations as hypotheses and never sees their proofs. POST is generic. *)
Section f.
Variable cx : rs_scx.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.

Definition rs_from_B7 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r np, rs_cut_B7 cx rest r np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_B7 regs2 mem2 md2) POST.
Definition rs_from_BO : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, rs_cut_BO cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_BO regs2 mem2 md2) POST.
Definition rs_from_PH : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, rs_cut_PH cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_PH regs2 mem2 md2) POST.
Definition rs_from_N (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = i)%nat ->
rs_cut_N cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_N regs2 mem2 md2) POST.
Definition rs_from_SEL7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 np ps r, (length ps = i)%nat ->
rs_cut_SEL7 cx np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_SEL7 regs2 mem2 md2) POST.
Definition rs_from_SELK (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
rs_cut_SELK cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_SELK regs2 mem2 md2) POST.
Definition rs_from_SELI (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
rs_cut_SELI cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_SELI regs2 mem2 md2) POST.
Definition rs_from_SELS (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
rs_cut_SELS cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_SELS regs2 mem2 md2) POST.
Definition rs_from_C (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_C cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_C regs2 mem2 md2) POST.
Definition rs_from_D (i k : nat) (kd : Z) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r, (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_D cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (rs_pc_D kd) regs2 mem2 md2) POST.
Definition rs_from_D0E (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es, (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_D0E cx sh np ps cnt es rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_D0E regs2 mem2 md2) POST.
Definition rs_from_G (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs, (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_G cx sh np ps cnt es rest rr r pb chs ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_G regs2 mem2 md2) POST.
Definition rs_from_J (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed, (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_J cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_J regs2 mem2 md2) POST.
Definition rs_from_CL (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat ->
rs_cut_CL cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_CL regs2 mem2 md2) POST.
Definition rs_from_LATCH (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
rs_cut_LATCH cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_LATCH regs2 mem2 md2) POST.
Definition rs_from_LATCHI (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
rs_cut_LATCHI cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_LATCHI regs2 mem2 md2) POST.
Definition rs_from_LATCH7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
rs_cut_LATCH7 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_LATCH7 regs2 mem2 md2) POST.
Definition rs_from_P : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
rs_cut_P cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_P regs2 mem2 md2) POST.
Definition rs_from_P1 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
rs_cut_P1 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_P1 regs2 mem2 md2) POST.
Definition rs_from_R (kk : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt,
rs_cut_R cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_R regs2 mem2 md2) POST.
Definition rs_from_RT : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps off bs r,
rs_cut_RT cx sh ps off bs rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_RT regs2 mem2 md2) POST.
Definition rs_from_C2 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2,
rs_cut_C2 cx rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (hi_c2 rate_himg_A) regs2 mem2 md2) POST.
(* the cuts of the checks and of the list reach their pc at the run's own float state *)
Definition rs_from_E : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_E cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_E regs2 mem2 md2) POST.
Definition rs_from_O (j : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_O cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_O regs2 mem2 md2) POST.
Definition rs_from_I (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_I cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_I regs2 mem2 md2) POST.
Definition rs_from_KM (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec kb, rs_cut_KM cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_KM regs2 mem2 md2) POST.
Definition rs_from_ABS : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_ABS cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_ABS regs2 mem2 md2) POST.
Definition rs_from_MAL : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_MAL cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_MAL regs2 mem2 md2) POST.
Definition rs_from_A : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_A cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_A regs2 mem2 md2) POST.
Definition rs_from_DEC (t : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_DEC cx fx2 rec t ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_DEC regs2 mem2 md2) POST.
Definition rs_from_T2 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_T2 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_T2 regs2 mem2 md2) POST.
Definition rs_from_C4 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, rs_cut_C4 cx fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs (hi_c4 rate_himg_A) regs2 mem2 md2) POST.
Definition rs_from_C7 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, rs_cut_C7 cx fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs (hi_c7 rate_himg_A) regs2 mem2 md2) POST.
End f.

(* ===================================================================================================
   THE PIECE STATEMENTS, one or more per piece of the three middle segments (pieces W3a .. W14; the
   harness-level pieces W2, W9 and the two malloc steps are stated in Section h below)
   =================================================================================================== *)
(* W3a: C1 -> the object's header (pod.h:384-395): the NULL test (dead), the block's memset, the two header reads,
   the top size word, and the header of this shape. Its start is the segment's own start state, which is
   rate_build_contract's premise set. *)
Definition rs_start_M01 (cx : rs_scx) (rest : list byte) : Prop :=
rs_pre cx /\
rt_fsh segs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shA rate_himg_A) /\
rt_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L1 rate_himg_A) /\
q_len (x_e cx) = rt_len rest /\ rs_in cx rest.
Definition rs_piece_W3a_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_B7 cx POST rest -> rs_from_BO cx POST rest ->
SRr segs (x_W cx) (cfg_at segs (hi_c1 rate_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
(* W3b: the two header pieces and the property loop's preheader (pod.h:389-398). *)
Definition rs_piece_W3b_hdr_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_PH cx POST rest -> rs_from_BO cx POST rest.
Definition rs_piece_W3b_b7_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_PH cx POST rest -> rs_from_B7 cx POST rest.
Definition rs_piece_W3b_pre_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_N cx POST rest 0 -> rs_from_P cx POST rest ->
rs_from_PH cx POST rest.
(* W4: one property's selector, its shape-7 body, its key, and the loop's latch (from its three entries). *)
Definition rs_piece_W4_sel_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_SEL7 cx POST rest i -> rs_from_SELK cx POST rest i ->
rs_from_N cx POST rest i.
Definition rs_piece_W4_int7_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_LATCH7 cx POST rest i -> rs_from_SEL7 cx POST rest i.
Definition rs_piece_W4_key_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_SELS cx POST rest i -> rs_from_SELI cx POST rest i ->
rs_from_SELK cx POST rest i.
Definition rs_piece_W4_latch_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_N cx POST rest (S i) -> rs_from_P1 cx POST rest ->
rs_from_LATCH cx POST rest i /\ rs_from_LATCHI cx POST rest i /\ rs_from_LATCH7 cx POST rest i.
(* W5: the Int-7 value pod (it enters the latch at its second entry), the params Struct's header and count, and its
   close (pod.h:412-438). *)
Definition rs_piece_W5_int_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_LATCHI cx POST rest i -> rs_from_SELI cx POST rest i.
Definition rs_piece_W5_open_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_C cx POST rest i 0 -> rs_from_CL cx POST rest i ->
rs_from_SELS cx POST rest i.
Definition rs_piece_W5_close_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_LATCH cx POST rest i -> rs_from_CL cx POST rest i.
(* W6a: the switch's dispatch and its two input-driven exits, then cases 2 and 3. *)
Definition rs_piece_W6a_disp_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 cx rest -> (forall kd, rs_from_D cx POST rest i k kd) -> rs_from_D0E cx POST rest i k ->
rs_from_C cx POST rest i k.
Definition rs_piece_W6a_cases_stmt : Prop :=
forall cx POST rest i k kd,
rs_start_M01 cx rest -> In (kd mod 10) [2; 3] -> rs_from_J cx POST rest i k ->
rs_from_D cx POST rest i k kd.
(* W6b: cases 1, 4, 5 and 9. W6c: cases 6, 7 and 8. *)
Definition rs_piece_W6b_stmt : Prop :=
forall cx POST rest i k kd,
rs_start_M01 cx rest -> In (kd mod 10) [1; 4; 5; 9] -> rs_from_J cx POST rest i k ->
rs_from_D cx POST rest i k kd.
Definition rs_piece_W6c_stmt : Prop :=
forall cx POST rest i k kd,
rs_start_M01 cx rest -> In (kd mod 10) [6; 7; 8] -> rs_from_J cx POST rest i k ->
rs_from_D cx POST rest i k kd.
(* W7a: case 0 up to the parts, from both its entries. W7b: the parts and the key's text. *)
Definition rs_piece_W7a_stmt : Prop :=
forall cx POST rest i k kd,
rs_start_M01 cx rest -> kd mod 10 = 0 -> rs_from_G cx POST rest i k ->
rs_from_D cx POST rest i k kd /\ rs_from_D0E cx POST rest i k.
Definition rs_piece_W7b_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 cx rest -> rs_from_J cx POST rest i k -> rs_from_G cx POST rest i k.
(* W8: the inlined pod_write_ent and the record copy (pod.h:428-432), then the pod loop's latch. *)
Definition rs_piece_W8_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 cx rest -> rs_from_C cx POST rest i (S k) -> rs_from_CL cx POST rest i ->
rs_from_J cx POST rest i k.
(* W10: the top size word, the corruption and the second block's request (pod.h:440-448, fuzz.h:73). *)
Definition rs_piece_W10_post_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> (forall kk, rs_from_R cx POST rest kk) -> rs_from_RT cx POST rest ->
rs_from_C2 cx POST rest ->
rs_from_P cx POST rest /\ rs_from_P1 cx POST rest.
Definition rs_piece_W10_corr_stmt : Prop :=
forall cx POST rest kk,
rs_start_M01 cx rest -> rs_from_R cx POST rest (S kk) -> rs_from_RT cx POST rest ->
rs_from_R cx POST rest kk.
Definition rs_piece_W10_req_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_C2 cx POST rest -> rs_from_RT cx POST rest.
(* W11a: the second block's fill, hz := 0x5a5a5a5a, the parse, the record's three tests and the two scan loops. Its
   start is rate_check_contract's premise set. The head leaves to E (uncorrupted record, flags bit 0 clear), MAL
   (uncorrupted, bit 0 set: the expectation is -1) and A (corrupted: no check). *)
Definition rs_start_M02 (cx : rs_scx) (inp : list byte) : Prop :=
rs_pre cx /\
rt_fsh segs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shA rate_himg_A) /\
rt_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L3 rate_himg_A) /\
q_len (x_e cx) = rt_len inp /\
rs_pp_at cx (x_W cx) (x_memc cx) (pp_bytes (fst (pod_build inp))) /\
q_pod (x_e cx) <> 0 /\ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)) /\
YK0o.frm_zero (@fp_csr fx).
Definition rs_piece_W11a_head_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_E cx POST -> rs_from_MAL cx POST -> rs_from_A cx POST ->
SRr segs (x_W cx) (cfg_at segs (hi_c3 rate_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
Definition rs_piece_W11a_setup_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_O cx POST 0 -> rs_from_ABS cx POST -> rs_from_MAL cx POST ->
rs_from_E cx POST.
Definition rs_piece_W11a_outer_stmt : Prop :=
forall cx POST inp j,
rs_start_M02 cx inp -> rs_from_I cx POST j j -> rs_from_ABS cx POST ->
rs_from_O cx POST j.
Definition rs_piece_W11a_inner_stmt : Prop :=
forall cx POST inp at0 m,
rs_start_M02 cx inp -> rs_from_I cx POST at0 (S m) -> rs_from_KM cx POST at0 m ->
rs_from_ABS cx POST ->
rs_from_I cx POST at0 m.
(* W11b: the key compare, the value's two readers and check_rate, and the absent and malformed checks. *)
Definition rs_piece_W11b_key_stmt : Prop :=
forall cx POST inp at0 m,
rs_start_M02 cx inp -> rs_from_O cx POST (S (S m)) -> rs_from_ABS cx POST ->
rs_from_MAL cx POST -> rs_from_A cx POST ->
rs_from_KM cx POST at0 m.
Definition rs_piece_W11b_checks_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_A cx POST ->
rs_from_ABS cx POST /\ rs_from_MAL cx POST.
(* W13: one decide turn (fuzz_rate.c:263-269) on asked[t], parametric in the turn: reac_rate_cfg_decide, the
   expectation (the role test, the two unrolled bit_of scans over closed_list), check_decide, reac_rate_refuse_code,
   check_code, reac_rate_bit, reac_rate_is_closed, reac_rate_best_drivable and check_list; the latch takes the turn
   flag (s3 = 1 on turn 0, 0 on turn 1) and goes back to the head with asked[1] or leaves to T2. The continuation at
   turn 2 is never used (the cut holds only for t < 2). *)
Definition rs_piece_W13_stmt : Prop :=
forall cx POST inp t,
rs_start_M02 cx inp -> rs_from_DEC cx POST (S t) -> rs_from_T2 cx POST ->
rs_from_DEC cx POST t.
(* W14: the asked[] set-up (fuzz_rate.c:262: asked[0] and asked[1] into scope and filled) up to the decide loop's
   first turn, the loop's tail (check_code(reac_rate_refuse_code(4), 4)) up to C4, and the list segment M03 (C6 ->
   C7: memset(buf, 0x5a, bl), reac_rate_drivable_csv, check_csv), whose start is rate_csv_contract's premise set.
   The malloc(buf) step C4 -> C6 is Section h's rh_S_C46_stmt. *)
Definition rs_piece_W14_asked_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_DEC cx POST 0 -> rs_from_A cx POST.
Definition rs_piece_W14_tail_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_C4 cx POST -> rs_from_T2 cx POST.
Definition rs_start_M03 (cx : rs_scx) : Prop :=
rs_pre cx /\
rt_fsh segs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shB rate_himg_A) /\
rt_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L6 rate_himg_A) /\
frames (x_Sc cx) = [(hi_cid rate_himg_A, x_pos cx)] /\
q_buf (x_e cx) <> 0 /\ In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_ly cx) (x_S cx)) /\
YK0o.frm_zero (@fp_csr fx).
Definition rs_piece_W14_csv_stmt : Prop :=
forall cx POST,
rs_start_M03 cx -> rs_from_C7 cx POST ->
SRr segs (x_W cx) (cfg_at segs (hi_c6 rate_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.

(* ===================================================================================================
   THE HARNESS LEVEL: the cuts C1 .. C7 relative to the harness's ENTRY state, the two malloc steps and the five
   segment statements S_E01 .. S_X01 (lib/Prog/LLVMFuzzerTestOneInput_c.v's names, in its continuation form)
   ===================================================================================================
   The whole run is chained in this order:
     ENTRY --S_E01--> C1 --rate_build_contract--> C2 --malloc(pod)--> C3 --rate_check_contract--> C4
     --malloc(buf)--> C6 --rate_csv_contract--> C7 --S_X01--> return,
   and S_M01 = C1 -> C3, S_M02 = C3 -> C4, S_M03 = C4 -> C7. Each harness cut is a self-contained state relative to the
   harness's ENTRY state (the record rh_hcx) and its journal from there (rh_j: FP = [], own = the frame for locals, k
   events so far): the frame F = frame_addr of the ENTRY layout (class 3, position pos), the run's quantities e with
   the header values and the input cursor tied to the input bytes (rh_hdr), the blocks made so far (appended to the
   entry's and not among them), the cut's values (RtPgImgA hi_L1 .. hi_L7), the frame's shadow, and the carried cells.
   - Left out on purpose: rt_seg_pre's static conjuncts (the registered globals' and the strings' shadow, the
     read-only cells and tables, rom_view, the real frame's checked cells, arodata_okP), which the chaining
     re-derives at C1, C3 and C6 from AR and the journal (rh_static_law, the journal's image clause); and the
     presence of the frame's bytes and shadow, which AR_frames_law gives at every state.
   - What must survive from C1 to C7 across the three middle contracts and the two malloc calls is carried by the
     contracts' "every byte outside the callees' stack and the write set is kept" clauses and the malloc rule's
     acall_kept: the 13 callee-saved words the prologue stores at [S - 0x68, S) (ra at S - 8, s0 at S - 16, ...,
     s11 at S - 0x68: `sd ra,0x1d8(sp)` 0x8071c .. `sd s11,0x178(sp)` 0x8074c after `addi sp,sp,-0x1e0`) and the
     frame's flag pointer word at F + 0x1f8 (the class-3 frame law's last word; the release stores 0 through it at
     0x82f20 .. 0x82f24). Both are rh_kept, over RtPgBase's cell form rt_at (LCell).
   - frame_addr and flag_addr read only ly_F, which every journal's layout_le keeps (YG0f.v layout_le), so one F
     serves every cut.
   - C4, C6 and C7 follow the float-changing parse, pod_nearest and the snprintf wrapper: each takes the cut's own
     float state with a zero rounding mode. *)
Section h.
(* the read-only range and the harness constants of RtPgCSpec.rt_lib_contract_x (image A: RtPgLib.RO_LO / RO_HI and
   the relocated frame's ACfn.RA_LLVMF / A_EMPTY / EV_LIB / LIVE_LIB / LLVMF_STK) *)
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* The 13 save slots as RtPgBase cells: S - 8 - 8 j holds the entry value of the j-th register of rs_saved_regs. *)
Definition rh_saves_L (regs0 : bvmap 5 word) : list (rt_loc * Z) :=
  map (fun j => (LCell XS (- 8 - 8 * Z.of_nat j), bv_unsigned (getr regs0 (nth j rs_saved_regs 0%bv)))) (seq 0 13).
(* The cells carried from C1 to C7: the saves, and the frame's flag pointer word at F + 0x1f8. *)
Definition rh_cells (regs0 : bvmap 5 word) (fl : Z) : list (rt_loc * Z) :=
  rh_saves_L regs0 ++ [(LCell XF 0x1f8, fl)].

(* ============================== the harness's entry ============================== *)
Record rh_hcx := RHCx {
h_ly : alayout; h_S : astate; h_W : world segs; h_regs : bvmap 5 word; h_mem : word -> option byte; h_md : Model;
h_p : Z; h_n : Z; h_pl : list byte }.

(* What every harness-level segment may use of the entry: RtPgCSpec.rt_lib_pre_x without the parts only the final
   leaf reads (asink_none, the fd and fs facts, ameta_inv, the meter) and without its float clause (which the
   segments after the parse, running at the float state it returns, must not mention). *)
Definition rh_base (hx : rh_hcx) : Prop :=
afn_pre segs B LLVMF_STK (h_ly hx) (h_S hx) (h_W hx) (h_regs hx) (h_mem hx) (h_md hx) [] /\
raZ (h_regs hx) = RA_LLVMF /\
getr (h_regs hx) 10 = w64 (h_p hx) /\ getr (h_regs hx) 11 = w64 (h_n hx) /\
((h_n hx = 0 /\ h_p hx = A_EMPTY) \/ (0 < h_n hx < 2 ^ 26 /\ In (h_p hx, h_n hx) (ablocks B (h_ly hx) (h_S hx)))) /\
h_n hx = Z.of_nat (length (h_pl hx)) /\
garr8 segs (mrestrict (w_H (h_W hx)) (h_mem hx)) (h_p hx) (map (fun b : byte => bv_unsigned b) (h_pl hx)) /\
frames (h_S hx) = [] /\ st_nev (h_S hx) + EV_LIB <= EV_MAX /\ blocks_bytes (h_S hx) + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H (h_W hx)) (h_mem hx)).

(* The harness's journal from its entry: no footprint, own = the frames taken, k events. *)
Definition rh_j (hx : rh_hcx) (own : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world segs)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx) own ly' S' W' mem' md' k.

(* The geometry: S the entry sp, R the 32-aligned base of the real frame, F the class-3 frame at pos. *)
Definition rh_geo (hx : rh_hcx) (pos : Z) (e : rt_renv) : Prop :=
q_S e = spZ (h_regs hx) /\ q_R e = 32 * ((q_S e - RS_RSZ) / 32) /\ q_F e = frame_addr (h_ly hx) RS_CID pos.

(* The carried cells (the 13 saves, the flag pointer) at a state. *)
Definition rh_kept (hx : rh_hcx) (pos : Z) (e : rt_renv) (W' : world segs) (mem' : word -> option byte)
(regs' : bvmap 5 word) : Prop :=
Forall (fun f => rt_at segs (w_H W') mem' regs' e (fst f) (snd f))
(rh_cells (h_regs hx) (flag_addr (h_ly hx) RS_CID pos)).

(* The header (fuzz_rate.c:236-239, fuzz.h:37-56: fuzz_u8 reads one byte, or gives 0 and reads nothing when no byte
   is left; fuzz_u32 is four fuzz_u8, little-endian): byte i of the input or 0; flags = byte 0, mask = byte 1,
   buflen = byte 2 mod 24, other = bytes 3 .. 6; pod_build reads the input after these 7 bytes, at
   p + min(7, n), n - min(7, n) of them (the plain walk's g_u8 .. g_k, lib/Prog/SlotInv.v). *)
Definition rh_u8 (pl : list byte) (i : nat) : Z :=
match nth_error pl i with Some b => bv_unsigned b | None => 0 end.
Definition rh_hdr (hx : rh_hcx) (e : rt_renv) (rest : list byte) : Prop :=
q_fl e = rh_u8 (h_pl hx) 0 /\ q_mask e = rh_u8 (h_pl hx) 1 /\ q_buflen e = rh_u8 (h_pl hx) 2 mod 24 /\
q_b3 e = rh_u8 (h_pl hx) 3 /\ q_b4 e = rh_u8 (h_pl hx) 4 /\ q_b5 e = rh_u8 (h_pl hx) 5 /\
q_b6 e = rh_u8 (h_pl hx) 6 /\
rest = skipn 7 (h_pl hx) /\ q_src e = h_p hx + Z.min 7 (h_n hx) /\ q_left e = h_n hx - Z.min 7 (h_n hx) /\
q_len e = rt_len rest.

(* rate_build_contract's input premises at rest (RtPgCSpec.v rate_build_contract, after rt_cut). *)
Definition rh_input (W' : world segs) (mem' : word -> option byte) (e : rt_renv) (rest : list byte) : Prop :=
q_left e = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H W') mem') (q_src e) (map (fun x : byte => bv_unsigned x) rest) /\
range_addressable (aview segs (w_H W') mem') SHADOW_OFF (q_src e) (q_left e) /\
0 < q_src e /\ q_src e + q_left e <= 2 ^ 63 /\ amem_range (q_src e) (q_left e) /\
(0 < q_left e -> shadow_hull_vis (aview segs (w_H W') mem') (q_src e) (q_left e)) /\
(forall a, q_src e <= a < q_src e + q_left e ->
 ~ (q_R e - T_SEG_STK <= a < q_R e) /\ ~ rt_inw e (hi_w1 rate_himg_A) a /\ ~ (q_pp e <= a < q_pp e + Layout.PP_SIZE)).

(* What every harness cut shares: the journal at k events with the frame for locals as the only frame, the blocks
   made so far (bl, in the order they were made) appended to the entry's and none of them among the entry's, sp = R,
   gp, tp, the geometry, the header tie, the header bounds, the carried cells, and the cut's values. *)
Definition rh_common (hx : rh_hcx) (pos : Z) (e : rt_renv) (rest : list byte) (k : Z) (bl : list (Z * Z))
(L : list (rt_loc * rt_x))
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_j hx [(RS_CID, pos)] ly2 S2 W2 mem2 md2 k /\ frames S2 = [(RS_CID, pos)] /\
Permutation (ablocks B ly2 S2) (ablocks B (h_ly hx) (h_S hx) ++ bl) /\
Forall (fun b => ~ In b (ablocks B (h_ly hx) (h_S hx))) bl /\
getr regs2 2 = w64 (q_R e) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
rh_geo hx pos e /\ rh_hdr hx e rest /\ rt_hdr_ok e /\
rt_cut segs (w_H W2) mem2 regs2 e L /\
rh_kept hx pos e W2 mem2 regs2.

(* ============================== C1: what S_E01 delivers ==============================
   The frame taken, malloc(pp) done (one event, the block appended), the prologue's frame shadow, the C1 values
   (RtPgImgA hi_L1), and the input after the 7-byte header (rh_input at rest = skipn 7 of the input). *)
Definition rh_cut_C1 (hx : rh_hcx) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 1 [(q_pp e, Layout.PP_SIZE)] (hi_L1 rate_himg_A) ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rs_P0 /\
rh_input W2 mem2 e rest.
(* ============================== C2: what rate_build_contract's post gives the malloc(pod) step ==============
   The C2 values (hi_L2), the prologue's shadow again, pp holding Layout.pp_bytes of the record pod_build made of
   rest, and the request's bounds (8 <= len <= 5440: RtPgCSpec's site lemma for the build). *)
Definition rh_cut_C2 (hx : rh_hcx) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 1 [(q_pp e, Layout.PP_SIZE)] (hi_L2 rate_himg_A) ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rs_P0 /\ 8 <= q_len e <= 5440 /\
garr8 segs (mrestrict (w_H W2) mem2) (q_pp e) (map (fun x : byte => bv_unsigned x) (pp_bytes (fst (pod_build rest)))).
(* ============================== C3: what the malloc(pod) step delivers ==============================
   Two events, pod appended (len bytes: len >= 8, so the request len + (len == 0) is len), the C3 values (hi_L3), the
   prologue's shadow, pp's bytes kept. *)
Definition rh_cut_C3 (hx : rh_hcx) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 2 [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e)] (hi_L3 rate_himg_A)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rs_P0 /\ 8 <= q_len e <= 5440 /\
garr8 segs (mrestrict (w_H W2) mem2) (q_pp e) (map (fun x : byte => bv_unsigned x) (pp_bytes (fst (pod_build rest)))).
(* ============================== C4: what rate_check_contract's post gives the malloc(buf) step ==============
   The C4 values (hi_L4), hz and asked in scope (rs_PB), at the cut's own float state fx4. *)
Definition rh_cut_C4 (hx : rh_hcx) (fx4 : YK11.FPState) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 2 [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e)] (hi_L4 rate_himg_A)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rs_PB /\ YK0o.frm_zero (@fp_csr fx4).
(* ============================== C6: what the malloc(buf) step delivers ==============================
   Three events, buf appended (its block length is the request rt_bl buflen in [1, 23]), the C6 values (hi_L6). *)
Definition rh_cut_C6 (hx : rh_hcx) (fx6 : YK11.FPState) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 3
  [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e); (q_buf e, rt_bl (q_buflen e))] (hi_L6 rate_himg_A)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ q_buf e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rs_PB /\
YK0o.frm_zero (@fp_csr fx6).
(* ============================== C7: what rate_csv_contract's post gives S_X01 ============================== *)
Definition rh_cut_C7 (hx : rh_hcx) (fx7 : YK11.FPState) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 3
  [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e); (q_buf e, rt_bl (q_buflen e))] (hi_L7 rate_himg_A)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ q_buf e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rs_PB /\
YK0o.frm_zero (@fp_csr fx7).

(* The return: knock's rt_post (APgRt.v) in rate's terms: at RA_LLVMF, the journal from the entry closed (own = [],
   at most the six events), the callee-saved registers restored, a0 = 0, the entry's blocks again. The float state
   is the one the configuration carries (S_X01 executes no float instruction; its callees keep the float state). *)
Definition rh_ret (hx : rh_hcx) : world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RA_LLVMF regs' mem' md' /\ YK0o.frm_zero (@fp_csr fx') /\
rh_j hx [] ly' S' W' mem' md' k /\ k <= RS_EV /\
aregs_preserved (h_regs hx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (h_ly hx) (h_S hx)).

(* ============================== the continuations at the harness cuts ============================== *)
Definition rh_from_C1 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C1 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_C1 regs2 mem2 md2) POST.
Definition rh_from_C2 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C2 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_C2 regs2 mem2 md2) POST.
Definition rh_from_C3 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C3 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RS_C3 regs2 mem2 md2) POST.
Definition rh_from_C4 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx4 pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C4 hx fx4 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx4 segs RS_C4 regs2 mem2 md2) POST.
Definition rh_from_C6 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx6 pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C6 hx fx6 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx6 segs RS_C6 regs2 mem2 md2) POST.
Definition rh_from_C7 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx7 pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C7 hx fx7 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx7 segs RS_C7 regs2 mem2 md2) POST.

(* ============================== the segment statements ==============================
   S_E01 (piece W2), ENTRY -> C1: the prologue (saves at [S - 0x68, S)); n < 2^26, so `beqz` 0x808dc falls through;
   the frame (option byte 1, __asan_stack_malloc_3(448) 0x80784), its header (0x807bc .. 0x807e8) and its shadow
   (0x807f4 .. 0x808d8); the seven header reads in their eight input-length arms (0x808e4 .. 0x809dc and the
   out-of-line block 0x82b94 .. 0x82c40); malloc(19744) at 0x809dc with ra = 0x809e0. *)
Definition S_E01 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C1 hx POST ->
SRr segs (h_W hx) (cfg_at segs RS_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) POST.
(* S_M01, C1 -> C3: rate_build_contract at rate_himg_A (from C1, with rt_seg_pre's static conjuncts from
   rh_static_law), then the malloc(pod) step (rh_S_C23_stmt). *)
Definition S_M01 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C3 hx POST -> rh_from_C1 hx POST.
(* S_M02, C3 -> C4: rate_check_contract at rate_himg_A. *)
Definition S_M02 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C4 hx POST -> rh_from_C3 hx POST.
(* S_M03, C4 -> C7: the malloc(buf) step (rh_S_C46_stmt), then rate_csv_contract at rate_himg_A. *)
Definition S_M03 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C7 hx POST -> rh_from_C4 hx POST.
(* S_X01 (piece W9), C7 -> RET: free(buf) 0x82ed8 (a0 = s5), free(pod) 0x82ee0 (a0 = R+0x138), free(pp) 0x82ee8
   (a0 = R+0xc0); hz, asked[0], asked[1] := 0xf8 (0x82ef0 .. 0x82ef8); F[0] := 0x45e0360e (0x82f0c); `bnez s8`
   0x82f10 taken (s8 = F from R+0x18); __asan_set_shadow_f5(s4, 64) 0x82f1c; the flag byte := 0 through
   F + 0x1f8 (0x82f20 .. 0x82f24); a0 = 0 and the epilogue (0x83014 .. 0x8304c). *)
Definition S_X01 : Prop :=
forall (hx : rh_hcx), rh_base hx -> rh_from_C7 hx (rh_ret hx).
Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_X01.

(* The two malloc steps the middle statements add to their contracts.
   C2 -> C3 (piece W10): the `jal` at 0x828b4 with a0 = len + (len == 0) = len (0x828a8 .. 0x828b0) and the call.
   C4 -> C6 (piece W14): `ld s3,0x50(s1)` (buflen), `seqz s7,s3`, `add s7,s3,s7`, `mv a0,s7` (0x82e84 .. 0x82e90),
   the `jal` at 0x82e94 and the call. *)
Definition rh_S_C23_stmt : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C3 hx POST -> rh_from_C2 hx POST.
Definition rh_S_C46_stmt : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C6 hx POST -> rh_from_C4 hx POST.

(* The five statements compose into the whole run: from ENTRY, the return. *)
Lemma rh_seg_chain : seg_lemmas -> forall hx : rh_hcx, rh_base hx ->
SRr segs (h_W hx) (cfg_at segs RS_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) (rh_ret hx).
Proof.
intros (HE & HM1 & HM2 & HM3 & HX) hx Hb.
exact (HE hx (rh_ret hx) Hb (HM1 hx _ Hb (HM2 hx _ Hb (HM3 hx _ Hb (HX hx Hb))))).
Qed.

(* ============================== the static facts of rt_seg_pre ==============================
   The shadow of the registered globals and of the strings, the read-only cells, the tables and every read-only byte,
   at any state AR accepts with the read-only data as in the image. They are static facts of the symbols B (the
   start-up's const cells and zero-shadow ranges, AR's am_const / al_zshadow, and the owned read-only bytes pinned as
   const cells), not facts a cut can carry: a global's shadow byte and an owned read-only byte are aowned, and the
   allocator's post keeps no aowned byte (YG0d.v acall_post). The chaining takes this law at the three middle
   contracts' starts. *)
Definition rh_static_law : Prop :=
forall ly S (W : world segs) mem md,
AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_A) /\
Forall (fun s => rt_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs rate_himg_A) /\
rt_ro_cells segs (w_H W) mem (hi_cells rate_himg_A) /\
Forall (fun t => rt_i32tab segs (w_H W) mem (fst t) (snd t)) (hi_i32 rate_himg_A) /\
Forall (fun t => rt_u64tab segs (w_H W) mem (fst t) (snd t)) (hi_u64 rate_himg_A) /\
rom_view segs W mem.
End h.

End d.
End c.
End b.
