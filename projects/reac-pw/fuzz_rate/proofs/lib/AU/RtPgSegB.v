(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSeg.v at 256ddb9487c and
   proofs/reac-pw/fuzz_role/lib/A/RPgHarn.v at 680a13dcf7c for reac-pw/fuzz_rate image A: role's pcs, registers and
   real-frame cells are replaced by the ones measured on fuzz_rate.asan and its contract file and image record by
   rate's (lib/A/RtPgCSpec.v, lib/A/RtPgImgA.v; the rl_ vocabulary becomes rt_); the build's latch gains a third
   entry; the checks' tail becomes the asked[] set-up, the decide loop and its tail; the third segment (the list), the
   two malloc steps and the five segment statements S_E01 .. S_X01 in the plain walk's continuation form are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgSeg.v at 24edf5468644 for image B
   (fuzz_rate.asan-ubsan): image B's pcs, registers, real-frame cells and frame objects, each list measured on image B's
   code; the record is lib/AU/RtPgImgB.v's and the frame's shadow lib/AU/RtPgMemB.v's; the latch has two entries; the
   pod object of the pod loop is e62; the Int pods of the shape-7 and the Int-7 pieces are written by a call. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose entry function and jump table bytes are the
   pin's): THE CUT STATES of the walk of LLVMFuzzerTestOneInput (0x8076c, 11756 bytes, 2939 instructions), the five
   segment statements and the statement of every piece the walk is split into. Statement text only: proves no
   function (kind: statement text).

   WHAT THIS FILE IS FOR. The walk is cut at the points the plain walk of the same function is cut at
   (lib/Prog/LLVMFuzzerTestOneInput_c.v): ENTRY, C1 = 0x80ae4 (malloc(pp) returned), C3 = 0x82a30 (malloc(pod)
   returned), C4 = 0x82f9c (check_code(reac_rate_refuse_code(4), 4) returned), C6 = 0x82fb0 (malloc(buf) returned),
   C7 = 0x82fec (check_csv returned) and RET. The five segments keep the plain walk's names S_E01 / S_M01 / S_M02 /
   S_M03 / S_X01 and its continuation form ("the H of the exit cut -> the H of the entry cut"). The three middle
   bodies are the fixed contracts rate_build_contract (C1 -> C2 = the malloc(pod) `jal` 0x82a2c),
   rate_check_contract (C3 -> C4) and rate_csv_contract (C6 -> C7) of lib/A/RtPgCSpec.v at image B's record
   RtPgImgB.rate_himg_B; S_M01 adds the malloc(pod) step C2 -> C3 and S_M03 the malloc(buf) step C4 -> C6 (through
   the `jal` C5 = 0x82fac). The first two contracts' walks are cut again at the heads and joins of their loops and at
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

   WHERE A VALUE LIVES. Image B keeps the harness's values in registers and in 8-byte cells of the real frame at
   R + off, R = 32 * floor((S - 0x220) / 32) being the 32-aligned base the prologue puts in sp and s1 (0x807ac,
   0x807b0) and S the entry sp (s0, 0x807a8). The locals whose address is taken live in the frame for locals F, a
   side-stack frame of class 4 that the prologue takes (0x807d8 `addi a0,zero,0x2c0`, 0x807dc the call, s8 = s9 = F at
   0x807e0 / 0x807ec): t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at F+0xf0 (the shape-7 Int
   pod), e42 (104) at F+0x180 (the Int-7 pod), e62 (104) at F+0x210 (the pod loop's pod) and hz at F+0x2a0. asked[0]
   and asked[1] are not frame objects: they are the 4-byte real-frame cells R+0x198 and R+0x19c. s3 = (F >> 3) + K
   is the frame's shadow base and s4 = K the runtime's shadow offset (until 0x82f9c). sp = R from 0x807ac to the
   epilogue. The seven header values (flags, mask, buflen = byte 2 mod 24, bytes 3 .. 6) are spilled to R-relative
   cells in E01 and the build and read back in the checks and the list. Every list below was measured on image B's
   code: each value is set on every path into its cut and read after it.

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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the pcs of the cuts ============================================
   Each is the address of the first instruction of the piece that starts there, a block leader of image B's code;
   the seven segment cuts are RtPgImgB.rate_himg_B's hi_c1 .. hi_c7 (rsb_pcs_himg). *)
Definition RSB_ENTRY : Z := 0x8076c.      (* `addi sp,sp,-0x220` *)
Definition RSB_RET : Z := 0x83088.        (* `ret` *)
Definition RSB_C1 : Z := 0x80ae4.         (* `bnez a0` after malloc(pp) (`jal` 0x80ae0) *)
Definition RSB_C2 : Z := 0x82a2c.         (* the `jal` of malloc(pod), a0 = len + (len == 0) *)
Definition RSB_C3 : Z := 0x82a30.         (* `beqz a0` after it returns *)
Definition RSB_C4 : Z := 0x82f9c.         (* `ld s4,0x18(s1)` after check_code(reac_rate_refuse_code(4), 4) returns
                                            (`jal` 0x82f98) *)
Definition RSB_C5 : Z := 0x82fac.         (* the `jal` of malloc(buf), a0 = buflen + (buflen == 0) *)
Definition RSB_C6 : Z := 0x82fb0.         (* `beqz a0` after it returns *)
Definition RSB_C7 : Z := 0x82fec.         (* `mv a0,s5` after check_csv returns (`jal` 0x82fe8), before free(buf) *)
Definition RSB_J83014 : Z := 0x83014.     (* `lui a0,0x45e03`: the frame's retirement word, after the three releases
                                            and hz's scope store *)
(* inside the build (M01) *)
Definition RSB_B7 : Z := 0x80c80.         (* the shape-7 object header *)
Definition RSB_BO : Z := 0x80d1c.         (* the Object header (shape <> 7) *)
Definition RSB_PH : Z := 0x80ea0.         (* the property loop's preheader (`sd a7,0x20(s1)`) *)
Definition RSB_N : Z := 0x80fb4.          (* `beqz t4`: the property loop's head (the selector byte's read) *)
Definition RSB_SEL7 : Z := 0x80ff4.       (* the shape-7 Int pod of one property (`sb zero,0x22(s3)`: e into scope) *)
Definition RSB_SELK : Z := 0x810a4.       (* a property's key, its flags and the `first` test *)
Definition RSB_SELI : Z := 0x82398.       (* the Int-7 value pod (`sb zero,0x34(s3)`: e42 into scope) *)
Definition RSB_SELS : Z := 0x81210.       (* the params Struct's header and its pod count *)
Definition RSB_C : Z := 0x813a0.          (* `sd a1,0x178(s1)`: the pod loop's head *)
Definition RSB_D0 : Z := 0x81460.         (* ent_build case 0 (the head-amp key), with input left *)
Definition RSB_D0E : Z := 0x814d0.        (* ent_build case 0 with no input left *)
Definition RSB_D1 : Z := 0x81900.
Definition RSB_D2 : Z := 0x817c4.
Definition RSB_D3 : Z := 0x81838.
Definition RSB_D4 : Z := 0x81774.
Definition RSB_D5 : Z := 0x81968.
Definition RSB_D6 : Z := 0x819a0.
Definition RSB_D7 : Z := 0x81888.
Definition RSB_D8 : Z := 0x819f0.
Definition RSB_D9 : Z := 0x81a94.
Definition RSB_G : Z := 0x8160c.          (* case 0 after the digits, the reverse and the odd_ch part *)
Definition RSB_J : Z := 0x820dc.          (* the pod is built: the capacity guard, then the call
                                            pod_write_ent(pp, e62) *)
Definition RSB_CL : Z := 0x824c0.         (* the params Struct's size word is about to be patched *)
Definition RSB_LATCH : Z := 0x82578.      (* the property loop's latch, from the Struct's close *)
Definition RSB_LATCH7 : Z := 0x8257c.     (* its second entry, from the shape-7 piece (`j` 0x810a0) and from the Int-7
                                            piece (`j` 0x82470) *)
Definition RSB_P : Z := 0x82684.          (* the builder's end, entered with no property *)
Definition RSB_P1 : Z := 0x82688.         (* its second entry, from the latch *)
Definition RSB_R : Z := 0x82960.          (* the corruption loop's head *)
Definition RSB_RT : Z := 0x829fc.         (* after the corruption: corrupt := 1, then the second request *)
(* inside the checks (M02) *)
Definition RSB_E : Z := 0x82aac.          (* the inlined expect_rate begins *)
Definition RSB_O : Z := 0x82b48.          (* its outer scan head *)
Definition RSB_I : Z := 0x82b74.          (* its inner scan at entry m: the instruction after the loop head 0x82b70,
                                            which tests the previous turn's result first (`bnez a0` -> KM) *)
Definition RSB_KM : Z := 0x82c40.         (* a key was found: the compare and then the value *)
Definition RSB_ABS : Z := 0x82d1c.        (* no pair matched: the absent check *)
Definition RSB_MAL : Z := 0x82de0.        (* the malformed check *)
Definition RSB_A : Z := 0x82dec.          (* the check is done: asked[] is set up *)
Definition RSB_DEC : Z := 0x82e44.        (* the decide loop's head (one turn per asked value) *)
Definition RSB_T2 : Z := 0x82f8c.         (* after the loop: check_code(reac_rate_refuse_code(4), 4) *)
(* two pcs inside one decide turn (lane W13), not cuts: the two bit_of scans over closed_list begin at 0x82e70 and the
   turn's calls after the expectation at 0x82f2c *)
Definition RSB_DBS : Z := 0x82e70.
Definition RSB_DCL : Z := 0x82f2c.

(* the 13 callee-saved words the prologue writes at [S - 0x68, S) (0x80774 .. 0x807a4) and the epilogue reads back
   (0x83050 .. 0x83080), in the order of their offsets -8, -0x10, ..., -0x68 *)
Definition rsb_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the frame for locals is a side-stack frame of class 4 (RtPgImgB: hi_cid rate_himg_B) *)
Definition RSB_CID : Z := 4.
(* the real frame below S (`addi sp,sp,-0x220`) *)
Definition RSB_RSZ : Z := 0x220.
(* the events the whole run's journal records: three allocations and three releases *)
Definition RSB_EV : Z := 6.

Lemma rsb_pcs_himg : hi_c1 rate_himg_B = RSB_C1 /\ hi_c2 rate_himg_B = RSB_C2 /\ hi_c3 rate_himg_B = RSB_C3 /\
  hi_c4 rate_himg_B = RSB_C4 /\ hi_c5 rate_himg_B = RSB_C5 /\ hi_c6 rate_himg_B = RSB_C6 /\
  hi_c7 rate_himg_B = RSB_C7 /\ hi_cid rate_himg_B = RSB_CID /\ hi_rsz rate_himg_B = RSB_RSZ.
Proof. repeat split; reflexivity. Qed.

(* The byte values of the frame's shadow at the states the walk passes through (one byte per 8-byte granule of F:
   the prologue writes 88, 0x80850 .. 0x809b0), in RtPgMemB's form rtmb_sh t ch r e e42 e62 hz (true = the object is
   in scope). P0 is the prologue's pattern (every object out of scope; RtPgMemB.rtmb_sh_P0: hi_shA rate_himg_B). PJ
   has e62's 13 granules 66 .. 78 in scope (each pod loop turn's stores 0x813a4 .. 0x813d4; out again at
   0x8217c .. / 0x82484 ..); PG has t (4 .. 15) and ch (20 .. 22) in scope as well, with r (28) back out of scope
   (0x81608); PB has hz's granule 84 in scope (0x82a60) and is RtPgMemB.rtmb_sh_PB: hi_shB rate_himg_B (image B keeps
   asked[] on the real frame, so no other object comes into scope in M02). e (30 .. 42) and e42 (48 .. 60) are in
   scope only inside the shape-7 and the Int-7 pieces, between their cuts. *)
Definition rsb_P0 : list Z := rtmb_sh false false false false false false false.
Definition rsb_PJ : list Z := rtmb_sh false false false false false true false.
Definition rsb_PG : list Z := rtmb_sh true true false false false true false.
Definition rsb_PB : list Z := rtmb_sh false false false false false false true.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

Definition rsb_u8s (l : list byte) : list Z := map (fun x : byte => bv_unsigned x) l.

(* a list of (location, value) facts, through RtPgBase.rt_at: a register holds the 64-bit word of v, a cell holds
   its 8 little-endian bytes *)
Definition rsb_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rt_renv)
(L : list (rt_loc * Z)) : Prop :=
Forall (fun f => rt_at segs H mem regs e (fst f) (snd f)) L.

(* ========================= what every cut INSIDE a segment carries =========================
   The segment's own journal from its start (with the segment's event count: no middle segment allocates), sp / gp /
   tp as at the start, the frames, the blocks, the I/O state and the meter as at the start, and every byte outside
   the callees' stack [R - T_SEG_STK, R) and outside the ranges the segment writes as at the start. These are exactly
   the clauses of RtPgCSpec.rt_seg_post without its pc and its result, so the cut at a segment's last pc IS that
   segment's post. *)
Definition rsb_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
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
Record rsb_scx := RSBCx {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z);
x_ly : alayout; x_S : astate; x_W0 : world segs; x_mem0 : word -> option byte; x_md0 : Model;
x_own : list (Z * Z); x_k : Z; x_regs : bvmap 5 word;
x_lyc : alayout; x_Sc : astate; x_W : world segs; x_memc : word -> option byte; x_mdc : Model;
x_RLO : Z; x_RHI : Z; x_e : rt_renv; x_pos : Z }.

(* what every segment's contract asks at its start (RtPgCSpec.rt_seg_pre at image B's record) *)
Definition rsb_pre (cx : rsb_scx) : Prop :=
rt_seg_pre segs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
(x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)
rate_himg_B (x_RLO cx) (x_RHI cx) (x_e cx) (x_pos cx).

(* the journal-and-frame part of a cut inside the segment, with the segment's write set E *)
Definition rsb_core (cx : rsb_scx) (E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rsb_mid (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
(x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) E ly2 S2 W2 regs2 mem2 md2.

(* the three segments' write sets, as their contracts state them: the image's ranges (RtPgImgB: hi_w1 / hi_w2 /
   hi_w3) and the block the segment fills; the list's also lets runtime-owned bytes change (its two callees take and
   release side-stack frames of their own) *)
Definition rsb_E1 (cx : rsb_scx) : Z -> Prop :=
fun a => rt_inw (x_e cx) (hi_w1 rate_himg_B) a \/
q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE.
Definition rsb_E2 (cx : rsb_scx) : Z -> Prop :=
fun a => rt_inw (x_e cx) (hi_w2 rate_himg_B) a \/
q_pod (x_e cx) <= a < q_pod (x_e cx) + q_len (x_e cx).
Definition rsb_E3 (cx : rsb_scx) : Z -> Prop :=
fun a => rt_inw (x_e cx) (hi_w3 rate_himg_B) a \/
q_buf (x_e cx) <= a < q_buf (x_e cx) + rt_bl (q_buflen (x_e cx)) \/ aowned B (x_lyc cx) (x_Sc cx) a.

(* the first block's bytes at a cut *)
Definition rsb_pp_at (cx : rsb_scx) (W2 : world segs) (mem2 : word -> option byte) (l : list byte) : Prop :=
garr8 segs (mrestrict (w_H W2) mem2) (q_pp (x_e cx)) (rsb_u8s l).
(* the frame's shadow bytes at a cut *)
Definition rsb_fsh_at (cx : rsb_scx) (W2 : world segs) (mem2 : word -> option byte) (pat : list Z) : Prop :=
rt_fsh segs (w_H W2) mem2 (q_F (x_e cx)) pat.
(* the values at a cut's locations *)
Definition rsb_at_cx (cx : rsb_scx) (W2 : world segs) (mem2 : word -> option byte) (regs2 : bvmap 5 word)
(L : list (rt_loc * Z)) : Prop :=
rsb_at (w_H W2) mem2 regs2 (x_e cx) L.

(* What is left of the input the build reads: a suffix of the bytes after the 7-byte header, and the cursor that
   names it. q_src is where those bytes lie and q_left how many there are. *)
Definition rsb_suffix (rest r : list byte) : Prop := exists j, (j <= length rest)%nat /\ r = skipn j rest.
Definition rsb_cur (cx : rsb_scx) (rest r : list byte) : Z :=
q_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r).
(* the input bytes, as rate_build_contract gives them: at q_src, outside the callees' stack, the ranges the
   segment writes and the first block *)
Definition rsb_in (cx : rsb_scx) (rest : list byte) : Prop :=
q_left (x_e cx) = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_src (x_e cx)) (rsb_u8s rest) /\
range_addressable (aview segs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (q_src (x_e cx)) (q_left (x_e cx)) /\
(0 < q_left (x_e cx) -> shadow_hull_vis (aview segs (w_H (x_W cx)) (x_memc cx)) (q_src (x_e cx)) (q_left (x_e cx))) /\
amem_range (q_src (x_e cx)) (q_left (x_e cx)) /\
0 < q_src (x_e cx) /\ q_src (x_e cx) + q_left (x_e cx) <= 2 ^ 63 /\
(forall a, q_src (x_e cx) <= a < q_src (x_e cx) + q_left (x_e cx) ->
 ~ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) /\ ~ rt_inw (x_e cx) (hi_w1 rate_himg_B) a /\
 ~ (q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE)).

(* ===================================================================================================
   THE BUILD (M01): the cuts of rate_build_contract's walk, from C1 = 0x80ae4 to C2 = 0x82a2c
   ===================================================================================================
   The builder writes one object into the first block. Its state at a cut is the record so far (a Model.pb_cut: the
   shape sh, the properties ps written and, inside a params Struct, the pods es written), what is left of the input,
   and the loop counters; the block holds Layout.pc_image of that state and the R-relative cells hold the loop's
   constants and counters. *)

(* The constants the build puts in R-relative cells and no piece writes again (each set on every path into N and
   read after it): 0x15555556 is the `% 12u` multiplier (pod.h:354, 0x80f5c), 0x10003 is SPA_PROP_VOLUME (0x80f40),
   0x80001 is SPA_PROP_params (0x80f48), -0x4001 and -0x3ffd are the two capacity bounds (0x80f50, 0x80bcc), R+0x20
   and R+0x28 are the top size word's offset (0: the block's length before the header) and its address (0x80ea0,
   0x80ea4); R+0x110 is the shape-7 flag (0x80c8c / 0x80e90), R+0x118 the property count np (E01's arms 0x80b38 /
   0x80b4c / 0x80b84); the cells R+0x58 / R+0x130 / R+0x150 hold e62's addresses (the pod loop's pod, F+0x210),
   R+0xd0 / R+0xb8 e's and its body's (the shape-7 pod, F+0xf0) and R+0x80 / R+0x78 e42's and its body's + 4 (the
   Int-7 pod, F+0x180); R+0xd8 / R+0xf0 / R+0x100 / R+0x108 hold the complements the trap tests compare against
   (0x80f80, 0x80fb0, 0x80fa4, 0x80bd8). The `v / 10` multiplier of the digit loop (pod.h:240-241) is the register s5
   (0x80f64). The flags byte is in R+0x50 from E01 on. *)
Definition RSB_MULT10 : Z := 0xcccccccd * 2 ^ 32.
Definition rsb_Kc (cx : rsb_scx) (sh np : Z) : list (rt_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x0, 0x15555556); (LCell XR 0x10, q_F e); (LCell XR 0x20, 0); (LCell XR 0x28, q_pp e);
 (LCell XR 0x58, q_F e + 0x220); (LCell XR 0x60, q_F e); (LCell XR 0x50, q_fl e); (LCell XR 0x88, 0x10003);
 (LCell XR 0x68, q_pp e + 0x4010); (LCell XR 0xc8, 0x80001); (LCell XR 0x90, q_pp e + 0x400c);
 (LCell XR 0xe0, q_F e + 0xa0); (LCell XR 0xe8, q_pp e + 0x4014);
 (LCell XR 0xf8, Z.shiftr (q_pp e + 0x4d14) 3); (LCell XR 0x158, q_pp e + 0x4000);
 (LCell XR 0x138, q_pp e + 0x4d14); (LCell XR 0x168, q_pp e); (LCell XR 0x118, np);
 (LCell XR 0x110, Z.b2z (sh =? 7)); (LCell XR 0x170, shadow_addr (q_pp e + 0x4000));
 (LCell XR 0x130, q_F e + 0x218); (LCell XR 0xc0, -0x4001); (LCell XR 0x120, -0x3ffd);
 (LCell XR 0x150, q_F e + 0x210);
 (LCell XR 0x8, q_pp e + 0x4008); (LCell XR 0x78, q_F e + 0x18c); (LCell XR 0x80, q_F e + 0x180);
 (LCell XR 0xb8, q_F e + 0xf8); (LCell XR 0xd0, q_F e + 0xf0); (LCell XR 0xd8, Z.lnot (q_F e + 0xa0));
 (LCell XR 0xf0, Z.lnot (q_pp e + 0x4014)); (LCell XR 0x100, Z.lnot (q_F e + 0x218));
 (LCell XR 0x108, Z.lnot (q_pp e))].

(* The six header values E01 spilled (fuzz_rate.c:236-239) that M01 never writes again (b4 and b6 are kept shifted
   left by 8); the checks read them back. buflen stays in s10 until the preheader's `sd s10,0x18(s1)` 0x80ea8, so the
   header cuts (B7, BO, PH) carry rsb_Hch. *)
Definition rsb_Hc (cx : rsb_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x48, q_b3 e); (LCell XR 0x30, Z.shiftl (q_b6 e) 8); (LCell XR 0x38, q_b5 e);
 (LCell XR 0x40, Z.shiftl (q_b4 e) 8); (LCell XR 0x18, q_buflen e); (LCell XR 0x148, q_mask e)].
Definition rsb_Hch (cx : rsb_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x48, q_b3 e); (LCell XR 0x30, Z.shiftl (q_b6 e) 8); (LCell XR 0x38, q_b5 e);
 (LCell XR 0x40, Z.shiftl (q_b4 e) 8); (LReg 26, q_buflen e); (LCell XR 0x148, q_mask e)].

(* the registers the property loop keeps: s0 = S, s1 = R, s3 = the frame's shadow base, s4 = the runtime's shadow
   offset, s7 = &r, s11 = &t, s5 = the digit loop's multiplier (0x80f64); and s8 = -8 (0x80f1c, set again after each
   body that borrows s8: 0x81094, 0x821b0, 0x82468), which some cuts carry (rsb_Rc). pp, &pp->len, -0x4001 and the
   shadow address of &pp->len are only in cells (rsb_Kc). *)
Definition rsb_Rc0 (cx : rsb_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 19, shadow_addr (q_F e)); (LReg 20, SHADOW_OFF);
 (LReg 23, q_F e + 0xe0); (LReg 27, q_F e + 0x20); (LReg 21, RSB_MULT10)].
Definition rsb_Rc (cx : rsb_scx) : list (rt_loc * Z) := rsb_Rc0 cx ++ [(LReg 24, -8)].

(* the cursor: in the header cuts and at N in.p is in s2 and in.n in t4; after the selector byte's read (SEL7, SELK,
   SELI, SELS) in.p is in s10 (`addi s10,s2,1` 0x80fb8 / `mv s10,s2` 0x80fe8) *)
Definition rsb_cur2 (cx : rsb_scx) (rest r : list byte) : list (rt_loc * Z) :=
[(LReg 18, rsb_cur cx rest r); (LReg 29, Z.of_nat (length r))].
Definition rsb_cur2s (cx : rsb_scx) (rest r : list byte) : list (rt_loc * Z) :=
[(LReg 26, rsb_cur cx rest r); (LReg 29, Z.of_nat (length r))].

(* the two header reads of pod_build (pod.h:385-386): the shape and the property count *)
Definition rsb_sh (rest : list byte) : Z := fst (Cursor.fuzz_u8 rest) mod 8.
Definition rsb_np (rest : list byte) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))) mod 4.
Definition rsb_r0 (rest : list byte) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))).
(* the record the loop may have built: what Model.pod_rec_wf asks of its parts *)
Definition rsb_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2 ^ 32 /\ pval_wf (snd kv)) ps /\
Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.
Definition rsb_plen (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))).
Definition rsb_seen (ps : list (Z * pval)) : Z := Z.b2z (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps).
Definition rsb_first (ps : list (Z * pval)) : Z :=
Z.b2z (negb (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps)).
(* the offset of an open params Struct's size word: the property's key and flags are already written *)
Definition rsb_at_of (sh : Z) (ps : list (Z * pval)) : Z := rsb_plen sh ps + 8.

(* ---------------- the build's first own cuts: 0x80c80 (shape 7) and 0x80d1c (any other shape) ----------
   The block was filled with zeros (0x80af8), the two header bytes were read (0x80afc .. 0x80b84), and the top size
   word was written as four zero bytes with len := 4 (0x80c40 .. 0x80c70). a0 is that length, a2 = len - 0x3ffd is
   the capacity test's left side, a6 = pp + 0 and a7 = 0 are the top word's address and offset, a1 = 0x4000 and
   s6 = 0x5000 are the constants the preheader turns into &pp->len's neighbours, and s8 = s9 = F. The shape is in a3 at
   BO only (B7's pc overwrites it; the arm fixes sh = 7). *)
Definition rsb_L_hdr (cx : rsb_scx) (np : Z) (rest r : list byte) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 10, 4); (LReg 12, 4 - 0x3ffd); (LReg 16, q_pp e); (LReg 17, 0); (LReg 22, 0x5000); (LReg 8, q_S e);
 (LReg 9, q_R e); (LReg 19, shadow_addr (q_F e)); (LReg 20, SHADOW_OFF); (LCell XR 0x158, q_pp e + 0x4000);
 (LReg 24, q_F e); (LReg 25, q_F e); (LCell XR 0x168, q_pp e); (LCell XR 0x50, q_fl e); (LCell XR 0x118, np);
 (LCell XR 0x170, shadow_addr (q_pp e + 0x4000)); (LCell XR 0x120, -0x3ffd);
 (LReg 11, 0x4000); (LCell XR 0x108, Z.lnot (q_pp e))]
++ rsb_Hch cx ++ rsb_cur2 cx rest r.
(* the block's bytes before the object's header: the top size word only *)
Definition rsb_img_hdr : list byte := pp_image (le32 0) false false false [] false.
Definition rsb_cut_hdr (cx : rsb_scx) (rest r : list byte) (sh np : Z)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_hdr cx np rest r) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\ rsb_pp_at cx W2 mem2 rsb_img_hdr /\
rsb_in cx rest /\ rsb_suffix rest r /\
sh = rsb_sh rest /\ np = rsb_np rest /\ r = rsb_r0 rest.
Definition rsb_cut_B7 (cx : rsb_scx) (rest r : list byte) (np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_cut_hdr cx rest r 7 np ly2 S2 W2 regs2 mem2 md2.
Definition rsb_cut_BO (cx : rsb_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_cut_hdr cx rest r sh np ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 [(LReg 13, sh)] /\ sh <> 7.

(* ---------------- PH = 0x80ea0: the header is written, the preheader is about to run ----------------
   The block holds the image of the empty record of this shape (its header bytes and, for an Object, is_props); a7
   and a6 still hold the top word's offset and address, which the preheader spills (0x80ea0, 0x80ea4); R+0x110 holds
   the shape-7 flag. *)
Definition rsb_L_PH (cx : rsb_scx) (sh np : Z) (rest r : list byte) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 16, q_pp e); (LReg 17, 0); (LReg 22, 0x5000); (LReg 8, q_S e); (LReg 9, q_R e);
 (LReg 19, shadow_addr (q_F e)); (LReg 20, SHADOW_OFF); (LCell XR 0x158, q_pp e + 0x4000); (LReg 24, q_F e);
 (LReg 25, q_F e); (LCell XR 0x168, q_pp e); (LCell XR 0x50, q_fl e); (LCell XR 0x118, np);
 (LCell XR 0x110, Z.b2z (sh =? 7)); (LCell XR 0x170, shadow_addr (q_pp e + 0x4000)); (LCell XR 0x120, -0x3ffd);
 (LReg 11, 0x4000); (LCell XR 0x108, Z.lnot (q_pp e))]
++ rsb_Hch cx ++ rsb_cur2 cx rest r.
Definition rsb_cut_PH (cx : rsb_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_PH cx sh np rest r) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh [] None)) /\
rsb_in cx rest /\ rsb_suffix rest r /\
sh = rsb_sh rest /\ np = rsb_np rest /\ r = rsb_r0 rest.

(* ---------------- N = 0x80fb4: the property loop's head, |ps| properties written ----------------
   The property index is in t0 and `seen` in s6; s9 = 1 is the left side of the trap tests (0x80f2c, 0x824ec). *)
Definition rsb_L_N (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rsb_Rc cx ++ [(LReg 25, 1); (LReg 5, Z.of_nat (length ps)); (LReg 22, rsb_seen ps)]
++ rsb_Kc cx sh np ++ rsb_Hc cx ++ rsb_cur2 cx rest r.
Definition rsb_cut_N (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_N cx sh np ps rest r) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
sh = rsb_sh rest /\ np = rsb_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (rsb_r0 rest).

(* ---------------- the two ends of one property's selector (pod.h:399-423) ----------------
   SEL7 0x80ff4 (shape 7: the property is an Int pod with no key; the cut is before e's scope store) and SELK 0x810a4
   (any other shape: the key, its flags and the `first` test). The selector byte was read: a1 holds it at SELK. Image
   B computes no pp->len here (pod_write_ent reads it itself in the shape-7 body; the key piece loads it after
   SELK). *)
Definition rsb_L_SEL (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rsb_Rc0 cx ++ [(LReg 25, 1); (LReg 22, rsb_seen ps); (LReg 5, Z.of_nat (length ps))]
++ rsb_Kc cx sh np ++ rsb_Hc cx ++ rsb_cur2s cx rest r.
(* what every cut of one property's body shares with N, with the tie of ps to the input: the properties written are
   the ones Model.props_loop makes of the bytes after the two header reads *)
Definition rsb_prop_base (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\ rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
ps = fst (props_loop sh (length ps) (rsb_r0 rest)) /\
sh = rsb_sh rest /\ np = rsb_np rest /\ Z.of_nat (length ps) < np /\ np <= 3.
Definition rsb_cut_SEL7 (cx : rsb_scx) (np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_prop_base cx 7 np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_SEL cx 7 np ps rest r) /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut 7 ps None)) /\
r = snd (Cursor.fuzz_u8 (snd (props_loop 7 (length ps) (rsb_r0 rest)))).
Definition rsb_cut_SELK (cx : rsb_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_SEL cx sh np ps rest r ++ [(LReg 24, -8); (LReg 11, sel)]) /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
sh <> 7 /\ 0 <= sel < 256 /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rsb_r0 rest))).

(* ---------------- the two ends of the key piece (pod.h:407-423) ----------------
   SELI 0x82398 writes the Int value pod of a property whose value is an Int (the volume property, and a params
   property whose selector has bit 4 set; the cut is before e42's scope store), SELS 0x81210 opens a params Struct.
   On both, the key word and the flags word are already written, so the block's bytes are the record's image with
   those eight bytes appended. seen' is in a4 (0x811e0 / 0x811e8) and `first` in R+0x160 (0x811f8), both written
   before the arm tests 0x811fc / 0x81208, with the volume arm's values (seen, 0) when sel mod 4 = 0. `at` is not
   computed before SELS (the Struct arm loads pp->len at 0x81224); at SELS s2 = &pp->len and t1 = -0x4001. *)
Definition rsb_img_key (sh : Z) (ps : list (Z * pval)) (kk : Z) : list byte :=
pp_image (pc_buf (PbCut sh ps None) ++ le32 kk ++ le32 0)
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
(* the key the selector chooses (Model.prop_step): the volume property, else the params property *)
Definition rsb_key_of (sel : Z) : Z := if sel mod 4 =? 0 then 0x10003 else 0x80001.
Definition rsb_L_KEY (cx : rsb_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rsb_Rc0 cx ++ [(LReg 25, 1); (LReg 5, Z.of_nat (length ps));
               (LReg 14, if sel mod 4 =? 0 then rsb_seen ps else 1)]
++ rsb_Kc cx sh np ++ rsb_Hc cx
++ [(LCell XR 0x160, if sel mod 4 =? 0 then 0 else rsb_first ps)]
++ rsb_cur2s cx rest r.
Definition rsb_cut_SELI (cx : rsb_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_KEY cx sh np sel ps rest r) /\
rsb_pp_at cx W2 mem2 (rsb_img_key sh ps (rsb_key_of sel)) /\ sh <> 7 /\ 0 <= sel < 256 /\
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rsb_r0 rest))).
Definition rsb_cut_SELS (cx : rsb_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_KEY cx sh np sel ps rest r ++ [(LReg 24, -8); (LReg 18, q_pp (x_e cx) + 0x4000); (LReg 6, -0x4001)]) /\
rsb_pp_at cx W2 mem2 (rsb_img_key sh ps 0x80001) /\ sh <> 7 /\ 0 <= sel < 256 /\
sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rsb_r0 rest))).

(* ---------------- C = 0x813a0: the pod loop's head, |es| pods written ----------------
   The pod index is in a1 (the pc spills it to R+0x178), the count in R+0x140, `at` in R+0xa0 and its address in
   R+0xa8, the property index in R+0xb0, seen' = 1 in R+0x98 and `first` in R+0x160 (0x81334 .. 0x81340, 0x8138c,
   0x811f8); the cursor is in s10, what is left in s9, and s6 = &e62. The frame's shadow is still the prologue's: the
   stores 0x813a4 .. 0x813d4 open e62's granules after the pc. *)
Definition rsb_L_pod (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (rest r : list byte)
: list (rt_loc * Z) :=
let e := x_e cx in
rsb_Rc cx ++ rsb_Kc cx sh np ++ rsb_Hc cx
++ [(LCell XR 0xb0, Z.of_nat (length ps)); (LCell XR 0xa0, rsb_at_of sh ps);
    (LCell XR 0xa8, q_pp e + rsb_at_of sh ps); (LCell XR 0x140, cnt); (LCell XR 0x98, 1);
    (LCell XR 0x160, rsb_first ps);
    (LReg 25, Z.of_nat (length r)); (LReg 26, rsb_cur cx rest r); (LReg 22, q_F e + 0x210)].
(* What every cut inside the pod loop shares, with the tie of the count and the pods to the input: the selector
   picked the params Struct, the count byte gave cnt = c mod 33 (pod.h:425) and the pods written are the ones
   Model.ents_loop makes of what follows it, leaving rr at the turn's start. *)
Definition rsb_pod_tie (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent) (rest rr : list byte)
: Prop :=
exists sel c r1 r2,
(sel, r1) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rsb_r0 rest))) /\
(c, r2) = Cursor.fuzz_u8 r1 /\ cnt = c mod 33 /\ sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
ents_loop (length es) r2 = (es, rr).
Definition rsb_pod_base (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_suffix rest rr /\ rsb_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
ps = fst (props_loop sh (length ps) (rsb_r0 rest)) /\
rsb_pod_tie sh ps cnt es rest rr /\
sh = rsb_sh rest /\ np = rsb_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ (length es < 32)%nat /\ Z.of_nat (length es) < cnt.
Definition rsb_cut_C (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base cx sh np ps cnt es rest r r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_pod cx sh np ps cnt rest r ++ [(LReg 11, Z.of_nat (length es))]) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))).

(* ---------------- the eleven entries of ent_build's switch (pod.h:265-379) ----------------
   The dispatch (0x813a0 .. 0x8145c) opens e62's granules, fills e62 with zeros (memset 0x813e4), reads the kind byte
   and jumps through the nine relative entries at .rodata 0x20f6c (`jr a1` 0x8145c); `bltu a2,a1` 0x81438 takes case 9
   and `beqz s9` 0x813e8 takes case 0 with no input left. At every entry s10 is the kind byte's address, s2 the cursor
   after it, s6 what is left after it, t1 what was left before it, a3 the sign-extended kind byte and a0 that byte
   shifted left by 56, a6 = 1 the trap tests' left side (0x813f0), and a2 = 8 the table's bound or the table's
   address. The pod loop's cells (rsb_podc) hold the property index, `at` and its address, the count, seen' = 1,
   `first` and the pod index. *)
Definition rsb_pc_D (kd : Z) : Z :=
if kd mod 10 =? 0 then RSB_D0 else if kd mod 10 =? 1 then RSB_D1 else if kd mod 10 =? 2 then RSB_D2
else if kd mod 10 =? 3 then RSB_D3 else if kd mod 10 =? 4 then RSB_D4 else if kd mod 10 =? 5 then RSB_D5
else if kd mod 10 =? 6 then RSB_D6 else if kd mod 10 =? 7 then RSB_D7 else if kd mod 10 =? 8 then RSB_D8
else RSB_D9.
Definition rsb_podc (cx : rsb_scx) (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rt_loc * Z) :=
[(LCell XR 0xb0, Z.of_nat (length ps)); (LCell XR 0xa0, rsb_at_of sh ps); (LCell XR 0x140, cnt);
 (LCell XR 0x98, 1); (LCell XR 0x160, rsb_first ps); (LCell XR 0x178, Z.of_nat (length es));
 (LCell XR 0xa8, q_pp (x_e cx) + rsb_at_of sh ps)].
Definition rsb_L_Dc0 (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rt_loc * Z) :=
rsb_Rc0 cx ++ rsb_Kc cx sh np ++ rsb_Hc cx ++ rsb_podc cx sh ps cnt es.
Definition rsb_L_Dc (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rt_loc * Z) :=
rsb_L_Dc0 cx sh np ps cnt es ++ [(LReg 24, -8)].
(* Case 9 is reached by `bltu a2,a1` 0x81438, before the instructions 0x8143c .. 0x81458 that form the table's
   address and shift and sign-extend the kind byte, so a2 holds the table's address and a3 and a0 the kind byte's two
   forms only on the nine table entries; on case 9 a2 is still the bound 8. *)
Definition rsb_L_D (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (kd : Z) : list (rt_loc * Z) :=
rsb_L_Dc cx sh np ps cnt es
++ [(LReg 6, Z.of_nat (length r) + 1); (LReg 26, rsb_cur cx rest r - 1);
    (LReg 18, rsb_cur cx rest r); (LReg 22, Z.of_nat (length r)); (LReg 16, 1)]
++ (if kd mod 10 =? 9 then [(LReg 12, 8)]
    else [(LReg 12, 0x20f6c); (LReg 13, kd - 256 * (kd / 128)); (LReg 10, kd * 2 ^ 56)]).
(* rr is what is left of the input when the turn begins (at C); the kind byte is the first of it and r what is left
   after it, so the pod the turn builds is Model.ent_build rr. *)
Definition rsb_cut_D (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (kd : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_D cx sh np ps cnt es rest r kd) /\
rsb_fsh_at cx W2 mem2 rsb_PJ /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x210) (rsb_u8s (zeros 104)) /\
rsb_suffix rest rr /\ (kd, r) = Cursor.fuzz_u8 rr /\ 0 <= kd < 256 /\ rr <> [].
(* the same with no input left: the kind byte reads as 0 and the cursor does not move (fuzz.h:37-43) *)
Definition rsb_cut_D0E (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_Dc cx sh np ps cnt es ++ [(LReg 26, rsb_cur cx rest []); (LReg 25, 0)]) /\
rsb_fsh_at cx W2 mem2 rsb_PJ /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x210) (rsb_u8s (zeros 104)).

(* ---------------- G = 0x8160c: case 0 after the digits, the reverse and the odd_ch part ----------------
   t and ch are in scope and r is out of scope again (0x81608; the odd_ch path never opens it), so the frame's shadow
   is neither the prologue's nor the pod loop's: rsb_PG is that state. s2 = &ch, s9 = the second input byte of the
   head-amp key, t1 what is left and the cell R+0x128 the cursor; ch holds the key's first part with its NUL. *)
(* what case 0 reads of the turn's input before G: the kind byte, then c and p (pod.h:224-262); chs is the key's
   first part, the decimal text of c mod 64 or the odd_ch string of c mod 14. *)
Definition rsb_g_of (rr : list byte) : list byte * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Definition rsb_cut_G (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (pb : Z) (chs : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_Dc0 cx sh np ps cnt es
 ++ [(LReg 6, Z.of_nat (length r)); (LReg 18, q_F (x_e cx) + 0xa0); (LReg 25, pb);
     (LCell XR 0x128, rsb_cur cx rest r)]) /\
rsb_fsh_at cx W2 mem2 rsb_PG /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0xa0) (rsb_u8s (chs ++ [NUL])) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x210) (rsb_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (chs, pb, r) = rsb_g_of rr /\
(length chs <= 21)%nat /\ 0 <= pb < 256.

(* ---------------- J = 0x820dc: the pod is built; the capacity check, then the call pod_write_ent(pp, e62) -------
   e62 holds Layout.ent_mem of the pod ent_build made of the turn's input, the cursor is in s10 and what is left in
   t1, and s2 and s6 hold the two values the cases reload from R+0x158 and R+0x150 (&pp->len, &e62). *)
Definition rsb_cut_J (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (ed : ent) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_Dc0 cx sh np ps cnt es
 ++ [(LReg 18, q_pp (x_e cx) + 0x4000); (LReg 22, q_F (x_e cx) + 0x210);
     (LReg 26, rsb_cur cx rest r); (LReg 6, Z.of_nat (length r))]) /\
rsb_fsh_at cx W2 mem2 rsb_PJ /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x210) (rsb_u8s (ent_mem ed)) /\
(ed, r) = ent_build rr /\ ent_wf ed.

(* ---------------- CL = 0x824c0: the count is reached; the Struct's size word is patched ----------------
   The pod loop wrote cnt pods and e62 is out of scope again (0x8217c .. 0x821b4, or never opened when the count is
   0 or no count byte is left); s2 = &pp->len, what is left in s9 and the cursor in s10. *)
Definition rsb_cut_CL (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_Rc cx ++ rsb_Kc cx sh np ++ rsb_Hc cx
 ++ [(LReg 18, q_pp (x_e cx) + 0x4000); (LReg 25, Z.of_nat (length r)); (LReg 26, rsb_cur cx rest r);
     (LCell XR 0xb0, Z.of_nat (length ps)); (LCell XR 0xa0, rsb_at_of sh ps);
     (LCell XR 0xa8, q_pp (x_e cx) + rsb_at_of sh ps); (LCell XR 0x98, 1); (LCell XR 0x160, rsb_first ps)]) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
ps = fst (props_loop sh (length ps) (rsb_r0 rest)) /\
rsb_pod_tie sh ps cnt es rest r /\
sh = rsb_sh rest /\ np = rsb_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ Z.of_nat (length es) = cnt.

(* ---------------- the latch 0x82578 / 0x8257c: one property is written ----------------
   At 0x82578 (from the Struct's close) the property index is in t0 (0x824d4) and `seen` in R+0x98 (the pc loads it
   into a3); 0x8257c is entered from 0x82578 and from the shape-7 and the Int-7 pieces (`j` 0x810a0 / 0x82470), each
   of which restores the index into t0 and `seen` into a3 itself. On every entry what is left is in t4, the cursor in
   s10 and s9 = 1. *)
Definition rsb_latch_body (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
sh = rsb_sh rest /\ np = rsb_np rest /\ 1 <= Z.of_nat (length ps) <= np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (rsb_r0 rest).
Definition rsb_L_LATCH (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rt_loc * Z) :=
rsb_Rc cx ++ rsb_Kc cx sh np ++ rsb_Hc cx
++ [(LReg 5, Z.of_nat (length ps) - 1); (LReg 29, Z.of_nat (length r)); (LReg 26, rsb_cur cx rest r);
    (LReg 25, 1)].
Definition rsb_cut_LATCH (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_LATCH cx sh np ps rest r ++ [(LCell XR 0x98, rsb_seen ps)]).
Definition rsb_cut_LATCH7 (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_LATCH cx sh np ps rest r ++ [(LReg 13, rsb_seen ps)]).

(* ---------------- P = 0x82684 / P1 = 0x82688: every property is written ----------------
   0x82684 is entered only when the object has no property (`j` 0x80ee0, after the preheader's stores 0x80ea0 ..
   0x80ed8 and before its later ones), with the cursor in s2; 0x82688 is also the latch's exit, where `mv s10,s2`
   0x82684 has moved the cursor into s10. What is left is in t4 on both. *)
Definition rsb_L_P (cx : rsb_scx) (rest r : list byte) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 19, shadow_addr (q_F e)); (LReg 20, SHADOW_OFF);
 (LReg 29, Z.of_nat (length r));
 (LCell XR 0x8, q_pp e + 0x4008); (LCell XR 0x10, q_F e); (LCell XR 0x20, 0); (LCell XR 0x28, q_pp e);
 (LCell XR 0x50, q_fl e); (LCell XR 0x60, q_F e); (LCell XR 0xf8, Z.shiftr (q_pp e + 0x4d14) 3);
 (LCell XR 0x108, Z.lnot (q_pp e)); (LCell XR 0x120, -0x3ffd); (LCell XR 0x138, q_pp e + 0x4d14);
 (LCell XR 0x158, q_pp e + 0x4000); (LCell XR 0x168, q_pp e);
 (LCell XR 0x170, shadow_addr (q_pp e + 0x4000))] ++ rsb_Hc cx.
Definition rsb_Pbody (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
sh = rsb_sh rest /\ np = rsb_np rest /\ Z.of_nat (length ps) = np /\
(ps, r) = props_loop sh (length ps) (rsb_r0 rest).
Definition rsb_cut_P (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_P cx rest r ++ [(LReg 18, rsb_cur cx rest r)]).
Definition rsb_cut_P1 (cx : rsb_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_P cx rest r ++ [(LReg 26, rsb_cur cx rest r)]).

(* ---------------- R = 0x82960 and RT = 0x829fc: the corruption (pod.h:441-448) ----------------
   The object is complete (its top size word was patched, 0x826e0 .. 0x82700), so the block holds the image of the
   record with no corruption yet. The loop writes one byte a turn: a3 = kk is the index, a2 = cnt - kk what is left
   of the count the input byte gave (`andi a2,a2,7` 0x82940, decremented at 0x829d4), a4 = off, a0 is the cursor of
   the byte reads and a5 what is left of the input; a6 = 1 is the left side of the trap test 0x82980. It also leaves
   through `bgeu a1,a7` 0x82974 when off + kk reaches the length, so the bytes written, bs, are the first
   min(cnt, len - off) of the input's. At RT the corruption is done but the corrupt word is NOT yet written
   (`sw a0,0(s8)` 0x82a10 is after the cut), so the block still holds the image with corrupt false and the record's
   own bytes. t2 = &pp->len (0x826a0) and s8 = &pp->corrupt (0x82704 .. 0x82708). *)
Definition rsb_L_post (cx : rsb_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 19, shadow_addr (q_F e)); (LReg 20, SHADOW_OFF);
 (LReg 7, q_pp e + 0x4000); (LReg 24, q_pp e + 0x4d18);
 (LCell XR 0x8, q_pp e + 0x4008); (LCell XR 0x10, q_F e); (LCell XR 0x50, q_fl e); (LCell XR 0x60, q_F e);
 (LCell XR 0xf8, Z.shiftr (q_pp e + 0x4d14) 3); (LCell XR 0x120, -0x3ffd);
 (LCell XR 0x138, q_pp e + 0x4d14); (LCell XR 0x168, q_pp e);
 (LCell XR 0x170, shadow_addr (q_pp e + 0x4000))] ++ rsb_Hc cx.
(* the block's bytes with the first kk corruption bytes written at off *)
Definition rsb_img_corr (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (kk : Z) : list byte :=
pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn (Z.to_nat kk) bs))
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Definition rsb_corr_wf (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (cnt : Z) : Prop :=
8 <= off /\ off + Z.of_nat (length bs) <= rsb_plen sh ps /\ (length bs <= 7)%nat /\
0 < cnt <= 7 /\ Z.of_nat (length bs) = Z.min cnt (rsb_plen sh ps - off).
Definition rsb_cut_R (cx : rsb_scx) (sh : Z) (ps : list (Z * pval)) (rest r : list byte)
(off : Z) (bs : list byte) (cnt kk : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_post cx ++ [(LCell XR 0x108, Z.lnot (q_pp (x_e cx))); (LReg 13, kk); (LReg 12, cnt - kk);
                   (LReg 14, off); (LReg 10, rsb_cur cx rest r); (LReg 15, Z.of_nat (length r)); (LReg 16, 1)]) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (rsb_img_corr sh ps off bs kk) /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
rsb_corr_wf sh ps off bs cnt /\ 0 <= kk < cnt /\ kk <= Z.of_nat (length bs) /\
skipn (Z.to_nat kk) bs = fst (fuzz_u8s (length bs - Z.to_nat kk) r).
Definition rsb_cut_RT (cx : rsb_scx) (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_post cx) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\
rsb_pp_at cx W2 mem2 (rsb_img_corr sh ps off bs (Z.of_nat (length bs))) /\
rsb_in cx rest /\ rsb_suffix rest r /\ rsb_wf sh ps /\
q_len (x_e cx) = rt_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
8 <= off /\ off + Z.of_nat (length bs) <= rsb_plen sh ps /\ (length bs <= 7)%nat.

(* ---------------- C2 = 0x82a2c: the build is done; the second request is in a0 ----------------
   This cut IS rate_build_contract's post, at the pc its contract names (hi_c2 rate_himg_B): the C2 value list, the
   frame's shadow back to the prologue's, and the block holding Layout.pp_bytes of the record. *)
Definition rsb_cut_C2 (cx : rsb_scx) (rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L2 rate_himg_B) /\
rsb_fsh_at cx W2 mem2 rsb_P0 /\ rsb_pp_at cx W2 mem2 (pp_bytes (fst (pod_build rest))) /\
q_len (x_e cx) = rt_len rest.

(* ===================================================================================================
   THE CHECKS (M02): the cuts of rate_check_contract's walk, from C3 = 0x82a30 to C4 = 0x82f9c
   ===================================================================================================
   The first block holds Layout.pp_bytes of the record some input made; the segment copies its first len bytes into
   the second block, puts 0x5a5a5a5a into hz (F+0x2a0, its granule in scope from 0x82a60 on: rsb_PB, the one frame
   shadow pattern of every cut of M02 and M03), runs the parse on the copy (or on NULL, by bit 0 of the flags byte),
   scans the record's entries for the rate key when the record is uncorrupted and runs the check its answer selects,
   sets up asked[0] and asked[1] in the real-frame cells R+0x198 and R+0x19c (no scope store), runs the decide turn
   twice and then check_code(refuse_code(4), 4). From the parse on, the float state is some fx2 that keeps every
   float register outside fa0, fa3, fa4 and fa5 and has a zero rounding mode (main's one float instruction is
   `flw fa0` 0x82dbc; the parse and pod_nearest change the others by their contracts). *)
(* the parse's answer on the block's bytes (NULL by bit 0 of the flags byte), the expectation the inlined scan
   computes, and hz after the parse: the value the parse wrote, else the 0x5a5a5a5a the harness put there *)
Definition rsb_PA (cx : rsb_scx) (rec : pod_rec) : option Z * Z :=
Rate.harness_parse (Z.testbit (q_fl (x_e cx)) 0) (buf rec).
Definition rsb_E0 (rec : pod_rec) : option Z * Z := Rate.expect_model false rec.
Definition rsb_hz (cx : rsb_scx) (rec : pod_rec) : Z := Rate.written_or 0x5a5a5a5a (rsb_PA cx rec).
(* the two asked values (fuzz_rate.c:262): rc == 1 ? hz : 48000, and the u32 `other` of header bytes 3 .. 6 in the
   form 0x82dec .. 0x82e0c computes it from the cells, (b4 << 8 | b3) | (b6 << 8 | b5) << 16 (its 4 bytes are what
   asked[1] holds; the code reads it back with a sign-extending `lw`) *)
Definition rsb_ask0 (cx : rsb_scx) (rec : pod_rec) : Z :=
if snd (rsb_PA cx rec) =? 1 then rsb_hz cx rec else 48000.
Definition rsb_other (e : rt_renv) : Z :=
Z.lor (Z.lor (Z.shiftl (q_b4 e) 8) (q_b3 e)) (Z.shiftl (Z.lor (Z.shiftl (q_b6 e) 8) (q_b5 e)) 16).
(* what every cut of the checks carries; the frame's shadow is rsb_PB throughout (hz in scope) *)
Definition rsb_chk_base (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_fxk [10; 13; 14; 15] fx fx2 /\
rsb_fsh_at cx W2 mem2 rsb_PB /\ rom_view segs W2 mem2 /\
rsb_pp_at cx W2 mem2 (pp_bytes rec) /\
pod_rec_wf rec /\ q_len (x_e cx) = Z.of_nat (length (buf rec)) /\
q_pod (x_e cx) <> 0 /\ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)).
(* the hz cell (the 4-byte frame object at F+0x2a0), at every cut after the parse *)
Definition rsb_hz_at (cx : rsb_scx) (rec : pod_rec) (W2 : world segs) (mem2 : word -> option byte) : Prop :=
val_mem segs (mrestrict (w_H W2) mem2) (q_F (x_e cx) + 0x2a0) 4 (rsb_hz cx rec mod 2 ^ 32).
(* the two asked cells, from the asked set-up on: the 4-byte real-frame cells R+0x198 (`sw` 0x82e30) and R+0x19c
   (`sw` 0x82e34), read back by `lw` 0x82e50 / 0x82f44 without an instrumented check *)
Definition rsb_ask_at (cx : rsb_scx) (rec : pod_rec) (W2 : world segs) (mem2 : word -> option byte) : Prop :=
val_mem segs (mrestrict (w_H W2) mem2) (q_R (x_e cx) + 0x198) 4 (rsb_ask0 cx rec mod 2 ^ 32) /\
val_mem segs (mrestrict (w_H W2) mem2) (q_R (x_e cx) + 0x19c) 4 (rsb_other (x_e cx)).
(* the values every cut of the checks carries up to the asked set-up: s0 = S, s1 = R, s3 = the frame's shadow base,
   s4 = the runtime's shadow offset, s5 = &hz (0x82a3c), pod in R+0x178 (0x82a9c), F in R+0x10, the flags byte in
   R+0x50 and the six header cells *)
Definition rsb_L_chk (cx : rsb_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 19, shadow_addr (q_F e)); (LReg 20, SHADOW_OFF);
 (LCell XR 0x178, q_pod e); (LReg 21, q_F e + 0x2a0);
 (LCell XR 0x10, q_F e); (LCell XR 0x50, q_fl e)] ++ rsb_Hc cx.

(* ---------------- E = 0x82aac: the inlined expect_rate begins ----------------
   Reached when the record is uncorrupted (`bnez a0` 0x82aa0 not taken) and bit 0 of the flags byte is clear
   (`bnez s2` 0x82aa8 not taken); a0 = &pp->is_props (0x82aa4), s10 = rc (0x82a8c), s6 = the mask (0x82a98), s7 = the
   flags byte (0x82a40). *)
Definition rsb_cut_E (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_chk cx ++ [(LReg 10, q_pp (x_e cx) + 0x4008); (LReg 26, snd (rsb_PA cx rec));
                 (LReg 22, q_mask (x_e cx)); (LReg 23, q_fl (x_e cx));
                 (LCell XR 0x60, q_F (x_e cx));
                 (LCell XR 0xf8, Z.shiftr (q_pp (x_e cx) + 0x4d14) 3);
                 (LCell XR 0x138, q_pp (x_e cx) + 0x4d14); (LCell XR 0x168, q_pp (x_e cx));
                 (LCell XR 0x120, -0x3ffd)]) /\
rsb_hz_at cx rec W2 mem2 /\
Z.testbit (q_fl (x_e cx)) 0 = false /\ corrupt rec = false /\
Rate.parse_model (buf rec) = rsb_E0 rec.

(* ---------------- O = 0x82b48: the outer scan's head ----------------
   rc is in the cell R+0x170 (0x82ac4) and R+0x138 holds the offset 0x4018 (0x82b30); the scan's fixed operands are
   s2 = &ent[0], a7 = &ent[0] + 4, t2 = s7 = &ent[0] + 8, the stride t1 = 104 << 32 (the `mulhu` 0x82b68 makes 104 m
   of it), the string type t3 = 8, n_ent in s10, and the trap tests' bounds s11 = ~&ent[0], t0 = ~(&ent[0] + 8); a2 is
   at. *)
Definition rsb_L_scan (cx : rsb_scx) (rec : pod_rec) : list (rt_loc * Z) :=
let e := x_e cx in
rsb_L_chk cx ++
[(LCell XR 0x170, snd (rsb_PA cx rec)); (LCell XR 0x138, 0x4018);
 (LReg 28, 8); (LReg 26, Z.of_nat (length (ents rec)));
 (LReg 18, q_pp e + 0x4014); (LReg 17, q_pp e + 0x4018); (LReg 7, q_pp e + 0x401c); (LReg 23, q_pp e + 0x401c);
 (LReg 27, Z.lnot (q_pp e + 0x4014)); (LReg 5, Z.lnot (q_pp e + 0x401c)); (LReg 6, 104 * 2 ^ 32);
 (LCell XR 0x60, q_F e); (LCell XR 0x168, q_pp e)].
Definition rsb_scan_inv (rec : pod_rec) (j : nat) : Prop :=
(j <= length (ents rec))%nat /\
rsb_E0 rec = Rate.rate_of_pairs Rate.expect_value (pairs_by key_of (skipn j (ents rec)) None).
Definition rsb_chk_rec (cx : rsb_scx) (rec : pod_rec) : Prop :=
corrupt rec = false /\ is_props rec = true /\ params_struct rec = true /\
snd (rsb_PA cx rec) = snd (rsb_E0 rec) /\ fst (rsb_PA cx rec) = fst (rsb_E0 rec).
Definition rsb_cut_O (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec) (j : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_scan cx rec ++ [(LReg 12, Z.of_nat j)]) /\
rsb_hz_at cx rec W2 mem2 /\ rsb_scan_inv rec j /\ rsb_chk_rec cx rec.

(* ---------------- I = 0x82b74: pod_next_pair's inner scan from at0, at entry m ----------
   Image B's inner loop is rotated: its head 0x82b70 first tests a0, the previous turn's result (0, or the body
   address of a key), and leaves to KM when it is set; the scan's own state ("entry m is next, no key in [at0, m)")
   holds one instruction later, at 0x82b74, which every turn of the loop passes (from O with m = at0 and a0 = 0 from
   0x82b64; from the latch 0x82c0c with m + 1). The bases stay fixed and s8 = 104 m is the offset of ent[m]; s6 = a2 =
   m; a3 = max(at0, 33) and a4 = ~(&ent[0] + 8) - 104 m are the bounds of the trap tests 0x82b74 / 0x82bc0. *)
Definition rsb_cut_I (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_scan cx rec ++
 [(LReg 12, Z.of_nat m); (LReg 22, Z.of_nat m); (LReg 24, 104 * Z.of_nat m);
  (LReg 13, Z.max (Z.of_nat at0) 33);
  (LReg 14, Z.lnot (q_pp (x_e cx) + 0x401c) - 104 * Z.of_nat m)]) /\
rsb_hz_at cx rec W2 mem2 /\ rsb_scan_inv rec at0 /\ rsb_chk_rec cx rec /\
(at0 <= m < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None).

(* ---------------- KM = 0x82c40: entry m is a key and entry m + 1 is its value ----------
   a0 is the key's body address, a2 = s6 = m + 1 the value's index and s8 = 104 (m + 1); the next `at` m + 2 is made
   by the cut's own `addiw s9,a2,1`; a7, t0, t1 and t2 are spilled around the string compare (0x82c54 .. 0x82c60) and
   reloaded after it. *)
Definition rsb_cut_KM (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat) (kb : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_scan cx rec ++
 [(LReg 10, q_pp (x_e cx) + 0x401c + 104 * Z.of_nat m); (LReg 12, Z.of_nat m + 1); (LReg 22, Z.of_nat m + 1);
  (LReg 24, 104 * (Z.of_nat m + 1))]) /\
rsb_hz_at cx rec W2 mem2 /\ rsb_scan_inv rec at0 /\ rsb_chk_rec cx rec /\
(at0 <= m)%nat /\ (m + 1 < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None) /\
key_of (nth m (ents rec) (Ent 0 0 [])) = Some kb.

(* ---------------- the two checks the answer selects, and the join after them ----------------
   ABS 0x82d1c: no pair of the record has the rate key (or there is no params Struct), so the answer is (None, 0) and
   check_absent runs; rc = 0 is in R+0x170. MAL 0x82de0: the answer is (None, -1) (the NULL flag, no Props object, or
   a value no reader takes) and check_malformed runs. A 0x82dec: the check is done (or skipped, for a corrupted record)
   and the asked set-up begins; s7 is the flags byte again (0x82a40, or reloaded at 0x82c8c / 0x82d30), whose bit 1
   is the role, and s6 the mask; pp is only in R+0x168. *)
Definition rsb_cut_ABS (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_chk cx ++ [(LCell XR 0x170, 0); (LCell XR 0x60, q_F (x_e cx)); (LCell XR 0x168, q_pp (x_e cx))]) /\
rsb_hz_at cx rec W2 mem2 /\ fst (rsb_PA cx rec) = None /\ snd (rsb_PA cx rec) = 0.
Definition rsb_cut_MAL (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_chk cx ++ [(LReg 26, -1); (LReg 22, q_mask (x_e cx)); (LReg 23, q_fl (x_e cx));
                 (LCell XR 0x60, q_F (x_e cx)); (LCell XR 0x168, q_pp (x_e cx))]) /\
rsb_hz_at cx rec W2 mem2 /\ fst (rsb_PA cx rec) = None /\ snd (rsb_PA cx rec) = -1.
Definition rsb_cut_A (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2
(rsb_L_chk cx ++ [(LReg 26, snd (rsb_PA cx rec)); (LReg 22, q_mask (x_e cx)); (LReg 23, q_fl (x_e cx));
                 (LCell XR 0x60, q_F (x_e cx)); (LCell XR 0x168, q_pp (x_e cx))]) /\
rsb_hz_at cx rec W2 mem2.

(* ---------------- DEC = 0x82e44, the decide loop's head, and T2 = 0x82f8c after it ----------------
   Both turns enter with asked[0] and asked[1] in their cells (rsb_ask_at). Turn t (0 or 1) has s10 = t (0x82e28, then
   the latch's 0x82f84) and its bound s9 = 2 (0x82e40); the turn forms s8 = R + 0x198 + 4 t itself (0x82e44 ..
   0x82e4c) and reads asked[t] through it; s5 = the role (flags bit 1, 0x82e2c), s6 = the mask (the A cut's, then
   0x82f60), s2 = &closed_list (0x82e38 .. 0x82e3c: RSB_CLOSED), s4 = K. What DEC, T2 and C4 all carry is rsb_L_dec,
   the values of RtPgImgB's hi_L4. *)
Definition RSB_CLOSED : Z := 0x21520.
Lemma rsb_closed_himg : In (RSB_CLOSED, RateCfg.closed_list) (hi_i32 rate_himg_B).
Proof. exact (or_introl eq_refl). Qed.
Definition rsb_L_dec (cx : rsb_scx) : list (rt_loc * Z) :=
let e := x_e cx in
[(LReg 8, q_S e); (LReg 9, q_R e); (LReg 19, shadow_addr (q_F e));
 (LCell XR 0x10, q_F e); (LCell XR 0x18, q_buflen e); (LCell XR 0x60, q_F e);
 (LCell XR 0x168, q_pp e); (LCell XR 0x148, q_mask e); (LCell XR 0x178, q_pod e)].
Definition rsb_L_DEC (cx : rsb_scx) (t : Z) : list (rt_loc * Z) :=
let e := x_e cx in
rsb_L_dec cx ++
[(LReg 20, SHADOW_OFF); (LReg 26, t); (LReg 25, 2);
 (LReg 21, Z.b2z (Z.testbit (q_fl e) 1)); (LReg 22, q_mask e); (LReg 18, RSB_CLOSED)].
Definition rsb_cut_DEC (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec) (t : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_DEC cx (Z.of_nat t)) /\
rsb_ask_at cx rec W2 mem2 /\ (t < 2)%nat.
Definition rsb_cut_T2 (cx : rsb_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rsb_at_cx cx W2 mem2 regs2 (rsb_L_dec cx).

(* ---------------- C4 = 0x82f9c: the checks are done ----------------
   This cut IS rate_check_contract's post, at the pc its contract names (hi_c4 rate_himg_B). *)
Definition rsb_cut_C4 (cx : rsb_scx) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_fxk [10; 13; 14; 15] fx fx2 /\
rt_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L4 rate_himg_B) /\
rsb_fsh_at cx W2 mem2 rsb_PB.

(* ===================================================================================================
   THE LIST (M03): rate_csv_contract's walk, from C6 = 0x82fb0 to C7 = 0x82fec (15 instructions, no internal cut)
   ===================================================================================================
   C7 IS rate_csv_contract's post, at the pc its contract names (hi_c7 rate_himg_B). *)
Definition rsb_cut_C7 (cx : rsb_scx) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rsb_core cx (rsb_E3 cx) ly2 S2 W2 regs2 mem2 md2 /\
rt_fxk [10] fx fx2 /\
rt_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L7 rate_himg_B) /\
rsb_fsh_at cx W2 mem2 rsb_PB.

(* ===================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   ===================================================================================================
   One per cut, with the LOOP INDEX as an argument (and never under the inner quantifier), so that the latch of a
   loop can hand the head its next index and the closure is an induction on the index, not a circular hypothesis:
   rsb_from_N .. (S i) is what the property loop's latch gives, rsb_from_C .. i (S k) what the pod loop's latch gives,
   rsb_from_DEC .. (S t) what the decide loop's latch gives. A piece lemma is `<its start premises> -> <the
   continuations of its end cuts> -> <the continuation of its start cut>`, so a lane proving one piece takes the other
   lanes' continuations as hypotheses and never sees their proofs. POST is generic. *)
Section f.
Variable cx : rsb_scx.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.

Definition rsb_from_B7 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r np, rsb_cut_B7 cx rest r np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_B7 regs2 mem2 md2) POST.
Definition rsb_from_BO : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, rsb_cut_BO cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_BO regs2 mem2 md2) POST.
Definition rsb_from_PH : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, rsb_cut_PH cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_PH regs2 mem2 md2) POST.
Definition rsb_from_N (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = i)%nat ->
rsb_cut_N cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_N regs2 mem2 md2) POST.
Definition rsb_from_SEL7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 np ps r, (length ps = i)%nat ->
rsb_cut_SEL7 cx np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_SEL7 regs2 mem2 md2) POST.
Definition rsb_from_SELK (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
rsb_cut_SELK cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_SELK regs2 mem2 md2) POST.
Definition rsb_from_SELI (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
rsb_cut_SELI cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_SELI regs2 mem2 md2) POST.
Definition rsb_from_SELS (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
rsb_cut_SELS cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_SELS regs2 mem2 md2) POST.
Definition rsb_from_C (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat -> (length es = k)%nat ->
rsb_cut_C cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_C regs2 mem2 md2) POST.
Definition rsb_from_D (i k : nat) (kd : Z) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r, (length ps = i)%nat -> (length es = k)%nat ->
rsb_cut_D cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (rsb_pc_D kd) regs2 mem2 md2) POST.
Definition rsb_from_D0E (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es, (length ps = i)%nat -> (length es = k)%nat ->
rsb_cut_D0E cx sh np ps cnt es rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_D0E regs2 mem2 md2) POST.
Definition rsb_from_G (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs, (length ps = i)%nat -> (length es = k)%nat ->
rsb_cut_G cx sh np ps cnt es rest rr r pb chs ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_G regs2 mem2 md2) POST.
Definition rsb_from_J (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed, (length ps = i)%nat -> (length es = k)%nat ->
rsb_cut_J cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_J regs2 mem2 md2) POST.
Definition rsb_from_CL (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat ->
rsb_cut_CL cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_CL regs2 mem2 md2) POST.
Definition rsb_from_LATCH (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
rsb_cut_LATCH cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_LATCH regs2 mem2 md2) POST.
Definition rsb_from_LATCH7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
rsb_cut_LATCH7 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_LATCH7 regs2 mem2 md2) POST.
Definition rsb_from_P : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
rsb_cut_P cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_P regs2 mem2 md2) POST.
Definition rsb_from_P1 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
rsb_cut_P1 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_P1 regs2 mem2 md2) POST.
Definition rsb_from_R (kk : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt,
rsb_cut_R cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_R regs2 mem2 md2) POST.
Definition rsb_from_RT : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps off bs r,
rsb_cut_RT cx sh ps off bs rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_RT regs2 mem2 md2) POST.
Definition rsb_from_C2 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2,
rsb_cut_C2 cx rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (hi_c2 rate_himg_B) regs2 mem2 md2) POST.
(* the cuts of the checks and of the list reach their pc at the run's own float state *)
Definition rsb_from_E : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_E cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_E regs2 mem2 md2) POST.
Definition rsb_from_O (j : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_O cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_O regs2 mem2 md2) POST.
Definition rsb_from_I (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_I cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_I regs2 mem2 md2) POST.
Definition rsb_from_KM (at0 m : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec kb, rsb_cut_KM cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_KM regs2 mem2 md2) POST.
Definition rsb_from_ABS : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_ABS cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_ABS regs2 mem2 md2) POST.
Definition rsb_from_MAL : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_MAL cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_MAL regs2 mem2 md2) POST.
Definition rsb_from_A : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_A cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_A regs2 mem2 md2) POST.
Definition rsb_from_DEC (t : nat) : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_DEC cx fx2 rec t ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_DEC regs2 mem2 md2) POST.
Definition rsb_from_T2 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rsb_cut_T2 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RSB_T2 regs2 mem2 md2) POST.
Definition rsb_from_C4 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, rsb_cut_C4 cx fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs (hi_c4 rate_himg_B) regs2 mem2 md2) POST.
Definition rsb_from_C7 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, rsb_cut_C7 cx fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs (hi_c7 rate_himg_B) regs2 mem2 md2) POST.
End f.

(* ===================================================================================================
   THE PIECE STATEMENTS, one or more per walk lane of the three middle segments (the plan's lanes W3a .. W14; the
   harness-level lanes W2, W9 and the two malloc steps are stated in Section h below)
   =================================================================================================== *)
(* W3a: C1 -> the object's header (pod.h:384-395): the NULL test (dead), the block's memset, the two header reads,
   the top size word, and the header of this shape. Its start is the segment's own start state, which is
   rate_build_contract's premise set. *)
Definition rsb_start_M01 (cx : rsb_scx) (rest : list byte) : Prop :=
rsb_pre cx /\
rt_fsh segs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shA rate_himg_B) /\
rt_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L1 rate_himg_B) /\
q_len (x_e cx) = rt_len rest /\ rsb_in cx rest.
Definition rsb_piece_W3a_stmt : Prop :=
forall cx POST rest,
rsb_start_M01 cx rest -> rsb_from_B7 cx POST rest -> rsb_from_BO cx POST rest ->
SRr segs (x_W cx) (cfg_at segs (hi_c1 rate_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
(* W3b: the two header pieces and the property loop's preheader (pod.h:389-398). *)
Definition rsb_piece_W3b_hdr_stmt : Prop :=
forall cx POST rest,
rsb_start_M01 cx rest -> rsb_from_PH cx POST rest -> rsb_from_BO cx POST rest.
Definition rsb_piece_W3b_b7_stmt : Prop :=
forall cx POST rest,
rsb_start_M01 cx rest -> rsb_from_PH cx POST rest -> rsb_from_B7 cx POST rest.
Definition rsb_piece_W3b_pre_stmt : Prop :=
forall cx POST rest,
rsb_start_M01 cx rest -> rsb_from_N cx POST rest 0 -> rsb_from_P cx POST rest ->
rsb_from_PH cx POST rest.
(* W4: one property's selector, its shape-7 body (e into scope, memset(e.body), type and size, the call
   pod_write_ent(pp, e) 0x81054, e out of scope; it enters the latch at its second entry), its key, and the loop's
   latch (from its two entries). *)
Definition rsb_piece_W4_sel_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_SEL7 cx POST rest i -> rsb_from_SELK cx POST rest i ->
rsb_from_N cx POST rest i.
Definition rsb_piece_W4_int7_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_LATCH7 cx POST rest i -> rsb_from_SEL7 cx POST rest i.
Definition rsb_piece_W4_key_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_SELS cx POST rest i -> rsb_from_SELI cx POST rest i ->
rsb_from_SELK cx POST rest i.
Definition rsb_piece_W4_latch_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_N cx POST rest (S i) -> rsb_from_P1 cx POST rest ->
rsb_from_LATCH cx POST rest i /\ rsb_from_LATCH7 cx POST rest i.
(* W5: the Int-7 value pod (e42 into scope, memset(e42), its body, the call pod_write_ent(pp, e42) 0x82404, e42 out of
   scope; it enters the latch at its second entry), the params Struct's header and count, and its close
   (pod.h:412-438). *)
Definition rsb_piece_W5_int_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_LATCH7 cx POST rest i -> rsb_from_SELI cx POST rest i.
Definition rsb_piece_W5_open_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_C cx POST rest i 0 -> rsb_from_CL cx POST rest i ->
rsb_from_SELS cx POST rest i.
Definition rsb_piece_W5_close_stmt : Prop :=
forall cx POST rest i,
rsb_start_M01 cx rest -> rsb_from_LATCH cx POST rest i -> rsb_from_CL cx POST rest i.
(* W6a: the switch's dispatch and its two input-driven exits, then cases 2 and 3. *)
Definition rsb_piece_W6a_disp_stmt : Prop :=
forall cx POST rest i k,
rsb_start_M01 cx rest -> (forall kd, rsb_from_D cx POST rest i k kd) -> rsb_from_D0E cx POST rest i k ->
rsb_from_C cx POST rest i k.
Definition rsb_piece_W6a_cases_stmt : Prop :=
forall cx POST rest i k kd,
rsb_start_M01 cx rest -> In (kd mod 10) [2; 3] -> rsb_from_J cx POST rest i k ->
rsb_from_D cx POST rest i k kd.
(* W6b: cases 1, 4, 5 and 9. W6c: cases 6, 7 and 8. *)
Definition rsb_piece_W6b_stmt : Prop :=
forall cx POST rest i k kd,
rsb_start_M01 cx rest -> In (kd mod 10) [1; 4; 5; 9] -> rsb_from_J cx POST rest i k ->
rsb_from_D cx POST rest i k kd.
Definition rsb_piece_W6c_stmt : Prop :=
forall cx POST rest i k kd,
rsb_start_M01 cx rest -> In (kd mod 10) [6; 7; 8] -> rsb_from_J cx POST rest i k ->
rsb_from_D cx POST rest i k kd.
(* W7a: case 0 up to the parts, from both its entries. W7b: the parts and the key's text. *)
Definition rsb_piece_W7a_stmt : Prop :=
forall cx POST rest i k kd,
rsb_start_M01 cx rest -> kd mod 10 = 0 -> rsb_from_G cx POST rest i k ->
rsb_from_D cx POST rest i k kd /\ rsb_from_D0E cx POST rest i k.
Definition rsb_piece_W7b_stmt : Prop :=
forall cx POST rest i k,
rsb_start_M01 cx rest -> rsb_from_J cx POST rest i k -> rsb_from_G cx POST rest i k.
(* W8: the capacity guard (0x820f0 .. 0x820fc), the call pod_write_ent(pp, e62) 0x82108, the record copy (pod.h:428-432,
   memcpy 0x82170) and e62 out of scope, then the pod loop's latch. *)
Definition rsb_piece_W8_stmt : Prop :=
forall cx POST rest i k,
rsb_start_M01 cx rest -> rsb_from_C cx POST rest i (S k) -> rsb_from_CL cx POST rest i ->
rsb_from_J cx POST rest i k.
(* W10: the top size word, the corruption and the second block's request (pod.h:440-448, fuzz.h:73). *)
Definition rsb_piece_W10_post_stmt : Prop :=
forall cx POST rest,
rsb_start_M01 cx rest -> (forall kk, rsb_from_R cx POST rest kk) -> rsb_from_RT cx POST rest ->
rsb_from_C2 cx POST rest ->
rsb_from_P cx POST rest /\ rsb_from_P1 cx POST rest.
Definition rsb_piece_W10_corr_stmt : Prop :=
forall cx POST rest kk,
rsb_start_M01 cx rest -> rsb_from_R cx POST rest (S kk) -> rsb_from_RT cx POST rest ->
rsb_from_R cx POST rest kk.
Definition rsb_piece_W10_req_stmt : Prop :=
forall cx POST rest,
rsb_start_M01 cx rest -> rsb_from_C2 cx POST rest -> rsb_from_RT cx POST rest.
(* W11a: the second block's fill, hz := 0x5a5a5a5a, the parse, the record's three tests and the two scan loops. Its
   start is rate_check_contract's premise set. The head leaves to E (uncorrupted record, flags bit 0 clear), MAL
   (uncorrupted, bit 0 set: the expectation is -1) and A (corrupted: no check). *)
Definition rsb_start_M02 (cx : rsb_scx) (inp : list byte) : Prop :=
rsb_pre cx /\
rt_fsh segs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shA rate_himg_B) /\
rt_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L3 rate_himg_B) /\
q_len (x_e cx) = rt_len inp /\
rsb_pp_at cx (x_W cx) (x_memc cx) (pp_bytes (fst (pod_build inp))) /\
q_pod (x_e cx) <> 0 /\ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)) /\
YK0o.frm_zero (@fp_csr fx).
Definition rsb_piece_W11a_head_stmt : Prop :=
forall cx POST inp,
rsb_start_M02 cx inp -> rsb_from_E cx POST -> rsb_from_MAL cx POST -> rsb_from_A cx POST ->
SRr segs (x_W cx) (cfg_at segs (hi_c3 rate_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
Definition rsb_piece_W11a_setup_stmt : Prop :=
forall cx POST inp,
rsb_start_M02 cx inp -> rsb_from_O cx POST 0 -> rsb_from_ABS cx POST -> rsb_from_MAL cx POST ->
rsb_from_E cx POST.
Definition rsb_piece_W11a_outer_stmt : Prop :=
forall cx POST inp j,
rsb_start_M02 cx inp -> rsb_from_I cx POST j j -> rsb_from_ABS cx POST ->
rsb_from_O cx POST j.
Definition rsb_piece_W11a_inner_stmt : Prop :=
forall cx POST inp at0 m,
rsb_start_M02 cx inp -> rsb_from_I cx POST at0 (S m) -> rsb_from_KM cx POST at0 m ->
rsb_from_ABS cx POST ->
rsb_from_I cx POST at0 m.
(* W11b: the key compare, the value's two readers and check_rate, and the absent and malformed checks. *)
Definition rsb_piece_W11b_key_stmt : Prop :=
forall cx POST inp at0 m,
rsb_start_M02 cx inp -> rsb_from_O cx POST (S (S m)) -> rsb_from_ABS cx POST ->
rsb_from_MAL cx POST -> rsb_from_A cx POST ->
rsb_from_KM cx POST at0 m.
Definition rsb_piece_W11b_checks_stmt : Prop :=
forall cx POST inp,
rsb_start_M02 cx inp -> rsb_from_A cx POST ->
rsb_from_ABS cx POST /\ rsb_from_MAL cx POST.
(* W13: one decide turn (fuzz_rate.c:263-269) on asked[t], parametric in the turn: reac_rate_cfg_decide, the
   expectation (the role test, the two unrolled bit_of scans over closed_list), check_decide, reac_rate_refuse_code,
   check_code, reac_rate_bit, reac_rate_is_closed, reac_rate_best_drivable and check_list; the latch counts the turn
   in s10 (`bne s10,s9` 0x82f88 with s9 = 2) and goes back to the head with asked[1] or leaves to T2. The
   continuation at turn 2 is never used (the cut holds only for t < 2). *)
Definition rsb_piece_W13_stmt : Prop :=
forall cx POST inp t,
rsb_start_M02 cx inp -> rsb_from_DEC cx POST (S t) -> rsb_from_T2 cx POST ->
rsb_from_DEC cx POST t.
(* W14: the asked[] set-up (fuzz_rate.c:262: asked[0] and asked[1] into the real-frame cells R+0x198 and R+0x19c; no
   scope store) up to the decide loop's
   first turn, the loop's tail (check_code(reac_rate_refuse_code(4), 4)) up to C4, and the list segment M03 (C6 ->
   C7: memset(buf, 0x5a, bl), reac_rate_drivable_csv, check_csv), whose start is rate_csv_contract's premise set.
   The malloc(buf) step C4 -> C6 is Section h's rhb_S_C46_stmt. *)
Definition rsb_piece_W14_asked_stmt : Prop :=
forall cx POST inp,
rsb_start_M02 cx inp -> rsb_from_DEC cx POST 0 -> rsb_from_A cx POST.
Definition rsb_piece_W14_tail_stmt : Prop :=
forall cx POST inp,
rsb_start_M02 cx inp -> rsb_from_C4 cx POST -> rsb_from_T2 cx POST.
Definition rsb_start_M03 (cx : rsb_scx) : Prop :=
rsb_pre cx /\
rt_fsh segs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) (hi_shB rate_himg_B) /\
rt_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L6 rate_himg_B) /\
frames (x_Sc cx) = [(hi_cid rate_himg_B, x_pos cx)] /\
q_buf (x_e cx) <> 0 /\ In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_ly cx) (x_S cx)) /\
YK0o.frm_zero (@fp_csr fx).
Definition rsb_piece_W14_csv_stmt : Prop :=
forall cx POST,
rsb_start_M03 cx -> rsb_from_C7 cx POST ->
SRr segs (x_W cx) (cfg_at segs (hi_c6 rate_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.

(* ===================================================================================================
   THE HARNESS LEVEL: the cuts C1 .. C7 relative to the harness's ENTRY state, the two malloc steps and the five
   segment statements S_E01 .. S_X01 (lib/Prog/LLVMFuzzerTestOneInput_c.v's names, in its continuation form)
   ===================================================================================================
   The whole run is chained in this order:
     ENTRY --S_E01--> C1 --rate_build_contract--> C2 --malloc(pod)--> C3 --rate_check_contract--> C4
     --malloc(buf)--> C6 --rate_csv_contract--> C7 --S_X01--> return,
   and S_M01 = C1 -> C3, S_M02 = C3 -> C4, S_M03 = C4 -> C7. Each harness cut is a self-contained state relative to the
   harness's ENTRY state (the record rhb_hcx) and its journal from there (rhb_j: FP = [], own = the frame for locals, k
   events so far): the frame F = frame_addr of the ENTRY layout (class 4, position pos), the run's quantities e with
   the header values and the input cursor tied to the input bytes (rhb_hdr), the blocks made so far (appended to the
   entry's and not among them), the cut's values (RtPgImgB hi_L1 .. hi_L7), the frame's shadow, and the carried cells.
   - Left out on purpose: rt_seg_pre's static conjuncts (the registered globals' and the strings' shadow, the
     read-only cells and tables, rom_view, the real frame's checked cells, arodata_okP), which the chaining
     re-derives at C1, C3 and C6 from AR and the journal (rhb_static_law, the journal's image clause); and the
     presence of the frame's bytes and shadow, which AR_frames_law gives at every state.
   - What must survive from C1 to C7 across the three middle contracts and the two malloc calls is carried by the
     contracts' "every byte outside the callees' stack and the write set is kept" clauses and the malloc rule's
     acall_kept: the 13 callee-saved words the prologue stores at [S - 0x68, S) (ra at S - 8, s0 at S - 16, ...,
     s11 at S - 0x68: `sd ra,0x218(sp)` 0x80774 .. `sd s11,0x1b8(sp)` 0x807a4 after `addi sp,sp,-0x220`) and the
     frame's flag pointer word at F + 0x3f8 (the class-4 frame law's last word; the release reads it at 0x83030 and
     stores 0 through it at 0x83034). Both are rhb_kept, over RtPgBase's cell form rt_at (LCell).
   - frame_addr and flag_addr read only ly_F, which every journal's layout_le keeps (YG0f.v layout_le), so one F
     serves every cut.
   - C4, C6 and C7 follow the float-changing parse, pod_nearest and the snprintf wrapper: each takes the cut's own
     float state with a zero rounding mode. *)
Section h.
(* the read-only range and the harness constants of RtPgCSpec.rt_lib_contract_x (image B's twins of image A's
   RtPgLib.RO_LO / RO_HI and the relocated frame's ACfn.RA_LLVMF / A_EMPTY / EV_LIB / LIVE_LIB / LLVMF_STK) *)
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* The 13 save slots as RtPgBase cells: S - 8 - 8 j holds the entry value of the j-th register of rsb_saved_regs. *)
Definition rhb_saves_L (regs0 : bvmap 5 word) : list (rt_loc * Z) :=
  map (fun j => (LCell XS (- 8 - 8 * Z.of_nat j), bv_unsigned (getr regs0 (nth j rsb_saved_regs 0%bv)))) (seq 0 13).
(* The cells carried from C1 to C7: the saves, and the frame's flag pointer word at F + 0x3f8. *)
Definition rhb_cells (regs0 : bvmap 5 word) (fl : Z) : list (rt_loc * Z) :=
  rhb_saves_L regs0 ++ [(LCell XF 0x3f8, fl)].

(* ============================== the harness's entry ============================== *)
Record rhb_hcx := RHBCx {
h_ly : alayout; h_S : astate; h_W : world segs; h_regs : bvmap 5 word; h_mem : word -> option byte; h_md : Model;
h_p : Z; h_n : Z; h_pl : list byte }.

(* What every harness-level segment may use of the entry: RtPgCSpec.rt_lib_pre_x without the parts only the final
   leaf reads (asink_none, the fd and fs facts, ameta_inv, the meter) and without its float clause (which the
   segments after the parse, running at the float state it returns, must not mention). *)
Definition rhb_base (hx : rhb_hcx) : Prop :=
afn_pre segs B LLVMF_STK (h_ly hx) (h_S hx) (h_W hx) (h_regs hx) (h_mem hx) (h_md hx) [] /\
raZ (h_regs hx) = RA_LLVMF /\
getr (h_regs hx) 10 = w64 (h_p hx) /\ getr (h_regs hx) 11 = w64 (h_n hx) /\
((h_n hx = 0 /\ h_p hx = A_EMPTY) \/ (0 < h_n hx < 2 ^ 26 /\ In (h_p hx, h_n hx) (ablocks B (h_ly hx) (h_S hx)))) /\
h_n hx = Z.of_nat (length (h_pl hx)) /\
garr8 segs (mrestrict (w_H (h_W hx)) (h_mem hx)) (h_p hx) (map (fun b : byte => bv_unsigned b) (h_pl hx)) /\
frames (h_S hx) = [] /\ st_nev (h_S hx) + EV_LIB <= EV_MAX /\ blocks_bytes (h_S hx) + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H (h_W hx)) (h_mem hx)).

(* The harness's journal from its entry: no footprint, own = the frames taken, k events. *)
Definition rhb_j (hx : rhb_hcx) (own : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world segs)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx) own ly' S' W' mem' md'
k.

(* The geometry: S the entry sp, R the 32-aligned base of the real frame, F the class-4 frame at pos. *)
Definition rhb_geo (hx : rhb_hcx) (pos : Z) (e : rt_renv) : Prop :=
q_S e = spZ (h_regs hx) /\ q_R e = 32 * ((q_S e - RSB_RSZ) / 32) /\ q_F e = frame_addr (h_ly hx) RSB_CID pos.

(* The carried cells (the 13 saves, the flag pointer) at a state. *)
Definition rhb_kept (hx : rhb_hcx) (pos : Z) (e : rt_renv) (W' : world segs) (mem' : word -> option byte)
(regs' : bvmap 5 word) : Prop :=
Forall (fun f => rt_at segs (w_H W') mem' regs' e (fst f) (snd f))
(rhb_cells (h_regs hx) (flag_addr (h_ly hx) RSB_CID pos)).

(* The header (fuzz_rate.c:236-239, fuzz.h:37-56: fuzz_u8 reads one byte, or gives 0 and reads nothing when no byte
   is left; fuzz_u32 is four fuzz_u8, little-endian): byte i of the input or 0; flags = byte 0, mask = byte 1,
   buflen = byte 2 mod 24, other = bytes 3 .. 6; pod_build reads the input after these 7 bytes, at
   p + min(7, n), n - min(7, n) of them (the plain walk's g_u8 .. g_k, lib/Prog/SlotInv.v). *)
Definition rhb_u8 (pl : list byte) (i : nat) : Z :=
match nth_error pl i with Some b => bv_unsigned b | None => 0 end.
Definition rhb_hdr (hx : rhb_hcx) (e : rt_renv) (rest : list byte) : Prop :=
q_fl e = rhb_u8 (h_pl hx) 0 /\ q_mask e = rhb_u8 (h_pl hx) 1 /\ q_buflen e = rhb_u8 (h_pl hx) 2 mod 24 /\
q_b3 e = rhb_u8 (h_pl hx) 3 /\ q_b4 e = rhb_u8 (h_pl hx) 4 /\ q_b5 e = rhb_u8 (h_pl hx) 5 /\
q_b6 e = rhb_u8 (h_pl hx) 6 /\
rest = skipn 7 (h_pl hx) /\ q_src e = h_p hx + Z.min 7 (h_n hx) /\ q_left e = h_n hx - Z.min 7 (h_n hx) /\
q_len e = rt_len rest.

(* rate_build_contract's input premises at rest (RtPgCSpec.v rate_build_contract, after rt_cut). *)
Definition rhb_input (W' : world segs) (mem' : word -> option byte) (e : rt_renv) (rest : list byte) : Prop :=
q_left e = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H W') mem') (q_src e) (map (fun x : byte => bv_unsigned x) rest) /\
range_addressable (aview segs (w_H W') mem') SHADOW_OFF (q_src e) (q_left e) /\
0 < q_src e /\ q_src e + q_left e <= 2 ^ 63 /\ amem_range (q_src e) (q_left e) /\
(0 < q_left e -> shadow_hull_vis (aview segs (w_H W') mem') (q_src e) (q_left e)) /\
(forall a, q_src e <= a < q_src e + q_left e ->
 ~ (q_R e - T_SEG_STK <= a < q_R e) /\ ~ rt_inw e (hi_w1 rate_himg_B) a /\ ~ (q_pp e <= a < q_pp e + Layout.PP_SIZE)).

(* What every harness cut shares: the journal at k events with the frame for locals as the only frame, the blocks
   made so far (bl, in the order they were made) appended to the entry's and none of them among the entry's, sp = R,
   gp, tp, the geometry, the header tie, the header bounds, the carried cells, and the cut's values. *)
Definition rhb_common (hx : rhb_hcx) (pos : Z) (e : rt_renv) (rest : list byte) (k : Z) (bl : list (Z * Z))
(L : list (rt_loc * rt_x))
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_j hx [(RSB_CID, pos)] ly2 S2 W2 mem2 md2 k /\ frames S2 = [(RSB_CID, pos)] /\
Permutation (ablocks B ly2 S2) (ablocks B (h_ly hx) (h_S hx) ++ bl) /\
Forall (fun b => ~ In b (ablocks B (h_ly hx) (h_S hx))) bl /\
getr regs2 2 = w64 (q_R e) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
rhb_geo hx pos e /\ rhb_hdr hx e rest /\ rt_hdr_ok e /\
rt_cut segs (w_H W2) mem2 regs2 e L /\
rhb_kept hx pos e W2 mem2 regs2.

(* ============================== C1: what S_E01 delivers ==============================
   The frame taken, malloc(pp) done (one event, the block appended), the prologue's frame shadow, the C1 values
   (RtPgImgB hi_L1), and the input after the 7-byte header (rhb_input at rest = skipn 7 of the input). *)
Definition rhb_cut_C1 (hx : rhb_hcx) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_common hx pos e rest 1 [(q_pp e, Layout.PP_SIZE)] (hi_L1 rate_himg_B) ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rsb_P0 /\
rhb_input W2 mem2 e rest.
(* ============================== C2: what rate_build_contract's post gives the malloc(pod) step ==============
   The C2 values (hi_L2), the prologue's shadow again, pp holding Layout.pp_bytes of the record pod_build made of
   rest, and the request's bounds (8 <= len <= 5440: RtPgCSpec's site lemma for the build). *)
Definition rhb_cut_C2 (hx : rhb_hcx) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_common hx pos e rest 1 [(q_pp e, Layout.PP_SIZE)] (hi_L2 rate_himg_B) ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rsb_P0 /\ 8 <= q_len e <= 5440 /\
garr8 segs (mrestrict (w_H W2) mem2) (q_pp e) (map (fun x : byte => bv_unsigned x) (pp_bytes (fst (pod_build rest)))).
(* ============================== C3: what the malloc(pod) step delivers ==============================
   Two events, pod appended (len bytes: len >= 8, so the request len + (len == 0) is len), the C3 values (hi_L3), the
   prologue's shadow, pp's bytes kept. *)
Definition rhb_cut_C3 (hx : rhb_hcx) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_common hx pos e rest 2 [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e)] (hi_L3 rate_himg_B)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rsb_P0 /\ 8 <= q_len e <= 5440 /\
garr8 segs (mrestrict (w_H W2) mem2) (q_pp e) (map (fun x : byte => bv_unsigned x) (pp_bytes (fst (pod_build rest)))).
(* ============================== C4: what rate_check_contract's post gives the malloc(buf) step ==============
   The C4 values (hi_L4), hz in scope (rsb_PB), at the cut's own float state fx4. *)
Definition rhb_cut_C4 (hx : rhb_hcx) (fx4 : YK11.FPState) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_common hx pos e rest 2 [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e)] (hi_L4 rate_himg_B)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rsb_PB /\ YK0o.frm_zero (@fp_csr fx4).
(* ============================== C6: what the malloc(buf) step delivers ==============================
   Three events, buf appended (its block length is the request rt_bl buflen in [1, 23]), the C6 values (hi_L6). *)
Definition rhb_cut_C6 (hx : rhb_hcx) (fx6 : YK11.FPState) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_common hx pos e rest 3
  [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e); (q_buf e, rt_bl (q_buflen e))] (hi_L6 rate_himg_B)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ q_buf e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rsb_PB /\
YK0o.frm_zero (@fp_csr fx6).
(* ============================== C7: what rate_csv_contract's post gives S_X01 ============================== *)
Definition rhb_cut_C7 (hx : rhb_hcx) (fx7 : YK11.FPState) (pos : Z) (e : rt_renv) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rhb_common hx pos e rest 3
  [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e); (q_buf e, rt_bl (q_buflen e))] (hi_L7 rate_himg_B)
  ly2 S2 W2 regs2 mem2 md2 /\
q_pp e <> 0 /\ q_pod e <> 0 /\ q_buf e <> 0 /\ rt_fsh segs (w_H W2) mem2 (q_F e) rsb_PB /\
YK0o.frm_zero (@fp_csr fx7).

(* The return: knock's rt_post (APgRt.v) in rate's terms: at RA_LLVMF, the journal from the entry closed (own = [],
   at most the six events), the callee-saved registers restored, a0 = 0, the entry's blocks again. The float state
   is the one the configuration carries (S_X01 executes no float instruction; its callees keep the float state). *)
Definition rhb_ret (hx : rhb_hcx) : world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RA_LLVMF regs' mem' md' /\ YK0o.frm_zero (@fp_csr fx') /\
rhb_j hx [] ly' S' W' mem' md' k /\ k <= RSB_EV /\
aregs_preserved (h_regs hx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (h_ly hx) (h_S hx)).

(* ============================== the continuations at the harness cuts ============================== *)
Definition rhb_from_C1 (hx : rhb_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rhb_cut_C1 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_C1 regs2 mem2 md2) POST.
Definition rhb_from_C2 (hx : rhb_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rhb_cut_C2 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_C2 regs2 mem2 md2) POST.
Definition rhb_from_C3 (hx : rhb_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rhb_cut_C3 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RSB_C3 regs2 mem2 md2) POST.
Definition rhb_from_C4 (hx : rhb_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx4 pos e rest ly2 S2 W2 regs2 mem2 md2, rhb_cut_C4 hx fx4 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx4 segs RSB_C4 regs2 mem2 md2) POST.
Definition rhb_from_C6 (hx : rhb_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx6 pos e rest ly2 S2 W2 regs2 mem2 md2, rhb_cut_C6 hx fx6 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx6 segs RSB_C6 regs2 mem2 md2) POST.
Definition rhb_from_C7 (hx : rhb_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx7 pos e rest ly2 S2 W2 regs2 mem2 md2, rhb_cut_C7 hx fx7 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx7 segs RSB_C7 regs2 mem2 md2) POST.

(* ============================== the segment statements ==============================
   S_E01 (lane W2), ENTRY -> C1: the prologue (saves at [S - 0x68, S)); n < 2^26, so `beqz` 0x809b4 is taken;
   the frame (option byte 1, so `beqz` 0x807d4 falls through: frame_alloc_4(704) 0x807dc, `bnez s8` 0x807f0 taken),
   its header (0x80814 .. 0x80844) and its shadow (0x80850 .. 0x809b0); the seven header reads in their eight
   input-length arms (0x809bc .. 0x80adc and the out-of-line blocks 0x8276c .. 0x827a8, 0x8286c .. 0x828d8,
   0x82d38 .. 0x82d70); malloc(19744) at 0x80ae0 with ra = 0x80ae4. *)
Definition S_E01 : Prop :=
forall (hx : rhb_hcx) POST, rhb_base hx -> rhb_from_C1 hx POST ->
SRr segs (h_W hx) (cfg_at segs RSB_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) POST.
(* S_M01, C1 -> C3: rate_build_contract at rate_himg_B (from C1, with rt_seg_pre's static conjuncts from
   rhb_static_law), then the malloc(pod) step (rhb_S_C23_stmt). *)
Definition S_M01 : Prop :=
forall (hx : rhb_hcx) POST, rhb_base hx -> rhb_from_C3 hx POST -> rhb_from_C1 hx POST.
(* S_M02, C3 -> C4: rate_check_contract at rate_himg_B. *)
Definition S_M02 : Prop :=
forall (hx : rhb_hcx) POST, rhb_base hx -> rhb_from_C4 hx POST -> rhb_from_C3 hx POST.
(* S_M03, C4 -> C7: the malloc(buf) step (rhb_S_C46_stmt), then rate_csv_contract at rate_himg_B. *)
Definition S_M03 : Prop :=
forall (hx : rhb_hcx) POST, rhb_base hx -> rhb_from_C7 hx POST -> rhb_from_C4 hx POST.
(* S_X01 (lane W9), C7 -> RET: free(buf) 0x82ff0 (a0 = s5), free(pod) 0x82ff8 (a0 = R+0x178), free(pp) 0x83000
   (a0 = R+0x168); hz := 0xf8 (0x83008); F[0] := 0x45e0360e (0x8301c, F = R+0x60 in s9); `beqz s8` 0x83020 not taken
   (s8 = the frame call's result from R+0x10); meta_fill_f5(s3, 128) 0x8302c; the flag byte := 0 through F + 0x3f8
   (0x83030 .. 0x83034); a0 = 0 (0x83048) and the epilogue (0x8304c .. 0x83088). *)
Definition S_X01 : Prop :=
forall (hx : rhb_hcx), rhb_base hx -> rhb_from_C7 hx (rhb_ret hx).
Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_X01.

(* The two malloc steps the middle statements add to their contracts.
   C2 -> C3 (lane W10): the `jal` at 0x82a2c with a0 = len + (len == 0) = len (`ld s6,0(t2)`, `seqz a0,s6`,
   `add a0,s6,a0`, 0x82a20 .. 0x82a28) and the call.
   C4 -> C6 (lane W14): `ld s4,0x18(s1)` (buflen), `seqz s6,s4`, `add s6,s4,s6`, `mv a0,s6` (0x82f9c .. 0x82fa8),
   the `jal` at 0x82fac and the call. *)
Definition rhb_S_C23_stmt : Prop :=
forall (hx : rhb_hcx) POST, rhb_base hx -> rhb_from_C3 hx POST -> rhb_from_C2 hx POST.
Definition rhb_S_C46_stmt : Prop :=
forall (hx : rhb_hcx) POST, rhb_base hx -> rhb_from_C6 hx POST -> rhb_from_C4 hx POST.

(* The five statements compose into the whole run: from ENTRY, the return. *)
Lemma rhb_seg_chain : seg_lemmas -> forall hx : rhb_hcx, rhb_base hx ->
SRr segs (h_W hx) (cfg_at segs RSB_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) (rhb_ret hx).
Proof.
intros (HE & HM1 & HM2 & HM3 & HX) hx Hb.
exact (HE hx (rhb_ret hx) Hb (HM1 hx _ Hb (HM2 hx _ Hb (HM3 hx _ Hb (HX hx Hb))))).
Qed.

(* ============================== the static facts of rt_seg_pre ==============================
   The shadow of the registered globals and of the strings, the read-only cells, the tables and every read-only byte,
   at any state AR accepts with the read-only data as in the image. They are static facts of the symbols B (the
   start-up's const cells and zero-shadow ranges, AR's am_const / al_zshadow, and the owned read-only bytes pinned as
   const cells), not facts a cut can carry: a global's shadow byte and an owned read-only byte are aowned, and the
   allocator's post keeps no aowned byte (YG0d.v acall_post). The chaining takes this law at the three middle
   contracts' starts. *)
Definition rhb_static_law : Prop :=
forall ly S (W : world segs) mem md,
AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_B) /\
Forall (fun s => rt_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs rate_himg_B) /\
rt_ro_cells segs (w_H W) mem (hi_cells rate_himg_B) /\
Forall (fun t => rt_i32tab segs (w_H W) mem (fst t) (snd t)) (hi_i32 rate_himg_B) /\
Forall (fun t => rt_u64tab segs (w_H W) mem (fst t) (snd t)) (hi_u64 rate_himg_B) /\
rom_view segs W mem.
End h.

End d.
End c.
End b.

Print Assumptions rsb_pcs_himg.
Print Assumptions rsb_closed_himg.
Print Assumptions rhb_seg_chain.
