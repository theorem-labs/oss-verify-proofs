(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): THE CUT STATES of the walk
   of LLVMFuzzerTestOneInput (0x7ff88, 11308 bytes, 2827 instructions) and the statement of every segment and of
   every piece the walk is split into. Statement text only: no function is proved here.

   WHAT THIS FILE IS FOR. The walk is cut at the four points the plain walk of the same function is cut at
   (lib/Prog/LLVMFuzzerTestOneInput_c.v): ENTRY, K80194 (the malloc of the first block returned), K820c4 (the malloc
   of the second block returned), K82478 (the instruction after the last check returns) and RET. The four segments
   keep the plain walk's names S_E01 / S_M01 / S_M02 / S_X01, and the two middle ones are the fixed contracts
   role_build_contract and role_check_contract of lib/A/RPgCSpec.v at image A's record RPgImgA.role_himg_A. Each of
   those two segments is cut again at the heads and the joins of its loops and at the boundaries of its pieces, and
   every piece is stated here, so that the pieces are proved in parallel and each proof sees only the STATEMENTS of
   the pieces its continuation goes to.

   HOW A CUT IS STATED, AND WHY NOT AS A SYMBOLIC STATE. A cut is a SEMANTIC predicate over
   (ly, S, W, regs, mem, md) at the cut's pc: the caller's journal from the segment's start, the frame's shadow
   bytes, the first block's image, the input bytes left, and a list of (location, value) facts over the run's
   quantities (RPgBase.rl_at: a register, or the 8-byte cell at an offset of a base). A symbolic state can only be
   written down after the piece before it has been run, which would serialise the pieces; a semantic cut lets each
   piece rebuild its own symbolic state from the cut, as the released walks rebuild the entry one.
   A cut states only POSITIVE facts. What a call leaves alone is not restated: the journal's own clauses and each
   callee's write-set post carry it between cuts.

   WHERE A VALUE LIVES. Image A keeps the harness's values in registers and in 8-byte cells of the real frame at
   R + off, R = 32 * floor((S - 0x1a0) / 32) being the 32-aligned base the prologue puts in s1 and sp (0x7ffc8,
   0x7ffcc) and S the entry sp (s0, 0x7ffc4). The locals whose address is taken live in the frame for locals F, a
   side-stack frame of class 3 that the prologue takes (0x7fff4 `addi a0,zero,0x1a0`, 0x7fff8 the call, s6 = s9 = F):
   t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at F+0xf0 and role at F+0x180. s3 = (F >> 3) + K
   is the frame's shadow base and s7 = K the runtime's shadow offset. sp = R from 0x7ffcc to the epilogue.

   THE MODEL. The quantities a cut names are the shared model's (lib/Pod): the record built so far is a
   Model.pb_cut (the shape, the properties written and, inside a params Struct, the pods written), the first block
   holds Layout.pc_image of it, what is left of the input is a suffix of the bytes after the flags byte, and the
   cursor that names it is src + |rest| - |r|. At the end of the build the block holds Layout.pp_bytes of the record
   Model.pod_build makes; the checking segment reads it back and its scan computes Role.expect_model step by step. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Role Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the pcs of the cuts ============================================
   Each is the address of the first instruction of the piece that starts there; the four segment cuts are
   RPgImgA.role_himg_A's hi_c1 .. hi_c4. *)
Definition RS_ENTRY : Z := 0x7ff88.      (* `addi sp,sp,-0x1a0` *)
Definition RS_RET : Z := 0x825cc.        (* `ret` *)
Definition RS_K82480 : Z := 0x82480.     (* `mv a0,s11` after the first release *)
Definition RS_J82494 : Z := 0x82494.     (* `lui a0,0x45e03`: the frame's retirement word, after both releases *)
(* inside the build (M01) *)
Definition RS_B7 : Z := 0x802f4.         (* the shape-7 object header, from `bne a3,a2` 0x802f0 *)
Definition RS_BO : Z := 0x80364.         (* the Object header (shape <> 7) *)
Definition RS_PH : Z := 0x8051c.         (* `sd a6,0x10(s1)`: the property loop's preheader *)
Definition RS_N : Z := 0x805e8.          (* `sd a6,0xb8(s1)`: the property loop's head *)
Definition RS_SEL7 : Z := 0x80654.       (* the shape-7 Int pod of one property *)
Definition RS_SELK : Z := 0x80800.       (* a property's key, its flags and the `first` test *)
Definition RS_SELI : Z := 0x81ae8.       (* the Int-7 value pod *)
Definition RS_SELS : Z := 0x80940.       (* the params Struct's header and its pod count *)
Definition RS_C : Z := 0x80a80.          (* `sd a1,0xd8(s1)`: the pod loop's head *)
Definition RS_D0 : Z := 0x80b40.         (* ent_build case 0 (the head-amp key), with input left *)
Definition RS_D0E : Z := 0x80bac.        (* ent_build case 0 with no input left *)
Definition RS_D1 : Z := 0x80fd8.
Definition RS_D2 : Z := 0x80eb4.
Definition RS_D3 : Z := 0x80f1c.
Definition RS_D4 : Z := 0x80e68.
Definition RS_D5 : Z := 0x81020.
Definition RS_D6 : Z := 0x810a8.
Definition RS_D7 : Z := 0x80f64.
Definition RS_D8 : Z := 0x810f8.
Definition RS_D9 : Z := 0x81184.
Definition RS_G : Z := 0x80d14.          (* case 0 after the digits, the reverse and the odd_ch part *)
Definition RS_J : Z := 0x8165c.          (* the pod is built: the inlined pod_write_ent begins *)
Definition RS_CL : Z := 0x81ccc.         (* the params Struct's size word is about to be patched *)
Definition RS_LATCH : Z := 0x81d6c.      (* the property loop's latch *)
Definition RS_LATCH7 : Z := 0x81d74.     (* its second entry, from the shape-7 piece *)
Definition RS_P : Z := 0x81ed4.          (* the builder's end, entered with no property *)
Definition RS_P1 : Z := 0x81ed8.         (* its second entry, from the latch *)
Definition RS_R : Z := 0x82018.          (* the corruption loop's head *)
Definition RS_RT : Z := 0x82094.         (* after the corruption: corrupt := 1, then the second request *)
(* inside the checks (M02) *)
Definition RS_E : Z := 0x8212c.          (* the inlined expect_role begins *)
Definition RS_O : Z := 0x821bc.          (* its outer scan head *)
Definition RS_I : Z := 0x821e0.          (* its inner scan head *)
Definition RS_KM : Z := 0x822a8.         (* a key was found: the compare and then the value *)
Definition RS_ABS : Z := 0x82380.        (* no pair matched: the absent check *)
Definition RS_MAL : Z := 0x823fc.        (* the malformed check *)
Definition RS_T : Z := 0x82408.          (* the tail: the answer and the two codes *)

(* the 13 callee-saved words the prologue writes at [S - 0x68, S) (0x7ff90 .. 0x7ffc0) and the epilogue reads back
   (0x82594 .. 0x825c4), in the order of their offsets -8, -0x10, ..., -0x68 *)
Definition rs_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the frame for locals is a side-stack frame of class 3 (RPgImgA: hi_cid role_himg_A) *)
Definition RS_CID : Z := 3.
(* the real frame below S (`addi sp,sp,-0x1a0`) *)
Definition RS_RSZ : Z := 0x1a0.
(* the events the walk's journal records: two allocations and two releases *)
Definition RS_EV : Z := 4.

(* The byte values of the frame's shadow at the states the walk passes through. P0 is the prologue's pattern
   (RPgImgA.role_A_shA, 52 granules); PJ opens e's 13 granules 0x1e .. 0x2a (the pod loop's stores 0x80a84 ..
   0x80ab4; closed again at 0x81858 / 0x81c98); PB opens the role granule 0x30 (0x820ec; closed at 0x8248c) and is
   RPgImgA.role_A_shB. *)
Definition rs_P0 : list Z := role_A_shA.
Definition rs_PJ : list Z := firstn 30 role_A_shA ++ repeat 0 13 ++ skipn 43 role_A_shA.
Definition rs_PB : list Z := role_A_shB.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

Definition rs_u8s (l : list byte) : list Z := map (fun x : byte => bv_unsigned x) l.

(* a list of (location, value) facts, through RPgBase.rl_at: a register holds the 64-bit word of v, a cell holds
   its 8 little-endian bytes *)
Definition rs_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rl_env)
(L : list (rl_loc * Z)) : Prop :=
Forall (fun f => rl_at segs H mem regs e (fst f) (snd f)) L.

(* ========================= what every cut INSIDE a segment carries =========================
   The segment's own journal from its start (with the segment's event count: neither middle segment allocates),
   sp / gp / tp as at the start, the frames, the blocks, the I/O state and the meter as at the start, and every
   byte outside the callees' stack [R - T_SEG_STK, R) and outside the ranges the segment writes as at the start.
   These are exactly the clauses of RPgCSpec.rl_seg_post without its pc and its result, so the cut at a segment's
   last pc IS that segment's post. *)
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
   (RPgBase.rl_env: S, R, F, the two blocks, len, the flags byte, the input cursor and what is left of it), the
   position of the frame for locals among the side stack's frames of its class, and the read-only range. A cut
   inside the segment is a predicate over this record and the state at the cut. *)
Record rs_scx := RSCx {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z);
x_ly : alayout; x_S : astate; x_W0 : world segs; x_mem0 : word -> option byte; x_md0 : Model;
x_own : list (Z * Z); x_k : Z; x_regs : bvmap 5 word;
x_lyc : alayout; x_Sc : astate; x_W : world segs; x_memc : word -> option byte; x_mdc : Model;
x_RLO : Z; x_RHI : Z; x_e : rl_env; x_pos : Z }.

(* what the segment's contract asks at its start (RPgCSpec.rl_seg_pre at image A's record) *)
Definition rs_pre (cx : rs_scx) : Prop :=
rl_seg_pre segs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
(x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)
role_himg_A (x_RLO cx) (x_RHI cx) (x_e cx) (x_pos cx).

(* the journal-and-frame part of a cut inside the segment, with the segment's write set E *)
Definition rs_core (cx : rs_scx) (E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rs_mid (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
(x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) E ly2 S2 W2 regs2 mem2 md2.

(* the two segments' write sets, as their contracts state them: the image's ranges (RPgImgA: hi_w1 = the frame's
   objects, their shadow bytes and the real frame; hi_w2 = the role cell, its shadow byte, the spills around the
   string compare and the two checked real-frame cells) and the block the segment fills *)
Definition rs_E1 (cx : rs_scx) : Z -> Prop :=
fun a => rl_inw (x_e cx) (hi_w1 role_himg_A) a \/
e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE.
Definition rs_E2 (cx : rs_scx) : Z -> Prop :=
fun a => rl_inw (x_e cx) (hi_w2 role_himg_A) a \/
e_pod (x_e cx) <= a < e_pod (x_e cx) + e_len (x_e cx).

(* the first block's bytes at a cut *)
Definition rs_pp_at (cx : rs_scx) (W2 : world segs) (mem2 : word -> option byte) (l : list byte) : Prop :=
garr8 segs (mrestrict (w_H W2) mem2) (e_pp (x_e cx)) (rs_u8s l).
(* the frame's shadow bytes at a cut *)
Definition rs_fsh_at (cx : rs_scx) (W2 : world segs) (mem2 : word -> option byte) (pat : list Z) : Prop :=
rl_fsh segs (w_H W2) mem2 (e_F (x_e cx)) pat.
(* the values at a cut's locations *)
Definition rs_at_cx (cx : rs_scx) (W2 : world segs) (mem2 : word -> option byte) (regs2 : bvmap 5 word)
(L : list (rl_loc * Z)) : Prop :=
rs_at (w_H W2) mem2 regs2 (x_e cx) L.

(* What is left of the input the build reads: a suffix of the bytes after the flags byte, and the cursor that
   names it. e_src is where those bytes lie and e_left how many there are. *)
Definition rs_suffix (rest r : list byte) : Prop := exists j, (j <= length rest)%nat /\ r = skipn j rest.
Definition rs_cur (cx : rs_scx) (rest r : list byte) : Z :=
e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r).
(* the input bytes, as role_build_contract gives them: at e_src, outside the callees' stack, the ranges the
   segment writes and the first block *)
Definition rs_in (cx : rs_scx) (rest : list byte) : Prop :=
e_left (x_e cx) = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_src (x_e cx)) (rs_u8s rest) /\
range_addressable (aview segs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)) /\
(0 < e_left (x_e cx) -> shadow_hull_vis (aview segs (w_H (x_W cx)) (x_memc cx)) (e_src (x_e cx)) (e_left (x_e cx))) /\
amem_range (e_src (x_e cx)) (e_left (x_e cx)) /\
0 < e_src (x_e cx) /\ e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 63 /\
(forall a, e_src (x_e cx) <= a < e_src (x_e cx) + e_left (x_e cx) ->
 ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) /\ ~ rl_inw (x_e cx) (hi_w1 role_himg_A) a /\
 ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)).

(* ===================================================================================================
   THE BUILD (M01): the cuts of role_build_contract's walk, from C1 = 0x80194 to C2 = 0x820c0
   ===================================================================================================
   The builder writes one object into the first block. Its state at a cut is the record so far (a
   Model.pb_cut: the shape sh, the properties ps written and, inside a params Struct, the pods es written),
   what is left of the input, and the loop counters; the block holds Layout.pc_image of that state and the
   R-relative cells hold the loop's constants and counters. *)

(* The constants the preheader (0x8051c .. 0x805e4) puts in R-relative cells and no piece writes again:
   0x15555556 is the `% 12u` multiplier (pod.h:354, 0x805ac), 0x10003 is SPA_PROP_VOLUME (0x805b4), 0x80001 is
   SPA_PROP_params (0x805bc), -0x4001 and -0x3ffd are the two capacity bounds (0x805a0, 0x80260), R+0x10 and
   R+0x18 are the top size word's offset (0: the block's length before the header) and its address. *)
Definition rs_Kc (cx : rs_scx) (sh np : Z) : list (rl_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x0, 0x15555556); (LCell XR 0x8, e_F e); (LCell XR 0x10, 0); (LCell XR 0x18, e_pp e);
 (LCell XR 0x20, e_F e + 0x100); (LCell XR 0x28, e_F e); (LCell XR 0x30, e_fl e);
 (LCell XR 0x38, 0x10003); (LCell XR 0x40, e_pp e + 0x4010);
 (LCell XR 0x48, 0x80001); (LCell XR 0x50, e_pp e + 0x400c);
 (LCell XR 0x58, e_F e + 0xa0); (LCell XR 0x60, e_pp e + 0x4014);
 (LCell XR 0x68, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0x70, e_pp e + 0x4000);
 (LCell XR 0x78, e_pp e + 0x4d14); (LCell XR 0x80, e_pp e);
 (LCell XR 0x90, np); (LCell XR 0x98, sh);
 (LCell XR 0xb0, shadow_addr (e_pp e + 0x4000)); (LCell XR 0xc0, e_F e + 0xf8);
 (LCell XR 0xe0, -0x4001); (LCell XR 0xe8, -0x3ffd); (LCell XR 0xf0, e_F e + 0xf0)].

(* the `v / 10` multiplier of the digit loop (pod.h:240-241), in s2 from 0x805a4 / 0x805c8 *)
Definition RS_MULT10 : Z := 0xcccccccd * 2 ^ 32.

(* the registers the property loop keeps: s0 = S, s1 = R, s3 = the frame's shadow base, s7 = the runtime's
   shadow offset, s2 = the multiplier, s6 = &r, s10 = &t, s11 = the block, s5 = &pp->len *)
Definition rs_Rc0 (cx : rs_scx) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 18, RS_MULT10); (LReg 22, e_F e + 0xe0); (LReg 26, e_F e + 0x20);
 (LReg 21, e_pp e + 0x4000)].
Definition rs_Rc (cx : rs_scx) : list (rl_loc * Z) := rs_Rc0 cx ++ [(LReg 27, e_pp (x_e cx))].

(* the cursor's two cells: R+0xc8 holds in.p and R+0xf8 in.n *)
Definition rs_cur2 (cx : rs_scx) (rest r : list byte) : list (rl_loc * Z) :=
[(LCell XR 0xc8, rs_cur cx rest r); (LCell XR 0xf8, Z.of_nat (length r))].

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

(* ---------------- the build's first own cuts: 0x802f4 (shape 7) and 0x80364 (any other shape) ----------
   The block was filled with zeros (0x801a8), the two header bytes were read, and the top size word was
   written as four zero bytes with len := 4 (0x802a0 .. 0x802c8). a0 is that length, a1 = len - 0x3ffd is the
   capacity test's left side, a5 = pp + 0 and a6 = 0 are the top word's address and offset, and s4 = 0x5000
   is the constant the preheader turns into &pp->n_ent. *)
Definition rs_L_hdr (cx : rs_scx) (sh np : Z) (rest r : list byte) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 10, 4); (LReg 11, 4 - 0x3ffd); (LReg 15, e_pp e); (LReg 16, 0); (LReg 20, 0x5000);
 (LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 22, e_F e); (LReg 25, e_F e); (LReg 27, e_pp e);
 (LCell XR 0x30, e_fl e); (LCell XR 0x90, np); (LCell XR 0x98, sh);
 (LCell XR 0xb0, shadow_addr (e_pp e + 0x4000)); (LCell XR 0xe8, -0x3ffd)] ++ rs_cur2 cx rest r.
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

(* ---------------- PH = 0x8051c: the header is written, the preheader is about to run ----------------
   The block holds the image of the empty record of this shape (its header bytes and, for an Object,
   is_props); a6 and a5 still hold the top word's offset and address, which the preheader spills. *)
Definition rs_L_PH (cx : rs_scx) (sh np : Z) (rest r : list byte) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 15, e_pp e); (LReg 16, 0); (LReg 20, 0x5000);
 (LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 22, e_F e); (LReg 25, e_F e); (LReg 27, e_pp e);
 (LCell XR 0x30, e_fl e); (LCell XR 0x90, np); (LCell XR 0x98, sh);
 (LCell XR 0xb0, shadow_addr (e_pp e + 0x4000)); (LCell XR 0xe8, -0x3ffd)] ++ rs_cur2 cx rest r.
Definition rs_cut_PH (cx : rs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_PH cx sh np rest r) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh [] None)) /\
rs_in cx rest /\ rs_suffix rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ r = rs_r0 rest.

(* ---------------- N = 0x805e8: the property loop's head, |ps| properties written ----------------
   The property index is in a6 and `seen` in s9. R+0xb8 is NOT part of the state: the pc writes it. *)
Definition rs_L_N (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc cx ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
             (LReg 16, Z.of_nat (length ps)); (LReg 25, rs_seen ps)]
++ rs_Kc cx sh np ++ rs_cur2 cx rest r.
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
   SEL7 0x80654 (shape 7: the property is an Int pod with no key) and SELK 0x80800 (any other shape: the
   key, its flags and the `first` test). a0 is pp->len at the cut and a2 = len - 0x3ffd its capacity test's
   left side; a1 is the selector byte at SELK. *)
Definition rs_L_SEL (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc cx ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
             (LReg 10, rs_plen sh ps); (LReg 12, rs_plen sh ps - 0x3ffd); (LReg 25, rs_seen ps)]
++ rs_Kc cx sh np ++ [(LCell XR 0xb8, Z.of_nat (length ps))] ++ rs_cur2 cx rest r.
(* what every cut of one property's body shares with N, with the tie of ps to the input: the properties
   written are the ones Model.props_loop makes of the bytes after the two header reads *)
Definition rs_prop_base (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
e_len (x_e cx) = rl_len rest /\
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
   SELI 0x81ae8 writes the Int value pod of a property whose value is an Int (the volume property, and a
   params property whose selector has bit 4 set), SELS 0x80940 opens a params Struct. On both, the key
   word and the flags word are already written, so the block's bytes are the record's image with those
   eight bytes appended; `at` (R+0xa0) is the open Struct's size word offset and a0 = at - 0x3ffd is the
   capacity test's left side (0x8092c .. 0x80934). The cells R+0x88 (seen') and R+0xd0 (first) are set
   only on the params arm (0x808f0 .. 0x8091c). *)
Definition rs_img_key (sh : Z) (ps : list (Z * pval)) (kk : Z) : list byte :=
pp_image (pc_buf (PbCut sh ps None) ++ le32 kk ++ le32 0)
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
(* the key the selector chooses (Model.prop_step): the volume property, else the params property *)
Definition rs_key_of (sel : Z) : Z := if sel mod 4 =? 0 then 0x10003 else 0x80001.
Definition rs_L_KEY (cx : rs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc cx ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 10, rs_at_of sh ps - 0x3ffd)]
++ rs_Kc cx sh np
++ [(LCell XR 0xb8, Z.of_nat (length ps)); (LCell XR 0xa0, rs_at_of sh ps);
    (LCell XR 0x88, if sel mod 4 =? 0 then rs_seen ps else 1);
    (LCell XR 0xd0, if sel mod 4 =? 0 then 0 else rs_first ps)]
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

(* ---------------- C = 0x80a80: the pod loop's head, |es| pods written ----------------
   The cursor moves into s9 here and R+0xc8 is dead; the pod index is in a1 (the pc spills it to R+0xd8),
   the count in R+0xa8, `at` in R+0xa0, `first` in R+0xd0 and seen' = 1 in R+0x88. The frame's shadow is
   still the prologue's: the pc at 0x80a84 opens e's granules. *)
Definition rs_L_pod (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc cx ++ rs_Kc cx sh np
++ [(LCell XR 0xb8, Z.of_nat (length ps)); (LCell XR 0xa0, rs_at_of sh ps);
    (LCell XR 0xa8, cnt); (LCell XR 0x88, 1); (LCell XR 0xd0, rs_first ps);
    (LCell XR 0xf8, Z.of_nat (length r)); (LReg 25, rs_cur cx rest r)].
(* What every cut inside the pod loop shares, with the tie of the count and the pods to the input: the
   selector picked the params Struct, the count byte gave cnt = c mod 33 (pod.h:425) and the pods written
   are the ones Model.ents_loop makes of what follows it, leaving rr at the turn's start. *)
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
e_len (x_e cx) = rl_len rest /\
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
   The dispatch (0x80a84 .. 0x80b3c) opens e's granules, fills e with zeros, reads the kind byte and jumps
   through the nine relative entries at .rodata 0x20e94; `bltu 8,a1` 0x80b18 takes case 9 and `beqz` 0x80acc
   takes case 0 with no input left. At every entry a4 is the kind byte's address, s8 the cursor after it, s9
   what is left after it, R+0xf8 what was left before it, s4 the sign-extended kind byte and a0 that byte
   shifted left by 56; a7 = 10 and a2 = 8 are the two constants of the `% 10` and of the table's bound. *)
Definition rs_pc_D (kd : Z) : Z :=
if kd mod 10 =? 0 then RS_D0 else if kd mod 10 =? 1 then RS_D1 else if kd mod 10 =? 2 then RS_D2
else if kd mod 10 =? 3 then RS_D3 else if kd mod 10 =? 4 then RS_D4 else if kd mod 10 =? 5 then RS_D5
else if kd mod 10 =? 6 then RS_D6 else if kd mod 10 =? 7 then RS_D7 else if kd mod 10 =? 8 then RS_D8
else RS_D9.
Definition rs_L_Dc0 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rl_loc * Z) :=
rs_Rc0 cx ++ rs_Kc cx sh np
++ [(LCell XR 0xb8, Z.of_nat (length ps)); (LCell XR 0xa0, rs_at_of sh ps);
    (LCell XR 0xa8, cnt); (LCell XR 0x88, 1); (LCell XR 0xd0, rs_first ps);
    (LCell XR 0xd8, Z.of_nat (length es))].
Definition rs_L_Dc (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rl_loc * Z) :=
rs_L_Dc0 cx sh np ps cnt es ++ [(LReg 27, e_pp (x_e cx))].
(* Case 9 is reached by `bltu a2,a1` 0x80b18, before the four instructions 0x80b20 .. 0x80b38 that form
   the table's address and shift and sign-extend the kind byte, so a2 holds the table's address and a0
   and s4 the kind byte's two forms only on the nine table entries; on case 9 a2 is still the bound 8. *)
Definition rs_L_D (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (kd : Z) : list (rl_loc * Z) :=
rs_L_Dc cx sh np ps cnt es
++ [(LCell XR 0xf8, Z.of_nat (length r) + 1);
    (LReg 14, rs_cur cx rest r - 1); (LReg 24, rs_cur cx rest r); (LReg 25, Z.of_nat (length r));
    (LReg 17, 10)]
++ (if kd mod 10 =? 9 then [(LReg 12, 8)]
    else [(LReg 12, 0x20e94); (LReg 20, kd - 256 * (kd / 128)); (LReg 10, kd * 2 ^ 56)]).
(* rr is what is left of the input when the turn begins (at C); the kind byte is the first of it and r what
   is left after it, so the pod the turn builds is Model.ent_build rr. *)
Definition rs_cut_D (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (kd : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_D cx sh np ps cnt es rest r kd) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (rs_u8s (zeros 104)) /\
rs_suffix rest rr /\ (kd, r) = Cursor.fuzz_u8 rr /\ 0 <= kd < 256 /\ rr <> [].
(* the same with no input left: the kind byte reads as 0 and the cursor does not move (fuzz.h:37-43) *)
Definition rs_cut_D0E (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_Dc cx sh np ps cnt es ++ [(LCell XR 0xf8, 0); (LReg 25, rs_cur cx rest [])]) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (rs_u8s (zeros 104)).

(* ---------------- G = 0x80d14: case 0 after the digits, the reverse and the odd_ch part ----------------
   t and ch are in scope and r is out of scope again (0x80d10), so the frame's shadow is neither the
   prologue's nor the pod loop's: rs_PG is that state. s4 = &ch, s11 = the second input byte of the head-amp
   key and s9 the cursor; ch holds the key's first part with its NUL. *)
Definition rs_PG : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0xf2; 0xf2; 0xf2; 0xf2;
   0; 0; 0;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf2;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf3; 0xf3; 0xf3].
(* what case 0 reads of the turn's input before G: the kind byte, then c and p (pod.h:224-262); chs is the
   key's first part, the decimal text of c mod 64 or the odd_ch string of c mod 14. *)
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
 ++ [(LCell XR 0xf8, Z.of_nat (length r));
     (LReg 20, e_F (x_e cx) + 0xa0); (LReg 27, pb); (LReg 25, rs_cur cx rest r)]) /\
rs_fsh_at cx W2 mem2 rs_PG /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xa0) (rs_u8s (chs ++ [NUL])) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (chs, pb, r) = rs_g_of rr /\
(length chs <= 21)%nat /\ 0 <= pb < 256.

(* ---------------- J = 0x8165c: the pod is built; the inlined pod_write_ent begins ----------------
   e holds Layout.ent_mem of the pod ent_build made of the turn's input, the cursor is in s9 and what is
   left in R+0xf8, and s4, s5 and s11 hold the three values the cases reload from R+0xb0, R+0x70, R+0x80. *)
Definition rs_cut_J (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (ed : ent) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_L_Dc cx sh np ps cnt es
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 25, rs_cur cx rest r);
     (LCell XR 0xf8, Z.of_nat (length r))]) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (rs_u8s (ent_mem ed)) /\
(ed, r) = ent_build rr /\ ent_wf ed.

(* ---------------- CL = 0x81ccc: the count is reached; the Struct's size word is patched ----------------
   The pod loop wrote cnt pods and e is out of scope again (0x81c98). *)
Definition rs_cut_CL (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 25, rs_cur cx rest r);
     (LCell XR 0xb8, Z.of_nat (length ps)); (LCell XR 0xa0, rs_at_of sh ps);
     (LCell XR 0x88, 1); (LCell XR 0xd0, rs_first ps);
     (LCell XR 0xf8, Z.of_nat (length r))]) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
e_len (x_e cx) = rl_len rest /\
ps = fst (props_loop sh (length ps) (rs_r0 rest)) /\
rs_pod_tie sh ps cnt es rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ Z.of_nat (length es) = cnt.

(* ---------------- the latch 0x81d6c / 0x81d74: one property is written ----------------
   At 0x81d6c the property index and `seen` are still in cells (the pc loads them); at 0x81d74, which the
   shape-7 piece jumps to, they are already in a6 and s9. *)
Definition rs_latch_body (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
sh = rs_sh rest /\ np = rs_np rest /\ 1 <= Z.of_nat (length ps) <= np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (rs_r0 rest).
Definition rs_cut_LATCH (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LCell XR 0xb8, Z.of_nat (length ps) - 1); (LCell XR 0x88, rs_seen ps)]
 ++ rs_cur2 cx rest r).
Definition rs_cut_LATCH7 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LReg 16, Z.of_nat (length ps) - 1); (LReg 25, rs_seen ps)]
 ++ rs_cur2 cx rest r).

(* ---------------- P = 0x81ed4 / P1 = 0x81ed8: every property is written ----------------
   0x81ed4 is entered only when the object has no property (0x8054c) and reloads the shadow address of
   &pp->len from R+0xb0 into s4; 0x81ed8 is the latch's exit, where s4 already holds it. *)
Definition rs_L_P (cx : rs_scx) (rest r : list byte) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 27, e_pp e);
 (LCell XR 0x8, e_F e); (LCell XR 0x10, 0); (LCell XR 0x18, e_pp e); (LCell XR 0x28, e_F e);
 (LCell XR 0x30, e_fl e); (LCell XR 0x68, Z.shiftr (e_pp e + 0x4d14) 3);
 (LCell XR 0x78, e_pp e + 0x4d14); (LCell XR 0x80, e_pp e);
 (LCell XR 0xb0, shadow_addr (e_pp e + 0x4000))] ++ rs_cur2 cx rest r.
Definition rs_Pbody (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
e_len (x_e cx) = rl_len rest /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) = np /\
(ps, r) = props_loop sh (length ps) (rs_r0 rest).
Definition rs_cut_P (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_P cx rest r).
Definition rs_cut_P1 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_P cx rest r ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000))]).

(* ---------------- R = 0x82018 and RT = 0x82094: the corruption (pod.h:441-448) ----------------
   The object is complete (its top size word was patched at 0x81f00 .. 0x81f14), so the block holds the
   image of the record with no corruption yet. The loop writes one byte a turn: a3 = kk is the index,
   a2 = cnt - kk what is left of the count the input byte gave (`andi a3,a3,7` 0x81fe8, decremented at
   0x8206c), a4 = off, a0 is the cursor of the byte reads and a5 what is left of the input. It also leaves
   through `bgeu a1,a6` 0x82028 when off + kk reaches the length, so the bytes written, bs, are the first
   min(cnt, len - off) of the input's. At RT the corruption is done but the corrupt word is NOT yet
   written (`sw a0,0(s10)` 0x820a8 is after the cut), so the block still holds the image with corrupt
   false and the record's own bytes. *)
Definition rs_L_post (cx : rs_scx) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 27, e_pp e); (LReg 25, e_F e);
 (LReg 20, shadow_addr (e_pp e + 0x4000)); (LReg 26, e_pp e + 0x4d18);
 (LCell XR 0x8, e_F e); (LCell XR 0x28, e_F e); (LCell XR 0x30, e_fl e);
 (LCell XR 0x68, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0x78, e_pp e + 0x4d14);
 (LCell XR 0x80, e_pp e)].
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
e_len (x_e cx) = rl_len rest /\
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
e_len (x_e cx) = rl_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
8 <= off /\ off + Z.of_nat (length bs) <= rs_plen sh ps /\ (length bs <= 7)%nat.

(* ---------------- C2 = 0x820c0: the build is done; the second request is in a0 ----------------
   This cut IS role_build_contract's post, at the pc its contract names (hi_c2 role_himg_A): the C2 value
   list, the frame's shadow back to the prologue's, and the block holding Layout.pp_bytes of the record. *)
Definition rs_cut_C2 (cx : rs_scx) (rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rl_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L2 role_himg_A) /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_pp_at cx W2 mem2 (pp_bytes (fst (pod_build rest))) /\
e_len (x_e cx) = rl_len rest.

(* ===================================================================================================
   THE CHECKS (M02): the cuts of role_check_contract's walk, from C3 = 0x820c4 to C4 = 0x82478
   ===================================================================================================
   The first block holds Layout.pp_bytes of the record some input made; the segment copies its first len
   bytes into the second block, runs the parse on them (or on NULL, by bit 0 of the flags byte), scans the
   record's entries for the role key and runs the check its answer selects. From the role cell's store at
   0x820ec on, the frame's shadow is RPgImgA.role_A_shB, and the float state is some fx2 that keeps every
   float register outside fa0, fa3, fa4 and fa5 and has a zero rounding mode. *)
Definition rs_rcell (o : option Role.role) : Z :=
match o with Some ro => Role.role_z ro | None => 0x5a end.
(* the answer the inlined scan computes, and the parse's answer on the block's bytes *)
Definition rs_E0 (rec : pod_rec) : option Role.role * Z := Role.expect_model false rec.
Definition rs_PA (cx : rs_scx) (rec : pod_rec) : option Role.role * Z :=
rl_parse_res (Z.testbit (e_fl (x_e cx)) 0) (buf rec).
(* what every cut of the checks carries *)
Definition rs_chk_base (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rl_fxk [10; 13; 14; 15] fx fx2 /\
rs_fsh_at cx W2 mem2 rs_PB /\ rom_view segs W2 mem2 /\
rs_pp_at cx W2 mem2 (pp_bytes rec) /\
pod_rec_wf rec /\ e_len (x_e cx) = Z.of_nat (length (buf rec)) /\
e_pod (x_e cx) <> 0 /\ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)).
(* the role cell, at every cut after the parse *)
Definition rs_role_at (cx : rs_scx) (rec : pod_rec) (W2 : world segs) (mem2 : word -> option byte)
: Prop :=
val_mem segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x180) 4 (rs_rcell (fst (rs_PA cx rec))).
Definition rs_L_chk (cx : rs_scx) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 18, e_pod e); (LReg 22, e_F e + 0x180);
 (LCell XR 0x8, e_F e); (LCell XR 0x30, e_fl e)].

(* ---------------- E = 0x8212c: the inlined expect_role begins ---------------- *)
Definition rs_cut_E (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 21, e_pp (x_e cx) + 0x4000); (LReg 24, snd (rs_PA cx rec));
                 (LReg 25, e_F (x_e cx)); (LReg 27, e_pp (x_e cx));
                 (LCell XR 0x28, e_F (x_e cx));
                 (LCell XR 0x68, Z.shiftr (e_pp (x_e cx) + 0x4d14) 3);
                 (LCell XR 0x78, e_pp (x_e cx) + 0x4d14); (LCell XR 0x80, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2 /\
Z.testbit (e_fl (x_e cx)) 0 = false /\ corrupt rec = false /\
Role.parse_model (buf rec) = rs_E0 rec.

(* ---------------- O = 0x821bc: the outer scan's head ----------------
   t2 = n_ent, s4 = n_ent - 1, a1 = at, and the five fixed operands of the scan: t3 and s11 = &ent[0],
   t6 = &ent[0] + 4, t4 and t5 = &ent[0] + 8. *)
Definition rs_L_scan (cx : rs_scx) (rec : pod_rec) : list (rl_loc * Z) :=
let e := x_e cx in
rs_L_chk cx ++
[(LReg 24, snd (rs_PA cx rec)); (LReg 1, -1); (LReg 26, 8);
 (LReg 7, Z.of_nat (length (ents rec))); (LReg 20, Z.of_nat (length (ents rec)) - 1);
 (LReg 28, e_pp e + 0x4014); (LReg 27, e_pp e + 0x4014);
 (LReg 31, e_pp e + 0x4018); (LReg 29, e_pp e + 0x401c); (LReg 30, e_pp e + 0x401c);
 (LCell XR 0x28, e_F e); (LCell XR 0x80, e_pp e)].
Definition rs_scan_inv (rec : pod_rec) (j : nat) : Prop :=
(j <= length (ents rec))%nat /\
rs_E0 rec = Role.role_of_pairs Role.expect_value (pairs_by key_of (skipn j (ents rec)) None).
Definition rs_chk_rec (cx : rs_scx) (rec : pod_rec) : Prop :=
corrupt rec = false /\ is_props rec = true /\ params_struct rec = true /\
snd (rs_PA cx rec) = snd (rs_E0 rec) /\ fst (rs_PA cx rec) = fst (rs_E0 rec).
Definition rs_cut_O (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (j : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_scan cx rec ++ [(LReg 11, Z.of_nat j); (LReg 14, 104)]) /\
rs_role_at cx rec W2 mem2 /\ rs_scan_inv rec j /\ rs_chk_rec cx rec.

(* ---------------- I = 0x821e0: pod_next_pair's inner head, scanning from at0 for a key ----------
   a4 = 104 * at0 is fixed and the five operand registers advance by 104 a turn, so the entry the turn
   reads is &ent[m] with m the inner index. *)
Definition rs_cut_I (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_scan cx rec ++
 [(LReg 14, 104 * Z.of_nat at0); (LReg 21, Z.of_nat m); (LReg 25, Z.of_nat m + 1);
  (LReg 16, e_pp (x_e cx) + 0x4014 + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 15, e_pp (x_e cx) + 0x4014 + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 12, e_pp (x_e cx) + 0x4018 + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 13, e_pp (x_e cx) + 0x401c + 104 * (Z.of_nat m - Z.of_nat at0));
  (LReg 17, e_pp (x_e cx) + 0x401c + 104 * (Z.of_nat m - Z.of_nat at0))]) /\
rs_role_at cx rec W2 mem2 /\ rs_scan_inv rec at0 /\ rs_chk_rec cx rec /\
(at0 <= m < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None).

(* ---------------- KM = 0x822a8: entry m is a key and entry m + 1 is its value ----------
   a0 is the key's body address and s5 = m + 1 the value's index; the five operands are spilled around the
   string compare (0x822b8 .. 0x822cc) and reloaded after it. *)
Definition rs_cut_KM (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat) (kb : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_scan cx rec ++
 [(LReg 10, e_pp (x_e cx) + 0x401c + 104 * Z.of_nat m); (LReg 21, Z.of_nat m + 1);
  (LReg 25, Z.of_nat m + 2)]) /\
rs_role_at cx rec W2 mem2 /\ rs_scan_inv rec at0 /\ rs_chk_rec cx rec /\
(at0 <= m)%nat /\ (m + 1 < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None) /\
key_of (nth m (ents rec) (Ent 0 0 [])) = Some kb.

(* ---------------- the two checks the answer selects, and the tail ----------------
   ABS 0x82380: no pair of the record has the role key, so the answer is (None, 0) and check_absent runs.
   MAL 0x823fc: the answer is (None, -1) and check_malformed runs. T 0x82408: the check is done and the
   tail runs the answer and the two refusal codes. *)
Definition rs_cut_ABS (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 24, 0); (LCell XR 0x28, e_F (x_e cx)); (LCell XR 0x80, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2 /\ fst (rs_PA cx rec) = None /\ snd (rs_PA cx rec) = 0.
Definition rs_cut_MAL (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 24, -1); (LReg 25, e_F (x_e cx)); (LReg 27, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2 /\ fst (rs_PA cx rec) = None /\ snd (rs_PA cx rec) = -1.
Definition rs_cut_T (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 24, snd (rs_PA cx rec)); (LReg 25, e_F (x_e cx));
                 (LReg 27, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2.

(* ---------------- C4 = 0x82478: the checks are done ----------------
   This cut IS role_check_contract's post, at the pc its contract names (hi_c4 role_himg_A). *)
Definition rs_cut_C4 (cx : rs_scx) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rl_fxk [10; 13; 14; 15] fx fx2 /\
rl_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L4 role_himg_A) /\
rs_fsh_at cx W2 mem2 rs_PB.

(* ===================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   ===================================================================================================
   One per cut, with the LOOP INDEX as an argument (and never under the inner quantifier), so that the
   latch of a loop can hand the head its next index and the closure is an induction on the index, not a
   circular hypothesis: rs_from_N .. (S i) is what the property loop's latch gives, rs_from_C .. i (S k)
   what the pod loop's latch gives. A piece lemma is `rs_pre cx -> <the continuations of its end cuts> ->
   <the continuation of its start cut>`, so a lane proving one piece takes the other lanes' continuations
   as hypotheses and never sees their proofs. POST is generic. *)
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
SRr segs W2 (cfg_at segs (hi_c2 role_himg_A) regs2 mem2 md2) POST.
(* the cuts of the checks reach their pc at the run's own float state *)
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
Definition rs_from_T : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2 rec, rs_cut_T cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs RS_T regs2 mem2 md2) POST.
Definition rs_from_C4 : Prop :=
forall fx2 ly2 S2 W2 regs2 mem2 md2, rs_cut_C4 cx fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs (hi_c4 role_himg_A) regs2 mem2 md2) POST.
End f.

(* ===================================================================================================
   THE PIECE STATEMENTS, one per walk lane of the two middle segments
   =================================================================================================== *)
(* W3a: C1 -> the object's header (pod.h:384-395): the NULL test (dead), the block's memset, the two
   header reads, the top size word, and the header of this shape. Its start is the segment's own start
   state, which is role_build_contract's premise set. *)
Definition rs_start_M01 (cx : rs_scx) (rest : list byte) : Prop :=
rs_pre cx /\
rl_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L1 role_himg_A) /\
e_len (x_e cx) = rl_len rest /\ rs_in cx rest.
Definition rs_piece_W3a_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_B7 cx POST rest -> rs_from_BO cx POST rest ->
SRr segs (x_W cx) (cfg_at segs (hi_c1 role_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
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
(* W4: one property's selector, its shape-7 body, its key, and the loop's latch. *)
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
rs_from_LATCH cx POST rest i /\ rs_from_LATCH7 cx POST rest i.
(* W5: the Int-7 value pod, the params Struct's header and count, and its close (pod.h:412-438). *)
Definition rs_piece_W5_int_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_LATCH cx POST rest i -> rs_from_SELI cx POST rest i.
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
(* W11a: the second block's fill, the parse, the record's three tests and the two scan loops. *)
Definition rs_start_M02 (cx : rs_scx) (inp : list byte) : Prop :=
rs_pre cx /\
rl_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L3 role_himg_A) /\
e_len (x_e cx) = rl_len inp /\
rs_pp_at cx (x_W cx) (x_memc cx) (pp_bytes (fst (pod_build inp))) /\
e_pod (x_e cx) <> 0 /\ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)) /\
YK0o.frm_zero (@fp_csr fx).
Definition rs_piece_W11a_head_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_E cx POST -> rs_from_ABS cx POST -> rs_from_MAL cx POST ->
rs_from_T cx POST ->
SRr segs (x_W cx) (cfg_at segs (hi_c3 role_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
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
(* W11b: the key compare, the value's two readers, the three checks and the tail. *)
Definition rs_piece_W11b_key_stmt : Prop :=
forall cx POST inp at0 m,
rs_start_M02 cx inp -> rs_from_O cx POST (S (S m)) -> rs_from_ABS cx POST ->
rs_from_MAL cx POST -> rs_from_T cx POST ->
rs_from_KM cx POST at0 m.
Definition rs_piece_W11b_checks_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_T cx POST ->
rs_from_ABS cx POST /\ rs_from_MAL cx POST.
Definition rs_piece_W11b_tail_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_C4 cx POST -> rs_from_T cx POST.

End d.
End c.
End b.
