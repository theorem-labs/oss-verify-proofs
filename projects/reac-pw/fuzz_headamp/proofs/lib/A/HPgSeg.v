(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSeg.v at a6c58f5ab69 (its lines 1-221, 222-682, 820-914 and 942-1037: the cut-state machinery, the cut states of the build and their continuations, and the 21 build piece statements) for reac-pw/fuzz_headamp image A; module paths changed, the rs_ prefix renamed to hs_, every pc, register and real-frame cell moved to headamp's twin, the input cursor kept in s11 and pp in R+0xf0 where role keeps them in R+0xc8 and s11, role's flags byte replaced by headamp's cap and null flag; role's check half (lines 684-818, 915-939, 1038-1077) is not taken. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): THE CUT STATES of the
   build segment M01 of LLVMFuzzerTestOneInput (0x80bc0, 12924 bytes, 3231 instructions) and the statement of
   every piece that segment is split into. Statement text only: proves no function (kind: segment lemma).

   WHAT THIS FILE IS FOR. M01 runs from C1 = 0x80e94 (the malloc of the first block returned) to C2 = 0x82e60 (the
   `jal` of the second block's malloc, not executed); its contract is HPgCSpec.headamp_build_contract at image A's
   record HPgImgA.headamp_himg_A. M01 is cut again at the heads and the joins of its loops and at the boundaries of
   its pieces, and every piece is stated here, so that the pieces are proved in parallel and each proof sees only
   the STATEMENTS of the pieces its continuation goes to. The builder is the one fuzz_role's image A runs (the same
   pod.h, inlined the same way): each cut below is the twin of a cut of fuzz_role's walk, and its facts are those
   facts moved to the registers and real-frame cells headamp's code keeps them in.
   The first part of the file (the record hs_scx, hs_at, hs_mid, hs_pre, hs_core, hs_pp_at, hs_fsh_at, hs_at_cx) is
   the machinery every segment's cuts are stated with; the cuts of the later segments are stated over it in their
   own file.

   HOW A CUT IS STATED, AND WHY NOT AS A SYMBOLIC STATE. A cut is a SEMANTIC predicate over
   (ly, S, W, regs, mem, md) at the cut's pc: the caller's journal from the segment's start, the frame's shadow
   bytes, the first block's image, the input bytes left, and a list of (location, value) facts over the run's
   quantities (HPgBase.hd_at: a register, or the 8-byte cell at an offset of a base). A symbolic state can only be
   written down after the piece before it has been run, which would serialise the pieces; a semantic cut lets each
   piece rebuild its own symbolic state from the cut, as the released walks rebuild the entry one.
   A cut states only POSITIVE facts. What a call leaves alone is not restated: the journal's own clauses and each
   callee's write-set post carry it between cuts.

   WHERE A VALUE LIVES. Image A keeps the harness's values in registers and in 8-byte cells of the real frame at
   R + off, R = (S - 0x1e0) & -32 being the 32-aligned base the prologue puts in s1 and sp (0x80c0c, 0x80c10) and S
   the entry sp (s0, 0x80c08). The locals whose address is taken live in the frame for locals F, a side-stack frame
   of class 4 that the prologue takes (0x80c38 `addi a0,zero,0x280`, 0x80c3c the call, s6 = s10 = F): t[96] at
   F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at F+0xf0, res at F+0x180 and x at F+0x1a0. s3 = (F >> 3)
   + K is the frame's shadow base and s7 = K the runtime's shadow offset. sp = R from 0x80c10 to the epilogue.
   Through the whole build the first block's address is in R+0xf0 (0x80e9c), the cap in R+0x28 (from 0x8122c) and
   the null flag in R+0x40 (0x80e24 / 0x80e3c); the input cursor is in s11 outside the pod loop and in s9 inside it,
   and what is left of the input is in R+0x118.

   THE MODEL. The quantities a cut names are the shared model's (lib/Pod): the record built so far is a
   Model.pb_cut (the shape, the properties written and, inside a params Struct, the pods written), the first block
   holds Layout.pc_image of it, what is left of the input is a suffix of the bytes after the two harness bytes, and
   the cursor that names it is src + |rest| - |r|. At the end of the build the block holds Layout.pp_bytes of the
   record Model.pod_build makes. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the pcs of the cuts ============================================
   Each is the address of the first instruction of the piece that starts there; the two segment cuts are
   HPgImgA.headamp_himg_A's hi_c1 and hi_c2. *)
Definition HS_B7 : Z := 0x80fec.         (* the shape-7 object header, from `bne a3,a2` 0x80fe8 *)
Definition HS_BO : Z := 0x81060.         (* the Object header (shape <> 7) *)
Definition HS_PH : Z := 0x81224.         (* `sd a6,0x30(s1)`: the property loop's preheader *)
Definition HS_N : Z := 0x812f4.          (* `sd a7,0xd8(s1)`: the property loop's head *)
Definition HS_SEL7 : Z := 0x81358.       (* the shape-7 Int pod of one property *)
Definition HS_SELK : Z := 0x81514.       (* a property's key, its flags and the `first` test *)
Definition HS_SELI : Z := 0x82808.       (* the Int-7 value pod *)
Definition HS_SELS : Z := 0x8165c.       (* `mv s9,s11`: the params Struct's header and its pod count *)
Definition HS_C : Z := 0x817a0.          (* `sd a1,0xf8(s1)`: the pod loop's head *)
Definition HS_D0 : Z := 0x81860.         (* ent_build case 0 (the head-amp key), with input left *)
Definition HS_D0E : Z := 0x818cc.        (* ent_build case 0 with no input left *)
Definition HS_D1 : Z := 0x81cf8.
Definition HS_D2 : Z := 0x81bd4.
Definition HS_D3 : Z := 0x81c3c.
Definition HS_D4 : Z := 0x81b88.
Definition HS_D5 : Z := 0x81d40.
Definition HS_D6 : Z := 0x81dc8.
Definition HS_D7 : Z := 0x81c84.
Definition HS_D8 : Z := 0x81e18.
Definition HS_D9 : Z := 0x81ea4.
Definition HS_G : Z := 0x81a34.          (* case 0 after the digits, the reverse and the odd_ch part *)
Definition HS_J : Z := 0x8237c.          (* the pod is built: the inlined pod_write_ent begins *)
Definition HS_CL : Z := 0x82a14.         (* the params Struct's size word is about to be patched *)
Definition HS_LATCH : Z := 0x82ac0.      (* the property loop's latch *)
Definition HS_LATCH7 : Z := 0x82ac8.     (* its second entry, from the shape-7 piece *)
Definition HS_P : Z := 0x82c68.          (* the builder's end, entered with no property *)
Definition HS_P1 : Z := 0x82c6c.         (* its second entry, from the latch *)
Definition HS_R : Z := 0x82da4.          (* the corruption loop's head *)
Definition HS_RT : Z := 0x82e2c.         (* after the corruption: corrupt := 1, then the second request *)

(* The byte values of the frame's shadow at the states the build passes through. P0 is the prologue's pattern
   (HPgImgA.headamp_A_shA, 80 granules); PJ opens e's 13 granules 0x1e .. 0x2a (the pod loop's stores 0x817a4 ..
   0x817d4; closed again at 0x82578 / 0x829e0). *)
Definition hs_P0 : list Z := headamp_A_shA.
Definition hs_PJ : list Z := firstn 30 headamp_A_shA ++ repeat 0 13 ++ skipn 43 headamp_A_shA.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* a list of (location, value) facts, through HPgBase.hd_at: a register holds the 64-bit word of v, a cell holds
   its 8 little-endian bytes *)
Definition hs_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
(L : list (hd_loc * Z)) : Prop :=
Forall (fun f => hd_at segs H mem regs e (fst f) (snd f)) L.

(* ========================= what every cut INSIDE a segment carries =========================
   The segment's own journal from its start (with the segment's event count: no middle segment allocates), sp / gp
   / tp as at the start, the frames, the blocks, the I/O state and the meter as at the start, and every byte outside
   the callees' stack [R - T_SEG_STK, R) and outside the ranges the segment writes as at the start. These are
   exactly the clauses of HPgCSpec.hd_seg_post without its pc, its float state and its result, so the cut at a
   segment's last pc IS that segment's post. *)
Definition hs_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
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
   (HPgBase.hd_env: S, R, F, the four blocks, len, cap, the null flag, rc, the input cursor and what is left of it),
   the position of the frame for locals among the side stack's frames of its class, and the read-only range. A cut
   inside the segment is a predicate over this record and the state at the cut. *)
Record hs_scx := HSCx {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z);
x_ly : alayout; x_S : astate; x_W0 : world segs; x_mem0 : word -> option byte; x_md0 : Model;
x_own : list (Z * Z); x_k : Z; x_regs : bvmap 5 word;
x_lyc : alayout; x_Sc : astate; x_W : world segs; x_memc : word -> option byte; x_mdc : Model;
x_RLO : Z; x_RHI : Z; x_e : hd_env; x_pos : Z }.

(* what a segment's contract asks at its start (HPgCSpec.hd_seg_pre at image A's record), with the frame's shadow
   bytes sh the contract names: hi_shA headamp_himg_A for M01, M02 and M03, hi_shB headamp_himg_A for M04a / M04b *)
Definition hs_pre (cx : hs_scx) (sh : list Z) : Prop :=
hd_seg_pre segs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
(x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)
headamp_himg_A sh (x_RLO cx) (x_RHI cx) (x_e cx) (x_pos cx).

(* the journal-and-frame part of a cut inside the segment, with the segment's write set E *)
Definition hs_core (cx : hs_scx) (E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
hs_mid (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
(x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) E ly2 S2 W2 regs2 mem2 md2.

(* the first block's bytes at a cut *)
Definition hs_pp_at (cx : hs_scx) (W2 : world segs) (mem2 : word -> option byte) (l : list byte) : Prop :=
garr8 segs (mrestrict (w_H W2) mem2) (e_pp (x_e cx)) (hd_zbytes l).
(* the frame's shadow bytes at a cut *)
Definition hs_fsh_at (cx : hs_scx) (W2 : world segs) (mem2 : word -> option byte) (pat : list Z) : Prop :=
hd_fsh segs (w_H W2) mem2 (e_F (x_e cx)) pat.
(* the values at a cut's locations *)
Definition hs_at_cx (cx : hs_scx) (W2 : world segs) (mem2 : word -> option byte) (regs2 : bvmap 5 word)
(L : list (hd_loc * Z)) : Prop :=
hs_at (w_H W2) mem2 regs2 (x_e cx) L.

(* M01's write set, as headamp_build_contract states it: the image's range list hi_w1 (the frame's objects
   [F+0x20, F+0x158), their 80 shadow bytes and the real-frame cells [R, R+0x160)) and the first block *)
Definition hs_E1 (cx : hs_scx) : Z -> Prop :=
fun a => hd_inw (x_e cx) (hi_w1 headamp_himg_A) a \/
e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE.

(* What is left of the input the build reads: a suffix of the bytes after the two harness bytes, and the cursor
   that names it. e_src is where those bytes lie and e_left how many there are. *)
Definition hs_suffix (rest r : list byte) : Prop := exists j, (j <= length rest)%nat /\ r = skipn j rest.
Definition hs_cur (cx : hs_scx) (rest r : list byte) : Z :=
e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r).
(* the input bytes, as headamp_build_contract gives them: at e_src, outside the callees' stack, the ranges the
   segment writes and the first block *)
Definition hs_in (cx : hs_scx) (rest : list byte) : Prop :=
e_left (x_e cx) = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_src (x_e cx)) (hd_zbytes rest) /\
range_addressable (aview segs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)) /\
(0 < e_left (x_e cx) -> shadow_hull_vis (aview segs (w_H (x_W cx)) (x_memc cx)) (e_src (x_e cx)) (e_left (x_e cx))) /\
amem_range (e_src (x_e cx)) (e_left (x_e cx)) /\
0 < e_src (x_e cx) /\ e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 63 /\
(forall a, e_src (x_e cx) <= a < e_src (x_e cx) + e_left (x_e cx) ->
 ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) /\ ~ hd_inw (x_e cx) (hi_w1 headamp_himg_A) a /\
 ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)).

(* ===================================================================================================
   THE BUILD (M01): the cuts of headamp_build_contract's walk, from C1 = 0x80e94 to C2 = 0x82e60
   ===================================================================================================
   The builder writes one object into the first block. Its state at a cut is the record so far (a
   Model.pb_cut: the shape sh, the properties ps written and, inside a params Struct, the pods es written),
   what is left of the input, and the loop counters; the block holds Layout.pc_image of that state and the
   R-relative cells hold the loop's constants and counters. *)

(* The constants the preheader (0x81224 .. 0x812f0) puts in R-relative cells and no piece writes again, with the
   six cells written before it (R+0xf0 = the first block at 0x80e9c, R+0xb0 = np and R+0xb8 = sh at the two header
   reads, R+0xd0 at 0x80f3c, R+0x108 at 0x80f58, and R+0x40 = the null flag before C1 at 0x80e24 / 0x80e3c):
   0x15555556 is the `% 12u` multiplier (pod.h:354, 0x812b8), 0x10003 is SPA_PROP_VOLUME (0x812c0), 0x80001 is
   SPA_PROP_params (0x812c8), -0x4001 and -0x3ffd are the two capacity bounds (0x812ac, 0x80f58), R+0x30 and
   R+0x38 are the top size word's offset (0: the block's length before the header) and its address; the preheader
   also writes R+0x28 = the cap (0x8122c) and R+0x20, R+0x60 = the frame for locals (0x81230, 0x8124c). *)
Definition hs_Kc (cx : hs_scx) (sh np : Z) : list (hd_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x18, 0x15555556); (LCell XR 0x20, e_F e); (LCell XR 0x30, 0); (LCell XR 0x38, e_pp e);
 (LCell XR 0x48, e_F e + 0x100); (LCell XR 0x28, e_cap e); (LCell XR 0x40, e_null e);
 (LCell XR 0x50, 0x10003); (LCell XR 0x58, e_pp e + 0x4010);
 (LCell XR 0x70, 0x80001); (LCell XR 0x78, e_pp e + 0x400c);
 (LCell XR 0x80, e_F e + 0xa0); (LCell XR 0x88, e_pp e + 0x4014);
 (LCell XR 0x90, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0x98, e_pp e + 0x4000);
 (LCell XR 0xa0, e_pp e + 0x4d14); (LCell XR 0x60, e_F e); (LCell XR 0xf0, e_pp e);
 (LCell XR 0xb0, np); (LCell XR 0xb8, sh);
 (LCell XR 0xd0, shadow_addr (e_pp e + 0x4000)); (LCell XR 0xe0, e_F e + 0xf8);
 (LCell XR 0x100, -0x4001); (LCell XR 0x108, -0x3ffd); (LCell XR 0x110, e_F e + 0xf0)].

(* the `v / 10` multiplier of the digit loop (pod.h:240-241), in s2 from 0x812b0 / 0x812d4 *)
Definition HS_MULT10 : Z := 0xcccccccd * 2 ^ 32.

(* the registers both loops keep: s0 = S, s1 = R, s3 = the frame's shadow base, s7 = the runtime's shadow offset,
   s2 = the multiplier, s6 = &r, s10 = &t, s5 = &pp->len; inside the pod loop s11 is the first block too (it is
   reloaded from R+0xf0 at 0x81660 and after each case) *)
Definition hs_Rc0 (cx : hs_scx) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 18, HS_MULT10); (LReg 22, e_F e + 0xe0); (LReg 26, e_F e + 0x20);
 (LReg 21, e_pp e + 0x4000)].
Definition hs_Rc (cx : hs_scx) : list (hd_loc * Z) := hs_Rc0 cx ++ [(LReg 27, e_pp (x_e cx))].

(* the cursor outside the pod loop: s11 holds in.p and R+0x118 in.n *)
Definition hs_cur2 (cx : hs_scx) (rest r : list byte) : list (hd_loc * Z) :=
[(LReg 27, hs_cur cx rest r); (LCell XR 0x118, Z.of_nat (length r))].

(* the two header reads of pod_build (pod.h:385-386): the shape and the property count *)
Definition hs_sh (rest : list byte) : Z := fst (Cursor.fuzz_u8 rest) mod 8.
Definition hs_np (rest : list byte) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))) mod 4.
Definition hs_r0 (rest : list byte) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))).
(* the record the loop may have built: what Model.pod_rec_wf asks of its parts *)
Definition hs_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2 ^ 32 /\ pval_wf (snd kv)) ps /\
Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.
Definition hs_plen (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))).
Definition hs_seen (ps : list (Z * pval)) : Z := Z.b2z (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps).
Definition hs_first (ps : list (Z * pval)) : Z :=
Z.b2z (negb (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps)).
(* the offset of an open params Struct's size word: the property's key and flags are already written *)
Definition hs_at_of (sh : Z) (ps : list (Z * pval)) : Z := hs_plen sh ps + 8.

(* ---------------- the build's first own cuts: 0x80fec (shape 7) and 0x81060 (any other shape) ----------
   The block was filled with zeros (0x80ea8), the two header reads were made, and the top size word was
   written as four zero bytes with len := 4 (0x80f98 .. 0x80fc0). a0 is that length, a1 = len - 0x3ffd is the
   capacity test's left side, a5 = pp + 0 and a6 = 0 are the top word's address and offset, s4 = 0x5000 is the
   constant the preheader turns into &pp->n_ent, and s8 is the cap, which the preheader spills to R+0x28. *)
Definition hs_L_hdr (cx : hs_scx) (sh np : Z) (rest r : list byte) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 10, 4); (LReg 11, 4 - 0x3ffd); (LReg 15, e_pp e); (LReg 16, 0); (LReg 20, 0x5000);
 (LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 22, e_F e); (LReg 26, e_F e); (LReg 24, e_cap e);
 (LCell XR 0x40, e_null e); (LCell XR 0xf0, e_pp e); (LCell XR 0xb0, np); (LCell XR 0xb8, sh);
 (LCell XR 0xd0, shadow_addr (e_pp e + 0x4000)); (LCell XR 0x108, -0x3ffd)] ++ hs_cur2 cx rest r.
(* the block's bytes before the object's header: the top size word only *)
Definition hs_img_hdr : list byte := pp_image (le32 0) false false false [] false.
Definition hs_cut_hdr (cx : hs_scx) (rest r : list byte) (sh np : Z)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_hdr cx sh np rest r) /\
hs_fsh_at cx W2 mem2 hs_P0 /\ hs_pp_at cx W2 mem2 hs_img_hdr /\
hs_in cx rest /\ hs_suffix rest r /\
sh = hs_sh rest /\ np = hs_np rest /\ r = hs_r0 rest.
Definition hs_cut_B7 (cx : hs_scx) (rest r : list byte) (np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_cut_hdr cx rest r 7 np ly2 S2 W2 regs2 mem2 md2.
Definition hs_cut_BO (cx : hs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_cut_hdr cx rest r sh np ly2 S2 W2 regs2 mem2 md2 /\ sh <> 7.

(* ---------------- PH = 0x81224: the header is written, the preheader is about to run ----------------
   The block holds the image of the empty record of this shape (its header bytes and, for an Object,
   is_props); a6 and a5 still hold the top word's offset and address, which the preheader spills. *)
Definition hs_L_PH (cx : hs_scx) (sh np : Z) (rest r : list byte) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 15, e_pp e); (LReg 16, 0); (LReg 20, 0x5000);
 (LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 22, e_F e); (LReg 26, e_F e); (LReg 24, e_cap e);
 (LCell XR 0x40, e_null e); (LCell XR 0xf0, e_pp e); (LCell XR 0xb0, np); (LCell XR 0xb8, sh);
 (LCell XR 0xd0, shadow_addr (e_pp e + 0x4000)); (LCell XR 0x108, -0x3ffd)] ++ hs_cur2 cx rest r.
Definition hs_cut_PH (cx : hs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_PH cx sh np rest r) /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh [] None)) /\
hs_in cx rest /\ hs_suffix rest r /\
sh = hs_sh rest /\ np = hs_np rest /\ r = hs_r0 rest.

(* ---------------- N = 0x812f4: the property loop's head, |ps| properties written ----------------
   The property index is in a7 and `seen` in s9. R+0xd8 is NOT part of the state: the pc writes it. *)
Definition hs_L_N (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (hd_loc * Z) :=
hs_Rc0 cx ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
              (LReg 17, Z.of_nat (length ps)); (LReg 25, hs_seen ps)]
++ hs_Kc cx sh np ++ hs_cur2 cx rest r.
Definition hs_cut_N (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_N cx sh np ps rest r) /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
sh = hs_sh rest /\ np = hs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (hs_r0 rest).

(* ---------------- the two ends of one property's selector (pod.h:399-423) ----------------
   SEL7 0x81358 (shape 7: the property is an Int pod with no key) and SELK 0x81514 (any other shape: the
   key, its flags and the `first` test). a0 is pp->len at the cut and a2 = len - 0x3ffd its capacity test's
   left side; a1 is the selector byte at SELK. *)
Definition hs_L_SEL (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (hd_loc * Z) :=
hs_Rc0 cx ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
              (LReg 10, hs_plen sh ps); (LReg 12, hs_plen sh ps - 0x3ffd); (LReg 25, hs_seen ps)]
++ hs_Kc cx sh np ++ [(LCell XR 0xd8, Z.of_nat (length ps))] ++ hs_cur2 cx rest r.
(* what every cut of one property's body shares with N, with the tie of ps to the input: the properties
   written are the ones Model.props_loop makes of the bytes after the two header reads *)
Definition hs_prop_base (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_fsh_at cx W2 mem2 hs_P0 /\ hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
ps = fst (props_loop sh (length ps) (hs_r0 rest)) /\
sh = hs_sh rest /\ np = hs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3.
Definition hs_cut_SEL7 (cx : hs_scx) (np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_prop_base cx 7 np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_SEL cx 7 np ps rest r) /\
hs_pp_at cx W2 mem2 (pc_image (PbCut 7 ps None)) /\
r = snd (Cursor.fuzz_u8 (snd (props_loop 7 (length ps) (hs_r0 rest)))).
Definition hs_cut_SELK (cx : hs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_SEL cx sh np ps rest r ++ [(LReg 11, sel)]) /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
sh <> 7 /\ 0 <= sel < 256 /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hs_r0 rest))).

(* ---------------- the two ends of the key piece (pod.h:407-423) ----------------
   SELI 0x82808 writes the Int value pod of a property whose value is an Int (the volume property, and a
   params property whose selector has bit 4 set), SELS 0x8165c opens a params Struct. On both, the key
   word and the flags word are already written, so the block's bytes are the record's image with those
   eight bytes appended; `at` (R+0xc0) is the open Struct's size word offset and a0 = at - 0x3ffd is the
   capacity test's left side (0x81648 .. 0x81650). The cells R+0xa8 (seen') and R+0xe8 (first) are written on
   both arms (0x81618, 0x81638): seen and 0 on the volume arm, 1 and `first` on the params arm. s4 is still the
   shadow address of &pp->len, which both pieces read before they reload it (0x82858, 0x816b0). *)
Definition hs_img_key (sh : Z) (ps : list (Z * pval)) (kk : Z) : list byte :=
pp_image (pc_buf (PbCut sh ps None) ++ le32 kk ++ le32 0)
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
(* the key the selector chooses (Model.prop_step): the volume property, else the params property *)
Definition hs_key_of (sel : Z) : Z := if sel mod 4 =? 0 then 0x10003 else 0x80001.
Definition hs_L_KEY (cx : hs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (hd_loc * Z) :=
hs_Rc0 cx ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 10, hs_at_of sh ps - 0x3ffd)]
++ hs_Kc cx sh np
++ [(LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps);
    (LCell XR 0xa8, if sel mod 4 =? 0 then hs_seen ps else 1);
    (LCell XR 0xe8, if sel mod 4 =? 0 then 0 else hs_first ps)]
++ hs_cur2 cx rest r.
Definition hs_cut_SELI (cx : hs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_KEY cx sh np sel ps rest r) /\
hs_pp_at cx W2 mem2 (hs_img_key sh ps (hs_key_of sel)) /\ sh <> 7 /\ 0 <= sel < 256 /\
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hs_r0 rest))).
Definition hs_cut_SELS (cx : hs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_KEY cx sh np sel ps rest r) /\
hs_pp_at cx W2 mem2 (hs_img_key sh ps 0x80001) /\ sh <> 7 /\ 0 <= sel < 256 /\
sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hs_r0 rest))).

(* ---------------- C = 0x817a0: the pod loop's head, |es| pods written ----------------
   The cursor moved into s9 at 0x8165c and s11 holds the first block from 0x81660; the pod index is in a1 (the pc
   spills it to R+0xf8), the count in R+0xc8, `at` in R+0xc0, `first` in R+0xe8 and seen' = 1 in R+0xa8. The
   frame's shadow is still the prologue's: the pc at 0x817a4 opens e's granules. *)
Definition hs_L_pod (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (rest r : list byte)
: list (hd_loc * Z) :=
hs_Rc cx ++ hs_Kc cx sh np
++ [(LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps);
    (LCell XR 0xc8, cnt); (LCell XR 0xa8, 1); (LCell XR 0xe8, hs_first ps);
    (LCell XR 0x118, Z.of_nat (length r)); (LReg 25, hs_cur cx rest r)].
(* What every cut inside the pod loop shares, with the tie of the count and the pods to the input: the
   selector picked the params Struct, the count byte gave cnt = c mod 33 (pod.h:425) and the pods written
   are the ones Model.ents_loop makes of what follows it, leaving rr at the turn's start. *)
Definition hs_pod_tie (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent) (rest rr : list byte)
: Prop :=
exists sel c r1 r2,
(sel, r1) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hs_r0 rest))) /\
(c, r2) = Cursor.fuzz_u8 r1 /\ cnt = c mod 33 /\ sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
ents_loop (length es) r2 = (es, rr).
Definition hs_pod_base (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_in cx rest /\ hs_suffix rest r /\ hs_suffix rest rr /\ hs_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
ps = fst (props_loop sh (length ps) (hs_r0 rest)) /\
hs_pod_tie sh ps cnt es rest rr /\
sh = hs_sh rest /\ np = hs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ (length es < 32)%nat /\ Z.of_nat (length es) < cnt.
Definition hs_cut_C (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base cx sh np ps cnt es rest r r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_pod cx sh np ps cnt rest r ++ [(LReg 11, Z.of_nat (length es))]) /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))).

(* ---------------- the eleven entries of ent_build's switch (pod.h:265-379) ----------------
   The dispatch (0x817a4 .. 0x8185c) opens e's granules, fills e with zeros, reads the kind byte and jumps
   through the nine relative entries at .rodata 0x20e9c; `bltu a2,a1` 0x81838 takes case 9 and `beqz` 0x817ec
   takes case 0 with no input left. At every entry a4 is the kind byte's address, s8 the cursor after it, s9
   what is left after it, R+0x118 what was left before it and a7 = 10, the constant of the `% 10`; on the nine
   table entries a2 is the table's address, s4 the sign-extended kind byte and a0 that byte shifted left by 56,
   and on case 9 a2 is still the table's bound 8. *)
Definition hs_pc_D (kd : Z) : Z :=
if kd mod 10 =? 0 then HS_D0 else if kd mod 10 =? 1 then HS_D1 else if kd mod 10 =? 2 then HS_D2
else if kd mod 10 =? 3 then HS_D3 else if kd mod 10 =? 4 then HS_D4 else if kd mod 10 =? 5 then HS_D5
else if kd mod 10 =? 6 then HS_D6 else if kd mod 10 =? 7 then HS_D7 else if kd mod 10 =? 8 then HS_D8
else HS_D9.
Definition hs_L_Dc0 (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (hd_loc * Z) :=
hs_Rc0 cx ++ hs_Kc cx sh np
++ [(LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps);
    (LCell XR 0xc8, cnt); (LCell XR 0xa8, 1); (LCell XR 0xe8, hs_first ps);
    (LCell XR 0xf8, Z.of_nat (length es))].
Definition hs_L_Dc (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (hd_loc * Z) :=
hs_L_Dc0 cx sh np ps cnt es ++ [(LReg 27, e_pp (x_e cx))].
(* Case 9 is reached by `bltu a2,a1` 0x81838, before the four instructions 0x81840 .. 0x81858 that form
   the table's address and shift and sign-extend the kind byte, so a2 holds the table's address and a0
   and s4 the kind byte's two forms only on the nine table entries; on case 9 a2 is still the bound 8. *)
Definition hs_L_D (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (kd : Z) : list (hd_loc * Z) :=
hs_L_Dc cx sh np ps cnt es
++ [(LCell XR 0x118, Z.of_nat (length r) + 1);
    (LReg 14, hs_cur cx rest r - 1); (LReg 24, hs_cur cx rest r); (LReg 25, Z.of_nat (length r));
    (LReg 17, 10)]
++ (if kd mod 10 =? 9 then [(LReg 12, 8)]
    else [(LReg 12, 0x20e9c); (LReg 20, kd - 256 * (kd / 128)); (LReg 10, kd * 2 ^ 56)]).
(* rr is what is left of the input when the turn begins (at C); the kind byte is the first of it and r what
   is left after it, so the pod the turn builds is Model.ent_build rr. *)
Definition hs_cut_D (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (kd : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_D cx sh np ps cnt es rest r kd) /\
hs_fsh_at cx W2 mem2 hs_PJ /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)) /\
hs_suffix rest rr /\ (kd, r) = Cursor.fuzz_u8 rr /\ 0 <= kd < 256 /\ rr <> [].
(* the same with no input left: the kind byte reads as 0 and the cursor does not move (fuzz.h:37-43) *)
Definition hs_cut_D0E (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_L_Dc cx sh np ps cnt es ++ [(LCell XR 0x118, 0); (LReg 25, hs_cur cx rest [])]) /\
hs_fsh_at cx W2 mem2 hs_PJ /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)).

(* ---------------- G = 0x81a34: case 0 after the digits, the reverse and the odd_ch part ----------------
   t and ch are in scope and r is out of scope again (0x81a30), so the frame's shadow is neither the
   prologue's nor the pod loop's: hs_PG is that state (granules 0x00 .. 0x2f as listed, the rest the prologue's).
   s4 = &ch, s11 = the second input byte of the head-amp key and s9 the cursor; ch holds the key's first part with
   its NUL. *)
Definition hs_PG : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0xf2; 0xf2; 0xf2; 0xf2;
   0; 0; 0;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf2;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2] ++ skipn 48 headamp_A_shA.
(* what case 0 reads of the turn's input before G: the kind byte, then c and p (pod.h:224-262); chs is the
   key's first part, the decimal text of c mod 64 or the odd_ch string of c mod 14. *)
Definition hs_g_of (rr : list byte) : list byte * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Definition hs_cut_G (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (pb : Z) (chs : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_L_Dc0 cx sh np ps cnt es
 ++ [(LCell XR 0x118, Z.of_nat (length r));
     (LReg 20, e_F (x_e cx) + 0xa0); (LReg 27, pb); (LReg 25, hs_cur cx rest r)]) /\
hs_fsh_at cx W2 mem2 hs_PG /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xa0) (hd_zbytes (chs ++ [NUL])) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (chs, pb, r) = hs_g_of rr /\
(length chs <= 21)%nat /\ 0 <= pb < 256.

(* ---------------- J = 0x8237c: the pod is built; the inlined pod_write_ent begins ----------------
   e holds Layout.ent_mem of the pod ent_build made of the turn's input, the cursor is in s9 and what is
   left in R+0x118, and s4, s5 and s11 hold the three values the cases reload from R+0xd0, R+0x98, R+0xf0. *)
Definition hs_cut_J (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (ed : ent) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_Rc cx ++ hs_L_Dc cx sh np ps cnt es
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 25, hs_cur cx rest r);
     (LCell XR 0x118, Z.of_nat (length r))]) /\
hs_fsh_at cx W2 mem2 hs_PJ /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xf0) (hd_zbytes (ent_mem ed)) /\
(ed, r) = ent_build rr /\ ent_wf ed.

(* ---------------- CL = 0x82a14: the count is reached; the Struct's size word is patched ----------------
   The pod loop wrote cnt pods and e is out of scope again (0x82578 .. 0x825ac when the count is reached,
   0x829e0 .. on the capacity break). *)
Definition hs_cut_CL (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_Rc cx ++ hs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 25, hs_cur cx rest r);
     (LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps);
     (LCell XR 0xa8, 1); (LCell XR 0xe8, hs_first ps);
     (LCell XR 0x118, Z.of_nat (length r))]) /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
ps = fst (props_loop sh (length ps) (hs_r0 rest)) /\
hs_pod_tie sh ps cnt es rest r /\
sh = hs_sh rest /\ np = hs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ Z.of_nat (length es) = cnt.

(* ---------------- the latch 0x82ac0 / 0x82ac8: one property is written ----------------
   At 0x82ac0 the property index and `seen` are still in cells (the pc loads them); at 0x82ac8, which the
   shape-7 piece jumps to, they are already in a7 and s9. *)
Definition hs_latch_body (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
sh = hs_sh rest /\ np = hs_np rest /\ 1 <= Z.of_nat (length ps) <= np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (hs_r0 rest).
Definition hs_cut_LATCH (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_Rc0 cx ++ hs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LCell XR 0xd8, Z.of_nat (length ps) - 1); (LCell XR 0xa8, hs_seen ps)]
 ++ hs_cur2 cx rest r).
Definition hs_cut_LATCH7 (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_Rc0 cx ++ hs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LReg 17, Z.of_nat (length ps) - 1); (LReg 25, hs_seen ps)]
 ++ hs_cur2 cx rest r).

(* ---------------- P = 0x82c68 / P1 = 0x82c6c: every property is written ----------------
   0x82c68 is entered only when the object has no property (0x81258) and reloads the shadow address of
   &pp->len from R+0xd0 into s4; 0x82c6c is the latch's exit, where s4 already holds it. *)
Definition hs_L_P (cx : hs_scx) (rest r : list byte) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000);
 (LCell XR 0x20, e_F e); (LCell XR 0x30, 0); (LCell XR 0x38, e_pp e); (LCell XR 0x28, e_cap e);
 (LCell XR 0x40, e_null e); (LCell XR 0x90, Z.shiftr (e_pp e + 0x4d14) 3);
 (LCell XR 0xa0, e_pp e + 0x4d14); (LCell XR 0x60, e_F e); (LCell XR 0xf0, e_pp e);
 (LCell XR 0xd0, shadow_addr (e_pp e + 0x4000))] ++ hs_cur2 cx rest r.
Definition hs_Pbody (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
sh = hs_sh rest /\ np = hs_np rest /\ Z.of_nat (length ps) = np /\
(ps, r) = props_loop sh (length ps) (hs_r0 rest).
Definition hs_cut_P (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_P cx rest r).
Definition hs_cut_P1 (cx : hs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_L_P cx rest r ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000))]).

(* ---------------- R = 0x82da4 and RT = 0x82e2c: the corruption (pod.h:441-448) ----------------
   The object is complete (its top size word was patched at 0x82cc0 .. 0x82ccc), so the block holds the
   image of the record with no corruption yet. The loop writes one byte a turn: a3 = kk is the index,
   a2 = cnt - kk what is left of the count the input byte gave (`andi a2,a2,7` 0x82d78, decremented at
   0x82e04), a4 = off, a0 is the cursor of the byte reads and a5 what is left of the input. It also leaves
   through `bgeu a1,a6` 0x82db8 when off + kk reaches the length, so the bytes written, bs, are the first
   min(cnt, len - off) of the input's. At RT the corruption is done but the corrupt word is NOT yet
   written (`sw a0,0(s2)` 0x82e40 is after the cut), so the block still holds the image with corrupt
   false and the record's own bytes. s10 is the frame for locals again (0x82c8c), s2 = &pp->corrupt
   (0x82cd4); the first block is read from R+0xf0. *)
Definition hs_L_post (cx : hs_scx) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 26, e_F e);
 (LReg 20, shadow_addr (e_pp e + 0x4000)); (LReg 18, e_pp e + 0x4d18);
 (LCell XR 0x20, e_F e); (LCell XR 0x28, e_cap e); (LCell XR 0x40, e_null e);
 (LCell XR 0x90, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0xa0, e_pp e + 0x4d14);
 (LCell XR 0x60, e_F e); (LCell XR 0xf0, e_pp e)].
(* the block's bytes with the first kk corruption bytes written at off *)
Definition hs_img_corr (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (kk : Z) : list byte :=
pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn (Z.to_nat kk) bs))
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Definition hs_corr_wf (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (cnt : Z) : Prop :=
8 <= off /\ off + Z.of_nat (length bs) <= hs_plen sh ps /\ (length bs <= 7)%nat /\
0 < cnt <= 7 /\ Z.of_nat (length bs) = Z.min cnt (hs_plen sh ps - off).
Definition hs_cut_R (cx : hs_scx) (sh : Z) (ps : list (Z * pval)) (rest r : list byte)
(off : Z) (bs : list byte) (cnt kk : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2
(hs_L_post cx ++ [(LReg 13, kk); (LReg 12, cnt - kk); (LReg 14, off);
                  (LReg 10, hs_cur cx rest r); (LReg 15, Z.of_nat (length r))]) /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (hs_img_corr sh ps off bs kk) /\
hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
hs_corr_wf sh ps off bs cnt /\ 0 <= kk < cnt /\ kk <= Z.of_nat (length bs) /\
skipn (Z.to_nat kk) bs = fst (fuzz_u8s (length bs - Z.to_nat kk) r).
Definition hs_cut_RT (cx : hs_scx) (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx cx W2 mem2 regs2 (hs_L_post cx) /\
hs_fsh_at cx W2 mem2 hs_P0 /\
hs_pp_at cx W2 mem2 (hs_img_corr sh ps off bs (Z.of_nat (length bs))) /\
hs_in cx rest /\ hs_suffix rest r /\ hs_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
8 <= off /\ off + Z.of_nat (length bs) <= hs_plen sh ps /\ (length bs <= 7)%nat.

(* ---------------- C2 = 0x82e60: the build is done; the second request is in a0 ----------------
   This cut IS headamp_build_contract's post, at the pc its contract names (hi_c2 headamp_himg_A): the C2 value
   list, the frame's shadow back to the prologue's, and the block holding Layout.pp_bytes of the record. *)
Definition hs_cut_C2 (cx : hs_scx) (rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hs_core cx (hs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hd_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L2 headamp_himg_A) /\
hs_fsh_at cx W2 mem2 hs_P0 /\ hs_pp_at cx W2 mem2 (pp_bytes (fst (pod_build rest))) /\
e_len (x_e cx) = hd_len rest.

(* ===================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   ===================================================================================================
   One per cut, with the LOOP INDEX as an argument (and never under the inner quantifier), so that the
   latch of a loop can hand the head its next index and the closure is an induction on the index, not a
   circular hypothesis: hs_from_N .. (S i) is what the property loop's latch gives, hs_from_C .. i (S k)
   what the pod loop's latch gives. A piece lemma is `hs_start_M01 cx rest -> <the continuations of its end
   cuts> -> <the continuation of its start cut>`, so a lane proving one piece takes the other lanes'
   continuations as hypotheses and never sees their proofs. POST is generic. *)
Section f.
Variable cx : hs_scx.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.

Definition hs_from_B7 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r np, hs_cut_B7 cx rest r np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_B7 regs2 mem2 md2) POST.
Definition hs_from_BO : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, hs_cut_BO cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_BO regs2 mem2 md2) POST.
Definition hs_from_PH : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, hs_cut_PH cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_PH regs2 mem2 md2) POST.
Definition hs_from_N (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = i)%nat ->
hs_cut_N cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_N regs2 mem2 md2) POST.
Definition hs_from_SEL7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 np ps r, (length ps = i)%nat ->
hs_cut_SEL7 cx np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_SEL7 regs2 mem2 md2) POST.
Definition hs_from_SELK (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
hs_cut_SELK cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_SELK regs2 mem2 md2) POST.
Definition hs_from_SELI (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
hs_cut_SELI cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_SELI regs2 mem2 md2) POST.
Definition hs_from_SELS (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
hs_cut_SELS cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_SELS regs2 mem2 md2) POST.
Definition hs_from_C (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat -> (length es = k)%nat ->
hs_cut_C cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_C regs2 mem2 md2) POST.
Definition hs_from_D (i k : nat) (kd : Z) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r, (length ps = i)%nat -> (length es = k)%nat ->
hs_cut_D cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (hs_pc_D kd) regs2 mem2 md2) POST.
Definition hs_from_D0E (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es, (length ps = i)%nat -> (length es = k)%nat ->
hs_cut_D0E cx sh np ps cnt es rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_D0E regs2 mem2 md2) POST.
Definition hs_from_G (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs, (length ps = i)%nat -> (length es = k)%nat ->
hs_cut_G cx sh np ps cnt es rest rr r pb chs ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_G regs2 mem2 md2) POST.
Definition hs_from_J (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed, (length ps = i)%nat -> (length es = k)%nat ->
hs_cut_J cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_J regs2 mem2 md2) POST.
Definition hs_from_CL (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat ->
hs_cut_CL cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_CL regs2 mem2 md2) POST.
Definition hs_from_LATCH (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
hs_cut_LATCH cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_LATCH regs2 mem2 md2) POST.
Definition hs_from_LATCH7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
hs_cut_LATCH7 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_LATCH7 regs2 mem2 md2) POST.
Definition hs_from_P : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
hs_cut_P cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_P regs2 mem2 md2) POST.
Definition hs_from_P1 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
hs_cut_P1 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_P1 regs2 mem2 md2) POST.
Definition hs_from_R (kk : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt,
hs_cut_R cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_R regs2 mem2 md2) POST.
Definition hs_from_RT : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps off bs r,
hs_cut_RT cx sh ps off bs rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs HS_RT regs2 mem2 md2) POST.
Definition hs_from_C2 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2,
hs_cut_C2 cx rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (hi_c2 headamp_himg_A) regs2 mem2 md2) POST.
End f.

(* ===================================================================================================
   THE PIECE STATEMENTS, one per walk lane of the build
   =================================================================================================== *)
(* W3a: C1 -> the object's header (pod.h:384-395): the NULL test (dead), the block's memset, the two
   header reads, the top size word, and the header of this shape. Its start is the segment's own start
   state, which is headamp_build_contract's premise set. *)
Definition hs_start_M01 (cx : hs_scx) (rest : list byte) : Prop :=
hs_pre cx (hi_shA headamp_himg_A) /\
hd_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L1 headamp_himg_A) /\
e_len (x_e cx) = hd_len rest /\ hs_in cx rest.
Definition hs_piece_W3a_stmt : Prop :=
forall cx POST rest,
hs_start_M01 cx rest -> hs_from_B7 cx POST rest -> hs_from_BO cx POST rest ->
SRr segs (x_W cx) (cfg_at segs (hi_c1 headamp_himg_A) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
(* W3b: the two header pieces and the property loop's preheader (pod.h:389-398). *)
Definition hs_piece_W3b_hdr_stmt : Prop :=
forall cx POST rest,
hs_start_M01 cx rest -> hs_from_PH cx POST rest -> hs_from_BO cx POST rest.
Definition hs_piece_W3b_b7_stmt : Prop :=
forall cx POST rest,
hs_start_M01 cx rest -> hs_from_PH cx POST rest -> hs_from_B7 cx POST rest.
Definition hs_piece_W3b_pre_stmt : Prop :=
forall cx POST rest,
hs_start_M01 cx rest -> hs_from_N cx POST rest 0 -> hs_from_P cx POST rest ->
hs_from_PH cx POST rest.
(* W4: one property's selector, its shape-7 body, its key, and the loop's latch. *)
Definition hs_piece_W4_sel_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_SEL7 cx POST rest i -> hs_from_SELK cx POST rest i ->
hs_from_N cx POST rest i.
Definition hs_piece_W4_int7_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_LATCH7 cx POST rest i -> hs_from_SEL7 cx POST rest i.
Definition hs_piece_W4_key_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_SELS cx POST rest i -> hs_from_SELI cx POST rest i ->
hs_from_SELK cx POST rest i.
Definition hs_piece_W4_latch_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_N cx POST rest (S i) -> hs_from_P1 cx POST rest ->
hs_from_LATCH cx POST rest i /\ hs_from_LATCH7 cx POST rest i.
(* W5: the Int-7 value pod, the params Struct's header and count, and its close (pod.h:412-438). *)
Definition hs_piece_W5_int_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_LATCH cx POST rest i -> hs_from_SELI cx POST rest i.
Definition hs_piece_W5_open_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_C cx POST rest i 0 -> hs_from_CL cx POST rest i ->
hs_from_SELS cx POST rest i.
Definition hs_piece_W5_close_stmt : Prop :=
forall cx POST rest i,
hs_start_M01 cx rest -> hs_from_LATCH cx POST rest i -> hs_from_CL cx POST rest i.
(* W6a: the switch's dispatch and its two input-driven exits, then cases 2 and 3. *)
Definition hs_piece_W6a_disp_stmt : Prop :=
forall cx POST rest i k,
hs_start_M01 cx rest -> (forall kd, hs_from_D cx POST rest i k kd) -> hs_from_D0E cx POST rest i k ->
hs_from_C cx POST rest i k.
Definition hs_piece_W6a_cases_stmt : Prop :=
forall cx POST rest i k kd,
hs_start_M01 cx rest -> In (kd mod 10) [2; 3] -> hs_from_J cx POST rest i k ->
hs_from_D cx POST rest i k kd.
(* W6b: cases 1, 4, 5 and 9. W6c: cases 6, 7 and 8. *)
Definition hs_piece_W6b_stmt : Prop :=
forall cx POST rest i k kd,
hs_start_M01 cx rest -> In (kd mod 10) [1; 4; 5; 9] -> hs_from_J cx POST rest i k ->
hs_from_D cx POST rest i k kd.
Definition hs_piece_W6c_stmt : Prop :=
forall cx POST rest i k kd,
hs_start_M01 cx rest -> In (kd mod 10) [6; 7; 8] -> hs_from_J cx POST rest i k ->
hs_from_D cx POST rest i k kd.
(* W7a: case 0 up to the parts, from both its entries. W7b: the parts and the key's text. *)
Definition hs_piece_W7a_stmt : Prop :=
forall cx POST rest i k kd,
hs_start_M01 cx rest -> kd mod 10 = 0 -> hs_from_G cx POST rest i k ->
hs_from_D cx POST rest i k kd /\ hs_from_D0E cx POST rest i k.
Definition hs_piece_W7b_stmt : Prop :=
forall cx POST rest i k,
hs_start_M01 cx rest -> hs_from_J cx POST rest i k -> hs_from_G cx POST rest i k.
(* W8: the inlined pod_write_ent and the record copy (pod.h:428-432), then the pod loop's latch. *)
Definition hs_piece_W8_stmt : Prop :=
forall cx POST rest i k,
hs_start_M01 cx rest -> hs_from_C cx POST rest i (S k) -> hs_from_CL cx POST rest i ->
hs_from_J cx POST rest i k.
(* W10: the top size word, the corruption and the second block's request (pod.h:440-448, fuzz.h:73). *)
Definition hs_piece_W10_post_stmt : Prop :=
forall cx POST rest,
hs_start_M01 cx rest -> (forall kk, hs_from_R cx POST rest kk) -> hs_from_RT cx POST rest ->
hs_from_C2 cx POST rest ->
hs_from_P cx POST rest /\ hs_from_P1 cx POST rest.
Definition hs_piece_W10_corr_stmt : Prop :=
forall cx POST rest kk,
hs_start_M01 cx rest -> hs_from_R cx POST rest (S kk) -> hs_from_RT cx POST rest ->
hs_from_R cx POST rest kk.
Definition hs_piece_W10_req_stmt : Prop :=
forall cx POST rest,
hs_start_M01 cx rest -> hs_from_C2 cx POST rest -> hs_from_RT cx POST rest.

(* ============================== checks on the stated data ==============================
   Every cut list but J's names each location once (J repeats hs_Rc0's eight registers and s11 with the same
   values, as role's J does), so no list binds one location to two values. hs_PG and hs_PJ cover the frame's 80
   shadow granules, as hs_P0 does, and the three differ only below granule 0x30. *)
Definition hs_lkey (l : hd_loc) : Z :=
match l with LReg r => r | LCell XR o => 0x10000 + o | LCell _ _ => -1 end.
Fixpoint hs_nodupb (l : list Z) : bool :=
match l with [] => true | x :: t => negb (existsb (Z.eqb x) t) && hs_nodupb t end.
Definition hs_keys_ok (L : list (hd_loc * Z)) : bool := hs_nodupb (map (fun f => hs_lkey (fst f)) L).
Lemma hs_cut_lists_nodup : forall (cx : hs_scx) sh np sel ps cnt es (rest r : list byte) kd pb,
hs_keys_ok (hs_L_hdr cx sh np rest r) = true /\ hs_keys_ok (hs_L_PH cx sh np rest r) = true /\
hs_keys_ok (hs_L_N cx sh np ps rest r) = true /\ hs_keys_ok (hs_L_SEL cx sh np ps rest r) = true /\
hs_keys_ok (hs_L_SEL cx sh np ps rest r ++ [(LReg 11, sel)]) = true /\
hs_keys_ok (hs_L_KEY cx sh np sel ps rest r) = true /\
hs_keys_ok (hs_L_pod cx sh np ps cnt rest r ++ [(LReg 11, Z.of_nat (length es))]) = true /\
hs_keys_ok (hs_L_D cx sh np ps cnt es rest r kd) = true /\
hs_keys_ok (hs_L_Dc cx sh np ps cnt es ++ [(LCell XR 0x118, 0); (LReg 25, hs_cur cx rest [])]) = true /\
hs_keys_ok (hs_L_Dc0 cx sh np ps cnt es
 ++ [(LCell XR 0x118, Z.of_nat (length r));
     (LReg 20, e_F (x_e cx) + 0xa0); (LReg 27, pb); (LReg 25, hs_cur cx rest r)]) = true /\
hs_keys_ok (hs_Rc cx ++ hs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000)); (LReg 25, hs_cur cx rest r);
     (LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps);
     (LCell XR 0xa8, 1); (LCell XR 0xe8, hs_first ps);
     (LCell XR 0x118, Z.of_nat (length r))]) = true /\
hs_keys_ok (hs_Rc0 cx ++ hs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LCell XR 0xd8, Z.of_nat (length ps) - 1); (LCell XR 0xa8, hs_seen ps)]
 ++ hs_cur2 cx rest r) = true /\
hs_keys_ok (hs_Rc0 cx ++ hs_Kc cx sh np
 ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000));
     (LReg 17, Z.of_nat (length ps) - 1); (LReg 25, hs_seen ps)]
 ++ hs_cur2 cx rest r) = true /\
hs_keys_ok (hs_L_P cx rest r) = true /\
hs_keys_ok (hs_L_P cx rest r ++ [(LReg 20, shadow_addr (e_pp (x_e cx) + 0x4000))]) = true /\
hs_keys_ok (hs_L_post cx) = true /\
hs_keys_ok (hs_L_post cx ++ [(LReg 13, 0); (LReg 12, 0); (LReg 14, 0); (LReg 10, 0); (LReg 15, 0)]) = true.
Proof.
intros. unfold hs_L_D. destruct (kd mod 10 =? 9); vm_compute; repeat split.
Qed.
Lemma hs_patterns_len :
  length hs_P0 = 80%nat /\ length hs_PJ = 80%nat /\ length hs_PG = 80%nat /\
  skipn 48 hs_PJ = skipn 48 hs_P0 /\ skipn 48 hs_PG = skipn 48 hs_P0.
Proof. vm_compute. repeat split. Qed.

End d.
End c.
End b.
