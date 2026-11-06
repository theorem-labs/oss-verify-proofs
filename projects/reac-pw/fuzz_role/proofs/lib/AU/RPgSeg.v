(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSeg.v at 3c7e900fc63, restated in the shape
   of proofs/reac-pw/fuzz_rate/lib/AU/RtPgSegB.v at 24c66d54276 (its lines 1-1264: the same cut predicates, list
   helpers, continuations and piece statements, argument for argument) for reac-pw/fuzz_role image B
   (fuzz_role.asan-ubsan): image B's pcs, registers, real-frame cells and frame objects, each list measured on image B's
   code; the record is lib/AU/RPgImgA.v's and the frame's shadow lib/AU/RPgMem.v's; the Int-7 piece enters the latch
   at its second entry; the pods of the shape-7 and the Int-7 pieces are written by a call; the inner scan's cut is
   one instruction after its rotated head; the checks' head has no absent exit; role's model terms (Role.*,
   rl_parse_res, the role cell) are image A's. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): THE CUT STATES of the walk
   of LLVMFuzzerTestOneInput (0x80020, 10848 bytes, 2712 instructions) inside its two middle segments, and the
   statement of every piece those segments are split into. Statement text only: proves no function (kind: statement
   text).

   WHAT THIS FILE IS FOR. The walk is cut at the points the plain walk of the same function is cut at
   (lib/Prog/LLVMFuzzerTestOneInput_c.v): ENTRY, C1 = 0x802c4 (malloc(pp) returned), C3 = 0x82168 (malloc(pod)
   returned), C4 = 0x82570 (check_code returned) and RET; lib/AU/RPgHarn.v states them and the segments between them.
   The two middle bodies are the fixed contracts role_build_contract (C1 -> C2 = the malloc(pod) `jal` 0x82164) and
   role_check_contract (C3 -> C4) of lib/A/RPgCSpec.v at image B's record RPgImgA.role_himg_B. Their walks are cut
   again at the heads and joins of their loops and at the boundaries of their pieces, and every piece is stated here,
   so that the pieces are proved in parallel and each proof sees only the STATEMENTS of the pieces its continuation
   goes to.

   HOW A CUT IS STATED, AND WHY NOT AS A SYMBOLIC STATE. A cut is a SEMANTIC predicate over
   (ly, S, W, regs, mem, md) at the cut's pc: the caller's journal from the segment's start, the frame's shadow
   bytes, the first block's image, the input bytes left, and a list of (location, value) facts over the run's
   quantities (RPgBase.rl_at: a register, or the 8-byte cell at an offset of a base). A symbolic state can only be
   written down after the piece before it has been run, which would serialise the pieces; a semantic cut lets each
   piece rebuild its own symbolic state from the cut, as the released walks rebuild the entry one.
   A cut states only POSITIVE facts. What a call leaves alone is not restated: the journal's own clauses and each
   callee's write-set post carry it between cuts.

   WHERE A VALUE LIVES. Image B keeps the harness's values in registers and in 8-byte cells of the real frame at
   R + off, R = 32 * floor((S - 0x200) / 32) being the 32-aligned base the prologue puts in sp and s1 (0x80060,
   0x80064) and S the entry sp (s0, 0x8005c). The locals whose address is taken live in the frame for locals F, a
   side-stack frame of class 4 that the prologue takes (0x8008c `addi a0,zero,0x2c0`, 0x80090 the call, s7 = s10 = F
   at 0x80094 / 0x800a0; R+0x20 := s7 and R+0x38 := s10 at 0x8066c / 0x80690): t[96] at F+0x20, ch[24] at F+0xa0,
   r[4] at F+0xe0, e (104 bytes) at F+0xf0 (the shape-7 Int pod), e42 (104) at F+0x180 (the Int-7 pod), e62 (104) at
   F+0x210 (the pod loop's pod) and role at F+0x2a0 (RPgMem's RM_* offsets). parts[4] and the Float child's flag are
   not frame objects: they are the real-frame cells R+0x178 .. R+0x197. s3 = (F >> 3) + K is the frame's shadow base
   and s11 = K the runtime's shadow offset throughout. sp = R from 0x80060 to the epilogue (the real-stack arm
   0x800a8 .. 0x800c0 is not run: the option byte is 1 and the class-4 call returns a frame). The flags byte is in
   R+0x40 from E01 on. Every list below was measured on image B's code: a forward pass over the 2396 instructions
   that reach the `ret` (the 316 failure-path instructions removed), with the symbols S, R, F, K, pp, pod and the
   constants, joined at every merge, gives each value that every path into the cut sets; a backward pass gives the
   locations the code after the cut reads before it writes them; and the reaching setters of every location were read
   (each is named in the comment of its list).

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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require RoleImgB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the pcs of the cuts ============================================
   Each is the address of the first instruction of the piece that starts there; the segment cuts are
   RPgImgA.role_himg_B's hi_c1 .. hi_c4 (lib/AU/RPgHarn.v RH_C1 .. RH_C4). *)
Definition RS_ENTRY : Z := 0x80020.      (* `addi sp,sp,-0x200` *)
Definition RS_RET : Z := 0x82600.        (* `ret` *)
Definition RS_K82578 : Z := 0x82578.     (* `mv a0,s6` after the first release (free(pod) `jal` 0x82574) *)
Definition RS_J8258c : Z := 0x8258c.     (* `lui a0,0x45e03`: the frame's retirement word, after both releases and
                                           role's scope store *)
(* inside the build (M01) *)
Definition RS_B7 : Z := 0x8045c.         (* the shape-7 object header, from `bne a3,a4` 0x80458 *)
Definition RS_BO : Z := 0x804f0.         (* the Object header (shape <> 7) *)
Definition RS_PH : Z := 0x80664.         (* `sd a7,0x28(s1)`: the property loop's preheader *)
Definition RS_N : Z := 0x80770.          (* `beqz t3`: the property loop's head (the selector byte's read) *)
Definition RS_SEL7 : Z := 0x807b4.       (* the shape-7 Int pod of one property (`sb zero,0x22(s3)`: e into scope) *)
Definition RS_SELK : Z := 0x8086c.       (* a property's key, its flags and the `first` test *)
Definition RS_SELI : Z := 0x81b98.       (* the Int-7 value pod (`sb zero,0x34(s3)`: e42 into scope) *)
Definition RS_SELS : Z := 0x809d4.       (* the params Struct's header and its pod count *)
Definition RS_C : Z := 0x80b54.          (* `sd a1,0x150(s1)`: the pod loop's head *)
Definition RS_D0 : Z := 0x80c14.         (* ent_build case 0 (the head-amp key), with input left *)
Definition RS_D0E : Z := 0x80c88.        (* ent_build case 0 with no input left *)
Definition RS_D1 : Z := 0x810d0.
Definition RS_D2 : Z := 0x80f88.
Definition RS_D3 : Z := 0x80ffc.
Definition RS_D4 : Z := 0x80f34.
Definition RS_D5 : Z := 0x8113c.
Definition RS_D6 : Z := 0x811d8.
Definition RS_D7 : Z := 0x81050.
Definition RS_D8 : Z := 0x8122c.
Definition RS_D9 : Z := 0x812d4.
Definition RS_G : Z := 0x80dc8.          (* case 0 after the digits, the reverse and the odd_ch part *)
Definition RS_J : Z := 0x818d8.          (* the pod is built: the capacity guard, then the call
                                           pod_write_ent(pp, e62) *)
Definition RS_CL : Z := 0x81ccc.         (* the params Struct's size word is about to be patched *)
Definition RS_LATCH : Z := 0x81d84.      (* the property loop's latch, from the Struct's close *)
Definition RS_LATCH7 : Z := 0x81d88.     (* its second entry, from the shape-7 piece (`j` 0x80868) and from the
                                           Int-7 piece (`j` after 0x81c18) *)
Definition RS_P : Z := 0x81e6c.          (* the builder's end, entered with no property *)
Definition RS_P1 : Z := 0x81e70.         (* its second entry, from the latch *)
Definition RS_R : Z := 0x8209c.          (* the corruption loop's head *)
Definition RS_RT : Z := 0x82134.         (* after the corruption: corrupt := 1, then the second request *)
(* inside the checks (M02) *)
Definition RS_E : Z := 0x821dc.          (* the inlined expect_role begins *)
Definition RS_O : Z := 0x82278.          (* its outer scan head *)
Definition RS_I : Z := 0x822a4.          (* its inner scan at entry m: the instruction after the loop head 0x822a0,
                                           which tests the previous turn's result first (`bnez a0` -> KM) *)
Definition RS_KM : Z := 0x82370.         (* a key was found: the compare and then the value *)
Definition RS_ABS : Z := 0x8245c.        (* no pair matched: the absent check *)
Definition RS_MAL : Z := 0x824f8.        (* the malformed check *)
Definition RS_T : Z := 0x82504.          (* the tail: the answer and the two codes *)

(* the 13 callee-saved words the prologue writes at [S - 0x68, S) (0x80028 .. 0x80058) and the epilogue reads back
   (0x825c8 .. 0x825f8), in the order of their offsets -8, -0x10, ..., -0x68 *)
Definition rs_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the frame for locals is a side-stack frame of class 4 (RPgImgA: hi_cid role_himg_B) *)
Definition RS_CID : Z := 4.
(* the real frame below S (`addi sp,sp,-0x200`) *)
Definition RS_RSZ : Z := 0x200.
(* the events the walk's journal records: two allocations and two releases *)
Definition RS_EV : Z := 4.

Lemma rs_cid_himg : hi_cid role_himg_B = RS_CID /\ hi_rsz role_himg_B = RS_RSZ.
Proof. split; reflexivity. Qed.

(* The byte values of the frame's shadow at the states the walk passes through (one byte per 8-byte granule of F:
   the prologue writes 88, 0x80104 .. 0x80264), in RPgMem's form rm_sh t ch r e e42 e62 ro (true = the object is in
   scope). P0 is the prologue's pattern (every object out of scope; RPgMem.rm_sh_P0: hi_shA role_himg_B). PJ has
   e62's 13 granules 0x42 .. 0x4e in scope (each pod loop turn's stores 0x80b58 .. 0x80b88; out again at
   0x8197c .. 0x819b4 / 0x81c94 .. 0x81cc8); PG has t (0x04 .. 0x0f) and ch (0x14 .. 0x16) in scope as well, with r
   (0x1c) back out of scope (0x80dc4; the odd_ch path never opens it); PB has role's granule 0x54 in scope (0x82194)
   and is RPgMem.rm_sh_PB: hi_shB role_himg_B (image B keeps parts and the flag on the real frame, so no other object
   comes into scope in M02). e (0x1e .. 0x2a) and e42 (0x30 .. 0x3c) are in scope only inside the shape-7 and the
   Int-7 pieces, between their cuts. *)
Definition rs_P0 : list Z := rm_sh false false false false false false false.
Definition rs_PJ : list Z := rm_sh false false false false false true false.
Definition rs_PG : list Z := rm_sh true true false false false true false.
Definition rs_PB : list Z := rm_sh false false false false false false true.

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
   The segment's own journal from its start (with the segment's event count: neither middle segment allocates), sp
   / gp / tp as at the start, the frames, the blocks, the I/O state and the meter as at the start, and every byte
   outside the callees' stack [R - T_SEG_STK, R) and outside the ranges the segment writes as at the start. These are
   exactly the clauses of RPgCSpec.rl_seg_post without its pc and its result, so the cut at a segment's last pc IS
   that segment's post. *)
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

(* what every segment's contract asks at its start (RPgCSpec.rl_seg_pre at image B's record) *)
Definition rs_pre (cx : rs_scx) : Prop :=
rl_seg_pre segs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
(x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)
role_himg_B (x_RLO cx) (x_RHI cx) (x_e cx) (x_pos cx).

(* the journal-and-frame part of a cut inside the segment, with the segment's write set E *)
Definition rs_core (cx : rs_scx) (E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rs_mid (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
(x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) E ly2 S2 W2 regs2 mem2 md2.

(* the two segments' write sets, as their contracts state them: the image's ranges (RPgImgA: hi_w1 = the frame's
   objects t .. e62, their shadow granules and M01's real-frame cells; hi_w2 = the role cell, its shadow byte, the
   spills around the string compare, rc and the flag / out cell) and the block the segment fills *)
Definition rs_E1 (cx : rs_scx) : Z -> Prop :=
fun a => rl_inw (x_e cx) (hi_w1 role_himg_B) a \/
e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE.
Definition rs_E2 (cx : rs_scx) : Z -> Prop :=
fun a => rl_inw (x_e cx) (hi_w2 role_himg_B) a \/
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
 ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) /\ ~ rl_inw (x_e cx) (hi_w1 role_himg_B) a /\
 ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)).

(* ===================================================================================================
   THE BUILD (M01): the cuts of role_build_contract's walk, from C1 = 0x802c4 to C2 = 0x82164
   ===================================================================================================
   The builder writes one object into the first block. Its state at a cut is the record so far (a Model.pb_cut: the
   shape sh, the properties ps written and, inside a params Struct, the pods es written), what is left of the input,
   and the loop counters; the block holds Layout.pc_image of that state and the R-relative cells hold the loop's
   constants and counters. *)

(* The constants the build puts in R-relative cells and no piece writes again (each set on every path into N and
   read after it): 0x15555556 is the `% 12u` multiplier (pod.h:354, 0x80714), 0x10003 is SPA_PROP_VOLUME (0x806f8),
   0x80001 is SPA_PROP_params (0x80700), -0x4001 and -0x3ffd are the two capacity bounds (0x80708, 0x803ac); R+0x28
   and R+0x30 are the top size word's offset (0: the block's length before the header, `ld a7,0(s6)` 0x8039c after
   the memset) and its address (0x80664, 0x80668); R+0x20 and R+0x38 are F (the frame call's result and its copy,
   0x8066c / 0x80690); R+0x100 is the shape-7 flag (0x80468 / 0x80654), R+0x108 the property count np (0x8031c /
   0x80330 / 0x8036c); R+0x158 / R+0x110 / R+0x48 hold e62's address, its body's and its body's + 8 (the pod loop's
   pod, F+0x210: 0x80724, 0x80754, 0x8072c), R+0xb8 / R+0xa0 e's and its body's (the shape-7 pod, F+0xf0: 0x80748,
   0x80750) and R+0x68 / R+0x60 e42's and its body's + 4 (the Int-7 pod, F+0x180: 0x8073c, 0x80744); R+0xd0 is &ch
   (0x80730); R+0x18 / R+0x78 / R+0x50 / R+0xd8 / R+0x120 / R+0x130 are the fields &is_props, &has_params,
   &params_struct, &ent[0], &n_ent and &len (0x80694, 0x806c4, 0x806d4, 0x80760, 0x80680, 0x8076c), R+0xe8 the
   shadow index of &n_ent (0x80688) and R+0x148 the shadow address of &len (0x8038c); R+0xc8 / R+0xe0 / R+0xf0 /
   R+0xf8 hold the complements the trap tests compare against (0x80738, 0x80768, 0x8075c, 0x803b8). The `v / 10`
   multiplier of the digit loop (pod.h:240-241) is the register s7 (0x8070c, 0x8071c). *)
Definition RS_MULT10 : Z := 0xcccccccd * 2 ^ 32.
Definition rs_Kc (cx : rs_scx) (sh np : Z) : list (rl_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x10, 0x15555556); (LCell XR 0x20, e_F e); (LCell XR 0x28, 0); (LCell XR 0x30, e_pp e);
 (LCell XR 0x48, e_F e + 0x220); (LCell XR 0x38, e_F e); (LCell XR 0x40, e_fl e); (LCell XR 0x70, 0x10003);
 (LCell XR 0x50, e_pp e + 0x4010); (LCell XR 0xb0, 0x80001); (LCell XR 0x78, e_pp e + 0x400c);
 (LCell XR 0xd0, e_F e + 0xa0); (LCell XR 0xd8, e_pp e + 0x4014);
 (LCell XR 0xe8, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0x130, e_pp e + 0x4000);
 (LCell XR 0x120, e_pp e + 0x4d14); (LCell XR 0x140, e_pp e); (LCell XR 0x108, np);
 (LCell XR 0x100, Z.b2z (sh =? 7)); (LCell XR 0x148, shadow_addr (e_pp e + 0x4000));
 (LCell XR 0x110, e_F e + 0x218); (LCell XR 0xa8, -0x4001); (LCell XR 0xc0, -0x3ffd);
 (LCell XR 0x158, e_F e + 0x210);
 (LCell XR 0x18, e_pp e + 0x4008); (LCell XR 0x60, e_F e + 0x18c); (LCell XR 0x68, e_F e + 0x180);
 (LCell XR 0xa0, e_F e + 0xf8); (LCell XR 0xb8, e_F e + 0xf0); (LCell XR 0xc8, Z.lnot (e_F e + 0xa0));
 (LCell XR 0xe0, Z.lnot (e_pp e + 0x4014)); (LCell XR 0xf0, Z.lnot (e_F e + 0x218));
 (LCell XR 0xf8, Z.lnot (e_pp e))].

(* the registers the property loop keeps: s0 = S, s1 = R, s3 = the frame's shadow base, s11 = the runtime's shadow
   offset, s5 = &r (0x806b0), s9 = &t (0x806a8), s7 = the digit loop's multiplier (0x8070c, 0x8071c); and s10 = -8
   (0x806d8, set again after each body that borrows s10: 0x8085c, 0x819b0, 0x81c74, 0x81cc4), which some cuts carry
   (rs_Rc). pp, -0x4001 and the shadow address of &pp->len are only in cells (rs_Kc); &pp->len is also in s6 from
   0x80380 on (the bodies that borrow s6 reload it from R+0x130). *)
Definition rs_Rc0 (cx : rs_scx) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 21, e_F e + 0xe0); (LReg 25, e_F e + 0x20); (LReg 23, RS_MULT10)].
Definition rs_Rc (cx : rs_scx) : list (rl_loc * Z) := rs_Rc0 cx ++ [(LReg 26, -8)].

(* the cursor: in the header cuts and at N in.p is in s4 and in.n in t3; after the selector byte's read (SEL7, SELK,
   SELI, SELS) in.p is in t4 (`addi t4,s4,1` 0x80774 / `mv t4,s4` 0x807a8) *)
Definition rs_cur2 (cx : rs_scx) (rest r : list byte) : list (rl_loc * Z) :=
[(LReg 20, rs_cur cx rest r); (LReg 28, Z.of_nat (length r))].
Definition rs_cur2s (cx : rs_scx) (rest r : list byte) : list (rl_loc * Z) :=
[(LReg 29, rs_cur cx rest r); (LReg 28, Z.of_nat (length r))].

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

(* ---------------- the build's first own cuts: 0x8045c (shape 7) and 0x804f0 (any other shape) ----------
   The block was filled with zeros (memset 0x802d8), the two header bytes were read (0x802dc .. 0x8036c), and the
   top size word was written as four zero bytes with len := 4 (0x80420 .. 0x8044c). a0 is that length, a2 =
   len - 0x3ffd is the capacity test's left side (0x80450 / 0x80454), a5 = pp (0x802fc / 0x80334), a6 = pp + 0 and
   a7 = 0 are the top word's address and offset (0x803bc, 0x8039c), a1 = 0x4000 (0x8037c) and s5 = 0x5000 (0x802b4)
   are the constants the preheader turns into the fields' addresses, s6 = &pp->len (0x80380) and s7 = s10 = F. The
   shape is in a3 at BO only (B7's pc overwrites it; the arm fixes sh = 7). *)
Definition rs_L_hdr (cx : rs_scx) (np : Z) (rest r : list byte) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 10, 4); (LReg 12, 4 - 0x3ffd); (LReg 16, e_pp e); (LReg 17, 0); (LReg 21, 0x5000); (LReg 8, e_S e);
 (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF); (LReg 22, e_pp e + 0x4000);
 (LReg 23, e_F e); (LReg 26, e_F e); (LCell XR 0x140, e_pp e); (LCell XR 0x40, e_fl e); (LCell XR 0x108, np);
 (LCell XR 0x148, shadow_addr (e_pp e + 0x4000)); (LCell XR 0xc0, -0x3ffd);
 (LReg 11, 0x4000); (LCell XR 0xf8, Z.lnot (e_pp e)); (LReg 15, e_pp e)]
++ rs_cur2 cx rest r.
(* the block's bytes before the object's header: the top size word only *)
Definition rs_img_hdr : list byte := pp_image (le32 0) false false false [] false.
Definition rs_cut_hdr (cx : rs_scx) (rest r : list byte) (sh np : Z)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_hdr cx np rest r) /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_pp_at cx W2 mem2 rs_img_hdr /\
rs_in cx rest /\ rs_suffix rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ r = rs_r0 rest.
Definition rs_cut_B7 (cx : rs_scx) (rest r : list byte) (np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_cut_hdr cx rest r 7 np ly2 S2 W2 regs2 mem2 md2.
Definition rs_cut_BO (cx : rs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_cut_hdr cx rest r sh np ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 [(LReg 13, sh)] /\ sh <> 7.

(* ---------------- PH = 0x80664: the header is written, the preheader is about to run ----------------
   The block holds the image of the empty record of this shape (its header bytes and, for an Object, is_props); a7
   and a6 still hold the top word's offset and address, which the preheader spills (0x80664, 0x80668); R+0x100 holds
   the shape-7 flag. It is entered from the shape-7 header (`bltu` 0x8046c, or 0x804ec after the Struct header), from
   the Object header (0x80660) and from the dead capacity arm 0x803cc. *)
Definition rs_L_PH (cx : rs_scx) (sh np : Z) (rest r : list byte) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 16, e_pp e); (LReg 17, 0); (LReg 21, 0x5000); (LReg 8, e_S e); (LReg 9, e_R e);
 (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF); (LReg 22, e_pp e + 0x4000); (LReg 23, e_F e);
 (LReg 26, e_F e); (LCell XR 0x140, e_pp e); (LCell XR 0x40, e_fl e); (LCell XR 0x108, np);
 (LCell XR 0x100, Z.b2z (sh =? 7)); (LCell XR 0x148, shadow_addr (e_pp e + 0x4000)); (LCell XR 0xc0, -0x3ffd);
 (LReg 11, 0x4000); (LCell XR 0xf8, Z.lnot (e_pp e)); (LReg 15, e_pp e)]
++ rs_cur2 cx rest r.
Definition rs_cut_PH (cx : rs_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_PH cx sh np rest r) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh [] None)) /\
rs_in cx rest /\ rs_suffix rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ r = rs_r0 rest.

(* ---------------- N = 0x80770: the property loop's head, |ps| properties written ----------------
   The property index is in t1 (0x806a4, the latch's 0x81d88) and `seen` in s2 (0x806a0, the latch's 0x81d90);
   s6 = &pp->len. *)
Definition rs_L_N (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc cx ++ [(LReg 6, Z.of_nat (length ps)); (LReg 18, rs_seen ps); (LReg 22, e_pp (x_e cx) + 0x4000)]
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
   SEL7 0x807b4 (shape 7: the property is an Int pod with no key; the cut is e's first scope store) and SELK 0x8086c
   (any other shape: the key, its flags and the `first` test), split by the shape-7 flag (`ld a0,0x100(s1)`,
   `beqz a0` 0x807ac / 0x807b0). The selector byte was read: a1 holds it at SELK. Image B computes no pp->len here
   (pod_write_ent reads it itself in the shape-7 body; the key piece loads it after SELK). *)
Definition rs_L_SEL (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc0 cx ++ [(LReg 18, rs_seen ps); (LReg 6, Z.of_nat (length ps)); (LReg 22, e_pp (x_e cx) + 0x4000)]
++ rs_Kc cx sh np ++ rs_cur2s cx rest r.
(* what every cut of one property's body shares with N, with the tie of ps to the input: the properties written are
   the ones Model.props_loop makes of the bytes after the two header reads *)
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
rs_at_cx cx W2 mem2 regs2 (rs_L_SEL cx sh np ps rest r ++ [(LReg 26, -8); (LReg 11, sel)]) /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
sh <> 7 /\ 0 <= sel < 256 /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))).

(* ---------------- the two ends of the key piece (pod.h:407-423) ----------------
   SELI 0x81b98 writes the Int value pod of a property whose value is an Int (the volume property, and a params
   property whose selector has bit 4 set; the cut is e42's first scope store), SELS 0x809d4 opens a params Struct. On
   both, the key word and the flags word are already written, so the block's bytes are the record's image with those
   eight bytes appended. seen' is in a4 (0x809a0 / 0x809a8) and `first` in R+0x138 (0x809b8), both written before the
   arm tests 0x809c0 / 0x809cc, with the volume arm's values (seen, 0) when sel mod 4 = 0; s8 = pp (0x809bc). `at` is
   not computed before SELS (the Struct arm loads pp->len at 0x809e4); at SELS s6 = &pp->len, t0 = -0x3ffd and
   t2 = -0x4001 (0x80874 / 0x80878). *)
Definition rs_img_key (sh : Z) (ps : list (Z * pval)) (kk : Z) : list byte :=
pp_image (pc_buf (PbCut sh ps None) ++ le32 kk ++ le32 0)
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
(* the key the selector chooses (Model.prop_step): the volume property, else the params property *)
Definition rs_key_of (sel : Z) : Z := if sel mod 4 =? 0 then 0x10003 else 0x80001.
Definition rs_L_KEY (cx : rs_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc0 cx ++ [(LReg 6, Z.of_nat (length ps));
              (LReg 14, if sel mod 4 =? 0 then rs_seen ps else 1); (LReg 24, e_pp (x_e cx))]
++ rs_Kc cx sh np
++ [(LCell XR 0x138, if sel mod 4 =? 0 then 0 else rs_first ps)]
++ rs_cur2s cx rest r.
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
rs_at_cx cx W2 mem2 regs2
(rs_L_KEY cx sh np sel ps rest r ++
 [(LReg 26, -8); (LReg 22, e_pp (x_e cx) + 0x4000); (LReg 5, -0x3ffd); (LReg 7, -0x4001)]) /\
rs_pp_at cx W2 mem2 (rs_img_key sh ps 0x80001) /\ sh <> 7 /\ 0 <= sel < 256 /\
sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (rs_r0 rest))).

(* ---------------- C = 0x80b54: the pod loop's head, |es| pods written ----------------
   The pod index is in a1 (the pc spills it to R+0x150), the count in R+0x128, `at` in R+0x90 and its address in
   R+0x88, the property index in R+0x98, seen' = 1 in R+0x80 (0x80aec .. 0x80af8, 0x80b44) and `first` in R+0x138
   (0x809b8); the cursor is in s8, what is left in s2 (0x80b04 / 0x80b40, the latch's 0x818e4 / 0x818e8), and s4 = 1
   the left side of the trap tests (0x809f0, the latch's 0x818f8). The frame's shadow is still the prologue's: the
   stores 0x80b58 .. 0x80b88 open e62's granules after the pc. *)
Definition rs_L_pod (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (rest r : list byte)
: list (rl_loc * Z) :=
let e := x_e cx in
rs_Rc cx ++ rs_Kc cx sh np
++ [(LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x90, rs_at_of sh ps);
    (LCell XR 0x88, e_pp e + rs_at_of sh ps); (LCell XR 0x128, cnt); (LCell XR 0x80, 1);
    (LCell XR 0x138, rs_first ps);
    (LReg 18, Z.of_nat (length r)); (LReg 24, rs_cur cx rest r); (LReg 20, 1)].
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
   The dispatch (0x80b54 .. 0x80c10) opens e62's granules, fills e62 with zeros (memset 0x80b98), reads the kind
   byte and jumps through the nine relative entries at .rodata 0x20ed4 (`jr a1` 0x80c10); `bltu a2,a1` 0x80bec takes
   case 9 and `beqz s2` 0x80b9c takes case 0 with no input left. At every entry a6 (0x80bb4) and s8 are the kind
   byte's address, s2 the cursor after it (0x80ba4), s6 what is left after it (0x80be4), t1 what was left before it
   (0x80ba0), a3 the sign-extended kind byte and a0 that byte shifted left by 56 (0x80c04, 0x80c0c), t2 = 10 the
   `% 10` constant (0x80ba8), and a2 = 8 the table's bound or the table's address (0x80be8, 0x80bf4 / 0x80bf8). The
   pod loop's cells (rs_podc) hold the property index, `at` and its address, the count, seen' = 1, `first` and the pod
   index. *)
Definition rs_pc_D (kd : Z) : Z :=
if kd mod 10 =? 0 then RS_D0 else if kd mod 10 =? 1 then RS_D1 else if kd mod 10 =? 2 then RS_D2
else if kd mod 10 =? 3 then RS_D3 else if kd mod 10 =? 4 then RS_D4 else if kd mod 10 =? 5 then RS_D5
else if kd mod 10 =? 6 then RS_D6 else if kd mod 10 =? 7 then RS_D7 else if kd mod 10 =? 8 then RS_D8
else RS_D9.
(* the nine table entries are the targets lib/Pod/RoleImgB.v reads from image B's table bytes at 0x20ed4 (its
   role_asanubsan_jt); case 9 is the `bltu` target *)
Lemma rs_pc_D_jt : forall k, (k < 9)%nat -> rs_pc_D (Z.of_nat k) = nth k RoleImgB.role_asanubsan_jt_tgts 0.
Proof. intros k Hk. do 9 (destruct k as [|k]; [reflexivity|]). lia. Qed.
Lemma rs_pc_D_9 : rs_pc_D 9 = RS_D9.
Proof. reflexivity. Qed.
Definition rs_podc (cx : rs_scx) (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rl_loc * Z) :=
[(LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x90, rs_at_of sh ps); (LCell XR 0x128, cnt);
 (LCell XR 0x80, 1); (LCell XR 0x138, rs_first ps); (LCell XR 0x150, Z.of_nat (length es));
 (LCell XR 0x88, e_pp (x_e cx) + rs_at_of sh ps)].
Definition rs_L_Dc0 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rl_loc * Z) :=
rs_Rc0 cx ++ rs_Kc cx sh np ++ rs_podc cx sh ps cnt es.
Definition rs_L_Dc (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (rl_loc * Z) :=
rs_L_Dc0 cx sh np ps cnt es ++ [(LReg 26, -8); (LReg 20, 1)].
(* Case 9 is reached by `bltu a2,a1` 0x80bec, before the instructions 0x80bf0 .. 0x80c0c that form the table's
   address and shift and sign-extend the kind byte, so a2 holds the table's address and a3 and a0 the kind byte's two
   forms only on the nine table entries; on case 9 a2 is still the bound 8. *)
Definition rs_L_D (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (kd : Z) : list (rl_loc * Z) :=
rs_L_Dc cx sh np ps cnt es
++ [(LReg 6, Z.of_nat (length r) + 1); (LReg 24, rs_cur cx rest r - 1); (LReg 16, rs_cur cx rest r - 1);
    (LReg 18, rs_cur cx rest r); (LReg 22, Z.of_nat (length r)); (LReg 7, 10)]
++ (if kd mod 10 =? 9 then [(LReg 12, 8)]
    else [(LReg 12, 0x20ed4); (LReg 13, kd - 256 * (kd / 128)); (LReg 10, kd * 2 ^ 56)]).
(* rr is what is left of the input when the turn begins (at C); the kind byte is the first of it and r what is left
   after it, so the pod the turn builds is Model.ent_build rr. *)
Definition rs_cut_D (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (kd : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_D cx sh np ps cnt es rest r kd) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x210) (rs_u8s (zeros 104)) /\
rs_suffix rest rr /\ (kd, r) = Cursor.fuzz_u8 rr /\ 0 <= kd < 256 /\ rr <> [].
(* the same with no input left: the kind byte reads as 0 and the cursor does not move (fuzz.h:37-43); s2 = 0 *)
Definition rs_cut_D0E (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_Dc cx sh np ps cnt es ++ [(LReg 24, rs_cur cx rest []); (LReg 18, 0)]) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x210) (rs_u8s (zeros 104)).

(* ---------------- G = 0x80dc8: case 0 after the digits, the reverse and the odd_ch part ----------------
   t and ch are in scope and r is out of scope again (0x80dc4; the odd_ch path never opens it), so the frame's shadow
   is neither the prologue's nor the pod loop's: rs_PG is that state. s2 = &ch (0x80cdc / 0x815d0), s8 = the second
   input byte of the head-amp key (0x815b4, or 0 with no byte left: 0x80c7c / 0x80cc4), t1 what is left and the cell
   R+0x118 the cursor (0x80c74 / 0x80cd8 / 0x815c0); ch holds the key's first part with its NUL. *)
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
 ++ [(LReg 6, Z.of_nat (length r)); (LReg 18, e_F (x_e cx) + 0xa0); (LReg 24, pb);
     (LCell XR 0x118, rs_cur cx rest r)]) /\
rs_fsh_at cx W2 mem2 rs_PG /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0xa0) (rs_u8s (chs ++ [NUL])) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x210) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (chs, pb, r) = rs_g_of rr /\
(length chs <= 21)%nat /\ 0 <= pb < 256.

(* ---------------- J = 0x818d8: the pod is built; the capacity check, then the call pod_write_ent(pp, e62) -------
   e62 holds Layout.ent_mem of the pod ent_build made of the turn's input; every case leaves the cursor in a3 and
   what is left in t1, and a5 = pp and s6 = &pp->len, which the cases reload from R+0x140 and R+0x130 (case 0:
   0x80eb8, 0x80f24, 0x80f28, 0x80f2c). *)
Definition rs_cut_J (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (ed : ent) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_Dc0 cx sh np ps cnt es
 ++ [(LReg 13, rs_cur cx rest r); (LReg 6, Z.of_nat (length r)); (LReg 22, e_pp (x_e cx) + 0x4000);
     (LReg 15, e_pp (x_e cx))]) /\
rs_fsh_at cx W2 mem2 rs_PJ /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x210) (rs_u8s (ent_mem ed)) /\
(ed, r) = ent_build rr /\ ent_wf ed.

(* ---------------- CL = 0x81ccc: the count is reached; the Struct's size word is patched ----------------
   The pod loop wrote cnt pods and e62 is out of scope again (0x8197c .. 0x819b4 / 0x81c94 .. 0x81cc8, or never
   opened when the count is 0 or no count byte is left: 0x80b4c, 0x81c84); s6 = &pp->len, what is left in s2
   (0x81c88 on the no-byte path), the cursor in s8 (0x81c84) and s4 = 1. *)
Definition rs_cut_CL (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_Rc cx ++ rs_Kc cx sh np
 ++ [(LReg 22, e_pp (x_e cx) + 0x4000); (LReg 18, Z.of_nat (length r)); (LReg 24, rs_cur cx rest r);
     (LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x90, rs_at_of sh ps);
     (LCell XR 0x88, e_pp (x_e cx) + rs_at_of sh ps); (LCell XR 0x80, 1); (LCell XR 0x138, rs_first ps);
     (LReg 20, 1)]) /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
e_len (x_e cx) = rl_len rest /\
ps = fst (props_loop sh (length ps) (rs_r0 rest)) /\
rs_pod_tie sh ps cnt es rest r /\
sh = rs_sh rest /\ np = rs_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ Z.of_nat (length es) = cnt.

(* ---------------- the latch 0x81d84 / 0x81d88: one property is written ----------------
   At 0x81d84 (from the Struct's close) the property index is in t1 (0x81ce0) and `seen` in R+0x80 (the pc loads it
   into a2); 0x81d88 is entered from 0x81d84 and from the shape-7 and the Int-7 pieces (`j` 0x80868 / after 0x81c18),
   each of which restores the index into t1 and `seen` into a2 itself. On every entry what is left is in t3, the
   cursor in a7 (0x81d00, 0x8081c, 0x81c0c) and s6 = &pp->len. *)
Definition rs_latch_body (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rs_fsh_at cx W2 mem2 rs_P0 /\
rs_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
rs_in cx rest /\ rs_suffix rest r /\ rs_wf sh ps /\
sh = rs_sh rest /\ np = rs_np rest /\ 1 <= Z.of_nat (length ps) <= np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (rs_r0 rest).
Definition rs_L_LATCH (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (rl_loc * Z) :=
rs_Rc cx ++ rs_Kc cx sh np
++ [(LReg 6, Z.of_nat (length ps) - 1); (LReg 28, Z.of_nat (length r)); (LReg 17, rs_cur cx rest r);
    (LReg 22, e_pp (x_e cx) + 0x4000)].
Definition rs_cut_LATCH (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_LATCH cx sh np ps rest r ++ [(LCell XR 0x80, rs_seen ps)]).
Definition rs_cut_LATCH7 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_latch_body cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_LATCH cx sh np ps rest r ++ [(LReg 12, rs_seen ps)]).

(* ---------------- P = 0x81e6c / P1 = 0x81e70: every property is written ----------------
   0x81e6c is entered only when the object has no property (`j` 0x8069c, after the preheader's stores 0x80664 ..
   0x80694 and before its later ones), with the cursor in s4; 0x81e70 is also the latch's exit, where `mv a7,s4`
   0x81e6c has moved the cursor into a7. What is left is in t3 on both, and s6 = &pp->len. *)
Definition rs_L_P (cx : rs_scx) (rest r : list byte) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 28, Z.of_nat (length r)); (LReg 22, e_pp e + 0x4000);
 (LCell XR 0x18, e_pp e + 0x4008); (LCell XR 0x20, e_F e); (LCell XR 0x28, 0); (LCell XR 0x30, e_pp e);
 (LCell XR 0x40, e_fl e); (LCell XR 0x38, e_F e); (LCell XR 0xe8, Z.shiftr (e_pp e + 0x4d14) 3);
 (LCell XR 0xf8, Z.lnot (e_pp e)); (LCell XR 0xc0, -0x3ffd); (LCell XR 0x120, e_pp e + 0x4d14);
 (LCell XR 0x140, e_pp e); (LCell XR 0x148, shadow_addr (e_pp e + 0x4000))].
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
rs_at_cx cx W2 mem2 regs2 (rs_L_P cx rest r ++ [(LReg 20, rs_cur cx rest r)]).
Definition rs_cut_P1 (cx : rs_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_P cx rest r ++ [(LReg 17, rs_cur cx rest r)]).

(* ---------------- R = 0x8209c and RT = 0x82134: the corruption (pod.h:441-448) ----------------
   The object is complete (its top size word was patched, 0x81ed4 .. 0x81ee0), so the block holds the image of the
   record with no corruption yet. The loop writes one byte a turn: a3 = kk is the index (0x82084, 0x82110), a2 =
   cnt - kk what is left of the count the input byte gave (`andi a2,a2,7` 0x8207c, decremented at 0x8210c), a4 = off
   (0x82090 / 0x82094), a0 is the cursor of the byte reads (0x8205c, 0x820d8) and a5 what is left of the input
   (0x8208c, 0x820d4); a6 = 1 is the left side of the trap test 0x820bc (0x82098) and t2 = pp (0x81f48 / 0x81f54). It
   also leaves through `bgeu a1,a7` 0x820b0 when off + kk reaches the length, so the bytes written, bs, are the first
   min(cnt, len - off) of the input's. At RT the corruption is done but the corrupt word is NOT yet written (`sw
   a0,0(s7)` 0x82148 is after the cut), so the block still holds the image with corrupt false and the record's own
   bytes. s6 = &pp->len and s7 = &pp->corrupt (0x81ee4 .. 0x81ee8). *)
Definition rs_L_post (cx : rs_scx) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 22, e_pp e + 0x4000); (LReg 23, e_pp e + 0x4d18);
 (LCell XR 0x18, e_pp e + 0x4008); (LCell XR 0x20, e_F e); (LCell XR 0x40, e_fl e); (LCell XR 0x38, e_F e);
 (LCell XR 0xe8, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0xc0, -0x3ffd);
 (LCell XR 0x120, e_pp e + 0x4d14); (LCell XR 0x140, e_pp e);
 (LCell XR 0x148, shadow_addr (e_pp e + 0x4000))].
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
(rs_L_post cx ++ [(LCell XR 0xf8, Z.lnot (e_pp (x_e cx))); (LReg 13, kk); (LReg 12, cnt - kk);
                  (LReg 14, off); (LReg 10, rs_cur cx rest r); (LReg 15, Z.of_nat (length r)); (LReg 16, 1);
                  (LReg 7, e_pp (x_e cx))]) /\
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

(* ---------------- C2 = 0x82164: the build is done; the second request is in a0 ----------------
   This cut IS role_build_contract's post, at the pc its contract names (hi_c2 role_himg_B): the C2 value list, the
   frame's shadow back to the prologue's, and the block holding Layout.pp_bytes of the record. *)
Definition rs_cut_C2 (cx : rs_scx) (rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
rl_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L2 role_himg_B) /\
rs_fsh_at cx W2 mem2 rs_P0 /\ rs_pp_at cx W2 mem2 (pp_bytes (fst (pod_build rest))) /\
e_len (x_e cx) = rl_len rest.

(* ===================================================================================================
   THE CHECKS (M02): the cuts of role_check_contract's walk, from C3 = 0x82168 to C4 = 0x82570
   ===================================================================================================
   The first block holds Layout.pp_bytes of the record some input made; the segment copies its first len bytes into
   the second block (memcpy 0x82188 when len <> 0), brings role's granule into scope (0x82194: rs_PB, the one frame
   shadow pattern of every cut of M02) and puts 0x5a into role (0x821a0), runs the parse on the copy (or on NULL, by
   bit 0 of the flags byte; 0x821b0), scans the record's entries for the role key when the record is uncorrupted and
   runs the check its answer selects, then the tail (changes, apply_state, check_answer, refuse_code twice and
   check_code). From the parse on, the float state is some fx2 that keeps every float register outside fa0, fa3, fa4
   and fa5 and has a zero rounding mode (main's one float instruction is `flw fa0` 0x824c8; the parse and pod_nearest
   change the others by their contracts). *)
Definition rs_rcell (o : option Role.role) : Z :=
match o with Some ro => Role.role_z ro | None => 0x5a end.
(* the answer the inlined scan computes, and the parse's answer on the block's bytes *)
Definition rs_E0 (rec : pod_rec) : option Role.role * Z := Role.expect_model false rec.
Definition rs_PA (cx : rs_scx) (rec : pod_rec) : option Role.role * Z :=
rl_parse_res (Z.testbit (e_fl (x_e cx)) 0) (buf rec).
(* what every cut of the checks carries; the frame's shadow is rs_PB throughout (role in scope) *)
Definition rs_chk_base (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rl_fxk [10; 13; 14; 15] fx fx2 /\
rs_fsh_at cx W2 mem2 rs_PB /\ rom_view segs W2 mem2 /\
rs_pp_at cx W2 mem2 (pp_bytes rec) /\
pod_rec_wf rec /\ e_len (x_e cx) = Z.of_nat (length (buf rec)) /\
e_pod (x_e cx) <> 0 /\ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)).
(* the role cell (the 4-byte frame object at F+0x2a0), at every cut after the parse: the value the parse wrote,
   else the 0x5a the harness put there *)
Definition rs_role_at (cx : rs_scx) (rec : pod_rec) (W2 : world segs) (mem2 : word -> option byte)
: Prop :=
val_mem segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x2a0) 4 (rs_rcell (fst (rs_PA cx rec))).
(* the values every cut of the checks carries: s0 = S, s1 = R, s3 = the frame's shadow base, s11 = the runtime's
   shadow offset, s2 = pod (0x8216c), s4 = &role (0x82174), F in R+0x20 (the frame call's result, which the release
   reloads at 0x82588) and the flags byte in R+0x40 *)
Definition rs_L_chk (cx : rs_scx) : list (rl_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 18, e_pod e); (LReg 20, e_F e + 0x2a0);
 (LCell XR 0x20, e_F e); (LCell XR 0x40, e_fl e)].

(* ---------------- E = 0x821dc: the inlined expect_role begins ----------------
   Reached when the record is uncorrupted (`bnez a0` 0x821d0 not taken) and bit 0 of the flags byte is clear
   (`bnez s5` 0x821d8 not taken); a0 = &pp->is_props (0x821d4), s9 = rc (0x821c0), s6 = pp (0x821cc), s8 = the
   flags byte (0x82198), s10 = F (0x82170); the cells are rl_seg_pre's C3 values that the scan still reads. *)
Definition rs_cut_E (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 10, e_pp (x_e cx) + 0x4008); (LReg 25, snd (rs_PA cx rec));
                 (LReg 22, e_pp (x_e cx)); (LReg 24, e_fl (x_e cx)); (LReg 26, e_F (x_e cx));
                 (LCell XR 0x38, e_F (x_e cx));
                 (LCell XR 0xe8, Z.shiftr (e_pp (x_e cx) + 0x4d14) 3);
                 (LCell XR 0x120, e_pp (x_e cx) + 0x4d14); (LCell XR 0x140, e_pp (x_e cx));
                 (LCell XR 0xc0, -0x3ffd)]) /\
rs_role_at cx rec W2 mem2 /\
Z.testbit (e_fl (x_e cx)) 0 = false /\ corrupt rec = false /\
Role.parse_model (buf rec) = rs_E0 rec.

(* ---------------- O = 0x82278: the outer scan's head ----------------
   rc is in the cell R+0x158 (0x821f4) and R+0x120 holds the offset 0x4018 (0x82260); the scan's fixed operands are
   s10 = &ent[0], a7 = &ent[0] + 4, t2 = t3 = &ent[0] + 8, the stride t1 = 104 << 32 (the `mulhu` 0x82298 makes 104 m
   of it), the string type t4 = 8, n_ent in s9 (0x82234), and the trap tests' bounds s6 = ~&ent[0], t0 = ~(&ent[0] +
   8) (0x82224 .. 0x82274; the key piece reloads the five spilled ones at 0x8239c .. 0x823b0); a2 is at. *)
Definition rs_L_scan (cx : rs_scx) (rec : pod_rec) : list (rl_loc * Z) :=
let e := x_e cx in
rs_L_chk cx ++
[(LCell XR 0x158, snd (rs_PA cx rec)); (LCell XR 0x120, 0x4018);
 (LReg 29, 8); (LReg 25, Z.of_nat (length (ents rec)));
 (LReg 26, e_pp e + 0x4014); (LReg 17, e_pp e + 0x4018); (LReg 28, e_pp e + 0x401c); (LReg 7, e_pp e + 0x401c);
 (LReg 22, Z.lnot (e_pp e + 0x4014)); (LReg 5, Z.lnot (e_pp e + 0x401c)); (LReg 6, 104 * 2 ^ 32);
 (LCell XR 0x38, e_F e); (LCell XR 0x140, e_pp e)].
Definition rs_scan_inv (rec : pod_rec) (j : nat) : Prop :=
(j <= length (ents rec))%nat /\
rs_E0 rec = Role.role_of_pairs Role.expect_value (pairs_by key_of (skipn j (ents rec)) None).
Definition rs_chk_rec (cx : rs_scx) (rec : pod_rec) : Prop :=
corrupt rec = false /\ is_props rec = true /\ params_struct rec = true /\
snd (rs_PA cx rec) = snd (rs_E0 rec) /\ fst (rs_PA cx rec) = fst (rs_E0 rec).
Definition rs_cut_O (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (j : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2 (rs_L_scan cx rec ++ [(LReg 12, Z.of_nat j)]) /\
rs_role_at cx rec W2 mem2 /\ rs_scan_inv rec j /\ rs_chk_rec cx rec.

(* ---------------- I = 0x822a4: pod_next_pair's inner scan from at0, at entry m ----------
   Image B's inner loop is rotated: its head 0x822a0 first tests a0, the previous turn's result (0, or the body
   address of a key), and leaves to KM when it is set; the scan's own state ("entry m is next, no key in [at0, m)")
   holds one instruction later, at 0x822a4, which every turn of the loop passes (from O with m = at0 and a0 = 0 from
   0x82294; from the latch 0x8233c with m + 1). The bases stay fixed and s7 = 104 m is the offset of ent[m] (0x82298,
   0x82330); s5 = a2 = m (0x82280, 0x8232c; 0x82334); a3 = max(at0, 33) (0x82288 / 0x82290) and a4 = ~(&ent[0] + 8) -
   104 m (0x8229c, 0x82338) are the bounds of the trap tests 0x822a4 / 0x822f0. *)
Definition rs_cut_I (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_scan cx rec ++
 [(LReg 12, Z.of_nat m); (LReg 21, Z.of_nat m); (LReg 23, 104 * Z.of_nat m);
  (LReg 13, Z.max (Z.of_nat at0) 33);
  (LReg 14, Z.lnot (e_pp (x_e cx) + 0x401c) - 104 * Z.of_nat m)]) /\
rs_role_at cx rec W2 mem2 /\ rs_scan_inv rec at0 /\ rs_chk_rec cx rec /\
(at0 <= m < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None).

(* ---------------- KM = 0x82370: entry m is a key and entry m + 1 is its value ----------
   a0 is the key's body address (0x82320), a2 = s5 = m + 1 the value's index and s7 = 104 (m + 1) (the latch's
   0x8232c .. 0x82334); the next `at` m + 2 is made by the cut's own `addiw s8,a2,1`; a7, t0, t1, t2 and t3 are
   spilled around the string compare (0x82384 .. 0x82394) and reloaded after it. *)
Definition rs_cut_KM (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec) (at0 m : nat) (kb : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_scan cx rec ++
 [(LReg 10, e_pp (x_e cx) + 0x401c + 104 * Z.of_nat m); (LReg 12, Z.of_nat m + 1); (LReg 21, Z.of_nat m + 1);
  (LReg 23, 104 * (Z.of_nat m + 1))]) /\
rs_role_at cx rec W2 mem2 /\ rs_scan_inv rec at0 /\ rs_chk_rec cx rec /\
(at0 <= m)%nat /\ (m + 1 < length (ents rec))%nat /\
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) (Ent 0 0 [])) = None) /\
key_of (nth m (ents rec) (Ent 0 0 [])) = Some kb.

(* ---------------- the two checks the answer selects, and the tail ----------------
   ABS 0x8245c: no pair of the record has the role key (or there is no params Struct: `beqz a0` 0x82210), so the
   answer is (None, 0) and check_absent runs; rc = 0 is in R+0x158. MAL 0x824f8: the answer is (None, -1) (the NULL
   flag `bnez s5` 0x821d8, no Props object, or a value no reader takes: 0x82404 ..) and check_malformed runs; it
   carries s9 = rc, s6 = pp, s8 = the flags byte and s10 = F, which the tail reads without reloading them. T 0x82504:
   the check is done (or skipped, for a corrupted record: `bnez a0` 0x821d0) and the tail runs the answer and the two
   refusal codes; its four registers are set on every path into it (0x821c0 / 0x823cc / 0x82460, 0x821cc / 0x823f8 /
   0x82470, 0x82198 / 0x823e4 / 0x82474, 0x82170 / 0x823f4 / 0x8246c). *)
Definition rs_cut_ABS (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LCell XR 0x158, 0); (LCell XR 0x38, e_F (x_e cx)); (LCell XR 0x140, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2 /\ fst (rs_PA cx rec) = None /\ snd (rs_PA cx rec) = 0.
Definition rs_cut_MAL (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 25, -1); (LReg 22, e_pp (x_e cx)); (LReg 24, e_fl (x_e cx)); (LReg 26, e_F (x_e cx));
                 (LCell XR 0x38, e_F (x_e cx)); (LCell XR 0x140, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2 /\ fst (rs_PA cx rec) = None /\ snd (rs_PA cx rec) = -1.
Definition rs_cut_T (cx : rs_scx) (fx2 : YK11.FPState) (rec : pod_rec)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx cx W2 mem2 regs2
(rs_L_chk cx ++ [(LReg 25, snd (rs_PA cx rec)); (LReg 22, e_pp (x_e cx)); (LReg 24, e_fl (x_e cx));
                 (LReg 26, e_F (x_e cx)); (LCell XR 0x38, e_F (x_e cx)); (LCell XR 0x140, e_pp (x_e cx))]) /\
rs_role_at cx rec W2 mem2.

(* ---------------- C4 = 0x82570: the checks are done ----------------
   This cut IS role_check_contract's post, at the pc its contract names (hi_c4 role_himg_B). *)
Definition rs_cut_C4 (cx : rs_scx) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_core cx (rs_E2 cx) ly2 S2 W2 regs2 mem2 md2 /\
rl_fxk [10; 13; 14; 15] fx fx2 /\
rl_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L4 role_himg_B) /\
rs_fsh_at cx W2 mem2 rs_PB.

(* ===================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   ===================================================================================================
   One per cut, with the LOOP INDEX as an argument (and never under the inner quantifier), so that the latch of a
   loop can hand the head its next index and the closure is an induction on the index, not a circular hypothesis:
   rs_from_N .. (S i) is what the property loop's latch gives, rs_from_C .. i (S k) what the pod loop's latch gives.
   A piece lemma is `<its start premises> -> <the continuations of its end cuts> -> <the continuation of its start
   cut>`, so the proof of one piece takes the other pieces' continuations as hypotheses and never sees their
   proofs. POST is generic. *)
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
SRr segs W2 (cfg_at segs (hi_c2 role_himg_B) regs2 mem2 md2) POST.
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
SRr segs W2 (@cfg_at fx2 segs (hi_c4 role_himg_B) regs2 mem2 md2) POST.
End f.

(* ===================================================================================================
   THE PIECE STATEMENTS, one or more per group W3a .. W11b of the two middle segments (the harness-level segments
   and the malloc(pod) step are stated in lib/AU/RPgHarn.v)
   =================================================================================================== *)
(* W3a: C1 -> the object's header (pod.h:384-395): the NULL test (dead), the block's memset, the two header reads,
   the top size word (its capacity arm 0x803c4 is dead: len = 0 after the memset), and the header of this shape. Its
   start is the segment's own start state, which is role_build_contract's premise set. *)
Definition rs_start_M01 (cx : rs_scx) (rest : list byte) : Prop :=
rs_pre cx /\
rl_fsh segs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) (hi_shA role_himg_B) /\
rl_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L1 role_himg_B) /\
e_len (x_e cx) = rl_len rest /\ rs_in cx rest.
Definition rs_piece_W3a_stmt : Prop :=
forall cx POST rest,
rs_start_M01 cx rest -> rs_from_B7 cx POST rest -> rs_from_BO cx POST rest ->
SRr segs (x_W cx) (cfg_at segs (hi_c1 role_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
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
(* W4: one property's selector, its shape-7 body (e into scope, memset(e.body) 0x80800, type and size, the call
   pod_write_ent(pp, e) 0x80818, e out of scope; it enters the latch at its second entry), its key, and the loop's
   latch (from its two entries). *)
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
(* W5: the Int-7 value pod (e42 into scope, memset(e42.body + 4) 0x81be8, its body, the call pod_write_ent(pp, e42)
   0x81c08, e42 out of scope; it enters the latch at its second entry, where image A's entered the first), the params
   Struct's header and count, and its close (pod.h:412-438). *)
Definition rs_piece_W5_int_stmt : Prop :=
forall cx POST rest i,
rs_start_M01 cx rest -> rs_from_LATCH7 cx POST rest i -> rs_from_SELI cx POST rest i.
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
(* W8: the capacity guard (`bltu a1,a0` 0x818fc), the call pod_write_ent(pp, e62) 0x81908, the record copy
   (pod.h:428-432, memcpy 0x81970) and e62 out of scope, then the pod loop's latch. *)
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
(* W11a: the second block's fill, role := 0x5a, the parse, the record's two tests and the two scan loops. Its start
   is role_check_contract's premise set. The head leaves to E (uncorrupted record, flags bit 0 clear), MAL
   (uncorrupted, bit 0 set: the parse of NULL answers -1) and T (corrupted: no check); unlike image A's, it never
   reaches ABS (B tests is_props after E). *)
Definition rs_start_M02 (cx : rs_scx) (inp : list byte) : Prop :=
rs_pre cx /\
rl_fsh segs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) (hi_shA role_himg_B) /\
rl_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L3 role_himg_B) /\
e_len (x_e cx) = rl_len inp /\
rs_pp_at cx (x_W cx) (x_memc cx) (pp_bytes (fst (pod_build inp))) /\
e_pod (x_e cx) <> 0 /\ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx)) /\
YK0o.frm_zero (@fp_csr fx).
Definition rs_piece_W11a_head_stmt : Prop :=
forall cx POST inp,
rs_start_M02 cx inp -> rs_from_E cx POST -> rs_from_MAL cx POST -> rs_from_T cx POST ->
SRr segs (x_W cx) (cfg_at segs (hi_c3 role_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
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
(* W11b: the key compare (strcmp 0x82398), the value's two readers (the Int arm, the Float arm with pod_nearest
   0x824d0 at R+0x178) and check_role, the absent and malformed checks, and the tail (changes, apply_state,
   check_answer, refuse_code twice and check_code). *)
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
