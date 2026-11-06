(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgCSpec.v at origin/ossv/recipes 6ebe35ba632
   (the Section form of its lines 32-164) and proofs/libreac/fuzz_grant/lib/A/ACfn.v at origin/ossv/recipes
   2638f9235e2 (lines 50-61 and 87-116: tfib_lib_post_x, tfib_lib_pre_xf, tfib_lib_contract_xf) for
   reac-pw/fuzz_role, image A and image B. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCSpec.v at
   0de5d668c87 for reac-pw/fuzz_headamp, image A (fuzz_headamp.asan) and image B (fuzz_headamp.asan-ubsan): module
   paths changed, the rl_ prefix renamed to hd_, role's ten callee contracts replaced by headamp's ten (the parse,
   its 8-byte wrapper and the eight check functions), and role's two middle-segment contracts replaced by headamp's
   five. What differs from role's file, and why:
   - FOUR live blocks, freed LIFO (pp 19744 bytes, pod len | 1, out 3 (cap + 1), first 3 max(rc, 0) | 1), where role
     has two. The harness walk takes the allocator's operations as Section hypotheses at the malloc / free call
     sites, as role's does; a segment contract names the blocks it needs through hd_fresh_block.
   - FIVE middle segments between the allocator calls, with the names and the cut set of headamp's plain / UBSan
     walk (the plain walk's cuts ENTRY, K13044, K1404c, K14080, K14168, K141b4, RET): headamp_build_contract (M01, the
     inlined pod.h builder, the plain walk's evt headamp_build), headamp_dup_contract (M02, fuzz_dup of the pod),
     headamp_check_contract (M03, the plain walk's evt headamp_check: the parse, the first three checks, expect_of
     with the inlined pod_nearest, the last four checks), headamp_first_contract (M04a, fuzz_dup of out) and
     headamp_plain_contract (M04b, the second parse and check_plain). E01 (ENTRY to the malloc of pp) and X01 (the
     four frees to RET) are NOT contract texts here, for the reason role's E01 and X01 are not: each of them makes
     or ends blocks and the frame for locals, so its post is not of the segment shape (the block list and the frame
     list change); they are proved inside the harness walk, where the allocator and frame operations are Section
     hypotheses (knock's APgMain0 / APgMain7 precedent). Image B's walks consume the same five texts. Image B's M01
     also calls pod_write_ent (B 0x84634, from 0x81538, 0x82648 and 0x8295c; image A inlines it): it has no contract
     text here and is walked inside M01, as role's image B walks its twin.
   - headamp's parse writes a heap block (out), a 12-byte struct in the frame for locals (res) and the errno cell,
     and calls the strtol and strncmp wrappers, which role's program does not; so the parse contract carries the
     stack-guard cells, the errno cell and the four read-only strings those wrappers read.
   - role's pod_nearest contract has no counterpart: headamp inlines pod_nearest into M03 (no symbol, lo = 0,
     hi = 255 folded in), so its steps are part of headamp_check_contract.
   The ASan texts restate the plain contracts of lib/Prog at 87a4cb29502 (
   reac_headamp_prop_parse_result_c.v, reac_headamp_prop_parse_c.v, check_*_c.v) over the same shared model
   (lib/Pod/Headamp.v, lib/Spec/HeadBytes.v) and must not weaken them: each ASan contract's premises are the plain
   ones plus the shadow facts the instrumented checks read, and each post states the plain post's memory and
   register facts in the reader form of this engine. *)
(* The ASan-level contracts of reac-pw/fuzz_headamp's own functions. IMAGE-INDEPENDENT: no image module is
   Required; segs, the symbol record B, the meter MT, the sink K, every entry address, string address, table
   address and constant cell is a Section variable, a parameter or a field of the record hd_himg, so image A
   (fuzz_headamp.asan) and image B (fuzz_headamp.asan-ubsan) instantiate the same texts. Statement text only: no
   function is proved here. Proves no function (kind: statement text).

   Each callee contract has knock's form (APgCSpec.v): the caller's journal from its own entry to the call
   (ajournal ... lyc Sc W memc mdc k), the call's registers, the stack bound sp0 - STK <= sp - T_f, and the
   function's own premises; its post (hd_post) returns to ra with the caller's journal extended, the callee-saved
   registers kept, the frames, blocks, I/O state and meter as at the call, and every byte outside the callee's
   stack [sp - T_f, sp) and the bytes E it writes for its caller unchanged.

   Measured on image A (unstripped fuzz_headamp.asan sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a) and image B (unstripped
   fuzz_headamp.asan-ubsan sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff), capstone 5.0.7
   over the two files:
   - frames: image A's eight check functions each take `addi sp,sp,-0x10` (check_no_overrun 0x83e3c, check_count
     0x83ee8, check_cells_valid 0x83f7c, check_object 0x8405c, check_cells 0x84148, check_keys 0x842e8,
     check_refusal 0x84368, check_plain 0x843e8); image B's check_cells (0x841c0) takes `addi sp,sp,-0x20` and
     saves ra, s0, s1 in it, so the common bound T_check_STK is 32. None calls anything on the path that returns;
     the abort path of each (the no-return helper and abort) is behind a test the premises make false. Image B's
     check functions also carry alignment and pointer-overflow checks (B 0x83f48, 0x83ffc, 0x840cc, 0x8410c,
     0x841d4, 0x8422c, 0x84240, 0x84244, 0x843b4, 0x84448, 0x844fc, 0x84500), which the 4-alignment, index and
     address-bound premises below exclude, as the plain UBSan texts (lib/U/Prog/check_*_c.v) state them.
     reac_headamp_prop_parse_result (A 0x845b4) takes `addi sp,sp,-0x100` and then `andi sp,sp,-0x20`, so it uses at
     most 0x100 + 0x20 bytes below its caller's sp, and below that the deepest of its callees: the strtol wrapper
     (3 ESTACK, plugin-hostd/fuzz_command lib/A/Rt/RtNumber.v astrtol_realizes), the strncmp wrapper and the strcmp
     wrapper (2 ESTACK each). reac_headamp_prop_parse (A 0x845ac) is `mv a3,zero; j` into it: no frame.
   - float registers: the parse writes fa4 and fa5 (f14, f15: fld, fcvt.d.s, fadd.d, fcvt.d.l at A
     0x84cb4-0x84ce8) and saves and restores fs0 (fsd 0x845ec / fld 0x847a0); it accrues fflags and writes no
     rounding mode; its fadd.d and fcvt.d.l read the dynamic rounding mode, hence the frm_zero premise. The eight
     check functions use no float instruction. In the entry function, M03 writes fs0, fs1, fs2 (f8, f9, f18:
     fmv.w.x A 0x83030 and 0x83044, flw A 0x834a4), on image B also fs3 (f19: fmv.w.x B 0x830e0, the 2^63 bound of
     its float-cast check, restored only by the epilogue), and fa0 (f10: fmv.s A 0x834c0, the argument of the
     soft-float call), and the parse's fa4 and fa5; every other segment leaves the float state as it is.
   - the strtol and strncmp wrappers are NOT restated here: their texts are the ones their port sources state,
     plugin-hostd/fuzz_command lib/A/Rt/RtNumber.v astrtol_realizes (at 2d2ff01bb6f2) and
     reac-pw/fuzz_pin lib/A/PPgWrap.v astrncmp_realizes (with its
     len + 8 range), and the strcmp and strlen wrappers' are fuzz_identity's astrcmp_realizes / astrlen_realizes.
     Each walk takes the one it calls as a Section hypothesis at its own image's trampoline (image A:
     __interceptor_trampoline_strtol 0x41c28, _strncmp 0x41ba4, _strcmp 0x41ba0, _strlen 0x41b98; image B 0x41ca8,
     0x41c24, 0x41c20, 0x41c18). Restating them here would be a second copy of a text that already has one.
     F1: decided (d); the parse walk carries ARH of lib/A/HPgHole.v between the prologue's poison and the
     epilogue's unpoison; hd_parse_result_specX is unchanged (the hole opens after entry and closes before ret).
     The parse's walk also takes api_env segs B (YCbq.v errno_low's Section hypothesis) for the errno cell.
   - the soft-float routines (__extendsftf2, __floatditf, __subtf3, __getf2, __lttf2; image A 0x85248, 0x853a4,
     0x854c8, 0x84ffc, 0x84f34) keep the trunk's CJ contracts; M03's walk takes them as it takes the wrappers.
   - the parse writes the shadow bytes of its OWN real-stack frame: it marks the 64 bytes [sp + 0x40, sp + 0x80)
     of that frame (the strtol end-pointer cell among them) at image A 0x84648 .. 0x84668, brings the end-pointer
     cell into scope (0x849f8) and out again (0x84aec, 0x84b2c), and writes the eight shadow bytes back to 0
     before it returns (0x84744 .. 0x84760). The caller's stack shadow is therefore the same at the return as at
     the call: those shadow bytes are outside the parse's effect set E, so hd_post's memory clause states exactly
     that.
   - abort paths: each check function calls the no-return helper and abort only on its failure branch (image A
     0x83eb8, 0x83f4c, 0x84048, 0x840f8, 0x842a8, 0x84360, 0x843e0, 0x84518); every error-path call (an
     __asan_report_ entry) sits behind an instrumented check that the premises make pass. Reaching ra at all is the
     content of a check's contract. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================= the stack each callee uses below its caller's sp (both images) ======================= *)
(* The parse's own frame: `addi sp,sp,-0x100` and then `andi sp,sp,-0x20`. *)
Definition T_PARSE_FRAME : Z := 0x100 + 0x20.
(* Below it, the deepest of its callees: the strtol wrapper's 3 ESTACK (the strncmp and strcmp wrappers take 2). *)
Definition T_parse_STK : Z := T_PARSE_FRAME + 3 * ESTACK.
(* Every check function takes a frame and calls nothing on the path that returns. The bound is the larger of the
   two images' frames: image A's eight check functions each take `addi sp,sp,-0x10`; image B's check_cells
   (0x841c0) takes `addi sp,sp,-0x20` and saves ra, s0 and s1 at sp+0x18, sp+0x10 and sp+8 (pinned
   fuzz_headamp.asan-ubsan 53edda9bdeeb). *)
Definition T_check_STK : Z := 32.

(* The parse's first argument: the pod bytes, or NULL when the harness's null flag is set
   (fuzz_headamp.c:333; Pod/Headamp.v parse_props takes the option). *)
Definition hd_props (null : Z) (bs : list byte) : option (list byte) := if null =? 0 then Some bs else None.
(* A block live now that was made since the journal's start: the journal's own write right on every byte of it
   (HPgBase.hd_fresh_awr). The harness's four blocks are of this kind inside every middle segment. *)
Definition hd_fresh_block (bl0 blc : list (Z * Z)) (p n : Z) : Prop :=
p <> 0 /\ In (p, n) blc /\ ~ In (p, n) bl0.

(* ===================== LLVMFuzzerTestOneInput's five middle segments: what each image fills =====================
   The cuts are the plain walk's, one at each allocator return and one at each allocator
   call: C1 after malloc(pp); C2 the `jal` of malloc(pod); C3 after it; C4 the `jal` of malloc(out); C5 after it;
   C6 the `jal` of malloc(first); C7 after it; C8 after the memcpy that fills first (the plain walk's M04 split);
   C9 before the `jal` of free(first). An image gives:
   - hi_cid: the side-stack class of the frame for locals (image A 4: `addi a0,zero,0x280` + the class-4 call at
     0x80c38 / 0x80c3c; image B 4 as well, with its own request);
   - hi_c1 .. hi_c9: the nine pcs;
   - hi_rsz: the real frame's size below the entry sp S (R + hi_rsz <= S, R the 32-aligned base in s1);
   - hi_L1 .. hi_L9: the live values at C1 .. C9 (HPgBase.hd_cut);
   - hi_shA: the shadow bytes of the frame for locals after the prologue, which M01 and M02 leave as they are;
     hi_shB: the same with the granules of res in scope (x has gone out of scope again), which M03 leaves;
   - hi_w1 .. hi_w5: the ranges M01 / M02 / M03 / M04a / M04b write besides the block each fills and the callees'
     stacks (frame objects, their shadow bytes, real-frame cells);
   - hi_rz: real-frame ranges (offset from R, length) whose shadow bytes the code checks (image A: the 8 bytes at
     R+0x148, the parts[1] store checked at 0x81a84 .. 0x81a98);
   - hi_globs: the registered globals (address, size) whose bytes the runtime marked usable and the segments read;
   - hi_strs / hi_cells: the strings (hd_cstr) and 8-byte constant cells (hd_ro_cells) the segments and their
     callees read;
   - hi_akey / hi_aph / hi_apad / hi_asens: the parse's own four literals ("reac.headamp.", "phantom", "pad",
     "sens"); hi_hkey / hi_hph / hi_hpad / hi_hsens: the harness's four (expect_of compares with its own copies);
   - hi_dcs: the parse's read-only doubles, which it loads without a shadow check (image A: 0.5 and 256.0; image B
     also the two float-cast bounds at 0x103f0 and 0x10358);
   - hi_gotw / hi_guard: the stack-guard cells musl's strtol reads through the strtol wrapper (the GOT word and the
     guard it points to). *)
Record hd_himg := HDImg {
hi_cid : Z;
hi_c1 : Z; hi_c2 : Z; hi_c3 : Z; hi_c4 : Z; hi_c5 : Z; hi_c6 : Z; hi_c7 : Z; hi_c8 : Z; hi_c9 : Z;
hi_rsz : Z;
hi_L1 : list (hd_loc * hd_x); hi_L2 : list (hd_loc * hd_x); hi_L3 : list (hd_loc * hd_x);
hi_L4 : list (hd_loc * hd_x); hi_L5 : list (hd_loc * hd_x); hi_L6 : list (hd_loc * hd_x);
hi_L7 : list (hd_loc * hd_x); hi_L8 : list (hd_loc * hd_x); hi_L9 : list (hd_loc * hd_x);
hi_shA : list Z; hi_shB : list Z;
hi_w1 : list (hd_x * Z * Z); hi_w2 : list (hd_x * Z * Z); hi_w3 : list (hd_x * Z * Z);
hi_w4 : list (hd_x * Z * Z); hi_w5 : list (hd_x * Z * Z);
hi_rz : list (Z * Z);
hi_globs : list (Z * Z);
hi_strs : list (Z * list Z);
hi_cells : list (Z * Z);
hi_akey : Z; hi_aph : Z; hi_apad : Z; hi_asens : Z;
hi_hkey : Z; hi_hph : Z; hi_hpad : Z; hi_hsens : Z;
hi_dcs : list (Z * Z);
hi_gotw : Z; hi_guard : Z }.
(* The stack the segments' callees may use below R (the harness sp throughout the five segments): the allocator's
   ASTACK, so that the allocator calls at the segment ends fit too; it bounds every callee of a middle segment
   (__asan_memset / __asan_memcpy ESTACK, the string wrappers 2 ESTACK, the strtol wrapper 3 ESTACK, the parse
   T_parse_STK = 12576, the check functions T_check_STK = 32). *)
Definition T_SEG_STK : Z := ASTACK.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
(* The two stack-guard cells musl's strtol reads: the GOT word holds the guard's address and the guard is
   readable (plugin-hostd/fuzz_command lib/A/Rt/RtDefs.v aguard_ok, in this engine's reader form). *)
Definition hd_guard_ok (rd : reader) (gotw guard : Z) : Prop :=
rdword rd gotw = Some guard /\ (exists can, rdword rd guard = Some can).
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== the post of a callee ===================================== *)
(* The call returns to ra (getr regs 1) at some float state fx2 with FX fx2, its journal extends the caller's
   (k events: none of these callees allocates), the callee-saved registers and ra are as at the call (every plain
   post of lib/Prog keeps ra), and every byte outside its stack [sp - T, sp) and outside E is as at the call. R is
   what the function computes. *)
Definition hd_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\ FX fx2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ getr regs2 (Z_to_bv 5 1) = getr regs (Z_to_bv 5 1) /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
R W2 regs2 mem2.

(* The premises every callee contract shares (knock's, without the frame-chain premise: no callee here records a
   call trace): the caller's journal, the call's ra / gp / tp, and the callee's stack T inside the caller's
   stack window. *)
Definition hd_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - T /\ spZ regs <= sp0 /\
st_nev S + k <= EV_MAX.

(* A range the callee only reads: it is outside the callee's own stack window, so the callee's frame store does
   not meet it. *)
Definition hd_off_stack (regs : bvmap 5 word) (T p n : Z) : Prop :=
forall x, p <= x < p + n -> ~ (spZ regs - T <= x < spZ regs).
(* The bytes [p, p + n) lie in application memory outside the image: AR's laws al_blocks / al_frames with
   al_client_img give it for a live block or a frame of the caller's state. The check functions' instrumented loads
   need it: the engine's token load and branch ask the checked range below 2^47 (so its shadow byte stays away
   from the callee's ra save slot) and apart from the image's cells it reads itself (the shadow-offset GOT word and
   the shadow-offset cell). *)
Definition hd_app_rng (p n : Z) : Prop := in_app p n /\ (forall x, p <= x < p + n -> ~ in_img segs x).
(* Where a check function reads two ranges in one straight line (check_object res and x, check_cells out and x,
   check_keys / check_refusal res and x, check_plain out and first), its text also states the two ranges apart:
   the engine holds both as symbolic regions at once, and its memory invariant asks their extents disjoint. *)

(* ====================== check_no_overrun(guard) (fuzz_headamp.c:183-192) ======================
   Returns exactly when the three bytes at a0 (guard->ch, ->param, ->value, read by three instrumented `lbu`) are
   the harness's guard byte 0xa5; else it aborts. *)
Definition hd_check_no_overrun_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (g : Z),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 g ->
garr8 segs (mrestrict (w_H W) memc) g (hd_zbytes (repeat GUARD_BYTE 3)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF g 3 ->
hd_off_stack regs T_check_STK g 3 -> hd_app_rng g 3 ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ====================== check_count(rc, cap, res) (fuzz_headamp.c:194-205) ======================
   Returns exactly when -1 <= rc <= cap and, for rc >= 0, res->n = rc and res->keys >= rc, the two words read by
   instrumented `lw` at res and res + 4 (for rc = -1 it reads no memory). *)
Definition hd_check_count_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (rcc cap keys r : Z),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 rcc -> getr regs 11 = w64 cap -> getr regs 12 = w64 r ->
-1 <= rcc <= cap -> cap < 2 ^ 31 ->
(0 <= rcc -> r mod 4 = 0 /\
 val_mem segs (mrestrict (w_H W) memc) r 4 (rcc mod 2 ^ 32) /\
 val_mem segs (mrestrict (w_H W) memc) (r + 4) 4 (keys mod 2 ^ 32) /\ rcc <= keys < 2 ^ 31 /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF r 8 /\ hd_off_stack regs T_check_STK r 8 /\ hd_app_rng r 8) ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ==================== check_cells_valid(out, rc) (fuzz_headamp.c:207-219) ====================
   The loop runs rc times over the 3-byte cells at out, each read by three instrumented `lbu`, and returns exactly
   when rc <= 0 or every one of the rc cells is valid (Pod/Headamp.v cell_valid). *)
Definition hd_check_cells_valid_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (rcc o : Z) (cs : list Headamp.cell),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 o -> getr regs 11 = w64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 ->
(0 < rcc ->
 Z.of_nat (length cs) = rcc /\ Forall Headamp.cell_valid cs /\ 0 <= o /\ o + 3 * rcc <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) o (hd_zbytes (ha_cells_bytes cs)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF o (3 * rcc) /\
 hd_off_stack regs T_check_STK o (3 * rcc) /\ hd_app_rng o (3 * rcc)) ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ====================== check_object(rc, res, x) (fuzz_headamp.c:221-237) ======================
   Returns exactly when (rc = -1) and (x->rc = -1) agree and, for rc = -1, the three words of res are 0
   (REFUSE_NONE = 0); x->rc and, in that case, res are read by instrumented `lw`. *)
Definition hd_check_object_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (rcc xrc r x : Z),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 rcc -> getr regs 11 = w64 r -> getr regs 12 = w64 x ->
- 2 ^ 31 <= rcc < 2 ^ 31 -> - 2 ^ 31 <= xrc < 2 ^ 31 -> (rcc = -1 <-> xrc = -1) ->
val_mem segs (mrestrict (w_H W) memc) x 4 (xrc mod 2 ^ 32) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF x 4 -> hd_off_stack regs T_check_STK x 4 ->
hd_app_rng x 4 -> x mod 4 = 0 ->
(rcc = -1 -> r mod 4 = 0 /\
 garr8 segs (mrestrict (w_H W) memc) r (hd_zbytes (ha_res_bytes 0 0 0)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF r 12 /\ hd_off_stack regs T_check_STK r 12 /\
 hd_app_rng r 12 /\ (r + 12 <= x \/ x + 4 <= r)) ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ======================= check_cells(out, rc, x) (fuzz_headamp.c:239-259) =======================
   Returns exactly when rc = x->rc and, for i < rc, out[i]'s three bytes (instrumented `lbu`) equal x->cell[i]'s
   three ints (instrumented `lw`), field by field. rc <= 10 because image B's copy checks the index of
   x->cell[10] (B 0x84240); x mod 4 = 0 and the address bounds exclude image B's alignment and pointer-overflow
   checks, as the plain UBSan text (lib/U/Prog/check_cells_c.v) states them. *)
Definition hd_check_cells_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (rcc o x : Z) (cs : list Headamp.cell),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 o -> getr regs 11 = w64 rcc -> getr regs 12 = w64 x -> - 2 ^ 31 <= rcc <= 10 ->
val_mem segs (mrestrict (w_H W) memc) x 4 (rcc mod 2 ^ 32) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF x 4 -> hd_off_stack regs T_check_STK x 4 ->
hd_app_rng x 4 -> x mod 4 = 0 ->
(0 < rcc ->
 Z.of_nat (length cs) = rcc /\ Forall cell_bytes_ok cs /\
 0 <= o /\ o + 3 * rcc <= 2 ^ 63 /\ 0 <= x /\ x + 4 + 12 * rcc <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) o (hd_zbytes (ha_cells_bytes cs)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF o (3 * rcc) /\
 hd_off_stack regs T_check_STK o (3 * rcc) /\ hd_app_rng o (3 * rcc) /\
 garr8 segs (mrestrict (w_H W) memc) (x + 4) (hd_zbytes (x_cells_bytes cs)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (x + 4) (12 * rcc) /\
 hd_off_stack regs T_check_STK (x + 4) (12 * rcc) /\ hd_app_rng (x + 4) (12 * rcc) /\
 (o + 3 * rcc <= x \/ x + 4 + 12 * rcc <= o)) ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ============ check_keys(res, x) and check_refusal(res, x) (fuzz_headamp.c:261-285) ============
   Each returns exactly when the word at res + off and the word at x + xoff are the same four bytes, both read by
   an instrumented `lw`: off / xoff = 4 / X_KEYS_OFF for check_keys, 8 / X_RF_OFF for check_refusal. *)
Definition hd_check_word_specX (a off xoff : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (r x v : Z),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 r -> getr regs 11 = w64 x -> r mod 4 = 0 -> x mod 4 = 0 ->
val_mem segs (mrestrict (w_H W) memc) (r + off) 4 v ->
val_mem segs (mrestrict (w_H W) memc) (x + xoff) 4 v ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (r + off) 4 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (x + xoff) 4 ->
hd_off_stack regs T_check_STK (r + off) 4 -> hd_off_stack regs T_check_STK (x + xoff) 4 ->
hd_app_rng (r + off) 4 -> hd_app_rng (x + xoff) 4 ->
(r + off + 4 <= x + xoff \/ x + xoff + 4 <= r + off) ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).
Definition hd_check_keys_specX (a : Z) : Prop := hd_check_word_specX a 4 X_KEYS_OFF.
Definition hd_check_refusal_specX (a : Z) : Prop := hd_check_word_specX a 8 X_RF_OFF.

(* ================= check_plain(plain, rc, out, first) (fuzz_headamp.c:297-309) =================
   Returns exactly when plain = rc and, for rc > 0, the 3 rc bytes at out and at first are equal, read pairwise by
   instrumented `lbu`. *)
Definition hd_check_plain_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (rcc o fp : Z) (w : list Z),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 rcc -> getr regs 11 = w64 rcc -> getr regs 12 = w64 o -> getr regs 13 = w64 fp ->
- 2 ^ 31 <= rcc < 2 ^ 31 ->
(0 < rcc ->
 Z.of_nat (length w) = 3 * rcc /\ 0 <= o /\ o + 3 * rcc <= 2 ^ 63 /\ 0 <= fp /\ fp + 3 * rcc <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) o w /\ garr8 segs (mrestrict (w_H W) memc) fp w /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF o (3 * rcc) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF fp (3 * rcc) /\
 hd_off_stack regs T_check_STK o (3 * rcc) /\ hd_off_stack regs T_check_STK fp (3 * rcc) /\
 hd_app_rng o (3 * rcc) /\ hd_app_rng fp (3 * rcc) /\ (o + 3 * rcc <= fp \/ fp + 3 * rcc <= o)) ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ============ reac_headamp_prop_parse_result(props, out, max, res) (reac_headamp_prop.c:108-182) ============
   a0 = 0 (the harness's null flag) or the pod at P; the answer is Pod/Headamp.v's parse_props on those bytes with
   max = cap (the plain contract's parse_props (parse_arg null bs) cap,
   lib/Prog/reac_headamp_prop_parse_result_c.v). It writes: the n cells at out, three bytes each (instrumented
   `sb`, so [out, out + 3 n) is marked usable and n <= cap, the guard cell out[cap] untouched); the three words of
   res when res <> 0 (instrumented `sw`); the errno cell, through musl's strtol inside the strtol wrapper; its own
   stack. Every read of the pod is an instrumented load inside [P, P + len); the key compares are the strncmp
   wrapper against the literal "reac.headamp." at akey and up to three strcmp wrapper calls against "phantom",
   "pad" and "sens" at aph / apad / asens; the channel is read by the strtol wrapper, whose end pointer is a cell
   of the parse's own frame; the doubles it compares with (image A two, image B four) are read from read-only data without a shadow check
   (dcs). The three wrappers also read the read-only image bytes and the stack-guard cells, hence arodata_okP and
   hd_guard_ok. *)
Definition hd_parse_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(O R : Z) (o : answer) : world segs -> config -> Prop :=
hd_post STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc
(hd_fxk [14; 15] fx)
(fun x => (O <= x < O + 3 * Z.of_nat (length (ans_cells o))) \/ (R <> 0 /\ R <= x < R + 12) \/
 (as_errno B <= x < as_errno B + 4))
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (ans_rc o) /\
garr8 segs (mrestrict (w_H W2) mem2) O (hd_zbytes (ha_cells_bytes (ans_cells o))) /\
(R <> 0 -> garr8 segs (mrestrict (w_H W2) mem2) R (hd_zbytes (ans_res_bytes o))) /\
(exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev')).

Definition hd_parse_args (STK sp0 : Z) (ly : alayout) (S : astate) (lyc : alayout) (Sc : astate)
(W : world segs) (memc : word -> option byte) (own : list (Z * Z)) (regs : bvmap 5 word)
(RLO RHI : Z) (akey aph apad asens gotw guard : Z) (dcs : list (Z * Z))
(null P O R cap ev : Z) (bs : list byte) : Prop :=
(null = 0 ->
 0 < P /\ P mod 16 = 0 /\ 8 <= Z.of_nat (length bs) <= 16384 /\ Z.of_nat (length bs) mod 8 = 0 /\
 Spa.u32_at bs 0 = Z.of_nat (length bs) - 8 /\
 P + Z.of_nat (length bs) <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) P (hd_zbytes bs) /\
 In (P, Z.of_nat (length bs)) (ablocks B lyc Sc) /\
 (P + Z.of_nat (length bs) <= O \/ O + 3 * (cap + 1) <= P) /\
 (R = 0 \/ P + Z.of_nat (length bs) <= R \/ R + 12 <= P) /\
 (P + Z.of_nat (length bs) <= as_errno B \/ as_errno B + 4 <= P) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF P (Z.of_nat (length bs)) /\
 shadow_hull_vis (aview segs (w_H W) memc) P (Z.of_nat (length bs)) /\
 amem_range P (Z.of_nat (length bs) + 8) /\
 hd_off_stack regs T_parse_STK P (Z.of_nat (length bs))) /\
0 <= cap <= 9 /\
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) O (3 * (cap + 1)) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF O (3 * (cap + 1)) /\
hd_off_stack regs T_parse_STK O (3 * (cap + 1)) /\
(R = 0 \/ (hd_wcell STK sp0 lyc own (spZ regs) T_parse_STK R 12 /\ R mod 4 = 0 /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF R 12)) /\
hd_cstr segs (w_H W) memc akey (hd_zbytes Headamp.HA_PREFIX) /\
hd_cstr segs (w_H W) memc aph (hd_zbytes Headamp.NAME_PHANTOM) /\
hd_cstr segs (w_H W) memc apad (hd_zbytes Headamp.NAME_PAD) /\
hd_cstr segs (w_H W) memc asens (hd_zbytes Headamp.NAME_SENS) /\
hd_ro_cells segs (w_H W) memc dcs /\
hd_guard_ok (aview segs (w_H W) memc) gotw guard /\
rd32 (aview segs (w_H W) memc) (as_errno B) ev /\
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) /\
YK0o.frm_zero (@fp_csr fx).

Definition hd_parse_result_specX (a : Z) (RLO RHI akey aph apad asens gotw guard : Z) (dcs : list (Z * Z)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(null P O R cap ev : Z) (bs : list byte),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
0 <= null <= 1 ->
getr regs 10 = w64 (if null =? 0 then P else 0) -> getr regs 11 = w64 O ->
getr regs 12 = w64 cap -> getr regs 13 = w64 R ->
hd_parse_args STK sp0 ly S lyc Sc W memc own regs RLO RHI akey aph apad asens gotw guard dcs
  null P O R cap ev bs ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_parse_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc O R
 (Headamp.parse_props (hd_props null bs) cap)).

(* ============== reac_headamp_prop_parse(props, out, max) (reac_headamp_prop.c:102-106) ==============
   `mv a3,zero; j reac_headamp_prop_parse_result`: no frame, ra kept, so the parse returns to this function's
   caller. Its contract is the one above at R = 0, whatever a3 holds on entry. *)
Definition hd_parse_specX (a : Z) (RLO RHI akey aph apad asens gotw guard : Z) (dcs : list (Z * Z)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(null P O cap ev : Z) (bs : list byte),
hd_pre STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
0 <= null <= 1 ->
getr regs 10 = w64 (if null =? 0 then P else 0) -> getr regs 11 = w64 O -> getr regs 12 = w64 cap ->
hd_parse_args STK sp0 ly S lyc Sc W memc own regs RLO RHI akey aph apad asens gotw guard dcs
  null P O 0 cap ev bs ->
SRr segs W (cfg_at segs a regs memc mdc)
(hd_parse_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc O 0
 (Headamp.parse_props (hd_props null bs) cap)).

(* ====================== LLVMFuzzerTestOneInput's five middle segments ======================
   A segment runs inside the harness's own journal (from its entry: sp0 = S, own = the harness's side-stack
   frame); it ends at a fixed pc (not at ra), with sp, gp, tp as at its start, the frames, blocks, I/O state and
   meter as at its start, and every byte outside the callees' stack [R - T_SEG_STK, R), the image's write ranges
   and the blocks it fills as at its start. *)
Definition hd_seg_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (w64 pc) mem2 (seg_rom segs)) md2 /\ FX fx2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
R W2 regs2 mem2.

(* What all five segments ask at their start: the harness's journal from its entry; sp = R; R 32-aligned with the
   real frame below S = sp0 and the callees' stack inside the journal's window; the frame for locals F = the
   side-stack frame (hi_cid, pos) the harness holds, with the shadow bytes sh; the cap and the null flag in range;
   the read-only data as in the image (the harness pre's arodata_okP, which the journal keeps, and rom_view, every
   byte of a read-only segment as the image's, which the soft-float callees of M03 need and every callee's post
   keeps); the shadow facts the code's instrumented checks and its callees read; and the pp block, live and made
   since the journal's start: a block of the start keeps its bytes under the journal (YCbq.v ajournal, the clause
   for blocks live at both ends), and a write to pp is the journal's own only as a block made since the start
   (YCbq.v awr_byte, in_tmp_block; HPgBase.hd_fresh_awr). The harness's malloc(pp), after the journal's start and
   before all five segments, gives it. *)
Definition hd_seg_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(I : hd_himg) (sh : list Z) (RLO RHI : Z) (e : hd_env) (pos : Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\ st_nev S + k <= EV_MAX /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
e_S e = sp0 /\ e_R e mod 32 = 0 /\ e_R e + hi_rsz I <= e_S e /\ sp0 - STK <= e_R e - T_SEG_STK /\
In (hi_cid I, pos) own /\ e_F e = frame_addr lyc (hi_cid I) pos /\
hd_fsh segs (w_H W) memc (e_F e) sh /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1 /\
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) /\
Forall (fun g => range_addressable (aview segs (w_H W) memc) SHADOW_OFF (fst g) (snd g)) (hi_globs I) /\
Forall (fun z => range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_R e + fst z) (snd z)) (hi_rz I) /\
Forall (fun s => hd_cstr segs (w_H W) memc (fst s) (snd s)) (hi_strs I) /\
hd_ro_cells segs (w_H W) memc (hi_cells I) /\
hd_guard_ok (aview segs (w_H W) memc) (hi_gotw I) (hi_guard I) /\
rom_view segs W memc /\
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pp e) Layout.PP_SIZE.

(* M01, the build: from C1 (pp <> 0, so the abort branch is not taken) to C2 (the `jal` of malloc(pod), not
   executed). The input bytes after the two harness bytes, rest, lie at src (shadow-checked reads, marked usable,
   their shadow hull readable and low enough for the shadow map: M01's __asan_memcpy calls copy from the input,
   and its contract asks amem_range and shadow_hull_vis of the source), apart from the ranges M01 writes; len is
   hd_len rest. It returns at C2 with the image's C2 values, the frame's shadow back to the prologue's, and the pp
   block holding Layout.pp_bytes of the record Model.pod_build makes of rest (the corruption included); it changes
   no float register (no float instruction in M01 or in its callees). Its writes to pp are the journal's own by
   hd_seg_pre's last conjunct. *)
Definition headamp_build_contract (I : hd_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : hd_env) (pos : Z) (rest : list byte),
hd_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I (hi_shA I) RLO RHI e pos ->
hd_cut segs (w_H W) memc regs e (hi_L1 I) ->
e_left e = Z.of_nat (length rest) -> e_len e = hd_len rest ->
garr8 segs (mrestrict (w_H W) memc) (e_src e) (hd_zbytes rest) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_src e) (e_left e) ->
0 < e_src e -> e_src e + e_left e <= 2 ^ 63 -> amem_range (e_src e) (e_left e) ->
(0 < e_left e -> shadow_hull_vis (aview segs (w_H W) memc) (e_src e) (e_left e)) ->
(forall a, e_src e <= a < e_src e + e_left e ->
 ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ hd_inw e (hi_w1 I) a /\ ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)) ->
SRr segs W (cfg_at segs (hi_c1 I) regs memc mdc)
(hd_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c2 I)
(fun f => f = fx)
(fun a => hd_inw e (hi_w1 I) a \/ e_pp e <= a < e_pp e + Layout.PP_SIZE)
(fun W2 regs2 mem2 =>
hd_cut segs (w_H W2) mem2 regs2 e (hi_L2 I) /\
hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shA I) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pp e)
(hd_zbytes (Layout.pp_bytes (fst (Model.pod_build rest)))))).

(* M02, the copy into the pod: from C3 (pod <> 0) to C4 (the `jal` of malloc(out)). The pp block holds the record
   r of some input and the pod block of len = |Model.buf r| bytes is live; __asan_memcpy copies the first len
   bytes of pp (the record's buffer) into pod. It returns at C4 with the image's C4 values, the frame's shadow as
   at its start, and the pod block holding Model.buf r; it changes no float register. *)
Definition headamp_dup_contract (I : hd_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : hd_env) (pos : Z) (r : Model.pod_rec),
hd_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I (hi_shA I) RLO RHI e pos ->
hd_cut segs (w_H W) memc regs e (hi_L3 I) ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_pod e) (e_len e) ->
SRr segs W (cfg_at segs (hi_c3 I) regs memc mdc)
(hd_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c4 I)
(fun f => f = fx)
(fun a => hd_inw e (hi_w2 I) a \/ e_pod e <= a < e_pod e + e_len e)
(fun W2 regs2 mem2 =>
hd_cut segs (w_H W2) mem2 regs2 e (hi_L4 I) /\
hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shA I) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pod e) (hd_zbytes (Model.buf r)))).

(* M03, the checks: from C5 (out <> 0) to C6 (the `jal` of malloc(first)). It fills out with the guard byte, sets
   res to 0x5a, runs the parse on the pod (or on NULL by the null flag), the first three checks, the corrupt test,
   the inlined expect_of (the pair loop, the string compares against the harness's own four literals, read_channel
   and the inlined pod_nearest with its soft-float calls) and the last four checks; reaching C6 is the property:
   no check aborts and no instrumented check fails. It returns at some float state that keeps every float register
   outside fs0, fs1, fa0, fa4, fa5, fs2, fs3 (f8, f9, f10, f14, f15, f18, f19; image A never writes fs3, image B
   does) with a zero rounding mode, the image's C6
   values, the frame's shadow with the res and x granules in scope (hi_shB), and the out block holding the parse's
   cells. The parse's answer fixes e_rc. *)
Definition headamp_check_contract (I : hd_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : hd_env) (pos ev : Z) (r : Model.pod_rec),
hd_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I (hi_shA I) RLO RHI e pos ->
hd_cut segs (w_H W) memc regs e (hi_L5 I) ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_pod e) (e_len e) ->
shadow_hull_vis (aview segs (w_H W) memc) (e_pod e) (e_len e) ->
amem_range (e_pod e) (e_len e + 8) -> e_pod e mod 16 = 0 ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
e_rc e = ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs (hi_c5 I) regs memc mdc)
(hd_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c6 I)
(hd_fxk [8; 9; 10; 14; 15; 18; 19] fx)
(fun a => hd_inw e (hi_w3 I) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
 (as_errno B <= a < as_errno B + 4))
(fun W2 regs2 mem2 =>
hd_cut segs (w_H W2) mem2 regs2 e (hi_L6 I) /\
hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB I) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_out e)
(hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
(exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))).

(* M04a, the copy into first: from C7 (first <> 0) to C8 (after the __asan_memcpy that fills it). It copies the
   3 max(rc, 0) bytes of out into first; it changes no float register. *)
Definition headamp_first_contract (I : hd_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : hd_env) (pos : Z) (cs : list Headamp.cell),
hd_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I (hi_shB I) RLO RHI e pos ->
hd_cut segs (w_H W) memc regs e (hi_L7 I) ->
-1 <= e_rc e <= e_cap e -> Z.of_nat (length cs) = Z.max (e_rc e) 0 ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes cs)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_first e) (hd_xv e XRc3NZ) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_first e) (hd_xv e XRc3NZ) ->
SRr segs W (cfg_at segs (hi_c7 I) regs memc mdc)
(hd_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c8 I)
(fun f => f = fx)
(fun a => hd_inw e (hi_w4 I) a \/ e_first e <= a < e_first e + hd_xv e XRc3NZ)
(fun W2 regs2 mem2 =>
hd_cut segs (w_H W2) mem2 regs2 e (hi_L8 I) /\
hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB I) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_first e) (hd_zbytes (ha_cells_bytes cs)))).

(* M04b, the second parse: from C8 to C9 (before the `jal` of free(first)). It fills out with the guard byte
   again, runs the parse with res = NULL on the same pod bytes and the same cap, and runs check_plain against
   first; reaching C9 is the property. It returns at a float state that keeps every float register outside fa4 and
   fa5, with the image's C9 values and the frame's shadow as at its start. *)
Definition headamp_plain_contract (I : hd_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : hd_env) (pos ev : Z) (r : Model.pod_rec),
hd_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I (hi_shB I) RLO RHI e pos ->
hd_cut segs (w_H W) memc regs e (hi_L8 I) ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_pod e) (e_len e) ->
shadow_hull_vis (aview segs (w_H W) memc) (e_pod e) (e_len e) ->
amem_range (e_pod e) (e_len e + 8) -> e_pod e mod 16 = 0 ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_first e) (hd_xv e XRc3NZ) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_first e) (hd_xv e XRc3NZ) ->
garr8 segs (mrestrict (w_H W) memc) (e_first e)
(hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) ->
e_rc e = ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs (hi_c8 I) regs memc mdc)
(hd_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c9 I)
(hd_fxk [14; 15] fx)
(fun a => hd_inw e (hi_w5 I) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
 (as_errno B <= a < as_errno B + 4))
(fun W2 regs2 mem2 =>
hd_cut segs (w_H W2) mem2 regs2 e (hi_L9 I) /\
hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB I) /\
(exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))).
End d.

(* =============================== LLVMFuzzerTestOneInput, the whole run ===============================
   fuzz_grant's exists-fx' text (lib/A/ACfn.v tfib_lib_pre_xf, tfib_lib_post_x, tfib_lib_contract_xf) over abstract
   segs, sink K, read-only range RLO .. RHI (arodata_okP, HPgBase.v) and harness constants: the entry asks a zero
   rounding mode, and the function returns at some float state with a zero rounding mode (headamp's harness changes
   fs0, fs1, fs2 and fa0, and its callees fa4 and fa5). lib/A/HPgLib.v instantiates it at image A's values; image
   B's twin at its own. *)
Section e. Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition hd_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (hd_zbytes pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) /\
asink_none segs K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
YK0o.frm_zero (@fp_csr fx).
Definition hd_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs K (rd W' mem') md' /\
ameta_inv segs K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition hd_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (Kl : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
hd_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@fp_csr fx') /\
hd_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (Kl l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) Kl).
End e.
End c.
End b.
