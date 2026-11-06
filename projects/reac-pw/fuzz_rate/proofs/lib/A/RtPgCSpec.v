(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v lines 190-246 (rfc_post, trfc_specX) in the Section form of lib/YC7y.v lines 4-18, 26-32 and 69-113 at c8557374ad2e to libreac/fuzz_knock: rfc_post -> kn_post_init / kn_post_heard / kn_post_step, trfc_specX -> tknock_init_specX / tknock_heard_specX / tknock_step_specX, tfibsegs -> the Section variable segs, A_read_frameconfig -> the parameter a, LAY_FrameConfig -> LAY_Knock, the parse_frameN result -> knock_step_f (reac_knock_step_c.v lines 11-18 restated over Z), the 32-byte destination dst -> the 40-byte struct kp in the caller's frame, written through awr_byte's in_frames case by In (cid, pos) own for any frame class cid (knock's harness frame is class 1), its addressability carried by afobj (APgBase.v) and kp <> 0; the stack struct st, the heap blocks Bb, the CTX_read_frameconfig premise and the malloc budget are dropped, because knock's three callees allocate nothing and call only the memset intrinsic; TRFC_STK = 112 + ASTACK -> T_init_STK = 48 + ESTACK (addi sp,sp,-48 at 0x7f44c), T_heard_STK = 16 (addi sp,sp,-16 at 0x7f4e8), T_step_STK = 16 (addi sp,sp,-16 at 0x7f570); EV_RFC = 6 -> EV_init = EV_heard = EV_step = 0; RFC_COST MT N -> 0 in mo_le; the file states no image-end or RELRO address. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgCSpec.v at origin/ossv/recipes 6ebe35ba632 (the
   Section form of its lines 32-164) and proofs/libreac/fuzz_grant/lib/A/ACfn.v at origin/ossv/recipes 2638f9235e2
   (lines 50-61 and 87-116: tfib_lib_post_x, tfib_lib_pre_xf, tfib_lib_contract_xf) for reac-pw/fuzz_role, image A and
   image B: knock's three callee contracts become the contracts of role's ten program callees, with one post shape
   rl_post that leaves the float state open (role's parse and pod_nearest change float registers); the harness
   contract is grant's exists-fx' form over abstract segs, sink, read-only range and harness constants; the two
   middle segments of LLVMFuzzerTestOneInput are stated over role's shared Pod model. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCSpec.v at 0de5d668c87e for reac-pw/fuzz_rate
   (image A and image B): module paths changed; the prefix rl_ becomes rt_ (rl_post -> rt_cpost, rl_pre -> rt_cpre,
   rl_himg -> rt_himg, rl_seg_post / rl_seg_pre -> rt_seg_post / rt_seg_pre, rl_lib_x -> rt_lib_x); role's ten callee
   contracts are replaced by rate's fifteen, stated over rate's shared Pod model (Pod/Rate.v, RateCfg.v, RateCsv.v,
   Nearest.v); two of them take a side-stack frame of their own (a class parameter) and let runtime-owned bytes change;
   role's two middle segments become rate's three (rate_build_contract, rate_check_contract, rate_csv_contract), the
   image record gains the cuts, live lists, write ranges and tables of the third block and the third segment; the
   lessons role's walks found in its texts (rom_view; the input's amem_range, shadow_hull_vis, 0 < src and
   src + left <= 2^63; the fresh-block premises) are kept from the start. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/DiscoAsanT.v at origin/ossv/recipes
   09c6822d886; its H_RO_stmt (ro_unowned of the read ranges, globs_marked, img_shadow_vis) becomes rt_img_facts over
   the image record's lists (rt_ro_ranges, new) and range; rt_img_static and rt_static_of_img_facts are new. *)
(* The ASan-level contracts of reac-pw/fuzz_rate's own functions. IMAGE-INDEPENDENT: no image module is Required;
   segs, the symbol record B, the meter MT, the sink K, every entry address, string address, table address, constant
   cell and side-stack class are Section variables or parameters, so image A (fuzz_rate.asan) and image B
   (fuzz_rate.asan-ubsan) instantiate the same texts. Statement text only: proves no function (kind: statement text).

   Each callee contract has knock's form (APgCSpec.v): the caller's journal from its own entry to the call
   (ajournal ... lyc Sc W memc mdc k), the call's registers, the stack bound sp0 - STK <= sp - T_f, and the
   function's own premises; its post (rt_cpost, or rt_cpost_o for the two callees that take a side-stack frame of
   their own) returns to ra with the caller's journal extended, the callee-saved
   registers kept, the frames, blocks, I/O state and meter as at the call, and every byte outside the callee's stack
   [sp - T_f, sp) and the bytes E it writes for its caller unchanged. Measured on image A (unstripped fuzz_rate.asan
   sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3) and image B (unstripped
   fuzz_rate.asan-ubsan sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1), capstone over the
   two files (A's pcs below):
   - frames: reac_rate_prop_parse `addi sp,sp,-96` (0x8449c); pod_nearest `addi sp,sp,-64` (0x83dc0) and below it
     __addtf3's `addi sp,sp,-48` (0x84f7c; __subtf3 is a `j` to it, the other soft-float callees take none, and
     __addtf3's own callees __fe_getround and __fe_raise_inexact are leaves without a frame);
     check_absent, check_rate, check_malformed, check_decide, check_code, check_list and reac_rate_refuse_code
     `addi sp,sp,-16`; reac_rate_is_closed, reac_rate_bit, reac_rate_best_drivable and reac_rate_cfg_decide none;
     reac_rate_drivable_csv `addi sp,sp,-224` then `andi sp,sp,-32` (0x84074, 0x840b4) and a side-stack frame of class
     1 (`li a0,128` + `jal __asan_stack_malloc_1`, 0x840e8 / 0x840ec); check_csv `addi sp,sp,-160` then
     `andi sp,sp,-32` (image A; image B `addi sp,sp,-192`) (0x838e0, 0x83920) and a side-stack frame of class 2
     (`jal __asan_stack_malloc_2` 0x83958). A
     wrapper called by a function (strcmp by the parse and check_code, snprintf by drivable_csv, bcmp by check_csv)
     uses 2 ESTACK below its sp (astrcmp_realizes of lib/Reusable/AStrcmpDef.v in the released fuzz_identity and
     fuzz_ctrl trees, not yet ported into this one; YG0d.v abcmp_realizes; the snprintf wrapper's window by the same
     convention, released fuzz_boxreg lib/A/Rt/SnprintfDef.v, whose depth for "%s%d" the wrapper's lane measures).
     Image B's frames are the same except check_csv `addi sp,sp,-192`; image B's M01 also calls its own
     pod_write_ent (frame 48), which has no contract here.
   - float registers: parse writes fa3, fa4, fa5 (f13-f15: flw, fld, fcvt.d.s, fadd.d, fcvt.d.l, 0x8484c-0x84884);
     pod_nearest writes fa5 (fmv.w.x 0x83e08) and saves and restores fs0 (fsd 0x83ddc / fld 0x83ee4); both accrue
     fflags and write no rounding mode; parse's fadd.d and fcvt.d.l read the dynamic rounding mode, hence the
     frm_zero premise; pod_nearest's soft-float addition reads frm through __fe_getround (`frrm`), and with frm 0 it
     does not reach that helper's table load. The snprintf wrapper's post leaves f10 and the flags open
     (SnprintfDef.v; the musl printf core under it loses fa0), hence drivable_csv's rt_fxk [10].
   - abort paths: each check function calls the no-return helper and abort only on its failure branch (image A
     0x836b4 / 0x836dc / 0x8370c / 0x8372c / 0x83798 / 0x838d8 / 0x83d88; image B 0x8357c / 0x835a8 / 0x835dc /
     0x83600 / 0x83670 / 0x837b4, each followed by an `unimp`); every error-path call (an __asan_report_ entry) sits
     behind an instrumented check that the premises make pass. Reaching ra at all is the content of a check's
     contract. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Spa Nearest Rate RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The stack each callee uses below its caller's sp (both images; see the header). drivable_csv and check_csv
   realign their frame down to 32: from a 16-aligned sp the realigned base is at most 16 below sp - frame. *)
Definition T_parse_STK : Z := 96 + 2 * ESTACK.
Definition T_nearest_STK : Z := 64 + 48.
Definition T_check_STK : Z := 16.
Definition T_cmp_STK : Z := 16 + 2 * ESTACK.
Definition T_leaf_STK : Z := 0.
(* reac_rate_drivable_csv and check_csv take their stack use as a parameter T. drivable_csv's frame is the same in
   both images (`addi sp,sp,-224` then `andi sp,sp,-32`); check_csv's is not (image A 160, image B 192), so each
   image's own file states its check_csv bound. Each bound covers the side-stack path, the only live one (the
   use-after-return option cell is 1 at start-up, so the real-stack fallback after a zero frame is dead). *)
Definition T_dcsv_STK : Z := 224 + 16 + 2 * ESTACK.

(* reac_rate_refuse_code(r) for r the 64-bit word in a0 (the `bgeu` against 4): codes[r] of its 5-entry table cs for
   r <= 4, else the literal cov the compiler put on that path (the value of codes[0], the "none" literal, in both
   images). *)
Definition rt_refuse (cs : list Z) (cov r : Z) : Z := if r <=? 4 then nth (Z.to_nat r) cs cov else cov.
(* pod_nearest's return value: 1 on Some, 0 on None (the plain contract's pod_near_rc). *)
Definition rt_near_rc (o : option Z) : Z := match o with Some _ => 1 | None => 0 end.
(* The bytes of a refusal code's text (RateCfg.refuse_code_res) and of the harness's code_of (RateCfg.code_of_res),
   as values without the NUL. *)
Definition rt_refuse_txt (r : Z) : list Z := map (fun x : byte => bv_unsigned x) (RateCfg.refuse_code_res r).
Definition rt_code_of_txt (r : Z) : list Z := map (fun x : byte => bv_unsigned x) (RateCfg.code_of_res r).

(* ===================== LLVMFuzzerTestOneInput's three middle segments: what each image fills =====================
   The segments M01 (after malloc(pp) returns, to the `jal` of malloc(pod)), M02 (after malloc(pod) returns, to the pc
   after check_code(reac_rate_refuse_code(4), 4) returns) and M03 (after malloc(buf) returns, to the pc after check_csv
   returns) are the plain walk's cuts (lib/Prog/LLVMFuzzerTestOneInput_c.v RATE_BUILD / RATE_MALLOC2 / RATE_CHECK /
   RATE_CHECK_END / RATE_CSV / RATE_FREE). An image gives:
   - hi_cid: the side-stack class of the frame for locals (image A 3: `li a0,0x1c0` + `jal __asan_stack_malloc_3` at
     0x80780 / 0x80784; image B 4);
   - hi_c1 .. hi_c7: the seven pcs (C1 = M01's first pc, C2 = the malloc(pod) `jal`, C3 = the pc after it, C4 = M02's
     end, C5 = the malloc(buf) `jal`, C6 = the pc after it = M03's first pc, C7 = M03's end);
   - hi_rsz: the real frame's size below S (R + hi_rsz <= S);
   - hi_L1 .. hi_L7: the live values at C1 .. C7 (RtPgBase rt_cut);
   - hi_shA / hi_shB: the shadow bytes of the frame for locals at C1, C2, C3 (the prologue's) and at C4 .. C7 (the
     objects M02 brings into scope);
   - hi_w1 / hi_w2 / hi_w3: the ranges M01 / M02 / M03 write besides the block they fill and the callees' stacks
     (frame objects, their shadow bytes, real-frame cells);
   - hi_rz: real-frame ranges (offset from R, length) whose shadow bytes the code checks (they must mark the bytes
     usable);
   - hi_globs: the registered globals (address, size) whose bytes the runtime marked usable and the segments read;
   - hi_strs / hi_cells: the strings (rt_cstr) and 8-byte constant cells (rt_ro_cells) the segments and their callees
     read;
   - hi_i32 / hi_u64: the tables of 4-byte and 8-byte values the callees read by instrumented loads (rt_i32tab,
     rt_u64tab). *)
Record rt_himg := RtHImg {
hi_cid : Z;
hi_c1 : Z; hi_c2 : Z; hi_c3 : Z; hi_c4 : Z; hi_c5 : Z; hi_c6 : Z; hi_c7 : Z;
hi_rsz : Z;
hi_L1 : list (rt_loc * rt_x); hi_L2 : list (rt_loc * rt_x); hi_L3 : list (rt_loc * rt_x);
hi_L4 : list (rt_loc * rt_x); hi_L5 : list (rt_loc * rt_x); hi_L6 : list (rt_loc * rt_x);
hi_L7 : list (rt_loc * rt_x);
hi_shA : list Z; hi_shB : list Z;
hi_w1 : list (rt_x * Z * Z); hi_w2 : list (rt_x * Z * Z); hi_w3 : list (rt_x * Z * Z);
hi_rz : list (Z * Z);
hi_globs : list (Z * Z);
hi_strs : list (Z * list Z);
hi_cells : list (Z * Z);
hi_i32 : list (Z * list Z);
hi_u64 : list (Z * list Z) }.
(* The stack the segments' callees may use below R (the harness sp throughout the three segments): the allocator's
   ASTACK, so that the malloc at C2 and C5 and the frees after C7 fit too; it bounds every callee of M01
   (__asan_memset / __asan_memcpy ESTACK, the strlen wrapper 2 ESTACK; in image B also its own pod_write_ent, frame
   48), of M02 (T_parse_STK and the others) and of M03 (T_dcsv_STK and each image's check_csv bound). *)
Definition T_SEG_STK : Z := ASTACK.
(* The bounds of the seven header values (fuzz_rate.c:236-239): bytes, buflen mod 24. *)
Definition rt_hdr_ok (e : rt_renv) : Prop :=
0 <= q_fl e < 256 /\ 0 <= q_mask e < 256 /\ 0 <= q_buflen e < 24 /\
0 <= q_b3 e < 256 /\ 0 <= q_b4 e < 256 /\ 0 <= q_b5 e < 256 /\ 0 <= q_b6 e < 256.
(* The read-only bytes the segments and their callees read, as (start, length): each string of hi_strs with its NUL,
   each table of hi_i32 and hi_u64, each 8-byte cell of hi_cells (rt_img_facts below asks that none is an owned static
   or an errno byte). *)
Definition rt_ro_ranges (I : rt_himg) : list (Z * Z) :=
map (fun s => (fst s, Z.of_nat (length (snd s)) + 1)) (hi_strs I) ++
map (fun t => (fst t, 4 * Z.of_nat (length (snd t)))) (hi_i32 I) ++
map (fun t => (fst t, 8 * Z.of_nat (length (snd t)))) (hi_u64 I) ++
map (fun c => (fst c, 8)) (hi_cells I).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== the post of a callee ===================================== *)
(* The call returns to ra (getr regs 1) at some float state fx2 with FX fx2, its journal extends the caller's
   (k events: none of these callees allocates; a side-stack frame changes no event count, YG01.v stack_malloc_post),
   and every byte outside its stack [sp - T, sp) and outside E is as at the call. R is what the function computes. *)
Definition rt_cpost_g (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(O : alayout -> astate -> Prop)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\ FX fx2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ O ly2 S2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
R W2 regs2 mem2.
(* The thirteen callees that take no side-stack frame of their own: nothing more is asked of the state they
   return at. *)
Definition rt_cpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
rt_cpost_g STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc (fun _ _ => True) FX E R.
(* reac_rate_drivable_csv and check_csv let runtime-owned bytes change (they take and release a side-stack frame
   of their own), so their E is `aowned B lyc Sc`. A caller that calls both in a row needs the SECOND call's owned
   set to be inside the FIRST call's state's owned set, which rt_cpost's clauses do not give: aowned reads the
   layout, the chunks and the frames, and rt_cpost relates ly2 S2 to lyc Sc only by the frames and the block
   permutation. So these two contracts add that one clause (found by the walk of rate_csv_contract, which must keep
   every byte outside [R - T_SEG_STK, R), hi_w3, buf and the owned set AT M03's START). Their walks discharge it
   from ly2 = lyc, st_chunks S2 = st_chunks Sc and frames S2 = frames Sc: the side-stack allocation and its inline
   release, the snprintf wrapper and the bcmp wrapper change neither the layout nor the chunks. *)
Definition rt_cpost_o (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
rt_cpost_g STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc
(fun ly2 S2 => forall a, aowned B ly2 S2 a -> aowned B lyc Sc a) FX E R.

(* The premises every callee contract shares (knock's, without the frame-chain premise: no callee here records a
   call trace): the caller's journal, the call's ra / gp / tp, and the callee's stack T inside the caller's
   stack window. *)
Definition rt_cpre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - T /\ spZ regs <= sp0 /\
st_nev S + k <= EV_MAX.

(* ========================== check_absent(rc, hz) (fuzz_rate.c:130-141) ==========================
   Returns when a0 = 0 and a1 = 0x5a5a5a5a, both 64-bit words (`bnez a0`, `bne a1,a0` after `lui; addiw`); else it
   aborts. The plain contract's premises (lib/Prog/check_absent_c.v). *)
Definition rt_check_absent_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 0 -> getr regs 11 = w64 0x5a5a5a5a ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ========================== check_rate(rc, hz, want) (fuzz_rate.c:143-156) ==========================
   Returns when a0 = 1 and a1 = a2 (64-bit words); else it aborts. *)
Definition rt_check_rate_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 1 -> getr regs 11 = getr regs 12 ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ======================== check_malformed(rc, hz) (fuzz_rate.c:158-173) ========================
   Returns when a0 = -1 and a1 = 0x5a5a5a5a (64-bit words); else it aborts. *)
Definition rt_check_malformed_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 (-1) -> getr regs 11 = w64 0x5a5a5a5a ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ========================== check_decide(got, want) (fuzz_rate.c:175-188) ==========================
   Returns when a0 = a1 (64-bit words); else it aborts. *)
Definition rt_check_decide_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = getr regs 11 ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ================ reac_rate_cfg_decide(role, hz, mask) (reac_rate_cfg.c:77-90) ================
   a0 := RateCfg.decide_res of the three 64-bit words (the plain contract's result); no stack, no store. *)
Definition rt_cfg_decide_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 =
  w64 (RateCfg.decide_res (bv_unsigned (getr regs 10)) (bv_unsigned (getr regs 11)) (bv_unsigned (getr regs 12))))).

(* ======================== reac_rate_bit(hz) (reac_rate_cfg.c:30-38) ========================
   a0 := RateCfg.rate_bit of the 64-bit word; no stack, no store. *)
Definition rt_bit_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 = w64 (RateCfg.rate_bit (bv_unsigned (getr regs 10))))).

(* ===================== reac_rate_is_closed(hz) (reac_rate_cfg.c:24-28) =====================
   a0 := RateCfg.rate_closed of the 64-bit word; no stack, no store. *)
Definition rt_is_closed_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 = w64 (RateCfg.rate_closed (bv_unsigned (getr regs 10))))).

(* ================== reac_rate_best_drivable(mask) (reac_rate_cfg.c:40-47) ==================
   a0 := RateCfg.rate_best of the 64-bit word (bits 2, 1, 0); no stack, no store. *)
Definition rt_best_drivable_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 = w64 (RateCfg.rate_best (bv_unsigned (getr regs 10))))).

(* ========================== reac_rate_refuse_code(r) (reac_rate_cfg.c:16-22) ==========================
   For r = the 64-bit word in a0: r <= 4 (`bgeu`, unsigned) loads codes[r] from the 5-entry table cs at tbl (one
   instrumented 8-byte load: the table's 40 bytes are marked usable), else returns cov. The table, its values and cov
   are the image's (image A: tbl = reac_rate_refuse_code.codes 0x9bc80 in .data.rel.ro, cov = codes[0] = 0x21600). *)
Definition rt_refuse_code_specX (a tbl cov : Z) (cs : list Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
length cs = 5%nat -> 0 <= cov < 2 ^ 64 ->
rt_u64tab segs (w_H W) memc tbl cs ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 = w64 (rt_refuse cs cov (bv_unsigned (getr regs 10))))).

(* ========================= check_code(got, r) (fuzz_rate.c:190-200, code_of :52-61) =========================
   For r = the 64-bit word in a1, r <= 4 (the plain contract's premise: the 32-bit `addiw` and refuse_code's 64-bit
   `bgeu` agree only there): r - 1 <= 3 (`addiw`, `bltu`) loads code_of(r) from the 4-entry table cs at tbl (one
   instrumented 8-byte load; image A: switch.table.check_code 0x9bc40 in .data.rel.ro), else (r = 0) takes its literal
   lnone ("none", image A 0x215c0); then it compares the string at a0 with it by the strcmp wrapper. It returns when
   the string at a0 has the text of refuse_code(r) (RateCfg.refuse_code_res), which is code_of(r)'s
   (RateCfg.code_of_refuse); the ASan images keep the two literal sets apart, so the compare is by text. *)
Definition rt_check_code_specX (a tbl lnone : Z) (cs : list Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s : Z),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 s -> bv_unsigned (getr regs 11) <= 4 ->
rt_cstr segs (w_H W) memc s (rt_refuse_txt (bv_unsigned (getr regs 11))) ->
length cs = 4%nat -> rt_u64tab segs (w_H W) memc tbl cs ->
(forall i, 0 <= i < 4 -> rt_cstr segs (w_H W) memc (nth (Z.to_nat i) cs 0) (rt_code_of_txt (i + 1))) ->
rt_cstr segs (w_H W) memc lnone (rt_code_of_txt 0) ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ================= check_list(hz, bit, closed, mask, best) (fuzz_rate.c:202-215, bit_of :43-49) =================
   Returns when a1 = rate_bit hz, a2 = rate_closed hz and a4 = rate_best mask (RateCfg; hz = a0 and mask = a3 as
   64-bit words: the plain contract's premises). It reads closed_list (the 3-entry table tcl, image A 0x21520) twice
   by instrumented 4-byte loads. *)
Definition rt_check_list_specX (a tcl : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 11 = w64 (RateCfg.rate_bit (bv_unsigned (getr regs 10))) ->
getr regs 12 = w64 (RateCfg.rate_closed (bv_unsigned (getr regs 10))) ->
getr regs 14 = w64 (RateCfg.rate_best (bv_unsigned (getr regs 13))) ->
rt_i32tab segs (w_H W) memc tcl RateCfg.closed_list ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ================================ pod_nearest(f, out) (pod.h:152-171) ================================
   The out-of-line copy with lo = INT32_MIN and hi = INT32_MAX folded in: fa0 holds the binary32 b (NaN-boxed);
   it returns 1 and stores the nearest integer r as 8 bytes at out (one instrumented 8-byte store: out's 8 bytes
   are marked usable) when Nearest.nearest b gives Some r, else returns 0 and stores nothing (the plain contract's
   pod_nearest_contract, Prog/pod_nearest_c.v). Its soft-float callees (__extendsftf2, __cmptf2 / __lttf2,
   __floatditf, __subtf3 -> __addtf3, __getf2) make no instrumented access; their walks run them as the CJ contracts
   on the normalized store, whose step back needs the read-only agreement, hence rom_view (YG0d.v): every byte of a
   read-only segment reads as the image's. *)
Definition rt_pod_nearest_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (out b : Z),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_nearest_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 out -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
rt_wcell STK sp0 lyc own (spZ regs) T_nearest_STK out 8 -> out mod 8 = 0 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF out 8 ->
rom_view segs W memc ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_nearest_STK regs lyc Sc W memc mdc
(rt_fxk [15] fx)
(fun x => Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\ out <= x < out + 8)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (rt_near_rc (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX)) /\
match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
| Some r => val_mem segs (mrestrict (w_H W2) mem2) out 8 (r mod 2 ^ 64)
| None => True
end)).

(* ====================== reac_rate_prop_parse(props, out_hz) (reac_rate_cfg.c:115-152) ======================
   a0 = 0 (null) returns -1 without reading memory; else the len >= 8 bytes bs at P (top size word len - 8) are
   parsed: the answer is Rate.harness_parse null bs (Rate.parse_model bs; the plain contract's result), and when it
   writes v, the 4 bytes of v at Q (one instrumented 4-byte store: Q's 4 bytes are marked usable). Every read of the
   pod is an instrumented load inside [P, P + len) (the pod's len bytes are marked usable); the key compare is the
   strcmp wrapper against the literal "reac.cfg.rate" at akey (the image's address); the doubles it compares with are
   read from read-only data without a shadow check: dcs lists those cells and their values (the image's: 0.5, -2^31,
   2^31 in image A at 0x10380, 0x103e8, 0x10338). *)
Definition rt_parse_specX (a akey : Z) (dcs : list (Z * Z)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(null : bool) (P Q : Z) (bs : list byte),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 (if null then 0 else P) -> getr regs 11 = w64 Q ->
(null = false ->
 0 < P /\ P mod 16 = 0 /\ 8 <= Z.of_nat (length bs) /\ Spa.u32_at bs 0 = Z.of_nat (length bs) - 8 /\
 P + Z.of_nat (length bs) <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) P (map (fun x : byte => bv_unsigned x) bs) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF P (Z.of_nat (length bs)) /\
 shadow_hull_vis (aview segs (w_H W) memc) P (Z.of_nat (length bs)) /\
 amem_range P (Z.of_nat (length bs)) /\
 (P + Z.of_nat (length bs) <= spZ regs - T_parse_STK \/ spZ regs <= P)) ->
rt_wcell STK sp0 lyc own (spZ regs) T_parse_STK Q 4 -> 0 < Q -> Q mod 4 = 0 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF Q 4 ->
rt_cstr segs (w_H W) memc akey (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) ->
rt_ro_cells segs (w_H W) memc dcs ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc
(rt_fxk [13; 14; 15] fx)
(fun x => fst (Rate.harness_parse null bs) <> None /\ Q <= x < Q + 4)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (snd (Rate.harness_parse null bs)) /\
match fst (Rate.harness_parse null bs) with
| Some v => val_mem segs (mrestrict (w_H W2) mem2) Q 4 (v mod 2 ^ 32)
| None => True
end)).

(* =============== reac_rate_drivable_csv(mask, buf, buflen) (reac_rate_cfg.c:49-75) ===============
   It takes a side-stack frame of class cid (class 1 in both images, 128 bytes: tmp[32] at +32, cell[16] at +96; the
   caller supplies a free frame of that class: count_cid cid (frames Sc) < fs_frames cid, the premise of
   YG0d.v astack_malloc_realizes) and releases it before it returns (flag byte 0, shadow 0xf5), so its post lets
   runtime-owned bytes change (aowned at the call: the free frames, their shadow and flag bytes, the side stack's
   hint). For i = 0, 1, 2 it reads ordered[i] from the 3-entry table tord (image A 0x216a0) by an instrumented
   4-byte load, tests reac_rate_bit(ordered[i]) & mask (64-bit and), and on a set bit calls the snprintf wrapper
   with (cell, 16, afmt "%s%d", sep, ordered[i]), sep = aempty "" while the list is empty and acomma "," after,
   then __asan_memcpy(tmp + len, cell, n); at the end, for n = buflen > 0, __asan_memcpy(buf, tmp, copy) with
   copy = min(len, n - 1) and an instrumented 1-byte store of the NUL at buf + copy. So it returns
   |csv_list mask| (RateCsv.v) and, for n > 0, leaves csv_cut L n and a NUL at buf (the plain contract's post,
   Prog/reac_rate_drivable_csv_c.v); for n = 0 it writes no byte of buf.
   THE SNPRINTF WRAPPER IS NOT STATED HERE. The walk of this contract takes the wrapper's contract as a Section
   hypothesis at the wrapper entry (image A: __interceptor_trampoline_snprintf 0x421d4, the `jal` at 0x8427c) in the
   form of the kit's wrapper contracts (YG0d.v abcmp_realizes; released fuzz_boxreg lib/A/Rt/SnprintfDef.v
   asnprintf_realizes): from ecall_pre, 2 ESTACK of present stack below sp and the facts below, an SRr to raZ regs
   with W' = W, some fx' that keeps every float register but f10 and has a zero rounding mode, AR kept with the same
   ly S W, aregs_preserved, same_but_materialized, a0 = |T| for T = sep ++ RateCsv.csv_dec v, the bytes
   firstn (n - 1) T ++ [0] at d, every other byte outside the 2 ESTACK window unchanged, presence kept. The facts it
   may ask, which this contract's premises and the frame's state supply: d = the cell (16 bytes inside the class-cid
   frame the function holds, its shadow made usable by the function, outside the window), n = 16, the format and the
   separator as rt_cstr (bytes, NUL, image, amem_range, range_addressable, shadow_hull_vis), v = ordered[i] as a
   sign-extended 32-bit int, rt_rom_kept (the musl printf core's constants), frm_zero at entry. The released form
   also asks facts rt_cstr does not state (the rest of each string's NUL word readable and apart from d,
   amem_range of the string's length + 8, the format below the image's guard slot); for literals at the image's own
   .rodata addresses the walk computes them from the image. After the frame call the shadow of the format, the
   separators and ordered comes from the symbol record's invariant rt_img_facts (their bytes are kept: no owned
   static), not from these premises; RtPgBase.rt_cstr_at / rt_i32tab_at rebuild the two predicates there. *)
Definition rt_drivable_csv_specX (a cid T afmt acomma aempty tord : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (mask buf n : Z),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
getr regs 10 = w64 mask -> 0 <= mask < 2 ^ 64 ->
getr regs 11 = w64 buf -> getr regs 12 = w64 n -> 0 <= n <= 23 ->
(0 < n ->
 0 < buf /\ buf + n <= 2 ^ 63 /\
 (exists m, In (buf, m) (ablocks B lyc Sc) /\ ~ In (buf, m) (ablocks B ly S) /\ n <= m) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF buf n /\
 shadow_hull_vis (aview segs (w_H W) memc) buf n /\ amem_range buf n /\
 (buf + n <= spZ regs - T \/ spZ regs <= buf)) ->
0 <= cid <= 10 -> count_cid cid (frames Sc) < fs_frames cid ->
rt_cstr segs (w_H W) memc afmt STR_FMT_SD ->
rt_cstr segs (w_H W) memc acomma STR_COMMA -> rt_cstr segs (w_H W) memc aempty STR_EMPTY ->
rt_i32tab segs (w_H W) memc tord RateCfg.closed_list ->
rt_rom_kept segs B W memc ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost_o STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc
(rt_fxk [10] fx)
(fun x => aowned B lyc Sc x \/ (0 < n /\ buf <= x < buf + n))
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (Z.of_nat (length (RateCsv.csv_list mask))) /\
(0 < n -> garr8 segs (mrestrict (w_H W2) mem2) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])))).

(* =============== check_csv(buf, buflen, len, mask) (fuzz_rate.c:217-229, csv_holds :103-128) ===============
   It takes a side-stack frame of class cid (class 2 in both images, 256 bytes; want[40] and d[8] in it; the caller
   supplies a free frame of that class) and releases it before it returns, so its post lets runtime-owned bytes
   change. It recomputes the list of mask (reading closed_list, the 3-entry table tcl, image A 0x21520, by
   instrumented 4-byte loads); with len = |csv_list mask| (64-bit compare) it returns when buf holds 0x5a (n = 0, an
   instrumented 1-byte load of buf[0]) or csv_cut L n and a NUL (n > 0: the bcmp wrapper on c = min(len, n - 1)
   bytes, then an instrumented 1-byte load of buf[c]); the plain contract's premises (Prog/check_csv_c.v). It writes
   no byte of buf. The bcmp wrapper's contract is the kit's YG0d.v abcmp_realizes (image A entry 0x421a8).
   buf must be a LIVE BLOCK, not only an addressable range: the function takes its side-stack frame before it reads
   buf at all, and __asan_stack_malloc keeps only the bytes that are owned at neither state (YG0d.v
   astack_malloc_realizes), so the walk re-derives buf's shadow from the allocator's block law and its bytes from
   the block being a client's. Without the premise the text is false for an abstract state: buf could point into
   the free class-cid frame the call then hands out, whose header and shadow stores run before the compare. *)
Definition rt_check_csv_specX (a cid T tcl : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z),
rt_cpre STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
getr regs 10 = w64 buf -> getr regs 11 = w64 n -> 0 <= n <= 23 ->
getr regs 12 = w64 (Z.of_nat (length (RateCsv.csv_list mask))) -> getr regs 13 = w64 mask -> 0 <= mask < 2 ^ 64 ->
0 < buf -> buf + Z.max n 1 <= 2 ^ 63 ->
(exists m, In (buf, m) (ablocks B lyc Sc) /\ Z.max n 1 <= m) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF buf (Z.max n 1) ->
shadow_hull_vis (aview segs (w_H W) memc) buf (Z.max n 1) -> amem_range buf (Z.max n 1) ->
(buf + Z.max n 1 <= spZ regs - T \/ spZ regs <= buf) ->
(n = 0 -> garr8 segs (mrestrict (w_H W) memc) buf [0x5a]) ->
(0 < n -> garr8 segs (mrestrict (w_H W) memc) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])) ->
0 <= cid <= 10 -> count_cid cid (frames Sc) < fs_frames cid ->
rt_i32tab segs (w_H W) memc tcl RateCfg.closed_list ->
SRr segs W (cfg_at segs a regs memc mdc)
(rt_cpost_o STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc
(fun f => f = fx) (fun x => aowned B lyc Sc x) (fun _ _ _ => True)).

(* ============================ LLVMFuzzerTestOneInput's three middle segments ============================
   The ASan-level counterparts of the plain walk's rate_build_contract, rate_check_contract and rate_csv_contract
   (lib/Prog/LLVMFuzzerTestOneInput_c.v), with the same names, the same cuts and the same Pod model (Model.pod_build,
   Layout.pp_bytes, rt_len = rate_len, rt_bl = rate_bl, RateCsv), over the image's rt_himg I. A segment runs inside
   the harness's own journal (from its entry: sp0 = S, own = the harness's side-stack frame); it ends at a fixed pc
   (not at ra), with sp, gp, tp as at its start, the frames, blocks, I/O state and meter as at its start, and every
   byte outside the callees' stack [R - T_SEG_STK, R), the image's write ranges and the block it fills as at its
   start (for M03 also outside the runtime-owned bytes at its start: its two callees take and release side-stack
   frames). *)
Definition rt_seg_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
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
(* What the three segments ask at their start: the harness's journal from its entry; sp = R; R 16-aligned with the
   real frame below S = sp0 and the callees' stack inside the journal's window; the frame for locals F = the
   side-stack frame (hi_cid, pos) the harness holds; the pp block live; the header
   values in their ranges; the read-only data as in the image (the harness pre's arodata_okP, which the journal
   keeps, and rom_view, every byte of a read-only segment as the image's, which pod_nearest's soft-float callees need
   and every M02 callee's post keeps); the shadow facts the code's instrumented checks and its callees read; pp not
   among the journal's start blocks (ablocks B ly S): a block of the start keeps its bytes under the journal
   (YCbq.v ajournal, the clause for blocks live at both ends), and a write to pp is the journal's own only as a block
   made since the start (YCbq.v awr_byte, in_tmp_block; RtPgBase.rt_fresh_awr), which the harness's malloc(pp), after
   the journal's start and before the three segments, gives; and, last, the tables the callees read by instrumented
   loads. rom_view also covers the read-only words M01 loads without a shadow check that are not cells of hi_cells
   (image A: the division constants 0x10408, 0x10318, 0x10310 and the jump table [0x20f64, 0x20f88)). These shadow
   facts hold at a segment's start; after a call that lets runtime-owned bytes change (a malloc, a side-stack frame,
   reac_rate_drivable_csv's post) a walk re-derives the shadow from rt_img_facts (the symbol record's invariant: the
   globals' shadow in every AR state, the read ranges no owned static), as the released units do, and the bytes
   either kept from the state before the call (RtPgBase.rt_cstr_at, rt_i32tab_at, rt_u64tab_at) or, at a state
   with arodata_okP, from the image (rt_static_of_img_facts below; with RtPgBase.rt_rom_pinned also rom_view). Only
   M01 and M02 rely on the frame's prologue shadow (rt_fsh hi_shA); M03 starts from hi_shB, which its contract
   asks. *)
Definition rt_seg_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(I : rt_himg) (RLO RHI : Z) (e : rt_renv) (pos : Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\ st_nev S + k <= EV_MAX /\
getr regs 2 = w64 (q_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
q_S e = sp0 /\ q_R e mod 16 = 0 /\ q_R e + hi_rsz I <= q_S e /\ sp0 - STK <= q_R e - T_SEG_STK /\
In (hi_cid I, pos) own /\ q_F e = frame_addr lyc (hi_cid I) pos /\
q_pp e <> 0 /\ In (q_pp e, Layout.PP_SIZE) (ablocks B lyc Sc) /\
rt_hdr_ok e /\
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) /\
Forall (fun g => range_addressable (aview segs (w_H W) memc) SHADOW_OFF (fst g) (snd g)) (hi_globs I) /\
Forall (fun z => range_addressable (aview segs (w_H W) memc) SHADOW_OFF (q_R e + fst z) (snd z)) (hi_rz I) /\
Forall (fun s => rt_cstr segs (w_H W) memc (fst s) (snd s)) (hi_strs I) /\
rt_ro_cells segs (w_H W) memc (hi_cells I) /\
rom_view segs W memc /\
~ In (q_pp e, Layout.PP_SIZE) (ablocks B ly S) /\
Forall (fun t => rt_i32tab segs (w_H W) memc (fst t) (snd t)) (hi_i32 I) /\
Forall (fun t => rt_u64tab segs (w_H W) memc (fst t) (snd t)) (hi_u64 I).

(* Image B's bound obligations on pp at a segment's start (its checks of undefined behaviour ask pp mod 8 = 0 and
   pp + 19744 <= 2^63): the journal's AR and the live pp block give them (RtPgBase.rt_block_bounds). *)
Lemma rt_seg_pp_bounds : AR_laws segs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc I RLO RHI e pos,
rt_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
0 < q_pp e /\ q_pp e mod 16 = 0 /\ q_pp e + Layout.PP_SIZE <= 2 ^ 63.
Proof.
intros LAWS STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos HP.
destruct HP as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hin & _). destruct HJ as (HAR & _).
exact (rt_block_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hin).
Qed.
(* Image B's bound obligations on the frame for locals (its checks ask F + its size not to wrap): the journal's
   frames clause puts F among the live frames, whose AR bounds and alignment give them (RtPgBase.rt_frame_bounds,
   YG0d.v AR_frames_law). *)
Lemma rt_seg_frame_bounds : AR_laws segs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc I RLO RHI e pos,
rt_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
0 < q_F e /\ q_F e mod 32 = 0 /\ q_F e + fs_frame_bytes (hi_cid I) <= 2 ^ 63.
Proof.
intros LAWS STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos HP.
destruct HP as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _).
destruct HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid I, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (rt_frame_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hin) as [H0 H1].
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H32 & _).
rewrite HF. split; [exact H0|]. split; [exact H32|exact H1].
Qed.
(* =================== the image's read-only data in every state of the runtime invariant ===================
   What a walk needs to re-derive, after a call that lets runtime-owned bytes change (a malloc, a side-stack frame,
   rt_cpost_o), the string, cell and table facts that rt_seg_pre and the callee contracts state at a call
   (RtPgBase.v, Section img): no byte of the read ranges rt_ro_ranges I is an owned static or an errno byte (so it is
   owned in no AR state and every such call keeps it), the registered globals hi_globs I have the runtime's shadow in
   every AR state, and every shadow byte of the image's range [lo, hi) is readable in every AR state. A fact of the
   symbol record B and the image alone: the released fuzz_disco lib/A/DiscoAsanT.v H_RO_stmt, with the image's lists.
   The walks take it as a hypothesis, with AR_laws; each image's close proves it at its own symbol record by
   computation (released: fuzz_disco lib/A/Prog/DiscoRoClose.v, lib/A/DiscoRoA.v disco_H_RO). Image A's instance is
   RtPgSiteA.v rate_A_img_facts. *)
Definition rt_img_facts (I : rt_himg) (lo hi : Z) : Prop :=
Forall (fun r => rt_ro_unowned B (fst r) (snd r)) (rt_ro_ranges I) /\
rt_globs_marked segs B (hi_globs I) /\ rt_img_shadow_vis segs B lo hi.
(* The image side of the record's read data (no state): each string of hi_strs is the image's bytes and NUL in the
   read-only range (RtPgBase.in_roP), with rt_cstr's bounds, a registered global of hi_globs with room for it, 64 bytes
   inside [lo, hi); each cell of hi_cells is the image's 8-byte value in the read-only range; each table of hi_i32 /
   hi_u64 is the image's values in the read-only range, with rt_i32tab / rt_u64tab's bounds, a registered global with
   room for it. Each image proves it by computation from its loaded segments (image A: RtPgSatSeg.v
   rate_A_img_static). *)
Definition rt_img_static (I : rt_himg) (lo hi RLO RHI : Z) : Prop :=
Forall (fun s =>
  rt_img_bytes segs RLO RHI (fst s) (snd s ++ [0]) /\ Forall (fun b => 0 < b < 256) (snd s) /\
  0 < fst s /\ fst s + Z.of_nat (length (snd s)) + 1 <= 2 ^ 63 /\
  (forall i, 0 <= i <= Z.of_nat (length (snd s)) -> in_img segs (fst s + i)) /\
  amem_range (fst s) (Z.of_nat (length (snd s)) + 1) /\
  (exists sz, In (fst s, sz) (hi_globs I) /\ Z.of_nat (length (snd s)) + 1 <= sz) /\
  lo + 64 <= fst s /\ fst s + Z.of_nat (length (snd s)) + 1 + 64 <= hi) (hi_strs I) /\
Forall (fun c => rt_img_val segs RLO RHI (fst c) 8 (snd c)) (hi_cells I) /\
Forall (fun t =>
  (forall i, 0 <= i < 4 * Z.of_nat (length (snd t)) -> in_img segs (fst t + i)) /\ fst t mod 4 = 0 /\
  (forall i, 0 <= i < Z.of_nat (length (snd t)) ->
   rt_img_val segs RLO RHI (fst t + 4 * i) 4 (nth (Z.to_nat i) (snd t) 0)) /\
  (exists sz, In (fst t, sz) (hi_globs I) /\ 4 * Z.of_nat (length (snd t)) <= sz)) (hi_i32 I) /\
Forall (fun t =>
  (forall i, 0 <= i < 8 * Z.of_nat (length (snd t)) -> in_img segs (fst t + i)) /\ fst t mod 8 = 0 /\
  Forall (fun v => 0 <= v < 2 ^ 64) (snd t) /\
  (forall i, 0 <= i < Z.of_nat (length (snd t)) ->
   rt_img_val segs RLO RHI (fst t + 8 * i) 8 (nth (Z.to_nat i) (snd t) 0)) /\
  (exists sz, In (fst t, sz) (hi_globs I) /\ 8 * Z.of_nat (length (snd t)) <= sz)) (hi_u64 I).
(* At every AR state that has the read-only data as in the image (arodata_okP, the harness pre's, which every
   journal keeps), rt_img_facts and the image side give rt_seg_pre's globals, strings, cells and tables: what the
   main walk's chaining needs at C1, C3 and C6 after the two mallocs (besides rom_view). *)
Lemma rt_static_of_img_facts : forall I lo hi RLO RHI,
rt_img_facts I lo hi -> rt_img_static I lo hi RLO RHI ->
forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs I) /\
Forall (fun s => rt_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs I) /\
rt_ro_cells segs (w_H W) mem (hi_cells I) /\
Forall (fun t => rt_i32tab segs (w_H W) mem (fst t) (snd t)) (hi_i32 I) /\
Forall (fun t => rt_u64tab segs (w_H W) mem (fst t) (snd t)) (hi_u64 I).
Proof.
intros I lo hi RLO RHI (HU & HG & HV) (SS & SC & SI & SU) ly S W mem md HAR HA.
rewrite Forall_forall in HU, SS, SC, SI, SU.
split.
{ apply Forall_forall. intros (q, sz) Hin. cbn [fst snd].
  exact (rt_glob_usable segs B (hi_globs I) ly S W mem md q sz q sz HG Hin HAR ltac:(lia) ltac:(lia)). }
split.
{ apply Forall_forall. intros (a, s) Hin. cbn [fst snd].
  destruct (SS (a, s) Hin) as (B1 & B2 & B3 & B4 & B5 & B6 & (sz & Hg & Hsz) & Hlo & Hhi). cbn [fst snd] in *.
  assert (Hu : rt_ro_unowned B a (Z.of_nat (length (s ++ [0])))).
  { replace (Z.of_nat (length (s ++ [0]))) with (Z.of_nat (length s) + 1) by (rewrite length_app; cbn [length]; lia).
    exact (HU (a, Z.of_nat (length s) + 1) (in_or_app _ _ _ (or_introl
      (in_map (fun s0 : Z * list Z => (fst s0, Z.of_nat (length (snd s0)) + 1)) (hi_strs I) (a, s) Hin)))). }
  pose proof (rt_bytes_of_ro segs B RLO RHI W mem a (s ++ [0]) HA Hu B1) as BY.
  destruct (rt_glob_read_ok segs B (hi_globs I) lo hi ly S W mem md a sz a (Z.of_nat (length s) + 1) HG Hg HV HAR
    ltac:(lia) ltac:(lia) ltac:(lia) Hlo ltac:(lia)) as [RA HH].
  unfold rt_cstr. split.
  { intros i Hi. rewrite (BY i ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth1 by lia. reflexivity. }
  split.
  { rewrite (BY (Z.of_nat (length s)) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity. }
  split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
  split; [exact RA | exact HH]. }
split.
{ unfold rt_ro_cells. apply Forall_forall. intros (c, v) Hin. cbn [fst snd].
  pose proof (SC (c, v) Hin) as Hc. cbn [fst snd] in Hc.
  assert (Hu : rt_ro_unowned B c 8).
  { exact (HU (c, 8) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror
      (in_map (fun c0 : Z * Z => (fst c0, 8)) (hi_cells I) (c, v) Hin)))))))). }
  exact (rt_val_of_ro segs B RLO RHI W mem c 8 v HA Hu Hc). }
split.
{ apply Forall_forall. intros (t, vs) Hin. cbn [fst snd].
  destruct (SI (t, vs) Hin) as (T1 & T2 & T3 & (sz & Hg & Hsz)). cbn [fst snd] in *.
  assert (Hu : rt_ro_unowned B t (4 * Z.of_nat (length vs))).
  { exact (HU (t, 4 * Z.of_nat (length vs)) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl
      (in_map (fun t0 : Z * list Z => (fst t0, 4 * Z.of_nat (length (snd t0)))) (hi_i32 I) (t, vs) Hin)))))). }
  unfold rt_i32tab. split; [exact T1|]. split; [exact T2|]. split.
  - intros i Hi. apply (rt_val_of_ro segs B RLO RHI W mem (t + 4 * i) 4 _ HA); [|exact (T3 i Hi)].
    intros x Hx. apply Hu. lia.
  - exact (rt_glob_usable segs B (hi_globs I) ly S W mem md t sz t (4 * Z.of_nat (length vs)) HG Hg HAR
      ltac:(lia) ltac:(lia)). }
apply Forall_forall. intros (t, vs) Hin. cbn [fst snd].
destruct (SU (t, vs) Hin) as (T1 & T2 & T3 & T4 & (sz & Hg & Hsz)). cbn [fst snd] in *.
assert (Hu : rt_ro_unowned B t (8 * Z.of_nat (length vs))).
{ exact (HU (t, 8 * Z.of_nat (length vs)) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _
    (or_introl (in_map (fun t0 : Z * list Z => (fst t0, 8 * Z.of_nat (length (snd t0)))) (hi_u64 I) (t, vs) Hin)))))))). }
unfold rt_u64tab. split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split.
- intros i Hi. apply (rt_val_of_ro segs B RLO RHI W mem (t + 8 * i) 8 _ HA); [|exact (T4 i Hi)].
  intros x Hx. apply Hu. lia.
- exact (rt_glob_usable segs B (hi_globs I) ly S W mem md t sz t (8 * Z.of_nat (length vs)) HG Hg HAR
    ltac:(lia) ltac:(lia)).
Qed.

(* M01, the build: from C1 (pp <> 0, so the abort branch is not taken) to C2 (the malloc(pod) `jal`, not
   executed). The frame for locals has the prologue's shadow bytes. The input bytes after the 7-byte header, rest,
   lie at src (shadow-checked reads, marked usable, their shadow hull readable and low enough for the shadow map: M01's
   __asan_memcpy calls copy from the input, and its contract asks amem_range and shadow_hull_vis of the source;
   0 < src and src + left <= 2^63, as the image-B walk needs), apart from the ranges M01 writes; len is rt_len rest.
   It returns at C2 with the image's C2 values, the frame's shadow back to the prologue's, and the pp block holding
   Layout.pp_bytes of the record Model.pod_build made of rest (the corruption included); it changes no float register
   (no float instruction in M01 or in its callees). Its writes to pp are the journal's own by rt_seg_pre's pp
   conjunct. *)
Definition rate_build_contract (I : rt_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : rt_renv) (pos : Z) (rest : list byte),
rt_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
rt_fsh segs (w_H W) memc (q_F e) (hi_shA I) ->
rt_cut segs (w_H W) memc regs e (hi_L1 I) ->
q_left e = Z.of_nat (length rest) -> q_len e = rt_len rest ->
garr8 segs (mrestrict (w_H W) memc) (q_src e) (map (fun x : byte => bv_unsigned x) rest) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (q_src e) (q_left e) ->
0 < q_src e -> q_src e + q_left e <= 2 ^ 63 -> amem_range (q_src e) (q_left e) ->
(0 < q_left e -> shadow_hull_vis (aview segs (w_H W) memc) (q_src e) (q_left e)) ->
(forall a, q_src e <= a < q_src e + q_left e ->
 ~ (q_R e - T_SEG_STK <= a < q_R e) /\ ~ rt_inw e (hi_w1 I) a /\ ~ (q_pp e <= a < q_pp e + Layout.PP_SIZE)) ->
SRr segs W (cfg_at segs (hi_c1 I) regs memc mdc)
(rt_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c2 I)
(fun f => f = fx)
(fun a => rt_inw e (hi_w1 I) a \/ q_pp e <= a < q_pp e + Layout.PP_SIZE)
(fun W2 regs2 mem2 =>
rt_cut segs (w_H W2) mem2 regs2 e (hi_L2 I) /\
rt_fsh segs (w_H W2) mem2 (q_F e) (hi_shA I) /\
garr8 segs (mrestrict (w_H W2) mem2) (q_pp e)
(map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest)))))).

(* M02, the checks: from C3 (pod <> 0, so the abort branch is not taken) to C4. The frame for locals has the
   prologue's shadow bytes; the pp block holds the record of some input inp (as M01 leaves it) and the pod block of
   len = rt_len inp bytes is live (len >= 8, so the request len + (len == 0) is len). It copies pp's len bytes into
   pod, runs the parse on pod (or NULL by flags bit 0) into the hz cell, the inlined expect_rate scan (strcmp against
   the harness's key, pod_nearest) and the check its answer selects (when the record is uncorrupted), then for asked =
   {rc = 1 ? hz : 48000, other}: reac_rate_cfg_decide, check_decide, reac_rate_refuse_code, check_code, reac_rate_bit,
   reac_rate_is_closed, reac_rate_best_drivable and check_list, twice; then check_code(refuse_code(4), 4). Reaching C4
   is the property: no check aborts and no instrumented check fails. It returns at some float state fx' (fa0 by the
   harness's flw, fa3-fa5 by the parse, fa5 by pod_nearest) with a zero rounding mode, the image's C4 values and the
   frame objects M02 brings into scope (hi_shB: image A hz and asked, image B hz only, its asked lies on the real
   stack). The pod block is not among the journal's start blocks, as pp in
   rt_seg_pre (its memcpy writes pod; the malloc(pod) post gives it). *)
Definition rate_check_contract (I : rt_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : rt_renv) (pos : Z) (inp : list byte),
rt_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
rt_fsh segs (w_H W) memc (q_F e) (hi_shA I) ->
rt_cut segs (w_H W) memc regs e (hi_L3 I) ->
q_len e = rt_len inp ->
garr8 segs (mrestrict (w_H W) memc) (q_pp e)
(map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build inp)))) ->
q_pod e <> 0 -> In (q_pod e, q_len e) (ablocks B lyc Sc) ->
~ In (q_pod e, q_len e) (ablocks B ly S) ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs (hi_c3 I) regs memc mdc)
(rt_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c4 I)
(rt_fxk [10; 13; 14; 15] fx)
(fun a => rt_inw e (hi_w2 I) a \/ q_pod e <= a < q_pod e + q_len e)
(fun W2 regs2 mem2 =>
rt_cut segs (w_H W2) mem2 regs2 e (hi_L4 I) /\
rt_fsh segs (w_H W2) mem2 (q_F e) (hi_shB I))).

(* M03, the list: from C6 (buf <> 0, so the abort branch is not taken) to C7. The frame for locals has the shadow
   bytes M02 left (hi_shB); the buf block of rt_bl buflen bytes is live and not among the journal's start blocks (the
   malloc(buf) post gives it); the frames held are the harness's own only, so a frame of every other class is free
   for drivable_csv and check_csv (YG0d.v astack_malloc_realizes asks count_cid c (frames S) < fs_frames c). It runs
   memset(buf, 0x5a, bl), len = reac_rate_drivable_csv(mask, buf, buflen) and check_csv(buf, buflen, len, mask).
   Reaching C7 is the property: check_csv does not abort and no instrumented check fails. It returns at some float
   state fx' (f10 by the snprintf wrapper) with a zero rounding mode, the image's C7 values and the frame's shadow as
   at its start; besides hi_w3 and buf it may change runtime-owned bytes (its callees' side-stack frames). *)
Definition rate_csv_contract (I : rt_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : rt_renv) (pos : Z),
rt_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
rt_fsh segs (w_H W) memc (q_F e) (hi_shB I) ->
rt_cut segs (w_H W) memc regs e (hi_L6 I) ->
frames Sc = [(hi_cid I, pos)] ->
q_buf e <> 0 -> In (q_buf e, rt_bl (q_buflen e)) (ablocks B lyc Sc) ->
~ In (q_buf e, rt_bl (q_buflen e)) (ablocks B ly S) ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs (hi_c6 I) regs memc mdc)
(rt_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c7 I)
(rt_fxk [10] fx)
(fun a => rt_inw e (hi_w3 I) a \/ q_buf e <= a < q_buf e + rt_bl (q_buflen e) \/ aowned B lyc Sc a)
(fun W2 regs2 mem2 =>
rt_cut segs (w_H W2) mem2 regs2 e (hi_L7 I) /\
rt_fsh segs (w_H W2) mem2 (q_F e) (hi_shB I))).
End d.
(* =============================== LLVMFuzzerTestOneInput, the whole run ===============================
   fuzz_grant's exists-fx' text (lib/A/ACfn.v tfib_lib_pre_xf, tfib_lib_post_x, tfib_lib_contract_xf) over abstract
   segs, sink K, read-only range RLO .. RHI (arodata_okP, RtPgBase.v) and harness constants: the entry asks a zero
   rounding mode, and the function returns at some float state with a zero rounding mode (rate's harness changes
   fa0 and its callees fa0 and fa3-fa5). lib/A/RtPgLib.v instantiates it at image A's values; image B's twin at its own. *)
Section e. Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition rt_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) /\
asink_none segs K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
YK0o.frm_zero (@fp_csr fx).
Definition rt_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
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
(* Image B's bound obligation at the entry (0 < data and data + n <= 2^63, its checks of undefined behaviour at the
   header reads): the input is the image's empty block A_EMPTY or a live block, whose AR bounds give it
   (RtPgBase.rt_block_bounds). *)
Lemma rt_lib_pre_bounds : AR_laws segs B -> 0 < A_EMPTY -> A_EMPTY <= 2 ^ 63 ->
forall (regs : bvmap 5 word) ly S (W : world segs) mem md p n pl M,
rt_lib_pre_x regs ly S W mem md p n pl M -> 0 < p /\ p + n <= 2 ^ 63.
Proof.
intros LAWS H0 H1 regs ly S W mem md p n pl M HP.
destruct HP as (HF & _ & _ & _ & Hb & _). destruct HF as (HAR & _).
destruct Hb as [[-> ->] | [Hn Hin]]; [lia|].
destruct (rt_block_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hin) as (A & _ & C). lia.
Qed.

Definition rt_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (Kl : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
rt_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@fp_csr fx') /\
rt_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (Kl l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) Kl).
End e.
End c.
End b.

(* ===================== two image-independent facts the call-site lemmas of each image use ===================== *)
(* pp->len after the build is between 8 and 5440 (Pod/Spa.v buf_header): the pod request at C2 is len. *)
Lemma rt_len_bounds : forall rest, 8 <= rt_len rest <= 5440.
Proof.
intros rest. unfold rt_len.
destruct (Model.pod_build rest) as [r rest'] eqn:E. cbn [fst].
pose proof (Spa.buf_header r (Model.pod_build_wf rest r rest' E)) as (_ & _ & _ & H). exact H.
Qed.
Section ck. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* Every location of a cut list that a call kept keeps its value: what moves a cut list across a malloc. *)
Lemma rt_cut_keep : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : rt_renv) L,
rt_cut segs H mem regs e L ->
(forall r, In (LReg r) (map fst L) -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall b o, In (LCell b o) (map fst L) -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (rt_xv e b + o + i) = mbyte segs (mrestrict H mem) (rt_xv e b + o + i)) ->
rt_cut segs H mem' regs' e L.
Proof.
intros H mem mem' regs regs' e L HC Hr Hc. unfold rt_cut in *. rewrite Forall_forall in *.
intros f Hf. specialize (HC f Hf).
assert (Hin : In (fst f) (map fst L)) by (apply in_map; exact Hf).
destruct (fst f) as [r|b o]; cbn [rt_at] in *.
- rewrite (Hr r Hin). exact HC.
- intros k Hk. rewrite (Hc b o Hin (Z.of_nat k) ltac:(lia)). exact (HC k Hk).
Qed.
End ck.
