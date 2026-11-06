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
(* The ASan-level contracts of reac-pw/fuzz_role's own functions. IMAGE-INDEPENDENT: no image module is Required;
   segs, the symbol record B, the meter MT, the sink K, every entry address, string address, table address and
   constant cell are Section variables or parameters, so image A (fuzz_role.asan) and image B (fuzz_role.asan-ubsan)
   instantiate the same texts. Statement text only: no function is proved here.

   Each callee contract has knock's form (APgCSpec.v): the caller's journal from its own entry to the call
   (ajournal ... lyc Sc W memc mdc k), the call's registers, the stack bound sp0 - STK <= sp - T_f, and the
   function's own premises; its post (rl_post) returns to ra with the caller's journal extended, the callee-saved
   registers kept, the frames, blocks, I/O state and meter as at the call, and every byte outside the callee's stack
   [sp - T_f, sp) and the bytes E it writes for its caller unchanged (one clause over all addresses, as fuzz_qdisc's
   leaves state it; it implies knock's three per-region clauses). Measured on image A (unstripped fuzz_role.asan
   sha256 6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6) and image B (unstripped
   fuzz_role.asan-ubsan sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a), capstone over the
   two files:
   - frames: reac_role_prop_parse `addi sp,sp,-0x60` (A 0x82ef0, B 0x83130); pod_nearest `addi sp,sp,-0x40`
     (A 0x82ccc, B 0x82eb4) and below it __addtf3's `addi sp,sp,-0x30` (A 0x839d8, B 0x83c78), the deepest of its
     soft-float callees (the others take no frame); check_absent, check_role, check_malformed, check_answer,
     check_code and reac_role_refuse_code `addi sp,sp,-0x10`; reac_role_cfg_changes and reac_role_cfg_apply_state
     take none. The strcmp wrapper (called by parse, check_answer, check_code) uses 2 ESTACK below its sp
     (lib/Reusable AStrcmpDef's astrcmp_realizes, the text of record in the released fuzz_identity tree).
   - float registers: parse writes fa3, fa4, fa5 (f13-f15: fld, fcvt.d.s, fadd.d, A 0x832ac-0x832e4); pod_nearest
     writes fa5 (fmv.w.x, A 0x82d14, B 0x82efc) and saves and restores fs0 (fsd / fld); both accrue fflags and write
     no rounding mode; parse's fadd.d and the soft-float addition read the dynamic rounding mode, hence the
     frm_zero premise.
   - abort paths: each check function calls the no-return helper and abort only on its failure branch (A
     0x82bd4 / 0x82bfc / 0x82c28 / 0x82c78 / 0x82cc4); every error-path call (an __asan_report_ entry) sits behind an
     instrumented check that the premises make pass. Reaching ra at all is the content of a check's contract. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout Spa Role Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The stack each callee uses below its caller's sp (both images; see the header). *)
Definition T_parse_STK : Z := 96 + 2 * ESTACK.
Definition T_nearest_STK : Z := 64 + 48.
Definition T_check_STK : Z := 16.
Definition T_cmp_STK : Z := 16 + 2 * ESTACK.
Definition T_leaf_STK : Z := 0.

(* reac_role_cfg_changes(cur, req) = (cur != req), the two compared as 64-bit words. *)
Definition rl_changes (cur req : Z) : Z := if cur =? req then 0 else 1.
(* reac_role_refuse_code(r) for r the 64-bit word in a0 (the `bgeu` against 1): codes[0] or codes[1] of its table
   for r <= 1, else the literal the compiler put on that path (codes[0]'s text in both images). *)
Definition rl_refuse (c0 c1 cov r : Z) : Z := if r =? 0 then c0 else if r =? 1 then c1 else cov.
(* reac_role_prop_parse's answer: (None, -1) for a NULL argument, else Role.parse_model of the pod bytes (the plain
   contract's parse_res). *)
Definition rl_parse_res (null : bool) (bs : list byte) : option Role.role * Z :=
if null then (None, -1) else Role.parse_model bs.
(* pod_nearest's return value: 1 on Some, 0 on None (the plain contract's pod_near_rc). *)
Definition rl_near_rc (o : option Z) : Z := match o with Some _ => 1 | None => 0 end.

(* ===================== LLVMFuzzerTestOneInput's two middle segments: what each image fills =====================
   The segments M01 (after malloc(pp) returns, to the `jal` of malloc(pod)) and M02 (after malloc(pod) returns, to
   the instruction after check_code's return, which moves pod into a0 for the free) are the plain walk's cuts
   (lib/Prog/LLVMFuzzerTestOneInput_c.v ROLE_BUILD / ROLE_MALLOC2 / ROLE_CHECK / ROLE_FREE). An image gives:
   - hi_cid: the side-stack class of the frame for locals (image A 3: `addi a0,zero,0x1a0` + `jal
     __asan_stack_malloc_3` at 0x7fff4 / 0x7fff8; image B 4);
   - hi_c1 .. hi_c4: the four pcs (cuts C1 = M01's first pc, C2 = the malloc(pod) `jal`, C3 = the pc after it,
     C4 = the pc after check_code's return);
   - hi_rsz: the real frame's size below S (R + hi_rsz <= S);
   - hi_L1 .. hi_L4: the live values at C1 .. C4 (RPgBase rl_cut);
   - hi_shA / hi_shB: the shadow bytes of the frame for locals at C1, C2, C3 (the prologue's) and at C4 (the role
     cell in scope);
   - hi_w1 / hi_w2: the ranges M01 / M02 write besides the pp / pod block and the callees' stacks (frame objects,
     their shadow bytes, real-frame cells);
   - hi_rz: real-frame ranges (offset from R, length) whose shadow bytes the code checks (they must mark the bytes
     usable);
   - hi_globs: the registered globals (address, size) whose bytes the runtime marked usable and the segments read;
   - hi_strs / hi_cells: the strings (rl_cstr) and 8-byte constant cells (rl_ro_cells) the segments' callees read. *)
Record rl_himg := RLHImg {
hi_cid : Z;
hi_c1 : Z; hi_c2 : Z; hi_c3 : Z; hi_c4 : Z;
hi_rsz : Z;
hi_L1 : list (rl_loc * rl_x); hi_L2 : list (rl_loc * rl_x); hi_L3 : list (rl_loc * rl_x); hi_L4 : list (rl_loc * rl_x);
hi_shA : list Z; hi_shB : list Z;
hi_w1 : list (rl_x * Z * Z); hi_w2 : list (rl_x * Z * Z);
hi_rz : list (Z * Z);
hi_globs : list (Z * Z);
hi_strs : list (Z * list Z);
hi_cells : list (Z * Z) }.
(* The stack the segments' callees may use below R (the harness sp throughout both segments): the allocator's
   ASTACK, so that the malloc(pod) at C2 and the free(pod) after C4 fit too; it bounds every callee of M01
   (__asan_memset / __asan_memcpy ESTACK, the strlen wrapper 2 ESTACK) and of M02 (T_parse_STK and the others). *)
Definition T_SEG_STK : Z := ASTACK.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== the post of a callee ===================================== *)
(* The call returns to ra (getr regs 1) at some float state fx2 with FX fx2, its journal extends the caller's
   (k events: none of these callees allocates), and every byte outside its stack [sp - T, sp) and outside E is as
   at the call. R is what the function computes. *)
Definition rl_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\ FX fx2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
R W2 regs2 mem2.

(* The premises every callee contract shares (knock's, without the frame-chain premise: no callee here records a
   call trace): the caller's journal, the call's ra / gp / tp, and the callee's stack T inside the caller's
   stack window. *)
Definition rl_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - T /\ spZ regs <= sp0 /\
st_nev S + k <= EV_MAX.

(* ========================== check_absent(rc, role) (fuzz_role.c:65-76) ==========================
   Returns when a0 = 0 and a1 = 0x5a (ROLE_UNSET), both 64-bit words; else it aborts. *)
Definition rl_check_absent_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 0 -> getr regs 11 = w64 0x5a ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ========================== check_role(rc, role, want) (fuzz_role.c:78-89) ==========================
   Returns when a0 = 1 and a1 = a2 (64-bit words); else it aborts. *)
Definition rl_check_role_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 1 -> getr regs 11 = getr regs 12 ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ======================== check_malformed(rc, role) (fuzz_role.c:91-105) ========================
   Returns when a0 = -1 and a1 = 0x5a (64-bit words); else it aborts. *)
Definition rl_check_malformed_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 (-1) -> getr regs 11 = w64 0x5a ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ============================ reac_role_cfg_changes(cur, req) (reac_role_cfg.c:22-25) ============================
   a0 := (cur != req) on the 64-bit words; no stack, no store. *)
Definition rl_cfg_changes_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (cur req : Z),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 cur -> 0 <= cur < 2 ^ 64 -> getr regs 11 = w64 req -> 0 <= req < 2 ^ 64 ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ regs2 _ => getr regs2 10 = w64 (rl_changes cur req))).

(* ===================== reac_role_cfg_apply_state(cur, req) (reac_role_cfg.c:27-37) =====================
   a0 := the address sa of "applied" when cur = req (64-bit words), else the address sp' of
   "role_reestablish_pending"; it only forms the address (auipc / addi). sa and sp' are the image's. *)
Definition rl_cfg_apply_state_specX (a sa sp' : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (cur req : Z),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 cur -> 0 <= cur < 2 ^ 64 -> getr regs 11 = w64 req -> 0 <= req < 2 ^ 64 ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_leaf_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 = w64 (if cur =? req then sa else sp'))).

(* ======================= check_answer(changes, state, cur, req) (fuzz_role.c:107-119) =======================
   Returns when a0 = (cur != req) and the string at a1 has the text of "applied" when cur = req, else of
   "role_reestablish_pending"; it compares a1 by the strcmp wrapper with its own literal (la or lp, the image's
   addresses: the ASan images keep the literals apart from apply_state's, so the compare is by text). *)
Definition rl_check_answer_specX (a la lp : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (cur req s : Z),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 (rl_changes cur req) -> getr regs 11 = w64 s ->
getr regs 12 = w64 cur -> 0 <= cur < 2 ^ 64 -> getr regs 13 = w64 req -> 0 <= req < 2 ^ 64 ->
rl_cstr segs (w_H W) memc s (if cur =? req then STR_APPLIED else STR_PENDING) ->
rl_cstr segs (w_H W) memc la STR_APPLIED -> rl_cstr segs (w_H W) memc lp STR_PENDING ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ========================== reac_role_refuse_code(r) (reac_role_cfg.c:14-20) ==========================
   For r = the 64-bit word in a0: r <= 1 loads codes[r] from the 16-byte table at tbl (one instrumented 8-byte
   load: the table's 16 bytes are marked usable), else returns cov. The table and its two values are the image's. *)
Definition rl_refuse_code_specX (a tbl c0 c1 cov : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
0 <= c0 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= cov < 2 ^ 64 ->
(forall i, 0 <= i < 16 -> in_img segs (tbl + i)) ->
val_mem segs (mrestrict (w_H W) memc) tbl 8 c0 -> val_mem segs (mrestrict (w_H W) memc) (tbl + 8) 8 c1 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF tbl 16 ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False)
(fun _ regs2 _ => getr regs2 10 = w64 (rl_refuse c0 c1 cov (bv_unsigned (getr regs 10))))).

(* ========================= check_code(none, malformed) (fuzz_role.c:121-131) =========================
   Returns when the string at a0 has the text "none" and the one at a1 the text "malformed"; it compares them by
   the strcmp wrapper with its own literals ln and lm (the image's addresses). *)
Definition rl_check_code_specX (a ln lm : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (sn sm : Z),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 sn -> getr regs 11 = w64 sm ->
rl_cstr segs (w_H W) memc sn STR_NONE -> rl_cstr segs (w_H W) memc sm STR_MALFORMED ->
rl_cstr segs (w_H W) memc ln STR_NONE -> rl_cstr segs (w_H W) memc lm STR_MALFORMED ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).

(* ================================ pod_nearest(f, out) (pod.h:152-171) ================================
   The out-of-line copy with lo = INT32_MIN and hi = INT32_MAX folded in: fa0 holds the binary32 b (NaN-boxed);
   it returns 1 and stores the nearest integer r as 8 bytes at out (one instrumented 8-byte store: out's 8 bytes
   are marked usable) when Nearest.nearest b gives Some r, else returns 0 and stores nothing (the plain contract's
   pod_nearest_contract, Prog/pod_nearest_c.v). Its soft-float callees (__extendsftf2, __lttf2 / __letf2,
   __floatditf, __subtf3 -> __addtf3, __getf2 / __gttf2) make no instrumented access; their walks run them as the
   CJ contracts on the normalized store, whose step back needs the read-only agreement, hence rom_view (YG0d.v):
   every byte of a read-only segment reads as the image's. *)
Definition rl_pod_nearest_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (out b : Z),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_nearest_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 out -> 0 <= b < 2 ^ 32 ->
Sem.reg_get (@fp_regs fx) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
rl_wcell STK sp0 lyc own (spZ regs) T_nearest_STK out 8 -> out mod 8 = 0 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF out 8 ->
rom_view segs W memc ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_nearest_STK regs lyc Sc W memc mdc
(rl_fxk [15] fx)
(fun x => Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\ out <= x < out + 8)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (rl_near_rc (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX)) /\
match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
| Some r => val_mem segs (mrestrict (w_H W2) mem2) out 8 (r mod 2 ^ 64)
| None => True
end)).

(* ====================== reac_role_prop_parse(props, out_role) (reac_role_cfg.c:63-104) ======================
   a0 = 0 (null) returns -1 at once; else the len >= 8 bytes bs at P (top size word len - 8) are parsed: the answer
   is Role.parse_model bs (the plain contract's parse_res), and on a role the 4 bytes of role_z at Q (one
   instrumented 4-byte store: Q's 4 bytes are marked usable). Every read of the pod is an instrumented load inside
   [P, P + len) (the pod's len bytes are marked usable); the key compare is the strcmp wrapper against the literal
   "reac.cfg.role" at akey (the image's address); the doubles it compares with are read from read-only data without
   a shadow check: dcs lists those cells and their values (the image's: 0.5, -2^31, 2^31 in image A; image B adds
   its float-cast checks' bounds). *)
Definition rl_parse_specX (a akey : Z) (dcs : list (Z * Z)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(null : bool) (P Q : Z) (bs : list byte),
rl_pre STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 (if null then 0 else P) -> getr regs 11 = w64 Q ->
(null = false ->
 0 < P /\ P mod 16 = 0 /\ 8 <= Z.of_nat (length bs) /\ Spa.u32_at bs 0 = Z.of_nat (length bs) - 8 /\
 P + Z.of_nat (length bs) <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) P (map (fun x : byte => bv_unsigned x) bs) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF P (Z.of_nat (length bs)) /\
 shadow_hull_vis (aview segs (w_H W) memc) P (Z.of_nat (length bs)) /\
 amem_range P (Z.of_nat (length bs)) /\
 (P + Z.of_nat (length bs) <= spZ regs - T_parse_STK \/ spZ regs <= P)) ->
rl_wcell STK sp0 lyc own (spZ regs) T_parse_STK Q 4 -> Q mod 4 = 0 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF Q 4 ->
rl_cstr segs (w_H W) memc akey (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY) ->
rl_ro_cells segs (w_H W) memc dcs ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs a regs memc mdc)
(rl_post STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc
(rl_fxk [13; 14; 15] fx)
(fun x => fst (rl_parse_res null bs) <> None /\ Q <= x < Q + 4)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (snd (rl_parse_res null bs)) /\
match fst (rl_parse_res null bs) with
| Some r => val_mem segs (mrestrict (w_H W2) mem2) Q 4 (Role.role_z r)
| None => True
end)).

(* ============================ LLVMFuzzerTestOneInput's two middle segments ============================
   The ASan-level counterparts of the plain walk's role_build_contract and role_check_contract
   (lib/Prog/LLVMFuzzerTestOneInput_c.v), with the same names, the same cuts and the same Pod model (Model.pod_build,
   Layout.pp_bytes, rl_len = role_len), over the image's rl_himg I. A segment runs inside the harness's own journal
   (from its entry: sp0 = S, own = the harness's side-stack frame); it ends at a fixed pc (not at ra), with sp, gp, tp
   as at its start, the frames, blocks, I/O state and meter as at its start, and every byte outside the callees'
   stack [R - T_SEG_STK, R), the image's write ranges and the block it fills as at its start. *)
Definition rl_seg_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
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
(* What both segments ask at their start: the harness's journal from its entry; sp = R; R 16-aligned with the real
   frame below S = sp0 and the callees' stack inside the journal's window; the frame for locals F = the side-stack
   frame (hi_cid, pos) the harness holds, with the prologue's shadow bytes; the pp block live; the flags byte; the
   read-only data as in the image (the harness pre's arodata_okP, which the journal keeps, and rom_view, every
   byte of a read-only segment as the image's, which pod_nearest's soft-float callees need and every callee's post
   keeps); the shadow facts the code's instrumented checks and its callees read; and, last, pp is not among the
   journal's start blocks (ablocks B ly S): a block of the start keeps its bytes under the journal (YCbq.v ajournal,
   the clause for blocks live at both ends), and a write to pp is the journal's own only as a block made since the
   start (YCbq.v awr_byte, in_tmp_block; RPgBase.rl_fresh_awr). The harness's malloc(pp), after the journal's
   start and before both segments, gives it. *)
Definition rl_seg_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(I : rl_himg) (RLO RHI : Z) (e : rl_env) (pos : Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\ st_nev S + k <= EV_MAX /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
e_S e = sp0 /\ e_R e mod 16 = 0 /\ e_R e + hi_rsz I <= e_S e /\ sp0 - STK <= e_R e - T_SEG_STK /\
In (hi_cid I, pos) own /\ e_F e = frame_addr lyc (hi_cid I) pos /\
rl_fsh segs (w_H W) memc (e_F e) (hi_shA I) /\
e_pp e <> 0 /\ In (e_pp e, Layout.PP_SIZE) (ablocks B lyc Sc) /\
0 <= e_fl e < 256 /\
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) /\
Forall (fun g => range_addressable (aview segs (w_H W) memc) SHADOW_OFF (fst g) (snd g)) (hi_globs I) /\
Forall (fun z => range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_R e + fst z) (snd z)) (hi_rz I) /\
Forall (fun s => rl_cstr segs (w_H W) memc (fst s) (snd s)) (hi_strs I) /\
rl_ro_cells segs (w_H W) memc (hi_cells I) /\
rom_view segs W memc /\
~ In (e_pp e, Layout.PP_SIZE) (ablocks B ly S).

(* M01, the build: from C1 (pp <> 0, so the abort branch is not taken) to C2 (the malloc(pod) `jal`, not
   executed). The input bytes after the flags byte, rest, lie at src (shadow-checked reads, marked usable, their
   shadow hull readable and low enough for the shadow map: M01's __asan_memcpy calls copy from the input, and its
   contract asks amem_range and shadow_hull_vis of the source), apart from the ranges M01 writes; len is rl_len rest.
   It returns at C2 with the image's C2 values, the frame's shadow
   back to the prologue's, and the pp block holding Layout.pp_bytes of the record Model.pod_build made of rest (the
   corruption included); it changes no float register (no float instruction in M01 or in its callees). Its writes
   to pp are the journal's own by rl_seg_pre's last conjunct. *)
Definition role_build_contract (I : rl_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : rl_env) (pos : Z) (rest : list byte),
rl_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
rl_cut segs (w_H W) memc regs e (hi_L1 I) ->
e_left e = Z.of_nat (length rest) -> e_len e = rl_len rest ->
garr8 segs (mrestrict (w_H W) memc) (e_src e) (map (fun x : byte => bv_unsigned x) rest) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_src e) (e_left e) ->
0 < e_src e -> e_src e + e_left e <= 2 ^ 63 -> amem_range (e_src e) (e_left e) ->
(0 < e_left e -> shadow_hull_vis (aview segs (w_H W) memc) (e_src e) (e_left e)) ->
(forall a, e_src e <= a < e_src e + e_left e ->
 ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ rl_inw e (hi_w1 I) a /\ ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)) ->
SRr segs W (cfg_at segs (hi_c1 I) regs memc mdc)
(rl_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c2 I)
(fun f => f = fx)
(fun a => rl_inw e (hi_w1 I) a \/ e_pp e <= a < e_pp e + Layout.PP_SIZE)
(fun W2 regs2 mem2 =>
rl_cut segs (w_H W2) mem2 regs2 e (hi_L2 I) /\
rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shA I) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pp e)
(map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest)))))).

(* M02, the checks: from C3 (pod <> 0, so the abort branch is not taken) to C4. The pp block holds the record of
   some input inp (as M01 leaves it) and the pod block of len = rl_len inp bytes is live. It copies pp's len bytes
   into pod, runs the parse on pod (or NULL by flags bit 0), the inlined expect_role scan, the check its answer
   selects, cfg_changes, apply_state, check_answer, refuse_code twice and check_code; reaching C4 is the property:
   no check aborts and no instrumented check fails. It returns at some float state fx' (fa0 by the harness's flw,
   fa3-fa5 by the parse and pod_nearest) with a zero rounding mode, the image's C4 values and the role cell's
   granule in scope (hi_shB). The pod block is not among the journal's start blocks, as pp in rl_seg_pre (its
   memcpy writes pod; the malloc(pod) post gives it). *)
Definition role_check_contract (I : rl_himg) (RLO RHI : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(e : rl_env) (pos : Z) (inp : list byte),
rl_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I RLO RHI e pos ->
rl_cut segs (w_H W) memc regs e (hi_L3 I) ->
e_len e = rl_len inp ->
garr8 segs (mrestrict (w_H W) memc) (e_pp e)
(map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build inp)))) ->
e_pod e <> 0 -> In (e_pod e, e_len e) (ablocks B lyc Sc) ->
~ In (e_pod e, e_len e) (ablocks B ly S) ->
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs (hi_c3 I) regs memc mdc)
(rl_seg_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c4 I)
(rl_fxk [10; 13; 14; 15] fx)
(fun a => rl_inw e (hi_w2 I) a \/ e_pod e <= a < e_pod e + e_len e)
(fun W2 regs2 mem2 =>
rl_cut segs (w_H W2) mem2 regs2 e (hi_L4 I) /\
rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shB I))).
End d.

(* =============================== LLVMFuzzerTestOneInput, the whole run ===============================
   fuzz_grant's exists-fx' text (lib/A/ACfn.v tfib_lib_pre_xf, tfib_lib_post_x, tfib_lib_contract_xf) over abstract
   segs, sink K, read-only range RLO .. RHI (arodata_okP, RPgBase.v) and harness constants: the entry asks a zero
   rounding mode, and the function returns at some float state with a zero rounding mode (role's harness changes
   fa0 and its callees fa3-fa5). lib/A/RPgLib.v instantiates it at image A's values; image B's twin at its own. *)
Section e. Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition rl_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
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
Definition rl_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
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
Definition rl_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (Kl : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
rl_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@fp_csr fx') /\
rl_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (Kl l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) Kl).
End e.
End c.
End b.
