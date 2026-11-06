(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are
   restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc from
   proofs/libreac/fuzz_knock/lib/A/APgCSpec.v (the Section form of its lines 32-164) and
   proofs/libreac/fuzz_knock/lib/A/ACfn.v (lines 27-71, the harness contract tfib_lib_pre_x / _post_x /
   _contract_x; its lines 72-73, tfib_lib_contract_x_all, are not carried here) at origin/ossv/recipes
   6ebe35ba632, with their module paths changed (h-small-a3). rule 24 (reuse): no function is proved here;
   this file states the three ASan-level contracts only.

   THE QDISC CHANGES, and why each one is there.
   - knock's three callees (reac_knock_init / _heard / _step) write a 40-byte struct in the caller's fake
     frame; qdisc's two callees (reac_qdisc_etf_catchup_slots, check_slots) are register-only leaves that
     write nothing but check_slots' own return-address slot. So kn_post_* 's object clause (obj_at) and
     its FOUR memory conjuncts -- the stack side above alloc_ceiling outside the callee's window, the live
     blocks, the frames and their shadow, and the image -- are replaced by ONE memory clause,
     `aview W2 mem2 a = aview W memc a` outside [sp - STK_f, sp), which implies all four and needs no
     object. Its proof needs no block, separation or frame law of AR either (knock's four conjuncts needed
     AR's block and separation facts to place the object): check_slots' walk takes from the caller's
     journal only its stack-presence clause (`forall a, sp0 - STK <= a < sp0 -> apresent ..`) and astk_ok
     (sp0's alignment and bounds), with the contract's two stack-window premises. Both posts state the
     clause in that same shape, so the text does not depend on
     the value of either STK_f. T_slots_STK is 0 (the leaf has no frame: `addi a2,zero,1` is its first
     instruction in both images, image A 0x7e94c and image B 0x7e984, no sp move; at 0 the excluded window
     is empty and the clause holds at every address), T_check_STK is 16 (image A 0x7e870 and image B
     0x7e8a4 `addi sp,sp,-0x10`, then `sd ra,8(sp)`).
   - both leaves divide by 10^6 with the 8-byte constant 0x431BDE82D7B634DB = ceil(2 ^ 82 / 10 ^ 6)
     (lib/Prog/qdisc_div.v:7-10). The load is NOT shadow-checked in either image (image A
     `auipc a1,0xfff92` 0x7e8b4 + `ld a1,-0x564(a1)` 0x7e8b8 -> 0x10350, and the same cell 0x10350 in the
     asan-ubsan image from 0x7e8e8 / -0x598; capstone 5.0.7 over the pinned bytes). The cell is .rodata, so
     its value is not derivable from an abstract `segs`: the contract takes its ADDRESS as a parameter `am`
     and its value as the premise `val_mem segs .. am 8 QD_MAGIC`. Each image discharges that premise from
     its own read-only-data fact. The constant is image-shared: the 8 bytes at 0x10350 are
     0x431BDE82D7B634DB in both fuzz_qdisc.asan (980e2b845852) and fuzz_qdisc.asan-ubsan (eb657d77bd4b),
     read out of the pinned files by this lane and checked independently by h-small-a3; only `am` could
     differ between images (here both load 0x10350).
   - the result: catchup's post pins a0 to slots_spec (lib/Prog/qdisc_spec.v:8-11, the C source's
     slots_of); check_slots returns void, and its contract's content is that it RETURNS -- its abort
     (the abort call at image A 0x7e8dc, reached only from `bne a0,a3` at 0x7e8cc) is
     unreachable when a0 is slots_spec of the same (lead, fps). That is the harness's property.
   - the harness contract is ACfn's text with knock's names changed and its read-only premise written over
     lib/A/QPgBase.v's image-independent in_roP / arodata_okP, so that image B instantiates the same text.

   IMAGE-INDEPENDENT: this file Requires no image module. `segs`, the symbol record `B`, the meter `MT`,
   the sink `K`, the entry addresses and the harness constants are all Section variables or parameters. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCSpec.v, with its module paths and module names changed; 6 of its 69 lines of code are new or changed and 64 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths and module names changed; 25 of its 45 lines of code are new or changed and 49 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE ASSEMBLY of the piece value_nearest of segment M03 of LLVMFuzzerTestOneInput
   (0x80c40). It chains the four lanes lib/AU/HPgM3dBaseU.v cuts the piece into - the value dispatch with the
   Bool and Int arms (VAL 0x83490 -> FA / TAIL / CELL / RF), the Float arm with __extendsftf2 and the pod.h:160
   float-cast check (FA 0x83578 -> CV / RF), the rounding half of the inlined pod_nearest with __floatditf,
   __subtf3, __getf2 and __lttf2 (CV 0x83608 -> TAIL / RF) and the Tail (TAIL 0x83694 -> CELL / RF) - into
   lib/AU/HPgSegM.v's hqu_piece_M3d_value_stmt, the piece statement the segment's seam headamp_check_holds
   consumes. No instruction is walked here: lib/AU/HPgM3dBaseU.v hvu_value_of_lanes is the chaining, and the
   last theorem supplies the four lanes.

   proves function LLVMFuzzerTestOneInput (reuse search: at ossv/recipes 2d2ff01bb6f2, read by the released-proof
   index v5 built 2026-10-30T13:16:21Z, no released proof of these pieces; the lookup record is in the PR body).

   WHY FOUR LANES AND NOT IMAGE A'S THREE. Image B's Float arm makes SIX soft-float calls where image A makes
   five: pod.h:160's float-cast check is `flt.s fs0,fs3` against fs3 = 2^63 (binary32) AND a second __gttf2 of
   the binary128 against -(2^63 + 1) (the cells R+0xb8 / R+0xb0), which image A does not have. The arm is
   therefore cut once more, at CV 0x83608 (`fcvt.l.s`), so that the part before the rounding and the rounding
   itself are proved apart. The Bool arm does not pass the Tail: a Bool value is 0 or 1 and every param's top
   value is at least 1, so the compiler elided the test and 0x83520 jumps straight to CELL.

   THE TWO SECTION HYPOTHESES are runtime facts of their discharging files' exact types: MTL, the meter's laws
   (lib/AU/HPgCallsSFIU.v's soft-float call adapters take it), and errno_low, the errno cell's place in the
   image (lib/Reusable/YCbq.v api_env, the type lib/A/HPgCalls.v's Section fr names errno_low); the dispatch,
   the Float arm and the rounding need it to show that their stores to the real frame and __subtf3's frame below
   R miss the errno cell that hqu_base3 carries. Image A discharges the same hypothesis with lib/A/ACeg.v
   tl_env; image B's frame has no twin of tl_env yet. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgM3dBaseU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgM3dTailU HPgM3dDispU HPgM3dFltU HPgM3dCvU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The four lanes, in the order their continuations depend on each other: the Tail needs only the two segment
   exits CELL and RF; the rounding needs RF and the Tail; the Float arm needs RF and the rounding; the dispatch
   needs all four. *)
Section seam.
Hypothesis PDisp : @hvu_piece_disp_stmt fx rc SK B MT.
Hypothesis PFlt : @hvu_piece_flt_stmt fx rc SK B MT.
Hypothesis PCv : @hvu_piece_cv_stmt fx rc SK B MT.
Hypothesis PTail : @hvu_piece_tail_stmt fx rc SK B MT.

Theorem headamp_m3d_value_holds_B : @hqu_piece_M3d_value_stmt fx rc SK rsegs B MT.
Proof. exact (hvu_value_of_lanes B MT PDisp PFlt PCv PTail). Qed.

End seam.

Section top.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

Theorem headamp_m3d_value_B : @hqu_piece_M3d_value_stmt fx rc SK rsegs B MT.
Proof.
exact (headamp_m3d_value_holds_B (hvu_disp_B B MT errno_low) (hvu_flt_B B MT MTL)
         (hvu_cv_B B MT MTL errno_low) (hvu_tail_B B MT)).
Qed.

End top.
End c.
End b.

Print Assumptions headamp_m3d_value_holds_B.
Print Assumptions headamp_m3d_value_B.
