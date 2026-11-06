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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths and module names changed; 32 of its 52 lines of code are new or changed and 49 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE ASSEMBLY of the piece value_nearest of segment M03 of LLVMFuzzerTestOneInput
   (0x80bc0). It chains the three lanes lib/A/HPgM3dBase.v cuts the piece into - the value dispatch with the Bool
   and Int arms (VAL 0x83364 -> FA / TAIL / CELL / RF / RFA), the Float arm with its five soft-float calls
   (FA 0x83430 -> TAIL / RFA) and the Tail (TAIL 0x83534 -> CELL / RF) - into lib/A/HPgSegM.v's
   hq_piece_M3d_value_stmt, the piece statement the segment's seam headamp_check_holds consumes.
   No instruction is walked here: the three lanes are its Section hypotheses, and the last theorem supplies them.

   proves function LLVMFuzzerTestOneInput (reuse search: at ossv/recipes 2d2ff01bb6f2, read by the released-proof
   index v5 built 2026-10-30T13:16:21Z, no released proof of these pieces; the lookup record is in the PR body).

   WHY THE TWO EXTRA CUTS. FA and TAIL are the piece's own, not the segment's: the Float arm is long enough to be
   a lane of its own, and the Int and the Float arms meet at 0x83534, so the range test against the param's top
   value and the two segment exits it leads to (CELL 0x83548 and RF 0x83460) are proved once. The Bool arm does
   not pass the Tail: a Bool value is 0 or 1 and every param's top value is at least 1, so the compiler elided
   the test and 0x833e4 jumps straight to CELL. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3dVal HPgM3dBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3dDisp HPgM3dFlt HPgM3dTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The three lanes, in the order their continuations depend on each other: the Tail needs only the two segment
   exits CELL and RF; the Float arm needs RFA and the Tail; the dispatch needs all five. *)
Section seam.
Hypothesis PDisp : hv_piece_disp_stmt B MT.
Hypothesis PFlt : hv_piece_flt_stmt B MT.
Hypothesis PTail : hv_piece_tail_stmt B MT.

Theorem headamp_m3d_value_holds : hq_piece_M3d_value_stmt rsegs B MT.
Proof.
unfold hq_piece_M3d_value_stmt.
intros cx POST r ev at0 m HS HCELL HRF HRFA.
assert (HTAIL : hv_from_TAIL B MT cx r POST at0 m)
  by exact (PTail cx POST r ev at0 m HS HCELL HRF).
assert (HFA : hv_from_FA B MT cx r POST at0 m)
  by exact (PFlt cx POST r ev at0 m HS HRFA HTAIL).
exact (PDisp cx POST r ev at0 m HS HCELL HRF HRFA HTAIL HFA).
Qed.

End seam.

(* The piece itself, from the three proved lanes. Its two Section hypotheses are runtime facts of their
   discharging files' exact types: MTL, the meter's laws (the soft-float call adapters of lib/A/HPgCallsSFI.v
   take it), and errno_low, the errno cell's place in the image (lib/Reusable/YCbq.v api_env, the type
   lib/A/HPgCalls.v's Section fr names errno_low); the dispatch and the Float arm need it to show that their
   stores to the real frame miss the errno cell that hq_base3 carries. *)
Section top.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

Theorem headamp_m3d_value_A : hq_piece_M3d_value_stmt rsegs B MT.
Proof.
exact (headamp_m3d_value_holds (hvd_disp_A B MT errno_low) (hvl_flt_A B MT MTL errno_low) (hvt_tail_A B MT)).
Qed.

End top.
End c.
End b.

Print Assumptions headamp_m3d_value_holds.
Print Assumptions headamp_m3d_value_A.
