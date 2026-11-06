(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignore_file_c.v; 15 of its 42 lines of code are new or changed and 14 lines of the source are left out. *)
(* reac_segconf_init (reac_segconf.c:19-22; fuzz_segconf.asan 0x87a54, 36 bytes, 9 instructions; frame 16 bytes, no
   side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_segconf_init_c.v:10-41, restated over the ASan
   reader; its reac_segconf_init_pre (:24-26) keeps its name here.
   What the code does (objdump of fuzz_segconf.asan, 0x87a54-0x87a74): addi sp,sp,-16; sd ra; a1 = 0;
   a2 = 0x40e8 = 16616; jal __asan_memset (0x87a68); ld ra; addi sp,sp,16; ret. In image A this is a CALL with a
   16-byte frame, not the plain image's tail call `j memset` (plain contract :10-12): it returns to its own
   caller with memset's a0, which is c (the kit's memset post: a0 = d). The post is the plain one: a0 = c, the
   16616 bytes at c are zero, and they encode SegModel.rconf0 (seg_spec.rconf_enc_zero, lib/Prog/seg_spec.v:511).
   What it reads: nothing of its own (no inline check, no load of the shadow base). What it writes: its frame,
   inside its stack window, and [c, c + 16616) through memset, so its footprint is [(c, c + 16616)], the plain
   write list. No abort site (provenance/evidence/image-tables/program.asan.tsv line 18). NAME PREMISE: none, it takes no string, so
   it does not use the family's query_pre (lib/A/Prog/reac_segconf_find_c.v).
   ASAN FACTS ADDED over the plain contract:
   - inline checks: none (program.asan.tsv line 18: 0 report calls).
   - __asan_memset's own range check over [c, c + 16616) (callsites.asan.tsv line 227: a1 = 0 at 0x87a68):
     killed by reac_segconf_init_pre's sa_addr rd c SEG_C_SIZE (range_addressable and shadow_hull_vis, the
     kit's aintrin_realizes premises, lib/Reusable/YG0d.v:329-331).
   - where the block lies: sa_heap, a live heap block (malloc(0x40e8) at LLVMFuzzerTestOneInput 0x84f80, kept in
     s6, stored at 0x84f98, tested non-zero at 0x84f9c, reloaded as a0 = ld 160(s1) at 0x84fe4 for the call at
     0x84fec), never an address bound against the image's end. The kit's AR_blocks_law (YG0d.v:431-437) gives
     its bytes present and not runtime-owned, below alloc_ceiling <= ly_stk_lo, so memset's dest_ok
     (YG0d.v:320-321; writable_at by apresent_writable, YCbq.v:878) follows from it: the plain rw_cells, stack_ok
     and apart conjuncts are not restated.
   - no side-stack frame, no printf, no string interceptor (so no arodata_okP: aintrin_realizes asks no
     read-only view): apost_base, EV_reac_segconf_init = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK (fun a => c <= a < c + SEG_C_SIZE) in the post (SegABase.v's sa_kept,
     found by the G4 / G5 walk of check_absent: the journal keeps no shadow of an image object). True of the code:
     its only own store is ra into its frame (0x87a58); it takes no side-stack frame and calls no set_shadow
     entry; memset's post keeps every byte outside [c, c + 16616) and its ESTACK scratch (aintrin_realizes,
     YG0d.v:343), which lies in the window when STK >= 16 + ESTACK.
   Call site (provenance/evidence/image-tables/callsites.asan.tsv line 6): LLVMFuzzerTestOneInput 0x84fec, a0 = the malloc(0x40e8)
   block above.
   image A: A_reac_segconf_init = 0x87a54; STK_reac_segconf_init = 16 + ESTACK (INFERENCE: its frame and the
   ESTACK window aintrin_realizes's ecall_pre asks below it, YG0d.v:286-292).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_init, STK_reac_segconf_init and every image cell
   are parameters (or fields of B).
   The WALK takes these runtime entries as Section hypotheses:
     aintrin_realizes OSet (YG0d.v:326) at pc_memset, the checked __asan_memset (image A 0x55d7c): the kit's
     text, the image-A owner's frame, as fuzz_command's socket_send_c.v:60-61 at 501c0d516c69 takes it; "Not in this
     layer" in provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626), not a row.
   They are NOT premises of this contract: the statement does not mention them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the plain reac_segconf_init_pre over the reader rd = aview segs (w_H W) mem: c is nonzero and 16-aligned, a
   live heap block of 16616 bytes (the plain rw_cells / apart / stack_ok follow from it and afn_pre), and its
   bytes are addressable for memset's range check. Outside the sections: reac_segconf_init_pre segs B ly S rd c. *)
Definition reac_segconf_init_pre (ly : alayout) (S : astate) (rd : reader) (c : Z) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\ sa_addr rd c seg_spec.SEG_C_SIZE.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_reac_segconf_init : Z := 0.
Definition reac_segconf_init_contract (A_reac_segconf_init STK_reac_segconf_init : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c : Z),
afn_pre segs B STK_reac_segconf_init ly S W regs mem md ch ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
reac_segconf_init_pre ly S (aview segs (w_H W) mem) c ->
st_nev S + EV_reac_segconf_init <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_init regs mem md)
(apost_base segs B STK_reac_segconf_init [(c, c + seg_spec.SEG_C_SIZE)] regs ly S W mem md EV_reac_segconf_init
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 c /\
 sa_bytes (aview segs (w_H W') mem') c (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE)) /\
 sa_rconf (aview segs (w_H W') mem') c rconf0 /\
 sa_kept segs W mem W' mem' regs STK_reac_segconf_init (fun a => c <= a < c + seg_spec.SEG_C_SIZE) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
