(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 26 of its 46 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_refusals (fuzz_segconf.c:516-529; fuzz_segconf.asan 0x873c8, 240 bytes, 60 instructions; frame 16 bytes):
   the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr
   of apost_base at the return). Functional content: the plain contract lib/Prog/check_refusals_c.v:10-42
   (check_refusals_pre :25-29), restated over the ASan reader rd = aview segs (w_H W) mem.
   c->refused <> m->refused or c->n_refusals <> m->n_kept aborts. The code reads c->refused (c + 0x34cc) and
   m->refused (m + 0x2008) and compares them (0x8741c), then c->n_refusals (c + 0x34c8) and m->n_kept (m + 0x23ac)
   and compares them (0x87454), all four with `lw` (sign-extended 32-bit values). It writes only its frame: unlike
   the plain build, the ASan build sets up its 16-byte frame at the entry, on the path that returns too.
   The abort site 0x87468 (after __asan_handle_no_return 0x87464) is reached from 0x8741c and 0x87454; both are dead
   under SegModel.check_refusals rcs mcs = true, the last conjunct of check_refusals_pre: the four words are u32_enc
   values (seg_spec.rconf_enc / mconf_encp), so equal sign extensions are equal values and the model's two
   equalities make both branches fall through.
   Post: the plain post is ret_void's `fun _ => True` with munch []; here apost_base with footprint [] (the frame is
   inside the call's own window [sp - STK_check_refusals, sp)) and the post tail sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract:
   - sa_addr rd c SEG_C_SIZE kills the two load4 check sites in c: c + 0x34cc (shadow byte `lb` 0x873f0, error arm
     __asan_report_load4 0x8747c) and c + 0x34c8 (shadow byte 0x87430, error arm 0x874a0).
   - sa_addr rd mm SEG_M_SIZE kills the two load4 check sites in m: m + 0x2008 (shadow byte 0x8740c, error arm
     0x87490) and m + 0x23ac (shadow byte 0x87444, error arm 0x874b4).
   - sa_heap of both blocks in place of the plain `apart _ _ lo sp`: c = malloc(0x40e8) and m = calloc(1, 0x2414)
     are the harness's blocks (PREMISES-A section 2.3), and a live heap block lies outside the stack window.
   - The shadow base is read through the GOT word 0xa2a50 and __asan_shadow_memory_dynamic_address 0xabff8
     (0x873d0-0x873dc; PREMISES-A section 1.5): AR's const cells as_got_shadow / as_shadow_cell
     (lib/Reusable/YG0f.v aso_const_law), so neither is a premise or a parameter.
   - No side-stack frame, no interceptor, no allocator entry: EV_check_refusals = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_refusals (fun _ => False): every byte outside the window
     [sp - STK_check_refusals, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow entry,
     and its one store is into its frame (`sd ra,8(sp)` 0x873cc); the abort and report arms are dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_refusals and STK_check_refusals are parameters (image A:
   A_check_refusals = 0x873c8; STK_check_refusals covers the 16-byte frame).
   Call site: LLVMFuzzerTestOneInput 0x855a8 (segA/evidence/callsites.asan.tsv).
   The WALK takes no runtime entry as a Section hypothesis: the code calls only __asan_handle_no_return and abort,
   on the dead abort path, and __asan_report_load4, on the dead error arms. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_refusals_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_check_refusals : Z := 0.
(* the plain check_refusals_pre over the reader: the two blocks (where they lie and their shadow added) and
   SegModel.check_refusals *)
Definition check_refusals_pre (ly : alayout) (S : astate) (rd : reader) (c mm : Z) (rcs : rconf) (mcs : mconf)
: Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf rd c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr rd c seg_spec.SEG_C_SIZE /\
mm <> 0 /\ mm mod 16 = 0 /\ sa_mconf rd mm mcs /\ sa_heap B ly S mm seg_spec.SEG_M_SIZE /\
sa_addr rd mm seg_spec.SEG_M_SIZE /\
check_refusals rcs mcs = true.
Definition check_refusals_contract (A_check_refusals STK_check_refusals : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c mm : Z) (rcs : rconf) (mcs : mconf),
afn_pre segs B STK_check_refusals ly S W regs mem md ch ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
getr regs 11 = w64 mm -> 0 <= mm < 2 ^ 64 ->
check_refusals_pre ly S (aview segs (w_H W) mem) c mm rcs mcs ->
st_nev S + EV_check_refusals <= EV_MAX ->
SRr segs W (cfg_at segs A_check_refusals regs mem md)
(apost_base segs B STK_check_refusals [] regs ly S W mem md EV_check_refusals
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_refusals (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
