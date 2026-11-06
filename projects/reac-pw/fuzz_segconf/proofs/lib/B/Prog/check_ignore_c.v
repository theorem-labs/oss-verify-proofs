(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 24 of its 44 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_ignore (fuzz_segconf.c:470-483; fuzz_segconf.asan 0x87288, 88 bytes, 22 instructions; frame 16 bytes): the
   contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of
   apost_base at the return). Functional content: the plain contract lib/Prog/check_ignore_c.v:10-41
   (check_ignore_pre :25-28), restated over the ASan reader rd = aview segs (w_H W) mem.
   got (a0) <> want->ignore aborts. The code reads want->ignore (want + 0x18, `lw`) and compares it with a0 as full
   registers (0x872b4). It writes only its frame: unlike the plain build, the ASan build sets up its 16-byte frame
   at the entry (`addi sp,sp,-16; sd ra,8(sp)`), on the path that returns too.
   The abort site 0x872dc (after __asan_handle_no_return 0x872d8) is reached from 0x872b4 only; it is dead under
   got = b2z b /\ Bool.eqb b (ms_ignore g) = true: the ignore field is flag_enc (ms_ignore g), the word 0 or 1, so
   the sign extension of `lw` equals a0.
   Post: the plain post is ret_void's `fun _ => True` with munch []; here apost_base with footprint [] (the frame is
   inside the call's own window [sp - STK_check_ignore, sp)) and the post tail sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract:
   - sa_addr rd want MSEG_SIZE kills the one load4 check site, want + 0x18 (shadow byte `lb` 0x872a8, error arm
     __asan_report_load4 0x872d4).
   - sa_heap B ly S want MSEG_SIZE in place of the plain `apart want MSEG_SIZE lo sp`: want = &m->seg[i] lies in
     the harness's block m = calloc(1, 0x2414) (PREMISES-A section 2.3), and a live heap block lies outside the
     stack window.
   - The shadow base is read through the GOT word 0xa2a50 and __asan_shadow_memory_dynamic_address 0xabff8
     (0x87290-0x87298; PREMISES-A section 1.5): AR's const cells as_got_shadow / as_shadow_cell
     (lib/Reusable/YG0f.v aso_const_law), so neither is a premise or a parameter.
   - No side-stack frame, no interceptor, no allocator entry: EV_check_ignore = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_ignore (fun _ => False): every byte outside the window
     [sp - STK_check_ignore, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow entry,
     and its one store is into its frame (`sd ra,8(sp)` 0x8728c); the abort and report arms are dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_ignore and STK_check_ignore are parameters (image A:
   A_check_ignore = 0x87288; STK_check_ignore covers the 16-byte frame).
   Call site: LLVMFuzzerTestOneInput 0x8553c (segA/evidence/callsites.asan.tsv).
   The WALK takes no runtime entry as a Section hypothesis: the code calls only __asan_handle_no_return and abort,
   on the dead abort path, and __asan_report_load4, on the dead error arm. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_ignore_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Definition EV_check_ignore : Z := 0.
(* the plain check_ignore_pre over the reader: the mseg entry want (where it lies and its shadow added), the
   argument value, and check_seg's third conjunct *)
Definition check_ignore_pre (ly : alayout) (S : astate) (rd : reader) (got want : Z) (b : bool) (g : mseg)
: Prop :=
want mod 4 = 0 /\ sa_mseg rd want g /\ sa_heap B ly S want seg_spec.MSEG_SIZE /\
sa_addr rd want seg_spec.MSEG_SIZE /\
got = seg_spec.b2z b /\ Bool.eqb b (ms_ignore g) = true.
Definition check_ignore_contract (A_check_ignore STK_check_ignore : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (got want : Z) (b : bool) (g : mseg),
afn_pre segs B STK_check_ignore ly S W regs mem md ch ->
getr regs 10 = w64 got -> 0 <= got < 2 ^ 64 ->
getr regs 11 = w64 want -> 0 <= want < 2 ^ 64 ->
check_ignore_pre ly S (aview segs (w_H W) mem) got want b g ->
st_nev S + EV_check_ignore <= EV_MAX ->
SRr segs W (cfg_at segs A_check_ignore regs mem md)
(apost_base segs B STK_check_ignore [] regs ly S W mem md EV_check_ignore
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_ignore (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
