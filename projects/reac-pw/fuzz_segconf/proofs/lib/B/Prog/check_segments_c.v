(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 28 of its 48 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_segments (fuzz_segconf.c:392-400, 407-429; fuzz_segconf.asan 0x8704c, 316 bytes, 79 instructions; frame
   48 bytes): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return). Functional content: the plain contract
   lib/Prog/check_segments_c.v:10-44 (check_segments_pre :26-31), restated over the ASan reader
   rd = aview segs (w_H W) mem.
   segments_are(c, m) || !returned aborts. The code reads c->n (c + 0x2c80) and m->n (m + 0x2000) and compares them
   (0x870b8), reads c->overflow (c + 0x34d0) and m->overflow (m + 0x2004) and compares them (0x870f0), all four with
   `lw`; then for i < c->n (`blez s3` 0x870f4, the count kept in s3) it calls strcmp(c + 356 i, m + 256 i)
   (0x87100: the names of c->seg[i] and m->seg[i]) and tests the result (0x87104); last it tests returned (a2, the
   full register, kept in s0; `beqz s0` 0x87118). It writes only its frame.
   The abort site 0x8713c (after __asan_handle_no_return 0x87138) is reached from 0x870b8, 0x870f0, 0x87104 and
   0x87118; all four are dead under SegModel.check_segments rcs mcs returned = true, the last conjunct of
   check_segments_pre: the counts and the overflows are u32_enc values (seg_spec.rconf_enc / mconf_encp), so equal
   sign extensions are equal values; the first n names compare equal, so the strcmp row's post gives zero results;
   returned = true makes a2 = b2z true = 1.
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - 48, sp)]; here apost_base with footprint []
   (the frame is inside the call's own window [sp - STK_check_segments, sp)) and the post tail
   sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract:
   - sa_addr rd c SEG_C_SIZE kills the load4 check sites of c + 0x2c80 (shadow byte `lb` 0x8708c, error arm
     __asan_report_load4 0x87150) and c + 0x34d0 (shadow byte 0x870cc, error arm 0x87174), and gives strcmp's
     range of each name c + 356 i (its length + 1 bytes, inside the block).
   - sa_addr rd mm SEG_M_SIZE kills the load4 check sites of m + 0x2000 (shadow byte 0x870a8, error arm 0x87160)
     and m + 0x2004 (shadow byte 0x870e0, error arm 0x87184), and gives strcmp's range of each name m + 256 i.
   - each name's tail, which the strcmp row asks (atail_vis), lies inside its struct: a name is cstr_enc 16, so its
     tail ends within the first 24 bytes of a 356-byte (c) or 256-byte (m) entry, and sa_rconf / sa_mconf fix
     every byte of the two structs; no premise of its own.
   - sa_heap of both blocks in place of the plain `apart _ _ lo sp`: c = malloc(0x40e8) and m = calloc(1, 0x2414)
     are the harness's blocks (PREMISES-A section 2.3), and a live heap block lies outside the stack window and
     outside the interceptor's scratch.
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes its
     own RELRO bounds): the strcmp row asks rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does not
     give.
   - The shadow base is read through the GOT word 0xa2a50 and __asan_shadow_memory_dynamic_address 0xabff8
     (0x8706c-0x87078; PREMISES-A section 1.5): AR's const cells as_got_shadow / as_shadow_cell
     (lib/Reusable/YG0f.v aso_const_law), so neither is a premise or a parameter.
   - No side-stack frame, no printf, no allocator entry: EV_check_segments = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_segments (fun _ => False): every byte outside the window
     [sp - STK_check_segments, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow entry,
     its own stores are into its frame (`sd` 0x87050-0x87060), and the strcmp row's post keeps every byte
     outside the interceptor's scratch window with E = False (art_post, fuzz_command lib/A/Rt/RtDefs.v:89-99;
     RtString.v astrcmp_realizes), a window STK_check_segments covers; the abort and report arms are dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_segments, STK_check_segments, RLO and RHI are
   parameters (image A: A_check_segments = 0x8704c; STK_check_segments covers the 48-byte frame and the window the
   strcmp row asks).
   Call site: LLVMFuzzerTestOneInput 0x854a8 (segA/evidence/callsites.asan.tsv).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); rows 16-19 were added by the
   accepted v1, 5e0b8a44fdc):
     RtString.astrcmp_realizes (row 17) at the strcmp trampoline (image A 0x43a14), once per segment.
   It is NOT a premise of this contract: the statement does not mention it. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_segments_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Definition EV_check_segments : Z := 0.
(* the plain check_segments_pre over the reader: the two blocks (where they lie and their shadow added), the
   flag returned and SegModel.check_segments *)
Definition check_segments_pre (ly : alayout) (S : astate) (rd : reader) (c mm retv : Z) (rcs : rconf)
(mcs : mconf) (returned : bool) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf rd c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr rd c seg_spec.SEG_C_SIZE /\
mm <> 0 /\ mm mod 16 = 0 /\ sa_mconf rd mm mcs /\ sa_heap B ly S mm seg_spec.SEG_M_SIZE /\
sa_addr rd mm seg_spec.SEG_M_SIZE /\
retv = seg_spec.b2z returned /\ check_segments rcs mcs returned = true.
Definition check_segments_contract (A_check_segments STK_check_segments RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c mm retv : Z) (rcs : rconf) (mcs : mconf) (returned : bool),
afn_pre segs B STK_check_segments ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
getr regs 11 = w64 mm -> 0 <= mm < 2 ^ 64 ->
getr regs 12 = w64 retv -> 0 <= retv < 2 ^ 64 ->
check_segments_pre ly S (aview segs (w_H W) mem) c mm retv rcs mcs returned ->
st_nev S + EV_check_segments <= EV_MAX ->
SRr segs W (cfg_at segs A_check_segments regs mem md)
(apost_base segs B STK_check_segments [] regs ly S W mem md EV_check_segments
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_segments (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
