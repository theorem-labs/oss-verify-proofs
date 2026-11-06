(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* reac_segconf_ignore_file (reac_segconf.c:549-553; fuzz_segconf.asan 0x89750, 152 bytes, 38 instructions;
   frame 16 bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's
   lib/A/Prog form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_segconf_ignore_file_c.v:11-38, restated over the
   ASan reader. What the code does (objdump of fuzz_segconf.asan, 0x89750-0x897e4): s = reac_segconf_find(c,
   name) (jal 0x89768); 0 when s is 0, when s->ignore_set = 0 (lw of s + 0x1c at 0x89784) or when
   s->ignore_file[0] = 0 (lbu of s + 0x100 at 0x897a0); else s + 0x100. The post is the plain one:
   a0 = seg_spec.ignore_file_ptr c rcs nm.
   What it reads: the shadow base (the GOT word as_got_shadow B, image A 0xa2a50, loaded at 0x8975c-0x89764 before
   the call; AR_const_law), what find reads, and the ignore_set word and first ignore_file byte of the entry
   found. What it writes: its own frame and find's, all inside its stack window, so its footprint is []. No
   abort site (provenance/evidence/image-tables/program.asan.tsv line 28).
   Premise: query_pre of lib/A/Prog/reac_segconf_find_c.v, the one find asks. NAME PREMISE: sa_str, not
   sa_strz: the only reader of the name is find, which hands it to strcmp, and row 17's
   RtString.astrcmp_realizes asks the slack after the NUL (atail_vis; see reac_segconf_find_c.v).
   ASAN FACTS ADDED over the plain contract (s = c + 356 i with i < length (rc_seg rcs) <= 32, by find's post
   seg_spec.find_ptr and seg_spec.rconf_enc, so every field of s lies in the block):
   - inline check 1, load4 of s->ignore_set at s + 0x1c (shadow test 0x89770-0x897d0, error arm
     __asan_report_load4 at 0x897d8): killed by query_pre's sa_addr rd c SEG_C_SIZE.
   - inline check 2, load1 of s->ignore_file[0] at s + 0x100 (shadow test 0x8978c-0x897e0, error arm
     __asan_report_load1 at 0x897e4): killed by the same sa_addr.
   - find's facts (its load4 of c->n, strcmp's two ranges, rt_rom_view from arodata_okP segs RLO RHI B rd):
     query_pre and arodata_okP, handed to find unchanged, with the same RLO RHI.
   - no side-stack frame and no printf: apost_base, EV_reac_segconf_ignore_file = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK (fun _ => False) in the post (SegABase.v's sa_kept, found by
     the G4 / G5 walk of check_absent: the journal keeps no shadow of an image object). True of the code: its only
     stores are ra and s0 into its frame (0x89754, 0x89758); it takes no side-stack frame and calls no
     set_shadow entry; find's post gives the same clause over find's window, which lies in this one when
     STK >= 16 + STK_reac_segconf_find.
   Call site (provenance/evidence/image-tables/callsites.asan.tsv line 28): LLVMFuzzerTestOneInput 0x85558 (c, g->name with
   g = &m->seg[i]); no constant argument.
   image A: A_reac_segconf_ignore_file = 0x89750; STK_reac_segconf_ignore_file = 16 + STK_reac_segconf_find =
   16 + 32 + 2 * ESTACK (INFERENCE: its frame above find's window); RLO = 0xa14a0 (.data.rel.ro start),
   RHI = 0xa3748 (.got end), the one pair this unit uses, as SegGlob.SEG_RLO / SEG_RHI has it (the listing lane,
   2026-10-30; the earlier 0xa1468 / 0xa4000 here was the whole PT_GNU_RELRO and was wrong).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_ignore_file, STK_reac_segconf_ignore_file, RLO,
   RHI and every image cell are parameters (or fields of B).
   The WALK takes as Section hypotheses: reac_segconf_find_contract (lib/A/Prog/reac_segconf_find_c.v) at find's
   entry and stack. It calls no runtime entry itself (find's walk takes RtString.astrcmp_realizes, row 17 of
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626), accepted v1 5e0b8a44fdc;
   at e45889d6935a strcmp is that file's DECISION 2, option (b)). They are NOT premises of this contract: the
   statement does not mention them. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the events this call spends: 0, it reaches no allocator entry (nor does find) *)
Definition EV_reac_segconf_ignore_file : Z := 0.
Definition reac_segconf_ignore_file_contract
(A_reac_segconf_ignore_file STK_reac_segconf_ignore_file RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c name : Z) (rcs : rconf) (nm : list Z),
afn_pre segs B STK_reac_segconf_ignore_file ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 name -> 0 <= name < 2 ^ 64 ->
query_pre segs B ly S (aview segs (w_H W) mem) c name rcs nm ->
st_nev S + EV_reac_segconf_ignore_file <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_ignore_file regs mem md)
(apost_base segs B STK_reac_segconf_ignore_file [] regs ly S W mem md EV_reac_segconf_ignore_file
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.ignore_file_ptr c rcs nm) /\
 sa_kept segs W mem W' mem' regs STK_reac_segconf_ignore_file (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
