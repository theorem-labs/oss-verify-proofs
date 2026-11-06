(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7z.v, with its module paths and module names changed; 20 of its 41 lines of code are new or changed and 51 lines of the source are left out. *)
(* reac_segconf_model (reac_segconf.c:555-559; fuzz_segconf.asan 0x897e8, 108 bytes, 27 instructions; frame 16
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_segconf_model_c.v:11-36, restated over the ASan
   reader. What the code does (objdump of fuzz_segconf.asan, 0x897e8-0x89850): s = reac_segconf_find(c, name)
   (jal 0x89800); 0 when s is 0 or s->model_set = 0 (lw of s + 0x3c at 0x8981c); else s + 0x24. The post is the
   plain one: a0 = seg_spec.model_ptr c rcs nm.
   What it reads: the shadow base (the GOT word as_got_shadow B, image A 0xa2a50, loaded at 0x897f4-0x897fc before
   the call; AR_const_law), what find reads, and the model_set word of the entry found. What it writes: its own
   frame and find's, all inside its stack window, so its footprint is []. No abort site
   (segA/evidence/program.asan.tsv line 29).
   Premise: query_pre of lib/A/Prog/reac_segconf_find_c.v, the one find asks. NAME PREMISE: sa_str, not
   sa_strz: the only reader of the name is find, which hands it to strcmp, and row 17's
   RtString.astrcmp_realizes asks the slack after the NUL (atail_vis; see reac_segconf_find_c.v).
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load4 of s->model_set at s + 0x3c (shadow test 0x89808-0x89848, error arm
     __asan_report_load4 at 0x89850): killed by query_pre's sa_addr rd c SEG_C_SIZE, since s = c + 356 i with
     i < length (rc_seg rcs) <= 32 by find's post (seg_spec.find_ptr) and seg_spec.rconf_enc.
   - find's facts (its load4 of c->n, strcmp's two ranges, rt_rom_view from arodata_okP segs RLO RHI B rd):
     query_pre and arodata_okP, handed to find unchanged, with the same RLO RHI.
   - no side-stack frame and no printf: apost_base, EV_reac_segconf_model = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK (fun _ => False) in the post (SegABase.v's sa_kept, found by
     the G4 / G5 walk of check_absent: the journal keeps no shadow of an image object). True of the code: its only
     stores are ra and s0 into its frame (0x897ec, 0x897f0); it takes no side-stack frame and calls no
     set_shadow entry; find's post gives the same clause over find's window, which lies in this one when
     STK >= 16 + STK_reac_segconf_find.
   Call sites (segA/evidence/callsites.asan.tsv lines 23, 210): LLVMFuzzerTestOneInput 0x85520 (c, g->name with
   g = &m->seg[i]), check_absent 0x87634 (c, the probe); no constant argument at either.
   image A: A_reac_segconf_model = 0x897e8; STK_reac_segconf_model = 16 + STK_reac_segconf_find =
   16 + 32 + 2 * ESTACK (INFERENCE: its frame above find's window); RLO = 0xa14a0 (.data.rel.ro start),
   RHI = 0xa3748 (.got end), the one pair this unit uses, as SegGlob.SEG_RLO / SEG_RHI has it (the listing lane,
   2026-10-30; the earlier 0xa1468 / 0xa4000 here was the whole PT_GNU_RELRO and was wrong).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_model, STK_reac_segconf_model, RLO, RHI and
   every image cell are parameters (or fields of B).
   The WALK takes as Section hypotheses: reac_segconf_find_contract (lib/A/Prog/reac_segconf_find_c.v) at find's
   entry and stack. It calls no runtime entry itself (find's walk takes RtString.astrcmp_realizes, row 17 of
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626), accepted v1 5e0b8a44fdc;
   at e45889d6935a strcmp is that file's DECISION 2, option (b)). They are NOT premises of this contract: the
   statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/reac_segconf_model_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c.
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
Definition EV_reac_segconf_model : Z := 0.
Definition reac_segconf_model_contract (A_reac_segconf_model STK_reac_segconf_model RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c name : Z) (rcs : rconf) (nm : list Z),
afn_pre segs B STK_reac_segconf_model ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 name -> 0 <= name < 2 ^ 64 ->
query_pre segs B ly S (aview segs (w_H W) mem) c name rcs nm ->
st_nev S + EV_reac_segconf_model <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_model regs mem md)
(apost_base segs B STK_reac_segconf_model [] regs ly S W mem md EV_reac_segconf_model
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.model_ptr c rcs nm) /\
 sa_kept segs W mem W' mem' regs STK_reac_segconf_model (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
