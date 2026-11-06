(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignore_file_c.v; 14 of its 44 lines of code are new or changed and 11 lines of the source are left out. *)
(* reac_segconf_find (reac_segconf.c:517-525; fuzz_segconf.asan 0x894ec, 168 bytes, 42 instructions; frame 32
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_segconf_find_c.v:10-50, restated over the ASan
   reader. Its query_pre (:31-36), what every reader query asks of its caller, is restated HERE ONCE over the
   reader; reac_segconf_ignored, _role, _role_file, _ignore_file and _model (lib/A/Prog/<F>_c.v) Require this
   file and use it.
   What the code does (objdump of fuzz_segconf.asan, 0x894ec-0x89590): 0 for a NULL c or name (the premise
   excludes both: no call site passes one); else n = c->n (lw of c + 0x2c80 at 0x8953c) and, for i = 0 .. n-1,
   strcmp(c + 356 i, name) (jal 0x8954c to the strcmp trampoline); the first 0 returns c + 356 i, none returns 0.
   The post is the plain one: a0 = seg_spec.find_ptr c rcs nm.
   What it reads: the shadow base, through the GOT word as_got_shadow B (image A 0xa2a50, which holds 0xabff8,
   the cell __asan_shadow_memory_dynamic_address = as_shadow_cell B; read from the pin with its program headers),
   both fields of B whose values AR gives (AR_const_law, lib/Reusable/YG0d.v:469-475), so the contract names
   neither; c->n; the names of seg[0 .. n); the string at name. What it writes: its own frame only, so its
   footprint is []. No abort site (provenance/evidence/image-tables/program.asan.tsv line 24).
   NAME PREMISE: sa_str (string, NUL, and the slack to the next 8-byte boundary), not sa_strz. strcmp's own loop
   reads string + NUL only, but row 17's RtString.astrcmp_realizes asks atail_vis of BOTH strings (fuzz_command
   lib/A/Rt/RtString.v:108-120 and lib/A/Rt/RtDefs.v:54-55 at origin/ossv/recipes 501c0d516c69), so the walk
   needs the slack of the name; the slack of seg[i].name lies inside the block (16-byte field, 356-byte entry).
   It also asks 0 <= length + 1 < 2 ^ 32 of each range (aread_ok, RtDefs.v:35-36): the last conjunct.
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load4 of c->n at c + 0x2c80 (shadow test 0x8952c-0x8958c, error arm __asan_report_load4
     at 0x89590): killed by query_pre's sa_addr rd c SEG_C_SIZE (0x2c80 + 4 <= 16616).
   - strcmp's range checks: [c + 356 i, ...) lies in the block, killed by the same sa_addr;
     [name, name + length nm + 1) is killed by query_pre's sa_addr rd name (length nm + 1).
   - where each object lies: the block by sa_heap (malloc(0x40e8) at LLVMFuzzerTestOneInput 0x84f80, the a0 of
     reac_segconf_init at 0x84fec), never by an address bound against the image's end; the name by sa_loc (a heap
     mconf block for m->seg[i].name, main's class-3 side-stack frame for check_absent's probe, .rodata for
     "nosuch0"). The real stack window [sp - STK, sp) is apart from all three (kit: blocks and frames lie below
     alloc_ceiling <= ly_stk_lo, AR_blocks_law / AR_sep_law and astk_ok; image bytes lie in ly_img, AR's ALedger
     al_img, lib/Reusable/YG0n.v:312, which layout_ok keeps apart from the stack band, static_extents,
     YG0f.v:303-304), so the plain apart premises are not restated.
   - arodata_okP segs RLO RHI B rd, RLO RHI the read-only window, contract parameters after A and STK (the image-A
     owner's decision, 2026-10-30): row 17 asks rt_rom_view, which AR does not give and which fuzz_command
     derives from arodata_okP (lib/A/Prog/CmdRecImg.v:51-54 at 501c0d516c69). It is not part of query_pre: it
     is about the image, not the query's objects.
   - no side-stack frame and no printf: apost_base, EV_reac_segconf_find = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK (fun _ => False) in the post: every byte outside the stack window reads
     as at the entry, the shadow of an image object included (apost_base's journal keeps no shadow below
     alloc_ceiling; SegABase.v's sa_kept, found by the G4 / G5 walk of check_absent). True of the code: its only
     stores are ra, s0, s1, s2 into its frame (0x894f0-0x894fc); it takes no side-stack frame and calls no
     set_shadow entry; row 17's post keeps every byte outside strcmp's 2 * ESTACK scratch (art_post,
     RtDefs.v:89-97), which lies in the window when STK >= 32 + 2 * ESTACK.
   Call sites (provenance/evidence/image-tables/callsites.asan.tsv lines 207, 353, 355, 359, 362, 365): check_absent 0x87600,
   reac_segconf_ignored 0x895ac, reac_segconf_role 0x89610, reac_segconf_role_file 0x896d0,
   reac_segconf_ignore_file 0x89768, reac_segconf_model 0x89800; no constant argument at any.
   image A: A_reac_segconf_find = 0x894ec; STK_reac_segconf_find = 32 + 2 * ESTACK (INFERENCE: its frame and
   the 2 * ESTACK window row 17 asks below it); RLO = 0xa14a0 (.data.rel.ro start), RHI = 0xa3748 (.got end),
   the one pair this unit uses, as SegGlob.SEG_RLO / SEG_RHI and the other contracts' comments have it
   (the listing lane, 2026-10-30; the earlier 0xa1468 / 0xa4000 here was the whole PT_GNU_RELRO and was wrong).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_find, STK_reac_segconf_find, RLO, RHI and every
   image cell are parameters (or fields of B).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); row 17 is in the accepted v1,
   5e0b8a44fdc; at e45889d6935a strcmp is that file's DECISION 2, option (b)):
     RtString.astrcmp_realizes (row 17), at the strcmp trampoline (image A 0x43a14, interceptor 0x43fe8).
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
(* What every reader query asks of its caller (the plain query_pre, lib/Prog/reac_segconf_find_c.v:31-36, over the
   reader rd = aview segs (w_H W) mem): c is the reader's block, a live heap block of 16616 bytes holding rcs,
   addressable; name is the C string nm with its slack (sa_str: row 17 asks it), in a heap block, a side-stack
   frame or the image, its bytes and NUL addressable, and short enough for the interceptor's range (aread_ok's
   n < 2 ^ 32). The plain depth / stack_ok / apart / mem_inv conjuncts are afn_pre's and the locations' here.
   Outside the sections: query_pre segs B ly S rd c name rcs nm. *)
Definition query_pre (ly : alayout) (S : astate) (rd : reader) (c name : Z) (rcs : rconf) (nm : list Z) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf rd c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr rd c seg_spec.SEG_C_SIZE /\
name <> 0 /\ sa_str rd name nm /\ sa_loc segs B ly S name (Z.of_nat (length nm) + 1) /\
sa_addr rd name (Z.of_nat (length nm) + 1) /\ Z.of_nat (length nm) + 1 < 2 ^ 32.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_reac_segconf_find : Z := 0.
Definition reac_segconf_find_contract (A_reac_segconf_find STK_reac_segconf_find RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c name : Z) (rcs : rconf) (nm : list Z),
afn_pre segs B STK_reac_segconf_find ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 name -> 0 <= name < 2 ^ 64 ->
query_pre ly S (aview segs (w_H W) mem) c name rcs nm ->
st_nev S + EV_reac_segconf_find <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_find regs mem md)
(apost_base segs B STK_reac_segconf_find [] regs ly S W mem md EV_reac_segconf_find
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.find_ptr c rcs nm) /\
 sa_kept segs W mem W' mem' regs STK_reac_segconf_find (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
