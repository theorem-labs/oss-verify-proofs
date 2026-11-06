(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 40 lines of code are new or changed and 51 lines of the source are left out. *)
(* reac_box_catalogue (catalogue.c:38-43; fuzz_segconf.asan 0x8a100, 72 bytes, 18 instructions; frame 16 bytes, no
   side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_box_catalogue_c.v:11-25, restated over the ASan
   reader: a0 = the table's address (the plain BOX_CATALOGUE, here the parameter cat), and when the count pointer
   c is not NULL the 8 bytes at c hold 11 (the plain bytes_at c (le8 11), here sa_val c 8 11). Catalogue shape
   agreed with the G3 contracts lane (reac_segconf_parse_file, the one caller) and accepted by the contracts lane.
   The same code is walked in libreac/fuzz_identity's ASan image: its lib/A/Prog/reac_box_catalogue.v (tcat_spec)
   is one of the callee contracts with a proved walk that its lib/A/Prog/IdentEntryLink.v:22 lists (and :261-263
   applies), at origin/ossv/recipes 501c0d516c69. Its spec takes the count pointer nonzero (8-aligned, in a
   side-stack frame or the real stack); this one keeps the plain contract's c = 0 arm, which the code has
   (beqz 0x8a108).
   What the code does (objdump of fuzz_segconf.asan, 0x8a100-0x8a144): a 16-byte frame (saves ra); c = 0 skips to
   the return; else the shadow byte of c (lbu 0x8a120) nonzero goes to the error arm, zero stores 11 as 8 bytes
   at c (sd 0x8a12c); a0 = fuzz_catalogue (auipc/addi 0x8a130-0x8a134, image A 0xa18e0); return. It writes its
   frame and, when c <> 0, the 8 bytes at c: its footprint is [(c, c + 8)] then, [] when c = 0. A leaf: no call
   but the error arm; no abort site (provenance/evidence/image-tables/program.asan.tsv line 35).
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image A 0xa2a50, ld at 0x8a110),
   whose value and target AR gives (AR_const_law, lib/Reusable/YG0d.v:469-475), so the contract names neither.
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, store8 of *c (shadow byte lbu 0x8a120, bnez to 0x8a144, error arm __asan_report_store8 at
     0x8a144): killed by sa_addr rd c 8 with c mod 8 = 0 (one granule, shadow byte 0).
   - where c lies: sa_dst (a side-stack frame or a heap block with its shadow addressable, or a slot of the
     caller's real stack above the entry sp and below the layout's top, present; the one caller passes a slot of
     its class-5 side-stack frame, zeroed at 0x8862c), in place of the plain wr_at; the journal admits the
     store through the footprint.
   - no runtime entry, no side-stack frame, no printf: apost_base, no arodata_okP (it calls no interceptor and
     loads no image cell; cat is an address the code computes, not a load), EV_reac_box_catalogue = 0, post tail
     sa_noalloc.
   Call site: reac_segconf_parse_file 0x88634 (provenance/evidence/image-tables/callsites.asan.tsv line 271; a0 = s3, the 8-byte
   slot its sd zero at 0x8862c cleared).
   image A: A_reac_box_catalogue = 0x8a100; cat = 0xa18e0 (nm line 2296); STK_reac_box_catalogue = 16 (its frame;
   the error arm is dead).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_box_catalogue, STK_reac_box_catalogue and cat are
   parameters.
   The WALK takes no runtime entry as a Section hypothesis: the function calls none on its good path. *)
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
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_reac_box_catalogue : Z := 0.
Definition reac_box_catalogue_contract (A_reac_box_catalogue STK_reac_box_catalogue cat : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c : Z),
afn_pre segs B STK_reac_box_catalogue ly S W regs mem md ch ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
(* the count pointer: NULL, or an 8-aligned addressable slot the call may write (the plain :15) *)
c = 0 \/ (c mod 8 = 0 /\ sa_addr (aview segs (w_H W) mem) c 8 /\ sa_dst segs B ly S W mem regs c 8) ->
st_nev S + EV_reac_box_catalogue <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_box_catalogue regs mem md)
(apost_base segs B STK_reac_box_catalogue (if c =? 0 then [] else [(c, c + 8)]) regs ly S W mem md
EV_reac_box_catalogue
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 cat /\
 (c <> 0 -> sa_val (aview segs (w_H W') mem') c 8%nat 11) /\
 sa_kept segs W mem W' mem' regs STK_reac_box_catalogue (fun a => c <> 0 /\ c <= a < c + 8) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
