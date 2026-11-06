(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 22 of its 42 lines of code are new or changed and 147 lines of the source are left out. *)
(* fuzz_catalogue_row (catalogue.c:29-35; fuzz_segconf.asan 0x8a038, 200 bytes, 50 instructions; frame 64 bytes,
   no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/fuzz_catalogue_row_c.v:9-53, restated over the ASan
   reader. The plain post is a0 = pin_spec.row_ptr FUZZ_CATALOGUE sb (:47); this one states the same value as
   seg_spec.cat_ptr cat (SegModel.cat_row (seg_spec.zs sb)), equal for every cat and sb by
   lib/Spec/SegBridge.v:682-686 (bridge_cat_row), so that the table premise and the post are both in
   SegModel.cat_toks's terms, as the callers' posts are (m_file's model reads cat_row, by_token's post is cat_ptr
   of SegModel.by_token). This is the catalogue shape agreed with the G3 contracts lane (reac_segconf_parse_file) and
   accepted by the contracts lane: the table address is the parameter cat, the table premise is SegABase's sa_cat.
   What the code does (objdump of fuzz_segconf.asan, 0x8a038-0x8a0fc): s0 = fuzz_catalogue (auipc/addi at
   0x8a070-0x8a074, image A 0xa18e0), and for the 11 rows (s6 counts 11 down, s0 and s3 step 0x128 = 296, the
   shadow pointer s5 steps 37): the token pointer tp = ld 0(s0) (0x8a090), strlen(tp) (jal 0x8a098 to the strlen
   trampoline) = n goes on to bcmp(tp, s, n) (jal 0x8a0ac to the bcmp trampoline), whose 0 returns s0 (0x8a0cc);
   after row 10 it returns 0 (0x8a0c8). It reads the 11 token-pointer words of the table, the 11 tokens, and the
   n bytes at s (only through bcmp, only when a token has length n: 5, 6 or 11, pin_spec.tok_lengths); it writes
   its own frame only, so its footprint is []. No abort site (segA/evidence/program.asan.tsv line 34).
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image A 0xa2a50, ld at 0x8a068),
   whose value and target AR gives (AR_const_law, lib/Reusable/YG0d.v:469-475), so the contract names neither.
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load8 of row i's token-pointer word at cat + 0x128 i (shadow byte lbu 0x8a088, bnez to
     0x8a0f8, error arm __asan_report_load8 at 0x8a0fc with a0 = the row): killed by sa_cat's
     sa_pinned segs B cat CAT_BYTES (the table addressable at every allocator state, lib/A/Prog/SegABase.v).
   - strlen's range [tp, tp + length + 1) and bcmp's first range [tp, tp + n): sa_cat gives each token as a
     sa_lit (string with slack, addressable at every state by sa_pinned, its slack mapped by sa_romtail,
     0 < tp, an image object). bcmp's second range [s, s + n): killed by sa_addr rd s n.
   - the table: an image object (sa_cat's sa_img: fuzz_catalogue is in .data.rel.ro, nm line 2296, 0xfe0 bytes with
     its redzone) whose token pointers are read from the image's own words (sa_cat's existential); the plain
     table premise (:43, mrd = seg_rom over [FUZZ_CATALOGUE, + CAT_BYTES)) is replaced by sa_cat, which names no
     image number. The tokens' bytes are pin_spec.tok_bytes, which seg_spec.cat_toks_bytes ties to
     SegModel.cat_toks.
   - where s lies: sa_loc (m_file passes low, a buffer of its own class-1 side-stack frame;
     reac_box_catalogue_by_token passes its token, low of reac_segconf_parse_file's class-5 frame). The real stack
     window [sp - STK, sp) is apart from all three places, so the plain apart premise (:42) is not restated.
   - arodata_okP over the read-only window RLO RHI, a contract parameter (each image's walk gives its RELRO
     bounds): row 16 asks rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does not give.
   - no side-stack frame and no printf: apost_base, EV_fuzz_catalogue_row = 0, post tail sa_noalloc.
   Call sites: m_file 0x86878 (segA/evidence/callsites.asan.tsv line 107; a0 = low, a1 = its length, at most 23)
   and the tail jump of reac_box_catalogue_by_token at 0x8a174 (program.asan.tsv line 36).
   image A: A_fuzz_catalogue_row = 0x8a038; cat = 0xa18e0 (nm line 2296); STK_fuzz_catalogue_row =
   64 + 2 * ESTACK (INFERENCE: its frame and the 2 * ESTACK window abcmp_realizes asks, YG0d.v:364).
   IMAGE-INDEPENDENT: no image module is Required; A_fuzz_catalogue_row, STK_fuzz_catalogue_row, RLO, RHI and cat
   are parameters.
   The WALK takes these runtime entries as Section hypotheses:
     RtString.astrlen_realizes, the interceptor lane's interface row 16 (in the accepted v1, 5e0b8a44fdc; at
     e45889d6935a strlen is DECISION 2, option (b), of provenance/evidence/interceptors/INTERFACE-A-interceptors.md
     (commit 7068323e2626)), at the strlen trampoline (image A 0x43a0c, interceptor 0x43abc);
     the kit's abcmp_realizes (the image-A owner's frame; lib/Reusable/YG0d.v:361), at the bcmp trampoline (image A
     0x43a38, interceptor 0x46e80).
   They are NOT premises of this contract: the statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/fuzz_catalogue_row_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Definition EV_fuzz_catalogue_row : Z := 0.
Definition fuzz_catalogue_row_contract (A_fuzz_catalogue_row STK_fuzz_catalogue_row RLO RHI cat : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p n : Z) (sb : list byte),
afn_pre segs B STK_fuzz_catalogue_row ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 p -> 0 <= p < 2 ^ 64 -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 64 ->
(* the n bytes sb at p (the plain :38-39), in a heap block, a side-stack frame or the image, addressable *)
sa_bytes (aview segs (w_H W) mem) p sb -> n = Z.of_nat (length sb) ->
sa_addr (aview segs (w_H W) mem) p n -> sa_loc segs B ly S p n ->
(* the table (the plain :43) *)
sa_cat segs B (aview segs (w_H W) mem) cat ->
st_nev S + EV_fuzz_catalogue_row <= EV_MAX ->
SRr segs W (cfg_at segs A_fuzz_catalogue_row regs mem md)
(apost_base segs B STK_fuzz_catalogue_row [] regs ly S W mem md EV_fuzz_catalogue_row
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.cat_ptr cat (SegModel.cat_row (seg_spec.zs sb))) /\
 sa_kept segs W mem W' mem' regs STK_fuzz_catalogue_row (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
