(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignore_file_c.v; 16 of its 44 lines of code are new or changed and 13 lines of the source are left out. *)
(* ieq (fuzz_segconf.c:127-138; fuzz_segconf.asan 0x87904, 232 bytes, 58 instructions; frame 48 bytes, no
   side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre
   at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/ieq_c.v:10-51 (ieq_pre :34-37, the post :44-45),
   restated over the ASan reader. The post is the plain one: a0 = seg_spec.b2z (SegModel.ieq (seg_spec.zs l) w),
   l the n bytes at s, w the C string at word.
   What the code does (objdump of fuzz_segconf.asan, 0x87904-0x879e8): k = strlen(word) (jal 0x87938 to the strlen
   trampoline); n <> k returns 0 (bne 0x8793c); n = 0 returns 1 (beqz 0x87944); else for i = 0 .. n-1 the byte s[i]
   (lbu 0x8796c) folded to lower case (0x87974-0x87984) against word[i] (lbu 0x87978), the first difference returns
   0, none returns 1. It reads the string at word and, when n = strlen(word), the n bytes at s; it writes its own
   frame only, so its footprint is []. No abort site (provenance/evidence/image-tables/program.asan.tsv line 17).
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image A 0xa2a50, ld at 0x87928),
   whose value and target AR gives (AR_const_law, lib/Reusable/YG0d.v:469-475), so the contract names neither.
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load1 of s[i] (shadow test 0x87950-0x8795c, slow path 0x879a8, error arm
     __asan_report_load1 at 0x879e8 with a0 = s + i): killed by ieq_pre's sa_addr rd s n.
   - inline check 2, load1 of word[i] (shadow test 0x87960-0x87970, slow path 0x879b4, error arm
     __asan_report_load1 at 0x879c0 with a0 = word + i): killed by sa_addr rd word (length w + 1).
   - strlen's range check [word, word + length w + 1): the same sa_addr; strlen's word loop reads the slack to the
     next 8-byte boundary, hence sa_str (not sa_strz), and the released strlen text asks length + 1 < 2 ^ 32 of
     the range (fuzz_command lib/A/Rt/RtDefs.v:35-36 aread_ok) and 0 < word (RtString.v astrlen_realizes): the
     last conjunct and word <> 0 with sa_addr's 0 <= word.
   - where each object lies: s and word by sa_loc (s points into m_file's text block, a heap block; word is a
     .rodata literal at every call site). The real stack window [sp - STK, sp) is apart from all three places, so
     the plain apart premises are not restated (reac_segconf_find_c.v gives the kit facts).
   - arodata_okP over the read-only window RLO RHI, a contract parameter (each image's walk gives its RELRO
     bounds): row 16 asks rt_rom_view (RtDefs.v:145), which AR does not give.
   - no side-stack frame and no printf: apost_base, EV_ieq = 0, post tail sa_noalloc.
   Call sites (provenance/evidence/image-tables/callsites.asan.tsv lines 100, 102, 106, 110-114, 118), all in m_file, a0 into the
   text block, a1 the length of that range, a2 a .rodata literal (image A, nm and objdump 0x864a4 .. 0x86b24):
   0x864b0 (a1 = 7, .str.8 0x21100 S_segment), 0x86694 (.str.9 0x21120 S_role), 0x867c8 (.str.15 0x21220
   S_model), 0x8694c (.str.16 0x21240 S_ignore), 0x86964 (.str.17 0x21260 S_yes), 0x86980 (.str.18 0x21280
   S_true), 0x869c0 (.str.19 0x212a0 S_no), 0x869d8 (.str.20 0x212c0 S_false), 0x86b30 (.str.21 0x212e0 S_knock);
   the text of each literal was read from the pin's LOAD bytes by this lane, not from the four listings
   (INFERENCE grade by the brief's rule), and agrees with the plain contract's list at the same sites.
   image A: A_ieq = 0x87904; STK_ieq = 48 + ESTACK (INFERENCE: its frame and the ESTACK window row 16 asks).
   IMAGE-INDEPENDENT: no image module is Required; A_ieq, STK_ieq, RLO and RHI are parameters, and the
   shadow-base cells are fields of B.
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); row 16 is in the accepted v1,
   5e0b8a44fdc; at e45889d6935a strlen is that file's DECISION 2, option (b)):
     RtString.astrlen_realizes (row 16), at the strlen trampoline (image A 0x43a0c, interceptor 0x43abc).
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
(* The plain ieq_pre (lib/Prog/ieq_c.v:34-37) over the reader rd = aview segs (w_H W) mem: the n bytes l at s, in
   a heap block, a side-stack frame or the image, addressable; word the C string w with its slack, its bytes and
   NUL addressable, in one of the same three places, short enough for the interceptor's range. The plain stack_ok
   / apart / mem_inv conjuncts are afn_pre's and the locations' here. Outside the sections:
   ieq_pre segs B ly S rd s n word l w. *)
Definition ieq_pre (ly : alayout) (S : astate) (rd : reader) (s n word : Z) (l : list byte) (w : list Z) : Prop :=
s <> 0 /\ sa_bytes rd s l /\ Z.of_nat (length l) = n /\ sa_addr rd s n /\ sa_loc segs B ly S s n /\
word <> 0 /\ sa_str rd word w /\ sa_addr rd word (Z.of_nat (length w) + 1) /\
sa_loc segs B ly S word (Z.of_nat (length w) + 1) /\ Z.of_nat (length w) + 1 < 2 ^ 32.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_ieq : Z := 0.
Definition ieq_contract (A_ieq STK_ieq RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (s n word : Z) (l : list byte) (w : list Z),
afn_pre segs B STK_ieq ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 s -> 0 <= s < 2 ^ 64 -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 64 ->
getr regs 12 = w64 word -> 0 <= word < 2 ^ 64 ->
ieq_pre ly S (aview segs (w_H W) mem) s n word l w ->
st_nev S + EV_ieq <= EV_MAX ->
SRr segs W (cfg_at segs A_ieq regs mem md)
(apost_base segs B STK_ieq [] regs ly S W mem md EV_ieq
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.b2z (SegModel.ieq (seg_spec.zs l) w)) /\
 sa_kept segs W mem W' mem' regs STK_ieq (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
