(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignore_file_c.v, with its module paths and module names changed; 19 of its 45 lines of code are new or changed and 15 lines of the source are left out. *)
(* reac_segconf_parse (reac_segconf.c:327-332; fuzz_segconf.asan 0x891d0, 72 bytes, 18 instructions; frame 32
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_baseF at the return: it reaches the printf wrappers through its
   callees).
   Functional content: the plain contract lib/Prog/reac_segconf_parse_c.v:13-39 (the contract :27-39, over
   the plain reader_pre of lib/Prog/reac_segconf_parse_file_c.v:40-46), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x891d0-0x89214): saves ra, s0 = c, s1;
   n = reac_segconf_parse_file(c, text, "reac-pw.conf") (jal 0x891f0, a2 = the literal .str.1 by auipc / addi at
   0x891e4), cross_check(c) (jal 0x891fc), returns n. The post is the plain one: a0 = snd (SegModel.r_parse rcs s)
   and c holds fst (SegModel.r_parse rcs s).
   What it reads: nothing itself (no load besides its frame); its callees read what reader_pre and
   cross_check_pre name. What it writes: its frame, its callees' frames and seg_spec.RC_PARSE_W c (cross_check's
   writes, cross_check_W c, lie inside it), the plain write list without its stack range. No abort site
   (segA/evidence/program.asan.tsv line 22).
   ASAN FACTS ADDED over the plain contract (it has no inline check and calls no runtime entry: program.asan.tsv
   line 22, `0` checks, no runtime callee; every fact below is one its two callees ask, which the plain contract
   got from mem_inv / printf_env / stack_ok):
   - the label it passes is lit S_base, a literal of reac_segconf_parse_file's list (reader_pre's sa_lit): it
     gives parse_file's label premise (sa_ostr, sa_loc by sa_img, sa_addr); its read span lies in the image,
     apart from c->reading in the heap block.
   - cross_check's two formats by sa_lit (CROSS_CHECK_LITS); parse_file's literals, the table and the text by
     reader_pre.
   - parse_file's class-5 frame with refuse's class-0 frame inside it: sa_room_n 2 S (cross_check needs only one
     of them, and none is live when it runs).
   - NO keep clause (sa_kept) in the post: its callees' posts have none (parse_file's class-5 frame and refuse's
     class-0 frame, with their shadow, are written outside every window and footprint), so none is provable here.
   - its callees reach snprintf and vsnprintf: apost_baseF; sa_frm0 and sa_ssp rd gotw guard are in reader_pre.
   - arodata_okP over the window RLO .. RHI: both callees' contracts ask it.
   - EV_reac_segconf_parse = 0, post tail sa_noalloc.
   Call site (segA/evidence/callsites.asan.tsv line 17): LLVMFuzzerTestOneInput 0x853c4 (c, the last file's text),
   after m_file and m_cross.
   image A: A_reac_segconf_parse = 0x891d0; STK_reac_segconf_parse = 32 + Z.max STK_reac_segconf_parse_file
   STK_cross_check (INFERENCE: its frame and the deeper of its callees' windows); RLO = 0xa14a0, RHI = 0xa3748
   (readelf, fuzz_command's CmdGlob.v convention); cat = 0xa18e0, gotw = 0xa36d8, guard = 0x5ff078 (as
   reac_segconf_parse_file_c.v); lit as reac_segconf_parse_file_c.v and cross_check_c.v (S_base = 0x21360, the
   one literal this function names itself).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_parse, STK_reac_segconf_parse, RLO, RHI, lit,
   cat, gotw and guard are parameters.
   The WALK takes as Section hypotheses: reac_segconf_parse_file_contract (lib/A/Prog/reac_segconf_parse_file_c.v,
   at 0x87a78, with lab = Some S_base and lp = lit S_base) and cross_check_contract (lib/A/Prog/cross_check_c.v,
   at 0x89218). It calls no interceptor and no runtime entry itself; the interceptor lane's rows and frame entries its
   callees take are named in their files. They are NOT premises of this contract: the statement does not mention
   them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/reac_segconf_parse_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c
reac_segconf_parse_file_c.
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
Definition EV_reac_segconf_parse : Z := 0.
Definition reac_segconf_parse_contract (A_reac_segconf_parse STK_reac_segconf_parse RLO RHI : Z)
(lit : list Z -> Z) (cat gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c t : Z) (rcs : rconf) (s : list Z),
afn_pre segs B STK_reac_segconf_parse ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 t -> 0 <= t < 2 ^ 64 ->
(* what every caller of the reader's parse supplies (reac_segconf_parse_file_c.v's reader_pre) *)
reader_pre segs B lit cat gotw guard ly S (aview segs (w_H W) mem) c t rcs s ->
(* cross_check's literals (its formats; refuse's are in reader_pre's list too) *)
(forall x, In x CROSS_CHECK_LITS -> sa_lit segs B (aview segs (w_H W) mem) (lit x) x) ->
(* room for parse_file's class-5 side-stack frame and refuse's class-0 frame inside it *)
sa_room_n 2 S ->
st_nev S + EV_reac_segconf_parse <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_parse regs mem md)
(apost_baseF segs B STK_reac_segconf_parse (seg_spec.RC_PARSE_W c) regs ly S W mem md EV_reac_segconf_parse
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (snd (SegModel.r_parse rcs s)) /\
 sa_rconf (aview segs (w_H W') mem') c (fst (SegModel.r_parse rcs s)) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
