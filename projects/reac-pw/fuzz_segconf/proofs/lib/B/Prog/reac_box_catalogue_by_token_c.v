(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 25 of its 45 lines of code are new or changed and 147 lines of the source are left out. *)
(* reac_box_catalogue_by_token (catalogue.c:47-50; fuzz_segconf.asan 0x8a148, 64 bytes, 16 instructions; frame 16
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_box_catalogue_by_token_c.v:11-51 (by_token_pre
   :35-37, the post :45), restated over the ASan reader. The post is the plain one: a0 = seg_spec.cat_ptr cat
   (SegModel.by_token s), &fuzz_catalogue[i] for the first row i whose token is the string s, else 0. Catalogue
   shape agreed with the G3 contracts lane and accepted by the contracts lane: the table address is the parameter
   cat, the table premise is SegABase's sa_cat (in place of the plain cat_img).
   What the code does (objdump of fuzz_segconf.asan, 0x8a148-0x8a184): a 16-byte frame (saves ra and s0); NULL
   returns 0 (beqz 0x8a154; no call site passes NULL, the premise excludes it); else n = strlen(token) (jal 0x8a15c
   to the strlen trampoline), the frame popped (0x8a168-0x8a170), then the tail jump to fuzz_catalogue_row
   (j 0x8a174) with a0 = token, a1 = n, which returns to the caller's ra with its a0. It writes its own frame and
   fuzz_catalogue_row's (the tail call runs at the entry sp), both inside the stack window, so its footprint is
   []. No inline check, no abort site (segA/evidence/program.asan.tsv line 36).
   ASAN FACTS ADDED over the plain contract:
   - no inline check (program.asan.tsv line 36: 0 report calls).
   - strlen's range [token, token + length s + 1): killed by by_token_pre's sa_addr; strlen's word loop reads the
     slack to the next 8-byte boundary, hence sa_str; the released strlen text asks 0 < token (token <> 0 with
     sa_addr's 0 <= token) and length + 1 < 2 ^ 32 (fuzz_command lib/A/Rt/RtDefs.v:35-36): the last conjunct.
   - fuzz_catalogue_row's premises at the tail jump: its bytes are the string's (sa_str), its range is inside
     the string's (sa_addr), its place is the string's (sa_loc), and its table is sa_cat.
   - where token lies: sa_loc (the one call site passes low of reac_segconf_parse_file's class-5 side-stack
     frame). The real stack window [sp - STK, sp) is apart from all three places, so the plain apart premise is
     not restated.
   - arodata_okP over the read-only window RLO RHI, a contract parameter (each image's walk gives its RELRO
     bounds): row 16 asks rt_rom_view (RtDefs.v:145), which AR does not give, and fuzz_catalogue_row's contract
     takes it with the same window.
   - no side-stack frame and no printf: apost_base, EV_reac_box_catalogue_by_token = 0, post tail sa_noalloc.
   Call site: reac_segconf_parse_file 0x88538 (segA/evidence/callsites.asan.tsv line 268; a0 = s4 = low, whose
   NUL is stored at 0x88530).
   image A: A_reac_box_catalogue_by_token = 0x8a148; cat = 0xa18e0 (nm line 2296); STK_reac_box_catalogue_by_token
   = 64 + 2 * ESTACK (INFERENCE: fuzz_catalogue_row's window at the entry sp, deeper than its own 16-byte frame
   and strlen's ESTACK).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_box_catalogue_by_token, STK_reac_box_catalogue_by_token,
   RLO, RHI and cat are parameters.
   The WALK takes these as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); row 16 is in the accepted v1,
   5e0b8a44fdc; at e45889d6935a strlen is that file's DECISION 2, option (b)):
     RtString.astrlen_realizes (row 16), at the strlen trampoline (image A 0x43a0c, interceptor 0x43abc);
     fuzz_catalogue_row_contract (lib/A/Prog/fuzz_catalogue_row_c.v) at fuzz_catalogue_row (image A 0x8a038).
   They are NOT premises of this contract: the statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/reac_box_catalogue_by_token_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
(* The plain by_token_pre (lib/Prog/reac_box_catalogue_by_token_c.v:35-37) over the reader
   rd = aview segs (w_H W) mem: token the C string s with its slack, its bytes and NUL addressable, in a heap
   block, a side-stack frame or the image, short enough for the interceptor's range; the table at cat (sa_cat, in
   place of the plain cat_img). The plain stack_ok / apart / mem_inv conjuncts are afn_pre's and the location's
   here. Outside the sections: by_token_pre segs B ly S rd cat tok s. *)
Definition by_token_pre (ly : alayout) (S : astate) (rd : reader) (cat tok : Z) (s : list Z) : Prop :=
tok <> 0 /\ sa_str rd tok s /\ sa_addr rd tok (Z.of_nat (length s) + 1) /\
sa_loc segs B ly S tok (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
sa_cat segs B rd cat.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_reac_box_catalogue_by_token : Z := 0.
Definition reac_box_catalogue_by_token_contract
(A_reac_box_catalogue_by_token STK_reac_box_catalogue_by_token RLO RHI cat : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (tok : Z) (s : list Z),
afn_pre segs B STK_reac_box_catalogue_by_token ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 tok -> 0 <= tok < 2 ^ 64 ->
by_token_pre ly S (aview segs (w_H W) mem) cat tok s ->
st_nev S + EV_reac_box_catalogue_by_token <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_box_catalogue_by_token regs mem md)
(apost_base segs B STK_reac_box_catalogue_by_token [] regs ly S W mem md EV_reac_box_catalogue_by_token
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.cat_ptr cat (SegModel.by_token s)) /\
 sa_kept segs W mem W' mem' regs STK_reac_box_catalogue_by_token (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
