(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignore_file_c.v; 19 of its 47 lines of code are new or changed and 13 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_segments_c.v; 20 of its 51 lines of code are new or changed and 16 lines of the source are left out. *)
(* cross_check (reac_segconf.c:303-325, static; fuzz_segconf.asan 0x89218, 724 bytes, 181 instructions; frame 128
   bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog
   form (afn_pre at the entry, SRr of apost_baseF at the return: it reaches the printf wrappers through refuse).
   Functional content: the plain contract lib/Prog/cross_check_c.v:13-47 (cross_check_pre :28-31,
   cross_check_W :33-34, the contract :36-47), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x89218-0x894e8): for i < c->n (lw of c + 0x2c80, reloaded
   each pass), s = &c->seg[i]: model_set and not (role_set and role = BOX) -> refuse(c, 0, F_xmodel, s->name,
   s->model) (jal 0x89350), model_set = 0 (sw 0x89364), `sb zero` s->model[0] (0x89378); else BOX without
   model_set -> refuse(c, 0, F_xbox, s->name) (jal 0x8939c), role_set = 0 (0x893a8), role = AUTO (0x893b4). The
   post is the plain one: c holds SegModel.cross_check rcs.
   What it reads: the shadow base through the GOT word as_got_shadow B (image A 0xa2a50, an AR constant), the c
   block, the two formats (CROSS_CHECK_LITS), and through refuse what refuse_pre names. What it writes: its frame,
   refuse's frames, the seg entries (model[0], model_set, role, role_set) and through refuse refusal[],
   n_refusals, refused (cross_check_W, the plain write list without its stack range). No abort site
   (provenance/evidence/image-tables/program.asan.tsv line 23).
   ASAN FACTS ADDED over the plain contract:
   - the 10 inline checks (program.asan.tsv: _load4:6 _store1:1 _store4:3), each with its error arm
     (provenance/evidence/image-tables/callsites.asan.tsv lines 341-350): load4 c->n at entry (arm 0x894ac) and in the loop (arm
     0x894bc); load4 s->role_set at s + 20 (arm 0x894b4); load4 s->role at s + 16 (arm 0x894c4); load4
     s->model_set at s + 60 on both paths (arms 0x894c8, 0x894e0); store4 model_set (arm 0x894d0); store1 model[0]
     at s + 36 (arm __asan_report_store1 0x894d8); store4 role_set (arm 0x894e8); store4 role (arm 0x8945c). Every
     address lies in the block: killed by cross_check_pre's sa_addr rd c SEG_C_SIZE.
   - where the block lies: sa_heap (malloc(0x40e8) at LLVMFuzzerTestOneInput 0x84f80); the strings it hands
     refuse (s->name, s->model) lie in it, which gives refuse_pre's refuse_va_locs.
   - the formats F_xmodel and F_xbox, and refuse's own literals, by sa_lit (CROSS_CHECK_LITS).
   - no side-stack frame of its own; refuse takes the first one: sa_room S.
   - NO keep clause (sa_kept) in the post: refuse's post has none (its class-0 frame and that frame's shadow are
     written outside every window and footprint, see refuse_c.v), so none is provable here either.
   - it reaches snprintf and vsnprintf through refuse: apost_baseF, sa_frm0, sa_ssp rd gotw guard.
   - arodata_okP over the window RLO .. RHI: refuse's contract asks it.
   - EV_cross_check = 0, post tail sa_noalloc.
   Call site (callsites.asan.tsv line 338): reac_segconf_parse 0x891fc (c, after reac_segconf_parse_file of the
   last file).
   image A: A_cross_check = 0x89218; STK_cross_check = 128 + STK_refuse (INFERENCE: its frame and refuse's window
   below it); RLO = 0xa14a0, RHI = 0xa3748 (readelf, fuzz_command's CmdGlob.v convention); gotw = 0xa36d8, guard =
   0x5ff078 (as refuse_c.v); lit F_xmodel = 0x21c00 (.str.44), lit F_xbox = 0x21ca0 (.str.45) (objdump 0x892a0,
   0x892a4; bytes read from the pin), and refuse's three (refuse_c.v).
   IMAGE-INDEPENDENT: no image module is Required; A_cross_check, STK_cross_check, RLO, RHI, lit, gotw and guard
   are parameters.
   The WALK takes as Section hypotheses: refuse_contract (lib/A/Prog/refuse_c.v, at A_refuse 0x88da4). It calls
   no interceptor and no runtime entry itself (program.asan.tsv line 23: no runtime callee); refuse's entries are
   refuse's walk's. It is NOT a premise of this contract: the statement does not mention it. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* The literals cross_check passes (its two formats) and those of its callee refuse (reac_segconf.c's module). *)
Definition CROSS_CHECK_LITS : list (list Z) := [F_xmodel; F_xbox] ++ REFUSE_LITS.
(* The bytes outside its stack window cross_check writes (the plain cross_check_W, lib/Prog/cross_check_c.v:33-34,
   without its first range, which is the call's own stack window here). *)
Definition cross_check_W (c : Z) : list (Z * Z) :=
[(c, c + seg_spec.RSEG_SIZE * 32); (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW)].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What cross_check asks of its caller (the plain cross_check_pre, lib/Prog/cross_check_c.v:28-31, over the reader
   rd = aview segs (w_H W) mem): c is the reader's block, a live heap block of 16616 bytes holding rcs,
   addressable, with room for 64 more refusals in the u32 c->refused (two per entry, 32 entries); printf's machine
   (the rounding mode and the stack-protector cells); the literals. The plain stack_ok / apart / blk_noimg /
   mem_inv conjuncts are afn_pre's, sa_heap's and sa_lit's here.
   Outside the sections: cross_check_pre segs B lit gotw guard ly S rd c rcs. *)
Definition cross_check_pre (lit : list Z -> Z) (gotw guard : Z) (ly : alayout) (S : astate) (rd : reader)
(c : Z) (rcs : rconf) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf rd c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr rd c seg_spec.SEG_C_SIZE /\
rc_refused rcs + 64 < 2 ^ 32 /\
sa_frm0 /\ sa_ssp rd gotw guard /\
(forall x, In x CROSS_CHECK_LITS -> sa_lit segs B rd (lit x) x).
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_cross_check : Z := 0.
Definition cross_check_contract (A_cross_check STK_cross_check RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z)
: Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c : Z) (rcs : rconf),
afn_pre segs B STK_cross_check ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
cross_check_pre lit gotw guard ly S (aview segs (w_H W) mem) c rcs ->
(* room for refuse's class-0 side-stack frame, the first of the nest *)
sa_room S ->
st_nev S + EV_cross_check <= EV_MAX ->
SRr segs W (cfg_at segs A_cross_check regs mem md)
(apost_baseF segs B STK_cross_check (cross_check_W c) regs ly S W mem md EV_cross_check
(fun ly' S' W' regs' mem' md' =>
 sa_rconf (aview segs (w_H W') mem') c (SegModel.cross_check rcs) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
