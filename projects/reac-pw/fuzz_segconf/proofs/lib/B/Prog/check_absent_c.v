(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 23 of its 44 lines of code are new or changed and 146 lines of the source are left out. *)
(* check_absent (fuzz_segconf.c:544-554; fuzz_segconf.asan 0x875e8, 112 bytes, 28 instructions; frame 32 bytes):
   the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr
   of apost_base at the return). Functional content: the plain contract lib/Prog/check_absent_c.v:11-41
   (check_absent_pre :27-28), restated over the ASan reader rd = aview segs (w_H W) mem.
   reac_segconf_find(c, name) (0x87600), reac_segconf_role(c, name, NULL) (0x87614, a2 = 0 by `li a2,0` at
   0x87610), reac_segconf_ignored(c, name) (0x87624) or reac_segconf_model(c, name) (0x87634) nonzero aborts, each
   tested in that order by `bnez a0`. c and name are kept in s1 / s0 across the calls. It has no inline check of
   its own and writes only its frame; the four callees write only their own frames (role writes no out cell when
   out = NULL).
   The abort site 0x87654 (after __asan_handle_no_return 0x87650) is reached from 0x87604, 0x87618, 0x87628 and
   0x87638; all four are dead under SegModel.absent rcs nm = true, the second conjunct of check_absent_pre: absent
   asks r_find = None, r_role = None, r_ignored = false and r_model = None, and for these answers the callee
   contracts return seg_spec.find_ptr c rcs nm = 0 (find), 0 (role and ignored) and seg_spec.model_ptr c rcs nm = 0
   (model).
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - CHECK_ABSENT_STACK, sp)]; here apost_base
   with footprint [] (its frame and the callees' frames are inside the call's own window
   [sp - STK_check_absent, sp)) and the post tail sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract (no inline check site: the row of program.asan.tsv counts 0). The first
   conjunct of check_absent_pre is the G5 contracts lane's A-level query_pre (lib/A/Prog/reac_segconf_find_c.v), which
   this file Requires, as the plain check_absent_pre uses the plain query_pre; it carries, over the plain query_pre:
   - sa_addr rd c SEG_C_SIZE and sa_addr rd name (length nm + 1): the callees' inline checks of c and the strcmp
     row's ranges of the names and of name;
   - sa_heap B ly S c SEG_C_SIZE (c = malloc(0x40e8), PREMISES-A section 2.3) and sa_loc for name (the probe in
     LLVMFuzzerTestOneInput's class-3 side-stack frame, call site 0x85744, or the .rodata literal "nosuch0" at
     0x21040, call site 0x857a4, segA/evidence/callsites.asan.tsv) in place of the plain `apart _ _ lo sp`;
   - name with its tail (sa_str: the strcmp row asks atail_vis) and length nm + 1 < 2 ^ 32 (aread_ok).
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes its
     own RELRO bounds): the callees' contracts ask it, for the strcmp row's rt_rom_view.
   - No side-stack frame, no printf, no allocator entry, and none in the callees: EV_check_absent = 0, apost_base,
     sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_absent (fun _ => False): every byte outside the window
     [sp - STK_check_absent, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). It is what lets the walk re-give query_pre at each of the
     four calls when name is the .rodata literal "nosuch0" (the G4 / G5 walk of check_absent). This clause RESTS ON
     THE CALLEES' sa_kept: its own stores are into its 32-byte frame (`sd` 0x875ec-0x875f4), and the rest of the
     window is the four callees', each called at sp - 32 with STK_check_absent covering 32 bytes plus that
     callee's STK; each callee's contract (the G5 contracts lane's) states sa_kept over its own window and its
     footprint, and the four footprints are empty here: find, ignored and model write none, and role's role_W out _
     is [] at out = 0 (a2 = 0 at 0x87610). The four keeps chain by transitivity of equality of aview.
   IMAGE-INDEPENDENT: no image module is Required; A_check_absent, STK_check_absent, RLO and RHI are parameters
   (image A: A_check_absent = 0x875e8). STK_check_absent is ONE parameter: it covers the 32-byte frame and the
   deepest of the four callees' own STK parameters; the walk instantiates it, no arithmetic over another
   function's constants is stated here.
   The WALK takes these contracts as Section hypotheses (none is a premise of this contract):
     reac_segconf_find_contract (image A 0x894ec), reac_segconf_role_contract (0x895f0, its role_pre's out = 0
     arm), reac_segconf_ignored_contract (0x89594), reac_segconf_model_contract (0x897e8), all in lib/A/Prog
     (the G5 contracts lane), each at the same RLO RHI.
   Through them, RtString.astrcmp_realizes (row 17 of the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); rows 16-19 were added by the
   accepted v1, 5e0b8a44fdc) is a hypothesis of the callees' walks, not of this one. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_absent_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
(* the events this call spends: 0, it reaches no allocator entry, nor do its four callees *)
Definition EV_check_absent : Z := 0.
(* the plain check_absent_pre over the reader: the A-level query_pre of reac_segconf_find (the reader's block c
   and the string name) and SegModel.absent *)
Definition check_absent_pre (ly : alayout) (S : astate) (rd : reader) (c name : Z) (rcs : rconf) (nm : list Z)
: Prop :=
query_pre segs B ly S rd c name rcs nm /\ absent rcs nm = true.
Definition check_absent_contract (A_check_absent STK_check_absent RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c name : Z) (rcs : rconf) (nm : list Z),
afn_pre segs B STK_check_absent ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
getr regs 11 = w64 name -> 0 <= name < 2 ^ 64 ->
check_absent_pre ly S (aview segs (w_H W) mem) c name rcs nm ->
st_nev S + EV_check_absent <= EV_MAX ->
SRr segs W (cfg_at segs A_check_absent regs mem md)
(apost_base segs B STK_check_absent [] regs ly S W mem md EV_check_absent
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_absent (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
