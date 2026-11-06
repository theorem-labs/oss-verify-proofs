(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 29 of its 49 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_knock_refused (fuzz_segconf.c:502-514; fuzz_segconf.asan 0x87508, 48 bytes, 12 instructions; frame 16
   bytes): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return). Functional content: the plain contract
   lib/Prog/check_knock_refused_c.v:10-47 (check_knock_refused_pre :28-34), restated over the ASan reader
   rd = aview segs (w_H W) mem.
   was_knock (a1, `beqz a1` 0x87510, the full register) and strstr(got, "takes no plan") = NULL aborts. The needle
   is the .rodata literal .str.22 at 0x21300 (32-byte object, nm), formed by `auipc a1; addi a1,a1,-532`
   (0x87514-0x87518); strstr is called at 0x8751c and its result tested at 0x87520. It has no inline check of its
   own and writes only its frame.
   The abort site 0x87534 (after __asan_handle_no_return 0x87530) is reached from 0x87520 only; it is dead under
   check_kept's second conjunct, (negb k || strstr_found gs TNP) = true: kn = b2z k, so k = false returns at 0x87510
   and k = true asks that TNP occurs in gs, so the strstr row returns a nonzero pointer.
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - 2272, sp)]; here apost_base with footprint
   [] (the frame and strstr's frames are inside the call's own window [sp - STK_check_knock_refused, sp)) and the
   post tail sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract (no inline check site: the row of program.asan.tsv counts 0):
   - sa_addr rd got (length gs + 1): the strstr row's range of the haystack (the interceptor's StrstrCheck reads at
     most length gs + 1 bytes of it: fuzz_manifest lib/A/FMH_Rt.v, the comment of astrstr_realizes, the template
     of row 8).
   - the needle by the base's literal shape: forall s, In s check_knock_refused_LITS -> sa_lit segs B rd (lit s) s,
     with check_knock_refused_LITS = [TNP] and lit a parameter (image A: lit TNP = 0x21300). sa_lit gives the
     needle's bytes, NUL and tail, its range sa_addr rd (lit TNP) (length TNP + 1), and that it is an image object
     the runtime does not own; the plain contract read it at seg_spec.STR_TNP through mem_inv.
   - got's tail: got is stated with sa_str (sa_strz plus sa_tail), as the plain contract's cstr_at had its slack
     for musl's strstr (plain head :17-19: the haystack's slack); row 8's text, RtSeg.astrstr_realizes (pc gotw
     guard) at commit 80d098bd1905 (lib/A/Rt/RtSeg.v:117), asks atail_vis of both strings.
   - length gs + 1 < 2 ^ 32: the RtString-form rows' range check, aread_ok, asks it (fuzz_command
     lib/A/Rt/RtDefs.v:35-36 at 501c0d516c69; row 8 is in that form); sa_addr bounds it only by 2 ^ 63.
     got = c->refusal[i] is char[200].
   - sa_ssp rd gotw guard, gotw guard parameters (image A: gotw = 0xa36d8, the GOT word twoway_strstr loads at
     0x9b238; guard = __stack_chk_guard 0x5ff078, nm): musl's twoway_strstr (0x9b1f0) loads the guard word
     (0x9b23c) and stores it in its frame (0x9b250), a stack canary, as the plain contract's sa_got_guard /
     sa_guard premises say for the plain image.
   - sa_heap B ly S got (length gs + 1) in place of the plain `apart got _ lo sp`: got = c + 0x2e88 + 200 i lies in
     the reader's block c = malloc(0x40e8) (PREMISES-A section 2.3); a live heap block lies outside the stack
     window and outside the interceptor's scratch.
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes its
     own RELRO bounds): the string rows ask rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does not
     give.
   - No side-stack frame, no printf, no allocator entry: EV_check_knock_refused = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_knock_refused (fun _ => False): every byte outside the window
     [sp - STK_check_knock_refused, sp) reads at the exit as at the entry, the shadow of image objects included,
     which the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow
     entry, its one store is into its frame (`sd ra,8(sp)` 0x8750c), and below it musl's strstr and
     twoway_strstr store only into their own frames (16 bytes at 0x9b000; 2032 + 208 bytes at 0x9b1f0 /
     0x9b228, the canary at 0x9b250 among them). Row 8's text carries the RtString rows' keep clause with E =
     False (art_post, fuzz_command lib/A/Rt/RtDefs.v:89-99), which is what the walk needs for this conjunct
    (checked by the interceptor lane's review of its interface rows against these contracts, row 8).
   IMAGE-INDEPENDENT: no image module is Required; A_check_knock_refused, STK_check_knock_refused, RLO, RHI, lit,
   gotw and guard are parameters (image A: A_check_knock_refused = 0x87508; STK_check_knock_refused at least
   16 + 2 * ESTACK = 8,208, the 16-byte frame and the window row 8 asks, per the interceptor lane's review, O2).
   Call site: LLVMFuzzerTestOneInput 0x85668 (segA/evidence/callsites.asan.tsv).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); the row text below is the
   accepted v1, 5e0b8a44fdc):
     RtSeg.astrstr_realizes (pc gotw guard) (row 8, accepted at commit 80d098bd1905,
       lib/A/Rt/RtSeg.v:117) at the strstr trampoline (image A 0x43a24), with this contract's gotw guard.
   It is NOT a premise of this contract: the statement does not mention it. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_knock_refused_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Definition EV_check_knock_refused : Z := 0.
(* the .rodata literals the code passes to an interceptor: the needle "takes no plan" *)
Definition check_knock_refused_LITS : list (list Z) := [TNP].
(* the plain check_knock_refused_pre over the reader: the haystack got (where it lies, its shadow, its tail and its
   length bound added), the flag, check_kept's second conjunct, the needle literal and the stack-protector pair *)
Definition check_knock_refused_pre (ly : alayout) (S : astate) (rd : reader) (lit : list Z -> Z)
(got kn gotw guard : Z) (gs : list Z) (k : bool) : Prop :=
got <> 0 /\ sa_str rd got gs /\ Z.of_nat (length gs) + 1 < 2 ^ 32 /\
sa_heap B ly S got (Z.of_nat (length gs) + 1) /\ sa_addr rd got (Z.of_nat (length gs) + 1) /\
kn = seg_spec.b2z k /\ (negb k || strstr_found gs TNP) = true /\
(forall s, In s check_knock_refused_LITS -> sa_lit segs B rd (lit s) s) /\
sa_ssp rd gotw guard.
Definition check_knock_refused_contract (A_check_knock_refused STK_check_knock_refused RLO RHI : Z)
(lit : list Z -> Z) (gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (got kn : Z) (gs : list Z) (k : bool),
afn_pre segs B STK_check_knock_refused ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 got -> 0 <= got < 2 ^ 64 ->
getr regs 11 = w64 kn -> 0 <= kn < 2 ^ 64 ->
check_knock_refused_pre ly S (aview segs (w_H W) mem) lit got kn gotw guard gs k ->
st_nev S + EV_check_knock_refused <= EV_MAX ->
SRr segs W (cfg_at segs A_check_knock_refused regs mem md)
(apost_base segs B STK_check_knock_refused [] regs ly S W mem md EV_check_knock_refused
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_knock_refused (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
