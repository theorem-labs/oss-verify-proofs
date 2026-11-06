(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 40 of its 60 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_declared (fuzz_segconf.c:375-388, 556-577; fuzz_segconf.asan 0x87658, 376 bytes, 94 instructions; frame 80
   bytes): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return). Functional content: the plain contract
   lib/Prog/check_declared_c.v:10-52 (check_declared_pre :29-38), restated over the ASan reader
   rd = aview segs (w_H W) mem.
   vlans_are(got, want, tab, n, mt, mn, cap) = 0 aborts. The code compares got (a0) with want (a1) (0x87680) and n
   (a3) with mn (a5) (0x87688) as full registers; for i < n (`blez s3` 0x876a0) it reads tab[i].vid (`lhu`,
   tab + 18 i + 16) and mt[i].vid (`lw`, mt + 20 i + 16) and compares them (0x876dc), then calls
   strcmp(tab + 18 i, mt + 20 i) (0x876e8) and tests the result (0x876ec); last it forms tab + 18 cap from the low
   32 bits of cap (a6; slli / mulhu / add, 0x87730-0x87740) and reads the 18 bytes there one by one (`lbu`
   0x87760), each compared with 0x5a (0x87764, then 0x87790). It writes only its frame (80 bytes; the plain build's
   is 48).
   The abort site 0x877c4 (after __asan_handle_no_return 0x877c0) is reached from 0x87680, 0x87688, 0x876dc,
   0x876ec and 0x87790; all five are dead under vlans_are (gv, gt) (wv, wt) cap = true and the guard entry
   (sa_guardtab): gv = wv makes got = want; the lengths are equal, so n = mn; each pair's vids are equal (the
   rvlan vid is below 65536, so `lhu` and the sign extension of `lw` read the same value) and its parents compare
   equal, so the strcmp row's post gives zero results; tab[cap] holds 0x5a x 18.
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - 48, sp)]; here apost_base with footprint []
   (the frame is inside the call's own window [sp - STK_check_declared, sp)) and the post tail
   sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract:
   - sa_addr rd tab (RVLAN_SIZE * (cap + 1)) kills the load2 check site of tab + 18 i + 16 (shadow byte `lb`
     0x876bc, slow path 0x8770c-0x87714, error arm __asan_report_load2 0x877cc) and the load1 check site of the
     guard bytes tab + 18 cap + j, j < 18 (shadow byte 0x87758, slow path 0x87780-0x87784, error arm
     __asan_report_load1 0x87788), and gives strcmp's range of each parent tab + 18 i.
   - sa_addr rd mt (MVLAN_SIZE * (cap + 1)) kills the load4 check site of mt + 20 i + 16 (shadow byte 0x876cc,
     error arm __asan_report_load4 0x8772c) and gives strcmp's range of each parent mt + 20 i.
   - each parent with its tail (sa_str): the strcmp row asks atail_vis of both strings, and a parent's tail can run
     past its 18- or 20-byte entry into the next one, which sa_rtab / sa_mtab do not fix when it is the entry after
     the last; so each tab[i].parent and mt[i].parent is stated with sa_str beside the plain rtab_at / mtab_at.
   - sa_heap of both tables in place of the plain `apart _ _ lo sp`: tab = calloc(cap + 1, 0x12) and
     mt = calloc(cap + 1, 0x14) are the harness's blocks (LLVMFuzzerTestOneInput 0x857b8 / 0x857c8, PREMISES-A
     section 2.3); a live heap block lies outside the stack window and outside the interceptor's scratch.
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes its
     own RELRO bounds): the strcmp row asks rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does not
     give.
   - The shadow base is read through the GOT word 0xa2a50 and __asan_shadow_memory_dynamic_address 0xabff8
     (0x87694-0x8769c; PREMISES-A section 1.5): AR's const cells as_got_shadow / as_shadow_cell
     (lib/Reusable/YG0f.v aso_const_law), so neither is a premise or a parameter.
   - No side-stack frame, no printf, no allocator entry: EV_check_declared = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_declared (fun _ => False): every byte outside the window
     [sp - STK_check_declared, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow entry,
     its own stores are into its frame (`sd` 0x8765c-0x8767c), and the strcmp row's post keeps every byte
     outside the interceptor's scratch window with E = False (art_post, fuzz_command lib/A/Rt/RtDefs.v:89-99;
     RtString.v astrcmp_realizes), a window STK_check_declared covers; the abort and report arms are dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_declared, STK_check_declared, RLO and RHI are parameters
   (image A: A_check_declared = 0x87658; STK_check_declared covers the 80-byte frame and the window the strcmp row
   asks).
   Call site: LLVMFuzzerTestOneInput 0x85c10 (segA/evidence/callsites.asan.tsv).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); rows 16-19 were added by the
   accepted v1, 5e0b8a44fdc):
     RtString.astrcmp_realizes (row 17) at the strcmp trampoline (image A 0x43a14), once per entry.
   It is NOT a premise of this contract: the statement does not mention it. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_declared_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Definition EV_check_declared : Z := 0.
(* the plain check_declared_pre over the reader: the two answers, the two tables (where each lies, its shadow and
   each parent's tail added), the guard entry, the counts and the spine's vlans_are *)
Definition check_declared_pre (ly : alayout) (S : astate) (rd : reader) (got want tab n mt mn cap : Z)
(gv wv : Z) (gt wt : list (list Z * Z)) : Prop :=
got = gv mod 2 ^ 64 /\ want = wv mod 2 ^ 64 /\ - 2 ^ 31 <= gv < 2 ^ 31 /\ - 2 ^ 31 <= wv < 2 ^ 31 /\
0 <= cap < 40 /\
tab <> 0 /\ tab mod 16 = 0 /\ sa_rtab rd tab gt /\ sa_guardtab rd tab cap /\
sa_heap B ly S tab (seg_spec.RVLAN_SIZE * (cap + 1)) /\ sa_addr rd tab (seg_spec.RVLAN_SIZE * (cap + 1)) /\
(forall i, (i < length gt)%nat ->
 sa_str rd (tab + seg_spec.RVLAN_SIZE * Z.of_nat i) (fst (nth i gt ([], 0)))) /\
n = Z.of_nat (length gt) /\
mt <> 0 /\ mt mod 16 = 0 /\ sa_mtab rd mt wt /\
sa_heap B ly S mt (seg_spec.MVLAN_SIZE * (cap + 1)) /\ sa_addr rd mt (seg_spec.MVLAN_SIZE * (cap + 1)) /\
(forall i, (i < length wt)%nat ->
 sa_str rd (mt + seg_spec.MVLAN_SIZE * Z.of_nat i) (fst (nth i wt ([], 0)))) /\
Z.of_nat (length wt) <= cap /\ mn = Z.of_nat (length wt) /\
vlans_are (gv, gt) (wv, wt) cap = true.
Definition check_declared_contract (A_check_declared STK_check_declared RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (got want tab n mt mn cap gv wv : Z) (gt wt : list (list Z * Z)),
afn_pre segs B STK_check_declared ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 got -> 0 <= got < 2 ^ 64 ->
getr regs 11 = w64 want -> 0 <= want < 2 ^ 64 ->
getr regs 12 = w64 tab -> 0 <= tab < 2 ^ 64 ->
getr regs 13 = w64 n -> 0 <= n < 2 ^ 64 ->
getr regs 14 = w64 mt -> 0 <= mt < 2 ^ 64 ->
getr regs 15 = w64 mn -> 0 <= mn < 2 ^ 64 ->
getr regs 16 = w64 cap -> 0 <= cap < 2 ^ 64 ->
check_declared_pre ly S (aview segs (w_H W) mem) got want tab n mt mn cap gv wv gt wt ->
st_nev S + EV_check_declared <= EV_MAX ->
SRr segs W (cfg_at segs A_check_declared regs mem md)
(apost_base segs B STK_check_declared [] regs ly S W mem md EV_check_declared
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_declared (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
