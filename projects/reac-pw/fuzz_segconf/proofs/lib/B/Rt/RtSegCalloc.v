(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC5d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YC5d.v, with its module paths and module names changed; 16 of its 43 lines of code are new or changed and 89 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan builds: the contract of the calloc wrapper (interface row 13,
   proofs/reac-pw/fuzz_segconf/provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626)), in the form of the kit's malloc rule
   (lib/Reusable/YC5d.v:58-75 amalloc04_rule), as the image-A owner ruled (2026-10-30 16:17Z) on the consumer's shape
   (the calloc call shape the harness walk of LLVMFuzzerTestOneInput asked for). Statement text only:
   no function of the binary is proved here.

   Against amalloc04_rule, line by line: the same journal / chain / gp / tp / ra / alignment premises; a0 = m, a1 = n
   (the calloc ABI) with the size m * n in place of n, no overflow arm (m * n < MALLOC_MAX), and the primary-size cap
   m * n <= YGCalloc.PRIM_MAX (64512): asan_calloc zero-fills only a block of the primary allocator (image B
   0x33b84-0x33b94 skip the fill otherwise; image A 0x33af8-0x33b08) and no released proof shows a secondary block's bytes read 0
   (YGCalloc.v:140-144); the entry pc and the
   stack window the calloc path uses below the call's sp are parameters (the kit's acode has no calloc field); the post
   is the malloc post at size m * n - one allocator event (k + 1), the block (res, m * n) appended, the meter charged
   mo_malloc MT (m * n) - plus every one of the m * n bytes reading 0. No trace premise (this kernel's malloc and free
   rules take none). The name differs from lib/Reusable/YGCalloc.v's acalloc04_rule (fuzz_decode's form, with a trace
   premise), so both can be imported.

   Image-independent: pc_calloc and cstk are parameters (image B: the calloc trampoline 0x56cc4, PC_calloc in
   lib/B/Rt/SegRtPC.v). The image-B twin of lib/A/Rt/RtSegCalloc.v (commit 755e9278f8ff, sha256
   53722c5175e3): the same Definition word for word over the image-B kit copies (lib/B). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YGCalloc.
Import ListNotations.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.

Definition aseg_calloc04_rule (pc_calloc cstk : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (m n : Z) (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 m -> getr regsT 11 = w64 n ->
0 <= m -> 0 <= n -> m * n < MALLOC_MAX -> m * n <= YGCalloc.PRIM_MAX -> blocks_bytes Sc + m * n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> cstk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT (m * n)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc_calloc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m * n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - cstk) (sp0 + o) (fun a => res <= a < res + req_size (m * n)) /\
(forall i, 0 <= i < m * n -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
mo_le MT Sc S2 (mo_malloc MT (m * n))).

End d.
End b.
