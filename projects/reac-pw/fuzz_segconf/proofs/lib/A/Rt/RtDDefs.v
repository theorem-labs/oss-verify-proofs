(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer's lib/YG0d.v acall_pre, malloc_leaf and amalloc_realizes with the scratch window as a parameter, and two inner entries of the malloc path of plugin-hostd/fuzz_command's memory-checking image (the malloc interceptor's body, and asan_malloc with a stack trace built by its caller), which its strndup and strdup entries call. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDDefs.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Open Scope Z_scope.

(* The allocating string entries call the malloc path below the trampoline cgif's amalloc_realizes is stated at
   (pc_wrap_malloc = 0x58984 on this image): strndup at 0x4576c calls the interceptor's body 0x58b58, which builds
   the stack trace itself (pc0 = 0x58c20); strdup builds the trace in its own frame (BufferedStackTrace at its sp,
   unwinder pc 0x4cdd0) and calls __asan::asan_malloc 0x34528 with a0 = size, a1 = &trace.

   Window. astrdup_realizes and astrndup_realizes (RtAlloc.v) give ASTACK below the entry's sp; the entry's own frame
   is 2,144 (strdup) or 2,160 (strndup) bytes, so at the inner call ASTACK - 2,160 = 14,224 bytes are known present.
   The inner contracts are therefore stated at MALLOC_IN_STK = 14,208 (16-aligned), not at cgif's ASTACK; the measured
   depth of the malloc path below the inner entry is 5,584 bytes (7,744 - 2,160). *)
Definition MALLOC_IN_STK : Z := 14208.
Definition PC_malloc_body : Z := 0x56e0c.
Definition PC_asan_malloc : Z := 0x330bc.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* YG0d.v acall_pre with the window [stk] for ASTACK, MINUS `ly_bot ly < spZ regs`. That premise is dropped on
   purpose (2026-10-29): a caller of these inner entries has it for its OWN stack pointer, not for
   the entry's, which sits 2,128 bytes lower (strndup 2,160), and the model allows ly_bot to be anywhere up to the
   caller's sp (lib/Reusable/YG0f.v:327 gives only ly_stk_lo <= ly_bot < ly_top). So a composition from the
   caller's acall_pre could not discharge it, and the entries' own walks take the unwinder's bottom case instead:
   where the frame pointer is at or below ly_bot, UnwindFast stops at once and the recorded trace is [pc_ra0],
   which is what the trace below says. *)
Definition acall_pre_w (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
AR segs B ly S W mem md /\ aregime S /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + stk <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
qmeter S.

(* The trace an inner entry records: [pc_ra0] alone when the frame pointer is at or below ly_bot (UnwindFast's
   bottom case, 0x78f34), else the chain the caller passes. *)
Definition inner_trace (ly : alayout) (pc_ra0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
if spZ regs <=? ly_bot ly then [pc_ra0] else call_trace ly pc_ra0 regs ch.

(* YG0d.v malloc_leaf with the window [stk] for ASTACK. *)
Definition malloc_leaf_w (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post segs B stk ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r).

(* The malloc interceptor's body, entered by a call (strndup 0x4576c): YG0d.v amalloc_realizes at [pc] with the
   unwinder pc [pc_ra0] and the window MALLOC_IN_STK. *)
Definition amalloc_body_realizes (pc pc_ra0 : Z) : Prop :=
forall ly S W regs mem md n ch,
acall_pre_w MALLOC_IN_STK ly S W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In (inner_trace ly pc_ra0 regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
amreal segs (malloc n (inner_trace ly pc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(malloc_leaf_w MALLOC_IN_STK ly S W regs mem md n).

(* A BufferedStackTrace at [p] holding the frames [tr]: the trace pointer (to its own buffer at p + 16), the
   32-bit size and the 32-bit tag (0), and the frames. *)
Definition astrace_at (W : world segs) (mem : word -> option byte) (p : Z) (tr : list Z) : Prop :=
rdword (aview segs (w_H W) mem) p = Some (p + 16) /\
rd32 (aview segs (w_H W) mem) (p + 8) (Z.of_nat (length tr)) /\
rd32 (aview segs (w_H W) mem) (p + 12) 0 /\
(forall i, (i < length tr)%nat -> rdword (aview segs (w_H W) mem) (p + 16 + 8 * Z.of_nat i) = Some (nth i tr 0)).

(* __asan::asan_malloc(size, &stack) with a trace its caller built (strdup 0x4cdc0): the same model step as a call
   of malloc, with the trace read from memory. The trace object lies in the caller's frame, above the window.
   Window MALLOC_ASAN_STK = 12,080 = MALLOC_IN_STK - 2,128 (the malloc interceptor's frame), so the body form at
   0x58b58 and the trampoline form at 0x58984 (cgif's amalloc_realizes, ASTACK) both follow from this one by the
   walk of the interceptor's own code; strdup calls it with ASTACK - 2,144 = 14,240 bytes known present. Measured
   depth below asan_malloc's entry: 3,456 bytes. *)
Definition MALLOC_ASAN_STK : Z := 12080.
Definition amalloc_inner_realizes (pc : Z) : Prop :=
forall ly S W regs mem md n p tr,
AR segs B ly S W mem md -> aregime S ->
YK0s.ret_ok (getr regs 1) ->
(* [spZ regs + 2128 <= ly_stk_hi ly]: the caller's own frame holds at least the interceptor body's 2,128 bytes, so
   the body's entry sp0 = spZ regs + 2128 stays at or below the stack's top. Every caller gives it: the body has
   sp = sp0_body - 2128 with sp0_body <= ly_stk_hi, strdup's frame is 2,144 bytes and strndup's 2,160. *)
spZ regs mod 16 = 0 -> ly_stk_lo ly + MALLOC_ASAN_STK <= spZ regs -> spZ regs + 2128 <= ly_stk_hi ly ->
(forall a, spZ regs - MALLOC_ASAN_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> qmeter S ->
getr regs 10 = w64 n -> getr regs 11 = w64 p ->
(* The trace object at [p] is 8-aligned, has room for the depot's 30 frames, and holds at least one frame: the chain
   hands it to StackDepotPut, whose spec (lib/A/AFl0.v:68-78 tfib_depot_spec) asks buf = p + 16 to be 8-aligned
   with buf + 8 * 30 <= ly_stk_hi, and keeps the trace size in [1, 30]. Every caller gives these: the body's trace
   object sits in its 2,128-byte frame (p = sp0 - 2128, sp0 mod 16 = 0, so p + 256 <= sp0) and always holds pc0
   (inner_trace); strdup's BufferedStackTrace has a 255-entry buffer in its frame and holds the pc. strndup does not
   call this entry: it calls the interceptor body, which builds the trace in its own frame. *)
spZ regs <= p -> p mod 8 = 0 -> p + 16 + 8 * 30 <= ly_stk_hi ly ->
astrace_at W mem p tr -> (1 <= length tr)%nat -> (length tr <= kUnwindMax)%nat ->
0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In tr (as_universe B) \/ st_nev S < EV_MAX ->
amreal segs (malloc n tr S) W
(cfg_at segs pc regs mem md)
(malloc_leaf_w MALLOC_ASAN_STK ly S W regs mem md n).

End c.
End b.
