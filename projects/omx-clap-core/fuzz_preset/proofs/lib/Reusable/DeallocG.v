(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AllocG.v at
   origin/cold/c-asan-realloc-primary b97c2fd1d44 (c-asan's milestone M1, the revision whose leaf gives
   apath + gflag instead of ireturns), with its module paths changed and the cgif_file instantiation at the end
   dropped: libreac/fuzz_decode instantiates the Section at its own image in lib/A/DecodeCalloc.v, and the cgif
   image files (YB1v, YB1q, YF0l, YF0m) that only the dropped instantiation needed are not imported. Statement
   only; no proof of it is on this branch (rule 24). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/Reusable/YGAlloc.v, with its module paths changed; 4 of its 82 lines of code are new or changed and 7 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AllocG.v at 95e6f1d72b6 (sha256 9fd0d69116a5) into lib/Reusable (shared by both images), with its module paths changed; the M1 text of this file (10c1218e6df) is replaced, not kept beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/Reusable/YGAlloc.v, with its module paths changed; 53 of its 99 lines of code are new or changed and 36 lines of the source are left out. *)
(* copy of proofs/cgif/cgif_file_fuzzer/lib/DeallocG.v@e8a7dd66acf2; do not edit. Only this line is added, and the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable. *)
(* The frame-generic contract of __asan::Allocator::Deallocate.

   The run starts at Deallocate's first instruction [pcD] and ends at the [ret] that comes back to Deallocate's
   caller: the early [ret] when the pointer is NULL, or, on a live block, the [ret] of the quarantine path
   (Deallocate tail-jumps to Allocator::QuarantineChunk after its epilogue, QuarantineChunk tail-jumps to
   Quarantine::Put, and Put returns to Deallocate's caller).  The caller's frame is abstract: the entry sp, the
   return pc, the BufferedStackTrace object [so], its trace buffer [bp] and the allocator instance [inst]
   (this, a0) are arbitrary, so that every caller (asan_free, Reallocate) uses the one walk.  The registers at
   the entry are Deallocate(this = inst, ptr = p, delete_size = 0, delete_alignment = 0, stack = so,
   alloc_type = atp).

   Section variables, in the order of AllocG.v (and of the realloc statements):
   - [segs], [B], [U]: the image, its symbols, the trace universe;
   - [mt], [ft]: the malloc tree and the free tree (cgif: YG00.malloc / free; the shared instance:
     malloc_cf / free_cf);
   - [ARX inst]: the allocator relation over the instance at [inst] (cgif: [inst = TFIB_INST /\ AR]);
   - [AOX]: the addresses the allocator owns (cgif: aowned B);
   - [rpre]: the premise on the state and the block size (cgif: rpre_dealloc_cgif);
   - [nmax], [lmax]: the size bound and the live-bytes bound (not used by Deallocate);
   - [lpost]: the extra post on the state (cgif: qtight);
   - [fpre]: the free call site's premise on the released block [fpre ly S W mem p n] (fuzz_state: no poisoned
     range inside the block; cgif: True);
   - [pcD]: Deallocate's entry pc;
   - [atp]: the alloc_type argument of the caller's call site (asan_free and Reallocate: FROM_MALLOC = 1);
   - [MP]: a predicate on the entry memory, which the walks carry to Put's call of Enqueue (DGif0.DIface's MP;
     cgif: fun _ => True).
   Coq drops the unused variables per definition: [adealloc_realizes] and its raw twin [adealloc_realizes_raw] take
   segs B U ft ARX AOX rpre lpost fpre pcD atp MP.  The plain form frames the memory on the view ([aview]); the raw
   twin adds the same frame on the raw bytes.

   [DFSTACK_G] is Deallocate's stack need below its entry sp.  Measured on the cgif_file asan-ubsan image:
   Deallocate's frame is 64 bytes, QuarantineChunk's 48 (it calls StackDepotPut, whose contract uses 512 bytes),
   Quarantine::Put's 80 (it calls QuarantineCache::Enqueue, 1088 bytes, and Quarantine::Drain, 4096 bytes, at
   its sp); both tail jumps run after the caller's epilogue, so every frame starts at Deallocate's entry sp.  The
   deepest chain is Put -> Drain, 80 + 4096 = 4176 bytes; DFSTACK_G = 8192 leaves room for the drain arm's
   callees.

   The leaf gives a trace [trc] with [apath (ft p tr S) trc r] and [gflag trc = true]: the result is the end of
   a path of the free tree whose every kernel answer was granted (the form amreal_SRr04 exports).

   The walk's own facts about ARX (the cells it reads, the post it re-establishes) are hypotheses of the proof,
   not part of this statement.  The proof is for the cgif_file asan-ubsan image: segs = tfibsegs, pcD = 0x3123c,
   atp = 1. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG.
Import ListNotations.
Open Scope Z_scope.

(* Deallocate's stack need below its entry sp (see the header). *)
Definition DFSTACK_G : Z := 8192.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
(* The trace premise (as in AllocG). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable pcD : Z.
Variable atp : Z.
(* The memory predicate at Deallocate's entry that the interface's Enqueue field needs at Put's call (DGif0.MP;
   cgif: fun _ => True). *)
Variable MP : (word -> option byte) -> Prop.

(* The machine state at Deallocate's entry.  [p] is NULL or a live block of size [n]. *)
Definition dealloc_pre (inst so bp : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z) : Prop :=
ARX inst ly S W mem md /\ rpre S n /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + DFSTACK_G <= spZ regs /\ ly_bot ly < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - DFSTACK_G <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 inst /\ getr regs 11 = w64 (sptr_addr B ly p) /\ getr regs 12 = w64 0 /\ getr regs 13 = w64 0 /\
getr regs 14 = w64 so /\ getr regs 15 = w64 atp /\
(* The stack object and its trace buffer: in the caller's frame, at or above the entry sp. *)
spZ regs <= so /\ so + 16 <= ly_stk_hi ly /\ so mod 8 = 0 /\
spZ regs <= bp /\ bp + 8 * 30 <= ly_stk_hi ly /\ bp mod 8 = 0 /\
(1 <= length tr <= 30)%nat /\
val_mem segs (mrestrict (w_H W) mem) so 8 bp /\
val_mem segs (mrestrict (w_H W) mem) (so + 8) 8 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict (w_H W) mem) (bp + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
U tr S /\ (p = PNull \/ In (p, n) (blocks S)) /\ fpre ly S W mem p n.

(* The post at the caller's return pc: ARX again, callee-saved registers kept, memory changed only on owned
   addresses, Deallocate's stack window, errno and the freed block's bytes.  The frame is on the view ([aview]), as
   the released callee contracts state it; [dealloc_post_raw] below adds the same frame on the raw memory. *)
Definition dealloc_post (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B DFSTACK_G regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - DFSTACK_G <= a < spZ regs -> apresent (w_H W') mem' a).

Definition dealloc_leaf (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* The raw twin: the post with the frame also on the raw memory (an ARX-style relation that reads raw bytes, which
   aview hides, can be carried across the call).  Its proof takes the callee contracts with raw frames
   (DIfaceR). *)
Definition dealloc_post_raw (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B DFSTACK_G regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(* The same frame on the raw memory (ARX-style relations read raw bytes that aview hides). *)
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
~ ascratch B DFSTACK_G regs (bv_unsigned x) -> ~ E (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - DFSTACK_G <= a < spZ regs -> apresent (w_H W') mem' a).

Definition dealloc_leaf_raw (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post_raw inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Definition adealloc_realizes : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md)
(dealloc_leaf inst ly S W regs mem md p n tr).

Definition adealloc_realizes_raw : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md)
(dealloc_leaf_raw inst ly S W regs mem md p n tr).
End b.

End a.
