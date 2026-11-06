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
(* The frame-generic contract of __asan::Allocator::Allocate.

   The run starts at Allocate's first instruction [pcA] and ends at its [ret], back at the caller's return pc.
   The caller's frame is abstract: the entry sp, the return pc, the BufferedStackTrace object [so], its trace
   buffer [bp] and the allocator instance [inst] (this, a0) are arbitrary, so that every caller (asan_malloc,
   Reallocate, asan_realloc's NULL-input call, calloc) uses the one walk.  The registers at the entry are
   Allocate(this = inst, size = n, alignment = al, stack = so, alloc_type = atp, can_fill = cf).

   Section variables, in this order (the Deallocate and realloc statements use the same order):
   - [segs], [B], [U]: the image, its symbols, the trace universe;
   - [mt], [ft]: the malloc tree and the free tree (cgif: YG00.malloc / free; the shared instance:
     malloc_cf / free_cf);
   - [ARX inst]: the allocator relation over the instance at [inst] (cgif: [inst = TFIB_INST /\ AR]);
   - [AOX]: the addresses the allocator owns (cgif: aowned B);
   - [rpre]: the premise on the state and the size (cgif: aregime /\ qmeter; the shared instance: True);
   - [nmax], [lmax]: the size bound and the live-bytes bound;
   - [lpost]: the extra post on the state (cgif: qtight);
   - [pcA]: Allocate's entry pc; [oomb]: the allocator's out-of-memory byte;
   - [al], [atp], [cf]: the alignment, alloc_type and can_fill arguments of the caller's call site.
   The size premise n < nmax keeps Allocate's size-too-big branch off: every instantiation has
   nmax <= kMaxAllowedMalloc - kPage.

   The leaf accepts both results of [mt]: a block (a0 = its address) or PNull (a0 = 0, the out-of-memory byte
   set; the caller sets errno).  It also gives a trace [trc] with [apath (mt n tr S) trc r] and
   [gflag trc = true]: the result is the end of a path of the model tree whose every kernel answer was granted
   (the form amreal_SRr04 exports), so a consumer reads the model-level post (e.g. a refusal's unchanged
   blocks, or its refutation by room) from its own lemma about [mt].

   The walk's own facts about ARX (the cells it reads, the post it re-establishes, the refusal arm) are
   hypotheses of the proof (AGtop.v), not part of this statement.  The proof is for the cgif_file asan-ubsan
   image: segs = tfibsegs, pcA = 0x31550, oomb = TFIB_OOM, al = 8, atp = 1 (FROM_MALLOC), cf in {0, 1}. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

(* Allocate's stack need below its entry sp (the same value as AGhy.AFSTACK). *)
Definition AFSTACK_G : Z := 4096.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
(* The trace premise on the stack trace and the state (cgif: the trace is in the universe; fuzz_state: C5,
   in the universe or st_nev S < EV_MAX). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable pcA : Z.
Variable oomb : Z.
Variable al : Z.
Variable atp : Z.
Variable cf : Z.

(* The machine state at Allocate's entry. *)
Definition alloc_pre (inst so bp : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z) : Prop :=
ARX inst ly S W mem md /\ rpre S n /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + AFSTACK_G <= spZ regs /\ ly_bot ly < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - AFSTACK_G <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 inst /\ getr regs 11 = w64 n /\ getr regs 12 = w64 al /\ getr regs 13 = w64 so /\
getr regs 14 = w64 atp /\ getr regs 15 = w64 cf /\
(* The stack object and its trace buffer: in the caller's frame, above the entry sp. *)
spZ regs <= so /\ so + 16 <= ly_stk_hi ly /\ so mod 8 = 0 /\
spZ regs <= bp /\ bp + 8 * 30 <= ly_stk_hi ly /\ bp mod 8 = 0 /\
(1 <= length tr <= 30)%nat /\
val_mem segs (mrestrict (w_H W) mem) so 8 bp /\
val_mem segs (mrestrict (w_H W) mem) (so + 8) 8 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict (w_H W) mem) (bp + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
U tr S /\ 0 <= n < nmax /\ blocks_bytes S + n <= lmax.

(* The post at the caller's return pc: ARX again, callee-saved registers kept, memory changed only on owned
   addresses, Allocate's stack window, errno and the new block. *)
Definition alloc_post (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B AFSTACK_G regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(* The same frame on the raw memory (ARX-style relations read raw bytes that aview hides). *)
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
~ ascratch B AFSTACK_G regs (bv_unsigned x) -> ~ E (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - AFSTACK_G <= a < spZ regs -> apresent (w_H W') mem' a).

Definition alloc_leaf (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
alloc_post inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) /\
(fst r = PNull -> val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

(* M1: the contract for the primary sizes (0 <= n <= 64512); [aalloc_realizes] (every n < nmax) adds the
   secondary path. *)
Definition aalloc_prim_realizes : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre inst so bp ly S W regs mem md n tr -> n <= 64512 ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf inst ly S W regs mem md n tr).

Definition aalloc_realizes : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre inst so bp ly S W regs mem md n tr ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf inst ly S W regs mem md n tr).
End b.

End a.
