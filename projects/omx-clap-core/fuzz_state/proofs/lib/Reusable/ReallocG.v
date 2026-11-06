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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/Reusable/YGAlloc.v, with its module paths and module names changed; 127 of its 160 lines of code are new or changed and 49 lines of the source are left out. *)
(* copied from proofs/cgif/cgif_file_fuzzer/lib/ReallocG.v @ 2bd8ae006ef (a working branch; byte-identical at a Theorem Labs lane's buildable snapshot 478a815d97c, a working branch), module paths changed only. *)
(* The frame-generic realloc statements on the cgif_file core.

   ported from proofs/cgif/cgif_rgb_fuzzer/lib (cgif_rgb's released realloc family on the cgif_rgb image: the
   YF6s-YF6u prefix, the YF78 composition with its NULL-return arm, realloc_tree at YG0f.v:15, the realloc leaf at
   YG0f.v:204, and the section-variable statements of ReallocP.v), restated over the cgif_file core with the leaves
   in AllocG.v's style (ARX, AOX, lpost, the granted trace).

   Section variables, in the order of AllocG.v and DeallocG.v:
   - [segs], [B], [U]: the image, its symbols, the trace premise of the Allocate / Deallocate calls ([U tr S]; not
     used by the statements here, kept for the shared order);
   - [mt], [ft]: the malloc tree and the free tree (cgif: YG00.malloc / free; the shared instance:
     malloc_cf / free_cf);
   - [ARX inst]: the allocator relation over the instance at [inst];
   - [AOX]: the addresses the allocator owns;
   - [rpre]: realloc's premise on the state and the new size (cgif: the three-event regime, cgif_rgb's aregime3,
     with qmeter).  It is NOT the Allocate premise: the composition (RGtop.v) takes Allocate's and Deallocate's
     premises as its own variables and relates them to [rpre] by its model obligations;
   - [nmax], [lmax]: the size bound and the live-bytes bound;
   - [lpost]: the extra post on the state (cgif: qtight);
   - [fpre]: the free call site's premise on the released old block, [fpre ly S W mem p n_old] (fuzz_state: no
     poisoned range inside the block; cgif: True).  realloc(p, n) takes it at the entry; the composition passes
     it on to DeallocG's contract at Reallocate's call of Deallocate;
   - [rU]: realloc's entry premise on the trace and the state, [rU (call_trace ly pc0 regs ch) S] (cgif:
     fun tr _ => In tr (as_universe B); fuzz_state: In tr Uc \/ st_nev S + 2 < EV_MAX, realloc ticks st_nev three
     times).  RGtop.v's model obligations transport it to [U] at the Allocate and Deallocate calls;
   then the image constants:
   - [pcR]: realloc's entry pc (the realloc wrapper, __wrap_realloc);
   - [pc0]: the first pc of the trace (the return pc of the interceptor's second GetCurrentPc call, the long branch);
   - [inst]: the allocator instance asan_realloc passes to Reallocate / Allocate;
   - [oomb]: the allocator's out-of-memory byte;
   - [pcM]: the entry pc of Reallocate's copy routine, REAL(memcpy) (the uninstrumented libc memcpy reached through
     the GOT; NOT __asan_memcpy).  [amemcpy_realizes] is its contract; RGtop.v takes it as a hypothesis.
   Coq drops the unused variables per definition (e.g. [realloc_pre] takes segs B ARX inst).

   The statements:
   - [arealloc_realizes_all]: p a live block, 1 <= n < nmax, the tree [realloc_tree_with mt ft p n tr S];
   - [arealloc_null_realizes]: p = NULL, the tree [realloc_null_tree_with mt ft n tr S];
   - the NULL-return arm, inside the first: when the result is PNull, [realloc_leaf] gives [mt_refused], the old
     block still live, errno 12 at [as_errno B] and the out-of-memory byte; [realloc_leaf_null] extracts it as
     [realloc_null_post].

   No realloc code exists on the cgif_file asan-ubsan image (frame/REALLOC-ADDRS-cgif_file.md), so these
   statements have no default instantiation here; a consumer instantiates them on its own image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

(* Reallocate's continuation after the inner malloc: on PNull return it; on a block q, free the old block p and
   return q. *)
Definition realloc_k (ft : sptr -> list Z -> M unit) (p : sptr) (tr : list Z) (q : sptr) : M sptr :=
match q with
| PNull => YG00.ret PNull
| _ => YG00.bind (ft p tr) (fun _ => YG00.ret q)
end.

(* The realloc tree over a malloc tree [mt] and a free tree [ft]: the entry step [ft PNull], [mt n], then
   [realloc_k].  At [mt = YG00.malloc], [ft = YG00.free] it is cgif_rgb's YG0f.realloc_tree. *)
Definition realloc_tree_with (mt : Z -> list Z -> M sptr) (ft : sptr -> list Z -> M unit)
(p : sptr) (n : Z) (tr : list Z) : M sptr :=
YG00.bind (ft PNull tr) (fun _ => YG00.bind (mt n tr) (realloc_k ft p tr)).

(* realloc(NULL, n): the entry step, then the malloc tree. *)
Definition realloc_null_tree_with (mt : Z -> list Z -> M sptr) (ft : sptr -> list Z -> M unit)
(n : Z) (tr : list Z) : M sptr :=
YG00.bind (ft PNull tr) (fun _ => mt n tr).

Lemma realloc_k_null : forall ft p tr, realloc_k ft p tr PNull = YG00.ret PNull.
Proof. reflexivity. Qed.

Lemma realloc_k_block : forall ft p tr q, q <> PNull -> realloc_k ft p tr q = YG00.bind (ft p tr) (fun _ => YG00.ret q).
Proof. intros ft p tr q H. destruct q; [exfalso; exact (H eq_refl) | reflexivity | reflexivity | reflexivity]. Qed.

(* The refusal witness: along granted traces, the entry step [ft PNull] returns in S1 from S, and [mt n] returns
   PNull in S' from S1.  A caller that has room refutes it with its malloc model's success lemma. *)
Definition mt_refused (mt : Z -> list Z -> M sptr) (ft : sptr -> list Z -> M unit)
(n : Z) (tr : list Z) (S S' : astate) : Prop :=
exists S1 trc1 trc2, apath (ft PNull tr S) trc1 (tt, S1) /\ gflag trc1 = true /\
apath (mt n tr S1) trc2 (PNull, S') /\ gflag trc2 = true.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
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
Variable rU : list Z -> astate -> Prop.
(* A bound on realloc's own frames down to its inner calls (the Allocate / Deallocate / copy calls): the inner
   calls' sp lies within RSTACK below realloc's entry sp.  Each instance computes it from its image (fuzz_state:
   0x8a0). *)
Variable RSTACK : Z.
Variable pcR : Z.
Variable pc0 : Z.
Variable inst : Z.
Variable oomb : Z.
Variable pcM : Z.

(* The machine state at realloc's entry: YG0d.acall_pre with [ARX inst] for AR (realloc's own premise [rpre] is
   a separate hypothesis of the statements). *)
Definition realloc_pre (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARX inst ly S W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ASTACK <= spZ regs /\ ly_bot ly + RSTACK < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch.

(* One stage of the run, from (ly, S, W, mem, md) to (ly', S', W', mem', md'): ARX at the end, the layout and
   the world only grow, the model's io parts are kept, memory changes only on owned addresses, realloc's stack
   window and errno ([ascratch B ASTACK regs]) and [E] (in the view and in the raw memory, as AllocG.alloc_post),
   and realloc's stack window stays present. *)
Definition rstage (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B ASTACK regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
~ ascratch B ASTACK regs (bv_unsigned x) -> ~ E (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W') mem' a).

(* realloc(p, n) on a live block p of size n_old, at realloc's return pc.  Every result is the end of a granted
   path of the realloc tree.  On PNull (the NULL-return arm): one stage with nothing but owned bytes, the stack
   window and errno changed, the refusal witness, the old block still live, errno = ENOMEM (12) and the
   out-of-memory byte set.  On a block q: a first stage up to Reallocate's call of Deallocate (Allocate's block is
   the only extra changed range; ly2 / S2 is the state after the inner malloc), the copy of min(n_old, n) bytes,
   a second stage through the free of the old block (its bytes are the extra changed range), and a0 = q's
   address under ly2. *)
Definition realloc_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
(exists trc, apath (realloc_tree_with mt ft p n tr S) trc r /\ gflag trc = true) /\
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ lpost (snd r) /\
(fst r = PNull ->
getr regs' 10 = w64 0 /\
rstage ly S W regs mem md (fun _ => False) ly' (snd r) W' mem' md' /\
mt_refused mt ft n tr S (snd r) /\ In (p, n_old) (blocks (snd r)) /\
val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
val_mem segs (mrestrict (w_H W') mem') oomb 1 1) /\
(fst r <> PNull ->
exists ly2 S2 W2 mem2 md2,
getr regs' 10 = w64 (sptr_addr B ly2 (fst r)) /\
rstage ly S W regs mem md (fun a => sptr_addr B ly2 (fst r) <= a < sptr_addr B ly2 (fst r) + req_size n)
ly2 S2 W2 mem2 md2 /\
(exists trc, apath (realloc_null_tree_with mt ft n tr S) trc (fst r, S2) /\ gflag trc = true) /\ lpost S2 /\
(forall i, 0 <= i < Z.min n_old n ->
aview segs (w_H W2) mem2 (sptr_addr B ly2 (fst r) + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
rstage ly2 S2 W2 regs mem2 md2 (fun a => sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old)
ly' (snd r) W' mem' md' /\
(exists trc, apath (ft p tr S2) trc (tt, snd r) /\ gflag trc = true)).

(* realloc(NULL, n), at realloc's return pc: one stage whose extra changed range is the new block, a0 = the
   result's address; on PNull the refusal witness, errno = ENOMEM and the out-of-memory byte. *)
Definition realloc_null_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
(exists trc, apath (realloc_null_tree_with mt ft n tr S) trc r /\ gflag trc = true) /\
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ lpost (snd r) /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
rstage ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' mem' md' /\
(fst r = PNull ->
mt_refused mt ft n tr S (snd r) /\
val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

(* Statement 1: realloc(p, n) for a live block p and 1 <= n < nmax. *)
Definition arealloc_realizes_all : Prop :=
forall ly S W regs mem md p n_old n ch,
realloc_pre ly S W regs mem md ch -> rpre S n ->
In (p, n_old) (blocks S) -> fpre ly S W mem p n_old ->
getr regs 10 = w64 (sptr_addr B ly p) -> getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= lmax ->
rU (call_trace ly pc0 regs ch) S ->
amreal segs (realloc_tree_with mt ft p n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pcR regs mem md)
(realloc_leaf ly S W regs mem md p n_old n (call_trace ly pc0 regs ch)).

(* Statement 2: realloc(NULL, n) for 1 <= n < nmax. *)
Definition arealloc_null_realizes : Prop :=
forall ly S W regs mem md n ch,
realloc_pre ly S W regs mem md ch -> rpre S n ->
getr regs 10 = w64 0 -> getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= lmax ->
rU (call_trace ly pc0 regs ch) S ->
amreal segs (realloc_null_tree_with mt ft n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pcR regs mem md)
(realloc_null_leaf ly S W regs mem md n (call_trace ly pc0 regs ch)).

(* Statement 3, the NULL-return arm of statement 1: the post when realloc(p, n) returns NULL. *)
Definition realloc_null_post (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z) (tr : list Z)
(S' : astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
rstage ly S W regs mem md (fun _ => False) ly' S' W' mem' md' /\
mt_refused mt ft n tr S S' /\ In (p, n_old) (blocks S') /\ lpost S' /\
val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
val_mem segs (mrestrict (w_H W') mem') oomb 1 1.

Lemma realloc_leaf_null : forall ly S W regs mem md p n_old n tr S' W' c',
realloc_leaf ly S W regs mem md p n_old n tr (PNull, S') W' c' ->
realloc_null_post ly S W regs mem md p n_old n tr S' W' c'.
Proof.
intros ly S W regs mem md p n_old n tr S' W' c' H. destruct H as [_ H].
destruct H as (ly' & regs' & mem' & md' & Ec & CS & LP & HN & _). cbn [fst snd] in LP, HN.
destruct (HN eq_refl) as (A0 & ST & MR & KB & ER & OM). exists ly', regs', mem', md'.
exact (conj Ec (conj CS (conj A0 (conj ST (conj MR (conj KB (conj LP (conj ER OM)))))))).
Qed.

(* The copy routine's contract (uninstrumented memcpy): from its entry [pcM] with a0 = dst, a1 = src, a2 = len,
   it returns to ra with the callee-saved registers kept, the model changed only in its materialized pages,
   [dst, dst + len) holding src's bytes and every other raw memory byte unchanged (also the hidden ones, so that
   a frame law over raw bytes applies); it reads no ASan state and uses no stack. *)
Definition rmemcpy_pre (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (d s n : Z) : Prop :=
YK0s.ret_ok (getr regs 1) /\
getr regs 10 = w64 d /\ getr regs 11 = w64 s /\ getr regs 12 = w64 n /\
0 <= n /\ 0 <= d /\ d + n <= 2 ^ 64 /\ 0 <= s /\ s + n <= 2 ^ 64 /\ (d + n <= s \/ s + n <= d) /\
(forall a, d <= a < d + n -> writable_at segs (mrestrict (w_H W) mem) a) /\
(forall a, s <= a < s + n -> aview segs (w_H W) mem a <> None).

Definition amemcpy_realizes : Prop :=
forall (W : world segs) regs mem md d s n,
rmemcpy_pre W regs mem d s n ->
SRr segs W (cfg_at segs pcM regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = aview segs (w_H W) mem (s + i)) /\
(forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End b.
End a.
