(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN00.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YM06 YM02 YP09 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0u YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN03 YN31 YN2b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : malloc_syms.
Let segs := ms_segs B.
Definition malloc_leaf_g (MR : MR_t) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n g : Z)
(r : option sptr * astate) (c' : config) : Prop :=
malloc_leaf B MR L A regs mem md n r c' /\ word_mem segs (ms_mem (cfg_ms c')) (ms_guard B) g.
Definition malloc_realizes_g (MR : MR_t) : Prop :=
forall L A regs mem md n g,
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
word_mem segs mem (ms_guard B) g ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md) (malloc n A) (malloc_leaf_g MR L A regs mem md n g).
Definition malloc_small_hyp_g : Prop :=
forall L A regs mem md n g,
call_pre B (MRx B) L A regs mem md ->
getr regs 10 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
word_mem segs mem (ms_guard B) g ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md) (malloc n A) (malloc_leaf_g (MRx B) L A regs mem md n g).
Definition alloc_slot_hyp_g : Prop :=
forall L A regs mem md sc n g,
Inv [] None U0 A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD -> n + IB <= class_size sc ->
midrep B L A mem md ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) ->
callee_pre B regs mem AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n ->
word_mem segs mem (ms_guard B) g ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (pc_alloc_slot (ms_pcs B))) mem (seg_rom segs)) md)
(alloc_slot NEST_FUEL sc n A)
(fun r c' => (exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
midrep B L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\ rsv_ok (snd r) /\ span_ok (snd r) /\ layout_le A L L' /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 ->
~ owned B L A x -> ~ owned B L' (snd r) x -> ~ in_nonmap_region L' (snd r) x ->
~ call_scratch B (spZ regs) AS_STACK x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, call_scratch B (spZ regs) AS_STACK a -> writable_at segs mem' a) /\
getr regs' 10 = Z_to_bv 64 (fst r) /\
(0 <= fst r -> forall gg am, active_hd (snd r) sc = Some gg -> MT (snd r) gg = Some (MUsed am) ->
stride_of am < class_size sc ->
forall i, 0 <= i < stride_of am - IB ->
mbyte segs mem' (ptr_addr L' (slot_start am (fst r)) + i) = Some (Z_to_bv 8 0)) /\
word_mem segs mem' (ms_guard B) g)).
Lemma malloc_leaf_of_g MR L A regs mem md n g r c' : malloc_leaf_g MR L A regs mem md n g r c' -> malloc_leaf B MR L A regs mem md n r c'.
Proof. intros [H _]. exact H. Qed.
End c.
End b.
