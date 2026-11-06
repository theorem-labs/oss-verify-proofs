(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMcdGI.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 373cdb6eb68f) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 13 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk): the INTERFACE between the
   two halves of CacheDealloc's (0x34234) GROWTH arm (cache full, the free array has no room: rg_mapped_fa < 4 * (old + N)).
   - W1 (a Theorem Labs lane): CacheDealloc's entry -> EnsureFreeArraySpace's entry 0x34a94 (ra = 0x348d0), ending in [at_EFA]: the
     machine satisfies the closed symbolic state DMcdK.K9 under an environment that agrees with the seed's (DMcdGk.E0) on
     the seed atoms, and memory moved only in DMcdGk.WINX; then FGtN.tfib_efa_spec_lk.
   - W2 (a Theorem Labs lane, a Theorem Labs lane 02:34Z): from EnsureFreeArraySpace's GROWTH leaf (FGtN.efa_leafT_lk, second disjunct) back at
     0x348d0, to CacheDealloc's return: [w2_t].  Port of the released YFgz.segK2's tail (0x348d0 -> 0x348e8 -> copy ->
     0x34c14 -> YFgo.segO / 0x34920 -> 0x342a8 -> ret), re-fitted to the grown free array.
   The leaf [at_RETKG] is DMcdGk.at_RETK for the full cache, but in the world / model / memory the call left: the frame is
   relative to the memory at 0x348d0, and RG+24 holds the grown mapped size.
   rule 24: proves function SizeClassAllocator64LocalCache::Deallocate (interface of its growth-arm walk); reuse: the
   released YFgz.segK2 walks the same machine path on the no-growth arm; `proof-index ReturnToAllocator
   EnsureFreeArraySpace 0x348d0 0x3476c` 2026-10-30T01:1xZ exit 4 found no released walk of the growth arm. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMcdGk DMcdK FGsN FGtN.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z) (X : astate).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let m0 := mrestrict (w_H W) mem0.
Let PCv : Z := DMcdGk.PCv ly c.
Let RGv : Z := DMcdGk.RGv ly c.
Let SLOTv : Z := DMcdGk.SLOTv ly c cnt.
Let DSTv : Z := DMcdGk.DSTv ly c old.
Let SRCv : Z := DMcdGk.SRCv ly c cnt.
Let Nv : Z := max_cached c / 2.

(* W1's leaf: the state at EnsureFreeArraySpace's entry. *)
Definition at_EFA (c9 : config) : Prop :=
  exists ms9 mat9 (E : env),
    c9 = mkCfg ms9 (with_vm_backing (m_vm_lazy md0) mat9 md0) /\
    (forall k, (k < aHAVf)%nat -> ew E k = ew (DMcdGk.E0 ly regs0 c off cnt old mf j80 j88 jst) k) /\
    st_ok tfibsegs E DMcdK.K9 (restrict (w_H W) ms9) /\
    DMcdGk.MEQX ly regs0 mem0 c cnt (ms_mem ms9).

(* W1's machine facts at EnsureFreeArraySpace's entry (beside [at_EFA]): the registers the call reads and the values of
   the cells FGtN.efa_pre_lk asks, with the presence of the windows W1 wrote.  Everything else at the call is the entry's
   memory outside DMcdGk.WINX ([at_EFA]'s frame). *)
Definition efa_mach (c9 : config) : Prop :=
  exists regs9 mem9 mat9,
    c9 = mkCfg (mkst regs9 (w64 FGsN.A_EFA) mem9 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat9 md0) /\
    getr regs9 1 = w64 FGsN.A_RTA_EFA /\ getr regs9 2 = Z_to_bv 64 (sp0 - 240) /\ getr regs9 4 = w64 TFIB_TP /\
    getr regs9 10 = w64 A_ALLOCATOR /\ getr regs9 11 = w64 RGv /\ getr regs9 12 = w64 (DMcdGk.RBv ly c) /\
    getr regs9 13 = w64 (old + Nv) /\
    (forall a, (sp0 - 320 <= a < sp0) \/ (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88) \/
               (PCv <= a < PCv + 4) \/ (T + 2784 <= a < T + 2792) -> apresent (w_H W) mem9 a) /\
    let m := mrestrict (w_H W) mem9 in
    val_mem tfibsegs m RGv 8 (2 ^ 60) /\ val_mem tfibsegs m (RGv + 16) 8 old /\ val_mem tfibsegs m (RGv + 24) 8 mf /\
    val_mem tfibsegs m (RGv + 80) 8 j80 /\ val_mem tfibsegs m (RGv + 88) 8 j88 /\
    val_mem tfibsegs m PCv 4 Nv /\ val_mem tfibsegs m (PCv + 8) 8 (class_size c) /\ val_mem tfibsegs m (T + 2784) 8 jst.

(* The full-cache write window (DMcdGk.WIN with cnt = MAX). *)
Definition WING (a : Z) : Prop :=
  (sp0 - 320 <= a < sp0) \/ (PCv <= a < PCv + 4) \/ (SLOTv <= a < SLOTv + 4) \/ (T + t_cache + 2576 <= a < T + t_cache + 2584) \/
  (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88) \/ (DSTv <= a < DSTv + 4 * Nv).

(* W2's leaf: CacheDealloc's return, in the world / model the call left, memory relative to the memory at 0x348d0. *)
Definition at_RETKG (W3 : world tfibsegs) (md3 : Model) (mem3 : word -> option byte) (mf2 : Z)
    (W' : world tfibsegs) (cfg' : config) : Prop :=
  W' = W3 /\ exists regs' mem' mat,
    cfg' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md3) mat md3) /\
    getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r DMcdGk.SREGS -> getr regs' r = getr regs0 r) /\
    (forall x : word, ~ WING (bv_unsigned x) -> mem' x = mem3 x) /\
    (forall a, WING a -> apresent (w_H W3) mem' a) /\
    let m := mrestrict (w_H W3) mem' in
    val_mem tfibsegs m PCv 4 (DMcdGk.CNTPv c cnt + 1) /\ val_mem tfibsegs m SLOTv 4 (DMcdGk.RELv c off / 16) /\
    val_mem tfibsegs m RGv 8 0 /\ val_mem tfibsegs m (RGv + 16) 8 (old + Nv) /\ val_mem tfibsegs m (RGv + 24) 8 mf2 /\
    (forall i v, 0 <= i < Nv -> val_mem tfibsegs m0 (SRCv + 4 * i) 4 v -> val_mem tfibsegs m (DSTv + 4 * i) 4 v).

(* W2's statement.  X is the model state at the call (EnsureFreeArraySpace's S); regs9 / mem9 / md9 the machine at its
   entry (W1's leaf); the leaf is the growth disjunct of FGtN.efa_leafT_lk (the first disjunct is refuted by [GROW]). *)
Definition w2_t : Prop :=
  DMcdGk.free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst ->
  cnt = max_cached c -> rg_mapped_fa (reg X c) = mf -> mf < 4 * (old + Nv) ->
  (Z.to_nat c < length (st_regions X))%nat ->
  forall c9, at_EFA c9 ->
  forall regs9 mem9 md9, c9 = cfg_at tfibsegs FGsN.A_EFA regs9 mem9 md9 ->
  forall r W' c', FGtN.efa_leafT_lk ly X W regs9 mem9 md9 c (old + Nv) j80 j88 jst old (rg_alloc_user (reg X c)) (rg_mapped_user (reg X c)) r W' c' ->
  SRr tfibsegs W' c' (at_RETKG W' (cfg_model c') (ms_mem (cfg_ms c')) (rg_mapped_fa (reg (snd r) c))).
End g.
End d.
