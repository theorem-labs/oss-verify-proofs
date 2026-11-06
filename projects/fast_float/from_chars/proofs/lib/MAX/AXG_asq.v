(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 AXG_as1 AXG_as5 AXG_ag1 AXG_am8.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition KAS (sc : Z) : Z := 72 * Z.of_nat (need sc) + 1440.

(* [comment removed for export] *)
Definition UGROW (s0 s' : astate) (sc : Z) : Prop :=
  (forall c, 0 <= c < sc -> usage_of s' c = usage_of s0 c) /\
  (forall c, 0 <= c < 48 -> usage_of s0 c <= usage_of s' c <= usage_of s0 c + 32).

(* [comment removed for export] *)
Definition as_qpost (UB0 : Z -> Prop) (HTOP : Z) (X : list sptr) (U : Z -> Z) (L0 : layout) (s0 : astate) (m0 : word -> option byte)
    (regs0 : bvmap 5 word) (sp0 K sc req : Z) : @wpost (Z * astate) :=
  fun L' r R' pc m' => exists idx s' g am, r = (idx, s') /\ pc = wa 0x52b8c /\ getr R' 10 = wa idx /\
    (forall k, In k callee_as -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP X (Some (g, idx)) U L' s' m' sp0 K /\ GROWX UB0 sp0 K L0 s0 m0 L' s' m' /\
    markers_hold L' s' (bview SEGS m') /\
    active_hd s' sc = Some g /\ usedX X s' g am /\ am_sc am = sc /\ req + IB <= stride_of am /\ 0 <= idx <= am_last am /\
    heads_below s0 s' sc /\ ub_same s0 s' /\ UGROW s0 s' sc.

(* [comment removed for export] *)
Definition as_wk_stmt {fx : FPState} : Prop :=
  forall FORB, (forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x87000)) ->
  forall fuel UB0 HTOP X U L s m (regs : bvmap 5 word) rom sp0 K sc req,
  CUT HTOP X None U L s m sp0 K -> markers_hold L s (bview SEGS m) -> KAS sc <= K ->
  0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= fuel)%nat ->
  getr regs 2 = wa sp0 -> getr regs 10 = wa sc -> getr regs 11 = wa req ->
  (forall c, 0 <= c < 48 -> usage_of s c < 2^40) ->
  DBT m -> TABS m -> rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  (st_init_done s = true \/ AMI L m sp0) ->
  (forall x, UB0 x -> in_user_block L s x) ->
  wk SEGS FORB HTOP rom L regs (wa 0x522f0) m (alloc_slot fuel sc req s) (as_qpost UB0 HTOP X U L s m regs sp0 K sc req).
