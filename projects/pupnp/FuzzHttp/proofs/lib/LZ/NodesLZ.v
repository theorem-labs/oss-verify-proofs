(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree RelSpec Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require AsanAcct BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Fixpoint pagesN (lo : Z) (k : nat) : list word :=
  match k with
  | O => []
  | S k' => Z_to_bv 64 lo :: pagesN (lo + page_size) k'
  end.

Definition pages_of (lo hi : Z) : list word := pagesN lo (Z.to_nat ((hi - lo) / page_size)).

Definition in_rangeb (lo hi : Z) (a : word) : bool := (lo <=? bv_unsigned a) && (bv_unsigned a <? hi).

Definition unhide_range (lo hi : Z) (H : word -> bool) : word -> bool :=
  fun a => H a && negb (in_rangeb lo hi a).

Definition hide_range (lo hi : Z) (H : word -> bool) : word -> bool :=
  fun a => H a || in_rangeb lo hi a.

Definition unhide_zb (lo hi : Z) (H : word -> bool) : word -> bool :=
  fun a => H a && negb (in_rangeb lo hi a && zb a).

Definition cut_pages (lo hi : Z) (P : list word) : list word := List.filter (page_outside_range lo hi) P.

Definition shw_lo (off a : Z) : Z := ((a / 8 + off) / page_size) * page_size.
Definition shw_hi (off a n : Z) : Z := (((a + n) / 8 + off + (page_size - 1)) / page_size) * page_size.

Definition lenZ (len : Z) : Z := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)).
Definition lenW (len : Z) : word := Z_to_bv 64 (lenZ len).
Definition addrZ (addr : Z) : Z := bv_unsigned (Z_to_bv 64 addr).

Definition MAPF_ANON_PRIVATE : Z := 34.
Definition MAPF_NR : Z := 16418.
Definition MAPF_FIXED : Z := 50.
Definition MAPF_FIXED_NR : Z := 16434.
Definition PROT_RW : Z := 3.

Definition ret_alignedb (rsp : resp) : bool := (bv_unsigned (eff_ret rsp) mod page_size =? 0).

Inductive nodeL : Type :=
| LNode (n : node)
| LMmapHeap (len off : Z)
| LMmapNR (len : Z)
| LMmapFixed (addr len flags : Z)
| LMmapCommit (addr len off : Z)
| LMadvise (addr len : Z).

Section AtNodeL.
Variable segs : list Segment.

Definition mmap_regs (ms : machine_state) (addr len flags : Z) : Prop :=
  ms_svc_pending ms = Some (Z_to_bv 64 222) /\
  areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
  areg ms 12 = Z_to_bv 64 PROT_RW /\ areg ms 13 = Z_to_bv 64 flags /\
  areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0 /\
  w_is0 (Z_to_bv 64 len) = false.

Definition madv_regs (ms : machine_state) (addr len : Z) : Prop :=
  ms_svc_pending ms = Some (Z_to_bv 64 233) /\
  areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 MADV_DONTNEED /\
  w_is0 (Z_to_bv 64 len) = false.

Definition at_nodeL (n : nodeL) (ms : machine_state) : Prop :=
  match n with
  | LNode n => at_node segs n ms
  | LMmapHeap len off => mmap_regs ms 0 len MAPF_ANON_PRIVATE /\ 0 <= off < 2^47
  | LMmapNR len => mmap_regs ms 0 len MAPF_NR
  | LMmapFixed addr len flags =>
      mmap_regs ms addr len flags /\ (flags = MAPF_FIXED \/ flags = MAPF_FIXED_NR) /\
      (addr mod page_size = 0) /\ 0 < addr /\ addr + lenZ len <= 2^47
  | LMmapCommit addr len off =>
      mmap_regs ms addr len MAPF_FIXED /\
      (addr mod page_size = 0) /\ 0 < addr /\ addr + lenZ len <= 2^47 /\ 0 <= off < 2^47
  | LMadvise addr len =>
      madv_regs ms addr len /\ (addr mod page_size = 0) /\ 0 < addr /\ addr + lenZ len <= 2^47 /\

      (forall a : word, addr <= bv_unsigned a < addr + lenZ len -> find_segment segs (bv_unsigned a) 1 = None)
  end.
End AtNodeL.

Definition grant_maps (h : VmMaps) (a n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition lmheap_post (mo : Model) (a : word) (len off : Z) : Model :=
  with_vm_backing (m_vm_lazy mo)
    (pages_of (shw_lo off (bv_unsigned a)) (shw_hi off (bv_unsigned a) (lenZ len)) ++ m_vm_materialized mo)
    (with_vmmaps (grant_maps (m_vmmaps mo) a (lenW len)) mo).

Definition lmnr_post (mo : Model) (a : word) (len : Z) : Model :=
  with_vm_backing (lazy_interior a (lenW len) ++ m_vm_lazy mo)
    (pages_of (bv_unsigned a) (bv_unsigned a + lenZ len) ++ m_vm_materialized mo)
    (with_vmmaps (grant_maps (m_vmmaps mo) a (lenW len)) mo).

Definition lmfixed_next (h : VmMaps) (A n : word) : VmMaps :=
  if map_contains (vm_maps h) A n then mmap_fixed_rw_next h A n else mmap_fixed_rw_span_next h A n.

Definition lmfixed_post (mo : Model) (addr len flags : Z) : Model :=
  let A := Z_to_bv 64 addr in let n := lenW len in let FL := Z_to_bv 64 flags in
  let sp := with_mmap_replacement FL A n (with_vmmaps (lmfixed_next (m_vmmaps mo) A n) mo) in
  with_vm_backing (m_vm_lazy sp)
    ((if mmap_noreserve_b FL then pages_of (addrZ addr) (addrZ addr + lenZ len) else []) ++ m_vm_materialized sp) sp.

Definition lmcommit_post (mo : Model) (addr len off : Z) : Model :=
  let A := Z_to_bv 64 addr in let n := lenW len in
  let sp := with_mmap_replacement (Z_to_bv 64 MAPF_FIXED) A n (with_vmmaps (lmfixed_next (m_vmmaps mo) A n) mo) in
  with_vm_backing (m_vm_lazy sp)
    (pages_of (shw_lo off (addrZ addr)) (shw_hi off (addrZ addr) (lenZ len)) ++ m_vm_materialized sp) sp.

Definition gap_refused (mo : Model) (len : Z) (eff : resp) (mo' : Model) : Prop :=
  exists e, In e (mmap_errnos_when (negb (vm_gap_available (m_vmmaps mo) (lenZ len))))
            /\ strip eff = efferr e /\ mo' = mo.

Definition nstepL (n : nodeL) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | LNode n => nstep n mo eff mo' evs
  | LMmapHeap len off =>
      evs = [] /\
      (gap_refused mo len eff mo'
       \/ exists a, mmap_placed mo 0 len MAPF_ANON_PRIVATE a /\
            strip eff = mkEffect a [] [(a, lenW len)] /\ mo' = lmheap_post mo a len off)
  | LMmapNR len =>
      evs = [] /\
      (gap_refused mo len eff mo'
       \/ exists a, mmap_placed mo 0 len MAPF_NR a /\
            strip eff = mkEffect a [] [(a, lenW len)] /\ mo' = lmnr_post mo a len)
  | LMmapFixed addr len flags =>
      evs = [] /\ strip eff = mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, lenW len)] /\
      mo' = lmfixed_post mo addr len flags
  | LMmapCommit addr len off =>
      evs = [] /\ strip eff = mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, lenW len)] /\
      mo' = lmcommit_post mo addr len off
  | LMadvise addr len =>

      evs = [] /\ strip eff = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, lenW len)] /\
      mo' = with_vm_backing (m_vm_lazy mo) (cut_pages (addrZ addr) (addrZ addr + lenZ len) (m_vm_materialized mo)) mo
  end.

Definition nexitL (n : nodeL) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | LNode n => nexit n mo code mo'
  | _ => False
  end.

Definition lazy_in_maps (mo : Model) : Prop :=
  forall r x, In r (m_vm_lazy mo) ->
    bv_unsigned (fst r) <= x < bv_unsigned (fst r) + bv_unsigned (snd r) ->
    BackingAlgebra.covered (vm_maps (m_vmmaps mo)) x = true.

Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Definition strip_vm (mo : Model) : Model := with_vm_backing [] [] mo.

Definition minvL (mo : Model) : Prop :=
  minv (strip_vm mo) /\ lazy_in_maps mo /\ BackingAlgebra.model_ivs_wf mo /\ seps (vm_maps (m_vmmaps mo)).

Definition lz_room (mo : Model) (nZ extra : Z) : Prop :=
  vm_backing_used mo + nZ + extra <= vm_limit (m_vmmaps mo).

Definition nsafeL (n : nodeL) (mo : Model) : Prop :=
  match n with
  | LNode n =>
      nsafe n mo /\
      match n with
      | NMmap addr len prot flags =>
          mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
          mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo (lenZ len) = true
      | NBrk _ | NMprotect _ _ _ | NMremap _ _ _ => False
      | NOpenW _ | NIoctlF _ | NWritevF _ _ | NLseek _ _ _ | NReadv _ _ _ _ _ | NUnlink _ => False
      | _ => True
      end
  | LMmapHeap len off => lz_room mo (lenZ len) (lenZ len / 8 + 2 * page_size)
  | LMmapNR len => lz_room mo (lenZ len) 0
  | LMmapFixed addr len flags =>
      let h := m_vmmaps mo in let A := Z_to_bv 64 addr in let n := lenW len in
      addr + lenZ len <= alloc_top h /\
      region_free (vm_reserved h) A n = true /\ map_contains (vm_maps h) A n = true /\
      vm_backing_within_limit (lmfixed_post mo addr len flags) = true
  | LMmapCommit addr len off =>
      let h := m_vmmaps mo in let A := Z_to_bv 64 addr in let n := lenW len in
      addr + lenZ len <= alloc_top h /\
      region_free (vm_reserved h) A n = true /\ map_contains (vm_maps h) A n = true /\
      vm_backing_within_limit (lmcommit_post mo addr len off) = true
  | LMadvise addr len =>
      madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (lenW len) = true
  end.

Definition hideL (n : nodeL) (rsp : resp) (H : word -> bool) : word -> bool :=
  match n with
  | LNode (NMmap addr len prot flags) =>
      if ret_alignedb rsp then let a := bv_unsigned (eff_ret rsp) in unhide_range a (a + lenZ len) H else H
  | LNode (NMunmap addr len) => unhide_range (addrZ addr) (addrZ addr + lenZ len) H
  | LNode _ => H
  | LMmapHeap len off =>
      if ret_alignedb rsp then
        let a := bv_unsigned (eff_ret rsp) in
        unhide_zb (shw_lo off a) (shw_hi off a (lenZ len)) (unhide_range a (a + lenZ len) H)
      else H
  | LMmapNR len =>
      if ret_alignedb rsp then let a := bv_unsigned (eff_ret rsp) in unhide_range a (a + lenZ len) H else H
  | LMmapFixed addr len flags => unhide_range (addrZ addr) (addrZ addr + lenZ len) H
  | LMmapCommit addr len off =>
      unhide_zb (shw_lo off (addrZ addr)) (shw_hi off (addrZ addr) (lenZ len))
                (unhide_range (addrZ addr) (addrZ addr + lenZ len) H)
  | LMadvise addr len => hide_range (addrZ addr) (addrZ addr + lenZ len) H
  end.

Definition allowL (n : nodeL) (rsp : resp) (P : list word) : list word :=
  match n with
  | LNode (NMmap addr len prot flags) =>
      if mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
      then cut_pages (addrZ addr) (addrZ addr + lenZ len) P else P
  | LNode (NMunmap addr len) => cut_pages (addrZ addr) (addrZ addr + lenZ len) P
  | LNode _ => P
  | LMmapHeap len off =>
      if ret_alignedb rsp then
        let a := bv_unsigned (eff_ret rsp) in pages_of (shw_lo off a) (shw_hi off a (lenZ len)) ++ P
      else P
  | LMmapNR len =>
      if ret_alignedb rsp then let a := bv_unsigned (eff_ret rsp) in pages_of a (a + lenZ len) ++ P else P
  | LMmapFixed addr len flags =>
      (if mmap_noreserve_b (Z_to_bv 64 flags) then pages_of (addrZ addr) (addrZ addr + lenZ len) else [])
      ++ cut_pages (addrZ addr) (addrZ addr + lenZ len) P
  | LMmapCommit addr len off =>
      pages_of (shw_lo off (addrZ addr)) (shw_hi off (addrZ addr) (lenZ len))
      ++ cut_pages (addrZ addr) (addrZ addr + lenZ len) P
  | LMadvise addr len => cut_pages (addrZ addr) (addrZ addr + lenZ len) P
  end.
