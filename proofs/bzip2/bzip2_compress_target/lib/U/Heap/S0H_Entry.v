(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatSim ShapeAlg MmapSim RefNodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc EvtBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad MSafe Prog KInv KStep KStepC MI_Inv MI_Kit MI_Arith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Contracts MTight.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MSafe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MTight.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep MallocTree MallocBlocks MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocTight AllocCover TreeBridge TightBridge. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import S0H_Iface S0H_Tight S0H_Cover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0World.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre U.S0TRDefs.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs.
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)

Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Arith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0H_Tpl.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MSafe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MTight.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocBlocks OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_ifaceP.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.AllocLayout0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocTight OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.TreeBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.TightBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Tight OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith.TplPack.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.

Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition o_none : MallocTree.mem := fun _ => None.
Definition PH_B : Z := 0x30000000.
Definition PH_A : Z := 0x7e0000000000.
Definition PH_G : Z := 0x7f0000000000.

(* [comment removed for export] *)
Definition AC_TPL : ACeil := mkACeil 0x7fffff80000.
Definition run65536 (ans : list Z) : mstate :=
  match follow (mrun o_none (@malloc AC_TPL (minit 0 ref_reserved) 65536)) ans with
  | Some (_, (st, _)) => st
  | None => minit 0 []
  end.
(* [comment removed for export] *)
Definition st0c_brk : mstate := ltac:(packed_state (run65536 [PH_B; PH_B + 8192; PH_B; PH_G])).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition st0c_mm : mstate := ltac:(packed_state (run65536 [PH_B; PH_B; PH_A; 0; PH_G])).   (* [comment removed for export] *)

Definition regs0 (brkworld : bool) (abase gbase : Z) : gmap N region :=
  <[1%N := mkRegion RKGroup gbase 69632]> (<[0%N := mkRegion (if brkworld then RKBrk else RKMeta) abase 8192]> ∅).

(* [comment removed for export] *)
Definition hav_extra : list (Z * list (Z * N)) :=
  (1, [(12, 1%N)]) :: (4351, [(7, 1%N)]) :: map (fun i => (4098 + Z.of_nat i, [(16, 1%N)])) (seq 0 253).
Definition SHX : shadow := ltac:(packed_shadow
  (let sh := default shadow0 (s_shadow st0c_brk !! 1%N) in
   mkShadow (r_cells sh) (fold_right (fun e acc => <[fst e := snd e]> acc) (r_hav sh) hav_extra) (r_havp sh))).

(* [comment removed for export] *)
Definition with_secret (sec : Z) (st : mstate) : mstate :=
  mkState (set_secret sec (s_ctx st)) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st)
          {[(0%N, 4096) := mkArea sec None 101]} (s_groups st) (s_slots st) (s_tick st) sec (s_reserved st).

(* [comment removed for export] *)
Definition st0 (brkworld : bool) (area gm : Z) : mstate :=
  with_secret run_secret
    (set_shadow {[1%N := SHX]} (set_regions (regs0 brkworld (area - 4096) gm) (if brkworld then st0c_brk else st0c_mm))).

Definition L0 (brkworld : bool) (area gm : Z) : mled :=
  mkLed ref_reserved [(gm, 69632)]
        (if brkworld then [] else [(area - 4096, 8192, 1)])
        (if brkworld then Some (area - 4096, 8192) else None)
        (if brkworld then BPLive else BPDead)
        [(1%N, 16)].

Definition slot0 : aptr := (0%N, 4120).
Definition BL0 : list blk := [(((1%N, 16) : cptr), 1, 65536)].
Definition LS0 (h : lhead) : list aptr := match h with LActive sc => if sc =? 44 then [slot0] else [] | LFree => [] end.
Definition pb0 : bid := ((1%N, 16), 1).
Definition LB0 (gm : Z) : list ablock := [(pb0, gm + 32, 65536)].
Definition W0 (gm : Z) : TBW := mkTBW slot0 1%N 44 17 gm 69632.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TPL.
Variables (b : bool) (area gm : Z).
Let st := st0 b area gm.

Lemma st0_ctx_eq : s_ctx st = set_secret run_secret (s_ctx (if b then st0c_brk else st0c_mm)). Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_metas_eq : s_metas st = s_metas st0c_brk. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_groups_eq : s_groups st = s_groups st0c_brk. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_slots_eq : s_slots st = s_slots st0c_brk. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_shadow_eq : s_shadow st = {[1%N := SHX]}. Proof. reflexivity. Qed.
Lemma st0_regions : s_regions st = regs0 b (area - 4096) gm. Proof. reflexivity. Qed.
Lemma st0_next_rid : s_next_rid st = 2%N. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_tick : s_tick st = 1%N. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_secret : s_secret st = run_secret. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_reserved : s_reserved st = ref_reserved. Proof. unfold st, st0. destruct b; reflexivity. Qed.

Lemma st0_init : c_init_done (s_ctx st) = 1. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_secret_c : c_secret (s_ctx st) = run_secret. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_mc : c_mmap_counter (s_ctx st) = 1. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_fh : c_free_meta_head (s_ctx st) = None. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_am : c_avail_meta (s_ctx st) = Some (0%N, 4160). Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_amc : c_avail_meta_count (s_ctx st) = 100. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_amac : c_avail_meta_area_count (s_ctx st) = 0. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_mas : c_meta_alloc_shift (s_ctx st) = if b then 0 else 1. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_mah : c_meta_area_head (s_ctx st) = Some (0%N, 4096). Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_mat : c_meta_area_tail (s_ctx st) = Some (0%N, 4096). Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_amas : c_avail_meta_areas (s_ctx st) = Some (0%N, 8192). Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_useq : c_unmap_seq (s_ctx st) = ∅. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_bnc : c_bounces (s_ctx st) = ∅. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_seq : c_seq (s_ctx st) = 1. Proof. unfold st, st0. destruct b; reflexivity. Qed.
Lemma st0_brk : c_brk (s_ctx st) = if b then BrkLive 0 8192 else BrkDead. Proof. unfold st, st0. destruct b; reflexivity. Qed.

Lemma st0_active : forall sc, active st sc = if sc =? 44 then Some slot0 else None.
Proof.
  intros sc. unfold active, ctx. rewrite st0_ctx_eq. cbn [c_active set_secret].
  destruct (Z.eqb_spec sc 44) as [->|NE]; [destruct b; vm_compute; reflexivity|].
  assert (E : c_active (s_ctx (if b then st0c_brk else st0c_mm)) = {[44 := slot0]}) by (destruct b; vm_compute; reflexivity).
  rewrite E. rewrite lookup_insert_ne by congruence. apply lookup_empty.
Qed.
Lemma st0_usage : forall sc, usage st sc = if sc =? 44 then 1 else 0.
Proof.
  intros sc. unfold usage, ctx. rewrite st0_ctx_eq. cbn [c_usage set_secret].
  destruct (Z.eqb_spec sc 44) as [->|NE]; [destruct b; vm_compute; reflexivity|].
  assert (E : c_usage (s_ctx (if b then st0c_brk else st0c_mm)) = {[44 := 1]}) by (destruct b; vm_compute; reflexivity).
  rewrite E. rewrite lookup_insert_ne by congruence. rewrite lookup_empty. reflexivity.
Qed.

Definition meta_slot0 : meta := mkMeta (Some slot0) (Some slot0) (Some (1%N, 0)) 0 0 0 1 44 17.
Lemma st0_metas : s_metas st = {[slot0 := meta_slot0]}.
Proof. rewrite st0_metas_eq. vm_compute. reflexivity. Qed.
Lemma st0_MR : forall x, MR st x = if aptr_eqb x slot0 then meta_slot0 else meta0.
Proof.
  intros x. unfold MR, get_meta_rec. rewrite st0_metas. destruct (aptr_eqb_spec x slot0) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. reflexivity.
Qed.
Lemma st0_groups : s_groups st = {[(1%N, 0) := mkGhdr (Some slot0) 0]}.
Proof. rewrite st0_groups_eq. vm_compute. reflexivity. Qed.
Lemma st0_slots : s_slots st = {[(1%N, 16) := (slot0, 0)]}.
Proof. rewrite st0_slots_eq. vm_compute. reflexivity. Qed.
Lemma st0_areas : s_areas st = {[(0%N, 4096) := mkArea run_secret None 101]}.
Proof. unfold st, st0. destruct b; reflexivity. Qed.

Lemma st0_in_pool : forall x, in_pool st x <-> exists i, 0 <= i /\ x = (0%N, 4160 + 40 * i).
Proof.
  intros x. unfold in_pool. rewrite st0_fh, st0_am. split.
  - intros [H|(am & i & H & Hi & ->)]; [discriminate|]. injection H as <-. exists i. split; [exact Hi|]. unfold aadd, META_SIZE. cbn. f_equal; lia.
  - cps_intros (i & Hi & ->). right. exists (0%N, 4160), i. split; [reflexivity|]. split; [exact Hi|]. unfold aadd, META_SIZE. cbn. f_equal; lia.
Qed.

Lemma st0_TT : TT 100 st.
Proof.
  constructor.
  - rewrite st0_init. lia.
  - intros sc. rewrite st0_active. destruct (sc =? 44); [right| left; reflexivity].
    exists slot0. split; [reflexivity|]. split; [unfold full1; rewrite st0_MR, aptr_eqb_refl; cbn; auto|].
    rewrite st0_in_pool. cps_intros (i & Hi & E). unfold slot0 in E. injection E. lia.
  - apply st0_bnc.
  - apply st0_useq.
  - intros m Hm. rewrite st0_fh in Hm. discriminate.
  - rewrite st0_am. discriminate.
  - rewrite st0_amc. lia.
Qed.

Lemma st0_INJ : INJ st.
Proof. intros a c g. rewrite !st0_active. destruct (Z.eqb_spec a 44); destruct (Z.eqb_spec c 44); intros; try discriminate; lia. Qed.

End TPL.

End ACeilS1.
End S0H_Tpl.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Entry.S0H_Tpl.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)

Lemma lookup_In {K A} `{Countable K} `{EqDecision K} (m : gmap K A) k v : m !! k = Some v -> In (k, v) (map_to_list m).
Proof. intros Hl. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record geo (b : bool) (area gm : Z) : Prop := mkGeo {
  ge_area_al : area mod 4096 = 0;
  ge_gm_al : gm mod 4096 = 0;
  ge_area_rng : 0x2000 <= area /\ area + 4096 <= alloc_ceiling;
  ge_area_img : area + 4096 <= 0x10000 \/ 0x67000 <= area;
  ge_gm_rng : 0x66000 <= gm /\ gm + 69632 <= alloc_ceiling;
  ge_disj : area + 4096 <= gm \/ gm + 69632 <= area
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INV0.
Variables (b : bool) (area gm : Z).
Hypothesis GE : geo b area gm.
Local Notation st := (st0 b area gm) (only parsing).
Local Notation L := (L0 b area gm) (only parsing).

(* [comment removed for export] *)
Local Notation SH0 := SHX (only parsing).

Lemma get_shadow_st0 : forall rid, get_shadow st rid = if (rid =? 1)%N then SHX else shadow0.
Proof.
  intros rid. unfold get_shadow. rewrite st0_shadow_eq.
  destruct (N.eqb_spec rid 1) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
  rewrite lookup_insert_ne by congruence. rewrite lookup_empty. reflexivity.
Qed.

Definition known_b (sh : shadow) (o v : Z) : bool := match cell_read sh o with Known v' => v' =? v | _ => false end.
Definition unknown_b (sh : shadow) (o : Z) : bool := match cell_read sh o with Unknown _ => true | _ => false end.
Lemma known_b_true sh o v : known_b sh o v = true -> cell_read sh o = Known v.
Proof. unfold known_b. destruct (cell_read sh o); [|discriminate]. intros H. apply Z.eqb_eq in H. congruence. Qed.
Lemma unknown_b_true sh o : unknown_b sh o = true -> exists h, cell_read sh o = Unknown h.
Proof. unfold unknown_b. destruct (cell_read sh o); [discriminate|]. intros _. eexists. reflexivity. Qed.

(* [comment removed for export] *)
Lemma SH0_cells_keys : forall o vt, r_cells SH0 !! o = Some vt ->
  In o [31; 69623; 15; 69627; 29; 13; 69625; 30; 14; 69626; 28; 69624; 65568].
Proof.
  intros o vt H. apply lookup_In in H. apply (in_map fst) in H.
  assert (K : map fst (map_to_list (r_cells SH0)) = [31; 69623; 15; 69627; 29; 13; 69625; 30; 14; 69626; 28; 69624; 65568]) by (vm_compute; reflexivity).
  rewrite K in H. exact H.
Qed.
Lemma SH0_hav_units : forallb (fun u => bool_decide (r_hav SH0 !! u = Some [(16, 1%N)])) (zrange 2 254 ++ [4096; 4097] ++ zrange 4098 253) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SH0_havp_pages : forallb (fun pg => bool_decide (r_havp SH0 !! pg = Some 1%N)) (zrange 1 15) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SH0_user : forall a, 32 <= a < 65568 -> exists h, cell_read SH0 a = Unknown h.
Proof.
  intros a Ha.
  assert (NC : r_cells SH0 !! a = None).
  { destruct (r_cells SH0 !! a) eqn:E; [|reflexivity]. exfalso. apply SH0_cells_keys in E. cbn in E. lia. }
  unfold cell_read. rewrite NC.
  destruct (Z_lt_le_dec a 4096) as [P0|P1]; [| destruct (Z_lt_le_dec a 65536) as [PM|P16]].
  - (* [comment removed for export] *)
    assert (HU : r_hav SH0 !! (a / 16) = Some [(16, 1%N)]).
    { pose proof SH0_hav_units as K. rewrite forallb_forall in K.
      specialize (K (a / 16) ltac:(apply in_or_app; left; apply in_zrange; [lia|]; split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia])).
      apply bool_decide_eq_true in K. exact K. }
    rewrite HU.
    match goal with |- exists h, (if ?c then _ else _) = _ => replace c with true end; [eexists; reflexivity|].
    symmetry. apply orb_true_intro. right.
    cbn -[Z.ltb Z.modulo]. replace (a mod 16 <? 16) with true by (symmetry; apply Z.ltb_lt; apply Z.mod_pos_bound; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (HP : r_havp SH0 !! (a / 4096) = Some 1%N).
    { pose proof SH0_havp_pages as K. rewrite forallb_forall in K.
      specialize (K (a / 4096) ltac:(apply in_zrange; [lia|]; split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia])).
      apply bool_decide_eq_true in K. exact K. }
    rewrite HP. cbn [stale_pg orb]. eexists. reflexivity.
  - (* [comment removed for export] *)
    assert (HU : r_hav SH0 !! (a / 16) = Some [(16, 1%N)]).
    { pose proof SH0_hav_units as K. rewrite forallb_forall in K.
      assert (a / 16 = 4096 \/ a / 16 = 4097) as [E|E] by (pose proof (Z.div_mod a 16 ltac:(lia)); pose proof (Z.mod_pos_bound a 16 ltac:(lia)); lia).
      all: specialize (K (a / 16) ltac:(apply in_or_app; right; apply in_or_app; left; rewrite E; cbn; auto)); apply bool_decide_eq_true in K; exact K. }
    rewrite HU.
    match goal with |- exists h, (if ?c then _ else _) = _ => replace c with true end; [eexists; reflexivity|].
    symmetry. apply orb_true_intro. right.
    cbn -[Z.ltb Z.modulo]. replace (a mod 16 <? 16) with true by (symmetry; apply Z.ltb_lt; apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma SH0_hdr : forallb (fun a => unknown_b SH0 a) (zrange 0 12) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SH0_known : forallb (fun ov => known_b SH0 (fst ov) (snd ov))
  [(12, 0); (69628, 0); (28, 0); (29, 160); (30, 1); (31, 0); (69623, 0); (69624, 220); (69625, 15); (69626, 0); (69627, 0); (65568, 0); (13, 224); (14, 1); (15, 0)] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SH0_cells : forall o v t, r_cells SH0 !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= 1)%N.
Proof.
  intros o v t H. apply lookup_In in H.
  assert (K : forallb (fun e => (0 <=? fst (snd e)) && (fst (snd e) <? 256) && (snd (snd e) <=? 1)%N) (map_to_list (r_cells SH0)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. specialize (K _ H). cbn [fst snd] in K.
  apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2. apply N.leb_le in K3. lia.
Qed.
Lemma SH0_hav : forall u hl ch, r_hav SH0 !! u = Some hl -> In ch hl -> (snd ch <= 1)%N.
Proof.
  intros u hl ch H Hin. apply lookup_In in H.
  assert (K : forallb (fun e => forallb (fun c => (snd c <=? 1)%N) (snd e)) (map_to_list (r_hav SH0)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. specialize (K _ H). cbn [snd] in K. rewrite forallb_forall in K. specialize (K _ Hin). apply N.leb_le in K. exact K.
Qed.
Lemma SH0_havp : forall pg t, r_havp SH0 !! pg = Some t -> (t <= 1)%N.
Proof.
  intros pg t H. apply lookup_In in H.
  assert (K : forallb (fun e => (snd e <=? 1)%N) (map_to_list (r_havp SH0)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. specialize (K _ H). cbn [snd] in K. apply N.leb_le in K. exact K.
Qed.

Lemma regs0_lookup : forall rid r, s_regions st !! rid = Some r ->
  (rid = 1%N /\ r = mkRegion RKGroup gm 69632) \/ (rid = 0%N /\ r = mkRegion (if b then RKBrk else RKMeta) (area - 4096) 8192).
Proof.
  intros rid r H. idtac. rewrite st0_regions in H. unfold regs0 in H.
  apply lookup_insert_Some in H as [[<- <-]|[NE H]]; [left; auto|].
  apply lookup_insert_Some in H as [[<- <-]|[NE2 H]]; [right; auto|]. rewrite lookup_empty in H. discriminate.
Qed.
Lemma regs0_1 : s_regions st !! 1%N = Some (mkRegion RKGroup gm 69632).
Proof. rewrite st0_regions. unfold regs0. apply lookup_insert_eq. Qed.
Lemma regs0_0 : s_regions st !! 0%N = Some (mkRegion (if b then RKBrk else RKMeta) (area - 4096) 8192).
Proof. rewrite st0_regions. unfold regs0. rewrite lookup_insert_ne by discriminate. apply lookup_insert_eq. Qed.

Lemma map_to_list_regs0 : map_to_list (s_regions st) ≡ₚ [(1%N, mkRegion RKGroup gm 69632); (0%N, mkRegion (if b then RKBrk else RKMeta) (area - 4096) 8192)].
Proof.
  rewrite st0_regions. unfold regs0.
  rewrite map_to_list_insert by (rewrite lookup_insert_ne by discriminate; apply lookup_empty).
  apply perm_skip. rewrite map_to_list_insert by apply lookup_empty. rewrite map_to_list_empty. reflexivity.
Qed.

Lemma frontier_st0 : forall rid r, frontier st rid r = if (0 =? rid)%N then 8192 else r_len r.
Proof. intros rid r. unfold frontier. rewrite st0_amas. reflexivity. Qed.

Lemma round_up_pg_69632 : round_up_pg 69632 = 69632. Proof. reflexivity. Qed.
Lemma round_up_pg_8192 : round_up_pg 8192 = 8192. Proof. reflexivity. Qed.

Lemma gcnt_st0 : forall sc, gcnt st sc = if sc =? 44 then 1 else 0.
Proof.
  intros sc. unfold gcnt. rewrite st0_groups, map_to_list_singleton. cbn [map zsum fold_right snd g_meta].
  rewrite (st0_MR b area gm slot0), aptr_eqb_refl. cbn [m_sizeclass cnt_of m_last_idx meta_slot0].
  destruct (Z.eqb_spec 44 sc); destruct (Z.eqb_spec sc 44); try lia; reflexivity.
Qed.

Lemma LS0_in : forall h m, In m (LS0 h) -> h = LActive 44 /\ m = slot0.
Proof. intros h m. unfold LS0. destruct h as [sc|]; [| intros []]. destruct (Z.eqb_spec sc 44) as [->|NE]; [| intros []]. intros [<-|[]]. auto. Qed.

Lemma hosts_st0 : forall bb m, hosts st bb m <-> bb = (1%N, 0) /\ m = slot0.
Proof.
  intros bb m. unfold hosts. rewrite st0_groups. split.
  - intros [ai H]. apply lookup_singleton_Some in H as [<- H]. injection H as <- <-. auto.
  - intros [-> ->]. exists 0. apply lookup_insert_eq.
Qed.

Hypothesis DISJM : b = false -> area + 4096 <= gm \/ gm + 69632 <= area - 4096.

Lemma shadow_st0_lookup : forall rid sh, s_shadow st !! rid = Some sh -> rid = 1%N /\ sh = SH0.
Proof.
  intros rid sh H. idtac. rewrite st0_shadow_eq in H. apply lookup_singleton_Some in H as [<- <-]. auto.
Qed.

Lemma known_SH0 : forall o v, In (o, v) [(12, 0); (69628, 0); (28, 0); (29, 160); (30, 1); (31, 0); (69623, 0); (69624, 220); (69625, 15); (69626, 0); (69627, 0); (65568, 0); (13, 224); (14, 1); (15, 0)] ->
  cell_read SH0 o = Known v.
Proof.
  intros o v Hin. pose proof SH0_known as K. rewrite forallb_forall in K. apply known_b_true. exact (K _ Hin).
Qed.

Lemma region_rng : 0x1000 <= area - 4096 /\ area + 4096 <= alloc_ceiling /\ 0x66000 <= gm /\ gm + 69632 <= alloc_ceiling
  /\ (area - 4096) mod 4096 = 0 /\ gm mod 4096 = 0.
Proof.
  destruct GE. bz_ceil.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; lia.
Qed.

Theorem INVL0 : INVL x0 st L BL0 LS0.
Proof.
  cps_pose region_rng as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof frontier_st0 as FR. pose proof regs0_lookup as RL. pose proof regs0_0 as RG0. pose proof regs0_1 as RG1.
  pose proof map_to_list_regs0 as MTL. pose proof shadow_st0_lookup as SHL. pose proof get_shadow_st0 as GS.
  pose proof (st0_MR b area gm) as MRst. idtac.
  assert (MR0 : MR st slot0 = meta_slot0) by (rewrite MRst, aptr_eqb_refl; reflexivity).
  assert (LENMAX : LEN_MAX = 2^63) by reflexivity.
  assert (HOST : forall bb m, hosts st bb m <-> bb = (1%N, 0) /\ m = slot0) by (apply hosts_st0).
  assert (INL : forall m, in_list LS0 m <-> m = slot0).
  { intros m. unfold in_list. split; [intros [h H]; exact (proj2 (LS0_in h m H))| intros ->; exists (LActive 44); left; reflexivity]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) constructor.
    + intros rid r H. rewrite st0_next_rid. destruct (RL rid r H) as [[-> _]|[-> _]]; lia.
    + intros rid r H. rewrite LENMAX. destruct (RL rid r H) as [[-> ->]|[-> ->]]; cbn [r_base r_len is_metakind r_kind].
      * rewrite round_up_pg_69632. unfold PGSZ. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros [E|E]; discriminate.
      * rewrite round_up_pg_8192. unfold PGSZ. split; [lia|]. split; [exact R5|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _. split; [reflexivity| lia].
    + intros rid1 rid2 r1 r2 H1 H2 NE.
      destruct (RL rid1 r1 H1) as [[-> ->]|[-> ->]]; destruct (RL rid2 r2 H2) as [[-> ->]|[-> ->]]; try congruence;
        unfold region_live_range; cbn [r_kind r_base r_len]; rewrite ?round_up_pg_69632, ?round_up_pg_8192; unfold PGSZ;
        destruct b; cbn; destruct GE; try lia; specialize (DISJM eq_refl); lia.
    + unfold L0. cbn [ld_resv]. rewrite st0_reserved. reflexivity.
    + unfold L0. cbn [ld_groups]. destruct (Permutation_length_2_inv (Permutation_sym MTL)) as [E|E]; rewrite E; destruct b; cbn; apply Permutation_refl.
    + unfold L0. cbn [ld_metas]. destruct (Permutation_length_2_inv (Permutation_sym MTL)) as [E|E]; rewrite E; destruct b; cbn -[Z.sub Z.div frontier];
        try apply Permutation_refl; rewrite FR; cbn; apply Permutation_refl.
    + intros rid r H K. destruct (RL rid r H) as [[-> ->]|[-> ->]]; cbn [r_kind r_len] in K |- *; [discriminate|].
      destruct b; [discriminate|]. rewrite FR. cbn. unfold PGSZ. split; [exists 1; split; [lia| reflexivity]|]. lia.
    + intros rid r H K. destruct (RL rid r H) as [[-> ->]|[-> ->]]; cbn [r_kind r_len] in K |- *; [discriminate|].
      rewrite FR. reflexivity.
    + rewrite st0_mas. destruct b; [split; [lia| left; reflexivity]|]. split; [lia| right].
      exists 0%N, (mkRegion RKMeta (area - 4096) 8192). split; [exact RG0| split; reflexivity].
    + intros bb l. unfold L0. cbn [ld_brkreg]. destruct b.
      * split; [intros E; injection E as <- <-; exists 0%N, (mkRegion RKBrk (area - 4096) 8192); split; [exact RG0| repeat split; reflexivity]|].
        cps_intros (rid & r & H & K & <- & <-). destruct (RL rid r H) as [[-> ->]|[-> ->]]; cbn in K |- *; [discriminate| reflexivity].
      * split; [discriminate|]. cps_intros (rid & r & H & K & _). destruct (RL rid r H) as [[-> ->]|[-> ->]]; cbn in K; discriminate.
    + intros rid1 rid2 r1 r2 H1 H2 K1 K2. destruct (RL rid1 r1 H1) as [[-> ->]|[-> ->]]; [cbn in K1; discriminate|].
      destruct (RL rid2 r2 H2) as [[-> ->]|[-> ->]]; [cbn in K2; discriminate| reflexivity].
    + rewrite st0_brk. unfold L0. cbn [ld_brk]. destruct b.
      * split; [reflexivity|]. eexists. split; [exact RG0|]. split; reflexivity.
      * reflexivity.
    + rewrite st0_amac, st0_amas. split; [lia|]. split; [lia|].
      intros rid off E. injection E as <- <-. eexists. split; [exact RG0|]. cbn [is_metakind r_kind r_len]. unfold PGSZ.
      split; [destruct b; [left| right]; reflexivity|]. repeat split; lia.
    + intros rid H. discriminate.
  - (* [comment removed for export] *) constructor.
    + rewrite st0_mc, st0_seq, st0_bnc, st0_useq.
      split; [lia|]. split; [lia|]. split; intros i v H; rewrite lookup_empty in H; discriminate.
    + rewrite st0_secret, st0_init, st0_secret_c. split; [pose proof run_secret_range; lia|]. right. auto.
    + intros a ar H. idtac. rewrite st0_areas in H. apply lookup_singleton_Some in H as [<- <-]. cbn [fst snd a_check a_nslots a_next].
      split; [| split; [rewrite st0_secret_c; reflexivity| split; [reflexivity| intros aa E; discriminate]]].
      eexists. split; [exact RG0|]. cbn [is_metakind r_kind]. rewrite FR. cbn. unfold PGSZ.
      split; [destruct b; [left|right]; reflexivity|]. repeat split; lia.
    + intros h H. idtac. rewrite st0_mah in H. injection H as <-. rewrite st0_areas, lookup_insert_eq. discriminate.
    + intros t H. idtac. rewrite st0_mat in H. injection H as <-. rewrite st0_areas, lookup_insert_eq. discriminate.
    + intros H. idtac. rewrite st0_mat in H. discriminate.
    + intros m mr H. idtac. rewrite st0_metas in H. apply lookup_singleton_Some in H as [<- <-].
      exists (0%N, 4096), (mkArea run_secret None 101), 0. rewrite st0_areas, lookup_insert_eq. split; [reflexivity|]. split; [unfold NSLOTS; lia|]. reflexivity.
    + rewrite st0_amc, st0_mat, st0_am. unfold NSLOTS. split; [lia|]. intros _.
      eexists. split; [reflexivity|]. split; [reflexivity|]. intros k Hk. rewrite st0_metas. apply lookup_singleton_ne.
      unfold mslot, aadd, AREA_HDR, META_SIZE, slot0. cbn. intros E. injection E. lia.
    + intros q H. idtac. rewrite st0_am in H. injection H as <-. cbn [fst]. eexists. split; [exact RG0|]. cbn [is_metakind r_kind]. destruct b; [left|right]; reflexivity.
    + intros sc Hsc. rewrite st0_usage. rewrite gcnt_st0. reflexivity.
    + intros sc v H. idtac. idtac. rewrite st0_ctx_eq in H. cbn [c_usage set_secret] in H.
      assert (E : c_usage (s_ctx (if b then st0c_brk else st0c_mm)) = {[44 := 1]}) by (destruct b; vm_compute; reflexivity).
      rewrite E in H. apply lookup_singleton_Some in H as [<- _]. lia.
    + intros sc g H. idtac. idtac. rewrite st0_ctx_eq in H. cbn [c_active set_secret] in H.
      assert (E : c_active (s_ctx (if b then st0c_brk else st0c_mm)) = {[44 := slot0]}) by (destruct b; vm_compute; reflexivity).
      rewrite E in H. apply lookup_singleton_Some in H as [<- _]. lia.
  - (* [comment removed for export] *) constructor.
    + intros m H. rewrite MRst in H |- *. destruct (aptr_eqb m slot0); [cbn in H; discriminate| reflexivity].
    + intros m bb H. rewrite MRst in H. destruct (aptr_eqb_spec m slot0) as [->|NE]; [| cbn in H; discriminate]. cbn in H. injection H as <-.
      left. apply HOST. auto.
    + intros bb h H. idtac. rewrite st0_groups in H. apply lookup_singleton_Some in H as [<- <-]. exists slot0. cbn [g_meta g_active_idx].
      split; [reflexivity|]. rewrite MR0. cbn. split; [reflexivity| lia].
    + intros m [].
    + intros z [].
  - (* [comment removed for export] *) constructor.
    + intros h. destruct h as [sc|]; cbn [get_head LS0 head_of].
      * rewrite st0_active. destruct (sc =? 44); reflexivity.
      * rewrite st0_fh. reflexivity.
    + intros h. destruct h as [sc|]; cbn [LS0 dll]; [| exact I]. destruct (sc =? 44); cbn [dll linked app]; [| exact I].
      rewrite MR0. cbn. auto.
    + intros h. destruct h as [sc|]; cbn [LS0]; [| constructor]. destruct (sc =? 44); [| constructor]. constructor; [intros H; inversion H| constructor].
    + intros h1 h2 m H1 H2. destruct (LS0_in h1 m H1) as [-> _]. destruct (LS0_in h2 m H2) as [-> _]. reflexivity.
    + intros m. fold (in_list LS0 m). rewrite INL, MRst. destruct (aptr_eqb_spec m slot0) as [->|NE]; cbn; [split; [split; [discriminate| auto]| discriminate]|].
      split; [split; [congruence| intros H; exfalso; apply H; reflexivity]| reflexivity].

    + intros m [].
    + intros sc m H. cbn [LS0] in H. destruct (Z.eqb_spec sc 44) as [->|NE]; [| destruct H]. destruct H as [<-|[]].
      split; [lia|]. split; [exists (1%N, 0); apply HOST; auto|]. rewrite MR0. reflexivity.
    + intros hh HH. destruct hh as [sc0|]; [| exact I]. cbn [LS0] in HH. destruct (Z.eqb_spec sc0 44) as [E|NE]; [lia|]. exfalso. apply HH. reflexivity.
  - (* [comment removed for export] *) constructor.
    + intros m bb ai H. idtac. rewrite st0_groups in H. apply lookup_singleton_Some in H as [<- H]. injection H as <- <-.
      assert (GS69 : get_stride meta_slot0 = 69616) by reflexivity.
      assert (SC44 : size_class 44 = 4680) by reflexivity.
      constructor; rewrite ?MR0.
      * rewrite st0_metas, lookup_insert_eq. discriminate.
      * cbn. lia.
      * cbn. lia.
      * left. cbn. lia.
      * reflexivity.
      * cbn. lia.
      * cbn [m_avail m_freed m_last_idx meta_slot0]. unfold tbit. split; [lia|]. split; [lia|].
        split; [intros i Hi T; rewrite Z.testbit_0_l in T; discriminate|]. split; [intros i Hi T; rewrite Z.testbit_0_l in T; discriminate|].
        split; [intros i Hi T; rewrite Z.testbit_0_l in T; discriminate|]. intros i Hi. lia.
      * cbn [m_last_idx meta_slot0]. intros _ H. lia.
      * intros _ _ H. exfalso. apply H. apply INL. reflexivity.
      * intros _ sc H NE. exfalso. apply NE. cbn [LS0] in H |- *. destruct (Z.eqb_spec sc 44) as [Esc|?]; [| destruct H]. reflexivity.
      * intros _. rewrite GS69. cbn [m_sizeclass m_last_idx m_maplen meta_slot0]. rewrite SC44. unfold UNIT, cnt_of. cbn [m_last_idx meta_slot0].
        split; [left; lia|]. split; [intros _; split; [discriminate| lia]|]. cbn. lia.
      * intros _ _ _. cbn. auto.
      * cbn. split; [lia| reflexivity].
      * intros _. cbn [snd]. split; [reflexivity|]. eexists. split; [exact RG1|]. cbn [r_kind r_len m_maplen meta_slot0]. rewrite round_up_pg_69632.
        split; [reflexivity|]. split; [reflexivity|]. unfold gend, sstart, cnt_of, gbase. rewrite GS69. cbn -[Z.mul Z.add Z.le]. unfold UNIT. lia.
      * cbn [m_maplen meta_slot0]. intros H. discriminate.
      * cbn [m_sizeclass meta_slot0]. intros H. discriminate.
    + intros bb ai H. idtac. rewrite st0_groups in H. apply lookup_singleton_Some in H as [_ H]. discriminate.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2 _ _ _. idtac. rewrite st0_groups in H1, H2.
      apply lookup_singleton_Some in H1 as [_ H1]. apply lookup_singleton_Some in H2 as [_ H2]. congruence.
    + intros rid r H K _. destruct (RL rid r H) as [[-> ->]|[-> ->]]; [| destruct b; cbn in K; discriminate].
      exists slot0. split; [apply HOST; auto|]. rewrite MR0. discriminate.
    + intros bb h H. idtac. rewrite st0_groups in H. apply lookup_singleton_Some in H as [<- _]. eexists. split; [exact RG1| reflexivity].
  - (* [comment removed for export] *) constructor.
    + intros sl m i H. idtac. rewrite st0_slots in H. apply lookup_singleton_Some in H as [<- H]. injection H as <- <-.
      split; [exists (1%N, 0); apply HOST; auto|]. rewrite MR0. cbn. split; [lia| reflexivity].
    + intros bb m i HH Hi. apply HOST in HH as [-> ->]. rewrite MR0 in Hi |- *. cbn in Hi. assert (i = 0) by lia. subst i.
      rewrite st0_slots. apply lookup_insert_eq.
    + intros bb m ai i H Hi. idtac. rewrite st0_groups in H. apply lookup_singleton_Some in H as [<- H]. injection H as <- <-.
      rewrite MR0 in Hi |- *. cbn in Hi. assert (i = 0) by lia. subst i.
      cbn [m_avail m_freed meta_slot0 slot_start' m_mem default x_pend x0 map bslot BL0 fst]. unfold tbit. rewrite !Z.testbit_0_l.
      rewrite st0_groups. unfold one5. rewrite lookup_singleton_ne by discriminate. cbn [In].
      intuition congruence.
    + intros sl H. discriminate.
    + cbn. constructor; [intros H; inversion H| constructor].
    + intros k [<-|[]]. exists slot0, 0. cbn [bslot boff bsize fst snd]. rewrite st0_slots, lookup_insert_eq. split; [reflexivity|].
      rewrite MR0. change (get_stride meta_slot0) with 69616. unfold UNIT, IB. lia.
  - (* [comment removed for export] *) constructor.
    + intros rid sh H. destruct (SHL rid sh H) as [-> ->]. eexists. split; [exact RG1| reflexivity].
    + intros rid sh H. destruct (SHL rid sh H) as [-> ->]. rewrite st0_tick. split; [| split].
      * intros o v t Hc. destruct (SH0_cells o v t Hc). split; [lia| lia].
      * intros u hl ch Hu Hin. pose proof (SH0_hav u hl ch Hu Hin). lia.
      * intros pg t Hp. pose proof (SH0_havp pg t Hp). lia.
    + intros bb m i HH Hi. apply HOST in HH as [-> ->]. rewrite MR0 in Hi |- *. unfold known, SHd. cbn [fst snd]. rewrite GS. cbn [N.eqb].
      unfold sstart, gbase, cnt_of in *. cbn -[Z.add Z.mul Z.sub Z.le] in Hi |- *. change (get_stride meta_slot0) with 69616.
      assert (i = 0 \/ i = 1) as [->| ->] by lia; apply known_SH0; cbn; [left| right; left]; reflexivity.
    + intros bb m o HH Ho. apply HOST in HH as [-> ->]. unfold unknown, SHd. cbn [fst snd]. rewrite GS. cbn [N.eqb].
      apply unknown_b_true. pose proof SH0_hdr as K. rewrite forallb_forall in K. apply K. apply in_zrange; lia.
    + intros bb m pp i HH Hml. apply HOST in HH as [-> ->]. rewrite MR0 in Hml. cbn in Hml. discriminate.
    + intros k m i [<-|[]] H. idtac. rewrite st0_slots in H. cbn [bslot fst] in H. rewrite lookup_insert_eq in H. injection H as <- <-.
      rewrite MR0. unfold known, unknown, SHd. cbn [fst snd bslot boff bsize BL0 gbase m_mem meta_slot0 default]. rewrite GS. cbn [N.eqb].
      change (get_stride meta_slot0) with 69616. unfold UNIT, IB. cbn -[Z.le Z.lt Z.pow cell_read SH0].
      repeat split; try (apply known_SH0; cbn; tauto); try lia.
      intros a Ha. apply SH0_user. lia.
Qed.
End INV0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma resv_S0 : map wwZ (segments_reserved Ubsan.M.loaded_segments) = ref_reserved.
Proof. vm_compute. reflexivity. Qed.
Lemma reserved_top_S0 : reserved_top (segments_reserved Ubsan.M.loaded_segments) = 0x66000.
Proof. vm_compute. reflexivity. Qed.

Lemma seps_pwdisj : forall l, seps l -> pwdisj l.
Proof.
  induction 1 as [|p l HF HS IH]; constructor; [| exact IH].
  intros e' Hin. pose proof (proj1 (Forall_forall _ _) HF e' Hin) as D. unfold iv_disjoint in D. unfold edisj, elo, ehi. lia.
Qed.

Lemma mod_sub_pg a : a mod 4096 = 0 -> (a - 4096) mod 4096 = 0.
Proof.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  intros H. lia.
Qed.

Section KL0.
Variables (sp0 gm area brkv mas : Z) (VM : VmMaps) (MD : Model).
Hypothesis TV : target_vm gm area VM.
Hypothesis TX : target_vmx sp0 gm area brkv mas VM.
Hypothesis SMv : m_vmmaps MD = VM.
Hypothesis SMh : m_halted MD = None.
Hypothesis SMl : m_vm_lazy MD = [].
Hypothesis GE : geo (mas =? 0) area gm.
Hypothesis ATOP : atop_ok VM.   (* [comment removed for export] *)

Definition pbrk0 : Z := area + 4096.

Lemma KL_L0 : KL (L0 (mas =? 0) area gm) pbrk0 MD.
Proof.
  destruct TV as [TVr TVh TVa TVl TVp TVs TVlim].
  destruct GE as [GA GG GAR GAI GGR GD].
  cps_destruct TX as (brk0 & mbase & VB & CASES).
  cps_destruct VB as (VB1 & VB2 & VB3). rewrite reserved_top_S0 in VB1, VB2. unfold brk_aslr_max in VB2. unfold page_size in VB3.
  bz_ceil.
  assert (WF : vmwf (vm_maps VM)).
  { split; [| apply seps_pwdisj; exact TVs]. intros e He. pose proof (proj1 (Forall_forall _ _) TVp e He) as [S1 S3]. unfold elo, ehi. lia. }
  assert (RT : forall e, In e (vm_reserved VM) -> ehi e <= 0x66000).
  { intros e He. rewrite TVr in He. unfold ehi.
    assert (K : Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= 0x66000) (segments_reserved Ubsan.M.loaded_segments)).
    { apply Forall_forall. intros x Hx. apply (in_map wwZ) in Hx. rewrite resv_S0 in Hx. unfold wwZ in Hx.
      cbn in Hx. destruct x as [x1 x2]; cbn in Hx |- *.
      destruct Hx as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia. }
    exact (proj1 (Forall_forall _ _) K e He). }
  destruct CASES as [(M0 & AR & BV & maps & na & EVM & MC)|(M1 & BV & a & AR & EVM)].
  - (* [comment removed for export] *)
    assert (Eb : (mas =? 0) = true) by (rewrite M0; reflexivity). rewrite Eb.
    assert (VMr : vm_reserved (m_vmmaps MD) = vm_reserved VM) by (rewrite SMv; reflexivity).
    assert (VMm : vm_maps (m_vmmaps MD) = (Z_to_bv 64 gm, Z_to_bv 64 69632) :: maps) by (rewrite SMv, EVM; reflexivity).
    assert (VMs : vm_start_brk (m_vmmaps MD) = brk0) by (rewrite SMv, EVM; reflexivity).
    assert (VMb : vm_brk (m_vmmaps MD) = Z_to_bv 64 (bv_unsigned brk0 + 8192)) by (rewrite SMv, EVM; reflexivity).
    assert (VMm0 : vm_maps VM = (Z_to_bv 64 gm, Z_to_bv 64 69632) :: maps) by (rewrite EVM; reflexivity).
    assert (U8 : bv_unsigned (Z_to_bv 64 (bv_unsigned brk0 + 8192)) = bv_unsigned brk0 + 8192) by (apply unsigned_lit; lia).
    constructor; rewrite ?VMr, ?VMm, ?VMs, ?VMb; cbn [ld_resv ld_groups ld_metas ld_brkreg ld_brk L0].
    + exact SMh. + exact SMl.
    + rewrite <- VMm0. exact WF.
    + rewrite TVr. symmetry. exact resv_S0.
    + intros e He. pose proof (RT e He). lia.
    + rewrite U8. unfold PGSZ. bz_ceil. lia.
    + intros bb l [E|[]]. injection E as <- <-. unfold LEN_MAX, PGSZ. bz_ceil.
      rewrite (mmap_len_of_aligned 69632) by (try lia; reflexivity).
      split; [lia|]. split; [lia|]. split; [exact GG|]. split; [lia|]. split.
      * left. reflexivity.
      * intros b0 l0 E. injection E as <- <-. unfold PGSZ. lia.
    + intros bb l k [].
    + cbn. constructor; [intros H; inversion H| constructor].
    + intros bb l E. injection E as <- <-. unfold PGSZ. bz_ceil.
      split; [lia|]. split; [apply mod_sub_pg; exact GA|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
      intros x Hx. destruct MC as [[-> NA]|[-> ->]].
      * exists (brk0, Z_to_bv 64 8192). split; [right; left; reflexivity|]. unfold elo, ehi. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
      * exists (Z_to_bv 64 (bv_unsigned brk0 + 4096), Z_to_bv 64 4096). split; [right; left; reflexivity|]. unfold elo, ehi. cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
    + exists (area - 4096), 8192. split; [reflexivity|]. rewrite U8. unfold pbrk0. lia.
    + rewrite SMv. exact ATOP.
  - (* [comment removed for export] *)
    assert (Eb : (mas =? 0) = false) by (rewrite M1; reflexivity). rewrite Eb.
    assert (Ea : Z_to_bv 64 (area - 4096) = a) by (rewrite AR; replace (bv_unsigned a + 4096 - 4096) with (bv_unsigned a) by lia; apply Z_to_bv_bv_unsigned).
    assert (VMr : vm_reserved (m_vmmaps MD) = vm_reserved VM) by (rewrite SMv; reflexivity).
    assert (VMm : vm_maps (m_vmmaps MD) = [(Z_to_bv 64 gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)]) by (rewrite SMv, EVM; reflexivity).
    assert (VMs : vm_start_brk (m_vmmaps MD) = brk0) by (rewrite SMv, EVM; reflexivity).
    assert (VMb : vm_brk (m_vmmaps MD) = brk0) by (rewrite SMv, EVM; reflexivity).
    assert (VMm0 : vm_maps VM = [(Z_to_bv 64 gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)]) by (rewrite EVM; reflexivity).
    constructor; rewrite ?VMr, ?VMm, ?VMs, ?VMb; cbn [ld_resv ld_groups ld_metas ld_brkreg ld_brk L0].
    + exact SMh. + exact SMl.
    + rewrite <- VMm0. exact WF.
    + rewrite TVr. symmetry. exact resv_S0.
    + intros e He. pose proof (RT e He). lia.
    + unfold PGSZ. bz_ceil. lia.
    + intros bb l [E|[]]. injection E as <- <-. unfold LEN_MAX, PGSZ. bz_ceil.
      rewrite (mmap_len_of_aligned 69632) by (try lia; reflexivity).
      split; [lia|]. split; [lia|]. split; [exact GG|]. split; [lia|]. split.
      * left. reflexivity.
      * intros b0 l0 E. discriminate.
    + intros bb l k [E|[]]. injection E as <- <- <-. unfold LEN_MAX, PGSZ. bz_ceil.
      rewrite (mmap_len_of_aligned 8192) by (try lia; reflexivity).
      split; [lia|]. split; [lia|]. split; [apply mod_sub_pg; exact GA|]. split; [lia|].
      split; [lia|]. split; [lia|]. split.
      * unfold went, KInv.wz. rewrite Ea. right. left. reflexivity.
      * split; [intros b0 l0 E; discriminate|]. intros q Hq1 Hq2. lia.
    + cbn. constructor; [| constructor; [intros H; inversion H| constructor]]. intros H. cbn in H. destruct GE; lia.
    + intros bb l E. discriminate.
    + exact I.
    + rewrite SMv. exact ATOP.
Qed.
End KL0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZIMG (a : Z) : bool :=
  match seg_rom s0segs (wa a) with Some v => (bv_unsigned v =? 0) | None => false end.
Lemma zimg_ok : forallb ZIMG (zrange 0x440f0 (0x66000 - 0x440f0)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)

Lemma seg_rom_zero : forall a, 0x440f0 <= a < 0x66000 -> seg_rom s0segs (wa a) = Some (b8 0).
Proof.
  intros a Ha. pose proof (forallb_zrange ZIMG 0x440f0 (0x66000 - 0x440f0) a zimg_ok ltac:(lia) ltac:(lia)) as K.
  unfold ZIMG in K. destruct (seg_rom s0segs (wa a)) as [v|] eqn:E; [|discriminate].
  f_equal. apply bv_eq. apply Z.eqb_eq in K. rewrite K. reflexivity.
Qed.

Lemma wr_img : forall m A n, 0x440f0 <= A -> A + n <= 0x66000 -> 0 <= n -> wr_at s0segs m A n.
Proof.
  intros m A n H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (m (wa (A + i))) as [v|] eqn:E.
  - unfold wview. rewrite E. discriminate.
  - rewrite wview_rw_data_pristine; [| unfold rw_data; lia | exact E]. rewrite seg_rom_zero by lia. discriminate.
Qed.

Lemma bytes_zero_img : forall m A n, img_pristine m A (A + n) -> 0x440f0 <= A -> A + n <= 0x66000 -> 0 <= n ->
  bytes_at s0segs m A (zeros (Z.to_nat n)).
Proof.
  intros m A n HP H1 H2 H3. split; [lia|]. unfold zeros. rewrite repeat_length. split; [lia|].
  intros i Hi. unfold mrd. rewrite (HP (A + Z.of_nat i)) by lia. rewrite seg_rom_zero by lia.
  symmetry. apply nth_error_repeat. exact Hi.
Qed.

Lemma u8arr_zero_img : forall m A n, img_pristine m A (A + n) -> 0x440f0 <= A -> A + n <= 0x66000 -> 0 <= n ->
  u8arr s0segs m A (zeros (Z.to_nat n)).
Proof.
  intros m A n HP H1 H2 H3. split; [apply bytes_zero_img; assumption|].
  unfold zeros. rewrite repeat_length. apply wr_img; lia.
Qed.

Lemma wr_off : forall m A n, (forall i, 0 <= i < n -> m (Z_to_bv 64 (A + i)) <> None) ->
  (A + n <= 0x10000 \/ 0x66000 <= A) -> 0 <= A -> A + n <= 2^64 -> 0 <= n -> wr_at s0segs m A n.
Proof.
  intros m A n HD HO H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia). apply HD. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_byte : forall m a v, m (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> (a + 1 <= 0x10000 \/ 0x66000 <= a) -> 0 <= a -> a + 1 <= 2^64 ->
  bytes_at s0segs m a [b8 v].
Proof.
  intros m a v H HO H1 H2. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia].
  cbn [nth_error]. rewrite Z.add_0_r. rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). exact H.
Qed.

Lemma zeros_bytes_at : forall m a n, zero_bytes m a n -> (a + n <= 0x10000 \/ 0x66000 <= a) -> 0 <= a -> a + n <= 2^64 -> 0 <= n ->
  bytes_at s0segs m a (zeros (Z.to_nat n)).
Proof.
  intros m a n HZ HO H1 H2 H3. split; [lia|]. unfold zeros. rewrite repeat_length. split; [lia|].
  intros i Hi. rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). unfold wa. rewrite (HZ (Z.of_nat i)) by lia.
  symmetry. apply nth_error_repeat. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma rdn_byte : forall n m a bs (i : nat) v, rdn s0segs m (Z_to_bv 64 a) n = Some bs -> option_map bv_unsigned (nth_error bs i) = Some v ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> (a + Z.of_nat n <= 0x10000 \/ 0x66000 <= a) ->
  bytes_at s0segs m (a + Z.of_nat i) [b8 v].
Proof.
  intros n m a bs i v H Hi H1 H2 HO.
  destruct (nth_error bs i) as [v'|] eqn:N; [| discriminate]. cbn in Hi. injection Hi as <-.
  cps_pose (bytes_at_of_rdn n m a bs H H1 H2) as (B1 & B2 & B3).
  pose proof (nth_error_lt _ _ _ N) as L.
  pose proof (rdn_length _ _ _ _ _ H) as LEN.
  split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. destruct j; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
  rewrite (B3 i L), N. f_equal. apply bv_eq. unfold b8. rewrite Z_to_bv_small; [reflexivity|]. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RM0.
Variables (area gm brkv mas tid hw : Z) (M : word -> option byte).
Hypothesis W : world0 area gm brkv mas tid hw M.
Hypothesis MB : (mas = 0 /\ brkv = area + 4096) \/ (mas = 1 /\ brkv = 2^64 - 1).
Let b : bool := mas =? 0.
Hypothesis DISJM : b = false -> area + 4096 <= gm \/ gm + 69632 <= area - 4096.
Local Notation st := (st0 b area gm) (only parsing).

Lemma GE_W : geo b area gm.
Proof. destruct W. constructor; assumption. Qed.

Lemma conc0g : forall bb off, conc (st0 bb area gm) (0%N, off) = area - 4096 + off.
Proof. intros bb off. unfold conc, get_region. cbn [fst snd]. rewrite (regs0_0 bb area gm). reflexivity. Qed.
Lemma conc1g : forall bb off, conc (st0 bb area gm) (1%N, off) = gm + off.
Proof. intros bb off. unfold conc, get_region. cbn [fst snd]. rewrite (regs0_1 bb area gm). reflexivity. Qed.
Lemma conc0 : forall off, conc st (0%N, off) = area - 4096 + off. Proof. apply conc0g. Qed.
Lemma conc1 : forall off, conc st (1%N, off) = gm + off. Proof. apply conc1g. Qed.

Lemma mas_b : (if b then 0 else 1) = mas.
Proof. unfold b. destruct MB as [[-> _]|[-> _]]; reflexivity. Qed.
Lemma brkv_b : brkv = if b then area + 4096 else 2^64 - 1.
Proof. unfold b. destruct MB as [[-> ->]|[-> ->]]; reflexivity. Qed.

Lemma ctx_head_st0 : ctx_head_cells st =
  [C8 (wz run_secret); C4 (wz 1); C4 (wz 1); C8 (wz 0); C8 (wz (area + 64)); C8 (wz 100); C8 (wz 0); C8 (wz mas);
   C8 (wz area); C8 (wz area); C8 (wz (area + 4096))].
Proof.
  unfold ctx_head_cells, ctx. cbv zeta.
  rewrite (st0_secret_c b area gm), (st0_init b area gm), (st0_mc b area gm), (st0_fh b area gm), (st0_am b area gm),
    (st0_amc b area gm), (st0_amac b area gm), (st0_mas b area gm), (st0_mah b area gm), (st0_mat b area gm), (st0_amas b area gm).
  unfold pw, oconc. rewrite !conc0, mas_b.
  repeat first [reflexivity | f_equal; try (f_equal; f_equal; lia)].
Qed.

Lemma actives_st0 : actives st = repeat (wz 0) 44 ++ [wz (area + 24)] ++ repeat (wz 0) 3.
Proof.
  unfold actives.
  rewrite (map_ext _ (fun i => if Z.of_nat i =? 44 then wz (area + 24) else wz 0)).
  2:{ intros i. rewrite (st0_active b area gm). destruct (Z.of_nat i =? 44); [| reflexivity]. unfold pw, oconc, slot0. rewrite conc0. f_equal. lia. }
  cbn -[wz Z.add]. reflexivity.
Qed.
Lemma usages_st0 : usages st = repeat (wz 0) 44 ++ [wz 1] ++ repeat (wz 0) 3.
Proof.
  unfold usages.
  rewrite (map_ext _ (fun i => if Z.of_nat i =? 44 then wz 1 else wz 0)).
  2:{ intros i. rewrite (st0_usage b area gm). destruct (Z.of_nat i =? 44); reflexivity. }
  cbn -[wz]. reflexivity.
Qed.
Lemma unmap_seqs_st0 : unmap_seqs st = zeros 32.
Proof.
  unfold unmap_seqs. rewrite (map_ext _ (fun _ => b8 0)); [cbn -[b8]; reflexivity|].
  intros i. unfold unmap_seq, ctx. rewrite (st0_useq b area gm), lookup_empty. reflexivity.
Qed.
Lemma bouncess_st0 : bouncess st = zeros 32.
Proof.
  unfold bouncess. rewrite (map_ext _ (fun _ => b8 0)); [cbn -[b8]; reflexivity|].
  intros i. unfold bounces, ctx. rewrite (st0_bnc b area gm), lookup_empty. reflexivity.
Qed.
Lemma ctx_tail_st0 : ctx_tail_cells st = [C1 (b8 1); CB 7 (zeros 7); C8 (wz brkv)].
Proof.
  unfold ctx_tail_cells, brk_word, ctx. rewrite (st0_seq b area gm), (st0_brk b area gm), brkv_b.
  clearbody b. destruct b; [| reflexivity]. rewrite conc0g. do 3 f_equal. f_equal. f_equal. lia.
Qed.

Lemma meta_cells_slot0 : meta_cells st meta_slot0 = [C8 (wz (area + 24)); C8 (wz (area + 24)); C8 (wz gm); C4 (wz 0); C4 (wz 0); C8 (wz W64K)].
Proof.
  unfold meta_cells, pw, oconc. cbn [m_prev m_next m_mem m_avail m_freed meta_slot0 slot0]. rewrite !conc0, conc1.
  replace (meta_word meta_slot0) with W64K by reflexivity.
  repeat first [reflexivity | f_equal; try (f_equal; f_equal; lia)].
Qed.
Lemma meta_cells_meta0 : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma PR : forall lo hi, In (lo, hi) img_clear_ivs -> img_pristine M lo hi.
Proof.
  intros lo hi Hin a Ha. pose proof (proj1 (Forall_forall _ _) (w_img _ _ _ _ _ _ _ W) _ Hin) as C. cbn [fst snd] in C. apply C. exact Ha.
Qed.

(* [comment removed for export] *)

Local Ltac norm_addr :=
  cbv [Z.of_nat Pos.of_succ_nat Pos.succ];
  repeat match goal with |- rw_cells _ _ (?a + ?x + ?y) _ =>
    let s := eval cbv in (x + y) in replace (a + x + y) with (a + s) by lia end.
Local Ltac split1 :=
  lazymatch goal with |- rw_cells _ _ ?A (?c :: ?rest) =>
    change (c :: rest) with ([c] ++ rest); apply rw_cells_app; cbn [cells_size csize Nat.add app]; norm_addr end.
Local Ltac split_cells :=
  repeat match goal with
  | |- rw_cells _ _ ?A (?c :: ?rest) =>
      lazymatch rest with
      | [] => idtac
      | _ => change (c :: rest) with ([c] ++ rest); apply rw_cells_app; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]
      end
  end.

Lemma W64 : gm + 69632 <= 2^64 /\ 0x66000 <= gm /\ 0x2000 <= area /\ area + 4096 <= 2^64 /\ (area + 4096 <= 0x10000 \/ 0x67000 <= area).
Proof. destruct W. lia. Qed.

Lemma ranges_free_ref : forall a n, 0 <= n -> (a + n <= 0x10000 \/ 0x66000 <= a) -> ranges_free ref_reserved a n = true.
Proof.
  intros a n Hn H. unfold ranges_free, ref_reserved, Malloc.iv_disjoint. cbn -[Z.add Z.leb orb andb].
  rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le. lia.
Qed.

Lemma regions_wf0 : rregions_wf st.
Proof.
  cps_pose (region_rng b area gm GE_W) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof GE_W as [GA GG GAR GAI GGR GD].
  split; [apply st0_reserved|]. split; [| split; [| split]].
  + intros rid r H. destruct (regs0_lookup b area gm rid r H) as [[-> ->]|[-> ->]]; cbn [r_base r_len];
      rewrite ?round_up_pg_69632, ?round_up_pg_8192.
    * split; [lia|]. split; [exact R6|]. split; [lia|]. split; [bz_ceil; lia|]. apply ranges_free_ref; lia.
    * split; [lia|]. split; [exact R5|]. split; [lia|]. split; [bz_ceil; lia|]. apply ranges_free_ref; lia.
  + intros rid1 r1 rid2 r2 H1 H2 NE.
    destruct (regs0_lookup b area gm rid1 r1 H1) as [[-> ->]|[-> ->]]; destruct (regs0_lookup b area gm rid2 r2 H2) as [[-> ->]|[-> ->]]; try congruence;
      unfold lr_lo; cbn [r_base r_len r_kind]; rewrite ?round_up_pg_69632, ?round_up_pg_8192; clearbody b; destruct b; cbn [r_kind]; try lia.
    all: specialize (DISJM eq_refl); lia.
  + intros a ar H. rewrite (st0_areas b area gm) in H. apply lookup_singleton_Some in H as [<- <-]. cbn [fst snd].
    eexists. split; [apply regs0_0|]. cbn [r_len r_kind r_base]. rewrite round_up_pg_8192. unfold lr_lo. cbn [r_kind r_base].
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [clearbody b; destruct b; discriminate|]. clearbody b; destruct b; cbn; lia.
  + intros bb gh H. rewrite (st0_groups b area gm) in H. apply lookup_singleton_Some in H as [<- <-]. cbn [fst snd].
    eexists. split; [apply regs0_1|]. cbn [r_len r_kind]. rewrite round_up_pg_69632. split; [reflexivity|]. split; [lia|]. split; [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma bytes_eq_u : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|c l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma rw_cells_of_bytes : forall m A cs, cells_wf cs -> bytes_at s0segs m A (cells_bytes cs) -> wr_at s0segs m A (Z.of_nat (cells_size cs)) ->
  rw_cells s0segs m A cs.
Proof. intros m A cs H1 H2 H3. split; [split; assumption| assumption]. Qed.

Lemma bytes_at_cell : forall m a n v, cell m a n v -> 0 <= a -> a + Z.of_nat n <= 2^64 -> bytes_at s0segs m a (word_to_le_bytes n (Z_to_bv 64 v)).
Proof. intros m a n v H H1 H2. apply (bytes_at_of_rdn n); [exact H| lia| lia]. Qed.

Lemma rw_C8_cell : forall m a v, cell m a 8 v -> wr_at s0segs m a 8 -> rw_cells s0segs m a [C8 (wz v)].
Proof. intros m a v H HW. apply rw_cells_C8_of_rdn; [exact H| exact HW]. Qed.
Lemma rw_C4_cell : forall m a v, cell m a 4 v -> wr_at s0segs m a 4 -> rw_cells s0segs m a [C4 (wz v)].
Proof. intros m a v H HW. apply rw_cells_C4_of_rdn; [exact H| exact HW]. Qed.
Lemma rw_C1_cell : forall m a v, cell m a 1 v -> 0 <= v < 256 -> wr_at s0segs m a 1 -> rw_cells s0segs m a [C1 (b8 v)].
Proof.
  intros m a v H Hv HW. cps_pose HW as (H1 & H2 & _). apply rw_cells_of_bytes; [exact (conj I I)| | exact HW].
  cbn [cells_bytes cbytes app]. eapply bytes_at_ext; [apply (bytes_at_cell m a 1 v H); lia|].
  cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. pose proof (bv_wrap_small 8 v). pose proof (bv_wrap_small 64 v).
  unfold bv_modulus in *. rewrite H3 by lia. reflexivity.
Qed.

Lemma u64s_repeat0 : forall k, u64s (repeat (wz 0) k) = zeros (8 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH.
  replace (8 * S k)%nat with (8 + 8 * k)%nat by lia. unfold zeros. rewrite repeat_app. f_equal.
Qed.

Lemma u64arr_3 : forall m A k1 w k2,
  bytes_at s0segs m A (zeros (8 * k1)) -> bytes_at s0segs m (A + 8 * Z.of_nat k1) (le8 w) ->
  bytes_at s0segs m (A + 8 * Z.of_nat k1 + 8) (zeros (8 * k2)) -> wr_at s0segs m A (8 * (Z.of_nat k1 + 1 + Z.of_nat k2)) ->
  u64arr s0segs m A (repeat (wz 0) k1 ++ [w] ++ repeat (wz 0) k2).
Proof.
  intros m A k1 w k2 B1 B2 B3 HW. split.
  - rewrite !u64s_app, !u64s_repeat0. cbn [u64s]. rewrite app_nil_r.
    apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1|].
    unfold zeros at 1. rewrite repeat_length. replace (A + Z.of_nat (8 * k1)) with (A + 8 * Z.of_nat k1) by lia.
    apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B2|]. rewrite length_le8.
    replace (A + 8 * Z.of_nat k1 + Z.of_nat 8) with (A + 8 * Z.of_nat k1 + 8) by lia. exact B3.
  - rewrite !app_length, !repeat_length. cbn [length]. replace (8 * Z.of_nat (k1 + (1 + k2)))%Z with (8 * (Z.of_nat k1 + 1 + Z.of_nat k2)) by lia. exact HW.
Qed.

(* [comment removed for export] *)

Lemma PRz : forall lo hi A n, In (lo, hi) img_clear_ivs -> lo <= A -> A + n <= hi -> img_pristine M A (A + n).
Proof. intros lo hi A n Hin H1 H2 a Ha. apply (PR lo hi Hin). lia. Qed.

Lemma ctx0 : rmrep_ctx st M.
Proof.
  pose proof (w_secret _ _ _ _ _ _ _ W) as Wsecret. pose proof (w_init _ _ _ _ _ _ _ W) as Winit. pose proof (w_ctr _ _ _ _ _ _ _ W) as Wctr. pose proof (w_fmh _ _ _ _ _ _ _ W) as Wfmh. pose proof (w_am _ _ _ _ _ _ _ W) as Wam. pose proof (w_amc _ _ _ _ _ _ _ W) as Wamc. pose proof (w_amac _ _ _ _ _ _ _ W) as Wamac. pose proof (w_mas _ _ _ _ _ _ _ W) as Wmas. pose proof (w_mah _ _ _ _ _ _ _ W) as Wmah. pose proof (w_mat _ _ _ _ _ _ _ W) as Wmat. pose proof (w_amas _ _ _ _ _ _ _ W) as Wamas. pose proof (w_active44 _ _ _ _ _ _ _ W) as Wact. pose proof (w_usage44 _ _ _ _ _ _ _ W) as Wusg. pose proof (w_seq _ _ _ _ _ _ _ W) as Wseq. pose proof (w_brk _ _ _ _ _ _ _ W) as Wbrk.
  unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count,
    ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas,
    ctx_active, ctx_usage, ctx_seq, ctx_brk, CTX in *.
  unfold rmrep_ctx. rewrite ctx_head_st0, actives_st0, usages_st0, unmap_seqs_st0, bouncess_st0, ctx_tail_st0. unfold RCTX.
  split; [| split; [| split; [| split; [| split]]]].
  - split_cells.
    all: first [apply rw_C8_cell | apply rw_C4_cell]; try apply wr_img; try lia.
    all: lazymatch goal with |- cell _ ?a _ _ => let e := eval cbv in a in change a with e end; assumption.
  - apply u64arr_3; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Z.mul Pos.mul Z.add Pos.add].
    + apply (bytes_zero_img M 0x64538 352); [apply (PRz 0x64538 0x64698); [cbv; tauto| lia| lia] | lia | lia | lia].
    + apply (bytes_at_cell M _ 8 _ Wact); lia.
    + apply (bytes_zero_img M 0x646a0 24); [apply (PRz 0x646a0 0x64818); [cbv; tauto| lia| lia] | lia | lia | lia].
    + apply wr_img; lia.
  - apply u64arr_3; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Z.mul Pos.mul Z.add Pos.add].
    + apply (bytes_zero_img M 0x646b8 352); [apply (PRz 0x646a0 0x64818); [cbv; tauto| lia| lia] | lia | lia | lia].
    + apply (bytes_at_cell M _ 8 _ Wusg); lia.
    + apply (bytes_zero_img M 0x64820 24); [apply (PRz 0x64820 0x64878); [cbv; tauto| lia| lia] | lia | lia | lia].
    + apply wr_img; lia.
  - apply (u8arr_zero_img M 0x64838 32); [apply (PRz 0x64820 0x64878); [cbv; tauto| lia| lia] | lia | lia | lia].
  - apply (u8arr_zero_img M 0x64858 32); [apply (PRz 0x64820 0x64878); [cbv; tauto| lia| lia] | lia | lia | lia].
  - split_cells.
    + apply rw_C1_cell; [exact Wseq| lia| apply wr_img; lia].
    + apply rw_cells_of_bytes; [cbn; repeat split| | apply wr_img; cbn; lia]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_zero_img M 0x64879 7); [apply (PRz 0x64879 0x64880); [cbv; tauto| lia| lia] | lia | lia | lia].
    + apply rw_C8_cell; [exact Wbrk| apply wr_img; lia].
Qed.

Lemma got_img : exists bs, image_bytes s0segs RGOT_SSP 8 = Some bs /\ map bv_unsigned bs = map bv_unsigned (le8 (wz RSSP_GUARD)).
Proof.
  let v := eval vm_compute in (image_bytes s0segs RGOT_SSP 8) in lazymatch v with Some ?l => exists l end.
  split; vm_compute; reflexivity.
Qed.

Lemma globals0 : rmrep_globals M.
Proof.
  pose proof (w_self _ _ _ _ _ _ _ W) as Wself. pose proof (w_canary _ _ _ _ _ _ _ W) as Wcan. pose proof (w_pagesz _ _ _ _ _ _ _ W) as Wpg. pose proof (w_lock80 _ _ _ _ _ _ _ W) as Wlock.
  unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD.
  split; [| split; [| split; [| split]]].
  - apply rw_cells_of_bytes; [exact (conj I I)| | apply wr_img; cbn; lia]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    eapply bytes_at_ext; [apply (bytes_zero_img M 0x644e0 4); [apply (PRz 0x644e0 0x644e8); [cbv; tauto| lia| lia] | lia | lia | lia]|]. vm_compute. reflexivity.
  - apply rw_cells_of_bytes; [exact (conj I I)| | apply wr_img; cbn; lia]. cbn [cells_bytes cbytes app].
    eapply bytes_at_ext; [apply (bytes_zero_img M 0x64473 1); [apply (PRz 0x64471 0x64478); [cbv; tauto| lia| lia] | lia | lia | lia]|]. vm_compute. reflexivity.
  - apply rw_C8_cell; [exact Wpg| apply wr_img; lia].
  - cps_destruct got_img as (bs & HI & HE). apply rw_cells_of_bytes; [exact (conj I I)| |]. 
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- (bytes_eq_u _ _ HE).
      apply (bytes_at_pristine M RGOT_SSP 8 bs); [apply (PRz 0x10000 0x34090); [cbv; tauto| unfold RGOT_SSP; lia| unfold RGOT_SSP; lia] | exact HI | unfold RGOT_SSP; lia | unfold RGOT_SSP; lia].
    + cbn. split; [lia|]. split; [lia|]. intros i Hi.
      destruct (M (wa (205112 + i))) as [v|] eqn:E; [unfold wview; rewrite E; discriminate|].
      rewrite wview_rw_data_pristine; [| unfold rw_data; lia | exact E].
      replace (205112 + i) with (205112 + Z.of_nat (Z.to_nat i)) by lia. rewrite (image_bytes_nth 8 205112 bs (Z.to_nat i) HI) by lia.
      destruct (nth_error bs (Z.to_nat i)) eqn:N; [discriminate|]. apply nth_error_None in N.
      pose proof (image_bytes_length s0segs 8 205112 bs HI). lia.
  - apply rw_C8_cell; [exact Wcan| apply wr_img; lia].
Qed.

Lemma area_off : area + 4096 <= 0x10000 \/ 0x66000 <= area - 4096.
Proof. destruct W. lia. Qed.

Lemma wr_area : forall A n, area <= A -> A + n <= area + 4096 -> 0 <= n -> wr_at s0segs M A n.
Proof.
  intros A n H1 H2 H3. cps_pose W64 as (G1 & G2 & G3 & G4 & G5). apply wr_off; try lia.
  intros i Hi. replace (A + i) with (area + (A - area + i)) by lia. apply (w_area_def _ _ _ _ _ _ _ W). lia.
Qed.
Lemma wr_grp : forall A n, gm <= A -> A + n <= gm + 69632 -> 0 <= n -> wr_at s0segs M A n.
Proof.
  intros A n H1 H2 H3. cps_pose W64 as (G1 & G2 & G3 & G4 & G5). apply wr_off; try lia.
  intros i Hi. replace (A + i) with (gm + (A - gm + i)) by lia. apply (w_grp_def _ _ _ _ _ _ _ W). lia.
Qed.

Lemma get_meta_rec_area : forall k, 0 <= k -> get_meta_rec st (aadd (0%N, 4096) (AREA_HDR + META_SIZE * k)) = if k =? 0 then meta_slot0 else meta0.
Proof.
  intros k Hk. change (get_meta_rec st ?x) with (MR st x). rewrite (st0_MR b area gm).
  unfold aadd, AREA_HDR, META_SIZE, slot0. cbn [fst snd].
  destruct (Z.eqb_spec k 0) as [->|NE]; [reflexivity|].
  destruct (aptr_eqb_spec (0%N, 4096 + (24 + 40 * k)) (0%N, 4120)) as [E|NE2]; [| reflexivity]. exfalso. injection E. lia.
Qed.

Lemma areas0 : rmrep_areas st M.
Proof.
  cps_pose W64 as (G1 & G2 & G3 & G4 & G5). pose proof area_off as AO.
  pose proof (w_area_chk _ _ _ _ _ _ _ W) as Wachk. pose proof (w_area_next _ _ _ _ _ _ _ W) as Wanext. pose proof (w_area_ns _ _ _ _ _ _ _ W) as Wans. pose proof (w_slot0_prev _ _ _ _ _ _ _ W) as Ws0p. pose proof (w_slot0_next _ _ _ _ _ _ _ W) as Ws0n. pose proof (w_slot0_mem _ _ _ _ _ _ _ W) as Ws0m. pose proof (w_slot0_msk _ _ _ _ _ _ _ W) as Ws0k. pose proof (w_slot0_W _ _ _ _ _ _ _ W) as Ws0W. pose proof (w_area_rest _ _ _ _ _ _ _ W) as Warest. pose proof (w_area_def _ _ _ _ _ _ _ W) as Wadef.
  intros a ar H. rewrite (st0_areas b area gm) in H. apply lookup_singleton_Some in H as [<- <-].
  unfold rarea_rep. cbn [a_check a_next a_nslots]. rewrite conc0. replace (area - 4096 + 4096) with area by lia.
  split; [| split].
  - unfold pw, oconc. split1; [apply rw_C8_cell; [exact Wachk| apply wr_area; lia]|].
    split1; [apply rw_C8_cell; [exact Wanext| apply wr_area; lia]|].
    apply rw_cells_of_bytes; [exact (conj I (conj I I))| | apply wr_area; cbn; lia]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    eapply bytes_at_ext; [apply (bytes_at_cell M _ 8 _ Wans); lia|]. vm_compute. reflexivity.
  - intros k Hk. rewrite get_meta_rec_area by lia. unfold AREA_HDR, META_SIZE, NSLOTS in *.
    destruct (Z.eqb_spec k 0) as [->|NE].
    + rewrite meta_cells_slot0. replace (area + 24 + 40 * 0) with (area + 24) by lia.
      split1; [apply rw_C8_cell; [exact Ws0p| apply wr_area; lia]|].
      split1; [apply rw_C8_cell; [exact Ws0n| apply wr_area; lia]|].
      split1; [apply rw_C8_cell; [exact Ws0m| apply wr_area; lia]|].
      change [C4 (wz 0); C4 (wz 0); C8 (wz W64K)] with ([C4 (wz 0); C4 (wz 0)] ++ [C8 (wz W64K)]). apply rw_cells_app; cbn [cells_size csize Nat.add app]; norm_addr.
      * apply rw_cells_of_bytes; [exact (conj I (conj I I))| | apply wr_area; cbn; lia]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        eapply bytes_at_ext; [apply (bytes_at_cell M _ 8 _ Ws0k); lia|]. vm_compute. reflexivity.
      * apply rw_C8_cell; [exact Ws0W| apply wr_area; lia].
    + rewrite meta_cells_meta0. apply rw_cells_of_bytes; [cbn; repeat split| | apply wr_area; cbn; lia].
      eapply bytes_at_ext; [apply (zeros_bytes_at M (area + 24 + 40 * k) 40); try lia|]; [| vm_compute; reflexivity].
      intros i Hi. replace (area + 24 + 40 * k + i) with (area + 64 + (40 * (k - 1) + i)) by lia. apply Warest. lia.
  - apply rw_cells_of_bytes; [cbn; repeat split| | apply wr_area; cbn; lia]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply (zeros_bytes_at M (area + 4064) 32); try lia. intros i Hi. replace (area + 4064 + i) with (area + 64 + (4000 + i)) by lia. apply Warest. lia.
Qed.

Lemma groups0 : rmrep_groups st M.
Proof.
  cps_pose W64 as (G1 & G2 & G3 & G4 & G5).
  pose proof (w_grp_meta _ _ _ _ _ _ _ W) as Wgmeta. pose proof (w_grp_aidx _ _ _ _ _ _ _ W) as Wgaidx.
  intros bb gh H. rewrite (st0_groups b area gm) in H. apply lookup_singleton_Some in H as [<- <-].
  exists (b8 0). cbn [g_meta g_active_idx]. rewrite conc1, Z.add_0_r. split; [| reflexivity].
  unfold pw, oconc, slot0. rewrite conc0. replace (area - 4096 + 4120) with (area + 24) by lia. split_cells.
  - apply rw_C8_cell; [exact Wgmeta| apply wr_grp; lia].
  - apply rw_C1_cell; [exact Wgaidx| lia| apply wr_grp; lia].
Qed.

(* [comment removed for export] *)
Definition KN : list (Z * Z) :=
  [(12,0); (13,224); (14,1); (15,0); (28,0); (29,160); (30,1); (31,0); (65568,0);
   (69623,0); (69624,220); (69625,15); (69626,0); (69627,0); (69628,0); (69629,0); (69630,0); (69631,0)].
Definition KCHK (o : Z) : bool :=
  match cell_read SHX o with Known v => existsb (fun p => (fst p =? o) && (snd p =? v)) KN | Unknown _ => true end.
(* [comment removed for export] *)
Fixpoint zlist (k : nat) (lo : Z) : list Z := match k with O => [] | S k' => lo :: zlist k' (lo + 1) end.
Lemma in_zlist_nat : forall k lo x, lo <= x < lo + Z.of_nat k -> In x (zlist k lo).
Proof.
  induction k as [|k IH]; intros lo x Hx; [lia|]. cbn [zlist]. destruct (Z.eq_dec lo x) as [->|NE]; [left; reflexivity| right]. apply IH. lia.
Qed.
Lemma in_zlist : forall n lo x, lo <= x < lo + n -> In x (zlist (Z.to_nat n) lo).
Proof. intros n lo x H. apply in_zlist_nat. rewrite Z2Nat.id by lia. exact H. Qed.
Lemma kchk_ok : forallb KCHK (zlist (Z.to_nat 69632) 0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Lemma SHX_known : forall o v, 0 <= o < 69632 -> cell_read SHX o = Known v -> In (o, v) KN.
Proof.
  intros o v Ho Hc. pose proof kchk_ok as K. rewrite forallb_forall in K. specialize (K o (in_zlist 69632 0 o ltac:(lia))).
  unfold KCHK in K. rewrite Hc in K. apply existsb_exists in K as (p & Hin & E).
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. destruct p as [p1 p2]. cbn in E1, E2. subst. exact Hin.
Qed.

Lemma shadow0_rep : rmrep_shadow st M.
Proof.
  cps_pose W64 as (G1 & G2 & G3 & G4 & G5).
  pose proof (w_grp_pad _ _ _ _ _ _ _ W) as Wgpad. pose proof (w_enframe _ _ _ _ _ _ _ W) as Wenf. pose proof (w_grp_tail _ _ _ _ _ _ _ W) as Wgtail. pose proof (w_grp_def _ _ _ _ _ _ _ W) as Wgdef.
  destruct Wenf as [P_p P_e P_r P_q Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst P_p P_e P_r P_q.
  specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)). specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
  intros rid r H K. destruct (regs0_lookup b area gm rid r H) as [[-> ->]|[-> ->]]; [| exfalso; clearbody b; destruct b; cbn in K; discriminate].
  unfold rshadow_rep. cbn [r_base r_len]. rewrite round_up_pg_69632. split; [apply wr_grp; lia|].
  intros o v Ho Hc. rewrite (get_shadow_st0 b area gm) in Hc. cbn [N.eqb Pos.eqb] in Hc.
  apply SHX_known in Hc; [| exact Ho]. cbn [KN In] in Hc.
  assert (OFF : forall a, gm <= a -> a + 1 <= 0x10000 \/ 0x66000 <= a) by (intros; lia).
  repeat match type of Hc with
  | _ \/ _ => destruct Hc as [Hc|Hc]
  | False => destruct Hc
  end.
  all: injection Hc as <- <-; split; [| lia].
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 12) with (gm + 9 + 3) by lia. apply Wgpad. lia.
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 13) with (gm + 16 - 3) by lia. exact Ps3.
  - replace (gm + 14) with (gm + 16 - 2 + Z.of_nat 0) by lia. eapply (rdn_byte 2); [exact Ps2| vm_compute; reflexivity| lia| lia| cbn; lia].
  - replace (gm + 15) with (gm + 16 - 2 + Z.of_nat 1) by lia. eapply (rdn_byte 2); [exact Ps2| vm_compute; reflexivity| lia| lia| cbn; lia].
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 28) with (gm + 16 + 16 * 1 - 4) by lia. exact Pm4.
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 29) with (gm + 16 + 16 * 1 - 3) by lia. exact Pm3.
  - replace (gm + 30) with (gm + 16 + 16 * 1 - 2 + Z.of_nat 0) by lia. eapply (rdn_byte 2); [exact Pm2| vm_compute; reflexivity| lia| lia| cbn; lia].
  - replace (gm + 31) with (gm + 16 + 16 * 1 - 2 + Z.of_nat 1) by lia. eapply (rdn_byte 2); [exact Pm2| vm_compute; reflexivity| lia| lia| cbn; lia].
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 65568) with (gm + 16 + 16 * 1 + 65536) by lia. exact Pzr.
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 69623) with (gm + 16 + 69616 - 4 - 5) by lia. exact Pe5.
  - replace (gm + 69624) with (gm + 16 + 69616 - 4 - 4 + Z.of_nat 0) by lia. eapply (rdn_byte 4); [exact Pe4| vm_compute; reflexivity| lia| lia| cbn; lia].
  - replace (gm + 69625) with (gm + 16 + 69616 - 4 - 4 + Z.of_nat 1) by lia. eapply (rdn_byte 4); [exact Pe4| vm_compute; reflexivity| lia| lia| cbn; lia].
  - replace (gm + 69626) with (gm + 16 + 69616 - 4 - 4 + Z.of_nat 2) by lia. eapply (rdn_byte 4); [exact Pe4| vm_compute; reflexivity| lia| lia| cbn; lia].
  - replace (gm + 69627) with (gm + 16 + 69616 - 4 - 4 + Z.of_nat 3) by lia. eapply (rdn_byte 4); [exact Pe4| vm_compute; reflexivity| lia| lia| cbn; lia].
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 69628) with (gm + 69628 + 0) by lia. apply Wgtail. lia.
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 69629) with (gm + 69628 + 1) by lia. apply Wgtail. lia.
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 69630) with (gm + 69628 + 2) by lia. apply Wgtail. lia.
  - apply bytes_at_byte; [| apply OFF; lia| lia| lia]. replace (gm + 69631) with (gm + 69628 + 3) by lia. apply Wgtail. lia.
Qed.

Theorem rmrep0 : rmrep st M.
Proof.
  split; [apply regions_wf0|]. split; [apply ctx0|]. split; [apply globals0|]. split; [apply areas0|]. split; [apply groups0| apply shadow0_rep].
Qed.
End RM0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INJ_strip : forall st, INJ st -> INJ (strip st).
Proof. intros st H a c g. rewrite !active_strip. apply H. Qed.

Lemma TT_strip : forall c st, TT c st -> TT c (strip st).
Proof.
  intros c st [A B C D E F G]. constructor; cbn [s_ctx strip]; assumption.
Qed.

Section ENTRY.
Variables (sp0 gm area brkv mas tid hw : Z) (M : word -> option byte) (VM : VmMaps) (MD : Model).
Hypothesis WLD0 : world0 area gm brkv mas tid hw M.
Hypothesis SP : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis TV : target_vm gm area VM.
Hypothesis TX : target_vmx sp0 gm area brkv mas VM.
Hypothesis AX : auxv0 sp0 M.
Hypothesis ATOP : atop_ok VM.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ACSP : alloc_ceiling <= sp0.
Proof.
  pose proof (target_vmx_alloc_top sp0 gm area brkv mas VM ltac:(lia) TX) as E.
  unfold atop_ok in ATOP. rewrite <- ATOP, E. lia.
Qed.
Hypothesis SMv : m_vmmaps MD = VM.
Hypothesis SMh : m_halted MD = None.
Hypothesis SMl : m_vm_lazy MD = [].
Hypothesis SMm : m_vm_materialized MD = [].

Let b : bool := mas =? 0.
Let st : mstate := st0 b area gm.
Definition s_entry : PState := mkPS (strip st) (area + 4096) (0, 0) tt.

Lemma MB0 : (mas = 0 /\ brkv = area + 4096) \/ (mas = 1 /\ brkv = 2^64 - 1).
Proof.
  cps_destruct TX as (brk0 & mbase & VB & [(M0 & AR & BV & _)|(M1 & BV & a & AR & _)]); [left| right]; split; lia.
Qed.

Lemma DISJM0 : b = false -> area + 4096 <= gm \/ gm + 69632 <= area - 4096.
Proof.
  intros Hb. unfold b in Hb. destruct TV as [TVr TVh TVa TVl TVp TVs TVlim].
  cps_destruct TX as (brk0 & mbase & VB & [(M0 & _)|(M1 & BV & a & AR & EVM)]); [rewrite M0 in Hb; discriminate|].
  pose proof WLD0 as WW. destruct WW. 
  rewrite EVM in TVs. cbn in TVs. inversion TVs as [|p l HF HS E1]; subst.
  apply Forall_inv in HF. unfold iv_disjoint in HF. cbn [fst snd] in HF.
  rewrite !unsigned_lit in HF by lia. lia.
Qed.

Lemma GE0 : geo b area gm. Proof. exact (GE_W _ _ _ _ _ _ _ WLD0). Qed.

Lemma INV_entry : S0_inv s_entry (LB0 gm) M MD.
Proof.
  pose proof GE0 as GE. pose proof DISJM0 as DM. pose proof WLD0 as WW.
  assert (HINVL : INVL x0 st (L0 b area gm) BL0 LS0) by (apply INVL0; [exact GE| exact DM]).
  split.
  - (* [comment removed for export] *)
    exists st, (LB0 gm). split; [apply Permutation_refl|]. split; [reflexivity|]. split; [exact (rmrep0 _ _ _ _ _ _ _ WW MB0 DM)|].
    split.
    + (* [comment removed for export] *) unfold brk_link, ctx. cbn [ps_brk s_entry]. unfold st. rewrite (st0_brk b area gm).
      clearbody b. destruct b; [| exact I]. rewrite (conc0g area gm true). lia.
    + exists (L0 b area gm), LS0, BL0. split; [exact HINVL|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply st0_secret|]. constructor; [| constructor].
      unfold corr1. cbn -[conc Z.add Z.mul]. split; [reflexivity|]. split; [reflexivity|]. unfold st. rewrite (conc1g area gm b). unfold UNIT. lia.
  - (* [comment removed for export] *)
    split; [| split; [| exact I]].
    + exists (L0 b area gm). split; [| split].
      * exists st, BL0, LS0. split; [reflexivity|]. split; [exact HINVL| reflexivity].
      * cbn [ps_brk s_entry]. pose proof (KL_L0 sp0 gm area brkv mas VM MD TV TX SMv SMh SMl GE ATOP) as K. unfold pbrk0 in K. exact K.
      * apply Permutation_refl.
    + cbn. constructor; [intros []| constructor].
Qed.

Lemma VMT_entry : VMT 1 MD.
Proof.
  destruct TV as [TVr TVh TVa TVl TVp TVs TVlim].
  unfold VMT. rewrite SMv. split; [rewrite TVlim; cbv [source_alloc_limit target_alloc_limit]; lia|]. split; [exact SMm|]. split.
  - apply Forall_app. split.
    + rewrite TVr. apply Forall_forall. intros x Hx. apply (in_map wwZ) in Hx. rewrite resv_S0 in Hx. unfold wwZ in Hx. cbn in Hx.
      destruct x as [x1 x2]; cbn in Hx. cbn [fst snd]. destruct Hx as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; rewrite <- E1, <- E2; lia.
    + apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) TVp e He) as X. cbn beta in X. lia.
  - rewrite length_app. assert (length (vm_reserved VM) = 4%nat); [| lia].
    rewrite TVr. rewrite <- (length_map wwZ), resv_S0. reflexivity.
Qed.

Lemma TIGHT_entry : S0_tightP s_entry (LB0 gm) MD.
Proof.
  pose proof GE0 as [GA GG GAR GAI GGR GD]. destruct TV as [TVr TVh TVa TVl TVp TVs TVlim].
  unfold S0_tightP, s_entry, st, LB0. cbn [ps_m length]. change (Z.of_nat 1) with 1.
  split; [reflexivity|]. split; [apply INJ_strip; apply st0_INJ|]. split; [apply TT_strip; cbn [s_ctx strip]; rewrite (st0_amc b area gm); apply st0_TT|].
  split; [cbn [s_ctx strip]; rewrite (st0_amc b area gm); unfold fl_len; cbn [s_ctx strip]; rewrite (st0_fh b area gm); lia|].
  split; [exact VMT_entry|].
  split.
  { intros b0 g _. unfold MR. rewrite get_meta_rec_strip. change (get_meta_rec ?s ?x) with (MR s x). rewrite (st0_MR b area gm).
    destruct (aptr_eqb g slot0); reflexivity. }
  exists [W0 gm]. split; [| split; [| split; [| split; [| split; [| split; [cbn; lia| cbn; intros; lia]]]]]].
  - constructor; [| constructor]. unfold TB. cbn [tw_g tw_rid tw_sc tw_ml tw_base tw_len W0 blk_id fst snd pb0].
    split; [rewrite s_slots_strip, (st0_slots b area gm); apply lookup_insert_eq|].
    split.
    { exists (Some slot0), (Some slot0). split; [unfold MR; rewrite get_meta_rec_strip; change (get_meta_rec ?s ?x) with (MR s x); rewrite (st0_MR b area gm), aptr_eqb_refl; reflexivity|].
      right. split; [lia|]. split; [reflexivity|]. split; [rewrite active_strip, (st0_active b area gm); reflexivity|].
      change (size_class 44) with 4680. unfold UNIT. lia. }
    split; [lia|]. split; [unfold in_pool, ctx; cbn [s_ctx strip]; fold (ctx (st0 b area gm)); intros Hp; apply (proj1 (st0_in_pool b area gm slot0)) in Hp; cps_destruct Hp as (i & Hi & E); unfold slot0 in E; injection E; lia|].
    split; [intros a; rewrite active_strip, (st0_active b area gm); destruct (Z.eqb_spec a 44); [intros _; lia| discriminate]|].
    split; [reflexivity|].
    split; [cbn [s_regions strip st0 set_shadow set_regions]; apply (regs0_1 b area gm)|].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact GG|]. split; [bz_ceil; lia|].
    cbn [s_next_rid strip]. rewrite (st0_next_rid b area gm). lia.
  - cbn. constructor; [intros []| constructor].
  - cbn. constructor; [intros []| constructor].
  - cbn. constructor; [intros []| constructor].
  - constructor; [| constructor]. cbn [tw_base tw_ml W0]. rewrite SMv. change (17 * 4096) with 69632. exact TVh.
Qed.

Lemma AUX_entry : rauxv_ok M sp0.
Proof.
  pose proof ACSP as AC.
  cps_destruct AX as (av & rnd & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & CS & B1 & B2 & B3 & B4).
  exists av, 0, 0, 0, 0, 0, 0, 0, rnd. split; [| split; [| split]].
  - apply rw_C8_cell; [exact C0| apply wr_img; unfold RAUXV_CELL; lia].
  - unfold auxv_keys, le8, wz. repeat match goal with |- _ /\ _ => split end; (eapply bytes_at_cell; [eassumption| lia| lia]).
  - unfold le8, wz. eapply bytes_at_cell; [exact CS| lia| lia].
  - lia.
Qed.

Theorem S0_entry0 :
  ai_inv S0_alloc s_entry (LB0 gm) M MD /\ at_tight S0_tight s_entry (LB0 gm) MD /\ ai_aux S0_alloc M sp0.
Proof. split; [exact INV_entry|]. split; [exact TIGHT_entry| exact AUX_entry]. Qed.
End ENTRY.

(* [comment removed for export] *)
Theorem S0_entry0w : forall (sp0 gm area brkv mas tid hw : Z) (M : word -> option byte) (VM : VmMaps) (MD : Model),
  world0 area gm brkv mas tid hw M -> 0x7fff80000000 <= sp0 <= 0x800000000000 ->
  target_vm gm area VM -> target_vmx sp0 gm area brkv mas VM -> auxv0 sp0 M -> atop_ok VM ->
  m_vmmaps MD = VM -> m_halted MD = None -> m_vm_lazy MD = [] -> m_vm_materialized MD = [] ->
  exists (s : ai_AS S0_alloc) (pb : bid),
    ai_inv S0_alloc s [(pb, gm + 32, 65536)] M MD /\ at_tight S0_tight s [(pb, gm + 32, 65536)] MD /\ ai_aux S0_alloc M sp0.
Proof.
  intros sp0 gm area brkv mas tid hw M VM MD W SP TV TX AX AT SMv SMh SMl SMm.
  exists (s_entry gm area mas), pb0. exact (S0_entry0 sp0 gm area brkv mas tid hw M VM MD W SP TV TX AX AT SMv SMh SMl SMm).
Qed.

(* [comment removed for export] *)
Theorem S0_tight_cover : forall s LB m MD, ai_inv S0_alloc s LB m MD -> at_tight S0_tight s LB MD ->
  ac_c21 S0_cover C21_none s LB /\ exists K0, ac_vm S0_cover K0 s MD /\ (80 <= K0)%nat.
Proof. intros s LB m MD HI HT. exact (S0_tight_cover0 s LB m MD HI HT). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem S0_entry_facts0 : forall (sp0 gm area brkv mas tid hw : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (MD : Model),
  target_pre sp0 gm area brkv mas tid hw content R M -> target_vm gm area VM -> target_vmx sp0 gm area brkv mas VM ->
  auxv0 sp0 M -> atop_ok VM ->
  m_vmmaps MD = VM -> m_halted MD = None -> m_vm_lazy MD = [] -> m_vm_materialized MD = [] ->
  exists (s : ai_AS S0_alloc) (LB : list ablock) (pb : bid) (bufN B : Z),
    ai_inv S0_alloc s LB M MD /\ In (pb, gm + 32, bufN) LB /\ Z.of_nat (length content) <= bufN /\ ai_aux S0_alloc M B /\ sp0 <= B /\
    (forall n, 0 < n < 2 ^ 26 -> ai_sys_ok S0_alloc s LB n MD) /\
    ac_c21 S0_cover C21_none s LB /\ (exists K0, ac_vm S0_cover K0 s MD /\ (80 <= K0)%nat).
Proof.
  intros sp0 gm area brkv mas tid hw content R M VM MD TP TV TX AX AT SMv SMh SMl SMm.
  pose proof (tp_len _ _ _ _ _ _ _ _ _ _ TP) as LEN. pose proof (tp_sp0 _ _ _ _ _ _ _ _ _ _ TP) as SP.
  cps_destruct (S0_entry0 sp0 gm area brkv mas tid hw M VM MD (tp_world _ _ _ _ _ _ _ _ _ _ TP) (proj1 SP) TV TX AX AT SMv SMh SMl SMm) as (H1 & H2 & H3).
  exists (s_entry gm area mas), (LB0 gm), pb0, 65536, sp0.
  split; [exact H1|]. split; [left; reflexivity|]. split; [lia|]. split; [exact H3|]. split; [lia|].
  split; [intros n Hn; apply (at_sys S0_tight H1 H2); unfold MAX_REQ; lia|].
  exact (S0_tight_cover _ _ _ _ H1 H2).
Qed.

End ACeilS1.
