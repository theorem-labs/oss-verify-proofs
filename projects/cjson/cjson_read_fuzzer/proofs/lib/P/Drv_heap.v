(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_Simrel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMalloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_fentry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require AsanCeil.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module KB_drv.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MmapSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.ImplRz.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_m0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Can OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Room OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_Simrel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Sites OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.RF_malloc_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DHEAPx (s : PState) (L : mled) (LBi : list block) (SPB : Z) (m : mem) (mo : Model) : Prop :=
  exists B, RHEAP s LBi m
    /\ MI_Contracts.SIMREL (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map blk_slot LBi) (ld_live L)
    /\ MOK mo /\ rauxv_ok m B /\ SPB <= B /\ vm_reserved (m_vmmaps mo) = segments_reserved psegs.

Definition DHEAP (cs : mstate) (LBi : list block) (SPB : Z) (m : mem) (mo : Model) : Prop :=
  exists s L B, ps_m s = cs /\ RHEAP s LBi m
    /\ MI_Contracts.SIMREL cs L /\ KL L (ps_brk s) mo /\ incl (map blk_slot LBi) (ld_live L)
    /\ MOK mo /\ rauxv_ok m B /\ SPB <= B /\ vm_reserved (m_vmmaps mo) = segments_reserved psegs.

Lemma dheapx_dheap : forall s L LBi SPB m mo, DHEAPx s L LBi SPB m mo -> DHEAP (ps_m s) LBi SPB m mo.
Proof using . intros s L LBi SPB m mo (B & H). exists s, L, B. split; [reflexivity| exact H]. Qed.

Lemma dheap_dheapx : forall cs LBi SPB m mo, DHEAP cs LBi SPB m mo -> exists s L, ps_m s = cs /\ DHEAPx s L LBi SPB m mo.
Proof using . intros cs LBi SPB m mo (s & L & B & Hcs & H). exists s, L. split; [exact Hcs|]. exists B. subst cs. exact H. Qed.

(* [comment removed for export] *)
Definition DHEAP0 (SPB : Z) (m : mem) (mo : Model) : Prop :=
  DHEAPx (ps_init (reservedZ psegs)) (led_init (reservedZ psegs)) [] SPB m mo /\ vm_maps (m_vmmaps mo) = [].

Lemma dheap0_dheap : forall SPB m mo, DHEAP0 SPB m mo -> DHEAP (cs0 (reservedZ psegs)) [] SPB m mo.
Proof using . intros SPB m mo [H _]. apply dheapx_dheap in H. exact H. Qed.

Lemma dheap_lheap : forall cs LBi SPB m mo, DHEAP cs LBi SPB m mo -> LHEAPd SPB (map bview LBi) m mo.
Proof using .
  intros cs LBi SPB m mo (s & L & B & Hcs & HR & Hc & HK & Hi & HM & HA & HS & HV).
  exists s, LBi, B. splits; auto. split; [| exact (RHEAP_slot_nodup _ _ _ HR)]. exists L. rewrite Hcs. auto.
Qed.

Lemma dheap_mok : forall cs LBi SPB m mo, DHEAP cs LBi SPB m mo -> MOK mo.
Proof using . intros cs LBi SPB m mo (s & L & B & H). tclose. Qed.

Lemma dheap_lower : forall cs LBi SPB SPB' m mo, DHEAP cs LBi SPB m mo -> SPB' <= SPB -> DHEAP cs LBi SPB' m mo.
Proof using . intros cs LBi SPB SPB' m mo (s & L & B & H) HS. exists s, L, B. splits; try tclose. lia. Qed.

(* [comment removed for export] *)
Lemma dheap_model : forall cs LBi SPB m mo mo', DHEAP cs LBi SPB m mo -> m_vm mo' = m_vm mo -> m_halted mo' = None -> DHEAP cs LBi SPB m mo'.
Proof using .
  intros cs LBi SPB m mo mo' (s & L & B & Hcs & HR & Hc & HK & Hi & [Hh Hl] & HA & HS & HV) E Hh'.
  exists s, L, B. splits; auto.
  - assert (E1 : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite E; reflexivity).
    eapply KL_vm_eq; [exact HK| | | | | | | | |]; try (rewrite E1; reflexivity).
    + unfold m_vm_lazy. rewrite E. exact (kl_lazy _ _ _ HK).
    + unfold m_vm_materialized. rewrite E. exact (kl_mat _ _ _ HK).
  - split; [exact Hh'|]. unfold m_vm_lazy. rewrite E. exact Hl.
  - unfold m_vmmaps. rewrite E. exact HV.
Qed.

(* [comment removed for export] *)
Lemma dheap_frame : forall cs LBi SPB m m' mo W,
  DHEAP cs LBi SPB m mo -> munch W m m' -> wmono psegs m m' -> Forall (cj_write_ok SPB (map bview LBi)) W -> DHEAP cs LBi SPB m' mo.
Proof using .
  intros cs LBi SPB m m' mo W (s & L & B & Hcs & HR & Hc & HK & Hi & HM & HA & HS & HV) MU WM FW.
  assert (HL : LHEAPd SPB (map bview LBi) m' mo).
  { eapply lhd_frame; [| exact MU| exact WM| exact FW]. exists s, LBi, B. splits; auto. split; [| exact (RHEAP_slot_nodup _ _ _ HR)]. exists L. rewrite Hcs. auto. }
  (* [comment removed for export] *)
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  exists s, L, B. splits; auto.
  - apply (RHEAP_frame_proof s LBi m m' (nonempty_ivs W) HR (munch_nonempty _ _ _ MU) WM).
    apply Forall_forall. intros [lo hi] Hin. unfold nonempty_ivs in Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
    specialize (FW' _ Hin). unfold cj_write_ok, rclient_write_ok in *. cbn [fst snd] in *. (* [comment removed for export] *)
    unfold PERRNO, PGERROR, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *.
    destruct FW' as [E|[ST|[ER|[GE|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    right; right. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exists b. auto.
  - assert (HBc : alloc_ceiling <= B) by (destruct HA as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & HB & _); exact HB).
    eapply rauxv_ok_munch; eauto. intros lo hi Hin Hlt. specialize (FW' _ Hin).
    unfold cj_write_ok in FW'. cbn [fst snd] in FW'. (* [comment removed for export] *) unfold PERRNO, PGERROR, RLIBC, alloc_ceiling in *.
    destruct FW' as [E|[ST|[ER|[GE|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-).
    pose proof (RHEAP_block_range_proof s LBi m b HR Hb) as (R1 & R2 & R3 & R4 & R5). unfold alloc_ceiling in R4. lia.
Qed.

Lemma dheap_perm : forall cs LBi LBi' SPB m mo, DHEAP cs LBi SPB m mo -> Permutation LBi LBi' -> DHEAP cs LBi' SPB m mo.
Proof using .
  intros cs LBi LBi' SPB m mo (s & L & B & Hcs & HR & Hc & HK & Hi & HM & HA & HS & HV) HP.
  exists s, L, B. splits; auto.
  - eapply RHEAP_perm; eauto.
  - intros c Hc'. apply Hi. apply in_map_iff in Hc' as (b & <- & Hb). apply in_map. eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb].
Qed.

Lemma dheap_block_range : forall cs LBi SPB m mo b, DHEAP cs LBi SPB m mo -> In b LBi -> rblock_range (blk_addr b) (blk_size b).
Proof. intros cs LBi SPB m mo b (s & L & B & Hcs & HR & _) Hb. eapply RHEAP_block_range_proof; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem dheap_init : forall (m : mem) (auxv : word) (B : Z) (mo : Model) (brk : word) lim mbase (sp0 : word),
  (forall a : word, 0x53b88 <= bv_unsigned a < 0x53f30 -> m a = None) ->
  rw_cells psegs m 0x53b18 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0x53b20 [C8 auxv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                            C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
  rw_cells psegs m 0x224e8 [C8 (Z_to_bv 64 0x53af8)] ->
  rw_cells psegs m 0x53af8 [C8 ssp_guard_val] ->   (* [comment removed for export] *)
  mem_inv psegs m ->
  rauxv_ok m B ->
  m_vmmaps mo = mkVmMapsFull (segments_reserved psegs) [] [] brk brk lim mbase sp0 ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] -> m_halted mo = None ->
  valid_brk psegs brk -> drv_limit <= lim ->
  bv_unsigned sp0 - stack_max_size = alloc_ceiling ->   (* [comment removed for export] *)
  DHEAP0 B m mo.
Proof using .
  intros m auxv B mo brk lim mbase sp0 NONE LC LC2 GOT GUARD MI HA Evm Hl Hm Hh (V1 & V2 & V3) Hlim Htop.
  destruct (RHEAP_init_proof m auxv NONE LC LC2 GOT GUARD MI) as [HR _].
  assert (Hrtop : reserved_top (segments_reserved psegs) = 0x55000) by (vm_compute; reflexivity).
  rewrite Hrtop in V1, V2. rewrite page_size_eq in V3. unfold brk_aslr_max in V2.
  pose proof (@KL_init ACEIL (segments_reserved psegs) brk mo lim mbase sp0 Evm Hl Hm ltac:(lia) V3 ltac:(lia)) as HK.
  specialize (HK ltac:(intros e He; pose proof (reserved_top_ge _ _ He); lia) Hlim Htop). rewrite <- reservedZ_wwZ in HK.
  split; [| rewrite Evm; reflexivity].
  exists B. splits; auto.
  - apply simrel_init.
  - intros c [].
  - split; assumption.
  - lia.
  - rewrite Evm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MLEAF (cs : mstate) (n : Z) (cs' : mstate) (r : option cptr) : Prop :=
  exists ans, follow (cmalloc cs n) ans = Some (cs', r).
Definition FLEAF (cs : mstate) (c : cptr) (cs' : mstate) : Prop :=
  exists ans, follow (cfree cs (Some c)) ans = Some cs'.

Section Stmts.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model).

Definition drv_regs_post (m' : mem) (ms' : machine_state) (a0' : word) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs).

(* [comment removed for export] *)
Theorem drv_malloc_x : forall s L LBi SPB (n lo : Z) (errv : word) (TB : TSet), let cs := ps_m s in
  DHEAPx s L LBi SPB m mo ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CJ_iface.RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> a0 = wz n -> 0 <= n < 2^32 ->
  (forall p sf mof, tcan (raw_malloc n s) mo (fun x mo1 => x = Ok (p, sf) /\ mo1 = mof) -> is_none p = false) ->
  (forall ms' mo' m' errv' cs' c off A junk,
      drv_regs_post m' ms' (wz A) -> vm_only mo mo' ->
      mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' PERRNO [C4 errv'] ->
      cj_pres (map bview LBi) (bv_unsigned sp) m m' ->
      rblock_range A n -> ~ In A (map blk_addr LBi) -> rw_cells psegs m' A [CB (Z.to_nat n) junk] ->
      DHEAP cs' (((c, off), A, n) :: LBi) SPB m' mo' -> MLEAF cs n cs' (Some c) ->
      realizes psegs (mkCfg ms' mo') TB) ->
  realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz PMALLOC) fc None m (seg_rom psegs)) mo)
           TB.
Proof using .
  intros s L LBi SPB n lo errv TB cs (B & HR & Hc & HK & Hi & HM & HA & HS & HV) HSP ST Hlo Hlo2 ER MI Htp Ha0 Hn NN KB.
  (* [comment removed for export] *)
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi n lo B errv
                HR HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Hn) as Himpl.
  subst cs. assert (Hn0 : 0 <= n) by lia.
  pose proof (simrel_malloc_contract _ _ _ Hc Hn0) as CT.
  assert (Hpre : s = s /\ mo = mo /\ KL L (ps_brk s) mo) by auto.
  pose proof (raw_malloc_spec L s mo n _ CT s mo Hpre) as Hwf.
  eapply (implM_rz_only psegs (raw_malloc n) s _ _ (fun p => is_none (fst p)) TB _ mo Himpl HM Hwf).
  - (* [comment removed for export] *)
    eapply etwf_mono; [apply (etwf_reach _ mo _ (fun p _ => is_none (fst p) = false) Hwf)|].
    + intros [p sf] mof Hcan. cbn [fst]. exact (NN p sf mof Hcan).
    + intros a mo1 [_ H]. exact H.
  - intros r s' ms' mo' HQ HRr HM' Hsome. cbn [fst snd] in HRr, Hsome. destruct r as [[c off]|]; [|discriminate].
    destruct HRr as (L' & rc & Hp & HPost & HK' & Erc & Hfa & Hso & Hvo). destruct rc as [c'|]; [|discriminate]. injection Erc as Ec Eoff. subst c'.
    destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ER' & HA' & HP & _ & _ & Hr).
    destruct Hr as (A & junk & -> & HRng & HR' & RW & _).
    apply (KB _ mo' m' errv' (ps_m s') c off A junk).
    + eexists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. reflexivity.
    + exact Hvo.
    + exact MI'.
    + exact ST'.
    + rewrite Htp, errno_addr_PTP in ER'; exact ER'.
    + apply cj_pres_of_rheap_pres. exact HP.
    + exact HRng.
    + pose proof (RHEAP_addr_nodup _ _ _ HR') as ND. cbn [map blk_addr fst snd] in ND. inversion ND; assumption.
    + exact RW.
    + exists s', (set_live (c :: ld_live L') L'), B. split; [reflexivity|]. split; [exact HR'|].
      split; [exact (simrel_malloc_step _ _ _ _ _ _ Hc Hn0 Hp)|]. split; [apply KL_set_live; exact HK'|].
      split. { cbn [map blk_slot fst ld_live set_live]. intros x [<-|Hx]; [left; reflexivity| right]. rewrite (cpath_live _ _ _ _ Hp). apply Hi. exact Hx. }
      splits; auto. rewrite <- HV. apply (KL_resv_eq L (ps_brk s) mo L' (ps_brk s') mo' HK HK'). apply (MallocFacts_inv.cpath_resv _ _ _ _ Hp).
    + destruct (MI_Contracts.cpath_follow _ _ _ _ Hp) as (ans & Hf & _). exists ans. exact Hf.
Qed.

(* [comment removed for export] *)
Theorem drv_malloc : forall cs LBi SPB (n lo : Z) (errv : word) (TB : TSet),
  DHEAP cs LBi SPB m mo ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CJ_iface.RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> a0 = wz n -> 0 <= n < 2^32 ->
  never_none cs n mo ->
  (forall ms' mo' m' errv' cs' c off A junk,
      drv_regs_post m' ms' (wz A) -> vm_only mo mo' ->
      mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' PERRNO [C4 errv'] ->
      cj_pres (map bview LBi) (bv_unsigned sp) m m' ->
      rblock_range A n -> ~ In A (map blk_addr LBi) -> rw_cells psegs m' A [CB (Z.to_nat n) junk] ->
      DHEAP cs' (((c, off), A, n) :: LBi) SPB m' mo' -> MLEAF cs n cs' (Some c) ->
      realizes psegs (mkCfg ms' mo') TB) ->
  realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz PMALLOC) fc None m (seg_rom psegs)) mo)
           TB.
Proof using .
  intros cs LBi SPB n lo errv TB HD HSP ST Hlo Hlo2 ER MI Htp Ha0 Hn NN KB.
  destruct (dheap_dheapx _ _ _ _ _ HD) as (s & L & <- & HX). pose proof HX as (B & HR & Hc & HK & _).
  eapply (drv_malloc_x s L LBi SPB n lo errv TB HX); eauto.
Qed.

(* [comment removed for export] *)
Lemma img_reserved_small : Forall (fun p : word * word => bv_unsigned (snd p) <= 2^18) (segments_reserved psegs)
  /\ Z.of_nat (length (segments_reserved psegs)) = 4.
Proof.
  split; [| vm_compute; reflexivity].
  assert (E : map (fun p : word * word => bv_unsigned (snd p)) (segments_reserved psegs) = [8192; 65536; 4096; 204800]) by (vm_compute; reflexivity).
  apply Forall_forall. intros p Hp. apply (in_map (fun p : word * word => bv_unsigned (snd p))) in Hp. rewrite E in Hp.
  cbn in Hp. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem drv_malloc_site : forall cs LBi SPB (n lo hi0 lo0 : Z) (errv : word) (TB : TSet),
  DHEAP cs LBi SPB m mo -> one_mmap_site cs n lo0 hi0 -> 0 < lo0 -> hi0 + 4096 <= 2^27 - 4096 -> cs_small cs ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CJ_iface.RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> a0 = wz n -> 0 <= n < 2^32 ->
  (forall ms' mo' m' errv' cs' c off A junk,
      drv_regs_post m' ms' (wz A) -> vm_only mo mo' ->
      mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' PERRNO [C4 errv'] ->
      cj_pres (map bview LBi) (bv_unsigned sp) m m' ->
      rblock_range A n -> ~ In A (map blk_addr LBi) -> rw_cells psegs m' A [CB (Z.to_nat n) junk] ->
      DHEAP cs' (((c, off), A, n) :: LBi) SPB m' mo' -> MLEAF cs n cs' (Some c) ->
      realizes psegs (mkCfg ms' mo') TB) ->
  realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz PMALLOC) fc None m (seg_rom psegs)) mo)
           TB.
Proof using .
  intros cs LBi SPB n lo hi0 lo0 errv TB HD Hsite Hlo0 Hhi0 [HS1 HS2] HSP ST Hlo Hlo2 ER MI Htp Ha0 Hn KB.
  destruct (dheap_dheapx _ _ _ _ _ HD) as (s & L & <- & HX). pose proof HX as (B & HR & Hc & HK & _ & _ & _ & _ & Hresv).
  assert (HLS : led_small L (2^27 - 4096) 8).
  { apply (led_small_of_cs (ps_m s) L); [exact Hc| exact HS1| unfold PGSZ; lia| lia]. }
  destruct img_reserved_small as [PR1 PR2].
  destruct (KL_room_app L (ps_brk s) mo (2^27 - 4096) 8 4 HK HLS) as (F1 & F2 & F3);
    [rewrite Hresv; eapply Forall_impl; [| exact PR1]; cbn; intros; lia| rewrite Hresv; lia|].
  assert (A0 : 0 <= n) by lia.
  assert (A1 : (2^27 - 4096) mod 4096 = 0) by reflexivity.
  assert (A2 : Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= 12) by lia.
  (* [comment removed for export] *)
  assert (A3 : AsanCeil.bottomup_floor + 12 * (2 * (2^27 - 4096)) + (2^27 - 4096) <= alloc_top (m_vmmaps mo)).
  { rewrite (kl_top _ _ _ HK). rewrite AsanCeil.bottomup_floor_val. pose proof (@alloc_ceiling_lo ACEIL). lia. }
  assert (A3L : alloc_top (m_vmmaps mo) <= alloc_ceiling) by (rewrite (kl_top _ _ _ HK); lia).
  assert (A4 : vm_backing_used mo + (2^27 - 4096) <= vm_limit (m_vmmaps mo)).
  { pose proof (vm_backing_used_le_live mo (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK)). pose proof (kl_lim _ _ _ HK). unfold drv_limit in *. lia. }
  eapply (drv_malloc_x s L LBi SPB n lo errv TB HX); eauto.
  exact (site_never_none (ps_m s) n lo0 hi0 mo (2^27 - 4096) 12 Hsite A0 Hlo0 Hhi0 A1 F1 A2 A3 A4 s L eq_refl Hc HK).
Qed.

(* [comment removed for export] *)
Theorem drv_malloc_first : forall SPB (lo : Z) (errv : word) (TB : TSet),
  DHEAP0 SPB m mo ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CJ_iface.RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> a0 = wz 65536 ->
  (forall ms' mo' m' errv' cs' c off A junk,
      drv_regs_post m' ms' (wz A) -> vm_only mo mo' ->
      mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' PERRNO [C4 errv'] ->
      cj_pres [] (bv_unsigned sp) m m' ->
      rblock_range A 65536 -> rw_cells psegs m' A [CB (Z.to_nat 65536) junk] ->
      DHEAP cs' [((c, off), A, 65536)] SPB m' mo' -> MLEAF (cs0 (reservedZ psegs)) 65536 cs' (Some c) ->
      realizes psegs (mkCfg ms' mo') TB) ->
  realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz PMALLOC) fc None m (seg_rom psegs)) mo)
           TB.
Proof.
  intros SPB lo errv TB [HX Hmaps] HSP ST Hlo Hlo2 ER MI Htp Ha0 KB.
  pose proof HX as (B & HR & Hc & HK & _ & _ & _ & _ & Hresv). destruct img_reserved_small as [PR1 PR2].
  eapply (drv_malloc_x _ _ [] SPB 65536 lo errv TB HX); eauto.
  - lia.
  - apply (m0_never_none (reservedZ psegs)); [reflexivity| reflexivity| exact HK| rewrite Hresv; exact PR1| rewrite Hresv; lia].
Qed.

(* [comment removed for export] *)
Theorem drv_free : forall cs LBi SPB (p : bptr) (A n lo : Z) (errv : word) (T : TSet),
  DHEAP cs LBi SPB m mo -> In (p, A, n) LBi ->
  bv_unsigned sp <= SPB ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CJ_iface.RMALLOC_STACK ->
  rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> a0 = wz A ->
  (forall ms' mo' m' cs' a0',
      drv_regs_post m' ms' a0' -> vm_only mo mo' ->
      mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' PERRNO [C4 errv] ->
      cj_pres (map bview (lb_remove p LBi)) (bv_unsigned sp) m m' ->
      DHEAP cs' (lb_remove p LBi) SPB m' mo' -> FLEAF cs (fst p) cs' ->
      realizes psegs (mkCfg ms' mo') T) ->
  realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz PFREE) fc None m (seg_rom psegs)) mo) T.
Proof using .
  intros cs LBi SPB p A n lo errv T (s & L & B & Hcs & HR & Hc & HK & Hi & HM & HA & HS & HV) Hin HSP ST Hlo Hlo2 ER MI Htp Ha0 K.
  (* [comment removed for export] *)
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi p A n lo B errv
                HR Hin HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0) as Himpl.
  subst cs.
  assert (Hlive : In (fst p) (ld_live L)). { apply Hi. apply in_map_iff. exists (p, A, n). auto. }
  assert (Hpre : s = s /\ mo = mo /\ KL L (ps_brk s) mo) by auto.
  pose proof (raw_free_spec L s mo p _ (simrel_free_contract _ _ _ Hc Hlive) s mo Hpre) as Hwf.
  eapply (implM_rz_same psegs (raw_free p) s _ _ T _ mo Himpl HM Hwf).
  intros [] s' ms' mo' HQ HRr HM'. cbn [fst snd] in HRr.
  destruct HRr as (L' & Hp & HK' & Hfa & Hso & Hvo).
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ER' & HA' & HP & _ & _ & HR').
  apply (K _ mo' m' (ps_m s') a0').
  - eexists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. reflexivity.
  - exact Hvo.
  - exact MI'.
  - exact ST'.
  - rewrite Htp, errno_addr_PTP in ER'; exact ER'.
  - apply cj_pres_of_rheap_pres. exact HP.
  - exists s', (set_live (ap_remove (fst p) (ld_live L')) L'), B. split; [reflexivity|]. split; [exact HR'|].
    split; [exact (simrel_free_step _ _ _ _ _ Hc Hlive Hp)|]. split; [apply KL_set_live; exact HK'|]. split; [| auto].
    destruct (lb_remove_views LBi p A n (RHEAP_slot_nodup _ _ _ HR) (RHEAP_addr_nodup _ _ _ HR) Hin) as (V1 & _ & _).
    rewrite V1. cbn [ld_live set_live]. rewrite (cpath_live _ _ _ _ Hp).
    2:{ splits; auto. rewrite <- HV. apply (KL_resv_eq L (ps_brk s) mo L' (ps_brk s') mo' HK HK'). apply (MallocFacts_inv.cpath_resv _ _ _ _ Hp). }
    intros x Hx. apply in_ap_remove; [apply Hi; eapply ap_remove_In; exact Hx|].
    intros ->. exact (ap_remove_notin_self _ _ (RHEAP_slot_nodup _ _ _ HR) Hx).
  - destruct (MI_Contracts.cpath_follow _ _ _ _ Hp) as (ans & Hf & _). exists ans. exact Hf.
Qed.

End Stmts.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End KB_drv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Frame SCPS NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.ImplRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_A Malloc_iface Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv MallocFacts_inv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog KInv KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_m0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MEX_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KRaw KB_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Can.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Room.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_Simrel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Sites.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_SiteM0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMalloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_inst0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.RF_malloc_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_fentry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_iface CJ_heap_inst0.
Import KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_pad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition drv_write_ok (SPB : Z) (LB : list cblock) (iv : Z * Z) : Prop :=
  snd iv <= fst iv                                                                      (* [comment removed for export] *)
  \/ (alloc_ceiling <= fst iv /\ snd iv <= SPB)                                         (* [comment removed for export] *)
  \/ (0x22000 <= fst iv /\ snd iv <= RLIBC /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv)
                        /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))               (* [comment removed for export] *)
  \/ (RCTX + 928 <= fst iv /\ snd iv <= 0x55000)                                        (* [comment removed for export] *)
  \/ (exists A n, In (A, n) LB /\ A <= fst iv /\ snd iv <= A + n).                      (* [comment removed for export] *)

Lemma cj_write_ok_drv : forall SPB LB iv, cj_write_ok SPB LB iv -> drv_write_ok SPB LB iv.
Proof using .
  intros SPB LB [lo hi] H. unfold cj_write_ok, drv_write_ok, PERRNO, PGERROR, RLIBC, RSSP_GUARD, RGOT_SSP in *. cbn [fst snd] in *.
  (* [comment removed for export] *)
  destruct H as [H|[H|[H|[H|H]]]]; [lia| right; left; lia| right; right; left; lia| right; right; left; lia| right; right; right; right; exact H].
Qed.

Lemma rauxv_ok_munch2 : forall W m m' B LB, munch W m m' -> wmono psegs m m' -> rauxv_ok m B ->
  Forall (drv_write_ok B LB) W ->
  (forall A n, In (A, n) LB -> rblock_range A n) ->
  rauxv_ok m' B.
Proof using .
  intros W m m' B LB HM HW (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H1 & H2 & H3 & H4) FW HLB.   (* [comment removed for export] *)
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  assert (D : forall lo hi, In (lo, hi) W -> lo < hi ->
             (alloc_ceiling <= lo /\ hi <= B) \/ (hi <= RLIBC) \/ (RCTX + 928 <= lo /\ hi <= 0x55000)
             \/ (hi <= alloc_ceiling /\ (hi <= 0x10000 \/ 0x55000 <= lo))).
  { intros lo hi Hin Hlt. specialize (FW' _ Hin). unfold drv_write_ok in FW'. cbn [fst snd] in FW'.
    destruct FW' as [E|[E|[E|[E|(A & n & HinB & EA & EB)]]]]; [lia| left; lia| right; left; lia| right; right; left; lia|].
    right; right; right. pose proof (HLB _ _ HinB) as (R1 & R2 & R3 & R4 & R5). lia. }
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H4]]].
  - eapply rw_cells_munch; eauto. cbn [cells_size csize Nat.add]. unfold RAUXV_CELL. intros lo hi Hin Hlt.
    destruct (D lo hi Hin Hlt) as [E|[E|[E|E]]]; unfold alloc_ceiling, RLIBC, RCTX in *; lia.
  - eapply bytes_at_munch; eauto. intros lo hi Hin Hlt. rewrite u64s_length. unfold auxv_list. rewrite length_map. cbn [length Nat.mul Nat.add].
    destruct (D lo hi Hin Hlt) as [E|[E|[E|E]]]; unfold alloc_ceiling, RLIBC, RCTX in *; lia.
  - eapply bytes_at_munch; eauto. intros lo hi Hin Hlt. rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. (* [comment removed for export] *)
    destruct (D lo hi Hin Hlt) as [E|[E|[E|E]]]; unfold alloc_ceiling, RLIBC, RCTX in *; lia.
Qed.

Lemma lhd_frame_ext : forall SPB LB m m' mo W,
  LHEAPd SPB LB m mo -> munch W m m' -> wmono psegs m m' -> Forall (drv_write_ok SPB LB) W -> LHEAPd SPB LB m' mo.
Proof using .
  intros SPB LB m m' mo W (s & LBi & B & HR & -> & HO & HM & HA & HS) MU WM FW.
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  assert (HB : alloc_ceiling <= B) by (destruct HA as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & HB & _); exact HB).
  exists s, LBi, B. splits; auto.
  - apply (RHEAP_frame_proof s LBi m m' (nonempty_ivs W) HR (munch_nonempty _ _ _ MU) WM).
    apply Forall_forall. intros [lo hi] Hin. unfold nonempty_ivs in Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
    specialize (FW' _ Hin). unfold drv_write_ok, rclient_write_ok in *. cbn [fst snd] in *.
    unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *.
    destruct FW' as [E|[ST|[DA|[HI|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    right; right. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exists b. auto.
  - eapply (rauxv_ok_munch2 W m m' B (map bview LBi) MU WM HA).
    + eapply Forall_impl; [| exact FW]. intros iv Hiv. unfold drv_write_ok in *.
      destruct Hiv as [E|[E|[E|[E|E]]]]; [left; exact E| right; left; lia| right; right; left; exact E| right; right; right; left; exact E| right; right; right; right; exact E].
    + intros A n HinB. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exact (RHEAP_block_range_proof s LBi m b HR Hb).
Qed.

Lemma dheap_frame_ext : forall cs LBi SPB m m' mo W,
  DHEAP cs LBi SPB m mo -> munch W m m' -> wmono psegs m m' -> Forall (drv_write_ok SPB (map bview LBi)) W -> DHEAP cs LBi SPB m' mo.
Proof using .
  intros cs LBi SPB m m' mo W (s & L & B & Hcs & HR & Hc & HK & Hi & HM & HA & HS & HV) MU WM FW.
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  assert (HB : alloc_ceiling <= B) by (destruct HA as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & HB & _); exact HB).
  exists s, L, B. splits; auto.
  - apply (RHEAP_frame_proof s LBi m m' (nonempty_ivs W) HR (munch_nonempty _ _ _ MU) WM).
    apply Forall_forall. intros [lo hi] Hin. unfold nonempty_ivs in Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
    specialize (FW' _ Hin). unfold drv_write_ok, rclient_write_ok in *. cbn [fst snd] in *.
    unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *.
    destruct FW' as [E|[ST|[DA|[HI|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    right; right. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exists b. auto.
  - eapply (rauxv_ok_munch2 W m m' B (map bview LBi) MU WM HA).
    + eapply Forall_impl; [| exact FW]. intros iv Hiv. unfold drv_write_ok in *.
      destruct Hiv as [E|[E|[E|[E|E]]]]; [left; exact E| right; left; lia| right; right; left; exact E| right; right; right; left; exact E| right; right; right; right; exact E].
    + intros A n HinB. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exact (RHEAP_block_range_proof s LBi m b HR Hb).
Qed.

(* [comment removed for export] *)
Lemma dheapx_frame_ext : forall s L LBi SPB m m' mo W,
  DHEAPx s L LBi SPB m mo -> munch W m m' -> wmono psegs m m' -> Forall (drv_write_ok SPB (map bview LBi)) W -> DHEAPx s L LBi SPB m' mo.
Proof.
  intros s L LBi SPB m m' mo W (B & HR & Hc & HK & Hi & HM & HA & HS & HV) MU WM FW.
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  exists B. splits; auto.
  - apply (RHEAP_frame_proof s LBi m m' (nonempty_ivs W) HR (munch_nonempty _ _ _ MU) WM).
    apply Forall_forall. intros [lo hi] Hin. unfold nonempty_ivs in Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
    specialize (FW' _ Hin). unfold drv_write_ok, rclient_write_ok in *. cbn [fst snd] in *.
    unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *.
    destruct FW' as [E|[ST|[DA|[HI|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    right; right. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exists b. auto.
  - eapply (rauxv_ok_munch2 W m m' B (map bview LBi) MU WM HA).
    + eapply Forall_impl; [| exact FW]. intros iv Hiv. unfold drv_write_ok in *.
      destruct Hiv as [E|[E|[E|[E|E]]]]; [left; exact E| right; left; lia| right; right; left; exact E| right; right; right; left; exact E| right; right; right; right; exact E].
    + intros A n HinB. destruct (in_bview _ _ _ HinB) as (b & Hb & <- & <-). exact (RHEAP_block_range_proof s LBi m b HR Hb).
Qed.

Lemma dheapx_model : forall s L LBi SPB m mo mo', DHEAPx s L LBi SPB m mo -> m_vm mo' = m_vm mo -> m_halted mo' = None -> DHEAPx s L LBi SPB m mo'.
Proof using .
  intros s L LBi SPB m mo mo' (B & HR & Hc & HK & Hi & [Hh Hl] & HA & HS & HV) E Hh'.
  exists B. splits; auto.
  - assert (E1 : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite E; reflexivity).
    eapply KL_vm_eq; [exact HK| | | | | | | | |]; try (rewrite E1; reflexivity).
    + unfold m_vm_lazy. rewrite E. exact (kl_lazy _ _ _ HK).
    + unfold m_vm_materialized. rewrite E. exact (kl_mat _ _ _ HK).
  - split; [exact Hh'|]. unfold m_vm_lazy. rewrite E. exact Hl.
  - unfold m_vmmaps. rewrite E. exact HV.
Qed.

Lemma dheap0_frame_ext : forall SPB m m' mo W,
  DHEAP0 SPB m mo -> munch W m m' -> wmono psegs m m' -> Forall (drv_write_ok SPB []) W -> DHEAP0 SPB m' mo.
Proof. intros SPB m m' mo W [HX HV] MU WM FW. split; [| exact HV]. eapply dheapx_frame_ext; eauto. Qed.

Lemma dheap0_model : forall SPB m mo mo', DHEAP0 SPB m mo -> m_vm mo' = m_vm mo -> m_halted mo' = None -> DHEAP0 SPB m mo'.
Proof using .
  intros SPB m mo mo' [HX HV] E Hh. split; [eapply dheapx_model; eauto|]. unfold m_vmmaps in *. rewrite E. exact HV.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma img_mrd_some : forall m (a : Z),
  match seg_rom psegs (wa a) with Some _ => True | None => False end -> exists b, mrd psegs m (wa a) = Some b.
Proof using .
  intros m a H. unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|].
  destruct (seg_rom psegs (wa a)) as [b|]; [exists b; reflexivity| destruct H].
Qed.

(* [comment removed for export] *)
Lemma lhd_libc_cells : forall SPB LB m mo, LHEAPd SPB LB m mo ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m 0x53b18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof using .
  intros SPB LB m mo (s & LBi & B & (st & LB0 & _ & _ & MR & _) & _).
  destruct MR as (_ & _ & (_ & NL & _ & _ & _) & _). unfold RNEED_LOCKS in NL.
  destruct (img_mrd_some m 0x53b18 ltac:(vm_compute; exact I)) as [b0 H0].
  destruct (img_mrd_some m 0x53b19 ltac:(vm_compute; exact I)) as [b1 H1].
  destruct (img_mrd_some m 0x53b1a ltac:(vm_compute; exact I)) as [b2 H2].
  destruct (img_mrd_some m 0x53b1c ltac:(vm_compute; exact I)) as [c0 G0].
  destruct (img_mrd_some m 0x53b1d ltac:(vm_compute; exact I)) as [c1 G1].
  destruct (img_mrd_some m 0x53b1e ltac:(vm_compute; exact I)) as [c2 G2].
  destruct (img_mrd_some m 0x53b1f ltac:(vm_compute; exact I)) as [c3 G3].
  pose proof (bytes_le_to_Z_bound [c0; c1; c2; c3]) as BB. pose proof (bytes_le_to_Z_nonneg [c0; c1; c2; c3]) as BN.
  change (2 ^ (8 * Z.of_nat (length [c0; c1; c2; c3]))) with 4294967296 in BB.
  exists b0, b1, b2, (Z_to_bv 64 (bytes_le_to_Z [c0; c1; c2; c3])).
  destruct NL as [[_ NB] NW]. destruct NB as (_ & _ & NB1). specialize (NB1 0%nat ltac:(cbn; lia)).
  cbn [cells_bytes cbytes app nth_error] in NB1. rewrite Z.add_0_r in NB1.
  assert (L4 : le4 (Z_to_bv 64 (bytes_le_to_Z [c0; c1; c2; c3])) = [c0; c1; c2; c3]).
  { unfold le4. set (z := bytes_le_to_Z [c0; c1; c2; c3]) in *. rewrite unsigned_lit by lia. subst z. apply (StrFun.Z_to_le_bytes_to_Z [c0; c1; c2; c3]). }
  split; [split|].
  - cbn. repeat split; exact I.
  - cbn [cells_bytes cbytes app]. rewrite L4. cbn [app]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; try lia; rewrite ?Z.add_0_r.
    + exact H0. + exact H1. + exact H2. + exact NB1. + exact G0. + exact G1. + exact G2. + exact G3.
  - (* [comment removed for export] *)
    cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi.
    assert (WB : forall k : nat, (k < 8)%nat -> wview psegs (fun _ => None) (wa (0x53b18 + Z.of_nat k)) <> None).
    { intros k Hk. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia; vm_compute; discriminate. }
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    pose proof (WB (Z.to_nat i) ltac:(lia)) as W0. unfold wview in *. destruct (m (wa (0x53b18 + Z.of_nat (Z.to_nat i)))); [discriminate| exact W0].
Qed.

(* [comment removed for export] *)
Lemma lhd_ssp0 : forall SPB LB m mo, LHEAPd SPB LB m mo -> ssp_cells m ssp_guard_val.
Proof using .
  intros SPB LB m mo (s & LBi & B & (st & LB0 & _ & _ & MR & _) & _).
  destruct MR as (_ & _ & (_ & _ & _ & G1 & G2) & _). split; [exact G1| exact G2].
Qed.

Lemma dheap_libc_cells : forall cs LBi SPB m mo, DHEAP cs LBi SPB m mo ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m 0x53b18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof. intros cs LBi SPB m mo H. eapply lhd_libc_cells. eapply dheap_lheap. exact H. Qed.

Lemma dheap_ssp0 : forall cs LBi SPB m mo, DHEAP cs LBi SPB m mo -> ssp_cells m ssp_guard_val.
Proof using . intros cs LBi SPB m mo H. eapply lhd_ssp0. eapply dheap_lheap. exact H. Qed.

Lemma dheap0_libc_cells : forall SPB m mo, DHEAP0 SPB m mo ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m 0x53b18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof. intros SPB m mo H. eapply dheap_libc_cells. apply dheap0_dheap. exact H. Qed.

Lemma dheap0_ssp0 : forall SPB m mo, DHEAP0 SPB m mo -> ssp_cells m ssp_guard_val.
Proof using . intros SPB m mo H. eapply dheap_ssp0. apply dheap0_dheap. exact H. Qed.

(* [comment removed for export] *)
Ltac drv_write_ok_tac :=
  unfold drv_write_ok, alloc_ceiling, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, PERRNO, PGERROR; cbn [fst snd];
  first [ left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dheap_blocks_disjoint : forall cs LBi SPB m mo A1 n1 A2 n2,
  DHEAP cs LBi SPB m mo -> In (A1, n1) (map bview LBi) -> In (A2, n2) (map bview LBi) -> A1 <> A2 -> A1 + n1 <= A2 \/ A2 + n2 <= A1.
Proof. intros. eapply lhd_blocks_disjoint; eauto. eapply dheap_lheap; eauto. Qed.

Lemma dheap_remove_old : forall cs q B n p A k SPB m mo,
  DHEAP cs [(q, B, n); (p, A, k)] SPB m mo -> lb_remove p [(q, B, n); (p, A, k)] = [(q, B, n)].
Proof.
  intros cs q B n p A k SPB m mo (s & L & Bb & _ & HR & _).
  pose proof (RHEAP_slot_nodup _ _ _ HR) as ND. cbn [map blk_slot blk_id fst snd] in ND.
  rewrite lb_remove_cons. cbn [blk_id fst].
  destruct (bptr_eqb q p) eqn:E.
  - exfalso. apply bptr_eqb_eq in E. subst q. inversion ND; subst. apply H1. left. reflexivity.
  - rewrite lb_remove_cons. cbn [blk_id fst]. replace (bptr_eqb p p) with true; [reflexivity|].
    symmetry. apply (proj2 (bptr_eqb_eq p p)). reflexivity.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac drv_write_ok_tac :=
  unfold drv_write_ok, alloc_ceiling, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, PERRNO, PGERROR; cbn [fst snd];
  first [ left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia ].
