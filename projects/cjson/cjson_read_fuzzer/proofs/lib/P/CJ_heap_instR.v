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
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMalloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_fentry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module CJ_heap_inst.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.RF_malloc_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.
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
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Theorem lhd_realloc_null : rrealloc_null_stmt -> realloc_null_stmt LHEAPd.
Proof.
  intros RN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB n lo errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) HSP ST Hlo Hlo2 ER MI Htp Ha0 Ha1 Hn.
  (* [comment removed for export] *)
  pose proof (RN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi n lo B errv
                HR HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Ha1 Hn) as Himpl.
  pose proof (raw_malloc_etwf (map blk_slot LBi) s mo n HO ltac:(lia)) as Hwf.
  eapply scps_mono; [apply (implM_scps psegs (raw_malloc n) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ER' & HA' & HP & _ & _ & Hr).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  split; [apply cj_pres_of_rheap_pres; exact HP|].
  destruct r as [[c off]|].
  - destruct Hr as (A & junk & -> & HRng & HR' & RW & _). destruct HRr as (HO' & Hni & _ & _). cbn [fst snd] in HO'.
    right. exists A, junk. split; [reflexivity|]. split; [exact HRng|]. split.
    + rewrite map_fst_bview. pose proof (RHEAP_addr_nodup _ _ _ HR') as ND. cbn [map blk_addr fst snd] in ND. inversion ND; assumption.
    + split; [| exact RW]. exists s'. exists (((c, off), A, n) :: LBi). exists B. splits; auto.
  - destruct Hr as [-> HR']. left. split; [reflexivity|]. exists s', LBi, B. splits; auto.
Qed.

(* [comment removed for export] *)
Definition PHI (Hrealloc : realloc_scps_stmt LHEAPd) (Hrealloc_null : rrealloc_null_stmt) : cj_heap_iface :=
  mkCJHI LHEAPd
    lhd_mok lhd_frame lhd_perm lhd_lower lhd_block_range lhd_blocks_disjoint lhd_nodup lhd_block_wr lhd_block_slack lhd_ssp
    lhd_malloc lhd_free lhd_free_null Hrealloc (lhd_realloc_null Hrealloc_null).


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End CJ_heap_inst.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_malloc_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_alloc_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module RF_realloc_mentry.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
(* [comment removed for export] *)

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.RF_malloc_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.RF_alloc_slot OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_inst0.RF_malloc_big OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_alloc_meta.RF_am_P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_alloc_meta.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition RMALLOC_ESTACK : Z := 8128.

(* [comment removed for export] *)
Definition rmalloc_entry_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_ESTACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM psegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs)).

Section CORE8128.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Lemma rmalloc_core_implT8128 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
  RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8128 ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
  rimplT m (malloc_core full_lay (set_tick t st) n) s
        (rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs)).
Proof.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. (nelimp (rregion_facts st m rid r1 MR H1) 4%nat; intros X1 _ X2 _). unfold alloc_ceiling in X2. lia. }
  (nelimp MR 4%nat; intros WF0 CX0 GL0 _). (nelim GL0 3%nat; intros _ NL _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono psegs m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells psegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. unfold alloc_ceiling in CLO.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  - (* [comment removed for export] *)
    riprefixT. eapply evt_cut.
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI]. }
    intros ms' nelH_; (nelim nelH_ 8%nat; intros a1' m1 -> FR ST1 MU WM MI1).
    (nelim (PREP m1 MU WM) 6%nat; intros MR1 TK1 UA1 ERR1 AUX1 PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact NL]. }
    intros ms' nelH_; (nelim nelH_ 11%nat; intros a0' a1' a2' a3' m1 -> FR ST1 MU WM MI1).
    (nelim (PREP m1 MU WM) 6%nat; intros MR1 TK1 UA1 ERR1 AUX1 PE1).
    (nelimp (size_to_class_props n ltac:(lia)) 3%nat; intros SCR SFIT _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE8128.

Local Set Keyed Unification.
Section TOPLEVEL8128.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQe (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_entry_spec_proof : rmalloc_entry_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_ESTACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
  (nelim HEAP 6%nat; intros st LB0 HPERM Hst MR [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  unfold raw_malloc.
  eapply (implM_bind psegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0' s1' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  eapply (implM_bind psegs _ _ _ (rmidQe m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT8128 as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQe. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  (nelim MQ 9%nat; intros st2 r ans o1 Ecs Ec F1 F2 CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind psegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 40%nat; intros b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra' -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO MREL BL2 PSM PSF PSO)
.
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    (nelimp (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) 4%nat; intros R4 RAL RC RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    unfold alloc_ceiling in RC, CLO. unfold RMALLOC_ESTACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    (nelim EP 25%nat; intros st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' ER -> MI' ST' MR' TK' PE' LEAF).
    (nelim LEAF 7%nat; intros off OFF0 FIT Ep Est' Ep2 Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    (nelimp (strip_eq_proj _ _ SE) 8%nat; intros Ec Er En Em _ _ Esl Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. nexists 15%nat. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - clear - Ha X RI1 SPAN SKL SK B0 S16. first [heap_lia_imp | lia]. }   (* [comment removed for export] *)
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { unfold rblock_range, alloc_ceiling. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). clear - N0' RC RI1 SPAN SKL SK B0 FIT OFF0 S16. lia. }  (* [comment removed for export] *)
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 29%nat; intros m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO)
.
    apply evt_done. unfold rmalloc_post. nexists 15%nat. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL8128.


Theorem rmalloc_entry_spec : rmalloc_entry_stmt.
Proof.
  exact (rmalloc_entry_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.


End CeilWrap.
End RF_realloc_mentry.

(* [comment removed for export] *)
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSoundMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocksR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WRemap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_mremap.
Module RF_realloc_G1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
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
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Lemma implM_msys_of_impl {A} n (dec : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms :
  impl psegs (at_node psegs) (enode n dec) (epost P) ms ->
  implM psegs (msys n dec) s (fun a s' ms' => s' = s /\ P a ms') ms.
Proof.
  intros H. unfold implM, msys. cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (dec rsp) as [a|]; cbn in Hk |- *.
  - eapply evt_mono; [exact Hk|]. intros ms' HP. split; [reflexivity| exact HP].
  - exact Hk.
Qed.

(* [comment removed for export] *)
Lemma idx_land i res : 0 <= i < 32 -> 0 <= res -> Z.land (i + 32 * Z.min res 5) 31 = i.
Proof using .
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
  replace (i + 32 * Z.min res 5) with (i + Z.min res 5 * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma rsv_shiftr i res : 0 <= i < 32 -> 0 <= res -> Z.shiftr (i + 32 * Z.min res 5) 5 = Z.min res 5.
Proof using .
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. replace (i + 32 * Z.min res 5) with (i + Z.min res 5 * 32) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma addr_mod16 rb sb st i off : rb mod 4096 = 0 -> sb mod 16 = 0 -> st mod 16 = 0 -> (rb + sb + 16 + st * i + 16 * off) mod 16 = 0.
Proof using .
  intros H H0 H1. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide in H0; [|lia]. apply Z.mod_divide in H1; [|lia].
  destruct H as [x ->]. destruct H0 as [y ->]. destruct H1 as [z ->].
  apply Z.mod_divide; [lia|]. exists (x * 256 + y + 1 + z * i + off). lia.
Qed.
Lemma q_small_class (stride sz i off k q : Z) : 0 <= i -> 0 <= off -> 0 <= k -> 16 * off + k <= stride - 4 ->
  16 * q = stride * i + 16 * off -> (stride = 16 * sz \/ (i = 0 /\ (stride <= 16 * sz \/ 256 <= sz))) -> off <= 255 ->
  sz * i <= q < sz * (i + 1).
Proof using .
  intros Hi Ho Hk Hfit EQ D O255. destruct D as [->|[-> D]].
  - assert (Hq : q = sz * i + off) by nia. subst q. clear EQ. assert (off < sz) by lia. nia.
  - rewrite Z.mul_0_r, Z.add_0_l in EQ. assert (q = off) by lia. subst q. lia.
Qed.
Lemma q_maplen (stride i off k q maplen : Z) : 0 <= i -> 0 <= off -> 0 <= k -> 16 * off + k <= stride - 4 ->
  16 * q = stride * i + 16 * off -> 16 + stride * (i + 1) <= maplen * 4096 -> q <= maplen * 256 - 1.
Proof using . intros. nia. Qed.

(* [comment removed for export] *)
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac liac := clear_complex; lia.

Section RR.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : PState) (LB : list block) (p : bptr) (A k n lo Bx : Z) (old : list byte) (errv : word).
Variables (st : mstate) (LB0 : list block) (g b : aptr) (r : region) (i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MRP : rmrep st m.
Hypothesis BLK : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis RF : rrF st m LB0 p A k g b r i off.
Hypothesis Hin : In (p, A, k) LB.
Hypothesis Hin0 : In (p, A, k) LB0.
Hypothesis BA : bytes_at psegs m A old.
Hypothesis LEN : Z.of_nat (length old) = k.
Hypothesis AV : rauxv_ok m Bx.
Hypothesis HB : bv_unsigned sp <= Bx.
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - RREALLOC_STACK.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis A1 : a1 = Z_to_bv 64 n.
Hypothesis N : 0 <= n < 2^32.

(* [comment removed for export] *)
Definition Xstride : Z := get_stride (MR st g).
Definition XP0 : Z := conc st (fst p).
Definition XE : Z := XP0 + Xstride - IB.
Definition Xres : Z := XE - A - k.
Definition XB : Z := conc st b.
Definition XG : Z := conc st g.
Definition Xmword : Z := meta_word (MR st g).
Definition Xsc : Z := m_sizeclass (MR st g).
Definition Xq : Z := (snd (fst p) + UNIT * off - snd b - UNIT) / UNIT.

(* [comment removed for export] *)
Definition rr_mid_post : machine_state -> Prop :=
  fun ms' => exists m1 t3' t4',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 XE) (Z_to_bv 64 (XB + Xstride * i + 16)) (wz 0)
                  s0 (wz XG) a0 a1 (wz XB) (Z_to_bv 64 Xsc) (wz Xmword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 (XE + 4)) (Z_to_bv 64 (XE + - bv_unsigned a0))
                  (Z_to_bv 64 (XE - Xres)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
             F (Z_to_bv 64 0x16d74) fc None m1 (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1
    /\ stk psegs m1 lo (bv_unsigned sp + -64)
    /\ rw_cells psegs m1 (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6).

Lemma rr_prefix :
  evt psegs rr_mid_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom psegs)).
Proof using A0 A1 LEN LO MI N RF SLO ST.
  destruct RF as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH _].
  cbv zeta in BY. (nelim BY 8%nat; intros B4 B3 B2 HQ EQ16 BF BC BE).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold RREALLOC_STACK in SLO. unfold alloc_ceiling in LO, RC, G40.
  (* [comment removed for export] *)
  unfold RREALLOC_SYM. step. change (Z_to_bv 64 93072) with (Z_to_bv 64 rrealloc_entry).
  pose proof (go_li _ _ _ GOK) as LI. pose proof (go_avail _ _ _ GOK) as AVr. pose proof (go_freed _ _ _ GOK) as FRr. pose proof (go_freeable _ _ _ GOK) as FB.
  pose proof (go_sc _ _ _ GOK) as GSC. pose proof (go_maplen _ _ _ GOK) as ML. pose proof (go_stride _ _ _ GOK) as [S16 SM]. (nelimp (go_region _ _ _ GOK) 7%nat; intros rX HrX _ _ _ _ TOP).
  rewrite Hr in HrX. injection HrX as <-.
  change (get_meta_rec st g) with (MR st g) in LI, AVr, FRr, FB, GSC, ML, S16, SM, TOP.
  unfold rr_mid_post, XE, Xres, XP0, XB, XG, Xmword, Xsc, Xstride.
  set (mr := MR st g) in *.
  set (stride := get_stride mr) in *. assert (Estride : stride = get_stride mr) by reflexivity.
  set (sc := m_sizeclass mr) in *. assert (Esc : sc = m_sizeclass mr) by reflexivity.
  set (P0 := conc st (fst p)) in *. set (B := conc st b) in *. set (G := conc st g) in *.
  assert (EG : G = conc st g) by reflexivity. assert (EB : B = conc st b) by reflexivity. assert (EP0 : P0 = conc st (fst p)) by reflexivity.
  set (q := (snd (fst p) + UNIT * off - snd b - UNIT) / UNIT) in *.
  set (res := P0 + stride - IB - A - k) in *. assert (Eres : res = P0 + stride - IB - A - k) by reflexivity.
  clearbody stride sc P0 B G q res.
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; liac).
  assert (SIL : stride * i + stride <= stride * (m_last_idx mr + 1)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; liac).
  set (si := stride * i) in *. assert (Esi : si = stride * i) by reflexivity. clearbody si.
  set (sl := stride * (m_last_idx mr + 1)) in *. assert (Esl : sl = stride * (m_last_idx mr + 1)) by reflexivity. clearbody sl.
  assert (HP0 : P0 = B + 16 + si) by (rewrite Cc, Cb, Ec; cbn [snd]; unfold UNIT; liac).
  assert (RES : 0 <= res /\ res = stride - IB - UNIT * off - k) by (rewrite Eres, EA; unfold UNIT, IB in *; liac).
  pose proof (idx_land i res ltac:(liac) ltac:(liac)) as IDX.
  assert (B3' : 0 <= i + 32 * Z.min res 5 < 256) by liac.
  assert (AMOD : A mod 16 = 0) by (rewrite EA, HP0, Cb, Esi; unfold UNIT in *; apply addr_mod16; assumption).
  assert (HDR : bytes_at psegs m (A - 4) ([b8 0; b8 (i + 32 * Z.min res 5)] ++ le2 (wz q))).
  { change ([b8 0; b8 (i + 32 * Z.min res 5)] ++ le2 (wz q)) with ([b8 0] ++ ([b8 (i + 32 * Z.min res 5)] ++ le2 (wz q))).
    apply bytes_at_app. split; [exact B4|]. cbn [length]. change (Z.of_nat 1%nat) with 1. replace (A - 4 + 1) with (A - 3) by lia.
    apply bytes_at_app. split; [exact B3|]. cbn [length]. change (Z.of_nat 1%nat) with 1. replace (A - 3 + 1) with (A - 2) by lia. exact B2. }
  assert (MM' : rw_cells psegs m G [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz B); C4 (wz (m_avail mr)); C4 (wz (m_freed mr));
                                  C8 (wz (m_last_idx mr + 32 * m_freeable mr + 64 * sc + 4096 * m_maplen mr))]).
  { unfold meta_cells in MM. rewrite Hmem in MM. unfold pw at 3 in MM. cbn [oconc] in MM. rewrite <- EB in MM. rewrite Esc. exact MM. }
  unfold alloc_ceiling, UNIT, IB in *.
  assert (SC64 : 0 <= sc < 64) by (clear -GSC; lia).
  assert (SC63 : 48 <= sc -> sc = 63) by (clear -GSC; lia).
  assert (QSC : sc < 48 -> size_class sc * i <= q < size_class sc * (i + 1)).
  { intros Hsc; apply (q_small_class stride (size_class sc) i off k q); try liac.
    destruct (Z.eqb_spec (m_last_idx mr) 0) as [L0|L0].
    + right; split; [liac|]. destruct (SC28 Hsc) as [X|X]; [left; liac| right]. pose proof (MI_WFree.size_class_28 sc ltac:(liac)). liac.
    + left. rewrite Estride. unfold get_stride. replace (m_last_idx mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact L0). cbn [andb]. rewrite <- Esc. unfold UNIT. lia. }
  eapply evt_cut.
  { eapply (rr_hdr1_walk ra sp gp tp) with (P := A) (n := n) (G := G) (B := B) (A := G - G mod 4096) (b3 := i + 32 * Z.min res 5) (off16 := q)
      (avail := m_avail mr) (freed := m_freed mr) (last_idx := m_last_idx mr) (freeable := m_freeable mr) (sc := sc) (maplen := m_maplen mr) (secret := secret)
      (prev := pw st (m_prev mr)) (next := pw st (m_next mr)) (lo := lo);
    rewrite ?IDX; first [eassumption | idtac].
    all: unfold alloc_ceiling; try first [ match goal with
                 | |- bv_unsigned a0 = A => rewrite A0; apply unsigned_lit; liac
                 | |- bv_unsigned a1 = n => rewrite A1; apply unsigned_lit; liac
                 end
               | liac ].
  }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 7%nat; intros m1 H1 MU1 WM1 MI1 ST1 FR1). (nelim H1 3%nat; intros t3' t4' ->).
  assert (XP : forall a bs, bytes_at psegs m a bs -> a + Z.of_nat (length bs) <= lo -> bytes_at psegs m1 a bs).
  { intros a bs Ha Hl. eapply bytes_at_transport; [exact Ha| exact MU1|]. cbn [disjoint_from]. split; [left; clear -Hl SLO; lia| exact I]. }
  assert (ALE : A + 16 * 0 <= P0 + stride - 4 - k) by liac.
  assert (ELO : P0 + stride - 4 + 1 <= lo) by liac.
  assert (Estr2 : (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - UNIT else UNIT * size_class sc) = stride).
  { rewrite Estride, Esc. reflexivity. }
  assert (RSV : (if 160 <=? i + 32 * Z.min res 5 then res else Z.shiftr (i + 32 * Z.min res 5) 5) = res).
  { destruct (Z.leb_spec 160 (i + 32 * Z.min res 5)); [reflexivity|]. rewrite rsv_shiftr by liac. liac. }
  eapply evt_mono.
  { eapply (rr_hdr2_walk ra) with (P := A) (G := G) (r32 := res); rewrite ?IDX, ?Estr2, ?RSV; first [eassumption| idtac]; unfold UNIT, IB, alloc_ceiling; rewrite <- ?Esi, <- ?HP0.
    - rewrite A0; apply unsigned_lit; liac.
    - liac.
    - liac.
    - liac.
    - intros H160. assert (R5 : 5 <= res) by liac. split; [rewrite rsv_shiftr by liac; liac|]. split; [split; [exact R5| apply BF; exact R5]|].
      split; (apply XP; [apply BF; exact R5| rewrite ?length_le4; cbn [length]; liac]).
    - liac.
    - destruct (Z.eq_dec res 0) as [R0'|R0'].
      + rewrite R0', Z.sub_0_r. apply XP; [exact BE| cbn [length]; liac].
      + apply XP; [apply BC; liac| cbn [length]; liac].
    - apply XP; [exact BE| cbn [length]; liac].
    - liac.
    - liac.
    - liac.
    - liac.
    - intros Hml. destruct (TOP Hml) as [Hb2 Hml2]. apply (q_maplen stride i off k q (m_maplen mr)); liac.
    - intros HH. clear -HH GSC. lia.
  }
  cbv beta. intros ms2 nelH_; (nelim nelH_ 3%nat; intros t3'' t4'' ->). unfold rr_mid_post.
  exists m1, t3'', t4''. split; [| auto 10].
  f_equal. f_equal.
  all: rewrite ?IDX, ?Estr2, ?RSV; unfold XE, XP0, Xstride, UNIT, IB; fold mr; rewrite <- ?EP0, <- ?Estride, <- ?Esi, <- ?HP0.
  all: try reflexivity. all: try (f_equal; liac).
  unfold meta_word. rewrite Esc. reflexivity.
Qed.
Definition Xkb : Z := i + 32 * Z.min Xres 5.
Definition Xup : aptr := aadd (fst p) (UNIT * off).

Lemma brk_link_strip_eq (st1 st2 : mstate) pb : strip st2 = strip st1 -> brk_link st1 pb -> brk_link st2 pb.
Proof.
  intros E H. change (brk_link (strip st2) pb). rewrite E. change (brk_link st1 pb). exact H.
Qed.

Lemma perm_blocks n' : Permutation ((p, A, n') :: lbrm LB0 (p, A, k)) ((p, A, n') :: lb_remove p LB).
Proof using Hin PERM RF.
  apply perm_skip. rewrite (lb_remove_lbrm LB p A k); [apply lbrm_perm; exact PERM| | exact Hin].
  eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ (rf_C _ _ _ _ _ _ _ _ _ _ _ RF))].
Qed.

Lemma rplan_eq : rplan_of (ps_m s) (fst p) A n =
  if (n <=? Xstride - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (Xsc <=? size_to_class n + 1) then RPInPlace
  else if (48 <=? Xsc) && (MMAP_THRESHOLD <=? n)
       then (if negb (Xsc =? 63) then RPUndef else RPRemap (fst b) g XB (m_maplen (MR st g) * 4096) (rr_needed n (UNIT * off)))
       else RPFallback.
Proof using Hst RF old.
  rewrite <- Hst, rplan_of_strip. unfold rplan_of. rewrite (rf_slot _ _ _ _ _ _ _ _ _ _ _ RF).
  change (get_meta_rec st g) with (MR st g). rewrite (rf_mem _ _ _ _ _ _ _ _ _ _ _ RF).
  replace (A - conc st (fst p)) with (UNIT * off) by (rewrite (rf_A _ _ _ _ _ _ _ _ _ _ _ RF); lia).
  reflexivity.
Qed.

Lemma rss_mem_wmono mx P E nn kk : wmono psegs mx (rss_mem mx P E nn kk).
Proof using .
  unfold rss_mem. destruct (5 <=? E - P - nn); destruct (E - P - nn =? 0); repeat apply wmono_write; apply wmono_refl.
Qed.

Lemma rr_inplace_final : forall m1 ms' (errv' : word),
  munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 -> wmono psegs m m1 ->
  n <= XE - A -> XE - A - n < 2^32 ->
  rw_cells psegs m1 (errno_addr tp) [C4 errv'] ->
  rr_ret_post (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 A lo (rss_mem m1 A XE n Xkb) ms' ->
  rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A k n lo Bx old m (Some p) s ms'.
Proof.
  intros m1 ms' errv' MU1 WM1 NFIT RS ERR1 nelH_; (nelim nelH_ 17%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 -> MI' ST').
  destruct RF as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH IV].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold RREALLOC_STACK in SLO. pose proof LO as LO'. unfold alloc_ceiling in LO'.
  unfold alloc_ceiling in RC, G40.
  (nelimp MRP 6%nat; intros WF _ _ _ _ SH). (nelimp WF 5%nat; intros Hres WR DJ WA WG).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof (go_stride _ _ _ GOK) as [S16 SM]. change (get_meta_rec st g) with (MR st g) in S16, SM.
  unfold XE, XP0, Xstride in *. unfold Xkb, Xres, XE, XP0, Xstride.
  set (stride := get_stride (MR st g)) in *. set (P0 := conc st (fst p)) in *.
  set (m' := rss_mem m1 A (P0 + stride - IB) n (i + 32 * Z.min (P0 + stride - IB - A - k) 5)) in *.
  unfold IB, UNIT in *.
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; liac).
  assert (SIL : stride * i + stride <= stride * (m_last_idx (MR st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; liac. }
  assert (HP0 : P0 = r_base r + snd b + 16 + stride * i) by (rewrite Cc, Ec; cbn [snd]; lia).
  assert (AG1 : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> m1 (wa a) = m (wa a)).
  { intros a Ha Na. apply MU1. rewrite wa_unsigned by lia. cbn. lia. }
  assert (AG2 : forall a, 0 <= a < 2^64 -> a <> A - 3 -> ~ (A + n <= a < P0 + stride - 4) -> m' (wa a) = m1 (wa a)).
  { intros a Ha N1 N2. unfold m'. apply rss_mem_outside; rewrite ?wa_unsigned by lia; liac. }
  assert (WMM : wmono psegs m m') by (eapply wmono_trans; [exact WM1| apply rss_mem_wmono]).
  (* [comment removed for export] *)
  set (FP := fun a => (bv_unsigned sp - 64 <= a < bv_unsigned sp) \/ a = A - 3 \/ (A + n <= a < P0 + stride - 4)).
  assert (PE : rpres_except FP m m').
  { intros a Ha NC. subst FP. cbv beta in NC. split.
    - rewrite AG2 by liac. apply AG1; liac.
    - apply WMM. }
  assert (AMOD : A mod 16 = 0) by (rewrite EA, HP0; apply addr_mod16; assumption).
  assert (SP' : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) + 64) = sp).
  { rewrite unsigned_lit by liac. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite SP'. rewrite unsigned_lit in ST' by liac. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST' by lia.
  unfold rrealloc_post. exists w0, w1, w2, (Z_to_bv 64 A), w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rrw_cells_agree'; [exact ERR1|]. intros a Ha. rewrite TP in Ha. unfold RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. apply AG2; destruct RI as [RI'|RI']; liac. }
  split. { eapply rauxv_ok_pres_B; [exact AV| exact PE| |]; subst FP; cbv beta; intros a Ha; unfold RAUXV_CELL in *; destruct RI as [RI'|RI']; liac. }
  split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *)
  set (mn := Z.min k n).
  assert (MN : 0 <= mn <= k /\ mn <= n /\ (Z.to_nat mn <= length old)%nat) by (subst mn; liac).
  assert (W' : wr_at psegs m' A n).
  { eapply wr_at_transport; [| exact WMM]. eapply wr_at_sub; [exact HWr| liac| liac]. }
  (nelim (rwr_at_bytes_exist m' (A + mn) (n - mn) ltac:(eapply wr_at_sub; [exact W'| liac| liac]) ltac:(liac) ltac:(destruct RI as [RI'|RI']; liac)) 3%nat; intros junk JL JB).
  assert (OB : bytes_at psegs m' A (firstn (Z.to_nat mn) old)).
  { eapply rbytes_at_agree with (m := m).
    - pose proof BA as BA'. rewrite <- (firstn_skipn (Z.to_nat mn) old) in BA'. apply bytes_at_app in BA'. exact (proj1 BA').
    - intros a Ha. rewrite firstn_length_le in Ha by (clear - MN; lia).
      rewrite AG2 by (clear - Ha MN EA Ho Hk Hfit HP0 R0 B0 SI0 SIL SPAN RC N NFIT; lia).
      apply AG1; clear - Ha MN EA Ho Hk Hfit HP0 R0 B0 SI0 SIL SPAN RC N NFIT LO' SLO; lia. }
  exists A, junk. split; [reflexivity|].
  split. { unfold rblock_range, alloc_ceiling. split; [liac|]. split; [exact AMOD|]. split; [liac|]. split; [liac|]. destruct RI as [RI'|RI']; [left|right]; liac. }
  split.
  2:{ split; [| split; [| left; reflexivity]].
      - intros a Ha CA. apply PE; [exact Ha|]. subst FP; cbv beta.
        destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]]; [liac| destruct RI as [RI'|RI']; liac|].
        rewrite (lb_remove_lbrm LB p A k) in Hb' by (first [exact Hin | eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ C)]]).
        apply (In_lbrm_perm LB LB0) in Hb'; [| apply Permutation_sym; exact PERM].
        unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [HinL NEQ].
        assert (NES : blk_slot blk' <> fst p). { intros E. cbn [blk_slot fst] in NEQ. rewrite E, MI_Kit.aptr_eqb_refl in NEQ. exact NEQ. }
        destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
        (nelim (WR _ _ Hrg) 5%nat; intros _ _ _ RGC _). unfold alloc_ceiling in RGC.
        destruct (N.eq_dec (fst (blk_slot blk')) (fst b)) as [EQR|NER].
        + destruct (OTH blk' HinL NES EQR) as [O|O]; clear - Hab O EA Ho Hk Hfit NFIT AEND RGC LO' SLO N; lia.
        + destruct (DJ _ _ _ _ Hrg Hr NER) as [D|D]; rewrite ?(lr_lo_group _ Krg), ?(lr_lo_group _ Kr) in D; clear - Hab A16 AEND D HP0 B0 SI0 SIL SPAN EA Ho Hk Hfit N NFIT RGC LO' SLO; lia.
      - apply rw_cells_of_bytes.
        + cbn. rewrite firstn_length_le by liac. split; [reflexivity|]. split; [exact JL| exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OB|]. rewrite firstn_length_le by liac. rewrite Z2Nat.id by liac. exact JB.
        + cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_add, !Z2Nat.id by liac. replace (mn + (n - mn)) with n by lia. exact W'. }
  exists (rr_inplace_full st (fst p) Xup n), ((p, A, n) :: lbrm LB0 (p, A, k)).
  split; [apply perm_blocks|].
  split; [rewrite strip_rr_inplace_full; exact Hst|].
  pose proof (go_li _ _ _ GOK) as LI. change (get_meta_rec st g) with (MR st g) in LI.
  split.
  - (* [comment removed for export] *)
    unfold rr_inplace_full. rewrite Hs. cbv zeta.
    set (st1 := set_tick (N.succ (s_tick st)) st).
    set (e := aadd (fst p) (get_stride (get_meta_rec st g) - IB)).
    set (kb := i + 32 * Z.min (P0 + stride - 4 - A - k) 5) in *.
    assert (MR1 : rmrep st1 m1).
    { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MRP| exact MU1| exact WM1|].
      intros lo' hi' [E|[]]. injection E as <- <-. unfold alloc_ceiling. clear - LO' SLO; lia. }
    assert (TK1 : ticks_ok st1) by (apply ticks_ok_set_tick; [cbn; lia| exact (ci_ticks _ _ C)]).
    assert (Hr1 : s_regions st1 !! (fst Xup) = Some r). { unfold Xup, aadd. cbn [fst s_regions set_tick st1]. rewrite Ec. exact Hr. }
    assert (Fe : fst e = fst Xup) by reflexivity.
    assert (P4 : 4 <= snd Xup). { unfold Xup, aadd. rewrite Ec. cbn [fst snd]. unfold UNIT. clear - B0 SI0 Ho; lia. }
    assert (PNE : snd Xup + n <= snd e). { unfold Xup, e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. rewrite Ec. cbn [fst snd]. unfold IB, UNIT. clear - NFIT EA; lia. }
    assert (EHI : snd e + 1 <= round_up_pg (r_len r)). { unfold e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. rewrite Ec. cbn [fst snd]. unfold IB, UNIT. clear - SIL SPAN SI0 B0; lia. }
    assert (RS' : snd e - snd Xup - n < 2^32). { unfold Xup, e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. rewrite Ec. cbn [fst snd]. unfold IB, UNIT. clear - RS EA; lia. }
    assert (IDX : 0 <= i < 32) by (clear - Hi LI; lia).
    assert (KB : 0 <= kb < 256 /\ Z.land kb 31 = i). { subst kb. split; [clear - IDX EA Hfit Hk; lia| apply idx_land; [exact IDX| clear - EA Hfit Hk; lia]]. }
    assert (NOGRP : forall b' gh, s_groups st1 !! b' = Some gh -> fst b' = fst Xup -> snd b' + 9 <= snd Xup - 3 \/ snd e + 1 <= snd b').
    { intros b' gh Hb' Eb'. unfold Xup, e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. unfold IB.
      unfold Xup, aadd in Eb'. rewrite Ec in Eb'. cbn [fst] in Eb'.
      destruct (NOG b' gh Hb' Eb') as [O|O]; rewrite Ec; cbn [fst snd]; unfold UNIT; [left| right]; clear - O HP0 Cc Ho Hk Hfit N; lia. }
    pose proof (rmrep_set_size_i st1 m1 Xup e r n i kb MR1 TK1 Hr1 Kr Fe P4 (proj1 N) PNE EHI RS' IDX KB NOGRP) as SS.
    replace (r_base r + snd Xup) with A in SS by (unfold Xup, aadd; cbn [snd]; unfold UNIT; clear - EA Cc HP0; lia).
    replace (r_base r + snd e) with (P0 + stride - 4) in SS by (unfold e, aadd; cbn [snd]; change (get_meta_rec st g) with (MR st g); fold stride; unfold IB; clear - Cc HP0; lia).
    destruct SS as [R1 T1]. exact (proj1 (rmrep_havoc _ _ Xup n R1 T1)).
  - split.
    + eapply brk_link_strip_eq; [| exact BLK]. rewrite strip_rr_inplace_full. reflexivity.
    + eapply areach_ext; [exact AR|]. apply (aext_inplace ref_reserved st LB0 p A k n off Hin0 (proj1 Ho)).
      * exact EA.
      * liac.
      * intros g' i' E. rewrite Hs in E. injection E as <- <-. fold stride. unfold UNIT, IB. clear - NFIT RS EA; lia.
Qed.
End RR.


End CeilWrap.
(* [comment removed for export] *)
Notation RAREACH := (AREACH_from ref_reserved).
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac liac := clear_complex; lia.
End RF_realloc_G1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W14.
Module RF_realloc_G2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_P RF_realloc_G1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
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
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.
Ltac clear_keep := repeat match goal with K : keep _ |- _ => clear K end.
(* [comment removed for export] *)
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; clear_keep; lia.
Ltac liak1 H := prune; unfold keep in H; clear_keep; lia.
Ltac liak2 H1 H2 := prune; unfold keep in H1, H2; clear_keep; lia.
Ltac liak3 H1 H2 H3 := prune; unfold keep in H1, H2, H3; clear_keep; lia.

Notation RAREACH := (AREACH_from ref_reserved).

Lemma mod16_d d off : d mod 4096 = 0 -> (d + 16 * off + 16) mod 16 = 0.
Proof using .
  intros H. apply Z.mod_divide in H; [|lia]. destruct H as [x ->]. apply Z.mod_divide; [lia|]. exists (256 * x + off + 1). lia.
Qed.

Lemma ctx_cs_remap cs rid g d nn : ctx (cs_remap cs rid g d nn) = ctx cs.
Proof using . unfold cs_remap, upd_meta, upd_region, get_region, ctx. cbn. destruct (s_regions cs !! rid); reflexivity. Qed.

Lemma ticks_ok_of_TKS st : TKS st (s_tick st) -> ticks_ok st.
Proof using .
  intros T. split.
  - intros rid sh u hl ch Hsh Hu Hin. exact (proj1 (proj2 (T rid sh Hsh)) u hl ch Hu Hin).
  - intros rid sh pg t Hsh Hpg. exact (proj2 (proj2 (T rid sh Hsh)) pg t Hpg).
Qed.

(* [comment removed for export] *)
Lemma bytes_at_shift m m' a a' bs :
  bytes_at psegs m a bs -> 0 <= a' -> a' + Z.of_nat (length bs) <= 2^64 ->
  (a + Z.of_nat (length bs) <= 0x10000 \/ 0x55000 <= a) -> (a' + Z.of_nat (length bs) <= 0x10000 \/ 0x55000 <= a') ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> m' (wa (a' + j)) = m (wa (a + j))) ->
  bytes_at psegs m' a' bs.
Proof using .
  intros (A0 & A1 & HB) H0 H1 Hi Hi' E. split; [lia|]. split; [lia|].
  intros i Hi2. specialize (HB i Hi2).
  rewrite ref_mrd_overlay in HB by (rewrite wa_unsigned by lia; lia).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). rewrite E by lia. exact HB.
Qed.

(* [comment removed for export] *)
Lemma meta_word_remap mr nn : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  0 <= nn < 2^62 -> nn mod 4096 = 0 ->
  meta_word (m_set_maplen (nn / 4096) mr) = Z.lor (Z.land (meta_word mr) 4095) nn.
Proof using .
  intros. unfold meta_word. destruct mr; cbn in *.
  rewrite MI_WRemap.land_ones52 by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (lo := m_last_idx + 32 * m_freeable + 64 * m_sizeclass). assert (Hlo : 0 <= lo < 4096) by lia.
  replace (Z.land (lo + 4096 * m_maplen) 4095) with lo.
  2:{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
      replace (lo + 4096 * m_maplen) with (lo + m_maplen * 4096) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  replace nn with ((nn / 4096) * 2^12) at 2 by (change (2^12) with 4096; pose proof (Z_div_mod_eq_full nn 4096); lia).
  rewrite ASlot_W14.lor_small_shl by (first [apply Z.div_pos; lia | lia]). pose proof (Z_div_mod_eq_full nn 4096). lia.
Qed.
Section RR.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : PState) (LB : list block) (p : bptr) (A k n lo Bx : Z) (old : list byte) (errv : word).
Variables (st : mstate) (LB0 : list block) (g b : aptr) (r : region) (i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MRP : rmrep st m.
Hypothesis BLK : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis RF : rrF st m LB0 p A k g b r i off.
Hypothesis Hin : In (p, A, k) LB.
Hypothesis Hin0 : In (p, A, k) LB0.
Hypothesis BA : bytes_at psegs m A old.
Hypothesis LEN : Z.of_nat (length old) = k.
Hypothesis AV : rauxv_ok m Bx.
Hypothesis HB : bv_unsigned sp <= Bx.
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - RREALLOC_STACK.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis A1 : a1 = Z_to_bv 64 n.
Hypothesis N : 0 <= n < 2^32.

(* [comment removed for export] *)
Definition Xstride : Z := get_stride (MR st g).
Definition XP0 : Z := conc st (fst p).
Definition XE : Z := XP0 + Xstride - IB.
Definition Xres : Z := XE - A - k.
Definition XB : Z := conc st b.
Definition XG : Z := conc st g.
Definition Xmword : Z := meta_word (MR st g).
Definition Xsc : Z := m_sizeclass (MR st g).
Definition Xkb : Z := i + 32 * Z.min Xres 5.
Definition Xup : aptr := aadd (fst p) (UNIT * off).

(* [comment removed for export] *)
Variables (d : Z) (m2 mX : mem) (errv2 : word).
Definition Xon : Z := m_maplen (MR st g) * 4096.
Definition Xnn : Z := rr_needed n (UNIT * off).
Hypothesis BIGN : MMAP_THRESHOLD <= n.
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Hypothesis D0 : 0 < d.
Hypothesis DA : d mod 4096 = 0.
Hypothesis DCE : d + Xnn <= alloc_ceiling.
Hypothesis DRF : ranges_free ref_reserved d Xnn = true.
Hypothesis DJ : forall q rq, s_regions st !! q = Some rq -> q <> fst b ->
  r_base rq + round_up_pg (r_len rq) <= d \/ d + Xnn <= lr_lo rq.
Hypothesis DISJ : d = XB \/ (XB + Xon <= d \/ d + Xnn <= XB).
Hypothesis MU2 : munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m2.
Hypothesis WM2 : wmono psegs m m2.
Hypothesis ERR2 : rw_cells psegs m2 (errno_addr tp) [C4 errv2].
Hypothesis FR2 : rw_cells psegs m2 (bv_unsigned sp - 64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6).
Hypothesis X1 : forall a, 0 <= a < 2^64 -> ~ (XB <= a < XB + Xon) -> ~ (d <= a < d + Xnn) -> mX (wa a) = m2 (wa a).
Hypothesis X2 : forall j, 0 <= j < Z.min Xon Xnn -> mX (wa (d + j)) = m2 (wa (XB + j)).
Hypothesis X3 : forall j, Z.min Xon Xnn <= j < Xnn -> mX (wa (d + j)) = Some (b8 0).
Hypothesis X4 : wr_at psegs mX d Xnn.
Hypothesis MIX : mem_inv psegs mX.
Hypothesis STX : stk psegs mX lo (bv_unsigned sp + -64).

Lemma perm_blocks' A' n' : Permutation ((p, A', n') :: lbrm LB0 (p, A, k)) ((p, A', n') :: lb_remove p LB).
Proof using Hin PERM RF.
  apply perm_skip. rewrite (lb_remove_lbrm LB p A k); [apply lbrm_perm; exact PERM| | exact Hin].
  eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ (rf_C _ _ _ _ _ _ _ _ _ _ _ RF))].
Qed.

(* [comment removed for export] *)
Lemma rr_remap_final : forall (vra t0' t1' t2' a3' a4' a5' a6' a7' s2' u5 u6 t3' t4' t5' t6' : word),
  evt psegs (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A k n lo Bx old m
               (Some p) (set_m (cs_remap (ps_m s) (fst b) g d Xnn) s))
      (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 Xnn) (wz XG) a0 a1 (Z_to_bv 64 d) a3' a4' a5' a6' a7'
               s2' (Z_to_bv 64 (UNIT * off)) (Z_to_bv 64 4095) u5 u6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x16e80) fc None mX (seg_rom psegs)).
Proof using A0 A1 AR AV BA BIGN BLK D0 DA DCE DISJ DJ DRF ERR2 FR2 HB Hin Hin0 Hst LEN LO MIX MRP MU2 N PERM RF SC63 SLO STX TP WM2 X1 X2 X3 X4.
  intros.
  destruct RF as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH IV].
  cbv zeta in BY. (nelim BY 8%nat; intros B4 B3 B2 HQ EQ16 BF BC BE).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold RREALLOC_STACK in SLO. pose proof LO as LO'. unfold alloc_ceiling in LO', RC, G40, DCE.
  (nelimp MRP 6%nat; intros WF _ _ _ _ SH). (nelimp WF 5%nat; intros Hres WR DJR WA WG).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof (go_stride _ _ _ GOK) as [S16 SM]. change (get_meta_rec st g) with (MR st g) in S16, SM.
  pose proof (go_li _ _ _ GOK) as LI. pose proof (go_avail _ _ _ GOK) as AVr. pose proof (go_freed _ _ _ GOK) as FRr. pose proof (go_freeable _ _ _ GOK) as FB.
  pose proof (go_sc _ _ _ GOK) as GSC. pose proof (go_maplen _ _ _ GOK) as ML. (nelimp (go_region _ _ _ GOK) 7%nat; intros rX HrX _ _ _ _ TOP).
  rewrite Hr in HrX. injection HrX as <-.
  change (get_meta_rec st g) with (MR st g) in LI, AVr, FRr, FB, GSC, ML, TOP.
  (nelimp (rreserved_disjoint _ _ DRF) 4%nat; intros DI1 DI2 DI3 DI4).
  (* [comment removed for export] *)
  assert (L0 : m_last_idx (MR st g) = 0) by (clear -GSC SC63; lia).
  assert (MLP : 0 < m_maplen (MR st g)) by (clear -GSC SC63; lia).
  destruct (TOP ltac:(liac)) as [Hb0 EON].
  assert (I0 : i = 0) by (clear -Hi L0; lia).
  unfold Xon, Xnn, XB, XG, XE, XP0, Xstride, Xres, Xkb, Xup in *.
  set (on := m_maplen (MR st g) * 4096) in *. set (nn := rr_needed n (UNIT * off)) in *.
  set (stride := get_stride (MR st g)) in *. set (P0 := conc st (fst p)) in *. set (B := conc st b) in *. set (G := conc st g) in *.
  assert (Estride : stride = on - 16).
  { subst stride on. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (MR st g)) 0); [liac|]. cbn. unfold UNIT. liac. }
  assert (HP0 : P0 = B + 16) by (rewrite Cc, Cb, Ec, I0; cbn [snd]; unfold UNIT; liac).
  assert (HBr : B = r_base r) by (rewrite Cb; liac).
  pose proof (rr_needed_facts n (UNIT * off) (proj1 N) ltac:(unfold UNIT; clear -Ho; lia)) as NN. fold nn in NN. unfold UNIT, IB in NN.
  assert (N62 : nn < 2^62) by (clear -NN N Ho; lia).
  unfold UNIT, IB in *.
  set (kb := i + 32 * Z.min (P0 + stride - 4 - A - k) 5) in *.
  assert (KB8 : 0 <= kb < 256 /\ Z.land kb 31 = i) by (subst kb; split; [liac| apply idx_land; liac]).
  (* [comment removed for export] *)
  (nelim MSL 6%nat; intros aa ar kk Haa Hkk Eg).
  (nelim (WA aa ar Haa) 7%nat; intros rga Hra A0a A4096 AMOD NKa LRa).
  assert (HG : G = r_base rga + snd aa + (24 + 40 * kk)).
  { subst G. rewrite Eg. rewrite (conc_region' st (aadd aa (AREA_HDR + META_SIZE * kk)) rga Hra). unfold aadd, AREA_HDR, META_SIZE. cbn [snd]. liac. }
  unfold NSLOTS in Hkk.
  (nelim (WR _ _ Hra) 5%nat; intros Ra0 _ _ RaC RaF). unfold alloc_ceiling in RaC.
  assert (NEa : fst aa <> fst b) by (intros E; rewrite E, Hr in Hra; injection Hra as <-; exact (NKa Kr)).
  pose proof (lr_lo_ge rga) as LRG.
  assert (GND : keep (G + 40 <= d \/ d + nn <= G)) by (unfold keep; destruct (DJ _ _ Hra NEa) as [GD|GD]; liac).
  assert (GNB : keep (G + 40 <= B \/ B + on <= G)).
  { unfold keep. destruct (DJR _ _ _ _ Hra Hr NEa) as [GB|GB]; rewrite ?(lr_lo_group _ Kr) in GB; liac. }
  assert (GNI : keep (G + 40 <= 0x10000 \/ 0x55000 <= G)).
  { unfold keep. destruct (rreserved_disjoint1 _ _ RaF ltac:(liac)) as [X|X]; liac. }
  assert (DNI : keep (d + nn <= 0x10000 \/ 0x55000 <= d)) by (unfold keep; exact (rreserved_disjoint1 _ _ DRF ltac:(liac))).
  assert (RNI : keep (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r)) by exact RI.
  assert (KDISJ : keep (d = B \/ (B + on <= d \/ d + nn <= B))) by exact DISJ.
  clear LRG.
  assert (AG1 : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 176 <= a < bv_unsigned sp) -> m2 (wa a) = m (wa a))
    by (intros a Ha Na; apply MU2; rewrite wa_unsigned by liac; cbn; liac).
  (* [comment removed for export] *)
  assert (MMX : rw_cells psegs mX G [C8 (pw st (m_prev (MR st g))); C8 (pw st (m_next (MR st g))); C8 (wz B); C4 (wz (m_avail (MR st g))); C4 (wz (m_freed (MR st g))); C8 (wz (meta_word (MR st g)))]).
  { unfold meta_cells in MM. rewrite Hmem in MM. unfold pw at 3 in MM. cbn [oconc] in MM. fold B in MM.
    eapply rrw_cells_agree'; [exact MM|]. cbn. intros a Ha. Time rewrite X1 by first [liac | liak1 GNB | liak1 GND]. Time apply AG1; liac. }
  (* [comment removed for export] *)
  assert (BKX : bytes_at psegs mX (d + 16 * off + 16 - 3) [b8 kb]).
  { Time (eapply (bytes_at_shift m mX (A - 3)); [exact B3| liac| cbn; liac| cbn; liak1 RNI| cbn; liak1 DNI|]).
    cbn. intros j Hj. replace (d + 16 * off + 16 - 3 + j) with (d + (16 * off + 13 + j)) by liac. Time rewrite X2 by liac.
    Time replace (B + (16 * off + 13 + j)) with (A - 3 + j) by liac. Time (apply AG1; liac). }
  Time assert (WRX : wr_at psegs mX (d + 16 * off + 16 - 3) (d + nn - 4 - (d + 16 * off + 16) + 4)) by (eapply wr_at_sub; [exact X4| liac| liac]).
  assert (SP' : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp - 64) by (rewrite unsigned_lit by liac; liac).
  assert (FRX : rw_cells psegs mX (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { rewrite SP'. eapply rrw_cells_agree'; [exact FR2|]. cbn. intros a Ha. apply X1; liac. }
  assert (MWR : 0 <= meta_word (MR st g) < 2^64) by (unfold meta_word; liac).
  eapply evt_mono.
  { eapply (rr_fin2_walk (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp s2' s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 lo)
      with (P := A) (n := n) (G := G) (k := kb) (Bold := B) (mword := meta_word (MR st g)) (avail := m_avail (MR st g)) (freed := m_freed (MR st g))
           (prev := pw st (m_prev (MR st g))) (next := pw st (m_next (MR st g)));
      first [exact MMX | exact BKX | exact WRX | exact FRX | exact MIX | idtac].
    - rewrite A0. apply unsigned_lit. liac.
    - rewrite A1. apply unsigned_lit. liac.
    - unfold wz. apply unsigned_lit. liac.
    - exact D0.
    - liac.
    - liac.
    - liac.
    - liac.
    - liac.
    - liac.
    - exact MWR.
    - liac.
    - liac.
    - liac.
    - liak1 GND.
    - rewrite SP'. exact STX.
    - liac. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 7%nat; intros mF RET MUF WMF MIF CH BEF).
  (nelim RET 17%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 EMS MI' ST').
  rewrite SP' in EMS, ST'. replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in EMS, ST' by liac. rewrite Z_to_bv_bv_unsigned in EMS. subst ms'.
  set (m' := rss_mem mF (d + 16 * off + 16) (d + nn - 4) n kb) in *.
  set (P' := d + 16 * off + 16) in *. assert (EP' : P' = d + 16 * off + 16) by reflexivity. clearbody P'.
  (* [comment removed for export] *)
  assert (AGF : forall a, 0 <= a < 2^64 -> ~ (G + 16 <= a < G + 24) -> ~ (G + 32 <= a < G + 40) -> a <> d + nn - 4 -> mF (wa a) = mX (wa a)).
  { intros a Ha N1 N1' N2. apply MUF. rewrite wa_unsigned by liac. cbn. liac. }
  assert (AGR : forall a, 0 <= a < 2^64 -> a <> P' - 3 -> ~ (P' + n <= a < d + nn - 4) -> m' (wa a) = mF (wa a)).
  { intros a Ha N1 N2. unfold m'. apply rss_mem_outside; rewrite ?wa_unsigned by (clear - Ha; lia); clear - N EP' D0 Ho NN DCE Ha N1 N2; lia. }
  assert (WMM : wmono psegs mX m') by (eapply wmono_trans; [exact WMF| apply rss_mem_wmono]).
  set (FP := fun a => (bv_unsigned sp - 176 <= a < bv_unsigned sp) \/ (B <= a < B + on) \/ (d <= a < d + nn) \/ (G + 16 <= a < G + 40)).
  assert (PE : rpres_except FP m m').
  { intros a Ha NC. subst FP. cbv beta in NC.
    assert (E1 : mX (wa a) = m (wa a)) by (rewrite X1 by (clear - Ha NC; lia); apply AG1; clear - Ha NC; lia).
    split.
    - rewrite AGR by (clear - Ha NC EP' Ho NN N D0; lia). rewrite AGF by (clear - Ha NC NN; lia). exact E1.
    - intros W. apply WMM. rewrite (rwview_ext m mX) by exact E1. exact W. }
  unfold rrealloc_post. exists w0, w1, w2, (Z_to_bv 64 P'), w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, m', errv2.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rrw_cells_agree'; [exact ERR2|]. intros a Ha. rewrite TP in Ha. unfold RATP in Ha. rewrite unsigned_lit in Ha by liac. cbn in Ha.
           rewrite AGR by (unfold keep in DNI; clear - Ha EP' Ho NN N DNI D0; lia). rewrite AGF by (unfold keep in GNI, DNI; clear - Ha GNI DNI NN; lia).
           apply X1; [clear - Ha; lia| unfold keep in RNI; clear - Ha RNI HBr EON; lia| unfold keep in DNI; clear - Ha DNI; lia]. }
  split. { eapply rauxv_ok_pres_B; [exact AV| exact PE| |]; subst FP; cbv beta; intros a Ha; unfold RAUXV_CELL in *;
           [clear - Ha HB RC HBr EON LO' SLO DCE G40 NN; lia| unfold keep in GNI, DNI, RNI; clear - Ha LO' SLO RNI HBr EON DNI GNI NN; lia]. }
  split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *)
  set (mn := Z.min k n).
  assert (MN : 0 <= mn <= k /\ mn <= n) by (subst mn; clear -Hk N; lia).
  assert (MNL : (Z.to_nat mn <= length old)%nat) by (clear -MN LEN; lia).
  assert (W' : wr_at psegs m' P' n).
  { eapply wr_at_transport; [| exact WMM]. eapply wr_at_sub; [exact X4| liac| liac]. }
  (nelim (rwr_at_bytes_exist m' (P' + mn) (n - mn) ltac:(eapply wr_at_sub; [exact W'| liac| liac]) ltac:(liac) ltac:(liak1 DNI)) 3%nat; intros junk JL JB).
  assert (OB : bytes_at psegs m' P' (firstn (Z.to_nat mn) old)).
  { pose proof BA as BA'. rewrite <- (firstn_skipn (Z.to_nat mn) old) in BA'. apply bytes_at_app in BA'. apply proj1 in BA'.
    eapply (bytes_at_shift m m' A P'); [exact BA'| liac| rewrite firstn_length_le by exact MNL; liac
      | rewrite firstn_length_le by exact MNL; liak1 RNI| rewrite firstn_length_le by exact MNL; liak1 DNI|].
    rewrite firstn_length_le by exact MNL. intros j Hj. rewrite Z2Nat.id in Hj by (clear -MN; lia).
    rewrite AGR by liac. rewrite AGF by liak1 GND. replace (P' + j) with (d + (16 * off + 16 + j)) by liac. rewrite X2 by liac.
    replace (B + (16 * off + 16 + j)) with (A + j) by liac. apply AG1; liac. }
  exists P', junk. split; [reflexivity|].
  split. { unfold rblock_range, alloc_ceiling. split; [liac|]. split; [| split; [liac|]; split; [liac| unfold keep in DNI; destruct DNI as [X|X]; [left|right]; liac]].
           rewrite EP'. apply mod16_d. exact DA. }
  (* [comment removed for export] *)
  (nelim IV 9%nat; intros L LS BL INV LIVE RESV SEC CORR HkBL).
  assert (Eb : b = (fst (fst p), 0)) by (rewrite Ec; cbn [fst]; rewrite <- Hb0; destruct b; reflexivity).
  set (st1 := set_tick (N.succ (s_tick st)) st).
  set (sA := pa_s5 st1 (fst p) g d nn).
  assert (Hs1 : s_slots st1 !! (fst p) = Some (g, 0)) by (rewrite <- I0; exact Hs).
  assert (Hgb1 : s_groups st1 !! (fst (fst p), 0) = Some (mkGhdr (Some g) ai)) by (rewrite <- Eb; exact Hgb).
  assert (Hsc1 : 48 <= m_sizeclass (MR st1 g)) by (change (MR st1 g) with (MR st g); liac).
  assert (Hr1 : s_regions st1 !! (fst (fst p)) = Some r) by (rewrite Ec; cbn [fst]; exact Hr).
  assert (DA' : d mod PGSZ = 0) by exact DA.
  assert (Hnn1 : PGSZ <= nn) by (unfold PGSZ; clear - NN N Ho; lia).
  assert (Hnn2 : 2 * PGSZ <= nn) by (unfold PGSZ, MMAP_THRESHOLD in *; liac).
  assert (Hnna : nn mod PGSZ = 0) by (unfold PGSZ; exact (proj1 (proj2 NN))).
  assert (HnnM : nn < LEN_MAX) by (unfold LEN_MAX; liac).
  assert (Hfree : forall q rq, s_regions st !! q = Some rq -> q <> fst (fst p) ->
            d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d).
  { intros q rq Hq NE. rewrite Ec in NE. cbn [fst] in NE. destruct (DJ q rq Hq NE) as [X|X]; unfold region_live_range, lr_lo in *;
      destruct (r_kind rq); cbn [fst snd]; unfold PGSZ; liac. }
  pose proof (rm_INV_removed st L BL LS (fst p) off k d nn INV HkBL) as INV1. fold st1 in INV1.
  pose proof (pa_facts2 st1 L (bl_remove (fst p) BL) LS (fst p) g ai d nn INV1 Hgb1 Hsc1 D0 DA' Hnn1 Hnn2 Hnna) as PAF.
  pose proof (pa_INVL st1 L (bl_remove (fst p) BL) LS (fst p) g ai r d nn INV1 Hgb1 Hs1 Hsc1 Hr1 D0 DA' Hnn1 Hnn2 Hnna HnnM DCE Hfree) as INVA.
  fold sA in PAF, INVA.
  assert (TKA : ticks_ok sA) by (apply ticks_ok_of_TKS; exact (TKS_of _ _ _ _ _ INVA)).
  assert (MR2 : rmrep st1 m2).
  { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MRP| exact MU2| exact WM2|].
    intros lo' hi' [E|[]]. injection E as <- <-. unfold alloc_ceiling. clear -SLO LO'. lia. }
  assert (PTR : rr_ptrs (fst (fst p)) g st1).
  { rewrite Ec. cbn [fst]. exact (rr_ptrs_intro st LB0 L BL LS b g r m C INV MRP (ex_intro _ ai Hgb) Hsc1 Hr Kr Hb0). }
  assert (MW : 0 <= m_avail (MR st1 g) < 2^32 /\ 0 <= m_freed (MR st1 g) < 2^32 /\ 0 < m_maplen (MR st1 g)) by (change (MR st1 g) with (MR st g); liac).
  assert (DJ1 : forall q rq, s_regions st1 !! q = Some rq -> q <> fst (fst p) -> r_base rq + round_up_pg (r_len rq) <= d \/ d + nn <= lr_lo rq).
  { intros q rq Hq NE. rewrite Ec in NE. cbn [fst] in NE. exact (DJ q rq Hq NE). }
  assert (RM : remap_mem m2 mF B d on nn (pa_len st1 g nn) G).
  { change (pa_len st1 g nn) with (Z.min on nn). split; [| split; [| split; [| split]]].
    - intros a Ha N1 N2 N3 N4. rewrite AGF by (clear - Ha N2 N3 N4 NN; lia). apply X1; [exact Ha| exact N1| exact N2].
    - intros j Hj NE. unfold IB in NE. rewrite AGF by (clear - Hj NE GND D0 DCE; unfold keep in GND; lia). apply X2. exact Hj.
    - (nelimp BEF 3%nat; intros _ _ BB). specialize (BB 0%nat ltac:(cbn; lia)). cbn [Z.of_nat nth_error] in BB. rewrite Z.add_0_r in BB.
      rewrite ref_mrd_overlay in BB by (rewrite wa_unsigned by (clear - D0 DCE NN; lia); clear - DNI NN; unfold keep in DNI; lia).
      unfold IB. replace (d + (nn - 4)) with (d + nn - 4) by (clear; lia). exact BB.
    - intros j Hj. (nelimp (wr_at_transport psegs mX mF d nn X4 WMF) 3%nat; intros _ _ W). specialize (W j Hj).
      rewrite ref_wview_overlay in W by (rewrite wa_unsigned by (clear - D0 DCE Hj; lia); clear - DNI Hj; unfold keep in DNI; lia). exact W.
    - intros j Hj NE. unfold IB in NE. rewrite AGF by (clear - Hj NE GND D0 DCE MLP NN; unfold keep in GND; lia). apply X3. exact Hj. }
  assert (CH' : rw_cells psegs mF G (rr_newcells st1 g d nn)).
  { unfold rr_newcells. change (MR st1 g) with (MR st g). change (pw st1) with (pw st).
    rewrite (meta_word_remap (MR st g) nn) by (clear - LI FB SC63 ML NN N62; lia). exact CH. }
  assert (Hmem1 : m_mem (MR st1 g) = Some (fst (fst p), 0)) by (rewrite <- Eb; exact Hmem).
  rewrite HBr in RM.
  pose proof (rmrep_remap st1 m2 mF (fst p) g r d nn MR2 PAF Hr1 Kr (eq_sym EON) Hmem1 ltac:(exists aa, ar, kk; auto) PTR MW D0 DA Hnn2 Hnna DCE DRF DJ1 RM CH') as MRA.
  fold sA in MRA.
  (* [comment removed for export] *)
  set (e' := aadd (fst (fst p), 0) (nn - 4)).
  assert (HrA : s_regions sA !! (fst Xup) = Some (pa_r' r d nn)).
  { unfold sA, Xup, aadd. cbn [fst]. rewrite (pa_lookup st1 (fst p) g r d nn Hr1). rewrite N.eqb_refl. reflexivity. }
  assert (KrA : r_kind (pa_r' r d nn) = RKGroup) by exact Kr.
  assert (FeA : fst e' = fst Xup) by reflexivity.
  assert (XU2 : snd Xup = 16 + 16 * off). { unfold Xup, aadd. rewrite Ec, I0, Hb0. cbn [snd]. unfold UNIT. clear; lia. }
  assert (P4 : 4 <= snd Xup) by (rewrite XU2; clear - Ho; lia).
  assert (PNE : snd Xup + n <= snd e') by (rewrite XU2; unfold e', aadd; cbn [snd]; clear - NN; lia).
  assert (EHI : snd e' + 1 <= round_up_pg (r_len (pa_r' r d nn))).
  { unfold e', aadd, pa_r'. cbn [snd r_len]. rewrite KStep.round_up_pg_aligned by exact (proj1 (proj2 NN)). clear; lia. }
  assert (RSA : snd e' - snd Xup - n < 2^32) by (rewrite XU2; unfold e', aadd; cbn [snd]; clear - NN N; lia).
  assert (IDX0 : 0 <= 0 < 32) by (clear; lia).
  assert (KB0 : 0 <= kb < 256 /\ Z.land kb 31 = 0) by (destruct KB8 as [K1 K2]; split; [exact K1| rewrite K2; exact I0]).
  assert (NOGRP : forall b0 gh, s_groups sA !! b0 = Some gh -> fst b0 = fst Xup -> snd b0 + 9 <= snd Xup - 3 \/ snd e' + 1 <= snd b0).
  { intros b0 gh Hb0g Efb. left. rewrite XU2.
    (nelim PAF 5%nat; intros _ _ _ GR5 _). rewrite GR5 in Hb0g. change (s_groups st1) with (s_groups st) in Hb0g.
    (nelim (ci_grps _ _ C b0 gh Hb0g) 3%nat; intros g0 Hg0 _).
    assert (HH : hosts st b0 g0). { destruct gh as [gm ai0]. cbn in Hg0. subst gm. exists ai0. exact Hb0g. }
    unfold Xup, aadd in Efb. cbn [fst] in Efb. rewrite Ec in Efb. cbn [fst] in Efb.
    destruct (alone x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 b0 g0 HH Efb) as [_ ->]. rewrite Hb0. clear - Ho; lia. }
  pose proof (rmrep_set_size_i sA mF Xup e' (pa_r' r d nn) n 0 kb MRA TKA HrA KrA FeA P4 (proj1 N) PNE EHI RSA IDX0 KB0 NOGRP) as SS.
  cbn [r_base pa_r'] in SS. rewrite XU2 in SS. unfold e', aadd in SS. cbn [snd] in SS.
  replace (d + (16 + 16 * off)) with P' in SS by (clear - EP'; lia). replace (d + (0 + (nn - 4))) with (d + nn - 4) in SS by (clear; lia).
  fold m' in SS. destruct SS as [R1 T1].
  assert (EFULL : rr_remap_full st (fst p) Xup n d nn = havoc Xup n (set_size_i Xup (aadd (fst (fst p), 0) (nn - 4)) n 0 sA)).
  { unfold rr_remap_full. rewrite Hs. cbv zeta. change (get_meta_rec st g) with (MR st g). rewrite Hmem. cbn [default]. rewrite Eb, I0.
    unfold sA, pa_s5, pa_s4, pa_s3, pa_s2, pa_len, IB. reflexivity. }
  (* [comment removed for export] *)
  assert (HEAP : RHEAP (set_m (cs_remap (ps_m s) (fst b) g d nn) s) ((p, P', n) :: lb_remove p LB) m').
  { exists (rr_remap_full st (fst p) Xup n d nn), ((p, P', n) :: lbrm LB0 (p, A, k)).
    split; [apply perm_blocks'|].
    split. { rewrite strip_rr_remap_full, Hs, Hst. cbn [ps_m set_m]. rewrite Ec. reflexivity. }
    split. { rewrite EFULL. exact (proj1 (rmrep_havoc _ _ Xup n R1 T1)). }
    split.
    - (* [comment removed for export] *)
      change (brk_link (strip (rr_remap_full st (fst p) Xup n d nn)) (ps_brk s)). rewrite strip_rr_remap_full, Hs.
      unfold brk_link. rewrite ctx_cs_remap. change (ctx (strip st)) with (ctx st).
      pose proof BLK as BL0. unfold brk_link in BL0.
      (nelim PTR 8%nat; intros _ _ _ _ _ _ PB _). change (ctx st1) with (ctx st) in PB.
      destruct (c_brk (ctx st)) as [| |rid' boff] eqn:HBK; try exact I.
      rewrite conc_cs_remap by (cbn; rewrite Ec; cbn [fst]; rewrite Hr; discriminate).
      cbn [fst snd]. rewrite (proj2 (N.eqb_neq _ _) PB). exact BL0.
    - (* [comment removed for export] *)
      eapply areach_ext; [exact AR|].
      replace P' with (d + UNIT + UNIT * off) by (rewrite EP'; unfold UNIT; clear; lia).
      apply (aext_remap ref_reserved st LB0 p A k n off d nn g i Hin0 (proj1 Ho) EA (proj1 N));
        first [exact Hs| exact Hs1| exact Hsc1| exact D0| exact DA'| exact Hnn2| exact Hnna| exact HnnM| exact DCE| exact Hfree| unfold UNIT, IB; clear - NN N; lia]. }
  split; [exact HEAP|].
  split.
  { (* [comment removed for export] *)
    intros a Ha CA. apply PE; [exact Ha|]. subst FP; cbv beta.
    destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
    - clear - CA Ha SPR LO' SLO RC HBr EON DCE G40. lia.
    - clear - CA Ha SPR LO' SLO RNI HBr EON DNI GNI. unfold keep in *. lia.
    - rewrite (lb_remove_lbrm LB p A k) in Hb' by (first [exact Hin | eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ C)]]).
      apply (In_lbrm_perm LB LB0) in Hb'; [| apply Permutation_sym; exact PERM].
      unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [HinL NEQ].
      assert (NES : blk_slot blk' <> fst p). { intros E. cbn [blk_slot fst] in NEQ. rewrite E, MI_Kit.aptr_eqb_refl in NEQ. exact NEQ. }
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
      (nelim (WR _ _ Hrg) 5%nat; intros _ _ _ RGC RGF). unfold alloc_ceiling in RGC.
      destruct (N.eq_dec (fst (blk_slot blk')) (fst b)) as [EQR|NER].
      + (* [comment removed for export] *)
        exfalso. destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL) as [(g0 & i0 & bg0 & Hs0 & _) _ _].
        (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (blk_slot blk') g0 i0 Hs0 EQR) 3%nat; intros _ _ EQS).
        (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (fst p) g i Hs ltac:(rewrite Ec; reflexivity)) 3%nat; intros _ _ EQP).
        apply NES. rewrite EQS, <- EQP. reflexivity.
      + assert (NEa' : fst (blk_slot blk') <> fst aa) by (intros E; rewrite E, Hra in Hrg; injection Hrg as <-; exact (NKa Krg)).
        destruct (DJR _ _ _ _ Hrg Hr NER) as [D1|D1]; rewrite ?(lr_lo_group _ Krg), ?(lr_lo_group _ Kr) in D1;
        destruct (DJ _ _ Hrg NER) as [D2|D2]; rewrite ?(lr_lo_group _ Krg) in D2;
        destruct (DJR _ _ _ _ Hrg Hra NEa') as [D3|D3]; rewrite ?(lr_lo_group _ Krg) in D3;
        clear - Ha Hab A16 AEND RGC D1 D2 D3 HBr EON HG Hkk A0a A4096 LRa SPR LO' SLO; lia. }
  split.
  { apply rw_cells_of_bytes.
    - cbn. rewrite firstn_length_le by exact MNL. split; [reflexivity|]. split; [exact JL| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OB|]. rewrite firstn_length_le by exact MNL. rewrite Z2Nat.id by (clear - MN; lia). exact JB.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_add, !Z2Nat.id by (clear - MN N; lia). replace (mn + (n - mn)) with n by (clear; lia). exact W'. }
  (* [comment removed for export] *)
  unfold keep in KDISJ. destruct KDISJ as [ED|SEP].
  - left. rewrite EP', EA, HP0, ED. unfold UNIT. clear; lia.
  - right. intros b0 Hb0L E0.
    assert (Hb00 : In b0 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb0L]).
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) b0 Hb00) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
    destruct (N.eq_dec (fst (blk_slot b0)) (fst b)) as [EQR|NER].
    + (* [comment removed for export] *)
      destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b0 Hb00) as [(g0 & i0 & bg0 & Hs0 & _) _ _].
      (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (blk_slot b0) g0 i0 Hs0 EQR) 3%nat; intros _ _ EQS).
      (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (fst p) g i Hs ltac:(rewrite Ec; reflexivity)) 3%nat; intros _ _ EQP).
      assert (EB0 : b0 = (p, A, k)).
      { apply (NoDup_map_inj_in blk_slot LB0 (ci_nodup _ _ C) b0 (p, A, k) Hb00 Hin0). cbn [blk_slot fst]. rewrite EQS, <- EQP. reflexivity. }
      rewrite EB0 in E0. cbn [blk_addr fst snd] in E0.
      clear - E0 EP' EA HP0 HBr EON SEP NN Ho NFa MLP Hfit Estride. lia.
    + pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b0 Hb00)) as SZ0.
      destruct (DJ _ _ Hrg NER) as [D2|D2]; rewrite ?(lr_lo_group _ Krg) in D2.
      * clear - E0 EP' A16 AEND D2 NN Ho N SZ0. lia.
      * clear - E0 EP' A16 AEND D2 NN Ho N SZ0. lia.
Qed.
End RR.


End CeilWrap.
(* [comment removed for export] *)
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac clear_keep := repeat match goal with K : keep _ |- _ => clear K end.
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; clear_keep; lia.
Ltac liak1 H := prune; unfold keep in H; clear_keep; lia.
Ltac liak2 H1 H2 := prune; unfold keep in H1, H2; clear_keep; lia.
Ltac liak3 H1 H2 H3 := prune; unfold keep in H1, H2, H3; clear_keep; lia.
Notation RAREACH := (AREACH_from ref_reserved).
End RF_realloc_G2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_ifaceP.
Module RF_realloc_G3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.



Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry RF_realloc_G1.
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
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Lemma rheap_pres_of_munch LB SP W m m' :
  munch W m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros MU WM H a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. apply H; assumption.
Qed.

Lemma In_lb_remove b p LB : In b (lb_remove p LB) -> In b LB.
Proof using . unfold lb_remove. intros H. apply In_filter_iff in H. exact (proj1 H). Qed.

Section RR.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : PState) (LB : list block) (p : bptr) (A k n lo Bx : Z) (old : list byte) (errv : word).
Variables (st : mstate) (LB0 : list block) (g b : aptr) (r : region) (i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MRP : rmrep st m.
Hypothesis BLK : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis RF : rrF st m LB0 p A k g b r i off.
Hypothesis Hin : In (p, A, k) LB.
Hypothesis Hin0 : In (p, A, k) LB0.
Hypothesis BA : bytes_at psegs m A old.
Hypothesis LEN : Z.of_nat (length old) = k.
Hypothesis AV : rauxv_ok m Bx.
Hypothesis HB : bv_unsigned sp <= Bx.
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - RREALLOC_STACK.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis A1 : a1 = Z_to_bv 64 n.
Hypothesis N : 0 <= n < 2^32.


(* [comment removed for export] *)
Variables (mm : mem) (errvm : word).
Hypothesis MUm : munch [(bv_unsigned sp - 176, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)] m mm.
Hypothesis WMm : wmono psegs m mm.
Hypothesis MIm : mem_inv psegs mm.
Hypothesis STm : stk psegs mm lo (bv_unsigned sp + -64).
Hypothesis FRm : rw_cells psegs mm (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6).
Hypothesis ERRm : rw_cells psegs mm (errno_addr tp) [C4 errvm].

(* [comment removed for export] *)
Lemma rr_fallback_thm : forall (vra t0' t1' t2' s0' s1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' : word),
  implM psegs (rr_fallback p n) s
        (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A k n lo Bx old m)
        (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' s0' s1' a0 a1 a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (A + k)) s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 RR_MALLOC) fc None mm (seg_rom psegs)).
Proof using A0 A1 AR AV BA BLK ERRm FRm HB Hin Hst LEN LO MIm MRP MUm N PERM SLO STm TP WMm.
  intros.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK in SLO. pose proof LO as LO'. unfold alloc_ceiling in LO'.
  assert (ETP : bv_unsigned tp + -164 = RERRNO). { rewrite TP. unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. }
  assert (HEAP : RHEAP s LB m). { exists st, LB0. split; [exact PERM|]. split; [exact Hst|]. split; [exact MRP|]. split; [exact BLK| exact AR]. }
  pose proof (RHEAP_block_range_proof s LB m (p, A, k) HEAP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR. unfold rblock_range, alloc_ceiling in BR.
  assert (ABx : alloc_ceiling <= Bx) by (pose proof AV as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & AB & _); exact AB). unfold alloc_ceiling in ABx.
  assert (HEAPm : RHEAP s LB mm).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MUm| exact WMm|].
    constructor; [left; cbn [fst snd]; unfold alloc_ceiling; lia|].
    constructor; [|constructor]. right; left. cbn [fst snd]. rewrite ETP. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
  assert (AVm : rauxv_ok mm Bx).
  { eapply rauxv_ok_frame; [exact AV| exact MUm| exact WMm|].
    constructor; [cbn [fst snd]; unfold RAUXV_CELL; lia|]. constructor; [|constructor]. cbn [fst snd]. rewrite ETP. unfold RERRNO, RAUXV_CELL. lia. }
  assert (PRESm : forall LB', (forall b0, In b0 LB' -> In b0 LB) -> rheap_pres LB' (bv_unsigned sp) m mm).
  { intros LB' HLB'. eapply rheap_pres_of_munch; [exact MUm| exact WMm|]. intros a Ha Hc. rewrite ETP. cbn [outside]. unfold RERRNO.
    destruct Hc as [Hc|[[Hc NS]|(b0 & Hb0 & Hab)]].
    - clear -Hc SLO LO'. lia.
    - unfold ralloc_static, RERRNO in NS. clear -Hc NS SLO LO'. lia.
    - pose proof (RHEAP_block_range_proof s LB m b0 HEAP (HLB' b0 Hb0)) as (_ & _ & _ & B1 & B2). unfold alloc_ceiling in B1. clear -Hab B1 B2 SLO LO'. lia. }
  assert (SP64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp - 64) by (rewrite unsigned_lit by lia; lia).
  unfold rr_fallback.
  eapply (implM_bind psegs).
  { eapply (implM_evt psegs).
    { unfold RR_MALLOC. step. step. step. step.
      lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms0 : machine_state => ms0 = ms) end.
      apply evt_done. reflexivity. }
    cbv beta. intros ms1 ->.
    change (Z_to_bv 64 89264) with (Z_to_bv 64 rmalloc_entry).
    eapply rmalloc_entry_spec; first [exact HEAPm| exact AVm| exact LO| exact ERRm| exact MIm| exact TP| exact A1| exact N| idtac].
    - rewrite SP64. lia.
    - rewrite SP64. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact STm.
    - rewrite SP64. unfold RMALLOC_ESTACK. lia. }
  cbv beta. intros rq s' ms' POST.
  destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AV' & PRES' & FA' & SO' & RES).
  rewrite SP64 in ST', PRES'. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST' by lia.
  replace (ret_pc (Z_to_bv 64 93992)) with (Z_to_bv 64 93992) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  assert (FR' : rw_cells psegs m' (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rheap_pres_rw_cells; [exact PRES'| exact FRm| left; lia]. }
  destruct rq as [q|].
  2:{ (* [comment removed for export] *)
    destruct RES as [-> HEAP'].
    apply implM_ret.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. 2:{ exfalso. clear -K1. cbn in K1. lia. }
    unfold RF_realloc_A.rr_frame in FR'.
    step. step. step. step. step. step. step. step. step. step.
    release_frame FR' ST' (bv_unsigned sp).
    apply evt_done. unfold rrealloc_post. do 15 eexists. exists m', errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AV'|].
    split; [exact FA'|]. split; [exact SO'|]. split; [reflexivity|]. split; [exact HEAP'|].
    eapply rheap_pres_trans; [apply PRESm; auto|]. eapply rheap_pres_weaken; [exact PRES'| lia| auto]. }
  (* [comment removed for export] *)
  destruct RES as (A' & junk & -> & BR' & HEAP' & JK & _).
  pose proof BR' as BR2. unfold rblock_range, alloc_ceiling in BR2.
  pose proof (RHEAP_blocks_nodup_proof s' _ m' HEAP') as NDi. cbn [map blk_id fst] in NDi.
  pose proof (CJ_heap_inst0.RHEAP_addr_nodup s' _ m' HEAP') as NDa. cbn [map blk_addr fst snd] in NDa.
  apply List.NoDup_cons_iff in NDi as [Hq NDi2]. apply List.NoDup_cons_iff in NDa as [HA2 NDa2].
  assert (QP : q <> p). { intros ->. apply Hq. apply in_map_iff. exists (p, A, k). split; [reflexivity| exact Hin]. }
  assert (DISJ : forall b0, In b0 LB -> A' + n <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= A').
  { intros b0 Hb0. pose proof (RHEAP_blocks_disjoint_proof s' _ m' (q, A', n) b0 HEAP' (or_introl eq_refl) (or_intror Hb0)) as D.
    cbn [blk_addr blk_size blk_id fst snd] in D. apply D. intros E. apply Hq. rewrite E. apply in_map_iff. exists b0; auto. }
  pose proof (DISJ _ Hin) as DJp. cbn [blk_addr blk_size fst snd] in DJp.
  set (mn := Z.min k n).
  assert (MN : 0 <= mn <= k /\ mn <= n /\ (mn = k \/ mn = n)) by (subst mn; clear -BR N; lia).
  (* [comment removed for export] *)
  pose proof (rw_cells_split_CB psegs m' A' [] (Z.to_nat n) junk [] [Z.to_nat mn; Z.to_nat (n - mn)]%nat JK ltac:(cbn [sum_nat]; lia)) as JK2.
  cbn [app mk_CB_cells] in JK2.
  set (j1 := firstn (Z.to_nat mn) junk) in JK2. set (j2 := firstn _ _) in JK2.
  apply (proj1 (Malloc_ifaceP.rw_cells_app psegs m' A' [CB (Z.to_nat mn) j1] [CB (Z.to_nat (n - mn)) j2])) in JK2.
  destruct JK2 as [DST TAIL]. cbn [cells_size csize] in TAIL. rewrite Nat.add_0_r, Z2Nat.id in TAIL by lia.
  (* [comment removed for export] *)
  assert (OLD' : bytes_at psegs m' A old).
  { eapply rheap_pres_bytes_at; [exact PRES'| | right; right; exists (p, A, k); cbn [blk_addr blk_size fst snd]; split; [exact Hin| lia]].
    eapply bytes_at_transport; [exact BA| exact MUm|]. rewrite LEN, ETP. unfold RERRNO. cbn [disjoint_from]. clear -BR SLO LO'. lia. }
  assert (SRC : bytes_at psegs m' A (firstn (Z.to_nat mn) old)).
  { rewrite <- (firstn_skipn (Z.to_nat mn) old) in OLD'. apply bytes_at_app in OLD'. exact (proj1 OLD'). }
  assert (SRCL : length (firstn (Z.to_nat mn) old) = Z.to_nat mn) by (rewrite firstn_length_le; lia).
  eapply (implM_evt psegs _ _ _ (fun ms2 => exists (w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 : word) (m2 : mem),
     ms2 = MS (mkR (Z_to_bv 64 0x16f50) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp w0 w1 w2 (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 A) wa1 wa2 wa3 wa4 wa5 wa6 wa7
                   (Z_to_bv 64 (A + k)) s3' s4' s5' s6' s7 s8 s9 s10 s11 w3 w4 w5 w6) F (Z_to_bv 64 rfree_entry) fc None m2 (seg_rom psegs)
     /\ munch [(A', A' + mn)] m' m2 /\ wmono psegs m' m2 /\ mem_inv psegs m2
     /\ rw_cells psegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old)])).
  { rewrite A0, A1.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. { exfalso. clear -K1 BR2. lia. }
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (A + k)), (unsigned_lit A) by lia. replace (A + k - A) with k by lia.
    lazymatch goal with |- evt _ ?P _ =>
      assert (JOIN : forall a2v : word, a2v = Z_to_bv 64 mn ->
        evt psegs P (MS (mkR (Z_to_bv 64 93992) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 A') (Z_to_bv 64 k) a2v ra3 ra4 ra5 ra6 ra7
                         (Z_to_bv 64 (A + k)) s3' s4' s5' s6' s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x16f3c) fc None m' (seg_rom psegs)))
    end.
    { intros a2v ->.
      (* [comment removed for export] *)
      step. step. step.
      eapply evt_cut.
      { eapply (memcpy_spec) with (src := firstn (Z.to_nat mn) old) (junk := j1);
          rewrite ?(unsigned_lit A), ?(unsigned_lit A'), ?(unsigned_lit mn) by lia.
        - exact SRC.
        - exact SRCL.
        - exact DST.
        - clear -DJp MN BR BR2. lia.
        - exact MI'. }
      cbv beta. intros ms2 (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & DST2 & SRC2).
      rewrite ?(unsigned_lit A), ?(unsigned_lit A'), ?(unsigned_lit mn) in MU2, DST2 by lia.
      replace (ret_pc (Z_to_bv 64 94024)) with (Z_to_bv 64 94024) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      step. step. apply evt_done. do 15 eexists. split; [reflexivity|]. auto. }
    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2.
    - apply JOIN. f_equal. subst mn. clear -K2 MN. lia.
    - step. apply JOIN. f_equal. subst mn. clear -K2 MN. lia. }
  cbv beta. intros ms2 (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & DST2).
  (* [comment removed for export] *)
  assert (ST2 : stk psegs m2 lo (bv_unsigned sp + -64)).
  { eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2|]. cbn [disjoint_from]. clear -MN BR2 LO' SLO. lia. }
  assert (ERR2 : rw_cells psegs m2 (bv_unsigned tp + -164) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2|]. rewrite ETP. unfold RERRNO. cbn [disjoint_from cells_size csize Nat.add]. clear -MN BR2. lia. }
  assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rw_cells_transport; [exact FR'| exact MU2| exact WM2|]. cbn [disjoint_from]. clear -MN BR2 LO' SLO. lia. }
  assert (TAIL2 : rw_cells psegs m2 (A' + mn) [CB (Z.to_nat (n - mn)) j2]).
  { eapply rw_cells_transport; [exact TAIL| exact MU2| exact WM2|]. cbn [disjoint_from]. clear -MN. lia. }
  assert (AV2 : rauxv_ok m2 Bx).
  { eapply rauxv_ok_frame; [exact AV'| exact MU2| exact WM2|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. clear -MN BR2 ABx. lia. }
  assert (HEAP2 : RHEAP s' ((q, A', n) :: LB) m2).
  { eapply RHEAP_frame_proof; [exact HEAP'| exact MU2| exact WM2|]. constructor; [|constructor].
    right; right. exists (q, A', n). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity| clear -MN; lia]. }
  assert (LBeq : lb_remove p ((q, A', n) :: LB) = (q, A', n) :: lb_remove p LB).
  { rewrite CJ_heap_inst0.lb_remove_cons. cbn [blk_id fst]. destruct (bptr_eqb q p) eqn:E; [|reflexivity].
    exfalso. apply CJ_heap_inst0.bptr_eqb_eq in E. exact (QP E). }
  eapply (implM_bind psegs).
  { eapply rfree_entry_spec; [exact HEAP2| right; exact Hin| exact AV2| rewrite SP64; clear -HB; lia| rewrite SP64| exact LO| rewrite SP64; unfold RFREE_ESTACK; clear -SLO; lia| exact ERR2| exact MI2| exact TP| reflexivity].
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact ST2. }
  cbv beta. intros [] s'' ms3 FP.
  destruct FP as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & ERR3 & AV3 & PRES3 & FA3 & SO3 & HEAP3).
  rewrite SP64 in ST3, PRES3. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST3 by lia.
  rewrite LBeq in PRES3, HEAP3.
  apply implM_ret.
  replace (ret_pc (Z_to_bv 64 94032)) with (Z_to_bv 64 94032) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR3 : rw_cells psegs m3 (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rheap_pres_rw_cells; [exact PRES3| exact FR2| left; lia]. }
  unfold RF_realloc_A.rr_frame in FR3.
  (* [comment removed for export] *)
  step. step.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR3 ST3 (bv_unsigned sp).
  apply evt_done. unfold rrealloc_post. do 15 eexists. exists m3, errv'.
  split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AV3|].
  split; [rewrite FA3; exact FA'|]. split; [rewrite SO3; exact SO'|].
  fold mn.
  exists A', j2. split; [reflexivity|]. split; [exact BR'|]. split; [exact HEAP3|].
  split.
  { eapply rheap_pres_trans; [apply PRESm; intros b0 Hb0; exact (In_lb_remove _ _ _ Hb0)|].
    eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact PRES'| lia| intros b0 Hb0; exact (In_lb_remove _ _ _ Hb0)]|].
    eapply rheap_pres_trans.
    - eapply rheap_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc. cbn [outside]. split; [|exact I].
      destruct Hc as [Hc|[[Hc NS]|(b0 & Hb0 & Hab)]].
      + clear -Hc MN BR2 SLO LO'. lia.
      + clear -Hc MN BR2. lia.
      + pose proof (DISJ b0 (In_lb_remove _ _ _ Hb0)) as D. clear -Hab D MN. lia.
    - eapply rheap_pres_weaken; [exact PRES3| lia| intros b0 Hb0; right; exact Hb0]. }
  split.
  { assert (CH2 : rw_cells psegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old); CB (Z.to_nat (n - mn)) j2]).
    { apply (proj2 (Malloc_ifaceP.rw_cells_app psegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old)] [CB (Z.to_nat (n - mn)) j2])).
      split; [exact DST2|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact TAIL2. }
    eapply rheap_pres_rw_cells; [exact PRES3| exact CH2|]. right; right. exists (q, A', n). split; [left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. clear -MN. lia. }
  right. intros b0 Hb0 E. apply HA2. rewrite E. apply in_map_iff. exists b0; auto.
Qed.
End RR.


End CeilWrap.
(* [comment removed for export] *)
Notation RAREACH := (AREACH_from ref_reserved).
End RF_realloc_G3.

(* [comment removed for export] *)
Module RF_realloc_null.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.
Import RF_realloc_mentry.
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
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem rrealloc_null_spec : rrealloc_null_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
         HP AV HB ST LO SLO ERR MI TP A0 A1 N.
  eapply (implM_evt psegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs))).
  { unfold RREALLOC_SYM. subst a0. step. step. if_true. step. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rmalloc_entry_spec ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv);
    try eassumption. unfold RMALLOC_STACK in SLO. unfold RMALLOC_ESTACK. lia.
Qed.


End CeilWrap.
End RF_realloc_null.

(* [comment removed for export] *)
Module RF_realloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_realloc_P RF_realloc_G1 RF_realloc_G2 RF_realloc_G3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
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
Local Unset Keyed Unification.

Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; lia.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Lemma andb3_true_iff_Z a1 b1 a2 b2 a3 b3 :
  (a1 <=? b1) && (a2 <? b2) && (a3 <=? b3) = true <-> (a1 <= b1 /\ a2 < b2 /\ a3 <= b3).
Proof. rewrite !Bool.andb_true_iff, !Z.leb_le, Z.ltb_lt. tclose. Qed.
Lemma cond1_false a1 b1 a2 b2 a3 b3 : ~ (a1 <= b1 /\ a2 < b2 /\ a3 <= b3) -> (a1 <=? b1) && (a2 <? b2) && (a3 <=? b3) = false.
Proof using . intros H. destruct ((a1 <=? b1) && (a2 <? b2) && (a3 <=? b3)) eqn:E; [|reflexivity]. exfalso. apply H. apply andb3_true_iff_Z. exact E. Qed.
Lemma cond1_true a1 b1 a2 b2 a3 b3 : a1 <= b1 -> a2 < b2 -> a3 <= b3 -> (a1 <=? b1) && (a2 <? b2) && (a3 <=? b3) = true.
Proof using . intros. apply andb3_true_iff_Z. auto. Qed.
Lemma cond2_false a1 b1 a2 b2 : ~ (a1 <= b1 /\ a2 <= b2) -> (a1 <=? b1) && (a2 <=? b2) = false.
Proof using . intros H. destruct (Z.leb_spec a1 b1); destruct (Z.leb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. auto. Qed.
Lemma cond2_true a1 b1 a2 b2 : a1 <= b1 -> a2 <= b2 -> (a1 <=? b1) && (a2 <=? b2) = true.
Proof using . intros. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.leb_le _ _)) by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mem_ext (m1 m2 : mem) : (forall x, m1 x = m2 x) -> m1 = m2.
Proof using . intros H. apply functional_extensionality. exact H. Qed.

(* [comment removed for export] *)
Lemma bytes_at_same_byte m m' a bs (x : word) :
  bytes_at psegs m a bs -> bytes_at psegs m' a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ 0x55000 <= a) ->
  a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x.
Proof.
  intros (A0 & A1 & H1) (_ & _ & H2) Hi Hx.
  assert (E : x = wa (a + Z.of_nat (Z.to_nat (bv_unsigned x - a)))).
  { rewrite Z2Nat.id by lia. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  specialize (H1 (Z.to_nat (bv_unsigned x - a)) ltac:(lia)). specialize (H2 (Z.to_nat (bv_unsigned x - a)) ltac:(lia)).
  rewrite <- E in H1, H2. rewrite ref_mrd_overlay in H1, H2 by lia. rewrite H1, H2. reflexivity.
Qed.

Lemma mword_page mr : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  meta_word mr - meta_word mr mod 4096 = m_maplen mr * 4096.
Proof using .
  intros. unfold meta_word. set (L := m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr).
  replace (L + 4096 * m_maplen mr) with (L + m_maplen mr * 4096) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mword_same mr : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^35 ->
  Z.lor (Z.land (meta_word mr) 4095) (m_maplen mr * 4096) = meta_word mr.
Proof using .
  intros. rewrite <- (meta_word_remap mr (m_maplen mr * 4096)); [| lia| lia| lia| lia| lia| apply Z_mod_mult].
  unfold meta_word. destruct mr; cbn in *. rewrite Z.div_mul by lia. rewrite MI_WRemap.land_ones52 by lia. reflexivity.
Qed.

Lemma rreserved_free_intro a n : 0 <= n -> (a + n <= 0x10000 \/ 0x55000 <= a) -> ranges_free ref_reserved a n = true.
Proof.
  intros Hn H. apply ranges_free_intro. intros b k Hin. unfold ref_reserved in Hin. cbn in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma wr_at_join segs m a n1 n2 : wr_at segs m a n1 -> wr_at segs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at segs m a (n1 + n2).
Proof using .
  intros (A0 & _ & W1) (_ & A2 & W2) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z_lt_dec i n1); [apply W1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Theorem rrealloc_spec : rrealloc_stmt.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A k n lo Bx old errv.
  intros HR Hin BA LEN AV HB ST LO SLO ERR MI TP A0 A1 N.
  (nelim HR 6%nat; intros st LB0 PERM Hst MRP [BLK AR]).
  assert (Hin0 : In (p, A, k) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  (nelim (rrF_intro st m LB0 p A k AR MRP Hin0) 6%nat; intros g b r i off RF).
  pose proof RF as RF'.
  destruct RF' as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH IV].
  cbv zeta in BY. (nelim BY 8%nat; intros B4 B3 B2 HQ EQ16 BF BC BE).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof SLO as SLO'. unfold RREALLOC_STACK in SLO'. pose proof LO as LO'. unfold alloc_ceiling in LO', RC, G40.
  (nelimp MRP 6%nat; intros WF _ GL _ _ SH). (nelimp WF 5%nat; intros Hres WR DJR WA WG).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof (go_stride _ _ _ GOK) as [S16 SM]. pose proof (go_li _ _ _ GOK) as LI. pose proof (go_avail _ _ _ GOK) as AVr. pose proof (go_freed _ _ _ GOK) as FRr.
  pose proof (go_freeable _ _ _ GOK) as FB. pose proof (go_sc _ _ _ GOK) as GSC. pose proof (go_maplen _ _ _ GOK) as ML. (nelimp (go_region _ _ _ GOK) 7%nat; intros rX HrX _ _ _ _ TOP).
  rewrite Hr in HrX. injection HrX as <-.
  change (get_meta_rec st g) with (MR st g) in S16, SM, LI, AVr, FRr, FB, GSC, ML, TOP.
  (* [comment removed for export] *)
  set (STR := get_stride (MR st g)) in *. set (P0 := conc st (fst p)) in *. set (B := conc st b) in *. set (G := conc st g) in *.
  assert (ESTR : STR = RF_realloc_G1.Xstride st g) by reflexivity. assert (EP0 : P0 = RF_realloc_G1.XP0 p st) by reflexivity.
  assert (EB : B = RF_realloc_G1.XB st b) by reflexivity. assert (EG : G = RF_realloc_G1.XG st g) by reflexivity.
  assert (EE : RF_realloc_G1.XE p st g = P0 + STR - 4) by reflexivity.
  assert (ERES : RF_realloc_G1.Xres p A k st g = P0 + STR - 4 - A - k) by reflexivity.
  assert (ESC : RF_realloc_G1.Xsc st g = m_sizeclass (MR st g)) by reflexivity.
  assert (EMW : RF_realloc_G1.Xmword st g = meta_word (MR st g)) by reflexivity.
  unfold UNIT, IB in *.
  assert (SI0 : 0 <= STR * i) by (apply Z.mul_nonneg_nonneg; clear - S16 Hi; lia).
  assert (SIL : STR * i + STR <= STR * (m_last_idx (MR st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; clear - S16 Hi; lia. }
  assert (HP0 : P0 = r_base r + snd b + 16 + STR * i) by (rewrite Cc, Ec; cbn [snd]; clear; lia).
  assert (HBr : B = r_base r + snd b) by exact Cb.
  assert (ABND : r_base r + 16 <= A /\ 0 <= k /\ A + k + 4 <= P0 + STR /\ P0 + STR <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling)
    by (clear - EA HP0 R0 B0 SI0 Ho RC SPAN SIL Hfit Hk; lia).
  (* [comment removed for export] *)
  unfold raw_realloc.
  eapply (implM_bind psegs _ _ _ (fun a s1' ms1 => a = s /\ s1' = s /\ ms1 = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s_ s1' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  rewrite (rplan_eq m s p A k n old st LB0 g b r i off Hst RF). rewrite <- ESTR, ESC, <- EB.
  replace (16 * off) with (A - P0) by (clear - EA; lia).
  (* [comment removed for export] *)
  eapply implM_evt; [exact (rr_prefix ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p A k n lo old st LB0 g b r i off RF LEN ST LO SLO MI A0 A1 N)|].
  cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 t3' t4' -> MU1 WM1 MI1 ST1 FR1).
  rewrite EE, ERES, ESC, EMW, <- EB, <- EG, <- ESTR. unfold UNIT, IB.
  replace (16 * off) with (A - P0) by (clear - EA; lia).
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -64)) in *.
  set (E := P0 + STR - 4) in *.
  set (sc := m_sizeclass (MR st g)) in *.
  set (rom := seg_rom psegs) in *.
  assert (SP' : bv_unsigned sp' = bv_unsigned sp - 64) by (subst sp'; rewrite unsigned_lit by (clear - SPR SLO' LO'; lia); clear; lia).
  assert (XP1 : forall a bs, bytes_at psegs m a bs -> a + Z.of_nat (length bs) <= lo -> bytes_at psegs m1 a bs).
  { intros a bs Ha Hl. eapply bytes_at_transport; [exact Ha| exact MU1|]. cbn [disjoint_from]. split; [left; clear -Hl SLO'; lia| exact I]. }
  assert (ERR1 : rw_cells psegs m1 (errno_addr tp) [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite TP. unfold RATP. rewrite unsigned_lit by (clear; lia). cbn. clear - SPR SLO' LO'. lia. }
  (* [comment removed for export] *)
  set (QIN := fun ms => exists t1'' t2'' t3'' a4' a5' a7',
      ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1'' t2'' s0 (wz G) a0 a1 (Z_to_bv 64 (size_to_class n + 1)) (Z_to_bv 64 sc) a4' a5'
                   (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6) F (Z_to_bv 64 RR_INPLACE) fc None m1 rom
      /\ n <= E - A /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1).
  set (QMAL := fun ms => exists t1'' t2'' t3'' a2' a4' a5' a7',
      ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1'' t2'' s0 (wz G) a0 a1 a2' (Z_to_bv 64 sc) a4' a5'
                   (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6) F (Z_to_bv 64 RR_MALLOC) fc None m1 rom
      /\ ~ (n <= E - A /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1) /\ ~ (48 <= sc /\ MMAP_THRESHOLD <= n)).
  set (QBIG := fun ms => exists t2'' t3'' a5',
      ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + STR * i + 16)) t2'' s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz (meta_word (MR st g))) a5'
                   (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0)) (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6) F (Z_to_bv 64 RR_BIG) fc None m1 rom
      /\ MMAP_THRESHOLD <= n /\ sc = 63).
  eapply implM_evt.
  { eapply (rr_decide_walk ra sp' gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz G) _ (wz B) (wz (meta_word (MR st g))) t4' F fc m1 A n sc E (E - A - k)
              (fun ms => QIN ms \/ QMAL ms \/ QBIG ms)).
    - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
    - rewrite A1. apply unsigned_lit. clear - N; lia.
    - exact N.
    - clear - ABND R0 Hk. subst E. lia.
    - clear - ABND R0 Hk. subst E. lia.
    - clear - GSC. subst sc. lia.
    - clear - GSC. subst sc. lia.
    - exact MI1.
    - intros C1 C2 C3 t1'' t2'' t3'' a4' a5' a7'. apply evt_done. left. exists t1'', t2'', t3'', a4', a5', a7'. split; [reflexivity| auto].
    - intros C1 C2 t1'' t2'' t3'' a2' a4' a5' a7'. apply evt_done. right. left. exists t1'', t2'', t3'', a2', a4', a5', a7'. split; [reflexivity| auto].
    - intros C1 C2 t2'' t3'' a5'. apply evt_done. right. right. exists t2'', t3'', a5'. split; [reflexivity| auto]. }
  cbv beta. intros ms2 [QI|[QM|QB]].
  - (* [comment removed for export] *)
    (nelim QI 10%nat; intros t1'' t2'' t3'' a4' a5' a7' -> C1 C2 C3).
    rewrite (cond1_true n (STR - 4 - (A - P0)) n MMAP_THRESHOLD sc (size_to_class n + 1)) by (first [exact C2 | exact C3 | subst E; clear - C1; lia]).
    apply implM_ret.
    assert (SC48 : sc < 48).
    { pose proof (F_malloc_entry.size_to_class_props n ltac:(clear - N C2; unfold MMAP_THRESHOLD in *; lia)) as (SCR & _). clear - SCR C3 GSC. subst sc. lia. }
    eapply evt_mono.
    { eapply (rr_ss1_walk sp' gp tp s0 (wz G) (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 lo)
        with (P := A) (n := n) (k := i + 32 * Z.min (E - A - k) 5); rewrite ?SP'.
      - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
      - rewrite A1. apply unsigned_lit. clear - N; lia.
      - clear - N; lia.
      - clear - C1; subst E; lia.
      - specialize (S20 SC48). clear - S20 SIL SI0 Hk EA Ho N; subst E. lia.
      - clear - Hi LI Hfit Hk EA; subst E. lia.
      - clear - ABND R0; lia.
      - clear - ABND; subst E; lia.
      - exact MI1.
      - apply XP1; [exact B3|]. cbn [length]. change (Z.of_nat 1) with 1. clear - ABND LO'; lia.
      - eapply wr_at_transport; [| exact WM1]. eapply wr_at_sub; [exact HWr| clear - ABND; lia| clear - ABND; subst E; lia].
      - exact FR1.
      - exact ST1.
      - clear - ABND LO'; subst E; lia.
      - clear - SLO' LO'; lia. }
    cbv beta. intros ms' RET.
    eapply (rr_inplace_final ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
              PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP N m1 ms' errv MU1 WM1); [| | exact ERR1| exact RET].
    + clear - C1; subst E. exact C1.
    + specialize (S20 SC48). clear - S20 SIL SI0 Hk EA Ho N C1; subst E. unfold RF_realloc_G1.XE, RF_realloc_G1.XP0, RF_realloc_G1.Xstride, IB. fold STR P0. lia.
  - (* [comment removed for export] *)
    (nelim QM 10%nat; intros t1'' t2'' t3'' a2' a4' a5' a7' -> C1 C2).
    rewrite (cond1_false n (STR - 4 - (A - P0)) n MMAP_THRESHOLD sc (size_to_class n + 1)) by (intros X; apply C1; subst E; clear - X; lia).
    rewrite (cond2_false 48 sc MMAP_THRESHOLD n C2).
    replace (Z_to_bv 64 (E - (E - A - k))) with (Z_to_bv 64 (A + k)) by (f_equal; clear; lia).
    apply (rr_fallback_thm ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0
             PERM Hst MRP BLK AR Hin BA LEN AV HB LO SLO TP A0 A1 N m1 errv); [| exact WM1| exact MI1| exact ST1| exact FR1| exact ERR1].
    eapply munch_weaken; [| exact MU1]. intros x [X _]. cbn. split; [clear - X; lia| exact I].
  - (* [comment removed for export] *)
    (nelim QB 6%nat; intros t2'' t3'' a5' -> C1 C2).
    rewrite (cond1_false n (STR - 4 - (A - P0)) n MMAP_THRESHOLD sc (size_to_class n + 1)) by (clear - C1; unfold MMAP_THRESHOLD in *; lia).
    rewrite (cond2_true 48 sc MMAP_THRESHOLD n) by (clear - C1 C2; lia).
    rewrite C2. cbn [Z.eqb negb Pos.eqb].
    (* [comment removed for export] *)
    assert (L0 : m_last_idx (MR st g) = 0) by (clear -GSC C2; subst sc; lia).
    assert (MLP : 0 < m_maplen (MR st g)) by (clear -GSC C2; subst sc; lia).
    destruct (TOP ltac:(clear - MLP; lia)) as [Hb0 EON].
    assert (I0 : i = 0) by (clear -Hi L0; lia).
    set (on := m_maplen (MR st g) * 4096) in *.
    assert (ESTR63 : STR = on - 16).
    { subst STR on. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (MR st g)) 0); [exfalso; clear - MLP e; lia|]. cbn. unfold UNIT. clear; lia. }
    assert (HPB : P0 = B + 16) by (rewrite HP0, HBr, Hb0, I0; clear; lia).
    replace (A - P0) with (16 * off) by (clear - EA; lia).
    set (nn := rr_needed n (16 * off)) in *.
    pose proof (rr_needed_facts n (16 * off) (proj1 N) ltac:(clear - Ho; lia)) as NN. fold nn in NN. unfold UNIT, IB in NN.
    assert (EBASE : A - (B + STR * i + 16) = 16 * off) by (clear - I0 HPB EA; lia).
    assert (MWR : 0 <= meta_word (MR st g) < 2^64) by (unfold meta_word; clear - LI FB GSC ML; lia).
    set (QB2 := fun ms => (on = nn /\ exists a3' a5'',
            ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + STR * i + 16)) t2'' (Z_to_bv 64 nn) (wz G) a0 a1 (wz B) a3' (Z_to_bv 64 on) a5''
                        (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (E - (E - A - k))) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6)
                    F (Z_to_bv 64 0x16e80) fc None m1 rom)
        \/ (on <> nn /\ exists a5'',
            ms = MS (mkR (Z_to_bv 64 0x16e74) sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + STR * i + 16)) t2'' (Z_to_bv 64 nn) (wz G) (wz B) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 on) a5''
                        (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (E - (E - A - k))) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 t3'' t4' t5 t6)
                    F (Z_to_bv 64 rmremap_entry) fc None m1 rom)).
    eapply implM_evt.
    { eapply (rr_big_walk ra sp' gp tp s0 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz G) t2'' t3'' a5' s3 s4 s5 s6 t4' F fc m1 A n B 63 (meta_word (MR st g)) (m_maplen (MR st g)) E (E - A - k) STR i QB2).
      - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
      - rewrite A1. apply unsigned_lit. clear - N; lia.
      - exact N.
      - clear - HBr R0 B0; lia.
      - clear - HPB EA Ho I0; lia.
      - exact SI0.
      - clear - ABND R0 Hk; lia.
      - exact MWR.
      - apply mword_page; clear - LI FB GSC ML; lia.
      - intros EQ a3' a5''. apply evt_done. left. rewrite EBASE in EQ |- *. split; [exact EQ|]. exists a3', a5''. reflexivity.
      - intros NEQ a5''. apply evt_done. right. rewrite EBASE in NEQ |- *. split; [exact NEQ|]. exists a5''. reflexivity. }
    cbv beta. intros ms3 [[EQ (a3' & a5'' & ->)]|[NEQ (a5'' & ->)]].
    + (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq on nn) EQ). apply implM_ret.
      (* [comment removed for export] *)
      (nelim MSL 6%nat; intros aa ar kk Haa Hkk Eg).
      (nelim (WA aa ar Haa) 7%nat; intros rga Hra A0a A4096 AMOD NKa LRa).
      assert (HG : G = r_base rga + snd aa + (24 + 40 * kk)).
      { subst G. rewrite Eg. rewrite (conc_region' st (aadd aa (AREA_HDR + META_SIZE * kk)) rga Hra). unfold aadd, AREA_HDR, META_SIZE. cbn [snd]. clear; lia. }
      unfold NSLOTS in Hkk.
      (nelim (WR _ _ Hra) 5%nat; intros Ra0 _ _ RaC RaF). unfold alloc_ceiling in RaC.
      assert (NEa : fst aa <> fst b) by (intros X; rewrite X, Hr in Hra; injection Hra as <-; exact (NKa Kr)).
      assert (GNB : G + 40 <= B \/ B + on <= G).
      { destruct (DJR _ _ _ _ Hra Hr NEa) as [GB|GB]; rewrite ?(lr_lo_group _ Kr) in GB; clear - GB HG LRa Hkk A4096 HBr EON Hb0; lia. }
      assert (GNI : G + 40 <= 0x10000 \/ 0x55000 <= G).
      { destruct (rreserved_disjoint1 _ _ RaF ltac:(clear - A0a A4096; lia)) as [X|X]; clear - X HG LRa Hkk A4096 A0a; lia. }
      assert (MM1 : rw_cells psegs m1 G [C8 (pw st (m_prev (MR st g))); C8 (pw st (m_next (MR st g))); C8 (wz B); C4 (wz (m_avail (MR st g))); C4 (wz (m_freed (MR st g))); C8 (wz (meta_word (MR st g)))]).
      { unfold meta_cells in MM. rewrite Hmem in MM. unfold pw at 3 in MM. cbn [oconc] in MM. fold B in MM.
        eapply rw_cells_transport; [exact MM| exact MU1| exact WM1|]. cbn. clear - G40 LO' SLO'. lia. }
      assert (BE1 : bytes_at psegs m1 E [b8 0]) by (apply XP1; [exact BE| cbn [length]; change (Z.of_nat 1) with 1; clear - ABND LO'; subst E; lia]).
      eapply evt_mono.
      { eapply (rr_fin2_walk sp' gp tp (Z_to_bv 64 (E - (E - A - k))) s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 lo)
          with (P := A) (n := n) (G := G) (k := i + 32 * Z.min (E - A - k) 5) (Bold := B) (mword := meta_word (MR st g))
               (avail := m_avail (MR st g)) (freed := m_freed (MR st g)) (prev := pw st (m_prev (MR st g))) (next := pw st (m_next (MR st g)));
          rewrite ?SP'; first [exact MM1| exact MI1| exact FR1| exact ST1| exact MWR| idtac].
        - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
        - rewrite A1. apply unsigned_lit. clear - N; lia.
        - unfold wz. apply unsigned_lit. clear - G0 G40; lia.
        - clear - HBr R0 Hb0; lia.
        - clear - EQ EON HBr Hb0 RC LO'; lia.
        - clear - EQ EON HBr Hb0 RC; lia.
        - clear - Ho; lia.
        - clear - N; lia.
        - clear - NN; lia.
        - clear - NN N; lia.
        - clear - NN; lia.
        - clear - Hi LI ABND; subst E; lia.
        - clear - G40 LO'; lia.
        - clear - GNB EA HPB Ho EQ; lia.
        - replace (B + 16 * off + 16 - 3) with (A - 3) by (clear - EA HPB; lia). apply XP1; [exact B3|]. cbn [length]. change (Z.of_nat 1) with 1. clear - ABND LO'; lia.
        - eapply wr_at_transport; [| exact WM1]. eapply wr_at_sub; [exact HWr| clear - ABND HBr Hb0 EA HPB; lia| clear - EQ EON HBr Hb0 ABND EA HPB; lia].
        - clear - SLO' LO'; lia. }
      cbv beta. intros ms' nelH_; (nelim nelH_ 7%nat; intros mF RET MUF WMF MIF CH BEF).
      replace (B + 16 * off + 16) with A in RET by (clear - EA HPB; lia).
      replace (B + nn - 4) with E in RET, BEF by (clear - EQ ESTR63 HPB; subst E; lia).
      rewrite <- EQ in CH. cbv delta [on] in CH. rewrite mword_same in CH by (clear - LI FB GSC ML; lia).
      assert (EMF : mF = m1).
      { apply mem_ext. intros x. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR.
        destruct (Z_lt_dec (bv_unsigned x) G) as [L1|L1]; [| destruct (Z_lt_dec (bv_unsigned x) (G + 40)) as [L2|L2]].
        2:{ eapply (bytes_at_same_byte m1 mF G); [apply rw_cells_bytes_at; exact MM1| apply rw_cells_bytes_at; exact CH| cbn; exact GNI| cbn; clear - L1 L2; lia]. }
        all: destruct (Z.eq_dec (bv_unsigned x) E) as [L3|L3];
          [eapply (bytes_at_same_byte m1 mF E [b8 0]); [exact BE1| exact BEF| cbn [length]; change (Z.of_nat 1) with 1; clear - RI ABND; subst E; lia| cbn [length]; change (Z.of_nat 1) with 1; clear - L3; lia]|].
        all: apply MUF; cbn; refine (conj _ (conj _ (conj _ I))); (first [clear - L1 L2 L3 XR EQ ESTR63 HPB | clear - L1 L3 XR EQ ESTR63 HPB]; subst E; lia). }
      rewrite EMF in RET.
      eapply (rr_inplace_final ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
                PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP N m1 ms' errv MU1 WM1); [| | exact ERR1| exact RET].
      * unfold RF_realloc_G1.XE, RF_realloc_G1.XP0, RF_realloc_G1.Xstride, IB. fold STR P0. clear - NN EQ ESTR63 HPB EA; lia.
      * unfold RF_realloc_G1.XE, RF_realloc_G1.XP0, RF_realloc_G1.Xstride, IB. fold STR P0. clear - NN N EQ ESTR63 HPB EA; lia.
    + (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq on nn) NEQ).
      (nelimp GL 5%nat; intros _ _ _ GOT GRD).
      assert (GOT1 : rw_cells psegs m1 RGOT_SSP [C8 (wz RSSP_GUARD)]).
      { eapply rw_cells_transport; [exact GOT| exact MU1| exact WM1|]. unfold RGOT_SSP. cbn. clear - SPR SLO' LO'; lia. }
      assert (GRD1 : rw_cells psegs m1 RSSP_GUARD [C8 ssp_guard_val]).
      { eapply rw_cells_transport; [exact GRD| exact MU1| exact WM1|]. unfold RSSP_GUARD. cbn. clear - SPR SLO' LO'; lia. }
      assert (WR1 : wr_at psegs m1 B on). { rewrite HBr, Hb0, Z.add_0_r, EON. eapply wr_at_transport; [exact HWr| exact WM1]. }
      assert (BON : 0 < B /\ B mod 4096 = 0 /\ B + on <= alloc_ceiling /\ ranges_free ref_reserved B on = true /\ 4096 <= on /\ on mod 4096 = 0).
      { rewrite HBr, Hb0, Z.add_0_r, EON. split; [exact R0|]. split; [exact RAL|]. split; [exact RC|]. split; [exact RFr|].
        rewrite <- EON. subst on. split; [clear - MLP; lia| apply Z_mod_mult]. }
      (nelim BON 6%nat; intros BO0 BOA BOC BOF ON4 ONA).
      pose proof (rreserved_disjoint1 _ _ BOF ltac:(clear - ON4; lia)) as BNI.
      (nelim IV 9%nat; intros L LS BL INV LIVE RESV SEC CORR HkBL).
      eapply implM_bind.
      { apply implM_msys_of_impl.
        eapply rmremap_spec with (old := B) (on := on) (nn := nn) (errv := errv) (canary := ssp_guard_val) (lo := lo); rewrite ?SP';
          first [exact ERR1| exact GOT1| exact GRD1| exact MI1| exact WR1| exact TP| exact BO0| exact BOA| exact BOF| exact ONA| reflexivity| idtac].
        - exact ST1.
        - clear - ON4; lia.
        - clear - NN N Ho; lia.
        - clear - NN; lia.
        - exact BOC.
        - clear - SLO' LO'; lia.
        - exact LO. }
      cbv beta. intros a s' ms3 [-> HP]. destruct a as [e| |d].
      * (* [comment removed for export] *)
        (nelim HP 22%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m' -> MUE WME MIE STE ERRE HE).
        eapply (implM_evt psegs _ _ _ (fun ms => ms = MS (mkR (Z_to_bv 64 0x16e74) sp' gp tp u0 u1 u2 (Z_to_bv 64 nn) (wz G) a0 a1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) v4 v5 v6 v7
                     (Z_to_bv 64 (E - (E - A - k))) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 RR_MALLOC) fc None m' rom)).
        { rewrite ret_pc_even by (clear; first [lia| reflexivity]). subst rom.
          step. step. step. step. step. if_cases K1; zify_cond K1.
          - apply evt_done. reflexivity.
          - exfalso. clear - K1. exact (K1 eq_refl). }
        cbv beta. intros ms4 ->.
        replace (Z_to_bv 64 (E - (E - A - k))) with (Z_to_bv 64 (A + k)) by (f_equal; clear; lia).
        rewrite SP' in STE.
        apply (rr_fallback_thm ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0
                 PERM Hst MRP BLK AR Hin BA LEN AV HB LO SLO TP A0 A1 N m' (Z_to_bv 64 e)); [| | exact MIE| exact STE| | exact ERRE].
        -- eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MUE]].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
           ++ intros x [X [Y _]]. rewrite SP'. cbn. split; [clear - X; lia|]. split; [exact Y| exact I].
        -- eapply wmono_trans; [exact WM1| exact WME].
        -- eapply rw_cells_transport; [exact FR1| exact MUE| exact WME|]. rewrite SP'. rewrite TP. unfold RATP. rewrite unsigned_lit by (clear; lia). cbn. clear - SPR SLO' LO'; lia.
      * (* [comment removed for export] *)
        destruct (remap_grow_ok (ps_m s) B on nn) eqn:GROW; [| apply implM_unr].
        assert (GF : nn <= on \/ (B + nn <= alloc_ceiling /\ ranges_free (live_ranges st) (B + on) (nn - on) = true)).
        { unfold remap_grow_ok in GROW. apply Bool.orb_true_iff in GROW. destruct GROW as [X|X].
          - left. apply Z.leb_le. exact X.
          - right. apply Bool.andb_true_iff in X. destruct X as [X Y]. apply Z.leb_le in X. rewrite <- Hst, live_ranges_strip in Y. unfold alloc_ceiling in X. auto. }
        assert (GF2 : on < nn -> forall q rq, s_regions st !! q = Some rq -> B + nn <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= B + on).
        { intros LT q rq Hq. destruct GF as [X|[_ Y]]; [exfalso; clear - X LT; lia|].
          pose proof (ranges_free_regions st _ _ q rq Y Hq) as Z1. pose proof (live_range_pos _ _ _ _ _ q rq INV Hq) as Z2.
          unfold region_live_range, lr_lo in *. destruct (r_kind rq); cbn [fst snd] in Z1, Z2; unfold PGSZ in *; clear - Z1 Z2 LT; lia. }
        assert (LRP : forall q rq, s_regions st !! q = Some rq -> lr_lo rq < r_base rq + round_up_pg (r_len rq)).
        { intros q rq Hq. pose proof (live_range_pos _ _ _ _ _ q rq INV Hq) as Z2.
          unfold region_live_range, lr_lo in *. destruct (r_kind rq); cbn [fst snd] in Z2; unfold PGSZ in *; clear - Z2; lia. }
        assert (GF3 : on < nn -> B + nn <= alloc_ceiling /\ ranges_free ref_reserved (B + on) (nn - on) = true).
        { intros LT. destruct GF as [X|[X Y]]; [exfalso; clear - X LT; lia|]. split; [exact X|].
          apply ranges_free_intro. intros b0 k0 Hin0'. apply (ranges_free_In _ _ _ _ _ Y). unfold live_ranges. apply in_or_app. left. rewrite Hres. exact Hin0'. }
        assert (GFB : nn <= on \/ B + nn <= alloc_ceiling) by (destruct GF as [X|[X _]]; [left| right]; exact X).
        assert (DNI2 : B + nn <= 0x10000 \/ 0x55000 <= B).
        { pose proof (rreserved_disjoint1 _ _ BOF ltac:(clear - ON4; lia)) as X.
          destruct (Z_lt_dec on nn) as [LT|GE]; [| clear - X GE; lia].
          destruct (GF3 LT) as [_ Y]. pose proof (rreserved_disjoint1 _ _ Y ltac:(clear - LT; lia)) as X2. clear - X X2 LT ON4; lia. }
        assert (SANE : mrm_sane_inplace B on nn).
        { intros LT. destruct (GF3 LT) as [X Y]. split; [exact X| exact Y]. }
        (nelim (HP SANE) 21%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 ST2 ERR2). clear HP.
        rewrite SP' in MU2, ST2.
        eapply (implM_bind psegs _ _ _ (fun _ sx msx => sx = set_m (cs_remap (ps_m s) (fst b) g B nn) s /\ msx = _)).
        { apply implM_upd. apply evt_done. split; reflexivity. }
        cbv beta. intros [] sx ms4 [-> ->]. apply implM_ret.
        rewrite ret_pc_even by (clear; first [lia| reflexivity]). subst rom.
        step. step. step.
        assert (WR2 : wr_at psegs m2 B on) by (eapply wr_at_transport; [exact WR1| exact WM2]).
        eapply (rr_remap_final ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
                  PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP A0 A1 N B m2 (mrm_inplace B on nn m2) errv C1).
        -- subst sc. exact C2.
        -- exact BO0.
        -- exact BOA.
        -- unfold RF_realloc_G2.Xnn, UNIT. fold nn. destruct (Z_lt_dec on nn) as [LT|GE]; [exact (proj1 (GF3 LT))| clear - GE BOC; unfold alloc_ceiling; lia].
        -- unfold RF_realloc_G2.Xnn, UNIT. fold nn. apply rreserved_free_intro; [clear - NN; lia| exact DNI2].
        -- unfold RF_realloc_G2.Xnn, UNIT. fold nn. intros q rq Hq NE.
           destruct (DJR _ _ _ _ Hq Hr NE) as [D1|D1]; rewrite ?(lr_lo_group _ Kr), <- ?HBr in D1.
           ++ left. clear - D1 HBr Hb0. lia.
           ++ destruct (Z_lt_dec on nn) as [LT|GE].
              ** destruct (GF2 LT q rq Hq) as [D2|D2]; [right; exact D2|]. pose proof (LRP q rq Hq) as L3. exfalso. clear - D1 D2 L3 HBr Hb0 EON LT. lia.
              ** right. clear - D1 GE HBr Hb0 EON. lia.
        -- left. reflexivity.
        -- eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
        -- eapply wmono_trans; [exact WM1| exact WM2].
        -- exact ERR2.
        -- eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. clear - SPR SLO' LO'; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros a' Ha N1 N2.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC].
           ++ apply unmaps_outside; rewrite ?wa_unsigned by (clear - Ha; lia); clear - Ha N1 N2 HC BO0 BOC ON4 NN; lia.
           ++ apply zeros_outside; rewrite ?wa_unsigned by (clear - Ha; lia); clear - Ha N1 N2 HC BO0 BOC ON4 NEQ GFB NN; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC].
           ++ apply unmaps_outside; rewrite ?wa_unsigned by (clear - Hj BO0 BOC ON4 NN HC; lia); clear - Hj HC BO0 BOC ON4 NN; lia.
           ++ apply zeros_outside; rewrite ?wa_unsigned by (clear - Hj BO0 BOC ON4 NEQ GFB HC NN; lia); clear - Hj HC BO0 BOC ON4 NEQ GFB NN; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC]; [exfalso; clear - Hj HC; lia|].
           apply zeros_inside; rewrite ?wa_unsigned by (clear - Hj BO0 BOC ON4 NEQ GFB HC NN; lia); clear - Hj HC BO0 BOC ON4 NEQ GFB NN; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold nn B.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC].
           ++ apply wr_at_unmaps_other; [clear - BO0 BOC ON4 NN HC; lia| clear - BO0 BOC ON4 NN HC; lia| clear - BO0 BOC ON4 NN HC; lia| | clear; lia].
              eapply wr_at_sub; [exact WR2| clear; lia| clear - HC; lia].
           ++ replace nn with (on + (nn - on)) at 2 by (clear; lia). apply wr_at_join; [| | clear - ON4; lia| clear - HC; lia].
              ** apply wr_at_zeros; [clear - BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia| exact WR2].
              ** apply wr_at_zeros_new; [clear - BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia].
        -- exact MI2.
        -- exact ST2.
      * (* [comment removed for export] *)
        destruct (remap_move_ok (ps_m s) nn d) eqn:MOVE; [| apply implM_unr].
        unfold remap_move_ok in MOVE. rewrite !Bool.andb_true_iff in MOVE. destruct MOVE as [[[MD0 MDA] MDC] MRF].
        apply Z.ltb_lt in MD0. apply Z.eqb_eq in MDA. apply Z.leb_le in MDC. rewrite <- Hst, live_ranges_strip in MRF. unfold alloc_ceiling in MDC.
        assert (MRR : ranges_free ref_reserved d nn = true).
        { apply ranges_free_intro. intros b0 k0 Hin0'. apply (ranges_free_In _ _ _ _ _ MRF). unfold live_ranges. apply in_or_app. left. rewrite Hres. exact Hin0'. }
        assert (MDJ : forall q rq, s_regions st !! q = Some rq -> r_base rq + round_up_pg (r_len rq) <= d \/ d + nn <= lr_lo rq).
        { intros q rq Hq. pose proof (ranges_free_regions st _ _ q rq MRF Hq) as Z1.
          unfold region_live_range, lr_lo in *. destruct (r_kind rq); cbn [fst snd] in Z1; unfold PGSZ in *; clear - Z1; lia. }
        assert (SANE : mrm_sane_moved B on nn d).
        { split; [exact MRR|]. destruct (MDJ _ _ Hr) as [X|X]; rewrite ?(lr_lo_group _ Kr) in X; clear - X HBr Hb0 EON; lia. }
        (nelim (HP SANE) 26%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 ST2 ERR2 ONN DNE D0' DA' DCE'). clear HP.
        rewrite SP' in MU2, ST2. unfold alloc_ceiling in DCE'.
        pose proof SANE as [_ DSEP].
        eapply (implM_bind psegs _ _ _ (fun _ sx msx => sx = set_m (cs_remap (ps_m s) (fst b) g d nn) s /\ msx = _)).
        { apply implM_upd. apply evt_done. split; reflexivity. }
        cbv beta. intros [] sx ms4 [-> ->]. apply implM_ret.
        rewrite ret_pc_even by (clear; first [lia| reflexivity]). subst rom.
        step. step. step.
        assert (WR2 : wr_at psegs m2 B on) by (eapply wr_at_transport; [exact WR1| exact WM2]).
        assert (HSRC : forall j, 0 <= j < on -> m2 (wa (B + j)) <> None).
        { intros j Hj. (nelim WR2 3%nat; intros _ _ W). specialize (W j Hj). rewrite ref_wview_overlay in W by (rewrite wa_unsigned by (clear - Hj BO0 BOC; lia); clear - Hj BNI; lia). exact W. }
        eapply (rr_remap_final ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
                  PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP A0 A1 N d m2 (move_mem m2 B d on nn) errv C1).
        -- subst sc. exact C2.
        -- exact D0'.
        -- exact DA'.
        -- exact DCE'.
        -- exact MRR.
        -- intros q rq Hq NE. exact (MDJ q rq Hq).
        -- right. exact DSEP.
        -- eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
        -- eapply wmono_trans; [exact WM1| exact WM2].
        -- exact ERR2.
        -- eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. clear - SPR SLO' LO'; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros a' Ha N1 N2.
           apply (move_mem_outside m2 B d on nn); rewrite ?wa_unsigned by (clear - Ha; lia);
             clear - Ha N1 N2 BO0 BOC ON4 NN D0' DCE' ONN DSEP; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           apply (move_mem_inside m2 B d on nn); clear - Hj BO0 BOC ON4 NN D0' DCE' ONN DSEP; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           apply (move_mem_tail m2 B d on nn); clear - Hj BO0 BOC ON4 NN D0' DCE' ONN DSEP; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xnn, UNIT. fold nn.
           apply (wr_at_mremap_move psegs m2 B d on nn); [clear - BO0 BOC ON4; lia| clear - NN D0' DCE'; lia| clear - ON4; lia| exact ONN| exact DSEP| exact HSRC].
        -- exact MI2.
        -- exact ST2.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; lia.
Notation RAREACH := (AREACH_from ref_reserved).
End RF_realloc_spec.

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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_A Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog KInv MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv2 KRaw Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.KRawR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_ReallocR.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_heap_inst0.
Import CJ_heap_inst.
Import RF_realloc_null.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RF_realloc_F.
Import RF_realloc_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
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
Lemma RHEAP_addr_in_slot : forall s LBi m p A k,
  RHEAP s LBi m -> In (p, A, k) LBi -> addr_in_slot (ps_m s) (fst p) A.
Proof.
  intros s LBi m p A k (st & LB0 & HP & Hst & MRP & [_ AR]) Hin.
  assert (Hin0 : In (p, A, k) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hin]).
  destruct (rrF_intro st m LB0 p A k AR MRP Hin0) as (g & b & r & i & off & RF).
  pose proof (rf_slot _ _ _ _ _ _ _ _ _ _ _ RF) as Hs.
  pose proof (rf_A _ _ _ _ _ _ _ _ _ _ _ RF) as HA.
  pose proof (rf_off _ _ _ _ _ _ _ _ _ _ _ RF) as Ho.
  pose proof (rf_k _ _ _ _ _ _ _ _ _ _ _ RF) as Hk.
  pose proof (rf_fit _ _ _ _ _ _ _ _ _ _ _ RF) as Hfit.
  rewrite <- Hst. intros g' idx Hs'.
  rewrite s_slots_strip in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-.
  rewrite conc_strip, get_meta_rec_strip. fold (MR st g). unfold UNIT, IB in *. lia.
Qed.

Theorem lhd_realloc : realloc_scps_stmt LHEAPd.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB A k n lo old errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) Hin BY LEN HSP ST Hlo Hlo2 ER MI Htp Ha0 Ha1 Hn.
  (* [comment removed for export] *)
  destruct (in_bview _ _ _ Hin) as ([[p A'] k'] & Hb & E1 & E2). cbn [blk_addr blk_size fst snd] in E1, E2. subst A' k'.
  pose proof (rrealloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi p A k n lo B old errv
                HR Hb BY LEN HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Ha1 Hn) as Himpl.
  assert (Hinp : In (fst p) (map blk_slot LBi)). { apply in_map_iff. exists (p, A, k). auto. }
  pose proof (raw_realloc_etwf_closed (map blk_slot LBi) s mo p A n HO Hinp Hn (RHEAP_addr_in_slot s LBi m p A k HR Hb)) as Hwf.
  destruct (lb_remove_views LBi p A k (RHEAP_slot_nodup _ _ _ HR) (RHEAP_addr_nodup _ _ _ HR) Hb) as (V1 & V2 & V3).
  eapply scps_mono; [apply (implM_scps psegs (raw_realloc p A n) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ER' & HA' & _ & _ & Hr).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  destruct r as [q|].
  - destruct Hr as (A' & junk & -> & HRng & HR' & HP & RW & HA'A). destruct HRr as [HO' Hni].
    right. exists A', junk. split; [reflexivity|]. split; [exact HRng|]. split.
    + destruct HA'A as [E|NE]; [left; exact E| right]. rewrite map_fst_bview. intros HinA.
      apply in_map_iff in HinA as (b' & E & Hb'). exact (NE b' Hb' (eq_sym E)).
    + split; [| split; [rewrite <- V2; apply cj_pres_of_rheap_pres; exact HP| exact RW]].
      exists s', ((q, A', n) :: lb_remove p LBi), B. splits; auto.
      * cbn [map]. rewrite V2. reflexivity.
      * cbn [map]. rewrite V1. exact HO'.
  - destruct Hr as (-> & HR' & HP). left. split; [reflexivity|]. split; [| apply cj_pres_of_rheap_pres; exact HP].
    exists s', LBi, B. splits; auto.
Qed.

(* [comment removed for export] *)
Definition PHI0 : cj_heap_iface := PHI lhd_realloc rrealloc_null_spec.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
