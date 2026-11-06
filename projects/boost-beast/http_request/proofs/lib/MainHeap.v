(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec StoreOk ShapeAlg SReach RegsEquivM MainEqv MainDefs HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame MState SysStep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section Heap.
  Context {HCEIL : HeapCeil}.
  Variable HS : hsr.
  Hypothesis HH : heap_sr_hyps HS.
  Hypothesis HX : heap_extra HS.

  Let MALLOC : malloc_sr_stmt HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M & _). exact M. Qed.
  Let FREE : free_sr_stmt HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _). exact F. Qed.
  Let KREL_h : forall s mo, hs_KREL HS s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. destruct HH as (_ & K & _). exact K. Qed.

  (* [comment removed for export] *)
  Definition heap_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  (* [comment removed for export] *)
  Lemma malloc_call : forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
      (s : PState) (LB : list block) (n lo B : Z) (errv : word) (ra : Z) (K : TSet),
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 RATP ->
    getr regs 10 = Z_to_bv 64 n -> 1 <= n < 2 ^ 32 ->
    hs_RHEAP HS s LB mem -> hs_KREL HS s model -> hs_alloc_ok HS s LB n ->
    hs_rauxv_ok HS mem B -> bv_unsigned (getr regs 2) <= B ->
    stk rsegs mem lo (bv_unsigned (getr regs 2)) -> hceil <= lo -> lo <= bv_unsigned (getr regs 2) - RMALLOC_STACK ->
    rw_cells rsegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv rsegs mem ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) (A : Z) (p : bptr) (s' : PState)
            (errv' : word) (junk : list byte),
        (forall r, In r heap_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 A ->
        hs_KREL HS s' model' -> hs_MPRES HS model model' ->
        mem_inv rsegs mem' -> stk rsegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells rsegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> hs_rauxv_ok HS mem' B ->
        rheap_pres LB (bv_unsigned (getr regs 2)) mem mem' ->
        rblock_range A n -> hs_RHEAP HS s' ((p, A, n) :: LB) mem' ->
        rw_cells rsegs mem' A [CB (Z.to_nat n) junk] ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 RMALLOC_SYM) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s LB n lo B errv ra K Hra Hra64 Hra2 Htp Ha0 Hn HRH HKR HAL HAU HB HSTK HLO HLO2 HERR HINV HK.
    (* [comment removed for export] *)
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Htp, Ha0.
    eapply sreach_realizes.
    { apply (hx_sr HS HX).
      apply (MALLOC (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 RATP) (getr regs 5) (getr regs 6) (getr regs 7)
                    (getr regs 8) (getr regs 9) (Z_to_bv 64 n) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                    (getr regs 29) (getr regs 30) (getr regs 31)
                    bvmap_empty (Z_to_bv 32 0) mem s LB n lo B errv model);
        try assumption; try reflexivity.
      rewrite <- Htp. exact HERR. }
    intros c' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A & junk & p & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HBR & HRH' & HBLK).
    destruct c' as [ms' mo']. cbn [cfg_ms cfg_model] in *. subst ms'.
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m' mo' A p s' errv' junk); try exact HKR'; try exact HMP; try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HBR; try exact HRH'; try exact HBLK.
    - intros r Hr. unfold heap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.

  (* [comment removed for export] *)
  Lemma free_call : forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
      (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (ra : Z) (K : TSet),
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 RATP ->
    getr regs 10 = Z_to_bv 64 A ->
    hs_RHEAP HS s LB mem -> hs_KREL HS s model -> In (p, A, n) LB ->
    hs_rauxv_ok HS mem B -> bv_unsigned (getr regs 2) <= B ->
    stk rsegs mem lo (bv_unsigned (getr regs 2)) -> hceil <= lo -> lo <= bv_unsigned (getr regs 2) - RFREE_STACK ->
    rw_cells rsegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv rsegs mem ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) (s' : PState),
        (forall r, In r heap_kept -> getr regs' r = getr regs r) ->
        hs_KREL HS s' model' -> hs_MPRES HS model model' ->
        mem_inv rsegs mem' -> stk rsegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells rsegs mem' (errno_addr (getr regs 4)) [C4 errv] -> hs_rauxv_ok HS mem' B ->
        rheap_pres (hs_lb_remove HS p LB) (bv_unsigned (getr regs 2)) mem mem' ->
        hs_RHEAP HS s' (hs_lb_remove HS p LB) mem' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 RFREE_SYM) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s LB p A n lo B errv ra K Hra Hra64 Hra2 Htp Ha0 HRH HKR HIN HAU HB HSTK HLO HLO2 HERR HINV HK.
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) bvmap_empty (Z_to_bv 64 RFREE_SYM) (Z_to_bv 32 0) None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Htp, Ha0.
    eapply sreach_realizes.
    { apply (hx_sr HS HX).
      apply (FREE (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 RATP) (getr regs 5) (getr regs 6) (getr regs 7)
                  (getr regs 8) (getr regs 9) (Z_to_bv 64 A) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                  (getr regs 29) (getr regs 30) (getr regs 31)
                  bvmap_empty (Z_to_bv 32 0) mem s LB p A n lo B errv model);
        try assumption; try reflexivity.
      rewrite <- Htp. exact HERR. }
    intros c' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HRH').
    destruct c' as [ms' mo']. cbn [cfg_ms cfg_model] in *. subst ms'.
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m' mo' s'); try exact HKR'; try exact HMP; try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HRH'.
    - intros r Hr. unfold heap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite Htp. exact HERR'.
  Qed.
End Heap.
