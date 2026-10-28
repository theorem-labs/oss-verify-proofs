(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX SecLazy
     AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AG_MallocModel AG_Malloc2 AG_LargeModel AG_MallocLarge3
     AG_Frame AG_MallocCold AG_MallocTop AG_MallocLarge AG_WriteSet.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition mneeded (size : Z) : Z := round_up (Z.max size 8) 8 + rz_size size.
Definition mprimary (size : Z) : bool := mneeded size <=? kMaxSize.
Definition msz_of (size : Z) : Z := round_up (rq_needed (compute_req size)) kPageSize + kPageSize.
(* [comment removed for export] *)
Definition malloc_cost (size : Z) : Z := if mprimary size then 0 else lg_cost (msz_of size).

Lemma mprimary_iff : forall size, 1 <= size -> mprimary size = true <-> size <= 64512.
Proof.
  intros size Hs. unfold mprimary, mneeded, kMaxSize, rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog, round_up. rewrite Z.leb_le.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end.
  all: match goal with |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v end.
  all: Z.div_mod_to_equations; lia.
Qed.

Section MallocAllGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  Let st := a_st s.
  Let c := class_id (mneeded size).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf41c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2992 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.
  (* [comment removed for export] *)
  Hypothesis ALLOW : malloc_cost size <= a_AL s.
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.
  Hypothesis XTRA : if mprimary size then rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset
                    else AGAP (msz_of size) mo /\ zlen (as_sec st) + 1 <= kChunksBlockCount.   (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf354) fc None m (seg_rom asegs).

  Definition malloc_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (U : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ a_AL s - malloc_cost size <= a_AL s'
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz U) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP s' ((U, size) :: LB) m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo' /\ nonvm_same mo mo'   (* [comment removed for export] *)
    /\ DEPOT asegs d' m' /\ depot_placed s' d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ amframe s LB (bv_unsigned sp) m m' /\ wmono asegs m m'
    /\ acompl s s' d lo (bv_unsigned sp) m m' /\ avmx s s' mo mo'                      (* [comment removed for export] *)
    /\ (exists junk, rw_cells asegs m' U [CB (Z.to_nat size) junk]) /\ addressable m' U size
    /\ (exists kaddr st'' ev, am_malloc_k st size kaddr = Some (U, st'', ev) /\ same_but_shadow st'' (a_st s')).

  Theorem malloc_arep :
    (forall msF' mo', malloc_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. unfold malloc_cost in ALLOW.
    destruct (mprimary size) eqn:PR.
    - (* [comment removed for export] *)
      assert (SZ' : 1 <= size /\ round_up (Z.max size 8) 8 + rz_size size <= kMaxSize).
      { split; [clear - SZ; try acb; lia|]. unfold mprimary, mneeded in PR. apply Z.leb_le in PR. exact PR. }
      eapply (malloc_arep_prim ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH
                HR AX AMX DEP DPL DFS DCOV MI ST LO HI SPA SPT SZ' TP DCAP FCH Ha0 PROOM XTRA OK VISE).
      intros msF' mo' PO.
      destruct PO as (s' & U & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & AL
                      & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & FR' & WM' & CP' & AVX' & BLK & ADDR & MODEL).
      apply K. exists s', U, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. unfold malloc_cost. rewrite PR.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      { clear - AL. lia. }
      destruct (MODEL 0) as (st'' & ev & M1 & M2). exists 0, st'', ev. split; assumption.
    - (* [comment removed for export] *)
      assert (SZ' : 64512 < size < 2^32).
      { split; [| clear - SZ; try acb; lia]. destruct (Z.le_gt_cases size 64512) as [LE|GT]; [| exact GT].
        exfalso. apply (proj2 (mprimary_iff size ltac:(hci; clear - SZ; try acb; lia))) in LE. rewrite LE in PR. discriminate PR. }
      destruct XTRA as (AGP & NSEC).
      eapply (malloc_arep_large ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH
                HR AX AMX DEP DPL DCOV MI ST LO ltac:(hci; clear - HI; try acb; lia) SPA SPT SZ' TP DCAP FCH Ha0 ALLOW ltac:(hci; pose proof PROOM as PR'; unfold COLD_COST in PR'; change st with (a_st s) in PR'; clear - PR'; lia) AGP NSEC DFS OK VISE).
      intros msF' mo' PO.
      destruct PO as (a & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & A1 & A2 & A3
                      & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & MU' & WM' & FR' & CP' & AVX' & BLK & ADDR & MODEL).
      apply K. exists (mkAst (large_state st a size) (a_thr s) (a_ctx s) (a_fsb s) (lg_L (a_L s) (a_pa s) (as_n_reserved st) (zlen (as_sec st)))
                             ((wz (sh a), wz (msz_of size / 8)) :: a_S s) (a_Zr s) (a_AL s - lg_cost (msz_of size)) (a_top s) (a_bot s)),
                      (a + kPageSize + 2048), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [a_AL]; unfold malloc_cost; rewrite PR; clear; lia|].
      repeat match goal with |- _ /\ _ => split end; try assumption.
      destruct MODEL as (st'' & ev & M1 & M2). exists a, st'', ev. split; assumption.
  Qed.
End MallocAllGlue.

End HCW.

