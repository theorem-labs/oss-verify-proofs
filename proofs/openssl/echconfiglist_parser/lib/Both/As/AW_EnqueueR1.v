(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_PutR1 AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition enq_regsR (sp gp tp s7 s8 s9 s10 s11 : word) (U size TH qcache : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
      (wz (TH + OT_TQ)) a1 a2 a3 a4 a5 a6 a7
      (wz size) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Definition enq_appendR_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size TH qcache : Z) (k hdq LA lsize lcount qbytes : Z) (lchunks : list Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH qcache t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b46c) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp + -2288); (TH + OT_TQ + 24, TH + OT_TQ + 32); (LA + 8, LA + 24); (LA + 24 + 8 * lcount, LA + 32 + 8 * lcount)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2288)
    /\ rw_cells asegs m' (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz (qbytes + size))]
    /\ rw_cells asegs m' LA [C8 (wz 0); C8 (wz (lsize + size)); C8 (wz (lcount + 1))]
    /\ u64arr asegs m' (LA + 24) (wlist (lchunks ++ [U + -16]))
    /\ stk asegs m' (LA + 32 + 8 * lcount) (LA + kBatchSize).
End HCW.

Section EnqAppend.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U size TH qcache : Z) (k hdq LA lsize lcount qbytes : Z) (lchunks : list Z).
  Let W : list ivl := [(lo, bv_unsigned sp + -2288); (TH + OT_TQ + 24, TH + OT_TQ + 32); (LA + 8, LA + 24); (LA + 24 + 8 * lcount, LA + 32 + 8 * lcount)].
  Let POST := enq_appendR_post sp gp tp s7 s8 s9 s10 s11 F fc m lo U size TH qcache k hdq LA lsize lcount qbytes lchunks.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2576 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis LAR : hidden (AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ LA mod 16 = 0 /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH)).
  Hypothesis KR : 1 <= k < 2^64. Hypothesis HDQ : 0 <= hdq < 2^64.
  Hypothesis LC : 1 <= lcount < kBatchCount /\ lcount = zlen lchunks. Hypothesis LSZ : 0 <= lsize /\ lsize + size < 2^64.
  Hypothesis QB : 0 <= qbytes /\ qbytes + size < 2^64. Hypothesis QCR : 0 <= qcache < 2^64.
  Hypothesis LCH : Forall (fun x => 0 <= x < 2^64) lchunks.

  Theorem enq_appendR :
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2288) ->
    rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)] ->
    rw_cells asegs m LA [C8 (wz 0); C8 (wz lsize); C8 (wz lcount)] ->
    u64arr asegs m (LA + 24) (wlist lchunks) ->
    stk asegs m (LA + 24 + 8 * lcount) (LA + kBatchSize) ->
    evt asegs POST
      (MS (mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
               (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (U + -16)) (wz size) a5 a6 a7
               (wz size) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b478) fc None m (seg_rom asegs)).
  Proof.
    intros MI ST TQ LB LCHK LJ.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold W in MU. unfold AINST, OI_Q, OT_TQ, OT_CACHE, kBatchSize, kBatchCount, wz in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ bv_unsigned sp + 16 <= 140737488355328
               /\ 12599312 <= U /\ U + 8 <= aceil /\ 140735193776128 <= aceil /\ 17594333495296 <= LA /\ LA + 8192 <= aceil)
      by (clear - LO THR SPT UR LAR; try acb; destruct THR as [THR']; destruct UR as [UR']; destruct LAR as [LAR']; destruct SPT as [SPT'];
          unfold AHI_LO in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; aunf; lia).   (* [comment removed for export] *)
    region_sides. name_bands.
    assert (PLh : hidden (TH + 4096 <= LA \/ LA + 8192 <= TH)) by (destruct LAR as [LAR']; constructor; clear - LAR'; try acb; lia).
    replace (TH + 80 + 24) with (TH + 104) in MU by lia. replace (TH + 80 + 32) with (TH + 112) in MU by lia.
    replace (6976152 + 728) with 6976880 by reflexivity.
    assert (LENC : Z.of_nat (length (wlist lchunks)) = lcount) by (unfold wlist; rewrite length_map; unfold zlen in LC; lia).
    (* [comment removed for export] *)
    step. carve_frame 64%nat ST. do 7 st1.
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (LA + 24 + 8 * lcount) (LA + 32 + 8 * lcount) (LA + 8192) LJ ltac:(hci; lia)) as [SL LJ']. clear LJ.
    destruct (stk_cells _ _ _ SL ltac:(hci; lia)) as [sj SJ]. clear SL.
    replace (LA + 32 + 8 * lcount - (LA + 24 + 8 * lcount)) with 8 in SJ by lia. change (Z.to_nat 8) with 8%nat in SJ.
    replace (LA + 24 + 8 * lcount) with (LA + 8 * lcount + 24) in SJ by lia.
    match goal with |- context [Z_to_bv 64 (LA + ?x)] => replace (LA + x) with (LA + 8 * lcount) by (rewrite (unsigned_lit lcount), Z.shiftl_mul_pow2 by lia; lia) end.
    step. step. step.
    (* [comment removed for export] *)
    step. step. step. step.
    do 9 step.
    release_frame FR ST (bv_unsigned sp + -2288).
    apply evt_done. unfold POST, enq_appendR_post, enq_regsR, wz, AINST, OI_Q, OT_TQ, OT_CACHE, kBatchSize.
    replace (6976152 + 728) with 6976880 by reflexivity.
    do 15 eexists. split; [reflexivity|].
    split. { replace (TH + 80 + 24) with (TH + 104) by lia. replace (TH + 80 + 32) with (TH + 112) by lia. exact MU. }
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact TQ|]. split; [exact LB|].
    split. { unfold wlist. rewrite map_app. cbn [map]. apply (proj2 (u64arr_snoc asegs _ _ _ _)). split; [exact LCHK|].
             rewrite length_map. unfold zlen in LC. replace (LA + 24 + 8 * Z.of_nat (length lchunks)) with (LA + 8 * lcount + 24) by lia. exact SJ. }
    exact LJ'.
  Qed.
End EnqAppend.

