(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocFArms.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

Lemma list_nil_or_snoc : forall {A} (l : list A), l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  intros A l. induction l as [|a l IH]; [left; reflexivity | right].
  destruct IH as [-> | (l' & x & ->)]; [exists [], a; reflexivity | exists (a :: l'), x; reflexivity].
Qed.

Section ARMS.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable HP : option Z -> ast -> Prop.            (* [comment removed for export] *)
  #[local] Notation FPOST := (free_post BSEGS FXOK both_addrs (AAINV_F bt HP)) (only parsing).
  #[local] Notation ENTRY fx R M mdl := (cfg BSEGS fx R (ia_free both_addrs) M mdl) (only parsing).

  (* [comment removed for export] *)
  Definition ARM (cond : ast -> Z -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K ret sp m : Z) (p : word) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HP h st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      Lc = L1 ++ (U p, m) :: L2 -> K + kcost_free <= KCAP -> a_ialloc st = true -> cond st m ->
      katD BSEGS (ENTRY fx R M mdl) (FPOST h MSTK_A R M mdl (L1 ++ L2) FF (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) (K + kcost_free) ret sp).

  (* [comment removed for export] *)
  Definition cond_big (st : ast) (m : Z) : Prop := 2 ^ 28 < m.




End ARMS.
End BoAllocFArms.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFHypD.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition free_cells_nb (bt : as_boot) : Prop := In (IB bt + 32, 8%nat, bt_spacebeg bt) (bt_consts bt).

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WFX (bt : as_boot) (st : ast) (Lc FF : list (Z * Z)) : Prop :=
  exists qt qg, WFq bt st Lc FF qt qg /\ AsKSys7b.qroom Lc qt qg /\ a_kact st <= KCAP.
Lemma WFX_intro : forall bt st Lc FF qt qg, WFq bt st Lc FF qt qg -> AsKSys7b.qroom Lc qt qg -> a_kact st <= KCAP -> WFX bt st Lc FF.
Proof using. intros bt st Lc FF qt qg W Q K. exists qt, qg. exact (conj W (conj Q K)). Qed.

Lemma WFX_WFq : forall bt st Lc FF, WFX bt st Lc FF -> WFq bt st Lc FF (q_bytes (a_tq st)) (q_bytes (a_gq st)).
Proof using.
  intros bt st Lc FF (qt & qg & W & _ & _).
  destruct W as (W1 & W2 & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof (Z.le_refl (q_bytes (a_tq st))) as L1. pose proof (Z.le_refl (q_bytes (a_gq st))) as L2.
  (lazymatch goal with |- ?G => let G' := eval unfold WFq, wf_quarantine_q in G in change_no_check G' end).
  split; [assumption|]. split; [assumption|]. split; [repeat (split; [assumption|]); assumption|]. repeat (split; [assumption|]). assumption.
Qed.
Lemma WFX_qroom : forall bt st Lc FF, WFX bt st Lc FF -> AsKSys7b.qroom Lc (q_bytes (a_tq st)) (q_bytes (a_gq st)).
Proof using.
  intros bt st Lc FF (qt & qg & W & Q & _). destruct W as (_ & _ & (_ & _ & Q3 & Q4 & _) & _).
  unfold AsKSys7b.qroom in *. clear - Q Q3 Q4. lia.
Qed.
Lemma WFX_kact : forall bt st Lc FF, WFX bt st Lc FF -> a_kact st <= KCAP.
Proof using. intros bt st Lc FF (qt & qg & _ & _ & K). exact K. Qed.
Lemma WFq_mono_bytes : forall bt st Lc FF qt qg qt' qg', WFq bt st Lc FF qt qg -> q_bytes (a_tq st) <= qt' -> q_bytes (a_gq st) <= qg' ->
  WFq bt st Lc FF qt' qg'.
Proof using.
  intros bt st Lc FF qt qg qt' qg' W L1 L2.
  destruct W as (W1 & W2 & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  (lazymatch goal with |- ?G => let G' := eval unfold WFq, wf_quarantine_q in G in change_no_check G' end).
  split; [assumption|]. split; [assumption|]. split; [repeat (split; [assumption|]); assumption|]. repeat (split; [assumption|]). assumption.
Qed.
Lemma WFX_WF : forall bt st Lc FF, WFX bt st Lc FF -> q_bytes (a_tq st) <= 2 ^ 20 -> q_bytes (a_gq st) <= 2 ^ 28 -> WF bt st Lc FF.
Proof using. intros bt st Lc FF (qt & qg & W & _ & _) L1 L2. (lazymatch goal with |- ?G => let G' := eval unfold WF in G in change_no_check G' end). exact (WFq_mono_bytes bt st Lc FF qt qg _ _ W L1 L2). Qed.

(* [comment removed for export] *)
Definition drain_changed (bt : as_boot) (KDR : Z) (Lc FF : list (Z * Z)) (sp : Z) (a : Z) : Prop :=
  (sp - KDR <= a < sp) \/ rt_priv (bt_ia bt) Lc FF a \/ in_wins (ia_priv (bt_ia bt)) a.

(* [comment removed for export] *)
Definition drain_post (bt : as_boot) (FXOK : FPState -> Prop) (KDR : Z) (st1 : ast) (Lc FF : list (Z * Z))
           (M : mem) (mdl : Model) (R : bvmap 5 word) (sp ret : word) (c' : config) : Prop :=
  exists fx' st3 (M' : mem) mdl' (R' : bvmap 5 word),
    c' = mkCfg (@mkst fx' R' ret M' (seg_rom BSEGS)) mdl'
    /\ FXOK fx' /\ m_halted mdl' = None
    /\ WF bt st3 Lc FF /\ Rep bt st3 Lc FF M' mdl'
    /\ a_kact st3 = a_kact st1 /\ ((forall h, holes_le h st1 -> holes_le h st3) /\ free_keeps st1 st3)   (* [comment removed for export] *)
    /\ (forall a : word, M' a <> M a -> drain_changed bt KDR Lc FF (U sp) (U a) /\ (M' a <> None \/ rt_priv (bt_ia bt) Lc FF (U a)))   (* [comment removed for export] *)
    /\ lazy_kept (bt_ia bt) Lc FF mdl mdl'
    /\ regs_kept R R' /\ same_except_vm mdl mdl'
    /\ BackingAlgebra.model_ivs_wf mdl'.                                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HYP_DRAIN_stmt (bt : as_boot) (FXOK : FPState -> Prop) (KDR : Z) : Prop :=
  forall fx st1 Lc FF (M : mem) mdl (R : bvmap 5 word) (sp ret stk : word),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFX bt st1 Lc FF -> Rep bt st1 Lc FF M mdl -> a_tq st1 <> [] ->
    q_bytes (a_tq st1) < 2 ^ 40 -> q_bytes (a_gq st1) <= 2 ^ 28 ->                      (* [comment removed for export] *)
    getr R 1 = ret -> getr R 2 = sp ->
    getr R 10 = Z_to_bv 64 (IB bt + 728) -> getr R 11 = Z_to_bv 64 (bt_thread bt + T_QC) ->
    getr R 12 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 13 = stk ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->                                              (* [comment removed for export] *)
    U sp mod 16 = 0 -> CEIL + KDR <= U sp -> U sp + 2224 <= PTRHI -> ret_ok ret ->           (* [comment removed for export] *)
    (forall a : word, U sp - KDR <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e260) M (seg_rom BSEGS)) mdl)
         (drain_post bt FXOK KDR st1 Lc FF M mdl R sp ret).

(* [comment removed for export] *)
Definition HYP_RECYCLE_stmt (bt : as_boot) (FXOK : FPState -> Prop) (KDR : Z) : Prop :=
  forall fx st2 Lc FF (M M0 : mem) mdl (R : bvmap 5 word) (sp ret stk : word),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFX bt st2 Lc FF -> a_tq st2 = [] -> 2 ^ 28 < q_bytes (a_gq st2) < 2 ^ 41 ->
    (* [comment removed for export] *)
    Rep bt st2 Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> U a = IB bt + 881) -> M (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 1) ->
    (forall a : word, IB bt + 904 <= U a < IB bt + 912 -> M a <> None) ->      (* [comment removed for export] *)
    M0 (Z_to_bv 64 (IB bt + 880)) = Some (Z_to_bv 8 0) -> M0 (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 0) ->   (* [comment removed for export] *)
    getr R 1 = ret -> getr R 2 = sp ->
    getr R 10 = Z_to_bv 64 (IB bt + 728) -> getr R 12 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 13 = stk ->
    (exists mn, getr R 11 = Z_to_bv 64 mn /\ In (IB bt + 800, 8%nat, mn) (bt_consts bt)) ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
    U sp mod 16 = 0 -> CEIL + KDR <= U sp -> U sp + 2224 <= PTRHI -> ret_ok ret ->           (* [comment removed for export] *)
    (forall a : word, U sp - KDR <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS)) mdl)
         (drain_post bt FXOK KDR st2 Lc FF M mdl R sp ret).
End WithCeil.
End BoAllocFHypD.
Module BoAllocFHypR.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refill24_post_k (bt : as_boot) (FXOK : FPState -> Prop) (KR : Z) (X : Z -> Prop) (st : ast) (Lc FF : list (Z * Z))
           (M : mem) (mdl : Model) (R : bvmap 5 word) (sp ret : word) (c' : config) : Prop :=
  exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word) (ks : list Z) (k : Z),
    c' = mkCfg (@mkst fx' R' ret M' (seg_rom BSEGS)) mdl'
    /\ FXOK fx' /\ m_halted mdl' = None
    /\ WF bt st' Lc FF /\ RepX bt X st' Lc FF M' mdl'
    /\ a_cache st' BATCHCLASS = ks ++ [k]
    /\ a_tq st' = a_tq st /\ a_gq st' = a_gq st /\ a_sec st' = a_sec st /\ a_dep st' = a_dep st
    /\ a_ialloc st' = a_ialloc st /\ a_kact st' = a_kact st /\ (exists naa, a_aa st' = a_aa st ++ naa)
    /\ (forall a : word, X (U a) -> (U sp <= U a \/ U a < U sp - KR) -> ~ (bt_thread bt + 2768 <= U a < bt_thread bt + 3168) -> M' a = M a)
    /\ (forall a : word, M' a <> M a ->
          ((U sp - KR <= U a < U sp) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a)) /\ M' a <> None)
    /\ lazy_kept (bt_ia bt) Lc FF mdl mdl'
    /\ regs_kept R R' /\ getr R' 10 = Z_to_bv 64 1
    /\ same_except_vm mdl mdl'
    /\ BackingAlgebra.model_ivs_wf mdl'
    /\ (forall h : option Z, holes_le h st -> holes_le h st')
    /\ free_keeps st st'.
Definition refill24_fail_post_k (bt : as_boot) (FXOK : FPState -> Prop) (KR : Z) (X : Z -> Prop) (st : ast) (Lc FF : list (Z * Z))
           (M : mem) (mdl : Model) (R : bvmap 5 word) (sp ret : word) (c' : config) : Prop :=
  exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word),
    c' = mkCfg (@mkst fx' R' ret M' (seg_rom BSEGS)) mdl'
    /\ FXOK fx' /\ m_halted mdl' = None
    /\ WF bt st' Lc FF /\ RepX bt X st' Lc FF M' mdl'
    /\ getr R' 10 = Z_to_bv 64 0.
Definition HYP_REFILL24K_stmt (bt : as_boot) (FXOK : FPState -> Prop) (KR : Z) : Prop :=
  forall fx (X : Z -> Prop) st Lc FF (M : mem) mdl (R : bvmap 5 word) (sp ret : word),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WF bt st Lc FF -> RepX bt X st Lc FF M mdl ->
    (forall a, X a -> CEIL <= a \/ (bt_thread bt + 2768 <= a < bt_thread bt + 3168)
                      \/ (exists p n, In (p, n) Lc /\ (a = p - 16 \/ p <= a < p + 8 \/ sh_lo p <= a < sh_hi p n))) ->
    a_cache st BATCHCLASS = [] -> a_kact st <= KCAP ->
    mu_room st ->                                                                             (* [comment removed for export] *)
    getr R 1 = ret -> getr R 2 = sp ->
    getr R 10 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 11 = Z_to_bv 64 (bt_thread bt + T_PC + PC_SZ * BATCHCLASS) ->
    getr R 12 = Z_to_bv 64 (IB bt) -> getr R 13 = Z_to_bv 64 BATCHCLASS ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->                                              (* [comment removed for export] *)
    U sp mod 16 = 0 -> CEIL + KR <= U sp -> U sp <= PTRHI - 16 -> ret_ok ret ->
    (forall a : word, U sp - KR <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    (forall c', refill24_fail_post_k bt FXOK KR X st Lc FF M mdl R sp ret c' -> doomed BSEGS c') ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x5143c) M (seg_rom BSEGS)) mdl)
         (refill24_post_k bt FXOK KR X st Lc FF M mdl R sp ret).
End WithCeil.

(* [comment removed for export] *)
Definition free_cells_spin (bt : as_boot) : Prop :=
  In (0x105f58, 8%nat, 1) (bt_consts bt) /\ In (0x105f60, 8%nat, 0x19fcdc) (bt_consts bt) /\ In (0x19fcdc, 4%nat, 0) (bt_consts bt).
End BoAllocFHypR.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFMemD.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.BoAllocF7.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section D7MEM.
  Context {fx : FPState}.
  Variables (mem : word -> option byte) (S ra0 s0v s1v s2v s3v : word) (T len first lastq qb glen glast gqb : Z) (b1 b2 b3 : byte).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis HT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Hglast : 2 ^ 44 <= glast /\ glast + 8192 <= U S - 3584.
  Hypothesis HglastT : glast + 8192 <= T \/ T + 4096 <= glast.

  #[local] Abbreviation MN := (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3).
  #[local] Abbreviation ME := (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3).

  Ltac prep := pose proof (u64_range S) as HSr; destruct HT as (HT1 & HT2); unfold hideW in HT2; unfold hideW in HT2.
  Ltac lsideD := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdD := (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n, fr_d7e in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); rewrite ?at_at;
              repeat (wd_rdstep rd8_side).

  (* [comment removed for export] *)
  Lemma fr_d7n_outside : forall a : word,
    (U a < U S - 2256 \/ U S - 2208 <= U a) -> (U a < 0x10aec8 \/ 0x10aecc <= U a) -> (U a < glast \/ glast + 8 <= U a) ->
    (U a < 0x10aed0 \/ 0x10aed8 <= U a) -> (U a < 0x10aee0 \/ 0x10aef0 <= U a) -> (U a < T + 80 \/ T + 112 <= U a) -> MN a = mem a.
  Proof using Hglast HT HS. prep. intros a A1 A2 A3 A4 A5 A6. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite !wbytes_outside by lsideD. reflexivity. Qed.
  Lemma fr_d7n_foot : forall a : word, MN a <> mem a ->
    (U S - 2256 <= U a < U S - 2208) \/ (0x10aec8 <= U a < 0x10aecc) \/ (glast <= U a < glast + 8)
    \/ (0x10aed0 <= U a < 0x10aed8) \/ (0x10aee0 <= U a < 0x10aef0) \/ (T + 80 <= U a < T + 112).
  Proof using HglastT Hglast HT HS. prep. intros a NE.
    destruct (decide (U S - 2256 <= U a < U S - 2208)); [am_tauto|]. destruct (decide (0x10aec8 <= U a < 0x10aecc)); [am_tauto|].
    destruct (decide (glast <= U a < glast + 8)); [am_tauto|]. destruct (decide (0x10aed0 <= U a < 0x10aed8)); [am_tauto|].
    destruct (decide (0x10aee0 <= U a < 0x10aef0)); [am_tauto|]. destruct (decide (T + 80 <= U a < T + 112)); [am_tauto|].
    exfalso. apply NE. apply fr_d7n_outside; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fr_d7n_def904 : forall a : word, 0x10ab58 + 904 <= U a < 0x10ab58 + 912 -> MN a <> None.
  Proof using HT. prep. intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). repeat (match goal with |- wbytes _ ?ad _ _ <> None => lazymatch ad with Z_to_bv 64 (0x10ab58 + 904) => fail | _ => apply wbytes_grows end end).
    match goal with |- wbytes ?m ?ad ?bs ?x <> None => rewrite (wbytes_inside bs m ad x) by lsideD end. discriminate. Qed.
  Lemma fr_d7e_def904 : forall a : word, 0x10ab58 + 904 <= U a < 0x10ab58 + 912 -> ME a <> None.
  Proof using HT. prep. intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). repeat (match goal with |- wbytes _ ?ad _ _ <> None => lazymatch ad with Z_to_bv 64 (0x10ab58 + 904) => fail | _ => apply wbytes_grows end end).
    match goal with |- wbytes ?m ?ad ?bs ?x <> None => rewrite (wbytes_inside bs m ad x) by lsideD end. discriminate. Qed.
  Lemma fr_d7e_def896 : forall a : word, 0x10ab58 + 896 <= U a < 0x10ab58 + 904 -> ME a <> None.     (* [comment removed for export] *)
  Proof using HT. prep. intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). repeat (match goal with |- wbytes _ ?ad _ _ <> None => lazymatch ad with Z_to_bv 64 (0x10ab58 + 896) => fail | _ => apply wbytes_grows end end).
    match goal with |- wbytes ?m ?ad ?bs ?x <> None => rewrite (wbytes_inside bs m ad x) by lsideD end. discriminate. Qed.
  Lemma fr_d7n_grows : mem_grows mem MN.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma fr_d7e_outside : forall a : word,
    (U a < U S - 2256 \/ U S - 2208 <= U a) -> (U a < 0x10aec8 \/ 0x10aecc <= U a) ->
    (U a < 0x10aed0 \/ 0x10aef0 <= U a) -> (U a < T + 80 \/ T + 112 <= U a) -> ME a = mem a.
  Proof using HT HS. prep. clear Hglast HglastT. intros a A1 A2 A4 A6. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). rewrite !wbytes_outside by lsideD. reflexivity. Qed.
  Lemma fr_d7e_foot : forall a : word, ME a <> mem a ->
    (U S - 2256 <= U a < U S - 2208) \/ (0x10aec8 <= U a < 0x10aecc) \/ (0x10aed0 <= U a < 0x10aef0) \/ (T + 80 <= U a < T + 112).
  Proof using HT HS. clear Hglast HglastT. prep. intros a NE.
    destruct (decide (U S - 2256 <= U a < U S - 2208)); [am_tauto|]. destruct (decide (0x10aec8 <= U a < 0x10aecc)); [am_tauto|].
    destruct (decide (0x10aed0 <= U a < 0x10aef0)); [am_tauto|]. destruct (decide (T + 80 <= U a < T + 112)); [am_tauto|].
    exfalso. apply NE. apply fr_d7e_outside; lia.
  Qed.
  Lemma fr_d7e_grows : mem_grows mem ME.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_d7n_q80 : rdn BSEGS MN (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0)).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_q88 : rdn BSEGS MN (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 0)).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_q96 : rdn BSEGS MN (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 0)).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_q104 : rdn BSEGS MN (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 0)).  Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_g888 : rdn BSEGS MN (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 (glen + len))).  Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_g904 : rdn BSEGS MN (Z_to_bv 64 (0x10ab58 + 904)) 8 = Some (LE8 (Z_to_bv 64 lastq)).         Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_g912 : rdn BSEGS MN (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 (gqb + qb))).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7n_next : rdn BSEGS MN (Z_to_bv 64 glast) 8 = Some (LE8 (Z_to_bv 64 first)).                   Proof using HglastT Hglast HT HS. prep. rdD. Qed.
  (* [comment removed for export] *)
  Lemma fr_d7n_g896 : forall v, rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some v -> rdn BSEGS MN (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some v.
  Proof using Hglast HT HS. prep. intros v Hv. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]). exact Hv. Qed.
  Lemma fr_d7n_b880 : MN (Z_to_bv 64 0x10aec8) = Some (Z_to_bv 8 0).
  Proof using HT. prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. rewrite Z.sub_diag. reflexivity. Qed.
  Lemma fr_d7n_b881 : MN (Z_to_bv 64 0x10aec9) = Some b1.
  Proof using Hglast HT HS.
    prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite !wbytes_outside by lsideD.
    rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. replace (0x10aec9 - 0x10aec8) with 1 by reflexivity. reflexivity.
  Qed.
  Lemma fr_d7n_b882 : MN (Z_to_bv 64 0x10aeca) = Some b2.
  Proof using Hglast HT HS.
    prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite !wbytes_outside by lsideD.
    rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. replace (0x10aeca - 0x10aec8) with 2 by reflexivity. reflexivity.
  Qed.
  Lemma fr_d7n_b883 : MN (Z_to_bv 64 0x10aecb) = Some b3.
  Proof using Hglast HT HS.
    prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite !wbytes_outside by lsideD.
    rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. replace (0x10aecb - 0x10aec8) with 3 by reflexivity. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_d7e_q80 : rdn BSEGS ME (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0)).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_q88 : rdn BSEGS ME (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 0)).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_q96 : rdn BSEGS ME (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 0)).    Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_q104 : rdn BSEGS ME (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 0)).  Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_g888 : rdn BSEGS ME (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 len)).          Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_g896 : rdn BSEGS ME (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some (LE8 (Z_to_bv 64 first)).        Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_g904 : rdn BSEGS ME (Z_to_bv 64 (0x10ab58 + 904)) 8 = Some (LE8 (Z_to_bv 64 lastq)).        Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_g912 : rdn BSEGS ME (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 (gqb + qb))).   Proof using HT HS. prep. rdD. Qed.
  Lemma fr_d7e_b880 : ME (Z_to_bv 64 0x10aec8) = Some (Z_to_bv 8 0).
  Proof using HT. prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. rewrite Z.sub_diag. reflexivity. Qed.
  Lemma fr_d7e_b881 : ME (Z_to_bv 64 0x10aec9) = Some b1.
  Proof using HT HS.
    prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). rewrite !wbytes_outside by lsideD.
    rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. replace (0x10aec9 - 0x10aec8) with 1 by reflexivity. reflexivity.
  Qed.
  Lemma fr_d7e_b882 : ME (Z_to_bv 64 0x10aeca) = Some b2.
  Proof using HT HS.
    prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). rewrite !wbytes_outside by lsideD.
    rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. replace (0x10aeca - 0x10aec8) with 2 by reflexivity. reflexivity.
  Qed.
  Lemma fr_d7e_b883 : ME (Z_to_bv 64 0x10aecb) = Some b3.
  Proof using HT HS.
    prep. (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). rewrite !wbytes_outside by lsideD.
    rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. replace (0x10aecb - 0x10aec8) with 3 by reflexivity. reflexivity.
  Qed.
End D7MEM.
End BoAllocFMemD.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_dr0 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2296)) (LE8 ra0))
    (at_ S (-2304)) (LE8 s0v))
    (at_ S (-2312)) (LE8 s1v))
    (at_ S (-2320)) (LE8 s2v))
    (at_ S (-2328)) (LE8 s3v))
    (at_ S (-2336)) (LE8 s4v))
    (at_ S (-2344)) (LE8 s5v))
    (at_ S (-2352)) (LE8 s6v))
    (at_ S (-2360)) (LE8 s7v))
    (at_ S (-2368)) (LE8 s8v))
    (at_ S (-2376)) (LE8 s9v))
    (at_ S (-2392)) (LE8 a2v))
    (at_ S (-2384)) (LE8 a3v).
#[local] Hint Unfold fr_dr0 : asfr.

(* [comment removed for export] *)
Definition dr_regs (S : word) (r : bvmap 5 word) : Prop :=
    getr r 2 = at_ S (-2400) /\ getr r 8 = at_ S (-2288) /\ getr r 9 = Z_to_bv 64 0x10ab58 /\ getr r 21 = Z_to_bv 64 (2 ^ 37)
    /\ getr r 18 = Z_to_bv 64 (0x10ab58 + 64) /\ getr r 19 = Z_to_bv 64 (0x10ab58 + 688).
Definition dr_keep (r r' : bvmap 5 word) : Prop :=
    getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.

Section DRPRE.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word) (tsz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H11 : getr regs 11 = at_ S (-2288).
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Htsz : (0 <= tsz < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2400)) 112 = true.
  Hypothesis Rtsz : rdn BSEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 tsz)).

  #[local] Abbreviation M0 := (fr_dr0 mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v).

  Ltac dr_prefix :=
      an F_4e76c D_4e76c;                              (* [comment removed for export] *)
      fsd F_4e770 D_4e770 (at_ S (-2296));             (* [comment removed for export] *)
      fsd F_4e774 D_4e774 (at_ S (-2304));             (* [comment removed for export] *)
      fsd F_4e778 D_4e778 (at_ S (-2312));             (* [comment removed for export] *)
      fsd F_4e77c D_4e77c (at_ S (-2320));             (* [comment removed for export] *)
      fsd F_4e780 D_4e780 (at_ S (-2328));             (* [comment removed for export] *)
      fsd F_4e784 D_4e784 (at_ S (-2336));             (* [comment removed for export] *)
      fsd F_4e788 D_4e788 (at_ S (-2344));             (* [comment removed for export] *)
      fsd F_4e78c D_4e78c (at_ S (-2352));             (* [comment removed for export] *)
      fsd F_4e790 D_4e790 (at_ S (-2360));             (* [comment removed for export] *)
      fsd F_4e794 D_4e794 (at_ S (-2368));             (* [comment removed for export] *)
      fsd F_4e798 D_4e798 (at_ S (-2376));             (* [comment removed for export] *)
      cld8 F_4e79c D_4e79c (Z_to_bv 64 tsz) Rtsz;      (* [comment removed for export] *)
      fsd F_4e7a0 D_4e7a0 (at_ S (-2392));             (* [comment removed for export] *)
      fsd F_4e7a4 D_4e7a4 (at_ S (-2384)).             (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dr_pre_loop : (tsz <> 0)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e76c : word) mem rom) (mkst r (0x4e7e4 : word) M0 rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 10 = Z_to_bv 64 tsz.
  Proof using Rtsz Hstk Htsz HS H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H2 H1.
    intros Nz. (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - dr_prefix.
      ab_ft F_4e7a8 D_4e7a8 ltac:(condz).              (* [comment removed for export] *)
      an F_4e7ac D_4e7ac.                              (* [comment removed for export] *)
      an F_4e7b0 D_4e7b0.                              (* [comment removed for export] *)
      an F_4e7b4 D_4e7b4.                              (* [comment removed for export] *)
      an F_4e7b8 D_4e7b8.                              (* [comment removed for export] *)
      av F_4e7bc D_4e7bc (Z_to_bv 64 (2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
      an F_4e7c0 D_4e7c0.                              (* [comment removed for export] *)
      an F_4e7c4 D_4e7c4.                              (* [comment removed for export] *)
      an F_4e7c8 D_4e7c8.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0. wd_refl.
    - post.
  Qed.

End DRPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_drb (mem : word -> option byte) (S : word) (tsz tby bsz nx : Z) : word -> option byte :=
  let m1 := wbytes mem (at_ S (-2280)) (LE8 (Z_to_bv 64 nx)) in
  let m2 := if (nx =? 0)%Z then wbytes m1 (at_ S (-2272)) (LE8 (Z_to_bv 64 0)) else m1 in
  wbytes (wbytes m2 (at_ S (-2288)) (LE8 (Z_to_bv 64 (tsz - 1)))) (at_ S (-2264)) (LE8 (Z_to_bv 64 (tby - bsz))).

Section DRBHEAD.
  Variables (mem rom : word -> option byte) (S : word) (tsz tby b bsz nx cnt : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : dr_regs S regs.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 tsz.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Htsz : (1 <= tsz < 2 ^ 28)%Z.
  Hypothesis Htby : (0 <= bsz <= tby /\ tby < 2 ^ 42)%Z.
  Hypothesis Hnx : (0 <= nx < 2 ^ 64)%Z.
  Hypothesis Hcnt : (0 <= cnt <= 1021)%Z.
  Hypothesis Hb : (AIMGHI <= b /\ b + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2288)) 32 = true.
  Hypothesis Rfirst : rdn BSEGS mem (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 b)).
  Hypothesis Rtby : rdn BSEGS mem (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 tby)).
  Hypothesis Rnx : rdn BSEGS mem (Z_to_bv 64 b) 8 = Some (LE8 (Z_to_bv 64 nx)).
  Hypothesis Rbsz : rdn BSEGS mem (Z_to_bv 64 (b + 8)) 8 = Some (LE8 (Z_to_bv 64 bsz)).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 (b + 16)) 8 = Some (LE8 (Z_to_bv 64 cnt)).

  #[local] Abbreviation Mb := (fr_drb mem S tsz tby bsz nx).

  Ltac bh1 :=
      cld8 F_4e7e4 D_4e7e4 (Z_to_bv 64 b) Rfirst;      (* [comment removed for export] *)
      cld8 F_4e7e8 D_4e7e8 (Z_to_bv 64 nx) Rnx;        (* [comment removed for export] *)
      fsd F_4e7ec D_4e7ec (at_ S (-2280)).             (* [comment removed for export] *)
  Ltac bh2 :=
      av F_4e7f8 D_4e7f8 (Z_to_bv 64 (tsz - 1)) ltac:(valz);     (* [comment removed for export] *)
      fsd F_4e7fc D_4e7fc (at_ S (-2288));             (* [comment removed for export] *)
      cld8 F_4e800 D_4e800 (Z_to_bv 64 bsz) Rbsz;      (* [comment removed for export] *)
      cld8 F_4e804 D_4e804 (Z_to_bv 64 tby) Rtby;      (* [comment removed for export] *)
      av F_4e808 D_4e808 (Z_to_bv 64 (tby - bsz)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4e80c D_4e80c (at_ S (-2264));             (* [comment removed for export] *)
      cld8 F_4e810 D_4e810 (Z_to_bv 64 cnt) Rcnt.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dr_bhead_items : (cnt <> 0)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e7e4 : word) mem rom) (mkst r (0x4e824 : word) Mb rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = Z_to_bv 64 b
      /\ getr r 23 = Z_to_bv 64 (b + 152) /\ getr r 24 = Z_to_bv 64 (cnt + 16) /\ getr r 25 = Z_to_bv 64 16.
  Proof using Rcnt Rbsz Rnx Rtby Rfirst Hstk Hb Hcnt Hnx Htby Htsz HS H10 HR.
    intros Nc. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). destruct (Z.eqb_spec nx 0) as [Enx | Nnx]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    - wd_eexists. split.
      + bh1. ab_ft F_4e7f0 D_4e7f0 ltac:(condz). fsd F_4e7f4 D_4e7f4 (at_ S (-2272)). bh2.
        ab_ft F_4e814 D_4e814 ltac:(condz).            (* [comment removed for export] *)
        av F_4e818 D_4e818 (Z_to_bv 64 (b + 152)) ltac:(valz).   (* [comment removed for export] *)
        av F_4e81c D_4e81c (Z_to_bv 64 (cnt + 16)) ltac:(valz).  (* [comment removed for export] *)
        an F_4e820 D_4e820.                            (* [comment removed for export] *)
        wd_refl.
      + post.
    - wd_eexists. split.
      + bh1. ab_tk F_4e7f0 D_4e7f0 ltac:(condz). bh2.
        ab_ft F_4e814 D_4e814 ltac:(condz).
        av F_4e818 D_4e818 (Z_to_bv 64 (b + 152)) ltac:(valz).
        av F_4e81c D_4e81c (Z_to_bv 64 (cnt + 16)) ltac:(valz).
        an F_4e820 D_4e820.
        wd_refl.
      + post.
  Qed.

  (* [comment removed for export] *)
  Lemma dr_bhead_empty : (cnt = 0)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e7e4 : word) mem rom) (mkst r (0x4e83c : word) Mb rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = Z_to_bv 64 b.
  Proof using Rcnt Rbsz Rnx Rtby Rfirst Hstk Hb Hcnt Hnx Htby Htsz HS H10 HR.
    intros Ec. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). destruct (Z.eqb_spec nx 0) as [Enx | Nnx]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    - wd_eexists. split.
      + bh1. ab_ft F_4e7f0 D_4e7f0 ltac:(condz). fsd F_4e7f4 D_4e7f4 (at_ S (-2272)). bh2.
        ab_tk F_4e814 D_4e814 ltac:(condz). wd_refl.
      + post.
    - wd_eexists. split.
      + bh1. ab_tk F_4e7f0 D_4e7f0 ltac:(condz). bh2.
        ab_tk F_4e814 D_4e814 ltac:(condz). wd_refl.
      + post.
  Qed.
End DRBHEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DRITEM.
  Variables (mem rom : word -> option byte) (S : word) (c7 c8 i9 item : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : dr_regs S regs.
  Hypothesis H23 : getr regs 23 = Z_to_bv 64 c7.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 c8.
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 i9.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc7 : (128 <= c7 /\ c7 + 8 < 2 ^ 64)%Z.
  Hypothesis Hi9 : (0 <= i9 < 2 ^ 32 /\ 0 <= c8 < 2 ^ 32)%Z.

  Definition dr_cursor (r : bvmap 5 word) (x7 x8 x9 : Z) : Prop :=
    getr r 23 = Z_to_bv 64 x7 /\ getr r 24 = Z_to_bv 64 x8 /\ getr r 25 = Z_to_bv 64 x9 /\ getr r 20 = getr regs 20.

  (* [comment removed for export] *)
  Lemma dr_item_call :
    rdn BSEGS mem (Z_to_bv 64 (c7 - 128)) 8 = Some (LE8 (Z_to_bv 64 item)) ->
    exists r, msteps BSEGS (mkst regs (0x4e824 : word) mem rom) (mkst r (0x4e8a4 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ dr_cursor r c7 c8 i9
      /\ getr r 1 = Z_to_bv 64 0x4e830 /\ getr r 10 = at_ S (-2392) /\ getr r 11 = Z_to_bv 64 item.
  Proof using Hc7 H25 H24 H23 HR.
    intros Ritem. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep, dr_cursor in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e824 D_4e824 (Z_to_bv 64 item) Ritem.    (* [comment removed for export] *)
      an F_4e828 D_4e828.                              (* [comment removed for export] *)
      an F_4e82c D_4e82c.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma dr_item_next_more : (i9 + 1 <> c8)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e830 : word) mem rom) (mkst r (0x4e824 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ dr_cursor r (c7 + 8) c8 (i9 + 1).
  Proof using Hi9 Hc7 H25 H24 H23 HR.
    intros Nm. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep, dr_cursor in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - av F_4e830 D_4e830 (Z_to_bv 64 (i9 + 1)) ltac:(valz).   (* [comment removed for export] *)
      av F_4e834 D_4e834 (Z_to_bv 64 (c7 + 8)) ltac:(valz).   (* [comment removed for export] *)
      ab_tk F_4e838 D_4e838 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
  Lemma dr_item_next_done : (i9 + 1 = c8)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e830 : word) mem rom) (mkst r (0x4e83c : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = getr regs 20.
  Proof using Hi9 Hc7 H25 H24 H23 HR c7.
    intros Em. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - av F_4e830 D_4e830 (Z_to_bv 64 (i9 + 1)) ltac:(valz).
      av F_4e834 D_4e834 (Z_to_bv 64 (c7 + 8)) ltac:(valz).
      ab_ft F_4e838 D_4e838 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End DRITEM.

Section DRBFREE.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v cachev : word) (spb b d tsz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : dr_regs S regs.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 b.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis Hb : (b = spb + 24 * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32)%Z.                (* [comment removed for export] *)
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Rcache : rdn BSEGS mem (at_ S (-2392)) 8 = Some (LE8 cachev).

  (* [comment removed for export] *)
  Lemma dr_bfree_call :
    exists r, msteps BSEGS (mkst regs (0x4e83c : word) mem rom) (mkst r (0x4eca8 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = Z_to_bv 64 b
      /\ getr r 1 = Z_to_bv 64 0x4e868 /\ getr r 10 = cachev /\ getr r 11 = Z_to_bv 64 0x10ab58 /\ getr r 12 = Z_to_bv 64 24 /\ getr r 13 = Z_to_bv 64 b.
  Proof using Rcache Rspb Hb Hspb H20 HR d spb.
    destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct Hb as (Eb & Hd).
    wd_eexists. split.
    - cld8 F_4e83c D_4e83c (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      ab_ft F_4e840 D_4e840 ltac:(condz).              (* [comment removed for export] *)
      av F_4e844 D_4e844 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4e848 D_4e848 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e84c D_4e84c cachev Rcache.              (* [comment removed for export] *)
      av F_4e850 D_4e850 (Z_to_bv 64 (24 * 2 ^ 32 + d)) ltac:(valz).   (* [comment removed for export] *)
      an F_4e854 D_4e854.                              (* [comment removed for export] *)
      av F_4e858 D_4e858 (Z_to_bv 64 24) ltac:(apply (cls_of_off 24 d); lia).   (* [comment removed for export] *)
      an F_4e85c D_4e85c.                              (* [comment removed for export] *)
      an F_4e860 D_4e860.                              (* [comment removed for export] *)
      an F_4e864 D_4e864.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Rtsz : rdn BSEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 tsz)).
  Hypothesis Htsz : (0 <= tsz < 2 ^ 64)%Z.
  Lemma dr_bnext_more : (tsz <> 0)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e868 : word) mem rom) (mkst r (0x4e7e4 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 10 = Z_to_bv 64 tsz.
  Proof using Htsz Rtsz HR.
    intros Nz. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e868 D_4e868 (Z_to_bv 64 tsz) Rtsz.      (* [comment removed for export] *)
      ab_tk F_4e86c D_4e86c ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  Hypothesis Hret : ret_ok ra0.
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2296)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2304)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2312)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2320)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn BSEGS mem (at_ S (-2328)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn BSEGS mem (at_ S (-2336)) 8 = Some (LE8 s4v).
  Hypothesis Cs5 : rdn BSEGS mem (at_ S (-2344)) 8 = Some (LE8 s5v).
  Hypothesis Cs6 : rdn BSEGS mem (at_ S (-2352)) 8 = Some (LE8 s6v).
  Hypothesis Cs7 : rdn BSEGS mem (at_ S (-2360)) 8 = Some (LE8 s7v).
  Hypothesis Cs8 : rdn BSEGS mem (at_ S (-2368)) 8 = Some (LE8 s8v).
  Hypothesis Cs9 : rdn BSEGS mem (at_ S (-2376)) 8 = Some (LE8 s9v).
  Lemma dr_bnext_done : (tsz = 0)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e868 : word) mem rom) (mkst r ra0 mem rom)
      /\ getr r 2 = at_ S (-2288) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = s5v /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ dr_keep regs r.
  Proof using Cs9 Cs8 Cs7 Cs6 Cs5 Cs4 Cs3 Cs2 Cs1 Cs0 Cra Hret Htsz Rtsz HR.
    intros Ez. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e868 D_4e868 (Z_to_bv 64 tsz) Rtsz.      (* [comment removed for export] *)
      ab_ft F_4e86c D_4e86c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e870 D_4e870 ra0 Cra. cld8 F_4e874 D_4e874 s0v Cs0. cld8 F_4e878 D_4e878 s1v Cs1. cld8 F_4e87c D_4e87c s2v Cs2.
      cld8 F_4e880 D_4e880 s3v Cs3. cld8 F_4e884 D_4e884 s4v Cs4. cld8 F_4e888 D_4e888 s5v Cs5. cld8 F_4e88c D_4e88c s6v Cs6.
      cld8 F_4e890 D_4e890 s7v Cs7. cld8 F_4e894 D_4e894 s8v Cs8. cld8 F_4e898 D_4e898 s9v Cs9.
      an F_4e89c D_4e89c.                              (* [comment removed for export] *)
      aret F_4e8a0 D_4e8a0 ra0.                        (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End DRBFREE.
End FPGen.
End BoAllocFRc2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc2U.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem BoAllocFRc2.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Ltac lsideD := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.

Section DRBMEM.
  Variables (mem : word -> option byte) (S : word) (tsz tby bsz nx : Z).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  #[local] Abbreviation Mb := (fr_drb mem S tsz tby bsz nx).

  Lemma fr_drb_outside : forall a : word, (U a < U S - 2288 \/ U S - 2256 <= U a) -> Mb a = mem a.
  Proof using HS.
    intros a Ha. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec nx 0); rewrite !wbytes_outside by lsideD; reflexivity.
  Qed.
  Lemma fr_drb_grows : mem_grows mem Mb.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). destruct (Z.eqb_spec nx 0); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. Qed.
  Lemma fr_drb_bytes : rdn BSEGS Mb (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 (tby - bsz))).
  Proof using HS. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). apply rdn_wbytes_hit8. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. lia. Qed.
  Lemma fr_drb_size : rdn BSEGS Mb (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (tsz - 1))).
  Proof using HS.
    pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite rdn_wbytes_out by lsideD.
    apply rdn_wbytes_hit8. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. lia.
  Qed.
  Lemma fr_drb_first : rdn BSEGS Mb (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 nx)).
  Proof using HS.
    pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). do 2 rewrite rdn_wbytes_out by lsideD.
    destruct (Z.eqb_spec nx 0); [rewrite rdn_wbytes_out by lsideD|]; apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Qed.
End DRBMEM.

Section DR0MEM.
  Variables (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  #[local] Abbreviation M0 := (fr_dr0 mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v).

  Lemma fr_dr0_outside : forall a : word, (U a < U S - 2400 \/ U S - 2288 <= U a) -> M0 a = mem a.
  Proof using HS. intros a Ha. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_dr0 in G in change_no_check G' end). rewrite !wbytes_outside by lsideD. reflexivity. Qed.
  Lemma fr_dr0_grows : mem_grows mem M0.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_dr0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Ltac rdD := pose proof (u64_range S) as HSr; (lazymatch goal with |- ?G => let G' := eval unfold fr_dr0 in G in change_no_check G' end); repeat (wd_rdstep rd8_side).
  Lemma fr_dr0_ra : rdn BSEGS M0 (at_ S (-2296)) 8 = Some (LE8 ra0).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s0 : rdn BSEGS M0 (at_ S (-2304)) 8 = Some (LE8 s0v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s1 : rdn BSEGS M0 (at_ S (-2312)) 8 = Some (LE8 s1v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s2 : rdn BSEGS M0 (at_ S (-2320)) 8 = Some (LE8 s2v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s3 : rdn BSEGS M0 (at_ S (-2328)) 8 = Some (LE8 s3v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s4 : rdn BSEGS M0 (at_ S (-2336)) 8 = Some (LE8 s4v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s5 : rdn BSEGS M0 (at_ S (-2344)) 8 = Some (LE8 s5v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s6 : rdn BSEGS M0 (at_ S (-2352)) 8 = Some (LE8 s6v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s7 : rdn BSEGS M0 (at_ S (-2360)) 8 = Some (LE8 s7v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s8 : rdn BSEGS M0 (at_ S (-2368)) 8 = Some (LE8 s8v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_s9 : rdn BSEGS M0 (at_ S (-2376)) 8 = Some (LE8 s9v).  Proof using HS. rdD. Qed.
  Lemma fr_dr0_a2 : rdn BSEGS M0 (at_ S (-2392)) 8 = Some (LE8 a2v).  Proof using HS. rdD. Qed.

End DR0MEM.
End FPGen.
End BoAllocFRc2U.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcH.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition rc_changed (bt : as_boot) (Lc FF : list (Z * Z)) (S : Z) (a : Z) : Prop :=
  (S - 3584 <= a < S - 2400) \/ rt_priv (bt_ia bt) Lc FF a \/ in_wins (ia_priv (bt_ia bt)) a.

(* [comment removed for export] *)
Definition rc_step_post (bt : as_boot) (FXOK : FPState -> Prop) (X : Z -> Prop) (qt qg : Z) (st : ast) (Lc FF : list (Z * Z))
           (M : mem) (mdl : Model) (R : bvmap 5 word) (S ret : word) (GQ' : list batch) (c' : config) : Prop :=
  exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word),
    c' = mkCfg (@mkst fx' R' ret M' (seg_rom BSEGS)) mdl'
    /\ FXOK fx' /\ m_halted mdl' = None /\ BackingAlgebra.model_ivs_wf mdl'
    /\ WFq bt st' Lc FF qt qg /\ AsAinvOpsRc73.AsAinvRepX3.RepX bt X st' Lc FF M' mdl'
    /\ a_gq st' = GQ' /\ a_tq st' = a_tq st /\ a_kact st' = a_kact st /\ ((forall h, holes_le h st -> holes_le h st') /\ free_keeps st st')   (* [comment removed for export] *)
    /\ (forall z, X z -> XB bt st' z)
    /\ (forall a : word, X (U a) \/ U S - 2400 <= U a -> M' a = M a)
    /\ (forall a : word, M' a <> M a -> rc_changed bt Lc FF (U S) (U a) /\ (M' a <> None \/ rt_priv (bt_ia bt) Lc FF (U a)))
    /\ lazy_kept (bt_ia bt) Lc FF mdl mdl' /\ same_except_vm mdl mdl'
    /\ regs_kept R R'.

(* [comment removed for export] *)
Definition rc_budget (st : ast) (Lc : list (Z * Z)) (qt qg : Z) : Prop := AsKSys7b.qroom Lc qt qg /\ a_kact st <= KCAP.

(* [comment removed for export] *)
Definition rc_item_stmt (bt : as_boot) (FXOK : FPState -> Prop) (ARM : ast -> Z -> Z -> Prop) : Prop :=
  forall fx (X : Z -> Prop) (Xd : Xdec X) qt qg st Lc FF (M : mem) mdl (R : bvmap 5 word) (S ret : word) ba m n its rest,
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFq bt st Lc FF qt qg -> AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M mdl ->
    a_gq st = BATCH ba ((m, n) :: its) :: rest -> ARM st m n ->
    (forall z, X z -> XB bt st z) -> (forall z, qhdr bt z -> X z) -> (forall z, ba <= z < ba + BATCHSZ -> X z) ->
    (forall a : word, qhdr bt (U a) -> M a <> None) ->
    getr R 1 = ret -> ret_ok ret -> getr R 2 = at_ S (-2400) -> getr R 10 = at_ S (-2392) -> getr R 11 = Z_to_bv 64 m ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
    rdn BSEGS M (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (bt_thread bt + T_PC))) ->
    U S mod 16 = 0 -> CEIL + 3584 <= U S -> U S + 16 <= PTRHI ->
    (forall a : word, U S - 3584 <= U a < U S - 2400 -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    rc_budget st Lc qt qg ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS)) mdl)
         (rc_step_post bt FXOK X qt qg st Lc FF M mdl R S ret (BATCH ba its :: rest)).

(* [comment removed for export] *)
Definition rc_bfree_stmt (bt : as_boot) (FXOK : FPState -> Prop) (ARM : ast -> Prop) : Prop :=
  forall fx (X : Z -> Prop) (Xd : Xdec X) qt qg st Lc FF (M : mem) mdl (R : bvmap 5 word) (S ret : word) ba rest,
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFq bt st Lc FF qt qg -> AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M mdl ->
    a_gq st = BATCH ba [] :: rest -> ARM st ->
    (forall z, X z -> XB bt st z) -> (forall z, qhdr bt z -> X z) -> (forall z, ba <= z < ba + BATCHSZ -> X z) ->
    (forall a : word, qhdr bt (U a) -> M a <> None) ->
    getr R 1 = ret -> ret_ok ret -> getr R 2 = at_ S (-2400) ->
    getr R 10 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 11 = Z_to_bv 64 (IB bt) -> getr R 12 = Z_to_bv 64 BATCHCLASS -> getr R 13 = Z_to_bv 64 ba ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
    U S mod 16 = 0 -> CEIL + 3584 <= U S -> U S + 16 <= PTRHI ->
    (forall a : word, U S - 3584 <= U a < U S - 2400 -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    rc_budget st Lc qt qg ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS)) mdl)
         (rc_step_post bt FXOK X qt qg st Lc FF M mdl R S ret rest).

(* [comment removed for export] *)
Definition rc_cells (bt : as_boot) (TSDP : Z) : Prop :=
  In (IB bt + 48, 8%nat, bt_spacebeg bt + KSPACE) (bt_consts bt) /\ In (0x103b0, 8%nat, MAGIC) (bt_consts bt)
  /\ (TSDP + 8 <= IB bt + 888 \/ IB bt + 920 <= TSDP).

(* [comment removed for export] *)
Definition arm_prim_room (st : ast) (m n : Z) : Prop :=
  is_primary n = true /\ Z.of_nat (length (a_cache st (blk_class n))) < cache_max (blk_class n).
Definition arm_prim_full (st : ast) (m n : Z) : Prop :=
  is_primary n = true /\ cache_max (blk_class n) <= Z.of_nat (length (a_cache st (blk_class n))).
Definition arm_sec (st : ast) (m n : Z) : Prop := is_primary n = false.
Definition arm_room24 (st : ast) : Prop := Z.of_nat (length (a_cache st BATCHCLASS)) < cache_max BATCHCLASS.
Definition arm_full24 (st : ast) : Prop := cache_max BATCHCLASS <= Z.of_nat (length (a_cache st BATCHCLASS)).
Definition arm_any (st : ast) (m n : Z) : Prop := True.
Definition arm_any24 (st : ast) : Prop := True.

(* [comment removed for export] *)
Lemma rc_item_of_arms : forall bt FXOK,
  rc_item_stmt bt FXOK arm_prim_room -> rc_item_stmt bt FXOK arm_prim_full -> rc_item_stmt bt FXOK arm_sec ->
  rc_item_stmt bt FXOK arm_any.
Proof using.
  intros bt FXOK H1 H2 H3 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest.
  intros A1 A2 A3 A4 A5 A6 _.
  destruct (is_primary n) eqn:EP.
  - destruct (Z_lt_le_dec (Z.of_nat (length (a_cache st (blk_class n)))) (cache_max (blk_class n))) as [L | G].
    + apply (H1 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest A1 A2 A3 A4 A5 A6). split; [exact EP | exact L].
    + apply (H2 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest A1 A2 A3 A4 A5 A6). split; [exact EP | exact G].
  - apply (H3 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest A1 A2 A3 A4 A5 A6). exact EP.
Qed.
Lemma rc_bfree_of_arms : forall bt FXOK,
  rc_bfree_stmt bt FXOK arm_room24 -> rc_bfree_stmt bt FXOK arm_full24 -> rc_bfree_stmt bt FXOK arm_any24.
Proof using.
  intros bt FXOK H1 H2 fx X Xd qt qg st Lc FF M mdl R S ret ba rest.
  intros A1 A2 A3 A4 A5 A6 _.
  destruct (Z_lt_le_dec (Z.of_nat (length (a_cache st BATCHCLASS))) (cache_max BATCHCLASS)) as [L | G].
  - apply (H1 fx X Xd qt qg st Lc FF M mdl R S ret ba rest A1 A2 A3 A4 A5 A6). exact L.
  - apply (H2 fx X Xd qt qg st Lc FF M mdl R S ret ba rest A1 A2 A3 A4 A5 A6). exact G.
Qed.
End WithCeil.
End BoAllocFRcH.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK1a.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition nxaddr (q : list batch) : Z := match q with [] => 0 | b :: _ => ba_addr b end.

Fixpoint trips (q : list batch) (k : nat) : list ptrip :=
  match k, q with
  | Datatypes.S k', b :: q' => (ba_addr b, ba_bytes b, nxaddr q') :: trips q' k'
  | _, _ => []
  end.

Fixpoint npop (minsz : Z) (q : list batch) : nat :=
  match q with
  | [] => 0%nat
  | b :: q' => Datatypes.S (if minsz <? q_bytes q' then npop minsz q' else 0%nat)
  end.

Lemma q_bytes_consK : forall b q, q_bytes (b :: q) = ba_bytes b + q_bytes q.
Proof. reflexivity. Qed.

Lemma q_bytes_nonneg : forall q, (forall b, In b q -> 0 <= ba_bytes b) -> 0 <= q_bytes q.
Proof.
  induction q as [|b q IH]; intros H; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. rewrite q_bytes_consK.
  specialize (IH ltac:(intros b0 Hb0; apply H; right; exact Hb0)). specialize (H b (or_introl eq_refl)). lia.
Qed.

Lemma npop_le : forall minsz q, (npop minsz q <= length q)%nat.
Proof.
  intros minsz q. induction q as [|b q IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [npop length] in G in change_no_check G' end). destruct (minsz <? q_bytes q); lia.
Qed.
Lemma npop_pos : forall minsz q, q <> [] -> (1 <= npop minsz q)%nat.
Proof. intros minsz q NE. destruct q; [exfalso; exact (NE eq_refl) | (lazymatch goal with |- ?G => let G' := eval cbn [npop] in G in change_no_check G' end); lia]. Qed.

Lemma trips_len : forall q k, (k <= length q)%nat -> length (trips q k) = k.
Proof.
  induction q as [|b q IH]; intros k Hk; [cbn in Hk; destruct k; [reflexivity | lia]|].
  destruct k as [|k]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [trips length] in G in change_no_check G' end). rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.
Lemma trips_addr : forall q k, map p_addr (trips q k) = map ba_addr (firstn k q).
Proof.
  induction q as [|b q IH]; intros k; [destruct k; reflexivity|]. destruct k as [|k]; [reflexivity|].
  (lazymatch goal with |- ?G => let G' := eval cbn [trips firstn map] in G in change_no_check G' end). rewrite IH. reflexivity.
Qed.
Lemma trips_in : forall q k t, In t (trips q k) -> exists b, In b (firstn k q) /\ p_addr t = ba_addr b /\ p_sz t = ba_bytes b.
Proof.
  induction q as [|b q IH]; intros k t Ht; [destruct k; contradiction|]. destruct k as [|k]; [contradiction|].
  cbn [trips firstn] in *. destruct Ht as [<- | Ht]; [exists b; split; [left; reflexivity | split; reflexivity]|].
  destruct (IH k t Ht) as (b0 & Hb0 & E). exists b0. split; [right; exact Hb0 | exact E].
Qed.
Lemma trips_tot : forall q k, (k <= length q)%nat -> p_tot (trips q k) = q_bytes (firstn k q).
Proof.
  induction q as [|b q IH]; intros k Hk; [destruct k; reflexivity|]. destruct k as [|k]; [reflexivity|].
  (lazymatch goal with |- ?G => let G' := eval cbn [trips firstn p_tot] in G in change_no_check G' end). rewrite q_bytes_consK, IH by (cbn in Hk; lia). reflexivity.
Qed.
Lemma trips_lastnx : forall q k d, (1 <= k <= length q)%nat -> p_lastnx (trips q k) d = nxaddr (skipn k q).
Proof.
  induction q as [|b q IH]; intros k d Hk; [cbn in Hk; lia|]. destruct k as [|k]; [lia|].
  (lazymatch goal with |- ?G => let G' := eval cbn [trips p_lastnx skipn] in G in change_no_check G' end). destruct k as [|k].
  - destruct q; reflexivity.
  - rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.
Lemma trips_lasta : forall q k d, (1 <= k <= length q)%nat -> p_lasta (trips q k) d = nxaddr (rev (firstn k q)).
Proof.
  induction q as [|b q IH]; intros k d Hk; [cbn in Hk; lia|]. destruct k as [|k]; [lia|].
  (lazymatch goal with |- ?G => let G' := eval cbn [trips p_lasta firstn] in G in change_no_check G' end). destruct k as [|k].
  - destruct q; reflexivity.
  - rewrite IH by (cbn in Hk; lia). (lazymatch goal with |- ?G => let G' := eval cbn [rev] in G in change_no_check G' end). destruct q as [|b' q']; [cbn in Hk; lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [firstn rev] in G in change_no_check G' end).
    destruct (rev (firstn k q') ++ [b']) eqn:E; [destruct (rev (firstn k q')); discriminate E | reflexivity].
Qed.
Lemma trips_head : forall q k, (1 <= k)%nat -> q <> [] -> match trips q k with [] => 0 | t :: _ => p_addr t end = nxaddr q.
Proof. intros q k Hk NE. destruct q; [exfalso; exact (NE eq_refl)|]. destruct k; [lia | reflexivity]. Qed.


Theorem pops_ok_trips : forall minsz q,
  (forall b, In b q -> 0 <= ba_bytes b /\ 0 <= ba_addr b < 2 ^ 64) -> minsz < q_bytes q -> 0 <= minsz ->
  pops_ok minsz (nxaddr q) (q_bytes q) (trips q (npop minsz q)).
Proof.
  intros minsz. induction q as [|b q IH]; intros RNG Hlt Hmin; [cbn in Hlt; lia|].
  assert (RNG' : forall b0, In b0 q -> 0 <= ba_bytes b0 /\ 0 <= ba_addr b0 < 2 ^ 64) by (intros b0 Hb0; apply RNG; right; exact Hb0).
  pose proof (q_bytes_nonneg q ltac:(intros b0 Hb0; exact (proj1 (RNG' b0 Hb0)))) as QN. destruct (RNG b (or_introl eq_refl)) as [Bb Ba].
  (lazymatch goal with |- ?G => let G' := eval cbn [npop trips pops_ok p_addr p_sz p_nx fst snd nxaddr] in G in change_no_check G' end). rewrite q_bytes_consK in *.
  split; [reflexivity|]. split; [lia|].
  split; [destruct q as [|b' q']; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (proj2 (RNG' b' (or_introl eq_refl)))]|].
  destruct (Z.ltb_spec minsz (q_bytes q)) as [L | G].
  - assert (NE : q <> []) by (intros E; subst q; cbn in L; lia).
    destruct (trips q (npop minsz q)) eqn:ET.
    + exfalso. pose proof (trips_len q (npop minsz q) (npop_le minsz q)) as TL. rewrite ET in TL. pose proof (npop_pos minsz q NE). cbn in TL. lia.
    + split; [lia|]. replace (ba_bytes b + q_bytes q - ba_bytes b) with (q_bytes q) by lia. exact (IH RNG' L Hmin).
  - destruct q; (lazymatch goal with |- ?G => let G' := eval cbn [trips] in G in change_no_check G' end); lia.
Qed.

Lemma rest_bytes : forall minsz q, (forall b, In b q -> 0 <= ba_bytes b) -> 0 <= minsz -> q_bytes (skipn (npop minsz q) q) <= minsz.
Proof.
  intros minsz. induction q as [|b q IH]; intros RNG Hmin; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  (lazymatch goal with |- ?G => let G' := eval cbn [npop skipn] in G in change_no_check G' end). destruct (Z.ltb_spec minsz (q_bytes q)) as [L | G].
  - apply IH; [intros b0 Hb0; apply RNG; right; exact Hb0 | exact Hmin].
  - (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end). exact G.
Qed.

(* [comment removed for export] *)
Lemma all_sep_of : forall (l : list Z), List.NoDup l -> (forall x y, In x l -> In y l -> x <> y -> bsep x y) -> all_sep l.
Proof.
  induction l as [|x l IH]; intros ND SEP; [exact I|]. inversion ND as [|x' l' NI ND']; subst. (lazymatch goal with |- ?G => let G' := eval cbn [all_sep] in G in change_no_check G' end). split.
  - apply Forall_forall. intros y Hy. apply SEP; [left; reflexivity | right; exact Hy | intros E; subst y; exact (NI Hy)].
  - apply IH; [exact ND' | intros a b Ha Hb; apply SEP; right; assumption].
Qed.

(* [comment removed for export] *)
Lemma trips_nth : forall q k i t, nth_error (trips q k) i = Some t ->
  exists b, nth_error q i = Some b /\ (i < k)%nat /\ t = (ba_addr b, ba_bytes b, nxaddr (skipn (Datatypes.S i) q)).
Proof.
  induction q as [|b q IH]; intros k i t H; [destruct k, i; discriminate H|].
  destruct k as [|k]; [destruct i; discriminate H|]. cbn [trips] in H. destruct i as [|i].
  - cbn in H. injection H as <-. exists b. split; [reflexivity|]. split; [lia | reflexivity].
  - cbn [nth_error] in H. destruct (IH k i t H) as (b0 & Hb0 & Hi & Et). exists b0. split; [exact Hb0|]. split; [lia | exact Et].
Qed.
Lemma trips_forall : forall (P : ptrip -> Prop) q k,
  (forall i b, (i < k)%nat -> nth_error q i = Some b -> P (ba_addr b, ba_bytes b, nxaddr (skipn (Datatypes.S i) q))) -> Forall P (trips q k).
Proof.
  intros P q k H. apply Forall_forall. intros t Ht. destruct (In_nth_error _ _ Ht) as (i & Hi).
  destruct (trips_nth q k i t Hi) as (b & Hb & Lt & ->). exact (H i b Lt Hb).
Qed.
Lemma trips_nth_inv : forall q k i b, (i < k)%nat -> nth_error q i = Some b ->
  nth_error (trips q k) i = Some (ba_addr b, ba_bytes b, nxaddr (skipn (Datatypes.S i) q)).
Proof.
  induction q as [|b0 q IH]; intros k i b Hi Hb; [destruct i; discriminate Hb|].
  destruct k as [|k]; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [trips] in G in change_no_check G' end). destruct i as [|i].
  - cbn in Hb. injection Hb as <-. reflexivity.
  - cbn [nth_error] in Hb |- *. exact (IH k i b ltac:(lia) Hb).
Qed.
Lemma nxaddr_skipn : forall q i, nxaddr (skipn i q) = match nth_error q i with Some b => ba_addr b | None => 0 end.
Proof. induction q as [|b q IH]; intros i; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity | exact (IH i)]. Qed.
Lemma nxaddr_rev_app : forall (p r : list batch), r <> [] -> nxaddr (rev (p ++ r)) = nxaddr (rev r).
Proof.
  intros p r NE. rewrite rev_app_distr. destruct (rev r) as [|x y] eqn:E; [| reflexivity].
  exfalso. apply NE. apply (f_equal (@rev batch)) in E. rewrite rev_involutive in E. exact E.
Qed.
Lemma firstn_InK : forall {A} (l : list A) k x, In x (firstn k l) -> In x l.
Proof.
  intros A l. induction l as [|y l IH]; intros k x H; [destruct k; contradiction|].
  destruct k as [|k]; [contradiction|]. cbn [firstn] in H. destruct H as [<- | H]; [left; reflexivity | right; exact (IH k x H)].
Qed.
Lemma skipn_InK : forall {A} (l : list A) k x, In x (skipn k l) -> In x l.
Proof.
  intros A l. induction l as [|y l IH]; intros k x H; [destruct k; contradiction|].
  destruct k as [|k]; [exact H|]. cbn [skipn] in H. right. exact (IH k x H).
Qed.

Lemma nth_firstn_inv : forall {A} (l : list A) k i x, nth_error (firstn k l) i = Some x -> (i < k)%nat /\ nth_error l i = Some x.
Proof.
  intros A l. induction l as [|y l IH]; intros k i x H; [destruct k, i; discriminate H|].
  destruct k as [|k]; [destruct i; discriminate H|]. destruct i as [|i]; [cbn in H |- *; split; [lia | exact H]|].
  cbn [firstn nth_error] in H |- *. destruct (IH k i x H) as [L E]. split; [lia | exact E].
Qed.
Lemma nth_match_map : forall {A} (f : A -> Z) (l : list A) i, match nth_error l i with Some x => f x | None => 0 end = nth i (map f l) 0.
Proof. intros A f l. induction l as [|y l IH]; intros i; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity | exact (IH i)]. Qed.
Lemma trips_next_eq : forall q k i,
  match nth_error (trips q k) i with Some t => p_addr t | None => 0 end = match nth_error (firstn k q) i with Some b => ba_addr b | None => 0 end.
Proof. intros q k i. rewrite (nth_match_map p_addr), (nth_match_map ba_addr), trips_addr. reflexivity. Qed.
Lemma nxaddr_firstn : forall q k, (1 <= k)%nat -> nxaddr (firstn k q) = nxaddr q.
Proof. intros q k Hk. destruct q; [destruct k; reflexivity|]. destruct k; [lia | reflexivity]. Qed.
End BoAllocFRcK1a.
Module BoAllocFRcL.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Lemma restrict_mkstK : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defK : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

(* [comment removed for export] *)
Lemma cellX : forall (Hd : word -> bool) (M M0 : mem) (X : Z -> Prop) a n v,
  cellZ BSEGS M0 a n v -> (forall x : word, ~ X (U x) -> M x = M0 x) ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat n -> ~ X z /\ Hd (Z_to_bv 64 z) = false) ->
  rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros Hd M M0 X a n v C EQ Ha Hn OFF.
  rewrite rdn_mrestrict; [| wd_ulia | unorm; apply hid_off_of; intros z Hz; split; [lia | exact (proj2 (OFF z Hz))]].
  eapply rd_same; [| wd_ulia | exact C].
  intros x Hx. apply EQ. revert Hx. unorm. intros Hx. exact (proj1 (OFF (U x) Hx)).
Qed.

(* [comment removed for export] *)
Lemma sokX : forall (Hd : word -> bool) (M M0 : mem) lo hi a (n : nat),
  writableZ BSEGS M0 lo hi -> mem_grows M0 M ->
  lo <= a -> a + Z.of_nat n <= hi -> hi < 2 ^ 64 -> 0 <= a ->
  (forall z, a <= z < a + Z.of_nat n -> Hd (Z_to_bv 64 z) = false) ->
  store_ok BSEGS (mrestrict Hd M) (Z_to_bv 64 a) n = true.
Proof.
  intros Hd M M0 lo hi a n WR GR H1 H2 H3 H0 OFF.
  rewrite store_ok_mrestrict; [| wd_ulia | unorm; apply hid_off_of; intros z Hz; split; [lia | exact (OFF z Hz)]].
  eapply store_ok_mono; [exact GR|]. apply (writableZ_store_ok M0 lo hi _ _ WR); wd_ulia.
Qed.

(* [comment removed for export] *)
Lemma sokD : forall (Hd : word -> bool) (M : mem) a (n : nat),
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat n -> M (Z_to_bv 64 z) <> None /\ Hd (Z_to_bv 64 z) = false) ->
  store_ok BSEGS (mrestrict Hd M) (Z_to_bv 64 a) n = true.
Proof.
  intros Hd M a n H0 Hn OFF.
  rewrite store_ok_mrestrict; [| wd_ulia | unorm; apply hid_off_of; intros z Hz; split; [lia | exact (proj2 (OFF z Hz))]].
  apply store_ok_bytes; [| wd_ulia]. intros x Hx. apply store_ok1_defK.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (proj1 (OFF (U x) ltac:(revert Hx; unorm; intros Hx; lia))).
Qed.

(* [comment removed for export] *)
Lemma regs_kept_litK : forall (R R' : bvmap 5 word) (r : bv 5),
  regs_kept R R' -> existsb (Z.eqb (bv_unsigned r)) as_callee_saved = true -> getr R' r = getr R r.
Proof. intros R R' r RK Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply RK. apply in_cs. exact Hr. Qed.
End BoAllocFRcL.
Module BoAllocFRcK4a.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG BoAllocFRcL BoAllocFRcH.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

Section K4a.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.

  (* [comment removed for export] *)
  Definition acc_changed (Lc FF : list (Z * Z)) (S : Z) (a : Z) : Prop :=
    (S - 3584 <= a < S - 2208) \/ rt_priv (bt_ia bt) Lc FF a \/ in_wins (ia_priv (bt_ia bt)) a.

  Definition rc_acc (Lc FF : list (Z * Z)) (S : word) (X : Z -> Prop) (st0 : ast) (M0 : mem) (mdl0 : Model) (st : ast) (M : mem) (mdl : Model) : Prop :=
    a_tq st = a_tq st0 /\ a_kact st = a_kact st0 /\ ((forall h, holes_le h st0 -> holes_le h st) /\ free_keeps st0 st)   (* [comment removed for export] *)
    /\ (forall a : word, X (U a) -> M a = M0 a)
    /\ (forall a : word, M a <> M0 a -> acc_changed Lc FF (U S) (U a) /\ (M a <> None \/ rt_priv (bt_ia bt) Lc FF (U a)))
    /\ lazy_kept (bt_ia bt) Lc FF mdl0 mdl /\ same_except_vm mdl0 mdl.

  Lemma rc_acc_refl : forall Lc FF S X st M mdl, rc_acc Lc FF S X st M mdl st M mdl.
  Proof using.
    intros Lc FF S X st M mdl. (lazymatch goal with |- ?G => let G' := eval unfold rc_acc in G in change_no_check G' end).
    split; [reflexivity|]. split; [reflexivity|]. split; [split; [intros h H; exact H | apply fk_refl]|]. split; [intros a _; reflexivity|].
    split; [intros a NE; exfalso; exact (NE eq_refl)|]. split; [intros a _; reflexivity | apply same_except_vm_refl].
  Qed.

  Lemma rc_acc_trans : forall Lc FF S X st0 M0 mdl0 st1 M1 mdl1 st2 M2 mdl2,
    rc_acc Lc FF S X st0 M0 mdl0 st1 M1 mdl1 -> rc_acc Lc FF S X st1 M1 mdl1 st2 M2 mdl2 -> rc_acc Lc FF S X st0 M0 mdl0 st2 M2 mdl2.
  Proof using.
    intros Lc FF S X st0 M0 mdl0 st1 M1 mdl1 st2 M2 mdl2 (A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    (lazymatch goal with |- ?G => let G' := eval unfold rc_acc in G in change_no_check G' end). split; [congruence|]. split; [congruence|]. split; [split; [intros h H; exact (proj1 B3 h (proj1 A3 h H)) | exact (fk_trans _ _ _ (proj2 A3) (proj2 B3))]|].
    split; [intros a Ha; rewrite (B4 a Ha); exact (A4 a Ha)|].
    split.
    { intros a NE. destruct (decide (M2 a = M1 a)) as [E | N]; [| exact (B5 a N)]. rewrite E in NE |- *. exact (A5 a NE). }
    split; [intros a Ha; rewrite (B6 a Ha); exact (A6 a Ha)|].
    exact (same_except_vm_trans _ _ _ A7 B7).
  Qed.

  Lemma rc_acc_sbm : forall Lc FF S X st0 M0 mdl0 st M mdl mdl',
    rc_acc Lc FF S X st0 M0 mdl0 st M mdl -> same_but_materialized mdl mdl' -> rc_acc Lc FF S X st0 M0 mdl0 st M mdl'.
  Proof using.
    intros Lc FF S X st0 M0 mdl0 st M mdl mdl' (A1 & A2 & A3 & A4 & A5 & A6 & A7) SBM.
    pose proof (same_but_materialized_frame mdl mdl' SBM) as (_ & _ & Elz & _).
    (lazymatch goal with |- ?G => let G' := eval unfold rc_acc in G in change_no_check G' end). repeat (split; [assumption|]). split.
    - intros a Ha. rewrite <- (A6 a Ha). (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite Elz. reflexivity.
    - eapply same_except_vm_trans; [exact A7 | apply same_but_materialized_except_vm; exact SBM].
  Qed.

  (* [comment removed for export] *)
  Lemma rc_acc_step : forall Lc FF S X st M mdl st' (M' : mem) mdl',
    a_tq st' = a_tq st -> a_kact st' = a_kact st -> ((forall h, holes_le h st -> holes_le h st') /\ free_keeps st st') ->
    (forall a : word, X (U a) \/ U S - 2400 <= U a -> M' a = M a) ->
    (forall a : word, M' a <> M a -> rc_changed bt Lc FF (U S) (U a) /\ (M' a <> None \/ rt_priv (bt_ia bt) Lc FF (U a))) ->
    lazy_kept (bt_ia bt) Lc FF mdl mdl' -> same_except_vm mdl mdl' ->
    rc_acc Lc FF S X st M mdl st' M' mdl'.
  Proof using.
    intros Lc FF S X st M mdl st' M' mdl' A1 A2 A3 A4 A5 A6 A7. (lazymatch goal with |- ?G => let G' := eval unfold rc_acc in G in change_no_check G' end).
    repeat (split; [assumption|]). split; [intros a Ha; apply A4; left; exact Ha|]. split; [| exact (conj A6 A7)].
    intros a NE. destruct (A5 a NE) as [C D]. split; [| exact D]. unfold rc_changed in C. (lazymatch goal with |- ?G => let G' := eval unfold acc_changed in G in change_no_check G' end).
    destruct C as [C | [C | C]]; [left; lia | right; left; exact C | right; right; exact C].
  Qed.

  (* [comment removed for export] *)
  Lemma rc_acc_stack : forall Lc FF S X st M mdl (M' : mem) {qt qg : Z},
    WFq bt st Lc FF qt qg -> (forall z, X z -> XB bt st z) -> CEIL + 3584 <= U S ->
    (forall a : word, M' a <> M a -> (U S - 3584 <= U a < U S - 2208) /\ M' a <> None) ->
    rc_acc Lc FF S X st M mdl st M' mdl.
  Proof using.
    intros Lc FF S X st M mdl M' qt qg W XSUB Slo CH. (lazymatch goal with |- ?G => let G' := eval unfold rc_acc in G in change_no_check G' end).
    split; [reflexivity|]. split; [reflexivity|]. split; [split; [intros h H; exact H | apply fk_refl]|].
    split.
    { intros a Ha. destruct (decide (M' a = M a)) as [E | N]; [exact E|]. exfalso. destruct (CH a N) as [R _].
      pose proof (XB_below_ceil bt st Lc FF W _ (XSUB _ Ha)) as [_ LT]. lia. }
    split; [intros a NE; destruct (CH a NE) as [R D]; split; [left; exact R | left; exact D]|].
    split; [intros a Ha; reflexivity | apply same_except_vm_refl].
  Qed.

  (* [comment removed for export] *)
  Lemma katD_loadsX : forall fx st Lc FF (M M0 : mem) mdl (R R' : bvmap 5 word) (pc pc' : word) (Q : config -> Prop),
    Rep bt st Lc FF M0 mdl -> m_halted mdl = None ->
    msteps BSEGS (@mkst fx R pc (mrestrict (HID st mdl) M) (seg_rom BSEGS)) (@mkst fx R' pc' (mrestrict (HID st mdl) M) (seg_rom BSEGS)) ->
    (forall mdl', Rep bt st Lc FF M0 mdl' -> m_halted mdl' = None -> same_but_materialized mdl mdl' ->
        katD BSEGS (mkCfg (@mkst fx R' pc' M (seg_rom BSEGS)) mdl') Q) ->
    katD BSEGS (mkCfg (@mkst fx R pc M (seg_rom BSEGS)) mdl) Q.
  Proof using BT_ia.
    intros fx st Lc FF M M0 mdl R R' pc pc' Q RP HH RUN K.
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    apply (katD_msteps_acct BSEGS (HID st mdl) (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R pc M (seg_rom BSEGS)) (@mkst fx R' pc' (mrestrict (HID st mdl) M) (seg_rom BSEGS)) mdl Q).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - rewrite restrict_mkstK. exact RUN.
    - intros mdl' MI SBM HC. rewrite unrestrict_mkst.
      change (ms_mem (@mkst fx R pc M (seg_rom BSEGS))) with M. rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl' SBM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh & _).
      apply K; [exact (Rep_sbm bt st Lc FF M0 mdl mdl' RP MI SBM) | rewrite Eh; exact HH | exact SBM].
  Qed.

  (* [comment removed for export] *)
  Lemma RepX_stack : forall (X : Z -> Prop) st Lc FF (M M' : mem) mdl {qt qg : Z},
    WFq bt st Lc FF qt qg -> AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> CEIL <= U a /\ M' a <> None) ->
    AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M' mdl.
  Proof using.
    intros X st Lc FF M M' mdl qt qg W (M0 & RP & DX) CH.
    exists (fun a : word => if Z_le_dec CEIL (U a) then M' a else M0 a). split.
    - apply (Rep_frame_q bt st Lc FF M0 _ mdl W RP). intros a NE. destruct (Z_le_dec CEIL (U a)) as [GE | LT]; [| exfalso; exact (NE eq_refl)].
      split; [intros RC'; exact (ceil_not_cells bt st Lc FF W (U a) GE RC')|].
      destruct (decide (M' a = M a)) as [E | N]; [| exact (proj2 (CH a N))].
      rewrite E in NE |- *. exact (proj2 (DX a NE)).
    - intros a NE. destruct (Z_le_dec CEIL (U a)) as [GE | LT]; [exfalso; exact (NE eq_refl)|].
      destruct (decide (M' a = M a)) as [E | N]; [| exfalso; destruct (CH a N) as [G _]; lia].
      rewrite E in NE |- *. exact (DX a NE).
  Qed.

  (* [comment removed for export] *)
  Lemma rep_batches_tail : forall (M : mem) b q, rep_batches bt M (b :: q) -> rep_batches bt M q.
  Proof using. intros M b q RB i b' Hb'. exact (RB (Datatypes.S i) b' Hb'). Qed.

  Lemma rep_batches_same : forall (M M' : mem) q,
    rep_batches bt M q ->
    (forall b, In b q -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP) ->
    (forall b (a : word), In b q -> ba_addr b <= U a < ba_addr b + BATCHSZ -> M' a = M a) ->
    rep_batches bt M' q.
  Proof using.
    intros M M' q RB RNG AG i b Hb. pose proof (nth_error_In _ _ Hb) as Hin. destruct (RNG b Hin) as (R1 & R2 & R3).
    destruct (RB i b Hb) as (B1 & B2 & B3 & B4 & BW). unfold BATCHSZ, BATCHCAP in *.
    assert (AGb : forall z, ba_addr b <= z < ba_addr b + 8192 -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
    { intros z Hz. apply (AG b _ Hin). unorm. lia. }
    split; [eapply cellZ_frame; [exact B1 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply AGb; cbn in Hz; lia]|].
    split; [eapply cellZ_frame; [exact B2 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply AGb; cbn in Hz; lia]|].
    split; [eapply cellZ_frame; [exact B3 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply AGb; cbn in Hz; lia]|].
    split.
    - intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Lj.
      eapply cellZ_frame; [exact (B4 j mn Hj) | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply AGb; cbn in Hz; lia].
    - eapply writableZ_frame; [exact BW|]. intros z Hz. left. apply AGb. exact Hz.
  Qed.
End K4a.
End BoAllocFRcK4a.
Module BoAllocFRcK4b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD BoAllocFRc2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG BoAllocFRcL BoAllocFRcH BoAllocFRcK4a.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Lemma skipn_cons_nth : forall {A} (l : list A) i x r, skipn i l = x :: r -> nth_error l i = Some x /\ skipn (Datatypes.S i) l = r.
Proof.
  intros A l. induction l as [|y l IH]; intros i x r H.
  - destruct i; discriminate H.
  - destruct i as [|i]; [cbn in H; injection H as -> ->; split; reflexivity|]. cbn [skipn] in H. exact (IH i x r H).
Qed.
Lemma skipn_nonempty : forall {A} (l : list A) i, (i < length l)%nat -> exists x r, skipn i l = x :: r.
Proof.
  intros A l. induction l as [|y l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [exists y, l; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end). apply IH. cbn in Hi. lia.
Qed.

Section K4b.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis HITEM : rc_item_stmt bt FXOK arm_any.

  (* [comment removed for export] *)
  Variables (S : word) (X : Z -> Prop) (Xd : Xdec X) (qt qg : Z) (Lc FF : list (Z * Z)).
  Variables (st0 : ast) (M00 : mem) (mdl0 : Model).
  Variables (ba : Z) (items0 : list (Z * Z)) (rest : list batch).
  Hypothesis XQ : forall z, qhdr bt z -> X z.
  Hypothesis XOBJ : forall z, ba <= z < ba + BATCHSZ -> X z.
  Hypothesis S16 : U S mod 16 = 0.
  Hypothesis Slo : CEIL + 3584 <= U S.
  Hypothesis Shi : U S + 16 <= PTRHI.
  Hypothesis Gcnt : Z.of_nat (length items0) <= BATCHCAP.
  Hypothesis QRK : rc_budget st0 Lc qt qg.                       (* [comment removed for export] *)

  Definition ili (fx : FPState) (st : ast) (M : mem) (mdl : Model) (R : bvmap 5 word) (i : nat) : Prop :=
    FXOK fx /\ m_halted mdl = None /\ BackingAlgebra.model_ivs_wf mdl
    /\ WFq bt st Lc FF qt qg /\ AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M mdl
    /\ a_gq st = BATCH ba (skipn i items0) :: rest
    /\ (forall z, X z -> XB bt st z)
    /\ (forall a : word, qhdr bt (U a) -> M a <> None)
    /\ (forall j mn, nth_error items0 j = Some mn -> rdn BSEGS M (Z_to_bv 64 (ba + 24 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 (fst mn))))
    /\ rdn BSEGS M (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (bt_thread bt + T_PC)))
    /\ (forall a : word, U S - 3584 <= U a < U S - 2400 -> M a <> None /\ store_ok BSEGS M a 1%nat = true)
    /\ dr_regs S R /\ getr R 20 = Z_to_bv 64 ba /\ getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt))
    /\ rc_acc bt Lc FF S X st0 M00 mdl0 st M mdl.

  Definition item_loop_post (M : mem) (R : bvmap 5 word) (c' : config) : Prop :=
    exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word),
      c' = mkCfg (@mkst fx' R' (Z_to_bv 64 0x4e83c) M' (seg_rom BSEGS)) mdl'
      /\ ili fx' st' M' mdl' R' (length items0)
      /\ (forall a : word, U S - 2400 <= U a -> M' a = M a) /\ dr_keep R R'.

  Lemma dr_keep_trans : forall r1 r2 r3 : bvmap 5 word, dr_keep r1 r2 -> dr_keep r2 r3 -> dr_keep r1 r3.
  Proof using. intros r1 r2 r3 (A3 & A4 & A26 & A27) (B3 & B4 & B26 & B27). (lazymatch goal with |- ?G => let G' := eval unfold dr_keep in G in change_no_check G' end). repeat split; congruence. Qed.

  Definition cursor (R : bvmap 5 word) (i : nat) : Prop :=
    getr R 23 = Z_to_bv 64 (ba + 152 + 8 * Z.of_nat i) /\ getr R 24 = Z_to_bv 64 (Z.of_nat (length items0) + 16) /\ getr R 25 = Z_to_bv 64 (16 + Z.of_nat i).

  (* [comment removed for export] *)
  Lemma rc_item_step : forall (i : nat) fx st (M : mem) mdl (R : bvmap 5 word),
    (i < length items0)%nat -> ili fx st M mdl R i -> cursor R i ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e824) M (seg_rom BSEGS)) mdl)
         (fun c' => exists fx2 st2 (M2 : mem) mdl2 (R2 : bvmap 5 word),
            c' = mkCfg (@mkst fx2 R2 (Z_to_bv 64 0x4e830) M2 (seg_rom BSEGS)) mdl2
            /\ ili fx2 st2 M2 mdl2 R2 (Datatypes.S i) /\ cursor R2 i /\ (forall a : word, U S - 2400 <= U a -> M2 a = M a) /\ dr_keep R R2).
  Proof using QRK Gcnt Shi Slo S16 XOBJ XQ Xd HITEM BT_ia.
    intros i fx st M mdl R Hik INV (H23 & H24 & H25).
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr. unfold PTRHI, BATCHCAP, BATCHSZ in *.
    destruct INV as (HFX & HH & MW & W & RX & EGQ & XSUB & QDEF & ITEMS & CCB & SOK & HR & R20 & R4 & ACC).
    destruct (skipn_nonempty items0 i Hik) as ([m n] & its & ESK). destruct (skipn_cons_nth items0 i (m, n) its ESK) as [Hnth ESK'].
    rewrite ESK in EGQ.
    assert (Hb : In (BATCH ba ((m, n) :: its)) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    destruct (batch_facts bt st Lc FF W _ Hb) as (_ & _ & GB1 & GB2). cbn [ba_addr] in GB1, GB2.
    pose proof (thread_dyn bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    unfold KSPACE, PG, AS_HEAPLO, BATCHSZ in *.
    pose proof RX as (M0 & RP & DX).
    set (Hd := HID st mdl).
    assert (NHB : forall z, ba <= z < ba + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 GB1 GB2 CR; lia|].
      apply (rep_nolazy_batch bt st Lc FF M0 mdl W RP _ z Hb). (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). exact Hz. }
    assert (Hi : Z.of_nat i < Z.of_nat (length items0)) by lia.
    assert (Ritem : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (ba + 152 + 8 * Z.of_nat i - 128)) 8 = Some (LE8 (Z_to_bv 64 m))).
    { replace (ba + 152 + 8 * Z.of_nat i - 128) with (ba + 24 + 8 * Z.of_nat i) by (clear; lia).
      rewrite rdn_mrestrict; [exact (ITEMS i (m, n) Hnth) | clear - Hi Gcnt GB1 GB2 SB0 SB1 CR; wd_ulia_c |].
      rewrite u_Z2bv by (clear - Hi Gcnt GB1 GB2 SB0 SB1 CR; lia).
      apply hid_off_of. intros z Hz. split; [clear - Hz Hi Gcnt GB1 GB2 SB0 SB1 CR; cbn in Hz; lia | apply NHB; clear - Hz Hi Gcnt; cbn in Hz; lia]. }
    destruct (dr_item_call (mrestrict Hd M) (seg_rom BSEGS) S (ba + 152 + 8 * Z.of_nat i) (Z.of_nat (length items0) + 16) (16 + Z.of_nat i) m R HR H23 H24 H25
                ltac:(clear - Hi Gcnt GB1 GB2 SB0 SB1 CR; lia) Ritem)
      as (r1 & RUN1 & HR1 & (K3 & K4 & K26 & K27) & (C23 & C24 & C25 & C20) & C1 & C10 & C11).
    replace (0x4e824%bv : word) with (Z_to_bv 64 0x4e824 : word) in RUN1 by (apply bv_eq; reflexivity).
    apply (katD_loadsX bt BT_ia fx st Lc FF M M0 mdl R r1 _ _ _ RP HH RUN1). intros mdl1 RP1 HH1 SBM1.
    replace (0x4e8a4%bv : word) with (Z_to_bv 64 0x4e8a4 : word) by (apply bv_eq; reflexivity).
    pose proof HR1 as (D2 & D8 & D9 & D21 & D18 & D19).
    apply (katD_bind BSEGS _ (rc_step_post bt FXOK X qt qg st Lc FF M mdl1 r1 S (Z_to_bv 64 0x4e830) (BATCH ba its :: rest))).
    { apply (HITEM fx X Xd qt qg st Lc FF M mdl1 r1 S (Z_to_bv 64 0x4e830) ba m n its rest HFX HH1 (model_ivs_wf_sbm mdl mdl1 SBM1 MW) W
               (ex_intro _ M0 (conj RP1 DX)) EGQ I XSUB XQ).
      - intros z Hz. apply XOBJ. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). exact Hz.
      - exact QDEF.
      - exact C1.
      - apply ret_ok_lit; [clear; lia | reflexivity].
      - exact D2.
      - exact C10.
      - exact C11.
      - rewrite K4. exact R4.
      - exact CCB.
      - exact S16.
      - exact Slo.
      - (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). exact Shi.
      - exact SOK.
      - split; [exact (proj1 QRK) | rewrite (proj1 (proj2 ACC)); exact (proj2 QRK)]. }
    intros c2 POST2.
    destruct POST2 as (fx2 & st2 & M2 & mdl2 & R2 & -> & HFX2 & HH2 & MW2 & W2 & RX2 & EGQ2 & ETQ2 & EKA2 & HO2 & XSUB2 & KEPT2 & CH2 & LZ2 & SEV2 & RK2).
    apply katD_refl. exists fx2, st2, M2, mdl2, R2. split; [reflexivity|].
    assert (ACC2 : rc_acc bt Lc FF S X st0 M00 mdl0 st2 M2 mdl2).
    { eapply rc_acc_trans; [exact (rc_acc_sbm bt Lc FF S X _ _ _ _ _ _ _ ACC SBM1) | exact (rc_acc_step bt Lc FF S X st M mdl1 st2 M2 mdl2 ETQ2 EKA2 HO2 KEPT2 CH2 LZ2 SEV2)]. }
    assert (HR2 : dr_regs S R2).
    { (lazymatch goal with |- ?G => let G' := eval unfold dr_regs in G in change_no_check G' end). rewrite (regs_kept_litK r1 R2 2 RK2 eq_refl), (regs_kept_litK r1 R2 8 RK2 eq_refl), (regs_kept_litK r1 R2 9 RK2 eq_refl),
        (regs_kept_litK r1 R2 21 RK2 eq_refl), (regs_kept_litK r1 R2 18 RK2 eq_refl), (regs_kept_litK r1 R2 19 RK2 eq_refl). exact HR1. }
    assert (E20 : getr R2 20 = Z_to_bv 64 ba) by (rewrite (regs_kept_litK r1 R2 20 RK2 eq_refl), C20; exact R20).
    assert (E4 : getr R2 4 = Z_to_bv 64 (ia_tp (bt_ia bt))) by (rewrite (regs_kept_litK r1 R2 4 RK2 eq_refl), K4; exact R4).
    assert (ITEMS2 : forall j mn, nth_error items0 j = Some mn -> rdn BSEGS M2 (Z_to_bv 64 (ba + 24 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 (fst mn)))).
    { intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Lj.
      eapply rd_same; [| clear - Lj Gcnt GB1 GB2 SB0 SB1 CR; wd_ulia_c | exact (ITEMS j mn Hj)].
      intros x Hx. apply KEPT2. left. apply XOBJ. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). clear - Hx Lj Gcnt GB1 GB2 SB0 SB1 CR. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia. }
    assert (CCB2 : rdn BSEGS M2 (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (bt_thread bt + T_PC)))).
    { eapply rd_same; [| clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact CCB].
      intros x Hx. apply KEPT2. right. clear - Hx HSr Slo CR. rewrite at_u in Hx by lia. lia. }
    assert (QDEF2 : forall a : word, qhdr bt (U a) -> M2 a <> None) by (intros a Ha; rewrite (KEPT2 a (or_introl (XQ _ Ha))); exact (QDEF a Ha)).
    assert (SOK2 : forall a : word, U S - 3584 <= U a < U S - 2400 -> M2 a <> None /\ store_ok BSEGS M2 a 1%nat = true).
    { intros a Ha. assert (D : M2 a <> None).
      { destruct (decide (M2 a = M a)) as [E | N]; [rewrite E; exact (proj1 (SOK a Ha))|].
        destruct (proj2 (CH2 a N)) as [D | (LT & _)]; [exact D | exfalso; clear - LT Ha Slo; lia]. }
      exact (conj D (store_ok1_defK M2 a D)). }
    split; [| split; [| split]].
    - (lazymatch goal with |- ?G => let G' := eval unfold ili in G in change_no_check G' end). rewrite ESK'. repeat (split; [assumption|]). assumption.
    - (lazymatch goal with |- ?G => let G' := eval unfold cursor in G in change_no_check G' end). rewrite (regs_kept_litK r1 R2 23 RK2 eq_refl), (regs_kept_litK r1 R2 24 RK2 eq_refl), (regs_kept_litK r1 R2 25 RK2 eq_refl).
      exact (conj C23 (conj C24 C25)).
    - intros a Ha. apply KEPT2. right. exact Ha.
    - (lazymatch goal with |- ?G => let G' := eval unfold dr_keep in G in change_no_check G' end). rewrite (regs_kept_litK r1 R2 3 RK2 eq_refl), (regs_kept_litK r1 R2 4 RK2 eq_refl), (regs_kept_litK r1 R2 26 RK2 eq_refl), (regs_kept_litK r1 R2 27 RK2 eq_refl).
      exact (conj K3 (conj K4 (conj K26 K27))).
  Qed.

  (* [comment removed for export] *)
  Lemma ili_sbm : forall fx st (M : mem) mdl mdl' (R R' : bvmap 5 word) i,
    ili fx st M mdl R i -> same_but_materialized mdl mdl' -> m_halted mdl' = None ->
    (forall M0, Rep bt st Lc FF M0 mdl -> Rep bt st Lc FF M0 mdl') ->
    dr_regs S R' -> getr R' 20 = getr R 20 -> getr R' 4 = getr R 4 -> ili fx st M mdl' R' i.
  Proof using.
    intros fx st M mdl mdl' R R' i (A1 & A2 & A3 & A4 & (M0 & RP & DX) & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15) SBM HH' RPK HR' E20 E4.
    (lazymatch goal with |- ?G => let G' := eval unfold ili in G in change_no_check G' end). split; [exact A1|]. split; [exact HH'|]. split; [exact (model_ivs_wf_sbm mdl mdl' SBM A3)|]. split; [exact A4|].
    split; [exists M0; split; [exact (RPK M0 RP) | exact DX]|].
    split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11|].
    split; [exact HR'|]. split; [rewrite E20; exact A13|]. split; [rewrite E4; exact A14|].
    exact (rc_acc_sbm bt Lc FF S X _ _ _ _ _ _ _ A15 SBM).
  Qed.

  Theorem rc_item_loop : forall (k i : nat) fx st (M : mem) mdl (R : bvmap 5 word),
    (i + Datatypes.S k = length items0)%nat -> ili fx st M mdl R i -> cursor R i ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e824) M (seg_rom BSEGS)) mdl) (item_loop_post M R).
  Proof using QRK Gcnt Shi Slo S16 XOBJ XQ Xd HITEM BT_ia.
    induction k as [|k IH]; intros i fx st M mdl R Hik INV CUR.
    all: apply (katD_bind BSEGS _ _ _ (rc_item_step i fx st M mdl R ltac:(lia) INV CUR)).
    all: intros c2 (fx2 & st2 & M2 & mdl2 & R2 & -> & INV2 & (E23 & E24 & E25) & KEPTS & DK2).
    all: pose proof ceil_rng as CR; unfold BATCHCAP in *.
    all: pose proof INV2 as (_ & HH2 & _ & W2 & (M02 & RP2 & DX2) & EGQ2 & _ & _ & _ & _ & _ & HR2 & _).
    all: assert (Hb : In (BATCH ba (skipn (Datatypes.S i) items0)) (a_tq st2 ++ a_gq st2)) by (apply in_app_iff; right; rewrite EGQ2; left; reflexivity).
    all: destruct (batch_facts bt st2 Lc FF W2 _ Hb) as (_ & _ & GB1 & GB2); cbn [ba_addr] in GB1, GB2.
    all: pose proof (thread_dyn bt st2 Lc FF W2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    all: unfold KSPACE, PG, AS_HEAPLO, BATCHSZ in *.
    all: assert (Hi : Z.of_nat i < Z.of_nat (length items0)) by lia.
    - (* [comment removed for export] *)
      destruct (dr_item_next_done (mrestrict (HID st2 mdl2) M2) (seg_rom BSEGS) S (ba + 152 + 8 * Z.of_nat i) (Z.of_nat (length items0) + 16) (16 + Z.of_nat i) R2 HR2 E23 E24 E25
                  ltac:(clear - Hi Gcnt GB1 GB2 SB0 SB1 CR; lia) ltac:(clear - Hi Gcnt; lia) ltac:(clear - Hik; lia))
        as (r3 & RUN3 & HR3 & (L3 & L4 & L26 & L27) & L20).
      replace (0x4e830%bv : word) with (Z_to_bv 64 0x4e830 : word) in RUN3 by (apply bv_eq; reflexivity).
      apply (katD_loadsX bt BT_ia fx2 st2 Lc FF M2 M02 mdl2 R2 r3 _ _ _ RP2 HH2 RUN3). intros mdl3 RP3 HH3 SBM3.
      apply katD_refl. exists fx2, st2, M2, mdl3, r3.
      split; [f_equal; f_equal; apply bv_eq; reflexivity|]. split; [| split; [exact KEPTS | exact (dr_keep_trans _ _ _ DK2 (conj L3 (conj L4 (conj L26 L27))))]].
      replace (length items0) with (Datatypes.S i) by lia.
      apply (ili_sbm fx2 st2 M2 mdl2 mdl3 R2 r3 (Datatypes.S i) INV2 SBM3 HH3); [| exact HR3 | exact L20 | exact L4].
      intros M0' RP'. pose proof RP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _) & _).
      pose proof RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & MI3 & _) & _). exact (Rep_sbm bt st2 Lc FF M0' mdl2 mdl3 RP' MI3 SBM3).
    - (* [comment removed for export] *)
      destruct (dr_item_next_more (mrestrict (HID st2 mdl2) M2) (seg_rom BSEGS) S (ba + 152 + 8 * Z.of_nat i) (Z.of_nat (length items0) + 16) (16 + Z.of_nat i) R2 HR2 E23 E24 E25
                  ltac:(clear - Hi Gcnt GB1 GB2 SB0 SB1 CR; lia) ltac:(clear - Hi Gcnt; lia) ltac:(clear - Hik; lia))
        as (r3 & RUN3 & HR3 & (L3 & L4 & L26 & L27) & (L23 & L24 & L25 & L20)).
      replace (0x4e830%bv : word) with (Z_to_bv 64 0x4e830 : word) in RUN3 by (apply bv_eq; reflexivity).
      apply (katD_loadsX bt BT_ia fx2 st2 Lc FF M2 M02 mdl2 R2 r3 _ _ _ RP2 HH2 RUN3). intros mdl3 RP3 HH3 SBM3.
      replace (0x4e824%bv : word) with (Z_to_bv 64 0x4e824 : word) by (apply bv_eq; reflexivity).
      eapply katD_conseq; [apply (IH (Datatypes.S i) fx2 st2 M2 mdl3 r3 ltac:(lia)) |].
      + apply (ili_sbm fx2 st2 M2 mdl2 mdl3 R2 r3 (Datatypes.S i) INV2 SBM3 HH3); [| exact HR3 | exact L20 | exact L4].
        intros M0' RP'. pose proof RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & MI3 & _) & _). exact (Rep_sbm bt st2 Lc FF M0' mdl2 mdl3 RP' MI3 SBM3).
      + (lazymatch goal with |- ?G => let G' := eval unfold cursor in G in change_no_check G' end). split; [rewrite L23; f_equal; clear; lia|]. split; [exact L24 | rewrite L25; f_equal; clear; lia].
      + intros c' (fx' & st' & M' & mdl' & R' & Ec & INV' & KEPT' & DK'). exists fx', st', M', mdl', R'.
        split; [exact Ec|]. split; [exact INV'|]. split; [intros a Ha; rewrite (KEPT' a Ha); exact (KEPTS a Ha)|].
        exact (dr_keep_trans _ _ _ DK2 (dr_keep_trans _ _ _ (conj L3 (conj L4 (conj L26 L27))) DK')).
  Qed.
End K4b.
End BoAllocFRcK4b.
Module BoAllocFRcK4c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD BoAllocFRc2 BoAllocFRc2U.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG BoAllocFRcL BoAllocFRcH BoAllocFRcK4a BoAllocFRcK4b.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section K4c.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis HITEM : rc_item_stmt bt FXOK arm_any.
  Hypothesis HBFREE : rc_bfree_stmt bt FXOK arm_any24.

  (* [comment removed for export] *)
  Variables (S : word) (X : Z -> Prop) (Xd : Xdec X) (qt qg : Z) (Lc FF : list (Z * Z)).
  Variables (st0 : ast) (M00 : mem) (mdl0 : Model) (rest : list batch).
  Variables (ra_dr s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Hypothesis XQ : forall z, qhdr bt z -> X z.
  Hypothesis S16 : U S mod 16 = 0.
  Hypothesis Slo : CEIL + 3584 <= U S.
  Hypothesis Shi : U S + 16 <= PTRHI.
  Hypothesis Gqg : qg < 2 ^ 41.
  Hypothesis Hra : ret_ok ra_dr.
  Hypothesis QRK : rc_budget st0 Lc qt qg.                       (* [comment removed for export] *)

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition dr_frame (M : mem) : Prop :=
    rdn BSEGS M (at_ S (-2296)) 8 = Some (LE8 ra_dr) /\ rdn BSEGS M (at_ S (-2304)) 8 = Some (LE8 s0v) /\ rdn BSEGS M (at_ S (-2312)) 8 = Some (LE8 s1v)
    /\ rdn BSEGS M (at_ S (-2320)) 8 = Some (LE8 s2v) /\ rdn BSEGS M (at_ S (-2328)) 8 = Some (LE8 s3v) /\ rdn BSEGS M (at_ S (-2336)) 8 = Some (LE8 s4v)
    /\ rdn BSEGS M (at_ S (-2344)) 8 = Some (LE8 s5v) /\ rdn BSEGS M (at_ S (-2352)) 8 = Some (LE8 s6v) /\ rdn BSEGS M (at_ S (-2360)) 8 = Some (LE8 s7v)
    /\ rdn BSEGS M (at_ S (-2368)) 8 = Some (LE8 s8v) /\ rdn BSEGS M (at_ S (-2376)) 8 = Some (LE8 s9v)
    /\ rdn BSEGS M (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + T_PC))).

  (* [comment removed for export] *)
  Definition pend (M : mem) (pb : list batch) : Prop :=
    rep_batches bt M pb
    /\ rdn BSEGS M (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length pb))))
    /\ rdn BSEGS M (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 (match pb with [] => 0 | b :: _ => ba_addr b end)))
    /\ rdn BSEGS M (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes pb)))
    /\ (forall a : word, U S - 2288 <= U a < U S - 2256 -> M a <> None)
    /\ dr_frame M.

  Definition invb (fx : FPState) (st : ast) (M : mem) (mdl : Model) (R : bvmap 5 word) (pb : list batch) : Prop :=
    FXOK fx /\ m_halted mdl = None /\ BackingAlgebra.model_ivs_wf mdl
    /\ WFq bt st Lc FF qt qg /\ AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M mdl
    /\ a_gq st = pb ++ rest
    /\ (forall z, X z -> XB bt st z)
    /\ (forall a : word, qhdr bt (U a) -> M a <> None)
    /\ pend M pb
    /\ (forall a : word, U S - 3584 <= U a < U S - 2400 -> M a <> None /\ store_ok BSEGS M a 1%nat = true)
    /\ dr_regs S R /\ getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt))
    /\ rc_acc bt Lc FF S X st0 M00 mdl0 st M mdl.

  Lemma dr_frame_same : forall (M M' : mem), (forall a : word, U S - 2400 <= U a < U S - 2288 -> M' a = M a) -> dr_frame M -> dr_frame M'.
  Proof using Slo RC.
    intros M M' EQ (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold dr_frame in G in change_no_check G' end).
    repeat split; (eapply rd_same; [| clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | eassumption]);
      intros x Hx; apply EQ; clear - Hx HSr Slo CR; rewrite at_u in Hx by lia; cbn in Hx; lia.
  Qed.

  Lemma pend_same : forall (M M' : mem) pb,
    (forall b, In b pb -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP) ->
    (forall b (a : word), In b pb -> ba_addr b <= U a < ba_addr b + BATCHSZ -> M' a = M a) ->
    (forall a : word, U S - 2400 <= U a < U S - 2256 -> M' a = M a) ->
    pend M pb -> pend M' pb.
  Proof using Slo RC.
    intros M M' pb RNG OBJ STK (P1 & P2 & P3 & P4 & P5 & P6). pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold pend in G in change_no_check G' end). split; [exact (rep_batches_same bt M M' pb P1 RNG OBJ)|].
    split; [eapply rd_same; [| clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact P2]; intros x Hx; apply STK; clear - Hx HSr Slo CR; rewrite at_u in Hx by lia; cbn in Hx; lia|].
    split; [eapply rd_same; [| clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact P3]; intros x Hx; apply STK; clear - Hx HSr Slo CR; rewrite at_u in Hx by lia; cbn in Hx; lia|].
    split; [eapply rd_same; [| clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact P4]; intros x Hx; apply STK; clear - Hx HSr Slo CR; rewrite at_u in Hx by lia; cbn in Hx; lia|].
    split; [intros a Ha; rewrite (STK a ltac:(clear - Ha; lia)); exact (P5 a Ha)|].
    apply (dr_frame_same M M'); [intros a Ha; apply STK; clear - Ha; lia | exact P6].
  Qed.

  Lemma q_bytes_cons : forall b q, q_bytes (b :: q) = ba_bytes b + q_bytes q.
  Proof using. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma gq_sizes : forall st, WFq bt st Lc FF qt qg -> forall b m n, In b (a_gq st) -> In (m, n) (ba_items b) -> 0 <= n.
  Proof using S.
    intros st W b m n Hb Hin. destruct W as (_ & _ & (_ & QG & _) & _). rewrite Forall_forall in QG.
    destruct (QG b Hb) as (_ & _ & WI). destruct (WI m n Hin) as [Xn _]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition bhead_post (M : mem) (R : bvmap 5 word) (b : batch) (pb' : list batch) (c' : config) : Prop :=
    exists fx1 st1 (M1 : mem) mdl1 (R1 : bvmap 5 word),
      c' = mkCfg (@mkst fx1 R1 (Z_to_bv 64 (match ba_items b with [] => 0x4e83c | _ => 0x4e824 end)) M1 (seg_rom BSEGS)) mdl1
      /\ ili bt FXOK S X qt qg Lc FF st0 M00 mdl0 (ba_addr b) (ba_items b) (pb' ++ rest) fx1 st1 M1 mdl1 R1 0
      /\ (ba_items b <> [] -> cursor (ba_addr b) (ba_items b) R1 0)
      /\ pend M1 pb' /\ dr_keep R R1 /\ (forall a : word, U S - 2256 <= U a -> M1 a = M a).

  Lemma bhead_step : forall fx st (M : mem) mdl (R : bvmap 5 word) b pb',
    invb fx st M mdl R (b :: pb') -> getr R 10 = Z_to_bv 64 (Z.of_nat (length (b :: pb'))) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e7e4) M (seg_rom BSEGS)) mdl) (bhead_post M R b pb').
  Proof using Gqg Shi Slo BT_ia BT_segs.
    intros fx st M mdl R b pb' INV H10.
    destruct INV as (HFX & HH & MW & W & RX & EGQ & XSUB & QDEF & PEND & SOK & HR & R4 & ACC).
    destruct PEND as (RB & Psz & Pfirst & Pby & Pdef & FRM).
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr. unfold PTRHI in *.
    assert (Hb : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    destruct (batch_facts bt st Lc FF W _ Hb) as (_ & GBL & GB1 & GB2).
    pose proof (thread_dyn bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    pose proof (gq_sizes st W) as SZ.
    assert (QB : 8192 * Z.of_nat (length (b :: pb')) <= q_bytes (b :: pb') /\ q_bytes (b :: pb') <= qg /\ 8192 <= ba_bytes b /\ 0 <= q_bytes pb').
    { pose proof W as (_ & _ & (_ & _ & _ & QGB & _) & _). rewrite EGQ, q_bytes_app in QGB.
      pose proof (AsAinvOpsRc3.q_bytes_ge (b :: pb') ltac:(intros b0 m0 n0 Hb0 Hin0; apply (SZ b0 m0 n0); [rewrite EGQ; apply in_app_iff; left; exact Hb0 | exact Hin0])) as G1.
      pose proof (AsAinvOpsRc3.q_bytes_ge rest ltac:(intros b0 m0 n0 Hb0 Hin0; apply (SZ b0 m0 n0); [rewrite EGQ; apply in_app_iff; right; exact Hb0 | exact Hin0])) as G2.
      pose proof (AsAinvOpsRc3.q_bytes_ge pb' ltac:(intros b0 m0 n0 Hb0 Hin0; apply (SZ b0 m0 n0); [rewrite EGQ; apply in_app_iff; left; right; exact Hb0 | exact Hin0])) as G3.
      pose proof (AsAinvOpsRc3.ba_bytes_ge b ltac:(intros m0 n0 Hin0; apply (SZ b m0 n0); [rewrite EGQ; left; reflexivity | exact Hin0])) as G4.
      unfold BATCHSZ in *. clear - G1 G2 G3 G4 QGB. lia. }
    destruct QB as (QB1 & QB2 & QB3 & QB4).
    unfold KSPACE, PG, AS_HEAPLO, BATCHSZ, BATCHCAP in *.
    pose proof RX as (M0 & RP & DX).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _). destruct R14 as (B1 & B2 & _).
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). left. exact Hr. }
    assert (NHB : forall z, ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 GB1 GB2 CR; lia|].
      apply (rep_nolazy_batch bt st Lc FF M0 mdl W RP _ z Hb). (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). exact Hz. }
    destruct (RB 0%nat b eq_refl) as (C1 & C2 & C3 & C4 & CW). rewrite BT_segs in C1, C2, C3, C4. unfold cellZ, cellN in C1, C2, C3, C4.
    set (nx := match nth_error (b :: pb') 1 with Some b' => ba_addr b' | None => 0 end) in *.
    assert (Enx : nx = match pb' with [] => 0 | b' :: _ => ba_addr b' end) by ((lazymatch goal with |- ?G => let G' := eval unfold nx in G in change_no_check G' end); destruct pb'; reflexivity).
    assert (Hnx : 0 <= nx < 2 ^ 64).
    { rewrite Enx. destruct pb' as [|b' pb'']; [clear; lia|].
      assert (Hb' : In b' (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; right; left; reflexivity).
      destruct (batch_facts bt st Lc FF W _ Hb') as (_ & _ & GB1' & GB2'). unfold KSPACE, BATCHSZ in *. clear - GB1' GB2' SB0 SB1 CR. lia. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    Ltac stkK NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; apply hid_off_of; intros z Hz; split; [lia | apply NHs; lia] ].
    assert (K_first : rdn BSEGS memD (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr b)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Pfirst | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs; clear - Hz HSr Slo CR; lia]. }
    assert (K_tby : rdn BSEGS memD (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (b :: pb'))))).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Pby | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs; clear - Hz HSr Slo CR; lia]. }
    assert (OBJ : forall k, 0 <= k -> k + 8 <= 8192 -> forall bs, rdn BSEGS M (Z_to_bv 64 (ba_addr b + k)) 8 = Some bs -> rdn BSEGS memD (Z_to_bv 64 (ba_addr b + k)) 8 = Some bs).
    { intros k Hk1 Hk2 bs Hr. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | clear - Hk1 Hk2 GB1 GB2 SB0 SB1 CR; wd_ulia_c |].
      rewrite u_Z2bv by (clear - Hk1 Hk2 GB1 GB2 SB0 SB1 CR; lia).
      apply hid_off_of. intros z Hz. split; [clear - Hz Hk1 Hk2 GB1 GB2 SB0 SB1 CR; cbn in Hz; lia | apply NHB; clear - Hz Hk1 Hk2; cbn in Hz; lia]. }
    assert (K_nx : rdn BSEGS memD (Z_to_bv 64 (ba_addr b)) 8 = Some (LE8 (Z_to_bv 64 nx))).
    { replace (ba_addr b) with (ba_addr b + 0) at 1 by (clear; lia). apply OBJ; [clear; lia | clear; lia |]. replace (ba_addr b + 0) with (ba_addr b) by (clear; lia). exact C1. }
    assert (K_bsz : rdn BSEGS memD (Z_to_bv 64 (ba_addr b + 8)) 8 = Some (LE8 (Z_to_bv 64 (ba_bytes b)))) by (apply OBJ; [clear; lia | clear; lia | exact C2]).
    assert (K_cnt : rdn BSEGS memD (Z_to_bv 64 (ba_addr b + 16)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (ba_items b)))))) by (apply OBJ; [clear; lia | clear; lia | exact C3]).
    assert (SOKtmp : store_ok BSEGS memD (at_ S (-2288)) 32 = true).
    { replace (at_ S (-2288)) with (Z_to_bv 64 (U S - 2288) : word) by (clear - HSr Slo CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (Pdef (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
      - apply NHs; clear - Hz HSr Slo CR; lia. }
    assert (P_HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_tsz : 1 <= Z.of_nat (length (b :: pb')) < 2 ^ 28) by (cbn [length] in *; clear - QB1 QB2 Gqg; lia).
    assert (P_tby : 0 <= ba_bytes b <= q_bytes (b :: pb') /\ q_bytes (b :: pb') < 2 ^ 42) by (rewrite q_bytes_cons in *; clear - QB2 QB3 QB4 Gqg; lia).
    assert (P_cnt : 0 <= Z.of_nat (length (ba_items b)) <= 1021) by (clear - GBL; lia).
    assert (P_b : AIMGHI <= ba_addr b /\ ba_addr b + 8192 <= U S - 3584) by (clear - GB1 GB2 SBH SB1 Slo; lia).
    (* [comment removed for export] *)
    assert (RUNX : exists rf, msteps BSEGS (mkst R (0x4e7e4%bv : word) memD (seg_rom BSEGS))
                     (mkst rf (Z_to_bv 64 (match ba_items b with [] => 0x4e83c | _ => 0x4e824 end))
                           (fr_drb memD S (Z.of_nat (length (b :: pb'))) (q_bytes (b :: pb')) (ba_bytes b) nx) (seg_rom BSEGS))
                   /\ dr_regs S rf /\ dr_keep R rf /\ getr rf 20 = Z_to_bv 64 (ba_addr b)
                   /\ (ba_items b <> [] -> cursor (ba_addr b) (ba_items b) rf 0)).
    { destruct (ba_items b) as [|it its] eqn:EIT.
      - destruct (dr_bhead_empty memD (seg_rom BSEGS) S (Z.of_nat (length (b :: pb'))) (q_bytes (b :: pb')) (ba_addr b) (ba_bytes b) nx 0 R HR H10 P_HS P_tsz P_tby Hnx
                    ltac:(clear; lia) P_b SOKtmp K_first K_tby K_nx K_bsz K_cnt eq_refl) as (rf & RUN & Q1 & Q2 & Q3).
        exists rf. split; [replace (Z_to_bv 64 0x4e83c) with (0x4e83c%bv : word) by (apply bv_eq; reflexivity); exact RUN|].
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. intros NE. exfalso. exact (NE eq_refl).
      - cbn [length] in K_cnt, P_cnt.
        destruct (dr_bhead_items memD (seg_rom BSEGS) S (Z.of_nat (length (b :: pb'))) (q_bytes (b :: pb')) (ba_addr b) (ba_bytes b) nx _ R HR H10 P_HS P_tsz P_tby Hnx
                    P_cnt P_b SOKtmp K_first K_tby K_nx K_bsz K_cnt ltac:(clear; lia)) as (rf & RUN & Q1 & Q2 & Q3 & Q23 & Q24 & Q25).
        exists rf. split; [replace (Z_to_bv 64 0x4e824) with (0x4e824%bv : word) by (apply bv_eq; reflexivity); exact RUN|].
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. intros _. (lazymatch goal with |- ?G => let G' := eval unfold cursor in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end).
        split; [rewrite Q23; f_equal; clear; lia|]. split; [rewrite Q24; f_equal; clear; lia | rewrite Q25; f_equal; clear; lia]. }
    destruct RUNX as (rf & RUN & HRf & DKf & F20 & CURf).
    replace (0x4e7e4%bv : word) with (Z_to_bv 64 0x4e7e4 : word) in RUN by (apply bv_eq; reflexivity).
    remember (fr_drb memD S (Z.of_nat (length (b :: pb'))) (q_bytes (b :: pb')) (ba_bytes b) nx) as MF eqn:EMF.
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4e7e4) M (seg_rom BSEGS)) (@mkst fx rf (Z_to_bv 64 (match ba_items b with [] => 0x4e83c | _ => 0x4e824 end)) MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4e7e4) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (OUT1 : forall a : word, (U a < U S - 2288 \/ U S - 2256 <= U a) -> M1 a = M a).
    { intros a Ha. destruct (Hd a) eqn:Eh; [exact (HIDv a Eh)|]. rewrite (VIS a Eh), EMF, (fr_drb_outside memD S _ _ _ _ P_HS a Ha). exact (MrM a Eh). }
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh), EMF]. apply fr_drb_grows. rewrite (MrM a Eh). exact Ha. }
    assert (CH1 : forall a : word, M1 a <> M a -> (U S - 2288 <= U a < U S - 2256) /\ M1 a <> None).
    { intros a NE. split.
      - destruct (Z_lt_dec (U a) (U S - 2288)) as [L|L]; [exfalso; apply NE; apply OUT1; left; exact L|].
        destruct (Z_le_dec (U S - 2256) (U a)) as [G|G]; [exfalso; apply NE; apply OUT1; right; exact G|]. clear - L G. lia.
      - intros E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    assert (STKV : forall k v, -2288 <= k -> k + 8 <= -2256 -> rdn BSEGS MF (at_ S k) 8 = Some v -> rdn BSEGS M1 (at_ S k) 8 = Some v).
    { intros k v Hk1 Hk2 Hr. eapply rd_same; [| clear - Hk1 Hk2 HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range | clear - Hx Hk1 Hk2 HSr Slo CR; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (RX1 : AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M1 mdl1).
    { apply (RepX_stack bt X st Lc FF M M1 mdl1 W); [exists M0; split; [exact (Rep_sbm bt st Lc FF M0 mdl mdl1 RP MI1 SBM1) | exact DX]|].
      intros a NE. destruct (CH1 a NE) as [Rg D]. split; [clear - Rg Slo; lia | exact D]. }
    assert (ACC1 : rc_acc bt Lc FF S X st0 M00 mdl0 st M1 mdl1).
    { eapply rc_acc_trans; [exact (rc_acc_sbm bt Lc FF S X _ _ _ _ _ _ _ ACC SBM1)|].
      apply (rc_acc_stack bt Lc FF S X st M mdl1 M1 W XSUB Slo). intros a NE. destruct (CH1 a NE) as [Rg D]. split; [clear - Rg; lia | exact D]. }
    assert (RNGpb : forall b0, In b0 (b :: pb') -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. assert (Hb0' : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; apply in_app_iff; left; exact Hb0).
      destruct (batch_facts bt st Lc FF W _ Hb0') as (_ & L0 & G01 & G02). unfold KSPACE, BATCHSZ, BATCHCAP in *. clear - L0 G01 G02 SB0 SB1 CR. lia. }
    assert (OBJ1 : forall b0 (a : word), In b0 (b :: pb') -> ba_addr b0 <= U a < ba_addr b0 + BATCHSZ -> M1 a = M a).
    { intros b0 a Hb0 Ha. apply OUT1. left.
      assert (Hb0' : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; apply in_app_iff; left; exact Hb0).
      destruct (batch_facts bt st Lc FF W _ Hb0') as (_ & _ & G01 & G02). unfold KSPACE, BATCHSZ in *. clear - Ha G01 G02 SB1 Slo. lia. }
    assert (RB1 : rep_batches bt M1 (b :: pb')) by exact (rep_batches_same bt M M1 _ RB RNGpb OBJ1).
    apply katD_refl. exists fx, st, M1, mdl1, rf. split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold ili in G in change_no_check G' end). split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|]. split; [exact W|].
      split; [exact RX1|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end); rewrite EGQ; destruct b; reflexivity|]. split; [exact XSUB|].
      split; [intros a Ha; apply GR1; exact (QDEF a Ha)|].
      split.
      { intros j mn Hj. destruct (RB1 0%nat b eq_refl) as (_ & _ & _ & D4 & _). specialize (D4 j mn Hj). rewrite BT_segs in D4. exact D4. }
      split; [destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11); eapply rd_same; [| clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact F11];
              intros x Hx; apply OUT1; left; clear - Hx HSr Slo CR; rewrite at_u in Hx by lia; cbn in Hx; lia|].
      split.
      { intros a Ha. rewrite (OUT1 a ltac:(left; clear - Ha; lia)). destruct (SOK a Ha) as [D1 D2]. split; [exact D1|].
        apply store_ok1_defK. rewrite (OUT1 a ltac:(left; clear - Ha; lia)). exact D1. }
      split; [exact HRf|]. split; [exact F20|]. split; [destruct DKf as (_ & K4 & _); rewrite K4; exact R4 | exact ACC1]. }
    split; [exact CURf|].
    split.
    { (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold pend in G in change_no_check G' end). split; [exact (rep_batches_tail bt M1 b pb' RB1)|].
      split; [replace (Z.of_nat (length pb')) with (Z.of_nat (length (b :: pb')) - 1) by ((lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia);
              apply STKV; [clear; lia | clear; lia | rewrite EMF; apply fr_drb_size; exact P_HS]|].
      split; [rewrite <- Enx; apply STKV; [clear; lia | clear; lia | rewrite EMF; apply fr_drb_first; exact P_HS]|].
      split; [replace (q_bytes pb') with (q_bytes (b :: pb') - ba_bytes b) by (rewrite q_bytes_cons; clear; lia);
              apply STKV; [clear; lia | clear; lia | rewrite EMF; apply fr_drb_bytes; exact P_HS]|].
      split; [intros a Ha; apply GR1; exact (Pdef a Ha)|].
      apply (dr_frame_same M M1); [intros a Ha; apply OUT1; left; clear - Ha; lia | exact FRM]. }
    split; [exact DKf|]. intros a Ha. apply OUT1. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition bfree_post (M : mem) (R : bvmap 5 word) (pb' : list batch) (c' : config) : Prop :=
    exists fx2 st2 (M2 : mem) mdl2 (R2 : bvmap 5 word),
      c' = mkCfg (@mkst fx2 R2 (Z_to_bv 64 0x4e868) M2 (seg_rom BSEGS)) mdl2
      /\ invb fx2 st2 M2 mdl2 R2 pb' /\ dr_keep R R2 /\ (forall a : word, U S - 2256 <= U a -> M2 a = M a).

  Lemma skipn_all_nil : forall {A} (l : list A), skipn (length l) l = [].
  Proof using. intros A l. induction l as [|x l IH]; [reflexivity | exact IH]. Qed.

  Lemma bfree_step : forall fx st (M : mem) mdl (R : bvmap 5 word) ba items0 pb',
    ili bt FXOK S X qt qg Lc FF st0 M00 mdl0 ba items0 (pb' ++ rest) fx st M mdl R (length items0) -> pend M pb' ->
    (forall z, ba <= z < ba + BATCHSZ -> X z) -> (forall b z, In b pb' -> ba_addr b <= z < ba_addr b + BATCHSZ -> X z) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e83c) M (seg_rom BSEGS)) mdl) (bfree_post M R pb').
  Proof using QRK Shi Slo S16 XQ Xd HBFREE CELLNB BT_ia BT_segs.
    intros fx st M mdl R ba items0 pb' INV PEND XOBJ XPB.
    destruct INV as (HFX & HH & MW & W & RX & EGQ & XSUB & QDEF & ITEMS & CCB & SOK & HR & R20 & R4 & ACC).
    rewrite skipn_all_nil in EGQ.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr. unfold PTRHI in *. unfold free_cells_nb in CELLNB.
    assert (Hb : In (BATCH ba []) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    destruct (batch_facts bt st Lc FF W _ Hb) as (CV & _ & GB1 & GB2). cbn [ba_addr] in CV, GB1, GB2.
    assert (Hc : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W BATCHCLASS Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & _).
    pose proof (thread_dyn bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    destruct CV as (j & Hj0 & Hj1 & Eab). change (csize BATCHCLASS) with 8192 in Hj1, Eab.
    unfold IB in CELLNB. rewrite BT_ia in CELLNB. cbn [ia_instance both_addrs] in CELLNB.
    unfold chunk_addr, fa_beg, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, BATCHSZ, BATCHCLASS in *.
    change (csize 24) with 8192 in *.
    assert (Hd32 : 0 <= j * 8192 < 2 ^ 32 /\ ba = SBEG + 24 * 2 ^ 32 + j * 8192) by (clear - Hj0 Hj1 Q3 Q2 Eab; lia).
    pose proof RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    pose proof RP as (Rc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _). rewrite BT_segs in Rc.
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (K_spb : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELLNB) EQ0); [vm_compute; discriminate | vm_compute; reflexivity |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia].
      - apply NHs; [clear - Hz; lia | right; clear - Hz; lia]. }
    assert (K_cache : rdn BSEGS (mrestrict Hd M) (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + T_PC)))).
    { rewrite rdn_mrestrict; [exact CCB | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]]. }
    destruct (dr_bfree_call (mrestrict Hd M) (seg_rom BSEGS) S (Z_to_bv 64 (T + T_PC)) SBEG ba (j * 8192) R HR R20
                ltac:(clear - SB0 SB1 CR; lia) ltac:(clear - Hd32; lia) K_spb K_cache)
      as (r1 & RUN1 & HR1 & (K3 & K4 & K26 & K27) & C20 & C1 & C10 & C11 & C12 & C13).
    replace (0x4e83c%bv : word) with (Z_to_bv 64 0x4e83c : word) in RUN1 by (apply bv_eq; reflexivity).
    apply (katD_loadsX bt BT_ia fx st Lc FF M M0 mdl R r1 _ _ _ RP HH RUN1). intros mdl1 RP1 HH1 SBM1.
    replace (0x4eca8%bv : word) with (Z_to_bv 64 0x4eca8 : word) by (apply bv_eq; reflexivity).
    pose proof HR1 as (D2 & D8 & D9 & D21 & D18 & D19).
    apply (katD_bind BSEGS _ (rc_step_post bt FXOK X qt qg st Lc FF M mdl1 r1 S (Z_to_bv 64 0x4e868) (pb' ++ rest))).
    { apply (HBFREE fx X Xd qt qg st Lc FF M mdl1 r1 S (Z_to_bv 64 0x4e868) ba (pb' ++ rest) HFX HH1 (model_ivs_wf_sbm mdl mdl1 SBM1 MW) W
               (ex_intro _ M0 (conj RP1 DX)) EGQ I XSUB XQ).
      - intros z Hz. apply XOBJ. exact Hz.
      - exact QDEF.
      - exact C1.
      - apply ret_ok_lit; [clear; lia | reflexivity].
      - exact D2.
      - exact C10.
      - (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. exact C11.
      - exact C12.
      - exact C13.
      - rewrite K4. exact R4.
      - exact S16.
      - exact Slo.
      - (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). exact Shi.
      - exact SOK.
      - split; [exact (proj1 QRK) | rewrite (proj1 (proj2 ACC)); exact (proj2 QRK)]. }
    intros c2 POST2.
    destruct POST2 as (fx2 & st2 & M2 & mdl2 & R2 & -> & HFX2 & HH2 & MW2 & W2 & RX2 & EGQ2 & ETQ2 & EKA2 & HO2 & XSUB2 & KEPT2 & CH2 & LZ2 & SEV2 & RK2).
    apply katD_refl. exists fx2, st2, M2, mdl2, R2. split; [reflexivity|].
    split; [| split].
    - (lazymatch goal with |- ?G => let G' := eval unfold invb in G in change_no_check G' end). split; [exact HFX2|]. split; [exact HH2|]. split; [exact MW2|]. split; [exact W2|]. split; [exact RX2|]. split; [exact EGQ2|].
      split; [exact XSUB2|]. split; [intros a Ha; rewrite (KEPT2 a (or_introl (XQ _ Ha))); exact (QDEF a Ha)|].
      split.
      { apply (pend_same M M2 pb'); [| | | exact PEND].
        - intros b0 Hb0. assert (Hb0' : In b0 (a_tq st2 ++ a_gq st2)) by (apply in_app_iff; right; rewrite EGQ2; apply in_app_iff; left; exact Hb0).
          destruct (batch_facts bt st2 Lc FF W2 _ Hb0') as (_ & L0 & G01 & G02).
          pose proof (thread_dyn bt st2 Lc FF W2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0' & SB1' & _ & _).
          unfold KSPACE, PG, BATCHSZ, BATCHCAP in *. clear - L0 G01 G02 SB0' SB1' CR. lia.
        - intros b0 a Hb0 Ha. apply KEPT2. left. exact (XPB b0 _ Hb0 Ha).
        - intros a Ha. apply KEPT2. right. clear - Ha. lia. }
      split.
      { intros a Ha. assert (D : M2 a <> None).
        { destruct (decide (M2 a = M a)) as [E | N]; [rewrite E; exact (proj1 (SOK a Ha))|].
          destruct (proj2 (CH2 a N)) as [D | (LT & _)]; [exact D | exfalso; clear - LT Ha Slo; lia]. }
        exact (conj D (store_ok1_defK M2 a D)). }
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold dr_regs in G in change_no_check G' end). rewrite (regs_kept_litK r1 R2 2 RK2 eq_refl), (regs_kept_litK r1 R2 8 RK2 eq_refl), (regs_kept_litK r1 R2 9 RK2 eq_refl),
          (regs_kept_litK r1 R2 21 RK2 eq_refl), (regs_kept_litK r1 R2 18 RK2 eq_refl), (regs_kept_litK r1 R2 19 RK2 eq_refl). exact HR1. }
      split; [rewrite (regs_kept_litK r1 R2 4 RK2 eq_refl), K4; exact R4|].
      eapply rc_acc_trans; [exact (rc_acc_sbm bt Lc FF S X _ _ _ _ _ _ _ ACC SBM1) | exact (rc_acc_step bt Lc FF S X st M mdl1 st2 M2 mdl2 ETQ2 EKA2 HO2 KEPT2 CH2 LZ2 SEV2)].
    - (lazymatch goal with |- ?G => let G' := eval unfold dr_keep in G in change_no_check G' end). rewrite (regs_kept_litK r1 R2 3 RK2 eq_refl), (regs_kept_litK r1 R2 4 RK2 eq_refl), (regs_kept_litK r1 R2 26 RK2 eq_refl), (regs_kept_litK r1 R2 27 RK2 eq_refl).
      exact (conj K3 (conj K4 (conj K26 K27))).
    - intros a Ha. apply KEPT2. right. clear - Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Definition dr_done_post (M : mem) (R : bvmap 5 word) (c' : config) : Prop :=
    exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word),
      c' = mkCfg (@mkst fx' R' ra_dr M' (seg_rom BSEGS)) mdl'
      /\ FXOK fx' /\ m_halted mdl' = None /\ BackingAlgebra.model_ivs_wf mdl'
      /\ WFq bt st' Lc FF qt qg /\ AsAinvOpsRc73.AsAinvRepX3.RepX bt X st' Lc FF M' mdl'
      /\ a_gq st' = rest /\ (forall z, X z -> XB bt st' z) /\ (forall a : word, qhdr bt (U a) -> M' a <> None)
      /\ rc_acc bt Lc FF S X st0 M00 mdl0 st' M' mdl'
      /\ (getr R' 2 = at_ S (-2288) /\ getr R' 8 = s0v /\ getr R' 9 = s1v /\ getr R' 18 = s2v /\ getr R' 19 = s3v /\ getr R' 20 = s4v
          /\ getr R' 21 = s5v /\ getr R' 22 = s6v /\ getr R' 23 = s7v /\ getr R' 24 = s8v /\ getr R' 25 = s9v)
      /\ dr_keep R R' /\ (forall a : word, U S - 2256 <= U a -> M' a = M a).

  (* [comment removed for export] *)
  Lemma bnext_regs : forall fx st (M : mem) mdl (R : bvmap 5 word) pb, invb fx st M mdl R pb ->
    rdn BSEGS (mrestrict (HID st mdl) M) (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length pb))))
    /\ (forall k v, -2400 <= k -> k + 8 <= -2288 -> rdn BSEGS M (at_ S k) 8 = Some v -> rdn BSEGS (mrestrict (HID st mdl) M) (at_ S k) 8 = Some v).
  Proof using Slo.
    intros fx st M mdl R pb (_ & _ & _ & _ & (M0 & RP & _) & _ & _ & _ & (_ & Psz & _) & _).
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> HID st mdl (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). left. exact Hr. }
    split.
    - rewrite rdn_mrestrict; [exact Psz | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs; clear - Hz HSr Slo CR; lia].
    - intros k v Hk1 Hk2 Hr. rewrite rdn_mrestrict; [exact Hr | clear - Hk1 Hk2 HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - Hk1 Hk2 HSr Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz Hk1 Hk2 HSr Slo CR; lia | apply NHs; clear - Hz Hk1 Hk2 HSr Slo CR; lia].
  Qed.

  Theorem rc_batch_loop : forall pb fx st (M : mem) mdl (R : bvmap 5 word),
    pb <> [] -> invb fx st M mdl R pb -> getr R 10 = Z_to_bv 64 (Z.of_nat (length pb)) ->
    (forall b z, In b pb -> ba_addr b <= z < ba_addr b + BATCHSZ -> X z) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e7e4) M (seg_rom BSEGS)) mdl) (dr_done_post M R).
  Proof using QRK Hra Gqg Shi Slo S16 XQ Xd HBFREE HITEM CELLNB BT_ia BT_segs.
    induction pb as [|b pb' IH]; intros fx st M mdl R NE INV H10 XPB; [exfalso; exact (NE eq_refl)|].
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    apply (katD_bind BSEGS _ _ _ (bhead_step fx st M mdl R b pb' INV H10)).
    intros c1 (fx1 & st1 & M1 & mdl1 & R1 & -> & ILI1 & CUR1 & PEND1 & DK1 & KEPT1).
    assert (XOBJb : forall z, ba_addr b <= z < ba_addr b + BATCHSZ -> X z) by (intros z Hz; exact (XPB b z (or_introl eq_refl) Hz)).
    assert (XPB' : forall b0 z, In b0 pb' -> ba_addr b0 <= z < ba_addr b0 + BATCHSZ -> X z) by (intros b0 z Hb0 Hz; exact (XPB b0 z (or_intror Hb0) Hz)).
    (* [comment removed for export] *)
    assert (ATFREE : katD BSEGS (mkCfg (@mkst fx1 R1 (Z_to_bv 64 (match ba_items b with [] => 0x4e83c | _ => 0x4e824 end)) M1 (seg_rom BSEGS)) mdl1)
                       (fun c' => exists fx2 st2 (M2 : mem) mdl2 (R2 : bvmap 5 word),
                          c' = mkCfg (@mkst fx2 R2 (Z_to_bv 64 0x4e83c) M2 (seg_rom BSEGS)) mdl2
                          /\ ili bt FXOK S X qt qg Lc FF st0 M00 mdl0 (ba_addr b) (ba_items b) (pb' ++ rest) fx2 st2 M2 mdl2 R2 (length (ba_items b))
                          /\ pend M2 pb' /\ dr_keep R1 R2 /\ (forall a : word, U S - 2400 <= U a -> M2 a = M1 a))).
    { destruct (ba_items b) as [|it its] eqn:EIT.
      - apply katD_refl. exists fx1, st1, M1, mdl1, R1. split; [reflexivity|]. split; [exact ILI1|]. split; [exact PEND1|].
        split; [(lazymatch goal with |- ?G => let G' := eval unfold dr_keep in G in change_no_check G' end); repeat split; reflexivity | intros a _; reflexivity].
      - pose proof ILI1 as (_ & _ & _ & W1 & _ & EGQ1 & _ & _ & _ & _ & _ & _ & _ & _ & ACC1).
        assert (Hb1 : In (BATCH (ba_addr b) (skipn 0 (it :: its))) (a_tq st1 ++ a_gq st1)) by (apply in_app_iff; right; rewrite EGQ1; left; reflexivity).
        destruct (batch_facts bt st1 Lc FF W1 _ Hb1) as (_ & GBL & _). cbn [ba_items skipn] in GBL.
        eapply katD_conseq; [apply (rc_item_loop bt FXOK BT_ia HITEM S X Xd qt qg Lc FF st0 M00 mdl0 (ba_addr b) (it :: its) (pb' ++ rest) XQ XOBJb S16 Slo Shi
                                     ltac:(clear - GBL; lia) QRK (length its) 0%nat fx1 st1 M1 mdl1 R1 eq_refl ILI1 (CUR1 ltac:(discriminate)))|].
        intros c2 (fx2 & st2 & M2 & mdl2 & R2 & Ec & ILI2 & KEPT2 & DK2). exists fx2, st2, M2, mdl2, R2.
        split; [exact Ec|]. split; [exact ILI2|]. split; [| exact (conj DK2 KEPT2)].
        pose proof ILI2 as (_ & _ & _ & W2 & _ & EGQ2 & _ & _ & _ & _ & _ & _ & _ & _ & ACC2).
        apply (pend_same M1 M2 pb'); [| | | exact PEND1].
        + intros b0 Hb0. assert (Hb0' : In b0 (a_tq st2 ++ a_gq st2)) by (apply in_app_iff; right; rewrite EGQ2; right; apply in_app_iff; left; exact Hb0).
          destruct (batch_facts bt st2 Lc FF W2 _ Hb0') as (_ & L0 & G01 & G02).
          pose proof (thread_dyn bt st2 Lc FF W2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0' & SB1' & _ & _).
          unfold KSPACE, PG, BATCHSZ, BATCHCAP in *. clear - L0 G01 G02 SB0' SB1' CR. lia.
        + intros b0 a Hb0 Ha. destruct ACC1 as (_ & _ & _ & XK1 & _). destruct ACC2 as (_ & _ & _ & XK2 & _).
          rewrite (XK2 a (XPB' b0 _ Hb0 Ha)), (XK1 a (XPB' b0 _ Hb0 Ha)). reflexivity.
        + intros a Ha. apply KEPT2. clear - Ha. lia. }
    apply (katD_bind BSEGS _ _ _ ATFREE). clear ATFREE.
    intros c2 (fx2 & st2 & M2 & mdl2 & R2 & -> & ILI2 & PEND2 & DK2 & KEPT2).
    apply (katD_bind BSEGS _ _ _ (bfree_step fx2 st2 M2 mdl2 R2 (ba_addr b) (ba_items b) pb' ILI2 PEND2 XOBJb XPB')).
    intros c3 (fx3 & st3 & M3 & mdl3 & R3 & -> & INV3 & DK3 & KEPT3).
    assert (DK13 : dr_keep R R3) by exact (dr_keep_trans _ _ _ DK1 (dr_keep_trans _ _ _ DK2 DK3)).
    assert (KEPT13 : forall a : word, U S - 2256 <= U a -> M3 a = M a).
    { intros a Ha. rewrite (KEPT3 a Ha), (KEPT2 a ltac:(clear - Ha; lia)). exact (KEPT1 a Ha). }
    destruct (bnext_regs fx3 st3 M3 mdl3 R3 pb' INV3) as [K_sz STK3].
    pose proof INV3 as (HFX3 & HH3 & MW3 & W3 & (M03 & RP3 & DX3) & EGQ3 & XSUB3 & QDEF3 & PEND3 & SOK3 & HR3 & R43 & ACC3).
    assert (P_HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (unfold PTRHI in Shi; clear - Slo Shi CR; lia).
    assert (LEN : 0 <= Z.of_nat (length pb') < 2 ^ 64).
    { pose proof W3 as (_ & _ & (_ & _ & _ & QGB & _) & _).
      pose proof (AsAinvOpsRc3.q_bytes_ge (a_gq st3) ltac:(intros b0 m0 n0 Hb0 Hin0; exact (gq_sizes st3 W3 b0 m0 n0 Hb0 Hin0))) as G1.
      rewrite EGQ3, length_app in G1. rewrite EGQ3 in QGB. unfold BATCHSZ in G1. clear - G1 QGB Gqg. lia. }
    destruct pb' as [|b' pb''].
    - (* [comment removed for export] *)
      destruct PEND3 as (_ & _ & _ & _ & _ & (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11)).
      destruct (dr_bnext_done (mrestrict (HID st3 mdl3) M3) (seg_rom BSEGS) S ra_dr s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v 0 R3 HR3 K_sz ltac:(clear; lia) Hra
                  (STK3 (-2296) _ ltac:(clear; lia) ltac:(clear; lia) F0) (STK3 (-2304) _ ltac:(clear; lia) ltac:(clear; lia) F1) (STK3 (-2312) _ ltac:(clear; lia) ltac:(clear; lia) F2)
                  (STK3 (-2320) _ ltac:(clear; lia) ltac:(clear; lia) F3) (STK3 (-2328) _ ltac:(clear; lia) ltac:(clear; lia) F4) (STK3 (-2336) _ ltac:(clear; lia) ltac:(clear; lia) F5)
                  (STK3 (-2344) _ ltac:(clear; lia) ltac:(clear; lia) F6) (STK3 (-2352) _ ltac:(clear; lia) ltac:(clear; lia) F7) (STK3 (-2360) _ ltac:(clear; lia) ltac:(clear; lia) F8)
                  (STK3 (-2368) _ ltac:(clear; lia) ltac:(clear; lia) F9) (STK3 (-2376) _ ltac:(clear; lia) ltac:(clear; lia) F10) eq_refl)
        as (r4 & RUN4 & Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & DK4).
      replace (0x4e868%bv : word) with (Z_to_bv 64 0x4e868 : word) in RUN4 by (apply bv_eq; reflexivity).
      apply (katD_loadsX bt BT_ia fx3 st3 Lc FF M3 M03 mdl3 R3 r4 _ _ _ RP3 HH3 RUN4). intros mdl4 RP4 HH4 SBM4.
      apply katD_refl. exists fx3, st3, M3, mdl4, r4.
      split; [reflexivity|]. split; [exact HFX3|]. split; [exact HH4|]. split; [exact (model_ivs_wf_sbm mdl3 mdl4 SBM4 MW3)|]. split; [exact W3|].
      split; [exists M03; split; [exact RP4 | exact DX3]|]. split; [exact EGQ3|]. split; [exact XSUB3|]. split; [exact QDEF3|].
      split; [exact (rc_acc_sbm bt Lc FF S X _ _ _ _ _ _ _ ACC3 SBM4)|].
      split; [repeat split; assumption|]. split; [exact (dr_keep_trans _ _ _ DK13 DK4) | exact KEPT13].
    - (* [comment removed for export] *)
      destruct (dr_bnext_more (mrestrict (HID st3 mdl3) M3) (seg_rom BSEGS) S (Z.of_nat (length (b' :: pb''))) R3 HR3 K_sz LEN ltac:((lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia))
        as (r4 & RUN4 & HR4 & DK4 & Y10).
      replace (0x4e868%bv : word) with (Z_to_bv 64 0x4e868 : word) in RUN4 by (apply bv_eq; reflexivity).
      apply (katD_loadsX bt BT_ia fx3 st3 Lc FF M3 M03 mdl3 R3 r4 _ _ _ RP3 HH3 RUN4). intros mdl4 RP4 HH4 SBM4.
      replace (0x4e7e4%bv : word) with (Z_to_bv 64 0x4e7e4 : word) by (apply bv_eq; reflexivity).
      eapply katD_conseq; [apply (IH fx3 st3 M3 mdl4 r4 ltac:(discriminate)); [| exact Y10 | exact XPB']|].
      + (lazymatch goal with |- ?G => let G' := eval unfold invb in G in change_no_check G' end). split; [exact HFX3|]. split; [exact HH4|]. split; [exact (model_ivs_wf_sbm mdl3 mdl4 SBM4 MW3)|]. split; [exact W3|].
        split; [exists M03; split; [exact RP4 | exact DX3]|]. split; [exact EGQ3|]. split; [exact XSUB3|]. split; [exact QDEF3|].
        split; [exact PEND3|]. split; [exact SOK3|]. split; [exact HR4|]. split; [destruct DK4 as (_ & K4 & _); rewrite K4; exact R43|].
        exact (rc_acc_sbm bt Lc FF S X _ _ _ _ _ _ _ ACC3 SBM4).
      + intros c' (fx' & st' & M' & mdl' & R' & Ec & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & DK' & KEPT').
        exists fx', st', M', mdl', R'. split; [exact Ec|]. repeat (split; [assumption|]).
        split; [exact (dr_keep_trans _ _ _ DK13 (dr_keep_trans _ _ _ DK4 DK')) | intros a Ha; rewrite (KEPT' a Ha); exact (KEPT13 a Ha)].
  Qed.
End K4c.
End BoAllocFRcK4c.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK6a.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 BoAllocFRcH.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition fa_room (st : ast) (c : Z) : Prop :=
  4 * (Z.of_nat (length (r_free (a_reg st c))) + cache_max c / 2) <= r_mapped_fa (a_reg st c).
Definition arm_full24_room (st : ast) : Prop := arm_full24 st /\ fa_room st BATCHCLASS.
Definition arm_full24_map (st : ast) : Prop := arm_full24 st /\ ~ fa_room st BATCHCLASS.
Definition arm_prim_full_room (st : ast) (m n : Z) : Prop := arm_prim_full st m n /\ fa_room st (blk_class n).
Definition arm_prim_full_map (st : ast) (m n : Z) : Prop := arm_prim_full st m n /\ ~ fa_room st (blk_class n).

(* [comment removed for export] *)
Definition rc_cells_full (bt : as_boot) : Prop :=
  In (0x10ab80, 4%nat, 0xffffffff) (bt_consts bt) /\ In (0x105ef8, 8%nat, 0x19dc60) (bt_consts bt) /\ In (0x19dc60, 8%nat, 0x1000) (bt_consts bt)
  /\ In (0x10468, 8%nat, 0xafffff00000fffff) (bt_consts bt).

Section K6A.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).

  Lemma rc_bfree_full_of_arms : forall FXOK,
    rc_bfree_stmt bt FXOK arm_full24_room -> rc_bfree_stmt bt FXOK arm_full24_map -> rc_bfree_stmt bt FXOK arm_full24.
  Proof using.
    intros FXOK H1 H2 fx X Xd qt qg st Lc FF M mdl R S ret ba rest A1 A2 A3 A4 A5 A6 A7.
    destruct (Z_le_gt_dec (4 * (Z.of_nat (length (r_free (a_reg st BATCHCLASS))) + cache_max BATCHCLASS / 2)) (r_mapped_fa (a_reg st BATCHCLASS))) as [L | G].
    - apply (H1 fx X Xd qt qg st Lc FF M mdl R S ret ba rest A1 A2 A3 A4 A5 A6). split; [exact A7 | exact L].
    - apply (H2 fx X Xd qt qg st Lc FF M mdl R S ret ba rest A1 A2 A3 A4 A5 A6). split; [exact A7 | (lazymatch goal with |- ?G => let G' := eval unfold fa_room in G in change_no_check G' end); lia].
  Qed.
  Lemma rc_item_full_of_arms : forall FXOK,
    rc_item_stmt bt FXOK arm_prim_full_room -> rc_item_stmt bt FXOK arm_prim_full_map -> rc_item_stmt bt FXOK arm_prim_full.
  Proof using.
    intros FXOK H1 H2 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest A1 A2 A3 A4 A5 A6 A7.
    destruct (Z_le_gt_dec (4 * (Z.of_nat (length (r_free (a_reg st (blk_class n)))) + cache_max (blk_class n) / 2)) (r_mapped_fa (a_reg st (blk_class n)))) as [L | G].
    - apply (H1 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest A1 A2 A3 A4 A5 A6). split; [exact A7 | exact L].
    - apply (H2 fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest A1 A2 A3 A4 A5 A6). split; [exact A7 | (lazymatch goal with |- ?G => let G' := eval unfold fa_room in G in change_no_check G' end); lia].
  Qed.

  (* [comment removed for export] *)
  Definition Fdr (st : ast) (c m : Z) (z : Z) : Prop :=
    (reginfo bt c <= z < reginfo bt c + 8) \/ (reginfo bt c + 16 <= z < reginfo bt c + 24) \/ (reginfo bt c + 72 <= z < reginfo bt c + 128)
    \/ (fa_beg SBEG c + 4 * Z.of_nat (length (r_free (a_reg st c))) <= z < fa_beg SBEG c + 4 * (Z.of_nat (length (r_free (a_reg st c))) + m)).
  Definition Fdr_dec (st : ast) (c m : Z) : Xdec (Fdr st c m).
  Proof. (lazymatch goal with |- ?G => let G' := eval unfold Fdr in G in change_no_check G' end). repeat apply Xdec_or; apply Xdec_iv. Defined.

  Definition mid_mem (st : ast) (c m : Z) (M M1 : mem) : mem :=
    put4 (fun a : word => if Fdr_dec st c m (U a) then M1 a else M a) (T + T_PC + PC_SZ * c) (Z.of_nat (length (a_cache st c)) - m).

  Lemma Fdr_foot : forall st c m z, Fdr st c m z -> foot_drain_top bt st c m z.
  Proof using. intros st c m z H. unfold Fdr in H. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top in G in change_no_check G' end). tauto. Qed.

  Section Mid.
    Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z) (c m : Z).
    Hypothesis W : WFq bt st Lc FF qt qg.
    Hypothesis Hc : 1 <= c <= 30.
    Hypothesis Hm0 : 0 <= m.
    Hypothesis Hfa : 4 * (Z.of_nat (length (r_free (a_reg st c))) + m) <= r_mapped_fa (a_reg st c).
    #[local] Abbreviation pc_ := (T + T_PC + PC_SZ * c).

    Lemma pc_geo : 0 <= pc_ /\ pc_ + 4 < 2 ^ 63 /\ forall z, pc_ <= z < pc_ + 4 -> ~ Fdr st c m z.
    Proof using W Hc Hm0 Hfa.
      pose proof ceil_rng as CR.
      pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0 & SB1 & _).
      pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
      pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
      unfold T_PC, PC_SZ, PG, KSPACE in *. split; [lia|]. split; [lia|].
      intros z Hz Hf. unfold Fdr in Hf. unfold reginfo, fa_beg, region_beg, KREGION, KFAOFF, KSPACE in *.
      assert (0 <= Z.of_nat (length (r_free (a_reg st c)))) by lia.
      destruct Hf as [F|[F|[F|F]]]; lia.
    Qed.

    Lemma mid_mem_diff : forall (M M1 : mem) (a : word), M1 a <> mid_mem st c m M M1 a ->
      (pc_ <= U a < pc_ + 4) \/ (M1 a <> M a /\ ~ Fdr st c m (U a)).
    Proof using W Hc Hm0 Hfa.
      intros M M1 a NE. destruct pc_geo as (P0 & P1 & _).
      destruct (decide (pc_ <= U a < pc_ + 4)) as [I|O]; [left; exact I | right].
      unfold mid_mem in NE. rewrite put4_out in NE by lia.
      destruct (Fdr_dec st c m (U a)) as [F|F]; [exfalso; apply NE; reflexivity|]. split; [exact NE | exact F].
    Qed.

    Theorem drain_mid : forall (X : Z -> Prop) (Xd : Xdec X) (M M1 : mem) mdl mdl1,
      RepX bt X st Lc FF M mdl -> m <= Z.of_nat (length (a_cache st c)) ->
      (forall z, X z -> XB bt st z) ->
      (forall a : word, Fdr st c m (U a) -> M1 a <> M a -> M1 a <> None) ->
      cellZ SG M1 (reginfo bt c) 8 0 ->
      cellZ SG M1 (reginfo bt c + 16) 8 (Z.of_nat (length (r_free (a_reg st c))) + m) ->
      (forall i k, nth_error (skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - m)) (a_cache st c)) i = Some k ->
                   cellZ SG M1 (fa_beg SBEG c + 4 * (Z.of_nat (length (r_free (a_reg st c))) + Z.of_nat i)) 4 k) ->
      same_but_materialized mdl mdl1 -> MInv (a_aa st) mdl1 ->
      RepX bt X (op_drain_top st c m) Lc FF (mid_mem st c m M M1) mdl1.
    Proof using W Hc Hm0 Hfa.
      intros X Xd M M1 mdl mdl1 RX Hm1 XSUB DEF CMU CNF CFA SBM MI. assert (Hm : 0 <= m <= Z.of_nat (length (a_cache st c))) by lia.
      destruct pc_geo as (P0 & P1 & PF).
      pose proof ceil_rng as CR.
      pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB0 & SB1 & _).
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
      set (nf := Z.of_nat (length (r_free (a_reg st c)))) in *.
      assert (NX : forall z, foot_drain_top bt st c m z -> ~ X z).
      { intros z Hf Hx. exact (foot_drain_top_not_XB bt st Lc FF qt qg c m z W Hc (proj1 Hm) Hfa Hf (XSUB z Hx)). }
      set (Ma := mid_mem st c m M M1).
      assert (MaF : forall a : word, Fdr st c m (U a) -> Ma a = M1 a).
      { intros a F. (lazymatch goal with |- ?G => let G' := eval unfold Ma, mid_mem in G in change_no_check G' end). destruct (decide (pc_ <= U a < pc_ + 4)) as [I|O]; [exfalso; exact (PF _ I F)|]. rewrite put4_out by lia. destruct (Fdr_dec st c m (U a)) as [_|N]; [reflexivity | contradiction]. }
      apply (RepX_mono bt (fun z => X z /\ ~ False) X); [intros z [Hz _]; exact Hz|].
      apply (RepX_lift bt X (fun _ => False) (foot_drain_top bt st c m) Xd Xdec_false st (op_drain_top st c m) Lc Lc FF FF M Ma mdl mdl1 RX).
      - intros a NE. destruct (decide (pc_ <= U a < pc_ + 4)) as [I|O].
        + split; [(lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top in G in change_no_check G' end); right; right; right; left; exact I | (lazymatch goal with |- ?G => let G' := eval unfold Ma, mid_mem in G in change_no_check G' end); apply put4_def; [exact P0 | lia | exact I]].
        + unfold Ma, mid_mem in *. rewrite put4_out in * by lia.
          destruct (Fdr_dec st c m (U a)) as [F|F]; [| exfalso; apply NE; reflexivity].
          split; [apply Fdr_foot; exact F | exact (DEF a F NE)].
      - intros z Hf Hx. exact (NX z Hf Hx).
      - intros z a [].
      - intros M0 M0' R0 D0 EQ'.
        assert (EQa : forall i, 0 <= i < 2 ^ 64 -> foot_drain_top bt st c m i -> M0' (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)).
        { intros i Hi Hf. apply EQ'. left. rewrite u64_lit by lia. exact (NX i Hf). }
        unfold reginfo, fa_beg, region_beg, KREGION, KFAOFF, KSPACE, PG in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, SB0, SB1.
        apply (OPS_REP_drain_top_pf bt st Lc FF M0 M0' mdl mdl1 c m qt qg W R0 Hc Hm Hfa).
        + intros a NE. destruct (D0 a NE) as [[F | []] D]. split; [exact F | exact D].
        + apply (cellZ_frame SG Ma); [| (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
          * apply (cellZ_frame SG M1); [exact CMU | (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
            intros i Hi. apply MaF. rewrite u64_lit by (unfold reginfo, KSPACE in Hi; lia). (lazymatch goal with |- ?G => let G' := eval unfold Fdr in G in change_no_check G' end). left. cbn in Hi. lia.
          * intros i Hi. apply EQa; [unfold reginfo, KSPACE in Hi; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top in G in change_no_check G' end). left. cbn in Hi. lia.
        + apply (cellZ_frame SG Ma); [| (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
          * apply (cellZ_frame SG M1); [exact CNF | (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
            intros i Hi. apply MaF. rewrite u64_lit by (unfold reginfo, KSPACE in Hi; lia). (lazymatch goal with |- ?G => let G' := eval unfold Fdr in G in change_no_check G' end). right; left. cbn in Hi. lia.
          * intros i Hi. apply EQa; [unfold reginfo, KSPACE in Hi; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top in G in change_no_check G' end). right; left. cbn in Hi. lia.
        + apply (cellZ_frame SG Ma); [| exact P0 | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
          * (lazymatch goal with |- ?G => let G' := eval unfold Ma, mid_mem in G in change_no_check G' end). apply put4_hit; [exact P0 | lia].
          * intros i Hi. apply EQa; [cbn in Hi; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top in G in change_no_check G' end). right; right; right; left. cbn in Hi. lia.
        + intros i k Hik.
          assert (Hi : Z.of_nat i < m).
          { pose proof (nth_error_Some (skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - m)) (a_cache st c)) i) as [HS _].
            rewrite Hik in HS. specialize (HS ltac:(discriminate)). rewrite length_skipn in HS. lia. }
          fold nf. (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end).
          apply (cellZ_frame SG Ma); [| lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
          * apply (cellZ_frame SG M1); [exact (CFA i k Hik) | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
            intros j Hj. apply MaF. rewrite u64_lit by lia. (lazymatch goal with |- ?G => let G' := eval unfold Fdr in G in change_no_check G' end). do 3 right. fold nf. (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). cbn in Hj. lia.
          * intros j Hj. apply EQa; [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top in G in change_no_check G' end). do 4 right; left. fold nf. (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). cbn in Hj. lia.
        + exact SBM.
        + exact MI.
    Qed.
  End Mid.
End K6A.
End BoAllocFRcK6a.
Module BoAllocFRcK6h.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG BoAllocFRcL BoAllocFRcH BoAllocFRcK6a.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section K6H.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable TSDP : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis CELLSPIN : free_cells_spin bt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Definition Cshape (c : Z) (z : Z) : Prop :=
    (AIMGLO <= z < AIMGHI -> 0x10ab58 + 888 <= z < 0x10ab58 + 920)
    /\ ~ (T + 208 + 80 * c + 4 <= z < T + 208 + 80 * c + 80)
    /\ ~ (SBEG + 2 ^ 37 + 128 * c + 8 <= z < SBEG + 2 ^ 37 + 128 * c + 128).

  Definition dfull_cells_stmt (st : ast) (c : Z) (M : mem) (mdl : Model) : Prop :=
    let Hd := HID st mdl in let memD := mrestrict Hd M in
    let fa := SBEG + c * 2 ^ 32 + 3758096384 in let RIz := SBEG + 2 ^ 37 + 128 * c in let pc_ := T + 208 + 80 * c in
    (forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false)
    /\ (forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false)
    /\ (forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false)
    /\ (forall z, fa <= z < fa + r_mapped_fa (a_reg st c) -> Hd (Z_to_bv 64 z) = false)
    /\ rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))
    /\ rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SBEG + 2 ^ 37)))
    /\ rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff)
    /\ rdn BSEGS memD (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))
    /\ rdn BSEGS memD (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))
    /\ rdn BSEGS memD (Z_to_bv 64 0x10468) 8 = Some (LE8 (Z_to_bv 64 0xafffff00000fffff))
    /\ rdn BSEGS memD (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1))
    /\ rdn BSEGS memD (Z_to_bv 64 0x105f60) 8 = Some (LE8 (Z_to_bv 64 0x19fcdc))
    /\ rdn BSEGS memD (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
    /\ rdn BSEGS memD (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 (cache_max c))
    /\ (forall i k, nth_error (a_cache st c) i = Some k -> rdn BSEGS memD (Z_to_bv 64 (pc_ + 16 + 4 * Z.of_nat i)) 4 = Some (LE4 k))
    /\ rdn BSEGS memD (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (r_free (a_reg st c))))))
    /\ (forall i, T <= i < T + 4096 -> memD (Z_to_bv 64 i) <> None)
    /\ (forall i, RIz <= i < RIz + 128 -> memD (Z_to_bv 64 i) <> None)
    /\ store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true
    /\ store_ok BSEGS memD (Z_to_bv 64 RIz) 128 = true
    /\ (forall lo (n : nat), fa <= lo -> lo + Z.of_nat n <= fa + r_mapped_fa (a_reg st c) -> store_ok BSEGS memD (Z_to_bv 64 lo) n = true).

  Theorem dfull_cells : forall (Yx : Z -> Prop) st Lc FF (M : mem) mdl qt qg c,
    WFq bt st Lc FF qt qg -> RepX bt Yx st Lc FF M mdl -> 1 <= c <= 30 -> a_cinit st = true ->
    (forall z, Yx z -> Cshape c z) ->
    dfull_cells_stmt st c M mdl.
  Proof using CELLSPIN RCF RCC CELLNB BT_ia BT_segs TSDP.
    intros Yx st Lc FF M mdl qt qg c W RX Hc CINIT YS. (lazymatch goal with |- ?G => let G' := eval unfold dfull_cells_stmt in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    pose proof ceil_rng as CR.
    pose proof RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ Yx (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    unfold free_cells_nb in CELLNB. destruct RCC as (CELL_rib & _ & _). destruct RCF as (CELL_int & CELL_gpg & CELL_pg & CELL_470).
    destruct CELLSPIN as (CSP1 & CSP2 & CSP3).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & SB16).
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof W as (_ & WC & _). destruct (WC c Hc) as (CLEN & _ & _). clear WC.
    assert (P_Gmx : 2 <= cache_max c <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold cache_max, cache_hint in G in change_no_check G' end); clear; lia).
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    pose proof RP as (Rc & _ & Rt & Rr & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _).
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & _).
    destruct (TPC c Hc) as (PCcnt & PCmax & _ & PCks). rewrite CINIT in PCmax.
    destruct (Rr c Hc) as [(_ & _ & RInf & _ & _ & _ & _ & _ & _ & RIW) (_ & FAW & _)].
    rewrite BT_segs in *.
    unfold T_PC, PC_SZ, PG in *.
    unfold reginfo, chunk_addr, fa_beg, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, PTRHI in *.
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 CR; lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). exact Hz. }
    assert (NHF : forall z, SBEG + c * 2 ^ 32 + 3758096384 <= z < SBEG + c * 2 ^ 32 + 3758096384 + r_mapped_fa (a_reg st c) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 Q5 Q6 CR Hc; lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP c z Hc).
      (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). exact Hz. }
    assert (IMG : forall z, AIMGLO <= z < AIMGHI -> ~ (0x10ab58 + 888 <= z < 0x10ab58 + 920) -> ~ Yx z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz NQ. split; [intros Hy; exact (NQ (proj1 (YS z Hy) Hz)) | apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    Ltac czlh := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) ].
    Ltac konsth Hd M M0 Yx Rc EQ0 IMG C := apply (cellX Hd M M0 Yx _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czlh | czlh | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply IMG; clear - Hz; lia].
    split; [exact NHs|]. split; [exact NHT|]. split; [exact NHR|]. split; [exact NHF|].
    split; [konsth Hd M M0 Yx Rc EQ0 IMG CELLNB|]. split; [konsth Hd M M0 Yx Rc EQ0 IMG CELL_rib|]. split; [konsth Hd M M0 Yx Rc EQ0 IMG CELL_int|].
    split; [konsth Hd M M0 Yx Rc EQ0 IMG CELL_gpg|]. split; [konsth Hd M M0 Yx Rc EQ0 IMG CELL_pg|]. split; [konsth Hd M M0 Yx Rc EQ0 IMG CELL_470|].
    split; [konsth Hd M M0 Yx Rc EQ0 IMG CSP1|]. split; [konsth Hd M M0 Yx Rc EQ0 IMG CSP2|]. split; [konsth Hd M M0 Yx Rc EQ0 IMG CSP3|].
    assert (OFFT : forall z, T + 208 + 80 * c + 4 <= z < T + 208 + 80 * c + 80 -> ~ Yx z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [intros Hy; exact (proj1 (proj2 (YS z Hy)) Hz) | apply NHT; clear - Hz Hc; lia]. }
    assert (OFFR : forall z, SBEG + 2 ^ 37 + 128 * c + 8 <= z < SBEG + 2 ^ 37 + 128 * c + 128 -> ~ Yx z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [intros Hy; exact (proj2 (proj2 (YS z Hy)) Hz) | apply NHR; clear - Hz Hc; lia]. }
    split.
    { apply (cellX Hd M M0 Yx _ _ _ PCmax EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz. lia. }
    split.
    { intros i k Hik. assert (Hi : Z.of_nat i < cache_max c) by (apply (Z.lt_le_trans _ (Z.of_nat (length (a_cache st c)))); [apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate | exact CLEN]).
      specialize (PCks _ _ Hik).
      apply (cellX Hd M M0 Yx _ _ _ PCks EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR Hc Hi P_Gmx; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz Hi P_Gmx. lia. }
    split.
    { apply (cellX Hd M M0 Yx _ _ _ RInf EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz. lia. }
    split.
    { intros i Hi. fold Hd. rewrite mrestrict_off by (apply NHT; exact Hi). apply GR0. apply (writableZ_def M0 _ _ _ TW). exact Hi. }
    split.
    { intros i Hi. fold Hd. rewrite mrestrict_off by (apply NHR; clear - Hi Hc; lia). apply GR0. apply (writableZ_def M0 _ _ _ RIW). exact Hi. }
    split.
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    split.
    { apply (sokX Hd M M0 _ _ _ _ RIW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - SB1 CR Hc; lia | clear - SB0 Hc; lia |].
      intros z Hz. apply NHR. clear - Hz Hc. cbn in Hz. lia. }
    intros lo n Hlo Hhi.
    apply (sokX Hd M M0 _ _ _ _ FAW GR0); [exact Hlo | exact Hhi | clear - SB1 Q5 Q6 CR Hc; lia | clear - SB0 Hlo Hc; lia |].
    intros z Hz. apply NHF. clear - Hz Hlo Hhi. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem dfull_cells_A : forall (Yx : Z -> Prop) st Lc FF (M : mem) mdl qt qg c,
    WFq bt st Lc FF qt qg -> RepX bt Yx st Lc FF M mdl -> 1 <= c <= 30 ->
    (forall z, Yx z -> ~ (T + 208 + 80 * c <= z < T + 208 + 80 * c + 4) /\ ~ (SBEG + 2 ^ 37 + 128 * c <= z < SBEG + 2 ^ 37 + 128 * c + 8)) ->
    let memD := mrestrict (HID st mdl) M in
    rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 (Z.of_nat (length (a_cache st c))))
    /\ rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof using BT_segs.
    intros Yx st Lc FF M mdl qt qg c W RX Hc YS. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    pose proof ceil_rng as CR.
    pose proof RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ Yx (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & SB16).
    pose proof RP as (Rc & _ & Rt & Rr & _).
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & _).
    destruct (TPC c Hc) as (PCcnt & _).
    destruct (Rr c Hc) as [(RImu & _) _].
    rewrite BT_segs in *.
    unfold T_PC, PC_SZ, PG in *. unfold reginfo, KSPACE, PG in *.
    set (Hd := HID st mdl).
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 CR; lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). exact Hz. }
    split.
    - apply (cellX Hd M M0 Yx _ _ _ PCcnt EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [intros Hy; exact (proj1 (YS z Hy) Hz) | apply NHT; clear - Hz Hc; lia].
    - apply (cellX Hd M M0 Yx _ _ _ RImu EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [intros Hy; exact (proj2 (YS z Hy) Hz) | apply NHR; clear - Hz Hc; lia].
  Qed.
End K6H.
End BoAllocFRcK6h.
Require Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcM2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58 (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hda (q : list batch) (d : Z) : Z := match q with [] => d | b :: _ => ba_addr b end.
Fixpoint lasta (q : list batch) (d : Z) : Z := match q with [] => d | b :: r => lasta r (ba_addr b) end.
Definition blen (b : batch) : Z := Z.of_nat (length (ba_items b)).
Definition bmerge (b1 b2 : batch) : batch := BATCH (ba_addr b1) (ba_items b1 ++ ba_items b2).
Definition bempty (b : batch) : batch := BATCH (ba_addr b) [].

Fixpoint mergeF (cur : batch) (l : list batch) : list batch * list batch :=
  match l with
  | [] => ([cur], [])
  | nxt :: tl => if (blen cur + blen nxt <=? 1021)
                 then let (g, e) := mergeF (bmerge cur nxt) tl in (g, bempty nxt :: e)
                 else let (g, e) := mergeF nxt tl in (cur :: g, e)
  end.

Lemma lasta_app : forall q1 q2 d, q2 <> [] -> lasta (q1 ++ q2) d = lasta q2 d.
Proof.
  induction q1 as [|b r IH]; intros q2 d NE; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [app lasta] in G in change_no_check G' end). rewrite IH by exact NE.
  destruct q2 as [|b2 r2]; [exfalso; exact (NE eq_refl) | reflexivity].
Qed.
Lemma lasta_snoc : forall q b d, lasta (q ++ [b]) d = ba_addr b.
Proof. intros q b d. rewrite lasta_app by discriminate. reflexivity. Qed.
Lemma ba_bytes_merge : forall b1 b2, ba_bytes (bmerge b1 b2) = ba_bytes b1 + ba_bytes b2 - 8192.
Proof.
  intros b1 b2. (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes, bmerge, BATCHSZ in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end).
  induction (ba_items b1) as [|it r IH]; (lazymatch goal with |- ?G => let G' := eval cbn [app fold_right] in G in change_no_check G' end); lia.
Qed.

Lemma blen_merge : forall b1 b2, blen (bmerge b1 b2) = blen b1 + blen b2.
Proof. intros b1 b2. (lazymatch goal with |- ?G => let G' := eval unfold blen, bmerge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). rewrite length_app, Nat2Z.inj_add. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bcell (m : word -> option byte) (b : batch) (nx : Z) : Prop :=
  rdn BSEGS m (Z_to_bv 64 (ba_addr b)) 8 = Some (LE8 (Z_to_bv 64 nx))
  /\ rdn BSEGS m (Z_to_bv 64 (ba_addr b + 8)) 8 = Some (LE8 (Z_to_bv 64 (ba_bytes b)))
  /\ rdn BSEGS m (Z_to_bv 64 (ba_addr b + 16)) 8 = Some (LE8 (Z_to_bv 64 (blen b)))
  /\ (forall j mn, nth_error (ba_items b) j = Some mn ->
        rdn BSEGS m (Z_to_bv 64 (ba_addr b + 24 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 (fst mn)))).
Fixpoint chainR (m : word -> option byte) (q : list batch) (nx : Z) : Prop :=
  match q with
  | [] => True
  | b :: r => bcell m b (hda r nx) /\ chainR m r nx
  end.

Lemma chainR_app : forall m q1 q2 nx, chainR m (q1 ++ q2) nx <-> chainR m q1 (hda q2 nx) /\ chainR m q2 nx.
Proof.
  intros m q1 q2 nx. induction q1 as [|b r IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto|]. (lazymatch goal with |- ?G => let G' := eval cbn [app chainR] in G in change_no_check G' end).
  replace (hda (r ++ q2) nx) with (hda r (hda q2 nx)) by (destruct r; reflexivity). tauto.
Qed.

(* [comment removed for export] *)
Definition bgeo (b : batch) : Prop := 0 <= ba_addr b /\ ba_addr b + 8192 < 2 ^ 64 /\ blen b <= 1021.

Lemma rd8_eq : forall (m m' : word -> option byte) (c : Z) bs, 0 <= c -> c + 8 < 2 ^ 64 ->
  (forall x : word, c <= U x < c + 8 -> m' x = m x) -> rdn BSEGS m (Z_to_bv 64 c) 8 = Some bs -> rdn BSEGS m' (Z_to_bv 64 c) 8 = Some bs.
Proof.
  intros m m' c bs H0 H1 EQ Hr. apply (rd_same BSEGS m' m (Z_to_bv 64 c) 8 bs); [| wd_ulia_c | exact Hr].
  intros x Hx. apply EQ. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma bcell_frame2 : forall (m m' : word -> option byte) b nx nx', bgeo b ->
  (forall x : word, ba_addr b + 8 <= U x < ba_addr b + 8192 -> m' x = m x) ->
  rdn BSEGS m' (Z_to_bv 64 (ba_addr b)) 8 = Some (LE8 (Z_to_bv 64 nx')) ->
  bcell m b nx -> bcell m' b nx'.
Proof.
  intros m m' b nx nx' (G0 & G1 & G2) EQ NX (_ & C2 & C3 & C4). (lazymatch goal with |- ?G => let G' := eval unfold bcell in G in change_no_check G' end). split; [exact NX|].
  split; [apply (rd8_eq m m'); [lia | lia | intros x Hx; apply EQ; lia | exact C2]|].
  split; [apply (rd8_eq m m'); [lia | lia | intros x Hx; apply EQ; lia | exact C3]|].
  intros j mn Hj. assert (Hjl : (j < length (ba_items b))%nat) by (apply nth_error_Some; rewrite Hj; discriminate). unfold blen in G2.
  apply (rd8_eq m m'); [lia | lia | intros x Hx; apply EQ; lia | exact (C4 j mn Hj)].
Qed.
Lemma bcell_frame : forall (m m' : word -> option byte) b nx, bgeo b ->
  (forall x : word, ba_addr b <= U x < ba_addr b + 8192 -> m' x = m x) -> bcell m b nx -> bcell m' b nx.
Proof.
  intros m m' b nx G EQ C. pose proof G as (G0 & G1 & G2). apply (bcell_frame2 m m' b nx nx G); [intros x Hx; apply EQ; lia | | exact C].
  destruct C as (C1 & _). apply (rd8_eq m m'); [lia | lia | intros x Hx; apply EQ; lia | exact C1].
Qed.
Lemma chainR_frame : forall (m m' : word -> option byte) q nx, (forall b, In b q -> bgeo b) ->
  (forall b (x : word), In b q -> ba_addr b <= U x < ba_addr b + 8192 -> m' x = m x) -> chainR m q nx -> chainR m' q nx.
Proof.
  intros m m' q nx. induction q as [|b r IH]; intros G EQ C; [exact I|]. cbn [chainR] in *. destruct C as [C1 C2]. split.
  - apply (bcell_frame m m'); [apply G; left; reflexivity | intros x Hx; apply (EQ b x (or_introl eq_refl) Hx) | exact C1].
  - apply IH; [intros b0 Hb0; apply G; right; exact Hb0 | intros b0 x Hb0 Hx; apply (EQ b0 x (or_intror Hb0) Hx) | exact C2].
Qed.
(* [comment removed for export] *)
Lemma chainR_relink : forall (m m' : word -> option byte) q nx nx', q <> [] -> (forall b, In b q -> bgeo b) ->
  (forall b (x : word), In b q -> ba_addr b <= U x < ba_addr b + 8192 -> ~ (lasta q 0 <= U x < lasta q 0 + 8) -> m' x = m x) ->
  (forall b, In b q -> ba_addr b <> lasta q 0 -> ba_addr b + 8192 <= lasta q 0 \/ lasta q 0 + 8192 <= ba_addr b) ->
  List.NoDup (map ba_addr q) ->
  rdn BSEGS m' (Z_to_bv 64 (lasta q 0)) 8 = Some (LE8 (Z_to_bv 64 nx')) ->
  chainR m q nx -> chainR m' q nx'.
Proof.
  intros m m' q nx nx'. induction q as [|b r IH]; intros NE G EQ SEP ND NX C; [exfalso; exact (NE eq_refl)|].
  cbn [chainR] in *. destruct C as [C1 C2]. destruct r as [|b2 r2].
  - cbn [lasta hda chainR] in *. split; [| exact I].
    apply (bcell_frame2 m m' b nx nx'); [apply G; left; reflexivity | | exact NX | exact C1].
    intros x Hx. apply (EQ b x (or_introl eq_refl)); lia.
  - assert (EL : lasta (b :: b2 :: r2) 0 = lasta (b2 :: r2) 0) by reflexivity. rewrite EL in *.
    assert (Hlast : In (lasta (b2 :: r2) 0) (map ba_addr (b2 :: r2))).
    { clear. generalize b2 0. induction r2 as [|b3 r3 IH3]; intros b d; [left; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [lasta] in G in change_no_check G' end). right. exact (IH3 b3 (ba_addr b)). }
    inversion ND as [|a0 l0 NI ND']; subst.
    split.
    + (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end). apply (bcell_frame m m'); [apply G; left; reflexivity | | exact C1].
      intros x Hx. apply (EQ b x (or_introl eq_refl) Hx).
      assert (NEa : ba_addr b <> lasta (b2 :: r2) 0) by (intros E; apply NI; rewrite E; exact Hlast).
      destruct (SEP b (or_introl eq_refl) NEa) as [Q | Q]; lia.
    + apply IH; [discriminate | intros b0 Hb0; apply G; right; exact Hb0
                | intros b0 x Hb0 Hx NL; apply (EQ b0 x (or_intror Hb0) Hx NL)
                | intros b0 Hb0 NEa; apply (SEP b0 (or_intror Hb0) NEa) | exact ND' | exact NX | exact C2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nd_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [contradiction|]. cbn [app] in ND. inversion ND as [|y' l' NI ND']; subst.
  destruct H1 as [-> | H1]; [apply NI; apply in_app_iff; right; exact H2 | exact (IH l2 x ND' H1 H2)].
Qed.
Lemma lasta_in : forall q b, In (lasta q (ba_addr b)) (map ba_addr (b :: q)).
Proof.
  induction q as [|b2 r IH]; intros b; [left; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [lasta] in G in change_no_check G' end). right. exact (IH b2).
Qed.
Lemma lasta_in0 : forall q d, q <> [] -> In (lasta q d) (map ba_addr q).
Proof. intros q d NE. destruct q as [|b r]; [exfalso; exact (NE eq_refl)|]. (lazymatch goal with |- ?G => let G' := eval cbn [lasta] in G in change_no_check G' end). exact (lasta_in r b). Qed.


(* [comment removed for export] *)
Lemma nd_groups : forall (D T EE : list Z) c n, List.NoDup (D ++ c :: n :: T ++ EE) ->
  c <> n /\ (forall x, In x D \/ In x T \/ In x EE -> x <> c /\ x <> n)
  /\ (forall x, In x D \/ In x T -> ~ In x EE) /\ List.NoDup EE.
Proof.
  intros D T EE c n ND.
  pose proof (NoDup_remove _ _ _ ND) as [ND1 NI1]. pose proof (NoDup_remove D (T ++ EE) n ND1) as [ND2 NI2].
  assert (NDc : forall x, In x (D ++ n :: T ++ EE) -> x <> c) by (intros x Hx E; subst x; exact (NI1 Hx)).
  assert (NDn : forall x, In x (D ++ T ++ EE) -> x <> n) by (intros x Hx E; subst x; exact (NI2 Hx)).
  split; [intros E; apply (NDc n); [apply in_app_iff; right; left; reflexivity | symmetry; exact E]|].
  split.
  { intros x Hx. split; [apply NDc | apply NDn]; rewrite ?in_app_iff; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); rewrite ?in_app_iff; tauto. }
  split.
  { intros x Hx HE. destruct Hx as [Hx | Hx].
    - apply (nd_app_disj D (T ++ EE) x ND2 Hx). apply in_app_iff. right. exact HE.
    - apply (nd_app_disj T EE x (NoDup_app_remove_l _ _ ND2) Hx HE). }
  exact (NoDup_app_remove_l _ _ (NoDup_app_remove_l _ _ ND2)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MGLOOP.
  Context {fx : FPState}.
  Variables (rom : word -> option byte) (S : word) (A : list Z) (m0 : word -> option byte).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GEO : forall a, In a A -> AIMGHI <= a /\ a + 8192 <= U S - 3584.
  Hypothesis SEP : forall a1 a2, In a1 A -> In a2 A -> a1 <> a2 -> bsep a1 a2.
  Hypothesis WR0 : forall a k n, In a A -> 0 <= k -> k + Z.of_nat n <= 8192 -> store_ok BSEGS m0 (Z_to_bv 64 (a + k)) n = true.
  Hypothesis WRS : store_ok BSEGS m0 (at_ S (-2288)) 32 = true.

  Definition cellq (m : word -> option byte) (c v : Z) : Prop := rdn BSEGS m (Z_to_bv 64 c) 8 = Some (LE8 (Z_to_bv 64 v)).
  Definition cells (m : word -> option byte) (k v : Z) : Prop := rdn BSEGS m (at_ S k) 8 = Some (LE8 (Z_to_bv 64 v)).
  #[local] Abbreviation len l := (Z.of_nat (@length batch l)).

  Definition mg_inv (done : list batch) (cur : batch) (l E : list batch) (m : word -> option byte) : Prop :=
    mem_grows m0 m
    /\ chainR m done (ba_addr cur) /\ bcell m cur (hda l 0) /\ chainR m l 0 /\ chainR m E 0
    /\ cellq m (IBq + 888) (len done + 1 + len l) /\ cellq m (IBq + 904) (lasta l (ba_addr cur))
    /\ cells m (-2288) (len E) /\ cells m (-2280) (hda E 0) /\ cells m (-2272) (lasta E 0) /\ cells m (-2264) (8192 * len E)
    /\ (forall b, In b (done ++ cur :: l ++ E) -> In (ba_addr b) A /\ blen b <= 1021)
    /\ List.NoDup (map ba_addr (done ++ cur :: l ++ E))
    /\ (forall b, In b (cur :: l) -> 8192 <= ba_bytes b) /\ ba_bytes cur + q_bytes l < 2 ^ 41
    /\ len done + 1 + len l + len E < 2 ^ 28.

  Definition mg_footL (x : Z) : Prop :=
    (exists a, In a A /\ a <= x < a + 8192) \/ (IBq + 888 <= x < IBq + 896) \/ (IBq + 904 <= x < IBq + 912) \/ (U S - 2288 <= x < U S - 2256).

  Lemma atS : forall k, -4096 <= k <= 0 -> at_ S k = Z_to_bv 64 (U S + k).
  Proof using HS. intros k Hk. pose proof (u64_range S) as HSr. apply bv_eq. rewrite at_u by lia. unorm. reflexivity. Qed.

  Lemma bgeo_of : forall b, In (ba_addr b) A -> blen b <= 1021 -> bgeo b.
  Proof using GEO HS S. intros b HA HL. destruct (GEO _ HA) as [G1 G2]. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold bgeo in G in change_no_check G' end). clear - G1 G2 HL HS HSr. lia. Qed.

  (* [comment removed for export] *)
  Lemma adv_step : forall done cur nxt tl E m (regs : bvmap 5 word),
    mg_inv done cur (nxt :: tl) E m -> 1021 < blen cur + blen nxt ->
    mg_keep S regs regs -> mg_head regs (ba_addr cur) (ba_addr nxt) (8192 * len E) ->
    exists r, msteps BSEGS (mkst regs (0x4e620 : word) m rom) (mkst r (if (hda tl 0 =? 0) then (0x4e704 : word) else (0x4e620 : word)) m rom)
      /\ mg_keep S regs r /\ mg_head r (ba_addr nxt) (hda tl 0) (8192 * len E)
      /\ mg_inv (done ++ [cur]) nxt tl E m.
  Proof using GEO HS.
    intros done cur nxt tl E m regs INV BIG HK HH.
    destruct INV as (GR & CD & CC & CL & CE & Hlen & Hlast & Tsz & Tfirst & Tlast & Tb & INA & ND & SZ & TOT & LEN).
    cbn [chainR] in CL. destruct CL as [CN CT]. cbn [hda] in CC.
    destruct (INA cur ltac:(apply in_app_iff; right; left; reflexivity)) as [Ac Lc].
    destruct (INA nxt ltac:(apply in_app_iff; right; right; left; reflexivity)) as [An Ln].
    destruct (GEO _ Ac) as [Gc1 Gc2]. destruct (GEO _ An) as [Gn1 Gn2]. pose proof (u64_range S) as HSr.
    assert (Hnn : 0 <= hda tl 0 < 2 ^ 64).
    { destruct tl as [|b3 tl']; (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end); [lia|]. destruct (INA b3 ltac:(apply in_app_iff; right; right; right; left; reflexivity)) as [A3 _].
      destruct (GEO _ A3) as [G31 G32]. clear - G31 G32 HS HSr. lia. }
    pose proof CC as (_ & _ & Cc3 & _). pose proof CN as (Cn1 & _ & Cn3 & _).
    destruct (mg_adv m rom S (ba_addr cur) (ba_addr nxt) (8192 * len E) (blen cur) (blen nxt) (hda tl 0) regs HK HH) as (r & RUN & KEEP & HEAD);
      [clear - Lc; unfold blen in *; lia | clear - Ln; unfold blen in *; lia | exact BIG | clear - Gc1 Gc2 HS HSr; lia | clear - Gn1 Gn2 HS HSr; lia | exact Hnn | exact Cc3 | exact Cn3 | exact Cn1 |].
    exists r. split; [exact RUN|]. split; [exact KEEP|]. split; [exact HEAD|].
    (lazymatch goal with |- ?G => let G' := eval unfold mg_inv in G in change_no_check G' end). split; [exact GR|].
    split. { apply chainR_app. split; [exact CD|]. (lazymatch goal with |- ?G => let G' := eval cbn [chainR hda] in G in change_no_check G' end). split; [exact CC | exact I]. }
    split; [exact CN|]. split; [exact CT|]. split; [exact CE|].
    split. { replace (len (done ++ [cur]) + 1 + len tl) with (len done + 1 + len (nxt :: tl)); [exact Hlen|]. rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). clear. lia. }
    split; [exact Hlast|]. split; [exact Tsz|]. split; [exact Tfirst|]. split; [exact Tlast|]. split; [exact Tb|].
    split. { intros b Hb. apply INA. rewrite <- app_assoc in Hb. exact Hb. }
    split. { rewrite <- app_assoc. exact ND. }
    split. { intros b Hb. apply SZ. right. exact Hb. }
    split. { pose proof (SZ cur (or_introl eq_refl)) as Z1. change (q_bytes (nxt :: tl)) with (ba_bytes nxt + q_bytes tl) in TOT. clear - Z1 TOT. lia. }
    rewrite length_app. cbn [length] in *. clear - LEN. lia.
  Qed.

  Lemma mg_keep_self : forall r0 r, mg_keep S r0 r -> mg_keep S r r.
  Proof using. intros r0 r (A1 & A2 & A3 & _). (lazymatch goal with |- ?G => let G' := eval unfold mg_keep in G in change_no_check G' end). repeat split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma foot_other : forall cur nxt c1 (ws : list word) lastv tsz tlast a x,
    In a A -> In cur A -> In nxt A -> (tsz <> 0 -> In tlast A) -> a <> cur -> a <> nxt -> (tsz <> 0 -> a <> tlast) ->
    0 <= c1 /\ c1 + Z.of_nat (length ws) <= 1021 ->
    a <= x < a + 8192 -> ~ mg_foot S cur nxt c1 lastv tsz tlast ws x.
  Proof using SEP GEO.
    intros cur nxt c1 ws lastv tsz tlast a x Aa Ac An At N1 N2 N3 Hc Hx F.
    destruct (GEO _ Aa) as [Ga1 Ga2]. destruct (GEO _ Ac) as [Gc1 Gc2]. destruct (GEO _ An) as [Gn1 Gn2].
    pose proof (SEP a cur Aa Ac N1) as S1. pose proof (SEP a nxt Aa An N2) as S2. unfold bsep in S1, S2.
    unfold mg_foot in F. destruct F as [F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]].
    - clear - F Hx S1. lia.
    - clear - F Hx S1 Hc. lia.
    - clear - F Hx S2. lia.
    - clear - F Hx Ga1. lia.
    - clear - F Hx Ga1. lia.
    - clear - F Hx Ga2. lia.
    - destruct F as [Nt F]. pose proof (SEP a tlast Aa (At Nt) (N3 Nt)) as S3. unfold bsep in S3. clear - F Hx S3. lia.
    - clear - F Hx Ga2. lia.
    - clear - F Hx Ga2. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma foot_sub : forall cur nxt c1 (ws : list word) lastv tsz tlast x,
    In cur A -> In nxt A -> (tsz <> 0 -> In tlast A) -> 0 <= c1 /\ c1 + Z.of_nat (length ws) <= 1021 ->
    mg_foot S cur nxt c1 lastv tsz tlast ws x -> mg_footL x.
  Proof using.
    intros cur nxt c1 ws lastv tsz tlast x Ac An At Hc F. (lazymatch goal with |- ?G => let G' := eval unfold mg_footL in G in change_no_check G' end). unfold mg_foot in F.
    destruct F as [F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]].
    - left. exists cur. split; [exact Ac | clear - F; lia].
    - left. exists cur. split; [exact Ac | clear - F Hc; lia].
    - left. exists nxt. split; [exact An | clear - F; lia].
    - right. left. exact F.
    - right. right. left. exact (proj2 F).
    - right. right. right. clear - F. lia.
    - destruct F as [Nt F]. left. exists tlast. split; [exact (At Nt) | clear - F; lia].
    - right. right. right. clear - F. lia.
    - right. right. right. clear - F. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma merge_step : forall done cur nxt tl E m (regs : bvmap 5 word),
    mg_inv done cur (nxt :: tl) E m -> blen cur + blen nxt <= 1021 ->
    mg_keep S regs regs -> mg_head regs (ba_addr cur) (ba_addr nxt) (8192 * len E) ->
    exists r m', msteps BSEGS (mkst regs (0x4e620 : word) m rom) (mkst r (if (hda tl 0 =? 0) then (0x4e704 : word) else (0x4e620 : word)) m' rom)
      /\ mg_keep S regs r /\ mg_head r (ba_addr cur) (hda tl 0) (8192 * len (E ++ [bempty nxt]))
      /\ mg_inv done (bmerge cur nxt) tl (E ++ [bempty nxt]) m'
      /\ (forall x : word, ~ mg_footL (U x) -> m' x = m x) /\ mem_grows m m'
      /\ (forall x : word, IBq + 888 <= U x < IBq + 896 -> m' x <> None).
  Proof using WRS WR0 SEP GEO HS.
    intros done cur nxt tl E m regs INV FIT HK HH.
    destruct INV as (GR & CD & CC & CL & CE & Hlen & Hlast & Tsz & Tfirst & Tlast & Tb & INA & ND & SZ & TOT & LEN).
    cbn [chainR] in CL. destruct CL as [CN CT]. cbn [hda] in CC. pose proof (u64_range S) as HSr.
    set (ca := ba_addr cur) in *. set (na := ba_addr nxt) in *.
    set (ws := map (fun mn : Z * Z => Z_to_bv 64 (fst mn) : word) (ba_items nxt)).
    assert (Ews : Z.of_nat (length ws) = blen nxt) by ((lazymatch goal with |- ?G => let G' := eval unfold ws, blen in G in change_no_check G' end); rewrite length_map; reflexivity).
    destruct (INA cur ltac:(apply in_app_iff; right; left; reflexivity)) as [Ac Lc]. fold ca in Ac.
    destruct (INA nxt ltac:(apply in_app_iff; right; right; left; reflexivity)) as [An Ln]. fold na in An.
    destruct (GEO _ Ac) as [Gc1 Gc2]. destruct (GEO _ An) as [Gn1 Gn2].
    assert (Bc0 : 0 <= blen cur) by ((lazymatch goal with |- ?G => let G' := eval unfold blen in G in change_no_check G' end); lia). assert (Bn0 : 0 <= blen nxt) by ((lazymatch goal with |- ?G => let G' := eval unfold blen in G in change_no_check G' end); lia).
    assert (Hc : 0 <= blen cur /\ blen cur + Z.of_nat (length ws) <= 1021) by (rewrite Ews; clear - Bc0 FIT; lia).
    (* [comment removed for export] *)
    pose proof ND as ND'. rewrite map_app in ND'. cbn [map] in ND'. rewrite map_app in ND'. fold ca na in ND'.
    destruct (nd_groups _ _ _ _ _ ND') as (NEcn & NDo & NDe & NDE).
    assert (Hsep : ca + 8192 <= na \/ na + 8192 <= ca) by exact (SEP ca na Ac An NEcn).
    assert (INE : forall b, In b E -> In (ba_addr b) A) by (intros b Hb; apply INA; apply in_app_iff; right; right; right; apply in_app_iff; right; exact Hb).
    assert (TLA : len E <> 0 -> In (lasta E 0) A /\ lasta E 0 <> ca /\ lasta E 0 <> na).
    { intros NZ. assert (NEe : E <> []) by (intros EE; rewrite EE in NZ; cbn in NZ; exact (NZ eq_refl)).
      pose proof (lasta_in0 E 0 NEe) as HL. destruct (NDo (lasta E 0) ltac:(right; right; exact HL)) as [Q1 Q2].
      apply in_map_iff in HL. destruct HL as (bl & EL & HbL). split; [rewrite <- EL; exact (INE bl HbL) | split; assumption]. }
    assert (Htl : len E <> 0 -> (AIMGHI <= lasta E 0 /\ lasta E 0 + 8192 <= U S - 3584)
                                /\ (lasta E 0 + 8192 <= ca \/ ca + 8192 <= lasta E 0) /\ (lasta E 0 + 8192 <= na \/ na + 8192 <= lasta E 0)).
    { intros NZ. destruct (TLA NZ) as (T1 & T2 & T3). split; [exact (GEO _ T1)|]. split; [exact (SEP _ _ T1 Ac T2) | exact (SEP _ _ T1 An T3)]. }
    (* [comment removed for export] *)
    pose proof (SZ cur (or_introl eq_refl)) as Zc. pose proof (SZ nxt (or_intror (or_introl eq_refl))) as Zn.
    assert (Ztl : 0 <= q_bytes tl).
    { clear - SZ. induction tl as [|b r IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. change (q_bytes (b :: r)) with (ba_bytes b + q_bytes r).
      pose proof (SZ b ltac:(right; right; left; reflexivity)) as Zb.
      assert (0 <= q_bytes r) by (apply IH; intros b0 Hb0; apply SZ; destruct Hb0 as [-> | [-> | Hb0]]; [left; reflexivity | right; left; reflexivity | right; right; right; exact Hb0]). lia. }
    change (q_bytes (nxt :: tl)) with (ba_bytes nxt + q_bytes tl) in TOT.
    (* [comment removed for export] *)
    assert (WRm : forall a k n, In a A -> 0 <= k -> k + Z.of_nat n <= 8192 -> store_ok BSEGS m (Z_to_bv 64 (a + k)) n = true).
    { intros a k n Ha H0 H1. eapply store_ok_mono; [exact GR | exact (WR0 a k n Ha H0 H1)]. }
    assert (WRSm : store_ok BSEGS m (at_ S (-2288)) 32 = true) by (eapply store_ok_mono; [exact GR | exact WRS]).
    pose proof CC as (Cc1 & Cc2 & Cc3 & Cc4). pose proof CN as (Cn1 & Cn2 & Cn3 & Cn4). fold ca in Cc1, Cc2, Cc3, Cc4. fold na in Cn1, Cn2, Cn3, Cn4.
    assert (Hnn : 0 <= hda tl 0 < 2 ^ 64).
    { destruct tl as [|b3 tl']; (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end); [lia|]. destruct (INA b3 ltac:(apply in_app_iff; right; right; right; left; reflexivity)) as [A3 _].
      destruct (GEO _ A3) as [G31 G32]. clear - G31 G32 HS HSr. lia. }
    (* [comment removed for export] *)
    destruct (mg_mhead m rom S ca na (8192 * len E) (blen cur) (ba_bytes cur) ws regs HK HH) as (r1 & RUN1 & K1 & H1 & R13 & R6).
    { exact Bc0. } { exact (proj2 Hc). } { clear - Zc Zn Ztl TOT. lia. }
    { clear - Gc1 Gc2 HS HSr. lia. } { clear - Gn1 Gn2 HS HSr. lia. } { exact Hsep. }
    { intros k n H0 H1. exact (WRm ca k n Ac H0 H1). }
    { exact Cc3. } { rewrite Ews. exact Cn3. } { exact Cc2. }
    { intros i w Hi. unfold ws in Hi. rewrite nth_error_map in Hi. destruct (nth_error (ba_items nxt) i) as [mn|] eqn:Emn; [|discriminate Hi].
      cbn in Hi. injection Hi as <-. exact (Cn4 i mn Emn). }
    set (M1 := wws m (ca + 24 + 8 * blen cur) ws) in *.
    set (s1 := ba_bytes cur) in *. set (s2 := ba_bytes nxt) in *. set (cnt := blen cur + Z.of_nat (length ws)) in *.
    set (nn := hda tl 0) in *. set (glen := len done + 1 + len (nxt :: tl)) in *. set (lastv := lasta (nxt :: tl) ca) in *.
    set (tsz := len E) in *. set (tlast := lasta E 0) in *. set (ext := 8192 * tsz) in *.
    assert (GR1 : mem_grows m M1) by apply wws_grows.
    assert (W1 : forall c (n : nat), 0 <= c -> c + Z.of_nat n < 2 ^ 64 ->
                   (c + Z.of_nat n <= ca + 24 + 8 * blen cur \/ ca + 24 + 8 * (blen cur + Z.of_nat (length ws)) <= c) ->
                   rdn BSEGS M1 (Z_to_bv 64 c) n = rdn BSEGS m (Z_to_bv 64 c) n).
    { intros c n H0 H1' HD. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply rdn_wws_out; [clear - Gc1 Hc; lia | clear - Gc2 Hc HS HSr; lia | exact H0 | exact H1' | clear - HD; lia]. }
    assert (Glen : 1 <= glen < 2 ^ 28) by ((lazymatch goal with |- ?G => let G' := eval unfold glen in G in change_no_check G' end); clear - LEN; cbn [length] in *; lia).
    assert (Gtsz : 0 <= tsz < 2 ^ 28) by ((lazymatch goal with |- ?G => let G' := eval unfold tsz in G in change_no_check G' end); clear - LEN; lia).
    assert (Glast : 0 <= lastv < 2 ^ 64).
    { pose proof (lasta_in tl nxt) as HL. fold na in HL. change (lasta tl na) with lastv in HL.
      apply in_map_iff in HL. destruct HL as (bl & EL & HbL). destruct (INA bl ltac:(apply in_app_iff; right; right; apply in_app_iff; left; exact HbL)) as [Al _].
      rewrite EL in Al. destruct (GEO _ Al) as [G1 G2]. clear - G1 G2 HS HSr. lia. }
    (* [comment removed for export] *)
    destruct (mg_mtail_a M1 rom S ca na ext s1 s2 cnt nn glen lastv r1 (mg_keep_self _ _ K1) H1 R13 R6) as (r2 & RUN2 & K2 & H2 & Q13 & Q6 & Q7).
    { (lazymatch goal with |- ?G => let G' := eval unfold s1 in G in change_no_check G' end). clear - Zc Zn Ztl TOT. lia. } { (lazymatch goal with |- ?G => let G' := eval unfold s2 in G in change_no_check G' end). clear - Zc Zn Ztl TOT. lia. } { exact Glen. }
    { clear - Gc1 Gc2 HS HSr. lia. } { clear - Gn1 Gn2 HS HSr. lia. } { exact Hsep. }
    { eapply store_ok_mono; [exact GR1|]. replace ca with (ca + 0) by lia. apply WRm; [exact Ac | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [exact GR1|]. replace na with (na + 0) by lia. apply WRm; [exact An | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite W1; [exact Cn2 | clear - Gn1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gn2 HS HSr; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep Hc; lia]. }
    { rewrite W1; [exact Hlen | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc1 Bc0; lia]. }
    { rewrite W1; [exact Cn1 | clear - Gn1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gn2 HS HSr; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep Hc; lia]. }
    { rewrite W1; [exact Hlast | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc1 Bc0; lia]. }
    set (M5 := fr_mga M1 ca na s1 s2 cnt nn) in *.
    assert (GR5 : mem_grows M1 M5) by ((lazymatch goal with |- ?G => let G' := eval unfold M5, fr_mga in G in change_no_check G' end); clearbody M1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    assert (STK5 : forall k v, -2288 <= k -> k + 8 <= -2256 -> cells m k v -> rdn BSEGS M5 (at_ S k) 8 = Some (LE8 (Z_to_bv 64 v))).
    { intros k v Hk1 Hk2 Cv. unfold cells in Cv. rewrite atS in Cv |- * by (clear - Hk1 Hk2; lia). (lazymatch goal with |- ?G => let G' := eval unfold M5 in G in change_no_check G' end).
      rewrite fr_mga_rd; [| clear - Gc1; lia | clear - Gc2 HS HSr; lia | clear - Gn1; lia | clear - Gn2 HS HSr; lia | clear - HS Hk1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HS HSr Hk2; lia
                          | right; clear - Gc2 Hk1; lia | right; clear - Gn2 Hk1; lia].
      rewrite W1; [exact Cv | clear - HS Hk1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HS HSr Hk2; lia | right; clear - Gc2 Hc Hk1; lia]. }
    (* [comment removed for export] *)
    destruct (mg_mtail_b M5 rom S ca na ext glen lastv tsz tlast r2 (mg_keep_self _ _ K2) H2 Q13 Q7 HS Glen Glast Gtsz) as (r3 & RUN3 & K3 & H3 & P13).
    { exact (conj Gn1 Gn2). } { intros NZ. exact (proj1 (Htl NZ)). }
    { eapply store_ok_mono; [exact GR5|]. eapply store_ok_mono; [exact GR1 | exact WRSm]. }
    { eapply store_ok_mono; [exact GR5|]. eapply store_ok_mono; [exact GR1|]. replace na with (na + 0) by lia. apply WRm; [exact An | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { intros NZ. destruct (TLA NZ) as (T1 & _). eapply store_ok_mono; [exact GR5|]. eapply store_ok_mono; [exact GR1|].
      replace tlast with (tlast + 0) by lia. apply WRm; [exact T1 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { apply STK5; [clear; lia | clear; lia | exact Tsz]. }
    { apply STK5; [clear; lia | clear; lia | exact Tlast]. }
    set (M9 := fr_mgb M5 S ca na glen lastv tsz tlast) in *.
    assert (GR9 : mem_grows M5 M9).
    { (lazymatch goal with |- ?G => let G' := eval unfold M9, fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). clearbody M5. destruct (Z.eqb_spec lastv na); destruct (Z.eqb_spec tsz 0); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. }
    assert (Gtl9 : tsz <> 0 -> 0 <= tlast /\ tlast + 8 < 2 ^ 64).
    { intros NZ. destruct (Htl NZ) as ((T1 & T2) & _). clear - T1 T2 HS HSr. lia. }
    (* [comment removed for export] *)
    destruct (mg_mtail_c M9 rom S ca na ext nn tsz (8192 * tsz) r3 (mg_keep_self _ _ K3) H3 P13 HS Hnn) as (r4 & RUN4 & K4 & H4).
    { clear - Gtsz. lia. } { (lazymatch goal with |- ?G => let G' := eval unfold ext in G in change_no_check G' end). clear - Gtsz. lia. } { exact (conj Gc1 Gc2). }
    { eapply store_ok_mono; [exact GR9|]. eapply store_ok_mono; [exact GR5|]. eapply store_ok_mono; [exact GR1 | exact WRSm]. }
    { rewrite atS by (clear; lia). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end).
      rewrite (fr_mgb_rd S HS); [| clear - Gn1; lia | clear - Gn2 HS HSr; lia | exact Gtl9 | clear - HS; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HS HSr; lia
                                 | right; clear - HS; lia | intros _; right; clear - HS; lia | right; clear - Gn2; lia | intros _; right; clear; lia
                                 | intros NZ; destruct (Htl NZ) as ((_ & T2) & _); right; clear - T2; lia].
      rewrite <- atS by (clear; lia). apply STK5; [clear; lia | clear; lia | exact Tb]. }
    { (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end).
      rewrite (fr_mgb_rd S HS); [| clear - Gn1; lia | clear - Gn2 HS HSr; lia | exact Gtl9 | clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2 HS HSr; lia
                                 | right; clear - Gc1; lia | intros _; right; clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep; lia | intros _; left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia
                                 | intros NZ; destruct (Htl NZ) as (_ & T2 & _); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T2; lia].
      (lazymatch goal with |- ?G => let G' := eval unfold M5, fr_mga in G in change_no_check G' end). rd_hit8. }
    change (fr_mgc M9 S na tsz (8192 * tsz)) with (fr_mg M1 S ca na s1 s2 cnt nn glen lastv tsz tlast (8192 * tsz)) in RUN4.
    set (MM := fr_mg M1 S ca na s1 s2 cnt nn glen lastv tsz tlast (8192 * tsz)) in *.
    (* [comment removed for export] *)
    assert (HcurU : AIMGHI <= ca /\ ca + 8192 <= U S - 3584) by exact (conj Gc1 Gc2).
    assert (HnxtU : AIMGHI <= na /\ na + 8192 <= U S - 3584) by exact (conj Gn1 Gn2).
    pose proof (fr_mg_out m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl) as OUT.
    pose proof (fr_mg_grows m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl) as GRM.
    fold M1 cnt MM in OUT, GRM.
    assert (ATl : tsz <> 0 -> In tlast A) by (intros NZ; exact (proj1 (TLA NZ))).
    (* [comment removed for export] *)
    assert (OTHER : forall b (x : word), In (ba_addr b) A -> ba_addr b <> ca -> ba_addr b <> na -> (tsz <> 0 -> ba_addr b <> tlast) ->
                      ba_addr b <= U x < ba_addr b + 8192 -> MM x = m x).
    { intros b x Ab N1 N2 N3 Hx. apply OUT. exact (foot_other ca na (blen cur) ws lastv tsz tlast (ba_addr b) (U x) Ab Ac An ATl N1 N2 N3 Hc Hx). }
    assert (NEtl : forall x, In x (map ba_addr done) \/ In x (map ba_addr tl) -> tsz <> 0 -> x <> tlast).
    { intros x Hx NZ EQx. apply (NDe x Hx). rewrite EQx. apply lasta_in0. intros EE. unfold tsz in NZ. rewrite EE in NZ. exact (NZ eq_refl). }
    exists r4, MM.
    split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4]. }
    split. { eapply mg_keep_trans; [exact K1|]. eapply mg_keep_trans; [exact K2|]. eapply mg_keep_trans; [exact K3 | exact K4]. }
    split. { replace (8192 * len (E ++ [bempty nxt])) with (ext + 8192); [exact H4|]. (lazymatch goal with |- ?G => let G' := eval unfold ext, tsz in G in change_no_check G' end). rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). clear. lia. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold mg_inv in G in change_no_check G' end).
      split; [eapply mem_grows_trans; [exact GR | exact GRM]|].
      (* [comment removed for export] *)
      split.
      { apply (chainR_frame m MM); [intros b Hb; destruct (INA b ltac:(apply in_app_iff; left; exact Hb)) as [Ab Lb]; exact (bgeo_of b Ab Lb) | | exact CD].
        intros b x Hb Hx. destruct (INA b ltac:(apply in_app_iff; left; exact Hb)) as [Ab _].
        destruct (NDo (ba_addr b) ltac:(left; apply in_map; exact Hb)) as [Q1 Q2].
        apply (OTHER b x Ab Q1 Q2); [apply NEtl; left; apply in_map; exact Hb | exact Hx]. }
      (* [comment removed for export] *)
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold bcell in G in change_no_check G' end). change (ba_addr (bmerge cur nxt)) with ca. rewrite ba_bytes_merge, blen_merge. fold s1 s2. rewrite <- Ews. fold cnt.
        split; [exact (fr_mg_cnext m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)|].
        split; [exact (fr_mg_csize m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)|].
        split; [exact (fr_mg_ccount m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)|].
        intros j mn Hj. cbn [bmerge ba_items] in Hj. destruct (Nat.lt_ge_cases j (length (ba_items cur))) as [Lj | Gj].
        - rewrite nth_error_app1 in Hj by exact Lj. pose proof (Cc4 j mn Hj) as C0.
          apply (rd8_eq m MM); [clear - Gc1; lia | clear - Gc2 HS HSr Lj Lc; unfold blen in Lc; lia | | exact C0].
          intros x Hx. apply OUT. (lazymatch goal with |- ?G => let G' := eval unfold mg_foot in G in change_no_check G' end). intros F. unfold blen in *.
          destruct F as [F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]];
            [clear - F Hx; lia | clear - F Hx Lj; lia | clear - F Hx Hsep Lj Lc; lia | clear - F Hx Gc1; lia | clear - F Hx Gc1; lia | clear - F Hx Gc2 Lj Lc; lia
            | destruct F as [NZ F]; destruct (Htl NZ) as (_ & T2 & _); clear - F Hx T2 Lj Lc; lia | clear - F Hx Gc2 Lj Lc; lia | clear - F Hx Gc2 Lj Lc; lia].
        - rewrite nth_error_app2 in Hj by exact Gj.
          pose proof (fr_mg_item m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl
                        (j - length (ba_items cur))%nat (Z_to_bv 64 (fst mn))) as CI. fold M1 cnt MM in CI.
          replace (ca + 24 + 8 * Z.of_nat j) with (ca + 24 + 8 * (blen cur + Z.of_nat (j - length (ba_items cur)))) by ((lazymatch goal with |- ?G => let G' := eval unfold blen in G in change_no_check G' end); clear - Gj; lia).
          apply CI. (lazymatch goal with |- ?G => let G' := eval unfold ws in G in change_no_check G' end). rewrite nth_error_map, Hj. reflexivity. }
      (* [comment removed for export] *)
      split.
      { apply (chainR_frame m MM); [intros b Hb; destruct (INA b ltac:(apply in_app_iff; right; right; right; apply in_app_iff; left; exact Hb)) as [Ab Lb]; exact (bgeo_of b Ab Lb) | | exact CT].
        intros b x Hb Hx. destruct (INA b ltac:(apply in_app_iff; right; right; right; apply in_app_iff; left; exact Hb)) as [Ab _].
        destruct (NDo (ba_addr b) ltac:(right; left; apply in_map; exact Hb)) as [Q1 Q2].
        apply (OTHER b x Ab Q1 Q2); [apply NEtl; right; apply in_map; exact Hb | exact Hx]. }
      (* [comment removed for export] *)
      split.
      { apply chainR_app. (lazymatch goal with |- ?G => let G' := eval cbn [hda chainR] in G in change_no_check G' end). split.
        - destruct (Z.eq_dec tsz 0) as [Z0 | NZ].
          { assert (EE : E = []) by (apply length_zero_iff_nil; unfold tsz in Z0; clear - Z0; lia). rewrite EE. exact I. }
          apply (chainR_relink m MM E 0 na); [intros EE; apply NZ; (lazymatch goal with |- ?G => let G' := eval unfold tsz in G in change_no_check G' end); rewrite EE; reflexivity | intros b Hb; destruct (INA b ltac:(apply in_app_iff; right; right; right; apply in_app_iff; right; exact Hb)) as [Ab Lb]; exact (bgeo_of b Ab Lb)
                                             | | | exact NDE | | exact CE].
          + intros b x Hb Hx NL. apply OUT. fold tlast in NL. pose proof (INE b Hb) as Ab.
            destruct (NDo (ba_addr b) ltac:(right; right; apply in_map; exact Hb)) as [Q1 Q2].
            destruct (Z.eq_dec (ba_addr b) tlast) as [Et | Nt].
            * (* [comment removed for export] *)
              (lazymatch goal with |- ?G => let G' := eval unfold mg_foot in G in change_no_check G' end). intros F. destruct (Htl NZ) as ((T1a & T1b) & T2 & T3). rewrite Et in Hx.
              destruct F as [F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]];
                [clear - F Hx T2; lia | clear - F Hx T2 Hc; lia | clear - F Hx T3; lia | clear - F Hx T1a; lia | clear - F Hx T1a; lia | clear - F Hx T1b; lia
                | clear - F NL; lia | clear - F Hx T1b; lia | clear - F Hx T1b; lia].
            * exact (foot_other ca na (blen cur) ws lastv tsz tlast (ba_addr b) (U x) Ab Ac An ATl Q1 Q2 (fun _ => Nt) Hc Hx).
          + intros b Hb NEa. fold tlast in NEa |- *. exact (SEP _ _ (INE b Hb) (ATl NZ) NEa).
          + fold tlast. exact (fr_mg_tlnext m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl NZ).
        - split; [| exact I]. (lazymatch goal with |- ?G => let G' := eval unfold bcell in G in change_no_check G' end). change (ba_addr (bempty nxt)) with na. change (ba_bytes (bempty nxt)) with 8192. change (blen (bempty nxt)) with 0.
          split; [exact (fr_mg_nnext m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)|].
          split; [exact (fr_mg_nsize m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)|].
          split; [exact (fr_mg_ncount m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)|].
          intros j mn Hj. destruct j; discriminate Hj. }
      (* [comment removed for export] *)
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (len done + 1 + len tl) with (glen - 1) by ((lazymatch goal with |- ?G => let G' := eval unfold glen in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia).
        exact (fr_mg_glen m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl). }
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). change (ba_addr (bmerge cur nxt)) with ca. destruct tl as [|b3 tl'].
        - (lazymatch goal with |- ?G => let G' := eval cbn [lasta] in G in change_no_check G' end). apply (fr_mg_last m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl). reflexivity.
        - assert (NEt : b3 :: tl' <> []) by discriminate.
          assert (ELV : lastv = lasta (b3 :: tl') ca) by reflexivity.
          assert (NLV : lastv <> na).
          { intros EQx. destruct (NDo lastv) as [_ Q2]; [| exact (Q2 EQx)]. right. left. rewrite ELV. apply lasta_in0. exact NEt. }
          rewrite <- ELV. apply (rd8_eq m MM); [clear; lia | clear; lia | | exact Hlast].
          intros x Hx. apply OUT. (lazymatch goal with |- ?G => let G' := eval unfold mg_foot in G in change_no_check G' end). intros F.
          destruct F as [F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]];
            [clear - F Hx Gc1; lia | clear - F Hx Gc1 Hc; lia | clear - F Hx Gn1; lia | clear - F Hx; lia | exact (NLV (proj1 F)) | clear - F Hx HS; lia
            | destruct F as [NZ F]; destruct (Htl NZ) as ((T1 & _) & _); clear - F Hx T1; lia | clear - F Hx HS; lia | clear - F Hx HS; lia]. }
      (* [comment removed for export] *)
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). replace (len (E ++ [bempty nxt])) with (tsz + 1) by ((lazymatch goal with |- ?G => let G' := eval unfold tsz in G in change_no_check G' end); rewrite length_app; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia).
        exact (fr_mg_tsize m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl). }
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). destruct (Z.eq_dec tsz 0) as [Z0 | NZ].
        - assert (EE : E = []) by (apply length_zero_iff_nil; unfold tsz in Z0; clear - Z0; lia). rewrite EE. (lazymatch goal with |- ?G => let G' := eval cbn [app hda] in G in change_no_check G' end). change (ba_addr (bempty nxt)) with na.
          exact (fr_mg_tfirst m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl Z0).
        - assert (EH : hda (E ++ [bempty nxt]) 0 = hda E 0) by (destruct E as [|e0 E0]; [exfalso; apply NZ; reflexivity | reflexivity]). rewrite EH.
          unfold cells in Tfirst. rewrite atS in Tfirst |- * by (clear; lia).
          apply (rd8_eq m MM); [clear - HS; lia | clear - HS HSr; lia | | exact Tfirst].
          intros x Hx. apply OUT. (lazymatch goal with |- ?G => let G' := eval unfold mg_foot in G in change_no_check G' end). intros F.
          destruct F as [F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]];
            [clear - F Hx Gc2; lia | clear - F Hx Gc2 Hc; lia | clear - F Hx Gn2; lia | clear - F Hx HS; lia | clear - F Hx HS; lia | exact (NZ (proj1 F))
            | destruct F as [_ F]; destruct (Htl NZ) as ((_ & T1) & _); clear - F Hx T1; lia | clear - F Hx; lia | clear - F Hx; lia]. }
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). rewrite lasta_snoc. change (ba_addr (bempty nxt)) with na.
        exact (fr_mg_tlast m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl). }
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). replace (8192 * len (E ++ [bempty nxt])) with (8192 * tsz + 8192) by ((lazymatch goal with |- ?G => let G' := eval unfold tsz in G in change_no_check G' end); rewrite length_app; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia).
        exact (fr_mg_tbytes m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl). }
      (* [comment removed for export] *)
      split.
      { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb | [Hb | Hb]].
        - apply INA. apply in_app_iff. left. exact Hb.
        - subst b. split; [exact Ac|]. rewrite blen_merge. exact FIT.
        - apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [apply INA; apply in_app_iff; right; right; right; apply in_app_iff; left; exact Hb|].
          apply in_app_iff in Hb. destruct Hb as [Hb | [Hb | []]]; [apply INA; apply in_app_iff; right; right; right; apply in_app_iff; right; exact Hb|].
          subst b. split; [exact An | change (blen (bempty nxt)) with 0; clear; lia]. }
      split.
      { rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map] in G in change_no_check G' end). rewrite !map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map] in G in change_no_check G' end). change (ba_addr (bmerge cur nxt)) with ca. change (ba_addr (bempty nxt)) with na.
        apply (Permutation_NoDup (l := map ba_addr done ++ ca :: na :: map ba_addr tl ++ map ba_addr E)); [| exact ND'].
        apply Permutation_app_head. apply perm_skip. rewrite app_assoc. apply Permutation_cons_append. }
      split.
      { intros b [Hb | Hb]; [subst b; rewrite ba_bytes_merge; fold s1 s2; clear - Zc Zn; (lazymatch goal with |- ?G => let G' := eval unfold s1, s2 in G in change_no_check G' end); lia | apply SZ; right; right; exact Hb]. }
      split; [rewrite ba_bytes_merge; fold s1 s2; clear - TOT Zc Zn; unfold s1, s2 in *; lia|].
      rewrite length_app. cbn [length] in *. clear - LEN. lia. }
    split; [| split; [exact GRM | exact (fr_mg_glen_def m S ca na (blen cur) s1 s2 nn glen lastv tsz tlast (8192 * tsz) ws HS Hc HcurU HnxtU Hsep Htl)]].
    intros x NF. apply OUT. intros F. apply NF. exact (foot_sub ca na (blen cur) ws lastv tsz tlast (U x) Ac An ATl Hc F).
  Qed.

  (* [comment removed for export] *)
  Definition mg_fin (G' E' : list batch) (m m' : word -> option byte) : Prop :=
    mem_grows m m' /\ (forall x : word, ~ mg_footL (U x) -> m' x = m x)
    /\ chainR m' G' 0 /\ chainR m' E' 0
    /\ cellq m' (IBq + 888) (len G') /\ cellq m' (IBq + 904) (lasta G' 0)
    /\ cells m' (-2288) (len E') /\ cells m' (-2280) (hda E' 0) /\ cells m' (-2272) (lasta E' 0) /\ cells m' (-2264) (8192 * len E').

  Lemma inv_fin : forall done cur E m, mg_inv done cur [] E m -> mg_fin (done ++ [cur]) E m m.
  Proof using.
    intros done cur E m (GR & CD & CC & CL & CE & Hlen & Hlast & Tsz & Tfirst & Tlast & Tb & _).
    (lazymatch goal with |- ?G => let G' := eval unfold mg_fin in G in change_no_check G' end). split; [apply mem_grows_refl|]. split; [intros x _; reflexivity|].
    split; [apply chainR_app; split; [exact CD | (lazymatch goal with |- ?G => let G' := eval cbn [chainR hda] in G in change_no_check G' end); split; [exact CC | exact I]]|].
    split; [exact CE|].
    split; [replace (len (done ++ [cur])) with (len done + 1 + len []); [exact Hlen | rewrite length_app; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia]|].
    split; [rewrite lasta_snoc; exact Hlast|].
    split; [exact Tsz|]. split; [exact Tfirst|]. split; [exact Tlast | exact Tb].
  Qed.

  Theorem mg_loop : forall l done cur E m (regs : bvmap 5 word),
    l <> [] -> mg_inv done cur l E m -> mg_keep S regs regs -> mg_head regs (ba_addr cur) (hda l 0) (8192 * len E) ->
    exists r m', msteps BSEGS (mkst regs (0x4e620 : word) m rom) (mkst r (0x4e704 : word) m' rom)
      /\ mg_keep S regs r /\ getr r 12 = Z_to_bv 64 (8192 * len (E ++ snd (mergeF cur l)))
      /\ mg_fin (done ++ fst (mergeF cur l)) (E ++ snd (mergeF cur l)) m m'
      /\ (snd (mergeF cur l) <> [] -> forall x : word, IBq + 888 <= U x < IBq + 896 -> m' x <> None).
  Proof using WRS WR0 SEP GEO HS.
    induction l as [|nxt tl IH]; intros done cur E m regs NE INV HK HH; [exfalso; exact (NE eq_refl)|].
    cbn [hda] in HH.
    assert (TLZ : forall done' cur' E' m', mg_inv done' cur' tl E' m' -> (hda tl 0 =? 0) = match tl with [] => true | _ => false end).
    { intros done' cur' E' m' (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INA' & _). destruct tl as [|b3 tl']; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end).
      destruct (INA' b3 ltac:(apply in_app_iff; right; right; left; reflexivity)) as [A3 _]. destruct (GEO _ A3) as [G1 _]. apply Z.eqb_neq. clear - G1. lia. }
    (lazymatch goal with |- ?G => let G' := eval cbn [mergeF] in G in change_no_check G' end). destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [FIT | BIG].
    - (* [comment removed for export] *)
      destruct (merge_step done cur nxt tl E m regs INV FIT HK HH) as (r1 & m1 & RUN1 & K1 & H1 & INV1 & FR1 & GR1 & DEF1).
      rewrite (TLZ _ _ _ _ INV1) in RUN1. destruct (mergeF (bmerge cur nxt) tl) as [g e] eqn:EMF. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      destruct tl as [|b3 tl'].
      + cbn [mergeF] in EMF. injection EMF as <- <-. exists r1, m1. split; [exact RUN1|]. split; [exact K1|].
        split; [destruct H1 as (_ & _ & A12 & _); exact A12|].
        destruct (inv_fin _ _ _ _ INV1) as (_ & _ & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
        split; [| intros _; exact DEF1].
        (lazymatch goal with |- ?G => let G' := eval unfold mg_fin in G in change_no_check G' end). split; [exact GR1|]. split; [exact FR1|]. repeat (split; [assumption|]). assumption.
      + destruct (IH done (bmerge cur nxt) (E ++ [bempty nxt]) m1 r1 ltac:(discriminate) INV1 (mg_keep_self _ _ K1) H1) as (r2 & m2 & RUN2 & K2 & A12 & FIN2 & _).
        rewrite EMF in A12, FIN2. cbn [fst snd] in A12, FIN2. rewrite <- app_assoc in A12, FIN2. cbn [app] in A12, FIN2.
        exists r2, m2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact (mg_keep_trans _ _ _ _ K1 K2)|]. split; [exact A12|].
        destruct FIN2 as (G2 & FR2 & REST).
        split; [| intros _ x Hx; apply G2; exact (DEF1 x Hx)].
        (lazymatch goal with |- ?G => let G' := eval unfold mg_fin in G in change_no_check G' end). split; [eapply mem_grows_trans; [exact GR1 | exact G2]|].
        split; [intros x NF; rewrite (FR2 x NF); exact (FR1 x NF) | exact REST].
    - (* [comment removed for export] *)
      destruct (adv_step done cur nxt tl E m regs INV BIG HK HH) as (r1 & RUN1 & K1 & H1 & INV1).
      rewrite (TLZ _ _ _ _ INV1) in RUN1. destruct (mergeF nxt tl) as [g e] eqn:EMF. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      destruct tl as [|b3 tl'].
      + cbn [mergeF] in EMF. injection EMF as <- <-. exists r1, m. split; [exact RUN1|]. split; [exact K1|].
        split; [rewrite app_nil_r; destruct H1 as (_ & _ & A12 & _); exact A12|].
        split; [| intros NEe; exfalso; exact (NEe eq_refl)].
        pose proof (inv_fin _ _ _ _ INV1) as FIN. rewrite <- app_assoc in FIN. cbn [app] in FIN. rewrite app_nil_r. exact FIN.
      + destruct (IH (done ++ [cur]) nxt E m r1 ltac:(discriminate) INV1 (mg_keep_self _ _ K1) H1) as (r2 & m2 & RUN2 & K2 & A12 & FIN2 & DEF2).
        rewrite EMF in A12, FIN2, DEF2. cbn [fst snd] in A12, FIN2, DEF2. rewrite <- app_assoc in FIN2. cbn [app] in FIN2.
        exists r2, m2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact (mg_keep_trans _ _ _ _ K1 K2)|]. split; [exact A12|].
        split; [exact FIN2 | exact DEF2].
  Qed.
End MGLOOP.
End BoAllocFRcM2.
Module BoAllocFRcM3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.BoAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58%Z (only parsing).

Section FPGen.
Context {fx : FPState}.

Section RCPREM.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v a2v a3v : word).
  Variables (minsz glen gqb : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (IBq + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hmin : (0 <= minsz < 2 ^ 64)%Z.
  Hypothesis Hglen : (0 <= glen < 2 ^ 28)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 41)%Z.
  Hypothesis Hmerge : (8192 * glen < gqb /\ 100 * gqb < 1638400 * glen)%Z.     (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2288)) 80 = true.
  Hypothesis Rlock : rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis Rglen : rdn BSEGS mem (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn BSEGS mem (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).

  (* [comment removed for export] *)
  Definition rc_m_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x4e4ac /\ getr r 2 = at_ S (-2288) /\ getr r 10 = Z_to_bv 64 (IBq + 888) /\ getr r 11 = at_ S (-2288)
      /\ getr r 8 = Z_to_bv 64 (IBq + 888) /\ getr r 9 = Z_to_bv 64 minsz /\ getr r 18 = Z_to_bv 64 (IBq + 728) /\ getr r 19 = a3v /\ getr r 20 = a2v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma rc_pre_m :
    exists r,
      msteps BSEGS (mkst regs (0x4e404 : word) mem rom) (mkst r (0x4e5e8 : word) (fr_rc0 mem S ra0 s0v s1v s2v s3v s4v b1 b2 b3) rom)
      /\ rc_m_regs r.
  Proof using Rgqb Rglen Rlock Hstk Hmerge Hgqb Hglen HS H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 gqb glen.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_m_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - an F_4e404 D_4e404.                              (* [comment removed for export] *)
      fsd F_4e408 D_4e408 (at_ S (-2216)).             (* [comment removed for export] *)
      fsd F_4e40c D_4e40c (at_ S (-2224)).             (* [comment removed for export] *)
      fsd F_4e410 D_4e410 (at_ S (-2232)).             (* [comment removed for export] *)
      fsd F_4e414 D_4e414 (at_ S (-2240)).             (* [comment removed for export] *)
      fsd F_4e418 D_4e418 (at_ S (-2248)).             (* [comment removed for export] *)
      fsd F_4e41c D_4e41c (at_ S (-2256)).             (* [comment removed for export] *)
      fsd F_4e420 D_4e420 (at_ S (-2288)).             (* [comment removed for export] *)
      fsd F_4e424 D_4e424 (at_ S (-2280)).             (* [comment removed for export] *)
      fsd F_4e428 D_4e428 (at_ S (-2272)).             (* [comment removed for export] *)
      fsd F_4e42c D_4e42c (at_ S (-2264)).             (* [comment removed for export] *)
      an F_4e430 D_4e430.                              (* [comment removed for export] *)
      an F_4e434 D_4e434.                              (* [comment removed for export] *)
      an F_4e438 D_4e438.                              (* [comment removed for export] *)
      an F_4e43c D_4e43c.                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (recycle_lock_4e440 _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]
      | ].
      av F_4e45c D_4e45c (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4e460 D_4e460 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e464 D_4e464 (Z_to_bv 64 gqb) Rgqb.      (* [comment removed for export] *)
      cld8 F_4e468 D_4e468 (Z_to_bv 64 glen) Rglen.    (* [comment removed for export] *)
      av F_4e46c D_4e46c (Z_to_bv 64 (8192 * glen)) ltac:(valz).  (* [comment removed for export] *)
      ab_ft F_4e470 D_4e470 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4e474 D_4e474 ltac:(condz).              (* [comment removed for export] *)
      an F_4e478 D_4e478.                              (* [comment removed for export] *)
      an F_4e47c D_4e47c.                              (* [comment removed for export] *)
      av F_4e480 D_4e480 (Z_to_bv 64 (1638400 * glen)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_4e484 D_4e484 (Z_to_bv 64 (100 * gqb)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).        (* [comment removed for export] *)
      ab_ft F_4e488 D_4e488 ltac:(condz).              (* [comment removed for export] *)
      av F_4e48c D_4e48c (Z_to_bv 64 (IBq + 888)) ltac:(valz).    (* [comment removed for export] *)
      an F_4e490 D_4e490.                              (* [comment removed for export] *)
      an F_4e494 D_4e494.                              (* [comment removed for export] *)
      an F_4e498 D_4e498.                              (* [comment removed for export] *)
      an F_4e49c D_4e49c.                              (* [comment removed for export] *)
      an F_4e4a0 D_4e4a0.                              (* [comment removed for export] *)
      an F_4e4a4 D_4e4a4.                              (* [comment removed for export] *)
      an F_4e4a8 D_4e4a8.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_rc0 mem S ra0 s0v s1v s2v s3v s4v b1 b2 b3). wd_refl.
    - post.
  Qed.
End RCPREM.

Section RCPOSTM.
  Variables (mem rom : word -> option byte) (S a2v a3v : word) (minsz glen : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 (IBq + 888).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 minsz.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 (IBq + 728).
  Hypothesis H19 : getr regs 19 = a3v.
  Hypothesis H20 : getr regs 20 = a2v.
  Hypothesis Rglen : rdn BSEGS mem (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).

  Lemma rc_post_m :
    exists r, msteps BSEGS (mkst regs (0x4e4ac : word) mem rom) (mkst r (0x4e4c0 : word) mem rom)
      /\ getr r 2 = at_ S (-2288) /\ getr r 10 = Z_to_bv 64 (IBq + 728) /\ getr r 11 = Z_to_bv 64 minsz /\ getr r 12 = a2v /\ getr r 13 = a3v
      /\ getr r 16 = Z_to_bv 64 glen
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20.
  Proof using Rglen H20 H19 H18 H9 H8 H2.
    wd_eexists. split.
    - an F_4e4ac D_4e4ac.                              (* [comment removed for export] *)
      an F_4e4b0 D_4e4b0.                              (* [comment removed for export] *)
      an F_4e4b4 D_4e4b4.                              (* [comment removed for export] *)
      an F_4e4b8 D_4e4b8.                              (* [comment removed for export] *)
      cld8 F_4e4bc D_4e4bc (Z_to_bv 64 glen) Rglen.    (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End RCPOSTM.

Section RCHEADG.
  Variables (mem rom : word -> option byte) (S : word) (minsz gqb first tsz tlast : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (IBq + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hmin : (0 <= minsz < 2 ^ 64)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 41)%Z.
  Hypothesis Rt0 : rdn BSEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 tsz)).
  Hypothesis Rt16 : rdn BSEGS mem (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 tlast)).
  Hypothesis Rgqb : rdn BSEGS mem (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rfirst : rdn BSEGS mem (Z_to_bv 64 (IBq + 896)) 8 = Some (LE8 (Z_to_bv 64 first)).

  Lemma rc_head_none_g : (gqb <= minsz)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e4c0 : word) mem rom) (mkst r (0x4e55c : word) mem rom) /\ rc_keep regs r.
  Proof using Rgqb Rt16 Rt0 Hgqb Hmin H11 H10 H2 tlast tsz S.
    intros Hle. (lazymatch goal with |- ?G => let G' := eval unfold rc_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e4c0 D_4e4c0 (Z_to_bv 64 tsz) Rt0.       (* [comment removed for export] *)
      cld8 F_4e4c4 D_4e4c4 (Z_to_bv 64 tlast) Rt16.    (* [comment removed for export] *)
      cld8 F_4e4c8 D_4e4c8 (Z_to_bv 64 gqb) Rgqb.      (* [comment removed for export] *)
      ab_tk F_4e4cc D_4e4cc ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  Lemma rc_head_loop_g : (minsz < gqb)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e4c0 : word) mem rom) (mkst r (0x4e500 : word) mem rom) /\ rc_keep regs r
      /\ getr r 14 = Z_to_bv 64 tsz /\ getr r 15 = Z_to_bv 64 tlast /\ getr r 5 = Z_to_bv 64 first /\ getr r 16 = getr regs 16.
  Proof using Rfirst Rgqb Rt16 Rt0 Hgqb Hmin H11 H10 H2 S.
    intros Hlt. (lazymatch goal with |- ?G => let G' := eval unfold rc_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e4c0 D_4e4c0 (Z_to_bv 64 tsz) Rt0.
      cld8 F_4e4c4 D_4e4c4 (Z_to_bv 64 tlast) Rt16.
      cld8 F_4e4c8 D_4e4c8 (Z_to_bv 64 gqb) Rgqb.
      ab_ft F_4e4cc D_4e4cc ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e4d0 D_4e4d0 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      an F_4e4d4 D_4e4d4.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End RCHEADG.
End FPGen.
End BoAllocFRcM3.
Module BoAllocFRcM4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 BoAllocFRcM2.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma q_bytes_appM : forall q1 q2, q_bytes (q1 ++ q2) = q_bytes q1 + q_bytes q2.
Proof. induction q1 as [|b r IH]; intros q2; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). change (q_bytes (b :: r ++ q2)) with (ba_bytes b + q_bytes (r ++ q2)).
  change (q_bytes (b :: r)) with (ba_bytes b + q_bytes r). rewrite IH. lia. Qed.

Lemma mf_bytes : forall l cur, q_bytes (fst (mergeF cur l)) + 8192 * Z.of_nat (length (snd (mergeF cur l))) = ba_bytes cur + q_bytes l.
Proof.
  induction l as [|nxt tl IH]; intros cur; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [mergeF] in G in change_no_check G' end). change (q_bytes (nxt :: tl)) with (ba_bytes nxt + q_bytes tl).
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt)). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd length] in *. rewrite ba_bytes_merge in IH. lia.
  - specialize (IH nxt). destruct (mergeF nxt tl) as [g e]. cbn [fst snd] in *. change (q_bytes (cur :: g)) with (ba_bytes cur + q_bytes g). lia.
Qed.
Lemma mf_items : forall l cur, flat_map ba_items (fst (mergeF cur l)) = flat_map ba_items (cur :: l).
Proof.
  induction l as [|nxt tl IH]; intros cur; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [mergeF] in G in change_no_check G' end).
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt)). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd] in *. rewrite IH. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map bmerge ba_items] in G in change_no_check G' end).
    rewrite <- app_assoc. reflexivity.
  - specialize (IH nxt). destruct (mergeF nxt tl) as [g e]. cbn [fst snd] in *. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map] in G in change_no_check G' end). rewrite IH. reflexivity.
Qed.
Lemma mf_empties : forall l cur b, In b (snd (mergeF cur l)) -> ba_items b = [].
Proof.
  induction l as [|nxt tl IH]; intros cur b Hb; [destruct Hb|]. cbn [mergeF] in Hb.
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt) b). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd] in *. destruct Hb as [<- | Hb]; [reflexivity | exact (IH Hb)].
  - specialize (IH nxt b). destruct (mergeF nxt tl) as [g e]. cbn [fst snd] in *. exact (IH Hb).
Qed.
Lemma mf_items_all : forall l cur, flat_map ba_items (snd (mergeF cur l) ++ fst (mergeF cur l)) = flat_map ba_items (cur :: l).
Proof.
  intros l cur. rewrite flat_map_app, mf_items.
  assert (E0 : flat_map ba_items (snd (mergeF cur l)) = []).
  { pose proof (mf_empties l cur) as ME. induction (snd (mergeF cur l)) as [|b r IHr]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [flat_map] in G in change_no_check G' end).
    rewrite (ME b (or_introl eq_refl)), IHr; [reflexivity | intros b0 Hb0; apply ME; right; exact Hb0]. }
  rewrite E0. reflexivity.
Qed.
Lemma mf_addrs : forall l cur, Permutation (map ba_addr (snd (mergeF cur l) ++ fst (mergeF cur l))) (map ba_addr (cur :: l)).
Proof.
  induction l as [|nxt tl IH]; intros cur; [apply Permutation_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [mergeF] in G in change_no_check G' end).
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt)). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd] in *. (lazymatch goal with |- ?G => let G' := eval cbn [app map] in G in change_no_check G' end).
    change (ba_addr (bempty nxt)) with (ba_addr nxt). change (ba_addr (bmerge cur nxt)) with (ba_addr cur) in IH. cbn [map] in IH.
    eapply perm_trans; [apply perm_skip; exact IH|]. apply perm_swap.
  - specialize (IH nxt). destruct (mergeF nxt tl) as [g e]. cbn [fst snd] in *. rewrite map_app in *. cbn [map] in *.
    eapply perm_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. exact IH.
Qed.
Lemma mf_head : forall l cur d, hda (fst (mergeF cur l)) d = ba_addr cur.
Proof.
  induction l as [|nxt tl IH]; intros cur d; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [mergeF] in G in change_no_check G' end).
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt) d). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd] in *. exact IH.
  - destruct (mergeF nxt tl) as [g e]. reflexivity.
Qed.
Lemma mf_nonempty : forall l cur, fst (mergeF cur l) <> [].
Proof.
  induction l as [|nxt tl IH]; intros cur; [discriminate|]. (lazymatch goal with |- ?G => let G' := eval cbn [mergeF] in G in change_no_check G' end).
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt)). destruct (mergeF (bmerge cur nxt) tl) as [g e]. exact IH.
  - destruct (mergeF nxt tl) as [g e]. discriminate.
Qed.
(* [comment removed for export] *)
Lemma mf_forall : forall (PA : Z -> Prop) (PI : Z * Z -> Prop) l cur,
  (forall b, In b (cur :: l) -> PA (ba_addr b) /\ (forall it, In it (ba_items b) -> PI it) /\ blen b <= 1021) ->
  forall b, In b (snd (mergeF cur l) ++ fst (mergeF cur l)) -> PA (ba_addr b) /\ (forall it, In it (ba_items b) -> PI it) /\ 0 <= blen b <= 1021.
Proof.
  intros PA PI. induction l as [|nxt tl IH]; intros cur H b Hb.
  - cbn in Hb. destruct Hb as [<- | []]. destruct (H cur (or_introl eq_refl)) as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2 | unfold blen in *; lia].
  - cbn [mergeF] in Hb. destruct (H cur (or_introl eq_refl)) as (C1 & C2 & C3). destruct (H nxt (or_intror (or_introl eq_refl))) as (N1 & N2 & N3).
    destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
    + specialize (IH (bmerge cur nxt)). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd] in *. cbn [app] in Hb. destruct Hb as [<- | Hb].
      * split; [exact N1|]. split; [intros it []|]. change (blen (bempty nxt)) with 0. lia.
      * apply IH; [| exact Hb]. intros b0 [<- | Hb0].
        -- split; [exact C1|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn [bmerge ba_items] in G in change_no_check G' end); intros it Hit; apply in_app_iff in Hit; destruct Hit as [Hit | Hit]; [exact (C2 it Hit) | exact (N2 it Hit)]|].
           rewrite blen_merge. exact F.
        -- apply H. right. right. exact Hb0.
    + specialize (IH nxt). destruct (mergeF nxt tl) as [g e]. cbn [fst snd] in *. apply in_app_iff in Hb. destruct Hb as [Hb | [<- | Hb]].
      * apply IH; [intros b0 Hb0; apply H; right; exact Hb0 | apply in_app_iff; left; exact Hb].
      * split; [exact C1|]. split; [exact C2 | unfold blen in *; lia].
      * apply IH; [intros b0 Hb0; apply H; right; exact Hb0 | apply in_app_iff; right; exact Hb].
Qed.
Lemma mf_sz : forall l cur, (forall b, In b (cur :: l) -> 8192 <= ba_bytes b) -> forall b, In b (fst (mergeF cur l)) -> 8192 <= ba_bytes b.
Proof.
  induction l as [|nxt tl IH]; intros cur H b Hb; [cbn in Hb; destruct Hb as [<- | []]; apply H; left; reflexivity|].
  cbn [mergeF] in Hb. pose proof (H cur (or_introl eq_refl)) as Zc. pose proof (H nxt (or_intror (or_introl eq_refl))) as Zn.
  destruct (Z.leb_spec (blen cur + blen nxt) 1021) as [F | B].
  - specialize (IH (bmerge cur nxt)). destruct (mergeF (bmerge cur nxt) tl) as [g e]. cbn [fst snd] in *. apply IH; [| exact Hb].
    intros b0 [<- | Hb0]; [rewrite ba_bytes_merge; lia | apply H; right; right; exact Hb0].
  - specialize (IH nxt). destruct (mergeF nxt tl) as [g e]. cbn [fst snd] in *. destruct Hb as [<- | Hb]; [exact Zc|].
    apply IH; [intros b0 Hb0; apply H; right; exact Hb0 | exact Hb].
Qed.
End BoAllocFRcM4.
Module BoAllocFRcR1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L BoAllocFRc2 BoAllocFRc2U.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58 (only parsing).

Section FPGen.
Context {fx : FPState}.

Ltac lsideR := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.

Section RC0MEM.
  Variables (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (b1 b2 b3 : byte).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  #[local] Abbreviation Ma := (fr_rc0 mem S ra0 s0v s1v s2v s3v s4v b1 b2 b3).

  Lemma fr_rc0_outside : forall a : word, (U a < U S - 2288 \/ U S - 2208 <= U a) -> (U a < 0x10aec8 \/ 0x10aecc <= U a) -> Ma a = mem a.
  Proof using HS. intros a A1 A2. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_rc0 in G in change_no_check G' end). rewrite !wbytes_outside by lsideR. reflexivity. Qed.
  Lemma fr_rc0_grows : mem_grows mem Ma.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_rc0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Ltac rdR := pose proof (u64_range S) as HSr; (lazymatch goal with |- ?G => let G' := eval unfold fr_rc0 in G in change_no_check G' end); repeat (wd_rdstep rd8_side).
  Lemma fr_rc0_ra : rdn BSEGS Ma (at_ S (-2216)) 8 = Some (LE8 ra0).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_s0 : rdn BSEGS Ma (at_ S (-2224)) 8 = Some (LE8 s0v).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_s1 : rdn BSEGS Ma (at_ S (-2232)) 8 = Some (LE8 s1v).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_s2 : rdn BSEGS Ma (at_ S (-2240)) 8 = Some (LE8 s2v).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_s3 : rdn BSEGS Ma (at_ S (-2248)) 8 = Some (LE8 s3v).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_s4 : rdn BSEGS Ma (at_ S (-2256)) 8 = Some (LE8 s4v).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_t0 : rdn BSEGS Ma (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 0)).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_t16 : rdn BSEGS Ma (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 0)).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_sum : rdn BSEGS Ma (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 0)).  Proof using HS. rdR. Qed.
  Lemma fr_rc0_lock : Ma (Z_to_bv 64 0x10aeca) = Some b2 /\ Ma (Z_to_bv 64 0x10aecb) = Some b3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_rc0 in G in change_no_check G' end). split; rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia); unorm; reflexivity. Qed.
End RC0MEM.

Section RCUMEM.
  Variable mem : word -> option byte.
  Lemma fr_rcu_outside : forall a : word, (U a < 0x10aec8 \/ 0x10aeca <= U a) -> fr_rcu mem a = mem a.
  Proof using. intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold fr_rcu in G in change_no_check G' end). rewrite !wbytes_outside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). reflexivity. Qed.
  Lemma fr_rcu_grows : mem_grows mem (fr_rcu mem).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_rcu in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma fr_rcu_lock : fr_rcu mem (Z_to_bv 64 0x10aec8) = Some (Z_to_bv 8 0) /\ fr_rcu mem (Z_to_bv 64 0x10aec9) = Some (Z_to_bv 8 0).
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_rcu in G in change_no_check G' end). split.
    - rewrite wbytes_outside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. reflexivity.
    - rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. reflexivity.
  Qed.
End RCUMEM.

Section RUNPRE.
  Variables (memD rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word).
  Variables (minsz glen gqb first : Z) (b2 b3 : byte) (l : list ptrip).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (IBq + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Hmin : 0 <= minsz < 2 ^ 64.
  Hypothesis Hglen : 0 <= glen < 2 ^ 28.
  Hypothesis Hgqb : 0 <= gqb < 2 ^ 41.
  Hypothesis Hover : 8192 * glen <= gqb.
  Hypothesis Hnomerge : gqb <= 8192 * glen \/ 1638400 * glen <= 100 * gqb.
  Hypothesis Hfirst : 0 <= first < 2 ^ 64.
  Hypothesis Hlt : minsz < gqb.
  Hypothesis POK : pops_ok minsz first gqb l.
  Hypothesis Hlen : Z.of_nat (length l) <= glen.
  Hypothesis GEO : Forall (fun t => AIMGHI <= p_addr t /\ p_addr t + 8192 <= U S - 3584) l.
  Hypothesis SEP : all_sep (map p_addr l).
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2400)) 192 = true.
  Hypothesis SOKL : Forall (fun t => store_ok BSEGS memD (Z_to_bv 64 (p_addr t)) 8 = true) l.
  Hypothesis Rlock : rdn BSEGS memD (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3].
  Hypothesis Rglen : rdn BSEGS memD (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn BSEGS memD (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rfirst : rdn BSEGS memD (Z_to_bv 64 (IBq + 896)) 8 = Some (LE8 (Z_to_bv 64 first)).
  Hypothesis CELLS : Forall (fun t => rdn BSEGS memD (Z_to_bv 64 (p_addr t)) 8 = Some (LE8 (Z_to_bv 64 (p_nx t)))
                                      /\ rdn BSEGS memD (Z_to_bv 64 (p_addr t + 8)) 8 = Some (LE8 (Z_to_bv 64 (p_sz t)))) l.

  #[local] Abbreviation Ma := (fr_rc0 memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3).

  Theorem run_rc_pre :
    exists r mem',
      msteps BSEGS (mkst regs (0x4e404 : word) memD rom)
                   (mkst r (0x4e7e4 : word) (fr_dr0 (fr_rcu mem') S (Z_to_bv 64 0x4e574) s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v) rom)
      /\ pop_post S 0 0 glen gqb 0 l Ma mem'
      /\ dr_regs S r /\ getr r 10 = Z_to_bv 64 (Z.of_nat (length l))
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using CELLS Rfirst Rgqb Rglen Rlock SOKL Hstk SEP GEO Hlen POK Hlt Hnomerge Hover Hgqb Hglen Hmin HS H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 first minsz.
    pose proof (u64_range S) as HSr.
    assert (Hstk80 : store_ok BSEGS memD (at_ S (-2288)) 80 = true).
    { eapply (store_ok_sub BSEGS memD (at_ S (-2400)) _ 192); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (rc_pre memD rom S ra0 s0v s1v s2v s3v s4v a2v a3v minsz glen gqb (Z_to_bv 8 1) b2 b3 regs H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 HS Hglen Hgqb Hover Hnomerge
                Hstk80 Rlock Rglen Rgqb)
      as (r1 & RUN1 & (A2 & A10 & A11 & A12 & A13 & A8 & A9 & A18 & A19 & A20 & A3 & A4 & A21 & A22 & A23 & A24 & A25 & A26 & A27) & A16).
    pose proof (fr_rc0_grows memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3) as GRa.
    assert (OUTa : forall c bs, (c + 8 <= 0x10aec8 \/ 0x10aecc <= c) -> 0 <= c -> c + 8 <= U S - 2288 -> rdn BSEGS memD (Z_to_bv 64 c) 8 = Some bs -> rdn BSEGS Ma (Z_to_bv 64 c) 8 = Some bs).
    { intros c bs Hc H0 Hc2 Hr. eapply rd_same; [| wd_ulia_c | exact Hr].
      intros x Hx. apply (fr_rc0_outside memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
    assert (Rgqb' : rdn BSEGS Ma (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb))) by (apply OUTa; [lia | lia | lia | exact Rgqb]).
    assert (Rfirst' : rdn BSEGS Ma (Z_to_bv 64 (IBq + 896)) 8 = Some (LE8 (Z_to_bv 64 first))) by (apply OUTa; [lia | lia | lia | exact Rfirst]).
    destruct (rc_head_loop Ma rom S minsz gqb first r1 A2 A10 A11 Hmin Hgqb
                (fr_rc0_t0 memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS) (fr_rc0_t16 memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS) Rgqb' Rfirst' Hlt)
      as (r2 & RUN2 & KP2 & B14 & B15 & B5 & B16).
    pose proof KP2 as (C2 & C10 & C11 & C12 & C13 & C8 & C9 & C18 & C19 & C20 & C3 & C4 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
    pose proof (pops_tot minsz l first gqb POK) as PT.
    destruct (rc_pop_loop rom S minsz HS Hmin l r2 Ma 0 0 glen gqb 0 first POK
                ltac:(rewrite C2; exact A2) ltac:(rewrite C10; exact A10) ltac:(rewrite C11; exact A11) B14 B15 ltac:(rewrite B16; exact A16) B5
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (r3 & mem' & RUN3 & KP3 & PP).
    { exact GEO. }
    { exact SEP. }
    { intros N. exfalso. exact (N eq_refl). }
    { eapply store_ok_mono; [exact GRa | exact Hstk80]. }
    { eapply Forall_impl; [| exact SOKL]. intros t Ht. eapply store_ok_mono; [exact GRa | exact Ht]. }
    { intros N. exfalso. exact (N eq_refl). }
    { rewrite Forall_forall in CELLS, GEO |- *. intros t Ht. destruct (CELLS t Ht) as [Cn Cs]. destruct (GEO t Ht) as [G1 G2].
      split; apply OUTa; try lia; assumption. }
    { exact Rgqb'. }
    { exact (fr_rc0_sum memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS). }
    pose proof KP3 as (D2 & D10 & D11 & D12 & D13 & D8 & D9 & D18 & D19 & D20 & D3 & D4 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
    destruct (rc_unlock_call mem' rom S r3 ltac:(rewrite D2, C2; exact A2) ltac:(rewrite D10, C10; exact A10))
      as (r4 & RUN4 & (E2 & E10 & E12 & E13 & E8 & E9 & E18 & E19 & E20 & E3 & E4 & E21 & E22 & E23 & E24 & E25 & E26 & E27) & E1 & E11).
    destruct PP as (PO & PG' & Pfirst & Plast & Plen & Pbytes & Ptsz & Ptlast & Psum & Ptfirst & Pprev & Pchain & Pdef).
    assert (GRu : mem_grows memD (fr_rcu mem')) by (eapply mem_grows_trans; [exact GRa | eapply mem_grows_trans; [exact PG' | apply fr_rcu_grows]]).
    assert (Rtsz : rdn BSEGS (fr_rcu mem') (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length l))))).
    { eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | replace (Z.of_nat (length l)) with (0 + Z.of_nat (length l)) by lia; exact Ptsz].
      intros x Hx. apply fr_rcu_outside. rewrite at_u in Hx by lia. cbn in Hx. lia. }
    destruct (dr_pre_loop (fr_rcu mem') rom S (Z_to_bv 64 0x4e574) s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v (Z.of_nat (length l)) r4 E1
                ltac:(rewrite E2, D2, C2; exact A2) E11 ltac:(rewrite E12, D12, C12; exact A12) ltac:(rewrite E13, D13, C13; exact A13)
                ltac:(rewrite E8, D8, C8; exact A8) ltac:(rewrite E9, D9, C9; exact A9) ltac:(rewrite E18, D18, C18; exact A18)
                ltac:(rewrite E19, D19, C19; exact A19) ltac:(rewrite E20, D20, C20; exact A20)
                ltac:(rewrite E21, D21, C21, A21; exact H21) ltac:(rewrite E22, D22, C22, A22; exact H22) ltac:(rewrite E23, D23, C23, A23; exact H23)
                ltac:(rewrite E24, D24, C24, A24; exact H24) ltac:(rewrite E25, D25, C25, A25; exact H25)
                HS ltac:(lia))
      as (r5 & RUN5 & HR5 & (F3 & F4 & F26 & F27) & F10).
    { eapply (store_ok_sub BSEGS (fr_rcu mem') (at_ S (-2400)) _ 192); [rewrite at_u; lia | eapply store_ok_mono; [exact GRu | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact Rtsz. }
    { destruct l; [contradiction | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia]. }
    exists r5, mem'. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4 | exact RUN5]. }
    split; [repeat split; assumption|]. split; [exact HR5|]. split; [exact F10|].
    split; [rewrite F3, E3, D3, C3; exact A3|]. split; [rewrite F4, E4, D4, C4; exact A4|].
    split; [rewrite F26, E26, D26, C26; exact A26 | rewrite F27, E27, D27, C27; exact A27].
  Qed.
End RUNPRE.
End FPGen.
End BoAllocFRcR1.
Module BoAllocFRcM5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L BoAllocFRc2 BoAllocFRcR1 BoAllocFRcK1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U BoAllocFRcM2 BoAllocFRcM3 BoAllocFRcM4.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58 (only parsing).

(* [comment removed for export] *)
Lemma chainR_nth : forall m q nx i b, chainR m q nx -> nth_error q i = Some b -> bcell m b (hda (skipn (Datatypes.S i) q) nx).
Proof.
  intros m q nx. induction q as [|b0 r IH]; intros i b C Hi; [destruct i; discriminate Hi|].
  cbn [chainR] in C. destruct C as [C0 C1]. destruct i as [|i]; [cbn in Hi; injection Hi as <-; (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end); exact C0|].
  cbn [nth_error] in Hi. (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end). exact (IH i b C1 Hi).
Qed.
Lemma hda_nxaddr : forall q, hda q 0 = nxaddr q.
Proof. intros [|b r]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma chainR_popped : forall k q (m m' : word -> option byte) nx,
  (forall b, In b (firstn k q) -> bgeo b) ->
  (forall b (x : word), In b (firstn k q) -> ba_addr b + 8 <= U x < ba_addr b + 8192 -> m' x = m x) ->
  chain_cells m' (trips q k) -> chainR m q nx -> chainR m' (firstn k q) 0.
Proof.
  induction k as [|k IH]; intros q m m' nx G EQ CC C; [exact I|]. destruct q as [|b q']; [exact I|].
  cbn [firstn trips chain_cells chainR] in *. destruct CC as [CC0 CC1]. destruct C as [C0 C1]. split.
  - apply (bcell_frame2 m m' b (hda q' nx)); [apply G; left; reflexivity | intros x Hx; apply (EQ b x (or_introl eq_refl) Hx) | | exact C0].
    cbn [p_addr fst] in CC0. replace (hda (firstn k q') 0) with (match trips q' k with [] => 0 | t' :: _ => p_addr t' end); [exact CC0|].
    destruct k as [|k']; destruct q' as [|b' q'']; reflexivity.
  - apply (IH q' m m' nx); [intros b0 Hb0; apply G; right; exact Hb0 | intros b0 x Hb0 Hx; apply (EQ b0 x (or_intror Hb0) Hx) | exact CC1 | exact C1].
Qed.

Section POPCHAIN.
  Variables (S : word) (E G : list batch) (k : nat) (glen B sum : Z) (m m' : word -> option byte).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Hk : (1 <= k <= length G)%nat.
  Hypothesis BG : forall b, In b (E ++ G) -> bgeo b.
  Hypothesis GEOA : forall a, In a (map ba_addr (E ++ G)) -> AIMGHI <= a /\ a + 8192 <= U S - 3584.
  Hypothesis SEPA : forall a1 a2, In a1 (map ba_addr (E ++ G)) -> In a2 (map ba_addr (E ++ G)) -> a1 <> a2 -> bsep a1 a2.
  Hypothesis ND : List.NoDup (map ba_addr (E ++ G)).
  Hypothesis CE : chainR m E 0.
  Hypothesis CG : chainR m G 0.
  Hypothesis PP : pop_post S (Z.of_nat (length E)) (lasta E 0) glen B sum (trips G k) m m'.

  #[local] Abbreviation P := (firstn k G).
  #[local] Abbreviation rest := (skipn k G).
  #[local] Abbreviation pl := (trips G k).

  Lemma lf_obj : forall a x, AIMGHI <= a /\ a + 8192 <= U S - 3584 -> a <= x < a + 8192 ->
    (forall t, In t pl -> ~ (p_addr t <= x < p_addr t + 8)) -> (Z.of_nat (length E) <> 0 -> ~ (lasta E 0 <= x < lasta E 0 + 8)) ->
    ~ loop_foot S (Z.of_nat (length E)) (lasta E 0) pl x.
  Proof using.
    intros a x [G1 G2] Hx C2 C3 F. unfold loop_foot in F.
    destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
      [clear - F Hx G1; lia | clear - F Hx G1; lia | clear - F Hx G1; lia | destruct F as (t & Ht & Hr); exact (C2 t Ht Hr)
      | destruct F as [NZ Hr]; exact (C3 NZ Hr) | clear - F Hx G2; lia | clear - F Hx G2; lia | clear - F Hx G2; lia].
  Qed.

  Lemma in_P_G : forall b, In b P -> In b G.  Proof using. intros b Hb. exact (firstn_InK _ _ _ Hb). Qed.
  Lemma in_rest_G : forall b, In b rest -> In b G.  Proof using. intros b Hb. exact (skipn_InK _ _ _ Hb). Qed.
  Lemma addr_in : forall b, In b (E ++ G) -> In (ba_addr b) (map ba_addr (E ++ G)).  Proof using. intros b Hb. apply in_map. exact Hb. Qed.
  Lemma pl_addr : forall t, In t pl -> exists b, In b P /\ p_addr t = ba_addr b.
  Proof using. intros t Ht. destruct (trips_in G k t Ht) as (b & Hb & Ea & _). exists b. split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma prev_in : Z.of_nat (length E) <> 0 -> In (lasta E 0) (map ba_addr E).
  Proof using. intros NZ. apply lasta_in0. intros EE. rewrite EE in NZ. exact (NZ eq_refl). Qed.

  Lemma ndE : List.NoDup (map ba_addr E).  Proof using ND G. rewrite map_app in ND. exact (NoDup_app_remove_r _ _ ND). Qed.
  Lemma ndG : List.NoDup (map ba_addr G).  Proof using ND E. rewrite map_app in ND. exact (NoDup_app_remove_l _ _ ND). Qed.
  Lemma ndEG : forall x, In x (map ba_addr E) -> In x (map ba_addr G) -> False.
  Proof using ND. intros x H1 H2. rewrite map_app in ND. exact (nd_app_disj _ _ x ND H1 H2). Qed.
  Lemma ndPR : forall x, In x (map ba_addr P) -> In x (map ba_addr rest) -> False.
  Proof using ND E. intros x H1 H2. pose proof ndG as N. rewrite <- (firstn_skipn k G), map_app in N. exact (nd_app_disj _ _ x N H1 H2). Qed.

  Lemma pop_chain : chainR m' (E ++ P) 0 /\ chainR m' rest 0.
  Proof using PP CG CE ND SEPA GEOA BG Hk m sum B glen S.
    destruct PP as (PO & PG' & Pfirst & Plast & Plen & Pbytes & Ptsz & Ptlast & Psum & Ptfirst & Pprev & Pchain & Pdef).
    assert (CGs : chainR m P (hda rest 0) /\ chainR m rest 0) by (apply chainR_app; rewrite firstn_skipn; exact CG).
    destruct CGs as [CP CR].
    assert (INPa : forall b, In b P -> In (ba_addr b) (map ba_addr (E ++ G))) by (intros b Hb; apply addr_in; apply in_app_iff; right; exact (in_P_G b Hb)).
    assert (INRa : forall b, In b rest -> In (ba_addr b) (map ba_addr (E ++ G))) by (intros b Hb; apply addr_in; apply in_app_iff; right; exact (in_rest_G b Hb)).
    assert (INEa : forall b, In b E -> In (ba_addr b) (map ba_addr (E ++ G))) by (intros b Hb; apply addr_in; apply in_app_iff; left; exact Hb).
    assert (PRVa : Z.of_nat (length E) <> 0 -> In (lasta E 0) (map ba_addr (E ++ G))).
    { intros NZ. rewrite map_app. apply in_app_iff. left. exact (prev_in NZ). }
    split.
    - apply chainR_app. split.
      + (* [comment removed for export] *)
        destruct (Z.eq_dec (Z.of_nat (length E)) 0) as [Z0 | NZ].
        { assert (EE : E = []) by (apply length_zero_iff_nil; clear - Z0; lia). rewrite EE. exact I. }
        apply (chainR_relink m m' E 0 (hda P 0)); [intros EE; apply NZ; rewrite EE; reflexivity | intros b Hb; apply BG; apply in_app_iff; left; exact Hb | | | exact ndE | | exact CE].
        * intros b x Hb Hx NL. apply PO. apply (lf_obj (ba_addr b) (U x) (GEOA _ (INEa b Hb)) Hx); [| intros _; exact NL].
          intros t Ht Hr. destruct (pl_addr t Ht) as (bp & Hbp & Ea). rewrite Ea in Hr.
          assert (NEa : ba_addr b <> ba_addr bp) by (intros EQa; apply (ndEG (ba_addr b)); [apply in_map; exact Hb | rewrite EQa; apply in_map; exact (in_P_G bp Hbp)]).
          pose proof (SEPA _ _ (INEa b Hb) (INPa bp Hbp) NEa) as SP. unfold bsep in SP. clear - SP Hx Hr. lia.
        * intros b Hb NEa. exact (SEPA _ _ (INEa b Hb) (PRVa NZ) NEa).
        * replace (hda P 0) with (match pl with [] => 0 | t :: _ => p_addr t end); [exact (Pprev NZ)|].
          rewrite trips_head; [| clear - Hk; lia | intros EG; rewrite EG in Hk; cbn in Hk; clear - Hk; lia].
          rewrite hda_nxaddr, nxaddr_firstn; [reflexivity | clear - Hk; lia].
      + (* [comment removed for export] *)
        apply (chainR_popped k G m m' 0); [intros b Hb; apply BG; apply in_app_iff; right; exact (in_P_G b Hb) | | exact Pchain | exact CG].
        intros b x Hb Hx. apply PO. apply (lf_obj (ba_addr b) (U x) (GEOA _ (INPa b Hb)) ltac:(clear - Hx; lia)).
        * intros t Ht Hr. destruct (pl_addr t Ht) as (bp & Hbp & Ea). rewrite Ea in Hr.
          destruct (Z.eq_dec (ba_addr b) (ba_addr bp)) as [EQa | NEa]; [rewrite <- EQa in Hr; clear - Hx Hr; lia|].
          pose proof (SEPA _ _ (INPa b Hb) (INPa bp Hbp) NEa) as SP. unfold bsep in SP. clear - SP Hx Hr. lia.
        * intros NZ Hr.
          assert (NEa : ba_addr b <> lasta E 0) by (intros EQa; apply (ndEG (lasta E 0)); [exact (prev_in NZ) | rewrite <- EQa; apply in_map; exact (in_P_G b Hb)]).
          pose proof (SEPA _ _ (INPa b Hb) (PRVa NZ) NEa) as SP. unfold bsep in SP. clear - SP Hx Hr. lia.
    - (* [comment removed for export] *)
      apply (chainR_frame m m'); [intros b Hb; apply BG; apply in_app_iff; right; exact (in_rest_G b Hb) | | exact CR].
      intros b x Hb Hx. apply PO. apply (lf_obj (ba_addr b) (U x) (GEOA _ (INRa b Hb)) Hx).
      + intros t Ht Hr. destruct (pl_addr t Ht) as (bp & Hbp & Ea). rewrite Ea in Hr.
        assert (NEa : ba_addr b <> ba_addr bp) by (intros EQa; apply (ndPR (ba_addr b)); [rewrite EQa; apply in_map; exact Hbp | apply in_map; exact Hb]).
        pose proof (SEPA _ _ (INRa b Hb) (INPa bp Hbp) NEa) as SP. unfold bsep in SP. clear - SP Hx Hr. lia.
      + intros NZ Hr.
        assert (NEa : ba_addr b <> lasta E 0) by (intros EQa; apply (ndEG (lasta E 0)); [exact (prev_in NZ) | rewrite <- EQa; apply in_map; exact (in_rest_G b Hb)]).
        pose proof (SEPA _ _ (INRa b Hb) (PRVa NZ) NEa) as SP. unfold bsep in SP. clear - SP Hx Hr. lia.
  Qed.
End POPCHAIN.

Lemma q_bytes_empties : forall E, (forall b, In b E -> ba_items b = []) -> q_bytes E = 8192 * Z.of_nat (length E).
Proof.
  induction E as [|b r IH]; intros H; [reflexivity|]. change (q_bytes (b :: r)) with (ba_bytes b + q_bytes r).
  rewrite IH by (intros b0 Hb0; apply H; right; exact Hb0). (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes, BATCHSZ in G in change_no_check G' end). rewrite (H b (or_introl eq_refl)). (lazymatch goal with |- ?G => let G' := eval cbn [fold_right length] in G in change_no_check G' end). lia.
Qed.
Lemma lasta_rev : forall q d, lasta q d = match rev q with [] => d | b :: _ => ba_addr b end.
Proof.
  induction q as [|b r IH]; intros d; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [lasta rev] in G in change_no_check G' end). rewrite IH. destruct (rev r) as [|b' r']; reflexivity.
Qed.

Section RUNPREM.
  Context {fx : FPState}.
  Variables (memD rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word).
  Variables (minsz : Z) (b2 b3 : byte) (cur : batch) (l : list batch) (A : list Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (IBq + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Hmin : 0 <= minsz < 2 ^ 64.
  #[local] Abbreviation len q := (Z.of_nat (@length batch q)).
  #[local] Abbreviation B0 := (ba_bytes cur + q_bytes l).
  Hypothesis NEl : l <> [].
  Hypothesis GLEN : 1 + len l < 2 ^ 28.
  Hypothesis TOT : B0 < 2 ^ 41.
  Hypothesis Hmerge : 8192 * (1 + len l) < B0 /\ 100 * B0 < 1638400 * (1 + len l).
  Hypothesis Hlt0 : minsz < B0.
  Hypothesis GEO : forall a, In a A -> AIMGHI <= a /\ a + 8192 <= U S - 3584.
  Hypothesis SEP : forall a1 a2, In a1 A -> In a2 A -> a1 <> a2 -> bsep a1 a2.
  Hypothesis INA : forall b, In b (cur :: l) -> In (ba_addr b) A /\ blen b <= 1021.
  Hypothesis ND : List.NoDup (map ba_addr (cur :: l)).
  Hypothesis SZ : forall b, In b (cur :: l) -> 8192 <= ba_bytes b.
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2400)) 192 = true.
  Hypothesis WRD : forall a k n, In a A -> 0 <= k -> k + Z.of_nat n <= 8192 -> store_ok BSEGS memD (Z_to_bv 64 (a + k)) n = true.
  Hypothesis Rlock : rdn BSEGS memD (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3].
  Hypothesis CH : chainR memD (cur :: l) 0.
  Hypothesis Rglen : cellq memD (IBq + 888) (1 + len l).
  Hypothesis Rfirst : cellq memD (IBq + 896) (ba_addr cur).
  Hypothesis Rlast : cellq memD (IBq + 904) (lasta l (ba_addr cur)).
  Hypothesis Rgqb : cellq memD (IBq + 912) B0.

  #[local] Abbreviation Ma := (fr_rc0 memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3).
  #[local] Abbreviation G' := (fst (mergeF cur l)).
  #[local] Abbreviation E' := (snd (mergeF cur l)).
  Definition mk (minsz : Z) (G : list batch) : nat := if minsz <? q_bytes G then npop minsz G else 0%nat.
  #[local] Abbreviation k := (mk minsz G').
  #[local] Abbreviation P := (firstn k G').
  #[local] Abbreviation rest := (skipn k G').
  #[local] Abbreviation S0' := (Z_to_bv 64 (IBq + 888) : word).
  #[local] Abbreviation S1' := (Z_to_bv 64 minsz : word).
  #[local] Abbreviation S2' := (Z_to_bv 64 (IBq + 728) : word).

  (* [comment removed for export] *)
  Definition mfoot (x : Z) : Prop :=
    (exists a, In a A /\ a <= x < a + 8192) \/ (IBq + 888 <= x < IBq + 920) \/ (U S - 2304 <= x < U S - 2256).

  Definition rcm_post (mem' : word -> option byte) : Prop :=
    (forall x : word, ~ mfoot (U x) -> mem' x = Ma x) /\ mem_grows Ma mem'
    /\ chainR mem' (E' ++ P) 0 /\ chainR mem' rest 0
    /\ cellq mem' (IBq + 888) (len rest) /\ cellq mem' (IBq + 896) (hda rest 0) /\ cellq mem' (IBq + 904) (lasta rest 0) /\ cellq mem' (IBq + 912) (q_bytes rest)
    /\ cells S mem' (-2288) (len (E' ++ P)) /\ cells S mem' (-2280) (hda (E' ++ P) 0) /\ cells S mem' (-2272) (lasta (E' ++ P) 0)
    /\ cells S mem' (-2264) (q_bytes (E' ++ P))
    /\ (forall x : word, (IBq + 888 <= U x < IBq + 896 \/ IBq + 912 <= U x < IBq + 920) -> mem' x <> None)
    /\ E' ++ P <> [] /\ q_bytes rest <= minsz.

  (* [comment removed for export] *)
  Lemma mf_geo : forall b, In b (E' ++ G') -> In (ba_addr b) A /\ 0 <= blen b <= 1021.
  Proof using INA.
    intros b Hb. destruct (mf_forall (fun a => In a A) (fun _ => True) l cur) with (b := b) as (P1 & _ & P3); [| exact Hb | exact (conj P1 P3)].
    intros b0 Hb0. destruct (INA b0 Hb0) as [Q1 Q2]. split; [exact Q1|]. split; [intros; exact I | exact Q2].
  Qed.
  Lemma mf_nd : List.NoDup (map ba_addr (E' ++ G')).
  Proof using ND. apply (Permutation_NoDup (l := map ba_addr (cur :: l))); [apply Permutation_sym; apply mf_addrs | exact ND]. Qed.
  Lemma mf_bgeo : forall b, In b (E' ++ G') -> bgeo b.
  Proof using INA GEO HS A S. intros b Hb. destruct (mf_geo b Hb) as [Q1 [_ Q2]]. destruct (GEO _ Q1) as [G1 G2]. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold bgeo in G in change_no_check G' end). clear - G1 G2 Q2 HS HSr. lia. Qed.
  Lemma mf_ina : forall a, In a (map ba_addr (E' ++ G')) -> In a A.
  Proof using INA. intros a Ha. apply in_map_iff in Ha. destruct Ha as (b & <- & Hb). exact (proj1 (mf_geo b Hb)). Qed.

  Theorem run_rc_pre_m :
    exists r mem',
      msteps BSEGS (mkst regs (0x4e404 : word) memD rom)
                   (mkst r (0x4e7e4 : word) (fr_dr0 (fr_rcu mem') S (Z_to_bv 64 0x4e574) S0' S1' S2' a3v a2v s5v s6v s7v s8v s9v a2v a3v) rom)
      /\ rcm_post mem'
      /\ dr_regs S r /\ getr r 10 = Z_to_bv 64 (len (E' ++ P))
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rgqb Rlast Rfirst Rglen CH Rlock WRD Hstk SZ ND INA SEP GEO Hlt0 Hmerge TOT GLEN NEl Hmin HS H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    pose proof (u64_range S) as HSr.
    assert (Hstk80 : store_ok BSEGS memD (at_ S (-2288)) 80 = true).
    { eapply (store_ok_sub BSEGS memD (at_ S (-2400)) _ 192); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (INA cur (or_introl eq_refl)) as [Ac Lc]. destruct (GEO _ Ac) as [Gc1 Gc2].
    pose proof (SZ cur (or_introl eq_refl)) as Zc.
    assert (Zl : 0 <= q_bytes l).
    { clear - SZ. induction l as [|b r IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. change (q_bytes (b :: r)) with (ba_bytes b + q_bytes r).
      pose proof (SZ b ltac:(right; left; reflexivity)) as Zb.
      assert (0 <= q_bytes r) by (apply IH; intros b0 [<- | Hb0]; [apply SZ; left; reflexivity | apply SZ; right; right; exact Hb0]). lia. }
    (* [comment removed for export] *)
    destruct (rc_pre_m memD rom S ra0 s0v s1v s2v s3v s4v a2v a3v minsz (1 + len l) B0 (Z_to_bv 8 1) b2 b3 regs H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 HS
                ltac:(clear - GLEN; lia) ltac:(clear - TOT Zc Zl; lia) Hmerge Hstk80 Rlock Rglen Rgqb)
      as (r1 & RUN1 & (A1 & A2 & A10 & A11 & A8 & A9 & A18 & A19 & A20 & A3 & A4 & A21 & A22 & A23 & A24 & A25 & A26 & A27)).
    pose proof (fr_rc0_grows memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3) as GRa.
    assert (OUTa : forall x : word, AIMGLO <= U x < U S - 2304 -> (U x < 0x10aec8 \/ 0x10aecc <= U x) -> Ma x = memD x).
    { intros x Hx Hl. apply (fr_rc0_outside memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS); [left; clear - Hx; lia | exact Hl]. }
    (* [comment removed for export] *)
    assert (CHa : chainR Ma (cur :: l) 0).
    { apply (chainR_frame memD Ma); [| | exact CH].
      - intros b Hb. destruct (INA b Hb) as [Ab Lb]. destruct (GEO _ Ab) as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold bgeo in G in change_no_check G' end). clear - G1 G2 Lb HS HSr. lia.
      - intros b x Hb Hx. destruct (INA b Hb) as [Ab _]. destruct (GEO _ Ab) as [G1 G2]. apply OUTa; [clear - Hx G1 G2; lia | right; clear - Hx G1; lia]. }
    assert (HDa : forall c v, IBq + 888 <= c -> c + 8 <= IBq + 920 -> cellq memD c v -> cellq Ma c v).
    { intros c v H0 H1' C. unfold cellq in *. apply (rd8_eq memD Ma); [clear - H0; lia | clear - H1'; lia | | exact C].
      intros x Hx. apply OUTa; [clear - Hx H0 H1' HS; lia | right; clear - Hx H0; lia]. }
    pose proof CHa as CHa'. cbn [chainR] in CHa'. destruct CHa' as [(Cn & _) _].
    assert (Hnx : 0 < hda l 0 < 2 ^ 64).
    { destruct l as [|b1 l1]; [exfalso; exact (NEl eq_refl)|]. (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end). destruct (INA b1 ltac:(right; left; reflexivity)) as [A1' _].
      destruct (GEO _ A1') as [G1 G2]. clear - G1 G2 HS HSr. lia. }
    destruct (mg_entry Ma rom S (Z_to_bv 64 0x4e4ac) (ba_addr cur) (hda l 0) r1 A1 A2 A10 A11 HS (conj Gc1 Gc2) Hnx) as (r2 & RUN2 & K2 & H2').
    { eapply store_ok_mono; [exact GRa|]. eapply (store_ok_sub BSEGS memD (at_ S (-2400)) _ 192); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { apply HDa; [clear; lia | clear; lia | exact Rfirst]. }
    { exact Cn. }
    set (Mb := wbytes Ma (at_ S (-2296)) (LE8 (Z_to_bv 64 0x4e4ac))) in *.
    assert (GRb : mem_grows Ma Mb) by apply wbytes_grows.
    assert (OUTb : forall x : word, (U x < U S - 2296 \/ U S - 2288 <= U x) -> Mb x = Ma x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mb in G in change_no_check G' end). apply wbytes_outside; [rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hx; lia]. }
    (* [comment removed for export] *)
    assert (WRb : forall a k0 n, In a A -> 0 <= k0 -> k0 + Z.of_nat n <= 8192 -> store_ok BSEGS Mb (Z_to_bv 64 (a + k0)) n = true).
    { intros a k0 n Ha H0 H1'. eapply store_ok_mono; [exact GRb|]. eapply store_ok_mono; [exact GRa | exact (WRD a k0 n Ha H0 H1')]. }
    assert (WRSb : store_ok BSEGS Mb (at_ S (-2288)) 32 = true).
    { eapply store_ok_mono; [exact GRb|]. eapply store_ok_mono; [exact GRa|].
      eapply (store_ok_sub BSEGS memD (at_ S (-2400)) _ 192); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (CELLb : forall c v, 0 <= c -> c + 8 <= U S - 2304 -> cellq Ma c v -> cellq Mb c v).
    { intros c v H0 H1' C. unfold cellq in *. apply (rd8_eq Ma Mb); [exact H0 | clear - H1' HS HSr; lia | | exact C]. intros x Hx. apply OUTb. left. clear - Hx H1'. lia. }
    assert (STKb : forall kk v, -2288 <= kk -> kk + 8 <= -2208 -> rdn BSEGS Ma (at_ S kk) 8 = Some v -> rdn BSEGS Mb (at_ S kk) 8 = Some v).
    { intros kk v Hk1 Hk2 Hr. eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr]. intros x Hx. apply OUTb. right. rewrite at_u in Hx by lia. clear - Hx Hk1. lia. }
    assert (INVb : mg_inv S A Mb [] cur l [] Mb).
    { (lazymatch goal with |- ?G => let G' := eval unfold mg_inv in G in change_no_check G' end). split; [apply mem_grows_refl|]. split; [exact I|].
      assert (CHb : chainR Mb (cur :: l) 0).
      { apply (chainR_frame Ma Mb); [| | exact CHa].
        - intros b Hb. destruct (INA b Hb) as [Ab Lb]. destruct (GEO _ Ab) as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold bgeo in G in change_no_check G' end). clear - G1 G2 Lb HS HSr. lia.
        - intros b x Hb Hx. destruct (INA b Hb) as [Ab _]. destruct (GEO _ Ab) as [G1 G2]. apply OUTb. left. clear - Hx G2. lia. }
      cbn [chainR] in CHb. destruct CHb as [CB1 CB2]. split; [exact CB1|]. split; [exact CB2|]. split; [exact I|].
      split. { change (len [] + 1 + len l) with (0 + 1 + len l). replace (0 + 1 + len l) with (1 + len l) by (clear; lia).
               apply CELLb; [clear; lia | clear - HS; lia |]. apply HDa; [clear; lia | clear; lia | exact Rglen]. }
      split. { apply CELLb; [clear; lia | clear - HS; lia |]. apply HDa; [clear; lia | clear; lia | exact Rlast]. }
      split. { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). apply STKb; [clear; lia | clear; lia |]. exact (fr_rc0_t0 memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS). }
      split. { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). apply STKb; [clear; lia | clear; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fr_rc0 in G in change_no_check G' end).
               repeat (wd_rdstep rd8_side). }
      split. { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). apply STKb; [clear; lia | clear; lia |]. exact (fr_rc0_t16 memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS). }
      split. { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). apply STKb; [clear; lia | clear; lia |]. exact (fr_rc0_sum memD S ra0 s0v s1v s2v s3v s4v (Z_to_bv 8 1) b2 b3 HS). }
      split. { intros b Hb. cbn [app] in Hb. rewrite app_nil_r in Hb. exact (INA b Hb). }
      split. { (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). rewrite app_nil_r. exact ND. }
      split; [exact SZ|]. split; [exact TOT|]. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). clear - GLEN. lia. }
    destruct (mg_loop rom S A Mb HS GEO SEP WRb WRSb l [] cur [] Mb r2 NEl INVb (mg_keep_self S _ _ K2) H2') as (r3 & Mc & RUN3 & K3 & X12 & FIN & DEFc).
    cbn [app] in X12, FIN. destruct FIN as (GRc & FRc & CG & CE & Clen & Clast & Tsz & Tfirst & Tlast & Tb).
    (* [comment removed for export] *)
    pose proof (mf_bytes l cur) as EB. set (ext := 8192 * len E') in *.
    assert (QG0 : 0 <= q_bytes G').
    { apply q_bytes_nonneg. intros b Hb. pose proof (mf_sz l cur SZ b Hb) as Z8. clear - Z8. lia. }
    assert (EXT0 : 0 <= ext) by ((lazymatch goal with |- ?G => let G' := eval unfold ext in G in change_no_check G' end); clear; lia).
    assert (NFL : forall x, ~ (exists a, In a A /\ a <= x < a + 8192) -> ~ (IBq + 888 <= x < IBq + 896) -> ~ (IBq + 904 <= x < IBq + 912) ->
                   ~ (U S - 2288 <= x < U S - 2256) -> ~ mg_footL S A x).
    { intros x N1 N2 N3 N4 F. unfold mg_footL in F. destruct F as [F|[F|[F|F]]]; [exact (N1 F) | exact (N2 F) | exact (N3 F) | exact (N4 F)]. }
    assert (NOBJ : forall x, x < AIMGHI \/ U S - 3584 <= x -> ~ (exists a, In a A /\ a <= x < a + 8192)).
    { intros x Hx (a & Ha & Hr). destruct (GEO _ Ha) as [G1 G2]. clear - Hx Hr G1 G2. lia. }
    assert (RBc : rdn BSEGS Mc (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 B0))).
    { apply (rd8_eq Mb Mc); [clear; lia | clear; lia | |].
      - intros x Hx. apply FRc. apply NFL; [apply NOBJ; left; clear - Hx; lia | clear - Hx; lia | clear - Hx; lia | clear - Hx HS; lia].
      - apply CELLb; [clear; lia | clear - HS; lia |]. apply HDa; [clear; lia | clear; lia | exact Rgqb]. }
    assert (Rrac : rdn BSEGS Mc (at_ S (-2296)) 8 = Some (LE8 (Z_to_bv 64 0x4e4ac))).
    { eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval unfold Mb in G in change_no_check G' end); apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
      intros x Hx. rewrite at_u in Hx by lia. apply FRc. apply NFL; [apply NOBJ; right; clear - Hx; lia | clear - Hx HS; lia | clear - Hx HS; lia | clear - Hx; lia]. }
    assert (RET18 : ret_ok (Z_to_bv 64 0x4e4ac)) by (apply ret_ok_lit; [clear; lia | reflexivity]).
    destruct (mg_exit Mc rom S (Z_to_bv 64 0x4e4ac) ext B0 r3 (mg_keep_self S _ _ K3) X12 HS ltac:(clear - EB QG0 EXT0 TOT; fold ext in EB; lia) RET18 RBc Rrac)
      as (r4 & RUN4 & D2 & D8 & D9 & D18 & D19 & D20 & D3 & D4 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
    set (Md := wbytes Mc (Z_to_bv 64 (IBq + 912)) (LE8 (Z_to_bv 64 (B0 - ext)))) in *.
    assert (GRd : mem_grows Mc Md) by apply wbytes_grows.
    assert (OUTd : forall x : word, (U x < IBq + 912 \/ IBq + 920 <= U x) -> Md x = Mc x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Md in G in change_no_check G' end). apply wbytes_outside; [rewrite length_N_to_le_bytes; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | rewrite length_N_to_le_bytes; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hx; lia]. }
    assert (EBd : B0 - ext = q_bytes G') by (clear - EB; fold ext in EB; lia).
    (* [comment removed for export] *)
    destruct K2 as (_ & _ & _ & K2_8 & K2_9 & K2_18 & K2_19 & K2_20 & K2_3 & K2_4 & K2_21 & K2_22 & K2_23 & K2_24 & K2_25 & K2_26 & K2_27).
    destruct K3 as (_ & _ & _ & K3_8 & K3_9 & K3_18 & K3_19 & K3_20 & K3_3 & K3_4 & K3_21 & K3_22 & K3_23 & K3_24 & K3_25 & K3_26 & K3_27).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x4e4ac : word) with (0x4e4ac%bv : word) in RUN4 by (apply bv_eq; reflexivity).
    assert (Rglend : rdn BSEGS Md (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 (len G')))).
    { apply (rd8_eq Mc Md); [clear; lia | clear; lia | intros x Hx; apply OUTd; left; clear - Hx; lia | exact Clen]. }
    destruct (rc_post_m Md rom S a2v a3v minsz (len G') r4 D2 ltac:(rewrite D8, K3_8, K2_8; exact A8) ltac:(rewrite D9, K3_9, K2_9; exact A9)
                ltac:(rewrite D18, K3_18, K2_18; exact A18) ltac:(rewrite D19, K3_19, K2_19; exact A19) ltac:(rewrite D20, K3_20, K2_20; exact A20) Rglend)
      as (r5 & RUN5 & F2 & F10 & F11 & F12 & F13 & F16 & F3 & F4 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F8 & F9 & F18 & F19 & F20).
    (* [comment removed for export] *)
    assert (OBJd : forall b (x : word), In b (E' ++ G') -> ba_addr b <= U x < ba_addr b + 8192 -> Md x = Mc x).
    { intros b x Hb Hx. apply OUTd. right. destruct (GEO _ (proj1 (mf_geo b Hb))) as [G1 _]. clear - Hx G1. lia. }
    assert (CGd : chainR Md G' 0).
    { apply (chainR_frame Mc Md); [intros b Hb; apply mf_bgeo; apply in_app_iff; right; exact Hb | | exact CG].
      intros b x Hb Hx. apply (OBJd b x); [apply in_app_iff; right; exact Hb | exact Hx]. }
    assert (CEd : chainR Md E' 0).
    { apply (chainR_frame Mc Md); [intros b Hb; apply mf_bgeo; apply in_app_iff; left; exact Hb | | exact CE].
      intros b x Hb Hx. apply (OBJd b x); [apply in_app_iff; left; exact Hb | exact Hx]. }
    assert (STKd : forall kk v, -2288 <= kk -> kk + 8 <= -2256 -> cells S Mc kk v -> cells S Md kk v).
    { intros kk v Hk1 Hk2 C. unfold cells in *. eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact C].
      intros x Hx. apply OUTd. right. rewrite at_u in Hx by lia. clear - Hx Hk1 HS. lia. }
    assert (Rfirstd : cellq Md (IBq + 896) (ba_addr cur)).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). apply (rd8_eq Mc Md); [clear; lia | clear; lia | intros x Hx; apply OUTd; left; clear - Hx; lia|].
      apply (rd8_eq Mb Mc); [clear; lia | clear; lia | |].
      - intros x Hx. apply FRc. apply NFL; [apply NOBJ; left; clear - Hx; lia | clear - Hx; lia | clear - Hx; lia | clear - Hx HS; lia].
      - apply CELLb; [clear; lia | clear - HS; lia |]. apply HDa; [clear; lia | clear; lia | exact Rfirst]. }
    assert (Rlastd : cellq Md (IBq + 904) (lasta G' 0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). apply (rd8_eq Mc Md); [clear; lia | clear; lia | intros x Hx; apply OUTd; left; clear - Hx; lia | exact Clast]. }
    assert (Rgqbd : cellq Md (IBq + 912) (q_bytes G')).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). rewrite <- EBd. (lazymatch goal with |- ?G => let G' := eval unfold Md in G in change_no_check G' end). apply rdn_wbytes_hit8. unorm. clear. lia. }
    assert (DEF912 : forall x : word, IBq + 912 <= U x < IBq + 920 -> Md x <> None).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Md in G in change_no_check G' end). rewrite wbytes_inside; [discriminate | rewrite length_N_to_le_bytes; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | rewrite length_N_to_le_bytes; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hx; lia]. }
    assert (GRad : mem_grows Ma Md) by (eapply mem_grows_trans; [exact GRb|]; eapply mem_grows_trans; [exact GRc | exact GRd]).
    assert (FRad : forall x : word, ~ mfoot (U x) -> Md x = Ma x).
    { intros x NF. unfold mfoot in NF. rewrite OUTd by (clear - NF; lia).
      rewrite FRc by (intros F; apply NF; unfold mg_footL in F; destruct F as [F|[F|[F|F]]]; [left; exact F | right; left; clear - F; lia | right; left; clear - F; lia | right; right; clear - F; lia]).
      apply OUTb. clear - NF. lia. }
    assert (LENEG : len E' + len G' = 1 + len l).
    { pose proof (Permutation_length (mf_addrs l cur)) as PL. rewrite !length_map, length_app in PL. cbn [length] in PL. clear - PL. lia. }
    assert (QE : q_bytes E' = 8192 * len E') by (apply q_bytes_empties; exact (mf_empties l cur)).
    pose proof (mf_nonempty l cur) as NEG.
    assert (SOK80d : store_ok BSEGS Md (at_ S (-2288)) 80 = true) by (eapply store_ok_mono; [exact GRad|]; eapply store_ok_mono; [exact GRa | exact Hstk80]).
    pose proof (STKd (-2288) _ ltac:(clear; lia) ltac:(clear; lia) Tsz) as Tszd. pose proof (STKd (-2280) _ ltac:(clear; lia) ltac:(clear; lia) Tfirst) as Tfirstd.
    pose proof (STKd (-2272) _ ltac:(clear; lia) ltac:(clear; lia) Tlast) as Tlastd. pose proof (STKd (-2264) _ ltac:(clear; lia) ltac:(clear; lia) Tb) as Tbd.
    (* [comment removed for export] *)
    assert (CASE : exists r6 mem', msteps BSEGS (mkst r5 (0x4e4c0 : word) Md rom) (mkst r6 (0x4e55c : word) mem' rom) /\ rc_keep r5 r6
                     /\ (forall x : word, ~ mfoot (U x) -> mem' x = Md x) /\ mem_grows Md mem'
                     /\ chainR mem' (E' ++ P) 0 /\ chainR mem' rest 0
                     /\ cellq mem' (IBq + 888) (len rest) /\ cellq mem' (IBq + 896) (hda rest 0) /\ cellq mem' (IBq + 904) (lasta rest 0) /\ cellq mem' (IBq + 912) (q_bytes rest)
                     /\ cells S mem' (-2288) (len (E' ++ P)) /\ cells S mem' (-2280) (hda (E' ++ P) 0) /\ cells S mem' (-2272) (lasta (E' ++ P) 0)
                     /\ cells S mem' (-2264) (q_bytes (E' ++ P))
                     /\ (forall x : word, (IBq + 888 <= U x < IBq + 896 \/ IBq + 912 <= U x < IBq + 920) -> mem' x <> None)
                     /\ E' ++ P <> [] /\ q_bytes rest <= minsz).
    { (lazymatch goal with |- ?G => let G' := eval unfold mk in G in change_no_check G' end). destruct (Z.ltb_spec minsz (q_bytes G')) as [Hlt | Hge].
      - (* [comment removed for export] *)
        set (kk := npop minsz G'). set (pl := trips G' kk).
        assert (Hkk : (1 <= kk <= length G')%nat) by (split; [apply npop_pos; exact NEG | apply npop_le]).
        assert (LLEN : length pl = kk) by (apply trips_len; clear - Hkk; lia).
        assert (RNG : forall b, In b G' -> 0 <= ba_bytes b /\ 0 <= ba_addr b < 2 ^ 64).
        { intros b Hb. pose proof (mf_sz l cur SZ b Hb) as Z8. destruct (GEO _ (proj1 (mf_geo b ltac:(apply in_app_iff; right; exact Hb)))) as [G1 G2]. clear - Z8 G1 G2 HS HSr. lia. }
        pose proof (pops_ok_trips minsz G' RNG Hlt ltac:(clear - Hmin; lia)) as POK. fold kk pl in POK.
        pose proof (pops_tot minsz pl (nxaddr G') (q_bytes G') POK) as PT.
        destruct (rc_head_loop_g Md rom S minsz (q_bytes G') (ba_addr cur) (len E') (lasta E' 0) r5 F2 F10 F11 Hmin ltac:(clear - QG0 EBd EXT0 TOT Zc Zl; lia)
                    Tszd Tlastd Rgqbd Rfirstd Hlt)
          as (r6 & RUN6 & KP6 & B14 & B15 & B5 & B16).
        pose proof KP6 as (C2 & C10 & C11 & _).
        assert (ENX : nxaddr G' = ba_addr cur) by (rewrite <- hda_nxaddr; apply mf_head).
        assert (INGa : forall b, In b G' -> In (ba_addr b) A) by (intros b Hb; exact (proj1 (mf_geo b ltac:(apply in_app_iff; right; exact Hb)))).
        assert (INEa : forall b, In b E' -> In (ba_addr b) A) by (intros b Hb; exact (proj1 (mf_geo b ltac:(apply in_app_iff; left; exact Hb)))).
        assert (PRVA : len E' <> 0 -> In (lasta E' 0) (map ba_addr E')) by (intros NZ; apply lasta_in0; intros EE; rewrite EE in NZ; exact (NZ eq_refl)).
        assert (PLG : forall t, In t pl -> exists b, In b G' /\ p_addr t = ba_addr b).
        { intros t Ht. destruct (trips_in G' kk t Ht) as (b & Hb & Ea & _). exists b. split; [exact (firstn_InK _ _ _ Hb) | exact Ea]. }
        destruct (rc_pop_loop rom S minsz HS Hmin pl r6 Md (len E') (lasta E' 0) (len G') (q_bytes G') (8192 * len E') (nxaddr G') POK
                    ltac:(rewrite C2; exact F2) ltac:(rewrite C10; exact F10) ltac:(rewrite C11; exact F11) B14 B15 ltac:(rewrite B16; exact F16) ltac:(rewrite ENX; exact B5)
                    ltac:(clear; lia) ltac:(rewrite LLEN; clear - Hkk LENEG GLEN; lia) ltac:(rewrite LLEN; clear - Hkk LENEG GLEN; lia)
                    ltac:(clear - QG0 EBd EXT0 TOT Zc Zl; lia) ltac:(clear; lia) ltac:(clear - PT EB QE TOT; unfold ext in *; lia))
          as (r7 & mem' & RUN7 & KP7 & PP).
        { apply Forall_forall. intros t Ht. destruct (PLG t Ht) as (b & Hb & ->). exact (GEO _ (INGa b Hb)). }
        { (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_addr. apply all_sep_of.
          - pose proof mf_nd as N. rewrite map_app in N. pose proof (NoDup_app_remove_l _ _ N) as NG. rewrite <- (firstn_skipn kk G'), map_app in NG. exact (NoDup_app_remove_r _ _ NG).
          - intros x y Hx Hy NExy. apply in_map_iff in Hx. apply in_map_iff in Hy. destruct Hx as (bx & <- & Hbx). destruct Hy as (by' & <- & Hby).
            exact (SEP _ _ (INGa bx (firstn_InK _ _ _ Hbx)) (INGa by' (firstn_InK _ _ _ Hby)) NExy). }
        { intros NZ. pose proof (PRVA NZ) as HL. apply in_map_iff in HL. destruct HL as (bl & EL & HbL). split; [rewrite <- EL; exact (GEO _ (INEa bl HbL))|].
          apply Forall_forall. intros a Ha. apply in_map_iff in Ha. destruct Ha as (t & <- & Ht). destruct (PLG t Ht) as (b & Hb & ->).
          rewrite <- EL. apply (SEP _ _ (INEa bl HbL) (INGa b Hb)). intros EQa.
          pose proof mf_nd as N. rewrite map_app in N. apply (nd_app_disj _ _ (ba_addr bl) N); [apply in_map; exact HbL | rewrite EQa; apply in_map; exact Hb]. }
        { exact SOK80d. }
        { apply Forall_forall. intros t Ht. destruct (PLG t Ht) as (b & Hb & ->). eapply store_ok_mono; [exact GRad|]. eapply store_ok_mono; [exact GRa|].
          replace (ba_addr b) with (ba_addr b + 0) by (clear; lia). apply WRD; [exact (INGa b Hb) | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]. }
        { intros NZ. pose proof (PRVA NZ) as HL. apply in_map_iff in HL. destruct HL as (bl & EL & HbL). eapply store_ok_mono; [exact GRad|]. eapply store_ok_mono; [exact GRa|].
          rewrite <- EL. replace (ba_addr bl) with (ba_addr bl + 0) by (clear; lia). apply WRD; [exact (INEa bl HbL) | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]. }
        { apply trips_forall. intros i b Hi Hb. (lazymatch goal with |- ?G => let G' := eval cbn [p_addr p_nx p_sz fst snd] in G in change_no_check G' end). destruct (chainR_nth Md G' 0 i b CGd Hb) as (N1 & N2 & _).
          rewrite hda_nxaddr in N1. split; [exact N1 | exact N2]. }
        { exact Rgqbd. }
        { exact Tbd. }
        assert (SEPA : forall a1 a2, In a1 (map ba_addr (E' ++ G')) -> In a2 (map ba_addr (E' ++ G')) -> a1 <> a2 -> bsep a1 a2).
        { intros a1 a2 H1' H2'' NEa. exact (SEP _ _ (mf_ina a1 H1') (mf_ina a2 H2'') NEa). }
        assert (GEOA : forall a, In a (map ba_addr (E' ++ G')) -> AIMGHI <= a /\ a + 8192 <= U S - 3584) by (intros a Ha; exact (GEO _ (mf_ina a Ha))).
        destruct (pop_chain S E' G' kk (len G') (q_bytes G') (8192 * len E') Md mem' Hkk mf_bgeo GEOA SEPA mf_nd CEd CGd PP) as [CHT CHR].
        destruct PP as (PO & PG' & Pfirst & Plast & Plen & Pbytes & Ptsz & Ptlast & Psum & Ptfirst & Pprev & Pchain & Pdef).
        assert (NEP : firstn kk G' <> []).
        { destruct G' as [|g0 G0] eqn:EG'; [exfalso; exact (NEG eq_refl)|]. destruct kk; [exfalso; clear - Hkk; lia | discriminate]. }
        assert (LFM : forall z, loop_foot S (len E') (lasta E' 0) pl z -> mfoot z).
        { intros z F. unfold loop_foot in F. (lazymatch goal with |- ?G => let G' := eval unfold mfoot in G in change_no_check G' end).
          destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
            [right; left; clear - F; lia | right; left; clear - F; lia | right; left; clear - F; lia | | | right; right; clear - F; lia | right; right; clear - F; lia | right; right; clear - F; lia].
          - destruct F as (t & Ht & Hr). destruct (PLG t Ht) as (b & Hb & Ea). left. exists (ba_addr b). split; [exact (INGa b Hb) | rewrite Ea in Hr; clear - Hr; lia].
          - destruct F as [NZ Hr]. pose proof (PRVA NZ) as HL. apply in_map_iff in HL. destruct HL as (bl & EL & HbL). left. exists (lasta E' 0).
            split; [rewrite <- EL; exact (INEa bl HbL) | clear - Hr; lia]. }
        exists r7, mem'. split; [eapply msteps_trans; [exact RUN6 | exact RUN7]|]. split; [exact (rc_keep_trans _ _ _ KP6 KP7)|].
        split; [intros x NF; apply PO; intros F; exact (NF (LFM _ F))|]. split; [exact PG'|].
        split; [exact CHT|]. split; [exact CHR|].
        (* [comment removed for export] *)
        split. { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (len (skipn kk G')) with (len G' - Z.of_nat (length pl)); [exact Plen|]. rewrite LLEN, length_skipn. clear - Hkk. lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (hda (skipn kk G') 0) with (p_lastnx pl 1); [exact Pfirst|]. (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_lastnx by exact Hkk. symmetry. apply hda_nxaddr. }
        split.
        { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). destruct (skipn kk G') as [|rb rr] eqn:ER.
          - (lazymatch goal with |- ?G => let G' := eval cbn [lasta] in G in change_no_check G' end). apply Plast. (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_lastnx by exact Hkk. rewrite ER. reflexivity.
          - assert (NZL : p_lastnx pl 1 <> 0).
            { (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_lastnx by exact Hkk. rewrite ER. (lazymatch goal with |- ?G => let G' := eval cbn [nxaddr] in G in change_no_check G' end).
              destruct (GEO _ (INGa rb ltac:(apply (skipn_InK G' kk); rewrite ER; left; reflexivity))) as [G1 _]. clear - G1. lia. }
            replace (lasta (rb :: rr) 0) with (lasta G' 0) by (rewrite <- (firstn_skipn kk G') at 1; rewrite ER; apply lasta_app; discriminate).
            apply (rd8_eq Md mem'); [clear; lia | clear; lia | | exact Rlastd].
            intros x Hx. apply PO. intros F. unfold loop_foot in F.
            destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
              [clear - F Hx; lia | exact (NZL (proj1 F)) | clear - F Hx; lia | | | clear - F Hx HS; lia | clear - F Hx HS; lia | clear - F Hx HS; lia].
            + destruct F as (t & Ht & Hr). destruct (PLG t Ht) as (b & Hb & Ea). destruct (GEO _ (INGa b Hb)) as [G1 _]. rewrite Ea in Hr. clear - Hr Hx G1. lia.
            + destruct F as [NZ Hr]. pose proof (PRVA NZ) as HL. apply in_map_iff in HL. destruct HL as (bl & EL & HbL). destruct (GEO _ (INEa bl HbL)) as [G1 _].
              rewrite <- EL in Hr. clear - Hr Hx G1. lia. }
        split.
        { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (q_bytes (skipn kk G')) with (q_bytes G' - p_tot pl); [exact Pbytes|]. (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_tot by (clear - Hkk; lia).
          rewrite <- (firstn_skipn kk G') at 1. rewrite q_bytes_appM. clear. lia. }
        (* [comment removed for export] *)
        split. { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). replace (len (E' ++ firstn kk G')) with (len E' + Z.of_nat (length pl)); [exact Ptsz|]. rewrite LLEN, length_app, length_firstn. clear - Hkk. lia. }
        split.
        { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). destruct (Z.eq_dec (len E') 0) as [Z0 | NZ].
          - assert (EE : E' = []) by (apply length_zero_iff_nil; clear - Z0; lia). rewrite EE. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end).
            replace (hda (firstn kk G') 0) with (match pl with [] => 0 | t :: _ => p_addr t end); [exact (Ptfirst Z0)|].
            (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_head; [| clear - Hkk; lia | exact NEG]. rewrite hda_nxaddr, nxaddr_firstn; [reflexivity | clear - Hkk; lia].
          - assert (EH : hda (E' ++ firstn kk G') 0 = hda E' 0) by (destruct E' as [|e0 E0]; [exfalso; apply NZ; reflexivity | reflexivity]). rewrite EH.
            pose proof Tfirstd as TF. unfold cells in TF. rewrite atS in TF |- * by (exact HS || (clear; lia)).
            apply (rd8_eq Md mem'); [clear - HS; lia | clear - HS HSr; lia | | exact TF].
            intros x Hx. apply PO. intros F. unfold loop_foot in F.
            destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
              [clear - F Hx HS; lia | clear - F Hx HS; lia | clear - F Hx HS; lia | | | exact (NZ (proj1 F)) | clear - F Hx; lia | clear - F Hx; lia].
            + destruct F as (t & Ht & Hr). destruct (PLG t Ht) as (b & Hb & Ea). destruct (GEO _ (INGa b Hb)) as [_ G2]. rewrite Ea in Hr. clear - Hr Hx G2. lia.
            + destruct F as [_ Hr]. pose proof (PRVA NZ) as HL. apply in_map_iff in HL. destruct HL as (bl & EL & HbL). destruct (GEO _ (INEa bl HbL)) as [_ G2].
              rewrite <- EL in Hr. clear - Hr Hx G2. lia. }
        split.
        { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). replace (lasta (E' ++ firstn kk G') 0) with (p_lasta pl 0); [exact Ptlast|]. (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_lasta by exact Hkk.
          rewrite lasta_app by exact NEP. rewrite lasta_rev. destruct (rev (firstn kk G')); reflexivity. }
        split.
        { (lazymatch goal with |- ?G => let G' := eval unfold cells in G in change_no_check G' end). replace (q_bytes (E' ++ firstn kk G')) with (8192 * len E' + p_tot pl); [exact Psum|]. (lazymatch goal with |- ?G => let G' := eval unfold pl in G in change_no_check G' end). rewrite trips_tot by (clear - Hkk; lia).
          rewrite q_bytes_appM, QE. reflexivity. }
        split; [intros x Hx; apply Pdef; clear - Hx; lia|].
        split; [intros EQl; apply app_eq_nil in EQl; exact (NEP (proj2 EQl))|].
        apply rest_bytes; [intros b Hb; exact (proj1 (RNG b Hb)) | clear - Hmin; lia].
      - (* [comment removed for export] *)
        change (skipn 0 G') with G'. change (firstn 0 G') with (@nil batch). rewrite app_nil_r.
        assert (NEe : E' <> []).
        { intros EE. unfold ext in EBd. rewrite EE in EBd. cbn [length] in EBd. clear - EBd Hge Hlt0. lia. }
        destruct (rc_head_none_g Md rom S minsz (q_bytes G') (len E') (lasta E' 0) r5 F2 F10 F11 Hmin ltac:(clear - QG0 EBd EXT0 TOT Zc Zl; lia)
                    Tszd Tlastd Rgqbd Hge) as (r6 & RUN6 & KP6).
        exists r6, Md. split; [exact RUN6|]. split; [exact KP6|]. split; [intros x _; reflexivity|]. split; [apply mem_grows_refl|].
        split; [exact CEd|]. split; [exact CGd|]. split; [exact Rglend|]. split; [rewrite (mf_head l cur 0); exact Rfirstd|]. split; [exact Rlastd|]. split; [exact Rgqbd|].
        split; [exact Tszd|]. split; [exact Tfirstd|].
        split; [exact Tlastd|]. split; [rewrite QE; exact Tbd|].
        split; [intros x [Hx | Hx]; [apply GRd; exact (DEFc NEe x Hx) | exact (DEF912 x Hx)]|].
        split; [exact NEe | exact Hge]. }
    destruct CASE as (r6 & mem' & RUN6 & KP6 & FR6 & GR6 & CHT & CHR & Q888 & Q896 & Q904 & Q912 & T88 & T80 & T72 & T64 & DEF6 & NET & RESTB).
    (* [comment removed for export] *)
    assert (V8 : getr r5 8 = S0') by (rewrite F8, D8, K3_8, K2_8; exact A8).
    assert (V9 : getr r5 9 = S1') by (rewrite F9, D9, K3_9, K2_9; exact A9).
    assert (V18 : getr r5 18 = S2') by (rewrite F18, D18, K3_18, K2_18; exact A18).
    assert (V19 : getr r5 19 = a3v) by (rewrite F19, D19, K3_19, K2_19; exact A19).
    assert (V20 : getr r5 20 = a2v) by (rewrite F20, D20, K3_20, K2_20; exact A20).
    assert (V21 : getr r5 21 = s5v) by (rewrite F21, D21, K3_21, K2_21, A21; exact H21).
    assert (V22 : getr r5 22 = s6v) by (rewrite F22, D22, K3_22, K2_22, A22; exact H22).
    assert (V23 : getr r5 23 = s7v) by (rewrite F23, D23, K3_23, K2_23, A23; exact H23).
    assert (V24 : getr r5 24 = s8v) by (rewrite F24, D24, K3_24, K2_24, A24; exact H24).
    assert (V25 : getr r5 25 = s9v) by (rewrite F25, D25, K3_25, K2_25, A25; exact H25).
    assert (V3 : getr r5 3 = getr regs 3) by (rewrite F3, D3, K3_3, K2_3; exact A3).
    assert (V4 : getr r5 4 = getr regs 4) by (rewrite F4, D4, K3_4, K2_4; exact A4).
    assert (V26 : getr r5 26 = getr regs 26) by (rewrite F26, D26, K3_26, K2_26; exact A26).
    assert (V27 : getr r5 27 = getr regs 27) by (rewrite F27, D27, K3_27, K2_27; exact A27).
    pose proof KP6 as (C2 & C10 & C11 & C12 & C13 & C8 & C9 & C18 & C19 & C20 & C3 & C4 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
    destruct (rc_unlock_call mem' rom S r6 ltac:(rewrite C2; exact F2) ltac:(rewrite C10; exact F10))
      as (r8 & RUN8 & (E2 & E10 & E12 & E13 & E8 & E9 & E18 & E19 & E20 & E3 & E4 & E21 & E22 & E23 & E24 & E25 & E26 & E27) & E1 & E11).
    assert (GRu : mem_grows memD (fr_rcu mem')).
    { eapply mem_grows_trans; [exact GRa|]. eapply mem_grows_trans; [exact GRad|]. eapply mem_grows_trans; [exact GR6 | apply fr_rcu_grows]. }
    assert (Rtsz : rdn BSEGS (fr_rcu mem') (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (len (E' ++ P))))).
    { eapply rd_same; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact T88]. intros x Hx. apply fr_rcu_outside. rewrite at_u in Hx by lia. cbn in Hx. clear - Hx HS. lia. }
    assert (LENT : 1 <= len (E' ++ P) < 2 ^ 28).
    { split; [destruct (E' ++ P) as [|t0 tt]; [exfalso; exact (NET eq_refl) | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia]|].
      rewrite length_app, length_firstn. clear - LENEG GLEN. lia. }
    destruct (dr_pre_loop (fr_rcu mem') rom S (Z_to_bv 64 0x4e574) S0' S1' S2' a3v a2v s5v s6v s7v s8v s9v a2v a3v (len (E' ++ P)) r8 E1
                ltac:(rewrite E2, C2; exact F2) E11 ltac:(rewrite E12, C12; exact F12) ltac:(rewrite E13, C13; exact F13)
                ltac:(rewrite E8, C8; exact V8) ltac:(rewrite E9, C9; exact V9) ltac:(rewrite E18, C18; exact V18)
                ltac:(rewrite E19, C19; exact V19) ltac:(rewrite E20, C20; exact V20)
                ltac:(rewrite E21, C21; exact V21) ltac:(rewrite E22, C22; exact V22) ltac:(rewrite E23, C23; exact V23)
                ltac:(rewrite E24, C24; exact V24) ltac:(rewrite E25, C25; exact V25)
                HS ltac:(clear - LENT; lia))
      as (r9 & RUN9 & HR9 & (G3 & G4 & G26 & G27) & G10).
    { eapply (store_ok_sub BSEGS (fr_rcu mem') (at_ S (-2400)) _ 192); [rewrite at_u; lia | eapply store_ok_mono; [exact GRu | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact Rtsz. }
    { clear - LENT. lia. }
    exists r9, mem'. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN8 | exact RUN9]. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold rcm_post in G in change_no_check G' end). split; [intros x NF; rewrite (FR6 x NF); exact (FRad x NF)|]. split; [eapply mem_grows_trans; [exact GRad | exact GR6]|].
      repeat (split; [assumption|]). assumption. }
    split; [exact HR9|]. split; [exact G10|].
    split; [rewrite G3, E3, C3; exact V3|]. split; [rewrite G4, E4, C4; exact V4|].
    split; [rewrite G26, E26, C26; exact V26 | rewrite G27, E27, C27; exact V27].
  Qed.
End RUNPREM.
End BoAllocFRcM5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopD.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsD3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsD23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.BoAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r BoAllocFMemD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD BoAllocFArms.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Lemma rdn1_of_some : forall (m : mem) (a : word) b, m a = Some b -> rdn BSEGS m a 1 = Some [b].
Proof. intros m a b E. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite E. reflexivity. Qed.
(* [comment removed for export] *)
Lemma rdn1_ex_10af0a : forall m : mem, exists b, rdn BSEGS m (Z_to_bv 64 0x10aeca) 1 = Some [b].
Proof. intros m. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). destruct (m (Z_to_bv 64 0x10aeca)) as [b|]; [exists b; reflexivity|]. vm_compute. wd_eexists; reflexivity. Qed.
Lemma rdn1_ex_10af0b : forall m : mem, exists b, rdn BSEGS m (Z_to_bv 64 0x10aecb) 1 = Some [b].
Proof. intros m. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). destruct (m (Z_to_bv 64 0x10aecb)) as [b|]; [exists b; reflexivity|]. vm_compute. wd_eexists; reflexivity. Qed.

Lemma restrict_mkstD : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn4_of_bytes : forall (m : mem) (a : word) x0 x1 x2 x3,
  (bv_unsigned a + 4 < 2 ^ 64)%Z ->
  rdn BSEGS m a 1 = Some [x0] -> rdn BSEGS m (at_ a 1) 1 = Some [x1] -> rdn BSEGS m (at_ a 2) 1 = Some [x2] -> rdn BSEGS m (at_ a 3) 1 = Some [x3] ->
  rdn BSEGS m a 4 = Some [x0; x1; x2; x3].
Proof.
  intros m a x0 x1 x2 x3 Hnw H0 H1 H2 H3. pose proof (u64_range a) as Ha.
  change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))). change 4%nat with (1 + (1 + (1 + 1)))%nat.
  apply rdn_cat; [exact H0 | | lia]. apply rdn_cat; [exact H1 | | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
  rewrite at_at. apply rdn_cat; [exact H2 | | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. rewrite at_at. exact H3.
Qed.

Lemma nth_error_snoc_d : forall {A} (l : list A) (x : A), nth_error (l ++ [x]) (length l) = Some x.
Proof. intros A l x. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma regs_kept_trans : forall R1 R2 R3, regs_kept R1 R2 -> regs_kept R2 R3 -> regs_kept R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). exact (A r Hr). Qed.

(* [comment removed for export] *)
Ltac feed H :=
  lazymatch type of H with
  | ?A -> ?B =>
      lazymatch type of A with
      | Prop => let HA := fresh "HA" in
                assert (HA : A) by (first [assumption | hlia | lia]); specialize (H HA); clear HA; feed H
      | _ => idtac
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Lemma WFX_drain : forall {RC : run_ceil} bt st1 Lc FF, WFX bt st1 Lc FF -> WFX bt (op_drain st1) Lc FF.
Proof.
  intros RC bt st1 Lc FF (qt & qg & W & Q & K).
  apply (WFX_intro bt _ _ _ _ _ (OPS_WFq_drain_pf bt st1 Lc FF qt qg W)); [| exact K].
  destruct W as (_ & _ & (_ & _ & Q3 & Q4 & _) & _). unfold AsKSys7b.qroom in *. clear - Q Q3 Q4. lia.
Qed.

Lemma WFX_x : forall {RC : run_ceil} bt st Lc FF, WFX bt st Lc FF -> WFx bt st Lc FF.
Proof. intros RC bt st Lc FF (qt & qg & W & _). exists qt, qg. exact W. Qed.

Section TOPD.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable MINSZ : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELL_msz : In (0x10ab58 + 792, 8%nat, 2 ^ 28) (bt_consts bt).    (* [comment removed for export] *)
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ < 2 ^ 64.
  Hypothesis HYP_RECYCLE : HYP_RECYCLE_stmt bt FXOK 1376.

  #[local] Abbreviation T := (bt_thread bt).

  Theorem hyp_drain_pf : HYP_DRAIN_stmt bt FXOK 1376.
  Proof using HYP_RECYCLE G_min CELL_min CELL_msz BT_ia BT_segs MINSZ.
    (lazymatch goal with |- ?G => let G' := eval unfold HYP_DRAIN_stmt in G in change_no_check G' end).
    intros fx st1 Lc FF M mdl R sp ret stk HFX HH MW WX RP TQne QB40 GQ28 X1 X2 X10 X11 X12 X13 X4 SP16 SPlo SPhi RET SOK.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hsp.
    pose proof WX as (qt1 & qg1 & Wq & _).
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st1 Lc FF Wq) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    pose proof (fixed_members bt st1 Lc FF Wq) as (_ & _ & _ & INT & _).
    pose proof (space_vs_fixed bt st1 Lc FF Wq _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    unfold IB in X10. rewrite BT_ia in X10. cbn [ia_instance both_addrs] in X10.
    unfold PTRHI in SPhi. unfold AS_HEAPLO, AS_LO, PG, KSPACE, BATCHSZ in *.
    set (S := at_ sp 2208).
    assert (US : U S = U sp + 2208) by ((lazymatch goal with |- ?G => let G' := eval unfold S in G in change_no_check G' end); rewrite at_u by lia; reflexivity).
    assert (ES : at_ S (-2208) = sp) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (HS7 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite US; clear - CR SPlo SPhi Hsp; lia).
    assert (HT7 : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | rewrite US; clear - GTC SPlo; lia]. }
    (* [comment removed for export] *)
    assert (ETQ0 : exists b0 q0, a_tq st1 = b0 :: q0) by (destruct (a_tq st1) as [|b0 q0]; [exfalso; exact (TQne eq_refl) | exists b0, q0; reflexivity]).
    destruct ETQ0 as (b0 & q0 & ETQ).
    destruct (list_nil_or_snoc (a_tq st1)) as [E0 | (q1 & bl' & ETQ')]; [exfalso; exact (TQne E0)|].
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct TQ as (Qlen & Qfirst & Qlast & Qbytes).
    destruct R2 as (Inres & Insec & I680 & I880 & I881 & I984 & GQ & Iptr & Iwptr). destruct GQ as (Glen & Gfirst & Glast & Gbytes).
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    unfold IB in I880, I881, Glen, Gfirst, Glast, Gbytes. rewrite BT_ia in I880, I881, Glen, Gfirst, Glast, Gbytes.
    cbn [ia_instance both_addrs] in I880, I881, Glen, Gfirst, Glast, Gbytes.
    rewrite BT_segs in Qlen, Qfirst, Qlast, Qbytes, TW, I880, I881, Glen, Gfirst, Glast, Gbytes, R1.
    unfold T_QC in Qlen, Qfirst, Qlast, Qbytes.
    replace (match a_tq st1 with [] => 0 | b :: _ => ba_addr b end) with (ba_addr b0) in Qfirst by (rewrite ETQ; reflexivity).
    replace (match rev (a_tq st1) with [] => 0 | b :: _ => ba_addr b end) with (ba_addr bl') in Qlast by (rewrite ETQ', rev_app_distr; reflexivity).
    clear R4 R5 R7 R8 R9 R10 R11 R12 R15 R16 R17 R18 Tctx Ttop Tbot Tsw Tfs Tunw TPC Tback Ttid Ttls1 Ttls2 Inres Insec I680 I984 Iptr Iwptr.
    unfold PG, KSPACE, BATCHSZ in TW.
    (* [comment removed for export] *)
    assert (QA : 0 <= q_bytes (a_tq st1) /\ 0 <= q_bytes (a_gq st1) /\ 1 <= Z.of_nat (length (a_tq st1)) /\ q_bytes (a_tq st1) <= qt1 /\ q_bytes (a_gq st1) <= qg1
                 /\ 8192 * Z.of_nat (length (a_tq st1)) <= q_bytes (a_tq st1) /\ 8192 * Z.of_nat (length (a_gq st1)) <= q_bytes (a_gq st1)).
    { pose proof Wq as (_ & _ & (QT & QG & QTB & QGB & _) & _). rewrite Forall_forall in QT, QG.
      assert (IT : forall b, In b (a_tq st1) -> forall m0 n0, In (m0, n0) (ba_items b) -> 1 <= n0).
      { intros b Hb m0 n0 Hin. destruct (QT b Hb) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
      assert (IG : forall b, In b (a_gq st1) -> forall m0 n0, In (m0, n0) (ba_items b) -> 1 <= n0).
      { intros b Hb m0 n0 Hin. destruct (QG b Hb) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
      pose proof (q_bytes_ge (a_tq st1) IT) as G1. pose proof (q_bytes_ge (a_gq st1) IG) as G2.
      rewrite ETQ in G1 |- *. cbn [length] in G1 |- *. rewrite <- ETQ in G1 |- *.
      unfold BATCHSZ in G1, G2. clear - G1 G2 QTB QGB. repeat split; lia. }
    destruct QA as (QA1 & QA2 & QA3 & QA4 & QA5 & QA6 & QA7).
    assert (Hb0 : In b0 (a_tq st1 ++ a_gq st1)) by (rewrite ETQ; left; reflexivity).
    assert (Hbl' : In bl' (a_tq st1 ++ a_gq st1)) by (rewrite ETQ'; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
    pose proof (batch_facts bt st1 Lc FF Wq b0 Hb0) as (_ & _ & F01 & F02). unfold BATCHSZ, KSPACE in F01, F02.
    pose proof (batch_facts bt st1 Lc FF Wq bl' Hbl') as (_ & _ & L01 & L02). unfold BATCHSZ, KSPACE in L01, L02.
    (* [comment removed for export] *)
    set (Hd := HID st1 mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st1 mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_thread bt st1 Lc FF M mdl Wq RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHB : forall b z, In b (a_tq st1 ++ a_gq st1) -> ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros b z Hb Hz. pose proof (batch_facts bt st1 Lc FF Wq b Hb) as (_ & _ & GB1 & GB2). unfold BATCHSZ, KSPACE in GB1, GB2.
      apply HID_notlazy; [clear - GB1 GB2 Hz SB0 SB1 CR; lia|].
      apply (rep_nolazy_batch bt st1 Lc FF M mdl Wq RP b); [exact Hb | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    assert (K_len : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (a_tq st1)))))).
    { apply (cellZ_restrict Hd M _ 8 _ Qlen); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHT]. }
    assert (K_first : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr b0)))).
    { replace (T + 88) with (T + 80 + 8) by lia. apply (cellZ_restrict Hd M _ 8 _ Qfirst); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHT]. }
    assert (K_lastq : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr bl')))).
    { replace (T + 96) with (T + 80 + 16) by lia. apply (cellZ_restrict Hd M _ 8 _ Qlast); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHT]. }
    assert (K_qb : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_tq st1))))).
    { replace (T + 104) with (T + 80 + 24) by lia. apply (cellZ_restrict Hd M _ 8 _ Qbytes); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHT]. }
    assert (K_glen : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (a_gq st1)))))).
    { apply (cellZ_restrict Hd M _ 8 _ Glen); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
    assert (K_gqb : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_gq st1))))).
    { replace (0x10ab58 + 912) with (0x10ab58 + 888 + 24) by lia. apply (cellZ_restrict Hd M _ 8 _ Gbytes); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
    assert (K_max : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28)))).
    { apply (cellZ_restrict Hd M _ 8 _ (const_cell bt _ _ _ _ R1 CELL_msz)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
    assert (K_min : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 800)) 8 = Some (LE8 (Z_to_bv 64 MINSZ))).
    { apply (cellZ_restrict Hd M _ 8 _ (const_cell bt _ _ _ _ R1 CELL_min)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
    (* [comment removed for export] *)
    destruct (rdn1_ex_10af0a (mrestrict Hd M)) as [b2 Hb2]. destruct (rdn1_ex_10af0b (mrestrict Hd M)) as [b3 Hb3].
    assert (K_lock : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]).
    { apply rdn4_of_bytes; [wd_ulia | | | exact Hb2 | exact Hb3].
      - unfold byteZ, cellN in I880. rewrite w2b1 in I880 by lia. rewrite rdn_mrestrict; [exact I880 | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs].
      - unfold byteZ, cellN in I881. rewrite w2b1 in I881 by lia.
        replace (at_ (Z_to_bv 64 0x10aec8) 1) with (Z_to_bv 64 (0x10ab58 + 881) : word) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity).
        rewrite rdn_mrestrict; [exact I881 | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS (mrestrict Hd M) (at_ S (-2256)) 48 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
      apply (proj2 (SOK x ltac:(lia))). }
    assert (SOKT : store_ok BSEGS (mrestrict Hd M) (Z_to_bv 64 (T + 80)) 32 = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHT].
      apply (writableZ_store_ok M _ _ _ _ TW); wd_ulia_c. }
    (* [comment removed for export] *)
    assert (X2' : getr R 2 = at_ S (-2208)) by (rewrite ES; exact X2).
    assert (X11' : getr R 11 = at_ (Z_to_bv 64 T) 80) by (rewrite X11; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_QC in G in change_no_check G' end); wd_ulia).
    assert (Hlen : 1 <= Z.of_nat (length (a_tq st1)) < 2 ^ 40) by (clear - QA3 QA6 QB40; lia).
    assert (Hqb : 0 <= q_bytes (a_tq st1) < 2 ^ 40) by (clear - QA1 QB40; lia).
    assert (Hglen : 0 <= Z.of_nat (length (a_gq st1)) < 2 ^ 40) by (clear - QA7 GQ28; lia).
    assert (Hgqb : 0 <= q_bytes (a_gq st1) < 2 ^ 40) by (clear - QA2 GQ28; lia).
    assert (Hfirst : 0 <= ba_addr b0 < 2 ^ 64) by (clear - F01 F02 SB0 SB1 CR; lia).
    assert (Hlastq : 0 <= ba_addr bl' < 2 ^ 64) by (clear - L01 L02 SB0 SB1 CR; lia).
    assert (Hb10 : U (Z_to_bv 8 0) = 0) by reflexivity.
    (* [comment removed for export] *)
    assert (PRIVT : forall z, T <= z < T + 4096 -> rt_priv (bt_ia bt) Lc FF z).
    { intros z Hz. apply (OBL_rt_private_pf bt st1 Lc FF Wq). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (PRIVB : forall b z, In b (a_tq st1 ++ a_gq st1) -> ba_addr b <= z < ba_addr b + 8192 -> rt_priv (bt_ia bt) Lc FF z).
    { intros b z Hb Hz. apply (OBL_rt_private_pf bt st1 Lc FF Wq). right. exists b. split; [exact Hb | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
    assert (PRIVI : forall z, 0x10ab58 <= z < 0x10b9b8 -> in_wins (ia_priv (bt_ia bt)) z).
    { intros z Hz. rewrite BT_ia. exists 0x10ab58, 0x10b9b8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | am_tauto ] | exact Hz]. }
    (* [comment removed for export] *)
    destruct (list_nil_or_snoc (a_gq st1)) as [EG0 | (g1 & bl & EGQ)].
    - (* [comment removed for export] *)
      assert (Hglen0 : Z.of_nat (length (a_gq st1)) = 0) by (rewrite EG0; reflexivity).
      remember (fr_d7e (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as ME eqn:EME.
      (* [comment removed for export] *)
      pose proof (fr_d7e_foot (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as FT. feed FT. rewrite <- EME in FT.
      pose proof (fr_d7e_grows (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as GRE. feed GRE. rewrite <- EME in GRE.
      pose proof (fr_d7e_q80 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq80. feed Cq80. pose proof (fr_d7e_q88 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq88. feed Cq88.
      pose proof (fr_d7e_q96 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq96. feed Cq96. pose proof (fr_d7e_q104 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq104. feed Cq104.
      pose proof (fr_d7e_g888 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg888. feed Cg888. pose proof (fr_d7e_g896 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg896. feed Cg896.
      pose proof (fr_d7e_g904 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg904. feed Cg904. pose proof (fr_d7e_g912 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg912. feed Cg912.
      pose proof (fr_d7e_b880 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb880. feed Cb880. pose proof (fr_d7e_b881 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb881. feed Cb881.
      pose proof (fr_d7e_b882 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb882. feed Cb882. pose proof (fr_d7e_b883 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb883. feed Cb883.
      rewrite <- EME in Cq80, Cq88, Cq96, Cq104, Cg888, Cg896, Cg904, Cg912, Cb880, Cb881, Cb882, Cb883.
      (* [comment removed for export] *)
      assert (POSTE : forall mdl3, MInv (a_aa st1) mdl3 -> same_but_materialized mdl mdl3 ->
                Rep bt (op_drain st1) Lc FF (munrestrict Hd M ME) mdl3
                /\ mem_grows M (munrestrict Hd M ME)
                /\ (forall a : word, munrestrict Hd M ME a <> M a -> drain_changed bt 1376 Lc FF (U sp) (U a) /\ munrestrict Hd M ME a <> None)).
      { intros mdl3 MI3 SBM3.
        set (Mfin := munrestrict Hd M ME).
        assert (VIS : forall a : word, Hd a = false -> Mfin a = ME a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
        assert (HIDv : forall a : word, Hd a = true -> Mfin a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
        assert (MrM : forall a : word, Hd a = false -> mrestrict Hd M a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
        assert (GRfin : mem_grows M Mfin).
        { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRE. rewrite (MrM a Eh). exact Ha. }
        assert (DIFF : forall a : word, Mfin a <> M a ->
                  (U S - 2256 <= U a < U S - 2208) \/ (0x10aec8 <= U a < 0x10aecc) \/ (0x10aed0 <= U a < 0x10aef0) \/ (T + 80 <= U a < T + 112)).
        { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
          rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT a NE). }
        assert (XF : forall c bs0, 0 <= c -> c + 8 <= 2 ^ 64 -> (forall z, c <= z < c + 8 -> Hd (Z_to_bv 64 z) = false) ->
                  rdn BSEGS ME (Z_to_bv 64 c) 8 = Some bs0 -> rdn BSEGS Mfin (Z_to_bv 64 c) 8 = Some bs0).
        { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same BSEGS Mfin ME); [| wd_ulia_c | exact Hr].
          intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
        assert (XB : forall c b, 0 <= c < 2 ^ 64 -> Hd (Z_to_bv 64 c) = false -> ME (Z_to_bv 64 c) = Some b -> rdn BSEGS Mfin (Z_to_bv 64 c) 1 = Some [b]).
        { intros c b Hc NH E. apply rdn1_of_some. rewrite (VIS _ NH). exact E. }
        split; [| split; [exact GRfin|]].
        - (* [comment removed for export] *)
          apply (OPS_REP_drain_pf bt st1 Lc FF M Mfin mdl mdl3 (a_tq st1) (WFX_x bt st1 Lc FF WX) RP eq_refl TQne).
          + (* [comment removed for export] *)
            intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
            { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
              assert (D : M a <> None) by (rewrite E0; discriminate). apply GRfin in D. rewrite EF in D. exact (D eq_refl). }
            (lazymatch goal with |- ?G => let G' := eval unfold foot_drain in G in change_no_check G' end). rewrite EG0. (lazymatch goal with |- ?G => let G' := eval cbn [rev] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_QC, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            destruct (DIFF a NE) as [X|[X|[X|X]]].
            * do 5 right. rewrite US in X. clear - X SPlo CR. lia.
            * right; left. lia.
            * right; right; left. lia.
            * left. lia.
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80) with (T + 80) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq80].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 8) with (T + 88) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq88].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 16) with (T + 96) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq96].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 24) with (T + 104) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq104].
          + (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by lia.
            replace (0x10ab58 + 880) with 0x10aec8 by reflexivity. apply XB; [lia | apply NHs; lia | exact Cb880].
          + (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by lia.
            replace (0x10ab58 + 881) with 0x10aec9 by reflexivity. apply XB; [lia | apply NHs; lia | exact Cb881].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite Hglen0, Z.add_0_l.
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg888].
          + intros b q Eb. rewrite EG0 in Eb. cbn [app] in Eb. rewrite ETQ in Eb. injection Eb as <- _.
            (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg896].
          + intros q blq Eq. rewrite ETQ' in Eq. apply app_inj_tail in Eq. destruct Eq as [_ <-].
            (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg904].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg912].
          + intros g bl b q Eg _. exfalso. rewrite EG0 in Eg. destruct g; discriminate Eg.
          + exact SBM3.
          + exact MI3.
          + (* [comment removed for export] *)
            intros _ a Ha. unfold IB in Ha. rewrite BT_ia in Ha. cbn [ia_instance both_addrs] in Ha.
            rewrite (VIS a) by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Ha; lia]).
            rewrite EME. apply fr_d7e_def896; [exact HT7 | clear - Ha; lia].
        - (* [comment removed for export] *)
          intros a NE. split; [| destruct (Mfin a) eqn:EF; [discriminate|]; exfalso; apply NE; destruct (M a) eqn:E0; [|reflexivity];
                                  exfalso; assert (D : M a <> None) by (rewrite E0; discriminate); apply GRfin in D; rewrite EF in D; exact (D eq_refl)].
          (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end). destruct (DIFF a NE) as [X|[X|[X|X]]].
          + left. rewrite US in X. lia.
          + right; right. apply PRIVI. lia.
          + right; right. apply PRIVI. lia.
          + right; left. apply PRIVT. lia. }
      (* [comment removed for export] *)
      destruct (Z.le_gt_cases (q_bytes (a_gq st1) + q_bytes (a_tq st1)) (2 ^ 28)) as [NR | RCY].
      + (* [comment removed for export] *)
        destruct (drain_nr_e (mrestrict Hd M) (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T
                    (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (q_bytes (a_gq st1))
                    (Z_to_bv 8 0) b2 b3 R)
          as (rf & RUN & Z2 & Z8 & Z9 & Z18 & Z19 & Z3 & Z4 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
        all: try assumption. all: try reflexivity.
        all: let k := numgoals in guard k = 1.
        rewrite <- EME in RUN.
        replace (0x4e260%bv : word) with (Z_to_bv 64 0x4e260 : word) in RUN by (apply bv_eq; reflexivity).
        apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st1 Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st1)
                 (@mkst fx R (Z_to_bv 64 0x4e260) M (seg_rom BSEGS)) (@mkst fx rf ret ME (seg_rom BSEGS)) mdl).
        { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstD. exact RUN. }
        intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst. change (ms_mem _) with M.
        pose proof (same_but_materialized_frame mdl mdl3 SBM3) as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
        destruct (POSTE mdl3 MI3 SBM3) as (REP3 & GR3 & CH3).
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold drain_post in G in change_no_check G' end). exists fx, (op_drain st1), (munrestrict Hd M ME), mdl3, rf.
        split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh3; exact HH|].
        split; [exact (OPS_WF_drain_pf bt st1 Lc FF (WFX_x bt st1 Lc FF WX) NR)|]. split; [exact REP3|]. split; [reflexivity|].
        split; [split; [intros h HLE; unfold holes_le in HLE |- *; exact HLE | apply fk_drain]|].
        split; [intros a NE; destruct (CH3 a NE) as [D1 D2]; exact (conj D1 (or_introl D2))|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|].
        split; [apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity; symmetry; exact X2'|].
        split; [apply same_but_materialized_except_vm; exact SBM3|]. exact (model_ivs_wf_sbm mdl mdl3 SBM3 MW).
      + (* [comment removed for export] *)
        destruct (drain_rc_e (mrestrict Hd M) (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 12) stk T
                    (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (q_bytes (a_gq st1))
                    (Z_to_bv 8 0) b2 b3 R MINSZ)
          as (rf & RUN & W1 & W2 & W10 & W11 & W12 & W13 & W8 & W9 & W18 & W19 & W3 & W4 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
        all: try assumption. all: try reflexivity.
        all: let k := numgoals in guard k = 1.
        rewrite <- EME in RUN.
        replace (0x4e260%bv : word) with (Z_to_bv 64 0x4e260 : word) in RUN by (apply bv_eq; reflexivity).
        apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st1 Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st1)
                 (@mkst fx R (Z_to_bv 64 0x4e260) M (seg_rom BSEGS))
                 (@mkst fx rf (0x4e404%bv : word) (wbytes ME (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]) (seg_rom BSEGS)) mdl).
        { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstD. exact RUN. }
        intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst. change (ms_mem _) with M.
        pose proof (same_but_materialized_frame mdl mdl3 SBM3) as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
        destruct (POSTE mdl3 MI3 SBM3) as (REP3 & GR3 & CH3).
        set (M0 := munrestrict Hd M ME) in *. set (Mrc := munrestrict Hd M (wbytes ME (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])).
        assert (NHL : forall k, 0 <= k < 4 -> Hd (Z_to_bv 64 (0x10aec8 + k)) = false) by (intros k Hk; apply NHs; lia).
        assert (GRrc : mem_grows M0 Mrc).
        { intros a Ha. unfold M0, Mrc in *. destruct (Hd a) eqn:Eh.
          - rewrite munrestrict_on by exact Eh. rewrite munrestrict_on in Ha by exact Eh. exact Ha.
          - rewrite munrestrict_off by exact Eh. rewrite munrestrict_off in Ha by exact Eh. apply wbytes_grows. exact Ha. }
        assert (DRC : forall a : word, Mrc a <> M0 a -> U a = IB bt + 881).
        { intros a NE. pose proof (u64_range a) as Ha. unfold M0, Mrc in NE. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
          destruct (Hd a) eqn:Eh; [exfalso; apply NE; rewrite !munrestrict_on by exact Eh; reflexivity|].
          rewrite !munrestrict_off in NE by exact Eh.
          destruct (Z.lt_ge_cases (U a) 0x10aec8) as [L|G]; [exfalso; apply NE; apply wbytes_outside; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia|].
          destruct (Z.lt_ge_cases (U a) 0x10aecc) as [L2|G2]; [|exfalso; apply NE; apply wbytes_outside; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia].
          rewrite wbytes_inside in NE by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). revert NE. unorm.
          destruct (Z.eq_dec (U a) 0x10aec8) as [E|N1].
          { rewrite E. replace a with (Z_to_bv 64 0x10aec8 : word) by (apply bv_eq; wd_ulia). rewrite Cb880. intros X; exfalso; apply X; reflexivity. }
          destruct (Z.eq_dec (U a) 0x10aec9) as [E|N2]; [intros _; lia|].
          destruct (Z.eq_dec (U a) 0x10aeca) as [E|N3].
          { rewrite E. replace a with (Z_to_bv 64 0x10aeca : word) by (apply bv_eq; wd_ulia). rewrite Cb882. intros X; exfalso; apply X; reflexivity. }
          assert (E : U a = 0x10aecb) by lia.
          rewrite E. replace a with (Z_to_bv 64 0x10aecb : word) by (apply bv_eq; wd_ulia). rewrite Cb883. intros X; exfalso; apply X; reflexivity. }
        assert (L881 : Mrc (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 1)).
        { (lazymatch goal with |- ?G => let G' := eval unfold Mrc, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). replace (0x10ab58 + 881) with (0x10aec8 + 1) by reflexivity.
          rewrite munrestrict_off by (apply NHL; lia). rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. reflexivity. }
        assert (D904 : forall a : word, IB bt + 904 <= U a < IB bt + 912 -> Mrc a <> None).
        { intros a Ha. unfold IB in Ha. rewrite BT_ia in Ha. cbn [ia_instance both_addrs] in Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mrc in G in change_no_check G' end).
          rewrite munrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Ha; lia]).
          apply wbytes_grows. rewrite EME. apply fr_d7e_def904; [exact HT7 | clear - Ha; lia]. }
        assert (D880 : M0 (Z_to_bv 64 (IB bt + 880)) = Some (Z_to_bv 8 0) /\ M0 (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 0)).
        { (lazymatch goal with |- ?G => let G' := eval unfold M0, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
          replace (0x10ab58 + 880) with 0x10aec8 by reflexivity. replace (0x10ab58 + 881) with 0x10aec9 by reflexivity.
          rewrite !munrestrict_off by (apply NHs; clear; lia). exact (conj Cb880 Cb881). }
        assert (W2s : getr rf 2 = sp) by (rewrite W2; exact ES).
        assert (W12s : getr rf 12 = Z_to_bv 64 (T + T_PC)) by (rewrite W12; exact X12).
        assert (W10s : getr rf 10 = Z_to_bv 64 (IB bt + 728)) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); rewrite BT_ia; exact W10).
        assert (MIN : exists mn, getr rf 11 = Z_to_bv 64 mn /\ In (IB bt + 800, 8%nat, mn) (bt_consts bt)).
        { exists MINSZ. split; [exact W11|]. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). exact CELL_min. }
        assert (GQB : 2 ^ 28 < q_bytes (a_gq (op_drain st1)) < 2 ^ 41).
        { (lazymatch goal with |- ?G => let G' := eval cbn [a_gq op_drain set_gq set_tq] in G in change_no_check G' end). rewrite q_bytes_app. clear - RCY QB40 GQ28 QA1 QA2. lia. }
        assert (SOKrc : forall a : word, U sp - 1376 <= U a < U sp -> Mrc a <> None /\ store_ok BSEGS Mrc a 1%nat = true).
        { intros a Ha. destruct (SOK a Ha) as [D1 D2]. split; [apply GRrc; apply GR3; exact D1 | eapply store_ok_mono; [exact GRrc | eapply store_ok_mono; [exact GR3 | exact D2]]]. }
        replace (0x4e404%bv : word) with (Z_to_bv 64 0x4e404 : word) by (apply bv_eq; reflexivity).
        change (munrestrict Hd M (wbytes ME (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])) with Mrc.
        apply (katD_conseq BSEGS _ _ _
                 (HYP_RECYCLE fx (op_drain st1) Lc FF Mrc M0 mdl3 rf sp ret stk HFX ltac:(rewrite Eh3; exact HH) (model_ivs_wf_sbm mdl mdl3 SBM3 MW)
                    (WFX_drain bt st1 Lc FF WX) eq_refl GQB REP3 DRC L881 D904 (proj1 D880) (proj2 D880) W1 W2s W10s W12s W13 MIN ltac:(rewrite W4; exact X4) SP16 SPlo SPhi RET SOKrc)).
        intros c' POST.
        destruct POST as (fx5 & st3 & M5 & mdl5 & R5 & Ec & HFX5 & HH5 & W5 & RP5 & KA5 & HO5 & CH5 & LZ5 & RK5 & SEV5 & MW5).
        exists fx5, st3, M5, mdl5, R5.
        split; [exact Ec|]. split; [exact HFX5|]. split; [exact HH5|]. split; [exact W5|]. split; [exact RP5|].
        split; [rewrite KA5; reflexivity|].
        split; [split; [intros h HLE; apply (proj1 HO5); unfold holes_le in HLE |- *; exact HLE | exact (fk_trans _ _ _ (fk_drain st1) (proj2 HO5))]|].
        split.
        { intros a NE. destruct (decide (M5 a = Mrc a)) as [E5|N5].
          - rewrite E5 in NE |- *. destruct (decide (Mrc a = M0 a)) as [E0|N0].
            + rewrite E0 in NE |- *. destruct (CH3 a NE) as [D1 D2]. exact (conj D1 (or_introl D2)).
            + pose proof (DRC a N0) as Ea. unfold IB in Ea. rewrite BT_ia in Ea. cbn [ia_instance both_addrs] in Ea.
              assert (Ea' : a = Z_to_bv 64 (IB bt + 881)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end); wd_ulia).
              split.
              * (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end). right; right. apply PRIVI. lia.
              * left. rewrite Ea', L881. discriminate.
          - exact (CH5 a N5). }
        split.
        { intros a Ha. transitivity (lzb mdl3 a); [exact (LZ5 a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity]. }
        split.
        { apply (regs_kept_trans R rf R5); [| exact RK5].
          apply regs_kept_intro; rewrite ?W2s, ?W3, ?W4, ?W8, ?W9, ?W18, ?W19, ?W20, ?W21, ?W22, ?W23, ?W24, ?W25, ?W26, ?W27; try reflexivity. symmetry; exact X2. }
        split; [| exact MW5].
        eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM3 | exact SEV5].
    - (* [comment removed for export] *)
      assert (EGQ0 : exists bg0 gq0, a_gq st1 = bg0 :: gq0) by (destruct (a_gq st1) as [|x y]; [destruct g1; discriminate EGQ | exists x, y; reflexivity]).
      destruct EGQ0 as (bg0 & gq0 & EGQ0).
      assert (Hglen1 : 1 <= Z.of_nat (length (a_gq st1))) by (rewrite EGQ0; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia).
      assert (Hbl : In bl (a_tq st1 ++ a_gq st1)) by (apply in_app_iff; right; rewrite EGQ; apply in_app_iff; right; left; reflexivity).
      pose proof (batch_facts bt st1 Lc FF Wq bl Hbl) as (_ & _ & G01 & G02). unfold BATCHSZ, KSPACE in G01, G02.
      assert (Hglast : 2 ^ 44 <= ba_addr bl /\ ba_addr bl + 8192 <= U S - 3584) by (rewrite US; clear - G01 G02 SBH SB1 SPlo CR; lia).
      assert (HglastT : ba_addr bl + 8192 <= T \/ T + 4096 <= ba_addr bl) by (clear - SPT G01 G02; lia).
      assert (Hokgl : store_ok BSEGS (mrestrict Hd M) (Z_to_bv 64 (ba_addr bl)) 8 = true).
      { destruct (R6 (length g1) bl ltac:(rewrite EGQ; apply nth_error_snoc_d)) as (_ & _ & _ & _ & WB). rewrite BT_segs in WB. unfold BATCHSZ in WB.
        rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; apply hid_off_of; intros z Hz; split; [lia | apply (NHB bl); [exact Hbl | lia]]].
        apply (writableZ_store_ok M _ _ _ _ WB); wd_ulia_c. }
      assert (K_glast : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 904)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr bl)))).
      { replace (match rev (a_gq st1) with [] => 0 | b :: _ => ba_addr b end) with (ba_addr bl) in Glast by (rewrite EGQ, rev_app_distr; reflexivity).
        replace (0x10ab58 + 904) with (0x10ab58 + 888 + 16) by lia. apply (cellZ_restrict Hd M _ 8 _ Glast); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
      assert (K_gfirst : rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr bg0)))).
      { replace (match a_gq st1 with [] => 0 | b :: _ => ba_addr b end) with (ba_addr bg0) in Gfirst by (rewrite EGQ0; reflexivity).
        replace (0x10ab58 + 896) with (0x10ab58 + 888 + 8) by lia. apply (cellZ_restrict Hd M _ 8 _ Gfirst); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHs]. }
      remember (fr_d7n (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as MN eqn:EMN.
      (* [comment removed for export] *)
      pose proof (fr_d7n_foot (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as FT. feed FT. rewrite <- EMN in FT.
      pose proof (fr_d7n_grows (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as GRE. feed GRE. rewrite <- EMN in GRE.
      pose proof (fr_d7n_q80 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq80. feed Cq80. pose proof (fr_d7n_q88 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq88. feed Cq88.
      pose proof (fr_d7n_q96 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq96. feed Cq96. pose proof (fr_d7n_q104 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cq104. feed Cq104.
      pose proof (fr_d7n_g888 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg888. feed Cg888.
      pose proof (fr_d7n_g896 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg896. feed Cg896. specialize (Cg896 _ K_gfirst).
      pose proof (fr_d7n_next (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cnext. feed Cnext.
      pose proof (fr_d7n_g904 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg904. feed Cg904. pose proof (fr_d7n_g912 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cg912. feed Cg912.
      pose proof (fr_d7n_b880 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb880. feed Cb880. pose proof (fr_d7n_b881 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb881. feed Cb881.
      pose proof (fr_d7n_b882 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb882. feed Cb882. pose proof (fr_d7n_b883 (mrestrict Hd M) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1)) (Z_to_bv 8 0) b2 b3) as Cb883. feed Cb883.
      rewrite <- EMN in Cq80, Cq88, Cq96, Cq104, Cg888, Cg896, Cnext, Cg904, Cg912, Cb880, Cb881, Cb882, Cb883.
      (* [comment removed for export] *)
      assert (POSTN : forall mdl3, MInv (a_aa st1) mdl3 -> same_but_materialized mdl mdl3 ->
                Rep bt (op_drain st1) Lc FF (munrestrict Hd M MN) mdl3
                /\ mem_grows M (munrestrict Hd M MN)
                /\ (forall a : word, munrestrict Hd M MN a <> M a -> drain_changed bt 1376 Lc FF (U sp) (U a) /\ munrestrict Hd M MN a <> None)).
      { intros mdl3 MI3 SBM3.
        set (Mfin := munrestrict Hd M MN).
        assert (VIS : forall a : word, Hd a = false -> Mfin a = MN a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
        assert (HIDv : forall a : word, Hd a = true -> Mfin a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
        assert (MrM : forall a : word, Hd a = false -> mrestrict Hd M a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
        assert (GRfin : mem_grows M Mfin).
        { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRE. rewrite (MrM a Eh). exact Ha. }
        assert (DIFF : forall a : word, Mfin a <> M a ->
                  (U S - 2256 <= U a < U S - 2208) \/ (0x10aec8 <= U a < 0x10aecc) \/ (ba_addr bl <= U a < ba_addr bl + 8)
                  \/ (0x10aed0 <= U a < 0x10aed8) \/ (0x10aee0 <= U a < 0x10aef0) \/ (T + 80 <= U a < T + 112)).
        { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
          rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT a NE). }
        assert (XF : forall c bs0, 0 <= c -> c + 8 <= 2 ^ 64 -> (forall z, c <= z < c + 8 -> Hd (Z_to_bv 64 z) = false) ->
                  rdn BSEGS MN (Z_to_bv 64 c) 8 = Some bs0 -> rdn BSEGS Mfin (Z_to_bv 64 c) 8 = Some bs0).
        { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same BSEGS Mfin MN); [| wd_ulia_c | exact Hr].
          intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
        assert (XB : forall c b, 0 <= c < 2 ^ 64 -> Hd (Z_to_bv 64 c) = false -> MN (Z_to_bv 64 c) = Some b -> rdn BSEGS Mfin (Z_to_bv 64 c) 1 = Some [b]).
        { intros c b Hc NH E. apply rdn1_of_some. rewrite (VIS _ NH). exact E. }
        split; [| split; [exact GRfin|]].
        - (* [comment removed for export] *)
          apply (OPS_REP_drain_pf bt st1 Lc FF M Mfin mdl mdl3 (a_tq st1) (WFX_x bt st1 Lc FF WX) RP eq_refl TQne).
          + (* [comment removed for export] *)
            intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
            { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
              assert (D : M a <> None) by (rewrite E0; discriminate). apply GRfin in D. rewrite EF in D. exact (D eq_refl). }
            (lazymatch goal with |- ?G => let G' := eval unfold foot_drain in G in change_no_check G' end). rewrite EGQ, rev_app_distr. (lazymatch goal with |- ?G => let G' := eval cbn [rev app] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_QC, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            destruct (DIFF a NE) as [X|[X|[X|[X|[X|X]]]]].
            * do 5 right. rewrite US in X. clear - X SPlo CR. lia.
            * right; left. lia.
            * do 3 right; left. exact X.
            * right; right; left. lia.
            * right; right; left. lia.
            * left. lia.
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80) with (T + 80) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq80].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 8) with (T + 88) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq88].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 16) with (T + 96) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq96].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 24) with (T + 104) by lia. apply XF; [lia | lia | intros z Hz; apply NHT; lia | exact Cq104].
          + (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by lia.
            replace (0x10ab58 + 880) with 0x10aec8 by reflexivity. apply XB; [lia | apply NHs; lia | exact Cb880].
          + (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by lia.
            replace (0x10ab58 + 881) with 0x10aec9 by reflexivity. apply XB; [lia | apply NHs; lia | exact Cb881].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg888].
          + intros b q Eb. rewrite EGQ0 in Eb. cbn [app] in Eb. injection Eb as <- _.
            (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg896].
          + intros q blq Eq. rewrite ETQ' in Eq. apply app_inj_tail in Eq. destruct Eq as [_ <-].
            (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg904].
          + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
            apply XF; [lia | lia | intros z Hz; apply NHs; lia | exact Cg912].
          + intros g blx b q Eg Eb. rewrite EGQ in Eg. apply app_inj_tail in Eg. destruct Eg as [_ <-]. rewrite ETQ in Eb. injection Eb as <- _.
            (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply (NHB bl); [exact Hbl | lia] | exact Cnext].
          + exact SBM3.
          + exact MI3.
          + (* [comment removed for export] *)
            intros EGE. exfalso. rewrite EGQ in EGE. apply app_eq_nil in EGE. destruct EGE as [_ EGE]. discriminate EGE.
        - (* [comment removed for export] *)
          intros a NE. split; [| destruct (Mfin a) eqn:EF; [discriminate|]; exfalso; apply NE; destruct (M a) eqn:E0; [|reflexivity];
                                  exfalso; assert (D : M a <> None) by (rewrite E0; discriminate); apply GRfin in D; rewrite EF in D; exact (D eq_refl)].
          (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end). destruct (DIFF a NE) as [X|[X|[X|[X|[X|X]]]]].
          + left. rewrite US in X. lia.
          + right; right. apply PRIVI. lia.
          + right; left. apply (PRIVB bl); [exact Hbl | lia].
          + right; right. apply PRIVI. lia.
          + right; right. apply PRIVI. lia.
          + right; left. apply PRIVT. lia. }
      (* [comment removed for export] *)
      destruct (Z.le_gt_cases (q_bytes (a_gq st1) + q_bytes (a_tq st1)) (2 ^ 28)) as [NR | RCY].
      + (* [comment removed for export] *)
        destruct (drain_nr_n (mrestrict Hd M) (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) T
                    (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1))
                    (Z_to_bv 8 0) b2 b3 R)
          as (rf & RUN & Z2 & Z8 & Z9 & Z18 & Z19 & Z3 & Z4 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
        all: try assumption. all: try reflexivity.
        all: let k := numgoals in guard k = 1.
        rewrite <- EMN in RUN.
        replace (0x4e260%bv : word) with (Z_to_bv 64 0x4e260 : word) in RUN by (apply bv_eq; reflexivity).
        apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st1 Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st1)
                 (@mkst fx R (Z_to_bv 64 0x4e260) M (seg_rom BSEGS)) (@mkst fx rf ret MN (seg_rom BSEGS)) mdl).
        { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstD. exact RUN. }
        intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst. change (ms_mem _) with M.
        pose proof (same_but_materialized_frame mdl mdl3 SBM3) as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
        destruct (POSTN mdl3 MI3 SBM3) as (REP3 & GR3 & CH3).
        apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold drain_post in G in change_no_check G' end). exists fx, (op_drain st1), (munrestrict Hd M MN), mdl3, rf.
        split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh3; exact HH|].
        split; [exact (OPS_WF_drain_pf bt st1 Lc FF (WFX_x bt st1 Lc FF WX) NR)|]. split; [exact REP3|]. split; [reflexivity|].
        split; [split; [intros h HLE; unfold holes_le in HLE |- *; exact HLE | apply fk_drain]|].
        split; [intros a NE; destruct (CH3 a NE) as [D1 D2]; exact (conj D1 (or_introl D2))|].
        split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|].
        split; [apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity; symmetry; exact X2'|].
        split; [apply same_but_materialized_except_vm; exact SBM3|]. exact (model_ivs_wf_sbm mdl mdl3 SBM3 MW).
      + (* [comment removed for export] *)
        destruct (drain_rc_n (mrestrict Hd M) (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 12) stk T
                    (Z.of_nat (length (a_tq st1))) (ba_addr b0) (ba_addr bl') (q_bytes (a_tq st1)) (Z.of_nat (length (a_gq st1))) (ba_addr bl) (q_bytes (a_gq st1))
                    (Z_to_bv 8 0) b2 b3 R MINSZ)
          as (rf & RUN & W1 & W2 & W10 & W11 & W12 & W13 & W8 & W9 & W18 & W19 & W3 & W4 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
        all: try assumption. all: try reflexivity.
        all: let k := numgoals in guard k = 1.
        rewrite <- EMN in RUN.
        replace (0x4e260%bv : word) with (Z_to_bv 64 0x4e260 : word) in RUN by (apply bv_eq; reflexivity).
        apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st1 Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st1)
                 (@mkst fx R (Z_to_bv 64 0x4e260) M (seg_rom BSEGS))
                 (@mkst fx rf (0x4e404%bv : word) (wbytes MN (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]) (seg_rom BSEGS)) mdl).
        { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstD. exact RUN. }
        intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst. change (ms_mem _) with M.
        pose proof (same_but_materialized_frame mdl mdl3 SBM3) as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
        destruct (POSTN mdl3 MI3 SBM3) as (REP3 & GR3 & CH3).
        set (M0 := munrestrict Hd M MN) in *. set (Mrc := munrestrict Hd M (wbytes MN (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])).
        assert (NHL : forall k, 0 <= k < 4 -> Hd (Z_to_bv 64 (0x10aec8 + k)) = false) by (intros k Hk; apply NHs; lia).
        assert (GRrc : mem_grows M0 Mrc).
        { intros a Ha. unfold M0, Mrc in *. destruct (Hd a) eqn:Eh.
          - rewrite munrestrict_on by exact Eh. rewrite munrestrict_on in Ha by exact Eh. exact Ha.
          - rewrite munrestrict_off by exact Eh. rewrite munrestrict_off in Ha by exact Eh. apply wbytes_grows. exact Ha. }
        assert (DRC : forall a : word, Mrc a <> M0 a -> U a = IB bt + 881).
        { intros a NE. pose proof (u64_range a) as Ha. unfold M0, Mrc in NE. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
          destruct (Hd a) eqn:Eh; [exfalso; apply NE; rewrite !munrestrict_on by exact Eh; reflexivity|].
          rewrite !munrestrict_off in NE by exact Eh.
          destruct (Z.lt_ge_cases (U a) 0x10aec8) as [L|G]; [exfalso; apply NE; apply wbytes_outside; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia|].
          destruct (Z.lt_ge_cases (U a) 0x10aecc) as [L2|G2]; [|exfalso; apply NE; apply wbytes_outside; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia].
          rewrite wbytes_inside in NE by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). revert NE. unorm.
          destruct (Z.eq_dec (U a) 0x10aec8) as [E|N1].
          { rewrite E. replace a with (Z_to_bv 64 0x10aec8 : word) by (apply bv_eq; wd_ulia). rewrite Cb880. intros X; exfalso; apply X; reflexivity. }
          destruct (Z.eq_dec (U a) 0x10aec9) as [E|N2]; [intros _; lia|].
          destruct (Z.eq_dec (U a) 0x10aeca) as [E|N3].
          { rewrite E. replace a with (Z_to_bv 64 0x10aeca : word) by (apply bv_eq; wd_ulia). rewrite Cb882. intros X; exfalso; apply X; reflexivity. }
          assert (E : U a = 0x10aecb) by lia.
          rewrite E. replace a with (Z_to_bv 64 0x10aecb : word) by (apply bv_eq; wd_ulia). rewrite Cb883. intros X; exfalso; apply X; reflexivity. }
        assert (L881 : Mrc (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 1)).
        { (lazymatch goal with |- ?G => let G' := eval unfold Mrc, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). replace (0x10ab58 + 881) with (0x10aec8 + 1) by reflexivity.
          rewrite munrestrict_off by (apply NHL; lia). rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia). unorm. reflexivity. }
        assert (D904 : forall a : word, IB bt + 904 <= U a < IB bt + 912 -> Mrc a <> None).
        { intros a Ha. unfold IB in Ha. rewrite BT_ia in Ha. cbn [ia_instance both_addrs] in Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mrc in G in change_no_check G' end).
          rewrite munrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Ha; lia]).
          apply wbytes_grows. rewrite EMN. apply fr_d7n_def904; [exact HT7 | clear - Ha; lia]. }
        assert (D880 : M0 (Z_to_bv 64 (IB bt + 880)) = Some (Z_to_bv 8 0) /\ M0 (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 0)).
        { (lazymatch goal with |- ?G => let G' := eval unfold M0, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
          replace (0x10ab58 + 880) with 0x10aec8 by reflexivity. replace (0x10ab58 + 881) with 0x10aec9 by reflexivity.
          rewrite !munrestrict_off by (apply NHs; clear; lia). exact (conj Cb880 Cb881). }
        assert (W2s : getr rf 2 = sp) by (rewrite W2; exact ES).
        assert (W12s : getr rf 12 = Z_to_bv 64 (T + T_PC)) by (rewrite W12; exact X12).
        assert (W10s : getr rf 10 = Z_to_bv 64 (IB bt + 728)) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); rewrite BT_ia; exact W10).
        assert (MIN : exists mn, getr rf 11 = Z_to_bv 64 mn /\ In (IB bt + 800, 8%nat, mn) (bt_consts bt)).
        { exists MINSZ. split; [exact W11|]. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). exact CELL_min. }
        assert (GQB : 2 ^ 28 < q_bytes (a_gq (op_drain st1)) < 2 ^ 41).
        { (lazymatch goal with |- ?G => let G' := eval cbn [a_gq op_drain set_gq set_tq] in G in change_no_check G' end). rewrite q_bytes_app. clear - RCY QB40 GQ28 QA1 QA2. lia. }
        assert (SOKrc : forall a : word, U sp - 1376 <= U a < U sp -> Mrc a <> None /\ store_ok BSEGS Mrc a 1%nat = true).
        { intros a Ha. destruct (SOK a Ha) as [D1 D2]. split; [apply GRrc; apply GR3; exact D1 | eapply store_ok_mono; [exact GRrc | eapply store_ok_mono; [exact GR3 | exact D2]]]. }
        replace (0x4e404%bv : word) with (Z_to_bv 64 0x4e404 : word) by (apply bv_eq; reflexivity).
        change (munrestrict Hd M (wbytes MN (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])) with Mrc.
        apply (katD_conseq BSEGS _ _ _
                 (HYP_RECYCLE fx (op_drain st1) Lc FF Mrc M0 mdl3 rf sp ret stk HFX ltac:(rewrite Eh3; exact HH) (model_ivs_wf_sbm mdl mdl3 SBM3 MW)
                    (WFX_drain bt st1 Lc FF WX) eq_refl GQB REP3 DRC L881 D904 (proj1 D880) (proj2 D880) W1 W2s W10s W12s W13 MIN ltac:(rewrite W4; exact X4) SP16 SPlo SPhi RET SOKrc)).
        intros c' POST.
        destruct POST as (fx5 & st3 & M5 & mdl5 & R5 & Ec & HFX5 & HH5 & W5 & RP5 & KA5 & HO5 & CH5 & LZ5 & RK5 & SEV5 & MW5).
        exists fx5, st3, M5, mdl5, R5.
        split; [exact Ec|]. split; [exact HFX5|]. split; [exact HH5|]. split; [exact W5|]. split; [exact RP5|].
        split; [rewrite KA5; reflexivity|].
        split; [split; [intros h HLE; apply (proj1 HO5); unfold holes_le in HLE |- *; exact HLE | exact (fk_trans _ _ _ (fk_drain st1) (proj2 HO5))]|].
        split.
        { intros a NE. destruct (decide (M5 a = Mrc a)) as [E5|N5].
          - rewrite E5 in NE |- *. destruct (decide (Mrc a = M0 a)) as [E0|N0].
            + rewrite E0 in NE |- *. destruct (CH3 a NE) as [D1 D2]. exact (conj D1 (or_introl D2)).
            + pose proof (DRC a N0) as Ea. unfold IB in Ea. rewrite BT_ia in Ea. cbn [ia_instance both_addrs] in Ea.
              assert (Ea' : a = Z_to_bv 64 (IB bt + 881)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end); wd_ulia).
              split.
              * (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end). right; right. apply PRIVI. lia.
              * left. rewrite Ea', L881. discriminate.
          - exact (CH5 a N5). }
        split.
        { intros a Ha. transitivity (lzb mdl3 a); [exact (LZ5 a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity]. }
        split.
        { apply (regs_kept_trans R rf R5); [| exact RK5].
          apply regs_kept_intro; rewrite ?W2s, ?W3, ?W4, ?W8, ?W9, ?W18, ?W19, ?W20, ?W21, ?W22, ?W23, ?W24, ?W25, ?W26, ?W27; try reflexivity. symmetry; exact X2. }
        split; [| exact MW5].
        eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM3 | exact SEV5].
  Qed.
End TOPD.
End BoAllocFTopD.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L BoAllocFRc2 BoAllocFRc2U BoAllocFRcR1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG BoAllocFRcL BoAllocFRcH BoAllocFRcK4a BoAllocFRcK4b BoAllocFRcK4c BoAllocFRcK1a.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Lemma rdn1_exK : forall (m : mem) c, c = 0x10aeca \/ c = 0x10aecb -> exists b, rdn BSEGS m (Z_to_bv 64 c) 1 = Some [b].
Proof. intros m c [-> | ->]; (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end); (match goal with |- context [m ?a] => destruct (m a) as [b|] end; [exists b; reflexivity|]); vm_compute; wd_eexists; reflexivity. Qed.
Lemma rdn1_of_someK : forall (m : mem) (a : word) b, m a = Some b -> rdn BSEGS m a 1 = Some [b].
Proof. intros m a b E. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite E. reflexivity. Qed.
Lemma rdn4_of_bytesK : forall (m : mem) (a : word) x0 x1 x2 x3,
  (bv_unsigned a + 4 < 2 ^ 64)%Z ->
  rdn BSEGS m a 1 = Some [x0] -> rdn BSEGS m (at_ a 1) 1 = Some [x1] -> rdn BSEGS m (at_ a 2) 1 = Some [x2] -> rdn BSEGS m (at_ a 3) 1 = Some [x3] ->
  rdn BSEGS m a 4 = Some [x0; x1; x2; x3].
Proof.
  intros m a x0 x1 x2 x3 Hnw H0 H1 H2 H3. pose proof (u64_range a) as Ha.
  change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))). change 4%nat with (1 + (1 + (1 + 1)))%nat.
  apply rdn_cat; [exact H0 | | lia]. apply rdn_cat; [exact H1 | | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
  rewrite at_at. apply rdn_cat; [exact H2 | | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. rewrite at_at. exact H3.
Qed.

(* [comment removed for export] *)
Lemma chain_cells_nth : forall (m : mem) l i t, chain_cells m l -> nth_error l i = Some t ->
  rdn BSEGS m (Z_to_bv 64 (p_addr t)) 8 = Some (LE8 (Z_to_bv 64 (match nth_error l (Datatypes.S i) with Some t' => p_addr t' | None => 0 end))).
Proof.
  intros m l. induction l as [|t0 r IH]; intros i t CH Hi; [destruct i; discriminate Hi|].
  cbn [chain_cells] in CH. destruct CH as [C0 CH]. destruct i as [|i].
  - cbn in Hi. injection Hi as <-. (lazymatch goal with |- ?G => let G' := eval cbn [nth_error] in G in change_no_check G' end). destruct r; exact C0.
  - cbn [nth_error] in Hi |- *. exact (IH i t CH Hi).
Qed.

Section K1.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable MINSZ : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition XP (pb0 : list batch) (z : Z) : Prop := qhdr bt z \/ exists b, In b pb0 /\ ba_addr b <= z < ba_addr b + BATCHSZ.
  Lemma XP_dec : forall pb0, Xdec (XP pb0).
  Proof using.
    intros pb0. apply Xdec_or; [(lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); apply Xdec_iv|].
    apply (Xdec_ex_list pb0 (fun b z => ba_addr b <= z < ba_addr b + BATCHSZ)). intros b. apply Xdec_iv.
  Qed.

  (* [comment removed for export] *)
  Definition arm_nomerge (st : ast) : Prop :=
    q_bytes (a_gq st) <= 8192 * Z.of_nat (length (a_gq st)) \/ 1638400 * Z.of_nat (length (a_gq st)) <= 100 * q_bytes (a_gq st).

  Definition rc_pre_post (st2 : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) (R : bvmap 5 word) (S ret : word) (c' : config) : Prop :=
    exists fx1 (M1 : mem) mdl1 (R1 : bvmap 5 word) pb0 rest,
      c' = mkCfg (@mkst fx1 R1 (Z_to_bv 64 0x4e7e4) M1 (seg_rom BSEGS)) mdl1
      /\ a_gq st2 = pb0 ++ rest /\ pb0 <> [] /\ q_bytes rest <= MINSZ
      /\ invb bt FXOK S (XP pb0) (q_bytes (a_tq st2)) (q_bytes (a_gq st2)) Lc FF st2 M1 mdl1 rest (Z_to_bv 64 0x4e574)
              (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
              fx1 st2 M1 mdl1 R1 pb0
      /\ getr R1 10 = Z_to_bv 64 (Z.of_nat (length pb0))
      /\ rep_list bt M1 (IB bt + 888) rest
      /\ (rdn BSEGS M1 (at_ S (-2216)) 8 = Some (LE8 ret) /\ rdn BSEGS M1 (at_ S (-2224)) 8 = Some (LE8 (getr R 8))
          /\ rdn BSEGS M1 (at_ S (-2232)) 8 = Some (LE8 (getr R 9)) /\ rdn BSEGS M1 (at_ S (-2240)) 8 = Some (LE8 (getr R 18))
          /\ rdn BSEGS M1 (at_ S (-2248)) 8 = Some (LE8 (getr R 19)) /\ rdn BSEGS M1 (at_ S (-2256)) 8 = Some (LE8 (getr R 20)))
      /\ dr_keep R R1
      /\ (forall a : word, M1 a <> M a ->
            ((U S - 2400 <= U a < U S - 2208) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a)) /\ M1 a <> None)
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdl1 /\ same_except_vm mdl mdl1.

  Theorem rc_prefix_kat : forall fx st2 Lc FF (M M0 : mem) mdl (R : bvmap 5 word) (sp ret stk : word),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFX bt st2 Lc FF -> a_tq st2 = [] -> 2 ^ 28 < q_bytes (a_gq st2) < 2 ^ 41 -> arm_nomerge st2 ->
    Rep bt st2 Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> U a = IB bt + 881) -> M (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 1) ->
    (forall a : word, IB bt + 904 <= U a < IB bt + 912 -> M a <> None) ->
    M0 (Z_to_bv 64 (IB bt + 880)) = Some (Z_to_bv 8 0) -> M0 (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 0) ->
    getr R 1 = ret -> getr R 2 = sp ->
    getr R 10 = Z_to_bv 64 (IB bt + 728) -> getr R 12 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 13 = stk ->
    getr R 11 = Z_to_bv 64 MINSZ ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
    U sp mod 16 = 0 -> CEIL + 1376 <= U sp -> U sp + 2224 <= PTRHI -> ret_ok ret ->
    (forall a : word, U sp - 1376 <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS)) mdl)
         (rc_pre_post st2 Lc FF M mdl R (at_ sp 2208) ret).
  Proof using G_min BT_ia BT_segs.
    intros fx st2 Lc FF M M0 mdl R sp ret stk HFX HH MW WX ETQ GQB NOM RP DM L881 D904 D880 D881 X1 X2 X10 X12 X13 X11 X4 SP16 SPlo SPhi RET SOK.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hsp. unfold PTRHI in SPhi.
    pose proof (WFX_WFq bt st2 Lc FF WX) as W.
    set (gq := a_gq st2) in *. set (k := npop MINSZ gq). set (pb0 := firstn k gq). set (rest := skipn k gq). set (l := trips gq k).
    assert (EGQ : a_gq st2 = pb0 ++ rest) by ((lazymatch goal with |- ?G => let G' := eval unfold pb0, rest in G in change_no_check G' end); fold gq; symmetry; apply firstn_skipn).
    set (S := at_ sp 2208).
    assert (US : U S = U sp + 2208) by ((lazymatch goal with |- ?G => let G' := eval unfold S in G in change_no_check G' end); rewrite at_u by lia; reflexivity).
    assert (ES : at_ S (-2208) = sp) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (HS7 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite US; clear - CR SPlo SPhi Hsp; lia).
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st2 Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    assert (SZ : forall b m n, In b gq -> In (m, n) (ba_items b) -> 0 <= n).
    { intros b m n Hb Hin. destruct W as (_ & _ & (_ & QG & _) & _). rewrite Forall_forall in QG.
      destruct (QG b Hb) as (_ & _ & WI). destruct (WI m n Hin) as [Xn _]. clear - Xn. lia. }
    assert (BF : forall b, In b gq -> SBEG <= ba_addr b /\ ba_addr b + 8192 <= SBEG + 2 ^ 37 /\ 8192 <= ba_bytes b /\ Z.of_nat (length (ba_items b)) <= 1021).
    { intros b Hb. destruct (batch_facts bt st2 Lc FF W b ltac:(apply in_app_iff; right; exact Hb)) as (_ & L0 & G1 & G2).
      pose proof (AsAinvOpsRc3.ba_bytes_ge b ltac:(intros m0 n0 Hin0; exact (SZ b m0 n0 Hb Hin0))) as G4.
      unfold KSPACE, BATCHSZ, BATCHCAP in *. clear - L0 G1 G2 G4. lia. }
    unfold KSPACE, PG, AS_HEAPLO in *.
    assert (GLEN : 8192 * Z.of_nat (length gq) <= q_bytes gq).
    { pose proof (AsAinvOpsRc3.q_bytes_ge gq ltac:(intros b0 m0 n0 Hb0 Hin0; exact (SZ b0 m0 n0 Hb0 Hin0))) as G1. unfold BATCHSZ in G1. exact G1. }
    assert (NEgq : gq <> []) by (intros E; rewrite E in GQB; cbn in GQB; clear - GQB; lia).
    assert (Hk : (1 <= k <= length gq)%nat) by (split; [apply npop_pos; exact NEgq | apply npop_le]).
    assert (RNGq : forall b, In b gq -> 0 <= ba_bytes b /\ 0 <= ba_addr b < 2 ^ 64).
    { intros b Hb. destruct (BF b Hb) as (G1 & G2 & G3 & _). clear - G1 G2 G3 SB0 SB1 CR. lia. }
    assert (POK : pops_ok MINSZ (nxaddr gq) (q_bytes gq) l) by (apply pops_ok_trips; [exact RNGq | clear - GQB G_min; lia | clear - G_min; lia]).
    assert (RESTB : q_bytes rest <= MINSZ) by (apply rest_bytes; [intros b Hb; exact (proj1 (RNGq b Hb)) | clear - G_min; lia]).
    assert (LLEN : length l = k) by (apply trips_len; clear - Hk; lia).
    assert (PB0in : forall b, In b pb0 -> In b gq) by (intros b Hb; unfold pb0 in Hb; exact (firstn_InK _ _ _ Hb)).
    assert (NEpb : pb0 <> []).
    { (lazymatch goal with |- ?G => let G' := eval unfold pb0 in G in change_no_check G' end). destruct gq as [|b0 gq']; [exfalso; exact (NEgq eq_refl)|]. destruct k; [clear - Hk; lia | discriminate]. }
    (* [comment removed for export] *)
    pose proof RP as (_ & Ri & _ & _ & _ & RBg & _ & _ & _ & _ & _ & _ & R13 & R14 & _). fold gq in RBg.
    destruct Ri as (_ & _ & _ & I880 & I881 & _ & (Glen & Gfirst & Glast & Gbytes) & _). fold gq in Glen, Gfirst, Glast, Gbytes.
    destruct R14 as (B1 & B2 & _).
    rewrite BT_segs in I880, I881, Glen, Gfirst, Glast, Gbytes.
    unfold IB in I880, I881, Glen, Gfirst, Glast, Gbytes, DM, L881, D904, D880, D881, X10.
    rewrite BT_ia in I880, I881, Glen, Gfirst, Glast, Gbytes, DM, L881, D904, D880, D881, X10.
    cbn [ia_instance both_addrs] in I880, I881, Glen, Gfirst, Glast, Gbytes, DM, L881, D904, D880, D881, X10.
    assert (EQM : forall a : word, ~ (U a = 0x10ab58 + 881) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (DM a N)). }
    assert (GR0 : mem_grows M0 M).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha|].
      replace a with (Z_to_bv 64 (0x10ab58 + 881) : word) by (apply bv_eq; rewrite (DM a N); reflexivity). rewrite L881. discriminate. }
    set (Hd := HID st2 mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st2 mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHB : forall b z, In b gq -> ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros b z Hb Hz. destruct (BF b Hb) as (G1 & G2 & _). apply HID_notlazy; [clear - Hz G1 G2 SB0 SB1 CR; lia|].
      apply (rep_nolazy_batch bt st2 Lc FF M0 mdl W RP b z ltac:(apply in_app_iff; right; exact Hb)). (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). exact Hz. }
    pose (memD := mrestrict Hd M).
    pose (XL := fun z : Z => z = 0x10ab58 + 881).
    (* [comment removed for export] *)
    assert (IMGC : forall c v, cellZ BSEGS M0 c 8 v -> 0x10ab58 + 888 <= c -> c + 8 <= 0x10ab58 + 920 -> rdn BSEGS memD (Z_to_bv 64 c) 8 = Some (LE8 (Z_to_bv 64 v))).
    { intros c v C H1 H2. apply (cellX Hd M M0 XL c 8 v C EQM); [clear - H1; lia | clear - H2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [(lazymatch goal with |- ?G => let G' := eval unfold XL in G in change_no_check G' end); clear - Hz H1; lia | apply NHs; [clear - Hz H1 H2; lia | right; clear - Hz H1 H2; lia]]. }
    assert (K_glen : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length gq))))) by (apply IMGC; [exact Glen | clear; lia | clear; lia]).
    assert (K_first : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some (LE8 (Z_to_bv 64 (nxaddr gq)))).
    { replace (0x10ab58 + 896) with (0x10ab58 + 888 + 8) by (clear; lia). apply IMGC; [exact Gfirst | clear; lia | clear; lia]. }
    assert (K_gqb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes gq)))).
    { replace (0x10ab58 + 912) with (0x10ab58 + 888 + 24) by (clear; lia). apply IMGC; [exact Gbytes | clear; lia | clear; lia]. }
    (* [comment removed for export] *)
    destruct (rdn1_exK M 0x10aeca (or_introl eq_refl)) as [b2 Hb2]. destruct (rdn1_exK M 0x10aecb (or_intror eq_refl)) as [b3 Hb3].
    assert (K_lock : rdn BSEGS memD (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [| clear; wd_ulia_c | clear - NHs; unorm; apply hid_off_of; intros z Hz; split; [lia | apply NHs; [lia | right; lia]]].
      apply rdn4_of_bytesK; [clear; wd_ulia | | | |].
      - unfold byteZ, cellN in I880. rewrite w2b1 in I880 by (clear; lia). eapply rd_same; [| clear; wd_ulia_c | exact I880].
        intros x Hx. apply EQM. clear - Hx. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - replace (at_ (Z_to_bv 64 0x10aec8) 1) with (Z_to_bv 64 (0x10ab58 + 881) : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity).
        exact (rdn1_of_someK M _ _ L881).
      - replace (at_ (Z_to_bv 64 0x10aec8) 2) with (Z_to_bv 64 0x10aeca : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb2.
      - replace (at_ (Z_to_bv 64 0x10aec8) 3) with (Z_to_bv 64 0x10aecb : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb3. }
    (* [comment removed for export] *)
    assert (BCELL : forall b c v, In b gq -> cellZ BSEGS M0 c 8 v -> ba_addr b <= c -> c + 8 <= ba_addr b + 8192 -> rdn BSEGS memD (Z_to_bv 64 c) 8 = Some (LE8 (Z_to_bv 64 v))).
    { intros b c v Hb C H1 H2. destruct (BF b Hb) as (G1 & G2 & _).
      apply (cellX Hd M M0 XL c 8 v C EQM); [clear - H1 G1 SB0; lia | clear - H2 G2 SB1 CR; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [(lazymatch goal with |- ?G => let G' := eval unfold XL in G in change_no_check G' end); clear - Hz H1 G1 SBH; lia | apply (NHB b); [exact Hb | clear - Hz H1 H2; lia]]. }
    assert (CELLSl : Forall (fun t => rdn BSEGS memD (Z_to_bv 64 (p_addr t)) 8 = Some (LE8 (Z_to_bv 64 (p_nx t)))
                                      /\ rdn BSEGS memD (Z_to_bv 64 (p_addr t + 8)) 8 = Some (LE8 (Z_to_bv 64 (p_sz t)))) l).
    { apply trips_forall. intros i b Hi Hb. (lazymatch goal with |- ?G => let G' := eval cbn [p_addr p_nx p_sz fst snd] in G in change_no_check G' end). pose proof (nth_error_In _ _ Hb) as Hin.
      destruct (RBg i b Hb) as (C1 & C2 & _). rewrite BT_segs in C1, C2. rewrite nxaddr_skipn. split.
      - apply (BCELL b); [exact Hin | exact C1 | clear; lia | clear; lia].
      - apply (BCELL b); [exact Hin | exact C2 | clear; lia | clear; lia]. }
    assert (SOKl : Forall (fun t => store_ok BSEGS memD (Z_to_bv 64 (p_addr t)) 8 = true) l).
    { apply trips_forall. intros i b Hi Hb. (lazymatch goal with |- ?G => let G' := eval cbn [p_addr fst] in G in change_no_check G' end). pose proof (nth_error_In _ _ Hb) as Hin. destruct (BF b Hin) as (G1 & G2 & _).
      destruct (RBg i b Hb) as (_ & _ & _ & _ & BW). rewrite BT_segs in BW. unfold BATCHSZ in BW.
      apply (sokX Hd M M0 _ _ (ba_addr b) 8 BW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - G2 SB1 CR; lia | clear - G1 SB0; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply (NHB b); [exact Hin | clear - Hz; lia]. }
    assert (GEOl : Forall (fun t => AIMGHI <= p_addr t /\ p_addr t + 8192 <= U S - 3584) l).
    { apply trips_forall. intros i b Hi Hb. (lazymatch goal with |- ?G => let G' := eval cbn [p_addr fst] in G in change_no_check G' end). destruct (BF b (nth_error_In _ _ Hb)) as (G1 & G2 & _). rewrite US. clear - G1 G2 SBH SB1 SPlo. lia. }
    assert (NDgq : List.NoDup (map ba_addr gq)).
    { pose proof W as (_ & _ & (_ & _ & _ & _ & ND & _) & _). rewrite ETQ in ND. exact ND. }
    assert (SEPl : all_sep (map p_addr l)).
    { (lazymatch goal with |- ?G => let G' := eval unfold l in G in change_no_check G' end). rewrite trips_addr. fold pb0. apply all_sep_of.
      - assert (EGQ' : gq = pb0 ++ rest) by exact EGQ. rewrite EGQ', map_app in NDgq. exact (NoDup_app_remove_r _ _ NDgq).
      - intros x y Hx Hy NE. apply in_map_iff in Hx. apply in_map_iff in Hy. destruct Hx as (bx & <- & Hbx). destruct Hy as (by' & <- & Hby).
        destruct (batch_facts bt st2 Lc FF W bx ltac:(apply in_app_iff; right; exact (PB0in _ Hbx))) as (CVx & _).
        destruct (batch_facts bt st2 Lc FF W by' ltac:(apply in_app_iff; right; exact (PB0in _ Hby))) as (CVy & _).
        destruct (chunk_cases bt st2 Lc FF W BATCHCLASS (ba_addr bx) BATCHCLASS (ba_addr by') ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVx CVy) as [[_ E] | D];
          [exfalso; exact (NE E) | change (csize BATCHCLASS) with 8192 in D; (lazymatch goal with |- ?G => let G' := eval unfold bsep in G in change_no_check G' end); exact D]. }
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2400)) 192 = true).
    { replace (at_ S (-2400)) with (Z_to_bv 64 (U S - 2400) : word) by (clear - HS7; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - HS7; lia | clear - HS7; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz US Hsp SPlo CR. unorm. lia.
      - apply NHs; [clear - Hz US Hsp SPlo CR; lia | left; clear - Hz US SPlo; lia]. }
    assert (P_first : 0 <= nxaddr gq < 2 ^ 64).
    { destruct gq as [|b0 g'] eqn:EG; [exfalso; exact (NEgq eq_refl)|]. (lazymatch goal with |- ?G => let G' := eval cbn [nxaddr] in G in change_no_check G' end). exact (proj2 (RNGq b0 (or_introl eq_refl))). }
    (* [comment removed for export] *)
    destruct (run_rc_pre memD (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                (Z_to_bv 64 (T + T_PC)) stk MINSZ (Z.of_nat (length gq)) (q_bytes gq) (nxaddr gq) b2 b3 l R
                X1 ltac:(rewrite ES; exact X2) X10 X11 X12 X13 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HS7
                ltac:(clear - G_min; lia) ltac:(clear - GLEN GQB; lia) ltac:(clear - GQB; lia) GLEN NOM
                ltac:(clear - GQB G_min; lia) POK
                ltac:(rewrite LLEN; clear - Hk; lia) GEOl SEPl SOKstk SOKl K_lock K_glen K_gqb K_first CELLSl)
      as (r1 & mem' & RUN & PP & HR1 & A10 & A3 & A4 & A26 & A27).
    destruct PP as (PO & PG' & Pfirst & Plast & Plen & Pbytes & Ptsz & Ptlast & Psum & Ptfirst & Pprev & Pchain & Pdef).
    pose proof (fr_rc0_grows memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3) as GRa.
    pose proof (fr_rc0_outside memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3 HS7) as OUTa.
    remember (fr_rc0 memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3) as Ma eqn:EMa.
    pose proof (fr_dr0_outside (fr_rcu mem') S (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                  (Z_to_bv 64 (T + T_PC)) stk HS7) as OUTd.
    pose proof (fr_dr0_grows (fr_rcu mem') S (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                  (Z_to_bv 64 (T + T_PC)) stk) as GRd.
    assert (FRM : dr_frame bt S (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                    (fr_dr0 (fr_rcu mem') S (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                       (Z_to_bv 64 (T + T_PC)) stk)).
    { (lazymatch goal with |- ?G => let G' := eval unfold dr_frame in G in change_no_check G' end). repeat split; [apply fr_dr0_ra | apply fr_dr0_s0 | apply fr_dr0_s1 | apply fr_dr0_s2 | apply fr_dr0_s3 | apply fr_dr0_s4 | apply fr_dr0_s5
                                     | apply fr_dr0_s6 | apply fr_dr0_s7 | apply fr_dr0_s8 | apply fr_dr0_s9 | apply fr_dr0_a2]; exact HS7. }
    remember (fr_dr0 (fr_rcu mem') S (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                (Z_to_bv 64 (T + T_PC)) stk) as MF eqn:EMF.
    (* [comment removed for export] *)
    replace (0x4e404%bv : word) with (Z_to_bv 64 0x4e404 : word) in RUN by (apply bv_eq; reflexivity).
    replace (0x4e7e4%bv : word) with (Z_to_bv 64 0x4e7e4 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st2 Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st2)
             (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS)) (@mkst fx r1 (Z_to_bv 64 0x4e7e4) MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & _ & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GRF : mem_grows memD MF).
    { eapply mem_grows_trans; [exact GRa|]. eapply mem_grows_trans; [exact PG'|]. eapply mem_grows_trans; [apply fr_rcu_grows | exact GRd]. }
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF. rewrite (MrM a Eh). exact Ha. }
    assert (GR01 : mem_grows M0 M1) by (eapply mem_grows_trans; [exact GR0 | exact GR1]).
    (* [comment removed for export] *)
    pose (FOOT := fun z : Z => (U S - 2400 <= z < U S - 2208) \/ (0x10aec8 <= z < 0x10aecc) \/ loop_foot S 0 0 l z).
    assert (OUT1 : forall a : word, ~ FOOT (U a) -> M1 a = M a).
    { intros a NF. destruct (Hd a) eqn:Eh; [exact (HIDv a Eh)|]. rewrite (VIS a Eh), <- (MrM a Eh). unfold FOOT in NF.
      rewrite OUTd by (clear - NF; lia). rewrite fr_rcu_outside by (clear - NF; lia). rewrite (PO a ltac:(clear - NF; tauto)).
      apply OUTa; clear - NF; lia. }
    assert (FOOTd : Xdec FOOT).
    { assert (XC : forall (P : Prop), {P} + {~ P} -> Xdec (fun _ : Z => P)) by (intros P D z; exact D).
      (lazymatch goal with |- ?G => let G' := eval unfold FOOT, loop_foot in G in change_no_check G' end).
      apply Xdec_or; [apply Xdec_iv|]. apply Xdec_or; [apply Xdec_iv|].
      apply Xdec_or; [apply Xdec_iv|].
      apply Xdec_or; [apply Xdec_and; [apply XC; apply Z.eq_dec | apply Xdec_iv]|].
      apply Xdec_or; [apply Xdec_iv|].
      apply Xdec_or; [apply (Xdec_ex_list l (fun t z0 => p_addr t <= z0 < p_addr t + 8)); intros t; apply Xdec_iv|].
      apply Xdec_or; [apply Xdec_and; [apply XC; right; intros N; exact (N eq_refl) | apply Xdec_iv]|].
      apply Xdec_or; [apply Xdec_and; [apply XC; left; reflexivity | apply Xdec_iv]|].
      apply Xdec_or; apply Xdec_iv. }
    assert (CH1 : forall a : word, M1 a <> M a -> FOOT (U a)).
    { intros a NE. destruct (FOOTd (U a)) as [F | NF]; [exact F | exfalso; exact (NE (OUT1 a NF))]. }
    assert (DEF01 : forall a : word, M1 a <> M0 a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR01 in D. exact (D E1). }
    rewrite Forall_forall in GEOl.
    assert (LFq : forall z, loop_foot S 0 0 l z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ (exists t, In t l /\ p_addr t <= z < p_addr t + 8) \/ (U S - 2288 <= z < U S - 2256)).
    { intros z F. unfold loop_foot in F. destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
        [left; clear - F; lia | left; clear - F; lia | left; clear - F; lia | right; left; exact F | exfalso; clear - F; lia
        | right; right; clear - F; lia | right; right; clear - F; lia | right; right; clear - F; lia]. }
    assert (MEMP : forall a : word, Hd a = false -> (U a < U S - 2400 \/ U S - 2288 <= U a) -> (U a < 0x10aec8 \/ 0x10aeca <= U a) -> M1 a = mem' a).
    { intros a Eh A1 A2. rewrite (VIS a Eh), OUTd by exact A1. apply fr_rcu_outside. exact A2. }
    assert (STK1 : forall kk v, -2400 <= kk -> kk + 8 <= -2208 -> rdn BSEGS MF (at_ S kk) 8 = Some v -> rdn BSEGS M1 (at_ S kk) 8 = Some v).
    { intros kk v Hk1 Hk2 Hr. eapply rd_same; [| clear - Hk1 Hk2 HS7; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range | left; clear - Hx Hk1 Hk2 HS7 US SPlo; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (STKP : forall kk v, -2288 <= kk -> kk + 8 <= -2208 -> rdn BSEGS mem' (at_ S kk) 8 = Some v -> rdn BSEGS M1 (at_ S kk) 8 = Some v).
    { intros kk v Hk1 Hk2 Hr. eapply rd_same; [| clear - Hk1 Hk2 HS7; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. assert (Hx' : U S - 2288 <= U x < U S - 2208) by (clear - Hx Hk1 Hk2 HS7; rewrite at_u in Hx by lia; cbn in Hx; lia).
      apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [apply u64_range | left; clear - Hx' US SPlo; lia] | right; clear - Hx'; lia | right; clear - Hx' HS7; lia]. }
    assert (STKA : forall kk v, -2256 <= kk -> kk + 8 <= -2208 -> rdn BSEGS Ma (at_ S kk) 8 = Some v -> rdn BSEGS M1 (at_ S kk) 8 = Some v).
    { intros kk v Hk1 Hk2 Hr. apply STKP; [clear - Hk1; lia | exact Hk2 |].
      eapply rd_same; [| clear - Hk1 Hk2 HS7; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. assert (Hx' : U S - 2256 <= U x < U S - 2208) by (clear - Hx Hk1 Hk2 HS7; rewrite at_u in Hx by lia; cbn in Hx; lia).
      apply PO. intros F. destruct (LFq _ F) as [Q | [(t & Ht & Q) | Q]]; [clear - Q Hx' HS7; lia | destruct (GEOl t Ht) as [G1 G2]; clear - Q Hx' G2; lia | clear - Q Hx'; lia]. }
    assert (IMGP : forall c v, 0x10ab58 + 888 <= c -> c + 8 <= 0x10ab58 + 920 -> rdn BSEGS mem' (Z_to_bv 64 c) 8 = Some v -> rdn BSEGS M1 (Z_to_bv 64 c) 8 = Some v).
    { intros c v H1 H2 Hr. eapply rd_same; [| clear - H1 H2; wd_ulia_c | exact Hr].
      intros x Hx. assert (Hx' : c <= U x < c + 8) by (clear - Hx H1 H2; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia).
      apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [apply u64_range | right; clear - Hx' H1 H2; lia] | left; clear - Hx' H2 HS7; lia | right; clear - Hx' H1; lia]. }
    assert (OBJP : forall b c v, In b gq -> ba_addr b <= c -> c + 8 <= ba_addr b + 8192 -> rdn BSEGS mem' (Z_to_bv 64 c) 8 = Some v -> rdn BSEGS M1 (Z_to_bv 64 c) 8 = Some v).
    { intros b c v Hb H1 H2 Hr. destruct (BF b Hb) as (G1 & G2 & _). eapply rd_same; [| clear - H1 H2 G1 G2 SB0 SB1 CR; wd_ulia_c | exact Hr].
      intros x Hx. assert (Hx' : c <= U x < c + 8) by (clear - Hx H1 H2 G1 G2 SB0 SB1 CR; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia).
      apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 x); apply (NHB b); [exact Hb | clear - Hx' H1 H2; lia] | left; clear - Hx' H2 G2 SB1 US SPlo; lia | right; clear - Hx' H1 G1 SBH; lia]. }
    (* [comment removed for export] *)
    assert (PSEP : forall bx by', In bx pb0 -> In by' pb0 -> ba_addr bx = ba_addr by' \/ ba_addr bx + 8192 <= ba_addr by' \/ ba_addr by' + 8192 <= ba_addr bx).
    { intros bx by' Hbx Hby.
      destruct (batch_facts bt st2 Lc FF W bx ltac:(apply in_app_iff; right; exact (PB0in _ Hbx))) as (CVx & _).
      destruct (batch_facts bt st2 Lc FF W by' ltac:(apply in_app_iff; right; exact (PB0in _ Hby))) as (CVy & _).
      destruct (chunk_cases bt st2 Lc FF W BATCHCLASS (ba_addr bx) BATCHCLASS (ba_addr by') ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVx CVy) as [[_ E] | D];
        [left; exact E | right; change (csize BATCHCLASS) with 8192 in D; exact D]. }
    (* [comment removed for export] *)
    assert (OBJ0 : forall b z, In b pb0 -> ba_addr b + 8 <= z < ba_addr b + 8192 -> M1 (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
    { intros b z Hb Hz. destruct (BF b (PB0in _ Hb)) as (G1 & G2 & _).
      assert (Uz : U (Z_to_bv 64 z) = z) by (clear - Hz G1 G2 SB0 SB1 CR; wd_ulia).
      rewrite OUT1; [apply EQM; rewrite Uz; clear - Hz G1 SBH; lia|]. rewrite Uz. (lazymatch goal with |- ?G => let G' := eval unfold FOOT in G in change_no_check G' end). intros [F | [F | F]].
      - clear - F Hz G2 SB1 US SPlo. lia.
      - clear - F Hz G1 SBH. lia.
      - destruct (LFq _ F) as [Q | [(t & Ht & Q) | Q]]; [clear - Q Hz G1 SBH; lia | | clear - Q Hz G2 SB1 US SPlo; lia].
        destruct (trips_in gq k t Ht) as (bt0 & Hbt0 & Ea & _). fold pb0 in Hbt0. rewrite Ea in Q.
        destruct (PSEP b bt0 Hb Hbt0) as [E | D]; [clear - E Q Hz; lia | clear - D Q Hz; lia]. }
    assert (Lpb0 : length pb0 = k) by ((lazymatch goal with |- ?G => let G' := eval unfold pb0 in G in change_no_check G' end); rewrite length_firstn; clear - Hk; lia).
    assert (EGQ' : gq = pb0 ++ rest) by exact EGQ.
    (* [comment removed for export] *)
    set (Xd := XP_dec pb0).
    assert (LK0 : M1 (Z_to_bv 64 0x10aec8) = Some (Z_to_bv 8 0) /\ M1 (Z_to_bv 64 0x10aec9) = Some (Z_to_bv 8 0)).
    { destruct (fr_rcu_lock mem') as [L0 L1]. split.
      - rewrite VIS by (apply NHs; [clear; lia | right; clear; lia]). rewrite OUTd by (left; clear - HS7; wd_ulia). exact L0.
      - rewrite VIS by (apply NHs; [clear; lia | right; clear; lia]). rewrite OUTd by (left; clear - HS7; wd_ulia). exact L1. }
    assert (RX1 : AsAinvOpsRc73.AsAinvRepX3.RepX bt (XP pb0) st2 Lc FF M1 mdl1).
    { exists (fun a : word => if Xd (U a) then M0 a else M1 a). split.
      - apply (Rep_frame_q bt st2 Lc FF M0 _ mdl1 W (Rep_sbm bt st2 Lc FF M0 mdl mdl1 RP MI1 SBM1)).
        intros a NE. destruct (Xd (U a)) as [HX | NX]; [exfalso; exact (NE eq_refl)|].
        split; [| exact (DEF01 a NE)].
        intros RCELL. destruct (FOOTd (U a)) as [F | NF].
        + destruct F as [F | [F | F]].
          * exact (ceil_not_cells bt st2 Lc FF W (U a) ltac:(clear - F US SPlo; lia) RCELL).
          * destruct (Z.eq_dec (U a) 0x10aec8) as [E0 | N0].
            { apply NE. replace a with (Z_to_bv 64 0x10aec8 : word) by (apply bv_eq; rewrite E0; reflexivity). rewrite (proj1 LK0). symmetry. exact D880. }
            destruct (Z.eq_dec (U a) 0x10aec9) as [E1 | N1].
            { apply NE. replace a with (Z_to_bv 64 0x10aec9 : word) by (apply bv_eq; rewrite E1; reflexivity). rewrite (proj2 LK0). symmetry. exact D881. }
            apply (instpad_not_cells bt st2 Lc FF W (U a)); [| exact RCELL]. (lazymatch goal with |- ?G => let G' := eval unfold instpad, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). clear - F N0 N1. lia.
          * destruct (LFq _ F) as [Q | [(t & Ht & Q) | Q]].
            -- apply NX. left. (lazymatch goal with |- ?G => let G' := eval unfold qhdr, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). exact Q.
            -- apply NX. right. destruct (trips_in gq k t Ht) as (b0 & Hb0 & Ea & _). exists b0. split; [exact Hb0|]. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). rewrite <- Ea. clear - Q. lia.
            -- exact (ceil_not_cells bt st2 Lc FF W (U a) ltac:(clear - Q US SPlo; lia) RCELL).
        + apply NE. rewrite (OUT1 a NF). apply EQM. intros E. apply NF. (lazymatch goal with |- ?G => let G' := eval unfold FOOT in G in change_no_check G' end). right; left. clear - E. lia.
      - intros a NE. destruct (Xd (U a)) as [HX | NX]; [| exfalso; exact (NE eq_refl)]. split; [exact HX | exact (DEF01 a NE)]. }
    assert (XSUB : forall z, XP pb0 z -> XB bt st2 z).
    { intros z [Q | (b & Hb & Hz)]; [left; exact Q | right]. exists (ba_addr b). split; [| exact Hz].
      destruct (batch_facts bt st2 Lc FF W b ltac:(apply in_app_iff; right; exact (PB0in _ Hb))) as (CVb & _).
      split; [exact CVb | left; exists b; split; [apply in_app_iff; right; exact (PB0in _ Hb) | reflexivity]]. }
    assert (QDEF1 : forall a : word, qhdr bt (U a) -> M1 a <> None).
    { intros a Q. unfold qhdr, IB in Q. rewrite BT_ia in Q. cbn [ia_instance both_addrs] in Q.
      destruct (Z_le_dec (0x10ab58 + 904) (U a)) as [L1 | L1]; [destruct (Z_lt_dec (U a) (0x10ab58 + 912)) as [L2 | L2]|].
      - apply GR1. apply D904. clear - L1 L2. lia.
      - rewrite MEMP; [apply Pdef; right; clear - Q L2; lia | rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Q; lia]
                      | left; clear - Q HS7; lia | right; clear - Q; lia].
      - rewrite MEMP; [apply Pdef; left; clear - Q L1; lia | rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Q; lia]
                      | left; clear - Q HS7; lia | right; clear - Q; lia]. }
    (* [comment removed for export] *)
    assert (RB1 : rep_batches bt M1 pb0).
    { intros i b Hb. destruct (nth_firstn_inv gq k i b Hb) as [Hi Hbg]. pose proof (nth_error_In _ _ Hbg) as Hin. pose proof (nth_error_In _ _ Hb) as Hin0.
      destruct (BF b Hin) as (G1 & G2 & G3 & G4). destruct (RBg i b Hbg) as (_ & C2 & C3 & C4 & BW). rewrite BT_segs in *. unfold BATCHSZ in BW.
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply (OBJP b (ba_addr b) _ Hin ltac:(clear; lia) ltac:(clear; lia)).
        pose proof (chain_cells_nth mem' l i _ Pchain (trips_nth_inv gq k i b Hi Hbg)) as CN. cbn [p_addr fst] in CN.
        unfold l in CN. rewrite (trips_next_eq gq k (Datatypes.S i)) in CN. exact CN. }
      split; [eapply cellZ_frame; [exact C2 | clear - G1 SB0; lia | clear - G2 SB1 CR; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply (OBJ0 b z Hin0); clear - Hz; cbn in Hz; lia]|].
      split; [eapply cellZ_frame; [exact C3 | clear - G1 SB0; lia | clear - G2 SB1 CR; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply (OBJ0 b z Hin0); clear - Hz; cbn in Hz; lia]|].
      split.
      - intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Lj.
        eapply cellZ_frame; [exact (C4 j mn Hj) | clear - G1 SB0; lia | clear - G2 G4 Lj SB1 CR; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; apply (OBJ0 b z Hin0); clear - Hz Lj G4; cbn in Hz; lia].
      - eapply writableZ_frame; [exact BW|]. intros z Hz. right. apply GR01. exact (proj1 (BW z Hz)). }
    assert (PEND1 : pend bt S (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) M1 pb0).
    { (lazymatch goal with |- ?G => let G' := eval unfold pend in G in change_no_check G' end). split; [exact RB1|].
      split; [rewrite Lpb0, <- LLEN; apply STKP; [clear; lia | clear; lia | exact Ptsz]|].
      split.
      { rewrite (nxaddr_firstn gq k (proj1 Hk) : nxaddr pb0 = nxaddr gq) || idtac. apply STKP; [clear; lia | clear; lia |].
        replace (match pb0 with [] => 0 | b :: _ => ba_addr b end) with (match l with [] => 0 | t :: _ => p_addr t end); [exact (Ptfirst eq_refl)|].
        (lazymatch goal with |- ?G => let G' := eval unfold l in G in change_no_check G' end). rewrite (trips_head gq k (proj1 Hk) NEgq). symmetry. exact (nxaddr_firstn gq k (proj1 Hk)). }
      split; [replace (q_bytes pb0) with (0 + p_tot l) by ((lazymatch goal with |- ?G => let G' := eval unfold l, pb0 in G in change_no_check G' end); rewrite trips_tot by (clear - Hk; lia); clear; lia); apply STKP; [clear; lia | clear; lia | exact Psum]|].
      split; [intros a Ha; apply GR1; apply (proj1 (SOK a ltac:(clear - Ha US; lia)))|].
      rewrite EMF in FRM. destruct FRM as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). rewrite <- EMF in F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11.
      (lazymatch goal with |- ?G => let G' := eval unfold dr_frame in G in change_no_check G' end). repeat split; (apply STK1; [clear; lia | clear; lia | assumption]). }
    (* [comment removed for export] *)
    assert (Lrest : Z.of_nat (length rest) = Z.of_nat (length gq) - Z.of_nat (length l)).
    { (lazymatch goal with |- ?G => let G' := eval unfold rest in G in change_no_check G' end). rewrite length_skipn, LLEN. clear - Hk. lia. }
    assert (Enx : p_lastnx l 1 = nxaddr rest) by ((lazymatch goal with |- ?G => let G' := eval unfold l, rest in G in change_no_check G' end); apply trips_lastnx; exact Hk).
    assert (Ebytes : q_bytes gq - p_tot l = q_bytes rest).
    { (lazymatch goal with |- ?G => let G' := eval unfold l in G in change_no_check G' end). rewrite trips_tot by (clear - Hk; lia). fold pb0. rewrite EGQ', q_bytes_app. clear. lia. }
    assert (RL1 : rep_list bt M1 (IB bt + 888) rest).
    { (lazymatch goal with |- ?G => let G' := eval unfold rep_list, IB in G in change_no_check G' end). rewrite BT_segs, BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
      split; [rewrite Lrest; apply IMGP; [clear; lia | clear; lia | exact Plen]|].
      split; [replace (0x10ab58 + 888 + 8) with (0x10ab58 + 896) by (clear; lia); apply IMGP; [clear; lia | clear; lia |];
              replace (match rest with [] => 0 | b :: _ => ba_addr b end) with (p_lastnx l 1) by exact Enx; exact Pfirst|].
      split; [| replace (0x10ab58 + 888 + 24) with (0x10ab58 + 912) by (clear; lia); rewrite <- Ebytes; apply IMGP; [clear; lia | clear; lia | exact Pbytes]].
      replace (0x10ab58 + 888 + 16) with (0x10ab58 + 904) by (clear; lia).
      destruct rest as [|br rest'] eqn:ER.
      - (lazymatch goal with |- ?G => let G' := eval cbn [rev] in G in change_no_check G' end). apply IMGP; [clear; lia | clear; lia |]. apply Plast. rewrite Enx. reflexivity.
      - (* [comment removed for export] *)
        assert (NZ : p_lastnx l 1 <> 0).
        { rewrite Enx. (lazymatch goal with |- ?G => let G' := eval cbn [nxaddr] in G in change_no_check G' end). assert (Hbr : In br gq) by (rewrite EGQ'; apply in_app_iff; right; left; reflexivity).
          destruct (BF br Hbr) as (G1 & _). clear - G1 SBH. lia. }
        replace (match rev (br :: rest') with [] => 0 | b :: _ => ba_addr b end) with (nxaddr (rev gq))
          by (rewrite EGQ'; rewrite (nxaddr_rev_app pb0 (br :: rest') ltac:(discriminate)); reflexivity).
        unfold cellZ, cellN in Glast. replace (0x10ab58 + 888 + 16) with (0x10ab58 + 904) in Glast by (clear; lia).
        eapply rd_same; [| clear; wd_ulia_c | exact Glast].
        intros x Hx. assert (Hx' : 0x10ab58 + 904 <= U x < 0x10ab58 + 912) by (clear - Hx; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia).
        rewrite OUT1; [apply EQM; clear - Hx'; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold FOOT in G in change_no_check G' end). intros [F | [F | F]]; [clear - F Hx' HS7; lia | clear - F Hx'; lia|].
        unfold loop_foot in F. destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; try (clear - F Hx' HS7; lia).
        + exact (NZ (proj1 F)).
        + destruct F as (t & Ht & Q). destruct (GEOl t Ht) as [G1 _]. clear - Q Hx' G1. lia. }
    (* [comment removed for export] *)
    assert (SOK1 : forall a : word, U S - 3584 <= U a < U S - 2400 -> M1 a <> None /\ store_ok BSEGS M1 a 1%nat = true).
    { intros a Ha. assert (D : M1 a <> None) by (apply GR1; apply (proj1 (SOK a ltac:(clear - Ha US; lia)))). exact (conj D (store_ok1_defK M1 a D)). }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_pre_post in G in change_no_check G' end). exists fx, M1, mdl1, r1, pb0, rest.
    split; [reflexivity|]. split; [exact EGQ|]. split; [exact NEpb|]. split; [exact RESTB|].
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold invb in G in change_no_check G' end). split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|]. split; [exact W|].
      split; [exact RX1|]. split; [exact EGQ|]. split; [exact XSUB|]. split; [exact QDEF1|]. split; [exact PEND1|]. split; [exact SOK1|].
      split; [exact HR1|]. split; [rewrite A4; exact X4|]. apply rc_acc_refl. }
    split; [rewrite A10, LLEN, Lpb0; reflexivity|].
    split; [exact RL1|].
    split.
    { repeat split; (apply STKA; [clear; lia | clear; lia | rewrite EMa]);
        [apply fr_rc0_ra | apply fr_rc0_s0 | apply fr_rc0_s1 | apply fr_rc0_s2 | apply fr_rc0_s3 | apply fr_rc0_s4]; exact HS7. }
    split; [exact (conj A3 (conj A4 (conj A26 A27)))|].
    split.
    { intros a NE. split.
      - destruct (CH1 a NE) as [F | [F | F]]; [left; exact F | right; right; rewrite BT_ia; exists 0x10ab58, 0x10b9b8; split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | clear - F; lia]|].
        destruct (LFq _ F) as [Q | [(t & Ht & Q) | Q]].
        + right; right. rewrite BT_ia. exists 0x10ab58, 0x10b9b8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | clear - Q; lia].
        + right; left. destruct (trips_in gq k t Ht) as (b0 & Hb0 & Ea & _). apply (OBL_rt_private_pf bt st2 Lc FF W (U a)). right. exists b0.
          split; [apply in_app_iff; right; exact (PB0in _ Hb0) | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); rewrite <- Ea; clear - Q; lia].
        + left. clear - Q. lia.
      - intros E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity | apply same_but_materialized_except_vm; exact SBM1].
  Qed.
End K1.
