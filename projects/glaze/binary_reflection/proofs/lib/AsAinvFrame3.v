(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinv3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Inst.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable HP0 : ast -> Prop.      (* [comment removed for export] *)
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation AINV := (AAINVP HP0 bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem AAINV_mono : AAINV_mono_stmt AINV.
  Proof.
    intros Lc FF B C K B' C' K' M mdl (st & W & R & ((P1 & P2 & P3) & HP) & MW) HB HC HK.
    exists st. split; [exact W|]. split; [exact R|]. split; [| exact MW]. split; [(lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end); repeat split; lia | exact HP].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m_vm_eq_parts : forall mdl mdl', m_vm mdl' = m_vm mdl ->
    m_vmmaps mdl' = m_vmmaps mdl /\ m_vm_lazy mdl' = m_vm_lazy mdl /\ m_vm_materialized mdl' = m_vm_materialized mdl
    /\ eager_used mdl' = eager_used mdl.
  Proof.
    intros mdl mdl' E. (lazymatch goal with |- ?G => let G' := eval unfold m_vmmaps, m_vm_lazy, m_vm_materialized, eager_used, m_vmmaps, m_vm_lazy in G in change_no_check G' end). rewrite E. repeat split; reflexivity.
  Qed.

  Lemma MInv_vm_eq : forall AA mdl mdl', m_vm mdl' = m_vm mdl -> MInv AA mdl -> MInv AA mdl'.
  Proof.
    intros AA mdl mdl' E [N1 N2 N3 N4 N5]. destruct (m_vm_eq_parts mdl mdl' E) as (E1 & E2 & E3 & E4).
    constructor; rewrite ?E1, ?E2, ?E3, ?E4; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma model_ivs_wf_vm_eq : forall mdl mdl', m_vm mdl' = m_vm mdl -> BackingAlgebra.model_ivs_wf mdl -> BackingAlgebra.model_ivs_wf mdl'.
  Proof.
    intros mdl mdl' E H. destruct (m_vm_eq_parts mdl mdl' E) as (E1 & E2 & E3 & E4).
    unfold BackingAlgebra.model_ivs_wf in *. rewrite E1, E2. exact H.
  Qed.
  Lemma model_ivs_wf_sbm : forall mdl mdl', same_but_materialized mdl mdl' -> BackingAlgebra.model_ivs_wf mdl -> BackingAlgebra.model_ivs_wf mdl'.
  Proof.
    intros mdl mdl' S H. pose proof (same_but_materialized_frame mdl mdl' S) as F. destruct F as (_ & E1 & E2 & _).
    unfold BackingAlgebra.model_ivs_wf in *. rewrite E1, E2. exact H.
  Qed.

  Lemma rep_ledger_vm_eq : forall st mdl mdl', m_vm mdl' = m_vm mdl -> rep_ledger bt st mdl -> rep_ledger bt st mdl'.
  Proof.
    intros st mdl mdl' E H. destruct (m_vm_eq_parts mdl mdl' E) as (E1 & E2 & E3 & E4).
    unfold rep_ledger in *. rewrite E1. unfold pg_in_ivz in *. rewrite E2. exact H.
  Qed.

  Lemma rep_budget_vm_eq : forall st Lc mdl mdl', m_vm mdl' = m_vm mdl -> rep_budget bt st Lc mdl -> rep_budget bt st Lc mdl'.
  Proof.
    intros st Lc mdl mdl' E (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). destruct (m_vm_eq_parts mdl mdl' E) as (E1 & E2 & E3 & E4).
    (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). rewrite E4. repeat (split; [first [assumption | exact (MInv_vm_eq _ _ _ E B2)] |]). exact B8.
  Qed.

  Theorem AAINV_model : AAINV_model_stmt AINV.
  Proof.
    intros Lc FF B C K M mdl mdl' (st & W & R & Bd & MW) E. exists st. split; [exact W|]. split; [| split; [exact Bd | exact (model_ivs_wf_vm_eq mdl mdl' E MW)]].
    unfold Rep in *.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    repeat (split; [assumption|]) || idtac.
    split; [exact (rep_ledger_vm_eq st mdl mdl' E R13)|]. split; [exact (rep_budget_vm_eq st Lc mdl mdl' E R14)|]. exact R15.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rep_ledger_sbm : forall st mdl mdl', same_but_materialized mdl mdl' -> rep_ledger bt st mdl -> rep_ledger bt st mdl'.
  Proof.
    intros st mdl mdl' S H. pose proof (same_but_materialized_frame mdl mdl' S) as F.
    destruct F as (_ & E1 & E2 & _). unfold rep_ledger in *. rewrite E1. unfold pg_in_ivz in *. rewrite E2. exact H.
  Qed.

  Theorem AAINV_lazy : AAINV_lazy_stmt IA AINV (bt_fs bt).
  Proof.
    intros Lc FF B C K M mdl (st & W & R & Bd & MW).
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    exists (a_aa st). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    intros mdl' MI S. exists st. split; [exact W|]. split; [| split; [exact Bd | exact (model_ivs_wf_sbm mdl mdl' S MW)]].
    pose proof (same_but_materialized_frame mdl mdl' S) as F.
    destruct F as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). repeat (split; [assumption|]) || idtac.
    split; [exact (rep_ledger_sbm st mdl mdl' S R13)|].
    split; [| exact R15].
    (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). rewrite E3. repeat (split; [assumption|]). exact B8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem AAINV_zone : AAINV_zone_stmt IA AINV.
  Proof.
    intros Lc FF B C K M mdl b n (st & W & R & Bd) Hin.
    destruct W as (_ & _ & _ & _ & (WL & _ & _) & _). destruct (WL b n Hin) as (N & P16 & AB & _). repeat split; try lia; try assumption; apply AB.
  Qed.

  Lemma PHI_nonneg : forall L, (forall b n, In (b, n) L -> 0 <= n) -> 0 <= PHI L.
  Proof.
    induction L as [|[b n] r IH]; intros H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [lia|].
    assert (0 <= n) by (apply (H b n); left; reflexivity).
    assert (0 <= PHI r) by (apply IH; intros b' n' H'; apply (H b' n'); right; exact H').
    (lazymatch goal with |- ?G => let G' := eval unfold MBLK in G in change_no_check G' end). lia.
  Qed.

  Theorem AAINV_bounds : AAINV_bounds_stmt AINV.
  Proof.
    intros Lc FF B C K M mdl (st & W & R & ((P1 & P2 & P3) & _) & _).
    destruct W as (_ & _ & _ & _ & (WL & ND & _) & (WF1 & NDF & _) & _).
    repeat split; try lia; try assumption.
  Qed.

  Theorem AAINV_lazyzone : AAINV_lazyzone_stmt IA AINV.
  Proof.
    intros Lc FF B C K M mdl (st & W & R & Bd).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _).
    eapply Forall_impl; [|exact FA]. intros [a n] (H1 & H2 & H3 & H4 & H5). cbn in *. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition OBL_A1_frame : Prop := AAINV_frame_stmt IA AINV.
  Definition OBL_disj : Prop := AAINV_disj_stmt AINV.
  Definition OBL_perm : Prop := AAINV_perm_stmt AINV.
  Definition OBL_fzone : Prop := AAINV_fzone_stmt IA AINV (bt_fs bt).
  Definition OBL_fdisj : Prop := AAINV_fdisj_stmt AINV.
  Definition OBL_bfdisj : Prop := AAINV_bfdisj_stmt AINV.
  Definition OBL_cells (SEGS : list Segment) : Prop := AAINV_cells_stmt IA AINV SEGS.
  Definition OBL_nolazy : Prop := AAINV_nolazy_stmt AINV.

  (* [comment removed for export] *)
  Theorem AAINV_shdef : AAINV_shdef_stmt AINV.
  Proof.
    intros Lc FF B C K M mdl z (st & W & R & Bd) Hz.
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (SD & _)). exact (SD z Hz).
  Qed.

  Theorem AAINV_props_of : forall SEGS,
    OBL_A1_frame -> OBL_disj -> OBL_perm -> OBL_fzone -> OBL_fdisj -> OBL_bfdisj -> OBL_cells SEGS -> OBL_nolazy ->
    AAINV_props IA AINV (bt_fs bt) SEGS.
  Proof.
    intros SEGS H1 H2 H3 H4 H5 H6 H7 H8.
    exact (AAP IA AINV (bt_fs bt) SEGS H1 AAINV_model AAINV_mono AAINV_lazy AAINV_zone H2 H3 H4 H5 H6 AAINV_bounds AAINV_lazyzone H7 H8 AAINV_shdef).
  Qed.
End Inst.
End AsAinv3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvGeom3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 AsAinv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Geom.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable HP0 : ast -> Prop.
  #[local] Abbreviation AINV := (AAINVP HP0 bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem AAINV_disj : AAINV_disj_stmt AINV.
  Proof.
    intros Lc FF B C K M mdl L1 L2 b n b' n' (st & W & R & Bd) EL Hin.
    destruct W as (_ & _ & _ & _ & (WL & ND & DJ) & _).
    assert (Hin1 : In (b, n) Lc) by (rewrite EL; apply in_app_iff; right; left; reflexivity).
    assert (Hin2 : In (b', n') Lc).
    { rewrite EL. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [X|X]; [left; exact X | right; right; exact X]. }
    assert (NE : (b, n) <> (b', n')).
    { intros E. rewrite EL in ND. apply NoDup_remove_2 in ND. apply ND. rewrite E. exact Hin. }
    exact (DJ b n b' n' Hin1 Hin2 NE).
  Qed.

  (* [comment removed for export] *)
  Lemma fs_range : forall st Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg ->
    dyn_ok (bt_ia bt) (bt_fs bt) (bt_fs bt + FAKE_SIZE) /\ bt_fs bt mod PG = 0.
  Proof.
    intros st Lc FF qt qg W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & INFS & _).
    destruct (RNG _ _ ltac:((lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); apply in_app_iff; left; exact INFS)) as (A1 & A2 & A3 & A4).
    split; [exact A1 | exact A3].
  Qed.

  Ltac compute_pows :=
    repeat match goal with |- context [2 ^ ?e] => let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v end.

  Lemma frame_geom : forall k pos fs, 0 <= k <= KMAXCLASS -> 0 <= pos < FCAP k -> fs mod PG = 0 ->
    let f := fake_frame_addr fs k pos in
    fs + 0x9000 <= f /\ f + FS k <= fs + FAKE_SIZE /\ f mod FS k = 0 /\ 64 <= FS k <= 512
    /\ fs + 0x9000 + k * 2 ^ 20 <= f /\ f + FS k <= fs + 0x9000 + (k + 1) * 2 ^ 20.
  Proof.
    intros k pos fs Hk Hpos Hfs. unfold fake_frame_addr, FS, FCAP, FAKE_SIZE, KMAXCLASS, PG in *. cbn zeta.
    assert (E : fs = 4096 * (fs / 4096)) by (apply Z.div_exact; lia).
    set (q := fs / 4096) in *.
    assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    revert Hpos.
    destruct K as [-> | [-> | [-> | ->]]]; compute_pows; intros Hpos;
      (split; [lia|]); (split; [lia|]); (split; [| lia]);
      [ replace (fs + 36864 + 0 * 1048576 + 64 * 1 * pos) with ((64 * q + 576 + pos) * 64) by lia
      | replace (fs + 36864 + 1 * 1048576 + 64 * 2 * pos) with ((32 * q + 288 + 8192 + pos) * 128) by lia
      | replace (fs + 36864 + 2 * 1048576 + 64 * 4 * pos) with ((16 * q + 144 + 8192 + pos) * 256) by lia
      | replace (fs + 36864 + 3 * 1048576 + 64 * 8 * pos) with ((8 * q + 72 + 6144 + pos) * 512) by lia ];
      [ change (64 * 1) with 64 | change (64 * 2) with 128 | change (64 * 4) with 256 | change (64 * 8) with 512 ];
      apply Z_mod_mult.
  Qed.

  Theorem AAINV_fzone : AAINV_fzone_stmt (bt_ia bt) AINV (bt_fs bt).
  Proof.
    intros Lc FF B C K M mdl f k (st & W & R & Bd) Hin.
    pose proof (fs_range st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & F3).
    destruct W as (_ & _ & _ & _ & _ & (WF1 & _) & _).
    destruct (WF1 f k Hin) as (Hk & Hpos & Ef).
    pose proof (frame_geom k (fpos bt f k) (bt_fs bt) Hk Hpos F3) as G. cbn zeta in G. rewrite <- Ef in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6). unfold ablk_ok, FAKE_SIZE, PTRLO in *. repeat split; try lia.
  Qed.

  Lemma frames_apart : forall fs k pos k' pos', fs mod PG = 0 ->
    0 <= k <= KMAXCLASS -> 0 <= pos < FCAP k -> 0 <= k' <= KMAXCLASS -> 0 <= pos' < FCAP k' ->
    (k, pos) <> (k', pos') ->
    fake_frame_addr fs k pos + FS k <= fake_frame_addr fs k' pos' \/ fake_frame_addr fs k' pos' + FS k' <= fake_frame_addr fs k pos.
  Proof.
    intros fs k pos k' pos' Hfs Hk Hp Hk' Hp' NE.
    pose proof (frame_geom k pos fs Hk Hp Hfs) as G. pose proof (frame_geom k' pos' fs Hk' Hp' Hfs) as G'. cbn zeta in G, G'.
    destruct G as (_ & _ & _ & S1 & L1 & U1). destruct G' as (_ & _ & _ & S2 & L2 & U2).
    destruct (Z.lt_trichotomy k k') as [LT | [EQ | GT]].
    - left. assert ((k + 1) * 2 ^ 20 <= k' * 2 ^ 20) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - subst k'. assert (pos <> pos') by (intros ->; apply NE; reflexivity).
      unfold fake_frame_addr in *.
      destruct (Z.lt_trichotomy pos pos') as [LTp | [EQp | GTp]]; [left | lia | right];
        assert (FS k * pos + FS k <= FS k * pos' \/ FS k * pos' + FS k <= FS k * pos) by nia; nia.
    - right. assert ((k' + 1) * 2 ^ 20 <= k * 2 ^ 20) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  Qed.

  Theorem AAINV_fdisj : AAINV_fdisj_stmt AINV.
  Proof.
    intros Lc FF B C K M mdl F1 F2 f k f' k' (st & W & R & Bd) EF Hin.
    pose proof (fs_range st Lc FF W) as (RD & R3).
    destruct W as (_ & _ & _ & _ & _ & (WF1 & ND & _) & _).
    assert (Hin1 : In (f, k) FF) by (rewrite EF; apply in_app_iff; right; left; reflexivity).
    assert (Hin2 : In (f', k') FF).
    { rewrite EF. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [X|X]; [left; exact X | right; right; exact X]. }
    assert (NE : (f, k) <> (f', k')).
    { intros E. rewrite EF in ND. apply NoDup_remove_2 in ND. apply ND. rewrite E. exact Hin. }
    destruct (WF1 f k Hin1) as (Hk & Hp & E1). destruct (WF1 f' k' Hin2) as (Hk' & Hp' & E2).
    assert (NE2 : (k, fpos bt f k) <> (k', fpos bt f' k')).
    { intros E. injection E as Ek Ep. apply NE. rewrite E1, E2. rewrite <- Ep, <- Ek. reflexivity. }
    pose proof (frames_apart (bt_fs bt) k (fpos bt f k) k' (fpos bt f' k') R3 Hk Hp Hk' Hp' NE2) as FA.
    rewrite <- E1, <- E2 in FA. exact FA.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Definition disj (x y : Z * Z) : Prop := snd x <= fst y \/ snd y <= fst x.

  Lemma ar_disj_ne : forall st Lc FF x y {qt qg : Z}, WFq bt st Lc FF qt qg ->
    In x (all_ranges bt st) -> In y (all_ranges bt st) -> x <> y -> disj x y.
  Proof.
    intros st Lc FF [xl xh] [yl yh] qt qg W Hx Hy NE. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & _) & _).
    destruct (in_split _ _ Hx) as (l1 & l2 & E).
    assert (Hy' : In (yl, yh) (l1 ++ l2)).
    { rewrite E in Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Y | [Y | Y]]; [left; exact Y | exfalso; exact (NE Y) | right; exact Y]. }
    (lazymatch goal with |- ?G => let G' := eval unfold disj in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). destruct (PW l1 l2 xl xh yl yh E Hy'); lia.
  Qed.

  Lemma ar_disj_fixed_dyn : forall st Lc FF x y {qt qg : Z}, WFq bt st Lc FF qt qg ->
    In x (bt_fixed bt) -> In y (dyn_ranges st) -> disj x y.
  Proof.
    intros st Lc FF [xl xh] [yl yh] qt qg W Hx Hy. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & _) & _).
    destruct (in_split _ _ Hx) as (l1 & l2 & E).
    assert (EA : all_ranges bt st = l1 ++ (xl, xh) :: (l2 ++ dyn_ranges st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end). rewrite E. rewrite <- app_assoc. reflexivity. }
    assert (Hy' : In (yl, yh) (l1 ++ (l2 ++ dyn_ranges st))) by (apply in_app_iff; right; apply in_app_iff; right; exact Hy).
    (lazymatch goal with |- ?G => let G' := eval unfold disj in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). destruct (PW l1 (l2 ++ dyn_ranges st) xl xh yl yh EA Hy'); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma prim_block_in_space : forall st Lc FF p n {qt qg : Z}, WFq bt st Lc FF qt qg -> In (p, n) Lc -> is_primary n = true ->
    bt_spacebeg bt <= p - rz n /\ p + n <= bt_spacebeg bt + KSPACE.
  Proof.
    intros st Lc FF p n qt qg W Hin HP.
    destruct W as ((WR & _) & _ & _ & _ & (WL & _) & _).
    destruct (WL p n Hin) as (N1 & _ & _ & CARV). destruct (CARV HP) as (j & Hj & Hle & Ea).
    pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). unfold blk_class in *.
    set (c := class_of (needed n)) in *.
    destruct (WR c U2) as (R1 & _ & R3 & _). pose proof (csize_pos c U2) as ((S1 & S2) & _).
    unfold prim_alloc_beg, chunk_addr, region_beg, KREGION, KSPACE, KUSERMAP, KREGION_EXHAUST in *.
    assert (j * csize c + csize c <= r_alloc_user (a_reg st c)) by lia.
    assert (0 <= j * csize c) by lia.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia).
    assert (2 ^ 32 <= c * 2 ^ 32) by nia.
    lia.
  Qed.

  Lemma sec_block_in_map : forall st Lc FF p n {qt qg : Z}, WFq bt st Lc FF qt qg -> In (p, n) Lc -> is_primary n = false ->
    exists s, In s (a_sec st) /\ sc_map s <= p /\ p + n <= sc_map s + sc_mapsz s.
  Proof.
    intros st Lc FF p n qt qg W Hin HP.
    destruct W as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & REG & _) & (WL & _) & _).
    destruct (WL p n Hin) as (N1 & _).
    destruct (REG p n Hin HP) as (s & Hs & Eu & En). exists s. split; [exact Hs|].
    unfold sc_user, sc_mapsz, sec_user_off in *. rewrite En in *. pose proof (sec_map_size_ge n ltac:(lia)) as (G1 & _).
    pose proof (rz_range n). unfold PG in *. lia.
  Qed.

  Theorem AAINV_bfdisj : AAINV_bfdisj_stmt AINV.
  Proof.
    intros Lc FF B C K M mdl b n f k (st & W & R & Bd) Hb Hf.
    pose proof (fs_range st Lc FF W) as (FD & F3).
    pose proof W as (_ & _ & _ & _ & _ & (WF1 & _) & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & _) & _).
    destruct (WF1 f k Hf) as (Hk & Hpos & Ef).
    pose proof (frame_geom k (fpos bt f k) (bt_fs bt) Hk Hpos F3) as G. cbn zeta in G. rewrite <- Ef in G.
    destruct G as (G1 & G2 & _). pose proof (rz_range n).
    destruct (is_primary n) eqn:HP.
    - pose proof (prim_block_in_space st Lc FF b n W Hb HP) as (P1 & P2).
      assert (NE : (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) <> (bt_fs bt, bt_fs bt + FAKE_SIZE)).
      { intros E. injection E as E1 E2. unfold KSPACE, PG, FAKE_SIZE in *. lia. }
      assert (A6 : In (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) (all_ranges bt st)) by ((lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); apply in_app_iff; left; exact IN6).
      assert (AF : In (bt_fs bt, bt_fs bt + FAKE_SIZE) (all_ranges bt st)) by ((lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); apply in_app_iff; left; exact INFS).
      pose proof (ar_disj_ne st Lc FF _ _ W A6 AF NE) as D. unfold disj in D; cbn in D. unfold KSPACE, PG, FAKE_SIZE in *. lia.
    - destruct (sec_block_in_map st Lc FF b n W Hb HP) as (s & Hs & Q1 & Q2).
      assert (HD : In (sc_map s, sc_map s + sc_mapsz s) (dyn_ranges st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. left. apply in_map_iff. exists s. split; [reflexivity | exact Hs]. }
      pose proof (ar_disj_fixed_dyn st Lc FF _ _ W INFS HD) as D. unfold disj in D; cbn in D. unfold FAKE_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem AAINV_cells : AAINV_cells_stmt (bt_ia bt) AINV (bt_segs bt).
  Proof.
    intros Lc FF B C K M mdl (st & W & R & Bd).
    pose proof (fs_range st Lc FF W) as (FD & F3).
    pose proof W as (_ & _ & _ & _ & _ & (WF1 & _) & _).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RF & _ & _ & _ & _ & RL & RFF & RC1 & RC2 & RSD).
    destruct RF as (_ & _ & _ & _ & WFS & _).
    split; [|split; [|split; [exact RC1 | exact RC2]]].
    - intros b n a Hin [Ha | Ha]; destruct (RL b n Hin) as [W1 W2]; [exact (W1 a Ha) | exact (W2 a Ha)].
    - intros f k a Hin [Ha | Ha].
      + destruct (WF1 f k Hin) as (Hk & Hpos & Ef).
        pose proof (frame_geom k (fpos bt f k) (bt_fs bt) Hk Hpos F3) as G. cbn zeta in G. rewrite <- Ef in G.
        destruct G as (G1 & G2 & _). apply WFS. unfold FAKE_SIZE in *. lia.
      + exact (RFF f k Hin a Ha).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma in_perm {A} (l l' : list A) (x : A) : Permutation l l' -> (In x l' <-> In x l).
  Proof. intros P. split; intros H; [exact (Permutation_in _ (Permutation_sym P) H) | exact (Permutation_in _ P H)]. Qed.

  Lemma existsb_perm {A} (f : A -> bool) (l l' : list A) : Permutation l l' -> existsb f l' = existsb f l.
  Proof.
    intros P. destruct (existsb f l) eqn:E.
    - apply existsb_exists in E. destruct E as (x & Hx & Fx). apply existsb_exists. exists x. split; [apply (in_perm l l' x P); exact Hx | exact Fx].
    - destruct (existsb f l') eqn:E'; [|reflexivity]. apply existsb_exists in E'. destruct E' as (x & Hx & Fx).
      assert (existsb f l = true) by (apply existsb_exists; exists x; split; [apply (in_perm l l' x P); exact Hx | exact Fx]). congruence.
  Qed.

  Lemma in_live_c_perm : forall Lc Lc' c a, Permutation Lc Lc' -> in_live_c Lc' c a <-> in_live_c Lc c a.
  Proof.
    intros Lc Lc' c a P. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split; intros (p & n & Hin & X); exists p, n; (split; [|exact X]);
      [apply (in_perm Lc Lc' _ P); exact Hin | apply (in_perm Lc Lc' _ P); exact Hin].
  Qed.

  Lemma live_granule_perm : forall Lc Lc' g, Permutation Lc Lc' -> live_granule Lc' g <-> live_granule Lc g.
  Proof.
    intros Lc Lc' g P. (lazymatch goal with |- ?G => let G' := eval unfold live_granule in G in change_no_check G' end). split; intros (p & n & Hin & X); exists p, n; (split; [|exact X]);
      [apply (in_perm Lc Lc' _ P); exact Hin | apply (in_perm Lc Lc' _ P); exact Hin].
  Qed.

  Lemma partition_perm : forall st Lc Lc' c, Permutation Lc Lc' -> partition_c bt st Lc c -> partition_c bt st Lc' c.
  Proof.
    intros st Lc Lc' c P H. unfold partition_c in *.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact H9 | exact H10]]]]]]]]].
    - intros a. rewrite (in_live_c_perm Lc Lc' c a P). exact (H1 a).
    - intros a [X Y]. apply (H2 a). split; [apply (in_live_c_perm Lc Lc' c a P); exact X | exact Y].
    - intros a [X Y]. apply (H3 a). split; [apply (in_live_c_perm Lc Lc' c a P); exact X | exact Y].
    - intros a [X Y]. apply (H4 a). split; [apply (in_live_c_perm Lc Lc' c a P); exact X | exact Y].
    - exact H5. - exact H6. - exact H7.
    - intros a Hb Hc X. apply (H8 a Hb Hc). destruct X as [X|X]; [left; apply (in_live_c_perm Lc Lc' c a P); exact X | right; exact X].
  Qed.

  Lemma WF_perm : forall st Lc Lc' FF FF' {qt qg : Z}, Permutation Lc Lc' -> Permutation FF FF' -> WFq bt st Lc FF qt qg -> WFq bt st Lc' FF' qt qg.
  Proof.
    intros st Lc Lc' FF FF' qt qg PL PF W.
    destruct W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (L1 & L2 & L3) & (K1 & K2 & K3) & WD & WM & WMP & G1 & G2).
    split; [|split; [exact WC | split; [exact WQ | split; [| split; [| split; [| split; [exact WD | split; [exact WM | split; [exact WMP | split; [destruct G1 as (GA & GC & GB); split; [exact GA | split; [rewrite <- (Permutation_length PL); exact GC | rewrite <- (PHI_perm _ _ PL); exact GB]] | exact G2]]]]]]]]]].
    - split; [| exact WR2]. intros c Hc. destruct (WR1 c Hc) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). repeat (split; [assumption|]). split; [exact (partition_perm st Lc Lc' c PL X10) | exact X11].
    - (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
      split. { intros s0 Hs. rewrite (in_perm Lc Lc' _ PL). exact (S6 s0 Hs). }
      split. { intros p n Hin. apply (S7 p n). apply (in_perm Lc Lc' _ PL). exact Hin. }
      exact S8.
    - (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split. { intros p n Hin. apply L1. apply (in_perm Lc Lc' _ PL). exact Hin. }
      split. { apply (Permutation_NoDup PL). exact L2. }
      intros p n p' n' H1 H2. apply L3; apply (in_perm Lc Lc' _ PL); assumption.
    - (lazymatch goal with |- ?G => let G' := eval unfold wf_fake in G in change_no_check G' end). split. { intros f k Hin. apply K1. apply (in_perm FF FF' _ PF). exact Hin. }
      split. { apply (Permutation_NoDup PF). exact K2. } exact K3.
  Qed.

  Lemma rep_shadow_perm : forall st Lc Lc' M, Permutation Lc Lc' -> rep_shadow bt st Lc M -> rep_shadow bt st Lc' M.
  Proof.
    intros st Lc Lc' M P (H1 & H2 & H3 & H4 & H5 & H6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
    split; [|split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | exact H6]]]]].
    intros c g Hc Hg NL. apply (H1 c g Hc Hg). intros L. apply NL. apply (live_granule_perm Lc Lc' g P). exact L.
  Qed.

  Lemma rep_budget_perm : forall st Lc Lc' mdl, Permutation Lc Lc' -> rep_budget bt st Lc mdl -> rep_budget bt st Lc' mdl.
  Proof.
    intros st Lc Lc' mdl P (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split. { intros p n Hin. apply B4. apply (in_perm Lc Lc' _ P). exact Hin. }
    split; [exact B5|]. split; [exact B6|]. split; [exact B7|]. exact B8.
  Qed.

  Lemma Rep_perm : forall st Lc Lc' FF FF' M mdl, Permutation Lc Lc' -> Permutation FF FF' ->
    Rep bt st Lc FF M mdl -> Rep bt st Lc' FF' M mdl.
  Proof.
    intros st Lc Lc' FF FF' M mdl PL PF R.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & (H1 & H2) & R9 & RF & R11 & R12 & R13 & R14 & RL & RFF & RC1 & RC2 & RSD).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|].
    split; [exact R7|].
    split. { split; [|exact H2]. intros p n Hin. apply H1. apply (in_perm Lc Lc' _ PL). exact Hin. }
    split; [exact R9|].
    split. { destruct RF as (K1 & K2 & K3 & K4 & K5 & K6 & K7). (lazymatch goal with |- ?G => let G' := eval unfold rep_fake in G in change_no_check G' end). split; [exact K1|]. split; [exact K2|].
             split. { intros k pos Hk Hpos. rewrite (existsb_perm _ FF FF' PF). exact (K3 k pos Hk Hpos). }
             split. { intros f k Hin. apply K4. apply (in_perm FF FF' _ PF). exact Hin. }
             split; [exact K5 |]. split; [exact K6 | exact K7]. }
    split; [exact R11|]. split; [exact (rep_shadow_perm st Lc Lc' M PL R12)|]. split; [exact R13|].
    split; [exact (rep_budget_perm st Lc Lc' mdl PL R14)|].
    split. { intros p n Hin. apply RL. apply (in_perm Lc Lc' _ PL). exact Hin. }
    split. { intros f k Hin. apply RFF. apply (in_perm FF FF' _ PF). exact Hin. }
    split; [exact RC1|]. split; [exact RC2 | exact RSD].
  Qed.

  Theorem AAINV_perm : AAINV_perm_stmt AINV.
  Proof.
    intros Lc Lc' FF FF' B C K M mdl PL PF (st & W & R & ((P1 & P2 & P3) & HP) & MW).
    exists st. split; [exact (WF_perm st Lc Lc' FF FF' PL PF W)|]. split; [exact (Rep_perm st Lc Lc' FF FF' M mdl PL PF R)|].
    split; [| exact MW]. split; [| exact HP]. (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). rewrite <- (PHI_perm Lc Lc' PL), <- (Permutation_length PL). repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem AAINV_props_geom : OBL_A1_frame bt HP0 -> OBL_nolazy bt HP0 -> AAINV_props (bt_ia bt) AINV (bt_fs bt) (bt_segs bt).
  Proof.
    intros H1 H8. exact (AAINV_props_of bt HP0 (bt_segs bt) H1 AAINV_disj AAINV_perm AAINV_fzone AAINV_fdisj AAINV_bfdisj AAINV_cells H8).
  Qed.
End Geom.
End AsAinvGeom3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 AsAinv3 AsAinvGeom3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DEFK (M M' : mem) : Prop := forall a : word, M' a <> M a -> M' a <> None.

Lemma agree_at : forall (P : Z -> Prop) (M M' : mem),
  (forall a : word, M' a <> M a -> ~ P (bv_unsigned a)) ->
  forall i, P i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros P M M' H i Hi Hr. destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [exact E|].
  exfalso. apply (H _ NE). rewrite u_Z2bv by lia. exact Hi.
Qed.

Lemma def_keep : forall M M' (a : word), DEFK M M' -> M a <> None -> M' a <> None.
Proof.
  intros M M' a D H. destruct (decide (M' a = M a)) as [E|NE]; [rewrite E; exact H | exact (D a NE)].
Qed.

(* [comment removed for export] *)
Definition rep_last (bt : as_boot) (st : ast) (M : mem) : Prop :=
  (forall z, shmaps z -> M (Z_to_bv 64 z) <> None)
  /\ (a_gq st <> [] -> forall a : word, IB bt + 896 <= bv_unsigned a < IB bt + 904 -> M a <> None).
(* [comment removed for export] *)
Lemma rep_last_of : forall {RC : run_ceil} bt st Lc FF M mdl, Rep bt st Lc FF M mdl -> rep_last bt st M.
Proof. intros RC bt st Lc FF M mdl R. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L). exact L. Qed.

Lemma rep_first_def : forall {RC : run_ceil} bt st Lc FF M mdl, Rep bt st Lc FF M mdl -> a_gq st <> [] ->
  forall a : word, IB bt + 896 <= bv_unsigned a < IB bt + 904 -> M a <> None.
Proof. intros RC bt st Lc FF M mdl R. exact (proj2 (rep_last_of bt st Lc FF M mdl R)). Qed.
Lemma rep_last_keep : forall bt st st' M M', DEFK M M' -> rep_last bt st M -> (a_gq st' <> [] -> a_gq st <> []) -> rep_last bt st' M'.
Proof.
  intros bt st st' M M' D [S F] G. split.
  - intros z Hz. exact (def_keep M M' _ D (S z Hz)).
  - intros NE a Ha. exact (def_keep M M' a D (F (G NE) a Ha)).
Qed.

Lemma writableZ_keep : forall SEGS M M' lo hi, DEFK M M' -> writableZ SEGS M lo hi -> writableZ SEGS M' lo hi.
Proof.
  intros SEGS M M' lo hi D W. eapply writableZ_frame; [exact W|]. intros i Hi.
  destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [left; exact E | right; exact (D _ NE)].
Qed.

(* [comment removed for export] *)
Lemma nth_In_lt : forall {A} (l : list A) (d : A) i, (i < length l)%nat -> In (nth i l d) l.
Proof. intros A l d i Hi. apply nth_In. exact Hi. Qed.

Lemma nth_error_lt : forall {A} (l : list A) i (x : A), nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply nth_error_Some. rewrite H. discriminate. Qed.

(* [comment removed for export] *)
Ltac frAG AG := let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; apply AG; [| lia]; first [lia | eauto 7 | idtac].
Ltac frZ AG H := eapply (cellZ_frame _ _ _ _ _ _ H); [lia | lia | frAG AG].
Ltac frB AG H := eapply (byteZ_frame _ _ _ _ _ H); [lia | lia | apply AG; [| lia]; first [lia | eauto 7 | idtac]].
Ltac frF AG H := eapply (fillZ_frame _ _ _ _ _ _ H); [lia | lia | frAG AG].
Ltac frW DEF H := exact (writableZ_keep _ _ _ _ _ DEF H).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition consts_cells (a : Z) : Prop := exists c, In c (bt_consts bt) /\ fst (fst c) <= a < fst (fst c) + Z.of_nat (snd (fst c)).
  Definition instance_cells (st : ast) (a : Z) : Prop :=
    let I := IB bt in
    (I + 112 <= a < I + 128) \/ a = I + 680 \/ a = I + 880 \/ a = I + 881 \/ a = I + 984 \/ (I + 888 <= a < I + 920)
    \/ (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st))).
  Definition thread_cells (a : Z) : Prop :=
    let T := bt_thread bt in
    (T <= a < T + 24) \/ (T + 40 <= a < T + 64) \/ (T + 72 <= a < T + 80) \/ (T + T_QC <= a < T + T_QC + 32)
    \/ (T + T_PC + PC_SZ <= a < T + T_PC + PC_SZ * 31) \/ a = T + T_UNW
    \/ (bt_tctx bt + 152 <= a < bt_tctx bt + 160) \/ (bt_tctx bt + 8 <= a < bt_tctx bt + 12).
  Definition ialloc_cells (a : Z) : Prop :=
    (IA_FLAG bt <= a < IA_FLAG bt + 2) \/ (IA_INST bt + 8 <= a < IA_INST bt + 8 + 0x40000) \/ (IA_INST bt + 0x40dc0 <= a < IA_INST bt + 0x40dd0).
  Definition rtc_cells (a : Z) : Prop :=
    (ia_rtc_sb (bt_ia bt) <= a < ia_rtc_sb (bt_ia bt) + 8) \/ (ia_rtc_uar (bt_ia bt) <= a < ia_rtc_uar (bt_ia bt) + 4).

End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Groups.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M M' : mem).
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  Hypothesis DEF : DEFK M M'.

  Lemma rep_list_frame : forall hd q,
    rep_list bt M hd q -> 0 <= hd -> hd + 32 < 2 ^ 64 ->
    (forall i, hd <= i < hd + 32 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_list bt M' hd q.
  Proof using.
    intros hd q (L1 & L2 & L3 & L4) H0 H1 AG. (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end).
    split; [frZ AG L1|]. split; [frZ AG L2|]. split; [frZ AG L3|]. frZ AG L4.
  Qed.

  Lemma rep_instance_frame :
    rep_instance bt st M ->
    0 <= IB bt + 112 -> IB bt + 985 < 2 ^ 64 -> 0 <= bt_ptrarr bt -> bt_ptrarr bt + 8 * a_nres st < 2 ^ 64 ->
    Z.of_nat (length (a_sec st)) <= a_nres st ->
    (forall i, instance_cells bt st i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_instance bt st M'.
  Proof using DEF.
    intros (I1 & I2 & I3 & I4 & I5 & I6 & IL & IP & IW) R1 R2 R3 R4 R5 AG. unfold rep_instance, instance_cells in *.
    split; [frZ AG I1|]. split; [frZ AG I2|]. split; [frB AG I3|]. split; [frB AG I4|]. split; [frB AG I5|]. split; [frB AG I6|].
    split. { eapply rep_list_frame; [exact IL | lia | lia |]. intros i Hi Hr. apply AG; lia. }
    split. { intros i s Hs. pose proof (nth_error_lt _ _ _ Hs) as Hl. pose proof (IP i s Hs) as C. frZ AG C. }
    frW DEF IW.
  Qed.

  Lemma rep_pclass_frame : forall cinit c ks,
    rep_pclass bt M T cinit c ks -> 0 <= T + T_PC + PC_SZ * c -> T + T_PC + PC_SZ * c + 80 < 2 ^ 64 -> Z.of_nat (length ks) <= 16 ->
    (forall i, T + T_PC + PC_SZ * c <= i < T + T_PC + PC_SZ * c + 80 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_pclass bt M' T cinit c ks.
  Proof using.
    intros cinit c ks (P1 & P2 & P3 & P4) R1 R2 R3 AG. (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass in G in change_no_check G' end).
    split; [frZ AG P1|]. split; [frZ AG P2|]. split; [frZ AG P3|].
    intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. pose proof (P4 i k Hk) as C. frZ AG C.
  Qed.

  Lemma rep_thread_frame :
    rep_thread bt st M ->
    0 <= T -> T + PG < 2 ^ 64 -> 0 <= bt_tctx bt -> bt_tctx bt + 160 < 2 ^ 64 ->
    (forall c, 1 <= c <= 30 -> Z.of_nat (length (a_cache st c)) <= 16) ->
    (forall i, thread_cells bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_thread bt st M'.
  Proof using DEF.
    intros (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & C1 & C2 & C3 & C4) R1 R2 R3 R4 CL AG. unfold rep_thread, thread_cells in *.
    unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
    split; [frZ AG T1|]. split; [frZ AG T2|]. split; [frZ AG T3|]. split; [frB AG T4|]. split; [frZ AG T5|]. split; [frB AG T6|].
    split. { eapply rep_list_frame; [exact TL | lia | lia |]. intros i Hi Hr. apply AG; lia. }
    split. { intros c Hc. pose proof (CL c Hc). eapply rep_pclass_frame; [exact (TP c Hc) | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); lia | lia |].
             (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros i Hi Hr. apply AG; [|lia]. nia. }
    split; [frW DEF TW|]. split; [frZ AG C1|]. split; [frZ AG C2|]. split; [frZ AG C3 | frZ AG C4].
  Qed.

  (* [comment removed for export] *)
  Definition foot_region (c : Z) (i : Z) : Prop :=
    (reginfo bt c <= i < reginfo bt c + 72 /\ ~ (reginfo bt c + 64 <= i < reginfo bt c + 68))
    \/ (fa_beg SBEG c <= i < fa_beg SBEG c + 4 * Z.of_nat (length (r_free (a_reg st c)))).
  Lemma rep_region_frame : forall c,
    rep_reginfo bt M c (a_reg st c) -> rep_freearray bt M c (a_reg st c) ->
    0 <= reginfo bt c -> reginfo bt c + 128 < 2 ^ 64 -> 0 <= fa_beg SBEG c -> fa_beg SBEG c + r_mapped_fa (a_reg st c) < 2 ^ 64 ->
    4 * Z.of_nat (length (r_free (a_reg st c))) <= r_mapped_fa (a_reg st c) ->
    (forall i, foot_region c i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_reginfo bt M' c (a_reg st c) /\ rep_freearray bt M' c (a_reg st c).
  Proof using DEF.
    intros c (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GW) (F1 & F2 & F3) R1 R2 R3 R4 R5 AG. unfold foot_region in AG.
    split.
    - (lazymatch goal with |- ?G => let G' := eval unfold rep_reginfo in G in change_no_check G' end).
      split; [frZ AG G1|]. split; [frZ AG G2|]. split; [frZ AG G3|]. split; [frZ AG G4|]. split; [frZ AG G5|].
      split; [frZ AG G6|]. split; [frZ AG G7|]. split; [frZ AG G8|]. split; [frB AG G9|]. frW DEF GW.
    - (lazymatch goal with |- ?G => let G' := eval unfold rep_freearray in G in change_no_check G' end). split; [| split; [frW DEF F2 | frW DEF F3]].
      intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. pose proof (F1 i k Hk) as C. frZ AG C.
  Qed.

  (* [comment removed for export] *)
  Definition foot_batch (b : batch) (i : Z) : Prop := ba_addr b <= i < ba_addr b + 24 + 8 * Z.of_nat (length (ba_items b)).
  Lemma rep_batches_frame : forall q,
    rep_batches bt M q ->
    (forall b, In b q -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP) ->
    (forall b i, In b q -> foot_batch b i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_batches bt M' q.
  Proof using DEF.
    intros q RB RNG AG i b Hb. pose proof (nth_error_In _ _ Hb) as Hin. destruct (RNG b Hin) as (R1 & R2 & R3).
    destruct (RB i b Hb) as (B1 & B2 & B3 & B4 & BW). unfold foot_batch, BATCHSZ, BATCHCAP in *.
    assert (AGb : forall i0, ba_addr b <= i0 < ba_addr b + 24 + 8 * Z.of_nat (length (ba_items b)) -> 0 <= i0 < 2 ^ 64 ->
                  M' (Z_to_bv 64 i0) = M (Z_to_bv 64 i0)) by (intros i0 H0 H1; exact (AG b i0 Hin H0 H1)).
    split; [frZ AGb B1|]. split; [frZ AGb B2|]. split; [frZ AGb B3|]. split; [| frW DEF BW].
    intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. pose proof (B4 j mn Hj) as C. frZ AGb C.
  Qed.

  (* [comment removed for export] *)
  Definition foot_sec (sc : schunk) (i : Z) : Prop := sc_map sc <= i < sc_map sc + 32.
  Lemma rep_secondary_frame :
    rep_secondary bt st M ->
    (forall sc, In sc (a_sec st) -> 0 <= sc_map sc /\ sc_map sc + 32 < 2 ^ 64) ->
    (forall sc i, In sc (a_sec st) -> foot_sec sc i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_secondary bt st M'.
  Proof using DEF.
    intros RS RNG AG i sc Hs. pose proof (nth_error_In _ _ Hs) as Hin. destruct (RNG sc Hin) as (R1 & R2).
    destruct (RS i sc Hs) as (S1 & S2 & S3 & S4 & SW). unfold foot_sec in *.
    assert (AGs : forall i0, sc_map sc <= i0 < sc_map sc + 32 -> 0 <= i0 < 2 ^ 64 -> M' (Z_to_bv 64 i0) = M (Z_to_bv 64 i0))
      by (intros i0 H0 H1; exact (AG sc i0 Hin H0 H1)).
    split; [frZ AGs S1|]. split; [frZ AGs S2|]. split; [frZ AGs S3|]. split; [frZ AGs S4|]. frW DEF SW.
  Qed.

  (* [comment removed for export] *)
  Definition foot_hdr (p n : Z) (i : Z) : Prop :=
    (p - 16 <= i < p - 8) \/ (p - 4 <= i < p) \/ (16 < rz n /\ p - rz n <= i < p - rz n + 16).
  Lemma rep_hdr_frame : forall p n s,
    rep_hdr bt M p n s -> rz n <= p -> p < 2 ^ 64 - 16 ->
    (forall i, foot_hdr p n i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_hdr bt M' p n s.
  Proof using DEF.
    intros p n s (H1 & (b1 & Hb1 & H2) & H3 & H4 & HW & H5 & HL) R1 R2 AG. pose proof (rz_range n) as RZ. unfold foot_hdr in AG. (lazymatch goal with |- ?G => let G' := eval unfold rep_hdr in G in change_no_check G' end).
    split; [frB AG H1|]. split; [exists b1; split; [exact Hb1 | frB AG H2]|]. split; [frZ AG H3|]. split; [frZ AG H4|]. split; [frW DEF HW|]. split; [frZ AG H5|].
    intros Hrz. destruct (HL Hrz) as [L1 L2]. split; [frZ AG L1 | frZ AG L2].
  Qed.

  Lemma rep_headers_frame :
    rep_headers bt st Lc M ->
    (forall p n, In (p, n) Lc -> rz n <= p /\ p < 2 ^ 64 - 16) ->
    (forall m n, In (m, n) (quar st) -> rz n <= m + 16 /\ m + 16 < 2 ^ 64 - 16) ->
    (forall p n i, In (p, n) Lc \/ In (p - 16, n) (quar st) -> foot_hdr p n i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_headers bt st Lc M'.
  Proof using DEF.
    intros [HLc HQ] RL RQ AG. split.
    - intros p n Hin. destruct (RL p n Hin) as [R1 R2]. eapply rep_hdr_frame; [exact (HLc p n Hin) | lia | lia |].
      intros i Hi Hr. apply (AG p n i); [left; exact Hin | exact Hi | exact Hr].
    - intros m n Hin. destruct (RQ m n Hin) as [R1 R2]. destruct (HQ m n Hin) as [Hh HW]. split; [| frW DEF HW].
      eapply rep_hdr_frame; [exact Hh | lia | lia |].
      intros i Hi Hr. apply (AG (m + 16) n i); [right; replace (m + 16 - 16) with m by lia; exact Hin | exact Hi | exact Hr].
  Qed.

  (* [comment removed for export] *)
  Definition foot_depot_static (i : Z) : Prop :=
    (DEPOT_TAB bt <= i < DEPOT_TAB bt + 4 * 2 ^ 20 + 4) \/ i = DEPOT_NIDS bt + 8 \/ (DEPOT_MAP1 bt <= i < DEPOT_MAP1 bt + 8 * 2 ^ 15)
    \/ (SSOBJ bt <= i < SSOBJ bt + 8) \/ (SSOBJ bt + 16 <= i < SSOBJ bt + 16 + 16 * 2 ^ 12).
  Definition foot_node (d : depot) (id : Z) (i : Z) : Prop := node_addr bt d id <= i < node_addr bt d id + 16.
  Lemma rep_depot_frame :
    rep_depot bt st M ->
    0 <= DEPOT_TAB bt -> DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15 < 2 ^ 64 -> 0 <= SSOBJ bt -> SSOBJ bt + 16 + 16 * 2 ^ 12 < 2 ^ 64 ->
    (forall id, 1 <= id <= dp_nids (a_dep st) -> 0 <= node_addr bt (a_dep st) id /\ node_addr bt (a_dep st) id + 16 < 2 ^ 64) ->
    (forall i, foot_depot_static i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall id i, 1 <= id <= dp_nids (a_dep st) -> foot_node (a_dep st) id i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_depot bt st M'.
  Proof using DEF.
    intros (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9) R1 R2 R3 R4 RN AG AGN.
    unfold foot_depot_static, foot_node, DEPOT_NIDS, DEPOT_MAP1 in *. (lazymatch goal with |- ?G => let G' := eval unfold rep_depot, DEPOT_NIDS, DEPOT_MAP1 in G in change_no_check G' end).
    split. { intros i Hi. pose proof (D1 i Hi) as C. frZ AG C. }
    split; [frZ AG D2|]. split; [frB AG D3|].
    split. { intros i Hi. pose proof (D4 i Hi) as C. frZ AG C. }
    split. { intros id Hid. destruct (RN id Hid) as [N1 N2]. destruct (D5 id Hid) as (C1 & C2 & C3).
             assert (AGi : forall i, node_addr bt (a_dep st) id <= i < node_addr bt (a_dep st) id + 16 -> 0 <= i < 2 ^ 64 ->
                           M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) by (intros i H0 H1; exact (AGN id i Hid H0 H1)).
             split; [frZ AGi C1|]. split; [frZ AGi C2|]. frZ AGi C3. }
    split. { intros b Hb. frW DEF (D6 b Hb). }
    split; [frZ AG D7|].
    split. { intros i Hi. destruct (D8 i Hi) as (C1 & C2 & C3). split; [frZ AG C1|]. split; [frZ AG C2|]. frB AG C3. }
    intros b Hb. frW DEF (D9 b Hb).
  Qed.

  (* [comment removed for export] *)
  Definition foot_fake_static (i : Z) : Prop :=
    (bt_fs bt <= i < bt_fs bt + 96) \/ i = bt_fs bt + 96 \/ (bt_fs bt + 0x1000 <= i < bt_fs bt + 0x9000) \/ (bt_tls_fs bt <= i < bt_tls_fs bt + 16)
    \/ (bt_dtls bt + 24 <= i < bt_dtls bt + 32).     (* [comment removed for export] *)
  Definition foot_fword (f k : Z) (i : Z) : Prop := f + FS k - 8 <= i < f + FS k.

  Lemma flag_addr_range : forall fs k pos, 0 <= k <= 10 -> 0 <= pos < FCAP k ->
    fs + 0x1000 <= fake_flag_addr fs k pos < fs + 0x9000.
  Proof using.
    intros fs k pos Hk Hp. unfold fake_flag_addr, fake_flags_off, FCAP in *.
    assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct K as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]; cbn in *; lia.
  Qed.

  Lemma rep_fake_frame :
    rep_fake bt st FF M ->
    0 <= bt_fs bt -> bt_fs bt + FAKE_SIZE < 2 ^ 64 -> 0 <= bt_tls_fs bt -> bt_tls_fs bt + 16 < 2 ^ 64 -> 0 <= bt_dtls bt -> bt_dtls bt + 32 < 2 ^ 64 ->
    (forall f k, In (f, k) FF -> bt_fs bt + 0x9000 <= f /\ f + FS k <= bt_fs bt + FAKE_SIZE /\ 8 <= FS k) ->
    (forall i, foot_fake_static i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall f k i, In (f, k) FF -> foot_fword f k i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_fake bt st FF M'.
  Proof using DEF.
    intros (K1 & K2 & K3 & K4 & KW & KT & KS & KD1 & KD2) R1 R2 R3 R4 R5 R6 RF AG AGF. unfold foot_fake_static, foot_fword, FAKE_SIZE in *. (lazymatch goal with |- ?G => let G' := eval unfold rep_fake in G in change_no_check G' end).
    split. { intros k Hk. pose proof (K1 k Hk) as C. frZ AG C. }
    split; [frB AG K2|].
    split. { intros k pos Hk Hp. pose proof (flag_addr_range (bt_fs bt) k pos Hk Hp) as FR. pose proof (K3 k pos Hk Hp) as C. frB AG C. }
    split. { intros f k Hin. destruct (RF f k Hin) as (F1 & F2 & F3). pose proof (K4 f k Hin) as C.
             assert (AGi : forall i, f + FS k - 8 <= i < f + FS k -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
               by (intros i H0 H1; exact (AGF f k i Hin H0 H1)).
             frZ AGi C. }
    split; [frW DEF KW|]. split; [frZ AG KT|]. split; [frZ AG KS|]. split; [frZ AG KD1 | frZ AG KD2].
  Qed.

  (* [comment removed for export] *)
  Lemma rep_ialloc_frame :
    rep_ialloc bt st M ->
    0 <= IA_FLAG bt -> IA_FLAG bt + 2 < 2 ^ 64 -> 0 <= IA_INST bt + 8 -> IA_INST bt + 0x40dd0 < 2 ^ 64 ->
    (forall i, ialloc_cells bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_ialloc bt st M'.
  Proof using.
    intros (A1 & A2 & A3 & A4) R1 R2 R3 R4 AG. unfold ialloc_cells in AG. (lazymatch goal with |- ?G => let G' := eval unfold rep_ialloc in G in change_no_check G' end).
    split; [frB AG A1|]. split; [frB AG A2|]. split; [frF AG A3|].
    intros Hi. destruct (A4 Hi) as [C1 C2]. split; [frZ AG C1 | frZ AG C2].
  Qed.

  (* [comment removed for export] *)
  Definition foot_shreg (c : Z) (i : Z) : Prop :=
    (sh_lo (region_beg SBEG c) <= i < SB + (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8 /\ ~ live_granule Lc (i - SB))
    \/ (sh_lo (fa_beg SBEG c) <= i < SB + (fa_beg SBEG c + r_mapped_fa (a_reg st c)) / 8).
  Definition foot_shsec (sc : schunk) (i : Z) : Prop :=
    sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8
    /\ (~ user_granule (sc_user sc) (sc_n sc) (i - SB) \/ In (sc_user sc - 16, sc_n sc) (quar st)).
  Lemma rep_shadow_frame :
    rep_shadow bt st Lc M ->
    (forall c, 1 <= c <= 30 -> 0 <= region_beg SBEG c /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= CEIL
                            /\ 0 <= fa_beg SBEG c /\ fa_beg SBEG c + r_mapped_fa (a_reg st c) <= CEIL) ->
    (forall sc, In sc (a_sec st) -> 0 <= sc_map sc /\ sc_map sc + sc_mapsz sc <= CEIL /\ sc_map sc <= sc_user sc /\ sc_user sc + sc_n sc <= sc_map sc + sc_mapsz sc
                                    /\ (sc_map sc + sc_mapsz sc) mod 8 = 0) ->
    (forall c i, 1 <= c <= 30 -> foot_shreg c i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall sc i, In sc (a_sec st) -> foot_shsec sc i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_shadow bt st Lc M'.
  Proof using DEF.
    intros (S1 & S2 & S3 & S4 & S5 & S6) RC RS AG AGS. (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). ceil; unfold foot_shreg, foot_shsec, user_granule, sh_lo, SB in *.
    split. { intros c g Hc Hg NL. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (S1 c g Hc Hg NL) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AG c); [exact Hc | | lia]. left.
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [lia | exact NL]. }
    split. { intros c g Hc Hg. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (S2 c g Hc Hg) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AG c); [exact Hc | right; lia | lia]. }
    split. { intros sc g Hs Hg NU. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (S3 sc g Hs Hg NU) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AGS sc); [exact Hs | | lia].
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [lia | left; exact NU]. }
    split. { intros sc g Hs HQ HU. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (S4 sc g Hs HQ HU) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AGS sc); [exact Hs | | lia].
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [lia | right; exact HQ]. }
    split. { intros c g Hc Hg. exact (def_keep M M' _ DEF (S5 c g Hc Hg)). }
    intros sc g Hs Hg. exact (def_keep M M' _ DEF (S6 sc g Hs Hg)).
  Qed.

  (* [comment removed for export] *)
  Lemma rep_tail_frame :
    (forall p n, In (p, n) Lc -> writableZ SG M p (p + n) /\ writableZ SG M (sh_lo p) (sh_hi p n)) ->
    (forall f k, In (f, k) FF -> writableZ SG M (sh_lo f) (sh_hi f (FS k))) ->
    cellZ SG M (ia_rtc_sb (bt_ia bt)) 8 SB -> cellZ SG M (ia_rtc_uar (bt_ia bt)) 4 1 ->
    0 <= ia_rtc_sb (bt_ia bt) -> ia_rtc_sb (bt_ia bt) + 8 < 2 ^ 64 -> 0 <= ia_rtc_uar (bt_ia bt) -> ia_rtc_uar (bt_ia bt) + 4 < 2 ^ 64 ->
    (forall i, rtc_cells bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall p n, In (p, n) Lc -> writableZ SG M' p (p + n) /\ writableZ SG M' (sh_lo p) (sh_hi p n))
    /\ (forall f k, In (f, k) FF -> writableZ SG M' (sh_lo f) (sh_hi f (FS k)))
    /\ cellZ SG M' (ia_rtc_sb (bt_ia bt)) 8 SB /\ cellZ SG M' (ia_rtc_uar (bt_ia bt)) 4 1.
  Proof using DEF.
    intros WL WFF C1 C2 R1 R2 R3 R4 AG. unfold rtc_cells in AG.
    split. { intros p n Hin. destruct (WL p n Hin) as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k Hin. frW DEF (WFF f k Hin). }
    split; [frZ AG C1 | frZ AG C2].
  Qed.
End Groups.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.

  Lemma all_ranges_fixed : forall x, In x (bt_fixed bt) -> In x (all_ranges bt st).
  Proof using. intros x H. (lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end). apply in_app_iff. left. exact H. Qed.
  Lemma all_ranges_dyn : forall x, In x (dyn_ranges st) -> In x (all_ranges bt st).
  Proof using. intros x H. (lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end). apply in_app_iff. right. exact H. Qed.

  (* [comment removed for export] *)
  Lemma fixed_facts :
    0 < bt_thread bt /\ bt_thread bt + PG <= CEIL /\ 0 < bt_tctx bt /\ bt_tctx bt + 0x10000 <= CEIL
    /\ 0 < bt_fs bt /\ bt_fs bt + FAKE_SIZE <= CEIL /\ bt_fs bt mod PG = 0
    /\ 0 < bt_nodes0 bt /\ bt_nodes0 bt + 2 ^ 20 <= CEIL /\ 0 < bt_store0 bt /\ bt_store0 bt + 2 ^ 23 <= CEIL
    /\ 0 < bt_ptrarr bt /\ bt_ptrarr bt + 2 ^ 23 <= CEIL
    /\ 0 < SBEG /\ SBEG + KSPACE + PG <= CEIL /\ SBEG mod 2 ^ 16 = 0.
  Proof using W qg qt FF Lc st.
    destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & G1 & _).
    destruct WM as (RNG & _ & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _).
    destruct (RNG _ _ (all_ranges_fixed _ IN6)) as ((Z1 & _ & Z3 & _ & _) & _).
    destruct (RNG _ _ (all_ranges_fixed _ IN8)) as ((A1 & _ & A3 & _ & _) & A2 & _).
    destruct (RNG _ _ (all_ranges_fixed _ INFS)) as ((B1 & _ & B3 & _ & _) & B2 & B4 & _).
    destruct (RNG _ _ (all_ranges_fixed _ INT)) as ((C1 & _ & C3 & _ & _) & C2 & _).
    destruct (RNG _ _ (all_ranges_fixed _ INN)) as ((D1 & _ & D3 & _ & _) & D2 & _).
    destruct (RNG _ _ (all_ranges_fixed _ INS)) as ((E1 & _ & E3 & _ & _) & E2 & _).
    destruct (RNG _ _ (all_ranges_fixed _ INC)) as ((F1 & _ & F3 & _ & _) & F2 & _).
    repeat split; assumption || lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dtls_member : In (bt_dtls bt, bt_dtls bt + PG) (bt_fixed bt).
  Proof using W qg qt FF Lc st RUN. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _). destruct WM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INDT & _). exact INDT. Qed.
  Lemma dtls_facts : 0 < bt_dtls bt /\ bt_dtls bt + PG <= CEIL.
  Proof using W qg qt FF Lc st.
    destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _). pose proof WM as (RNG & _).
    destruct WM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INDT & _).
    destruct (RNG _ _ (all_ranges_fixed _ INDT)) as ((A1 & _ & A3 & _ & _) & _). split; assumption.
  Qed.

  Lemma dtls_vs_thread : bt_dtls bt + PG <= bt_thread bt \/ bt_thread bt + PG <= bt_dtls bt.
  Proof using W qg qt FF Lc st RUN. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _). destruct WM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEPT & _). exact SEPT. Qed.
  Lemma ptrarr_vs_store0 : bt_store0 bt + 2 ^ 23 <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= bt_store0 bt.
  Proof using W qg qt FF Lc st RUN. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _). destruct WM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP8 & _). exact SEP8. Qed.

  (* [comment removed for export] *)
  Lemma dtls_cell_facts : forall i, bt_dtls bt + 24 <= i < bt_dtls bt + 32 ->
    0 < i /\ i < CEIL /\ ~ (ia_img_lo (bt_ia bt) <= i < ia_img_hi (bt_ia bt)) /\ ~ (AS_LO <= i < AS_HEAPLO)
    /\ ~ (bt_thread bt <= i < bt_thread bt + PG)
    /\ (forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> ~ (lo <= i < hi))
    /\ (forall lo hi, In (lo, hi) (dyn_ranges st) -> ~ (lo <= i < hi)).
  Proof using W qg qt FF Lc.
    intros i Hi. pose proof dtls_member as INDT.
    destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _). pose proof WM as (RNG & PWs & _).
    destruct WM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEPT & _).
    destruct (RNG _ _ (all_ranges_fixed _ INDT)) as ((A1 & A2 & A3 & A4 & A5) & _). unfold PG in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split.
    - intros lo hi Hin NE Hr. destruct (in_split _ _ Hin) as (l1 & l2 & E).
      assert (Hd : In (bt_dtls bt, bt_dtls bt + 4096) (l1 ++ l2)).
      { rewrite E in INDT. apply in_app_iff in INDT. destruct INDT as [X | [X | X]]; [apply in_app_iff; left; exact X | exfalso; injection X; intros; lia | apply in_app_iff; right; exact X]. }
      assert (E' : all_ranges bt st = l1 ++ (lo, hi) :: (l2 ++ dyn_ranges st)) by ((lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); rewrite E, <- app_assoc; reflexivity).
      destruct (PWs l1 (l2 ++ dyn_ranges st) lo hi _ _ E' ltac:(rewrite app_assoc; apply in_app_iff; left; exact Hd)); lia.
    - intros lo hi Hin Hr.
      destruct (in_split _ _ INDT) as (l1 & l2 & E).
      assert (E' : all_ranges bt st = l1 ++ (bt_dtls bt, bt_dtls bt + 4096) :: (l2 ++ dyn_ranges st)) by ((lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); rewrite E, <- app_assoc; reflexivity).
      destruct (PWs l1 (l2 ++ dyn_ranges st) _ _ lo hi E' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma img_pw : PW (img_ranges (bt_ia bt) (bt_tls_fs bt)).
  Proof using W qg qt FF Lc st RUN.
    destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BT & _).   (* [comment removed for export] *)
    destruct BT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DJ). exact (PW_of_splits _ DJ).
  Qed.

  Lemma image_facts :
    let IA := bt_ia bt in
    0 <= IB bt + 112 /\ IB bt + 985 <= AS_LO /\ 0 <= DEPOT_TAB bt /\ DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15 <= AS_LO
    /\ 0 <= SSOBJ bt /\ SSOBJ bt + 16 + 16 * 2 ^ 12 <= AS_LO /\ 0 <= IA_FLAG bt /\ IA_FLAG bt + 8 <= AS_LO
    /\ 0 <= IA_INST bt /\ IA_INST bt + IASZ <= AS_LO /\ 0 <= bt_tls_fs bt /\ bt_tls_fs bt + 16 <= AS_LO
    /\ 0 <= ia_rtc_sb IA /\ ia_rtc_sb IA + 8 <= AS_LO /\ 0 <= ia_rtc_uar IA /\ ia_rtc_uar IA + 4 <= AS_LO
    /\ Forall (fun c => 0 <= fst (fst c) /\ fst (fst c) + Z.of_nat (snd (fst c)) < 2 ^ 64) (bt_consts bt).
  Proof using W qg qt FF Lc st RUN.
    destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BT & _).   (* [comment removed for export] *)
    destruct BT as (I1 & I2 & PR & C1 & C2 & C3 & C4 & C5 & C6 & CC & R1 & R2 & R3 & R4 & DC & DT & DR & DJ).
    assert (PC : forall lo hi, priv_cover (bt_ia bt) lo hi -> 0 <= lo /\ hi <= AS_LO).
    { intros lo hi (plo & phi & Hin & H1 & H2). destruct (PR plo phi (or_introl Hin)). lia. }
    assert (PC2 : forall lo hi, const_cover (bt_ia bt) lo hi -> 0 <= lo /\ hi <= AS_LO).
    { intros lo hi (plo & phi & Hin & H1 & H2). destruct (PR plo phi (or_intror Hin)). lia. }
    apply PC in C1. apply PC in C2. apply PC in C3. apply PC in C4. apply PC in C5. apply PC in C6.
    (lazymatch goal with |- ?G => let G' := eval unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST in G in change_no_check G' end). cbn zeta.
    repeat (split; [lia|]).
    rewrite Forall_forall in CC |- *. intros c Hc. destruct (CC c Hc) as [CV|CV]; [destruct (PC _ _ CV) | destruct (PC2 _ _ CV)]; unfold AS_LO in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_range : forall c a, 1 <= c <= 30 -> carved bt st c a ->
    region_beg SBEG c <= a /\ a + csize c <= region_beg SBEG c + r_alloc_user (a_reg st c)
    /\ SBEG <= a /\ a + csize c <= SBEG + KSPACE /\ a mod 16 = 0.
  Proof using W qg qt FF Lc RUN.
    intros c a Hc (j & Hj & Hle & Ea).
    destruct W as ((WR & _) & _). destruct (WR c Hc) as (R1 & _ & R3 & _). pose proof (csize_pos c Hc) as ((S1 & S2) & S3).
    pose proof fixed_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM).
    subst a. unfold chunk_addr, region_beg, KREGION, KSPACE, KUSERMAP, KREGION_EXHAUST in *.
    assert (0 <= j * csize c) by lia.
    assert (j * csize c + csize c <= r_alloc_user (a_reg st c)) by lia.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia).
    assert (2 ^ 32 <= c * 2 ^ 32) by nia.
    repeat (split; [lia|]).
    assert (E1 : SBEG = 2 ^ 16 * (SBEG / 2 ^ 16)) by (apply Z.div_exact; lia).
    assert (E2 : csize c = 16 * (csize c / 16)) by (apply Z.div_exact; lia).
    set (q1 := SBEG / 2 ^ 16) in *. set (q2 := csize c / 16) in *.
    apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). exists (2 ^ 12 * q1 + c * 2 ^ 28 + j * q2). nia.
  Qed.

  (* [comment removed for export] *)
  Lemma quar_item : forall m n, In (m, n) (quar st) ->
    1 <= n <= NMAX /\ ((is_primary n = true /\ carved bt st (blk_class n) (prim_alloc_beg (m + 16) n))
                       \/ (is_primary n = false /\ registered st (m + 16) n)).
  Proof using W qg qt FF Lc RUN.
    intros m n Hin. unfold quar in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hmn).
    destruct W as (_ & _ & (QT & QG & _) & _).
    assert (WB : wf_batch0 bt st b).
    { apply in_app_iff in Hb. rewrite Forall_forall in QT, QG. destruct Hb as [Hb|Hb]; [exact (wf_batch_0 bt st b (QT b Hb)) | exact (QG b Hb)]. }
    destruct WB as (_ & _ & IT). exact (IT m n Hmn).
  Qed.

  Lemma sec_facts : forall sc, In sc (a_sec st) ->
    0 < sc_map sc /\ sc_map sc + sc_mapsz sc <= CEIL /\ sc_map sc mod PG = 0 /\ sc_mapsz sc mod PG = 0
    /\ sc_map sc + PG + 16 <= sc_user sc /\ sc_user sc + sc_n sc <= sc_map sc + sc_mapsz sc /\ 64513 <= sc_n sc <= NMAX
    /\ sc_user sc = sc_map sc + PG + rz (sc_n sc).
  Proof using W qg qt FF Lc bt.
    intros sc Hs. pose proof W as (_ & _ & _ & (_ & _ & _ & SS & _) & _ & _ & _ & _ & (RNG & _) & _). destruct (SS sc Hs) as (N1 & A2).
    assert (HD : In (sc_map sc, sc_map sc + sc_mapsz sc) (dyn_ranges st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. left. apply in_map_iff. exists sc. split; [reflexivity | exact Hs]. }
    destruct (RNG _ _ (all_ranges_dyn _ HD)) as ((A1 & _ & A3 & _ & _) & _ & _ & A4).
    unfold sc_user, sc_mapsz, sec_user_off in *. pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)) as (G1 & G2).
    pose proof (rz_range (sc_n sc)). unfold PG in *. repeat split; lia.
  Qed.

  Lemma quar_item_range : forall m n, In (m, n) (quar st) ->
    0 < m + 16 - rz n /\ m + 16 + n <= CEIL /\ 1 <= n <= NMAX.
  Proof using W qg qt FF Lc bt.
    intros m n Hin. destruct (quar_item m n Hin) as (N & [[HP CV] | [HP RG]]).
    - pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). unfold blk_class in *.
      destruct (carved_range _ _ U2 CV) as (C1 & C2 & C3 & C4 & C5). unfold prim_alloc_beg in *.
      pose proof fixed_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _).
      pose proof (rounded_ge n) as (Q1 & _). unfold needed, KSPACE, PG in *. lia.
    - destruct RG as (sc & Hs & Eu & En). destruct (sec_facts sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      rewrite En in *. rewrite <- Eu. pose proof (rz_range n). unfold PG in *. lia.
  Qed.

  Lemma live_range : forall p n, In (p, n) Lc -> PTRLO <= p /\ p + n <= CEIL /\ 1 <= n <= NMAX /\ p mod 16 = 0.
  Proof using W qg qt FF st bt.
    intros p n Hin. destruct W as (_ & _ & _ & _ & (WL & _) & _). destruct (WL p n Hin) as (A1 & A2 & (B1 & B2 & B3 & B4) & _). repeat split; lia.
  Qed.

  Lemma batch_facts : forall b, In b (a_tq st ++ a_gq st) ->
    carved bt st BATCHCLASS (ba_addr b) /\ 0 <= Z.of_nat (length (ba_items b)) <= BATCHCAP
    /\ SBEG <= ba_addr b /\ ba_addr b + BATCHSZ <= SBEG + KSPACE.
  Proof using W qg qt FF Lc RUN.
    intros b Hb. destruct W as (_ & _ & (QT & QG & _) & _).
    assert (WB : wf_batch0 bt st b).
    { apply in_app_iff in Hb. rewrite Forall_forall in QT, QG. destruct Hb as [Hb'|Hb']; [exact (wf_batch_0 bt st b (QT b Hb')) | exact (QG b Hb')]. }
    destruct WB as (L1 & CV & _). destruct (carved_range BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV) as (C1 & C2 & C3 & C4 & C5).
    change (csize BATCHCLASS) with 8192 in *. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). split; [exact CV|]. repeat split; lia.
  Qed.

  Lemma region_facts : forall c, 1 <= c <= 30 ->
    let r := a_reg st c in
    SBEG <= region_beg SBEG c /\ region_beg SBEG c + r_mapped_user r <= fa_beg SBEG c /\ r_alloc_user r <= r_mapped_user r /\ 0 <= r_alloc_user r
    /\ fa_beg SBEG c + 2 ^ 29 <= SBEG + KSPACE /\ 0 <= r_mapped_fa r <= 2 ^ 29 /\ 4 * Z.of_nat (length (r_free r)) <= r_mapped_fa r
    /\ 0 <= r_mapped_user r
    /\ SBEG + KSPACE <= reginfo bt c /\ reginfo bt c + 128 <= SBEG + KSPACE + PG
    /\ region_beg SBEG c mod PG = 0 /\ fa_beg SBEG c mod PG = 0 /\ r_mapped_user r mod PG = 0 /\ r_mapped_fa r mod PG = 0.
  Proof using W qg qt FF Lc RUN.
    intros c Hc. destruct W as ((WR & _) & _). destruct (WR c Hc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _).
    pose proof fixed_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & SM).
    clear R4 WR W.
    cbn zeta. unfold region_beg, fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, KUSERMAP, KFAMAP, KREGION_EXHAUST, PG in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia).
    assert (2 ^ 32 <= c * 2 ^ 32) by nia.
    assert (E1 : SBEG = 65536 * (SBEG / 65536)) by (apply Z.div_exact; lia). set (q1 := SBEG / 65536) in *.
    assert (M1 : (SBEG + c * 2 ^ 32) mod 4096 = 0).
    { apply (proj2 (Z.mod_divide _ 4096 ltac:(lia))). exists (16 * q1 + c * 2 ^ 20). lia. }
    assert (M2 : (SBEG + c * 2 ^ 32 + 3758096384) mod 4096 = 0).
    { apply (proj2 (Z.mod_divide _ 4096 ltac:(lia))). exists (16 * q1 + c * 2 ^ 20 + 917504). lia. }
    assert (M3 : r_mapped_user (a_reg st c) mod 4096 = 0).
    { assert (E2 : r_mapped_user (a_reg st c) = 2 ^ 18 * (r_mapped_user (a_reg st c) / 2 ^ 18)) by (apply Z.div_exact; lia).
      apply (proj2 (Z.mod_divide _ 4096 ltac:(lia))). exists (64 * (r_mapped_user (a_reg st c) / 2 ^ 18)). lia. }
    assert (M4 : r_mapped_fa (a_reg st c) mod 4096 = 0).
    { assert (E2 : r_mapped_fa (a_reg st c) = 2 ^ 18 * (r_mapped_fa (a_reg st c) / 2 ^ 18)) by (apply Z.div_exact; lia).
      apply (proj2 (Z.mod_divide _ 4096 ltac:(lia))). exists (64 * (r_mapped_fa (a_reg st c) / 2 ^ 18)). lia. }
    repeat split; assumption || lia.
  Qed.

  Lemma node_blocks_range : forall b, In b (node_blocks bt (a_dep st)) -> 0 < b /\ b + 2 ^ 20 <= CEIL /\ b mod PG = 0.
  Proof using W qg qt FF Lc.
    intros b [<- | Hb].
    - pose proof fixed_facts as (_ & _ & _ & _ & _ & _ & _ & N1 & N2 & _).
      destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & _ & _ & INN & _) & _).
      destruct (RNG _ _ (all_ranges_fixed _ INN)) as ((A1 & _ & A3 & _ & _) & A2 & A4 & _). repeat split; lia || assumption.
    - destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
      assert (HD : In (b, b + 2 ^ 20) (dyn_ranges st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. }
      destruct (RNG _ _ (all_ranges_dyn _ HD)) as ((A1 & _ & A3 & _ & _) & A2 & A4 & _). repeat split; lia || assumption.
  Qed.

  Lemma store_blocks_range : forall b, In b (store_blocks bt (a_dep st)) -> 0 < b /\ b + 2 ^ 23 <= CEIL /\ b mod PG = 0.
  Proof using W qg qt FF Lc.
    intros b [<- | Hb].
    - destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & _ & _ & _ & INS & _) & _).
      destruct (RNG _ _ (all_ranges_fixed _ INS)) as ((A1 & _ & A3 & _ & _) & A2 & A4 & _). repeat split; lia || assumption.
    - destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
      assert (HD : In (b, b + 2 ^ 23) (dyn_ranges st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. right. apply in_app_iff. right. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. }
      destruct (RNG _ _ (all_ranges_dyn _ HD)) as ((A1 & _ & A3 & _ & _) & A2 & A4 & _). repeat split; lia || assumption.
  Qed.

  Lemma node_addr_range : forall id, 1 <= id <= dp_nids (a_dep st) ->
    In (nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) (node_blocks bt (a_dep st))
    /\ 0 < node_addr bt (a_dep st) id /\ node_addr bt (a_dep st) id + 16 <= CEIL /\ node_addr bt (a_dep st) id mod 8 = 0.
  Proof using W qg qt FF Lc.
    intros id Hid. destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & _) & _).
    assert (HIn : In (nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) (node_blocks bt (a_dep st))).
    { apply nth_In_lt. (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end).
      assert (id / 2 ^ 16 <= dp_nids (a_dep st) / 2 ^ 16) by (apply Z.div_le_mono; lia).
      assert (0 <= id / 2 ^ 16) by (apply Z.div_pos; lia). lia. }
    split; [exact HIn|]. destruct (node_blocks_range _ HIn) as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold node_addr in G in change_no_check G' end).
    set (b := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *.
    assert (0 <= id mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    unfold PG in *. repeat split; lia.
  Qed.

  Lemma node_addr_block : forall id, 1 <= id <= dp_nids (a_dep st) ->
    nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0 <= node_addr bt (a_dep st) id
    /\ node_addr bt (a_dep st) id + 16 <= nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0 + 2 ^ 20.
  Proof using.
    intros id Hid. (lazymatch goal with |- ?G => let G' := eval unfold node_addr in G in change_no_check G' end). assert (0 <= id mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia). lia.
  Qed.

  Lemma fake_frame_facts : forall f k, In (f, k) FF ->
    bt_fs bt + 0x9000 <= f /\ f + FS k <= bt_fs bt + FAKE_SIZE /\ f mod FS k = 0 /\ 64 <= FS k <= 512 /\ 0 <= k <= KMAXCLASS
    /\ 0 <= fpos bt f k < FCAP k /\ f = fake_frame_addr (bt_fs bt) k (fpos bt f k).
  Proof using W qg qt Lc st RUN.
    intros f k Hin. destruct W as (_ & _ & _ & _ & _ & (K1 & _) & _). destruct (K1 f k Hin) as (Hk & Hp & Ef).
    pose proof fixed_facts as (_ & _ & _ & _ & _ & _ & FSM & _).
    pose proof (frame_geom k (fpos bt f k) (bt_fs bt) Hk Hp FSM) as G. cbn zeta in G. rewrite <- Ef in G.
    destruct G as (G1 & G2 & G3 & G4 & _). repeat split; lia || assumption.
  Qed.

  Lemma cache_len : forall c, 1 <= c <= 30 -> Z.of_nat (length (a_cache st c)) <= 16.
  Proof using W qg qt FF Lc bt RUN.
    intros c Hc. destruct W as (_ & WC & _). destruct (WC c Hc) as (C1 & _). unfold cache_max, cache_hint in C1. lia.
  Qed.
End Facts.

(* [comment removed for export] *)
Definition rep_cells (bt : as_boot) (st : ast) (Lc FF : list (Z * Z)) (a : Z) : Prop :=
  consts_cells bt a
  \/ instance_cells bt st a
  \/ thread_cells bt a
  \/ (exists c, 1 <= c <= 30 /\ foot_region bt st c a)
  \/ (exists b, In b (a_tq st ++ a_gq st) /\ foot_batch b a)
  \/ (exists sc, In sc (a_sec st) /\ foot_sec sc a)
  \/ (exists p n, (In (p, n) Lc \/ In (p - 16, n) (quar st)) /\ foot_hdr p n a)
  \/ foot_depot_static bt a
  \/ (exists id, 1 <= id <= dp_nids (a_dep st) /\ foot_node bt (a_dep st) id a)
  \/ foot_fake_static bt a
  \/ (exists f k, In (f, k) FF /\ foot_fword f k a)
  \/ ialloc_cells bt a
  \/ (exists c, 1 <= c <= 30 /\ foot_shreg bt st Lc c a)
  \/ (exists sc, In sc (a_sec st) /\ foot_shsec st sc a)
  \/ rtc_cells bt a.

Section FrameThm.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  Definition OPS_Rep_frame : Prop := forall st Lc FF M M' mdl,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> ~ rep_cells bt st Lc FF (bv_unsigned a) /\ M' a <> None) ->
    Rep bt st Lc FF M' mdl.

  Tactic Notation "pick" integer(n) := do n right; left.

  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  (* [comment removed for export] *)
  Theorem Rep_frame_q : forall st Lc FF M M' mdl {qt qg : Z},
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> ~ rep_cells bt st Lc FF (bv_unsigned a) /\ M' a <> None) ->
    Rep bt st Lc FF M' mdl.
  Proof using.
    intros st Lc FF M M' mdl qt qg W R CH.
    assert (DEF : DEFK M M') by (intros a Ha; exact (proj2 (CH a Ha))).
    assert (AG : forall i, rep_cells bt st Lc FF i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { apply agree_at. intros a Ha. exact (proj1 (CH a Ha)). }
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in *.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    split. { (* [comment removed for export] *) eapply cells_hold_frame; [exact R1 | exact YC |]. intros c i Hc Hi.
             rewrite Forall_forall in YC. destruct (YC c Hc). apply AG; [| ulia]. pick 0. exists c. split; assumption. }
    split. { (* [comment removed for export] *) pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _).
             eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. apply AG; [pick 1; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_thread_frame; [exact DEF | exact R3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. apply AG; [pick 2; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) intros c Hc. destruct (R4 c Hc) as [G F]. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
             destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
             eapply rep_region_frame; [exact DEF | exact G | exact F | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. apply AG; [pick 3; exists c; split; [exact Hc | exact Hi] | exact Hr]. }
    assert (BR : forall b, In b (a_tq st ++ a_gq st) -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP).
    { intros b Hb. destruct (batch_facts bt st Lc FF W b Hb) as (_ & L1 & L2 & L3). unfold BATCHSZ in *. repeat split; ulia. }
    split. { (* [comment removed for export] *) eapply rep_batches_frame; [exact DEF | exact R5 | intros b Hb; apply BR; apply in_app_iff; left; exact Hb |].
             intros b i Hb Hi Hr. apply AG; [pick 4; exists b; split; [apply in_app_iff; left; exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_batches_frame; [exact DEF | exact R6 | intros b Hb; apply BR; apply in_app_iff; right; exact Hb |].
             intros b i Hb Hi Hr. apply AG; [pick 4; exists b; split; [apply in_app_iff; right; exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. apply AG; [pick 5; exists sc; split; [exact Hs | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_headers_frame; [exact DEF | exact R8 | | |].
             - intros p n Hin. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n). ulia.
             - intros m n Hin. destruct (quar_item_range bt st Lc FF W m n Hin) as (A1 & A2 & A3). pose proof (rz_range n). ulia.
             - intros p n i Hin Hi Hr. apply AG; [pick 6; exists p, n; split; [exact Hin | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. apply AG; [pick 7; exact Hi | exact Hr].
             - intros id i Hid Hi Hr. apply AG; [pick 8; exists id; split; [exact Hid | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k Hin. destruct (fake_frame_facts bt st Lc FF W f k Hin) as (A1 & A2 & A3 & A4 & _). (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end). ulia.
             - intros i Hi Hr. apply AG; [pick 9; exact Hi | exact Hr].
             - intros f k i Hin Hi Hr. apply AG; [pick 10; exists f, k; split; [exact Hin | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. apply AG; [pick 11; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_shadow_frame; [exact DEF | exact R12 | | | |].
             - intros c Hc. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
               destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros c i Hc Hi Hr. apply AG; [pick 12; exists c; split; [exact Hc | exact Hi] | exact Hr].
             - intros sc i Hs Hi Hr. apply AG; [pick 13; exists sc; split; [exact Hs | exact Hi] | exact Hr]. }
    split; [exact R13|]. split; [exact R14|].
    assert (AGR : forall i, rtc_cells bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) by (intros i Hi Hr; apply AG; [do 14 right; exact Hi | exact Hr]).
    pose proof (rep_tail_frame bt Lc FF M M' DEF R15 R16 R17 R18 ltac:(ulia) ltac:(ulia) ltac:(ulia) ltac:(ulia) AGR) as (T1' & T2' & T3' & T4').
    split; [exact T1'|]. split; [exact T2'|]. split; [exact T3'|]. split; [exact T4'|].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.

  Theorem Rep_frame : OPS_Rep_frame.
  Proof using. intros st Lc FF M M' mdl W R CH. exact (Rep_frame_q st Lc FF M M' mdl W R CH). Qed.
End FrameThm.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zforallb (f : Z -> bool) (lo : Z) (k : nat) : bool :=
  match k with O => true | S k' => f lo && zforallb f (lo + 1) k' end.
Lemma zforallb_spec : forall f k lo, zforallb f lo k = true -> forall n, lo <= n < lo + Z.of_nat k -> f n = true.
Proof.
  intros f k. induction k as [|k IH]; intros lo H n Hn; [lia|].
  cbn [zforallb] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec n lo) as [->|NE]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.
Definition RZC (c : Z) : Z :=
  if c <=? 2 then 0 else if c <=? 4 then 1 else if c <=? 16 then 2 else if c <=? 22 then 3 else if c <=? 26 then 4 else if c <=? 28 then 5 else 6.
Definition unif_test (n : Z) : bool := Z.eqb (rz_log n) (RZC (class_of (needed n))).
Lemma unif_check : zforallb unif_test 1 (Z.to_nat 64512) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_of_class : forall n, 1 <= n -> is_primary n = true -> rz_log n = RZC (blk_class n).
Proof.
  intros n Hn HP. apply (is_primary_iff n Hn) in HP.
  pose proof (zforallb_spec unif_test (Z.to_nat 64512) 1 unif_check n) as C.
  rewrite Z2Nat.id in C by lia. specialize (C ltac:(lia)). unfold unif_test in C. apply Z.eqb_eq in C. exact C.
Qed.
Lemma rz_unif : forall n n', 1 <= n -> 1 <= n' -> is_primary n = true -> is_primary n' = true ->
  blk_class n = blk_class n' -> rz n = rz n'.
Proof.
  intros n n' Hn Hn' P P' E. (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). rewrite (rz_of_class n Hn P), (rz_of_class n' Hn' P'), E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gran_sep : forall X Y p n g, (p + n <= X /\ X mod 8 = 0) \/ Y <= p ->
  p / 8 <= g < (p + n + 7) / 8 -> X / 8 <= g < Y / 8 -> False.
Proof. intros X Y p n g H H1 H2. lia. Qed.

Lemma NoDup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|h t IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|h' t' NI ND']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y ND' Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

Section Geom1.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  #[local] Definition disj (x y : Z * Z) : Prop := snd x <= fst y \/ snd y <= fst x.

  (* [comment removed for export] *)
  Lemma chunk_cases : forall c a c' a', 1 <= c <= 30 -> 1 <= c' <= 30 -> carved bt st c a -> carved bt st c' a' ->
    (c = c' /\ a = a') \/ a + csize c <= a' \/ a' + csize c' <= a.
  Proof using W qg qt FF Lc RUN.
    intros c a c' a' Hc Hc' CA CA'.
    destruct (carved_range bt st Lc FF W c a Hc CA) as (A1 & A2 & _). destruct (carved_range bt st Lc FF W c' a' Hc' CA') as (B1 & B2 & _).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. pose proof (region_facts bt st Lc FF W c' Hc') as RF'. cbn zeta in RF, RF'.
    destruct RF as (Q1 & Q2 & Q3 & _). destruct RF' as (Q1' & Q2' & Q3' & _).
    destruct (Z.eq_dec c c') as [<-|NE].
    - destruct CA as (j & Hj & Hle & Ea). destruct CA' as (j' & Hj' & Hle' & Ea').
      pose proof (csize_pos c Hc) as ((S1 & _) & _).
      destruct (Z.lt_trichotomy j j') as [LT|[EQ|GT]].
      + right; left. subst a a'. (lazymatch goal with |- ?G => let G' := eval unfold chunk_addr in G in change_no_check G' end). nia.
      + left. subst. split; reflexivity.
      + right; right. subst a a'. (lazymatch goal with |- ?G => let G' := eval unfold chunk_addr in G in change_no_check G' end). nia.
    - right. unfold region_beg, fa_beg, region_beg, KREGION, KFAOFF in *.
      destruct (Z.lt_trichotomy c c') as [LT|[EQ|GT]]; [| lia |].
      + left. assert (c * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by nia. lia.
      + right. assert (c' * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by nia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_chunk : forall p n, In (p, n) Lc -> is_primary n = true ->
    let c := blk_class n in let a := prim_alloc_beg p n in
    1 <= c <= 30 /\ carved bt st c a /\ in_live_c Lc c a /\ a + rz n = p /\ p + n <= a + csize c /\ 16 <= rz n.
  Proof using W qg qt FF RUN.
    intros p n Hin HP. destruct W as (_ & _ & _ & _ & (WL & _) & _). destruct (WL p n Hin) as (N1 & _ & _ & CV).
    pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). pose proof (rz_range n). cbn zeta.
    split; [exact U2|]. split; [exact (CV HP)|]. split; [exists p, n; repeat split; assumption || reflexivity|].
    unfold prim_alloc_beg, blk_class in *. repeat split; lia.
  Qed.

  Lemma quar_chunk : forall m n, In (m, n) (quar st) -> is_primary n = true ->
    let c := blk_class n in let a := prim_alloc_beg (m + 16) n in
    1 <= c <= 30 /\ carved bt st c a /\ in_quar_c st c a /\ a + rz n = m + 16 /\ m + 16 + n <= a + csize c /\ 16 <= rz n.
  Proof using W qg qt FF Lc RUN.
    intros m n Hin HP. destruct (quar_item bt st Lc FF W m n Hin) as (N1 & [[_ CV]|[HP' _]]); [| rewrite HP in HP'; discriminate HP'].
    pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). pose proof (rz_range n). cbn zeta.
    split; [exact U2|]. split; [exact CV|]. split; [exists m, n; repeat split; assumption || reflexivity|].
    unfold prim_alloc_beg, blk_class in *. repeat split; lia.
  Qed.

  Lemma live_sec : forall p n, In (p, n) Lc -> is_primary n = false ->
    exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n.
  Proof using W qg qt FF bt RUN.
    intros p n Hin HP. destruct W as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & REG & _) & _). exact (REG p n Hin HP).
  Qed.

  Lemma quar_sec : forall m n, In (m, n) (quar st) -> is_primary n = false ->
    exists sc, In sc (a_sec st) /\ sc_user sc = m + 16 /\ sc_n sc = n.
  Proof using W qg qt FF Lc bt RUN.
    intros m n Hin HP. destruct (quar_item bt st Lc FF W m n Hin) as (N1 & [[HP' _]|[_ RG]]); [rewrite HP in HP'; discriminate HP' | exact RG].
  Qed.

  Lemma sec_cases : forall s s', In s (a_sec st) -> In s' (a_sec st) ->
    s = s' \/ sc_map s + sc_mapsz s <= sc_map s' \/ sc_map s' + sc_mapsz s' <= sc_map s.
  Proof using W qg qt FF Lc bt RUN.
    intros s s' Hs Hs'. destruct W as (_ & _ & _ & (_ & _ & _ & _ & ND & _) & _).
    destruct (Z.eq_dec (sc_map s) (sc_map s')) as [E|NE].
    - left. exact (NoDup_map_inj sc_map (a_sec st) s s' ND Hs Hs' E).
    - right.
      assert (Hx : In (sc_map s, sc_map s + sc_mapsz s) (all_ranges bt st)).
      { apply all_ranges_dyn. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. left. apply in_map_iff. exists s. split; [reflexivity | exact Hs]. }
      assert (Hy : In (sc_map s', sc_map s' + sc_mapsz s') (all_ranges bt st)).
      { apply all_ranges_dyn. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. left. apply in_map_iff. exists s'. split; [reflexivity | exact Hs']. }
      pose proof (ar_disj_ne bt st Lc FF _ _ W Hx Hy ltac:(intros EQ; injection EQ; intros; exact (NE ltac:(assumption)))) as D.
      cbn in D. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_live_not_quar : forall sc, In sc (a_sec st) -> In (sc_user sc, sc_n sc) Lc -> ~ In (sc_user sc - 16, sc_n sc) (quar st).
  Proof using W qg qt FF bt RUN.
    intros sc Hs HL. destruct W as (_ & _ & _ & (_ & _ & _ & _ & _ & IFF & _) & _). exact (proj1 (IFF sc Hs) HL).
  Qed.

  (* [comment removed for export] *)
  Lemma resv6_facts : In (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) (bt_fixed bt)
    /\ bt_resv6 bt <= SBEG /\ SBEG + KSPACE + PG <= bt_resv6 bt + bt_resv6_len bt.
  Proof using W qg qt FF Lc st RUN. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6 & A & B & _) & _). repeat split; assumption. Qed.

  Lemma space_vs_fixed : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi <= SBEG \/ SBEG + KSPACE + PG <= lo.
  Proof using W qg qt FF Lc st RUN.
    intros lo hi Hin Hlen. destruct resv6_facts as (IN6 & A & B).
    assert (NE : (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) <> (lo, hi)) by (intros E; injection E; intros; unfold KSPACE, PG in *; lia).
    pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ IN6) (all_ranges_fixed bt st _ Hin) NE) as D. hnf in D. cbn in D. lia.
  Qed.

  Lemma space_vs_dyn : forall lo hi, In (lo, hi) (dyn_ranges st) -> hi <= SBEG \/ SBEG + KSPACE + PG <= lo.
  Proof using W qg qt FF Lc RUN.
    intros lo hi Hin. destruct resv6_facts as (IN6 & A & B).
    pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 Hin) as D. hnf in D. cbn in D. lia.
  Qed.

  Lemma fs_vs_fixed : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> FAKE_SIZE -> hi <= bt_fs bt \/ bt_fs bt + FAKE_SIZE <= lo.
  Proof using W qg qt FF Lc st RUN.
    intros lo hi Hin Hlen. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
    assert (NE : (bt_fs bt, bt_fs bt + FAKE_SIZE) <> (lo, hi)) by (intros E; injection E; intros; lia).
    pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ Hin) NE) as D. hnf in D. cbn in D. lia.
  Qed.

  Lemma fs_vs_dyn : forall lo hi, In (lo, hi) (dyn_ranges st) -> hi <= bt_fs bt \/ bt_fs bt + FAKE_SIZE <= lo.
  Proof using W qg qt FF Lc RUN.
    intros lo hi Hin. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
    pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INFS Hin) as D. hnf in D. cbn in D. lia.
  Qed.

  Lemma sec_dyn : forall sc, In sc (a_sec st) -> In (sc_map sc, sc_map sc + sc_mapsz sc) (dyn_ranges st).
  Proof using. intros sc Hs. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. left. apply in_map_iff. exists sc. split; [reflexivity | exact Hs]. Qed.
  Lemma node_dyn : forall b, In b (dp_nodeblocks (a_dep st)) -> In (b, b + 2 ^ 20) (dyn_ranges st).
  Proof using. intros b Hb. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. Qed.

  Lemma ar_disj_app : forall A B x y, all_ranges bt st = A ++ B -> In x A -> In y B -> disj x y.
  Proof using W qg qt FF Lc RUN.
    intros A B [xl xh] [yl yh] E Hx Hy. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & PW & _) & _).
    destruct (in_split _ _ Hx) as (A1 & A2 & EA).
    assert (E' : all_ranges bt st = A1 ++ (xl, xh) :: (A2 ++ B)) by (rewrite E, EA, <- app_assoc; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold disj in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). destruct (PW A1 (A2 ++ B) xl xh yl yh E' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hy)); lia.
  Qed.

  Lemma sec_vs_node : forall sc b, In sc (a_sec st) -> In b (dp_nodeblocks (a_dep st)) ->
    sc_map sc + sc_mapsz sc <= b \/ b + 2 ^ 20 <= sc_map sc.
  Proof using W qg qt FF Lc bt RUN.
    intros sc b Hs Hb.
    pose proof (ar_disj_app (bt_fixed bt ++ map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                            (map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)))
                            (sc_map sc, sc_map sc + sc_mapsz sc) (b, b + 2 ^ 20)) as D.
    unfold disj in D; cbn in D. apply D.
    - (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite <- app_assoc. reflexivity.
    - apply in_app_iff. right. apply in_map_iff. exists sc. split; [reflexivity | exact Hs].
    - apply in_app_iff. left. apply in_map_iff. exists b. split; [reflexivity | exact Hb].
  Qed.
  Lemma store_dyn : forall b, In b (dp_storeblocks (a_dep st)) -> In (b, b + 2 ^ 23) (dyn_ranges st).
  Proof using. intros b Hb. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff. right. apply in_app_iff. right. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. Qed.

  Lemma sec_vs_store : forall sc b, In sc (a_sec st) -> In b (dp_storeblocks (a_dep st)) ->
    sc_map sc + sc_mapsz sc <= b \/ b + 2 ^ 23 <= sc_map sc.
  Proof using W qg qt FF Lc bt RUN.
    intros sc b Hs Hb.
    pose proof (ar_disj_app (bt_fixed bt ++ map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st) ++ map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)))
                            (map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)))
                            (sc_map sc, sc_map sc + sc_mapsz sc) (b, b + 2 ^ 23)) as D.
    unfold disj in D; cbn in D. apply D.
    - (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite <- !app_assoc. reflexivity.
    - apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists sc. split; [reflexivity | exact Hs].
    - apply in_map_iff. exists b. split; [reflexivity | exact Hb].
  Qed.
End Geom1.


(* [comment removed for export] *)
