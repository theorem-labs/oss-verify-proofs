(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsKSys4.

Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section N6.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  (* [comment removed for export] *)
  Definition shpage_boot (pb n : Z) : Prop :=
    (exists b m : word, In (b, m) (bt_maps0 bt) /\ u b <= pb /\ pb + n <= u b + u m)
    /\ (forall a, pb <= a < pb + n -> pg_in_ivz (bt_lazy0 bt) a /\ ~ in_ivz (bt_noacc0 bt) a)
    /\ (forall iv, In iv (bt_reserved bt) -> u (fst iv) + u (snd iv) <= AS_LO).

  Section Range.
    Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl mdlm : Model) (pb n : Z).
    Hypothesis W : WF bt st Lc FF.
    Hypothesis R : Rep bt st Lc FF M mdl.
    Hypothesis SBM : same_but_materialized mdl mdlm.
    Hypothesis MI : MInv (a_aa st) mdlm.
    Hypothesis MWF : model_ivs_wf mdlm.
    Hypotheses (ALp : pb mod PG = 0) (ALn : n mod PG = 0) (POS : 0 < n) (LO : AS_LO <= pb) (HI : pb + n <= AS_HEAPLO).
    Hypothesis SB0 : shpage_boot pb n.
    #[local] Notation hm := (m_vmmaps mdlm).
    #[local] Notation wpb := (Z_to_bv 64 pb).
    #[local] Notation wn := (Z_to_bv 64 n).

    Lemma band_lits : 0 < AS_LO /\ AS_HEAPLO < CEIL0 /\ CEIL0 <= CEIL /\ 0 <= pb /\ pb + n < 2 ^ 64 /\ u wpb = pb /\ u wn = n.
    Proof using HI LO POS.
      pose proof ceil_rng as CR. unfold AS_LO, AS_HEAPLO in *.
      assert (X : 0 <= pb /\ pb + n < 2 ^ 64) by lia.
      repeat split; try lia; rewrite u64_lit; lia.
    Qed.


    Lemma ledger_m : rep_ledger bt st mdlm.
    Proof using SBM R mdl M FF Lc. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _). exact (rep_ledger_sbm bt st mdl mdlm SBM R13). Qed.


    Lemma range_not_noaccess : forall a, pb <= a < pb + n -> ~ in_ivz (vm_noaccess hm) a.
    Proof using SB0 SBM R mdl M FF Lc st bt RUN.
      intros a Ha X. destruct ledger_m as (_ & L2 & _). apply (proj1 (L2 a)) in X. destruct X as [X _].
      destruct SB0 as (_ & LZ & _). exact (proj2 (LZ a Ha) X).
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma shpage_map_contains : map_contains (vm_maps hm) wpb wn = true.
    Proof using SB0 HI LO POS SBM R mdl M FF Lc st bt RUN.
      pose proof band_lits as (_ & _ & _ & P0 & P1 & Upb & Un).
      destruct SB0 as ((b & m & Hin & B1 & B2) & _). (lazymatch goal with |- ?G => let G' := eval unfold map_contains in G in change_no_check G' end). apply existsb_exists. exists (b, m). split.
      - apply (maps0_in_vm_maps bt st mdlm (b, m) ledger_m Hin).
      - (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Upb, Un. apply andb_true_intro. split; apply Z.leb_le; lia.
    Qed.

    Lemma shpage_region_free : region_free (vm_reserved hm) wpb wn = true.
    Proof using SB0 HI LO POS SBM R mdl M FF Lc st bt RUN.
      pose proof band_lits as (_ & _ & _ & P0 & P1 & Upb & Un).
      destruct ledger_m as (_ & _ & _ & _ & ER & _). rewrite ER. destruct SB0 as (_ & _ & RS).
      assert (G : forall l, (forall iv, In iv l -> u (fst iv) + u (snd iv) <= AS_LO) -> region_free l wpb wn = true).
      { intros l. induction l as [|[a sz] t IH]; intros Hl; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [region_free] in G in change_no_check G' end).
        apply andb_true_intro. split.
        - (lazymatch goal with |- ?G => let G' := eval unfold iv_overlap in G in change_no_check G' end). rewrite Upb. pose proof (Hl (a, sz) (or_introl eq_refl)) as X. cbn [fst snd] in X.
          apply Bool.negb_true_iff. apply Bool.andb_false_iff. left. apply Z.ltb_ge. lia.
        - apply IH. intros iv Hiv. apply Hl. right. exact Hiv. }
      exact (G _ RS).
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma shpage_noaccess_free : region_free (vm_noaccess hm) wpb wn = true.
    Proof using SB0 HI LO POS SBM R mdl M FF Lc st bt RUN.
      pose proof band_lits as (_ & _ & _ & P0 & P1 & Upb & Un).
      apply AsKSys6.region_free_of_bytes.
      - destruct ledger_m as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NP). exact NP.
      - rewrite Un. exact POS.
      - intros a Ha X. rewrite Upb, Un in Ha. exact (range_not_noaccess a Ha X).
    Qed.

    (* [comment removed for export] *)
    Theorem shpage_madvise_ok : Madvise.madvise_dontneed_ok hm wpb wn = true.
    Proof using SB0 HI LO POS SBM R mdl M FF Lc st bt RUN.
      (lazymatch goal with |- ?G => let G' := eval unfold Madvise.madvise_dontneed_ok in G in change_no_check G' end). rewrite shpage_region_free, shpage_map_contains, shpage_noaccess_free. reflexivity.
    Qed.


    (* [comment removed for export] *)
    (* [comment removed for export] *)
    #[local] Notation mdl2 := (Madvise.madvise_dontneed_next mdlm wpb wn).







  End Range.
End N6.
End AsKSys5.
Module AsKSys5q.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 AsKSys5.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section N6q.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Definition shadow_boot : Prop :=
    forall pb n, 0 < n -> (AS_LO <= pb /\ pb + n <= AS_GAPLO) \/ (AS_GAPHI <= pb /\ pb + n <= AS_HEAPLO) -> shpage_boot bt pb n.

  Definition SHADOW_GATE_stmt : Prop :=
    forall st Lc FF (M0 : mem) mdl mdlm (qt qg pb n : Z),
      WFq bt st Lc FF qt qg -> Rep bt st Lc FF M0 mdl ->
      same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm -> model_ivs_wf mdlm ->
      pb mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
      (SB <= pb /\ pb + n <= AS_GAPLO) \/ (AS_GAPHI <= pb /\ pb + n <= AS_HEAPLO) ->
      Madvise.madvise_dontneed_ok (m_vmmaps mdlm) (Z_to_bv 64 pb) (Z_to_bv 64 n) = true.

  Theorem shadow_gate_pf : shadow_boot -> SHADOW_GATE_stmt.
  Proof using.
    intros SBT st Lc FF M0 mdl mdlm qt qg pb n _ R SBM _ _ _ _ POS RNG.
    assert (RNG' : (AS_LO <= pb /\ pb + n <= AS_GAPLO) \/ (AS_GAPHI <= pb /\ pb + n <= AS_HEAPLO)) by (unfold SB, AS_LO in *; lia).
    apply (shpage_madvise_ok bt st Lc FF M0 mdl mdlm pb n R SBM POS).
    - unfold AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO in *; lia.
    - unfold AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO in *; lia.
    - exact (SBT pb n POS RNG').
  Qed.
End N6q.
End AsKSys5q.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys9.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Definition fixed_cov (bt : as_boot) : Prop :=
  forall lo hi a, In (lo, hi) (bt_fixed bt) -> (lo, hi) <> (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) -> lo <= a < hi -> in_ivz (bt_maps0 bt) a.
Definition band_cov (bt : as_boot) : Prop := forall a, in_band a -> in_ivz (bt_maps0 bt) a.
Definition res_hull (bt : as_boot) : Prop :=
  forall (a n : word), 0 < u n -> u a + u n <= 2 ^ 64 -> region_free (bt_reserved bt) a n = true ->
    u a + u n <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= u a.
Definition boot_geom (bt : as_boot) : Prop :=
  res_low bt /\ noacc0_sub bt /\ fixed_cov bt /\ band_cov bt /\ res_hull bt.
End AsKSys9.
Module AsAinvBootF3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 AsKSys5 AsKSys5q OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b AsKSys9.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BootFacts.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  Definition ptr8_entry : Prop := In (Z_to_bv 64 (bt_ptrarr bt), Z_to_bv 64 (2 ^ 23)) (bt_maps0 bt).
  (* [comment removed for export] *)
  Definition ptr8_sep : Prop :=
    forall l1 l2 y, bt_maps0 bt = l1 ++ (Z_to_bv 64 (bt_ptrarr bt), Z_to_bv 64 (2 ^ 23)) :: l2 -> In y (l1 ++ l2) ->
      bv_unsigned (fst y) + bv_unsigned (snd y) <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= bv_unsigned (fst y).
  Definition res_in_hull : Prop :=
    forall iv, In iv (bt_reserved bt) -> ia_img_lo (bt_ia bt) <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_hi (bt_ia bt).

  (* [comment removed for export] *)
  Definition stack_geom : Prop :=
    (bt_tctx bt + 0x10000 <= bt_thread bt \/ bt_thread bt + PG <= bt_tctx bt)
    /\ 4096 <= bt_stack_top bt <= 2 ^ 47 /\ 0 <= bt_stack_bottom bt < bt_stack_top bt.

  Definition boot_facts : Prop := boot_ok bt /\ boot_geom bt /\ shadow_boot bt /\ ptr8_entry /\ res_in_hull /\ stack_geom /\ ptr8_sep.

  Lemma boot_facts_ok : boot_facts -> boot_ok bt.  Proof using. intros (H & _). exact H. Qed.
  Lemma boot_facts_geom : boot_facts -> boot_geom bt.  Proof using. intros (_ & H & _). exact H. Qed.

  Lemma boot_facts_shadow : boot_facts -> shadow_boot bt.  Proof using. intros (_ & _ & H & _). exact H. Qed.
  Lemma boot_facts_ptr8 : boot_facts -> ptr8_entry.  Proof using. intros (_ & _ & _ & H & _). exact H. Qed.
  Lemma boot_facts_res_in_hull : boot_facts -> res_in_hull.  Proof using. intros (_ & _ & _ & _ & H & _). exact H. Qed.
  Lemma boot_facts_stack : boot_facts -> stack_geom.  Proof using. intros (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma boot_facts_ptr8_sep : boot_facts -> ptr8_sep.  Proof using. intros (_ & _ & _ & _ & _ & _ & H). exact H. Qed.
  Lemma boot_facts_gate : boot_facts -> SHADOW_GATE_stmt bt.  Proof using. intros BF. exact (shadow_gate_pf bt (boot_facts_shadow BF)). Qed.

  (* [comment removed for export] *)
  Lemma dep0_bounds : boot_ok bt -> dp_nids (bt_dep0 bt) <= 2 ^ 20 /\ 1 <= dp_frames (bt_dep0 bt) <= 2 ^ 20.
  Proof using. intros (_ & _ & _ & Dn & _ & _ & _ & _ & _ & _ & Dfr & _). rewrite Dn. split; [lia | exact Dfr]. Qed.

End BootFacts.
End AsAinvBootF3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvDepotObl3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DepotObl.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.

  (* [comment removed for export] *)
  Lemma node_block_range : forall b, In b (node_blocks bt (a_dep st)) -> In (b, b + 2 ^ 20) (all_ranges bt st).
  Proof using W qg qt FF Lc RUN.
    intros b [<- | Hb]; [| exact (all_ranges_dyn bt st _ (node_dyn st b Hb))].
    destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & INN & _). exact (all_ranges_fixed bt st _ INN).
  Qed.
  Lemma store_block_range : forall b, In b (store_blocks bt (a_dep st)) -> In (b, b + 2 ^ 23) (all_ranges bt st).
  Proof using W qg qt FF Lc RUN.
    intros b [<- | Hb]; [| exact (all_ranges_dyn bt st _ (store_dyn st b Hb))].
    destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & _ & INS & _). exact (all_ranges_fixed bt st _ INS).
  Qed.

  Lemma node_blocks_nolazy : forall M mdl b a, Rep bt st Lc FF M mdl -> In b (node_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 20 -> lzb mdl a = false.
  Proof using W qg qt.
    intros M mdl b a R Hb Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
    pose proof (node_block_range b Hb) as HR.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
    destruct (RNG _ _ HR) as ((A1 & A1' & A3 & A4 & A5) & _).
    destruct (fixed_members bt st Lc FF W) as (IN6 & IN8 & _ & _ & _ & INS & _).
    assert (NE : forall lo hi, hi - lo <> 2 ^ 20 -> In (lo, hi) (all_ranges bt st) -> hi <= b \/ b + 2 ^ 20 <= lo).
    { intros lo hi NL Hin. pose proof (ar_disj_ne bt st Lc FF (lo, hi) (b, b + 2 ^ 20) W Hin HR ltac:(intros EQ; injection EQ; intros; lia)) as D. hnf in D. cbn in D. lia. }
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & R6a & R6b & _) & _).
    destruct (rep_lazy_cases bt st Lc FF M mdl W R a ltac:(clear - Ha A1 A3; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); clear - Ha A5; dsj; ulia) E) as [([Z6 | [Z8 | ZS]] & _) | (b' & Hb' & Zb)].
    - destruct (NE (bt_resv6 bt) (bt_resv6 bt + bt_resv6_len bt) ltac:(unfold KSPACE, PG in *; lia) (all_ranges_fixed bt st _ IN6)); lia.
    - destruct (NE (bt_ptrarr bt) (bt_ptrarr bt + 2 ^ 23) ltac:(lia) (all_ranges_fixed bt st _ IN8)); lia.
    - destruct (NE (bt_store0 bt) (bt_store0 bt + 2 ^ 23) ltac:(lia) (all_ranges_fixed bt st _ INS)); lia.
    - destruct (NE b' (b' + 2 ^ 23) ltac:(lia) (all_ranges_dyn bt st _ (store_dyn st b' Hb'))); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma range_priv : forall lo hi a, In (lo, hi) (all_ranges bt st) -> lo <= a < hi ->
    (forall p n elo ehi, In (p, n) Lc -> ext bt st Lc p n elo ehi -> ehi <= lo \/ hi <= elo) ->
    (hi <= bt_fs bt \/ bt_fs bt + FAKE_SIZE <= lo) -> rt_priv IA Lc FF a.
  Proof using W qg qt.
    intros lo hi a HR Ha EXT FSD. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
    destruct (RNG _ _ HR) as ((SD1 & SD2 & SD3 & SD4 & SD5) & _).
    split; [ulia|]. split; [clear -Ha SD4; dsj; ulia|].
    destruct (heap_not_shadowish bt st Lc FF W Lc a ltac:(intros p n H; exact H) ltac:(clear -Ha SD5; dsj; ulia)) as (N1 & N2 & N3 & N4). clear SD4 SD5.
    intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
    - destruct V as (p & n & Hin & Hpa). destruct (live_ext bt st Lc FF W p n Hin) as (elo & ehi & E & Y1 & Y2 & _ & _ & _ & _ & _ & (RZ1 & _) & _ & (N1' & _) & _).
      pose proof (up8_facts n ltac:(lia)) as (U1 & _). destruct (EXT p n elo ehi Hin E); lia.
    - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _). ulia.
  Qed.

  Lemma node_blocks_priv : forall b a, In b (node_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 20 -> rt_priv IA Lc FF a.
  Proof using W qg qt.
    intros b a Hb Ha. apply (range_priv _ _ a (node_block_range b Hb) Ha).
    - intros p n elo ehi Hin E. exact (live_ext_vs_node bt st Lc FF W p n elo ehi b Hin E Hb).
    - destruct (fixed_members bt st Lc FF W) as (_ & _ & INFS & _).
      pose proof (ar_disj_ne bt st Lc FF (b, b + 2 ^ 20) (bt_fs bt, bt_fs bt + FAKE_SIZE) W (node_block_range b Hb) (all_ranges_fixed bt st _ INFS) ltac:(intros EQ; injection EQ; intros; unfold FAKE_SIZE in *; lia)) as D.
      hnf in D. cbn in D. lia.
  Qed.
  Lemma store_blocks_priv : forall b a, In b (store_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 23 -> rt_priv IA Lc FF a.
  Proof using W qg qt.
    intros b a Hb Ha. apply (range_priv _ _ a (store_block_range b Hb) Ha).
    - intros p n elo ehi Hin E. exact (live_ext_vs_store bt st Lc FF W p n elo ehi b Hin E Hb).
    - destruct (fixed_members bt st Lc FF W) as (_ & _ & INFS & _).
      pose proof (ar_disj_ne bt st Lc FF (b, b + 2 ^ 23) (bt_fs bt, bt_fs bt + FAKE_SIZE) W (store_block_range b Hb) (all_ranges_fixed bt st _ INFS) ltac:(intros EQ; injection EQ; intros; unfold FAKE_SIZE in *; lia)) as D.
      hnf in D. cbn in D. lia.
  Qed.
End DepotObl.

(* [comment removed for export] *)
Theorem depot_obls_pf : forall {RUN : run_ceil} (bt : as_boot),
  (forall st Lc FF M mdl b a, WF bt st Lc FF -> Rep bt st Lc FF M mdl -> In b (node_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 20 -> lzb mdl a = false)
  /\ (forall st Lc FF b a, WF bt st Lc FF -> In b (node_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 20 -> rt_priv (bt_ia bt) Lc FF a)
  /\ (forall st Lc FF b a, WF bt st Lc FF -> In b (store_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 23 -> rt_priv (bt_ia bt) Lc FF a).
Proof.
  intros RUN bt. split; [| split].
  - intros st Lc FF M mdl b a W R Hb Ha. exact (node_blocks_nolazy bt st Lc FF _ _ W M mdl b a R Hb Ha).
  - intros st Lc FF b a W Hb Ha. exact (node_blocks_priv bt st Lc FF _ _ W b a Hb Ha).
  - intros st Lc FF b a W Hb Ha. exact (store_blocks_priv bt st Lc FF _ _ W b a Hb Ha).
Qed.
End AsAinvDepotObl3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMDm.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DM.
  Variable segs : list Segment.

  Lemma doomed_kclosedD : kclosedD segs (doomed segs).
  Proof using.
    (* [comment removed for export] *)
    intros c I i0 nx Hn _ Hall. apply (doomed_node segs c I i0 nx Hn).
    intros i. destruct (Hall i) as [X|[]]; exact X.
  Qed.


  Lemma kfam_dm_laws : forall K, kclosedD segs K -> kfamD_laws segs (KF K (doomed segs) K K).
  Proof using.
    (* [comment removed for export] *)
    intros K HK. constructor; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try exact HK; try exact doomed_kclosedD; intros c X; exact X.
  Qed.

  Lemma katwD_dm : forall c (Qok Qf : config -> Prop),
    katwD segs c Qok Qf -> (forall c', Qf c' -> doomed segs c') -> katD segs c Qok.
  Proof using. intros c Qok Qf H HQ K HK Hk. exact (H (KF K (doomed segs) K K) (kfam_dm_laws K HK) Hk HQ). Qed.

End DM.
End AsAllocMDm.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocMSbRepc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Gap.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Lemma secgap_vs_rep : forall p n a, In (p, n) Lc -> is_primary n = false -> p - 8 <= a < p - 4 -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros p n a Hin HP Ha RC.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
    destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En).
    destruct (sec_facts bt st Lc FF W sc Hs) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). rewrite Eu, En in *.
    assert (S1 : sc_map sc + PG + 8 <= a) by ulia.
    assert (S2 : a < sc_map sc + sc_mapsz sc) by ulia.
    assert (FIX : forall lo hi, In (lo, hi) (bt_fixed bt) -> lo <= a < hi -> False).
    { intros lo hi Hf Hr. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hf (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. ulia. }
    assert (SPC : SBEG <= a < SBEG + KSPACE + PG -> False).
    { intros Hr. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia. }
    assert (DK : dyn_kind bt st a) by (apply (dyn_kind_dyn bt st _ _ a (sec_dyn st sc Hs)); ulia).
    destruct (dyn_kind_facts bt st Lc FF W a DK) as (O1 & O2 & O3 & O4). unfold in_band in O4. pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct RC as [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | K]]]]]]]]]]]]]].
    - (* [comment removed for export] *) destruct (img_kinds bt st Lc FF W a ltac:(left; exact K)) as [B _]. ulia.
    - (* [comment removed for export] *) destruct (decide (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
      + pose proof W as (_ & _ & _ & (Q1 & Q2 & Q3 & _) & _). apply (FIX _ _ IN8); ulia.
      + destruct (img_kinds bt st Lc FF W a ltac:(right; left; split; [exact K | exact NI])) as [B _]. ulia.
    - (* [comment removed for export] *) unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
      destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIX _ _ INT); (first [clear - K | idtac]; ulia) | apply (FIX _ _ INC); (first [clear - K | idtac]; ulia)].
    - (* [comment removed for export] *) destruct K as (c & Hc & K). pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _). unfold foot_region in K. apply SPC; ulia.
    - (* [comment removed for export] *) destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CV & BL & Bb1 & Bb2).
      apply SPC; ulia.
    - (* [comment removed for export] *) destruct K as (sc' & Hs' & K). unfold foot_sec in K.
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; ulia.
    - (* [comment removed for export] *) destruct K as (p' & n' & Hown & K).
      pose proof (rz_range n') as RZ'. pose proof (rz_range n) as RZ. pose proof (rz_mod16 n) as RZ16.
      destruct (hdr_zone bt st Lc FF W p' n' a Hown K) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
      + apply SPC; ulia.
      + destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia].
        assert (p' = p /\ n' = n) as [-> ->] by (split; congruence).
        destruct Hown as [HL' | HQ']; [unfold foot_hdr in K; ulia|].
        apply (sec_live_not_quar bt st Lc FF W sc Hs); rewrite Eu, En; [exact Hin | exact HQ'].
    - (* [comment removed for export] *) destruct (img_kinds bt st Lc FF W a ltac:(right; right; left; exact K)) as [B _]. ulia.
    - (* [comment removed for export] *) destruct K as (id & Hid & K). unfold foot_node in K.
      destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3).
      pose proof (node_addr_block bt st id Hid) as Hb.
      set (b := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *.
      clearbody b. destruct HIn as [Eb | Hnb].
      + apply (FIX _ _ INN). rewrite Eb. ulia.
      + destruct (sec_vs_node bt st Lc FF W sc b Hs Hnb) as [D|D]; clear - S1 S2 Ha Hb K D; ulia.
    - (* [comment removed for export] *) unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: apply (FIX _ _ INFS); (first [clear - K | idtac]; ulia).
      + destruct (img_kinds bt st Lc FF W a ltac:(do 3 right; left; exact K)) as [B _]. ulia.
      + apply (FIX _ _ (dtls_member bt st Lc FF W)); ulia.
    - (* [comment removed for export] *) destruct K as (f & k & Hf & K). unfold foot_fword in K.
      destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _). apply (FIX _ _ INFS); ulia.
    - (* [comment removed for export] *) destruct (img_kinds bt st Lc FF W a ltac:(do 4 right; left; exact K)) as [B _]. ulia.
    - (* [comment removed for export] *) destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
    - (* [comment removed for export] *) destruct K as (sc' & Hs' & K). unfold foot_shsec, sh_lo in K.
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & _). ulia.
    - (* [comment removed for export] *) destruct (img_kinds bt st Lc FF W a ltac:(do 5 right; exact K)) as [B _]. ulia.
  Qed.
End Gap.


(* [comment removed for export] *)
Lemma rdn_pt_eq : forall segs (k : nat) (M1 M2 : mem) (a : word) bs,
  rdn segs M1 a k = Some bs -> rdn segs M2 a k = Some bs -> bv_unsigned a + Z.of_nat k <= 2 ^ 64 ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> M1 x <> None -> M2 x <> None -> M1 x = M2 x.
Proof.
  intros segs k. induction k as [|k IH]; intros M1 M2 a bs R1 R2 Hk x Hx D1 D2; [cbn [Z.of_nat] in Hx; lia|].
  cbn [rdn] in R1, R2.
  destruct (match M1 a with Some b => Some b | None => seg_rom segs a end) as [b1|] eqn:E1; [| discriminate R1].
  destruct (match M2 a with Some b => Some b | None => seg_rom segs a end) as [b2|] eqn:E2; [| discriminate R2].
  destruct (rdn segs M1 (a + 1) k) as [r1|] eqn:T1; [| discriminate R1].
  destruct (rdn segs M2 (a + 1) k) as [r2|] eqn:T2; [| discriminate R2].
  injection R1 as <-. injection R2 as Eb Er. subst b2 r2.
  rewrite Nat2Z.inj_succ in Hk, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Exa | NE].
  - assert (x = a) as -> by (apply bv_eq; exact Exa).
    destruct (M1 a) as [c1|]; [| exfalso; exact (D1 eq_refl)]. destruct (M2 a) as [c2|]; [| exfalso; exact (D2 eq_refl)]. congruence.
  - pose proof (u64_range a) as Har.
    assert (Ua1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1).
    { rewrite bv_add_unsigned. change (bv_unsigned (1 : word))%bv with 1. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia. }
    apply (IH M1 M2 (a + 1)%bv r1 T1 T2); [rewrite Ua1; lia | rewrite Ua1; lia | exact D1 | exact D2].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End AsAllocMSbRepc.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys7c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition OKh (addr n : word) (m : Model) : Model := with_mmap_backing (Z_to_bv 64 50) addr n (mmap_model addr n m).
Lemma OKh_eq : forall addr n m, OKh addr n m = mmap_model addr n m.
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold OKh in G in change_no_check G' end). apply with_mmap_backing_plain. apply mmap_noreserve_b_32. Qed.

Lemma eager_OKh_le : forall addr n m, model_ivs_wf m -> u addr + u n <= 2 ^ 64 -> eager_used (OKh addr n m) <= eager_used m + u n.
Proof.
  intros addr n m Hwf Hend. pose proof Hwf as (Wm & Wn & Wl & Wsp).
  assert (Hwf' : model_ivs_wf (OKh addr n m)).
  { rewrite OKh_eq. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). apply model_ivs_wf_with_vmmaps; [exact Hwf | | exact Wn | reflexivity].
    (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps] in G in change_no_check G' end). apply ivs_wf_cons; [| exact Wm]. (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). exact Hend. }
  rewrite (eager_used_sem _ Hwf'), (eager_used_sem _ Hwf). rewrite OKh_eq. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess sum_count] in G in change_no_check G' end).
  pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (B (addr, n)) (Z.to_nat (S (addr, n)))) as Z1.
  (lazymatch goal with |- ?G => let G' := eval unfold iv_count in G in change_no_check G' end). unfold S in *. cbn [snd] in *. pose proof (bv_unsigned_in_range 64 n). rewrite Z2Nat.id in Z1 by lia. lia.
Qed.

Lemma region_free_perm : forall l l' (lo n : word), Permutation l l' -> region_free l lo n = true -> region_free l' lo n = true.
Proof.
  intros l l' lo n HP H. apply RefNodes.region_free_intro. intros b s Hin.
  exact (RefNodes.region_free_In l lo n b s H (Permutation_in _ (Permutation_sym HP) Hin)).
Qed.

Section SlotH.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (M0 : mem) (mdl : Model) (lo : Z) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.                                       (* [comment removed for export] *)
  Hypothesis HQ : qroom Lc qt qg.
  Hypothesis R : Rep bt st Lc FF M0 mdl.
  Hypothesis MW : model_ivs_wf mdl.
  Hypothesis HH : m_halted mdl = None.
  Hypothesis KC : a_kact st <= KCAP.
  Hypothesis RL : res_low bt.
  Hypotheses (SL1 : (lo - SBEG) mod KUSERMAP = 0) (SL2 : SBEG <= lo) (SL3 : lo + KUSERMAP <= SBEG + KSPACE).
  Hypothesis HO : forall a, lo <= a < lo + KUSERMAP -> holes bt st a.
  #[local] Notation addr := (Z_to_bv 64 lo).
  #[local] Notation size := (Z_to_bv 64 KUSERMAP).
  #[local] Notation K := KUSERMAP.
  #[local] Notation A2 := (a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)]).

  (* [comment removed for export] *)
  Lemma hole_no_maps : region_free (vm_maps (m_vmmaps mdl)) addr size = true.
  Proof using HO SL3 SL2 R W qg qt M0 FF Lc st bt RUN.
    destruct (slot_lits bt st Lc FF lo qt qg W SL2 SL3) as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & FOK & FSEP & FCOV) & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M0R6 & M0POS & _).
    apply (region_free_perm _ _ _ _ (Permutation_sym PM)). apply RefNodes.region_free_intro. intros b s Hin. rewrite L5, L6.
    destruct (Z_le_gt_dec (lo + K) (u b)) as [LE|GT]; [left; exact LE|]. destruct (Z_le_gt_dec (u b + u s) lo) as [LE2|GT2]; [right; exact LE2|]. exfalso.
    assert (K0 : 0 < K) by ((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
    apply in_app_iff in Hin as [Hin | Hin]; [| apply in_app_iff in Hin as [Hin | Hin]].
    - (* [comment removed for export] *)
      rewrite Forall_forall in FOK. destruct (FOK (b, s) Hin) as (F1 & F2 & F3 & _). cbn [fst snd] in F1, F2, F3.
      set (a := Z.max (u b) lo). assert (Ha : lo <= a < lo + K) by ((lazymatch goal with |- ?G => let G' := eval unfold a in G in change_no_check G' end); lia).
      apply (proj1 (FCOV a ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_resv6, a in G in change_no_check G' end); lia))); [exists b, s; split; [exact Hin | (lazymatch goal with |- ?G => let G' := eval unfold a in G in change_no_check G' end); lia] | exact (HO a Ha)].
    - rewrite Forall_forall in M0POS. pose proof (M0POS (b, s) Hin) as Pn. cbn [snd] in Pn.
      apply (M0R6 b s (Z.max (u b) lo) Hin); lia.
    - assert (DR : exists dl dh, In (dl, dh) (dyn_ranges st) /\ b = Z_to_bv 64 dl /\ s = Z_to_bv 64 (dh - dl)).
      { unfold dyn_maps in Hin. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]];
          apply in_map_iff in Hin as (x & E & Hx); injection E as <- <-.
        - exists (sc_map x), (sc_map x + sc_mapsz x). split; [apply in_app_iff; left; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]].
        - exists x, (x + 2 ^ 20). split; [apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]].
        - exists x, (x + 2 ^ 23). split; [apply in_app_iff; right; apply in_app_iff; right; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]]. }
      destruct DR as (dl & dh & Hd & -> & ->).
      destruct (RNG dl dh (all_ranges_dyn bt st _ Hd)) as ((D1 & D2 & D3 & _) & D6 & _).
      pose proof ceil_rng as CR. rewrite (u64_lit dl) in GT, GT2 by lia. rewrite (u64_lit (dh - dl)) in GT2 by lia.
      destruct (space_vs_dyn bt st Lc FF W dl dh Hd) as [S|S]; unfold KSPACE, PG, KUSERMAP in *; lia.
  Qed.

  Lemma hole_no_noacc : forall a, lo <= a < lo + K -> ~ in_ivz (vm_noaccess (m_vmmaps mdl)) a.
  Proof using HO R M0 FF Lc st bt RUN.
    intros a Ha Hn. destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & NA & _). destruct (proj1 (NA a) Hn) as (_ & _ & NHo). exact (NHo (HO a Ha)).
  Qed.
  Lemma hole_no_lazy : forall a, lo <= a < lo + K -> ~ pg_in_ivz (m_vm_lazy mdl) a.
  Proof using HO SL3 SL2 R W qg qt M0 FF Lc st bt RUN.
    intros a Ha Hl. destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & LZ & _).
    destruct (proj1 (LZ a) Hl) as [(_ & _ & NHo) | (b & Hb & Zb)]; [exact (NHo (HO a Ha))|].
    destruct (space_vs_dyn bt st Lc FF W b (b + 2 ^ 23) (store_dyn st b Hb)) as [S|S]; unfold KSPACE, PG, KUSERMAP in *; lia.
  Qed.

  Section Mat.
    Variable mdlm : Model.
    Hypothesis SBM : same_but_materialized mdl mdlm.
    Hypothesis MI : MInv (a_aa st) mdlm.

    Lemma nodeH_free : region_free (vm_reserved (m_vmmaps mdlm) ++ vm_maps (m_vmmaps mdlm)) addr size = true.
    Proof using SBM HO SL3 SL2 RL HH MW R W qg qt mdl M0 FF Lc st bt RUN.
      rewrite RefNodes.region_free_app. apply andb_true_intro. split.
      - exact (node_region_free bt st Lc FF M0 mdl lo qt qg W R MW HH RL SL2 SL3 mdlm SBM).
      - destruct (sbm_vmmaps mdl mdlm SBM) as [E1 _]. rewrite E1. exact hole_no_maps.
    Qed.

    Lemma nodeH_backed : mmap_noreserve_backed_ok (Z_to_bv 64 50) mdlm K = true.
    Proof using MI SBM SL2 KC HH MW R HQ W qg qt lo mdl M0 FF Lc st bt RUN.
      (lazymatch goal with |- ?G => let G' := eval unfold mmap_noreserve_backed_ok in G in change_no_check G' end). rewrite mmap_noreserve_b_32. apply Z.leb_le.
      destruct (mat_eqs mdl MW HH mdlm SBM) as (E1 & E2 & E3 & E4 & E5).
      destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AW & _) & _).
      pose proof (vm_backing_used_le (a_aa st) mdlm MI AW). rewrite E1, E3 in *.
      pose proof (budget_slack bt st Lc FF M0 mdl lo qt qg W HQ R KC SL2). unfold ROOMSLACK, KUSERMAP in *. lia.
    Qed.

    Lemma nodeH_OK : m_halted (OKh addr size mdlm) = None /\ MInv (a_aa st) (OKh addr size mdlm)
      /\ (forall p, page_in_ranges p (m_vm_lazy (OKh addr size mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true).
    Proof using MI SBM SL3 SL2 KC HH MW R HQ W qg qt M0 FF Lc bt RUN.
      destruct (slot_lits bt st Lc FF lo qt qg W SL2 SL3) as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct (mat_eqs mdl MW HH mdlm SBM) as (E1 & E2 & E3 & E4 & E5).
      split; [rewrite OKh_eq; exact E4|]. split.
      - pose proof (eager_OKh_le addr size mdlm E5 ltac:(rewrite L5, L6; lia)) as EG. rewrite L6 in EG.
        destruct MI as [N1 N2 N3 N4 N5]. constructor; try (rewrite OKh_eq; assumption).
        rewrite OKh_eq at 2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end). rewrite E1, E3 in *.
        pose proof (budget_slack bt st Lc FF M0 mdl lo qt qg W HQ R KC SL2). unfold ROOMSLACK, KUSERMAP in *. lia.
      - intros p Hp. rewrite OKh_eq in Hp. unfold mmap_model in Hp. model_proj. rewrite <- E2. exact Hp.
    Qed.
  End Mat.

  Section PostH.
    Variables mdlm mdl' : Model.
    Hypothesis SBM : same_but_materialized mdl mdlm.
    Hypothesis SBM' : same_but_materialized (OKh addr size mdlm) mdl'.

    Lemma postH_eqs : m_vmmaps mdl' = m_vmmaps (mmap_model addr size mdl) /\ m_vm_lazy mdl' = m_vm_lazy mdl.
    Proof using SBM' SBM mdlm.
      destruct (sbm_vmmaps mdl mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite E3, E4, OKh_eq. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. rewrite E1, E2. split; reflexivity.
    Qed.

    Lemma postH_eager : eager_used mdl' <= eager_used mdl + K.
    Proof using SBM' SBM mdlm SL3 SL2 MW W qg qt lo FF Lc st bt RUN.
      destruct (slot_lits bt st Lc FF lo qt qg W SL2 SL3) as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct postH_eqs as [E1 E2].
      rewrite (eager_used_ext mdl' (OKh addr size mdl)); [| rewrite OKh_eq; exact E1 | rewrite OKh_eq; exact E2].
      pose proof (eager_OKh_le addr size mdl MW ltac:(rewrite L5, L6; lia)) as EG. rewrite L6 in EG. exact EG.
    Qed.

    Lemma postH_widen : MInv (a_aa st) mdl' -> MInv A2 mdl'.
    Proof using SBM' SBM mdlm SL3 SL2 KC MW R HQ W qg qt mdl M0 FF Lc bt RUN.
      intros MI. apply MInv_widen; [exact MI|]. destruct postH_eqs as [E1 _]. rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end).
      pose proof postH_eager. pose proof (budget_slack bt st Lc FF M0 mdl lo qt qg W HQ R KC SL2). unfold ROOMSLACK, KUSERMAP in *. change (2 ^ 18 / 8) with 32768. lia.
    Qed.

    Lemma postH_ledger :
      Permutation (vm_maps (m_vmmaps mdl')) ((addr, size) :: vm_maps (m_vmmaps mdl))
      /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + K))
      /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
      /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + K))
      /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
                (m_vm_lazy mdl')
      /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
      /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
      /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).
    Proof using SBM' SBM mdlm HO SL3 SL2 R W qg qt M0 FF Lc st.
      destruct postH_eqs as [E1 E2]. rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj.
      (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end).
      destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & LOK & _ & _ & _ & _ & _ & _ & _ & NPOS).
      split; [apply Permutation_refl|].
      split; [intros a; split; [intros Hn; split; [exact Hn | intros Ha; exact (hole_no_noacc a Ha Hn)] | intros [Hn _]; exact Hn]|].
      split; [exact NPOS|].
      split; [intros a; split; [intros Hl; split; [exact Hl | intros Ha; exact (hole_no_lazy a Ha Hl)] | intros [Hl _]; exact Hl]|].
      split; [exact LOK|]. repeat split; reflexivity.
    Qed.

    Lemma postH_rest : same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ model_ivs_wf mdl' /\ m_halted mdl' = None.
    Proof using SBM' SBM mdlm SL3 SL2 HH MW W qg qt lo st.
      destruct (slot_lits bt st Lc FF lo qt qg W SL2 SL3) as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct postH_eqs as [E1 E2].
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold same_except_vm in G in change_no_check G' end). rewrite (sbm_frame_vm _ _ SBM'). rewrite OKh_eq. rewrite (sbm_frame_vm _ _ SBM). reflexivity. }
      split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite E2; reflexivity|].
      split.
      { apply (model_ivs_wf_sbm7 _ _ SBM'). rewrite OKh_eq. pose proof (model_ivs_wf_sbm7 _ _ SBM MW) as MWm. pose proof MWm as (Wm & Wn & Wl & Wsp).
        (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). apply model_ivs_wf_with_vmmaps; [exact MWm | | exact Wn | reflexivity].
        (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps] in G in change_no_check G' end). apply ivs_wf_cons; [| exact Wm]. (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite L5, L6. lia. }
      pose proof (same_but_materialized_frame _ _ SBM') as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
      rewrite HL, OKh_eq. change (m_halted (mmap_model addr size mdlm)) with (m_halted mdlm).
      pose proof (same_but_materialized_frame _ _ SBM) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL2 & _). rewrite HL2. exact HH.
    Qed.
  End PostH.
End SlotH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section N3H.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation U := bv_unsigned.

  Definition N3H_body (st : ast) (Lc FF : list (Z * Z)) (mdl : Model) (lo : Z) (LEDGER : Model -> Model -> Prop) : Prop :=
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KUSERMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] in
    let OK := OKh addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm) ++ vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_noreserve_backed_ok (Z_to_bv 64 50) mdlm KUSERMAP = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          LEDGER mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).

  (* [comment removed for export] *)
  Definition N3UH_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_uhole (a_reg st c) = true ->
    BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    N3H_body st Lc FF mdl (region_beg SBEG c + r_mapped_user (a_reg st c)) (usermap_ledger bt st c).
  Definition N3UHq_stmt : Prop := forall st Lc FF M0 mdl c qt qg,
    WFq bt st Lc FF qt qg -> qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_uhole (a_reg st c) = true ->
    BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    N3H_body st Lc FF mdl (region_beg SBEG c + r_mapped_user (a_reg st c)) (usermap_ledger bt st c).
  (* [comment removed for export] *)
  Definition N3FH_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = true ->
    BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    N3H_body st Lc FF mdl (fa_beg SBEG c + r_mapped_fa (a_reg st c)) (famap_ledger bt st c).
  Definition N3FHq_stmt : Prop := forall st Lc FF M0 mdl c qt qg,
    WFq bt st Lc FF qt qg -> qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = true ->
    BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    N3H_body st Lc FF mdl (fa_beg SBEG c + r_mapped_fa (a_reg st c)) (famap_ledger bt st c).

  Hypothesis RL : res_low bt.

  Lemma slotH_pack : forall st Lc FF M0 mdl lo qt qg (LEDGER : Model -> Model -> Prop),
    WFq bt st Lc FF qt qg -> qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    (lo - SBEG) mod KUSERMAP = 0 -> SBEG <= lo -> lo + KUSERMAP <= SBEG + KSPACE ->
    (forall a, lo <= a < lo + KUSERMAP -> holes bt st a) ->
    (forall mdl', Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KUSERMAP) :: vm_maps (m_vmmaps mdl))
      /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KUSERMAP))
      /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
      /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KUSERMAP))
      /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
                (m_vm_lazy mdl')
      /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
      /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
      /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
      eager_used mdl' <= eager_used mdl + KUSERMAP -> LEDGER mdl mdl') ->
    N3H_body st Lc FF mdl lo LEDGER.
  Proof using RL.
    intros st Lc FF M0 mdl lo qt qg LEDGER W HQ R MW HH KC SL1 SL2 SL3 HO HLED. (lazymatch goal with |- ?G => let G' := eval unfold N3H_body in G in change_no_check G' end). cbn zeta.
    split; [exact (A2_wf bt st Lc FF M0 mdl lo qt qg W R SL1 SL2)|]. split; [|split].
    - intros mdlm SBM MI.
      destruct (node_top bt st Lc FF M0 mdl lo qt qg W R MW HH SL2 SL3 mdlm SBM) as [T1 T2].
      destruct (nodeH_OK bt st Lc FF M0 mdl lo qt qg W HQ R MW HH KC SL2 SL3 mdlm SBM MI) as (O1 & O2 & O3).
      split; [exact T1|]. split; [exact T2|].
      split; [exact (nodeH_free bt st Lc FF M0 mdl lo qt qg W R MW HH RL SL2 SL3 HO mdlm SBM)|].
      split; [exact (nodeH_backed bt st Lc FF M0 mdl lo qt qg W HQ R MW HH KC SL2 mdlm SBM MI)|].
      split; [exact O1|]. split; [exact O2 | exact O3].
    - intros mdlm mdl4 SBM SBM4 MI. exact (postH_widen bt st Lc FF M0 mdl lo qt qg W HQ R MW KC SL2 SL3 mdlm mdl4 SBM SBM4 MI).
    - intros mdlm mdl' SBM SBM'.
      destruct (postH_rest bt st Lc FF mdl lo qt qg W MW HH SL2 SL3 mdlm mdl' SBM SBM') as (Q1 & Q2 & Q3 & Q4).
      split; [| split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3 | exact Q4]].
      apply HLED; [exact (postH_ledger bt st Lc FF M0 mdl lo qt qg W R SL2 SL3 HO mdlm mdl' SBM SBM') | exact (postH_eager bt st Lc FF mdl lo qt qg W MW SL2 SL3 mdlm mdl' SBM SBM')].
  Qed.

  Theorem N3UHq_pf : N3UHq_stmt.
  Proof using RL.
    intros st Lc FF M0 mdl c qt qg W HQ R Hc UH MW HH KC.
    pose proof W as ((WR1 & _) & _). pose proof (WR1 c Hc) as (((A0 & A1) & _) & MUK & MUX & _).
    set (lo := region_beg SBEG c + r_mapped_user (a_reg st c)).
    assert (SL1 : (lo - SBEG) mod KUSERMAP = 0) by (exact (user_slot_aligned bt c _ MUK)).
    assert (SL2 : SBEG <= lo) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, region_beg, KREGION in G in change_no_check G' end); lia).
    assert (SL3 : lo + KUSERMAP <= SBEG + KSPACE) by (unfold lo, region_beg, KREGION, KUSERMAP, KSPACE, KREGION_EXHAUST in *; lia).
    assert (HO : forall a, lo <= a < lo + KUSERMAP -> holes bt st a).
    { intros a Ha. exists c. split; [exact Hc|]. left. split; [exact UH | exact Ha]. }
    apply (slotH_pack st Lc FF M0 mdl lo qt qg _ W HQ R MW HH KC SL1 SL2 SL3 HO).
    intros mdl' (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11) EG. (lazymatch goal with |- ?G => let G' := eval unfold usermap_ledger in G in change_no_check G' end). cbn zeta. fold lo.
    split; [intros E; rewrite UH in E; discriminate E|]. split; [intros _; exact G1|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    repeat (split; [assumption|]). exact EG.
  Qed.

  Theorem N3UH_pf : N3UH_stmt.
  Proof using RL. intros st Lc FF M0 mdl c W. exact (N3UHq_pf st Lc FF M0 mdl c (2 ^ 20) (2 ^ 28) W (qroom_WF bt st Lc FF W)). Qed.

  Theorem N3FHq_pf : N3FHq_stmt.
  Proof using RL.
    intros st Lc FF M0 mdl c qt qg W HQ R Hc FH MW HH KC.
    pose proof W as ((WR1 & _) & _). pose proof (WR1 c Hc) as (_ & MUK & MUX & _ & MF0 & MFK & _ & _ & _ & _ & FHR). pose proof (FHR FH) as FR.
    set (lo := fa_beg SBEG c + r_mapped_fa (a_reg st c)).
    assert (SL1 : (lo - SBEG) mod KUSERMAP = 0) by (exact (fa_slot_aligned bt c _ MFK)).
    assert (SL2 : SBEG <= lo) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); lia).
    assert (SL3 : lo + KUSERMAP <= SBEG + KSPACE) by (unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KUSERMAP, KSPACE in *; lia).
    assert (HO : forall a, lo <= a < lo + KUSERMAP -> holes bt st a).
    { intros a Ha. exists c. split; [exact Hc|]. right. split; [exact FH | exact Ha]. }
    apply (slotH_pack st Lc FF M0 mdl lo qt qg _ W HQ R MW HH KC SL1 SL2 SL3 HO).
    intros mdl' (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11) EG. (lazymatch goal with |- ?G => let G' := eval unfold famap_ledger in G in change_no_check G' end). cbn zeta. fold lo.
    split; [intros E; rewrite FH in E; discriminate E|]. split; [intros _; exact G1|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    repeat (split; [assumption|]). exact EG.
  Qed.
  Theorem N3FH_pf : N3FH_stmt.
  Proof using RL. intros st Lc FF M0 mdl c W. exact (N3FHq_pf st Lc FF M0 mdl c (2 ^ 20) (2 ^ 28) W (qroom_WF bt st Lc FF W)). Qed.
End N3H.
End AsKSys7c.
Module AsKSys9b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b AsKSys7c OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 AsKSys9.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section Grant.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (M0 : mem) (mdl : Model).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis R : Rep bt st Lc FF M0 mdl.
  Hypothesis BG : boot_geom bt.
  Variables (a : word) (nZ : Z).
  Hypothesis AL : u a mod 4096 = 0.
  Hypothesis POS : 0 < u a.
  Hypothesis NZ : 0 < nZ.
  Hypothesis NAL : nZ mod 4096 = 0.
  Hypothesis TOP : u a + nZ <= alloc_top (m_vmmaps mdl).
  Hypothesis FREE : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) a (Z_to_bv 64 nZ) = true.

  Lemma g_lits : u a + nZ < 2 ^ 64 /\ u (Z_to_bv 64 nZ) = nZ /\ u a + nZ <= CEIL.
  Proof using TOP NAL NZ POS AL R mdl M0 FF Lc st bt.
    pose proof (alloc_top_lt (m_vmmaps mdl)) as TL. unfold two_pow_64 in TL.
    destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PF & _).
    assert (X : u a + nZ < 2 ^ 64) by lia. split; [exact X|]. split; [rewrite u64_lit; lia|].
    rewrite <- PF. apply page_floor_bound; [apply mod0_add; [lia | exact AL | exact NAL] | exact TOP].
  Qed.

  (* [comment removed for export] *)
  Lemma g_not_maps : forall z, u a <= z < u a + nZ -> ~ in_ivz (vm_maps (m_vmmaps mdl)) z.
  Proof using FREE TOP NAL NZ POS AL R M0 FF Lc st bt RUN.
    intros z Hz (b & m & Hin & Hr). destruct g_lits as (_ & UN & _).
    rewrite RefNodes.region_free_app in FREE. apply andb_prop in FREE as [_ F2].
    pose proof (RefNodes.region_free_In _ a _ b m F2 Hin) as AP. rewrite UN in AP. lia.
  Qed.
  Lemma g_not_maps0 : forall z, u a <= z < u a + nZ -> ~ in_ivz (bt_maps0 bt) z.
  Proof using FREE TOP NAL NZ POS AL R mdl M0 FF Lc st RUN.
    intros z Hz (b & m & Hin & Hr). apply (g_not_maps z Hz). exists b, m. split; [| exact Hr].
    destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & _) & _). apply (Permutation_in _ (Permutation_sym PM)).
    apply in_app_iff. right. apply in_app_iff. left. exact Hin.
  Qed.

  Theorem grant_dyn_ok : dyn_ok IA (u a) (u a + nZ).
  Proof using FREE TOP NAL NZ POS AL BG R mdl M0 FF Lc st.
    destruct g_lits as (L64 & UN & LC). destruct BG as (_ & _ & _ & BC & RH).
    (lazymatch goal with |- ?G => let G' := eval unfold dyn_ok in G in change_no_check G' end). split; [exact POS|]. split; [lia|]. split; [exact LC|]. split.
    - destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & _ & RES & _).
      rewrite RefNodes.region_free_app in FREE. apply andb_prop in FREE as [F1 _]. rewrite RES in F1.
      pose proof (RH a (Z_to_bv 64 nZ) ltac:(rewrite UN; exact NZ) ltac:(rewrite UN; lia) F1) as X. rewrite UN in X. exact X.
    - destruct (Z_le_gt_dec (u a + nZ) AS_LO) as [L|G1]; [left; exact L|]. destruct (Z_le_gt_dec AS_HEAPLO (u a)) as [R'|G2]; [right; exact R'|]. exfalso.
      set (z := Z.max (u a) AS_LO). apply (g_not_maps0 z ltac:((lazymatch goal with |- ?G => let G' := eval unfold z in G in change_no_check G' end); lia)). apply BC. unfold in_band, z, AS_LO, AS_HEAPLO in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma g_apart_of_cov : forall lo hi, lo < hi -> (forall z, lo <= z < hi -> in_ivz (vm_maps (m_vmmaps mdl)) z) -> u a + nZ <= lo \/ hi <= u a.
  Proof using FREE TOP NAL NZ POS AL R M0 FF Lc st bt RUN.
    intros lo hi Hlh COV. destruct (Z_le_gt_dec (u a + nZ) lo) as [L|G1]; [left; exact L|]. destruct (Z_le_gt_dec hi (u a)) as [R'|G2]; [right; exact R'|]. exfalso.
    set (z := Z.max (u a) lo). exact (g_not_maps z ltac:((lazymatch goal with |- ?G => let G' := eval unfold z in G in change_no_check G' end); lia) (COV z ltac:((lazymatch goal with |- ?G => let G' := eval unfold z in G in change_no_check G' end); lia))).
  Qed.

  Variable h : option Z.
  Hypothesis SIZE : (forall z, ~ holes bt st z) \/ (2 ^ 19 < nZ /\ holes_le h st).

  Lemma maps0_in_maps : forall z, in_ivz (bt_maps0 bt) z -> in_ivz (vm_maps (m_vmmaps mdl)) z.
  Proof using R M0 FF Lc st RUN.
    intros z (b & m & Hin & Hr). exists b, m. split; [| exact Hr].
    destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & _) & _). apply (Permutation_in _ (Permutation_sym PM)).
    apply in_app_iff. right. apply in_app_iff. left. exact Hin.
  Qed.
  Lemma resv6_nohole_in_maps : forall z, in_resv6 bt z -> ~ holes bt st z -> in_ivz (vm_maps (m_vmmaps mdl)) z.
  Proof using R M0 FF Lc RUN.
    intros z Hz NHo. destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & _ & _ & FCOV) & _).
    destruct (proj2 (FCOV z Hz) NHo) as (b & m & Hin & Hr). exists b, m. split; [| exact Hr].
    apply (Permutation_in _ (Permutation_sym PM)). apply in_app_iff. left. exact Hin.
  Qed.

  Theorem grant_apart_all : forall lo hi, In (lo, hi) (all_ranges bt st) -> u a + nZ <= lo \/ hi <= u a.
  Proof using SIZE h FREE TOP NAL NZ POS AL BG R W qg qt mdl M0 FF Lc RUN.
    intros lo hi Hin. destruct g_lits as (L64 & UN & LC). destruct BG as (_ & _ & FC & _ & _).
    pose proof W as ((WR1 & _) & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & IN6 & R6a & R6b & _) & _).
    destruct (RNG lo hi Hin) as ((D1 & D2 & D3 & _) & D6 & _). pose proof ceil_rng as CR.
    unfold all_ranges in Hin. apply in_app_iff in Hin as [HF | HD].
    - destruct (Z.eq_dec lo (bt_resv6 bt)) as [E1 | NE1]; [destruct (Z.eq_dec hi (bt_resv6 bt + bt_resv6_len bt)) as [E2 | NE2]|].
      + (* [comment removed for export] *) subst lo hi.
        destruct (Z_le_gt_dec (u a + nZ) (bt_resv6 bt)) as [L|G1]; [left; exact L|]. destruct (Z_le_gt_dec (bt_resv6 bt + bt_resv6_len bt) (u a)) as [R'|G2]; [right; exact R'|]. exfalso.
        set (z0 := Z.max (u a) (bt_resv6 bt)).
        assert (Z0 : u a <= z0 < u a + nZ /\ in_resv6 bt z0) by ((lazymatch goal with |- ?G => let G' := eval unfold in_resv6, z0 in G in change_no_check G' end); lia).
        assert (WIT : exists z, u a <= z < u a + nZ /\ in_resv6 bt z /\ ~ holes bt st z).
        { destruct SIZE as [NO | [BIG HL]]; [exists z0; split; [tauto | split; [tauto | exact (NO z0)]]|].
          destruct h as [n|].
          2:{ exists z0. split; [tauto|]. split; [tauto|]. intros (c & Hc & [[FL _] | [FL _]]); destruct (HL c ltac:(tauto)) as (n0 & E0 & _); discriminate E0. }
          set (c0 := class_of (needed n)).
          destruct (Z_le_gt_dec 1 c0) as [C1|C1]; [destruct (Z_le_gt_dec c0 30) as [C2|C2]|].
          2,3: (exists z0; split; [tauto|]; split; [tauto|]; intros (c & Hc & FLG);
                assert (EC : c = c0) by (destruct (HL c ltac:(destruct FLG as [[FL _] | [FL _]]; [left; exact FL | right; exact FL])) as (n0 & E0 & _ & EC0); injection E0 as <-; exact EC0); lia).
          destruct (WR1 c0 ltac:(lia)) as (((A0 & A1) & _) & _ & MUX & _ & MF0 & _ & _ & MF29 & _).
          set (us := region_beg SBEG c0 + r_mapped_user (a_reg st c0)). set (fs := fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)).
          assert (NHZ : forall z, ~ (us <= z < us + KUSERMAP) -> ~ (fs <= z < fs + KFAMAP) -> ~ holes bt st z).
          { intros z NU NF (c & Hc & FLG).
            assert (EC : c = c0) by (destruct (HL c ltac:(destruct FLG as [[FL _] | [FL _]]; [left; exact FL | right; exact FL])) as (n0 & E0 & _ & EC0); injection E0 as <-; exact EC0).
            subst c. destruct FLG as [[_ X] | [_ X]]; [exact (NU X) | exact (NF X)]. }
          assert (GEO : bt_resv6 bt < us /\ us + KUSERMAP <= fs /\ fs + KFAMAP < bt_resv6 bt + bt_resv6_len bt).
          { unfold us, fs, fa_beg, region_beg, KREGION, KFAOFF, KUSERMAP, KFAMAP, KREGION_EXHAUST, KSPACE, PG in *. lia. }
          destruct GEO as (G3 & G4 & G5). unfold in_resv6, KUSERMAP, KFAMAP in *. destruct Z0 as [Z0a Z0b].
          destruct (Z_lt_ge_dec z0 us) as [P1|P1]; [exists z0; split; [exact Z0a | split; [exact Z0b | apply NHZ; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KFAMAP in G in change_no_check G' end); lia]]|].
          destruct (Z_lt_ge_dec z0 (us + 2 ^ 18)) as [P2|P2].
          { assert (EG : z0 = u a) by (unfold z0 in *; lia).
            destruct (Z_lt_ge_dec (us + 2 ^ 18) fs) as [P3|P3].
            - exists (us + 2 ^ 18). split; [lia|]. split; [lia|]. apply NHZ; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KFAMAP in G in change_no_check G' end); lia.
            - exists (fs + 2 ^ 18). split; [lia|]. split; [lia|]. apply NHZ; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KFAMAP in G in change_no_check G' end); lia. }
          destruct (Z_lt_ge_dec z0 fs) as [P4|P4]; [exists z0; split; [exact Z0a | split; [exact Z0b | apply NHZ; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KFAMAP in G in change_no_check G' end); lia]]|].
          destruct (Z_lt_ge_dec z0 (fs + 2 ^ 18)) as [P5|P5]; [| exists z0; split; [exact Z0a | split; [exact Z0b | apply NHZ; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KFAMAP in G in change_no_check G' end); lia]]].
          assert (EG : z0 = u a) by (unfold z0 in *; lia).
          exists (fs + 2 ^ 18). split; [lia|]. split; [lia|]. apply NHZ; (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP, KFAMAP in G in change_no_check G' end); lia. }
        destruct WIT as (z & Hz1 & Hz2 & Hz3). exact (g_not_maps z Hz1 (resv6_nohole_in_maps z Hz2 Hz3)).
      + apply (g_apart_of_cov lo hi D6). intros z Hz. apply maps0_in_maps. apply (FC lo hi z HF); [intros E; injection E; intros; lia | exact Hz].
      + apply (g_apart_of_cov lo hi D6). intros z Hz. apply maps0_in_maps. apply (FC lo hi z HF); [intros E; injection E; intros; lia | exact Hz].
    - apply (g_apart_of_cov lo hi D6). intros z Hz. exists (Z_to_bv 64 lo), (Z_to_bv 64 (hi - lo)). split; [| rewrite !u64_lit by lia; lia].
      destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & _) & _). apply (Permutation_in _ (Permutation_sym PM)).
      apply in_app_iff. right. apply in_app_iff. right. rewrite dyn_maps_w2. apply (in_map w2 _ _ HD).
  Qed.
End Grant.

(* [comment removed for export] *)
Section Gates.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M0 : mem) (mdl mdlm : Model) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis R : Rep bt st Lc FF M0 mdl.
  Hypothesis BG : boot_geom bt.
  Hypothesis EV : m_vmmaps mdlm = m_vmmaps mdl.
  Variables (hint a : word) (nZ : Z) (h : option Z).
  Hypothesis NZ : 0 < nZ.
  Hypothesis NAL : nZ mod 4096 = 0.
  Hypothesis SIZE : (forall z, ~ holes bt st z) \/ (2 ^ 19 < nZ /\ holes_le h st).

  Theorem grant_ok_facts : grant_ok hint mdlm a nZ = true ->
    dyn_ok (bt_ia bt) (u a) (u a + nZ) /\ u a mod PG = 0 /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> u a + nZ <= lo \/ hi <= u a).
  Proof using SIZE NAL NZ h EV BG R W qg qt mdl M0 FF Lc.
    intros G. apply grant_ok_unpack in G. destruct G as (G1 & G2 & G3 & G4 & _). rewrite EV in G3, G4. unfold page_size in G1.
    split; [eapply grant_dyn_ok; eassumption|]. split; [exact G1|].
    eapply grant_apart_all; eassumption.
  Qed.

End Gates.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PlainChild.
  Variables (mdl mdlk mdl' : Model) (a n : word).
  Hypothesis MW : model_ivs_wf mdl.
  Hypothesis EKV : m_vmmaps mdlk = m_vmmaps mdl.
  Hypothesis EKL : m_vm_lazy mdlk = m_vm_lazy mdl.
  Hypothesis END64 : u a + u n <= 2 ^ 64.

  Lemma plain_child_MInv : forall A, MInv A mdlk -> eager_used mdl + u n + A_bytes A <= vm_limit (m_vmmaps mdl) -> MInv A (mmap_model a n mdlk).
  Proof using END64 EKL EKV MW.
    intros A [N1 N2 N3 N4 N5] BUD. assert (MWk : model_ivs_wf mdlk) by (unfold model_ivs_wf in *; rewrite EKV, EKL; exact MW).
    pose proof (eager_OKh_le a n mdlk MWk END64) as EG. rewrite OKh_eq in EG.
    assert (EE : eager_used mdlk = eager_used mdl) by (apply eager_used_ext; assumption).
    constructor; try assumption. unfold mmap_model at 2. model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end). rewrite EKV. lia.
  Qed.

  Hypothesis SBM' : same_but_materialized (mmap_model a n mdlk) mdl'.

  Lemma plain_child_ledger :
    vm_maps (m_vmmaps mdl') = (a, n) :: vm_maps (m_vmmaps mdl)
    /\ vm_noaccess (m_vmmaps mdl') = vm_noaccess (m_vmmaps mdl) /\ m_vm_lazy mdl' = m_vm_lazy mdl
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + u n
    /\ model_ivs_wf mdl'.
  Proof using SBM' END64 EKL EKV MW mdlk.
    destruct (sbm_vmmaps _ mdl' SBM') as [E1 E2]. rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj.
    (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end). rewrite EKV, EKL.
    do 9 (split; [reflexivity|]).
    assert (MWk : model_ivs_wf mdlk) by (unfold model_ivs_wf in *; rewrite EKV, EKL; exact MW).
    split.
    - rewrite (eager_used_ext mdl' (mmap_model a n mdlk) E1 E2). pose proof (eager_OKh_le a n mdlk MWk END64) as EG. rewrite OKh_eq in EG.
      assert (EE : eager_used mdlk = eager_used mdl) by (apply eager_used_ext; assumption). lia.
    - apply (model_ivs_wf_sbm7 _ _ SBM'). pose proof MWk as (Wm & Wn & Wl & Wsp). (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end).
      apply model_ivs_wf_with_vmmaps; [exact MWk | | exact Wn | reflexivity]. (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps] in G in change_no_check G' end). apply ivs_wf_cons; [| exact Wm]. (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). exact END64.
  Qed.
End PlainChild.

(* [comment removed for export] *)
Section SecBudget.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.


End SecBudget.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NrChild.
  Variables (mdl mdlk mdl' : Model) (a n : word).
  Hypothesis MW : model_ivs_wf mdl.
  Hypothesis EKV : m_vmmaps mdlk = m_vmmaps mdl.
  Hypothesis EKL : m_vm_lazy mdlk = m_vm_lazy mdl.
  Hypothesis AAL : u a mod page_size = 0.
  Hypothesis NAL : u n mod page_size = 0.
  Hypothesis NPOS : 0 < u n.
  Hypothesis END64 : u a + u n <= 2 ^ 64.
  #[local] Notation child := (AsanAcctShape.NoReserve.mmap_model_noreserve a n mdlk).

  Lemma nr_child_eqs : m_vmmaps child = m_vmmaps (mmap_model a n mdl) /\ m_vm_lazy child = (a, n) :: m_vm_lazy mdl /\ m_vm_materialized child = m_vm_materialized mdlk.
  Proof using END64 NPOS NAL AAL EKL EKV.
    (lazymatch goal with |- ?G => let G' := eval unfold AsanAcctShape.NoReserve.mmap_model_noreserve in G in change_no_check G' end). model_proj. rewrite (lazy_interior_aligned a n AAL NAL NPOS END64). (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. rewrite EKV, EKL.
    repeat split; reflexivity.
  Qed.

  Lemma nr_child_wf : model_ivs_wf child.
  Proof using END64 NPOS NAL AAL EKL EKV MW mdl.
    destruct nr_child_eqs as (E1 & E2 & _). pose proof MW as (Wm & Wn & Wl & Wsp). (lazymatch goal with |- ?G => let G' := eval unfold model_ivs_wf in G in change_no_check G' end). rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess] in G in change_no_check G' end).
    assert (IW : iv_wf (a, n)) by ((lazymatch goal with |- ?G => let G' := eval unfold iv_wf, B, S in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); exact END64).
    split; [apply ivs_wf_cons; assumption|]. split; [exact Wn|]. split; [apply ivs_wf_cons; assumption|].
    eapply BackingAlgebra.AsanCeil.init_sp_ok_same; [| exact Wsp]. reflexivity.
  Qed.

  Lemma nr_child_eager : eager_used child <= eager_used mdl.
  Proof using END64 NPOS NAL AAL EKL EKV MW.
    destruct nr_child_eqs as (E1 & E2 & _). rewrite (eager_used_sem _ nr_child_wf), (eager_used_sem _ MW). rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess sum_count] in G in change_no_check G' end).
    assert (Z0 : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps mdl) ++ (a, n) :: m_vm_lazy mdl) x)) (a, n) = 0).
    { (lazymatch goal with |- ?G => let G' := eval unfold iv_count in G in change_no_check G' end). apply zcount_false. intros x Hx. unfold B, S in Hx. cbn [fst snd] in Hx. rewrite Z2Nat.id in Hx by lia.
      rewrite covered_app. unfold covered at 2. (lazymatch goal with |- ?G => let G' := eval cbn [existsb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold in_iv, in_rng, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. (lazymatch goal with |- ?G => let G' := eval cbn [andb orb] in G in change_no_check G' end). rewrite orb_true_r. reflexivity. }
    rewrite Z0. rewrite Z.add_0_l. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
    rewrite covered_app in *. apply orb_false_iff in Hx as [H1 H2]. unfold covered in H2. cbn [existsb] in H2. apply orb_false_iff in H2 as [_ H2].
    apply orb_false_iff. split; [exact H1 | exact H2].
  Qed.

  Lemma nr_child_MInv : forall A, MInv A mdlk -> MInv A child.
  Proof using END64 NPOS NAL AAL EKL EKV MW mdl.
    intros A [N1 N2 N3 N4 N5]. destruct nr_child_eqs as (E1 & E2 & E3).
    assert (EE : eager_used mdlk = eager_used mdl) by (apply eager_used_ext; assumption).
    constructor; rewrite ?E3; try assumption.
    - intros p Hp. rewrite E2. rewrite page_in_ranges_cons. rewrite <- EKL, (N4 p Hp). apply orb_true_r.
    - pose proof nr_child_eager. rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end). rewrite <- EKV. lia.
  Qed.

  Hypothesis SBM' : same_but_materialized child mdl'.

  Lemma nr_child_ledger :
    vm_maps (m_vmmaps mdl') = (a, n) :: vm_maps (m_vmmaps mdl)
    /\ vm_noaccess (m_vmmaps mdl') = vm_noaccess (m_vmmaps mdl) /\ m_vm_lazy mdl' = (a, n) :: m_vm_lazy mdl
    /\ (forall x, pg_in_ivz (m_vm_lazy mdl') x <-> pg_in_ivz (m_vm_lazy mdl) x \/ (0 <= x < 2 ^ 64 /\ u a <= x < u a + u n))
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl /\ model_ivs_wf mdl'.
  Proof using SBM' END64 NPOS NAL AAL EKL EKV MW mdlk.
    destruct (sbm_vmmaps _ mdl' SBM') as [E1 E2]. destruct nr_child_eqs as (C1 & C2 & _). rewrite E1, E2, C1, C2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). model_proj.
    (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { intros x. (lazymatch goal with |- ?G => let G' := eval unfold pg_in_ivz in G in change_no_check G' end). rewrite page_in_ranges_cons. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). unfold page_size in *. split.
      - intros [Rx Hx]. apply orb_true_iff in Hx as [Hx | Hx]; [right | left; split; assumption]. split; [exact Rx|].
        apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        pose proof (page_base_facts (Z_to_bv 64 x)) as (P1 & P2 & P3). rewrite u64_lit in P1, P2 by lia. lia.
      - intros [[Rx Hx] | [Rx Hx]]; (split; [exact Rx|]); apply orb_true_iff; [right; exact Hx | left].
        pose proof (page_of_byte_in_aligned (Z_to_bv 64 x) (u a) (u a + u n) AAL ltac:(apply mod0_add; [lia | exact AAL | exact NAL]) ltac:(rewrite u64_lit by lia; exact Hx)) as [P1 P2].
        apply andb_true_intro. split; apply Z.leb_le; lia. }
    do 6 (split; [reflexivity|]).
    split; [rewrite (eager_used_ext mdl' child E1 E2); exact nr_child_eager | exact (model_ivs_wf_sbm7 _ _ SBM' nr_child_wf)].
  Qed.
End NrChild.
End AsKSys9b.
Module AsDepotTop0.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section G.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Hypothesis W : WF bt st Lc FF.

  Lemma node_blocks_dyn : forall b, In b (node_blocks bt (a_dep st)) ->
    dyn_ok (bt_ia bt) b (b + 2 ^ 20) /\ b mod PG = 0 /\ In (b, b + 2 ^ 20) (all_ranges bt st).
  Proof using W FF Lc.
    intros b Hb. unfold node_blocks in Hb. destruct Hb as [<- | Hb].
    - destruct (nodes0_facts bt st Lc FF W) as [D M]. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & INN & _).
      split; [exact D|]. split; [exact M | exact (all_ranges_fixed bt st _ INN)].
    - pose proof (all_ranges_dyn bt st _ (node_dyn st b Hb)) as IN.
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _). destruct (RNG _ _ IN) as (D & _ & M & _).
      split; [exact D|]. split; [exact M | exact IN].
  Qed.
  Lemma store_blocks_dyn : forall b, In b (store_blocks bt (a_dep st)) ->
    dyn_ok (bt_ia bt) b (b + 2 ^ 23) /\ b mod PG = 0 /\ In (b, b + 2 ^ 23) (all_ranges bt st).
  Proof using W FF Lc.
    intros b Hb. unfold store_blocks in Hb. destruct Hb as [<- | Hb].
    - destruct (store0_facts bt st Lc FF W) as [D M]. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & _ & INS & _).
      split; [exact D|]. split; [exact M | exact (all_ranges_fixed bt st _ INS)].
    - pose proof (all_ranges_dyn bt st _ (store_dyn st b Hb)) as IN.
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _). destruct (RNG _ _ IN) as (D & _ & M & _).
      split; [exact D|]. split; [exact M | exact IN].
  Qed.

  (* [comment removed for export] *)
  Lemma node_vs_store : forall b q, In b (node_blocks bt (a_dep st)) -> In q (store_blocks bt (a_dep st)) -> b + 2 ^ 20 <= q \/ q + 2 ^ 23 <= b.
  Proof using W FF Lc RC.
    intros b q Hb Hq. destruct (node_blocks_dyn b Hb) as (_ & _ & INb). destruct (store_blocks_dyn q Hq) as (_ & _ & INq).
    assert (NE : (b, b + 2 ^ 20) <> (q, q + 2 ^ 23)) by (intros E; injection E; lia).
    pose proof (ar_disj_ne bt st Lc FF _ _ W INb INq NE) as D. hnf in D. cbn in D. lia.
  Qed.

  (* [comment removed for export] *)
  Definition PX (X : Z -> Prop) : Prop :=
    forall a, X a -> CEIL <= a \/ in_band a \/ exists lo hi, In (lo, hi) (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                                        /\ lo <= a < hi /\ lo <> bt_nodes0 bt /\ lo <> bt_store0 bt.

  Lemma px_tracked : forall X a, PX X -> X a -> a < CEIL -> ~ in_band a -> exists lo hi, In (lo, hi) (all_ranges bt st) /\ lo <= a < hi.
  Proof using.
    intros X a P Xa Ha NB. destruct (P a Xa) as [C | [C | (lo & hi & IN & R & _)]]; [lia | exact (False_ind _ (NB C)) |]. exists lo, hi. split; [| exact R].
    (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). apply in_app_iff in IN as [IN | IN]; apply in_app_iff; [left; exact IN | right; apply in_app_iff; left; exact IN].
  Qed.

  Lemma px_off_nodes : forall X a b, PX X -> X a -> In b (node_blocks bt (a_dep st)) -> ~ (b <= a < b + 2 ^ 20).
  Proof using W FF Lc.
    intros X a b P Xa Hb R. destruct (node_blocks_dyn b Hb) as ((_ & _ & DC & _ & DB) & _ & INb).
    destruct (P a Xa) as [C | [C | (lo & hi & IN & R' & N1 & _)]]; [lia | unfold in_band in C; lia |].
    unfold node_blocks in Hb. destruct Hb as [<- | Hb].
    - assert (INl : In (lo, hi) (all_ranges bt st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). apply in_app_iff in IN as [IN | IN]; apply in_app_iff; [left; exact IN | right; apply in_app_iff; left; exact IN]. }
      assert (NE : (lo, hi) <> (bt_nodes0 bt, bt_nodes0 bt + 2 ^ 20)) by (intros E; injection E; intros; contradiction).
      pose proof (ar_disj_ne bt st Lc FF _ _ W INl INb NE) as D. hnf in D. cbn in D. lia.
    - pose proof (ar_disj_app bt st Lc FF W (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                    (List.map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)))
                    (lo, hi) (b, b + 2 ^ 20)) as D.
      specialize (D ltac:((lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end); rewrite <- app_assoc; reflexivity) IN ltac:(apply in_app_iff; left; apply in_map_iff; exists b; split; [reflexivity | exact Hb])).
      hnf in D. cbn in D. lia.
  Qed.
  Lemma px_off_stores : forall X a q, PX X -> X a -> In q (store_blocks bt (a_dep st)) -> ~ (q <= a < q + 2 ^ 23).
  Proof using W FF Lc.
    intros X a q P Xa Hq R. destruct (store_blocks_dyn q Hq) as ((_ & _ & DC & _ & DB) & _ & INq).
    destruct (P a Xa) as [C | [C | (lo & hi & IN & R' & _ & N2)]]; [lia | unfold in_band in C; lia |].
    unfold store_blocks in Hq. destruct Hq as [<- | Hq].
    - assert (INl : In (lo, hi) (all_ranges bt st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). apply in_app_iff in IN as [IN | IN]; apply in_app_iff; [left; exact IN | right; apply in_app_iff; left; exact IN]. }
      assert (NE : (lo, hi) <> (bt_store0 bt, bt_store0 bt + 2 ^ 23)) by (intros E; injection E; intros; contradiction).
      pose proof (ar_disj_ne bt st Lc FF _ _ W INl INq NE) as D. hnf in D. cbn in D. lia.
    - pose proof (ar_disj_app bt st Lc FF W (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                    (List.map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)))
                    (lo, hi) (q, q + 2 ^ 23)) as D.
      specialize (D ltac:((lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end); rewrite <- app_assoc; reflexivity) IN ltac:(apply in_app_iff; right; apply in_map_iff; exists q; split; [reflexivity | exact Hq])).
      hnf in D. cbn in D. lia.
  Qed.
End G.
End AsDepotTop0.
Module AsDepotBud.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b AsKSys9 AsKSys9b AsDepotTop0.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DepotBud.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  Theorem depot_n1_budget : forall st Lc FF M0 mdl (qt qg : Z),
    Rep bt st Lc FF M0 mdl -> WFq bt st Lc FF qt qg -> qt + qg <= 2 ^ 28 + 2 ^ 21 -> a_kact st <= KCAP ->
    dp_nids (a_dep st) + 1 < 2 ^ 31 - 1 ->
    eager_used mdl + 2 ^ 20 + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl).
  Proof using.
    intros st Lc FF M0 mdl qt qg R W HQ KC NID1.
    (* [comment removed for export] *)
    pose proof (budget_room bt st Lc FF qt qg W HQ KC) as BR.
    destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LIM & _).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & BUD & _) & _).
    unfold ROOMSLACK in BR. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma grant_not_lazy : forall st Lc FF M mdl a n,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> dyn_ok (bt_ia bt) a (a + n) ->
    (forall lo hi, In (lo, hi) (all_ranges bt st) -> a + n <= lo \/ hi <= a) ->
    forall z, a <= z < a + n -> lzb mdl z = false.
  Proof using.
    intros st Lc FF M mdl a n W R (A1 & A2 & A3 & A4 & A5) AP z Hz. destruct (lzb mdl z) eqn:E; [| reflexivity]. exfalso.
    destruct (fixed_members bt st Lc FF W) as (IN6 & IN8 & _ & _ & _ & INS & _).
    destruct (rep_lazy_cases bt st Lc FF M mdl W R z ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); lia) E) as [([Z6 | [Z8 | ZS]] & _) | (b' & Hb' & Zb)].
    - destruct (AP _ _ (all_ranges_fixed bt st _ IN6)); lia.
    - destruct (AP _ _ (all_ranges_fixed bt st _ IN8)); lia.
    - destruct (AP _ _ (all_ranges_fixed bt st _ INS)); lia.
    - destruct (AP _ _ (all_ranges_dyn bt st _ (store_dyn st b' Hb'))); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma grant_apart_maps0 : forall st Lc FF M0 mdl mdlm (qt qg : Z) (hint a : word) nZ,
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M0 mdl -> m_vmmaps mdlm = m_vmmaps mdl -> 0 < nZ -> nZ mod 4096 = 0 ->
    grant_ok hint mdlm a nZ = true ->
    forall b0 n0, In (b0, n0) (bt_maps0 bt) -> bv_unsigned a + nZ <= bv_unsigned b0 \/ bv_unsigned b0 + bv_unsigned n0 <= bv_unsigned a.
  Proof using.
    intros st Lc FF M0 mdl mdlm qt qg hint a nZ W R EV NZ NAL G b0 n0 Hin.
    apply grant_ok_unpack in G. destruct G as (G1 & G2 & G3 & G4 & _). rewrite EV in G3, G4. unfold page_size in G1.
    destruct (g_lits bt st Lc FF M0 mdl R a nZ G1 G2 NZ NAL G3) as (_ & UN & _).
    rewrite RefNodes.region_free_app in G4. apply andb_prop in G4 as [_ F2].
    assert (Hin' : In (b0, n0) (vm_maps (m_vmmaps mdl))).
    { destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & _) & _). apply (Permutation.Permutation_in _ (Permutation.Permutation_sym PM)).
      apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    pose proof (RefNodes.region_free_In _ a _ b0 n0 F2 Hin') as AP. rewrite UN in AP. exact AP.
  Qed.
End DepotBud.

(* [comment removed for export] *)
Lemma sev_mmap_model : forall (a n : word) (m : Model), same_except_vm m (mmap_model a n m).
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma px_off_fresh : forall {RUN : run_ceil} bt st Lc FF (X : Z -> Prop) p n z, WF bt st Lc FF -> AsDepotTop0.PX bt st X -> X z ->
  (forall lo hi, In (lo, hi) (all_ranges bt st) -> p + n <= lo \/ hi <= p) -> dyn_ok (bt_ia bt) p (p + n) -> ~ (p <= z < p + n).
Proof.
  intros RUN bt st Lc FF X p n z W P Xz AP (_ & _ & HC & _ & HB) Hz.
  destruct (AsDepotTop0.px_tracked bt st X z P Xz ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); lia)) as (lo & hi & IN & R). destruct (AP lo hi IN); lia.
Qed.
End AsDepotBud.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys11.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.PlacementSearch OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b AsKSys9 AsAinvBootF3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.


(* [comment removed for export] *)
Definition NZEX : Z := 16 * 10 ^ 9.
Definition KEV : Z := KCAP / EVT.
Definition NODEMAX : Z := (2 ^ 20 + KEV) / 2 ^ 16.                   (* [comment removed for export] *)
Definition STOREMAX : Z := (2 ^ 20 + 9 * KEV) / (2 ^ 20 - 9).        (* [comment removed for export] *)
Definition QSECCNT : Z := (2 ^ 28 + 2 ^ 21) / 64513.                 (* [comment removed for export] *)
Definition XCNT : Z := 8.                                            (* [comment removed for export] *)
Definition XSZ : Z := 2 ^ 36.
Definition BOOTCNT : Z := 32.
Definition BOOTSZ : Z := 17730000000000.
Definition CNTMAX : Z := XCNT + BOOTCNT + 1 + LMAX + QSECCNT + NODEMAX + STOREMAX.
Definition SZMAX : Z := XSZ + BOOTSZ + (GBUDGET + 2 ^ 29) + 2 ^ 20 * NODEMAX + 2 ^ 23 * STOREMAX.
Lemma room_num : 4096 + NZEX + SZMAX + CNTMAX * (NZEX + 4095) <= alloc_ceiling.
Proof. vm_compute. intros H. discriminate H. Qed.

(* [comment removed for export] *)
Definition boot_totals (bt : as_boot) : Prop :=
  Z.of_nat (length (bt_reserved bt ++ bt_maps0 bt)) <= BOOTCNT
  /\ gw_sizes (bt_reserved bt ++ bt_maps0 bt) + bt_resv6_len bt <= BOOTSZ.

Lemma gw_sizes_app : forall l1 l2, gw_sizes (l1 ++ l2) = gw_sizes l1 + gw_sizes l2.
Proof. induction l1 as [|x t IH]; intros l2; (lazymatch goal with |- ?G => let G' := eval cbn [app gw_sizes] in G in change_no_check G' end); [reflexivity | rewrite IH; lia]. Qed.

Lemma gw_sizes_map_le : forall {A} (f : A -> word * word) (w : A -> Z) l, (forall x, In x l -> u (snd (f x)) <= w x) -> gw_sizes (map f l) <= wsum w l.
Proof.
  intros A f w l H. induction l as [|x t IH]; (lazymatch goal with |- ?G => let G' := eval cbn [map gw_sizes wsum fold_right] in G in change_no_check G' end); [lia|].
  pose proof (H x (or_introl eq_refl)). specialize (IH (fun y Hy => H y (or_intror Hy))). unfold wsum in IH. lia.
Qed.
Lemma u_le_self : forall x, 0 <= x -> u (Z_to_bv 64 x) <= x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). apply Z.mod_le; [exact Hx | reflexivity]. Qed.

Lemma region_free_cover : forall (L L' : list (word * word)) (a n : word),
  (forall b s, In (b, s) L -> exists b' s', In (b', s') L' /\ u b' <= u b /\ u b + u s <= u b' + u s') ->
  region_free L' a n = true -> region_free L a n = true.
Proof.
  intros L L' a n COV RF. apply RefNodes.region_free_intro. intros b s Hin. destruct (COV b s Hin) as (b' & s' & Hin' & C1 & C2).
  destruct (RefNodes.region_free_In L' a n b' s' RF Hin'); lia.
Qed.

(* [comment removed for export] *)
Section GapF.
  Variable fl : Z.
  Hypothesis FLp : fl mod page_size = 0.
  Hypothesis FL0 : 0 <= fl.
  Variable L : list (word * word).
  Variable nZ : Z.
  Hypothesis HnZ : 0 <= nZ.

  Definition scan_inv_f (c : Z) : Prop :=
    c mod page_size = 0 /\ fl <= c /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= alloc_ceiling.
  Definition gap_at_f (c : Z) : Prop :=
    c mod page_size = 0 /\ fl <= c /\ c + nZ <= alloc_ceiling /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  Lemma scan_step_f : forall c, scan_inv_f c ->
    gap_at_f c \/ exists c', scan_inv_f c' /\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
  Proof using HnZ FL0.
    intros c (Hal & Hfl & Hw).
    pose proof fg_alloc_ceiling_val as Hcv.
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (page_round_up_Z_ge (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095).
      { (lazymatch goal with |- ?G => let G' := eval unfold c', page_round_up_Z, page_size in G in change_no_check G' end).
        pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
      assert (Hlive : live_at c (b, s) = true) by ((lazymatch goal with |- ?G => let G' := eval unfold live_at in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by ((lazymatch goal with |- ?G => let G' := eval unfold live_at in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply page_round_up_Z_aligned|].
      split; lia.
  Qed.

  Lemma scan_f : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv_f c -> exists g, gap_at_f g.
  Proof using HnZ FL0.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_step_f c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia]. exists c. exact Hok.
    - destruct (scan_step_f c Hinv) as [Hok|(c' & Hinv' & Hlt)]; [exists c; exact Hok | apply (IH c'); [lia | exact Hinv']].
  Qed.

  Theorem free_gap_from : fl + nZ + gw_sizes L + Z.of_nat (length L) * (nZ + 4095) <= alloc_ceiling -> exists g, gap_at_f g.
  Proof using HnZ FL0 FLp.
    intros Hslack. rewrite <- Z.add_assoc, <- gap_weight_sizes in Hslack.
    assert (Hinv : scan_inv_f fl).
    { split; [exact FLp|]. split; [lia|]. pose proof (gap_weight_filter_le nZ (live_at fl) L HnZ). lia. }
    exact (scan_f _ fl (le_n _) Hinv).
  Qed.
End GapF.

(* [comment removed for export] *)
Lemma sec_weight_count : forall (P : schunk -> Prop) (cw : Z * Z -> Z) (f : schunk -> Z * Z) l,
  (forall s, In s l -> cw (f s) = 64513) -> 64513 * Z.of_nat (length l) = wsum cw (map f l).
Proof.
  intros _ cw f l H. induction l as [|s t IH]; [reflexivity|].
  (lazymatch goal with |- ?G => let G' := eval cbn [map length wsum fold_right] in G in change_no_check G' end). fold (wsum cw (map f t)). rewrite <- (IH (fun x Hx => H x (or_intror Hx))), (H s (or_introl eq_refl)), Nat2Z.inj_succ. lia.
Qed.

Section Counts.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.

  (* [comment removed for export] *)
  Lemma sec_count_le : 64513 * (Z.of_nat (length (a_sec st)) - Z.of_nat (length Lc)) <= qt + qg.
  Proof using W FF bt RUN.
    pose proof W as (_ & _ & (WB1 & WB2 & QT & QG & _ & _) & (_ & _ & _ & SR & SND & SLQ & _ & _) & (WL & _) & _).
    set (f := fun s : schunk => (sc_user s, sc_n s)).
    set (g := fun mn : Z * Z => (fst mn + 16, snd mn)).
    assert (ND : List.NoDup (map f (a_sec st))).
    { apply (NoDup_map_of f sc_map _ SND). intros x y Hx Hy E. unfold f, sc_user in E. injection E as E1 E2. rewrite E2 in E1. lia. }
    assert (INC : incl (map f (a_sec st)) (Lc ++ map g (quar st))).
    { intros y Hy. apply in_map_iff in Hy as (s & <- & Hs). apply in_app_iff.
      destruct (in_dec ZZ_eq_dec (f s) Lc) as [L|NL]; [left; exact L | right].
      destruct (in_dec ZZ_eq_dec (sc_user s - 16, sc_n s) (quar st)) as [Q|NQ].
      - apply in_map_iff. exists (sc_user s - 16, sc_n s). (lazymatch goal with |- ?G => let G' := eval unfold g, f in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). split; [f_equal; lia | exact Q].
      - exfalso. apply NL. apply (proj2 (SLQ s Hs)). exact NQ. }
    (* [comment removed for export] *)
    set (cw := fun pn : Z * Z => if is_primary (snd pn) then 0 else 64513).
    assert (S1 : 64513 * Z.of_nat (length (a_sec st)) = wsum cw (map f (a_sec st))).
    { apply (sec_weight_count (fun _ => True)). intros s Hs. (lazymatch goal with |- ?G => let G' := eval unfold cw, f in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end).
      destruct (SR s Hs) as [Hn _]. rewrite (not_primary_big (sc_n s) ltac:(lia)). reflexivity. }
    assert (S2 : wsum cw (map f (a_sec st)) <= wsum cw (Lc ++ map g (quar st))).
    { apply wsum_incl_le; [exact ND | exact INC | intros y; (lazymatch goal with |- ?G => let G' := eval unfold cw in G in change_no_check G' end); destruct (is_primary (snd y)); lia]. }
    rewrite wsum_app in S2.
    assert (S3 : wsum cw Lc <= 64513 * Z.of_nat (length Lc)).
    { rewrite <- (wsum_const 64513 Lc). apply wsum_le. intros x _. (lazymatch goal with |- ?G => let G' := eval unfold cw in G in change_no_check G' end). destruct (is_primary (snd x)); lia. }
    assert (S4 : wsum cw (map g (quar st)) <= wsum (fun it : Z * Z => snd it) (quar st)).
    { rewrite wsum_map. apply wsum_le. intros [m n] Hq. (lazymatch goal with |- ?G => let G' := eval unfold cw, g in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _).
      destruct (is_primary n) eqn:HP; [lia|].
      destruct (quar_sec bt st Lc FF W m n Hq HP) as (sc & Hsc & _ & En). destruct (SR sc Hsc) as [Hn _]. lia. }
    assert (S5 : wsum (fun it : Z * Z => snd it) (quar st) <= qt + qg).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). pose proof (items_sum_q (a_tq st ++ a_gq st)) as IQ. rewrite q_bytes_app in IQ. unfold BATCHSZ in IQ. lia. }
    lia.
  Qed.

  Hypothesis HQ : qt + qg <= 2 ^ 28 + 2 ^ 21.
  Hypothesis QR : qroom Lc qt qg.
  Hypothesis KC : a_kact st <= KCAP.
  Hypothesis BOK : boot_ok bt.

  Lemma sec_len_le : Z.of_nat (length (a_sec st)) <= LMAX + QSECCNT.
  Proof using HQ W qg qt FF Lc bt RUN.
    pose proof sec_count_le as SC.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & LL & _) & _).
    assert (X : Z.of_nat (length (a_sec st)) - Z.of_nat (length Lc) <= QSECCNT).
    { (lazymatch goal with |- ?G => let G' := eval unfold QSECCNT in G in change_no_check G' end). apply Z.div_le_lower_bound; [lia|]. lia. }
    lia.
  Qed.
End Counts.

(* [comment removed for export] *)
Section Exists.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z) (M : mem) (mdl : Model).
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis HQ : qt + qg <= 2 ^ 28 + 2 ^ 21.
  Hypothesis QR : qroom Lc qt qg.
  Hypothesis R : Rep bt st Lc FF M mdl.
  Hypothesis KC : a_kact st <= KCAP.
  Hypothesis BOK : boot_ok bt.
  Hypothesis BT : boot_totals bt.

  Lemma kev_le : a_kact st / EVT <= KEV.
  Proof using KC. (lazymatch goal with |- ?G => let G' := eval unfold KEV in G in change_no_check G' end). apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | exact KC]. Qed.
  Lemma kev_nonneg : 0 <= KEV.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold KEV in G in change_no_check G' end). apply Z.div_pos; [(lazymatch goal with |- ?G => let G' := eval unfold KCAP in G in change_no_check G' end) | (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end)]; lia. Qed.

  Lemma node_len_le : Z.of_nat (length (dp_nodeblocks (a_dep st))) <= NODEMAX.
  Proof using BOK KC W qg qt FF Lc bt RUN.
    pose proof W as (_ & _ & _ & _ & _ & _ & (_ & NID & _ & _ & _ & NB & _) & _).
    destruct (dep0_bounds bt BOK) as (D1 & _). pose proof kev_le as KE.
    rewrite NB. (lazymatch goal with |- ?G => let G' := eval unfold NODEMAX in G in change_no_check G' end). apply Z.div_le_mono; lia.
  Qed.
  Lemma store_len_le : Z.of_nat (length (dp_storeblocks (a_dep st))) <= STOREMAX.
  Proof using BOK KC W qg qt FF Lc bt RUN.
    pose proof W as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & F0 & _ & FR & SBL & _) & _).
    destruct (dep0_bounds bt BOK) as (_ & _ & D2). pose proof kev_le as KE. pose proof kev_nonneg as K0.
    set (B := Z.of_nat (length (dp_storeblocks (a_dep st)))) in *. set (fr := dp_frames (a_dep st)) in *.
    (lazymatch goal with |- ?G => let G' := eval unfold STOREMAX in G in change_no_check G' end). apply Z.div_le_lower_bound; [lia|].
    assert (B0 : 0 <= B) by ((lazymatch goal with |- ?G => let G' := eval unfold B in G in change_no_check G' end); lia).
    destruct (Z.le_gt_cases ((fr - 1) / 2 ^ 20) 0) as [LE | GT].
    - assert (B = 0) by lia. lia.
    - assert (BQ : B <= (fr - 1) / 2 ^ 20) by lia.
      pose proof (Z.mul_div_le (fr - 1) (2 ^ 20) ltac:(lia)) as MD. unfold FRW in FR. clear SBL. lia.
  Qed.

  Lemma dyn_len_le : Z.of_nat (length (dyn_maps st)) <= LMAX + QSECCNT + NODEMAX + STOREMAX.
  Proof using BOK KC HQ W qg qt FF Lc bt RUN.
    (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). rewrite !length_app, !length_map, !Nat2Z.inj_add.
    pose proof (sec_len_le bt st Lc FF qt qg W HQ). pose proof node_len_le. pose proof store_len_le. lia.
  Qed.

  Lemma dyn_sizes_le : gw_sizes (dyn_maps st) <= (GBUDGET + 2 ^ 29) + 2 ^ 20 * NODEMAX + 2 ^ 23 * STOREMAX.
  Proof using BOK KC QR HQ W qg qt FF Lc bt RUN.
    (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). rewrite !gw_sizes_app.
    assert (S1 : gw_sizes (map (fun s => (Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s))) (a_sec st)) <= sec_maps st).   (* [comment removed for export] *)
    { (lazymatch goal with |- ?G => let G' := eval unfold sec_maps in G in change_no_check G' end). apply gw_sizes_map_le. intros s Hs. (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). apply u_le_self.
      pose proof W as (_ & _ & _ & (_ & _ & _ & SR & _) & _). destruct (SR s Hs) as [Hn _].
      (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). destruct (sec_map_size_ge (sc_n s) ltac:(lia)) as (G1 & _). pose proof (rz_range (sc_n s)). unfold PG in G1. lia. }
    assert (S2 : gw_sizes (map (fun b => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 20))) (dp_nodeblocks (a_dep st))) <= 2 ^ 20 * Z.of_nat (length (dp_nodeblocks (a_dep st)))).
    { rewrite <- wsum_const. apply gw_sizes_map_le. intros b _. (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). apply u_le_self. lia. }
    assert (S3 : gw_sizes (map (fun b => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 23))) (dp_storeblocks (a_dep st))) <= 2 ^ 23 * Z.of_nat (length (dp_storeblocks (a_dep st)))).
    { rewrite <- wsum_const. apply gw_sizes_map_le. intros b _. (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). apply u_le_self. lia. }
    pose proof (sec_maps_le5 bt st Lc FF qt qg W) as SC. unfold qroom in QR.
    pose proof node_len_le. pose proof store_len_le. unfold GBUDGET in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition hull6 : word * word := (Z_to_bv 64 (bt_resv6 bt), Z_to_bv 64 (bt_resv6_len bt)).
  Definition coarse (extra : list (word * word)) : list (word * word) := extra ++ bt_reserved bt ++ hull6 :: bt_maps0 bt ++ dyn_maps st.

  Lemma hull6_u : u (fst hull6) = bt_resv6 bt /\ u (snd hull6) = bt_resv6_len bt.
  Proof using W qg qt FF Lc st RUN.
    destruct (space_facts bt st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & _). pose proof ceil_rng as CR.
    (lazymatch goal with |- ?G => let G' := eval unfold hull6 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite !u64_lit by lia. split; reflexivity.
  Qed.

  Lemma coarse_cover : forall extra hm, vm_reserved hm = vm_reserved (m_vmmaps mdl) -> incl (vm_maps hm) (extra ++ vm_maps (m_vmmaps mdl)) ->
    forall b s, In (b, s) (vm_reserved hm ++ vm_maps hm) ->
      exists b' s', In (b', s') (coarse extra) /\ u b' <= u b /\ u b + u s <= u b' + u s'.
  Proof using R W M qg qt FF Lc RUN.
    intros extra hm ER INC b s Hin.
    assert (LR : rep_ledger bt st mdl) by (destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _); exact R13).
    destruct LR as ((F6 & PM & FO & _ & _) & _ & _ & _ & RES & _).
    assert (SELF : In (b, s) (coarse extra) -> exists b' s', In (b', s') (coarse extra) /\ u b' <= u b /\ u b + u s <= u b' + u s')
      by (intros H; exists b, s; split; [exact H | lia]).
    unfold coarse in *. apply in_app_iff in Hin as [Hr | Hm].
    - apply SELF. apply in_app_iff. right. apply in_app_iff. left. rewrite <- RES, <- ER. exact Hr.
    - apply INC in Hm. apply in_app_iff in Hm as [Hx | Hm]; [apply SELF; apply in_app_iff; left; exact Hx|].
      apply (Permutation_in _ PM) in Hm. apply in_app_iff in Hm as [H6 | Hm].
      + rewrite Forall_forall in FO. destruct (FO _ H6) as (F1 & F2 & F3 & _). cbn [fst snd] in F1, F2, F3.
        destruct hull6_u as (U1 & U2). exists (fst hull6), (snd hull6). split.
        * apply in_app_iff. right. apply in_app_iff. right. left. destruct hull6; reflexivity.
        * rewrite U1, U2. lia.
      + apply SELF. apply in_app_iff. right. apply in_app_iff. right. right. exact Hm.
  Qed.

  Lemma coarse_totals : forall extra, Z.of_nat (length extra) <= XCNT -> gw_sizes extra <= XSZ ->
    Z.of_nat (length (coarse extra)) <= CNTMAX /\ gw_sizes (coarse extra) <= SZMAX.
  Proof using BT BOK KC QR HQ W qg qt FF Lc RUN.
    intros extra XL XS. destruct BT as (B1 & B2). pose proof dyn_len_le as DL. pose proof dyn_sizes_le as DS.
    destruct hull6_u as (_ & U2).
    (lazymatch goal with |- ?G => let G' := eval unfold coarse in G in change_no_check G' end). rewrite !length_app, !gw_sizes_app. (lazymatch goal with |- ?G => let G' := eval cbn [length gw_sizes] in G in change_no_check G' end). rewrite !length_app, !gw_sizes_app, U2.
    rewrite length_app, gw_sizes_app in *. (lazymatch goal with |- ?G => let G' := eval unfold CNTMAX, SZMAX in G in change_no_check G' end). split; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem grant_window : forall extra hm nZ,
    vm_reserved hm = vm_reserved (m_vmmaps mdl) -> incl (vm_maps hm) (extra ++ vm_maps (m_vmmaps mdl)) ->
    Z.of_nat (length extra) <= XCNT -> gw_sizes extra <= XSZ -> 0 <= nZ <= NZEX ->
    exists g, g mod page_size = 0 /\ 4096 <= g /\ g + nZ <= alloc_ceiling
              /\ region_free (vm_reserved hm ++ vm_maps hm) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof using BT BOK KC R QR HQ W M qg qt FF Lc st bt RUN.
    intros extra hm nZ ER INC XL XS HN.
    destruct (coarse_totals extra XL XS) as (CL & CS). pose proof room_num as RN.
    destruct (free_gap_from 4096 eq_refl ltac:(lia) (coarse extra) nZ ltac:(lia)) as (g & G1 & G2 & G3 & G4).
    { assert (P : Z.of_nat (length (coarse extra)) * (nZ + 4095) <= CNTMAX * (NZEX + 4095)) by (apply Z.mul_le_mono_nonneg; lia).
      clear - P CS RN HN. lia. }
    exists g. repeat (split; [assumption|]).
    exact (region_free_cover _ _ _ _ (coarse_cover extra hm ER INC) G4).
  Qed.

  Lemma ceiling_top : alloc_ceiling <= alloc_top (m_vmmaps mdl).
  Proof using R M FF Lc st bt RUN.
    assert (LR : rep_ledger bt st mdl) by (destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _); exact R13).
    destruct LR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    pose proof (page_floor_le (alloc_top (m_vmmaps mdl))). pose proof ceil_rng. rewrite fg_alloc_ceiling_val. lia.
  Qed.

  Theorem grant_nr_exists_x : forall extra hint mdlm nZ,
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> incl (vm_maps (m_vmmaps mdlm)) (extra ++ vm_maps (m_vmmaps mdl)) ->
    alloc_top (m_vmmaps mdlm) = alloc_top (m_vmmaps mdl) ->
    Z.of_nat (length extra) <= XCNT -> gw_sizes extra <= XSZ -> 0 <= nZ <= NZEX ->
    exists a, AsanAcctShape.NoReserve.grant_ok_nr hint mdlm a nZ = true.
  Proof using BT BOK KC R QR HQ W M qg qt FF Lc st bt RUN.
    intros extra hint mdlm nZ ER INC ET XL XS HN.
    destruct (grant_window extra (m_vmmaps mdlm) nZ ER INC XL XS HN) as (g & G1 & G2 & G3 & G4).
    pose proof ceiling_top as CT. pose proof fg_alloc_ceiling_val as CV.
    exists (Z_to_bv 64 g). (lazymatch goal with |- ?G => let G' := eval unfold AsanAcctShape.NoReserve.grant_ok_nr in G in change_no_check G' end). rewrite u64_lit by lia. rewrite G4, ET.
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt 0 g)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.
  Theorem grant_exists_x : forall extra hint mdlm nZ,
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> incl (vm_maps (m_vmmaps mdlm)) (extra ++ vm_maps (m_vmmaps mdl)) ->
    alloc_top (m_vmmaps mdlm) = alloc_top (m_vmmaps mdl) ->
    Z.of_nat (length extra) <= XCNT -> gw_sizes extra <= XSZ -> 0 <= nZ <= NZEX ->
    vm_backing_used mdlm + nZ <= vm_limit (m_vmmaps mdlm) ->
    exists a, MmapSim.grant_ok hint mdlm a nZ = true.
  Proof using BT BOK KC R QR HQ W M qg qt FF Lc st bt RUN.
    intros extra hint mdlm nZ ER INC ET XL XS HN BUD.
    destruct (grant_window extra (m_vmmaps mdlm) nZ ER INC XL XS HN) as (g & G1 & G2 & G3 & G4).
    pose proof ceiling_top as CT. pose proof fg_alloc_ceiling_val as CV.
    exists (Z_to_bv 64 g). (lazymatch goal with |- ?G => let G' := eval unfold MmapSim.grant_ok in G in change_no_check G' end). rewrite u64_lit by lia. rewrite G4, ET.
    rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt 0 g)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    rewrite (proj2 (Z.leb_le _ _) BUD). reflexivity.
  Qed.

  Theorem grant_exists : forall hint mdlm nZ, m_vmmaps mdlm = m_vmmaps mdl -> 0 <= nZ <= NZEX ->
    vm_backing_used mdlm + nZ <= vm_limit (m_vmmaps mdlm) ->
    exists a, MmapSim.grant_ok hint mdlm a nZ = true.
  Proof using BT BOK KC R QR HQ W M qg qt FF Lc st bt RUN.
    intros hint mdlm nZ E HN BUD. apply (grant_exists_x [] hint mdlm nZ); try (rewrite E; reflexivity); try exact HN; try exact BUD.
    - rewrite E. intros x Hx. exact Hx.
    - (lazymatch goal with |- ?G => let G' := eval unfold XCNT in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold XSZ in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [gw_sizes] in G in change_no_check G' end). lia.
  Qed.
End Exists.

(* [comment removed for export] *)
Lemma sec_map_size_NZEX : forall n, 64513 <= n <= GBUDGET -> 0 <= sec_map_size n <= NZEX.
Proof.
  intros n Hn. pose proof (sec_map_size_le n ltac:(lia)). destruct (sec_map_size_ge n ltac:(lia)) as (G1 & _). pose proof (rz_range n).
  unfold NZEX, GBUDGET, PG in *. lia.
Qed.
End AsKSys11.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 AsAinvBootF3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

Section Slot8.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation P8 := (bt_ptrarr bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (M0 : mem) (mdl mdl1 : Model) (mpw szw : word) (A : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis R : Rep bt st Lc FF M0 mdl.
  Hypothesis MW : model_ivs_wf mdl.
  (* [comment removed for export] *)
  Hypothesis PE : ptr8_entry bt.
  Hypothesis PS : ptr8_sep bt.
  Hypothesis RH : res_in_hull bt.
  (* [comment removed for export] *)
  Hypothesis GROW : a_nres st + 2 ^ 14 <= 2 ^ 20.
  (* [comment removed for export] *)
  Hypothesis EV1 : vm_maps (m_vmmaps mdl1) = (mpw, szw) :: vm_maps (m_vmmaps mdl).
  Hypothesis EN1 : vm_noaccess (m_vmmaps mdl1) = vm_noaccess (m_vmmaps mdl).
  Hypothesis EL1 : m_vm_lazy mdl1 = m_vm_lazy mdl.
  Hypothesis ER1 : vm_reserved (m_vmmaps mdl1) = vm_reserved (m_vmmaps mdl).
  Hypothesis EI1 : vm_init_sp (m_vmmaps mdl1) = vm_init_sp (m_vmmaps mdl).
  Hypothesis EB1 : vm_brk (m_vmmaps mdl1) = vm_brk (m_vmmaps mdl).
  Hypothesis ES1 : vm_start_brk (m_vmmaps mdl1) = vm_start_brk (m_vmmaps mdl).
  Hypothesis EMB1 : vm_mmap_base (m_vmmaps mdl1) = vm_mmap_base (m_vmmaps mdl).
  Hypothesis EM1 : vm_limit (m_vmmaps mdl1) = vm_limit (m_vmmaps mdl).
  Hypothesis EG1 : eager_used mdl1 <= eager_used mdl + u szw.
  Hypothesis MW1 : model_ivs_wf mdl1.
  Hypothesis HH1 : m_halted mdl1 = None.
  (* [comment removed for export] *)
  Hypothesis APC : u mpw + u szw <= P8 \/ P8 + 2 ^ 23 <= u mpw.
  (* [comment removed for export] *)
  Hypothesis AW : A_wf A.
  Hypothesis BUD : eager_used mdl + u szw + 2 ^ 17 + A_bytes A <= vm_limit (m_vmmaps mdl).

  Definition lo8 : Z := P8 + 8 * a_nres st.
  #[local] Notation lo := lo8.
  #[local] Notation K := (2 ^ 17).
  #[local] Notation addr := (Z_to_bv 64 lo8).
  #[local] Notation size := (Z_to_bv 64 (2 ^ 17)).

  Lemma s8_lits : 0 < P8 /\ P8 mod PG = 0 /\ P8 + 2 ^ 23 <= CEIL /\ (P8 + 2 ^ 23 <= ia_img_lo IA \/ ia_img_hi IA <= P8)
                  /\ 0 <= a_nres st /\ a_nres st mod 2 ^ 14 = 0 /\ P8 <= lo /\ lo + K <= P8 + 2 ^ 23 /\ lo + K < 2 ^ 64 /\ u addr = lo /\ u size = K.
  Proof using GROW W qg qt FF Lc.
    pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & IN8 & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((D1 & D2 & D3 & D4 & D5) & D6 & D7 & D8).
    pose proof ceil_rng as CR. (lazymatch goal with |- ?G => let G' := eval unfold lo8 in G in change_no_check G' end).
    assert (X : 0 < P8 + 8 * a_nres st /\ P8 + 8 * a_nres st + 2 ^ 17 < 2 ^ 64) by lia.
    repeat split; try lia; rewrite u64_lit; lia.
  Qed.
  Lemma s8_pg : lo mod 4096 = 0 /\ (lo + K) mod 4096 = 0.
  Proof using GROW W qg qt FF Lc RUN.
    destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & _). unfold lo8, PG in *.
    pose proof (Z.div_mod P8 4096 ltac:(lia)) as D1. rewrite L1 in D1.
    pose proof (Z.div_mod (a_nres st) (2 ^ 14) ltac:(lia)) as D2. rewrite L5 in D2.
    split.
    - replace (P8 + 8 * a_nres st) with ((P8 / 4096 + 32 * (a_nres st / 2 ^ 14)) * 4096) by lia. apply Z_mod_mult.
    - replace (P8 + 8 * a_nres st + 2 ^ 17) with ((P8 / 4096 + 32 * (a_nres st / 2 ^ 14) + 32) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Lemma ledger_R8 : rep_ledger bt st mdl.
  Proof using R M0 FF Lc. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _). exact R13. Qed.

  (* [comment removed for export] *)
  Lemma s8_overlap : overlap_sum (vm_maps (m_vmmaps mdl1)) lo (lo + K) <= K.
  Proof using APC EV1 GROW PS PE R W qg qt szw mpw mdl M0 FF Lc RUN.
    destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    destruct ledger_R8 as ((F6 & PM & FOK & FSEP & FCOV) & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    pose proof WM as (RNG & PW & IN6 & R6a & R6b & IN8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & M0POS & _ & _ & _ & M0DYN).
    rewrite EV1, overlap_sum_cons, (overlap_sum_perm _ _ lo (lo + K) PM), !overlap_sum_app.
    (* [comment removed for export] *)
    assert (OC : iv_count (in_rng lo (lo + K)) (mpw, szw) = 0).
    { apply iv_count_in_rng_disjoint. (lazymatch goal with |- ?G => let G' := eval unfold B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (A68 : bt_resv6 bt + bt_resv6_len bt <= P8 \/ P8 + 2 ^ 23 <= bt_resv6 bt).
    { assert (NE : (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) <> (P8, P8 + 2 ^ 23)).
      { intros E. injection E as E1 E2. unfold KSPACE, PG in *. lia. }
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ IN6) (all_ranges_fixed bt st _ IN8) NE) as D. hnf in D. cbn in D. lia. }
    assert (OF6 : overlap_sum F6 lo (lo + K) = 0).
    { apply overlap_sum_off. apply Forall_forall. intros iv Hiv. rewrite Forall_forall in FOK. destruct (FOK iv Hiv) as (G1 & G2 & G3 & _). lia. }
    (* [comment removed for export] *)
    destruct (in_split _ _ PE) as (l1 & l2 & EM).
    assert (OM0 : overlap_sum (bt_maps0 bt) lo (lo + K) <= K).
    { rewrite EM, overlap_sum_app, overlap_sum_cons.
      pose proof (iv_count_in_rng_le (Z_to_bv 64 P8, Z_to_bv 64 (2 ^ 23)) lo (lo + K) ltac:(lia)) as C8.
      rewrite (overlap_sum_off l1), (overlap_sum_off l2); [lia | |]; apply Forall_forall; intros y Hy;
        (destruct (PS l1 l2 y EM ltac:(apply in_or_app; am_tauto)) as [D|D]; [left; lia | right; lia]). }
    (* [comment removed for export] *)
    assert (ODY : overlap_sum (dyn_maps st) lo (lo + K) = 0).
    { apply overlap_sum_off. apply Forall_forall. intros [b n] Hbn. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      assert (DR : exists dl dh, In (dl, dh) (dyn_ranges st) /\ b = Z_to_bv 64 dl /\ n = Z_to_bv 64 (dh - dl)).
      { unfold dyn_maps in Hbn. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff in Hbn as [Hbn|Hbn]; [|apply in_app_iff in Hbn as [Hbn|Hbn]];
          apply in_map_iff in Hbn as (x & E & Hx); injection E as <- <-.
        - exists (sc_map x), (sc_map x + sc_mapsz x). split; [apply in_app_iff; left; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]].
        - exists x, (x + 2 ^ 20). split; [apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]].
        - exists x, (x + 2 ^ 23). split; [apply in_app_iff; right; apply in_app_iff; right; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]]. }
      destruct DR as (dl & dh & Hd & -> & ->).
      destruct (RNG dl dh (all_ranges_dyn bt st _ Hd)) as ((D1 & D2 & D3 & _) & D6 & _).
      pose proof ceil_rng as CR. rewrite !u64_lit by lia.
      pose proof (M0DYN _ _ dl dh PE Hd) as D. rewrite !u64_lit in D by lia. lia. }
    lia.
  Qed.
  Section Mat8.
    Variable mdlm : Model.
    Hypothesis SBM : same_but_materialized mdl1 mdlm.
    Hypothesis MI : MInv A mdlm.

    Lemma s8_mat_eqs : m_vmmaps mdlm = m_vmmaps mdl1 /\ m_vm_lazy mdlm = m_vm_lazy mdl1 /\ eager_used mdlm = eager_used mdl1 /\ m_halted mdlm = None /\ model_ivs_wf mdlm.
    Proof using SBM HH1 MW1.
      destruct (sbm_vmmaps mdl1 mdlm SBM) as [E1 E2]. split; [exact E1|]. split; [exact E2|]. split; [apply eager_used_ext; assumption|].
      split; [| exact (model_ivs_wf_sbm7 mdl1 mdlm SBM MW1)].
      pose proof (same_but_materialized_frame mdl1 mdlm SBM) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _). rewrite HL. exact HH1.
    Qed.

    Lemma s8_top : u addr + u size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64.
    Proof using SBM HH1 MW1 EI1 GROW R W qg qt mdl1 mdl M0 FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_mat_eqs as (E1 & _). rewrite E1.
      destruct ledger_R8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
      assert (ET : alloc_top (m_vmmaps mdl1) = alloc_top (m_vmmaps mdl)) by ((lazymatch goal with |- ?G => let G' := eval unfold alloc_top in G in change_no_check G' end); rewrite EI1; reflexivity). rewrite ET.
      pose proof (page_floor_le (alloc_top (m_vmmaps mdl))). split; [rewrite L9, L10; lia | apply alloc_top_lt].
    Qed.

    Lemma s8_region_free : region_free (vm_reserved (m_vmmaps mdlm)) addr size = true.
    Proof using SBM HH1 MW1 ER1 GROW RH R W qg qt mdl1 mdl M0 FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_mat_eqs as (E1 & _). rewrite E1, ER1.
      destruct ledger_R8 as (_ & _ & _ & _ & RES & _). rewrite RES.
      apply RefNodes.region_free_intro. intros b s Hbs. pose proof (RH (b, s) Hbs) as H. cbn [fst snd] in H. rewrite L9, L10. lia.
    Qed.

    Lemma s8_map_contains : map_contains (vm_maps (m_vmmaps mdlm)) addr size = true.
    Proof using SBM HH1 MW1 EV1 GROW PE R W qg qt szw mpw mdl1 mdl M0 FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_mat_eqs as (E1 & _). rewrite E1, EV1.
      destruct ledger_R8 as ((F6 & PM & _) & _).
      apply (map_contains_intro _ _ _ (Z_to_bv 64 P8) (Z_to_bv 64 (2 ^ 23))).
      - right. apply (Permutation_in _ (Permutation_sym PM)). apply in_or_app. right. apply in_or_app. left. exact PE.
      - rewrite L9, u64_lit by lia. lia.
      - rewrite L9, L10, !u64_lit by lia. lia.
    Qed.

    Lemma s8_budget : mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true.
    Proof using MI SBM BUD AW APC HH1 MW1 EG1 EM1 EV1 GROW PS PE R W qg qt A szw mpw mdl1 mdl M0 FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_mat_eqs as (E1 & E2 & E3 & E4 & E5).
      apply (budget_ok_commit A); [exact MI | exact AW | exact E5 |].
      rewrite E1, E3, L9, L10, EM1. pose proof s8_overlap. lia.
    Qed.

    Lemma s8_OK : m_halted (OKm addr size mdlm) = None /\ MInv A (OKm addr size mdlm)
      /\ (forall p, page_in_ranges p (m_vm_lazy (OKm addr size mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true).
    Proof using MI SBM BUD APC HH1 MW1 EG1 EM1 EL1 EV1 GROW PS PE MW R W qg qt szw mpw mdl1 M0 FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_mat_eqs as (E1 & E2 & E3 & E4 & E5). destruct s8_pg as [P1 P2].
      split; [rewrite OKm_halted; exact E4|]. split.
      - apply MInv_OKm; [exact MI | exact E5 | rewrite L9; exact P1 |].
        rewrite E1, E3, L9, L10, EM1. pose proof s8_overlap. lia.
      - intros p Hp. rewrite OKm_lazy, E2, EL1 in Hp. destruct MW as (_ & _ & Wl & _). exact (page_in_ranges_subtract_sub p _ _ _ Wl Hp).
    Qed.

    Lemma s8_DS : m_halted (DSm addr size mdlm) = None /\ MInv A (DSm addr size mdlm)
      /\ (forall p, page_in_ranges p (m_vm_lazy (DSm addr size mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true).
    Proof using MI SBM HH1 MW1 EL1 GROW MW W qg qt mdl1 FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_mat_eqs as (E1 & E2 & E3 & E4 & E5). destruct s8_pg as [P1 P2].
      split; [rewrite DSm_halted; exact E4|]. split.
      - apply MInv_DSm; [exact MI | exact E5 | rewrite L9; exact P1].
      - intros p Hp. rewrite DSm_lazy, E2, EL1 in Hp. destruct MW as (_ & _ & Wl & _). exact (page_in_ranges_subtract_sub p _ _ _ Wl Hp).
    Qed.
  End Mat8.
  (* [comment removed for export] *)
  Section Post8.
    Variables mdlm mdl' : Model.
    Hypothesis SBM : same_but_materialized mdl1 mdlm.
    Hypothesis SBM' : same_but_materialized (OKm addr size mdlm) mdl'.

    Lemma s8_post_eqs : m_vmmaps mdl' = mmap_fixed_rw_next (m_vmmaps mdl1) addr size
      /\ m_vm_lazy mdl' = maps_subtract (m_vm_lazy mdl) lo (lo + K).
    Proof using SBM' SBM mdlm EL1 GROW W qg qt FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
      destruct (sbm_vmmaps mdl1 mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite E3, E4, OKm_vmmaps, OKm_lazy, E1, E2, EL1, L9, L10. split; reflexivity.
    Qed.

    Lemma s8_post_eager : eager_used mdl' <= eager_used mdl + u szw + K.
    Proof using SBM' SBM mdlm APC MW1 EG1 EV1 GROW PS PE R W qg qt mpw mdl1 M0 FF Lc st bt RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
      destruct (sbm_vmmaps mdl1 mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite (eager_used_ext mdl' (OKm addr size mdl1)); [| rewrite E3, !OKm_vmmaps, E1; reflexivity | rewrite E4, !OKm_lazy, E2; reflexivity].
      pose proof (eager_OKm_le addr size mdl1 MW1) as H. rewrite L9, L10 in H. pose proof s8_overlap. lia.
    Qed.

    Lemma s8_post_ledger :
      vm_maps (m_vmmaps mdl') = (mpw, szw) :: vm_maps (m_vmmaps mdl)
      /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + K))
      /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
      /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + K))
      /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
                (m_vm_lazy mdl')
      /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
      /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
      /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).
    Proof using SBM' SBM mdlm EM1 EMB1 ES1 EB1 EI1 ER1 EL1 EN1 EV1 GROW MW R W qg qt mdl1 M0 FF Lc.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_pg as [P1 P2].
      destruct s8_post_eqs as [E1 E2]. rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_rw_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end).
      rewrite L9, L10, EV1, EN1, ER1, EB1, ES1, EMB1, EI1, EM1. destruct MW as (Wm & Wn & Wl & _).
      destruct ledger_R8 as (_ & _ & _ & LOK & _ & _ & _ & _ & _ & _ & _ & NPOS).
      pose proof ceil_rng as CR.
      split; [reflexivity|]. split; [intros a; apply in_ivz_maps_subtract; lia|].
      split; [apply ivs_pos_subtract; exact NPOS|].
      split; [intros a; apply pg_in_ivz_subtract; [exact Wl | exact P1 | exact P2 | lia]|].
      split; [apply (lazy_ok_subtract CEIL (ia_img_lo IA) (ia_img_hi IA)); [exact Wl | exact P1 | exact P2 | lia | lia | lia | exact LOK]|].
      repeat split; reflexivity.
    Qed.

    Lemma s8_post_rest : same_except_vm mdl1 mdl' /\ model_ivs_wf mdl' /\ m_halted mdl' = None
      /\ (forall a, ~ (lo <= a < lo + K) -> 0 <= a < 2 ^ 64 -> lzb mdl' a = lzb mdl a).
    Proof using SBM' SBM mdlm HH1 MW1 EL1 GROW MW W qg qt FF Lc RUN.
      destruct s8_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). destruct s8_post_eqs as [E1 E2]. destruct s8_pg as [P1 P2].
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold same_except_vm in G in change_no_check G' end). rewrite (sbm_frame_vm _ _ SBM'). rewrite (OKm_frame addr size mdlm). rewrite (sbm_frame_vm _ _ SBM). reflexivity. }
      split.
      { apply (model_ivs_wf_sbm7 _ _ SBM'). apply model_ivs_wf_OKm. exact (model_ivs_wf_sbm7 _ _ SBM MW1). }
      split.
      { pose proof (same_but_materialized_frame _ _ SBM') as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
        rewrite HL, OKm_halted.
        pose proof (same_but_materialized_frame _ _ SBM) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL2 & _). rewrite HL2. exact HH1. }
      intros a NS RA. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite E2. destruct MW as (_ & _ & Wl & _).
      apply page_in_ranges_subtract_out; [exact Wl | lia |].
      apply (page_of_byte_out_aligned (Z_to_bv 64 a) lo (lo + K) P1 P2). rewrite u64_lit by lia. lia.
    Qed.
  End Post8.
End Slot8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition chunk_child (mdl mdl1 : Model) (mpw szw : word) : Prop :=
  vm_maps (m_vmmaps mdl1) = (mpw, szw) :: vm_maps (m_vmmaps mdl)
  /\ vm_noaccess (m_vmmaps mdl1) = vm_noaccess (m_vmmaps mdl) /\ m_vm_lazy mdl1 = m_vm_lazy mdl
  /\ vm_reserved (m_vmmaps mdl1) = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl1) = vm_brk (m_vmmaps mdl)
  /\ vm_start_brk (m_vmmaps mdl1) = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl1) = vm_mmap_base (m_vmmaps mdl)
  /\ vm_init_sp (m_vmmaps mdl1) = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl1) = vm_limit (m_vmmaps mdl)
  /\ eager_used mdl1 <= eager_used mdl + u szw
  /\ model_ivs_wf mdl1
  /\ m_halted mdl1 = None.

Section N8.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation IA := (bt_ia bt).

  Definition N8_stmt : Prop := forall st Lc FF M0 mdl mdl1 (mpw szw : word) (A : list (Z * Z)) (qt qg : Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M0 mdl -> BackingAlgebra.model_ivs_wf mdl ->
    a_nres st + 2 ^ 14 <= 2 ^ 20 ->
    chunk_child mdl mdl1 mpw szw ->
    (u mpw + u szw <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= u mpw) ->
    A_wf A -> eager_used mdl + u szw + 2 ^ 17 + A_bytes A <= vm_limit (m_vmmaps mdl) ->
    let lo := bt_ptrarr bt + 8 * a_nres st in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 (2 ^ 17) in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    lo mod 4096 = 0 /\ 0 < lo /\ u addr = lo /\ u size = 2 ^ 17
    /\ (forall mdlm, same_but_materialized mdl1 mdlm -> MInv A mdlm ->
          u addr + u size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv A (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv A (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl', same_but_materialized mdl1 mdlm -> same_but_materialized (OK mdlm) mdl' ->
          vm_maps (m_vmmaps mdl') = (mpw, szw) :: vm_maps (m_vmmaps mdl)
          /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + 2 ^ 17))
          /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
          /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + 2 ^ 17))
          /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                         /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                         /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
                    (m_vm_lazy mdl')
          /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
          /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
          /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
          /\ eager_used mdl' <= eager_used mdl + u szw + 2 ^ 17
          /\ same_except_vm mdl1 mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None
          /\ (forall a, ~ (lo <= a < lo + 2 ^ 17) -> 0 <= a < 2 ^ 64 -> lzb mdl' a = lzb mdl a)).

  Theorem N8_pf : boot_facts bt -> N8_stmt.
  Proof using.
    intros BF st Lc FF M0 mdl mdl1 mpw szw A qt qg W R MW GROW (EV1 & EN1 & EL1 & ER1 & EB1 & ES1 & EMB1 & EI1 & EM1 & EG1 & MW1 & HH1) APC AW BUD. cbn zeta.
    pose proof (boot_facts_ptr8 bt BF) as PE. pose proof (boot_facts_ptr8_sep bt BF) as PS. pose proof (boot_facts_res_in_hull bt BF) as RH.
    pose proof (s8_lits bt st Lc FF qt qg W GROW) as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    pose proof (s8_pg bt st Lc FF qt qg W GROW) as [P1 P2]. fold (lo8 bt st) in *.
    split; [exact P1|]. split; [lia|]. split; [exact L9|]. split; [exact L10|]. split.
    - intros mdlm SBM MI.
      destruct (s8_top bt st Lc FF M0 mdl mdl1 qt qg W R GROW EI1 MW1 HH1 mdlm SBM) as [T1 T2].
      destruct (s8_OK bt st Lc FF M0 mdl mdl1 mpw szw A qt qg W R MW PE PS GROW EV1 EL1 EM1 EG1 MW1 HH1 APC BUD mdlm SBM MI) as (O1 & O2 & O3).
      destruct (s8_DS bt st Lc FF mdl mdl1 A qt qg W MW GROW EL1 MW1 HH1 mdlm SBM MI) as (D1 & D2 & D3).
      split; [exact T1|]. split; [exact T2|].
      split; [exact (s8_region_free bt st Lc FF M0 mdl mdl1 qt qg W R RH GROW ER1 MW1 HH1 mdlm SBM)|].
      split; [exact (s8_map_contains bt st Lc FF M0 mdl mdl1 mpw szw qt qg W R PE GROW EV1 MW1 HH1 mdlm SBM)|].
      split; [exact (s8_budget bt st Lc FF M0 mdl mdl1 mpw szw A qt qg W R PE PS GROW EV1 EM1 EG1 MW1 HH1 APC AW BUD mdlm SBM MI)|].
      split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact D1|]. split; [exact D2 | exact D3].
    - intros mdlm mdl' SBM SBM'.
      destruct (s8_post_ledger bt st Lc FF M0 mdl mdl1 mpw szw qt qg W R MW GROW EV1 EN1 EL1 ER1 EI1 EB1 ES1 EMB1 EM1 mdlm mdl' SBM SBM') as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
      destruct (s8_post_rest bt st Lc FF mdl mdl1 qt qg W MW GROW EL1 MW1 HH1 mdlm mdl' SBM SBM') as (Q1 & Q2 & Q3 & Q4).
      repeat (split; [assumption|]).
      split; [exact (s8_post_eager bt st Lc FF M0 mdl mdl1 mpw szw qt qg W R PE PS GROW EV1 EG1 MW1 APC mdlm mdl' SBM SBM')|].
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3 | exact Q4].
  Qed.

End N8.
