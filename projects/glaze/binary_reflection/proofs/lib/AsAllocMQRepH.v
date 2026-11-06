(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAinvHoleP3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsKSys6.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= Zify.zify; (xlia zchecker).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
#[local] Notation u := bv_unsigned.

Section FholeQ.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Definition OPS_REPq_fhole : Prop := forall st Lc FF M M' mdl mdl' c qt qg,
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    (forall a : word, M' a <> M a -> fslot bt st c (u a) /\ M' a = None) ->
    ledger_destroyed bt mdl mdl' (fa_beg SBEG c + r_mapped_fa (a_reg st c)) KFAMAP ->
    MInv (a_aa st) mdl' -> eager_used mdl' <= eager_used mdl ->
    Rep bt (op_fhole st c) Lc FF M' mdl'.

  Theorem OPS_REPq_fhole_pf : OPS_REPq_fhole.
  Proof using.
    intros st Lc FF M M' mdl mdl' c qt qg W R Hc NH FR CH LD MI EAG.
    set (lo := fa_beg SBEG c + r_mapped_fa (a_reg st c)) in *.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & LZ0 & LZB & LRI & M06 & M0K & _) & G).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _).
    assert (SLOT : SBEG <= lo /\ bt_resv6 bt <= lo /\ lo + KFAMAP <= bt_resv6 bt + bt_resv6_len bt /\ lo + KFAMAP <= SBEG + KSPACE /\ 0 <= lo /\ lo + KFAMAP < 2 ^ 64).
    { subst lo. unfold KFAMAP in *. ulia. }
    destruct SLOT as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6). assert (Elo : lo = lo) by reflexivity. unfold lo in Elo at 2. clearbody lo.
    assert (R' : Rep bt st Lc FF M' mdl).
    { apply (Rep_local bt st Lc FF M M' mdl W R). apply agree_at. intros a NE Hs.
      destruct (CH a NE) as [HU _]. exact (fslot_not_supp bt st Lc FF c _ _ W Hc FR (u a) Hs HU). }
    pose proof (st_regdata_fhole st c Hc) as EQ.
    apply (Rep_regdata_mem bt st (op_fhole st c) Lc FF M' mdl mdl' EQ R').
    - destruct R' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _).
      destruct R13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      destruct LD as (DM & DN & DL & DF & E1 & E2 & E3 & E4 & E5 & E6).
      assert (HOL : forall a, holes bt (op_fhole st c) a <-> holes bt st a \/ fslot bt st c a) by (intros a; exact (holes_fhole bt st c a Hc)).
      assert (COM : forall a, committed bt (op_fhole st c) a <-> committed bt st a) by (intros a; exact (committed_regdata bt st _ a EQ)).
      assert (USL : forall a, fslot bt st c a <-> lo <= a < lo + KFAMAP) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold fslot in G in change_no_check G' end); subst lo; tauto).
      (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end). change (dyn_maps (op_fhole st c)) with (dyn_maps st). change (a_dep (op_fhole st c)) with (a_dep st).
      split. { destruct L1 as (F6 & PF & FOK & FPW & FH).
               assert (WF6 : ivs_wf F6).
               { intros q Hq. rewrite Forall_forall in FOK. destruct (FOK q Hq) as (A1 & A2 & A3 & _). (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in G in change_no_check G' end).
                 clear -A1 A2 A3 SP3. ulia. }
               pose proof (frag_destroyed bt ltac:(clear -SP3; ulia) ltac:(clear -SP1; lia) F6 lo FOK (seps_of_split F6 FPW) WF6
                             ltac:(subst lo; apply fa_slot_aligned; exact Y6) SL2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); unfold KFAMAP in SL3; exact SL3)) as FD.
               cbn zeta in FD. destruct FD as (FOK' & FSP' & FWF' & FCV').
               exists (maps_subtract F6 lo (lo + KUSERMAP)).
               assert (EK : KUSERMAP = KFAMAP) by reflexivity.
               split. { rewrite DM, <- EK. eapply Permutation_trans; [apply maps_subtract_perm; exact PF|].
                        rewrite !maps_subtract_app.
                        rewrite (maps_subtract_id (bt_maps0 bt) lo (lo + KUSERMAP) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)).
                        2:{ pose proof M0K as M0. rewrite Forall_forall in M0 |- *. intros [b n] Hin. specialize (M0 _ Hin). cbn [fst snd] in M0 |- *.
                            (lazymatch goal with |- ?G => let G' := eval unfold off_range in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). split; [exact M0|]. rewrite EK.
                            pose proof (M06 b n) as M6b. clear -M0 M6b Hin SL2 SL3.
                            destruct (Z.lt_ge_cases (u b) (bt_resv6 bt)) as [B1|B1].
                            - left. destruct (Z.le_gt_cases (u b + u n) (bt_resv6 bt)) as [B2|B2]; [clear M6b Hin; lia|].
                              exfalso. apply (M6b (bt_resv6 bt) Hin); clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia.
                            - right. destruct (Z.lt_ge_cases (u b) (bt_resv6 bt + bt_resv6_len bt)) as [B2|B2]; [| clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia].
                              exfalso. apply (M6b (u b) Hin); clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia. }
                        rewrite (maps_subtract_id (dyn_maps st) lo (lo + KUSERMAP) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)); [apply Permutation_refl|].
                        rewrite Forall_forall. intros [b n] Hin. (lazymatch goal with |- ?G => let G' := eval unfold off_range in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite EK.
                        unfold dyn_maps in Hin. rewrite !in_app_iff, !in_map_iff in Hin.
                        destruct Hin as [(sc & E & Hs) | [(bb & E & Hb) | (bb & E & Hb)]]; injection E as <- <-.
                        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (sec_dyn st sc Hs)) as D. hnf in D. cbn in D.
                          pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)) as (MS1 & _). unfold sc_mapsz in *. rewrite !u64_lit by ulia. unfold KFAMAP in *. ulia.
                        + destruct (node_blocks_range bt st Lc FF W bb ltac:(right; exact Hb)) as (A1 & A2 & A3).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (node_dyn st bb Hb)) as D. hnf in D. cbn in D. rewrite !u64_lit by ulia. unfold KFAMAP in *. ulia.
                        + destruct (store_blocks_range bt st Lc FF W bb ltac:(right; exact Hb)) as (A1 & A2 & A3).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st bb Hb)) as D. hnf in D. cbn in D. rewrite !u64_lit by ulia. unfold KFAMAP in *. ulia. }
               split; [exact FOK'|]. split; [exact (split_of_seps _ FSP')|].
               intros a Ha. rewrite !in_ivz_covered, (FCV' a), (HOL a), (USL a), <- EK. rewrite <- in_ivz_covered. rewrite (FH a Ha). tauto. }
      split. { intros a. rewrite DN, (in_ivz_maps_subtract (vm_noaccess (m_vmmaps mdl)) lo (lo + KFAMAP) a SL5 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia) SL6), (L2 a), (COM a), (HOL a), (USL a). tauto. }
      split. { intros a. rewrite (DL a), (L3 a), (COM a), (HOL a), (USL a).
               assert (STORE : forall b, In b (dp_storeblocks (a_dep st)) -> b <= a < b + 2 ^ 23 -> ~ (lo <= a < lo + KFAMAP)).
               { intros b Hb Hab X. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st b Hb)) as D. hnf in D. cbn in D. clear -D Hab X SL2 SL3. unfold KFAMAP in *. lia. }
               split.
               - intros [[(A & B & Cn) | (b & Hb & Hab)] N]; [left; tauto | right; exists b; exact (conj Hb Hab)].
               - intros [(A & B & Cn) | (b & Hb & Hab)]; [split; [left; tauto | tauto] | split; [right; exists b; exact (conj Hb Hab) | exact (STORE b Hb Hab)]]. }
      split; [exact DF|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E5, E6. repeat (split; [assumption|]). rewrite DN. apply AsKSys6.ivs_pos_subtract. exact L12.
    - destruct R' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _).
      destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
      change (a_aa (op_fhole st c)) with (a_aa st). change (a_sec (op_fhole st c)) with (a_sec st). change (a_dep (op_fhole st c)) with (a_dep st).
      change (a_shsec (op_fhole st c)) with (a_shsec st). change (a_nres (op_fhole st c)) with (a_nres st).
      split; [exact B1|]. split; [exact MI|]. split; [exact B3|]. split; [exact B4|].
      split. { intros c0 Hc0. destruct (fhole_data st c c0) as (RMU & RAU & RFA & RFR). rewrite RMU, RFA. exact (B5 c0 Hc0). }
      split; [exact B6|]. split; [exact B7|].
      assert (PC : prim_charge (op_fhole st c) = prim_charge st).
      { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end). apply sum_classes_ext. intros c0. destruct (fhole_data st c c0) as (RMU & RAU & RFA & RFR). rewrite RMU, RFA. reflexivity. }
      rewrite PC. change (sec_charge (op_fhole st c)) with (sec_charge st). change (depot_charge (op_fhole st c)) with (depot_charge st). destruct B8 as [B8 B9]. split; [clear -B8 EAG; lia | exact B9].   (* [comment removed for export] *)
  Qed.
End FholeQ.
