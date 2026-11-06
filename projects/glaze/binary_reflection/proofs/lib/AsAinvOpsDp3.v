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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section Dp.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition nn_rng (newnode : option Z) : list (Z * Z) := List.map (fun b => (b, b + 2 ^ 20)) (blk_opt newnode).
  Definition ns_rng (newstore : option Z) : list (Z * Z) := List.map (fun b => (b, b + 2 ^ 23)) (blk_opt newstore).

  Lemma a_dep_depot_insert : forall st b h s2 sid fr' std' nn ns,
    a_dep (op_depot_insert st b h s2 sid fr' std' nn ns)
    = DEP (dp_nids (a_dep st) + 1) (fupdZ (dp_tab (a_dep st)) b (dp_nids (a_dep st) + 1))
          (fupdZ (dp_hash (a_dep st)) (dp_nids (a_dep st) + 1) h) (fupdZ (dp_link (a_dep st)) (dp_nids (a_dep st) + 1) s2)
          (fupdZ (dp_store (a_dep st)) (dp_nids (a_dep st) + 1) sid)
          (dp_nodeblocks (a_dep st) ++ blk_opt nn) (dp_storeblocks (a_dep st) ++ blk_opt ns) fr' std'.
  Proof using. intros. reflexivity. Qed.

  Lemma all_ranges_depot : forall st b h s2 sid fr' std' nn ns,
    all_ranges bt (op_depot_insert st b h s2 sid fr' std' nn ns)
    = (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st) ++ List.map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)))
      ++ nn_rng nn ++ (List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)) ++ ns_rng ns).
  Proof using.
    intros. (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite a_dep_depot_insert.
    (lazymatch goal with |- ?G => let G' := eval cbn [dp_nodeblocks dp_storeblocks a_sec op_depot_insert] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold nn_rng, ns_rng in G in change_no_check G' end). rewrite !map_app. rewrite <- !app_assoc. reflexivity.
  Qed.
  Lemma all_ranges_old3 : forall st,
    all_ranges bt st = (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st) ++ List.map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)))
      ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)).
  Proof using. intros st. (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite <- !app_assoc. reflexivity. Qed.
  Lemma in_all_ranges_depot : forall st b h s2 sid fr' std' nn ns x,
    In x (all_ranges bt (op_depot_insert st b h s2 sid fr' std' nn ns))
    <-> In x (all_ranges bt st) \/ In x (nn_rng nn) \/ In x (ns_rng ns).
  Proof using.
    intros. rewrite all_ranges_depot, all_ranges_old3. rewrite !in_app_iff. am_tauto.
  Qed.
  Lemma in_nn_rng : forall nn x, In x (nn_rng nn) <-> exists p, nn = Some p /\ x = (p, p + 2 ^ 20).
  Proof using.
    intros nn x. (lazymatch goal with |- ?G => let G' := eval unfold nn_rng in G in change_no_check G' end). destruct nn as [p|]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
    - split; [intros [<-|[]]; exists p; split; reflexivity | intros (p' & E & ->); injection E as ->; left; reflexivity].
    - split; [intros [] | intros (p' & E & _); discriminate E].
  Qed.
  Lemma in_ns_rng : forall ns x, In x (ns_rng ns) <-> exists p, ns = Some p /\ x = (p, p + 2 ^ 23).
  Proof using.
    intros ns x. (lazymatch goal with |- ?G => let G' := eval unfold ns_rng in G in change_no_check G' end). destruct ns as [p|]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
    - split; [intros [<-|[]]; exists p; split; reflexivity | intros (p' & E & ->); injection E as ->; left; reflexivity].
    - split; [intros [] | intros (p' & E & _); discriminate E].
  Qed.

  (* [comment removed for export] *)
  Lemma splits_app_end : forall (l : list (Z * Z)) (x : Z * Z),
    (forall m1 m2 lo hi lo' hi', l = m1 ++ (lo, hi) :: m2 -> In (lo', hi') (m1 ++ m2) -> hi <= lo' \/ hi' <= lo) ->
    (forall lo' hi', In (lo', hi') l -> snd x <= lo' \/ hi' <= fst x) ->
    forall m1 m2 lo hi lo' hi', l ++ [x] = m1 ++ (lo, hi) :: m2 -> In (lo', hi') (m1 ++ m2) -> hi <= lo' \/ hi' <= lo.
  Proof using.
    intros l x DJ AP. pose proof (splits_insert l [] x) as Q. rewrite app_nil_r in Q. exact (Q DJ AP).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem OPS_WF_depot_insert_pf : OPS_WF_depot_insert bt.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold OPS_WF_depot_insert in G in change_no_check G' end).
    intros st Lc FF b h s2 sid fr' std' nn ns W Hb Hh Hsid Hstd Hs2 [RM1 RM2] NID NN FR LSB CAP PN PS PNS PN0 PS0.
    pose proof W as (WR & WC & WQ & WS & WL & WK & WD & WM & WMP & G).
    destruct WD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    set (st' := op_depot_insert st b h s2 sid fr' std' nn ns).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, WFq in G in change_no_check G' end).
    split. { exact WR. } split. { exact WC. } split. { exact WQ. } split. { exact WS. } split. { exact WL. } split. { exact WK. }
    split. { (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_depot in G in change_no_check G' end). subst st'. rewrite a_dep_depot_insert. change (a_kact (op_depot_insert st b h s2 sid fr' std' nn ns)) with (a_kact st).
      (lazymatch goal with |- ?G => let G' := eval cbn [dp_nids dp_tab dp_hash dp_link dp_store dp_nodeblocks dp_storeblocks dp_frames dp_stored] in G in change_no_check G' end).
      rewrite !length_app, !Nat2Z.inj_add in *.
      split; [lia|]. split; [exact RM1|]. split; [exact NID|].
      split. { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). pose proof (D4 b Hb). destruct (Z.eqb_spec i b) as [->|NE]; [lia | pose proof (D4 i Hi); lia]. }
      split. { intros id Hid. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec id (dp_nids (a_dep st) + 1)) as [->|NE].
               - subst s2. pose proof (D4 b Hb). lia.
               - exact (D5 id ltac:(lia)). }
      split. { destruct nn as [p|]; cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in *.
               - assert (NE : (dp_nids (a_dep st) + 1) / 2 ^ 16 <> Z.of_nat (length (dp_nodeblocks (a_dep st)))) by (intros E; pose proof (proj2 NN E); discriminate).
                 assert (LO : dp_nids (a_dep st) / 2 ^ 16 <= (dp_nids (a_dep st) + 1) / 2 ^ 16) by (apply Z.div_le_mono; lia).
                 assert (HI : (dp_nids (a_dep st) + 1) / 2 ^ 16 <= dp_nids (a_dep st) / 2 ^ 16 + 1).
                 { replace (dp_nids (a_dep st) / 2 ^ 16 + 1) with ((dp_nids (a_dep st) + 1 * 2 ^ 16) / 2 ^ 16) by (apply Z.div_add; lia). apply Z.div_le_mono; lia. }
                 lia.
               - rewrite Z.add_0_r. symmetry. apply (proj1 NN). reflexivity. }
      split; [lia|]. split; [exact CAP|].
      split. { clear -RM2 FR D9. unfold FRW in *. destruct ns; cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in *; lia. }
      split; [exact LSB|]. split; [exact Hstd|].
      intros q Hq. rewrite <- app_assoc in Hq. apply in_app_iff in Hq. rewrite !in_app_iff in Hq.
      destruct Hq as [Hq|[Hq|[Hq|Hq]]].
      - apply D12. apply in_app_iff. left. exact Hq.
      - destruct nn as [p|]; [| destruct Hq]. destruct Hq as [<-|[]]. exact (proj1 (proj2 (PN p eq_refl))).
      - apply D12. apply in_app_iff. right. exact Hq.
      - destruct ns as [p|]; [| destruct Hq]. destruct Hq as [<-|[]]. exact (proj1 (proj2 (PS p eq_refl))). }
    split. { exact WM. }
    split. { (* [comment removed for export] *) destruct WMP as (RNG & PWS & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20).
      split; [| split; [| do 17 (split; [assumption|]);
        intros b0 n0 lo hi Hb0 Hin; unfold dyn_ranges in Hin; subst st'; rewrite a_dep_depot_insert in Hin; cbn [dp_nodeblocks dp_storeblocks a_sec op_depot_insert] in Hin;
        rewrite !map_app, !in_app_iff in Hin; fold (nn_rng nn) (ns_rng ns) in Hin;
        destruct Hin as [Hin | [[Hin | Hin] | [Hin | Hin]]];
        [ apply (K20 b0 n0 lo hi Hb0); (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end); rewrite !in_app_iff; left; exact Hin
        | apply (K20 b0 n0 lo hi Hb0); (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end); rewrite !in_app_iff; right; left; exact Hin
        | apply in_nn_rng in Hin; destruct Hin as (p & Ep & E); injection E as -> ->; exact (PN0 p b0 n0 Ep Hb0)
        | apply (K20 b0 n0 lo hi Hb0); (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end); rewrite !in_app_iff; right; right; exact Hin
        | apply in_ns_rng in Hin; destruct Hin as (p & Ep & E); injection E as -> ->; exact (PS0 p b0 n0 Ep Hb0) ]]].
      - intros lo hi Hin. apply in_all_ranges_depot in Hin. destruct Hin as [Hin | [Hin | Hin]]; [exact (RNG lo hi Hin) | |].
        + apply in_nn_rng in Hin. destruct Hin as (p & Ep & E). injection E as -> ->. destruct (PN p Ep) as (DY & AL & _).
          split; [exact DY|]. split; [lia|]. split; [exact AL|]. apply modpg_add; [exact AL | reflexivity].
        + apply in_ns_rng in Hin. destruct Hin as (p & Ep & E). injection E as -> ->. destruct (PS p Ep) as (DY & AL & _).
          split; [exact DY|]. split; [lia|]. split; [exact AL|]. apply modpg_add; [exact AL | reflexivity].
      - subst st'. intros l1 l2 lo hi lo' hi'. rewrite all_ranges_depot. revert l1 l2 lo hi lo' hi'.
        set (L1 := bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st) ++ List.map (fun b0 => (b0, b0 + 2 ^ 20)) (dp_nodeblocks (a_dep st))).
        set (L2 := List.map (fun b0 : Z => (b0, b0 + 2 ^ 23)) (dp_storeblocks (a_dep st))).
        assert (OLD : all_ranges bt st = L1 ++ L2) by (subst L1 L2; apply all_ranges_old3).
        (* [comment removed for export] *)
        assert (STEP1 : forall m1 m2 lo hi lo' hi', (L1 ++ L2) ++ ns_rng ns = m1 ++ (lo, hi) :: m2 -> In (lo', hi') (m1 ++ m2) -> hi <= lo' \/ hi' <= lo).
        { destruct ns as [q|]; (lazymatch goal with |- ?G => let G' := eval unfold ns_rng in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map] in G in change_no_check G' end).
          - apply splits_app_end; [rewrite <- OLD; exact PWS|]. intros lo' hi' Hin. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite <- OLD in Hin.
            destruct (PS q eq_refl) as (_ & _ & DJ). exact (DJ lo' hi' Hin).
          - rewrite app_nil_r. rewrite <- OLD. exact PWS. }
        destruct nn as [p|]; (lazymatch goal with |- ?G => let G' := eval unfold nn_rng in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map] in G in change_no_check G' end).
        + (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply splits_insert.
          * intros m1 m2 lo hi lo' hi' E. rewrite app_assoc in E. exact (STEP1 m1 m2 lo hi lo' hi' E).
          * intros lo' hi' Hin. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). apply in_app_iff in Hin. rewrite in_app_iff in Hin.
            destruct Hin as [Hin|[Hin|Hin]].
            -- destruct (PN p eq_refl) as (_ & _ & DJ). apply DJ. rewrite OLD. apply in_app_iff. left. exact Hin.
            -- destruct (PN p eq_refl) as (_ & _ & DJ). apply DJ. rewrite OLD. apply in_app_iff. right. exact Hin.
            -- apply in_ns_rng in Hin. destruct Hin as (q & Eq & E). injection E as -> ->. destruct (PNS p q eq_refl Eq); lia.
        + (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros l1 l2 lo hi lo' hi' E. rewrite app_assoc in E. exact (STEP1 l1 l2 lo hi lo' hi' E). }
    exact G.
  Qed.
End Dp.
