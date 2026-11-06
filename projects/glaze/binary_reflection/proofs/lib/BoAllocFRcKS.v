(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcHS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sec_cells (bt : as_boot) (TSDP : Z) : Prop :=
  In (IB bt + 64, 8%nat, 4096) (bt_consts bt) /\ In (IB bt + 72, 8%nat, bt_ptrarr bt) (bt_consts bt)
  /\ In (0x105ef8, 8%nat, 0x19dc60) (bt_consts bt) /\ In (0x19dc60, 8%nat, 4096) (bt_consts bt)
  /\ In (0x105f58, 8%nat, 1) (bt_consts bt)
  /\ In (0x19fce8 + 144, 8%nat, 0) (bt_consts bt) /\ In (0x19fce8 + 120, 8%nat, 18446744073709551615) (bt_consts bt)
  /\ (TSDP + 8 <= IB bt + 120 \/ IB bt + 728 <= TSDP).

Section WithCeil.
Context {RC : run_ceil}.
Definition HYP_SHADOW_GATE_stmt (bt : as_boot) : Prop :=
  forall st Lc FF (M0 : mem) mdl mdlm (qt qg pb n : Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M0 mdl ->
    same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm -> model_ivs_wf mdlm ->
    pb mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
    (SB <= pb /\ pb + n <= AS_GAPLO) \/ (AS_GAPHI <= pb /\ pb + n <= AS_HEAPLO) ->
    madvise_dontneed_ok (m_vmmaps mdlm) (Z_to_bv 64 pb) (Z_to_bv 64 n) = true.
End WithCeil.
End BoAllocFRcHS.
Require Stdlib.NArith.NArith Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcGS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRcS1.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gbb_scan_spec : forall p l acc, 0 <= acc <= p ->
  let r := gbb_scan p l acc in
  (r = acc \/ (In r l /\ r <= p)) /\ acc <= r /\ (forall x, In x l -> x <= p -> x <= r).
Proof.
  intros p l. induction l as [|h l IH]; intros acc Hacc; (lazymatch goal with |- ?G => let G' := eval cbn [gbb_scan] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). split; [left; reflexivity|]. split; [lia|]. intros x [].
  - set (acc' := if ((h <=? p) && (acc <? h))%bool then h else acc).
    assert (A : 0 <= acc' <= p /\ acc <= acc' /\ (acc' = acc \/ (acc' = h /\ h <= p)) /\ (h <= p -> h <= acc')).
    { (lazymatch goal with |- ?G => let G' := eval unfold acc' in G in change_no_check G' end). destruct (h <=? p) eqn:E1; destruct (acc <? h) eqn:E2; (lazymatch goal with |- ?G => let G' := eval cbn [andb] in G in change_no_check G' end);
        try apply Z.leb_le in E1; try apply Z.leb_gt in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E2; repeat split; try lia; tauto. }
    destruct A as (A1 & A2 & A3 & A4). specialize (IH acc' A1). cbv zeta in IH |- *. destruct IH as (I1 & I2 & I3).
    split; [| split].
    + destruct I1 as [I1 | (I1 & I1')]; [| right; split; [right; exact I1 | exact I1']].
      rewrite I1. destruct A3 as [A3 | (A3 & A3')]; [left; exact A3 | right; split; [left; symmetry; exact A3 | rewrite A3; exact A3']].
    + lia.
    + intros x [-> | Hx] Hxp; [specialize (A4 Hxp); lia | exact (I3 x Hx Hxp)].
Qed.

Lemma gbb_scan_max : forall p l h, In h l -> 0 < h <= p -> (forall x, In x l -> x <= p -> x <= h) -> gbb_scan p l 0 = h.
Proof.
  intros p l h Hin Hh Hmax. pose proof (gbb_scan_spec p l 0 ltac:(lia)) as S. cbv zeta in S. destruct S as (S1 & S2 & S3).
  pose proof (S3 h Hin ltac:(lia)) as LE.
  destruct S1 as [S1 | (S1 & S1')]; [lia|]. pose proof (Hmax _ S1 S1'). lia.
Qed.

Section RcGS.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Section W.
    Variables (st : ast) (Lc FF : list (Z * Z)).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.
    (* [comment removed for export] *)
    Hypothesis IMGLO : ia_img_lo IA <= 65536.

    (* [comment removed for export] *)
    Lemma sec_item_idx : forall m n, In (m, n) (quar st) -> is_primary n = false ->
      exists i s, nth_error (a_sec st) i = Some s /\ In s (a_sec st) /\ sc_user s = m + 16 /\ sc_n s = n.
    Proof using W qg qt FF Lc bt RUN.
      intros m n Hq HP. destruct (quar_sec bt st Lc FF W m n Hq HP) as (s & Hs & Eu & En).
      destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s. repeat split; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma sec_geom : forall s, In s (a_sec st) ->
      let h := sc_map s in let msz := sc_mapsz s in
      0 < h /\ h + msz <= CEIL /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\ 65536 <= msz
      /\ h + 4096 + 16 <= sc_user s /\ sc_user s + sc_n s <= h + msz /\ 64513 <= sc_n s <= NMAX
      /\ ia_img_hi IA <= h /\ (h + msz <= AS_LO \/ AS_HEAPLO <= h)
      /\ (h + msz <= SBEG \/ SBEG + KSPACE + PG <= h)
      /\ (h + msz <= T \/ T + PG <= h)
      /\ (h + msz <= bt_tctx bt \/ bt_tctx bt + 0x10000 <= h)
      /\ (h + msz <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= h).
    Proof using IMGLO W qg qt FF Lc.
      intros s Hs. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      destruct (sec_facts bt st Lc FF W s Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      pose proof (sec_dyn st s Hs) as HD.
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
      destruct (RNG _ _ (all_ranges_dyn bt st _ HD)) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (fixed_members bt st Lc FF W) as (_ & IN8 & _ & INT & _ & _ & INC).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT HD) as DT. hnf in DT. cbn in DT.
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INC HD) as DC. hnf in DC. cbn in DC.
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 HD) as D8. hnf in D8. cbn in D8.
      pose proof (space_vs_dyn bt st Lc FF W _ _ HD) as DS.
      pose proof (img_lits bt st Lc FF W) as [I1 I2].
      assert (M65 : 65536 <= sc_mapsz s) by (clear - A5 A6 A7; unfold PG in *; lia).
      assert (IMG : ia_img_hi IA <= sc_map s).
      { destruct D4 as [D4 | D4]; [| exact D4]. exfalso. clear - D4 I1 A1 A3 M65 IMGLO. unfold PG in *. Z.div_mod_to_equations. lia. }
      unfold PG in *. repeat split; try assumption; try lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sec_scan : forall s m, In s (a_sec st) -> sc_map s + 4096 <= m < sc_map s + sc_mapsz s ->
      gbb_scan m (map sc_map (a_sec st)) 0 = sc_map s.
    Proof using W qg qt FF Lc bt RUN.
      intros s m Hs Hm. destruct (sec_facts bt st Lc FF W s Hs) as (A1 & _).
      apply gbb_scan_max; [apply in_map; exact Hs | lia |].
      intros x Hx Hxm. apply in_map_iff in Hx as (s' & <- & Hs').
      destruct (sec_cases bt st Lc FF W s s' Hs Hs') as [<- | [D | D]]; [lia | | ].
      - exfalso. lia.
      - destruct (sec_facts bt st Lc FF W s' Hs') as (B1 & _ & _ & _ & B5 & B6 & B7 & _). unfold PG in *. lia.
    Qed.

    Lemma ptrarr_geom :
      ia_img_hi IA <= bt_ptrarr bt /\ bt_ptrarr bt + 2 ^ 23 <= CEIL /\ bt_ptrarr bt mod 4096 = 0
      /\ (bt_ptrarr bt + 2 ^ 23 <= AS_LO \/ AS_HEAPLO <= bt_ptrarr bt)
      /\ (bt_ptrarr bt + 2 ^ 23 <= SBEG \/ SBEG + KSPACE + PG <= bt_ptrarr bt)
      /\ (bt_ptrarr bt + 2 ^ 23 <= T \/ T + PG <= bt_ptrarr bt)
      /\ (bt_ptrarr bt + 2 ^ 23 <= bt_tctx bt \/ bt_tctx bt + 0x10000 <= bt_ptrarr bt)
      /\ Z.of_nat (length (a_sec st)) <= a_nres st <= 2 ^ 20.
    Proof using IMGLO W qg qt FF Lc.
      destruct (ptrarr_facts bt st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & P8).
      pose proof (fixed_members bt st Lc FF W) as (_ & IN8 & _ & INT & _ & _ & INC).
      pose proof (img_lits bt st Lc FF W) as [I1 I2].
      pose proof (space_vs_fixed bt st Lc FF W _ _ IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as DS.
      assert (NE1 : (T, T + PG) <> (bt_ptrarr bt, bt_ptrarr bt + 2 ^ 23)) by (intros E; injection E; intros; unfold PG in *; lia).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ IN8) NE1) as DT. hnf in DT. cbn in DT.
      assert (NE2 : (bt_tctx bt, bt_tctx bt + 0x10000) <> (bt_ptrarr bt, bt_ptrarr bt + 2 ^ 23)) by (intros E; injection E; intros; lia).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INC) (all_ranges_fixed bt st _ IN8) NE2) as DC. hnf in DC. cbn in DC.
      pose proof W as (_ & _ & _ & (WS1 & WS2 & WS3 & _) & _).
      assert (IMG : ia_img_hi IA <= bt_ptrarr bt) by (destruct D4 as [D4 | D4]; [exfalso; clear - D4 I1 D1 IMGLO; lia | exact D4]).
      unfold PG in *. repeat split; try assumption; try lia.
    Qed.

    (* [comment removed for export] *)
    Lemma range_private : forall lo hi a, lo <= a < hi -> 0 < lo -> hi <= CEIL ->
      (hi <= ia_img_lo IA \/ ia_img_hi IA <= lo) -> (hi <= AS_LO \/ AS_HEAPLO <= lo) ->
      (hi <= bt_fs bt \/ bt_fs bt + FAKE_SIZE <= lo) ->
      (forall p' n' lo' hi', In (p', n') Lc -> ext bt st Lc p' n' lo' hi' -> hi <= lo' \/ hi' <= lo) ->
      rt_priv IA Lc FF a.
    Proof using W qg qt.
      intros lo hi a Ha Hlo Hhi HI HB HF HL.
      split; [clear - Ha Hhi; lia|]. split; [clear - Ha HI; lia|].
      destruct (heap_not_shadowish bt st Lc FF W Lc a ltac:(intros p0 n0 H0; exact H0) ltac:(clear - Ha HB; lia)) as (N1 & N2 & N3 & N4).
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      - destruct V as (p' & n' & Hin & Hpa). destruct (live_ext bt st Lc FF W p' n' Hin) as (lo' & hi' & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n' ltac:(lia)) as (U1 & _).
        destruct (HL p' n' lo' hi' Hin E) as [D | D]; clear - D Ha Hpa Y1 Y2 U1 Y8; lia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        clear - HF Ha Hfa F1 F2 F3 F4. ulia.
    Qed.

    (* [comment removed for export] *)
    Lemma sec_quar_private : forall m n s a, In (m, n) (quar st) -> is_primary n = false -> In s (a_sec st) -> sc_user s = m + 16 -> sc_n s = n ->
      sc_map s <= a < sc_map s + sc_mapsz s -> rt_priv IA Lc FF a.
    Proof using IMGLO W qg qt.
      intros m n s a Hq HP Hs Eu En Ha.
      pose proof (sec_geom s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      pose proof (img_lits bt st Lc FF W) as [I1 I2].
      apply (range_private (sc_map s) (sc_map s + sc_mapsz s) a Ha G1 G2 ltac:(right; exact G9) G10 (fs_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs))).
      intros p' n' lo' hi' Hin E.
      destruct E as [(HP' & -> & -> & CV' & HC' & LIV' & S1 & S2) | (HP' & sc & Hsc & Eu' & En' & -> & ->)].
      - clear - G11 S1 S2. ulia.
      - destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [<- | D].
        + exfalso. apply (sec_live_not_quar bt st Lc FF W s Hs); [rewrite Eu', En'; exact Hin |]. rewrite Eu, En. replace (m + 16 - 16) with m by lia. exact Hq.
        + clear - D. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sec_hdr_private : forall s a, In s (a_sec st) -> sc_map s <= a < sc_map s + 4096 -> rt_priv IA Lc FF a.
    Proof using IMGLO W qg qt.
      intros s a Hs Ha.
      pose proof (sec_geom s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      pose proof (fs_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as DF.
      apply (range_private (sc_map s) (sc_map s + 4096) a Ha G1 ltac:(clear - G2 G5; lia) ltac:(right; exact G9) ltac:(clear - G10 G5; lia) ltac:(clear - DF G5; lia)).
      intros p' n' lo' hi' Hin E.
      destruct E as [(HP' & -> & -> & CV' & HC' & LIV' & S1 & S2) | (HP' & sc & Hsc & Eu' & En' & -> & ->)].
      - clear - G11 G5 S1 S2. ulia.
      - destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [<- | D]; [left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | clear - D G5; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia].
    Qed.

    (* [comment removed for export] *)
    Lemma ptrarr_private : forall a, bt_ptrarr bt <= a < bt_ptrarr bt + 2 ^ 23 -> rt_priv IA Lc FF a.
    Proof using W qg qt st.
      intros a Ha. destruct (ptrarr_facts bt st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & P8).
      pose proof (fixed_members bt st Lc FF W) as (_ & IN8 & _).
      apply (range_private (bt_ptrarr bt) (bt_ptrarr bt + 2 ^ 23) a Ha D1 D3 D4 D5 (fs_vs_fixed bt st Lc FF W _ _ IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia))).
      intros p' n' lo' hi' Hin E. destruct (live_ext_vs_fixed bt st Lc FF W p' n' lo' hi' _ _ Hin E IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as [D | D]; [right; exact D | left; exact D].
    Qed.

    (* [comment removed for export] *)
    Lemma shadow_private_of : forall lo L z, lo mod 8 = 0 -> L mod 8 = 0 -> 0 <= lo -> lo + L <= CEIL ->
      (lo + L <= ia_img_lo IA \/ ia_img_hi IA <= lo) ->
      (forall a, lo <= a < lo + L -> ~ app_visible IA Lc FF a) ->
      sh_lo lo <= z < sh_lo lo + L / 8 -> rt_priv IA Lc FF z.
    Proof using IMGLO W qg qt st.
      intros lo L z Hlo HL HLO HHI HIM NV Hz. pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof ceil_rng as CR.
      unfold sh_lo in Hz.
      pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo. rewrite Hlo in Dlo. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL in DL.
      set (g := z - SB) in *. assert (Eg : z = SB + g) by ((lazymatch goal with |- ?G => let G' := eval unfold g in G in change_no_check G' end); lia).
      assert (G8 : lo <= 8 * g < lo + L) by lia.
      split; [ulia|]. split; [ulia|].
      intros [V | [V | [V | [V | [V | V]]]]].
      - destruct V as (p & n & Hin & Hr).
        pose proof W as (_ & _ & _ & _ & (WL & _) & _). destruct (WL p n Hin) as (_ & _ & (B1 & B2 & B3 & B4) & _). ulia.
      - destruct V as (f & k & Hf & Hr). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & INFS & _) & _).
        destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((D1 & D2 & D3 & D4 & D5) & _). ulia.
      - destruct V as (p & n & Hin & Hr). unfold sh_lo, sh_hi in Hr.
        destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4).
        apply (NV (8 * g) G8). left. exists p, n. split; [exact Hin|].
        pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. assert (P8 : p mod 8 = 0) by (clear -L4; Z.div_mod_to_equations; lia). rewrite P8 in Dp.
        assert (g < (p + n + 7) / 8) by lia. assert (p / 8 <= g) by lia.
        assert (8 * g + 8 <= p + n + 7) by (clear -H; Z.div_mod_to_equations; lia). lia.
      - destruct V as (f & k & Hf & Hr). unfold sh_lo, sh_hi in Hr.
        destruct (frame_gran bt st Lc FF W f k Hf) as [F8 K8].
        apply (NV (8 * g) G8). right; left. exists f, k. split; [exact Hf|].
        pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite F8 in Df.
        assert (g < (f + FS k + 7) / 8) by lia. assert (f / 8 <= g) by lia.
        assert (8 * g + 8 <= f + FS k + 7) by (clear -H; Z.div_mod_to_equations; lia). lia.
      - unfold in_stack_shadow, sh_lo in V. pose proof ceil_pg as CP.
        assert (CEIL / 8 <= g) by lia. assert (CEIL <= 8 * g) by (clear -H CP; Z.div_mod_to_equations; lia). lia.
      - unfold in_image_shadow, sh_lo, sh_hi in V.
        assert (g < (ia_img_lo IA + (ia_img_hi IA - ia_img_lo IA) + 7) / 8) by lia.
        assert (ia_img_lo IA / 8 <= g) by lia.
        assert (8 * g + 8 <= ia_img_hi IA + 7) by (clear -H; Z.div_mod_to_equations; lia).
        assert (ia_img_lo IA <= 8 * g + 7) by (clear -H0; Z.div_mod_to_equations; lia).
        clear - H1 H2 G8 HIM Dlo DL. lia.
    Qed.

    Lemma sec_quar_shadow_private : forall m n s z, In (m, n) (quar st) -> is_primary n = false -> In s (a_sec st) -> sc_user s = m + 16 -> sc_n s = n ->
      sh_lo (sc_map s) <= z < sh_lo (sc_map s) + sc_mapsz s / 8 -> rt_priv IA Lc FF z.
    Proof using IMGLO W qg qt.
      intros m n s z Hq HP Hs Eu En Hz.
      pose proof (sec_geom s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      apply (shadow_private_of (sc_map s) (sc_mapsz s) z); [clear - G3; Z.div_mod_to_equations; lia | clear - G4; Z.div_mod_to_equations; lia | lia | exact G2 | right; exact G9 | | exact Hz].
      intros a Ha. exact (proj2 (proj2 (sec_quar_private m n s a Hq HP Hs Eu En Ha))).
    Qed.
  End W.
End RcGS.
End BoAllocFRcGS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcS4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_um1 (mem : word -> option byte) (S ra0 s0v s1v s2v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v).
#[local] Hint Unfold fr_um1 : asfr.

Section UM1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v : word) (h msz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 h.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 msz.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 0.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hh : (1 <= h /\ 1 <= msz /\ h + msz < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2448)) 48 = true.

  Definition um1_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x82a28 /\ getr r 2 = at_ S (-2448)
      /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz /\ getr r 17 = Z_to_bv 64 215
      /\ getr r 8 = Z_to_bv 64 msz /\ getr r 9 = Z_to_bv 64 0 /\ getr r 18 = Z_to_bv 64 h
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma um1_run :
    exists r, msteps BSEGS (mkst regs (0x829f8 : word) mem rom) (mkst r (0x811b8 : word) (fr_um1 mem S ra0 s0v s1v s2v) rom)
      /\ um1_regs r.
  Proof using Hstk Hh HS H12 H11 H10 H18 H9 H8 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold um1_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_829f8 D_829f8.                              (* [comment removed for export] *)
      fsd F_829fc D_829fc (at_ S (-2408)).             (* [comment removed for export] *)
      fsd F_82a00 D_82a00 (at_ S (-2416)).             (* [comment removed for export] *)
      fsd F_82a04 D_82a04 (at_ S (-2424)).             (* [comment removed for export] *)
      fsd F_82a08 D_82a08 (at_ S (-2432)).             (* [comment removed for export] *)
      ab_ft F_82a0c D_82a0c ltac:(condz).              (* [comment removed for export] *)
      an F_82a10 D_82a10.                              (* [comment removed for export] *)
      ab_ft F_82a14 D_82a14 ltac:(condz).              (* [comment removed for export] *)
      an F_82a18 D_82a18.                              (* [comment removed for export] *)
      an F_82a1c D_82a1c.                              (* [comment removed for export] *)
      an F_82a20 D_82a20.                              (* [comment removed for export] *)
      an F_82a24 D_82a24.                              (* [comment removed for export] *)
      an F_811b4 D_811b4.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_um1 mem S ra0 s0v s1v s2v). wd_refl.
    - post.
  Qed.
End UM1.

(* [comment removed for export] *)
Definition fr_um2 (mem : word -> option byte) (S : word) : word -> option byte :=
  wbytes mem (at_ S (-2436)) (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
#[local] Hint Unfold fr_um2 : asfr.

Section UM2.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v : word) (msz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x82a28.
  Hypothesis H2 : getr regs 2 = at_ S (-2448).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 msz.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2448)) 48 = true.
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (0x19fce8 + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).

  Definition um2_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma um2_run :
    exists r, msteps BSEGS (mkst regs (0x811bc : word) mem rom) (mkst r ra0 (fr_um2 mem S) rom)
      /\ um2_regs r.
  Proof using Cs2 Cs1 Cs0 Cra Rlim Rgcf Hstk Hret HS H8 H10 H2 H1 msz.
    (lazymatch goal with |- ?G => let G' := eval unfold um2_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - rt F_811bc D_811bc.                              (* [comment removed for export] *)
      an F_82a28 D_82a28.                              (* [comment removed for export] *)
      an F_82a2c D_82a2c.                              (* [comment removed for export] *)
      fsw F_82a30 D_82a30 (at_ S (-2436)).             (* [comment removed for export] *)
      an F_82a34 D_82a34.                              (* [comment removed for export] *)
      an F_82a38 D_82a38.                              (* [comment removed for export] *)
      an F_81188 D_81188.                              (* [comment removed for export] *)
      an F_8118c D_8118c.                              (* [comment removed for export] *)
      ab_tk F_81190 D_81190 ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_811a0 D_811a0.                              (* [comment removed for export] *)
      rt F_811a4 D_811a4.                              (* [comment removed for export] *)
      ab_ft F_82a3c D_82a3c ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_82a40 D_82a40.                              (* [comment removed for export] *)
      an F_82a44 D_82a44.                              (* [comment removed for export] *)
      an F_7d0d0 D_7d0d0.                              (* [comment removed for export] *)
      cld8 F_7d0d4 D_7d0d4 (Z_to_bv 64 0x19fce8) Rgcf. (* [comment removed for export] *)
      cld8 F_7d0d8 D_7d0d8 (Z_to_bv 64 0) Rlim.        (* [comment removed for export] *)
      ab_tk F_7d0dc D_7d0dc ltac:(condz).              (* [comment removed for export] *)
      rt F_7d0f0 D_7d0f0.                              (* [comment removed for export] *)
      cld8 F_82a48 D_82a48 ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_82a4c D_82a4c s0v Cs0. cld8 F_82a50 D_82a50 s1v Cs1. cld8 F_82a54 D_82a54 s2v Cs2.
      an F_82a58 D_82a58.                              (* [comment removed for export] *)
      aret F_82a5c D_82a5c ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_um2 mem S). wd_refl.
    - post.
  Qed.
End UM2.
End FPGen.
End BoAllocFRcS4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcS6.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 BoAllocFRcS4.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Lemma at0_litS6 : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof. intros c Hc. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. reflexivity. Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_sB (Mb : word -> option byte) (S ra0 s0v s1v s2v : word) (T : Z) (j0 j1 : word) : word -> option byte :=
  let N1 := fr_sd3 Mb S in
  let N2 := wbytes N1 (at_ S (-2456)) (LE8 (Z_to_bv 64 0x78004)) in
  let N3 := fr_sd4 N2 T j0 j1 in
  fr_um1 N3 S ra0 s0v s1v s2v.

Section RUNSB.
  Variables (Mb rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v tp tsdp : word).
  Variables (T tctx h msz : Z) (bu0 bu1 : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation u0 := (Z_to_bv 64 (bytes_le_to_Z bu0)).
  #[local] Abbreviation u1 := (Z_to_bv 64 (bytes_le_to_Z bu1)).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = at_ S (-2432).
  Hypothesis H8 : getr r0 8 = Z_to_bv 64 h.
  Hypothesis H18 : getr r0 18 = Z_to_bv 64 msz.
  Hypothesis H4 : getr r0 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Gh : (AIMGHI <= h /\ 4096 <= msz /\ h + msz <= U S - 3584)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS Mb (at_ S (-2512)) 112 = true.
  Hypothesis OkT : store_ok BSEGS Mb (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_kif : rdn BSEGS Mb (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS Mb (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS Mb (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS Mb tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS Mb (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_u0 : rdn BSEGS Mb (Z_to_bv 64 (T + 2888)) 8 = Some bu0.
  Hypothesis L_u0 : length bu0 = 8%nat.
  Hypothesis C_u1 : rdn BSEGS Mb (Z_to_bv 64 (T + 2896)) 8 = Some bu1.
  Hypothesis L_u1 : length bu1 = 8%nat.
  Hypothesis C_mbh : rdn BSEGS Mb (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis C_msz : rdn BSEGS Mb (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis C_ra : rdn BSEGS Mb (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis C_s0 : rdn BSEGS Mb (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis C_s1 : rdn BSEGS Mb (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis C_s2 : rdn BSEGS Mb (at_ S (-2432)) 8 = Some (LE8 s2v).

  Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  (* [comment removed for export] *)
  Ltac gl G := clear - G; unfold hideW in G; lia.
  Ltac gl0 G := clear - G; unfold hideW in G; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  (* [comment removed for export] *)
  Ltac xq G Q H :=
    eapply rd_same; [ intros x Hx; apply Q; clear - G Hx; unfold hideW in G; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | clear - G; unfold hideW in G; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
  Ltac rch := repeat (first [ reflexivity | assumption
                            | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
  Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold gct_clob in G in change_no_check G' end); notin)); rch.
  (* [comment removed for export] *)
  Ltac outwg GX :=
    rewrite !wbytes_outside;
    [ | (wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - GX; unfold hideW in GX;
         first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ]) .. ].
  Ltac sokstk Mx GR G := eapply (store_ok_sub BSEGS Mx (at_ S (-2512)) _ 112);
    [ clear - G; unfold hideW in G; rewrite at_u; lia | first [exact Hstk | eapply store_ok_mono; [exact GR | exact Hstk]]
    | clear - G; unfold hideW in G; rewrite ?at_at, !at_u; lia | clear - G; unfold hideW in G; rewrite ?at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].

  Theorem run_sB :
    exists r, msteps BSEGS (mkst r0 (0x4ef70 : word) Mb rom)
                           (mkst r (0x811b8 : word) (fr_sB Mb S ra0 s0v s1v s2v T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz))) rom)
      /\ um1_regs S h msz r0 r /\ getr r 4 = tp.
  Proof using C_s2 C_s1 C_s0 C_ra C_msz C_mbh L_u1 C_u1 L_u0 C_u0 C_thr C_tctx C_tsdp C_key C_kif OkT Hstk Gtsdp Gtp Gctx GT Gh GS H4 H18 H8 H2 tctx tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr.
    destruct GS as (GS1 & GS2). destruct Gh as (Gh1 & Gh4 & Gh5). destruct GT as (GT1 & (GTS & GT2)). destruct Gctx as (Gc1 & Gc2).
    pose proof (conj HSr (conj Htpr (conj Htsr (conj GS1 (conj GS2 (conj Gh1 (conj Gh4 (conj Gh5 (conj GT1 (conj GT2 (conj Gc1 (conj Gc2 (conj Gtp Gtsdp))))))))))))) as G0.
    hidehypW G0.
    pose proof (conj G0 GTS) as G0T. hidehypW G0T.
    (* [comment removed for export] *)
    destruct (sd3_run Mb rom S r0 H2 ltac:(gl G0) ltac:(sokstk Mb GR1 G0))
      as (r1 & RUN1 & W1 & W2 & W3 & W4 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
    assert (GR1 : mem_grows Mb (fr_sd3 Mb S)) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_sd3 in G in change_no_check G' end); grows_tac).
    assert (Q1 : forall x : word, ((U x < U S - 2440)%Z \/ (U S - 2432 <= U x)%Z) -> fr_sd3 Mb S x = Mb x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_sd3 in G in change_no_check G' end). intros x Hx. pose proof (conj G0 Hx) as GX. outwg GX. reflexivity. }
    assert (RA1 : rdn BSEGS (fr_sd3 Mb S) (at_ S (-2440)) 8 = Some (LE8 (Z_to_bv 64 0x4ef74))) by (clear - GS1 GS2 HSr; (lazymatch goal with |- ?G => let G' := eval unfold fr_sd3 in G in change_no_check G' end); rd_hit8).
    remember (fr_sd3 Mb S) as N1 eqn:EN1 in RUN1, GR1, Q1, RA1.
    (* [comment removed for export] *)
    assert (RET_G : ret_ok (Z_to_bv 64 0x78004)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (V4 : getr r1 4 = tp) by (rewrite W4; exact H4).
    assert (GH : gctH BSEGS both_gct_tab N1 (at_ S (-2448)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq G0 Q1 C_kif. - xq G0 Q1 C_key. - xq G0 Q1 C_tsdp. - xq G0 Q1 C_tctx. - xq G0 Q1 C_thr.
      - clear - Gc1 Gc2 HSr. unorm. lia.
      - rewrite at_at. sokstk N1 GR1 G0.
      - gl0 G0. - gl0 G0. - gl0 G0. - gl0 G0. - gl0 G0. }
    destruct (gct_run BSEGS both_gct_tab both_gct_tab_ok N1 rom r1 (Z_to_bv 64 0x78004) (at_ S (-2448)) tp tsdp ctxw thr GH RET_G W1 W2 V4)
      as (r2 & RUN2 & X10 & X11 & AGX).
    cbn [gt_rb both_gct_tab] in RUN2. rewrite at0_litS6 in RUN2 by lia. rewrite at_at in RUN2. change (-2448 + -8)%Z with (-2456)%Z in RUN2.
    assert (GR2 : mem_grows Mb (wbytes N1 (at_ S (-2456)) (LE8 (Z_to_bv 64 0x78004)))) by (eapply mem_grows_trans; [exact GR1|]; grows_tac).
    assert (Q2 : forall x : word, ((U x < U S - 2456)%Z \/ (U S - 2432 <= U x)%Z) -> wbytes N1 (at_ S (-2456)) (LE8 (Z_to_bv 64 0x78004)) x = Mb x).
    { intros x Hx. pose proof (conj G0 Hx) as GX. outwg GX. apply Q1; gl GX. }
    assert (RA2 : rdn BSEGS (wbytes N1 (at_ S (-2456)) (LE8 (Z_to_bv 64 0x78004))) (at_ S (-2440)) 8 = Some (LE8 (Z_to_bv 64 0x4ef74))).
    { rewrite rdn_wbytes_out; [ exact RA1 | clear - GS1 GS2 HSr; rd8_side | clear - GS1 GS2 HSr; rd8_side | clear - GS1 GS2 HSr; rd8_side ]. }
    remember (wbytes N1 (at_ S (-2456)) (LE8 (Z_to_bv 64 0x78004))) as N2 eqn:EN2 in RUN2, GR2, Q2, RA2.
    assert (Y2 : getr r2 2 = at_ S (-2448)) by viac AGX (2:reg).
    assert (Y8 : getr r2 8 = Z_to_bv 64 h) by viac AGX (8:reg).
    assert (Y18 : getr r2 18 = Z_to_bv 64 msz) by viac AGX (18:reg).
    (* [comment removed for export] *)
    destruct (sd4_run N2 rom S ra0 s0v s1v s2v T h msz bu0 bu1 r2 Y2 X10 Y8 Y18
                ltac:(gl G0) ltac:(split; [exact GT1 | split; [exact GTS | exact GT2]]) ltac:(gl G0) RA2
                ltac:(xq G0T Q2 C_u0) L_u0 ltac:(xq G0T Q2 C_u1) L_u1
                ltac:(eapply (store_ok_sub BSEGS N2 (Z_to_bv 64 T) _ (Z.to_nat 4096)); [clear - GT1 GT2 HSr; wd_ulia | eapply store_ok_mono; [exact GR2 | exact OkT] | clear - GT1 GT2 HSr; wd_ulia | clear - GT1 GT2 HSr; wd_ulia_c])
                ltac:(xq G0 Q2 C_mbh) ltac:(xq G0 Q2 C_msz) ltac:(xq G0 Q2 C_ra) ltac:(xq G0 Q2 C_s0) ltac:(xq G0 Q2 C_s1) ltac:(xq G0 Q2 C_s2))
      as (r3 & RUN3 & Z1 & Z2 & Z10 & Z11 & Z12 & Z8 & Z9 & Z18 & Z3 & Z4 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    assert (GR3 : mem_grows Mb (fr_sd4 N2 T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz)))) by (eapply mem_grows_trans; [exact GR2|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_sd4 in G in change_no_check G' end); grows_tac).
    remember (fr_sd4 N2 T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz))) as N3 eqn:EN3 in RUN3, GR3.
    (* [comment removed for export] *)
    destruct (um1_run N3 rom S ra0 s0v s1v s2v h msz r3 Z1 Z2 Z8 Z9 Z18 Z10 Z11 Z12 ltac:(gl G0) ltac:(gl G0) ltac:(sokstk N3 GR3 G0))
      as (r4 & RUN4 & UR).
    exists r4. split.
    { replace (0x78004 : word) with (Z_to_bv 64 0x78004 : word) in RUN3 by (apply bv_eq; reflexivity).
      replace (0x78e2c : word) with (Z_to_bv 64 0x78e2c : word) in RUN1 by (apply bv_eq; reflexivity).
      subst N3 N2 N1. (lazymatch goal with |- ?G => let G' := eval unfold fr_sB in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4]. }
    unfold um1_regs in *. destruct UR as (U1 & U2 & U10 & U11 & U17 & U8 & U9 & U18 & U3 & U4 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & U26 & U27).
    assert (R4c : getr r4 4 = tp) by (rewrite U4, Z4; viac AGX (4:reg)).
    split; [| exact R4c].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - rewrite U3, Z3. viac AGX (3:reg).
    - rewrite U4, Z4. viac AGX (4:reg).
    - rewrite U19, Z19. viac AGX (19:reg).
    - rewrite U20, Z20. viac AGX (20:reg).
    - rewrite U21, Z21. viac AGX (21:reg).
    - rewrite U22, Z22. viac AGX (22:reg).
    - rewrite U23, Z23. viac AGX (23:reg).
    - rewrite U24, Z24. viac AGX (24:reg).
    - rewrite U25, Z25. viac AGX (25:reg).
    - rewrite U26, Z26. viac AGX (26:reg).
    - rewrite U27, Z27. viac AGX (27:reg).
  Qed.
End RUNSB.
End FPGen.
End BoAllocFRcS6.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcSN.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Lemma katD_ecall_munmap : forall (segs : list Segment) regs (pc : word) mem rom model w (a : word) (len : Z) (Q : config -> Prop),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> U a mod 4096 = 0 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len -> len mod 4096 = 0 ->
  U a + len <= 2 ^ 47 ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 len) = true ->
  katD segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a (Z_to_bv 64 len) mem) rom)
                   (munmap_model a (Z_to_bv 64 len) model)) Q ->
  katD segs (mkCfg (mkst regs pc mem rom) model) Q.
Proof using.
  intros segs regs pc mem rom model w a len Q HF HE Hh H17 H10 Hal H11 Hlen Hlm Hce Hhas Hk.
  pose proof (u64_range a) as Ra.
  assert (Hpr : page_round_up_Z len = len) by (apply page_round_up_Z_aligned; [lia | exact Hlm]).
  apply (katD_ecall segs regs pc mem rom model w Q Hh HF HE). rewrite H17.
  set (ms := epend regs pc mem rom (Z_to_bv 64 215)).
  assert (E0 : ms_gpr ms 0 = a) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact H10).
  assert (E1 : ms_gpr ms 1 = Z_to_bv 64 len) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1; exact H11).
  assert (Hu1 : U (ms_gpr ms 1) = len) by (rewrite E1; apply u_Z2bv; lia).
  assert (Hprw : page_round_up (ms_gpr ms 1) = Z_to_bv 64 len) by ((lazymatch goal with |- ?G => let G' := eval unfold page_round_up in G in change_no_check G' end); rewrite Hu1, Hpr; reflexivity).
  apply (katD_munmap segs ms model (Z_to_bv 64 215) Q Hh eq_refl).
  { rewrite u_Z2bv by lia. reflexivity. }
  { (lazymatch goal with |- ?G => let G' := eval unfold munmap_args_ok in G in change_no_check G' end). rewrite E0, Hu1, Hprw, Hpr. split; [exact Hal|]. split.
    - intros Hz. rewrite E1 in Hz. apply (f_equal bv_unsigned) in Hz. rewrite u_Z2bv in Hz by lia. change (U (Z_to_bv 64 0)) with 0 in Hz. lia.
    - split; [(lazymatch goal with |- ?G => let G' := eval unfold TASK_SIZE in G in change_no_check G' end); lia | exact Hhas]. }
  (lazymatch goal with |- ?G => let G' := eval unfold munmap_eff in G in change_no_check G' end). rewrite E0, Hprw. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_unmaps1_epend. exact Hk.
Qed.
End FPGen.

(* [comment removed for export] *)
Lemma z2bv_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma lzb_of_iff : forall (l l' : list (word * word)),
  (forall a, pg_in_ivz l' a <-> pg_in_ivz l a) ->
  forall a, page_in_ranges (page_base (Z_to_bv 64 a)) l' = page_in_ranges (page_base (Z_to_bv 64 a)) l.
Proof.
  intros l l' IFF a. rewrite <- (z2bv_mod a). pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as R.
  specialize (IFF (a mod 2 ^ 64)). unfold pg_in_ivz in IFF.
  destruct (page_in_ranges (page_base (Z_to_bv 64 (a mod 2 ^ 64))) l') eqn:E1; destruct (page_in_ranges (page_base (Z_to_bv 64 (a mod 2 ^ 64))) l) eqn:E2; try reflexivity.
  - exfalso. destruct (proj1 IFF (conj R eq_refl)) as [_ X]. discriminate X.
  - exfalso. destruct (proj2 IFF (conj R eq_refl)) as [_ X]. discriminate X.
Qed.
Lemma lazy_cover_of_iff : forall (Hd : word -> bool) (l l' : list (word * word)) (A : list (Z * Z)),
  (forall a, pg_in_ivz l' a <-> pg_in_ivz l a) -> lazy_cover Hd l A -> lazy_cover Hd l' A.
Proof.
  intros Hd l l' A IFF LC w Hw Hh. apply (LC w); [| exact Hh].
  rewrite <- (Z_to_bv_bv_unsigned 64 w) in Hw |- *. rewrite (lzb_of_iff l l' IFF) in Hw. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac rd1 := intros m; (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end); match goal with |- context [m ?a] => destruct (m a) as [b|]; [exists b; reflexivity|] end; vm_compute; wd_eexists; reflexivity.
Lemma rdn1_ex_10ae41 : forall m : mem, exists b, rdn BSEGS m (Z_to_bv 64 0x10ae01) 1 = Some [b]. Proof. rd1. Qed.
Lemma rdn1_ex_10ae42 : forall m : mem, exists b, rdn BSEGS m (Z_to_bv 64 0x10ae02) 1 = Some [b]. Proof. rd1. Qed.
Lemma rdn1_ex_10ae43 : forall m : mem, exists b, rdn BSEGS m (Z_to_bv 64 0x10ae03) 1 = Some [b]. Proof. rd1. Qed.

(* [comment removed for export] *)
Lemma rdn8_ex_img : forall (m : mem) (a : Z),
  (forall k, 0 <= k < 8 -> seg_rom BSEGS (Z_to_bv 64 (a + k)) <> None) -> 0 <= a -> a + 8 < 2 ^ 64 ->
  exists bs, rdn BSEGS m (Z_to_bv 64 a) 8 = Some bs /\ length bs = 8%nat.
Proof.
  intros m a ROM Ha Hb.
  assert (G : forall (n : nat) (c : Z), a <= c -> c + Z.of_nat n <= a + 8 -> exists bs, rdn BSEGS m (Z_to_bv 64 c) n = Some bs /\ length bs = n).
  { induction n as [|n IH]; intros c Hc1 Hc2; [exists []; split; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    assert (B : exists b, match m (Z_to_bv 64 c) with Some b => Some b | None => seg_rom BSEGS (Z_to_bv 64 c) end = Some b).
    { destruct (m (Z_to_bv 64 c)) as [b|]; [exists b; reflexivity|]. pose proof (ROM (c - a) ltac:(lia)) as X. replace (a + (c - a)) with c in X by lia.
      destruct (seg_rom BSEGS (Z_to_bv 64 c)) as [b|]; [exists b; reflexivity | exfalso; exact (X eq_refl)]. }
    destruct B as (b & ->).
    replace ((Z_to_bv 64 c + 1)%bv) with (Z_to_bv 64 (c + 1) : word) by (apply bv_eq; rewrite u_add1 by (wd_ulia); wd_ulia).
    destruct (IH (c + 1) ltac:(lia) ltac:(lia)) as (bs & -> & L). exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
  exact (G 8%nat a ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
Qed.
Ltac rom8 := intros k Hk; assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia;
             destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
Lemma rdn8_ex_10ac28 : forall m : mem, exists bs, rdn BSEGS m (Z_to_bv 64 (0x10ab98 + 80)) 8 = Some bs /\ length bs = 8%nat.
Proof. intros m. apply rdn8_ex_img; [rom8 | lia | lia]. Qed.
Lemma rdn8_ex_10ac30 : forall m : mem, exists bs, rdn BSEGS m (Z_to_bv 64 (0x10ab98 + 88)) 8 = Some bs /\ length bs = 8%nat.
Proof. intros m. apply rdn8_ex_img; [rom8 | lia | lia]. Qed.
Lemma rdn8_ex_10ae58 : forall m : mem, exists bs, rdn BSEGS m (Z_to_bv 64 (0x10ab58 + 688 + 16)) 8 = Some bs /\ length bs = 8%nat.
Proof. intros m. apply rdn8_ex_img; [rom8 | lia | lia]. Qed.
Lemma rdn8_ex_10ae60 : forall m : mem, exists bs, rdn BSEGS m (Z_to_bv 64 (0x10ab58 + 688 + 24)) 8 = Some bs /\ length bs = 8%nat.
Proof. intros m. apply rdn8_ex_img; [rom8 | lia | lia]. Qed.
End BoAllocFRcSN.
Require Stdlib.Logic.FunctionalExtensionality OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcSU.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRcS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRcS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 BoAllocFRcS4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS5 BoAllocFRcS6.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
#[local] Ltac lia ::= (Zify.zify; xlia zchecker).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma wb_mr : forall (Hd : word -> bool) (m : word -> option byte) (a : word) bs (lo n : Z),
  hid_off Hd lo n -> (lo <= U a)%Z -> (U a + Z.of_nat (length bs) <= lo + n)%Z -> (U a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  wbytes (mrestrict Hd m) a bs = mrestrict Hd (wbytes m a bs).
Proof using. intros Hd m a bs lo n HO H1 H2 H3. apply wbytes_mrestrict; [exact H3 | intros x Hx; apply HO; lia]. Qed.

Lemma munrestrict_same : forall (Hd : word -> bool) (M M' : word -> option byte),
  (forall a, Hd a = true -> M' a = M a) -> munrestrict Hd M (mrestrict Hd M') = M'.
Proof using.
  intros Hd M M' E. apply functional_extensionality. intros a. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict, mrestrict in G in change_no_check G' end).
  destruct (Hd a) eqn:Ha; [symmetry; apply E; exact Ha | reflexivity].
Qed.

Ltac side := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ].
Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.

Lemma shad_h : forall (S : word) (h msz : Z), (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z ->
  (AIMGHI <= h /\ h mod 8 = 0 /\ msz mod 8 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584)%Z ->
  shad (Z_to_bv 64 h) = (0x7fff8000 + h / 8)%Z /\ shlen (Z_to_bv 64 msz) = (msz / 8)%Z /\ (0 <= msz / 8)%Z /\ (0x7fff8000 + h / 8 + msz / 8 <= 2 ^ 47)%Z.
Proof using.
  intros S h msz GS Gh. pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
  (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). unorm. repeat split; [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section A.
  Variables (M : word -> option byte).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 cbp : word) (b1 b2 b3 : byte) (m T h msz len ptr i last : Z) (j0 j1 wnf wca w16 w24 : word).
  #[local] Abbreviation shlo := (0x7fff8000 + h / 8)%Z.
  #[local] Abbreviation FA Mx := (fr_sA Mx S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gh : (AIMGHI <= h /\ h mod 8 = 0 /\ msz mod 8 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584)%Z.
  Hypothesis Gi : (0 <= i < len /\ len <= 2 ^ 20)%Z.
  Hypothesis Gptr : (AIMGHI <= ptr /\ ptr + 8 * len <= U S - 3584)%Z.
  Hypothesis Glast : (AIMGHI <= last /\ last + 32 <= U S - 3584)%Z.


  (* [comment removed for export] *)
  Definition outA (x : word) : Prop :=
    ((U x < U S - 2496)%Z \/ (U S - 2400 <= U x)%Z) /\ ((U x < 0x10ab98 + 56)%Z \/ (0x10ab58 + 688 + 32 <= U x)%Z)
    /\ ((U x < T + 2840)%Z \/ (T + 2856 <= U x)%Z) /\ ((U x < ptr + 8 * i)%Z \/ (ptr + 8 * i + 8 <= U x)%Z)
    /\ ((U x < last + 24)%Z \/ (last + 32 <= U x)%Z) /\ ((U x < shlo)%Z \/ (shlo + msz / 8 <= U x)%Z).

  Lemma fr_sA_out : forall x, outA x -> FA M x = M x.
  Proof using Glast Gptr Gi Gh GT GS. clear - Glast Gptr Gi Gh GT GS.
    intros x (O1 & O2 & O3 & O4 & O5 & O6).
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_sA, fr_ks1, fr_gbb0, fr_gbb1, fr_k3, fr_k4, fr_sd1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite repeat_length, SH1, SH2; unorm; rewrite Z2Nat.id by lia; lia | rewrite repeat_length, SH1, SH2; unorm; rewrite Z2Nat.id by lia; lia].
    rewrite !at_at. rewrite !wbytes_outside; [reflexivity | side ..].
  Qed.

  Lemma fr_sA_grows : mem_grows M (FA M).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_sA, fr_ks1, fr_gbb0, fr_gbb1, fr_k3, fr_k4, fr_sd1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). grows_tac. Qed.

  (* [comment removed for export] *)
  Hypothesis GlastH : (last = h \/ last + 32 <= h \/ h + msz <= last)%Z.
  Hypothesis GptrL : (ptr + 8 * len <= last \/ last + 32 <= ptr)%Z.
  Hypothesis Gsh : (shlo + msz / 8 <= AIMGLO \/ AIMGHI <= shlo)%Z.       (* [comment removed for export] *)
  Hypothesis GshS : (shlo + msz / 8 <= U S - 3584)%Z.
  Hypothesis GshP : (shlo + msz / 8 <= ptr \/ ptr + 8 * len <= shlo)%Z.
  Hypothesis GshL : (shlo + msz / 8 <= last \/ last + 32 <= shlo)%Z.

  Ltac peel_top SH1 SH2 :=
    (lazymatch goal with |- ?G => let G' := eval unfold fr_sA in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
    rewrite rdn_wbytes_out; [ | rewrite ?repeat_length, ?SH1, ?SH2; unorm; rewrite ?Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ..];
    (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end); rewrite !at_at;
    repeat (rewrite wc_rdn_wbytes_out3; [ | side ]).

  Lemma fr_sA_frame :
    rdn BSEGS (FA M) (at_ S (-2408)) 8 = Some (LE8 ra0) /\ rdn BSEGS (FA M) (at_ S (-2416)) 8 = Some (LE8 s0v)
    /\ rdn BSEGS (FA M) (at_ S (-2424)) 8 = Some (LE8 s1v) /\ rdn BSEGS (FA M) (at_ S (-2432)) 8 = Some (LE8 s2v).
  Proof using GshS Glast Gptr Gi Gh GT GS. clear - GshS Glast Gptr Gi Gh GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    repeat split; peel_top SH1 SH2; (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end); repeat (wd_rdstep side).
  Qed.

  Lemma fr_sA_nch : rdn BSEGS (FA M) (Z_to_bv 64 (0x10ab98 + 56)) 8 = Some (LE8 (Z_to_bv 64 (len - 1))).
  Proof using GshS Gsh Glast Gptr Gi Gh GT GS. clear - GshS Gsh Glast Gptr Gi Gh GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    peel_top SH1 SH2. (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end). repeat (wd_rdstep side).
  Qed.

  Lemma fr_sA_lock : rdn BSEGS (FA M) (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0].
  Proof using GshS Gsh Glast Gptr Gi Gh GT GS. clear - GshS Gsh Glast Gptr Gi Gh GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    peel_top SH1 SH2. (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end).
    apply (rdn_wbytes_hit BSEGS [Z_to_bv 8 0] _ (Z_to_bv 64 0x10ae00)). unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  Qed.

  Lemma fr_sA_slot : rdn BSEGS (FA M) (Z_to_bv 64 (ptr + 8 * i)) 8 = Some (LE8 (Z_to_bv 64 last)).
  Proof using GshL GshP GshS GptrL Glast Gptr Gi Gh GT GS. clear - GshL GshP GshS GptrL Glast Gptr Gi Gh GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    peel_top SH1 SH2. (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end). repeat (wd_rdstep side).
  Qed.

  Lemma fr_sA_idx : rdn BSEGS (FA M) (Z_to_bv 64 (last + 24)) 8 = Some (LE8 (Z_to_bv 64 i)).
  Proof using GshL GshS Glast Gptr Gi Gh GT GS. clear - GshL GshS Glast Gptr Gi Gh GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    peel_top SH1 SH2. (lazymatch goal with |- ?G => let G' := eval unfold fr_sd1 in G in change_no_check G' end). repeat (wd_rdstep side).
  Qed.
End A.

Section AMR.
  Variables (Hd : word -> bool) (M : word -> option byte).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 cbp : word) (b1 b2 b3 : byte) (m T h msz len ptr i last : Z) (j0 j1 wnf wca w16 w24 : word).
  #[local] Abbreviation shlo := (0x7fff8000 + h / 8)%Z.
  #[local] Abbreviation FA Mx := (fr_sA Mx S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gh : (AIMGHI <= h /\ h mod 8 = 0 /\ msz mod 8 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584)%Z.
  Hypothesis Gi : (0 <= i < len /\ len <= 2 ^ 20)%Z.
  Hypothesis Gptr : (AIMGHI <= ptr /\ ptr + 8 * len <= U S - 3584)%Z.
  Hypothesis Glast : (AIMGHI <= last /\ last + 32 <= U S - 3584)%Z.

  (* [comment removed for export] *)
  Hypothesis HOstk : hid_off Hd (U S - 2512) 112.
  Hypothesis HOinst : hid_off Hd 0x10ab98 656.
  Hypothesis HOT : hid_off Hd (T + 2840) 16.
  Hypothesis HOslot : hid_off Hd (ptr + 8 * i) 8.
  Hypothesis HOlast : hid_off Hd (last + 24) 8.
  Hypothesis HOsh : hid_off Hd shlo (msz / 8).

  Lemma fr_sA_mr : FA (mrestrict Hd M) = mrestrict Hd (FA M).
  Proof using HOsh HOlast HOslot HOT HOinst HOstk Glast Gptr Gi Gh GT GS. clear - HOsh HOlast HOslot HOT HOinst HOstk Glast Gptr Gi Gh GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    destruct Gi as (Gi1 & Gi2). destruct Gptr as (Gp1 & Gp2). destruct Glast as (Gl1 & Gl2). destruct (shad_h S h msz GS Gh) as (SH1 & SH2 & SH3 & SH4).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_sA, fr_ks1, fr_gbb0, fr_gbb1, fr_k3, fr_k4, fr_sd1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    (* [comment removed for export] *)
    do 6 (rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side).
    do 4 (rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side).
    do 2 (rewrite (wb_mr Hd _ _ _ _ _ HOinst) by side).
    do 2 (rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side).
    do 2 (rewrite (wb_mr Hd _ _ _ _ _ HOT) by side).
    (* [comment removed for export] *)
    do 4 (rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side).
    do 5 (rewrite (wb_mr Hd _ _ _ _ _ HOinst) by side).
    rewrite (wb_mr Hd _ _ _ _ _ HOslot) by side.
    rewrite (wb_mr Hd _ _ _ _ _ HOlast) by side.
    do 3 (rewrite (wb_mr Hd _ _ _ _ _ HOinst) by side).
    (* [comment removed for export] *)
    rewrite ps_frame_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply HOstk; lia].
    rewrite (wb_mr Hd _ _ _ _ _ HOsh); [reflexivity | | | ]; rewrite ?repeat_length, SH1, ?SH2; unorm; rewrite ?Z2Nat.id by lia; lia.
  Qed.

End AMR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section B.
  Variables (Hd : word -> bool) (Mb : word -> option byte).
  Variables (S ra0 s0v s1v s2v : word) (T : Z) (j0 j1 : word).
  #[local] Abbreviation FB Mx := (fr_sB Mx S ra0 s0v s1v s2v T j0 j1).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis HOstk : hid_off Hd (U S - 2512) 112.
  Hypothesis HOT : hid_off Hd (T + 2888) 16.

  Lemma fr_sB_mr : FB (mrestrict Hd Mb) = mrestrict Hd (FB Mb).
  Proof using HOT HOstk GT GS. clear - HOT HOstk GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_sB, fr_sd3, fr_sd4, fr_um1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    do 2 (rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side).
    do 2 (rewrite (wb_mr Hd _ _ _ _ _ HOT) by side).
    do 4 (rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side).
    reflexivity.
  Qed.

  Lemma fr_sB_out : forall x, ((U x < U S - 2456)%Z \/ (U S - 2400 <= U x)%Z) -> ((U x < T + 2888)%Z \/ (T + 2904 <= U x)%Z) -> FB Mb x = Mb x.
  Proof using GT GS. clear - GT GS.
    intros x O1 O2. pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_sB, fr_sd3, fr_sd4, fr_um1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite !wbytes_outside; [reflexivity | side ..].
  Qed.

  Lemma fr_sB_grows : mem_grows Mb (FB Mb).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_sB, fr_sd3, fr_sd4, fr_um1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). grows_tac. Qed.

  Lemma fr_sB_frame :
    rdn BSEGS (FB Mb) (at_ S (-2408)) 8 = Some (LE8 ra0) /\ rdn BSEGS (FB Mb) (at_ S (-2416)) 8 = Some (LE8 s0v)
    /\ rdn BSEGS (FB Mb) (at_ S (-2424)) 8 = Some (LE8 s1v) /\ rdn BSEGS (FB Mb) (at_ S (-2432)) 8 = Some (LE8 s2v).
  Proof using GS. clear - GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_sB, fr_um1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). repeat split; repeat (wd_rdstep side).
  Qed.

  Lemma fr_um2_mr : forall Mc, fr_um2 (mrestrict Hd Mc) S = mrestrict Hd (fr_um2 Mc S).
  Proof using HOstk GS. clear - HOstk GS.
    intros Mc. pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold fr_um2 in G in change_no_check G' end).
    rewrite (wb_mr Hd _ _ _ _ _ HOstk) by side. reflexivity.
  Qed.
  Lemma fr_um2_out : forall Mc x, ((U x < U S - 2436)%Z \/ (U S - 2432 <= U x)%Z) -> fr_um2 Mc S x = Mc x.
  Proof using GS. clear - GS.
    intros Mc x O1. pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold fr_um2 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | side ..].
  Qed.
  Lemma fr_um2_grows : forall Mc, mem_grows Mc (fr_um2 Mc S).
  Proof using. intros Mc. (lazymatch goal with |- ?G => let G' := eval unfold fr_um2 in G in change_no_check G' end). grows_tac. Qed.
End B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wview_local : forall segs (m m' : word -> option byte) x, (m x <> None -> m' x <> None) -> wview segs m x <> None -> wview segs m' x <> None.
Proof using.
  intros segs m m' x Hg Hx. unfold wview in *. destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm; [exfalso; apply Hg; [discriminate | reflexivity] | exact Hx].
Qed.
Lemma store_ok_local : forall segs n (m m' : word -> option byte) (a : word),
  (U a + Z.of_nat n <= 2 ^ 64)%Z -> (forall x : word, (U a <= U x < U a + Z.of_nat n)%Z -> m x <> None -> m' x <> None) ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof using.
  intros segs n; induction n as [|n IH]; intros m m' a Hnw Hg H; [reflexivity|].
  cbn [store_ok] in *. pose proof (u64_range a) as Ha.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - destruct n as [|n']; [reflexivity|].
    assert (Hu1 : U (a + 1) = (U a + 1)%Z) by (apply u_add1; lia).
    apply (IH m m'); [rewrite Hu1; lia | intros x Hx; apply Hg; rewrite Hu1 in Hx; lia | exact H].
  - exfalso. apply (wview_local segs m m' a); [apply Hg; lia | rewrite Hv; discriminate | exact Hv'].
Qed.

Section FIN.
  Variables (M : word -> option byte).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 cbp : word) (b1 b2 b3 : byte) (m T h msz len ptr i last : Z) (j0 j1 wnf wca w16 w24 k0 k1 : word) (pb l : Z).
  #[local] Abbreviation shlo := (0x7fff8000 + h / 8)%Z.
  #[local] Abbreviation FA Mx := (fr_sA Mx S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24).
  #[local] Abbreviation FB Mx := (fr_sB Mx S ra0 s0v s1v s2v T k0 k1).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gh : (AIMGHI <= h /\ h mod 8 = 0 /\ msz mod 8 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584)%Z.
  Hypothesis Gi : (0 <= i < len /\ len <= 2 ^ 20)%Z.
  Hypothesis Gptr : (AIMGHI <= ptr /\ ptr + 8 * len <= U S - 3584)%Z.
  Hypothesis Glast : (AIMGHI <= last /\ last + 32 <= U S - 3584)%Z.
  Hypothesis GshS : (shlo + msz / 8 <= U S - 3584)%Z.
  Hypothesis Gpb : (shlo <= pb /\ pb + l <= shlo + msz / 8 /\ 0 <= l)%Z.
  (* [comment removed for export] *)
  Hypothesis GlastH : hideW (last = h \/ last + 32 <= h \/ h + msz <= last)%Z.
  Hypothesis GptrL : hideW (ptr + 8 * len <= last \/ last + 32 <= ptr)%Z.
  Hypothesis GptrH : hideW (ptr + 8 * len <= h \/ h + msz <= ptr)%Z.
  Hypothesis GTi : hideW (T + 4096 <= AIMGLO \/ AIMGHI <= T)%Z.
  Hypothesis GptrT : hideW (ptr + 8 * len <= T \/ T + 4096 <= ptr)%Z.
  Hypothesis GlastT : hideW (last + 32 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Gsh : hideW (shlo + msz / 8 <= AIMGLO \/ AIMGHI <= shlo)%Z.
  Hypothesis GshP : hideW (shlo + msz / 8 <= ptr \/ ptr + 8 * len <= shlo)%Z.
  Hypothesis GshL : hideW (shlo + msz / 8 <= last \/ last + 32 <= shlo)%Z.

  (* [comment removed for export] *)
  Ltac feed H := repeat (let T := type of H in lazymatch T with ?A -> _ => let a := fresh in assert (a : A) by (first [assumption | unfold hideW in *; assumption]); specialize (H a); clear a end).
  Ltac gl G := clear - G; unfold hideW in G; lia.

  Definition mz_mem : word -> option byte :=
    zfill (Z_to_bv 64 pb) (Z_to_bv 64 l) (fl_frame (FA M) (at_ S (-2432)) (Z_to_bv 64 0x4ef70) (Z_to_bv 64 h) (Z_to_bv 64 h) (Z_to_bv 64 msz)).
  Definition mu_mem : word -> option byte := unfill (Z_to_bv 64 h) (Z_to_bv 64 msz) (FB mz_mem).
  Definition fin_mem : word -> option byte := fr_um2 mu_mem S.

  Lemma fin_lits : (0 <= U S < 2 ^ 64 /\ U (at_ S (-2432)) = U S - 2432 /\ U (Z_to_bv 64 pb) = pb /\ U (Z_to_bv 64 l) = l /\ U (Z_to_bv 64 h) = h /\ U (Z_to_bv 64 msz) = msz
                    /\ 0 <= h / 8 /\ 0 <= msz / 8 /\ shlo + msz / 8 <= 2 ^ 47)%Z.
  Proof using Gpb Gh GS. clear - Gpb Gh GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5). destruct Gpb as (P1 & P2 & P3).
    assert (D : (0 <= h / 8 /\ 0 <= msz / 8 /\ shlo + msz / 8 <= 2 ^ 47)%Z) by (clear - HSr GS2 Gh1 Gh4 Gh5; Z.div_mod_to_equations; lia).
    destruct D as (D1 & D2 & D3). clear - HSr GS1 GS2 Gh1 Gh4 Gh5 P1 P2 P3 D1 D2 D3. rewrite at_u by lia. unorm. repeat split; lia.
  Qed.

  Lemma mz_vsA : forall x, ((U x < U S - 2464)%Z \/ (U S - 2432 <= U x)%Z) -> ((U x < pb)%Z \/ (pb + l <= U x)%Z) -> mz_mem x = FA M x.
  Proof using Gpb Gh GS. clear - Gpb Gh GS.
    intros x O1 O2. destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold mz_mem in G in change_no_check G' end).
    rewrite zfill_out by (rewrite L2, L3; exact O2). apply fl_frame_out; rewrite L1; clear - O1 L0 GS1; lia.
  Qed.
  Lemma mz_out : forall x, outA S T h msz ptr i last x -> mz_mem x = M x.
  Proof using Gpb Glast Gptr Gi Gh GT GS. clear - Gpb Glast Gptr Gi Gh GT GS.
    intros x OA. pose proof OA as (O1 & O2 & O3 & O4 & O5 & O6). destruct Gpb as (P1 & P2 & P3).
    pose proof (fr_sA_out M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F.
    rewrite mz_vsA; [exact (F x OA) | clear - O1; lia | clear - O6 P1 P2 P3; lia].
  Qed.
  Lemma mz_grows : mem_grows M mz_mem.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold mz_mem, zfill in G in change_no_check G' end). eapply mem_grows_trans; [| apply zmem_grows]. eapply mem_grows_trans; [| apply fl_frame_grows]. apply fr_sA_grows.
  Qed.
  Ltac rd_via G L := eapply rd_same; [ intros x Hx; apply L; clear - G Hx; unfold hideW in G; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | clear - G; unfold hideW in G; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
  Lemma mz_frame :
    rdn BSEGS mz_mem (at_ S (-2408)) 8 = Some (LE8 ra0) /\ rdn BSEGS mz_mem (at_ S (-2416)) 8 = Some (LE8 s0v)
    /\ rdn BSEGS mz_mem (at_ S (-2424)) 8 = Some (LE8 s1v) /\ rdn BSEGS mz_mem (at_ S (-2432)) 8 = Some (LE8 s2v).
  Proof using Gpb GshS Glast Gptr Gi Gh GT GS. clear - Gpb GshS Glast Gptr Gi Gh GT GS.
    pose proof (fr_sA_frame M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F. destruct F as (F1 & F2 & F3 & F4).
    destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    pose proof (conj L0 (conj GS (conj GshS Gpb))) as G.
    repeat split; [rd_via G mz_vsA; exact F1 | rd_via G mz_vsA; exact F2 | rd_via G mz_vsA; exact F3 | rd_via G mz_vsA; exact F4].
  Qed.

  Lemma mu_vsB : forall x, ((U x < h)%Z \/ (h + msz <= U x)%Z) -> mu_mem x = FB mz_mem x.
  Proof using Gpb Gh GS. clear - Gpb Gh GS. intros x O. destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). (lazymatch goal with |- ?G => let G' := eval unfold mu_mem in G in change_no_check G' end). apply unfill_out. rewrite L4, L5. exact O. Qed.
  Lemma mu_frame :
    rdn BSEGS mu_mem (at_ S (-2408)) 8 = Some (LE8 ra0) /\ rdn BSEGS mu_mem (at_ S (-2416)) 8 = Some (LE8 s0v)
    /\ rdn BSEGS mu_mem (at_ S (-2424)) 8 = Some (LE8 s1v) /\ rdn BSEGS mu_mem (at_ S (-2432)) 8 = Some (LE8 s2v).
  Proof using Gpb Gh GS. clear - Gpb Gh GS.
    pose proof (fr_sB_frame mz_mem S ra0 s0v s1v s2v T k0 k1) as F. feed F. destruct F as (F1 & F2 & F3 & F4).
    destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    pose proof (conj L0 (conj GS Gh)) as G.
    repeat split; [rd_via G mu_vsB; exact F1 | rd_via G mu_vsB; exact F2 | rd_via G mu_vsB; exact F3 | rd_via G mu_vsB; exact F4].
  Qed.
  Lemma mu_out : forall x, outA S T h msz ptr i last x -> ((U x < T + 2888)%Z \/ (T + 2904 <= U x)%Z) -> ((U x < h)%Z \/ (h + msz <= U x)%Z) -> mu_mem x = M x.
  Proof using Gpb Glast Gptr Gi Gh GT GS. clear - Gpb Glast Gptr Gi Gh GT GS.
    intros x OA O7 O8. pose proof OA as (O1 & O2 & O3 & O4 & O5 & O6).
    rewrite mu_vsB by exact O8. pose proof (fr_sB_out mz_mem S ra0 s0v s1v s2v T k0 k1) as FBO. feed FBO.
    rewrite FBO; [apply mz_out; exact OA | clear - O1; lia | exact O7].
  Qed.
  Lemma mu_stk : store_ok BSEGS M (at_ S (-2512)) 112 = true -> store_ok BSEGS mu_mem (at_ S (-2512)) 112 = true.
  Proof using Gpb Gh GS. clear - Gpb Gh GS.
    intros OK. destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct GS as (GS1 & GS2). destruct Gh as (Gh1 & Gh2 & Gh3 & Gh4 & Gh5).
    apply (store_ok_local BSEGS 112 M mu_mem); [clear - L0 GS1; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | | exact OK].
    intros x Hx NN. rewrite at_u in Hx by (clear - L0 GS1; lia). rewrite mu_vsB by (clear - Hx Gh5 L0; lia).
    apply (fr_sB_grows mz_mem). apply mz_grows. exact NN.
  Qed.

  Lemma fin_vsA : forall x, ((U x < U S - 2464)%Z \/ (U S - 2400 <= U x)%Z) -> ((U x < T + 2888)%Z \/ (T + 2904 <= U x)%Z) ->
    ((U x < pb)%Z \/ (pb + l <= U x)%Z) -> ((U x < h)%Z \/ (h + msz <= U x)%Z) -> fin_mem x = FA M x.
  Proof using Gpb Gh GT GS. clear - Gpb Gh GT GS.
    intros x O1 O2 O3 O4. (lazymatch goal with |- ?G => let G' := eval unfold fin_mem in G in change_no_check G' end). pose proof (fr_um2_out S) as FUO. feed FUO. rewrite FUO by (clear - O1; lia). rewrite mu_vsB by exact O4.
    pose proof (fr_sB_out mz_mem S ra0 s0v s1v s2v T k0 k1) as FBO. feed FBO.
    rewrite FBO; [apply mz_vsA; [clear - O1; lia | exact O3] | clear - O1; lia | exact O2].
  Qed.
  Lemma fin_out : forall x, outA S T h msz ptr i last x -> ((U x < T + 2888)%Z \/ (T + 2904 <= U x)%Z) -> ((U x < h)%Z \/ (h + msz <= U x)%Z) -> fin_mem x = M x.
  Proof using Gpb Glast Gptr Gi Gh GT GS. clear - Gpb Glast Gptr Gi Gh GT GS.
    intros x OA O7 O8. pose proof OA as (O1 & O2 & O3 & O4 & O5 & O6). destruct Gpb as (P1 & P2 & P3).
    pose proof (fr_sA_out M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F.
    rewrite fin_vsA; [exact (F x OA) | clear - O1; lia | exact O7 | clear - O6 P1 P2 P3; lia | exact O8].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_def : forall x, fin_mem x <> M x -> fin_mem x <> None \/ (h <= U x < h + msz)%Z.
  Proof using Gpb Gh GS. clear - Gpb Gh GS.
    intros x NE.
    assert (D : (h <= U x < h + msz)%Z \/ ((U x < h)%Z \/ (h + msz <= U x)%Z)) by (clear; lia). destruct D as [D | D]; [right; exact D|].
    left. intros E. apply NE. rewrite E. destruct (M x) eqn:EM; [| reflexivity]. exfalso.
    assert (NN : M x <> None) by (rewrite EM; discriminate).
    apply mz_grows in NN. apply (fr_sB_grows mz_mem S ra0 s0v s1v s2v T k0 k1) in NN. rewrite <- (mu_vsB x D) in NN.
    apply (fr_um2_grows S mu_mem) in NN. exact (NN E).
  Qed.

  (* [comment removed for export] *)
  Lemma fin_foot : forall x, fin_mem x <> M x ->
    (U S - 2496 <= U x < U S - 2400)%Z \/ (0x10ab98 + 56 <= U x < 0x10ab58 + 688 + 32)%Z \/ (T + 2840 <= U x < T + 2856)%Z \/ (T + 2888 <= U x < T + 2904)%Z
    \/ (ptr + 8 * i <= U x < ptr + 8 * i + 8)%Z \/ (last + 24 <= U x < last + 32)%Z \/ (shlo <= U x < shlo + msz / 8)%Z \/ (h <= U x < h + msz)%Z.
  Proof using Gpb Glast Gptr Gi Gh GT GS. clear - Gpb Glast Gptr Gi Gh GT GS.
    intros x NE.
    assert (D1 : (U S - 2496 <= U x < U S - 2400)%Z \/ ((U x < U S - 2496)%Z \/ (U S - 2400 <= U x)%Z)) by (clear; lia). destruct D1 as [D1 | D1]; [left; exact D1|].
    assert (D2 : (0x10ab98 + 56 <= U x < 0x10ab58 + 688 + 32)%Z \/ ((U x < 0x10ab98 + 56)%Z \/ (0x10ab58 + 688 + 32 <= U x)%Z)) by (clear; lia). destruct D2 as [D2 | D2]; [do 1 right; left; exact D2|].
    assert (D3 : (T + 2840 <= U x < T + 2856)%Z \/ ((U x < T + 2840)%Z \/ (T + 2856 <= U x)%Z)) by (clear; lia). destruct D3 as [D3 | D3]; [do 2 right; left; exact D3|].
    assert (D4 : (T + 2888 <= U x < T + 2904)%Z \/ ((U x < T + 2888)%Z \/ (T + 2904 <= U x)%Z)) by (clear; lia). destruct D4 as [D4 | D4]; [do 3 right; left; exact D4|].
    assert (D5 : (ptr + 8 * i <= U x < ptr + 8 * i + 8)%Z \/ ((U x < ptr + 8 * i)%Z \/ (ptr + 8 * i + 8 <= U x)%Z)) by (clear; lia). destruct D5 as [D5 | D5]; [do 4 right; left; exact D5|].
    assert (D6 : (last + 24 <= U x < last + 32)%Z \/ ((U x < last + 24)%Z \/ (last + 32 <= U x)%Z)) by (clear; lia). destruct D6 as [D6 | D6]; [do 5 right; left; exact D6|].
    assert (D7 : (shlo <= U x < shlo + msz / 8)%Z \/ ((U x < shlo)%Z \/ (shlo + msz / 8 <= U x)%Z)) by (clear; lia). destruct D7 as [D7 | D7]; [do 6 right; left; exact D7|].
    assert (D8 : (h <= U x < h + msz)%Z \/ ((U x < h)%Z \/ (h + msz <= U x)%Z)) by (clear; lia). destruct D8 as [D8 | D8]; [do 7 right; exact D8|].
    exfalso. apply NE. apply fin_out; [(lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end); repeat split; assumption | exact D4 | exact D8].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_nch : rdn BSEGS fin_mem (Z_to_bv 64 (0x10ab98 + 56)) 8 = Some (LE8 (Z_to_bv 64 (len - 1))).
  Proof using Gsh GTi Gpb GshS Glast Gptr Gi Gh GT GS. clear - Gsh GTi Gpb GshS Glast Gptr Gi Gh GT GS.
    pose proof (fr_sA_nch M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F.
    destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    pose proof (conj L0 (conj GS (conj GT (conj Gh (conj Gpb (conj GTi Gsh)))))) as G.
    rd_via G fin_vsA. exact F.
  Qed.
  Lemma fin_lock : rdn BSEGS fin_mem (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0].
  Proof using Gsh GTi Gpb GshS Glast Gptr Gi Gh GT GS. clear - Gsh GTi Gpb GshS Glast Gptr Gi Gh GT GS.
    pose proof (fr_sA_lock M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F.
    destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    pose proof (conj L0 (conj GS (conj GT (conj Gh (conj Gpb (conj GTi Gsh)))))) as G.
    rd_via G fin_vsA. exact F.
  Qed.
  Lemma fin_slot : rdn BSEGS fin_mem (Z_to_bv 64 (ptr + 8 * i)) 8 = Some (LE8 (Z_to_bv 64 last)).
  Proof using GshL GshP GptrT GptrH GptrL Gpb GshS Glast Gptr Gi Gh GT GS. clear - GshL GshP GptrT GptrH GptrL Gpb GshS Glast Gptr Gi Gh GT GS.
    pose proof (fr_sA_slot M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F.
    destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    pose proof (conj L0 (conj GS (conj GT (conj Gh (conj Gpb (conj Gi (conj Gptr (conj GptrT (conj GshP GptrH))))))))) as G.
    rd_via G fin_vsA. exact F.
  Qed.
  Lemma fin_idx : last <> h -> rdn BSEGS fin_mem (Z_to_bv 64 (last + 24)) 8 = Some (LE8 (Z_to_bv 64 i)).
  Proof using GshL GlastT GlastH Gpb GshS Glast Gptr Gi Gh GT GS. clear - GshL GlastT GlastH Gpb GshS Glast Gptr Gi Gh GT GS.
    intros NEh. pose proof (fr_sA_idx M S ra0 s0v s1v s2v s3v s4v x21 cbp b1 b2 b3 m T h msz len ptr i last j0 j1 wnf wca w16 w24) as F. feed F.
    destruct fin_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    pose proof (conj L0 (conj GS (conj GT (conj Gh (conj Gpb (conj Glast (conj GlastT (conj GshL (conj GlastH NEh))))))))) as G.
    rd_via G fin_vsA. exact F.
  Qed.
End FIN.
End FPGen.
End BoAllocFRcSU.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI.AsRtFlushK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI.BoRtFlushI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRcS1 BoAllocFRcS4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS5 BoAllocFRcS6 BoAllocFRcSU BoAllocFRcSN.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53.AsAinvRelease3.   (* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94.AsAinvOpsRc63 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG BoAllocFRcGS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH BoAllocFRcHS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI.   (* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma cellM : forall (M M0 : mem) (X : Z -> Prop) a n v,
  cellZ BSEGS M0 a n v -> (forall x : word, ~ X (U x) -> M x = M0 x) ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall z, a <= z < a + Z.of_nat n -> ~ X z) ->
  rdn BSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros M M0 X a n v C EQ Ha Hn OFF. eapply rd_same; [| wd_ulia | exact C].
  intros x Hx. apply EQ. revert Hx. unorm. intros Hx. exact (OFF (U x) Hx).
Qed.


(* [comment removed for export] *)
Lemma rdRw : forall (Hd : word -> bool) (M M' : mem) (a : word) n bs,
  rdn BSEGS M a n = Some bs -> U a + Z.of_nat n < 2 ^ 64 ->
  (forall x : word, U a <= U x < U a + Z.of_nat n -> M' x = M x) ->
  (forall z, U a <= z < U a + Z.of_nat n -> Hd (Z_to_bv 64 z) = false) ->
  rdn BSEGS (mrestrict Hd M') a n = Some bs.
Proof.
  intros Hd M M' a n bs C Hn AG OFF. pose proof (u64_range a) as Ha.
  rewrite rdn_mrestrict; [| lia | apply hid_off_of; intros z Hz; split; [lia | exact (OFF z Hz)]].
  eapply rd_same; [| lia | exact C]. intros x Hx. apply AG. exact Hx.
Qed.
Lemma rdn4_of_bytesS : forall (m : mem) (a : word) x0 x1 x2 x3,
  (bv_unsigned a + 4 < 2 ^ 64)%Z ->
  rdn BSEGS m a 1 = Some [x0] -> rdn BSEGS m (at_ a 1) 1 = Some [x1] -> rdn BSEGS m (at_ a 2) 1 = Some [x2] -> rdn BSEGS m (at_ a 3) 1 = Some [x3] ->
  rdn BSEGS m a 4 = Some [x0; x1; x2; x3].
Proof.
  intros m a x0 x1 x2 x3 Hnw H0 H1 H2 H3. pose proof (u64_range a) as Ha.
  change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))). change 4%nat with (1 + (1 + (1 + 1)))%nat.
  apply rdn_cat; [exact H0 | | lia]. apply rdn_cat; [exact H1 | | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
  rewrite at_at. apply rdn_cat; [exact H2 | | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. rewrite at_at. exact H3.
Qed.

Lemma out_of_hidden : forall (Hd : word -> bool) lo n (a : word), hid_off Hd lo n -> Hd a = true -> U a < lo \/ lo + n <= U a.
Proof.
  intros Hd lo n a HO Ha. destruct (Z_lt_le_dec (U a) lo) as [C|C]; [left; exact C|]. destruct (Z_lt_le_dec (U a) (lo + n)) as [D|D]; [|right; exact D].
  exfalso. rewrite (HO a) in Ha by lia. discriminate Ha.
Qed.

Lemma munmap_except_vm : forall a n m, same_except_vm m (munmap_model a n m).
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sh_split : forall h msz, h mod 8 = 0 -> msz mod 8 = 0 -> 0 <= h -> 0 <= msz -> (h + msz + 7) / 8 = h / 8 + msz / 8 /\ 8 * (h / 8) = h /\ 8 * (msz / 8) = msz.
Proof. intros. lia. Qed.
Lemma pg_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KS.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation P8 := (bt_ptrarr bt).

  Ltac gl G := clear - G; unfold hideW in G; lia.

  Theorem rc_item_sec_pf : rc_item_stmt bt FXOK arm_sec.
  Proof using SHGATE BOOTG HTP SECC RCC CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_item_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest HFX HH MW W RX EGQ HP XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R4 CCB S16 Slo Shi SOK _.
    unfold arm_sec in HP.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    (* [comment removed for export] *)
    set (s0v := getr R 8) in *. set (s1v := getr R 9) in *. set (s2v := getr R 18) in *. set (s3v := getr R 19) in *. set (s4v := getr R 20) in *.
    set (x21 := getr R 21) in *. set (tpv := getr R 4) in *.
    set (cbw := at_ S (-2392)) in *.                                             (* [comment removed for export] *)
    assert (PC0 : (0x4e8a4%bv : word) = Z_to_bv 64 0x4e8a4) by (apply bv_eq; reflexivity).
    assert (PC1 : (0x4ef70%bv : word) = Z_to_bv 64 0x4ef70) by (apply bv_eq; reflexivity).
    assert (PC2 : v_addi (0x811b8%bv : word) 4 = Z_to_bv 64 0x811bc) by (apply bv_eq; reflexivity).
    assert (PC3 : (0x811bc%bv : word) = Z_to_bv 64 0x811bc) by (apply bv_eq; reflexivity).
    assert (PCF : (0x6ea68%bv : word) = ft_base both_flush_tab) by reflexivity.
    destruct RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct RCC as (CELL_rib & CELL_magic & G_tsdp).
    destruct SECC as (CELL_spg & CELL_chk & CELL_gpgc & CELL_pgc & CELL_seal & CELL_lim & CELL_thr & G_tsdp2).
    unfold free_cells_nb in CELLNB.
    (* [comment removed for export] *)
    assert (Hq : In (m, n) (quar st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply in_flat_map. exists (BATCH ba ((m, n) :: its)). split; [apply in_app_iff; right; rewrite EGQ; left; reflexivity | left; reflexivity]. }
    assert (IMGLO : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    destruct (sec_item_idx bt st Lc FF W m n Hq HP) as (i & s & Hnth & Hs & Eus & Ens).
    pose proof (sec_geom bt st Lc FF W IMGLO s Hs) as G. cbv zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
    assert (Hlen : (i < length (a_sec st))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
    destruct (nth_error (a_sec st) (length (a_sec st) - 1)) as [sl|] eqn:Hnl; [| exfalso; apply nth_error_None in Hnl; lia].
    assert (Hsl : In sl (a_sec st)) by exact (nth_error_In _ _ Hnl).
    pose proof (sec_geom bt st Lc FF W IMGLO sl Hsl) as GL. cbv zeta in GL.
    destruct GL as (L1 & L2 & L3 & L4 & L5 & _ & _ & _ & L9 & L10 & L11 & L12 & L13 & L14).
    pose proof (sec_cases bt st Lc FF W s sl Hs Hsl) as SCS.
    pose proof (ptrarr_geom bt st Lc FF W IMGLO) as (PG1 & PG2 & PG3 & PG4 & PG5 & PG6 & PG7 & PG8).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    rewrite BT_ia in GTI, GCI, G9, L9, PG1. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, G9, L9, PG1.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold KSPACE, PG, AS_HEAPLO, AS_LO, NMAX, PTRHI in *.
    remember (sc_map s) as h eqn:Eh. remember (sc_mapsz s) as msz eqn:Emsz. remember (sc_map sl) as last eqn:Elast. remember (sc_mapsz sl) as lsz eqn:Elsz.
    set (len := Z.of_nat (length (a_sec st))) in *. set (iz := Z.of_nat i) in *.
    assert (Em : sc_user s = m + 16) by exact Eus.
    rewrite Em in G6, G7. rewrite Ens in G7, G8.
    assert (T4 : 4096 <= T) by (clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    set (shlo := 0x7fff8000 + h / 8).
    destruct (sh_split h msz (pg_mod8 h G3) (pg_mod8 msz G4) ltac:(clear - G1; lia) ltac:(clear - G5; lia)) as (SHs & SH8h & SH8m).
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256) by (clear - Slo Shi CR; lia).       (* [comment removed for export] *)
    assert (P_GT : 4096 <= T /\ T + 4096 <= U S - 3584) by (clear - T4 GTC Slo; lia).
    assert (P_Gh8 : AIMGHI <= h /\ h mod 8 = 0 /\ msz mod 8 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584).
    { split; [exact G9|]. split; [exact (pg_mod8 h G3)|]. split; [exact (pg_mod8 msz G4)|]. clear - G5 G2 Slo. lia. }
    assert (P_Gi : 0 <= iz < len /\ len <= 2 ^ 20) by ((lazymatch goal with |- ?G => let G' := eval unfold iz, len in G in change_no_check G' end); clear - Hlen PG8; lia).
    assert (P_Gptr : AIMGHI <= P8 /\ P8 + 8 * len <= U S - 3584) by (clear - PG1 PG2 PG8 Slo; unfold len in *; lia).
    assert (P_Glast : AIMGHI <= last /\ last + 32 <= U S - 3584) by (clear - L9 L2 L5 Slo; lia).
    assert (P_GshS : shlo + msz / 8 <= U S - 3584) by ((lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end); clear - SH8h SH8m G2 Slo CR; lia).
    assert (P_GlastH : hideW (last = h \/ last + 32 <= h \/ h + msz <= last)).
    { (lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end). destruct SCS as [<- | [D | D]]; [left; rewrite Eh, Elast; reflexivity | right; right; clear - D; lia | right; left; clear - D L5; lia]. }
    assert (P_GptrL : hideW (P8 + 8 * len <= last \/ last + 32 <= P8)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - L14 L5 PG8; unfold len in *; lia).
    assert (P_GptrH : hideW (P8 + 8 * len <= h \/ h + msz <= P8)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - G14 PG8; unfold len in *; lia).
    assert (P_GTi : hideW (T + 4096 <= AIMGLO \/ AIMGHI <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI; lia).
    assert (P_GptrT : hideW (P8 + 8 * len <= T \/ T + 4096 <= P8)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - PG6 PG8; unfold len in *; lia).
    assert (P_GlastT : hideW (last + 32 <= T \/ T + 4096 <= last)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - L12 L5; lia).
    assert (SHB : (0x7fff8000 <= shlo /\ shlo + msz / 8 <= 0x8fff7000) \/ (0x2008fff7000 <= shlo /\ shlo + msz / 8 <= 0x10007fff8000)).
    { (lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end). clear - G10 G1 G5 G2 CR SH8h SH8m. lia. }
    assert (P_Gsh : hideW (shlo + msz / 8 <= AIMGLO \/ AIMGHI <= shlo)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - SHB; lia).
    assert (P_GshP : hideW (shlo + msz / 8 <= P8 \/ P8 + 8 * len <= shlo)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - SHB PG4 PG8; unfold len in *; lia).
    assert (P_GshL : hideW (shlo + msz / 8 <= last \/ last + 32 <= shlo)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - SHB L10 L5; lia).
    (* [comment removed for export] *)
    pose proof RP as (Rc & Ri & Rt & _ & _ & _ & Rsec & Rh & _ & _ & _ & _ & R13 & R14 & _ & _ & Csb & _ & SHM0).
    first [pose proof (proj1 SHM0) as SHM | pose proof SHM0 as SHM]. clear SHM0.          (* [comment removed for export] *)
    rewrite BT_ia in Csb. cbn [ia_rtc_sb both_addrs] in Csb.
    destruct Ri as (_ & Inch & Ilock & _ & _ & _ & _ & Ichunks & Iptrw).
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & _ & TW & Tback & _).
    destruct (Rsec i s Hnth) as (Hmap & Hsz & _ & Hidx & Hwr).
    destruct (Rsec _ sl Hnl) as (_ & _ & _ & _ & Lwr).
    destruct Rh as [_ RHQ]. destruct (RHQ m n Hq) as [(_ & _ & Hnhi & Hnlo & _) _].
    destruct R14 as (B1 & B2 & _ & _ & _ & BSS & _ & _ & B9).          (* [comment removed for export] *)
    rewrite BT_segs in *. unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold T_PC, PC_SZ, sh_lo, sh_hi, SB, PG in *.
    rewrite <- Eh in Hmap, Hsz, Hidx, Hwr. rewrite <- Emsz in Hsz, Hwr. rewrite <- Elast, <- Elsz in Lwr.
    replace (m + 16 - 14) with (m + 2) in Hnhi by lia. replace (m + 16 - 12) with (m + 4) in Hnlo by lia.
    (* [comment removed for export] *)
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    assert (XIMG : forall z, z < 0x10ab58 + 888 \/ (0x10ab58 + 920 <= z /\ z < AIMGHI) -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia]. }
    assert (XSTK : forall z, CEIL <= z -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q CR; lia | clear - Hz Q SB1; lia]. }
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SPC.
    unfold KSPACE, PG in SPT, SPC.
    assert (XT : forall z, T <= z < T + 4096 -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI; lia | clear - Hz Q SPT; lia]. }
    assert (XC : forall z, CTX <= z < CTX + 65536 -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GCI; lia | clear - Hz Q SPC; lia]. }
    assert (XH : forall z, h <= z < h + msz -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q G9; lia | clear - Hz Q G11; lia]. }
    assert (XL : forall z, last <= z < last + lsz -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q L9; lia | clear - Hz Q L11; lia]. }
    assert (XP : forall z, P8 <= z < P8 + 2 ^ 23 -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q PG1; lia | clear - Hz Q PG5; lia]. }
    assert (XSH : forall z, shlo <= z < shlo + msz / 8 -> ~ X z).
    { intros z Hz Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SHB; lia | clear - Hz Q SHB SBH; lia]. }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC : forall z, CTX <= z < CTX + 65536 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHH : forall z, h <= z < h + msz -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz G1 G2 CR; lia|]. apply (rep_nolazy_sec bt st Lc FF M0 mdl W RP s z Hs). rewrite <- Eh, <- Emsz. exact Hz. }
    assert (NHL : forall z, last <= z < last + lsz -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz L1 L2 CR; lia|]. apply (rep_nolazy_sec bt st Lc FF M0 mdl W RP sl z Hsl). rewrite <- Elast, <- Elsz. exact Hz. }
    assert (NHP : forall z, P8 <= z < P8 + 8 * len -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz PG1 PG2 PG8 CR; unfold len in *; lia|]. apply (rep_nolazy_ptrarr bt st Lc FF M0 mdl W RP). clear - Hz PG8. unfold len in *. lia. }
    assert (NHSH : forall z, shlo <= z < shlo + msz / 8 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply (BSS s Hs). rewrite <- Eh, <- Emsz. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). rewrite SHs. unfold shlo in Hz. clear - Hz. lia. }
    (* [comment removed for export] *)
    hidehypW G10. hidehypW G11. hidehypW G12. hidehypW G13. hidehypW G14. hidehypW L10. hidehypW L11. hidehypW L12. hidehypW L13. hidehypW L14.
    hidehypW PG4. hidehypW PG5. hidehypW PG6. hidehypW PG7. hidehypW GTI. hidehypW GTB. hidehypW GCI. hidehypW GCB. hidehypW GCT'. hidehypW SCS.
    hidehypW SPT. hidehypW SPC. hidehypW SHB. hidehypW G_tsdp. hidehypW G_tsdp2.
    Ltac ul := unfold hideW in *; lia.
    (* [comment removed for export] *)
    Ltac czl := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) | lia ].
    Ltac cimgM M M0 X Rc EQ0 XIMG C := apply (cellM M M0 X _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply XIMG; clear - Hz; lia].
    assert (C_spb : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by cimgM M M0 X Rc EQ0 XIMG CELLNB.
    assert (C_pg : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by cimgM M M0 X Rc EQ0 XIMG CELL_spg.
    assert (C_ptr : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 P8))) by cimgM M M0 X Rc EQ0 XIMG CELL_chk.
    assert (C_gsh : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by cimgM M M0 X Rc EQ0 XIMG CELL_gsh.
    assert (C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by cimgM M M0 X Rc EQ0 XIMG CELL_gmb.
    assert (C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by cimgM M M0 X Rc EQ0 XIMG CELL_mb.
    assert (C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by cimgM M M0 X Rc EQ0 XIMG CELL_gme.
    assert (C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by cimgM M M0 X Rc EQ0 XIMG CELL_me.
    assert (C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by cimgM M M0 X Rc EQ0 XIMG CELL_ghe.
    assert (C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by cimgM M M0 X Rc EQ0 XIMG CELL_he.
    assert (C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by cimgM M M0 X Rc EQ0 XIMG CELL_grm.
    assert (C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by cimgM M M0 X Rc EQ0 XIMG CELL_rm.
    assert (C_gcf : rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by cimgM M M0 X Rc EQ0 XIMG CELL_gcf.
    assert (C_thr64 : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615))) by cimgM M M0 X Rc EQ0 XIMG CELL_thr.
    assert (C_lim : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 144)) 8 = Some (LE8 (Z_to_bv 64 0))) by cimgM M M0 X Rc EQ0 XIMG CELL_lim.
    assert (C_gpgc : rdn BSEGS M (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))) by cimgM M M0 X Rc EQ0 XIMG CELL_gpgc.
    assert (C_pgc : rdn BSEGS M (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))) by cimgM M M0 X Rc EQ0 XIMG CELL_pgc.
    assert (C_seal : rdn BSEGS M (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1))) by cimgM M M0 X Rc EQ0 XIMG CELL_seal.
    assert (C_sh : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { apply (cellM M M0 X _ _ _ Csb EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply XIMG; clear - Hz; lia]. }
    assert (C_kif : rdn BSEGS M (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- w2b1 by (clear; lia). cimgM M M0 X Rc EQ0 XIMG CELL_kif. }
    assert (C_key : rdn BSEGS M (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). cimgM M M0 X Rc EQ0 XIMG CELL_key. }
    subst TP. cbn [ia_tp both_addrs] in CELL_tsdp, Gc9, Gc10.
    assert (Utp : U tpv = 0x641380) by (rewrite R4; vm_compute; reflexivity).
    assert (C_tsdp : rdn BSEGS M (at_ tpv (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tpv (-88)) with (Z_to_bv 64 (0x641380 - 88) : word) by (clear - Utp; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
      cimgM M M0 X Rc EQ0 XIMG CELL_tsdp. }
    assert (C_tctx : rdn BSEGS M (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (cellM M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELL_tctx) EQ0); [clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XIMG. clear - Hz G_tsdp Gc1 Gc2. ul. }
    assert (C_thr : rdn BSEGS M (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152) : word) by (clear - GC0 GCC CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (cellM M M0 X _ _ _ Tback EQ0); [clear - GC0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XC. clear - Hz. lia. }
    assert (Hrng : 0 <= h /\ h + msz < 2 ^ 64) by (clear - G1 G2 CR; lia).
    assert (C_mbh : rdn BSEGS M (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h))).
    { apply (cellM M M0 X _ _ _ Hmap EQ0); [clear - Hrng; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XH. clear - Hz G5. lia. }
    assert (C_msz : rdn BSEGS M (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))).
    { apply (cellM M M0 X _ _ _ Hsz EQ0); [clear - Hrng; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XH. clear - Hz G5. lia. }
    assert (C_idx : rdn BSEGS M (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 iz))).
    { apply (cellM M M0 X _ _ _ Hidx EQ0); [clear - Hrng; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XH. clear - Hz G5. lia. }
    assert (C_nhi : rdn BSEGS M (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { apply (cellM M M0 X _ _ _ Hnhi EQ0); [clear - Hrng G6; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G6 G7 G8; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XH. clear - Hz G6 G7 G8. lia. }
    assert (C_nlo : rdn BSEGS M (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))).
    { apply (cellM M M0 X _ _ _ Hnlo EQ0); [clear - Hrng G6; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G6 G7 G8; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XH. clear - Hz G6 G7 G8. lia. }
    assert (C_n : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 len))).
    { apply (cellM M M0 X _ _ _ Inch EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply XIMG; clear - Hz; lia]. }
    assert (C_hs : forall j x, nth_error (map sc_map (a_sec st)) j = Some x -> rdn BSEGS M (Z_to_bv 64 (P8 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 x))).
    { intros j x Hj. rewrite nth_error_map in Hj. destruct (nth_error (a_sec st) j) as [sj|] eqn:Ej; [| discriminate Hj]. injection Hj as <-.
      assert (Lj : (j < length (a_sec st))%nat) by (apply nth_error_Some; rewrite Ej; discriminate).
      apply (cellM M M0 X _ _ _ (Ichunks j sj Ej) EQ0); [clear - PG1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - PG2 CR Lj PG8; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XP. clear - Hz Lj PG8. lia. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    assert (Utsdp : U (Z_to_bv 64 TSDP) = TSDP) by (clear - Gc1 Gc2; unorm; reflexivity).
    assert (Uctx152 : U (at_ (Z_to_bv 64 CTX) 152) = CTX + 152) by (clear - GC0 GCC CR; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
    assert (Utp88 : U (at_ tpv (-88)) = 0x641380 - 88) by (clear - Utp; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
    assert (Ukey : U (at_ (Z_to_bv 64 0x10da20) 4) = 0x10da24) by (clear; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity).
    Ltac toD_img Hd M NHs C := apply (rdRw Hd M M _ _ _ C); [unorm; czl | intros x _; reflexivity | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by toD_img Hd M NHs C_spb.
    assert (K_pg : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by toD_img Hd M NHs C_pg.
    assert (K_ptr : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 P8))) by toD_img Hd M NHs C_ptr.
    assert (K_n : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 len))) by toD_img Hd M NHs C_n.
    assert (K_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by toD_img Hd M NHs C_gsh.
    assert (K_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))) by toD_img Hd M NHs C_sh.
    assert (K_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by toD_img Hd M NHs C_gmb.
    assert (K_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by toD_img Hd M NHs C_mb.
    assert (K_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by toD_img Hd M NHs C_gme.
    assert (K_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by toD_img Hd M NHs C_me.
    assert (K_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by toD_img Hd M NHs C_ghe.
    assert (K_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by toD_img Hd M NHs C_he.
    assert (K_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by toD_img Hd M NHs C_grm.
    assert (K_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by toD_img Hd M NHs C_rm.
    assert (K_gcf : rdn BSEGS memD (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by toD_img Hd M NHs C_gcf.
    assert (K_thr64 : rdn BSEGS memD (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615))) by toD_img Hd M NHs C_thr64.
    assert (K_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by toD_img Hd M NHs C_kif.
    assert (K_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { apply (rdRw Hd M M _ _ _ C_key); [rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x _; reflexivity | rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (K_tsdp : rdn BSEGS memD (at_ tpv (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { apply (rdRw Hd M M _ _ _ C_tsdp); [rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x _; reflexivity | rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (K_tctx : rdn BSEGS memD (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (rdRw Hd M M _ _ _ C_tctx); [rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia | intros x _; reflexivity | rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]]. }
    assert (K_thr : rdn BSEGS memD (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { apply (rdRw Hd M M _ _ _ C_thr); [rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia | intros x _; reflexivity | rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHC; clear - Hz; lia]. }
    Ltac toD_h Hd M NHH G C := apply (rdRw Hd M M _ _ _ C); [clear - G; wd_ulia_c | intros x _; reflexivity | rewrite u_Z2bv by (clear - G; lia); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHH; clear - Hz G; lia].
    pose proof (conj Hrng (conj G5 (conj G6 (conj G7 G8)))) as GH0.
    assert (K_mbh : rdn BSEGS memD (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h))) by toD_h Hd M NHH GH0 C_mbh.
    assert (K_msz : rdn BSEGS memD (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))) by toD_h Hd M NHH GH0 C_msz.
    assert (K_idx : rdn BSEGS memD (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 iz))) by toD_h Hd M NHH GH0 C_idx.
    assert (K_nhi : rdn BSEGS memD (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))) by toD_h Hd M NHH GH0 C_nhi.
    assert (K_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))) by toD_h Hd M NHH GH0 C_nlo.
    assert (K_hs : forall j x, nth_error (map sc_map (a_sec st)) j = Some x -> rdn BSEGS memD (Z_to_bv 64 (P8 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 x))).
    { intros j x Hj. pose proof (C_hs j x Hj) as CJ.
      assert (Lj : Z.of_nat j < len).
      { pose proof (nth_error_Some (map sc_map (a_sec st)) j) as NS. rewrite Hj in NS. rewrite length_map in NS. (lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end). assert (j < length (a_sec st))%nat by (apply NS; discriminate). lia. }
      pose proof (conj Lj (conj PG1 (conj PG2 (conj PG8 CR)))) as GJ.
      apply (rdRw Hd M M _ _ _ CJ); [clear - GJ; unfold len in *; wd_ulia_c | intros x0 _; reflexivity |].
      replace (U (Z_to_bv 64 (P8 + 8 * Z.of_nat j))) with (P8 + 8 * Z.of_nat j) by (clear - GJ; unfold len in *; unorm; reflexivity).
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHP. clear - Hz GJ. lia. }
    assert (Hnth_i : nth_error (map sc_map (a_sec st)) i = Some h) by (rewrite nth_error_map, Hnth, Eh; reflexivity).
    assert (Hnth_l : nth_error (map sc_map (a_sec st)) (length (a_sec st) - 1) = Some last) by (rewrite nth_error_map, Hnl, Elast; reflexivity).
    pose proof (K_hs i h Hnth_i) as K_slot. fold iz in K_slot.
    pose proof (K_hs _ last Hnth_l) as K_last. replace (Z.of_nat (length (a_sec st) - 1)) with (len - 1) in K_last by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear - Hlen; lia).
    (* [comment removed for export] *)
    destruct (rdn1_ex_10ae41 memD) as [b1 Hb1]. destruct (rdn1_ex_10ae42 memD) as [b2 Hb2]. destruct (rdn1_ex_10ae43 memD) as [b3 Hb3].
    assert (K_lock0 : rdn BSEGS memD (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0]).
    { unfold byteZ, cellN in Ilock. rewrite w2b1 in Ilock by (clear; lia).
      assert (C_l0 : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 680)) 1 = Some [Z_to_bv 8 0]).
      { eapply rd_same; [| clear; wd_ulia_c | exact Ilock]. intros x Hx. apply EQ0. apply XIMG. revert Hx. clear. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia. }
      toD_img Hd M NHs C_l0. }
    assert (K_lock : rdn BSEGS memD (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { apply rdn4_of_bytesS; [clear; wd_ulia | exact K_lock0 | | | ].
      - replace (at_ (Z_to_bv 64 0x10ae00) 1) with (Z_to_bv 64 0x10ae01 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb1.
      - replace (at_ (Z_to_bv 64 0x10ae00) 2) with (Z_to_bv 64 0x10ae02 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb2.
      - replace (at_ (Z_to_bv 64 0x10ae00) 3) with (Z_to_bv 64 0x10ae03 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb3. }
    set (lkw := [Z_to_bv 8 0; b1; b2; b3]).
    pose proof (bytes_le_to_Z_bound lkw) as Blk. cbn [length lkw] in Blk. pose proof (bytes_le_to_Z_nonneg lkw) as Blk0.
    assert (P_hv : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U (Z_to_bv 64 (bytes_le_to_Z lkw))) by (clear - Blk Blk0; unorm; reflexivity).
    (* [comment removed for export] *)
    unfold PG in TW.
    assert (TDEF : forall z, T <= z < T + 4096 -> M (Z_to_bv 64 z) <> None).
    { intros z Hz. apply GR0. apply (writableZ_def M0 _ _ _ TW). exact Hz. }
    assert (TDEFD : forall z, T <= z < T + 4096 -> memD (Z_to_bv 64 z) <> None).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hz). exact (TDEF z Hz). }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2840)) 8) as (bf0 & Cf0 & Lf0);
      [intros z Hz; apply TDEFD; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2848)) 8) as (bf1 & Cf1 & Lf1);
      [intros z Hz; apply TDEFD; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn8_ex_10ac28 memD) as (bnf & Cnf & Lnf). destruct (rdn8_ex_10ac30 memD) as (bca & Cca & Lca).
    destruct (rdn8_ex_10ae58 memD) as (b16 & C16 & L16). destruct (rdn8_ex_10ae60 memD) as (b24 & C24 & L24).
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    assert (SOKslot : store_ok BSEGS memD (Z_to_bv 64 (P8 + 8 * iz)) 8 = true).
    { apply (sokX Hd M M0 _ _ (P8 + 8 * iz) 8 Iptrw GR0); [clear - P_Gi; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - P_Gi PG8; unfold len in *; lia | clear - PG2 PG8 CR; lia | clear - PG1 P_Gi; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHP. clear - Hz P_Gi. lia. }
    assert (SOKlast : store_ok BSEGS memD (Z_to_bv 64 (last + 24)) 8 = true).
    { apply (sokX Hd M M0 _ _ (last + 24) 8 Lwr GR0); [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - L5; lia | clear - L2 CR; lia | clear - L1; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHL. clear - Hz L5. lia. }
    assert (SHrng : 0x7fff8000 <= shlo /\ shlo + msz / 8 <= 0x10007fff8000 /\ 0 <= msz / 8) by (clear - SHB SH8m G5; ul).
    assert (SOKsh : store_ok BSEGS memD (Z_to_bv 64 (AsRtPoison.shad (Z_to_bv 64 h))) (Z.to_nat (msz / 8)) = true).
    { replace (AsRtPoison.shad (Z_to_bv 64 h)) with shlo by (clear - Hrng G5; (lazymatch goal with |- ?G => let G' := eval unfold AsRtPoison.shad, shlo in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - SHrng; lia | rewrite Z2Nat.id by (clear - SHrng; lia); clear - SHrng; lia |].
      rewrite Z2Nat.id by (clear - SHrng; lia). intros z Hz. split; [| apply NHSH; exact Hz].
      apply GR0. apply SHM. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_GAPLO, AS_LO, AS_HEAPLO in G in change_no_check G' end). clear - Hz SHB. ul. }
    (* [comment removed for export] *)
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SBH SB1 CR; lia).
    assert (P_Gh : AIMGHI <= h /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584) by (clear - G9 G3 G4 G5 G2 Slo; lia).
    assert (P_Ghs : hideW (h + msz <= 0x7fff7000 \/ 0x10007fff8000 <= h)) by exact G10.
    assert (P_Ghp : hideW (h + msz <= SBEG \/ SBEG + 2 ^ 37 <= h)) by (clear - G11; ul).
    assert (P_Gm : h + 4096 <= m /\ m + 16 <= h + msz) by (clear - G6 G7 G8; lia).
    assert (P_Gn : 1 <= n <= 2 ^ 40) by (clear - G8; lia).
    assert (P_GTt : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact T4|]. split; [clear - GTI GTB; ul | clear - GTC Slo; lia]. }
    assert (P_GhT : hideW (h + msz <= T \/ T + 4096 <= h)) by exact G12.
    assert (P_Gctx : 1 <= CTX /\ CTX + 4096 <= U S - 3584) by (clear - GC0 GCC Slo; lia).
    assert (P_Gctxi : hideW (CTX + 4096 <= AIMGLO \/ AIMGHI <= CTX)) by (clear - GCI; ul).
    assert (P_Gtp : 0x10ae04 + 88 <= U tpv /\ U tpv + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_Gtsdp : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= 0x10ae00 \/ 0x10ae04 <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI).
    { rewrite Utsdp. clear - G_tsdp2 Gc1 Gc2. ul. }
    assert (P_Glen : 0 <= iz < len /\ len <= 2 ^ 20 /\ Z.of_nat (length (map sc_map (a_sec st))) = len) by (rewrite length_map; clear - P_Gi; unfold len in *; lia).
    assert (P_hs63 : Forall (fun x => 0 <= x < 2 ^ 63) (map sc_map (a_sec st))).
    { apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (sx & <- & Hsx). destruct (sec_facts bt st Lc FF W sx Hsx) as (A1 & A2 & _ & _ & A5 & A6 & A7 & _). clear - A1 A2 A5 A6 A7 CR. unfold PG in *. lia. }
    assert (P_scan : gbb_scan m (map sc_map (a_sec st)) 0 = h).
    { rewrite Eh. apply (sec_scan bt st Lc FF W s m Hs). rewrite <- Eh, <- Emsz. clear - P_Gm. lia. }
    (* [comment removed for export] *)
    destruct (run_sA memD (seg_rom BSEGS) R S ret s0v s1v s2v s3v s4v x21 cbw tpv (Z_to_bv 64 TSDP)
                (Z_to_bv 64 (bytes_le_to_Z lkw)) (Z_to_bv 64 MIDEND) b1 b2 b3 m n SBEG T CTX h msz iz len P8 last (map sc_map (a_sec st)) bf0 bf1 bnf bca b16 b24
                R1 R2 R10 R11 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_Gspb P_Gh P_Ghs P_Ghp P_Gm P_Gn P_GTt P_GhT P_Gctx P_Gctxi P_Gtp P_Gtsdp P_Glen P_Gptr P_GptrT P_GptrH P_Glast P_GlastH P_GptrL
                P_hs63 P_scan SOKstk SOKT SOKslot SOKlast SOKsh
                K_spb K_pg K_lock P_hv K_n K_ptr K_hs K_slot K_last K_mbh K_msz K_idx K_kif K_key K_tsdp K_tctx K_thr K_nhi K_nlo
                Cf0 Lf0 Cf1 Lf1 Cnf Lnf Cca Lca C16 L16 C24 L24 K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_gcf K_thr64)
      as (rA & RUNA & A1 & A2 & A10 & A11 & A8 & A9 & A18 & A19 & A20 & A21 & A3 & A4 & A22 & A23 & A24 & A25 & A26 & A27).
    set (j0 := at_ (Z_to_bv 64 (bytes_le_to_Z bf0)) 1) in *. set (j1 := v_add (Z_to_bv 64 n) (Z_to_bv 64 (bytes_le_to_Z bf1))) in *.
    set (wnf := at_ (Z_to_bv 64 (bytes_le_to_Z bnf)) 1) in *. set (wca := v_sub (Z_to_bv 64 (bytes_le_to_Z bca)) (Z_to_bv 64 msz)) in *.
    set (w16 := v_add (Z_to_bv 64 (bytes_le_to_Z b16)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 msz))) in *.
    set (w24 := v_add (Z_to_bv 64 (bytes_le_to_Z b24)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 msz))) in *.
    (* [comment removed for export] *)
    assert (HOstk : hid_off Hd (U S - 2512) 112).
    { apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]]. }
    assert (HOinst : hid_off Hd 0x10ab98 656).
    { apply hid_off_of. intros z Hz. split; [clear - Hz; lia | apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (HOT : hid_off Hd (T + 2840) 16).
    { apply hid_off_of. intros z Hz. split; [clear - Hz GT0 GTC CR; lia | apply NHT; clear - Hz; lia]. }
    assert (HOT2 : hid_off Hd (T + 2888) 16).
    { apply hid_off_of. intros z Hz. split; [clear - Hz GT0 GTC CR; lia | apply NHT; clear - Hz; lia]. }
    assert (HOslot : hid_off Hd (P8 + 8 * iz) 8).
    { apply hid_off_of. intros z Hz. split; [clear - Hz PG1 PG2 PG8 P_Gi CR; unfold len in *; lia | apply NHP; clear - Hz P_Gi; lia]. }
    assert (HOlast : hid_off Hd (last + 24) 8).
    { apply hid_off_of. intros z Hz. split; [clear - Hz L1 L2 L5 CR; lia | apply NHL; clear - Hz L5; lia]. }
    assert (HOsh : hid_off Hd shlo (msz / 8)).
    { apply hid_off_of. intros z Hz. split; [clear - Hz SHrng; lia | apply NHSH; exact Hz]. }
    (* [comment removed for export] *)
    set (st1 := op_sec_release st h (sc_n s)). set (Hd1 := HID st1 mdl).
    assert (RL1 : rep_ledger bt st1 mdl) by exact (rep_ledger_release bt st mdl h (sc_n s) R13).
    assert (NHs1 : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st1 mdl z RL1 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT1 : forall z, T <= z < T + 4096 -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC1 : forall z, CTX <= z < CTX + 65536 -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHH1 : forall z, h <= z < h + msz -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz G1 G2 CR; lia|]. apply (rep_nolazy_sec bt st Lc FF M0 mdl W RP s z Hs). rewrite <- Eh, <- Emsz. exact Hz. }
    assert (HOstk1 : hid_off Hd1 (U S - 2512) 112).
    { apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs1; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]]. }
    assert (HOT21 : hid_off Hd1 (T + 2888) 16).
    { apply hid_off_of. intros z Hz. split; [clear - Hz GT0 GTC CR; lia | apply NHT1; clear - Hz; lia]. }
    assert (HOFF1 : H_off_segments BSEGS Hd1).
    { intros a Ha. unfold Hd1 in Ha. apply HID_lazy in Ha. pose proof (u64_range a) as Ra.
      destruct (lazy_zone bt st mdl (U a) R13 ltac:(clear - Ra; lia) Ha) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi both_addrs] in Z2.
      destruct (find_segment BSEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate. }
    assert (AW1 : A_wf (a_aa st1)) by (cbv delta [st1]; (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_release] in G in change_no_check G' end); apply A_wf_release; [rewrite Ens; clear - G8; lia | exact B1]).
    (* [comment removed for export] *)
    rewrite PC0 in RUNA.
    eapply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) (@mkst fx R _ M (seg_rom BSEGS)) _ mdl);
      [ apply lazy_cover_HID | exact B1 | exact B2 | exact HH | rewrite restrict_mkstK; exact RUNA | ].
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    (lazymatch goal with |- ?G => let G' := eval cbn [ms_mem mkst] in G in change_no_check G' end).
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end).
    rewrite (fr_sA_mr Hd M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24
               P_GS P_GT P_Gh8 P_Gi P_Gptr P_Glast HOstk HOinst HOT HOslot HOlast HOsh).
    set (M1 := fr_sA M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24).
    assert (OUT1 : forall x : word, outA S T h msz P8 iz last x -> M1 x = M x).
    { intros x OA. exact (fr_sA_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24
                            P_GS P_GT P_Gh8 P_Gi P_Gptr P_Glast x OA). }
    assert (OUTH : forall x : word, Hd x = true -> outA S T h msz P8 iz last x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end).
      pose proof (out_of_hidden Hd _ _ x HOstk Hx) as O1. pose proof (out_of_hidden Hd _ _ x HOinst Hx) as O2. pose proof (out_of_hidden Hd _ _ x HOT Hx) as O3.
      pose proof (out_of_hidden Hd _ _ x HOslot Hx) as O4. pose proof (out_of_hidden Hd _ _ x HOlast Hx) as O5. pose proof (out_of_hidden Hd _ _ x HOsh Hx) as O6.
      fold shlo. repeat split; [clear - O1; lia | clear - O2; lia | clear - O3; lia | clear - O4; lia | clear - O5; lia | clear - O6; lia]. }
    rewrite (munrestrict_same Hd M M1 (fun a Ha => OUT1 a (OUTH a Ha))).
    (* [comment removed for export] *)
    assert (HALT1 : m_halted mdl1 = None) by (rewrite Eh1; exact HH).
    assert (OUTimg : forall x : word, AIMGLO <= U x < AIMGHI -> (U x < 0x10ab98 + 56 \/ 0x10ab58 + 688 + 32 <= U x) -> outA S T h msz P8 iz last x).
    { intros x Hx Hx2. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo.
      split; [left; clear - Hx Slo CR; lia|]. split; [exact Hx2|]. split; [clear - Hx GTI; ul|].
      split; [left; clear - Hx PG1 P_Gi; lia|]. split; [left; clear - Hx L9; lia|]. clear - Hx SHB. ul. }
    Ltac cM1 OUT1 OUTimg C := eapply rd_same; [ intros x Hx; apply OUT1; apply OUTimg; revert Hx; clear; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                              | clear; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C ].
    assert (Uh : U (Z_to_bv 64 h) = h /\ U (Z_to_bv 64 msz) = msz) by (clear - Hrng G5; unorm; split; reflexivity).
    destruct Uh as (Uh & Umsz).
    assert (GR1 : mem_grows M M1) by (apply fr_sA_grows).
    assert (FLH : flushH BSEGS both_flush_tab M1 (Z_to_bv 64 h) (Z_to_bv 64 msz) (at_ S (-2432)) (Z_to_bv 64 MIDEND)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ft_mt ft_g_pgsz ft_p_pgsz ft_g_seal ft_sv both_flush_tab] in G in change_no_check G' end).
      - split; (lazymatch goal with |- ?G => let G' := eval cbn [AsRtM2S.mt_g_shoff AsRtM2S.mt_p_shoff AsRtM2S.mt_g_midbeg AsRtM2S.mt_p_midbeg AsRtM2S.mt_g_midend AsRtM2S.mt_p_midend AsRtM2S.mt_g_hiend AsRtM2S.mt_p_hiend BoRtXStrlenI.BoRtM2SI.both_m2s_tab_6dffc] in G in change_no_check G' end).
        + cM1 OUT1 OUTimg C_gsh. + cM1 OUT1 OUTimg C_sh. + cM1 OUT1 OUTimg C_gmb. + cM1 OUT1 OUTimg C_mb.
        + cM1 OUT1 OUTimg C_gme. + cM1 OUT1 OUTimg C_me. + cM1 OUT1 OUTimg C_ghe. + cM1 OUT1 OUTimg C_he.
        + (lazymatch goal with |- ?G => let G' := eval unfold AsRtM2S.m2s_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [AsRtM2S.mt_g_shoff AsRtM2S.mt_p_shoff AsRtM2S.mt_g_midbeg AsRtM2S.mt_p_midbeg AsRtM2S.mt_g_midend AsRtM2S.mt_p_midend AsRtM2S.mt_g_hiend AsRtM2S.mt_p_hiend BoRtXStrlenI.BoRtM2SI.both_m2s_tab_6dffc] in G in change_no_check G' end).
          repeat constructor; lia.
        + rewrite Uh. clear - G10 G5. ul.
        + rewrite Uh. clear - G2 G5 CR. lia.
      - rewrite Uh, Umsz. clear - G10 G2 G5 CR. ul.
      - cM1 OUT1 OUTimg C_gpgc.
      - cM1 OUT1 OUTimg C_pgc.
      - cM1 OUT1 OUTimg C_seal.
      - rewrite both_flush_cells. rewrite at_u by (clear - HSr Slo CR; lia). repeat constructor; clear - Slo CR; lia.
      - rewrite at_u by (clear - HSr Slo CR; lia). clear - Slo CR. lia.
      - rewrite at_at. change (-2432 + -32) with (-2464).
        eapply store_ok_mono; [exact GR1|].
        assert (SOKM : store_ok BSEGS M (at_ S (-2512)) 112 = true).
        { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
          apply store_ok_bytes; [| clear - HSr Slo CR; wd_ulia_c]. intros x Hx. apply (proj2 (SOK x ltac:(clear - Hx HSr Slo CR; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia))). }
        eapply (store_ok_sub BSEGS M (at_ S (-2512)) _ 112); [clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact SOKM | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    assert (RET_F : ret_ok (Z_to_bv 64 0x4ef70)) by (apply ret_ok_lit; [lia | reflexivity]).
    pose proof (fl_geom_t (Z_to_bv 64 h) (Z_to_bv 64 msz) (fh_end _ _ _ _ _ _ _ FLH)) as FG. unfold fl_sb, fl_se in FG. rewrite Uh, Umsz in FG.
    replace ((h + msz) / 8 + 2147450880) with (shlo + msz / 8) in FG by ((lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end); clear - SH8h SH8m; Z.div_mod_to_equations; lia).
    replace (h / 8 + 2147450880) with shlo in FG by ((lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end); clear; lia).
    set (pb := fl_pb (Z_to_bv 64 h)) in *. set (pe := fl_pe (Z_to_bv 64 h) (Z_to_bv 64 msz)) in *.
    destruct FG as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    assert (PBE : pb < pe /\ shlo <= pb /\ pe <= shlo + msz / 8 /\ 8192 <= msz / 8) by (clear - F4 F5 F6 F7 G5; Z.div_mod_to_equations; lia).
    destruct PBE as (PBE1 & PBE2 & PBE3 & PBE4).
    rewrite PCF.
    apply (both_flush_katD2 Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd1 HOFF1 (a_aa st) (a_aa st1) rA M1 (seg_rom BSEGS) mdl1   (* [comment removed for export] *)
             (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 0x4ef70) (at_ S (-2432)) (Z_to_bv 64 MIDEND) _ FLH RET_F A1 A2 A10 A11).
    { rewrite both_flush_cells. repeat constructor; apply hid_off_of; intros z Hz; (split; [clear - Hz; lia | apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]). }
    { rewrite at_u by (clear - HSr Slo CR; lia). eapply hid_off_sub; [exact HOstk | clear; lia | clear; lia]. }
    { exact HALT1. }
    { rewrite Elz1. apply lazy_cover_HID. }
    { exact B1. }
    { exact MI1. }
    { (* [comment removed for export] *)
      intros _ mdlm SBMm MIm. fold pb pe.
      apply (SHGATE st Lc FF M0 mdl mdlm qt qg pb (pe - pb) W RP (same_but_materialized_trans _ _ _ SBM1 SBMm) MIm
               (model_ivs_wf_sbm _ _ (same_but_materialized_trans _ _ _ SBM1 SBMm) MW)).
      - exact F8.
      - clear - F8 F9. Z.div_mod_to_equations. lia.
      - clear - PBE1. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold SB, AS_GAPLO, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). clear - SHB PBE2 PBE3 PBE1. ul. }
    { (* [comment removed for export] *) exact AW1. }
    { (* [comment removed for export] *) rewrite Elz1. apply lazy_cover_HID. }
    { (* [comment removed for export] *)
      intros HLT mdlm SBMm MIm. fold pb pe. cbv delta [st1]. (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_release] in G in change_no_check G' end).
      assert (Epb : pb = sec_inner_lo h).
      { (lazymatch goal with |- ?G => let G' := eval unfold sec_inner_lo, pgup, sh_lo, SB, PG in G in change_no_check G' end). unfold shlo in F4, F5. clear - F4 F5 F8. Z.div_mod_to_equations. lia. }
      assert (Epe : pe = sec_inner_hi h (sc_n s)).
      { (lazymatch goal with |- ?G => let G' := eval unfold sec_inner_hi, pgdn, sh_hi, SB, PG in G in change_no_check G' end). replace (sec_map_size (sc_n s)) with msz by (rewrite Emsz; reflexivity).
        rewrite SHs. unfold shlo in F6, F7. clear - F6 F7 F9. Z.div_mod_to_equations. lia. }
      assert (Rpb : 0 <= pb /\ pe < 2 ^ 64) by (unfold shlo in PBE2, PBE3; clear - PBE1 PBE2 PBE3 G1 G2 G5 CR SH8h SH8m; lia).
      apply (MInv_release_madvise (a_aa st) h (sc_n s) mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb))).
      - rewrite Ens. clear - G8. lia.
      - exact B1.
      - pose proof (B9 s Hs) as HIN. rewrite <- Eh in HIN. exact HIN.
      - exact MIm.
      - rewrite u_Z2bv by (clear - Rpb PBE1; lia). exact Epb.
      - rewrite !u_Z2bv by (clear - Rpb PBE1; lia). rewrite <- Epe. clear. lia. }
    2:{ (* [comment removed for export] *) intros HGE. exfalso. fold pb pe in HGE. clear - HGE PBE1. lia. }
    intros _ rF mdlm mdl4 SBMm MIm SBM4 MI4 E1F E2F E10F AGF. fold pb pe in SBM4 |- *.
    (* [comment removed for export] *)
    try clear OUTH. try clear HOsh. try clear NHSH. clear NHs NHT NHC NHH HOstk HOT2. try clear HOinst. try clear HOT. try clear HOslot. try clear HOlast. try clear NHL. try clear NHP.
    rename Hd into Hd0. rename Hd1 into Hd. rename NHs1 into NHs. rename NHT1 into NHT. rename NHC1 into NHC. rename NHH1 into NHH.
    rename HOstk1 into HOstk. rename HOT21 into HOT2.
    rewrite A8, A9, A18.
    change (zfill (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)) (fl_frame M1 (at_ S (-2432)) (Z_to_bv 64 0x4ef70) (Z_to_bv 64 h) (Z_to_bv 64 h) (Z_to_bv 64 msz)))
      with (mz_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)).
    set (MZ := mz_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)).
    (* [comment removed for export] *)
    assert (SBMn : same_but_materialized mdlm (madvise_dontneed_next mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)))) by ((lazymatch goal with |- ?G => let G' := eval unfold madvise_dontneed_next in G in change_no_check G' end); apply with_vm_backing_same).
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBMm) SBMn) SBM4) as SBM04.
    pose proof (same_but_materialized_frame mdl mdl4 SBM04) as SF4.
    destruct SF4 as (_ & Evm4 & Elz4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh4 & _).
    (* [comment removed for export] *)
    assert (P_Gpb : shlo <= pb /\ pb + (pe - pb) <= shlo + msz / 8 /\ 0 <= pe - pb) by (clear - PBE1 PBE2 PBE3; lia).
    Ltac feedK H := repeat (let T := type of H in lazymatch T with ?A -> _ => let a := fresh in assert (a : A) by assumption; specialize (H a); clear a end).
    assert (OUTZ : forall x : word, outA S T h msz P8 iz last x -> MZ x = M x).
    { pose proof (mz_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)) as F. feedK F. exact F. }
    assert (GRZ : mem_grows M MZ) by (apply mz_grows).
    assert (OUTctx : forall x : word, CTX <= U x < CTX + 65536 -> outA S T h msz P8 iz last x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo.
      split; [left; clear - Hx GCC Slo; lia|]. split; [clear - Hx GCI; ul|]. split; [clear - Hx GCT'; ul|].
      split; [clear - Hx PG7 P_Gi PG8; unfold len in *; ul|]. split; [clear - Hx L13 L5; ul|]. clear - Hx SHB GCB. ul. }
    assert (OUTh : forall x : word, h <= U x < h + 16 -> outA S T h msz P8 iz last x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo.
      split; [left; clear - Hx G2 G5 Slo; lia|]. split; [right; clear - Hx G9; lia|]. split; [clear - Hx G12 G5; ul|].
      split; [clear - Hx P_GptrH P_Gi G5; ul|]. split; [clear - Hx P_GlastH G5; ul|]. clear - Hx SHB G10 G5. ul. }
    set (memZ := mrestrict Hd MZ).
    Ltac toZ_img Hd M MZ OUTZ OUTimg NHs C := apply (rdRw Hd M MZ _ _ _ C); [unorm; czl | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; clear; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                            | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]].
    assert (Z_kif : rdn BSEGS memZ (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by toZ_img Hd M MZ OUTZ OUTimg NHs C_kif.
    assert (Z_key : rdn BSEGS memZ (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { apply (rdRw Hd M MZ _ _ _ C_key); [rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; rewrite Ukey; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (Z_tsdp : rdn BSEGS memZ (at_ tpv (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { apply (rdRw Hd M MZ _ _ _ C_tsdp); [rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; rewrite Utp88; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                        | rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (Z_tctx : rdn BSEGS memZ (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (rdRw Hd M MZ _ _ _ C_tctx); [rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia
        | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; [clear - Hx Gc1 Gc2; lia | clear - Hx G_tsdp2; ul]
        | rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]]. }
    assert (Z_thr : rdn BSEGS memZ (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { apply (rdRw Hd M MZ _ _ _ C_thr); [rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia | intros x Hx; apply OUTZ; apply OUTctx; revert Hx; rewrite Uctx152; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHC; clear - Hz; lia]. }
    assert (Z_mbh : rdn BSEGS memZ (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h))).
    { apply (rdRw Hd M MZ _ _ _ C_mbh); [rewrite Uh; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia | intros x Hx; apply OUTZ; apply OUTh; revert Hx; rewrite Uh; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Uh; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHH; clear - Hz G5; lia]. }
    assert (Uh8 : U (Z_to_bv 64 (h + 8)) = h + 8) by (clear - Hrng G5; unorm; reflexivity).
    assert (Z_msz : rdn BSEGS memZ (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))).
    { apply (rdRw Hd M MZ _ _ _ C_msz); [rewrite Uh8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia | intros x Hx; apply OUTZ; apply OUTh; revert Hx; rewrite Uh8; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Uh8; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHH; clear - Hz G5; lia]. }
    (* [comment removed for export] *)
    pose proof (mz_frame M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)) as FRZ. feedK FRZ. destruct FRZ as (FZ_ra & FZ_s0 & FZ_s1 & FZ_s2).
    Ltac toZ_stk Hd MZ NHs G C := apply (rdRw Hd MZ MZ _ _ _ C); [clear - G; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x _; reflexivity
                                  | rewrite at_u by (clear - G; lia); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz G; lia | left; clear - Hz G; lia]].
    pose proof (conj HSr (conj Slo (conj Shi CR))) as GSTK.
    assert (Z_ra : rdn BSEGS memZ (at_ S (-2408)) 8 = Some (LE8 ret)) by toZ_stk Hd MZ NHs GSTK FZ_ra.
    assert (Z_s0 : rdn BSEGS memZ (at_ S (-2416)) 8 = Some (LE8 s0v)) by toZ_stk Hd MZ NHs GSTK FZ_s0.
    assert (Z_s1 : rdn BSEGS memZ (at_ S (-2424)) 8 = Some (LE8 s1v)) by toZ_stk Hd MZ NHs GSTK FZ_s1.
    assert (Z_s2 : rdn BSEGS memZ (at_ S (-2432)) 8 = Some (LE8 s2v)) by toZ_stk Hd MZ NHs GSTK FZ_s2.
    assert (TDEFZ : forall z, T <= z < T + 4096 -> memZ (Z_to_bv 64 z) <> None).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold memZ in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hz). apply GRZ. exact (TDEF z Hz). }
    destruct (rdn_defined_ex BSEGS memZ (Z_to_bv 64 (T + 2888)) 8) as (bu0 & Cu0 & Lu0);
      [intros z Hz; apply TDEFZ; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memZ (Z_to_bv 64 (T + 2896)) 8) as (bu1 & Cu1 & Lu1);
      [intros z Hz; apply TDEFZ; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    assert (SOKM : store_ok BSEGS M (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply store_ok_bytes; [| clear - HSr Slo CR; wd_ulia_c]. intros x Hx. apply (proj2 (SOK x ltac:(clear - Hx HSr Slo CR; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia))). }
    assert (SOKstkZ : store_ok BSEGS memZ (at_ S (-2512)) 112 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold memZ in G in change_no_check G' end). rewrite store_ok_mrestrict; [eapply store_ok_mono; [exact GRZ | exact SOKM] | clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by (clear - GSTK; lia); exact HOstk]. }
    assert (SOKTZ : store_ok BSEGS memZ (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd MZ M0 _ _ T _ TW (mem_grows_trans _ _ _ GR0 GRZ)); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    assert (P_GhB : AIMGHI <= h /\ 4096 <= msz /\ h + msz <= U S - 3584) by (clear - P_Gh; lia).
    assert (P_GtpB : AIMGLO + 88 <= U tpv /\ U tpv + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_GtsdpB : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (rewrite Utsdp; clear - Gc1 Gc2; lia).
    Ltac viaF AGF A := lazymatch type of A with getr _ ?k = _ => rewrite (AGF k) by ((lazymatch goal with |- ?G => let G' := eval unfold AsRtM2S.m2s_clob in G in change_no_check G' end); notin); exact A end.
    assert (F8r : getr rF _ = Z_to_bv 64 h) by viaF AGF A8.
    assert (F18r : getr rF _ = Z_to_bv 64 msz) by viaF AGF A18.
    assert (F4r : getr rF _ = tpv) by viaF AGF A4.
    destruct (run_sB memZ (seg_rom BSEGS) rF S ret s0v s1v s2v tpv (Z_to_bv 64 TSDP) T CTX h msz bu0 bu1
                E2F F8r F18r F4r P_GS P_GhB P_GTt P_Gctx P_GtpB P_GtsdpB SOKstkZ SOKTZ
                Z_kif Z_key Z_tsdp Z_tctx Z_thr Cu0 Lu0 Cu1 Lu1 Z_mbh Z_msz Z_ra Z_s0 Z_s1 Z_s2)
      as (rB & RUNB & UR & B4r).
    set (k0 := at_ (Z_to_bv 64 (bytes_le_to_Z bu0)) 1) in *. set (k1 := v_add (Z_to_bv 64 (bytes_le_to_Z bu1)) (Z_to_bv 64 msz)) in *.
    assert (HALT4 : m_halted mdl4 = None) by (rewrite Eh4; exact HH).
    rewrite PC1 in RUNB.
    eapply (katD_msteps_acct BSEGS Hd HOFF1 asanF_segs_wx (a_aa st1) (@mkst fx rF _ MZ (seg_rom BSEGS)) _ mdl4);
      [ rewrite Elz4; apply lazy_cover_HID | exact AW1 | exact MI4 | exact HALT4 | rewrite restrict_mkstK; exact RUNB | ].
    intros mdl5 MI5 SBM5 HC5. rewrite unrestrict_mkst.
    (lazymatch goal with |- ?G => let G' := eval cbn [ms_mem mkst] in G in change_no_check G' end).
    pose proof (same_but_materialized_trans _ _ _ SBM04 SBM5) as SBM05.
    pose proof (same_but_materialized_frame mdl mdl5 SBM05) as SF5.
    destruct SF5 as (_ & Evm5 & Elz5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh5 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold memZ in G in change_no_check G' end). rewrite (fr_sB_mr Hd MZ S ret s0v s1v s2v T k0 k1 P_GS P_GT HOstk HOT2).
    set (M5 := fr_sB MZ S ret s0v s1v s2v T k0 k1).
    assert (OUT5H : forall x : word, Hd x = true -> M5 x = MZ x).
    { intros x Hx. pose proof (out_of_hidden Hd _ _ x HOstk Hx) as O1. pose proof (out_of_hidden Hd _ _ x HOT2 Hx) as O2.
      apply (fr_sB_out MZ S ret s0v s1v s2v T k0 k1 P_GS P_GT x); [clear - O1; lia | clear - O2; lia]. }
    rewrite (munrestrict_same Hd MZ M5 OUT5H).
    (* [comment removed for export] *)
    unfold um1_regs in UR. destruct UR as (U1 & U2 & U10 & U11 & U17 & U8 & U9 & U18 & U3 & U4 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & U26 & U27).
    assert (HALT5 : m_halted mdl5 = None) by (rewrite Eh5; exact HH).
    pose proof (proj1 (proj2 BOOTG)) as NS.
    assert (MAPHAS : map_has (vm_maps (m_vmmaps mdl5)) (Z_to_bv 64 h) (Z_to_bv 64 msz) = true).
    { rewrite Evm5, Eh, Emsz. exact (AsKSys8.sec_map_has bt st Lc FF M0 mdl s W RP Hs). }
    apply (katD_ecall_munmap BSEGS rB _ M5 (seg_rom BSEGS) mdl5 _ (Z_to_bv 64 h) msz _ F_811b8 E_811b8 HALT5 U17 U10).
    { rewrite Uh. exact G3. } { exact U11. } { clear - G5; lia. } { exact G4. } { rewrite Uh. clear - G2 CR. lia. } { exact MAPHAS. }
    rewrite PC2.
    change (unfill (Z_to_bv 64 h) (Z_to_bv 64 msz) M5)
      with (mu_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    set (MU := mu_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    set (mdlU := munmap_model (Z_to_bv 64 h) (Z_to_bv 64 msz) mdl5).
    (* [comment removed for export] *)
    assert (EKV : m_vmmaps mdl5 = m_vmmaps mdl) by exact Evm5.
    assert (EKL : m_vm_lazy mdl5 = m_vm_lazy mdl) by exact Elz5.
    assert (MIU : MInv (a_aa st1) mdlU).
    { (lazymatch goal with |- ?G => let G' := eval unfold mdlU in G in change_no_check G' end). rewrite Eh, Emsz. exact (AsKSys8.child_MInv bt st Lc FF M0 mdl s W RP MW Hs NS (a_aa st1) mdl5 EKV EKL MI5). }
    assert (HALTU : m_halted mdlU = None) by ((lazymatch goal with |- ?G => let G' := eval unfold mdlU in G in change_no_check G' end); rewrite munmap_model_halted; exact HALT5).
    assert (LCU : lazy_cover Hd (m_vm_lazy mdlU) (a_aa st1)).
    { apply (lazy_cover_of_iff Hd (m_vm_lazy mdl) (m_vm_lazy mdlU)); [| apply lazy_cover_HID].
      pose proof (AsKSys8.secfree_ledger bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 (munmap_model (Z_to_bv 64 (sc_map s)) (Z_to_bv 64 (sc_mapsz s)) mdl5) EKV EKL (same_but_materialized_refl _)) as LG.
      rewrite <- Eh, <- Emsz in LG. exact (proj1 (proj2 (proj2 LG))). }
    (* [comment removed for export] *)
    set (memU := mrestrict Hd MU).
    assert (OUTU : forall x : word, outA S T h msz P8 iz last x -> (U x < T + 2888 \/ T + 2904 <= U x) -> (U x < h \/ h + msz <= U x) -> MU x = M x).
    { pose proof (mu_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as F. feedK F. exact F. }
    Ltac toU_img Hd M MU OUTU OUTimg NHs GI C := apply (rdRw Hd M MU _ _ _ C); [unorm; czl
        | intros x Hx; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; apply OUTU; [apply OUTimg; clear - Hx; lia | clear - Hx GI; ul | clear - Hx GI; ul]
        | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]].
    pose proof (conj GTI G9) as GIU.
    assert (U_gcf : rdn BSEGS memU (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by toU_img Hd M MU OUTU OUTimg NHs GIU C_gcf.
    assert (U_lim : rdn BSEGS memU (Z_to_bv 64 (0x19fce8 + 144)) 8 = Some (LE8 (Z_to_bv 64 0))) by toU_img Hd M MU OUTU OUTimg NHs GIU C_lim.
    pose proof (mu_frame M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FRU. feedK FRU. destruct FRU as (FU_ra & FU_s0 & FU_s1 & FU_s2).
    assert (U_ra : rdn BSEGS memU (at_ S (-2408)) 8 = Some (LE8 ret)) by toZ_stk Hd MU NHs GSTK FU_ra.
    assert (U_s0 : rdn BSEGS memU (at_ S (-2416)) 8 = Some (LE8 s0v)) by toZ_stk Hd MU NHs GSTK FU_s0.
    assert (U_s1 : rdn BSEGS memU (at_ S (-2424)) 8 = Some (LE8 s1v)) by toZ_stk Hd MU NHs GSTK FU_s1.
    assert (U_s2 : rdn BSEGS memU (at_ S (-2432)) 8 = Some (LE8 s2v)) by toZ_stk Hd MU NHs GSTK FU_s2.
    assert (SOKstkU : store_ok BSEGS memU (at_ S (-2448)) 48 = true).
    { pose proof (mu_stk M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as F. feedK F.
      (lazymatch goal with |- ?G => let G' := eval unfold memU in G in change_no_check G' end). rewrite store_ok_mrestrict; [| clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by (clear - GSTK; lia); eapply hid_off_sub; [exact HOstk | clear; lia | clear; lia]].
      eapply (store_ok_sub BSEGS MU (at_ S (-2512)) _ 112); [clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact F | clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    assert (P_GS24 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47 + 256) by (clear - P_GS; lia).
    match goal with |- context [regupd rB ?k ?v] => set (rU := regupd rB k v) end.
    destruct (um2_run memU (seg_rom BSEGS) S ret s0v s1v s2v msz rU) as (rC & RUNC & URC); try assumption.
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_other by (intros E; discriminate E). exact U1. }
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_other by (intros E; discriminate E). exact U2. }
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_same by (intros E; discriminate E). reflexivity. }
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_other by (intros E; discriminate E). exact U8. }
    rewrite PC3 in RUNC.
    eapply (katD_msteps_acct BSEGS Hd HOFF1 asanF_segs_wx (a_aa st1) (@mkst fx rU _ MU (seg_rom BSEGS)) _ mdlU);
      [ exact LCU | exact AW1 | exact MIU | exact HALTU | rewrite restrict_mkstK; exact RUNC | ].
    intros mdl6 MI6 SBM6 HC6. rewrite unrestrict_mkst.
    (lazymatch goal with |- ?G => let G' := eval cbn [ms_mem mkst] in G in change_no_check G' end).
    (lazymatch goal with |- ?G => let G' := eval unfold memU in G in change_no_check G' end). rewrite (fr_um2_mr Hd S P_GS HOstk MU).
    assert (OUT6H : forall x : word, Hd x = true -> fr_um2 MU S x = MU x).
    { intros x Hx. pose proof (out_of_hidden Hd _ _ x HOstk Hx) as O1. apply (fr_um2_out S P_GS MU x). clear - O1. lia. }
    rewrite (munrestrict_same Hd MU (fr_um2 MU S) OUT6H).
    change (fr_um2 MU S) with (fin_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    set (MF := fin_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    (* [comment removed for export] *)
    pose proof (fin_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FOUT. feedK FOUT.
    pose proof (fin_def M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FDEF. feedK FDEF.
    pose proof (fin_foot M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FFOOT. feedK FFOOT.
    pose proof (fin_nch M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FNCH. feedK FNCH.
    pose proof (fin_lock M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FLOCK. feedK FLOCK.
    pose proof (fin_slot M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FSLOT. feedK FSLOT.
    pose proof (fin_idx M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FIDX. feedK FIDX.
    fold MF in FOUT, FDEF, FFOOT, FNCH, FLOCK, FSLOT, FIDX.
    assert (SBM6' : same_but_materialized (munmap_model (Z_to_bv 64 (sc_map s)) (Z_to_bv 64 (sc_mapsz s)) mdl5) mdl6) by (rewrite <- Eh, <- Emsz; exact SBM6).
    pose proof (AsKSys8.secfree_perm bt st Lc FF M0 mdl s W RP Hs mdl5 mdl6 EKV EKL SBM6') as PM.
    pose proof (AsKSys8.secfree_ledger bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 mdl6 EKV EKL SBM6') as (LNA & LNP & LLZ & LFL & LE1 & LE2 & LE3 & LE4 & LE5 & LE6).
    pose proof (AsKSys8.secfree_eager bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 mdl6 EKV EKL SBM6') as EAG.
    pose proof (AsKSys8.child_wf bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 mdl6 EKV EKL SBM6') as MW6.
    pose proof (same_but_materialized_frame mdlU mdl6 SBM6) as SF6.
    destruct SF6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh6 & _).
    (* [comment removed for export] *)
    assert (FOOTX : forall a : word, MF a <> M a -> ~ X (U a) /\ U a < U S - 2400).
    { intros a NE. destruct (FFOOT a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - split; [apply XSTK; clear - F Slo; lia | clear - F; lia].
      - split; [apply XIMG; clear - F; lia | clear - F Slo CR; lia].
      - split; [apply XT; clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply XT; clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply XP; clear - F P_Gi PG8; unfold len in *; lia | clear - F P_Gptr P_Gi; lia].
      - split; [apply XL; clear - F L5; lia | clear - F P_Glast; lia].
      - split; [apply XSH; exact F | clear - F P_GshS; lia].
      - split; [apply XH; exact F | clear - F P_Gh; lia]. }
    assert (W' : WFq bt (op_recycle_sec st i) Lc FF qt qg) by exact (OPS_WFq_recycle_sec_pf bt st Lc FF ba m n its rest i s qt qg W EGQ HP Hnth Eus).
    assert (RX' : AsAinvOpsRc73.AsAinvRepX3.RepX bt X (op_recycle_sec st i) Lc FF MF mdl6).
    { apply (OPS_REPX_recycle_sec_pf bt X Xd st Lc FF M MF mdl mdl6 ba m n its rest i s qt qg W (ex_intro _ M0 (conj RP DX)) EGQ HP Hnth Eus XSUB XQ XOBJ).
      - intros a Ha. rewrite FOUT; [exact (QDEF a Ha) | | |]; unfold qhdr, IB in Ha; rewrite BT_ia in Ha; cbn [ia_instance both_addrs] in Ha.
        + (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo. split; [left; clear - Ha Slo CR; lia|]. split; [right; clear - Ha; lia|]. split; [clear - Ha GTI; ul|].
          split; [left; clear - Ha PG1 P_Gi; lia|]. split; [left; clear - Ha L9; lia|]. clear - Ha SHB. ul.
        + clear - Ha GTI. ul.
        + left. clear - Ha G9. lia.
      - intros a NE. split; [| rewrite <- Eh, <- Emsz; exact (FDEF a NE)]. left. (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_sec, idx_lo, idx_hi in G in change_no_check G' end). rewrite Hnl.
        (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite <- Eh, <- Emsz, <- Elast. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). rewrite SHs. fold iz.
        destruct (FFOOT a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
        + do 6 right. clear - F Slo. lia.
        + left. clear - F. lia.
        + do 5 right. left. clear - F. lia.
        + do 5 right. left. clear - F. lia.
        + right. left. exact F.
        + right. right. left. clear - F. lia.
        + do 4 right. left. unfold shlo in F. clear - F. lia.
        + do 3 right. left. exact F.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). fold len. exact FNCH.
      - (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by (clear; lia). exact FLOCK.
      - intros sl' Hlt Hnl'. rewrite Hnl in Hnl'. injection Hnl' as <-. rewrite <- Elast. fold iz. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs.
        split; [exact FSLOT|]. apply FIDX. intros E. subst last.
        assert (s = sl) by (apply (AsAinvFrame3.NoDup_map_inj sc_map (a_sec st) s sl); [destruct W as (_ & _ & _ & (_ & _ & _ & _ & ND & _) & _); exact ND | exact Hs | exact Hsl | rewrite <- Eh; symmetry; exact E]).
        subst sl. pose proof W as (_ & _ & _ & (_ & _ & _ & _ & ND & _) & _). apply NoDup_map_inv in ND.
        pose proof (proj1 (NoDup_nth_error (a_sec st)) ND i (length (a_sec st) - 1)%nat Hlen ltac:(rewrite Hnth, Hnl; reflexivity)) as EI.
        fold len in Hlt. unfold len in Hlt. clear - EI Hlt Hlen. lia.
      - exact PM. - exact LNA. - exact LNP. - exact LLZ. - exact LFL. - exact LE1. - exact LE2. - exact LE3. - exact LE4. - exact LE5. - exact LE6.
      - cbv delta [st1] in MI6. cbn [a_aa op_sec_release] in MI6. rewrite Eh in MI6. exact MI6.   (* [comment removed for export] *)
      - exact EAG. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_recycle_sec st i), MF, mdl6, rC.
    split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh6; exact HALTU|]. split; [exact MW6|].
    split; [exact W'|]. split; [exact RX'|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec, op_qitem in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec, op_qitem in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec, op_qitem in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [split; [intros hh HL; unfold holes_le in *; (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec, op_qitem in G in change_no_check G' end); rewrite EGQ; exact HL | apply fk_recycle_sec]|].          (* [comment removed for export] *)
    split; [intros z Hz; exact (XB_recycle_sec bt st ba (m, n) its rest i z EGQ (XSUB z Hz))|].
    split.
    { intros a Ha. destruct (decide (MF a = M a)) as [E|NE]; [exact E|]. exfalso. destruct (FOOTX a NE) as [N1 N2].
      destruct Ha as [Ha|Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
    split.
    { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      assert (PRIVI : forall z, 0x10ab58 <= z < 0x10b9b8 -> in_wins (ia_priv (bt_ia bt)) z).
      { intros z Hz. rewrite BT_ia. exists 0x10ab58, 0x10b9b8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | exact Hz]. }
      assert (IMGLO' : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
      destruct (FFOOT a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - split; [left; clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D P_Gh; lia]].
      - split; [right; right; apply PRIVI; clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D G9; lia]].
      - split; [right; left; apply (OBL_rt_private_pf bt st Lc FF W (U a)); left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D G12; ul]].
      - split; [right; left; apply (OBL_rt_private_pf bt st Lc FF W (U a)); left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D G12; ul]].
      - split; [right; left; apply (ptrarr_private bt st Lc FF W (U a)); clear - F P_Gi PG8; unfold len in *; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D P_GptrH P_Gi; ul]].
      - assert (PL : rt_priv (bt_ia bt) Lc FF (U a)) by (apply (sec_hdr_private bt st Lc FF W IMGLO' sl (U a) Hsl); rewrite <- Elast; clear - F; lia).
        split; [right; left; exact PL | right; exact PL].
      - assert (PS : rt_priv (bt_ia bt) Lc FF (U a)).
        { apply (sec_quar_shadow_private bt st Lc FF W IMGLO' m n s (U a) Hq HP Hs Eus Ens). rewrite <- Eh, <- Emsz. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). unfold shlo in F. exact F. }
        split; [right; left; exact PS | right; exact PS].
      - assert (PC : rt_priv (bt_ia bt) Lc FF (U a)) by (apply (sec_quar_private bt st Lc FF W IMGLO' m n s (U a) Hq HP Hs Eus Ens); rewrite <- Eh, <- Emsz; exact F).
        split; [right; left; exact PC | right; exact PC]. }
    split; [intros a _; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); exact (lzb_of_iff _ _ LLZ a)|].
    split.
    { apply (same_except_vm_trans mdl mdl5 mdl6); [apply same_but_materialized_except_vm; exact SBM05|].
      apply (same_except_vm_trans mdl5 mdlU mdl6); [apply munmap_except_vm | apply same_but_materialized_except_vm; exact SBM6]. }
    (* [comment removed for export] *)
    unfold um2_regs in URC. destruct URC as (V2 & V8 & V9 & V18 & V3 & V4 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27).
    Ltac viaR AGF U A := lazymatch type of U with getr _ ?k = _ => rewrite U; rewrite (AGF k) by ((lazymatch goal with |- ?G => let G' := eval unfold AsRtM2S.m2s_clob in G in change_no_check G' end); notin); exact A end.
    Ltac viaC r C := lazymatch type of C with getr _ ?k = _ => rewrite C; (lazymatch goal with |- ?G => let G' := eval unfold r in G in change_no_check G' end); rewrite getr_other by (intros E; discriminate E) end.
    apply regs_kept_intro.
    - rewrite V2. symmetry. exact R2.
    - viaC rU V3. viaR AGF U3 A3.
    - viaC rU V4. viaR AGF U4 A4.
    - exact V8. - exact V9. - exact V18.
    - viaC rU V19. viaR AGF U19 A19.
    - viaC rU V20. viaR AGF U20 A20.
    - viaC rU V21. viaR AGF U21 A21.
    - viaC rU V22. viaR AGF U22 A22.
    - viaC rU V23. viaR AGF U23 A23.
    - viaC rU V24. viaR AGF U24 A24.
    - viaC rU V25. viaR AGF U25 A25.
    - viaC rU V26. viaR AGF U26 A26.
    - viaC rU V27. viaR AGF U27 A27.
  Qed.
End KS.
