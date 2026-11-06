(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRcGS.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFRcS1.
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
End AsAllocFRcGS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFRcS1 AsAllocFRcGS.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rt_priv_sub : forall {RUN : run_ceil} IA (Lc Lc' FF : list (Z * Z)) a,
  (forall x, In x Lc' -> In x Lc) -> rt_priv IA Lc FF a -> rt_priv IA Lc' FF a.
Proof.
  intros RUN IA Lc Lc' FF a SUB (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros V. apply P3.
  destruct V as [(b & n & Hin & Hr) | [V | [(b & n & Hin & Hr) | V]]].
  - left. exists b, n. split; [exact (SUB _ Hin) | exact Hr].
  - right; left; exact V.
  - right; right; left. exists b, n. split; [exact (SUB _ Hin) | exact Hr].
  - right; right; right; exact V.
Qed.

Section RcGL.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.

  Section W.
    Variables (st : ast) (Lc FF : list (Z * Z)).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.
    Hypothesis IMGLO : ia_img_lo IA <= 65536.

    Lemma sec_live_idx : forall p n, In (p, n) Lc -> is_primary n = false ->
      exists i s, nth_error (a_sec st) i = Some s /\ In s (a_sec st) /\ sc_user s = p /\ sc_n s = n.
    Proof using W qg qt FF bt RUN.
      intros p n Hin HP. destruct (live_sec bt st Lc FF W p n Hin HP) as (s & Hs & Eu & En).
      destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s. repeat split; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma post_lists : forall L1 L2 p n, Lc = L1 ++ (p, n) :: L2 -> forall x, In x (L1 ++ L2) -> In x Lc /\ x <> (p, n).
    Proof using W qg qt FF st bt RUN.
      intros L1 L2 p n HL x Hx. pose proof W as (_ & _ & _ & _ & (_ & ND & _) & _).
      assert (NDL : List.NoDup (L1 ++ (p, n) :: L2)) by (rewrite <- HL; exact ND).
      rewrite HL. exact (proj1 (in_remove_mid L1 L2 (p, n) x NDL) Hx).
    Qed.

    (* [comment removed for export] *)
    Lemma sec_live_private : forall L1 L2 p n s a, Lc = L1 ++ (p, n) :: L2 -> is_primary n = false -> In s (a_sec st) -> sc_user s = p -> sc_n s = n ->
      sc_map s <= a < sc_map s + sc_mapsz s -> rt_priv IA (L1 ++ L2) FF a.
    Proof using IMGLO W qg qt.
      intros L1 L2 p n s a HL HP Hs Eu En Ha.
      pose proof (post_lists L1 L2 p n HL) as INL.
      pose proof (sec_geom bt st Lc FF W IMGLO s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      pose proof (img_lits bt st Lc FF W) as [I1 I2].
      pose proof (fs_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as DF.
      split; [clear - Ha G2; lia|]. split; [clear - Ha G9; lia|].
      destruct (heap_not_shadowish bt st Lc FF W (L1 ++ L2) a ltac:(intros p0 n0 H0; exact (proj1 (INL _ H0))) ltac:(clear - Ha G10; lia)) as (N1 & N2 & N3 & N4).
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      - destruct V as (p' & n' & Hin & Hpa). destruct (INL _ Hin) as [Hin2 NE].
        destruct (live_ext bt st Lc FF W p' n' Hin2) as (lo' & hi' & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n' ltac:(lia)) as (U1 & _).
        destruct E as [(HP' & -> & -> & CV' & HC' & LIV' & S1 & S2) | (HP' & sc & Hsc & Eu' & En' & -> & ->)].
        + clear - G11 S1 S2 Ha Hpa Y1 Y2 U1 Y8. ulia.
        + destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [<- | D].
          * apply NE. rewrite <- Eu', <- En', Eu, En. reflexivity.
          * clear - D Ha Hpa Y1 Y2 U1 Y8. unfold PG in *. lia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        clear - DF Ha Hfa F1 F2 F3 F4. ulia.
    Qed.

    (* [comment removed for export] *)
    Lemma shadow_private_of_sub : forall Lc' lo L z, (forall x, In x Lc' -> In x Lc) -> lo mod 8 = 0 -> L mod 8 = 0 -> 0 <= lo -> lo + L <= CEIL ->
      (lo + L <= ia_img_lo IA \/ ia_img_hi IA <= lo) ->
      (forall a, lo <= a < lo + L -> ~ app_visible IA Lc' FF a) ->
      sh_lo lo <= z < sh_lo lo + L / 8 -> rt_priv IA Lc' FF z.
    Proof using IMGLO W qg qt st.
      intros Lc' lo L z SUB Hlo HL HLO HHI HIM NV Hz. pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof ceil_rng as CR.
      unfold sh_lo in Hz.
      pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo. rewrite Hlo in Dlo. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL in DL.
      set (g := z - SB) in *. assert (Eg : z = SB + g) by ((lazymatch goal with |- ?G => let G' := eval unfold g in G in change_no_check G' end); lia).
      assert (G8 : lo <= 8 * g < lo + L) by lia.
      split; [ulia|]. split; [ulia|].
      intros [V | [V | [V | [V | [V | V]]]]].
      - destruct V as (p & n & Hin & Hr).
        pose proof W as (_ & _ & _ & _ & (WL & _) & _). destruct (WL p n (SUB _ Hin)) as (_ & _ & (B1 & B2 & B3 & B4) & _). ulia.
      - destruct V as (f & k & Hf & Hr). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & INFS & _) & _).
        destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((D1 & D2 & D3 & D4 & D5) & _). ulia.
      - destruct V as (p & n & Hin & Hr). unfold sh_lo, sh_hi in Hr.
        destruct (live_range bt st Lc FF W p n (SUB _ Hin)) as (L1 & L2 & L3 & L4).
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

    Lemma sec_live_shadow_private : forall L1 L2 p n s z, Lc = L1 ++ (p, n) :: L2 -> is_primary n = false -> In s (a_sec st) -> sc_user s = p -> sc_n s = n ->
      sh_lo (sc_map s) <= z < sh_lo (sc_map s) + sc_mapsz s / 8 -> rt_priv IA (L1 ++ L2) FF z.
    Proof using IMGLO W qg qt.
      intros L1 L2 p n s z HL HP Hs Eu En Hz.
      pose proof (sec_geom bt st Lc FF W IMGLO s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      apply (shadow_private_of_sub (L1 ++ L2) (sc_map s) (sc_mapsz s) z);
        [intros x Hx; exact (proj1 (post_lists L1 L2 p n HL x Hx)) | clear - G3; Z.div_mod_to_equations; lia | clear - G4; Z.div_mod_to_equations; lia | lia | exact G2 | right; exact G9 | | exact Hz].
      intros a Ha. exact (proj2 (proj2 (sec_live_private L1 L2 p n s a HL HP Hs Eu En Ha))).
    Qed.
  End W.
End RcGL.
