(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMalmys.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeB2 ATransp AFreeB3 AFreeB4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

Section FreeOwnC.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (li : liveinfo) (sp : word) (v' : mem) (lo : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOS : lo <= bv_unsigned sp.
  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation ch := (li_chunk li).
  Local Notation r8 := ((n0 + 7) / 8).
  Local Notation n0a := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation qt := (a_qthread A).
  Local Notation qg := (a_qglobal A).
  Variables (qt' qg' : list batch) (cache' : Z -> pcache) (D' : list (list Z)) (ia' : bool).
  Variable BX : Z -> Prop.
  Hypothesis BXW : forall a, BX a ->
       (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes)
    \/ (thr + 2128 <= a < thr + 2208)
    \/ (thr + 2784 <= a < thr + 2792)
    \/ (exists k, p_cached_ (a_cache A) kQuarantineBatchClass k /\
                  chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes)
    \/ xblk a.
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ W0 lo (bv_unsigned sp) thr p r8 n0a f0 a -> ~ BX a -> v' (wz a) = v (wz a).
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis SM : mapped v lo (bv_unsigned sp - lo).
  Local Notation A' := (freeA A p qt' qg' cache' D' ia').

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v. Proof. exact (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI)). Qed.

  Lemma wmono_NNC : forall (w w' : mem) a, wmono rsegs w w' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
    w (wz a) <> None -> w' (wz a) <> None.
  Proof.
    intros w w' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
    rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
    destruct (w (wz a)); [| congruence]. destruct (w' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
  Qed.
  Lemma NNoC : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  Proof. intros a H0 H1 H2. apply (wmono_NNC _ _ a WMv); lia. Qed.

  (* [comment removed for export] *)
  Ltac geop3 := let Gc := fresh "Gc" in let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gs := fresh "Gs" in
    (first [ pose proof ((GEOP A v p n0 li AR LU LN)) as dR_1; dand4 dR_1 as Gc Gt Gn Gf | pose proof (GEOP A v p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]); aobj_lin1 Gc; aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf;
    pose proof (GEOS A v p n0 li sp AR LU LN) as Gs; unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.
  Lemma CVoC : carved A ch. Proof. exact (known_carved A v AR _ _ (KN A v p n0 li AR LU LN)). Qed.

  (* [comment removed for export] *)
  Lemma chunk_owned_oldC : forall a, chunk_lo sb ch <= a < chunk_hi sb ch -> ~ (p <= a < p + n0) -> pa_owned A a.
  Proof.
    intros a Ha NU. apply (carved_owned A v AR ch a CVoC Ha). intros u li' Hl E Hu.
    destruct (Z.eq_dec u p) as [->|NE].
    - rewrite LU in Hl. injection Hl as <-. rewrite LN in Hu. exact (NU Hu).
    - exact (live_live_chunk A v AR u p li' li Hl LU NE E).
  Qed.

  (* [comment removed for export] *)
  Lemma batch_ownedC : forall b a, In b (qt ++ qg) -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> pa_owned A a.
  Proof.
    intros b a Hb Ha. apply (carved_owned A v AR _ a (batch_carved A v AR b Hb)).
    - rewrite (proj1 (c24_range A b.(ba_idx))), (proj2 (c24_range A (ba_idx b))). unfold batch_addr in Ha. exact Ha.
    - intros u li' Hl E _. exact (live_not_batch A v AR u li' b Hl Hb E).
  Qed.
  Lemma cached_ownedC : forall k a, p_cached_ (a_cache A) kQuarantineBatchClass k ->
    chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes -> pa_owned A a.
  Proof.
    intros k a Ck Ha. assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    apply (carved_owned A v AR _ a (cached_carved A v AR kQuarantineBatchClass k C24 Ck)).
    - rewrite (proj1 (c24_range A k)), (proj2 (c24_range A k)). exact Ha.
    - intros u li' Hl E _. exact (live_not_cached A v AR u li' kQuarantineBatchClass k Hl C24 Ck E).
  Qed.

  (* [comment removed for export] *)
  Lemma ia_ownedC : forall a, xblk a -> pa_owned A a.
  Proof. intros a H. apply asI_static_owned. cbn [cl_static LPA]. unfold xblk, ia_blk, gq_blk in H. unfold pa_static. lia. Qed.

  (* [comment removed for export] *)
  Lemma frame1C : forall a, 0 <= a < 2^64 -> ~ pa_owned A a -> ~ (lo <= a < bv_unsigned sp) -> ~ newblk p n0 a ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha NO NW NB. pose proof (GEO A v p n0 li sp AR LU LN) as G. geop3. unfold newblk, blk in NB.
    apply MU; [exact Ha| |].
    - unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
      + exact (NW H).
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. apply chunk_owned_oldC; lia.
      + destruct (Z_lt_dec a (p + n0)); [apply NB; left; split; [kung_all; lia| lia]|]. apply NO. apply chunk_owned_oldC; lia.
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. apply (dstat_owned A). exact H.
      + apply NO. apply (n0_owned A v AR). kung_all. lia.
      + apply NO. apply (f0_owned A v AR). kung_all. lia.
      + apply NB. right. split; [kung_all; lia| exact H].
      + apply NO. apply (thr_owned A v AR). lia.
    - intros HB. destruct (BXW a HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|H]]]].
      + apply NO. exact (batch_ownedC b a Hb Rb).
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. exact (cached_ownedC k a Ck Rk).
      + apply NO. exact (ia_ownedC a H).
  Qed.

  (* [comment removed for export] *)
  Lemma owned_monoC : forall a, pa_owned A a -> pa_owned A' a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_ in *. cbn [freeA a_pl a_reg a_livemap a_sec a_fframes].
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; [left; left; exact S| | left; right; left; right; exact HS| left; right; right; exact GH| right; exact I].
    left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_6; dex2 dR_6 as u li'; destruct dR_6 as [Hl Hu] | intro dR_6; dand4 dR_6 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). apply NU. exists u, li'. split; [| exact Hu].
    unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. exact (proj2 Hl).
  Qed.
  (* [comment removed for export] *)
  Lemma owned_newC : forall a, pa_owned A' a -> pa_owned A a \/ newblk p n0 a.
  Proof.
    intros a H. pose proof (GEO A v p n0 li sp AR LU LN) as G. geop3.
    destruct (decide (p <= a < p + n0)) as [Y|X]; [right; left; split; [kung_all; lia| exact Y]|]. left.
    unfold pa_owned, aowned, aowned_ in *. cbn [freeA a_pl a_reg a_livemap a_sec a_fframes] in H.
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; [left; left; exact S| | left; right; left; right; exact HS| left; right; right; exact GH| right; exact I].
    left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_7; dex2 dR_7 as u li'; destruct dR_7 as [Hl Hu] | intro dR_7; dand4 dR_7 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). 
    destruct (Z.eq_dec u p) as [->|NE].
    - rewrite LU in Hl. injection Hl as <-. rewrite LN in Hu. exact (X Hu).
    - apply NU. exists u, li'. split; [| exact Hu]. unfold free_lm. rewrite lookup_delete_Some. split; [congruence| exact Hl].
  Qed.
  (* [comment removed for export] *)
  Lemma victim_ownedC : forall a, newblk p n0 a -> pa_owned A' a.
  Proof.
    intros a NB. pose proof (GEO A v p n0 li sp AR LU LN) as G. geop3. (first [ pose proof ((carved_shadow A v AR ch CVoC)) as dR_2; dand3 dR_2 as CE CHS _ | pose proof (carved_shadow A v AR ch CVoC) as (CE & CHS & _) ]).
    (first [ dand8 G as PM CL1 L1 L2 CL2 NR R8 _ | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & _) ]).
    unfold newblk, blk in NB. destruct NB as [[_ Ha]|[_ Ha]].
    - (* [comment removed for export] *)
      destruct (carved_in_rt A v AR ch a CVoC ltac:(lia)) as [RIN NF].
      unfold pa_owned, aowned, aowned_. cbn [freeA a_pl a_reg a_livemap a_sec a_fframes].
      left. right. left. left. split; [exact RIN|]. split; [| exact NF].
      ((first [ intro dR_8; dex2 dR_8 as u li'; destruct dR_8 as [Hl Hu] | intro dR_8; dand4 dR_8 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NE Hl].
      pose proof (live_user_in_carved A v AR ch a u li' CVoC ltac:(lia) Hl Hu) as E. exact (live_live_chunk A v AR u p li' li Hl LU (fun H => NE (eq_sym H)) E).
    - (* [comment removed for export] *)
      apply owned_monoC. left. right. left. right. left.
      assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
      pose proof (sh_mono _ _ L1) as SMa. pose proof (sh_mono _ _ L2) as SMb. pose proof (sh_mono (p + -16) p ltac:(lia)) as SMc.
      exact (CHS a ltac:(lia)).
  Qed.

  Theorem free_frame_okC : frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) (bv_unsigned sp - lo) (newblk p n0) nowhere v v'.
  Proof.
    pose proof alloc_ceiling_val as CE. unfold frame_ok. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE' NB _. apply frame1C; [assumption| assumption| replace (bv_unsigned sp - (bv_unsigned sp - lo)) with lo in NW by lia; exact NW| assumption].
    - intros a Ha NI Hv. right. right. apply (wmono_NNC _ _ a WMv); [| exact Ha| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. lia.
    - replace (bv_unsigned sp - (bv_unsigned sp - lo)) with lo by lia. eapply mapped_mono; [exact SM|]. intros i Hi. pose proof (zr_word sp) as R; unfold inr64 in R. pose proof alloc_ceiling_val. apply NNoC; lia.
    - intros a Ha F. destruct F.
    - intros a Ha O'. destruct (owned_newC a O'); [left| right; left]; assumption.
    - intros a Ha O NO'. exfalso. exact (NO' (owned_monoC a O)).
    - intros a Ha NB. left. exact (victim_ownedC a NB).
  Qed.

  (* [comment removed for export] *)
  Theorem free_hiddenC : hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    hidden_repr (a_pl A) (a_reg A) (a_sec A) (munrestrict (hidc (pa_hull A)) m v').
  Proof.
    intros [H1 H2]. unfold hidden_repr. unfold munrestrict.
    assert (VIS : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> v' (wz z) <> None).
    { intros z Hz Hm E. apply NNoC; [lia| lia| lia|]. unfold aview_of, mrestrict. rewrite E. exact Hm. }
    split.
    - intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _].
      destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (conj P1 P2)|]. split.
      + apply VIS; [unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in Hz; kung_all; lia| exact P1| exact E].
      + intros NHS. rewrite <- (P2 NHS).
        transitivity (aview_of (pa_hull A) m (wz z)); [| unfold aview_of, mrestrict; rewrite E; reflexivity].
        pose proof (GEO A v p n0 li sp AR LU LN) as G. geop3. (first [ pose proof ((carved_shadow A v AR ch CVoC)) as dR_4; dand3 dR_4 as CE' CHS _ | pose proof (carved_shadow A v AR ch CVoC) as (CE' & CHS & _) ]).
        (first [ dand18 G as PM CL1 L1 L2 CL2 NR R8 PU T1 T2 N1 N2 F1 F2 S1 S2 CEQ SPR | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & PU & T1 & T2 & N1 & N2 & F1 & F2 & S1 & S2 & CEQ & SPR) ]).
        assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
        pose proof (sh_mono _ _ L1) as SMa. pose proof (sh_mono _ _ L2) as SMb. pose proof (sh_mono (p + -16) p ltac:(lia)) as SMc.
        unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in Hz. unfold ASTK in *.
        apply MU; [kung_all; lia| |].
        * unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; try (kung_all; lia).
          apply NHS. exact (CHS z ltac:(lia)).
        * intros HB. destruct (BXW z HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|H]]]]; [| kung_all; lia| kung_all; lia| | unfold xblk, ia_blk, gq_blk in H; kung_all; lia].
          -- pose proof (batch_range A v AR b Hb). kung_all. lia.
          -- pose proof (carved_prim_where A v AR _ _ (cached_carved A v AR kQuarantineBatchClass k ltac:(unfold kQuarantineBatchClass; lia) Ck)). kung_all. lia.
    - intros z Hz NB. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (H2 z Hz NB)|]. apply VIS; [unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NB)| exact E].
  Qed.
End FreeOwnC.

(* [comment removed for export] *)
Section CEILW.
Context {Clg : Ceiling}.
Lemma frame_ok_widen : forall (ow ow' vic nb : Z -> Prop) (w w' : mem) (usp lo hi : Z),
  usp <= hi ->
  frame_ok LPA ow ow' usp (usp - lo) vic nb w w' ->
  (forall a, usp <= a < hi -> w' (wz a) = w (wz a)) -> mapped w usp (hi - usp) ->
  frame_ok LPA ow ow' hi (hi - lo) vic nb w w'.
Proof.
  (intros ow ow' vic nb w w' usp lo hi LE; (first [ intro dR_9; dand7 dR_9 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ]); intros AGH MH). unfold frame_ok.
  replace (usp - (usp - lo)) with lo in * by lia. replace (hi - (hi - lo)) with lo by lia.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption.
  - intros a Ha NO NO' NW. apply (F1 a Ha NO NO'). clear -NW LE. lia.
  - intros k Hk. destruct (Z.lt_ge_cases (lo + k) usp) as [B|B].
    + apply F3. lia.
    + rewrite (AGH (lo + k)) by lia. replace (lo + k) with (usp + (lo + k - usp)) by lia. apply MH. lia.
Qed.
End CEILW.
