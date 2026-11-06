(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMalmys.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB2 ATransp AFreeB3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module AFreeB3R.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB2 ATransp AFreeB3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@B1R; @FIDR; @NR; @CL1; @L1; @Gc; @L2; @Hz; @R8; @Hi; @PU; @PL; @H; @SHP; @AB16; @PM; @CM2; @G'; @E; @RZ; @Q3; @Ha; @Q4; @Q1; @Q5; @MB; @Hc; @W; @RB'; @SM1; @SM3; @Q6; @ABlo; @RSB; @D; @SE; @SM2; @T1; @TA; @T2; @NZ; @CL2; @Hc'; @ABM; @Hn; @T3; @T5; @E2; @T4])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac alc_h H := cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
       al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks al_internal_alloc_inited al_internal_allocator_inst
       al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore al_tp AL_pasan cl_tp cl_shared cl_consts cl_segs LPA] in H.
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

Section FreeRepr.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (v : mem) (p n0 : Z) (li : liveinfo) (sp : word) (v' : mem) (lo : Z).
  Hypothesis AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp.
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation ch := (li_chunk li).
  Local Notation r8 := ((n0 + 7) / 8).
  Local Notation n0a := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation qt := (a_qthread A).
  Local Notation qg := (a_qglobal A).

  (* [comment removed for export] *)
  Variables (qt' qg' : list batch) (cache' : Z -> pcache) (D' : list (list Z)) (ia' : bool).
  (* [comment removed for export] *)
  Variable BX : Z -> Prop.
  Hypothesis BXW : forall a, BX a ->
       (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes)
    \/ (thr + 2128 <= a < thr + 2208)      (* [comment removed for export] *)
    \/ (thr + 2784 <= a < thr + 2792)      (* [comment removed for export] *)
    \/ (exists k, p_cached_ (a_cache A) kQuarantineBatchClass k /\
                  chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes)
    \/ xblk a.
  (* [comment removed for export] *)
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ W0 lo (bv_unsigned sp) thr p r8 n0a f0 a -> ~ BX a -> v' (wz a) = v (wz a).
  (* [comment removed for export] *)
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  Let WF0 : WF A. Proof. exact (proj1 AR). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (proj2 AR). Qed.

  (* [comment removed for export] *)
  #[using="LN LU AR p v Clg"] Lemma KN : known A ch n0. Proof. rewrite <- LN. exact (known_live A v AR p li LU). Qed.
  #[using="LN LU AR n0 p v Clg"] Lemma CV : carved A ch. Proof. exact (known_carved A v AR _ _ KN). Qed.

  #[using="WF0 LN LU AR v"] Lemma GEO :
    p mod 16 = 0 /\ 0x60a000 <= chunk_lo sb ch /\ chunk_lo sb ch <= p + -16 /\ p + 8 * r8 <= chunk_hi sb ch /\ chunk_hi sb ch <= alloc_ceiling /\
    1 <= n0 < REQ_MAX /\ n0 <= 8 * r8 < n0 + 8 /\ p = user_of sb ch n0 /\
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\
    4096 <= n0a /\ n0a + kDepotNodesBlock <= alloc_ceiling /\ 4096 <= f0 /\ f0 + kStackStoreBlockBytes <= alloc_ceiling /\
    0x7fff8200 <= sh p /\ sh p + r8 <= kHighMemBeg /\
    (140735332483072 <= alloc_ceiling <= 140737479966720) /\ bv_unsigned sp < 2^64.
  (* [comment removed for export] *)
  Proof. (* [comment removed for export] *) eapply AFreeB3.GEO; eassumption. Qed.

  (* [comment removed for export] *)
  #[using="WF0 LN LU AR n0 p v"] Lemma GEOP : aobj (chunk_lo sb ch) (chunk_hi sb ch - chunk_lo sb ch) /\ aobj thr 4096 /\ aobj n0a kDepotNodesBlock /\ aobj f0 kStackStoreBlockBytes.
  Proof. (* [comment removed for export] *) eapply AFreeB3.GEOP; eassumption. Qed.
  (* [comment removed for export] *)
  #[using="WF0 LN LU AR sp v Clg"] Lemma GEOS : (chunk_hi sb ch <= kLowShadowMapBeg /\ 0x7fff8200 <= sh p /\ sh p + r8 <= 0x8fff6e00)
               \/ (kHighMemBeg <= chunk_lo sb ch /\ kHighShadowMapBeg <= sh p /\ sh p + r8 <= kHighMemBeg).
  Proof. (* [comment removed for export] *) eapply AFreeB3.GEOS; eassumption. Qed.
  Ltac geop := let Gc := fresh "Gc" in let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gs := fresh "Gs" in
    (first [ pose proof (GEOP) as dR_19; dand4 dR_19 as Gc Gt Gn Gf | pose proof GEOP as (Gc & Gt & Gn & Gf) ]); aobj_lin1 Gc; aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf;
    pose proof GEOS as Gs; unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR Clg"] Lemma AG_gen : forall a, 0 <= a < 2^64 ->
    ~ (lo <= a < bv_unsigned sp) -> ~ (thr <= a < thr + 4096) ->
    ~ (chunk_lo sb ch <= a < chunk_hi sb ch) ->
    ~ (0x187288 <= a < 0x5d72a8) -> ~ (n0a <= a < n0a + 0x100000) -> ~ (f0 <= a < f0 + 0x800000) -> ~ (sh p <= a < sh p + r8) ->
    ~ (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes) ->
    ~ (exists k, p_cached_ (a_cache A) kQuarantineBatchClass k /\ chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes) ->
    ~ xblk a ->
    v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AG_gen; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li A Clg"] Lemma AGlow : forall a, kLowShadowMapBeg <= a < kHighShadowMapBeg -> ~ (sh p <= a < sh p + r8) -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGlow; eassumption. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) -> ~ xblk a -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGimg; eassumption. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGshared : forall a, cl_shared LPA a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGimg; unfold xblk, ia_blk, gq_blk; lia. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGconst : forall cst a, In cst (cl_consts LPA) -> cst <> ia_pad -> cst <> q_pad -> fst cst <= a < fst cst + Z.of_nat (length (snd cst)) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGconst; eassumption. Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGthr : forall a, thr <= a < thr + 4096 -> a <> thr + 3168 -> ~ (thr + 2824 <= a < thr + 2840) -> ~ (thr + 80 <= a < thr + 112) ->
    ~ (thr + 2128 <= a < thr + 2208) -> ~ (thr + 2784 <= a < thr + 2792) ->
    v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGthr; eassumption. Qed.

  Lemma c24_range : forall k, chunk_lo sb (ChP (CP kQuarantineBatchClass k)) = chunk_addr sb kQuarantineBatchClass k /\
                              chunk_hi sb (ChP (CP kQuarantineBatchClass k)) = chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes.
  Proof. intros k. cbn [chunk_lo chunk_hi alloc_beg]. rewrite class_size_24. split; reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp n0 p Clg"] Lemma AGch : forall ch', carved A ch' -> ch' <> ch ->
    (forall b, In b (qt ++ qg) -> ch' <> ChP (CP kQuarantineBatchClass (ba_idx b))) ->
    (forall k, p_cached_ (a_cache A) kQuarantineBatchClass k -> ch' <> ChP (CP kQuarantineBatchClass k)) ->
    forall a, chunk_lo sb ch' <= a < chunk_hi sb ch' -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGch; eassumption. Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li Clg"] Lemma AGhs : forall z, heap_shadow A z -> ~ (sh p <= z < sh p + r8) -> v' (wz z) = v (wz z).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGhs; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p"] Lemma AGhigh : forall b s a, aobj b s -> b <= a < b + s ->
    (b + s <= thr \/ thr + 4096 <= b) -> (b + s <= n0a \/ n0a + kDepotNodesBlock <= b) -> (b + s <= f0 \/ f0 + kStackStoreBlockBytes <= b) ->
    (forall ch', carved A ch' -> chunk_hi sb ch' <= b \/ b + s <= chunk_lo sb ch') ->
    v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGhigh; eassumption. Qed.

  Local Ltac bm i := let H := fresh in pose proof (bm_nth_fixed A) as H;
    lazymatch i with
    | 1%nat => exact (proj1 (proj2 H)) | 4%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 H)))))
    | 5%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))
    | 6%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))
    | 7%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))
    | 8%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))
    | 14%nat => exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))
    end.

  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGctx : forall a, p_ctx (a_pl A) <= a < p_ctx (a_pl A) + 0x10000 -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGctx; eassumption. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGdtls : forall a, p_dtls (a_pl A) <= a < p_dtls (a_pl A) + 4096 -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGdtls; eassumption. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGfs : forall a, a_fs A <= a < a_fs A + kFakeStackBytes -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGfs; eassumption. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGpa : forall a, p_pa (a_pl A) <= a < p_pa (a_pl A) + kPtrArrayReserve -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGpa; eassumption. Qed.
  (* [comment removed for export] *)
  #[using="WF0 AR n0 v Clg"] Lemma b6_apart : forall i bi si, nth_error (big_maps A) i = Some (bi, si) -> (i <> 0)%nat ->
    a_b6 A + kSpaceReserve <= bi \/ bi + si <= a_b6 A.
  Proof. intros i bi si Hi NZ. destruct (bm_sep A 0 i _ _ _ _ WF0 (proj1 (bm_nth_fixed A)) Hi ltac:(lia)); [left| right]; lia. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGri : forall a, a_ri A <= a < a_ri A + 4096 -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGri; eassumption. Qed.
  #[using="WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGfa : forall c' a, 1 <= c' <= 30 -> free_array_beg sb c' <= a < free_array_beg sb c' + rg_mapped_fa (a_reg A c') -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGfa; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp n0 Clg"] Lemma AGown : forall a, chunk_lo sb ch <= a < chunk_hi sb ch -> ~ (p + -16 <= a < p + -12) -> ~ (p <= a < p + 8) -> v' (wz a) = v (wz a).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGown; eassumption. Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR lo sp n0 p Clg"] Lemma AGsh : forall ch', carved A ch' -> ch' <> ch -> forall z, sh (chunk_lo sb ch') <= z < sh (chunk_hi sb ch') -> v' (wz z) = v (wz z).
  Proof. (* [comment removed for export] *) eapply AFreeB3.AGsh; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (b1 fid : Z).
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 0x7f = kHdrByte1Malloc.
  Hypothesis FIDR : 0 <= fid < 2^32.
  Hypothesis P_unw : rw_cells rsegs v' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis P_hdr : rw_cells rsegs v' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)].
  Hypothesis P_ctx : rw_cells rsegs v' p [C8 (wz fid)].
  Hypothesis P_sh : bytes_at rsegs v' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)).
  Hypothesis P_dr : depot_repL AL_pasan rsegs D' n0a f0 v'.
  Hypothesis P_qc : rw_cells rsegs v' (thr + 80)
     [C8 (wz (Z.of_nat (length qt'))); C8 (wz (qc_first A qt')); C8 (wz (qc_last A qt')); C8 (wz (q_bytes qt'))].
  Hypothesis P_br : batches_repr LPA v' sb qt'.
  Hypothesis P_qcg : let I := al_instance AL_pasan + off_q_cache_list_size in
    u64_at rsegs v' (I + 0) (Z.of_nat (length qg')) /\
    u64_at rsegs v' (I + 8) (match qg' with [] => 0 | b :: _ => batch_addr sb b end) /\
    u64_at rsegs v' (I + 16) (match qg' with [] => 0 | _ => batch_addr sb (last qg' (BA 0 [])) end) /\
    u64_at rsegs v' (I + 24) (q_bytes qg').
  Hypothesis P_brg : batches_repr LPA v' sb qg'.
  Hypothesis P_l24 :
    let e := thr + off_th_per_class kQuarantineBatchClass in let ks := pk_chunks (cache' kQuarantineBatchClass) in
    Z.of_nat (length ks) <= 16 /\
    u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
    (if a_cache_inited A && negb (kQuarantineBatchClass =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count kQuarantineBatchClass) /\ u64_at rsegs v' (e + off_pc_class_size) (class_size kQuarantineBatchClass)
     else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
    (forall i k, nth_error ks i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size kQuarantineBatchClass / kCompactPtrScale)) /\
    junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks))).
  (* [comment removed for export] *)
  Hypothesis IAH : (ia' = a_ia_inited A /\ (forall a, iafoot a -> v' (wz a) = v (wz a))) \/ (ia' = true /\ ia_repr_ LPA AL_pasan true v').
  (* [comment removed for export] *)
  Hypothesis IAL : u8_at rsegs v' 0x144e49 0.
  Hypothesis IAP : bytes_at rsegs v' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0].
  (* [comment removed for export] *)
  Hypothesis QLK : u8_at rsegs v' 0xb20c8 0.
  Hypothesis QPD : bytes_at rsegs v' 0xb20ca [Z_to_bv 8 0; Z_to_bv 8 0].
  (* [comment removed for export] *)
  Hypothesis QT'E : forall e, In e (q_entries (qt' ++ qg')) -> In e (q_entries (qt ++ qg)) \/ e = QE ch n0.
  Hypothesis QT'B : forall b, In b (qt' ++ qg') -> In (ba_idx b) (map ba_idx (qt ++ qg)) \/ p_cached_ (a_cache A) kQuarantineBatchClass (ba_idx b).
  Hypothesis C'O : forall c, c <> kQuarantineBatchClass -> cache' c = a_cache A c.
  Hypothesis C'S : forall k, p_cached_ cache' kQuarantineBatchClass k -> p_cached_ (a_cache A) kQuarantineBatchClass k.

  (* [comment removed for export] *)
  #[using="QPD IAP P_unw FIDR B1R fid b1 R WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma consts_P' : consts_repr_ LPA AL_pasan (a_pl A) v'.
  Proof. (* [comment removed for export] *) eapply AFreeB3.consts_P'; eassumption. Qed.

  #[using="FIDR B1R fid b1 WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGstat_all : forall a, 0x10000 <= a < 0x187288 -> ~ xblk a -> v' (wz a) = v (wz a).
  Proof. intros a Ha Hia. apply AGimg; [lia| lia| exact Hia]. Qed.

  (* [comment removed for export] *)
  #[using="QLK IAL FIDR B1R fid b1 R WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma locks_P'h : forall (held : list Z) (rl : Z), u8_at rsegs v' 0xb20c9 rl ->
    (forall x, lockb held x = if Z.eqb x 0xb20c9 then rl else 0) ->
    locks_repr_ LPA AL_pasan (a_pl A) held v'.
  Proof.
    intros held rl QRL HLD.
    pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    (first [ pose proof ((sb_facts A WF0)) as dR_45; dand5 dR_45 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold a_sb, a_b6 in HB6, RSB, SCE.
    change (al_internal_alloc_inited AL_pasan) with 0x144e48 in *. change (al_instance AL_pasan) with 0xb1d58 in *.
    rewrite lockb_nil in *. rewrite !HLD. cbn [Z.eqb Pos.eqb].
    unfold off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex. cbn [Z.add Pos.add Pos.succ Z.eqb Pos.eqb].
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. unfold p_ri in *.
      split; (eapply u64_at_agree; [eassumption|]; intros i Hi; apply AGri; unfold a_ri, p_ri; unfold kHighMemBeg, kSpaceSize, kRegionInfoSize in *; lia).
    - (first [ dand5 C as L1 L2 L3 L4 L5 | destruct C as (L1 & L2 & L3 & L4 & L5) ]). unfold off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex in *.
      split; [eapply u8_at_agree; [exact L1|]; apply AGstat_all; unfold xblk, ia_blk, gq_blk in *; lia|].
      split; [exact QLK|]. split; [exact QRL|].
      split; [eapply u8_at_agree; [exact L4|]; apply AGstat_all; unfold xblk, ia_blk, gq_blk in *; lia| exact IAL].
  Qed.
  (* [comment removed for export] *)
  #[using="QLK IAL FIDR B1R fid b1 R WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma locks_P'R : u8_at rsegs v' 0xb20c9 1 -> locks_repr_ LPA AL_pasan (a_pl A) [al_instance AL_pasan + off_q_recycle_mutex] v'.
  Proof.
    intros QRL. apply (locks_P'h _ 1 QRL). intros x. unfold lockb. cbn [al_instance AL_pasan]. unfold off_q_recycle_mutex.
    change (728408 + 881) with 0xb20c9. destruct (in_dec Z.eq_dec x [0xb20c9]) as [I|NI].
    - destruct I as [<-|[]]. rewrite Z.eqb_refl. reflexivity.
    - destruct (Z.eqb_spec x 0xb20c9) as [->|NE]; [exfalso; apply NI; left; reflexivity| reflexivity].
  Qed.

  #[using="FIDR B1R fid b1 WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma regions_P' : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (a_reg A c') v' c'.
  Proof. (* [comment removed for export] *) eapply AFreeB3.regions_P'; eassumption. Qed.

  #[using="FIDR B1R fid b1 WF0 cache' AR n0 v Clg"] Lemma sec_map_big : forall sc, In sc (sr_chunks (a_sec A)) -> 8192 <= map_size (cs_n sc).
  Proof. (* [comment removed for export] *) eapply AFreeB3.sec_map_big; eassumption. Qed.

  #[using="FIDR B1R fid b1 WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma sec_P' : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v'.
  Proof. (* [comment removed for export] *) eapply AFreeB3.sec_P'; eassumption. Qed.

  #[using="IAH AR v A Clg"] Lemma ia_P' : ia_repr_ LPA AL_pasan ia' v'.
  Proof. destruct IAH as [[-> AG]|[-> IR]]; [| exact IR]. apply (ia_P A v v' AR). exact AG. Qed.

  #[using="FIDR B1R fid b1 WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma fsbase_P' : fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof. apply (fsbase_P A v v' AR NN). intros a Ha. apply AGfs. unfold kFakeFlagsOffset, kFakeStackBytes in *. lia. Qed.
  #[using="FIDR B1R fid b1 WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma fsptrs_P' : fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsptrs_P A v v' AR). intros a Ha. apply AGfs. unfold kFakeFramesOffset, kFakeStackBytes in *. lia. Qed.
  #[using="FIDR B1R fid b1 WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma fsflags_P' : fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. (* [comment removed for export] *) eapply AFreeB3.fsflags_P'; eassumption. Qed.
  #[using="NN AR v"] Lemma maps_P' : maps_repr_ AL_pasan (a_pl A) v'.
  Proof. exact (maps_P A v v' AR NN). Qed.

  #[using="C'O P_l24 FIDR B1R fid b1 WF0 NN MU BXW BX LO LN LU AR lo sp li n0 p v Clg"] Lemma cache_P' : cache_repr_ LPA (a_pl A) cache' (a_cache_inited A) v'.
  Proof. (* [comment removed for export] *) eapply AFreeB3.cache_P'; eassumption. Qed.

  #[using="FIDR B1R fid b1 WF0 NN MU BXW BX LO LN LU AR lo sp li n0 v Clg"] Lemma live_P' : live_repr_ LPA sb (free_lm A p) v'.
  Proof. (* [comment removed for export] *) eapply AFreeB3.live_P'; eassumption. Qed.

  (* [comment removed for export] *)

  #[using="QT'E P_brg P_qcg P_br P_qc P_ctx P_hdr FIDR B1M B1R fid b1 R WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma quar_P' : quarantine_repr_ LPA AL_pasan (a_pl A) qt' qg' v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_52; dand3 dR_52 as QT QG QR | pose proof (ar_quar _ _ _ _ _ R) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *. pose proof GEO as G. geop.
    split; [|split].
    - (* [comment removed for export] *)
      unfold qcache_repr. offs. (first [ pose proof ((u64x4_of_rw v' _ _ _ _ _ P_qc)) as dR_53; dand4 dR_53 as Y1 Y2 Y3 Y4 | destruct (u64x4_of_rw v' _ _ _ _ _ P_qc) as (Y1 & Y2 & Y3 & Y4) ]).
      replace (thr + 80 + 0) with (thr + 80) by lia.
      split; [rewrite Z.add_0_r in Y1; exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4| exact P_br].
    - (* [comment removed for export] *)
      unfold qcache_repr. pose proof P_qcg as X. cbv zeta in X. (first [ dand4 X as Y1 Y2 Y3 Y4 | destruct X as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4| exact P_brg].
    - (* [comment removed for export] *)
      intros e He. destruct (QT'E e He) as [Hold| ->].
      + apply (quar_entry_P A v v' AR NN e Hold). intros a Ha.
        apply (AGch (qe_chunk e) (known_carved A v AR _ _ (known_quar A v AR e Hold))).
        * intros E. exact (live_not_quar_chunk A v AR p li e LU Hold (eq_sym E)).
        * intros b Hb. exact (quar_not_batch A v AR e b Hold Hb).
        * intros k Ck. apply (quar_not_cached A v AR e kQuarantineBatchClass k Hold); [unfold kQuarantineBatchClass; lia| exact Ck].
        * exact Ha.
      + cbn [qe_chunk qe_n]. (first [ pose proof ((ar_live _ _ _ _ _ R p li LU)) as dR_55; dand3 dR_55 as HR MUo MC | destruct (ar_live _ _ _ _ _ R p li LU) as (HR & MUo & MC) ]). rewrite LN in HR, MUo. change (p_sb (a_pl A)) with sb in HR, MC.
        (first [ dand9 G as PM CL1 L1 L2 CL2 NR R8 PU G' | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & PU & G') ]).
        assert (US : user_size n0 = n0) by (exact (proj2 (proj2 (user_size_pos n0 ltac:(lia))) ltac:(lia))).
        split; [|split].
        * (* [comment removed for export] *)
          destruct HR as [(ido & b10 & IDoR & Hb1 & Hb1m & RC) LH]. unfold hdr_repr_. cbv zeta. rewrite <- PU.
          pose proof RC as CTXo. unfold chunk_hdr_cells in CTXo. cbn [ch_state ch_b1 ch_size ch_ctx] in CTXo. rewrite US, <- PU in CTXo.
          apply (rw_cells_app_split _ _ [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b10); C2 (wz (size_hi n0)); C4 (wz n0)] [C8 (wz ido)]) in CTXo as [_ CTXo].
          cbn [cells_size csize Nat.add] in CTXo. replace (p - 16 + Z.of_nat 8) with (p + -8) in CTXo by lia.
          split.
          -- exists ido, b1. split; [exact IDoR|]. split; [exact B1R|]. split; [exact B1M|].
             unfold chunk_hdr_cells. cbn [ch_state ch_b1 ch_size ch_ctx]. rewrite US.
             apply (rw_cells_app_join _ _ [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] [C8 (wz ido)]).
             ++ replace (p - 16) with (p + -16) by lia. exact P_hdr.
             ++ cbn [cells_size csize Nat.add]. replace (p - 16 + Z.of_nat 8) with (p + -8) by lia.
                eapply rw_cells_agree; [exact CTXo|]. cbn [cells_size csize Nat.add]. intros i Hi. apply AGown; lia.
          -- intros NE16. pose proof NE16 as NE16'. rewrite PU in NE16'. destruct (LH NE16') as [X Y]. rewrite <- PU in Y.
             assert (AB16 : alloc_beg sb ch + 16 <= p - 16).
             { pose proof KN as K. unfold known in K. destruct (li_chunk li) as [[c' k']|[mb n0']] eqn:EC.
               - (first [ dand4 K as Hc Hk Hn Hcl | destruct K as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n0 Hc Hn Hcl)) as dR_58; dand5 dR_58 as _ _ _ _ L4 | pose proof (primary_layout sb c' k' n0 Hc Hn Hcl) as (_ & _ & _ & _ & L4) ]). cbv zeta in L4.
                 cbn [alloc_beg user_of] in *. pose proof (L4 NE16') as L4'. rewrite <- PU in L4'. exact L4'.
               - (first [ dand3 K as Hin Hn -> | destruct K as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n0 Hn)) as dR_60; dand7 dR_60 as _ S2 _ _ S5 S6 _ | pose proof (secondary_layout mb n0 Hn) as (_ & S2 & _ & _ & S5 & S6 & _) ]). cbn [alloc_beg user_of] in *.
                 unfold sec_alloc_beg, sec_user_beg, kPageSize in *. lia. }
             assert (ABlo : chunk_lo sb ch <= alloc_beg sb ch).
             { destruct (li_chunk li) as [[c' k']|[mb n0']]; cbn [chunk_lo alloc_beg]; [lia|]. unfold sec_alloc_beg, kPageSize. lia. }
             split; [eapply u64_at_agree; [exact X|] | eapply u64_at_agree; [exact Y|]]; intros i Hi; apply AGown; lia.
        * destruct P_ctx as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exists (le8 (wz fid)). split; [rewrite length_le8; reflexivity| rewrite <- PU; exact B].
        * apply (mapped_N v v' NN); [kung_all; lia| kung_all; lia| lia| exact MC].
  Qed.

  #[using="P_dr"] Lemma depot_P' : depot_repr_ LPA AL_pasan (a_pl A) D' v'.
  Proof. unfold depot_repr_. cbn [depot_rep DepotRepL]. exact P_dr. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="P_sh FIDR B1R fid b1 WF0 LN LU AR sp li A Clg"] Lemma requar : forall base L rest, 0 <= L ->
    bytes_at rsegs v base (fa8 L ++ shpat n0 ++ rest) -> sh p = base + L ->
    (forall z, base <= z < base + L -> v' (wz z) = v (wz z)) ->
    (forall z, base + L + r8 <= z < base + L + r8 + Z.of_nat (length rest) -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' base (fa8 L ++ fd8 r8 ++ rest).
  Proof. (* [comment removed for export] *) eapply AFreeB3.requar; eassumption. Qed.

  (* [comment removed for export] *)
  #[using="C'S C'O QT'B LU AR p v Clg"] Lemma old_state : forall c k, 1 <= c <= 30 ->
    (p_free_ (a_reg A) c k \/ p_cached_ cache' c k \/ p_batch_ qt' qg' c k) ->
    (p_free_ (a_reg A) c k \/ p_cached_ (a_cache A) c k \/ p_batch_ qt qg c k) /\ carved A (ChP (CP c k)) /\ ChP (CP c k) <> ch.
  Proof. (* [comment removed for export] *) eapply AFreeB3.old_state; eassumption. Qed.

  (* [comment removed for export] *)
  #[using="QT'E FIDR B1R fid b1 WF0 cache' qg' qt' LN LU AR n0 p v Clg"] Lemma tails_apart : forall c', 1 <= c' <= 30 ->
    chunk_hi sb ch <= region_beg sb c' + rg_allocated_user (a_reg A c') \/ region_beg sb c' + kRegionSize <= chunk_lo sb ch.
  Proof.
    intros c' Hc'. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'. change (a_sb A) with sb in *.
    (first [ pose proof ((sb_facts A WF0)) as dR_61; dand5 dR_61 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). change (a_sb A) with sb in *.
    pose proof CV as C. destruct (li_chunk li) as [[c k]|s] eqn:EC.
    - pose proof (carved_prim_where A v AR c k C) as W. change (a_sb A) with sb in W. destruct C as [Hc _]. cbn [chunk_lo chunk_hi alloc_beg].
      destruct (Z.eq_dec c c') as [->|NC]; [left; lia|]. destruct (regions_disjoint sb c c' NC ltac:(lia) ltac:(lia)); [left| right]; kung_all; lia.
    - unfold carved in C. destruct (sec_apart_b6 A v AR s C) as [D|D]; destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *;
        unfold a_b6 in *; [left| right]; kung_all; lia.
  Qed.

  #[using="C'S C'O QT'B QT'E P_sh P_ctx P_hdr FIDR B1R fid b1 R WF0 MU BXW BX LO LN LU AR lo sp li n0 v Clg"] Lemma shadow_P' : shadow_repr_ LPA sb (a_reg A) cache' (free_lm A p) qt' qg' v'.
  Proof.
    (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_62; dand6 dR_62 as S1 S2 S3 S4 S5 S6 | pose proof (ar_shadow _ _ _ _ _ R) as (S1 & S2 & S3 & S4 & S5 & S6) ]). pose proof GEO as G. geop. change (a_sb A) with sb in *.
    (first [ pose proof ((carved_shadow A v AR ch CV)) as dR_63; dand5 dR_63 as CE CHS CHR CM1 CM2 | pose proof (carved_shadow A v AR ch CV) as (CE & CHS & CHR & CM1 & CM2) ]).
    (first [ dand9 G as PM CL1 L1 L2 CL2 NR R8 PU G' | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & PU & G') ]).
    assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
    pose proof (sh_mono _ _ L1) as SM1. pose proof (sh_mono _ _ L2) as SM2. pose proof (sh_mono (p + -16) p ltac:(lia)) as SM3.
    assert (US : user_size n0 = n0) by (exact (proj2 (proj2 (user_size_pos n0 ltac:(lia))) ltac:(lia))).
    split; [|split; [|split; [|split; [|split]]]].
    - (* [comment removed for export] *)
      intros c k Hc ST. (first [ pose proof ((old_state c k Hc ST)) as dR_65; dand3 dR_65 as ST0 CK NEQ | destruct (old_state c k Hc ST) as (ST0 & CK & NEQ) ]).
      apply (shadow_free_P A v v' AR c k Hc ST0). intros z Hz.
      pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi alloc_beg] in E.
      apply (AGsh (ChP (CP c k)) CK NEQ). cbn [chunk_lo chunk_hi alloc_beg]. lia.
    - (* [comment removed for export] *)
      intros u c k n1 Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl].
      apply (shadow_live_P A v v' AR u c k n1 Hl). intros z Hz.
      pose proof (known_carved A v AR _ _ (known_live A v AR u _ Hl)) as CK. cbn [li_chunk] in CK.
      pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi alloc_beg] in E.
      apply (AGsh (ChP (CP c k)) CK); [| cbn [chunk_lo chunk_hi alloc_beg]; lia].
      intros EQ. exact (live_live_chunk A v AR u p _ li Hl LU (fun H => NEu (eq_sym H)) EQ).
    - (* [comment removed for export] *)
      intros c k n1 He. destruct (QT'E _ He) as [Hold|EQ].
      + apply (shadow_quar_P A v v' AR c k n1 Hold). intros z Hz.
        pose proof (known_carved A v AR _ _ (known_quar A v AR _ Hold)) as CK. cbn [qe_chunk] in CK.
        pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi alloc_beg] in E.
        apply (AGsh (ChP (CP c k)) CK); [| cbn [chunk_lo chunk_hi alloc_beg]; lia].
        intros EQ. exact (live_not_quar_chunk A v AR p li _ LU Hold (eq_sym EQ)).
      + injection EQ as EC En. subst n1.
        assert (Hl : a_livemap A !! p = Some (LI (ChP (CP c k)) n0)) by (rewrite LU; destruct li; cbn in EC, LN; subst; reflexivity).
        pose proof (S2 p c k n0 Hl) as B. pose proof KN as K. rewrite <- EC in K. unfold known in K. (first [ dand4 K as Hc Hk Hn Hcl | destruct K as (Hc & Hk & Hn & Hcl) ]).
        (first [ pose proof ((chunk_shadow A v AR c k Hc Hk)) as dR_67; dand4 dR_67 as E HS HR _ | pose proof (chunk_shadow A v AR c k Hc Hk) as (E & HS & HR & _) ]).
        rewrite <- EC in CE, CHS, CL1, CL2, L1, L2, SM1, SM2, PU. cbn [chunk_lo chunk_hi alloc_beg user_of] in CE, CHS, CL1, CL2, L1, L2, SM1, SM2, PU. unfold user_beg in PU.
        (first [ pose proof ((carved_chunk_bounds A c k WF0 Hc Hk)) as dR_68; dand4 dR_68 as _ _ B3 _ | pose proof (carved_chunk_bounds A c k WF0 Hc Hk) as (_ & _ & B3 & _) ]). pose proof (rz_size_range n0) as RZ.
        assert (ABM : chunk_addr sb c k mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]).
        assert (RZM : rz_size n0 mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (rz_size n0 / 8); lia).
        pose proof (sh_add (chunk_addr sb c k) (rz_size n0) ABM RZM) as SHP. rewrite <- PU in SHP.
        pose proof (pshadow_live_length c n0 ltac:(lia) Hcl) as PL. unfold pshadow_live in PL. rewrite !length_app, !Nat2Z.inj_add in PL.
        unfold pshadow_quar. unfold pshadow_live in B. rewrite US in B, PL |- *.
        unfold fa8 in PL. rewrite !repeat_length in PL. rewrite shpat_length in PL by lia.
        apply (requar (sh (chunk_addr sb c k)) (rz_size n0 / 8)); [lia| exact B| lia| |].
        * intros z Hz. apply AGhs; [apply HS; lia| lia].
        * intros z Hz. unfold fa8 in Hz. rewrite !repeat_length in Hz. apply AGhs; [apply HS; lia| lia].
    - (* [comment removed for export] *)
      intros c' Hc'. (first [ pose proof ((region_tail_shadow A v AR c' Hc')) as dR_69; dand7 dR_69 as E1 E1' E2 HS1 HS2 _ M4 | pose proof (region_tail_shadow A v AR c' Hc') as (E1 & E1' & E2 & HS1 & HS2 & _ & M4) ]). cbv zeta in E1, E1', E2, HS1, HS2, M4.
      change (a_sb A) with sb in *. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'. change (a_sb A) with sb in RB'.
      (first [ dand12 RB' as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
      pose proof (tails_apart c' Hc') as TA.
      pose proof (sh_mono (chunk_hi sb ch) (region_beg sb c' + rg_allocated_user (a_reg A c'))) as T1.
      pose proof (sh_mono (region_beg sb c' + kRegionSize) (chunk_lo sb ch)) as T2.
      pose proof (sh_mono (region_beg sb c' + rg_mapped_user (a_reg A c')) (region_beg sb c' + kRegionSize) ltac:(kung_all; lia)) as T3.
      pose proof (sh_mono (region_beg sb c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c')) (region_beg sb c' + kRegionSize) ltac:(kung_all; lia)) as T4.
      pose proof (sh_mono (region_beg sb c' + rg_allocated_user (a_reg A c')) (region_beg sb c' + kFreeArrayOffset) ltac:(kung_all; lia)) as T5.
      apply (shadow_tails_P A v v' AR c' Hc'); intros z Hz; apply AGhs.
      + apply HS1. exact Hz.
      + destruct TA as [TA|TA]; [specialize (T1 TA)| specialize (T2 TA)]; lia.
      + apply HS2. exact Hz.
      + destruct TA as [TA|TA]; [specialize (T1 TA)| specialize (T2 TA)]; lia.
    - (* [comment removed for export] *)
      intros u mb n1 Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl].
      apply (shadow_seclive_P A v v' AR u mb n1 Hl). intros z Hz.
      pose proof (known_carved A v AR _ _ (known_live A v AR u _ Hl)) as CK. cbn [li_chunk] in CK.
      pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi cs_map cs_n] in E.
      apply (AGsh (ChS (CS mb n1)) CK); [| cbn [chunk_lo chunk_hi cs_map cs_n]; lia].
      intros EQ. exact (live_live_chunk A v AR u p _ li Hl LU (fun H => NEu (eq_sym H)) EQ).
    - (* [comment removed for export] *)
      intros mb n2 n1 He. destruct (QT'E _ He) as [Hold|EQ].
      + apply (shadow_secquar_P A v v' AR mb n2 n1 Hold). intros z Hz.
        pose proof (known_quar A v AR _ Hold) as K. pose proof (known_carved A v AR _ _ K) as CK. cbn [qe_chunk qe_n] in CK, K. unfold known in K. (first [ dand3 K as _ _ -> | destruct K as (_ & _ & ->) ]).
        pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi cs_map cs_n] in E.
        apply (AGsh (ChS (CS mb n1)) CK); [| cbn [chunk_lo chunk_hi cs_map cs_n]; lia].
        intros EQ. exact (live_not_quar_chunk A v AR p li _ LU Hold (eq_sym EQ)).
      + injection EQ as EC En. subst n1. pose proof KN as K. rewrite <- EC in K. unfold known in K. (first [ dand3 K as Hin Hn -> | destruct K as (Hin & Hn & ->) ]).
        assert (Hl : a_livemap A !! p = Some (LI (ChS (CS mb n0)) n0)) by (rewrite LU; destruct li; cbn in EC, LN; subst; reflexivity).
        pose proof (S5 p mb n0 Hl) as B.
        (first [ pose proof ((sec_shadow A v AR _ Hin)) as dR_73; dand3 dR_73 as E HS HR | pose proof (sec_shadow A v AR _ Hin) as (E & HS & HR) ]). cbn [cs_map cs_n] in E, HS, HR.
        rewrite <- EC in PU. cbn [user_of] in PU. unfold sec_user_beg, kPageSize in PU. replace (mb + 4096 + 2048) with (mb + 6144) in PU by lia.
        (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_74; dand3 dR_74 as _ MB2 _ | pose proof (sec_chunk_bounds A _ WF0 Hin) as (_ & MB2 & _) ]). cbn [cs_map] in MB2.
        assert (M8 : mb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MB2]).
        pose proof (sh_add mb 6144 M8 eq_refl) as SHP. change (6144 / 8) with 768 in SHP. rewrite <- PU in SHP.
        pose proof (sshadow_live_length n0 Hn) as PL. unfold sshadow_live in PL. rewrite !length_app, !Nat2Z.inj_add in PL.
        unfold sshadow_quar. unfold sshadow_live in B. rewrite US in B, PL |- *.
        unfold fa8 in PL. rewrite !repeat_length in PL. rewrite shpat_length in PL by lia. pose proof (sec_map_big _ Hin) as MB. cbn [cs_n] in MB.
        apply (requar (sh mb) 768); [lia| exact B| lia| |].
        * intros z Hz. apply AGhs; [apply HS; lia| lia].
        * intros z Hz. unfold fa8 in Hz. rewrite !repeat_length in Hz. apply AGhs; [apply HS; lia| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="C'S C'O QT'B QT'E QPD QLK IAP IAL IAH P_l24 P_brg P_qcg P_br P_qc P_dr P_sh P_ctx P_hdr P_unw FIDR B1M B1R fid b1 R WF0 NN MU BXW BX LO LN LU AR lo sp li n0 v"] Theorem free_arepr2R : u8_at rsegs v' 0xb20c9 1 -> @arepr _ DepotRepL LPA AL_pasan [al_instance AL_pasan + off_q_recycle_mutex] (freeA A p qt' qg' cache' D' ia') v'.
  Proof.
    intros QRL.
    constructor; cbn [freeA a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes a_qlimbo a_scred a_deadsh].
    - exact consts_P'. - exact (locks_P'R QRL). - exact regions_P'. - exact cache_P'. - exact live_P'. - exact quar_P'. - exact sec_P'.
    - exact depot_P'. - exact ia_P'. - exact fsbase_P'. - exact fsptrs_P'. - exact fsflags_P'. - exact maps_P'. - exact shadow_P'.
  Qed.
End FreeRepr.
End AFreeB3R.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

Section FreeOwn.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (li : liveinfo) (sp : word) (v' : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
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
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ W0 (bv_unsigned sp - ASTK) (bv_unsigned sp) thr p r8 n0a f0 a -> ~ BX a -> v' (wz a) = v (wz a).
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis SM : mapped v (bv_unsigned sp - ASTK) ASTK.
  Local Notation A' := (freeA A p qt' qg' cache' D' ia').

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI)). Qed.

  Lemma wmono_NN : forall (w w' : mem) a, wmono rsegs w w' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
    w (wz a) <> None -> w' (wz a) <> None.
  Proof.
    intros w w' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
    rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
    destruct (w (wz a)); [| congruence]. destruct (w' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac geop3 := let Gc := fresh "Gc" in let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gs := fresh "Gs" in
    (first [ pose proof ((GEOP A v p n0 li AR LU LN)) as dR_1; dand4 dR_1 as Gc Gt Gn Gf | pose proof (GEOP A v p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]); aobj_lin1 Gc; aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf;
    pose proof (GEOS A v p n0 li sp AR LU LN) as Gs; unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End FreeOwn.
