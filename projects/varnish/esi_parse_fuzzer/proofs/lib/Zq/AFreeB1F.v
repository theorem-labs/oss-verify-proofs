(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 AMTac AMallocA AMalmys AMaldga AMalkbe ATransp AFreeB1 AFreeB3 AFreeFS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).

(* [comment removed for export] *)
Lemma class_of_7000 : class_of 7000 = kQuarantineBatchClass.
Proof. vm_compute. reflexivity. Qed.
Lemma max_count_24 : max_count kQuarantineBatchClass = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma refill_count_24 : refill_count kQuarantineBatchClass = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma skipn_last1 : forall (l : list Z), l <> [] -> skipn (length l - 1) l = [nth (length l - 1) l 0].
Proof.
  intros l NE. induction l as [|x l IH]; [congruence|]. destruct l as [|y l']; [reflexivity|].
  specialize (IH ltac:(discriminate)).
  replace (length (x :: y :: l') - 1)%nat with (S (length (y :: l') - 1))%nat by (cbn [length]; lia).
  set (k := (length (y :: l') - 1)%nat) in *. cbn [skipn nth]. exact IH.
Qed.

Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kCompactPtrScale, kQuarantineBatchBytes in *.

Section F24.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.   (* [comment removed for export] *)
  Let v := aview_of (pa_hull A) m.
  Local Notation fr := (rg_free (a_reg A kQuarantineBatchClass)).
  Local Notation nf := (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass)))).
  Local Notation kb := (nth (length (rg_free (a_reg A kQuarantineBatchClass)) - 1) (rg_free (a_reg A kQuarantineBatchClass)) 0).
  Local Notation sb := (a_sb A).
  Local Notation ri := (a_ri A).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation b := (chunk_addr (a_sb A) kQuarantineBatchClass (nth (length (rg_free (a_reg A kQuarantineBatchClass)) - 1) (rg_free (a_reg A kQuarantineBatchClass)) 0)).
  (* [comment removed for export] *)
  Hypothesis CI : a_cache_inited A = true.
  Hypothesis E24 : pk_chunks (a_cache A kQuarantineBatchClass) = [].
  Hypothesis NF1 : 1 <= Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v. Proof. exact (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let N24R : 1 <= 7000 <= kMaxPrimaryUser. Proof. unfold kMaxPrimaryUser. lia. Qed.
  Let C24 : 1 <= kQuarantineBatchClass <= 30. Proof. unfold kQuarantineBatchClass. lia. Qed.
  Let EMP' : pk_chunks (a_cache A (class_of 7000)) = []. Proof. rewrite class_of_7000. exact E24. Qed.
  Let ENOUGH' : refill_count (class_of 7000) <= Z.of_nat (length (rg_free (a_reg A (class_of 7000)))).
  Proof. rewrite class_of_7000, refill_count_24. exact NF1. Qed.

  (* [comment removed for export] *)
  Lemma f24_PC : exists ks, length ks = 16%nat /\
    rw_cells rsegs v (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)].
  Proof.
    (first [ pose proof ((ref_PC A m md 7000 AI N24R CI EMP')) as dR_1; dex1 dR_1 as ks; destruct dR_1 as [L X] | pose proof ((ref_PC A m md 7000 AI N24R CI EMP')) as dR_1; dand3 dR_1 as ks L X | destruct (ref_PC A m md 7000 AI N24R CI EMP') as (ks & L & X) ]). rewrite class_of_7000, max_count_24, class_size_24 in X.
    exists ks. split; [exact L|]. unfold kQuarantineBatchBytes, kQuarantineBatchClass in X.
    replace (thr + 208 + 80 * 24) with (thr + 208 + 1920) in X by lia. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma f24_kidx : In kb fr /\ 0 <= kb < carved_count A kQuarantineBatchClass /\ nth_error fr (length fr - 1) = Some kb /\ fr <> [].
  Proof. pose proof (ref_kidx A m md 7000 AI N24R ENOUGH') as X. rewrite class_of_7000 in X. exact X. Qed.
  Lemma f24_nf : 1 <= nf < 2^27 /\ 4 * nf <= rg_mapped_fa (a_reg A kQuarantineBatchClass).
  Proof. pose proof (ref_nf A m md 7000 AI N24R ENOUGH') as X. rewrite class_of_7000, refill_count_24 in X. exact X. Qed.

  (* [comment removed for export] *)
  Lemma f24_region : exists na : word,
    rw_cells rsegs v (ri + 3072) [C8 (wz 0)] /\
    rw_cells rsegs v (ri + 3072 + 16) [C8 (wz nf)] /\
    rw_cells rsegs v (ri + 3072 + 72) [C8 na] /\
    u32arr rsegs v (free_array_of sb 24 + 4 * (nf - 1)) [wz (kb * 512)].
  Proof.
    (first [ pose proof ((ref_region A m md 7000 AI N24R ENOUGH')) as dR_2; dex1 dR_2 as na; dand4 dR_2 as X1 X2 X3 X4 | pose proof ((ref_region A m md 7000 AI N24R ENOUGH')) as dR_2; dand5 dR_2 as na X1 X2 X3 X4 | destruct (ref_region A m md 7000 AI N24R ENOUGH') as (na & X1 & X2 & X3 & X4) ]). rewrite class_of_7000 in X1, X2, X3, X4. rewrite refill_count_24 in X4.
    unfold kQuarantineBatchClass in X1, X2, X3, X4. replace (128 * 24) with 3072 in X1, X2, X3 by lia.
    exists na. split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    unfold ref_ws in X4. (first [ dand4 f24_kidx as _ _ _ NE | destruct f24_kidx as (_ & _ & _ & NE) ]). unfold kQuarantineBatchClass in NE.
    change (Z.to_nat 1) with 1%nat in X4. rewrite (skipn_last1 _ NE) in X4. cbn [map] in X4.
    change (class_size 24) with 8192 in X4. unfold kCompactPtrScale in X4.
    replace (nth (length (rg_free (a_reg A 24)) - 1) (rg_free (a_reg A 24)) 0 * 8192 / 16) with (nth (length (rg_free (a_reg A 24)) - 1) (rg_free (a_reg A 24)) 0 * 512) in X4; [exact X4|].
    apply Z.div_unique_exact; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma f24_ri : ri = sb + kSpaceSize /\ kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling /\ ri mod 128 = 0 /\ sb mod 4096 = 0 /\
                 kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Proof.
    (first [ pose proof ((ref_ri A m md 7000 AI)) as dR_4; dand6 dR_4 as X1 X2 X3 X4 X5 _ | pose proof (ref_ri A m md 7000 AI) as (X1 & X2 & X3 & X4 & X5 & _) ]). (first [ pose proof ((sb_facts A W)) as dR_5; dand5 dR_5 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; kung_all; lia.
  Qed.
  Lemma f24_sep : apart thr 4096 ri 4096 /\ apart ri 4096 sb (2^37) /\ apart ri 4096 (p_ctx (a_pl A)) 0x10000 /\
                  apart ri 4096 (p_nodes0 (a_pl A)) kDepotNodesBlock /\ apart ri 4096 (p_frames0 (a_pl A)) kStackStoreBlockBytes /\
                  apart thr 4096 sb (2^37) /\ apart (p_nodes0 (a_pl A)) kDepotNodesBlock sb (2^37) /\ apart (p_frames0 (a_pl A)) kStackStoreBlockBytes sb (2^37).
  Proof.
    (first [ pose proof ((ref_sep A m md 7000 AI)) as dR_6; dand5 dR_6 as X1 X2 X3 X4 X5 | pose proof (ref_sep A m md 7000 AI) as (X1 & X2 & X3 & X4 & X5) ]).
    assert (Y3 : apart ri 4096 (p_ctx (a_pl A)) 0x10000) by (revert X3; clear; unfold apart; intros; lia).
    assert (Y4 : apart ri 4096 (p_nodes0 (a_pl A)) kDepotNodesBlock) by (revert X4; clear; unfold apart; intros; lia).
    assert (Y5 : apart ri 4096 (p_frames0 (a_pl A)) kStackStoreBlockBytes) by (revert X5; clear; unfold apart; intros; lia).
    (first [ pose proof ((bm_nth_fixed A)) as dR_7; dand10 dR_7 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    (first [ pose proof ((sb_facts A W)) as dR_8; dand5 dR_8 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
    assert (B6 : forall i b0 s, i <> 0%nat -> nth_error (big_maps A) i = Some (b0, s) -> apart b0 s sb (2^37)).
    { intros i b0 s Hi Hn. destruct (bm_sep A i 0 _ _ _ _ W Hn E0 Hi); unfold apart, a_sb, a_b6, kSpaceReserve, kSpaceSize in *; lia. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption.
    - exact (B6 4%nat _ _ ltac:(lia) E4).
    - exact (B6 7%nat _ _ ltac:(lia) E7).
    - exact (B6 8%nat _ _ ltac:(lia) E8).
  Qed.
  Lemma f24_CRI : ro_cells rsegs v 0xb1588 [C8 (wz ri)].
  Proof. exact (ref_CRI A m md 7000 AI N24R). Qed.
  Lemma f24_CSB : ro_cells rsegs v 0xb1578 [C8 (wz sb)].
  Proof. exact (hit_SBc A m md AI). Qed.

  (* [comment removed for export] *)
  Lemma f24_carved : carved A (ChP (CP kQuarantineBatchClass kb)).
  Proof. exact (free_carved A v AR _ _ C24 (proj1 f24_kidx)). Qed.
  Lemma f24_geom :
    b = sb + 24 * 2^32 + 16 * (kb * 512) /\ 0 <= kb * 512 < 2^32 /\
    kHighMemBeg <= b /\ b + 8192 <= alloc_ceiling /\ b + 8192 <= free_array_of sb 24 /\
    region_beg sb kQuarantineBatchClass <= b /\ b + 8192 <= region_beg sb kQuarantineBatchClass + rg_mapped_user (a_reg A kQuarantineBatchClass).
  Proof.
    pose proof (AMaldga.free_geom A m md 7000 kb AI N24R ltac:(rewrite class_of_7000; exact (proj1 f24_kidx))) as G. rewrite class_of_7000, class_size_24 in G.
    (first [ dand16 G as G1 _ _ G4 G5 _ G7 G8 G9 G10 _ _ _ _ G15 G16 | destruct G as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & G9 & G10 & _ & _ & _ & _ & G15 & G16) ]).
    pose proof (carved_prim_where A v AR _ _ f24_carved) as WB. pose proof alloc_ceiling_val as CE.
    assert (E512 : kb * kQuarantineBatchBytes / kCompactPtrScale = kb * 512) by (symmetry; apply Z.div_unique_exact; unfold kQuarantineBatchBytes, kCompactPtrScale; lia).
    rewrite E512 in G1, G15. unfold free_array_of, kQuarantineBatchClass in *. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.
  Lemma f24_BC : exists bj0 bj1 bj2 bj3 : word, rw_cells rsegs v b [C8 bj0; C8 bj1; C8 bj2; C8 bj3].
  Proof.
    (first [ pose proof (f24_geom) as dR_10; dand7 dR_10 as BE KR BLO BHI BFA R1 R2 | pose proof f24_geom as (BE & KR & BLO & BHI & BFA & R1 & R2) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24)) as dR_11; dand13 dR_11 as _ _ _ _ _ _ _ _ _ _ _ _ RM24 | destruct (ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RM24) ]). change (p_sb (a_pl A)) with sb in RM24.
    assert (BM : mapped v b 8192).
    { intros i Hi. replace (b + i) with (region_beg sb kQuarantineBatchClass + (b - region_beg sb kQuarantineBatchClass + i)) by lia. apply RM24. lia. }
    destruct (mapped_C8 v b ltac:(intros i Hi; apply BM; lia) ltac:(kung_all; lia) ltac:(lia)) as [bj0 BC0].
    destruct (mapped_C8 v (b + 8) ltac:(intros i Hi; replace (b + 8 + i) with (b + (8 + i)) by lia; apply BM; lia) ltac:(kung_all; lia) ltac:(lia)) as [bj1 BC1].
    destruct (mapped_C8 v (b + 16) ltac:(intros i Hi; replace (b + 16 + i) with (b + (16 + i)) by lia; apply BM; lia) ltac:(kung_all; lia) ltac:(lia)) as [bj2 BC2].
    destruct (mapped_C8 v (b + 24) ltac:(intros i Hi; replace (b + 24 + i) with (b + (24 + i)) by lia; apply BM; lia) ltac:(kung_all; lia) ltac:(lia)) as [bj3 BC3].
    exists bj0, bj1, bj2, bj3.
    apply (rw_cells_app_join _ _ [C8 bj0] [C8 bj1; C8 bj2; C8 bj3]); [exact BC0|]. cbn [cells_size csize Nat.add]. replace (b + Z.of_nat 8) with (b + 8) by lia.
    apply (rw_cells_app_join _ _ [C8 bj1] [C8 bj2; C8 bj3]); [exact BC1|]. cbn [cells_size csize Nat.add]. replace (b + 8 + Z.of_nat 8) with (b + 16) by lia.
    apply (rw_cells_app_join _ _ [C8 bj2] [C8 bj3]); [exact BC2|]. cbn [cells_size csize Nat.add]. replace (b + 16 + Z.of_nat 8) with (b + 24) by lia. exact BC3.
  Qed.
  (* [comment removed for export] *)
  Lemma f24_bsep : apart b 8192 thr 4096 /\ apart b 8192 (p_ctx (a_pl A)) 0x10000 /\
                   apart b 8192 (p_nodes0 (a_pl A)) kDepotNodesBlock /\ apart b 8192 (p_frames0 (a_pl A)) kStackStoreBlockBytes /\ apart b 8192 ri 4096.
  Proof.
    pose proof f24_carved as CKB. pose proof (c24_range A kb) as [L H]. pose proof class_size_24 as CS.
    pose proof (carved_apart_thr A v AR _ CKB) as Dt. pose proof (carved_apart_ctx A v AR _ CKB) as Dc.
    pose proof (carved_apart_n0 A v AR _ CKB) as Dn. pose proof (carved_apart_f0 A v AR _ CKB) as Df.
    rewrite L, H in Dt, Dc, Dn, Df. pose proof (carved_prim_where A v AR _ _ CKB) as WB. pose proof f24_ri as (RI & _).
    unfold apart. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma f24_STA : exists statv : word, rw_cells rsegs v (thr + 208 + 2576) [C8 statv].
  Proof.
    (first [ pose proof ((ar_cache _ _ _ _ _ (proj2 AR))) as dR_12; dand5 dR_12 as _ _ _ TM _ | destruct (ar_cache _ _ _ _ _ (proj2 AR)) as (_ & _ & _ & TM & _) ]). (first [ pose proof ((hit_place A m md AI)) as dR_13; dand3 dR_13 as TH1 TH2 _ | pose proof (hit_place A m md AI) as (TH1 & TH2 & _) ]). pose proof alloc_ceiling_val as CE.
    destruct (mapped_C8 v (thr + 208 + 2576) ltac:(intros i Hi; replace (thr + 208 + 2576 + i) with (thr + (2784 + i)) by lia; apply TM; lia)
                ltac:(apply aobj_facts in TH1; kung_all; lia) ltac:(lia)) as [statv STA].
    exists statv. exact STA.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section LiveChunk.
  Variables (p n0 : Z) (li : liveinfo).
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Local Notation r8 := ((n0 + 7) / 8).

  Lemma f24_psep : apart b 8192 (p + -16) (8 * r8 + 16) /\
                   apart ri 4096 (p + -16) (8 * r8 + 16) /\
                   apart (sb + 24 * 2^32 + 3758096384) (4 * 2^27) (p + -16) (8 * r8 + 16).
  Proof.
    pose proof (GEO A v p n0 li (wz 0) AR LU LN) as G. (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]).
    pose proof (KN A v p n0 li AR LU LN) as KNp. pose proof (known_carved A v AR _ _ KNp) as CVp.
    pose proof f24_carved as CKB. pose proof (c24_range A kb) as [L H]. pose proof class_size_24 as CS.
    pose proof (carved_disjoint A v AR _ _ CKB CVp ltac:(intros E; exact (live_not_free A v AR p li kQuarantineBatchClass kb LU C24 (proj1 f24_kidx) (eq_sym E)))) as D.
    rewrite L, H in D. pose proof f24_ri as (RI & _). pose proof (carved_prim_where A v AR _ _ CKB) as WB.
    split; [unfold apart; kung_all; lia|].
    (* [comment removed for export] *)
    rewrite <- LN in *. destruct (li_chunk li) as [[c' k']|s] eqn:ECH.
    - pose proof CVp as [Hc' _]. pose proof (carved_prim_where A v AR c' k' CVp) as W'. cbn [chunk_lo chunk_hi alloc_beg] in L1, L2.
      assert (RB : region_beg sb c' = sb + c' * 2^32) by (unfold region_beg; kung_all; lia).
      assert (RB24 : region_beg sb kQuarantineBatchClass = sb + 24 * 2^32) by (unfold region_beg, kQuarantineBatchClass; kung_all; lia).
      unfold apart. kung_all. split; [lia|]. destruct (Z.le_gt_cases c' 24); [| lia]. destruct (Z.eq_dec c' 24); [subst c'; lia| nia].
    - unfold carved in CVp. pose proof (sec_apart_b6 A v AR s CVp) as D6. destruct s as [mb n1]. cbn [chunk_lo chunk_hi cs_map cs_n] in L1, L2, D6.
      unfold apart. kung_all. lia.
  Qed.
  End LiveChunk.
End F24.

(* [comment removed for export] *)
Lemma batch_not_free {Clg : Ceiling} : forall (A : AState) (v : mem),
  WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v ->
  forall b c' k, In b (a_qthread A ++ a_qglobal A) -> 1 <= c' <= 30 -> p_free_ (a_reg A) c' k ->
  ChP (CP kQuarantineBatchClass (ba_idx b)) <> ChP (CP c' k).
Proof.
  intros A v AR b c' k Hb Hc F E. injection E as <- <-. pose proof (batch_known A v AR b Hb) as [Hk _].
  pose proof (wfX A (proj1 AR) kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) Hk) as X. cbv zeta in X.
  (first [ dand6 X as _ _ _ _ NFB _ | destruct X as (_ & _ & _ & _ & NFB & _) ]). apply NFB. split; [exact F|]. split; [reflexivity|]. unfold batch_indices_. apply in_map. exact Hb.
Qed.
