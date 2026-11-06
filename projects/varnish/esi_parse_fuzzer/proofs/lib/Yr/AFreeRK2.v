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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSrgm AMalmys AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf ATransp ATranspR AFreeRS AFreeRX AFreeRI AFreeRT.

Module AFreeRK.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSrgm AMalmys ANodeA7 ASecB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf ATransp ATranspR AFreeRS AFreeRT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section BusyKit.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (held : list Z).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis CI : a_cache_inited A = true.

  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan held A v. Proof. exact (proj2 AR). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).

  Let CF : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ R)). Qed.
  Let CR : consts_repr_ LPA AL_pasan (a_pl A) v.
  Proof. exact (ar_consts _ _ _ _ _ R). Qed.
  Ltac cell H a bs := pose proof (consts_cell v a bs CF eq_refl) as H.
  Ltac crtac := pose proof CR as C; unfold consts_repr_ in C; cbv zeta in C;
    cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory
         al_page_size_cache al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan cl_tp cl_shared cl_consts cl_segs LPA] in C;
    rewrite ?unsigned_lit in C by lia;
    unfold off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in C.

  (* [comment removed for export] *)
  #[using="CR CF R AR held A Clg"] Lemma rk_PCo : poison_consts v.
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var AL_pasan] in C.
    unfold poison_consts.
    cell H1 0xb4c1c [Z_to_bv 8 1]. cell H2 0xa9180 (le8 (Z_to_bv 64 0x146ee8)). cell H3 0xa9190 (le8 (Z_to_bv 64 0xb53b8)).
    cell H4 0xb53b8 (le8 (Z_to_bv 64 kShadowOffset)). cell H5 0xa9198 (le8 (Z_to_bv 64 0xb60a8)). cell H6 0xa91a0 (le8 (Z_to_bv 64 0xb60b0)).
    cell H7 0xa91a8 (le8 (Z_to_bv 64 0xb60a0)). cell H8 0xa91b0 (le8 (Z_to_bv 64 0xab038)). cell H9 0xab038 (le8 (Z_to_bv 64 0xa25c8)).
    cell H10 0xa9170 (le8 (Z_to_bv 64 0x144e60)). cell H11 0x144e60 (le8 (Z_to_bv 64 4096)).
    assert (K1 : u64_at rsegs v 745632 kHighMemEnd) by tauto. assert (K2 : u64_at rsegs v 745640 0) by tauto. assert (K3 : u64_at rsegs v 745648 0) by tauto.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try (apply bytes_ro_C8; assumption); try (apply bytes_ro_C1; assumption).
    - cell H 0x146ee8 pa_common_flags_bytes. apply bytes_ro_C8.
      apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 120 8 H ltac:(cbn; lia))). byteseq.
    - split; [exact (conj I (conj I (conj I I)))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. split; [exact K1|]. rewrite length_le8. apply bytes_at_app. split; [exact K2|]. rewrite length_le8. exact K3.
  Qed.

  (* [comment removed for export] *)
  #[using="CR R AR held A Clg"] Lemma rk_CPMH : ro_cells rsegs v 0xb1d90 [C1 (Z_to_bv 8 0)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u8_at rsegs v (728408 + off_PremappedHeap) 0) by tauto. apply u8_ro. exact X.
  Qed.
  #[using="CF R AR held A Clg"] Lemma rk_CGCF : ro_cells rsegs v 0xa9180 [C8 (wz ANodeA7.CF)].
  Proof. cell H 0xa9180 (le8 (Z_to_bv 64 0x146ee8)). rewrite CF_eq. apply bytes_ro_C8. exact H. Qed.
  #[using="CF R AR held A Clg"] Lemma rk_CDMP : ro_cells rsegs v (ANodeA7.CF + 260) [C1 (Z_to_bv 8 0)].
  Proof.
    cell H 0x146ee8 pa_common_flags_bytes. rewrite CF_eq. apply bytes_ro_C1.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 260 1 H ltac:(cbn; lia))). byteseq.
  Qed.

  #[using="CR R AR held Clg"] Lemma rk_SBc : ro_cells rsegs v 0xb1d78 [C8 (wz sb)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_SpaceBeg) (p_sb (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.
  #[using="CR R AR held Clg"] Lemma rk_CRI : ro_cells rsegs v RI_PTR [C8 (wz ri)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_RegionInfo_ptr) (p_ri (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.
  #[using="CR R AR held A Clg"] Lemma rk_CITV : ro_cells rsegs v 0xb1d80 [C4 (wz 4294967295)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u32_at rsegs v (728408 + off_release_interval) 0xffffffff) by tauto. apply u32_ro. exact X.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="CR CF R AR held Clg"] Lemma rk_tsd : u64_at rsegs v (0x5e83d8 - 88) pa_tsd /\ u64_at rsegs v pa_tsd (p_ctx P).
  Proof.
    crtac. destruct C as (_ & C). do 30 apply proj2 in C.
    lazymatch type of C with context [exists tsd, _] => idtac end.
    repeat match type of C with | (exists t, _) /\ _ => idtac | _ /\ _ => apply proj2 in C end.
    destruct C as ((tsd & T1 & _ & T2) & _).
    cell H 0x5e8380 (le8 (Z_to_bv 64 0x609780)). change (0x5e83d8 - 88) with 0x5e8380 in *.
    pose proof (bytes_at_bound _ _ _ _ T2) as B. rewrite length_le8 in B.
    assert (E : tsd = pa_tsd).
    { apply le8_wz_inj; [lia| unfold pa_tsd; lia|]. apply (bytes_at_inj v 0x5e8380); [exact T1| exact H| rewrite !length_le8; reflexivity]. }
    subst tsd. split; [exact T1| exact T2].
  Qed.

  #[using="W AR held v"] Lemma rk_place : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling /\ thr mod 16 = 0 /\
                   aobj (p_ctx P) 0x10000 /\ p_ctx P + 0x10000 <= alloc_ceiling /\
                   0 <= p_stk_top P < 2^64 /\ 0 <= p_stk_bot P < 2^64.
  Proof.
    (first [ pose proof ((place_factsT A W)) as dR_1; dand14 dR_1 as Pthr Pctx _ _ _ _ _ _ _ _ _ _ _ Ptb | pose proof (place_factsT A W) as (Pthr & Pctx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ptb) ]). cbv zeta in Pthr, Pctx, Ptb.
    pose proof alloc_ceiling_val as CE.
    (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). (first [ dand3 Pctx as Pctx1 Pctx2 Pctx3 | destruct Pctx as (Pctx1 & Pctx2 & Pctx3) ]).
    apply (proj1 (aobj_app_rangeA _ _)) in Pthr1. apply (proj1 (aobj_app_rangeA _ _)) in Pctx1.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia | apply (mod0_down _ 4096 16); [exists 256; reflexivity| assumption]].
  Qed.

  #[using="CR CF R W AR held"] Lemma rk_TC : thread_cells v (cl_tp LPA) pa_tsd (p_ctx P) thr.
  Proof.
    destruct rk_tsd as [T1 T2]. crtac. pose proof rk_place as PL. pose proof alloc_ceiling_val as CE.
    cell H1 0xb4c20 [Z_to_bv 8 1]. cell H2 0xb4c24 (le4 (Z_to_bv 64 0)).
    assert (T3 : u64_at rsegs v (p_ctx P + 152) (p_thr P)) by tauto.
    unfold thread_cells. cbn [cl_tp LPA]. rewrite unsigned_lit by lia.
    split; [apply bytes_ro_C1; exact H1|]. split; [apply bytes_ro_C4; exact H2|].
    split; [apply u64_ro; exact T1|]. split; [apply u64_ro; exact T2|]. split; [apply u64_ro; exact T3|].
    (first [ dand6 PL as PL1 PL2 PL3 PL4 PL5 _ | destruct PL as (PL1 & PL2 & PL3 & PL4 & PL5 & _) ]). pose proof (aobj_facts _ _ PL1) as F1. pose proof (aobj_facts _ _ PL4) as F4.
    unfold pa_tsd in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="R AR held Clg"] Lemma rk_TM : mapped v thr 4096.
  Proof. pose proof (ar_cache _ _ _ _ _ R) as C. unfold cache_repr_ in C. cbv zeta in C. tauto. Qed.
  #[using="R AR held Clg"] Lemma rk_TMi : forall a k, thr <= a -> a + k <= thr + 4096 -> mapped v a k.
  Proof. intros a k H1 H2 i Hi. replace (a + i) with (thr + (a - thr + i)) by lia. apply rk_TM. lia. Qed.

  (* [comment removed for export] *)
  #[using="R W AR held Clg"] Lemma rk_thr_words : forall a (k : nat), thr + off_th_stats <= a -> a + 8 * Z.of_nat k <= thr + off_th_stats + (112 + 8 * 32) ->
    exists ws, length ws = k /\ rw_cells rsegs v a (map C8 ws).
  Proof.
    intros a k H1 H2. unfold off_th_stats in *.
    pose proof (ar_cache _ _ _ _ _ R) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand5 C as _ _ JS TM _ | destruct C as (_ & _ & JS & TM & _) ]).
    unfold off_th_stats in JS. (first [ dex1 JS as bs; destruct JS as [LBS BS] | dand3 JS as bs LBS BS | destruct JS as (bs & LBS & BS) ]).
    pose proof alloc_ceiling_val as CE. (first [ pose proof (rk_place) as dR_7; dand3 dR_7 as PT PTC _ | pose proof rk_place as (PT & PTC & _) ]). pose proof (aobj_facts _ _ PT) as PTF.
    pose proof (bytes_at_mid v (thr + 2800) bs (Z.to_nat (a - (thr + 2800))) (8 * k) BS ltac:(lia)) as B.
    rewrite Z2Nat.id in B by lia. replace (thr + 2800 + (a - (thr + 2800))) with a in B by lia.
    exists (words8 (firstn (8 * k) (skipn (Z.to_nat (a - (thr + 2800))) bs)) k). split; [apply words8_length|].
    assert (LEN : length (firstn (8 * k) (skipn (Z.to_nat (a - (thr + 2800))) bs)) = (8 * k)%nat).
    { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
    apply ro_rw.
    - split; [apply CB8_wf|]. rewrite CB8_bytes, u64s_words8 by exact LEN. exact B.
    - rewrite CB8_size, words8_length, Nat2Z.inj_mul. apply rk_TMi; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="R W AR held Clg"] Lemma rk_stats : exists (statv : word) (rf rfd : Z),
    0 <= rf < 2^64 /\ 0 <= rfd < 2^64 /\
    rw_cells rsegs v (thr + 208 + 2576) [C8 statv] /\ rw_cells rsegs v (thr + 2840) [C8 (wz rf); C8 (wz rfd)].
  Proof.
    pose proof (ar_cache _ _ _ _ _ R) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand4 C as _ J1 _ _ | destruct C as (_ & J1 & _ & _) ]).
    unfold off_th_cache_stats in J1. (first [ dex1 J1 as b1; destruct J1 as [L1 B1] | dand3 J1 as b1 L1 B1 | destruct J1 as (b1 & L1 & B1) ]).
    pose proof alloc_ceiling_val as CE. (first [ pose proof (rk_place) as dR_10; dand3 dR_10 as PT PTC _ | pose proof rk_place as (PT & PTC & _) ]). pose proof (aobj_facts _ _ PT) as PTF.
    assert (X1 : bytes_at rsegs v (thr + 208 + 2576) (firstn 8 (skipn 16 b1))).
    { replace (thr + 208 + 2576) with (thr + 2768 + Z.of_nat 16) by lia. apply bytes_at_mid; [exact B1| lia]. }
    (first [ pose proof ((rk_thr_words (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_11; dex1 dR_11 as ws; destruct dR_11 as [L2 R2] | pose proof ((rk_thr_words (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_11; dand3 dR_11 as ws L2 R2 | destruct (rk_thr_words (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws & L2 & R2) ]).
    destruct ws as [|a1 [|b2 [|]]]; cbn in L2; try lia. cbn [map] in R2.
    exists (le_bytes_to_word (firstn 8 (skipn 16 b1))), (bv_unsigned a1), (bv_unsigned b2).
    pose proof (zr_word a1). pose proof (zr_word b2). unfold inr64 in *. rewrite !Z_to_bv_bv_unsigned.
    split; [lia|]. split; [lia|]. split; [| exact R2].
    apply ro_rw; [| apply rk_TMi; cbn; lia]. apply bytes_ro_C8. rewrite le8_of_bytes by (rewrite firstn_length, skipn_length; lia).
    exact X1.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="R W CI AR held Clg"] Lemma rk_line : forall c, 1 <= c <= 30 ->
    let ks' := pk_chunks (a_cache A c) in
    exists ks, length ks = 16%nat /\
      Forall (fun w => bv_unsigned w < 2^32) ks /\
      firstn (length ks') ks = map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks' /\
      Z.of_nat (length ks') <= max_count c /\ (forall k, In k ks' -> 0 <= k < carved_count A c) /\ NoDup ks' /\
      rw_cells rsegs v (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (Z.of_nat (length ks'))); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Proof.
    intros c CRc. cbv zeta. set (ks' := pk_chunks (a_cache A c)).
    pose proof (ar_cache _ _ _ _ _ R) as C. unfold cache_repr_ in C. cbv zeta in C. destruct C as (C & _).
    (first [ pose proof ((C c ltac:(lia))) as dR_12; dand5 dR_12 as L16 Hcnt Hmax Hent Hjunk | destruct (C c ltac:(lia)) as (L16 & Hcnt & Hmax & Hent & Hjunk) ]). rewrite CI in Hmax. cbn [andb negb] in Hmax.
    destruct (Z.eqb_spec c 0); [lia|]. destruct Hmax as [Hmax Hsz]. (first [ dex1 Hjunk as jb; destruct Hjunk as [Ljb Bjb] | dand3 Hjunk as jb Ljb Bjb | destruct Hjunk as (jb & Ljb & Bjb) ]). fold ks' in L16, Hcnt, Hent, Ljb, Bjb.
    pose proof alloc_ceiling_val as CE. (first [ pose proof (rk_place) as dR_14; dand3 dR_14 as PT PTC _ | pose proof rk_place as (PT & PTC & _) ]). pose proof (aobj_facts _ _ PT) as PTF.
    (first [ pose proof ((wtC A W)) as dR_15; dand3 dR_15 as WC _ _ | destruct (wtC A W) as (WC & _ & _) ]). (first [ pose proof ((WC c ltac:(lia))) as dR_16; dand4 dR_16 as WL WND WRG _ | destruct (WC c ltac:(lia)) as (WL & WND & WRG & _) ]). cbv zeta in WL, WND, WRG. fold ks' in WL, WND, WRG.
    unfold off_th_per_class, off_th_alloc_cache, off_pc_count, off_pc_max_count, off_pc_class_size, off_pc_chunk, kPerClassSize in *.
    set (e := thr + 208 + 80 * c). replace (thr + (208 + 80 * c)) with e in * by (subst e; lia).
    set (ks := map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks' ++ words4 jb (16 - length ks')).
    assert (SMALL : forall k, In k ks' -> 0 <= k * class_size c / kCompactPtrScale < 2^32).
    { intros k Hk. specialize (WRG k Hk).
      (first [ pose proof ((carved_chunk_boundsT A c k W CRc WRG)) as dR_17; dand3 dR_17 as B1 B2 _ | pose proof (carved_chunk_boundsT A c k W CRc WRG) as (B1 & B2 & _) ]). pose proof (region_piece_boundsT A c W CRc) as RB. cbv zeta in *.
      unfold chunk_addr, kCompactPtrScale, kFreeArrayOffset in *.
      split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    exists ks. assert (LK : length ks = 16%nat).
    { subst ks. rewrite length_app, length_map, words4_length. lia. }
    split; [exact LK|]. split.
    { subst ks. apply Forall_app. split; [| apply words4_small]. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (k & <- & Hk).
      pose proof (SMALL k Hk). rewrite unsigned_lit by lia. lia. }
    split.
    { subst ks. rewrite firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by (rewrite length_map; lia). reflexivity. }
    split; [exact WL|]. split; [exact WRG|]. split; [exact WND|].
    apply ro_rw.
    - split; [cbn; rewrite u32s_length, LK; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I || reflexivity|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. split; [rewrite Z.add_0_r in Hcnt; exact Hcnt|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4) with (e + 4) by lia; exact Hmax|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4 + Z.of_nat 4) with (e + 8) by lia; exact Hsz|]. rewrite length_le8.
      replace (e + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8) with (e + 16) by lia.
      subst ks. rewrite u32s_app. apply bytes_at_app. split.
      + apply u32s_of_entries; [| subst e; lia | subst e; lia].
        intros i k Hk. replace (e + 16 + 4 * Z.of_nat i) with (e + (16 + 4 * Z.of_nat i)) by lia. apply Hent. exact Hk.
      + rewrite u32s_length, length_map. rewrite u32s_words4 by lia.
        replace (e + 16 + Z.of_nat (4 * length ks')) with (e + (16 + 4 * Z.of_nat (length ks'))) by lia. exact Bjb.
    - cbn [cells_size csize Nat.add]. subst e. apply rk_TMi; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="W AR held v"] Lemma rk_ri : ri = sb + kSpaceSize /\ kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling /\ ri mod 128 = 0 /\ sb mod 4096 = 0 /\
                kHighMemBeg <= sb /\ sb + 2^37 <= ri /\
                (forall c, region_info_addr sb c = ri + 128 * c) /\ (forall c, free_array_beg sb c = free_array_of sb c) /\
                (forall c, region_beg sb c = sb + c * 2^32).
  Proof.
    (first [ pose proof ((sb_factsT A W)) as dR_18; dand5 dR_18 as _ SBM HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & SBM & HB6 & RSB & SCE) ]). unfold a_ri, p_ri, a_sb in *. pose proof alloc_ceiling_val.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (unfold kSpaceSize, kHighMemBeg in *; lia).
    all: try (apply (mod0_down _ 0x10000 128); [exists 512; reflexivity|]; unfold kSpaceSize; rewrite <- Zplus_mod_idemp_l, SBM; reflexivity).
    all: try (apply (mod0_down _ 0x10000 4096); [exists 16; reflexivity| exact SBM]).
    all: intros c; unfold region_info_addr, kRegionInfoSize, free_array_beg, free_array_of, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize in *; lia.
  Qed.

  #[using="W AR held v Clg"] Lemma rk_sep : apart thr 4096 ri 4096 /\ apart ri 4096 sb (2^37) /\ apart (p_ctx P) 0x10000 ri 4096 /\
                 apart thr 4096 sb (2^37) /\ apart (p_ctx P) 0x10000 thr 4096 /\ apart (p_ctx P) 0x10000 sb (2^37).
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_19; dand10 dR_19 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    (first [ pose proof ((sb_factsT A W)) as dR_20; dand5 dR_20 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]). destruct rk_ri as (RI & _).
    unfold a_thr, a_ctx, a_nodes0, a_frames0, a_b6, a_sb, a_ri in *. rewrite RI.
    assert (B6 : forall i b s, i <> 0%nat -> nth_error (big_maps A) i = Some (b, s) ->
                 apart b s (p_sb (a_pl A) + kSpaceSize) 4096 /\ apart b s (p_sb (a_pl A)) (2^37)).
    { intros i b s Hi Hn. destruct (bm_sepT A i 0 _ _ _ _ W Hn E0 Hi); unfold apart, kSpaceReserve, kSpaceSize in *; lia. }
    pose proof (B6 4%nat _ _ ltac:(lia) E4) as [T1 T2]. pose proof (B6 5%nat _ _ ltac:(lia) E5) as [C1 C2].
    split; [exact T1|]. split; [unfold apart, kSpaceSize; lia|]. split; [exact C1|]. split; [exact T2|]. split; [| exact C2].
    destruct (bm_sepT A 5 4 _ _ _ _ W E5 E4 ltac:(lia)); unfold apart; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="R W AR held Clg"] Lemma rk_region : forall c (h : nat), 1 <= c <= 30 ->
    let Rg := a_reg A c in let nf := Z.of_nat (length (rg_free Rg)) in let Ra := ri + 128 * c in
    4 * (nf + Z.of_nat h) <= rg_mapped_fa Rg ->
    exists (na nfs v88 : word) (junk : list word),
      rw_cells rsegs v Ra [C8 (wz 0)] /\
      rw_cells rsegs v (Ra + 16) [C8 (wz nf)] /\
      rw_cells rsegs v (Ra + 24) [C8 (wz (rg_mapped_fa Rg))] /\
      ro_cells rsegs v (Ra + 48) [C8 (wz (rg_mapped_user Rg))] /\
      rw_cells rsegs v (Ra + 72) [C8 na] /\
      rw_cells rsegs v (Ra + 80) [C8 nfs; C8 v88] /\
      length junk = h /\ u32arr rsegs v (free_array_of sb c + 4 * nf) junk.
  Proof.
    intros c h CRc. cbv zeta. intros ROOM. pose proof alloc_ceiling_val as CE.
    (first [ dand10 rk_ri as RI RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | destruct rk_ri as (RI & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    pose proof (ar_regions _ _ _ _ _ R c CRc) as RR. unfold region_repr_ in RR. cbv zeta in RR.
    rewrite RIA, FAE in RR. (first [ dand13 RR as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt ENT MFA MUS | destruct RR as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & ENT & MFA & MUS) ]).
    pose proof (ar_locks _ _ _ _ _ R) as LK. unfold locks_repr_ in LK. cbv zeta in LK. destruct LK as (LK & _).
    destruct (LK c ltac:(lia)) as [MX0 _]. change (p_ri (a_pl A)) with ri in MX0. unfold kRegionInfoSize in MX0. rewrite Z.add_0_r in MX0.
    (first [ pose proof ((ar_maps _ _ _ _ _ R)) as dR_23; dand3 dR_23 as _ MRI _ | pose proof (ar_maps _ _ _ _ _ R) as (_ & MRI & _) ]). change (p_ri (a_pl A)) with ri in MRI.
    pose proof (region_piece_boundsT A c W CRc) as RB. cbv zeta in RB.
    unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_mapped_user, off_ri_n_allocated in *.
    assert (TMi : forall a j, ri <= a -> a + j <= ri + 4096 -> mapped v a j).
    { intros a j H1 H2 i Hi. replace (a + i) with (ri + (a - ri + i)) by lia. apply MRI. lia. }
    (first [ dex1 Jna as bna; destruct Jna as [Lna Bna] | dand3 Jna as bna Lna Bna | destruct Jna as (bna & Lna & Bna) ]). (first [ dex1 Jrt as brt; destruct Jrt as [Lrt Brt] | dand3 Jrt as brt Lrt Brt | destruct Jrt as (brt & Lrt & Brt) ]). unfold off_ri_rtoi in Brt.
    assert (FAR : free_array_of sb c = region_beg sb c + kFreeArrayOffset) by (unfold free_array_of, region_beg, kRegionSize, kFreeArrayOffset; lia).
    (* [comment removed for export] *)
    set (fa := free_array_of sb c) in *.
    assert (MJ : mapped v (fa + 4 * Z.of_nat (length (rg_free (a_reg A c)))) (Z.of_nat (4 * h))).
    { intros i Hi. replace (fa + 4 * Z.of_nat (length (rg_free (a_reg A c))) + i) with (fa + (4 * Z.of_nat (length (rg_free (a_reg A c))) + i)) by lia.
      apply MFA. lia. }
    pose proof (rdbytes_bytes_at v (fa + 4 * Z.of_nat (length (rg_free (a_reg A c)))) (4 * h) MJ
                  ltac:(rewrite FAR; unfold kFreeArrayOffset, kHighMemBeg in *; lia) ltac:(rewrite FAR; unfold kRegionSize, kFreeArrayOffset, kSpaceSize in *; lia)) as BJ.
    exists (le_bytes_to_word (firstn 8 bna)), (le_bytes_to_word (firstn 8 (skipn 8 bna))), (le_bytes_to_word (firstn 8 brt)),
           (words4 (rdbytes v (fa + 4 * Z.of_nat (length (rg_free (a_reg A c)))) (4 * h)) h).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - apply ro_rw; [apply u64_ro; exact MX0| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hnf| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hfa| apply TMi; cbn; lia].
    - apply u64_ro. exact Hmu.
    - apply ro_rw; [| apply TMi; cbn; lia]. apply bytes_ro_C8. rewrite le8_of_bytes by (rewrite firstn_length; lia).
      replace (ri + 128 * c + 72) with (ri + 128 * c + 72 + Z.of_nat 0) by lia. apply (bytes_at_mid v _ bna 0 8 Bna). lia.
    - apply ro_rw; [| apply TMi; cbn; lia]. split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. rewrite length_le8. rewrite !le8_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia). split.
      + replace (ri + 128 * c + 80) with (ri + 128 * c + 72 + Z.of_nat 8) by lia. apply (bytes_at_mid v _ bna 8 8 Bna). lia.
      + replace (ri + 128 * c + 80 + Z.of_nat 8) with (ri + 128 * c + 88 + Z.of_nat 0) by lia. apply (bytes_at_mid v _ brt 0 8 Brt). lia.
    - apply words4_length.
    - split.
      + rewrite u32s_words4 by (rewrite rdbytes_length; lia). exact BJ.
      + rewrite words4_length. apply mapped_wr_at; [replace (4 * Z.of_nat h) with (Z.of_nat (4 * h)) by lia; exact MJ| rewrite FAR; unfold kFreeArrayOffset, kHighMemBeg in *; lia| rewrite FAR; unfold kRegionSize, kFreeArrayOffset, kSpaceSize in *; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="W AR held v Clg"] Lemma rk_region_facts : forall c, 1 <= c <= 30 ->
    let Rg := a_reg A c in
    0 <= rg_allocated_user Rg <= rg_mapped_user Rg /\ rg_mapped_user Rg <= kFreeArrayOffset /\ 0 <= rg_mapped_fa Rg <= kFreeArraySize /\
    rg_mapped_fa Rg mod kFreeArrayMapSize = 0 /\ 4 * Z.of_nat (length (rg_free Rg)) <= rg_mapped_fa Rg /\
    carved_count A c * class_size c = rg_allocated_user Rg /\ 0 <= carved_count A c.
  Proof.
    intros c CRc. cbv zeta. (first [ pose proof ((wtR A W)) as dR_26; dand3 dR_26 as WR _ _ | destruct (wtR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c CRc)) as dR_27; dand10 dR_27 as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 | destruct (WR c CRc) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10) ]). cbv zeta in *.
    pose proof (class_size_range c CRc) as CSR.
    unfold carved_count, carved_count_.
    pose proof (Z_div_exact_full_2 (rg_allocated_user (a_reg A c)) (class_size c) ltac:(lia) R4) as E.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try exact R6; apply Z.div_pos; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="W AR held v"] Lemma rk_batch : forall kb, 0 <= kb < carved_count A kQuarantineBatchClass ->
    let b := chunk_addr sb kQuarantineBatchClass kb in
    b = sb + 24 * 2^32 + 16 * (512 * kb) /\ kHighMemBeg <= b /\ b + 8192 <= alloc_ceiling /\ b mod 16 = 0 /\
    0 <= 512 * kb /\ 16 * (512 * kb) + 8192 <= 3758096384 /\
    apart b 8192 thr 4096 /\ apart b 8192 (p_ctx P) 0x10000 /\ apart b 8192 ri 4096.
  Proof.
    intros kb KB. cbv zeta. pose proof alloc_ceiling_val as CE.
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    (first [ pose proof ((carved_chunk_boundsT A kQuarantineBatchClass kb W C24 KB)) as dR_28; dand4 dR_28 as B1 B2 B3 B4 | pose proof (carved_chunk_boundsT A kQuarantineBatchClass kb W C24 KB) as (B1 & B2 & B3 & B4) ]). cbv zeta in *.
    pose proof (region_piece_boundsT A kQuarantineBatchClass W C24) as RB. cbv zeta in RB.
    (first [ dand8 rk_ri as RI RLO RHI RAL SBAL SBLO SBRI _ | destruct rk_ri as (RI & RLO & RHI & RAL & SBAL & SBLO & SBRI & _) ]). (first [ dand6 rk_sep as S1 S2 S3 S4 S5 S6 | destruct rk_sep as (S1 & S2 & S3 & S4 & S5 & S6) ]).
    change (class_size kQuarantineBatchClass) with 8192 in *. unfold kQuarantineBatchClass in *.
    unfold chunk_addr, region_beg, kRegionSize, kFreeArrayOffset, kHighMemBeg, apart in *. change (class_size 24) with 8192 in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    all: rewrite Z.add_mod, Z.mul_comm, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
    all: rewrite Z.add_mod, (Z.mul_comm 24), Z.mul_assoc by lia.
    all: replace (4294967296 * 24) with (268435456 * 24 * 16) by lia; rewrite Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
    all: apply (mod0_down _ 4096 16); [exists 256; reflexivity| exact SBAL].
  Qed.
End BusyKit.
End AFreeRK.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module AFreeRK3.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSrgm AMalmys ANodeA7 ASecB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf ATransp ATranspR AFreeRS AFreeRT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section BusyKit.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (held : list Z).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis CI : a_cache_inited A = true.

  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan held A v. Proof. exact (proj2 AR). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).

  Let CF : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ R)). Qed.
  Let CR : consts_repr_ LPA AL_pasan (a_pl A) v.
  Proof. exact (ar_consts _ _ _ _ _ R). Qed.
  Ltac cell H a bs := pose proof (consts_cell v a bs CF eq_refl) as H.

  Lemma rk_SEAL : ro_cells rsegs v 0xa91d0 [C8 (wz 1)].
  Proof. cell H 0xa91d0 (le8 (Z_to_bv 64 1)). apply bytes_ro_C8. exact H. Qed.
  Lemma rk_DYG : ro_cells rsegs v 0xa91d8 [C8 (wz 0x146edc)].
  Proof. cell H 0xa91d8 (le8 (Z_to_bv 64 0x146edc)). apply bytes_ro_C8. exact H. Qed.
  Lemma rk_DYF : ro_cells rsegs v 0x146edc [C4 (wz 0)].
  Proof. cell H 0x146edc (le4 (Z_to_bv 64 0)). apply bytes_ro_C4. exact H. Qed.
  Lemma rk_CML : ro_cells rsegs v (ANodeA7.CF + 144) [C8 (wz 0)].
  Proof.
    cell H 0x146ee8 pa_common_flags_bytes. rewrite CF_eq. apply bytes_ro_C8.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 144 8 H ltac:(cbn; lia))). byteseq.
  Qed.
End BusyKit.
End AFreeRK3.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma bytes_at_xfer : forall (v v' : mem) a bs,
  bytes_at rsegs v a bs -> (forall z, a <= z < a + Z.of_nat (length bs) -> v' (wz z) = v (wz z)) -> bytes_at rsegs v' a bs.
Proof. intros v v' a bs B AG. eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply AG. lia. Qed.

Section EntryKit.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (held : list Z) (c k n : Z).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis WE : wf_qentry_ (a_reg A) (a_sec A) (QE (ChP (CP c k)) n).
  Hypothesis LE : lentry_cells (a_sb A) v (QE (ChP (CP c k)) n).

  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation us := (user_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation rz := (rz_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation p := (chunk_addr (a_sb A) c k).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size c).

  Lemma ek_geo :
    1 <= c <= 30 /\ c = class_of n /\ 0 <= n <= kMaxPrimaryUser /\ 0 <= k < carved_count A c /\
    16 <= rz <= 2048 /\ rz mod 16 = 0 /\ 1 <= us /\ n <= us /\ us <= Z.max n 1 /\
    rz + round_up us 8 <= size /\ 32 <= size <= kMaxSize /\ size mod 32 = 0 /\
    p = sb + c * 2^32 + k * size /\ (k + 1) * size <= rg_allocated_user (a_reg A c) /\
    rg_allocated_user (a_reg A c) <= rg_mapped_user (a_reg A c) /\ rg_mapped_user (a_reg A c) <= kFreeArrayOffset /\
    kHighMemBeg <= p /\ p + size <= alloc_ceiling /\ p mod 32 = 0 /\ sb mod 4096 = 0 /\
    user_of sb (ChP (CP c k)) n = p + rz /\ hdr_of sb (ChP (CP c k)) n = p + rz - 16 /\
    alloc_beg sb (ChP (CP c k)) = p /\ chunk_lo sb (ChP (CP c k)) = p /\ chunk_hi sb (ChP (CP c k)) = p + size.
  Proof.
    destruct WE as (NR & NP & CC & KR). cbn [qe_n qe_chunk] in NR, NP, CC, KR. pose proof alloc_ceiling_val as CE.
    assert (CR : 1 <= c <= 30) by (rewrite CC; apply class_of_range; lia).
    (first [ pose proof ((carved_chunk_boundsT A c k W CR KR)) as dR_1; dand4 dR_1 as B1 B2 B3 B4 | pose proof (carved_chunk_boundsT A c k W CR KR) as (B1 & B2 & B3 & B4) ]). cbv zeta in B1, B2, B3, B4.
    (first [ pose proof ((region_piece_boundsT A c W CR)) as dR_2; dand10 dR_2 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 _ | pose proof (region_piece_boundsT A c W CR) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & _) ]). cbv zeta in *.
    (first [ pose proof ((sb_factsT A W)) as dR_3; dand3 dR_3 as _ SBM _ | pose proof (sb_factsT A W) as (_ & SBM & _) ]).
    pose proof (rz_size_range n) as RZ. pose proof (rz_size_mod16 n) as RZM. (first [ pose proof ((user_size_pos n ltac:(lia))) as dR_4; dand3 dR_4 as U1 U2 U3 | pose proof (user_size_pos n ltac:(lia)) as (U1 & U2 & U3) ]).
    pose proof (class_size_mod32 c CR) as CM. pose proof (user_end_fits 0 n ltac:(lia)) as [F1 F2]. rewrite <- CC in F2. unfold user_beg in F1.
    pose proof (rounded_user_size n ltac:(lia)) as RU. pose proof (rounded_size_mod8 n) as RM8.
    assert (R8 : round_up us 8 <= rounded_size n).
    { unfold rounded_size. apply round_up_mono; [lia|]. unfold user_size. destruct (Z.eqb_spec n 0); lia. }
    unfold needed_size in F1, F2.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try lia.
    - unfold carved_count. lia.
    - unfold user_size. destruct (Z.eqb_spec n 0); lia.
    - unfold chunk_addr, region_beg, kRegionSize. lia.
    - unfold chunk_addr, region_beg, kRegionSize in *. nia.
    - unfold user_of, alloc_beg, user_beg. reflexivity.
    - unfold hdr_of, user_of, alloc_beg, user_beg, kChunkHeaderSize. lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ek_cells : exists (b1 : Z) (ctxw : word),
    0 <= b1 < 256 /\
    rw_cells rsegs v (p + rz - 16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi us)); C4 (wz us)] /\
    rw_cells rsegs v (p + rz - 16 + 8) [C8 ctxw] /\
    (rz - 16 = 0 \/ rw_cells rsegs v p [C8 (wz kAllocBegMagic)]) /\
    rw_cells rsegs v (sh (p + rz - 16 + 16)) [CB (Z.to_nat (round_up us 8 / 8)) (fd8 ((us + 7) / 8))] /\
    bytes_at rsegs v (sh p) (pshadow_quar c n) /\ Z.of_nat (length (pshadow_quar c n)) = size / 8 /\
    sh (p + rz) = sh p + rz / 8 /\ round_up us 8 / 8 = (us + 7) / 8 /\
    mapped v p size.
  Proof.
    (first [ pose proof (ek_geo) as dR_5; dand25 dR_5 as CR CC NR KR RZ RZM U1 U2 U3 FIT CSR CM PE KA AM MK PLO PHI PM SBM UO HO ABE CLO CHI | pose proof ek_geo as (CR & CC & NR & KR & RZ & RZM & U1 & U2 & U3 & FIT & CSR & CM & PE & KA & AM & MK & PLO & PHI & PM & SBM & UO & HO & ABE & CLO & CHI) ]).
    pose proof alloc_ceiling_val as CE.
    destruct LE as (HR & JK & MP & SHQ). cbn [qe_chunk qe_n] in HR, JK, MP, SHQ. rewrite CLO, CHI in MP. replace (p + size - p) with size in MP by lia.
    unfold hdr_repr_ in HR. cbv zeta in HR. rewrite UO, ABE in HR. destruct HR as [(id & b1 & IDR & B1R & B1M & HC) MG].
    unfold chunk_hdr_cells in HC. cbn [ch_state ch_b1 ch_size ch_ctx] in HC.
    apply (rw_cells_app_split v (p + rz - 16) [C1 (b8 CHUNK_QUARANTINE); C1 (b8 b1); C2 (w64 (size_hi us)); C4 (w64 us)] [C8 (w64 id)]) in HC as [HC1 HC2].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HC2.
    assert (R88 : round_up us 8 / 8 = (us + 7) / 8).
    { unfold round_up. pose proof (Z_div_mod_eq_full (us + 7) 8). pose proof (Z.mod_pos_bound (us + 7) 8 ltac:(lia)).
      replace (us + 8 - 1) with (us + 7) by lia. rewrite Z.div_mul by lia. reflexivity. }
    assert (SHA : sh (p + rz) = sh p + rz / 8) by (apply sh_add; [apply (mod0_down _ 32 8); [exists 4; reflexivity| exact PM]| apply (mod0_down _ 16 8); [exists 2; reflexivity| exact RZM]]).
    pose proof (pshadow_quar_length c n NR CC) as QL.
    exists b1, (w64 id). split; [exact B1R|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - exact HC1.
    - exact HC2.
    - destruct (Z.eq_dec (rz - 16) 0) as [Z0|NZ]; [left; exact Z0| right].
      destruct (MG ltac:(lia)) as [M1 _]. apply ro_rw; [apply u64_ro; exact M1|]. cbn. intros i Hi. apply MP. lia.
    - (* [comment removed for export] *)
      replace (p + rz - 16 + 16) with (p + rz) by lia. rewrite SHA.
      unfold pshadow_quar in SHQ. apply bytes_at_app in SHQ as [_ SHQ]. unfold fa8 at 1 in SHQ. rewrite repeat_length in SHQ.
      apply bytes_at_app in SHQ as [SHQ _]. rewrite Z2Nat.id in SHQ by (apply Z.div_pos; lia).
      apply (bytes_rw_CB v _ _ _ SHQ).
      + unfold fd8. rewrite repeat_length. rewrite R88. reflexivity.
      + unfold sh. pose proof (Z.div_pos p 8). unfold kHighMemBeg in PLO. kung_all. lia.
    - exact SHQ.
    - exact QL.
    - exact SHA.
    - exact R88.
    - exact MP.
  Qed.
End EntryKit.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SlotKit.
Context {Clg : Ceiling}.
  Lemma ek_slot : forall (v : mem) sb a es j sz i e,
    lbatch_cells sb v a es j sz -> (j <= i)%nat -> nth_error es i = Some e -> Z.of_nat (length es) <= kQuarantineBatchCount ->
    rw_cells rsegs v (a + 24 + 8 * Z.of_nat i) [C8 (wz (hdr_of sb (qe_chunk e) (qe_n e)))].
  Proof.
    (intros v sb a es j sz i e; (first [ intro dR_6; dand3 dR_6 as SL SZ MP | intros (SL & SZ & MP) ]); intros Hj He LEN).
    pose proof (SL i e Hj He) as U. unfold off_qb_batch in U. replace (a + (24 + 8 * Z.of_nat i)) with (a + 24 + 8 * Z.of_nat i) in U by lia.
    pose proof (nth_error_Some_lt _ _ _ He) as IL.
    apply ro_rw; [apply u64_ro; exact U|]. cbn. intros q Hq. replace (a + 24 + 8 * Z.of_nat i + q) with (a + (24 + 8 * Z.of_nat i + q)) by lia. apply MP.
    unfold kQuarantineBatchBytes, kQuarantineBatchCount in *. lia.
  Qed.
End SlotKit.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ShadowRecycled.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)

  Lemma shadow_recycled : forall (v v' : mem) c n q,
    0 <= n <= kMaxPrimaryUser -> c = class_of n ->
    bytes_at rsegs v q (pshadow_quar c n) ->
    bytes_at rsegs v' (q + rz_size n / 8) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (round_up (user_size n) 8 / 8))) ->
    (forall z, q <= z < q + class_size c / 8 -> ~ (q + rz_size n / 8 <= z < q + rz_size n / 8 + (user_size n + 7) / 8) -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' q (pshadow_free c).
  Proof.
    intros v v' c n q NR CC SHQ NEW AG.
    assert (CR : 1 <= c <= 30) by (rewrite CC; apply class_of_range; lia).
    pose proof (pshadow_quar_length c n NR CC) as QL. pose proof (rz_size_range n) as RZ. pose proof (rz_size_mod16 n) as RZM.
    pose proof (user_size_pos n ltac:(lia)) as (U1 & _). pose proof (class_size_range c CR) as CSR.
    assert (R88 : round_up (user_size n) 8 / 8 = (user_size n + 7) / 8).
    { unfold round_up. replace (user_size n + 8 - 1) with (user_size n + 7) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite R88 in NEW.
    pose proof (Z_div_exact_full_2 (rz_size n) 8 ltac:(lia) (mod0_down _ 16 8 (divide_wit 8 2) RZM)) as RZ8.
    assert (U8 : 0 <= (user_size n + 7) / 8) by (apply Z.div_pos; lia).
    unfold pshadow_quar in SHQ, QL. rewrite !length_app in QL. unfold fa8, fd8 in QL. rewrite !repeat_length in QL.
    apply bytes_at_app in SHQ as [S1 S23]. unfold fa8 at 1 in S23. rewrite repeat_length in S23.
    apply bytes_at_app in S23 as [S2 S3]. unfold fd8 in S3. rewrite repeat_length in S3. unfold fa8 in S1, S3.
    rewrite (Z2Nat.id ((user_size n + 7) / 8)) in S3 by lia. rewrite (Z2Nat.id (rz_size n / 8)) in S2, S3 by lia.
    unfold pshadow_free. unfold fa8.
    replace (Z.to_nat (class_size c / 8)) with (Z.to_nat (rz_size n / 8) + (Z.to_nat ((user_size n + 7) / 8) + Z.to_nat (class_size c / 8 - rz_size n / 8 - (user_size n + 7) / 8)))%nat by lia.
    rewrite !repeat_app. apply bytes_at_app. split.
    - eapply bytes_at_xfer; [exact S1|]. rewrite repeat_length. intros z Hz. apply AG; lia.
    - rewrite repeat_length, Z2Nat.id by lia. apply bytes_at_app. split; [exact NEW|].
      rewrite repeat_length, Z2Nat.id by lia. eapply bytes_at_xfer; [exact S3|]. rewrite repeat_length. intros z Hz. apply AG; lia.
  Qed.
End ShadowRecycled.
