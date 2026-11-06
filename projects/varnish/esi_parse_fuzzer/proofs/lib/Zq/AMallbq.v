(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AMalq4j AMalghy.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMTac AMallocA AMallocH AMalmys AMal9l1 AMalgue AMaly5g AMaldga AMalkbe AMal8cv AMalzuh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module AMaljju.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AMalq4j AMalghy.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 AMTac AMallocA AMallocH AMalmys AMal9l1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g AMaldga AMalkbe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalzuh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalzuh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g.AMal5j7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalkbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalzuh.AMalrll OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalzuh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Section Vacuous.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  (* [comment removed for export] *)
  Lemma refill0_vacuous : forall A m md n, pa_ainv A m md -> 1 <= n <= kMaxPrimaryUser -> a_cache_inited A = false ->
    refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))) -> False.
  Proof.
    intros A m md n AI NR CI EN. pose proof (proj1 (hit_class n NR)) as CR. (first [ pose proof ((max_count_range _ CR)) as dR_1; dand3 dR_1 as _ _ KR | pose proof (max_count_range _ CR) as (_ & _ & KR) ]).
    (first [ pose proof ((wfR A (ai_wf _ _ _ _ _ _ _ AI))) as dR_2; dand3 dR_2 as R1 _ R3 | destruct (wfR A (ai_wf _ _ _ _ _ _ _ AI)) as (R1 & _ & R3) ]).
    destruct (Z.eq_dec (rg_mapped_user (a_reg A (class_of n))) 0) as [Z0|NZ].
    - (first [ pose proof ((R1 _ CR)) as dR_3; dand11 dR_3 as _ _ _ _ _ _ _ _ _ A10 _ | destruct (R1 _ CR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & A10 & _) ]). destruct (A10 Z0) as [_ E]. rewrite E in EN. cbn in EN. lia.
    - assert (T : a_cache_inited A = true) by (apply R3; exists (class_of n); split; [exact CR| exact NZ]). rewrite CI in T. discriminate.
  Qed.
End Vacuous.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
Context {Clg : Ceiling}.
  Hypothesis UNW : unwind_stmt.
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt depot_repL.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.

  (* [comment removed for export] *)
End Bridge.
End AMaljju.

   (* [comment removed for export] *)
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kHighShadowMapSize in *.   (* [comment removed for export] *)

(* [comment removed for export] *)

Section Post.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (n : Z) (key : list Z) (spa : word) (v' : mem) (lo hi : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation fr := (rg_free (a_reg A (class_of n))).
  Local Notation KK := (refill_count (class_of n)).
  Local Notation kidx := (refK A n).
  Local Notation ri := (a_ri A).
  Hypothesis ENOUGH : refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOSA : lo <= bv_unsigned spa - 1024.
  Hypothesis SAHI : bv_unsigned spa <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation AB := (chunk_addr (a_sb A) (class_of n) kidx).
  Local Notation u := (hit_user A n kidx).
  Local Notation n0 := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation W := (alloc_refill_W spa thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8) n0 f0 (a_ri A)).
  Local Notation shU := (AB / 8 + rz_size n / 8 + kShadowOffset).
  Local Notation A' := (refA A n key).
  Hypothesis MU : munch W v v'.
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis SM : mapped v lo (hi - lo).
  Let CEIL : alloc_ceiling <= bv_unsigned spa - 1024. Proof. clear - CLO LOSA. lia. Qed.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  (* [comment removed for export] *)
  #[using="WMv n"] Lemma NNb : forall a, 0x60a000 <= a -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  Proof. intros a H1 H2. apply wmono_NN; [exact WMv| lia| lia]. Qed.
  #[using="NR"] Lemma UEQb : u = AB + rz_size n.
  Proof. (first [ pose proof ((hit_u_range A n kidx NR)) as dR_1; dand3 dR_1 as _ _ UE | destruct (hit_u_range A n kidx NR) as (_ & _ & UE) ]). exact UE. Qed.

  (* [comment removed for export] *)
  #[using="WF0 CEIL LOSA CLO ENOUGH NR AI lo spa md m"] Lemma chunk_owned : forall a, AB <= a < AB + class_size c -> pa_owned A a.
  Proof.
    intros a Ha. pose proof (GEO A m md n spa AI NR ENOUGH CEIL) as G. pose proof (rt_class_in A c (proj1 (hit_class n NR))) as [RIN _].
    apply (owned_rt A a (region_beg sb c) (rg_mapped_user (a_reg A c)) RIN ltac:(lia)).
    - ((first [ intro dR_10; dex2 dR_10 as p li; destruct dR_10 as [Hl Hp] | intro dR_10; dand4 dR_10 as p li Hl Hp | intros (p & li & Hl & Hp) ])). pose proof (primary_chunk_no_other_user A c kidx a WF0 (proj1 (hit_class n NR)) ltac:(lia) Ha p li Hl Hp) as E.
      exact (rf_not_live A m md n AI NR ENOUGH p li Hl E).
    - apply b6_no_live_frame; [exact WF0|]. apply primary_in_b6; [exact WF0|]. kung_all. lia.
  Qed.
  #[using="WF0 NR AI n md m"] Lemma thr_owned : forall a, thr <= a < thr + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_2; dand6 dR_2 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
    apply (owned_rt A a thr 4096); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 4); [exact WF0| lia| exact E4| exact Ha]
      | eapply (fixed_bm_no_live_frame A 4); [exact WF0| lia| lia| exact E4| exact Ha]].
  Qed.
  #[using="WF0 NR AI n md m"] Lemma n0_owned : forall a, n0 <= a < n0 + kDepotNodesBlock -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_3; dand9 dR_3 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]).
    apply (owned_rt A a n0 kDepotNodesBlock); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 7); [exact WF0| lia| exact E7| exact Ha]
      | eapply (fixed_bm_no_live_frame A 7); [exact WF0| lia| lia| exact E7| exact Ha]].
  Qed.
  #[using="WF0 NR AI n md m"] Lemma f0_owned : forall a, f0 <= a < f0 + kStackStoreBlockBytes -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_4; dand10 dR_4 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]).
    apply (owned_rt A a f0 kStackStoreBlockBytes); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 8); [exact WF0| lia| exact E8| exact Ha]
      | eapply (fixed_bm_no_live_frame A 8); [exact WF0| lia| lia| exact E8| exact Ha]].
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 CEIL LOSA CLO ENOUGH NR AI lo spa n md m"] Lemma ri_owned : forall a, ri <= a < ri + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. pose proof (GEO A m md n spa AI NR ENOUGH CEIL) as G.
    apply (owned_rt A a ri 4096); [apply rt_fixed_in; cbn; tauto| exact Ha| |].
    - intros LU. destruct (live_user_zone A a WF0 LU) as [[_ SB]|(i & s & Hs & RG)]; [kung_all; lia|].
      pose proof (bm_nth_sec A i s Hs) as Es. pose proof (bm_nth_fixed A) as (E0 & _).
      pose proof (bm_sep A (15 + i) 0 _ _ _ _ WF0 Es E0 ltac:(lia)) as D. pose proof (primary_in_b6 A a WF0 ltac:(kung_all; lia)) as B6.
      unfold apart, a_b6 in *. kung_all. lia.
    - apply b6_no_live_frame; [exact WF0|]. apply primary_in_b6; [exact WF0|]. kung_all. lia.
  Qed.
  #[using="n"] Lemma dstat_owned : forall a, 0x186a88 <= a < 0x5d6aa8 -> pa_owned A a.
  Proof. intros a Ha. apply asI_static_owned. cbn [cl_static LPA]. apply depot_static. cbn. unfold kDepotNodesL1. lia. Qed.

  (* [comment removed for export] *)
  #[using="WF0 CEIL MU SAHI LOSA CLO ENOUGH NR AI spa md"] Lemma frame1 : forall a, 0 <= a < 2^64 -> ~ pa_owned A a -> ~ (lo <= a < hi) -> ~ newblk u n a ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha NO NW NB. pose proof (GEO A m md n spa AI NR ENOUGH CEIL) as G. pose proof UEQb as UE.
    pose proof (USH A m md n spa AI NR ENOUGH CEIL) as (U1 & _). unfold newblk, blk in NB. rewrite U1 in NB.
    apply (AGW A m n spa v' MU); [lia|].
    apply (W_shape A m md n spa AI NR ENOUGH CEIL).
    - clear - NW LOSA SAHI. lia.
    - intros X. apply NO. apply thr_owned. lia.
    - intros X. apply NO. apply thr_owned. lia.
    - intros X. destruct (Z_lt_dec a (AB + rz_size n)); [apply NO; apply chunk_owned; lia|]. apply NB. left. pose proof (Z.le_min_l n 4096). kung_all. lia.
    - intros X. apply NO. apply dstat_owned. exact X.
    - intros X. apply NO. apply n0_owned. kung_all. lia.
    - intros X. apply NO. apply f0_owned. kung_all. lia.
    - intros X. apply NB. right. kung_all. lia.
    - intros X. apply NO. apply thr_owned. lia.
    - intros X. apply NO. apply thr_owned. lia.
    - intros X. apply NO. apply ri_owned. lia.
    - intros X. apply NO. apply ri_owned. lia.
    - intros X. apply NO. apply ri_owned. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 CEIL LOSA CLO ENOUGH NR AI lo spa md m"] Lemma newblk_owned : forall a, newblk u n a -> pa_owned A a.
  Proof.
    intros a NB. pose proof (GEO A m md n spa AI NR ENOUGH CEIL) as G. pose proof UEQb as UE. (first [ pose proof ((USH A m md n spa AI NR ENOUGH CEIL)) as dR_5; dand6 dR_5 as U1 U2 U3 U4 U5 U6 | pose proof (USH A m md n spa AI NR ENOUGH CEIL) as (U1 & U2 & U3 & U4 & U5 & U6) ]).
    unfold newblk, blk in NB. destruct NB as [[_ Ha]|[_ Ha]].
    - apply chunk_owned. lia.
    - left. right. left. right. left. unfold heap_shadow_. left. exists c. split; [exact (proj1 (hit_class n NR))|]. cbv zeta. change (p_sb (a_pl A)) with sb.
      (first [ pose proof ((region_piece_bounds A c WF0 (proj1 (hit_class n NR)))) as dR_6; dand12 dR_6 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct (region_piece_bounds A c WF0 (proj1 (hit_class n NR))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
      pose proof (sh_mono (region_beg sb c) AB ltac:(lia)).
      pose proof (sh_mono (AB + class_size c) (region_beg sb c + rg_mapped_user (a_reg A c)) ltac:(lia)) as M2.
      rewrite (sh_add (region_beg sb c) (rg_mapped_user (a_reg A c)) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9]) Q10) in M2.
      rewrite U1 in Ha. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ENOUGH NR AI md m"] Lemma owned_sub : forall a, pa_owned A' a -> pa_owned A a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_ in *. cbn [refA a_pl a_reg a_livemap a_sec a_fframes] in H.
    rewrite ref_runtime_maps, ref_heap_shadow in H.
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; [left; left; exact S| | left; right; left; right; exact HS| left; right; right; exact GH| right; exact I].
    left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_11; dex2 dR_11 as p li; destruct dR_11 as [Hl Hp] | intro dR_11; dand4 dR_11 as p li Hl Hp | intros (p & li & Hl & Hp) ])). apply NU. exists p, li. split; [| exact Hp].
    rewrite lookup_insert_ne; [exact Hl|]. intros E. rewrite <- E in Hl. rewrite (rf_u_fresh A m md n AI NR ENOUGH) in Hl. discriminate.
  Qed.
  #[using="CEIL LOSA CLO ENOUGH NR AI lo spa md m"] Lemma owned_lost : forall a, pa_owned A a -> ~ pa_owned A' a -> newblk u n a.
  Proof.
    intros a H NH. unfold pa_owned, aowned, aowned_ in *. cbn [refA a_pl a_reg a_livemap a_sec a_fframes] in NH.
    rewrite ref_runtime_maps, ref_heap_shadow in NH.
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; try (exfalso; apply NH; tauto).
    destruct (decide (u <= a < u + n)) as [Y|X].
    - left. split; [pose proof (GEO A m md n spa AI NR ENOUGH CEIL); pose proof UEQb; kung_all; lia| exact Y].
    - exfalso. apply NH. left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_12; dex2 dR_12 as p li; destruct dR_12 as [Hl Hp] | intro dR_12; dand4 dR_12 as p li Hl Hp | intros (p & li & Hl & Hp) ])). 
      destruct (decide (p = u)) as [->|NEp].
      + rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_n] in Hp. exact (X Hp).
      + rewrite lookup_insert_ne in Hl by congruence. apply NU. exists p, li. auto.
  Qed.

  #[using="WF0 CEIL SM WMv MU HI47 SAHI LOSA CLO ENOUGH NR AI spa md"] Lemma ref_frame_ok : frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) nowhere (newblk u n) v v'.
  Proof.
    pose proof alloc_ceiling_val as CE. unfold frame_ok. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE' _ NB. apply frame1; [exact Ha| exact NO| replace lo with (hi - (hi - lo)) by lia; exact NW| exact NB].
    - intros a Ha NI Hv. right. right. apply (wmono_NN v v' a WMv); [| exact Ha| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. lia.
    - replace (hi - (hi - lo)) with lo by lia. eapply mapped_mono; [exact SM|]. intros i Hi. pose proof (zr_word spa) as R; unfold inr64 in R.
      pose proof alloc_ceiling_val as CV. apply NNb; clear - Hi R CV CLO LOSA SAHI HI47; lia.
    - intros a Ha NB. left. apply newblk_owned. exact NB.
    - intros a Ha O'. left. apply owned_sub. exact O'.
    - intros a Ha O NO'. left. apply owned_lost; assumption.
    - intros a Ha F. destruct F.
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 CEIL WMv MU LOSA CLO ENOUGH NR AI lo spa md"] Lemma ref_hidden : hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    hidden_repr (a_pl A) (ref_reg (a_reg A) c KK) (a_sec A) (munrestrict (hidc (pa_hull A)) m v').
  Proof.
    intros [H1 H2]. unfold hidden_repr. unfold munrestrict.
    assert (VIS : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> v' (wz z) <> None).
    { intros z Hz Hm E. apply NNb; [lia| lia|]. unfold aview_of, mrestrict. rewrite E. exact Hm. }
    split.
    - intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _]. unfold in_shadow_maps in Hz.
      destruct (hidc (pa_hull A) (wz z)) eqn:E; [split; [exact P1| intros X; apply P2; intros Y; apply X; apply (proj2 (ref_heap_shadow _ _ _ _ _ _)); exact Y]|]. split.
      + apply VIS; [kung_all; unfold kHighShadowMapSize in Hz; lia| exact P1| exact E].
      + intros NHS.
        assert (NHS' : ~ heap_shadow_ (p_sb (a_pl A)) (a_reg A) (a_sec A) z) by (intros X; apply NHS; apply (proj2 (ref_heap_shadow _ _ _ _ _ _)); exact X).
        rewrite <- (P2 NHS').
        (* [comment removed for export] *)
        transitivity (aview_of (pa_hull A) m (wz z)); [| unfold aview_of, mrestrict; rewrite E; reflexivity].
        pose proof (GEO A m md n spa AI NR ENOUGH CEIL) as G. (first [ pose proof ((USH A m md n spa AI NR ENOUGH CEIL)) as dR_7; dand6 dR_7 as U1 U2 U3 U4 U5 U6 | pose proof (USH A m md n spa AI NR ENOUGH CEIL) as (U1 & U2 & U3 & U4 & U5 & U6) ]).
        apply (AGW A m n spa v' MU); [kung_all; unfold kHighShadowMapSize in Hz; lia|].
        (* [comment removed for export] *)
        (first [ pose proof ((GEOP A m md AI)) as dR_8; dand3 dR_8 as Gt Gn Gf | pose proof (GEOP A m md AI) as (Gt & Gn & Gf) ]). aobj_lin1 Gt. aobj_lin1 Gn. aobj_lin1 Gf.
        apply (W_shape A m md n spa AI NR ENOUGH CEIL); try (kung_all; unfold kHighShadowMapSize in Hz; lia).
        intros X. apply NHS'. (* [comment removed for export] *)
        left. exists c. split; [exact (proj1 (hit_class n NR))|]. cbv zeta. change (p_sb (a_pl A)) with sb.
        (first [ pose proof ((region_piece_bounds A c WF0 (proj1 (hit_class n NR)))) as dR_9; dand12 dR_9 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct (region_piece_bounds A c WF0 (proj1 (hit_class n NR))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
        pose proof (sh_mono (region_beg sb c) AB ltac:(lia)).
        pose proof (sh_mono (AB + class_size c) (region_beg sb c + rg_mapped_user (a_reg A c)) ltac:(lia)) as M2.
        rewrite (sh_add (region_beg sb c) (rg_mapped_user (a_reg A c)) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9]) Q10) in M2.
        lia.
    - intros z Hz NB. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (H2 z Hz NB)|]. apply VIS; [unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NB)| exact E].
  Qed.
End Post.

