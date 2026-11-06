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
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMTac AMallocA AMallocH AMalmys AMal9l1 AMalgue AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kHighShadowMapSize in *.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Post.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (n kidx : Z) (key : list Z) (spa : word) (v' : mem) (lo hi : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation ks' := (pk_chunks (a_cache A (class_of n))).
  Hypothesis NE : ks' <> [].
  Hypothesis KID : kidx = nth (length ks' - 1) ks' 0.
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
  Local Notation W := (alloc_hit_W spa thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8) n0 f0).
  Local Notation shU := (AB / 8 + rz_size n / 8 + kShadowOffset).
  Local Notation A' := (hitA A n kidx key).
  Hypothesis MU : munch W v v'.
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis SM : mapped v lo (hi - lo).

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CEIL : alloc_ceiling <= bv_unsigned spa - 1024. Proof. clear - CLO LOSA. lia. Qed.
  (* [comment removed for export] *)
  #[using="WMv kidx n"] Lemma NNb : forall a, 0x60a000 <= a -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  Proof. intros a H1 H2. apply wmono_NN; [exact WMv| lia| lia]. Qed.
  #[using="NR"] Lemma UEQb : u = AB + rz_size n.
  Proof. (first [ pose proof ((hit_u_range A n kidx NR)) as dR_1; dand3 dR_1 as _ _ UE | destruct (hit_u_range A n kidx NR) as (_ & _ & UE) ]). exact UE. Qed.

  (* [comment removed for export] *)
  #[using="CEIL WF0 LOSA CLO KID NE NR AI lo spa md m"] Lemma chunk_owned : forall a, AB <= a < AB + class_size c -> pa_owned A a.
  Proof.
    intros a Ha. pose proof (GEO A m md n kidx spa AI NR NE KID CEIL) as G. pose proof (rt_class_in A c (proj1 (hit_class n NR))) as [RIN _].
    apply (owned_rt A a (region_beg sb c) (rg_mapped_user (a_reg A c)) RIN ltac:(lia)).
    - ((first [ intro dR_10; dex2 dR_10 as p li; destruct dR_10 as [Hl Hp] | intro dR_10; dand4 dR_10 as p li Hl Hp | intros (p & li & Hl & Hp) ])). pose proof (primary_chunk_no_other_user A c kidx a WF0 (proj1 (hit_class n NR)) ltac:(lia) Ha p li Hl Hp) as E.
      exact (hit_not_live A m md n kidx AI NR NE KID p li Hl E).
    - apply b6_no_live_frame; [exact WF0|]. apply primary_in_b6; [exact WF0|]. kung_all. lia.
  Qed.
  #[using="WF0 NR AI kidx n md m"] Lemma thr_owned : forall a, thr <= a < thr + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_2; dand6 dR_2 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
    apply (owned_rt A a thr 4096); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 4); [exact WF0| lia| exact E4| exact Ha]
      | eapply (fixed_bm_no_live_frame A 4); [exact WF0| lia| lia| exact E4| exact Ha]].
  Qed.
  #[using="WF0 NR AI kidx n md m"] Lemma n0_owned : forall a, n0 <= a < n0 + kDepotNodesBlock -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_3; dand9 dR_3 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]).
    apply (owned_rt A a n0 kDepotNodesBlock); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 7); [exact WF0| lia| exact E7| exact Ha]
      | eapply (fixed_bm_no_live_frame A 7); [exact WF0| lia| lia| exact E7| exact Ha]].
  Qed.
  #[using="WF0 NR AI kidx n md m"] Lemma f0_owned : forall a, f0 <= a < f0 + kStackStoreBlockBytes -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_4; dand10 dR_4 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]).
    apply (owned_rt A a f0 kStackStoreBlockBytes); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 8); [exact WF0| lia| exact E8| exact Ha]
      | eapply (fixed_bm_no_live_frame A 8); [exact WF0| lia| lia| exact E8| exact Ha]].
  Qed.
  #[using="kidx n"] Lemma dstat_owned : forall a, 0x186a88 <= a < 0x5d6aa8 -> pa_owned A a.
  Proof. intros a Ha. apply asI_static_owned. cbn [cl_static LPA]. apply depot_static. cbn. unfold kDepotNodesL1. lia. Qed.

  (* [comment removed for export] *)
  #[using="CEIL WF0 MU SAHI LOSA CLO KID NE NR AI spa md"] Lemma frame1 : forall a, 0 <= a < 2^64 -> ~ pa_owned A a -> ~ (lo <= a < hi) -> ~ newblk u n a ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha NO NW NB. pose proof (GEO A m md n kidx spa AI NR NE KID CEIL) as G. pose proof UEQb as UE.
    pose proof (USH A m md n kidx spa AI NR NE KID CEIL) as (U1 & _). unfold newblk, blk in NB. rewrite U1 in NB.
    apply (AGW A m n kidx spa v' MU); [lia|].
    apply (W_shape A m md n kidx spa AI NR NE KID CEIL).
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
  Qed.

  (* [comment removed for export] *)
  #[using="CEIL WF0 LOSA CLO KID NE NR AI lo spa md m"] Lemma newblk_owned : forall a, newblk u n a -> pa_owned A a.
  Proof.
    intros a NB. pose proof (GEO A m md n kidx spa AI NR NE KID CEIL) as G. pose proof UEQb as UE. (first [ pose proof ((USH A m md n kidx spa AI NR NE KID CEIL)) as dR_5; dand6 dR_5 as U1 U2 U3 U4 U5 U6 | pose proof (USH A m md n kidx spa AI NR NE KID CEIL) as (U1 & U2 & U3 & U4 & U5 & U6) ]).
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
  #[using="KID NE NR AI md m"] Lemma owned_sub : forall a, pa_owned A' a -> pa_owned A a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_ in *. cbn [hitA a_pl a_reg a_livemap a_sec a_fframes] in H.
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; [left; left; exact S| | left; right; left; right; exact HS| left; right; right; exact GH| right; exact I].
    left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_11; dex2 dR_11 as p li; destruct dR_11 as [Hl Hp] | intro dR_11; dand4 dR_11 as p li Hl Hp | intros (p & li & Hl & Hp) ])). apply NU. exists p, li. split; [| exact Hp].
    rewrite lookup_insert_ne; [exact Hl|]. intros E. rewrite <- E in Hl. rewrite (hit_u_fresh A m md n kidx AI NR NE KID) in Hl. discriminate.
  Qed.
  #[using="CEIL LOSA CLO KID NE NR AI lo spa md m"] Lemma owned_lost : forall a, pa_owned A a -> ~ pa_owned A' a -> newblk u n a.
  Proof.
    intros a H NH. unfold pa_owned, aowned, aowned_ in *. cbn [hitA a_pl a_reg a_livemap a_sec a_fframes] in NH.
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; try (exfalso; apply NH; tauto).
    destruct (decide (u <= a < u + n)) as [Y|X].
    - left. split; [pose proof (GEO A m md n kidx spa AI NR NE KID CEIL); pose proof UEQb; kung_all; lia| exact Y].
    - exfalso. apply NH. left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_12; dex2 dR_12 as p li; destruct dR_12 as [Hl Hp] | intro dR_12; dand4 dR_12 as p li Hl Hp | intros (p & li & Hl & Hp) ])). 
      destruct (decide (p = u)) as [->|NEp].
      + rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_n] in Hp. exact (X Hp).
      + rewrite lookup_insert_ne in Hl by congruence. apply NU. exists p, li. auto.
  Qed.

  #[using="CEIL WF0 SM WMv MU HI47 SAHI LOSA CLO KID NE NR AI spa md"] Lemma hit_frame_ok : frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) nowhere (newblk u n) v v'.
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
  #[using="CEIL WF0 WMv MU LOSA CLO KID NE NR AI lo spa kidx n md"] Lemma hit_hidden : hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    hidden_repr (a_pl A) (a_reg A) (a_sec A) (munrestrict (hidc (pa_hull A)) m v').
  Proof.
    intros [H1 H2]. unfold hidden_repr. unfold munrestrict.
    assert (VIS : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> v' (wz z) <> None).
    { intros z Hz Hm E. apply NNb; [lia| lia|]. unfold aview_of, mrestrict. rewrite E. exact Hm. }
    split.
    - intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _]. unfold in_shadow_maps in Hz.
      destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (conj P1 P2)|]. split.
      + apply VIS; [kung_all; unfold kHighShadowMapSize in Hz; lia| exact P1| exact E].
      + intros NHS. rewrite <- (P2 NHS).
        (* [comment removed for export] *)
        transitivity (aview_of (pa_hull A) m (wz z)); [| unfold aview_of, mrestrict; rewrite E; reflexivity].
        pose proof (GEO A m md n kidx spa AI NR NE KID CEIL) as G. (first [ pose proof ((USH A m md n kidx spa AI NR NE KID CEIL)) as dR_7; dand6 dR_7 as U1 U2 U3 U4 U5 U6 | pose proof (USH A m md n kidx spa AI NR NE KID CEIL) as (U1 & U2 & U3 & U4 & U5 & U6) ]).
        apply (AGW A m n kidx spa v' MU); [kung_all; unfold kHighShadowMapSize in Hz; lia|].
        (* [comment removed for export] *)
        (first [ pose proof ((GEOP A m md AI)) as dR_8; dand3 dR_8 as Gt Gn Gf | pose proof (GEOP A m md AI) as (Gt & Gn & Gf) ]). aobj_lin1 Gt. aobj_lin1 Gn. aobj_lin1 Gf.
        apply (W_shape A m md n kidx spa AI NR NE KID CEIL); try (kung_all; unfold kHighShadowMapSize in Hz; lia).
        intros X. apply NHS. (* [comment removed for export] *)
        left. exists c. split; [exact (proj1 (hit_class n NR))|]. cbv zeta. change (p_sb (a_pl A)) with sb.
        (first [ pose proof ((region_piece_bounds A c WF0 (proj1 (hit_class n NR)))) as dR_9; dand12 dR_9 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct (region_piece_bounds A c WF0 (proj1 (hit_class n NR))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
        pose proof (sh_mono (region_beg sb c) AB ltac:(lia)).
        pose proof (sh_mono (AB + class_size c) (region_beg sb c + rg_mapped_user (a_reg A c)) ltac:(lia)) as M2.
        rewrite (sh_add (region_beg sb c) (rg_mapped_user (a_reg A c)) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9]) Q10) in M2.
        lia.
    - intros z Hz NB. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (H2 z Hz NB)|]. apply VIS; [unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NB)| exact E].
  Qed.
End Post.

