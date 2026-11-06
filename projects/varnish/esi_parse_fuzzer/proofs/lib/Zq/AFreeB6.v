(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys AMal9l1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AQPart AQWf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQPart.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart.AQWfJ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_remove (sec : secreg) (i : nat) : secreg := SR (swap_remove (sr_chunks sec) i (CS 0 0)) (sr_reserved sec).

Definition freeS (A : AState) (p : Z) (i : nat) (D' : list (list Z)) (ia' : bool) (dead' : list (Z * Z)) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A)
      (free_lm A p) (a_qthread A) (a_qglobal A) (sec_remove (a_sec A) i) D'
      (a_fhint A) (a_fframes A) ia' (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A ++ dead') (a_pcred A) (a_paid A).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma nth_error_last : forall {X} (l : list X) d, l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
  intros X l d NE. induction l as [|a r IH]; [congruence|]. destruct r as [|b r']; [reflexivity|].
  specialize (IH ltac:(discriminate)).
  cbn [length] in IH |- *. replace (S (S (length r')) - 1)%nat with (S (S (length r') - 1))%nat by lia.
  cbn [nth_error]. cbn [nth_error] in IH. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sr_src (n i j : nat) : nat := if Nat.eqb j i then (n - 1)%nat else j.

Lemma swap_remove_src : forall {X} (l : list X) i d j x,
  (i < length l)%nat -> nth_error (swap_remove l i d) j = Some x -> nth_error l (sr_src (length l) i j) = Some x /\ (j < length l - 1)%nat.
Proof.
  intros X l i d j x Hi H.
  assert (NE : l <> []) by (intros ->; cbn in Hi; lia).
  pose proof (nth_error_Some_lt _ _ _ H) as JL. rewrite (swap_remove_length l i d NE) in JL.
  split; [| exact JL].
  rewrite (swap_remove_nth_error l i d j Hi ltac:(lia)) in H. unfold sr_src.
  destruct (Nat.eqb j i) eqn:E; [| exact H].
  injection H as <-. apply nth_error_last. exact NE.
Qed.

Lemma sr_src_inj : forall n i j k, (i < n)%nat -> (j < n - 1)%nat -> (k < n - 1)%nat -> j <> k -> sr_src n i j <> sr_src n i k.
Proof. intros n i j k Hi Hj Hk NE. unfold sr_src. destruct (Nat.eqb_spec j i); destruct (Nat.eqb_spec k i); lia. Qed.

Lemma swap_remove_In : forall {X} (l : list X) i d y, (i < length l)%nat -> In y (swap_remove l i d) -> In y l.
Proof. intros X l i d y Hi H. apply (swap_remove_incl l i d y); [intros ->; cbn in Hi; lia| exact H]. Qed.

(* [comment removed for export] *)
Lemma last_map' : forall {X Y} (f : X -> Y) (l : list X) d, last (map f l) (f d) = f (last l d).
Proof. intros X Y f l d. induction l as [|a r IH]; [reflexivity|]. cbn [map last]. rewrite IH. destruct r; reflexivity. Qed.
Lemma removelast_map : forall {X Y} (f : X -> Y) (l : list X), removelast (map f l) = map f (removelast l).
Proof. intros X Y f l. induction l as [|a r IH]; [reflexivity|]. cbn [map removelast]. rewrite IH. destruct r; reflexivity. Qed.
Lemma list_set_map : forall {X Y} (f : X -> Y) (l : list X) i x, list_set (map f l) i (f x) = map f (list_set l i x).
Proof. intros X Y f l. induction l as [|a r IH]; intros [|i] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma swap_remove_map : forall {X Y} (f : X -> Y) (l : list X) i d, swap_remove (map f l) i (f d) = map f (swap_remove l i d).
Proof. intros X Y f l i d. unfold swap_remove. rewrite last_map', list_set_map, removelast_map. reflexivity. Qed.

Lemma NoDup_swap_remove : forall {X} (l : list X) i d, (i < length l)%nat -> NoDup l -> NoDup (swap_remove l i d).
Proof.
  intros X l i d Hi ND. apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup.
  apply (proj2 (NoDup_nth_error (swap_remove l i d))). intros j k HjL E.
  destruct (nth_error (swap_remove l i d) j) as [x|] eqn:Ej; [| apply nth_error_None in Ej; lia].
  destruct (swap_remove_src l i d j x Hi Ej) as [Sj Jl].
  symmetry in E. destruct (swap_remove_src l i d k x Hi E) as [Sk Kl].
  destruct (Nat.eq_dec j k) as [EQ|NEQ]; [exact EQ|]. exfalso.
  apply (sr_src_inj (length l) i j k Hi Jl Kl NEQ).
  apply (proj1 (NoDup_nth_error l) ND); [apply nth_error_Some_lt in Sj; exact Sj|]. rewrite Sj, Sk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swap_remove_in_iff' : forall {X} (l : list X) i d x0 y, NoDup l -> nth_error l i = Some x0 ->
  (In y (swap_remove l i d) <-> In y l /\ y <> x0).
Proof. intros X l i d x0 y ND Hi. apply (swap_remove_in_iff l i d x0 y); assumption. Qed.

(* [comment removed for export] *)
Lemma sec_eager_app : forall l1 l2, sec_eager_ (l1 ++ l2) = sec_eager_ l1 + sec_eager_ l2.
Proof. induction l1 as [|a r IH]; intros l2; [reflexivity|]. cbn [app]. unfold sec_eager_ in *. cbn [fold_right]. rewrite IH. lia. Qed.
Lemma sec_eager_cons : forall a r, sec_eager_ (a :: r) = map_size (cs_n a) + sec_eager_ r. Proof. reflexivity. Qed.
Lemma sec_eager_set : forall l j x y, nth_error l j = Some x -> sec_eager_ (list_set l j y) = sec_eager_ l - map_size (cs_n x) + map_size (cs_n y).
Proof.
  induction l as [|a r IH]; intros [|j] x y H; cbn in H; try discriminate.
  - injection H as ->. cbn [list_set]. rewrite !sec_eager_cons. lia.
  - cbn [list_set]. rewrite !sec_eager_cons, (IH j x y H). lia.
Qed.
Lemma last_set : forall {X} (l : list X) j d, (j < length l)%nat -> last (list_set l j (last l d)) d = last l d.
Proof.
  induction l as [|a r IH]; intros [|j] d Hj; cbn in Hj; try lia; cbn [list_set].
  - destruct r; reflexivity.
  - specialize (IH j d ltac:(lia)). destruct r as [|b r']; [cbn in Hj; lia|].
    cbn [last] in IH |- *. destruct j; cbn [list_set] in IH |- *; exact IH.
Qed.
Lemma sec_eager_swap_remove : forall l j x, nth_error l j = Some x -> sec_eager_ (swap_remove l j (CS 0 0)) = sec_eager_ l - map_size (cs_n x).
Proof.
  intros l j x H. assert (JL : (j < length l)%nat) by (apply nth_error_Some; rewrite H; discriminate).
  assert (NE : l <> []) by (intros ->; cbn in JL; lia).
  assert (NE' : list_set l j (last l (CS 0 0)) <> []) by (destruct l; [congruence|]; destruct j; discriminate).
  pose proof (removelast_last_app (list_set l j (last l (CS 0 0))) (CS 0 0) NE') as E.
  apply (f_equal sec_eager_) in E. rewrite sec_eager_app, sec_eager_cons, (last_set l j _ JL), (sec_eager_set l j x _ H) in E.
  pose proof (removelast_last_app l (CS 0 0) NE) as E0. apply (f_equal sec_eager_) in E0. rewrite sec_eager_app, sec_eager_cons in E0.
  unfold swap_remove. unfold sec_eager_ in E, E0 |- *. cbn [fold_right] in E, E0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WfFreeS.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (li : liveinfo) (key : list Z) (s : chunkS) (i : nat) (ia' : bool) (dead' : list (Z * Z)).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis LC : li_chunk li = ChS s.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some s.
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  (* [comment removed for export] *)
  Hypothesis DEADF : Forall (fun lh => ((kHighShadowMapBeg <= fst lh /\ snd lh <= kHighMemBeg) \/ (kLowShadowBeg <= fst lh /\ snd lh <= kShadowGapBeg))
                      /\ fst lh <= snd lh <= fst lh + kDeadShadowBytes /\ fst lh mod 8 = 0 /\ snd lh mod 8 = 0) dead'.
  Hypothesis DEADL : (length dead' <= 2)%nat.
  Hypothesis DEADB : hull_bytes dead' <= kDeadShadowBytes.

  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  Let IL : (i < length chunks)%nat. Proof. exact (nth_error_Some_lt _ _ _ NTH). Qed.
  Let NEC : chunks <> []. Proof. intros E. pose proof IL as H. rewrite E in H. cbn in H. lia. Qed.
  Let INs : In s chunks. Proof. eapply nth_error_In. exact NTH. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma freeS_live_other : forall u l, a_livemap A !! u = Some l -> u <> p -> li_chunk l <> ChS s.
  Proof. intros u l Hu NE E. apply (free_uniq A m md p li AI LU u l Hu ltac:(congruence)). rewrite LC, E. reflexivity. Qed.
  Lemma freeS_quar_other : ~ In (ChS s) (quarantined_chunks_ (a_qthread A) (a_qglobal A)).
  Proof. (first [ pose proof ((wfQ A W)) as dR_4; dand8 dR_4 as _ _ _ _ _ _ _ Q8 | destruct (wfQ A W) as (_ & _ & _ & _ & _ & _ & _ & Q8) ]). rewrite <- LC. exact (Q8 p li LU). Qed.

  Lemma sec_nodup : NoDup chunks.
  Proof. destruct (wfS A W) as (S1 & _). exact (ABudget.NoDup_of_map cs_map _ S1). Qed.

  Lemma chunks'_in_iff : forall y, In y (swap_remove chunks i (CS 0 0)) <-> In y chunks /\ y <> s.
  Proof. intros y. apply swap_remove_in_iff'; [exact sec_nodup| exact NTH]. Qed.
  Lemma chunks'_length : length (swap_remove chunks i (CS 0 0)) = (length chunks - 1)%nat.
  Proof. apply swap_remove_length. exact NEC. Qed.

  (* [comment removed for export] *)
  Lemma freeS_bigmaps : wf_bigmaps_ (a_pl A) (sec_remove (a_sec A) i).
  Proof.
    destruct (wfM A W) as [M1 M2]. unfold wf_bigmaps_, big_maps_ in *. cbn [sec_remove sr_chunks] in *.
    set (FIX := [(p_b6 (a_pl A), kSpaceReserve); (p_pa (a_pl A), kPtrArrayReserve); (kHighShadowMapBeg, kHighShadowMapSize); (kLowShadowMapBeg, 268435456);
                 (p_thr (a_pl A), 4096); (p_ctx (a_pl A), 65536); (p_fs (a_pl A), kFakeStackBytes); (p_nodes0 (a_pl A), kDepotNodesBlock);
                 (p_frames0 (a_pl A), kStackStoreBlockBytes); (p_itab (a_pl A), 3727360); (p_m64k (a_pl A), 65536);
                 (p_gvec (a_pl A), 4096); (p_dvec (a_pl A), 4096); (p_m11 (a_pl A), 4096); (p_dtls (a_pl A), 4096)]) in *.
    set (f := fun s0 : chunkS => (cs_map s0, map_size (cs_n s0))) in *.
    assert (LF : length FIX = 15%nat) by reflexivity.
    (* [comment removed for export] *)
    set (g := fun j : nat => if Nat.ltb j 15 then j else (15 + sr_src (length chunks) i (j - 15))%nat).
    assert (G1 : forall j, (j < 15)%nat -> g j = j) by (intros j Hj; unfold g; rewrite (proj2 (Nat.ltb_lt j 15) Hj); reflexivity).
    assert (G2 : forall j, (15 <= j)%nat -> g j = (15 + sr_src (length chunks) i (j - 15))%nat) by (intros j Hj; unfold g; rewrite (proj2 (Nat.ltb_ge j 15) Hj); reflexivity).
    assert (SRC : forall j x, nth_error (FIX ++ map f (swap_remove chunks i (CS 0 0))) j = Some x ->
                  nth_error (FIX ++ map f chunks) (g j) = Some x /\ ((15 <= j)%nat -> (j - 15 < length chunks - 1)%nat)).
    { intros j x H. destruct (Nat.lt_ge_cases j 15) as [LT|GE].
      - rewrite (G1 j LT). rewrite nth_error_app1 in H by lia. rewrite nth_error_app1 by lia. split; [exact H| intros; lia].
      - rewrite (G2 j GE). rewrite nth_error_app2 in H by lia. rewrite LF in H.
        rewrite <- (swap_remove_map f chunks i (CS 0 0)) in H.
        destruct (swap_remove_src (map f chunks) i (f (CS 0 0)) (j - 15) x ltac:(rewrite length_map; exact IL) H) as [S JL].
        rewrite length_map in S, JL. rewrite nth_error_app2 by lia. rewrite LF. replace (15 + sr_src (length chunks) i (j - 15) - 15)%nat with (sr_src (length chunks) i (j - 15)) by lia.
        split; [exact S| intros _; exact JL]. }
    split.
    - intros j k bj sj bk sk Hj Hk NE.
      destruct (SRC j _ Hj) as [Sj Jl]. destruct (SRC k _ Hk) as [Sk Kl].
      apply (M1 (g j) (g k) bj sj bk sk Sj Sk).
      destruct (Nat.lt_ge_cases j 15) as [Lj|Lj]; destruct (Nat.lt_ge_cases k 15) as [Lk|Lk];
        rewrite ?(G1 j Lj), ?(G2 j Lj), ?(G1 k Lk), ?(G2 k Lk); try lia.
      specialize (Jl Lj). specialize (Kl Lk).
      pose proof (sr_src_inj (length chunks) i (j - 15) (k - 15) IL Jl Kl ltac:(lia)). lia.
    - intros b sz Hin. apply M2. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
      apply in_map_iff in Hin as (s0 & <- & Hs0). apply in_map. apply (swap_remove_In chunks i (CS 0 0)); [exact IL| exact Hs0].
  Qed.

  Lemma freeS_live : wf_live_ (a_sb A) (a_reg A) (free_lm A p) (sec_remove (a_sec A) i).
  Proof.
    (first [ pose proof ((wf_live_delete (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li (wfV A W) LU)) as dR_5; dand3 dR_5 as V1 V2 V3 | pose proof (wf_live_delete (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li (wfV A W) LU) as (V1 & V2 & V3) ]).
    unfold free_lm. split; [| split; [exact V2| exact V3]].
    intros u l Hu. (first [ pose proof ((V1 u l Hu)) as dR_6; dand3 dR_6 as N U M | pose proof (V1 u l Hu) as (N & U & M) ]). cbv zeta in M |- *. split; [exact N|]. split; [exact U|].
    destruct (li_chunk l) as [[c k]|[mb n1]] eqn:EC; [exact M|]. (first [ dand3 M as M1 M2 M3 | destruct M as (M1 & M2 & M3) ]). split; [exact M1|]. split; [exact M2|].
    cbn [sec_remove sr_chunks]. apply (proj2 (chunks'_in_iff _)). split; [exact M3|].
    rewrite lookup_delete_Some in Hu. destruct Hu as [NE Hu]. intros E. apply (freeS_live_other u l Hu ltac:(congruence)). rewrite EC, <- E, M2. reflexivity.
  Qed.

  Lemma freeS_qentry : forall e, wf_qentry_ (a_reg A) (a_sec A) e -> qe_chunk e <> ChS s -> wf_qentry_ (a_reg A) (sec_remove (a_sec A) i) e.
  Proof.
    intros e H NE. unfold wf_qentry_ in *. destruct H as [H1 H2]. split; [exact H1|].
    destruct (qe_chunk e) as [[c k]|[mb n1]] eqn:EC; [exact H2|]. (first [ dand3 H2 as A1 A2 A3 | destruct H2 as (A1 & A2 & A3) ]). split; [exact A1|]. split; [exact A2|].
    cbn [sec_remove sr_chunks]. apply (proj2 (chunks'_in_iff _)). split; [exact A3| congruence].
  Qed.

  Lemma freeS_quarantine : wf_quarantine_ (a_reg A) (free_lm A p) (a_qthread A) (a_qglobal A) (sec_remove (a_sec A) i).
  Proof.
    (first [ pose proof ((wfQ A W)) as dR_9; dand8 dR_9 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct (wfQ A W) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]). unfold wf_quarantine_, free_lm.
    assert (BW : forall bs, (forall e, In e (q_entries bs) -> In (qe_chunk e) (quarantined_chunks_ (a_qthread A) (a_qglobal A))) ->
                 Forall (wf_batch_ (a_reg A) (a_sec A)) bs -> Forall (wf_batch_ (a_reg A) (sec_remove (a_sec A) i)) bs).
    { intros bs SUB F. apply Forall_forall. intros b Hb. (first [ pose proof ((proj1 (Forall_forall _ _) F b Hb)) as dR_10; dand3 dR_10 as B1 B2 B3 | pose proof (proj1 (Forall_forall _ _) F b Hb) as (B1 & B2 & B3) ]).
      split; [exact B1|]. split; [exact B2|]. apply Forall_forall. intros e He. apply freeS_qentry; [exact (proj1 (Forall_forall _ _) B3 e He)|].
      intros E. apply freeS_quar_other. rewrite <- E. apply SUB. unfold q_entries. apply in_flat_map. exists b. split; [exact Hb| exact He]. }
    split; [| split; [| split; [exact Q3| split; [exact Q4| split; [exact Q5| split; [exact Q6| split; [exact Q7|]]]]]]].
    - apply BW; [| exact Q1]. intros e He. rewrite quarantined_chunks_def. apply in_map. apply in_or_app. left. exact He.
    - apply BW; [| exact Q2]. intros e He. rewrite quarantined_chunks_def. apply in_map. apply in_or_app. right. exact He.
    - intros u l Hu. rewrite lookup_delete_Some in Hu. destruct Hu as [_ Hu]. exact (Q8 u l Hu).
  Qed.

  Lemma freeS_sec : wf_sec_ AL_pboth (free_lm A p) (a_qthread A) (a_qglobal A) (sec_remove (a_sec A) i).
  Proof.
    (first [ pose proof ((wfS A W)) as dR_11; dand5 dR_11 as S1 S2 S3 S4 S5 | destruct (wfS A W) as (S1 & S2 & S3 & S4 & S5) ]). unfold wf_sec_, free_lm. cbn [sec_remove sr_chunks sr_reserved].
    split; [| split; [| split; [exact S3| split]]].
    - rewrite <- (swap_remove_map cs_map chunks i (CS 0 0)). apply NoDup_swap_remove; [rewrite length_map; exact IL| exact S1].
    - rewrite chunks'_length. lia.
    - intros s0 Hs0. apply S4. exact (proj1 (proj1 (chunks'_in_iff s0) Hs0)).
    - intros s0 Hs0. apply chunks'_in_iff in Hs0 as [Hs0 NE]. destruct (S5 s0 Hs0) as [(u & Hu)|Hq]; [| right; exact Hq].
      left. exists u. rewrite lookup_delete_Some. split; [| exact Hu]. intros ->. rewrite LU in Hu. injection Hu as E.
      apply NE. rewrite E in LC. cbn in LC. congruence.
  Qed.

  Lemma freeS_budget : wf_budget_ (a_tiny A) (free_lm A p) (a_qthread A) (a_qglobal A).
  Proof.
    (first [ pose proof ((wfB A W)) as dR_12; dand5 dR_12 as B1 B2 B3 B4 B5 | destruct (wfB A W) as (B1 & B2 & B3 & B4 & B5) ]). unfold wf_budget_, free_lm.
    rewrite (as_livebytes_delete' _ p li LU), (as_nlive_delete _ p li LU), (tiny_live_delete _ p li LU).
    (first [ pose proof ((wfV A W)) as dR_13; dand3 dR_13 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). pose proof (V1 p li LU) as (N & _). cbv zeta in N.
    pose proof (is_tiny_range01 (li_n li)) as IT.
    assert (TLN : forall (l : gmap Z liveinfo), 0 <= tiny_live_ l).
    { intros l. unfold tiny_live_. apply (map_fold_weak_ind (fun r _ => 0 <= r)); [lia|]. intros j x mm r _ Hr. pose proof (is_tiny_range01 (li_n x)). lia. }
    pose proof (TLN (delete p (a_livemap A))) as T0. rewrite (tiny_live_delete _ p li LU) in T0.
    pose proof (as_livebytes_nonneg (delete p (a_livemap A)) ltac:(intros u l Hu; rewrite lookup_delete_Some in Hu; destruct Hu as [_ Hu]; pose proof (V1 u l Hu) as (X & _); cbv zeta in X; lia)) as LB0.
    rewrite (as_livebytes_delete' _ p li LU) in LB0.
    split; [exact B1|]. split; [lia|]. split; [lia|]. split; [exact T0| lia].
  Qed.

  Lemma freeS_dead : wf_dead_ (a_scred A) (a_deadsh A ++ dead') (Z.of_nat (length (swap_remove chunks i (CS 0 0)))).
  Proof.
    (first [ pose proof ((wfE A W)) as dR_14; dand4 dR_14 as E1 E2 E3 E4 | destruct (wfE A W) as (E1 & E2 & E3 & E4) ]). rewrite chunks'_length.
    pose proof IL as ILn.
    split; [exact E1|]. split; [apply Forall_app; split; [exact E2| exact DEADF]|]. split.
    - rewrite length_app, Nat2Z.inj_add. clear -E3 DEADL ILn. lia.
    - rewrite hull_bytes_app. clear -E4 DEADB ILn. unfold kDeadShadowBytes in *. lia.
  Qed.

  Theorem freeS_WF : WF (freeS A p i (fst (depot_putC (a_depot A) key)) ia' dead').
  Proof.
    pose proof W as W0. destruct W0 as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN].
    constructor; cbn [freeS a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact freeS_bigmaps.
    - exact wR.
    - exact wC.
    - apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (free_lm A p) (a_qthread A) (a_qglobal A)))).
      unfold free_lm. apply (pfun_free_gen (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) p li).
      + apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + exact LU.
      + exact (free_uniq A m md p li AI LU).
      + exact (free_lrange A m md p li AI LU).
      + intros c k. cbn [qe_chunk]. rewrite LC. split; [intros H; left; exact H| intros [H|H]; [exact H| discriminate]].
      + intros c k. reflexivity.
    - exact freeS_live.
    - exact freeS_quarantine.
    - exact freeS_sec.
    - exact (free_wfD A m md key AI KEYU).
    - exact wF.
    - exact freeS_budget.
    - exact wI.
    - cbn [sec_remove sr_chunks]. exact freeS_dead.
    - exact wJ.
    - (* [comment removed for export] *)
      destruct wN as (P0 & PS & PD). split; [exact P0|]. split; [exact PS|]. unfold free_lm.
      intros c k Hc [V|Q]; apply (PD c k Hc); [left| right; exact Q].
      destruct V as (u0 & n1 & Hu). rewrite lookup_delete_Some in Hu. destruct Hu as [_ Hu]. exists u0, n1. exact Hu.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma freeS_livebytes : as_livebytes (freeS A p i (fst (depot_putC (a_depot A) key)) ia' dead') = as_livebytes A - n0.
  Proof. unfold as_livebytes. cbn [freeS a_livemap]. unfold free_lm. rewrite (as_livebytes_delete' _ _ _ LU), LN. reflexivity. Qed.
  Lemma freeS_nlive : as_nlive (freeS A p i (fst (depot_putC (a_depot A) key)) ia' dead') = as_nlive A - 1.
  Proof. unfold as_nlive. cbn [freeS a_livemap]. unfold free_lm. rewrite (as_nlive_delete _ _ _ LU). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma freeS_eager : aeager_of (freeS A p i (fst (depot_putC (a_depot A) key)) ia' dead') = aeager_of A - map_size (cs_n s).
  Proof.
    unfold aeager_of, aeager_of_. cbn [freeS a_pl a_reg a_sec sec_remove sr_chunks sr_reserved].
    rewrite (sec_eager_swap_remove chunks i s NTH). lia.
  Qed.
End WfFreeS.
