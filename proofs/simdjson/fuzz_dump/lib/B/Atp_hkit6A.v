(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_hkit2 Atp_hkit4A Atp_hkit5A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition lposx (L : list (Z * Z)) : Prop := forall p n, In (p, n) L -> exists n', In (p, n') L /\ 0 < n'.

Lemma lposx_of_pos : forall L, (forall p n, In (p, n) L -> 0 < n) -> lposx L.
Proof. intros L H p n Hin. exists n. split; [exact Hin| exact (H p n Hin)]. Qed.

Lemma lposx_cons : forall p n L, 0 < n -> lposx L -> lposx ((p, n) :: L).
Proof.
  intros p n L Hn HL q k [E|Hin].
  - injection E as <- <-. exists n. split; [left; reflexivity| exact Hn].
  - destruct (HL q k Hin) as (n' & H1 & H2). exists n'. split; [right; exact H1| exact H2].
Qed.

Lemma lposx_app : forall L1 L2, lposx L1 -> lposx L2 -> lposx (L1 ++ L2).
Proof.
  intros L1 L2 H1 H2 q k Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 q k Hin) as (n' & A & B). exists n'. split; [apply in_or_app; left; exact A| exact B].
  - destruct (H2 q k Hin) as (n' & A & B). exists n'. split; [apply in_or_app; right; exact A| exact B].
Qed.

Lemma lposx_ann_block : forall A n v, 0 < v -> lposx (ann_block A n v).
Proof.
  intros A n v Hv q k Hin. pose proof (ann_block_fst A n v (q, k) Hin) as E. cbn [fst] in E. subst q.
  exists v. split; [apply ann_block_vis| exact Hv].
Qed.

Lemma live_remove_one : forall (x n : Z) (pre1 pre2 L : list (Z * Z)),
  (forall e, In e pre1 -> fst e <> x) -> (forall e, In e pre2 -> fst e <> x) -> (forall e, In e L -> fst e <> x) ->
  live_remove x (pre1 ++ (x, n) :: pre2 ++ L) = pre1 ++ pre2 ++ L.
Proof.
  intros x n pre1 pre2 L H1 H2 HL.
  rewrite live_remove_app', live_remove_cons'. cbn [fst]. rewrite Z.eqb_refl. rewrite live_remove_app'.
  rewrite (live_remove_none' x pre1 H1), (live_remove_none' x pre2 H2), (live_remove_none' x L HL). reflexivity.
Qed.

Section Kit6.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma pos_prefix_facts : forall Σ m (pre acc L : list (Z * Z)),
  ART RT Σ m -> rt_live RT Σ = acc ++ pre ++ L ->
  (forall e, In e pre -> 0 < snd e) -> lposx L ->
  List.NoDup (map fst pre) /\ (forall e e', In e pre -> In e' L -> fst e <> fst e').
Proof using AF.
  intros Σ m pre. induction pre as [|[p n] pre IH]; intros acc L HA E HP HL.
  - split; [constructor| intros e e' [] _].
  - assert (Hn : 0 < n) by exact (HP (p, n) (or_introl eq_refl)).
    assert (DJ : forall q k, In (q, k) (pre ++ L) -> p + n <= q \/ q + k <= p).
    { intros q k Hin. apply (af_live_disj RT AF Σ m p n q k acc (pre ++ L) HA); [rewrite E; reflexivity|].
      apply in_or_app. right. exact Hin. }
    destruct (IH (acc ++ [(p, n)]) L HA ltac:(rewrite E, <- app_assoc; reflexivity) ltac:(intros e He; apply HP; right; exact He) HL) as [ND NI].
    split.
    + cbn [map fst]. constructor; [| exact ND]. intros Hin. apply in_map_iff in Hin. destruct Hin as ([q k] & Eq & Hq). cbn [fst] in Eq. subst q.
      pose proof (HP (p, k) (or_intror Hq)) as Hk. cbn [snd] in Hk. destruct (DJ p k ltac:(apply in_or_app; left; exact Hq)); lia.
    + intros e e' [<-|He] He'; [| exact (NI e e' He He')]. cbn [fst]. destruct e' as [q k]. cbn [fst]. intros <-.
      destruct (HL p k He') as (n' & Hin' & Hn'). destruct (DJ p n' ltac:(apply in_or_app; right; exact Hin')); lia.
Qed.

Lemma six_facts : forall Σ m (ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf : Z) (L : list (Z * Z)),
  ART RT Σ m -> rt_live RT Σ = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: L ->
  0 < nia -> 0 < noc -> 0 < nidx -> 0 < nimpl -> 0 < ntape -> 0 < nsbuf -> lposx L ->
  List.NoDup [sbuf; tape; ia; oc; idx; impl]
  /\ live_remove impl (live_remove idx (live_remove oc (live_remove ia (live_remove tape (live_remove sbuf
       ((ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: L)))))) = L.
Proof using AF.
  intros Σ m ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf L HA E P1 P2 P3 P4 P5 P6 HL.
  destruct (pos_prefix_facts Σ m [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf)] [] L HA
              ltac:(rewrite E; reflexivity)
              ltac:(intros e He; cbn [In] in He; destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [snd]; assumption) HL) as [ND NI].
  cbn [map fst] in ND. split; [exact (six_nodup0 ia oc idx impl tape sbuf [] ND)|].
  assert (NL : forall x k, In (x, k) [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf)] -> forall e, In e L -> fst e <> x).
  { intros x k Hx e He Ee. apply (NI (x, k) e Hx He). cbn [fst]. rewrite Ee. reflexivity. }
  pose proof (fun i j x y => @nodup_nth_neq Z _ i j x y ND) as NN.
  pose proof (NN 0%nat 1%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M01.
  pose proof (NN 0%nat 2%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M02.
  pose proof (NN 0%nat 3%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M03.
  pose proof (NN 0%nat 4%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M04.
  pose proof (NN 0%nat 5%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M05.
  pose proof (NN 1%nat 2%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M12.
  pose proof (NN 1%nat 3%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M13.
  pose proof (NN 1%nat 4%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M14.
  pose proof (NN 1%nat 5%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M15.
  pose proof (NN 2%nat 3%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M23.
  pose proof (NN 2%nat 4%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M24.
  pose proof (NN 2%nat 5%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M25.
  pose proof (NN 3%nat 4%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M34.
  pose proof (NN 3%nat 5%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M35.
  pose proof (NN 4%nat 5%nat _ _ eq_refl eq_refl ltac:(discriminate)) as M45.
  clear NN.
  Local Ltac pre_neq := intros e He; cbn [In] in He; repeat (destruct He as [<-|He]; [cbn [fst]; congruence|]); destruct He.
  pose proof (live_remove_one sbuf nsbuf [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape)] [] L
                ltac:(pre_neq) ltac:(intros e []) (NL sbuf nsbuf ltac:(cbn [In]; tauto))) as R. cbn [app] in R. rewrite R. clear R.
  pose proof (live_remove_one tape ntape [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl)] [] L
                ltac:(pre_neq) ltac:(intros e []) (NL tape ntape ltac:(cbn [In]; tauto))) as R. cbn [app] in R. rewrite R. clear R.
  pose proof (live_remove_one ia nia [] [(oc, noc); (idx, nidx); (impl, nimpl)] L
                ltac:(intros e []) ltac:(pre_neq) (NL ia nia ltac:(cbn [In]; tauto))) as R. cbn [app] in R. rewrite R. clear R.
  pose proof (live_remove_one oc noc [] [(idx, nidx); (impl, nimpl)] L
                ltac:(intros e []) ltac:(pre_neq) (NL oc noc ltac:(cbn [In]; tauto))) as R. cbn [app] in R. rewrite R. clear R.
  pose proof (live_remove_one idx nidx [] [(impl, nimpl)] L
                ltac:(intros e []) ltac:(pre_neq) (NL idx nidx ltac:(cbn [In]; tauto))) as R. cbn [app] in R. rewrite R. clear R.
  pose proof (live_remove_one impl nimpl [] [] L
                ltac:(intros e []) ltac:(intros e []) (NL impl nimpl ltac:(cbn [In]; tauto))) as R. cbn [app] in R. rewrite R. reflexivity.
Qed.

End Kit6.
