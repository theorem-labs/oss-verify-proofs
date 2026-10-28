(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec TacX CellsX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsUnwind.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Inductive achain (m : mem) : Z -> list (Z * Z) -> Prop :=
| ach_nil : forall cur, (cur <= aceil \/ cur mod 8 <> 0) -> achain m cur []
| ach_cons : forall cur CH fp ra,
    achain m cur CH -> 0 <= cur < 2^64 -> 0 <= ra < 2^64 ->
    fp mod 16 = 0 -> aceil + 16 <= fp -> fp < 2^64 ->
    rw_cells asegs m (fp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra)] ->
    achain m fp ((fp, ra) :: CH).

(* [comment removed for export] *)
Lemma achain_nil_law : forall m cur, (cur <= aceil \/ cur mod 8 <> 0) -> achain m cur [].
Proof. intros; apply ach_nil; assumption. Qed.

Lemma achain_cons_law : forall m cur CH fp ra, achain m cur CH -> 0 <= cur < 2^64 -> 0 <= ra < 2^64 ->
  fp mod 16 = 0 -> aceil + 16 <= fp -> fp < 2^64 ->
  rw_cells asegs m (fp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra)] -> achain m fp ((fp, ra) :: CH).
Proof. intros; eapply ach_cons; eassumption. Qed.

Lemma achain_range_law : forall m cur CH fp ra, achain m cur CH -> In (fp, ra) CH ->
  aceil + 16 <= fp < 2^64 /\ fp mod 8 = 0 /\ 0 <= ra < 2^64.
Proof.
  intros m cur CH fp ra H. induction H as [cur Hc|cur CH fp' ra' H IH Hcur Hra Hal Hlo Hhi RC]; intros IN; [destruct IN|].
  destruct IN as [E|IN]; [injection E; intros <- <-| apply IH; exact IN].
  split; [lia|]. split; [Z.div_mod_to_equations; nia| lia].
Qed.

Lemma achain_ext_law : forall m m' cur CH, achain m cur CH ->
  (forall fp ra a, In (fp, ra) CH -> fp - 16 <= a < fp -> m' (wa a) = m (wa a)) -> achain m' cur CH.
Proof.
  intros m m' cur CH H. induction H as [cur Hc|cur CH fp ra H IH Hcur Hra Hal Hlo Hhi RC]; intros EQ.
  - apply ach_nil. exact Hc.
  - apply (ach_cons m' cur); try assumption.
    + apply IH. intros fp' ra' a IN Ha. apply (EQ fp' ra'); [right; exact IN| exact Ha].
    + destruct RC as [[WF (B0 & B1 & BB)] (W0 & W1 & WW)]. split; [split; [exact WF|]|].
      * split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd. rewrite (EQ fp ra); [apply BB; exact Hi| left; reflexivity|].
        cbn in Hi. lia.
      * split; [exact W0|]. split; [exact W1|]. intros i Hi.
        pose proof (WW i Hi) as HW. unfold wview in *. rewrite (EQ fp ra); [exact HW| left; reflexivity| cbn in Hi; lia].
Qed.

(* [comment removed for export] *)
Lemma achain_laws : forall H, (forall m cur CH, as_chain H m cur CH <-> achain m cur CH) -> chain_laws H.
Proof.
  intros H E. split; [| split; [| split]].
  - intros m cur Hc. apply (proj2 (E _ _ _)). apply ach_nil. exact Hc.
  - intros m cur CH fp ra C Hcur Hra Hal Hlo Hhi RC. apply (proj2 (E _ _ _)). apply (ach_cons m cur); try assumption. apply (proj1 (E _ _ _)). exact C.
  - intros m m' cur CH C EQ. apply (proj2 (E _ _ _)). eapply achain_ext_law; [apply (proj1 (E _ _ _)); exact C| exact EQ].
  - intros m cur CH fp ra C IN. eapply achain_range_law; [apply (proj1 (E _ _ _)); exact C| exact IN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma upush_neq : forall pc0 ra acc, ra <> pc0 -> upush pc0 ra acc = acc ++ [ra].
Proof. intros pc0 ra acc NE. unfold upush. destruct (Z.eqb_spec ra pc0); [contradiction| reflexivity]. Qed.

Section Bridge.
  Variable top : Z.

  (* [comment removed for export] *)
  Lemma achain_frame_chain_gen : forall m L cur,
    achain m cur L ->
    forall bp ra0,
      rw_cells asegs m (bp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra0)] ->
      aceil <= bp -> 0 <= cur < 2^64 -> 0 <= ra0 < 2^64 ->
      exists CHu, frame_chain asegs m top bp CHu
        /\ forall pc0 md acc, ~ In pc0 (ra0 :: map snd L) ->
             exists j, uloop pc0 md CHu acc = acc ++ firstn j (ra0 :: map snd L).
  Proof.
    intros m L cur H. induction H as [cur Hc|cur L fp ra1 H IH Hcur Hra1 Hal Hlo Hhi RC]; intros bp ra0 REC BP CUR RA0.
    - (* [comment removed for export] *)
      assert (G : goodframe bp cur top = false).
      { unfold goodframe. destruct Hc as [Hc|Hc].
        - destruct (Z.ltb_spec bp cur); [lia| reflexivity].
        - destruct (Z.eqb_spec (cur mod 8) 0); [lia|]. rewrite andb_false_r. reflexivity. }
      exists [(ra0, cur)]. split.
      + apply fc_last; assumption.
      + intros pc0 md acc NI.
        destruct (Z.leb_spec md (Z.of_nat (length acc))).
        { exists 0%nat. rewrite uloop_cut by lia. cbn. rewrite app_nil_r. reflexivity. }
        destruct (Z.ltb_spec ra0 KPAGE).
        { exists 0%nat. rewrite uloop_page by lia. cbn. rewrite app_nil_r. reflexivity. }
        rewrite uloop_last by lia. rewrite upush_neq by (intros K; apply NI; left; exact K).
        exists 1%nat. reflexivity.
    - (* [comment removed for export] *)
      destruct (goodframe bp fp top) eqn:G.
      + destruct (IH fp ra1 RC ltac:(lia) Hcur Hra1) as (CH' & FC' & UL').
        exists ((ra0, fp) :: CH'). split.
        * apply fc_link; try assumption; lia.
        * intros pc0 md acc NI. pose proof (frame_chain_nonnil _ _ _ _ _ FC') as NN.
          destruct CH' as [|x rest]; [congruence|].
          destruct (Z.leb_spec md (Z.of_nat (length acc))).
          { exists 0%nat. rewrite uloop_cut by lia. cbn. rewrite app_nil_r. reflexivity. }
          destruct (Z.ltb_spec ra0 KPAGE).
          { exists 0%nat. rewrite uloop_page by lia. cbn. rewrite app_nil_r. reflexivity. }
          rewrite uloop_link by lia. rewrite upush_neq by (intros K; apply NI; left; exact K).
          destruct (UL' pc0 md (acc ++ [ra0]) ltac:(intros K; apply NI; right; exact K)) as [j E].
          exists (S j). rewrite E, <- app_assoc. reflexivity.
      + exists [(ra0, fp)]. split.
        * apply fc_last; try assumption; lia.
        * intros pc0 md acc NI.
          destruct (Z.leb_spec md (Z.of_nat (length acc))).
          { exists 0%nat. rewrite uloop_cut by lia. cbn. rewrite app_nil_r. reflexivity. }
          destruct (Z.ltb_spec ra0 KPAGE).
          { exists 0%nat. rewrite uloop_page by lia. cbn. rewrite app_nil_r. reflexivity. }
          rewrite uloop_last by lia. rewrite upush_neq by (intros K; apply NI; left; exact K).
          exists 1%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem achain_utrace : forall m bp cur ra0 L,
    achain m cur L ->
    rw_cells asegs m (bp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra0)] ->
    aceil <= bp -> 0 <= cur < 2^64 -> 0 <= ra0 < 2^64 ->
    exists CHu, frame_chain asegs m top bp CHu
      /\ forall pc0 bot md, ~ In pc0 (ra0 :: map snd L) ->
           exists j, (1 <= j)%nat /\ utrace pc0 bp top bot md CHu = firstn j (pc0 :: ra0 :: map snd L).
  Proof.
    intros m bp cur ra0 L C REC BP CUR RA0.
    destruct (achain_frame_chain_gen m L cur C bp ra0 REC BP CUR RA0) as (CHu & FC & UL).
    exists CHu. split; [exact FC|]. intros pc0 bot md NI. unfold utrace.
    destruct (top <? KPAGE); [exists 1%nat; split; [lia| reflexivity]|].
    destruct (goodframe bot bp top); [| exists 1%nat; split; [lia| reflexivity]].
    destruct (UL pc0 md [pc0] NI) as [j E]. exists (S j). split; [lia|]. rewrite E. reflexivity.
  Qed.
End Bridge.

(* [comment removed for export] *)
Lemma trace_ok_utrace : forall TRS pc0 t u j,
  trace_ok TRS pc0 t -> (1 <= j)%nat -> u = firstn j (pc0 :: t) -> In u TRS.
Proof. intros TRS pc0 t u j [_ OK] Hj ->. apply OK. exact Hj. Qed.

Lemma trace_ok_notin : forall TRS pc0 t, trace_ok TRS pc0 t -> ~ In pc0 t.
Proof. intros TRS pc0 t [NI _]. exact NI. Qed.

End HCW.

