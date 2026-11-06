(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvHS3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HS.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Lemma holes_lsopt_of_none : forall h st, holes_lsopt None st -> holes_lsopt h st.
  Proof. intros [n|] st H; [exact (holes_ls_of_opt None n st H (or_introl eq_refl)) | exact H]. Qed.

  Theorem AAINV_HS_weaken : forall h Lc FF B C K M mdl,
    AAINV_HS bt None Lc FF B C K M mdl -> AAINV_HS bt h Lc FF B C K M mdl.
  Proof.
    intros h Lc FF B C K M mdl (st & W & R & [Bd HP] & MW). exists st. split; [exact W|]. split; [exact R|]. split; [| exact MW]. split; [exact Bd|].
    exact (holes_lsopt_of_none h st HP).
  Qed.
End HS.
End AsAinvHS3.
Require Stdlib.NArith.NArith LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvPrist3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prist (S : Z -> Prop) (st : ast) : Prop := forall c, S c -> a_reg st c = region0 /\ a_cache st c = [].
Definition S_all : Z -> Prop := fun _ => True.
Definition S_nb : Z -> Prop := fun c => c <> BATCHCLASS.

Lemma prist_anti : forall (S S' : Z -> Prop) st, (forall c, S' c -> S c) -> prist S st -> prist S' st.
Proof. intros S S' st HS P c Hc. exact (P c (HS c Hc)). Qed.
Lemma prist_ext : forall (S : Z -> Prop) st st',
  (forall c, S c -> a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) -> prist S st -> prist S st'.
Proof. intros S st st' E P c Hc. destruct (E c Hc) as [E1 E2]. destruct (P c Hc) as [P1 P2]. rewrite E1, E2. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ops.
  Variable S : Z -> Prop.
  Ltac pe := intros; eapply prist_ext; [| eassumption]; intros c0 Hc0; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; reflexivity.
  Ltac pec c NS := intros; eapply prist_ext; [| eassumption]; intros c0 Hc0;
    assert (c0 <> c) by (intros E0; subst c0; exact (NS Hc0)); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite ?fupdZ_other by assumption; split; reflexivity.

  Lemma prist_set_cache : forall st c ks, ~ S c -> prist S st -> prist S (set_cache st c ks).
  Proof using. intros st c ks NS. pec c NS. Qed.


  Lemma prist_set_gq : forall st q, prist S st -> prist S (set_gq st q).  Proof using. pe. Qed.




  Lemma prist_add_meter : forall st cost naa shs, prist S st -> prist S (add_meter st cost naa shs).  Proof using. pe. Qed.



  Lemma prist_cache_init : forall st, prist S st -> prist S (op_cache_init st).  Proof using. pe. Qed.






  Lemma prist_sec_free : forall st i, prist S st -> prist S (op_sec_free st i).  Proof using. pe. Qed.




  (* [comment removed for export] *)
  Lemma prist_cache_pop : forall st c, ~ S c -> prist S st -> prist S (op_cache_pop st c).
  Proof using. intros st c NS. pec c NS. Qed.
  Lemma prist_cache_push : forall st c k, ~ S c -> prist S st -> prist S (op_cache_push st c k).
  Proof using. intros st c k NS. pec c NS. Qed.
  Lemma prist_refill : forall st c m, ~ S c -> prist S st -> prist S (op_refill st c m).
  Proof using. intros st c m NS. pec c NS. Qed.

  Lemma prist_usermap : forall st c, ~ S c -> prist S st -> prist S (op_usermap st c).
  Proof using. intros st c NS. pec c NS. Qed.
  Lemma prist_famap : forall st c, ~ S c -> prist S st -> prist S (op_famap st c).
  Proof using. intros st c NS. pec c NS. Qed.
  Lemma prist_carve : forall sb st c, ~ S c -> prist S st -> prist S (op_carve sb st c).
  Proof using. intros sb st c NS. pec c NS. Qed.



  Lemma prist_drain_top : forall st c m, ~ S c -> prist S st -> prist S (op_drain_top st c m).
  Proof using. intros st c m NS. pec c NS. Qed.

  Lemma prist_qbatch_free : forall sb st i, ~ S BATCHCLASS -> prist S st -> prist S (op_qbatch_free sb st i).
  Proof using. intros sb st i NS P. (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end). destruct (nth_error (a_gq st) i); [| exact P]. apply prist_set_cache; [exact NS | apply prist_set_gq, P]. Qed.

  (* [comment removed for export] *)
  Lemma prist_carved : forall bt st c a, 1 <= c <= 30 -> prist S st -> carved bt st c a -> ~ S c.
  Proof using.
    intros bt st c a Hc P (j & Hj & Hle & _) HS. destruct (P c HS) as [E _]. rewrite E in Hle. cbn [r_alloc_user region0] in Hle.
    pose proof (csize_pos c Hc) as ((C1 & _) & _). nia.
  Qed.
End Ops.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cellN_inj : forall SEGS M a (n : nat) v v', (n <= 8)%nat ->
  cellN SEGS M a n v -> cellN SEGS M a n v' -> 0 <= v < 2 ^ (8 * Z.of_nat n) -> 0 <= v' < 2 ^ (8 * Z.of_nat n) -> v = v'.
Proof.
  intros SEGS M a n v v' Hn C C' Hv Hv'. unfold cellN in *. rewrite C in C'. injection C' as E.
  apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_N in E.
  assert (P64 : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite !Mh32.StepTac.u_Z2bv in E by lia. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma cache_max_le16 : forall c, cache_max c <= 16.
Proof. intros c. (lazymatch goal with |- ?G => let G' := eval unfold cache_max, cache_hint in G in change_no_check G' end). generalize (1024 / csize c). intros z. lia. Qed.

Section Det.
  Context {RC : run_ceil}.
  Variable bt : as_boot.

  Lemma rep_class_det : forall st st' Lc FF Lc' FF' qt qg qt' qg' M mdl mdl' c, 1 <= c <= 30 ->
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl -> WFq bt st' Lc' FF' qt' qg' -> Rep bt st' Lc' FF' M mdl' ->
    length (a_cache st' c) = length (a_cache st c)
    /\ length (r_free (a_reg st' c)) = length (r_free (a_reg st c))
    /\ r_alloc_user (a_reg st' c) = r_alloc_user (a_reg st c)
    /\ r_mapped_user (a_reg st' c) = r_mapped_user (a_reg st c)
    /\ r_mapped_fa (a_reg st' c) = r_mapped_fa (a_reg st c).
  Proof using.
    intros st st' Lc FF Lc' FF' qt qg qt' qg' M mdl mdl' c Hc W R W' R'.
    destruct W as ((WR & _) & WC & _). destruct W' as ((WR' & _) & WC' & _).
    destruct (WR c Hc) as ((A1 & _ & A3) & A4 & A5 & _ & A7 & _ & A9 & A10 & _).
    destruct (WR' c Hc) as ((A1' & _ & A3') & A4' & A5' & _ & A7' & _ & A9' & A10' & _).
    destruct (WC c Hc) as (C1 & _). destruct (WC' c Hc) as (C1' & _).
    destruct R as (_ & _ & RT & RR & _). destruct R' as (_ & _ & RT' & RR' & _).
    destruct (RR c Hc) as ((_ & _ & G3 & G4 & G5 & _ & G7 & _) & _). destruct (RR' c Hc) as ((_ & _ & G3' & G4' & G5' & _ & G7' & _) & _).
    destruct RT as (_ & _ & _ & _ & _ & _ & _ & RP & _). destruct RT' as (_ & _ & _ & _ & _ & _ & _ & RP' & _).
    destruct (RP c Hc) as (P1 & _). destruct (RP' c Hc) as (P1' & _).
    pose proof (cache_max_le16 c) as HM.
    unfold AMAX, KREGION_EXHAUST, KUSERMAP in *.
    assert (E1 : Z.of_nat (length (a_cache st' c)) = Z.of_nat (length (a_cache st c))).
    { apply (cellN_inj _ _ _ 4 _ _ ltac:(lia) P1' P1); change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia. }
    assert (E2 : Z.of_nat (length (r_free (a_reg st' c))) = Z.of_nat (length (r_free (a_reg st c)))).
    { apply (cellN_inj _ _ _ 8 _ _ ltac:(lia) G3' G3); change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616; lia. }
    split; [lia|]. split; [lia|].
    split. { apply (cellN_inj _ _ _ 8 _ _ ltac:(lia) G5' G5); change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616; lia. }
    split. { apply (cellN_inj _ _ _ 8 _ _ ltac:(lia) G7' G7); change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616; lia. }
    apply (cellN_inj _ _ _ 8 _ _ ltac:(lia) G4' G4); change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition HP_q (Q : ast -> Prop) (h : option Z) : ast -> Prop :=
    match h with None => fun st => holes_lsopt None st /\ Q st | Some n => holes_lsopt (Some n) end.
  (* [comment removed for export] *)
  Definition AAINV_QX (Q : ast -> Prop) (h : option Z) := AAINVP (HP_q Q h) bt.

  Lemma HP_q_hint : forall Q, (forall st k v, Q st -> Q (set_hint st k v)) -> forall h st k v, HP_q Q h st -> HP_q Q h (set_hint st k v).
  Proof using. intros Q HQ [n|] st k v H; [exact H | destruct H as [H1 H2]; split; [exact H1 | exact (HQ st k v H2)]]. Qed.
  Lemma AAINV_QX_props : forall Q h, AAINV_props (bt_ia bt) (AAINV_QX Q h) (bt_fs bt) (bt_segs bt).
  Proof using. intros Q h. exact (AAINV_props_all bt (HP_q Q h)). Qed.
  Lemma AAINV_QX_HS : forall Q Lc FF B C K M mdl, AAINV_QX Q None Lc FF B C K M mdl -> AAINV_HS bt None Lc FF B C K M mdl.
  Proof using. intros Q Lc FF B C K M mdl (st & W & R & (Bd & HL & _) & MW). exists st. split; [exact W|]. split; [exact R|]. split; [split; [exact Bd | exact HL] | exact MW]. Qed.



  (* [comment removed for export] *)
  Definition HP_pr (S : Z -> Prop) : option Z -> ast -> Prop := HP_q (prist S).
  Definition AAINV_PR (S : Z -> Prop) := AAINVP (HP_pr S None) bt.









  (* [comment removed for export] *)
  Definition fresh_prim (n : Z) (st : ast) : Prop :=
    let c := class_of (needed n) in
    a_cache st c = []
    /\ Z.of_nat (length (r_free (a_reg st c))) < cache_hint c
    /\ r_mapped_user (a_reg st c) < r_alloc_user (a_reg st c) + csize c * (cache_hint c - Z.of_nat (length (r_free (a_reg st c)))).
  (* [comment removed for export] *)
  Definition FRESH_bt (Lc FF : list (Z * Z)) (B C K : Z) (M : mem) (mdl : Model) (n : Z) : Prop :=
    64512 < n \/ (n <= 64512 /\ forall st mdl0, WF bt st Lc FF -> Rep bt st Lc FF M mdl0 -> fresh_prim n st).

  Lemma FRESH_sbm : forall Lc FF B C K M mdl mdl1 n, FRESH_bt Lc FF B C K M mdl n -> same_but_materialized mdl mdl1 -> FRESH_bt Lc FF B C K M mdl1 n.
  Proof using. intros Lc FF B C K M mdl mdl1 n F _. exact F. Qed.


  (* [comment removed for export] *)
  Lemma FRESH_at : forall Lc FF B C K M mdl n st, FRESH_bt Lc FF B C K M mdl n -> WF bt st Lc FF -> Rep bt st Lc FF M mdl ->
    64512 < n \/ (n <= 64512 /\ fresh_prim n st).
  Proof using. intros Lc FF B C K M mdl n st [F | [Hn F]] W R; [left; exact F | right; split; [exact Hn | exact (F st mdl W R)]]. Qed.

  Lemma prist_fresh_prim : forall S st n, 1 <= n <= 64512 -> prist S st -> S (class_of (needed n)) -> fresh_prim n st.
  Proof using.
    intros S st n Hn P HS. destruct (P _ HS) as [E1 E2]. (lazymatch goal with |- ?G => let G' := eval unfold fresh_prim in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_user r_alloc_user region0 length Z.of_nat] in G in change_no_check G' end).
    assert (HP : is_primary n = true) by (apply is_primary_iff; lia). unfold is_primary in HP. apply Z.leb_le in HP.
    pose proof (rounded_ge n) as (R1 & R2 & _). pose proof (rz_range n) as RZ.
    assert (Hc : 1 <= class_of (needed n) <= 30) by (apply class_of_range; unfold needed in *; lia).
    pose proof (csize_pos _ Hc) as ((C1 & _) & _).
    assert (HH : 1 <= cache_hint (class_of (needed n))) by ((lazymatch goal with |- ?G => let G' := eval unfold cache_hint in G in change_no_check G' end); lia).
    split; [reflexivity|]. split; [lia|]. nia.
  Qed.

  (* [comment removed for export] *)
  Theorem FRESH_of_PR : forall S Lc FF B C K M mdl n, 1 <= n ->
    AAINV_PR S Lc FF B C K M mdl -> (n <= 64512 -> S (class_of (needed n))) -> FRESH_bt Lc FF B C K M mdl n.
  Proof using.
    intros S Lc FF B C K M mdl n Hn (st & W & R & (_ & _ & P) & _) HS.
    destruct (Z_lt_le_dec 64512 n) as [Hb | Hs]; [left; exact Hb | right; split; [exact Hs|]].
    intros st' mdl0 W' R'.
    pose proof (prist_fresh_prim S st n ltac:(lia) P (HS Hs)) as (F1 & F2 & F3).
    assert (HP : is_primary n = true) by (apply is_primary_iff; lia). unfold is_primary in HP. apply Z.leb_le in HP.
    pose proof (rounded_ge n) as (R1 & R2 & _). pose proof (rz_range n) as RZ.
    assert (Hc : 1 <= class_of (needed n) <= 30) by (apply class_of_range; unfold needed in *; lia).
    destruct (rep_class_det st st' Lc FF Lc FF _ _ _ _ M mdl mdl0 _ Hc W R W' R') as (D1 & D2 & D3 & D4 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold fresh_prim in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite F1 in D1. cbn [length] in D1.
    split; [destruct (a_cache st' (class_of (needed n))); [reflexivity | discriminate D1]|].
    rewrite D2, D3, D4. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma class_nb : forall n, 8193 <= n <= 64512 -> class_of (needed n) <> BATCHCLASS.
  Proof using.
    intros n Hn. pose proof (rounded_ge n) as (R1 & _). pose proof (rz_range n) as RZ.
    assert (H : 8192 < needed n) by ((lazymatch goal with |- ?G => let G' := eval unfold needed in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold class_of, BATCHCLASS in G in change_no_check G' end).
    repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end; lia.
  Qed.







  (* [comment removed for export] *)
  Lemma prist_live : forall S st Lc FF qt qg p n, WFq bt st Lc FF qt qg -> prist S st -> In (p, n) Lc -> is_primary n = true -> ~ S (blk_class n).
  Proof using.
    intros S st Lc FF qt qg p n W P Hin HP. destruct W as (_ & _ & _ & _ & (WL & _) & _).
    destruct (WL p n Hin) as (Hn & _ & _ & CV). specialize (CV HP).
    assert (HP' : needed n <= 65536) by (unfold is_primary in HP; apply Z.leb_le in HP; exact HP).
    pose proof (rounded_ge n) as (R1 & R2 & _). pose proof (rz_range n) as RZ.
    assert (Hc : 1 <= blk_class n <= 30) by (apply class_of_range; unfold needed in *; lia).
    exact (prist_carved S bt st _ _ Hc P CV).
  Qed.


End Det.
End AsAinvPrist3.
Module AsAinvDrvHist3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b AsAinvPrist3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DrvHist.
  Context {RC : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition drv_hist (st : ast) : Prop :=
    prist S_nb st
    /\ (a_kact st <= EVT -> prist S_all st)
    /\ (a_sec st <> [] -> EVT <= a_kact st).
  Lemma evt_ge : 1024 <= EVT.  Proof. (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end). lia. Qed.     (* [comment removed for export] *)
  Definition AAINV_DR := AAINV_QX bt drv_hist None.
  (* [comment removed for export] *)
  Definition AAINV_DRX := AAINV_QX bt drv_hist.

  Lemma drv_hist_hint : forall st k v, drv_hist st -> drv_hist (set_hint st k v).
  Proof. intros st k v H. exact H. Qed.
  Lemma prist_all_drv : forall st, prist S_all st -> a_sec st = [] -> drv_hist st.
  Proof.
    intros st P HS. split; [apply (prist_anti S_all S_nb); [intros; exact I | exact P]|]. split; [intros _; exact P|].
    intros NE. exfalso. exact (NE HS).
  Qed.
  (* [comment removed for export] *)
  Theorem AAINV_DR_main : forall M mdl, boot_ok bt -> main_facts bt M mdl -> AAINV_DR [] [] 0 0 0 M mdl.
  Proof.
    intros M mdl BOK EF. apply (AAINVP_main bt BOK M mdl EF). split.
    - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros c [R|R]; cbn [a_reg st0 r_uhole r_fhole region0] in R; discriminate R.
    - apply prist_all_drv; [intros c _; split; reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma drv_hist_malloc_sec : forall st st' n, drv_hist st -> 64512 < n -> 0 <= a_kact st ->
    (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) -> a_kact st + kcost_malloc n <= a_kact st' -> drv_hist st'.
  Proof.
    intros st st' n (H1 & H2 & H3) Hn K0 AG KC. unfold kcost_malloc in KC. (lazymatch goal with |- ?G => let G' := eval unfold drv_hist in G in change_no_check G' end). pose proof evt_ge as EG.
    split; [exact (prist_ext S_nb st st' (fun c _ => AG c) H1)|].
    split; [intros HK; exact (prist_ext S_all st st' (fun c _ => AG c) (H2 ltac:(lia))) | intros _; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma drv_hist_same : forall st st', drv_hist st ->
    (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) -> a_kact st <= a_kact st' -> (a_sec st' <> [] -> a_sec st <> []) -> drv_hist st'.
  Proof.
    intros st st' (H1 & H2 & H3) AG KC SEC.
    split; [exact (prist_ext S_nb st st' (fun c _ => AG c) H1)|].
    split; [intros HK; exact (prist_ext S_all st st' (fun c _ => AG c) (H2 ltac:(lia))) | intros NE; pose proof (H3 (SEC NE)); lia].
  Qed.


  (* [comment removed for export] *)
  Theorem FRESH_PAY : forall Lc FF B C K M mdl n, 1 <= n -> AAINV_DR Lc FF B C K M mdl -> K <= EVT \/ 8193 <= n ->   (* [comment removed for export] *)
    FRESH_bt bt Lc FF B C K M mdl n.
  Proof.
    intros Lc FF B C K M mdl n Hn A HC. destruct A as (st & W & R & ((Bd1 & Bd2 & Bd3) & HL & (H1 & H2 & H3)) & MW).
    destruct HC as [HK | HB].
    - apply (FRESH_of_PR bt S_all); [exact Hn | | intros _; exact I].
      exists st. split; [exact W|]. split; [exact R|]. split; [| exact MW]. split; [exact (conj Bd1 (conj Bd2 Bd3))|]. split; [exact HL | apply H2; lia].
    - apply (FRESH_of_PR bt S_nb); [exact Hn | | intros Hs; apply class_nb; lia].
      exists st. split; [exact W|]. split; [exact R|]. split; [| exact MW]. split; [exact (conj Bd1 (conj Bd2 Bd3))|]. split; [exact HL | exact H1].
  Qed.
End DrvHist.
End AsAinvDrvHist3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsCI3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section CI.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition foot_cache_init (a : Z) : Prop :=
    (exists i, 1 <= i <= 31 /\ T + T_PC + PC_SZ * i + 4 <= a < T + T_PC + PC_SZ * i + 16) \/ CEIL <= a.

  Definition OPS_REP_cache_init : Prop := forall st Lc FF (M M' : mem) mdl mdl',
    WF bt st Lc FF -> Rep bt st Lc FF M mdl ->
    agrees_off foot_cache_init M M' ->
    (forall i, 1 <= i <= 30 -> cellZ SG M' (T + T_PC + PC_SZ * i + 4) 4 (cache_max i) /\ cellZ SG M' (T + T_PC + PC_SZ * i + 8) 8 (csize i)) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_cache_init st) Lc FF M' mdl'.

  (* [comment removed for export] *)
  Lemma pc_off : forall c i, T + T_PC + PC_SZ * c <= i < T + T_PC + PC_SZ * c + PC_SZ -> (i - (T + T_PC)) mod PC_SZ = i - (T + T_PC + PC_SZ * c).
  Proof.
    intros c i Hi. unfold PC_SZ in *. replace (i - (T + T_PC)) with ((i - (T + T_PC + 80 * c)) + c * 80) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  Theorem OPS_REP_cache_init_pf : OPS_REP_cache_init.
  Proof.
    intros st Lc FF M M' mdl mdl' W R AGR CPC SBM MI.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & TPB).
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    box TPI. box TPB. box TPG.
    (* [comment removed for export] *)
    set (PIN := fun i : Z => T + T_PC + PC_SZ <= i < T + T_PC + PC_SZ * 31 /\ 4 <= (i - (T + T_PC)) mod PC_SZ < 16).
    set (Mmid := fun a : word => if decide (PIN (u a)) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R). intros a NEa. unfold Mmid in NEa |- *.
      destruct (decide (PIN (u a))) as [IN|NI]; [exfalso; exact (NEa eq_refl)|].
      destruct (AGR a NEa) as [Hf Hd]. split; [| exact Hd].
      intros HC. unfold foot_cache_init in Hf. unfold PIN in NI.
      destruct Hf as [(c & Hc & Hf)|Hf].
      - destruct (Z.eq_dec c 31) as [-> | NE31].
        + apply (tjunk_not_cells bt st Lc FF W (u a)); [| exact HC]. clear -Hf. unfold T_PC, PC_SZ in *. lia.
        + apply NI. rewrite (pc_off c (u a)) by (clear -Hf Hc; unfold PC_SZ in *; lia). clear -Hf Hc NE31. unfold PC_SZ in *. lia.
      - exact (ceil_not_cells bt st Lc FF W (u a) Hf HC). }
    (* [comment removed for export] *)
    assert (AG : forall i, ~ PIN i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (decide (PIN i)) as [IN|NI]; [exfalso; exact (Hi IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NEa. unfold Mmid in NEa. destruct (decide (PIN (u a))) as [IN|NI]; [| exfalso; exact (NEa eq_refl)]. exact (proj2 (AGR a NEa)). }
    assert (NTP : forall i, ~ (T + T_PC + PC_SZ <= i < T + T_PC + PC_SZ * 31) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X _]. exact (Hi X). }
    assert (OUTT : forall i, ~ (T <= i < T + PG) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply NTP; [| exact Hr]. clear -Hi. unfold T_PC, PC_SZ, PG in *. lia. }
    assert (IMGR : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi. apply OUTT; [clear -Hi TPI; Zlia | clear -Hi I1 I2; ulia]. }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGR i Hi). }
    assert (FIXR : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG ->
                   forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin Hpg i Hi Hr. apply OUTT; [| exact Hr].
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D.
      clear -Hi D. ulia. }
    assert (DYNR : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi Hr. apply OUTT; [| exact Hr].
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hin) as D. hnf in D. cbn in D. clear -Hi D. ulia. }
    assert (SPCR : forall i, SBEG <= i < SBEG + KSPACE + PG -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply OUTT; [clear -Hi TPG; Zlia | exact Hr]. }
    assert (BANDR : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply OUTT; [clear -Hi TPB; Zlia | exact Hr]. }
    assert (HDRR : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
      - apply SPCR; [clear -W1 W2 W3 W4 N1'; ulia | exact Hr].
      - apply (DYNR _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. ulia. }
    assert (BA : forall q, (forall b0, In b0 q -> In b0 (a_tq st ++ a_gq st)) -> rep_batches bt Mmid q -> rep_batches bt M' q).
    { intros q SUB RB. eapply rep_batches_frame; [exact DEF | exact RB | intros b0 Hb0; exact (BR b0 (SUB b0 Hb0)) |].
      intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 (SUB b0 Hb0)) as (_ & BL1 & BL2 & BL3).
      apply SPCR; [clear -Hi BL1 BL2 BL3; ulia | exact Hr]. }
    clear WR2 WQ S2 S4 S5 S6 S7 S8 LV1 LV3 WK WD WM' RNG PW' R6a R6b IN6 G.
    set (st' := op_cache_init st).
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in YC. destruct (YC c0 Hc0).
             exact (IMGK i (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) ltac:(lia)). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact P2 | uilia | uilia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXR _ _ IN8); [ulia | clear -IN S1 S3; lia | exact Hr].
             - exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) Hr). }
    (* [comment removed for export] *)
    split. { destruct P3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st). change (a_cinit st') with true. change (a_cache st') with (a_cache st).
             assert (AGC : forall i, bt_tctx bt <= i < bt_tctx bt + 160 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros i Hi Hr. apply (FIXR _ _ INC); [ulia | clear -Hi; lia | exact Hr]. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ NTP T1|]. split; [frZ NTP T2|]. split; [frZ NTP T3|]. split; [frB NTP T4|]. split; [frZ NTP T5|]. split; [frB NTP T6|].
             split. { eapply rep_list_frame; [exact TL | lia | lia |]. intros i Hi Hr. apply NTP; [clear -Hi; lia | exact Hr]. }
             split. { intros c Hc. destruct (TP c Hc) as (Q1 & Q2 & Q3 & Q4). destruct (CPC c Hc) as [N4 N8]. pose proof (cache_len bt st Lc FF W c Hc) as CL.
                      unfold T_PC, PC_SZ in Q1, Q2, Q3, Q4, N4, N8.
                      assert (AGc : forall i, T + 208 + 80 * c <= i < T + 208 + 80 * c + 80 -> ~ (4 <= i - (T + 208 + 80 * c) < 16) -> 0 <= i < 2 ^ 64 ->
                                    M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
                      { intros i Hi Hn Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros [_ X].
                        pose proof (pc_off c i) as E. unfold T_PC, PC_SZ in E. rewrite E in X by (clear -Hi; lia). exact (Hn X). }
                      (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass in G in change_no_check G' end). cbn zeta. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). split; [| split; [exact N4 | split; [exact N8 |]]].
                      - eapply (cellZ_frame _ _ _ _ _ _ Q1); [lia | lia |]. intros i Hi. apply AGc; [clear -Hi; cbn in Hi; lia | clear -Hi; cbn in Hi; lia | lia].
                      - intros j k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. pose proof (Q4 j k Hk) as C.
                        eapply (cellZ_frame _ _ _ _ _ _ C); [lia | lia |]. intros i Hi. apply AGc; [clear -Hi Hl CL; cbn in Hi; lia | clear -Hi Hl CL; cbn in Hi; lia | lia]. }
             split; [frW DEF TW|]. split; [frZ AGC TC1|]. split; [frZ AGC TC2|]. split; [frZ NTP TC3 | frZ NTP TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi].
             - apply SPCR; [clear -Hi E9 E10; ulia | exact Hr].
             - apply SPCR; [clear -Hi E1 E2 E5 E6 E7 E8; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split; [change (a_tq st') with (a_tq st); apply BA; [intros b0 Hb0; apply in_app_iff; left; exact Hb0 | exact P5]|].
    split; [change (a_gq st') with (a_gq st); apply BA; [intros b0 Hb0; apply in_app_iff; right; exact Hb0 | exact P6]|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact P7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNR _ _ (sec_dyn st sc Hs)); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { change (rep_headers bt st' Lc M') with (rep_headers bt st Lc M'). destruct P8 as [HLh HQh]. split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros i Hi Hr. exact (HDRR p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRR (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear -Hi Hbk Eb; rewrite Eb; lia | exact Hr].
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hi Hbk; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear -Hi; ulia | exact Hr].
               + exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) Hr).
               + apply OUTT; [| exact Hr]. pose proof (dtls_vs_thread bt st Lc FF W) as DV. clear -Hi DV. ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear -Hi A1 A2 A4; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st). change (quar st') with (quar st).
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1 B6 B7. Zlia. }
             split. { intros c0 g Hc0 Hg NL'. pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs HQ HU. pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep Mmid M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { change (rep_ledger bt st mdl'). exact (rep_ledger_sbm bt st mdl mdl' SBM P13). }
    (* [comment removed for export] *)
    split. { destruct P14 as (BU1 & BU2 & BU3 & BU4 & BU5 & BU6 & BU7 & BU8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st).
             change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
             split; [exact BU1|]. split; [exact MI|]. split; [exact BU3|]. split; [exact BU4|]. split; [exact BU5|]. split; [exact BU6|]. split; [exact BU7|].
             rewrite E3. change (prim_charge st') with (prim_charge st). change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st). exact BU8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia)) ltac:(ulia))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia)) ltac:(ulia))] |].
    exact (rep_last_keep bt _ _ Mmid M' DEF P19 (fun H => H)).
  Qed.
End CI.
End AsAinvOpsCI3.
Module AsAinvXTrk3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section XTrk.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  #[local] Abbreviation T := (bt_thread bt).

  Definition xtracked (a : Z) : Prop :=
    CEIL <= a \/ exists lo hi, In (lo, hi) (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                               /\ lo <= a < hi /\ lo <> bt_nodes0 bt /\ lo <> bt_store0 bt.

  Lemma xtracked_stack : forall a, CEIL <= a -> xtracked a.
  Proof. intros a H. left. exact H. Qed.

  (* [comment removed for export] *)
  Lemma fixed_not_depot : forall lo hi a, In (lo, hi) (bt_fixed bt) -> lo <= a < hi -> hi - lo <> 2 ^ 20 -> hi - lo <> 2 ^ 23 \/ (lo, hi) = (bt_ptrarr bt, bt_ptrarr bt + 2 ^ 23) ->
    lo <> bt_nodes0 bt /\ lo <> bt_store0 bt.
  Proof.
    intros lo hi a Hin Ha N20 N23.
    destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & INN & INS & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PS8 & _) & _).
    split; intros E.
    - assert (NE : (lo, hi) <> (bt_nodes0 bt, bt_nodes0 bt + 2 ^ 20)) by (intros E2; injection E2 as _ E3; lia).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INN) NE) as D. hnf in D. cbn in D. lia.
    - destruct N23 as [N23 | E8].
      + assert (NE : (lo, hi) <> (bt_store0 bt, bt_store0 bt + 2 ^ 23)) by (intros E2; injection E2 as _ E3; lia).
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INS) NE) as D. hnf in D. cbn in D. lia.
      + injection E8 as E9 _. lia.
  Qed.

  Lemma xtracked_fixed : forall lo hi a, In (lo, hi) (bt_fixed bt) -> lo <= a < hi -> hi - lo <> 2 ^ 20 -> hi - lo <> 2 ^ 23 \/ (lo, hi) = (bt_ptrarr bt, bt_ptrarr bt + 2 ^ 23) -> xtracked a.
  Proof.
    intros lo hi a Hin Ha N20 N23. destruct (fixed_not_depot lo hi a Hin Ha N20 N23) as [A B].
    right. exists lo, hi. split; [apply in_or_app; left; exact Hin|]. split; [exact Ha | split; assumption].
  Qed.

  Lemma xtracked_thread : forall a, T <= a < T + PG -> xtracked a.
  Proof.
    intros a Ha. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
    apply (xtracked_fixed _ _ a INT Ha); (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); [lia | left; lia].
  Qed.



  Lemma xtracked_resv6 : forall a, bt_resv6 bt <= a < bt_resv6 bt + bt_resv6_len bt -> xtracked a.
  Proof.
    intros a Ha. destruct (fixed_members bt st Lc FF W) as (IN6 & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & R6a & R6b & _) & _).
    apply (xtracked_fixed _ _ a IN6 Ha); unfold KSPACE, PG in *; [lia | left; lia].
  Qed.
  Lemma xtracked_space : forall a, bt_spacebeg bt <= a < bt_spacebeg bt + KSPACE + PG -> xtracked a.
  Proof.
    intros a Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & R6a & R6b & _) & _). apply xtracked_resv6. lia.
  Qed.

  Lemma xtracked_sec : forall s a, In s (a_sec st) -> sc_map s <= a < sc_map s + sc_mapsz s -> xtracked a.
  Proof.
    intros s a Hs Ha. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & INN & INS & _).
    assert (Hd : In (sc_map s, sc_map s + sc_mapsz s) (dyn_ranges st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_or_app. left. apply in_map_iff. exists s. split; [reflexivity | exact Hs]. }
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INN)) as (_ & LN & _). destruct (RNG _ _ (all_ranges_fixed bt st _ INS)) as (_ & LS & _).
    right. exists (sc_map s), (sc_map s + sc_mapsz s). split; [apply in_or_app; right; apply in_map_iff; exists s; split; [reflexivity | exact Hs]|].
    destruct (RNG _ _ (all_ranges_dyn bt st _ Hd)) as (_ & LD & _).
    split; [exact Ha|]. split; intros E.
    - pose proof (fixed_dyn_sep bt st Lc FF W _ _ _ _ INN Hd) as D. lia.
    - pose proof (fixed_dyn_sep bt st Lc FF W _ _ _ _ INS Hd) as D. lia.
  Qed.

End XTrk.
End AsAinvXTrk3.
Module AsAllocFKeep0.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 AsAinvPrist3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition free_keeps (st st' : ast) : Prop :=
  (forall S : Z -> Prop, ~ S BATCHCLASS -> prist S st -> prist S st') /\ (forall s, In s (a_sec st') -> In s (a_sec st)).

Lemma fk_refl : forall st, free_keeps st st.
Proof. intros st. split; [intros S _ P; exact P | intros s H; exact H]. Qed.
Lemma fk_trans : forall st1 st2 st3, free_keeps st1 st2 -> free_keeps st2 st3 -> free_keeps st1 st3.
Proof. intros st1 st2 st3 [A1 A2] [B1 B2]. split; [intros S NS P; exact (B1 S NS (A1 S NS P)) | intros s H; exact (A2 s (B2 s H))]. Qed.

(* [comment removed for export] *)
Definition touchable (bt : as_boot) (st : ast) (c : Z) : Prop := c = BATCHCLASS \/ (1 <= c <= 30 /\ exists a, carved bt st c a).
Lemma touchable_notS : forall bt st c (S : Z -> Prop), touchable bt st c -> ~ S BATCHCLASS -> prist S st -> ~ S c.
Proof. intros bt st c S [-> | (Hc & a & CV)] NS P; [exact NS | exact (prist_carved S bt st c a Hc P CV)]. Qed.

(* [comment removed for export] *)
Lemma fk_of_ext : forall st st', (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) -> a_sec st' = a_sec st -> free_keeps st st'.
Proof. intros st st' AG ES. split; [intros S _ P; exact (prist_ext S st st' (fun c _ => AG c) P) | intros s H; rewrite <- ES; exact H]. Qed.


Lemma fk_set_tq : forall st q, free_keeps st (set_tq st q).
Proof. intros. apply fk_of_ext; [intros c; split; reflexivity | reflexivity]. Qed.
Lemma fk_set_gq : forall st q, free_keeps st (set_gq st q).
Proof. intros. apply fk_of_ext; [intros c; split; reflexivity | reflexivity]. Qed.
Lemma fk_quar_append : forall st m n, free_keeps st (op_quar_append st m n).
Proof. intros st m n. (lazymatch goal with |- ?G => let G' := eval unfold op_quar_append in G in change_no_check G' end). destruct (rev (a_tq st)); [apply fk_refl | apply fk_set_tq]. Qed.
Lemma fk_quar_newbatch : forall st ba m n, free_keeps st (op_quar_newbatch st ba m n).
Proof. intros. apply fk_set_tq. Qed.
Lemma fk_drain : forall st, free_keeps st (op_drain st).
Proof. intros. apply fk_of_ext; [intros c; split; reflexivity | reflexivity]. Qed.
Lemma fk_qitem : forall st, free_keeps st (op_qitem st).
Proof. intros st. (lazymatch goal with |- ?G => let G' := eval unfold op_qitem in G in change_no_check G' end). destruct (a_gq st) as [|[ba [|it its]] rest]; try apply fk_refl. apply fk_set_gq. Qed.

(* [comment removed for export] *)
Lemma fk_cache_pop : forall bt st c, touchable bt st c -> free_keeps st (op_cache_pop st c).
Proof. intros bt st c TC. split; [intros S NS P; exact (prist_cache_pop S st c (touchable_notS bt st c S TC NS P) P) | intros s H; exact H]. Qed.
Lemma fk_cache_push : forall bt st c k, touchable bt st c -> free_keeps st (op_cache_push st c k).
Proof. intros bt st c k TC. split; [intros S NS P; exact (prist_cache_push S st c k (touchable_notS bt st c S TC NS P) P) | intros s H; exact H]. Qed.
Lemma fk_drain_top : forall bt st c m, touchable bt st c -> free_keeps st (op_drain_top st c m).
Proof. intros bt st c m TC. split; [intros S NS P; exact (prist_drain_top S st c m (touchable_notS bt st c S TC NS P) P) | intros s H; exact H]. Qed.
Lemma fk_qbatch_free : forall sb st i, free_keeps st (op_qbatch_free sb st i).
Proof. intros sb st i. split; [intros S NS P; exact (prist_qbatch_free S sb st i NS P)|]. intros s H. unfold op_qbatch_free in H. destruct (nth_error (a_gq st) i); exact H. Qed.

Lemma fk_firstn_In : forall {A} (l : list A) k x, In x (firstn k l) -> In x l.
Proof. intros A l k x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.
Lemma fk_skipn_In : forall {A} (l : list A) k x, In x (skipn k l) -> In x l.
Proof. intros A l k x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.
(* [comment removed for export] *)
Lemma swap_remove_in : forall {A} (l : list A) i x, In x (swap_remove l i) -> In x l.
Proof.
  intros A l i x H. unfold swap_remove in H. destruct (rev l) as [|lst r] eqn:ER; [exact H|]. cbv zeta in H.
  assert (EL : l = rev r ++ [lst]) by (rewrite <- (rev_involutive l), ER; reflexivity).
  rewrite EL. apply in_app_iff. destruct (Nat.ltb i (length (rev r))).
  - apply in_app_iff in H. destruct H as [H | H]; [left; exact (fk_firstn_In _ _ _ H)|].
    cbn [app] in H. destruct H as [<- | H]; [right; left; reflexivity | left; exact (fk_skipn_In _ _ _ H)].
  - left. exact H.
Qed.
Lemma fk_sec_free : forall st i, free_keeps st (op_sec_free st i).
Proof. intros st i. split; [intros S _ P; exact (prist_sec_free S st i P) | intros s H; exact (swap_remove_in (a_sec st) i s H)]. Qed.
Lemma fk_recycle_sec : forall st i, free_keeps st (op_recycle_sec st i).
Proof. intros st i. (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec in G in change_no_check G' end). exact (fk_trans _ _ _ (fk_qitem st) (fk_sec_free (op_qitem st) i)). Qed.
Lemma fk_recycle_prim : forall bt st c k, touchable bt (op_qitem st) c -> free_keeps st (op_recycle_prim st c k).
Proof. intros bt st c k TC. (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim in G in change_no_check G' end). exact (fk_trans _ _ _ (fk_qitem st) (fk_cache_push bt (op_qitem st) c k TC)). Qed.
(* [comment removed for export] *)
Lemma touchable_alloc : forall bt st st' c, (forall c0, r_alloc_user (a_reg st' c0) = r_alloc_user (a_reg st c0)) -> touchable bt st c -> touchable bt st' c.
Proof.
  intros bt st st' c E [-> | (Hc & a & (j & J1 & J2 & J3))]; [left; reflexivity | right]. split; [exact Hc|].
  exists a, j. rewrite (E c). repeat split; assumption.
Qed.
Lemma touchable_reg : forall bt st st' c, (forall c0, a_reg st' c0 = a_reg st c0) -> touchable bt st c -> touchable bt st' c.
Proof. intros bt st st' c E. apply touchable_alloc. intros c0. rewrite (E c0). reflexivity. Qed.
Lemma alloc_drain_top : forall st c m c0, r_alloc_user (a_reg (op_drain_top st c m) c0) = r_alloc_user (a_reg st c0).
Proof.
  intros st c m c0. (lazymatch goal with |- ?G => let G' := eval unfold op_drain_top in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_cache set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
  destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity.
Qed.
Lemma a_reg_qitem : forall st c0, a_reg (op_qitem st) c0 = a_reg st c0.
Proof. intros st c0. (lazymatch goal with |- ?G => let G' := eval unfold op_qitem in G in change_no_check G' end). destruct (a_gq st) as [|[ba [|it its]] rest]; reflexivity. Qed.
(* [comment removed for export] *)
Lemma fk_recycle_prim_at : forall bt st c k, touchable bt st c -> free_keeps st (op_recycle_prim st c k).
Proof. intros bt st c k TC. apply (fk_recycle_prim bt). exact (touchable_reg bt st (op_qitem st) c (a_reg_qitem st) TC). Qed.
Lemma touchable_carved : forall bt st c a, 1 <= c <= 30 -> carved bt st c a -> touchable bt st c.
Proof. intros bt st c a Hc CV. right. split; [exact Hc | exists a; exact CV]. Qed.
End AsAllocFKeep0.
Require Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRcG.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RcG.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Section W.
    Variables (st : ast) (Lc FF : list (Z * Z)).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.

    (* [comment removed for export] *)
    Lemma quar_chunk_vs_live : forall m n p' n' lo hi, In (m, n) (quar st) -> is_primary n = true -> In (p', n') Lc -> ext bt st Lc p' n' lo hi ->
      prim_alloc_beg (m + 16) n + csize (blk_class n) <= lo \/ hi <= prim_alloc_beg (m + 16) n.
    Proof using W qg qt FF RUN.
      intros m n p' n' lo hi Hq HP Hin E.
      pose proof (quar_chunk bt st Lc FF W m n Hq HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
      destruct E as [(HP' & -> & -> & CV' & HC' & LIV' & S1 & S2) | (HP' & sc & Hs & Eu & En & -> & ->)].
      - destruct (chunk_cases bt st Lc FF W _ _ _ _ G1 HC' G2 CV') as [[EC EA] | D]; [| clear - D; lia].
        exfalso. destruct W as ((WR & _) & _). destruct (WR _ G1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & LQ & _).
        apply (LQ (prim_alloc_beg (m + 16) n)). split; [rewrite EC, EA; exact LIV' | exact G3].
      - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
    Qed.

    Lemma quar_prim_private : forall m n a, In (m, n) (quar st) -> is_primary n = true ->
      prim_alloc_beg (m + 16) n <= a < prim_alloc_beg (m + 16) n + csize (blk_class n) -> rt_priv IA Lc FF a.
    Proof using W qg qt.
      intros m n a Hq HP Ha.
      pose proof (quar_chunk bt st Lc FF W m n Hq HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). pose proof (img_lits bt st Lc FF W) as [I1 I2].
      split; [clear - Ha C4 SP8 SP3; ulia|]. split; [clear - Ha C3 SP7 SPH I2; ulia|].
      destruct (heap_not_shadowish bt st Lc FF W Lc a ltac:(intros p0 n0 H0; exact H0) ltac:(right; clear - Ha C3 SP7 SPH; lia)) as (N1 & N2 & N3 & N4).
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      - destruct V as (p' & n' & Hin & Hpa). destruct (live_ext bt st Lc FF W p' n' Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n' ltac:(lia)) as (U1 & _).
        destruct (quar_chunk_vs_live m n p' n' lo hi Hq HP Hin E) as [D | D]; clear - D Ha Hpa Y1 Y2 U1 Y8; lia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & _) & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)); ulia.
    Qed.

    Lemma quar_prim_shadow_private : forall m n a, In (m, n) (quar st) -> is_primary n = true ->
      sh_lo (m + 16) <= a < sh_hi (m + 16) n -> rt_priv IA Lc FF a.
    Proof using W qg qt.
      intros m n a Hq HP Ha.
      pose proof (quar_chunk bt st Lc FF W m n Hq HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5). pose proof (csize_pos _ G1) as ((S1 & S2) & S3).
      destruct (quar_item_range bt st Lc FF W m n Hq) as (Q1 & Q2 & Q3). pose proof (rz_mod16 n) as RM.
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). pose proof (img_lits bt st Lc FF W) as [I1 I2].
      set (ab := prim_alloc_beg (m + 16) n) in *. set (cs := csize (blk_class n)) in *.
      (* [comment removed for export] *)
      assert (GR : ab <= 8 * (a - SB) /\ 8 * (a - SB) + 8 <= ab + cs /\ AS_LO <= a < AS_HEAPLO).
      { unfold sh_lo, sh_hi in Ha. clear - Ha G4 G5 G6 C5 S3 RM C3 C4 SP7 SP8 SP3 SPH Q2. Zlia. }
      destruct GR as (GR1 & GR2 & GR3).
      split; [clear - GR3; ulia|]. split; [clear - GR3 I2; ulia|].
      intros [V | [V | [V | [V | [V | V]]]]].
      - destruct V as (p' & n' & Hin & Hpa). destruct (live_ext bt st Lc FF W p' n' Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n' ltac:(lia)) as (U1 & _). clear - GR3 Hpa Y1 Y2 U1 Y8 Y12. unfold boxed in Y12. ulia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        pose proof (fs_range bt st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & D6). clear - GR3 Hfa F1 F2 D5. ulia.
      - destruct V as (p' & n' & Hin & Hs). destruct (live_ext bt st Lc FF W p' n' Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n' ltac:(lia)) as (U1 & U2 & U3 & U4).
        assert (GL : lo <= 8 * (a - SB) /\ 8 * (a - SB) + 8 <= hi).
        { unfold sh_lo, sh_hi in Hs. clear - Hs Y1 Y2 Y4 Y5 Y8 Y9 Y10 U1 U3 U4. unfold up8 in *. Zlia. }
        destruct (quar_chunk_vs_live m n p' n' lo hi Hq HP Hin E) as [D | D]; fold ab cs in D; clear - D GR1 GR2 GL; lia.
      - destruct V as (f & k & Hf & Hs). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        destruct (frame_gran bt st Lc FF W f k Hf) as (FG1 & FG2).
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & _) & _).
        assert (GL : f <= 8 * (a - SB) /\ 8 * (a - SB) + 8 <= f + FS k).
        { unfold sh_lo, sh_hi in Hs. clear - Hs FG1 FG2 F4. Zlia. }
        destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)) as [D | D]; clear - D GL GR1 GR2 F1 F2 C3 C4; ulia.
      - unfold in_stack_shadow, sh_lo in V. clear - V GR2 C4 SP8 SP3 C5 S3. Zlia.
      - unfold in_image_shadow, sh_lo, sh_hi in V. clear - V GR1 C3 SP7 SPH I1 I2. Zlia.
    Qed.
    (* [comment removed for export] *)
    Lemma XB_zone : forall z, AsAinvOpsRc73.AsAinvOpsRc33.XB bt st z -> AsAinvOpsRc73.AsAinvOpsRc23.qhdr bt z \/ SBEG <= z < SBEG + KSPACE.
    Proof using W qg qt FF Lc RUN.
      intros z [Q | (a & (CV & _) & Ha)]; [left; exact Q | right].
      destruct (carved_range bt st Lc FF W BATCHCLASS a ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV) as (_ & _ & C3 & C4 & _).
      change (csize BATCHCLASS) with 8192 in C4. unfold BATCHSZ in Ha. lia.
    Qed.
  End W.
End RcG.
End AsAllocFRcG.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 AsAinvPrist3 AsAinvDrvHist3 AsAllocFKeep0.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Fam.
  Context {RC : run_ceil}.
  Variable bt : as_boot.

  Record hp_fam (HP HPc : option Z -> ast -> Prop) : Prop := HPFAM {
    hp_le   : forall h st, HP h st -> holes_le h st;
    hp_ia   : forall h st, HP h st -> HP h (set_ialloc st);
    hp_chg  : forall h st st1 Lc FF p n, WF bt st Lc FF -> In (p, n) Lc -> HP h st ->
                (forall c, a_reg st1 c = a_reg st c /\ a_cache st1 c = a_cache st c) -> a_sec st1 = a_sec st ->
                a_kact st1 = a_kact st + kcost_free -> a_kact st1 <= KCAP -> HPc h st1;      (* [comment removed for export] *)
    hp_neut : forall h st st', HPc h st -> (forall h', holes_le h' st -> holes_le h' st') -> free_keeps st st' ->
                a_kact st' = a_kact st -> HPc h st';
    hp_fin  : forall h st, HPc h st -> HP h st;
    hp_kcap : forall h st, HPc h st -> a_kact st <= KCAP }.                                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition AAINV_F (HP : option Z -> ast -> Prop) (h : option Z) := AAINVP (HP h) bt.


  (* [comment removed for export] *)
  Definition HPlc (h : option Z) (st : ast) : Prop := holes_le h st /\ a_kact st <= KCAP.
  Lemma hp_fam_le : hp_fam holes_le HPlc.
  Proof using.
    constructor.
    - intros h st H; exact H.
    - intros h st H. unfold holes_le in H |- *. exact H.
    - intros h st st1 Lc FF p n _ _ H AG _ _ KC. split; [| exact KC]. unfold holes_le in H |- *. intros c Hc. apply H. rewrite <- (proj1 (AG c)). exact Hc.
    - intros h st st' [H KC] HO _ EK. split; [exact (HO h H) | rewrite EK; exact KC].
    - intros h st [H _]; exact H.
    - intros h st [_ KC]; exact KC.
  Qed.

  (* [comment removed for export] *)
  Definition HPd (h : option Z) (st : ast) : Prop := holes_le h st /\ drv_hist st.
  (* [comment removed for export] *)
  Definition HPdc (h : option Z) (st : ast) : Prop := holes_le h st /\ prist S_nb st /\ 2 * EVT <= a_kact st /\ a_kact st <= KCAP.
  Lemma hp_fam_drv : hp_fam HPd HPdc.
  Proof using.
    pose proof evt_ge as EG.
    constructor.
    - intros h st [H _]; exact H.
    - intros h st [H D]. split; [unfold holes_le in H |- *; exact H|].
      apply (drv_hist_same st (set_ialloc st) D); [intros c; split; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros NE; exact NE].
    - intros h st st1 Lc FF p n W Hin [H (H1 & H2 & H3)] AG ES EK KC. unfold kcost_free in EK.
      assert (BIG : EVT <= a_kact st).
      { destruct (is_primary n) eqn:HPn.
        - destruct (Z_le_gt_dec (a_kact st) EVT) as [LE | GT]; [| lia].
          exfalso. exact (prist_live bt S_all st Lc FF _ _ p n W (H2 LE) Hin HPn I).
        - apply H3. destruct (live_sec bt st Lc FF W p n Hin HPn) as (sc & Hsc & _). intros E. rewrite E in Hsc. destruct Hsc. }
      split; [unfold holes_le in H |- *; intros c Hc; apply H; rewrite <- (proj1 (AG c)); exact Hc|].
      split; [exact (prist_ext S_nb st st1 (fun c _ => AG c) H1) | split; [lia | exact KC]].
    - intros h st st' (H & P & K & KC) HO [FK _] EK. split; [exact (HO h H)|]. split; [| split; [lia | rewrite EK; exact KC]].
      apply (FK S_nb); [intros N; exact (N eq_refl) | exact P].
    - intros h st (H & P & K & _). split; [exact H|]. split; [exact P|]. split; [intros LE; exfalso; lia | intros _; lia].
    - intros h st (_ & _ & _ & KC); exact KC.
  Qed.

End Fam.
