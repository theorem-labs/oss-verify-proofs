(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib LiveStats.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma nodup_fst_unique : forall (l : list (Z * Z)) d a b, NoDup (map fst l) -> In (d, a) l -> In (d, b) l -> a = b.
Proof.
  induction l as [|[q k] l IH]; intros d a b ND Ha Hb; [destruct Ha|]. cbn [map fst] in ND.
  inversion ND as [|q' l' Hq Hl]; subst.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - rewrite Ha in Hb; injection Hb; auto.
  - injection Ha as -> ->. exfalso. apply Hq. apply list_elem_of_In. apply (in_map fst) in Hb. exact Hb.
  - injection Hb as -> ->. exfalso. apply Hq. apply list_elem_of_In. apply (in_map fst) in Ha. exact Ha.
  - exact (IH d a b Hl Ha Hb).
Qed.

Lemma nodup_fst_filter : forall (f : Z * Z -> bool) (l : list (Z * Z)), NoDup (map fst l) -> NoDup (map fst (List.filter f l)).
Proof.
  intros f l. induction l as [|[q k] l IH]; intros ND; [constructor|]. cbn [map fst List.filter] in *.
  inversion ND as [|q' l' Hq Hl]; subst. destruct (f (q, k)); [|apply IH; exact Hl].
  cbn [map fst]. apply NoDup_cons_2; [|apply IH; exact Hl].
  intros Hin. apply Hq. apply list_elem_of_In. apply list_elem_of_In in Hin. apply in_map_iff in Hin.
  destruct Hin as (x & Hx & Hin). apply filter_In in Hin. apply in_map_iff. exists x. split; [exact Hx | exact (proj1 Hin)].
Qed.

Section Room.
Context {AC : AllocCeiling}.
  Variable SEGS : list Segment.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.

  Definition classes_sep : Prop :=
    forall j, 0 <= j -> 96 * 2 ^ j < BIG MI -> size_class MI (48 * 2 ^ j) + 1 < size_class MI (96 * 2 ^ j).
  Definition round_big_add : Prop :=
    forall a b, 0 <= a -> 0 <= b -> round_big MI a + round_big MI b <= round_big MI (a + b + 2 ^ 14).
  Hypothesis CLS : classes_sep.
  Hypothesis RBA : round_big_add.

  Variables (A0 : AS MI) (m0 : sbuf).
  Hypothesis ND0 : NoDup (map fst (live MI A0)).
  Hypothesis BL0 : forall b, In b (str_blocks m0) -> In b (live MI A0).
  Hypothesis SH0 : forall d asz, m0 = SLong d asz -> exists j, 0 <= j /\ asz = 48 * 2 ^ j.
  Hypothesis ROOM0 : ds_room SEGS L MI A0.

  Definition inb (x : Z * Z) (l : list (Z * Z)) : bool := existsb (fun y => Z.eqb (fst x) (fst y) && Z.eqb (snd x) (snd y)) l.
  Lemma inb_spec : forall x l, inb x l = true <-> In x l.
  Proof using.
    intros [q k] l. unfold inb. rewrite existsb_exists. split.
    - intros ([q' k'] & Hin & Hb). cbn in Hb. apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
    - intros Hin. exists (q, k). split; [exact Hin|]. cbn. rewrite !Z.eqb_refl. reflexivity.
  Qed.
  Definition R0 : list (Z * Z) := List.filter (fun x => negb (inb x (str_blocks m0))) (live MI A0).
  Lemma R0_spec : forall x, In x R0 <-> In x (live MI A0) /\ ~ In x (str_blocks m0).
  Proof using AC SEGS L MI A0 m0.
    intros x. unfold R0. rewrite filter_In. split; intros [H1 H2]; split; try exact H1.
    - intros Hin. apply (proj2 (inb_spec x _)) in Hin. rewrite Hin in H2. discriminate H2.
    - destruct (inb x (str_blocks m0)) eqn:E; [|reflexivity]. exfalso. apply H2. apply inb_spec. exact E.
  Qed.
  Lemma R0_nodup : NoDup (map fst R0).
  Proof using AC SEGS L MI A0 m0 ND0. unfold R0. apply nodup_fst_filter. exact ND0. Qed.

  Lemma R0_fresh0 : forall b x, In b (str_blocks m0) -> In x R0 -> fst x <> fst b.
  Proof using AC SEGS L MI A0 m0 ND0 BL0 SH0.
    intros b x Hb Hx E. apply R0_spec in Hx. destruct Hx as [Hx Hnx]. destruct m0 as [|d0 a0]; [destruct Hb|].
    cbn [str_blocks] in *. destruct Hb as [<-|[]]. destruct x as [q k]. cbn in E. subst q. apply Hnx. left. f_equal.
    symmetry. exact (nodup_fst_unique _ _ _ _ ND0 Hx (BL0 _ ltac:(left; reflexivity))).
  Qed.

  Lemma perm0 : Permutation (live MI A0) (str_blocks m0 ++ R0).
  Proof using AC SEGS L MI A0 m0 ND0 BL0 SH0.
    apply live_equiv_perm; [exact ND0 | |].
    - apply NoDup_fst_app; [destruct m0; [apply NoDup_fst_nil | apply NoDup_fst_single] | exact R0_nodup |].
      intros q k Hx Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & HbIn). exact (R0_fresh0 b (q, k) HbIn Hx (eq_sym Hb)).
    - intros q k. rewrite in_app_iff, R0_spec. split; [|intros [H|[H _]]; [apply BL0; exact H | exact H]].
      intros Hx. destruct (inb (q, k) (str_blocks m0)) eqn:E; [left; apply inb_spec; exact E | right].
      split; [exact Hx|]. intros Hin. apply inb_spec in Hin. rewrite Hin in E. discriminate E.
  Qed.

  Record ds_ri (A : AS MI) (m : sbuf) (w : Z) : Prop := DS_RI {
    ri_caps  : caps MI A = caps MI A0;
    ri_big   : bigcap MI A = bigcap MI A0;
    ri_mem   : forall x, In x (live MI A) <-> In x (str_blocks m) \/ (In x (live MI A0) /\ ~ In x (str_blocks m0));
    ri_fresh : forall b x, In b (str_blocks m) -> In x (live MI A0) -> ~ In x (str_blocks m0) -> fst x <> fst b;
    ri_shape : m = m0 \/ exists d j, 0 <= j /\ m = SLong d (48 * 2 ^ j) /\ 48 * 2 ^ j <= 2 * w + 48;
    ri_w     : 0 <= w
  }.

  Lemma ri_init : forall w, 0 <= w -> ds_ri A0 m0 w.
  Proof using AC SEGS L MI A0 m0 ND0 BL0 SH0.
    intros w Hw. constructor; try reflexivity; try lia; [| | left; reflexivity].
    - intros x. rewrite <- R0_spec, <- in_app_iff. split; intros H.
      + apply (Permutation_in x perm0). exact H.
      + apply (Permutation_in x (Permutation_sym perm0)). exact H.
    - intros b x Hb Hx Hnx. apply (R0_fresh0 b x Hb). apply R0_spec. split; assumption.
  Qed.

  Lemma perm_of_ri : forall A M model m w, ainv MI A M model -> ds_ri A m w -> Permutation (live MI A) (str_blocks m ++ R0).
  Proof using AC SEGS L MI A0 m0 ND0.
    intros A M model m w AI RI. apply live_equiv_perm; [exact (ai_live_nodup MI A M model AI) | |].
    - apply NoDup_fst_app; [destruct m; [apply NoDup_fst_nil | apply NoDup_fst_single] | exact R0_nodup |].
      intros q k Hx Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & HbIn). apply R0_spec in Hx. destruct Hx as [Hx Hnx].
      exact (ri_fresh _ _ _ RI b (q, k) HbIn Hx Hnx (eq_sym Hb)).
    - intros q k. rewrite in_app_iff, R0_spec. apply (ri_mem _ _ _ RI).
  Qed.

  Lemma shape_pos : forall j, 0 <= j -> 48 <= 48 * 2 ^ j.
  Proof using. intros j Hj. assert (2 ^ 0 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_0_r in H. nia. Qed.

  Lemma ri_grow : forall A M model m w, ainv MI A M model -> ds_ri A m w -> w = str_cap m -> w + 1 <= DS_MAXLEN ->
      str_grow m <= NMAX MI /\ roomL MI A (live MI A) (str_grow m).
  Proof using AC SEGS L MI CLS RBA A0 m0 ND0 BL0 SH0 ROOM0.
    intros A M model m w AI RI Hw HB. destruct ROOM0 as [HNM ROOM].
    pose proof (ai_big_pos MI) as HBIG.
    pose proof (perm_of_ri A M model m w AI RI) as P. pose proof perm0 as P0.
    set (g := str_grow m).
    assert (Hg : 0 < g <= 2 * w + 4 /\ 48 <= g).
    { subst g w. destruct m as [|d asz]; cbn [str_grow str_cap]; [unfold SSO_CAP; lia|].
      destruct (ri_shape _ _ _ RI) as [E0|(d' & j & Hj & E & _)].
      - destruct (SH0 d asz (eq_sym E0)) as (j & Hj & ->). pose proof (shape_pos j Hj). lia.
      - injection E as E1 E2. pose proof (shape_pos j Hj). subst asz. lia. }
    unfold DS_MAXLEN, DS_MAXBLK in *. split; [lia|].
    destruct (ROOM g ltac:(lia)) as [RS RB]. unfold roomL.
    rewrite (count_class_f_perm _ _ _ _ _ P), (count_class_f_perm _ _ _ _ _ P), (big_bytes_f_perm _ _ _ _ P).
    rewrite (count_class_f_perm _ _ _ _ _ P0), (count_class_f_perm _ _ _ _ _ P0) in RS. rewrite (big_bytes_f_perm _ _ _ _ P0) in RB.
    rewrite !count_class_f_app, !big_bytes_f_app in *. rewrite (ri_caps _ _ _ RI), (ri_big _ _ _ RI).
    split.
    - intros Hsmall. specialize (RS Hsmall).
      enough (E : forall c, c = size_class MI g \/ c = size_class MI g + 1 ->
                 count_class_f (size_class MI) (BIG MI) (str_blocks m) c <= count_class_f (size_class MI) (BIG MI) (str_blocks m0) c).
      { pose proof (E _ (or_introl eq_refl)). pose proof (E _ (or_intror eq_refl)). lia. }
      intros c Hc. destruct (ri_shape _ _ _ RI) as [->|(d' & j & Hj & -> & _)]; [lia|].
      cbn [str_blocks count_class_f str_grow] in *. subst g.
      replace (2 * (48 * 2 ^ j)) with (96 * 2 ^ j) in * by lia.
      pose proof (CLS j Hj Hsmall) as HC.
      assert (Hnn : 0 <= count_class_f (size_class MI) (BIG MI) (str_blocks m0) c).
      { destruct m0; cbn [str_blocks count_class_f]; [lia|]. destruct (_ && _); lia. }
      destruct (48 * 2 ^ j <? BIG MI) eqn:E1; [|cbn; lia].
      destruct (size_class MI (48 * 2 ^ j) =? c) eqn:E2; [|cbn; lia]. apply Z.eqb_eq in E2. exfalso. lia.
    - intros Hbig. specialize (RB Hbig).
      destruct (ri_shape _ _ _ RI) as [->|(d' & j & Hj & -> & _)]; [exact RB|].
      pose proof (proj2 (ROOM (2 ^ 28) ltac:(lia)) ltac:(lia)) as RM.
      rewrite (big_bytes_f_perm _ _ _ _ P0), big_bytes_f_app in RM.
      assert (Hnn : 0 <= big_bytes_f (round_big MI) (BIG MI) (str_blocks m0)).
      { destruct m0; cbn [str_blocks big_bytes_f]; [lia|]. destruct (_ <=? _); [|lia]. pose proof (ai_round_big_nonneg MI asz).
        destruct (SH0 _ _ eq_refl) as (j0 & Hj0 & ->). pose proof (shape_pos j0 Hj0). lia. }
      cbn [str_blocks big_bytes_f str_grow str_cap] in *. subst g w.
      pose proof (shape_pos j Hj).
      pose proof (RBA (48 * 2 ^ j) (2 * (48 * 2 ^ j)) ltac:(lia) ltac:(lia)) as HA.
      pose proof (ai_round_big_mono MI (48 * 2 ^ j + 2 * (48 * 2 ^ j) + 2 ^ 14) (2 ^ 28) ltac:(lia)) as HM.
      pose proof (ai_round_big_nonneg MI (48 * 2 ^ j) ltac:(lia)).
      destruct (BIG MI <=? 48 * 2 ^ j); lia.
  Qed.

  Lemma ri_step : forall A A' M' model' m w d, ainv MI A' M' model' -> ds_ri A m w -> w = str_cap m ->
      lapply (live MI A) (LAdd d (str_grow m) :: sbuf_del m) (live MI A') ->
      caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
      ds_ri A' (SLong d (str_grow m)) (w + 1).
  Proof using AC SEGS L MI A0 m0 BL0 SH0.
    intros A A' M' model' m w d AI' RI Hw LAP HC HBC.
    cbn [lapply] in LAP. destruct LAP as (lv1 & [-> Hfresh] & LAP).
    assert (MEM' : forall x, In x (live MI A') <-> x = (d, str_grow m) \/ (In x (live MI A) /\ ~ In x (str_blocks m))).
    { intros [q k]. destruct m as [|dm am]; cbn [sbuf_del lapply str_blocks] in LAP |- *.
      - rewrite LAP. cbn [In]. split; [intros [H|H]; [left; symmetry; exact H | right; split; [exact H | intros []]] | intros [H|[H _]]; [left; symmetry; exact H | right; exact H]].
      - destruct LAP as (lv2 & DEL & ->). rewrite (DEL q k). cbn [In]. split.
        + intros [[H|H] Hne]; [left; symmetry; exact H | right]. split; [exact H|]. intros [E|[]]. injection E. lia.
        + intros [H|[H Hn]].
          * split; [left; symmetry; exact H|]. injection H as -> ->. intros ->. apply Hfresh. apply in_map_iff. exists (dm, am). split; [reflexivity|].
            apply (proj2 (ri_mem _ _ _ RI (dm, am))). left. left. reflexivity.
          * split; [right; exact H|]. intros ->. apply Hn. left. f_equal.
            apply (proj1 (ri_mem _ _ _ RI _)) in H. destruct H as [[E|[]]|[H0 Hn0]]; [injection E; auto|].
            exfalso. exact (ri_fresh _ _ _ RI (dm, am) (dm, k) ltac:(left; reflexivity) H0 Hn0 eq_refl). }
    constructor.
    - rewrite HC. exact (ri_caps _ _ _ RI). - rewrite HBC. exact (ri_big _ _ _ RI).
    - intros x. rewrite MEM'. cbn [str_blocks In]. rewrite (ri_mem _ _ _ RI x). split.
      + intros [->|[[H|[H Hn]] Hnm]]; [left; left; reflexivity | exfalso; exact (Hnm H) | right; split; assumption].
      + intros [[<-|[]]|[H Hn]]; [left; reflexivity | right]. split; [right; split; assumption|].
        intros Hb. exact (ri_fresh _ _ _ RI x x Hb H Hn eq_refl).
    - intros b x Hb Hx Hnx. cbn [str_blocks] in Hb. destruct Hb as [<-|[]]. cbn [fst]. intros E.
      apply Hfresh. apply in_map_iff. exists x. split; [exact E|]. apply (proj2 (ri_mem _ _ _ RI x)). right. split; assumption.
    - right. pose proof (ri_w _ _ _ RI). destruct (ri_shape _ _ _ RI) as [->|(d' & j & Hj & -> & Hb)].
      + destruct m0 as [|d0 a0]; cbn [str_grow str_cap] in *.
        * exists d, 0. rewrite Z.pow_0_r. repeat split; lia.
        * destruct (SH0 d0 a0 eq_refl) as (j & Hj & ->). exists d, (j + 1). rewrite Z.pow_add_r, Z.pow_1_r by lia.
          pose proof (shape_pos j Hj). split; [lia|]. split; [f_equal; lia | lia].
      + cbn [str_grow str_cap] in *. exists d, (j + 1). rewrite Z.pow_add_r, Z.pow_1_r by lia.
        pose proof (shape_pos j Hj). split; [lia|]. split; [f_equal; lia | lia].
    - pose proof (ri_w _ _ _ RI). lia.
  Qed.

  Lemma ri_mono : forall A m w w', ds_ri A m w -> w <= w' <= str_cap m -> ds_ri A m w'.
  Proof using AC SEGS L MI A0 m0.
    intros A m w w' RI Hw. pose proof (ri_w _ _ _ RI) as Hw0. destruct RI. constructor; try assumption; [|lia].
    destruct ri_shape0 as [H0|(d' & j & Hj & E & Hb)]; [left; exact H0 | right]. exists d', j. split; [lia|]. split; [exact E | lia].
  Qed.

  Lemma ri_xfer : forall A m w, ds_ri A m w -> blk_xfer (str_blocks m0) (str_blocks m) (live MI A0) (live MI A).
  Proof using AC SEGS L MI A0 m0 BL0.
    intros A m w RI. split; [exact BL0|]. split.
    - intros b x Hb Hx Hnx. exact (ri_fresh _ _ _ RI b x Hb Hx Hnx).
    - intros x. exact (ri_mem _ _ _ RI x).
  Qed.
End Room.

