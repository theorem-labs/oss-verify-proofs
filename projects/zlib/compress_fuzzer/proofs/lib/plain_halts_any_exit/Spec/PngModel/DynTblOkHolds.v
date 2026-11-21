(** * DynTblOkHolds — the inhabitation of [StepReach.DynTblOk].

    OWNER: an earlier development run (inhabitation lap; the statement negotiations are
    settled: chain repair + amb_ok landed by an earlier development run, the dyn_amb_wb
    CODES guard adopted by an earlier development run in my spelling-1).  Every field
    routes through three landed pillars: [ItGSubCover.it_covers_all]
    (root classification + sub coverage), [ItGAmb.it_model_amb] (ambient
    preservation, all exits), and the ported width/leafpos machinery. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees Inflate InflateFast InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblRepl GtTblWidth
  GtUsedBits ItGSubCover ItGAmb.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  StepReach.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 0.  The unconditional range walk (no invariants: every write is a
       [mkCodeT], whose fields are masked by construction) *)

Definition RngE (e : Code) : Prop :=
  0 <= c_bits e /\ 0 <= c_val e < 65536.

Lemma rng_mkCodeT : forall a b v, RngE (mkCodeT a b v).
Proof.
  intros a b v. unfold mkCodeT, RngE. cbn [c_bits c_val].
  unfold u8, u16.
  pose proof (Z.mod_pos_bound b 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound v 65536 ltac:(lia)).
  lia.
Qed.

Lemma rng_here : forall c st, RngE (it_here c st).
Proof.
  intros c st. unfold it_here.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c));
    [apply rng_mkCodeT|].
  destruct (Z.leb (x_match c) (x_work c (s_sym st))); apply rng_mkCodeT.
Qed.

Lemma rng_tset : forall t i e,
  (forall j, RngE (t j)) -> RngE e -> forall j, RngE (tset t i e j).
Proof.
  intros t i e Ht He j.
  destruct (Z.eq_dec j i) as [->|Hne];
    [rewrite tset_same; exact He | rewrite tset_other by exact Hne; apply Ht].
Qed.

Lemma rng_fill : forall n t bi incr h,
  (forall j, RngE (t j)) -> RngE h ->
  forall j, RngE (it_fill n t bi incr h j).
Proof.
  induction n as [|k IH]; intros t bi incr h Ht Hh j; cbn [it_fill];
    [apply Ht|].
  apply IH; [|exact Hh].
  apply rng_tset; [exact Ht | exact Hh].
Qed.

Lemma rng_step : forall c st,
  (forall j, RngE (s_tbl st j)) ->
  match it_step c st with
  | ItCont st' => forall j, RngE (s_tbl st' j)
  | ItBreak st' => forall j, RngE (s_tbl st' j)
  | ItOverflow t => forall j, RngE (t j)
  end.
Proof.
  intros c st Ht.
  assert (Hfill : forall j, RngE
            (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                                / Z.shiftl 1 (s_len st - s_drop st)))
               (s_tbl st)
               (s_next st + Z.shiftr (s_huff st) (s_drop st))
               (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st) j))
    by (apply rng_fill; [exact Ht | apply rng_here]).
  unfold it_step. cbv zeta.
  destruct (Z.eqb _ 0); cbn [andb].
  - destruct (Z.eqb (s_len st) (x_max c)); cbv beta match iota.
    + cbn [s_tbl]. exact Hfill.
    + destruct (Z.ltb (x_root c) _); cbn [andb]; cbv beta match iota.
      * destruct (Z.eqb _ (s_low st)); cbn [andb negb]; cbv beta match iota.
        -- cbn [s_tbl]. exact Hfill.
        -- destruct (it_enough _ _); cbv beta match iota.
           ++ exact Hfill.
           ++ cbn [s_tbl]. apply rng_tset; [exact Hfill | apply rng_mkCodeT].
      * cbn [s_tbl]. exact Hfill.
  - destruct (Z.ltb (x_root c) _); cbn [andb]; cbv beta match iota.
    + destruct (Z.eqb _ (s_low st)); cbn [andb negb]; cbv beta match iota.
      * cbn [s_tbl]. exact Hfill.
      * destruct (it_enough _ _); cbv beta match iota.
        -- exact Hfill.
        -- cbn [s_tbl]. apply rng_tset; [exact Hfill | apply rng_mkCodeT].
    + cbn [s_tbl]. exact Hfill.
Qed.

Lemma rng_loop : forall n c st r,
  (forall j, RngE (s_tbl st j)) ->
  it_loop n c st = Some r ->
  match r with
  | ItBreak st1 => forall j, RngE (it_finish st1 j)
  | ItOverflow t => forall j, RngE (t j)
  | ItCont _ => True
  end.
Proof.
  induction n as [|k IH]; intros c st r Ht Hl; cbn [it_loop] in Hl;
    [discriminate Hl|].
  destruct (it_step c st) as [st'|st'|t'] eqn:Hs;
    pose proof (rng_step c st Ht) as HR; rewrite Hs in HR.
  - exact (IH c st' r HR Hl).
  - injection Hl as <-.
    intro j. unfold it_finish.
    destruct (Z.eqb (s_huff st') 0); [apply HR|].
    apply rng_tset; [exact HR | apply rng_mkCodeT].
  - injection Hl as <-. exact HR.
Qed.

(** [o_tbl]'s fields are in range on every [Some] exit. *)
Lemma rng_model : forall ty lens codes root0 t0 out,
  (forall j, RngE (t0 j)) ->
  it_model ty lens codes root0 t0 = Some out ->
  forall j, RngE (o_tbl out j).
Proof.
  intros ty lens codes root0 t0 out Ht0 Hm.
  unfold it_model in Hm.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hm as <-. exact Ht0.
  - rewrite (it_pre_empty_shape _ _ _ _ _ _ Hpre) in Hm.
    injection Hm as <-. cbn [o_tbl].
    intro j.
    apply rng_tset; [apply rng_tset; [exact Ht0|]|]; apply rng_mkCodeT.
  - injection Hm as <-. exact Ht0.
  - assert (Hst : forall j, RngE (s_tbl st j))
      by (rewrite (it_pre_go_tbl _ _ _ _ _ _ _ Hpre); exact Ht0).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:Hl;
      [|discriminate Hm].
    pose proof (rng_loop _ _ _ _ Hst Hl) as HR.
    destruct r as [st'|st'|tt].
    + discriminate Hm.
    + injection Hm as <-. exact HR.
    + injection Hm as <-. exact HR.
Qed.

(** ** 1.  [o_bits] is in [1,15] on accepted builds *)

Lemma it_model_bits_range : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  1 <= o_bits out <= 15.
Proof.
  intros ty lens codes root0 t0 out Hc Hl Hr Hm Hret.
  unfold it_model in Hm.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hm as <-. cbn in Hret. lia.
  - injection Hm as <-. cbn [o_bits]. lia.
  - injection Hm as <-. cbn in Hret. lia.
  - destruct (cov_pre ty lens codes root0 t0 c st Hc Hl Hr Hpre)
      as [Hctx _].
    destruct Hctx as (Hroot & _).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hlo;
      try discriminate Hm.
    + injection Hm as <-. cbn [o_bits]. exact Hroot.
    + injection Hm as <-. cbn in Hret. lia.
Qed.

(** ** 2.  Field [dyn_codes_tblside] *)

Lemma dyn_codes_tblside_holds :
  forall lens codes root0 cs o,
    amb_ok cs ->
    it_wf CT_CODES lens codes root0 ->
    it_model CT_CODES lens codes root0 (fun i => cs (0 + i)) = Some o ->
    o_ret o = 0 ->
    TblSide (fun i => codes_wb cs 0 (o_tbl o) (0 + i)).
Proof.
  intros lens codes root0 cs o Hamb Hwf Hm Hret i.
  cbv beta.
  destruct Hwf as (Hc0 & Hlens & Hroot0 & _).
  unfold codes_wb.
  destruct (Z.leb 0 (0 + i)) eqn:Hi.
  - assert (Hb15 : c_bits (o_tbl o (0 + i - 0)) <= 15).
    { refine (built_table_bits_le_15 CT_CODES lens codes root0 _ o
                ltac:(lia) Hlens Hroot0 _ Hm Hret (0 + i - 0)).
      intro j. cbv beta. destruct (Hamb (0 + j)) as (Hb & _). lia. }
    assert (Hrng : RngE (o_tbl o (0 + i - 0))).
    { refine (rng_model CT_CODES lens codes root0 _ o _ Hm (0 + i - 0)).
      intro j. cbv beta.
      destruct (Hamb (0 + j)) as (Hb & Hv & _).
      split; [lia | exact Hv]. }
    destruct Hrng as [Hb0 Hv].
    split; [lia | exact Hv].
  - apply Z.leb_gt in Hi.
    destruct (Hamb (0 + i)) as (Hb & Hv & _).
    split; [exact Hb | exact Hv].
Qed.

(** ** 3.  Fields [dyn_lenbits] / [dyn_distbits] *)

Lemma dyn_lenbits_holds : forall d, db_ok d -> 1 <= o_bits (db_o1 d) <= 15.
Proof.
  intros d Hok.
  destruct Hok as (Hamb & Hwf1 & Hm1 & Hr1 & _).
  destruct Hwf1 as (Hc0 & Hlens & Hroot0 & _).
  exact (it_model_bits_range CT_LENS (db_lens d) (db_nlen d) 9 _ (db_o1 d)
           ltac:(lia) Hlens Hroot0 Hm1 Hr1).
Qed.

Lemma dyn_distbits_holds : forall d, db_ok d -> 1 <= o_bits (db_o2 d) <= 15.
Proof.
  intros d Hok.
  destruct Hok as (Hamb & Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  destruct Hwf2 as (Hc0 & Hlens & Hroot0 & _).
  exact (it_model_bits_range CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
           ltac:(lia) Hlens Hroot0 Hm2 Hr2).
Qed.

(** ** 4.  The two views of the installed state

    Under [db_installed], the LEN view is [t_codes] at offset 0 and the
    DIST view at offset [o_used (db_o1 d)]; [t_codes] itself is the
    double [codes_wb].  The ambient facts need no index split (they are
    pointwise over the WHOLE array); the coverage facts need the two
    read-through equalities below. *)

Lemma db_amb2 : forall d, db_ok d ->
  amb_ok (codes_wb (codes_wb (db_cs d) 0 (o_tbl (db_o1 d)))
            (0 + o_used (db_o1 d)) (o_tbl (db_o2 d))).
Proof.
  intros d Hok.
  destruct Hok as (Hamb & Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  apply (it_model_amb CT_DISTS (fun i => db_lens d (i + db_nlen d))
           (db_ndist d) 6
           (codes_wb (db_cs d) 0 (o_tbl (db_o1 d)))
           (0 + o_used (db_o1 d)) (db_o2 d)).
  - apply (it_model_amb CT_LENS (db_lens d) (db_nlen d) 9 (db_cs d) 0
             (db_o1 d)); [exact Hamb | exact Hwf1 | | exact Hm1].
    intro HK. exfalso. vm_compute in HK. discriminate HK.
  - exact Hwf2.
  - intro HK. exfalso. vm_compute in HK. discriminate HK.
  - exact Hm2.
Qed.

Lemma db_amb_state : forall d q', db_ok d -> db_installed d q' ->
  amb_ok (t_codes (s_tab (q_st q'))).
Proof.
  intros d q' Hok Hin.
  destruct Hin as (_ & _ & _ & _ & Hcs).
  rewrite Hcs. apply db_amb2. exact Hok.
Qed.

Lemma db_view_len : forall d q', db_installed d q' ->
  forall i, 0 <= i < o_used (db_o1 d) ->
  t_codes (s_tab (q_st q')) (0 + i) = o_tbl (db_o1 d) i.
Proof.
  intros d q' Hin i Hi.
  destruct Hin as (_ & _ & _ & _ & Hcs).
  rewrite Hcs. unfold codes_wb.
  destruct (Z.leb (0 + o_used (db_o1 d)) (0 + i)) eqn:E1.
  - exfalso. apply Z.leb_le in E1. lia.
  - destruct (Z.leb 0 (0 + i)) eqn:E2.
    + replace (0 + i - 0) with i by lia. reflexivity.
    + exfalso. apply Z.leb_gt in E2. lia.
Qed.

Lemma db_view_dist : forall d q', db_installed d q' ->
  forall i, 0 <= i ->
  t_codes (s_tab (q_st q')) ((0 + o_used (db_o1 d)) + i) = o_tbl (db_o2 d) i.
Proof.
  intros d q' Hin i Hi.
  destruct Hin as (_ & _ & _ & _ & Hcs).
  rewrite Hcs. unfold codes_wb.
  destruct (Z.leb (0 + o_used (db_o1 d)) ((0 + o_used (db_o1 d)) + i))
    eqn:E1.
  - replace ((0 + o_used (db_o1 d)) + i - (0 + o_used (db_o1 d))) with i
      by lia.
    reflexivity.
  - exfalso. apply Z.leb_gt in E1. lia.
Qed.

(** The two coverage instances. *)
Lemma db_cover1 : forall d, db_ok d ->
  2 ^ o_bits (db_o1 d) <= o_used (db_o1 d)
  /\ (forall j, 0 <= j < 2 ^ o_bits (db_o1 d) ->
      RootEntry CT_LENS (o_bits (db_o1 d)) (o_used (db_o1 d))
        (o_tbl (db_o1 d) j))
  /\ (forall i, 2 ^ o_bits (db_o1 d) <= i < o_used (db_o1 d) ->
      SubEntry CT_LENS (o_bits (db_o1 d)) (o_tbl (db_o1 d) i)).
Proof.
  intros d Hok.
  destruct Hok as (Hamb & Hwf1 & Hm1 & Hr1 & _).
  exact (it_covers_all CT_LENS (db_lens d) (db_nlen d) 9 _ (db_o1 d)
           (or_introl eq_refl) Hwf1 Hm1 Hr1).
Qed.

Lemma db_cover2 : forall d, db_ok d ->
  2 ^ o_bits (db_o2 d) <= o_used (db_o2 d)
  /\ (forall j, 0 <= j < 2 ^ o_bits (db_o2 d) ->
      RootEntry CT_DISTS (o_bits (db_o2 d)) (o_used (db_o2 d))
        (o_tbl (db_o2 d) j))
  /\ (forall i, 2 ^ o_bits (db_o2 d) <= i < o_used (db_o2 d) ->
      SubEntry CT_DISTS (o_bits (db_o2 d)) (o_tbl (db_o2 d) i)).
Proof.
  intros d Hok.
  destruct Hok as (Hamb & Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  exact (it_covers_all CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
           (or_intror eq_refl) Hwf2 Hm2 Hr2).
Qed.

(** ** 5.  Chain-shape bookkeeping *)

Lemma leaf_lc_chains_false : forall ty e,
  LeafShape ty e -> lc_chains (c_op e) = false.
Proof.
  intros ty e HL. destruct HL as (H1 & _).
  unfold lc_chains.
  destruct H1 as [H0 | [H16 | H64]].
  - rewrite H0. reflexivity.
  - replace (Z.land (c_op e) 16 =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact H16).
    rewrite andb_false_r. reflexivity.
  - replace (Z.land (c_op e) 64 =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact H64).
    rewrite andb_false_r. reflexivity.
Qed.

Lemma leaf_dc_chains_false : forall e,
  LeafShape CT_DISTS e -> dc_chains (c_op e) = false.
Proof.
  intros e HL. destruct HL as (H1 & H2 & _).
  specialize (H2 eq_refl).
  unfold dc_chains.
  destruct H1 as [H0 | [H16 | H64]]; [contradiction| |].
  - replace (Z.land (c_op e) 16 =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact H16).
    reflexivity.
  - replace (Z.land (c_op e) 64 =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact H64).
    rewrite andb_false_r. reflexivity.
Qed.

Lemma lc_chains_true_shape : forall op, lc_chains op = true ->
  op <> 0 /\ Z.land op 16 = 0 /\ Z.land op 64 = 0.
Proof.
  intros op H. unfold lc_chains in H.
  apply andb_prop in H as [H a64]. apply andb_prop in H as [n0 a16].
  apply negb_true_iff in n0. apply Z.eqb_neq in n0.
  apply Z.eqb_eq in a16. apply Z.eqb_eq in a64.
  auto.
Qed.

Lemma dc_chains_true_shape : forall op, dc_chains op = true ->
  Z.land op 16 = 0 /\ Z.land op 64 = 0.
Proof.
  intros op H. unfold dc_chains in H.
  apply andb_prop in H as [a16 a64].
  apply Z.eqb_eq in a16. apply Z.eqb_eq in a64.
  auto.
Qed.

(** A chain-taking masked root read is a POINTER (leaves never chain),
    and its one hop lands inside the sub-table region [2^b, u). *)
Lemma root_chain_hop : forall ty b u (t : ztbl) v s,
  1 <= b <= 15 ->
  2 ^ b <= u ->
  (forall j, 0 <= j < 2 ^ b -> RootEntry ty b u (t j)) ->
  0 <= v < 2 ^ b ->
  c_op (t v) <> 0 ->
  Z.land (c_op (t v)) 16 = 0 ->
  Z.land (c_op (t v)) 64 = 0 ->
  c_bits (t v) = b
  /\ 1 <= c_op (t v) <= 15 - b
  /\ 2 ^ b <= c_val (t v) + if_low (c_op (t v)) s
  /\ c_val (t v) + if_low (c_op (t v)) s < u.
Proof.
  intros ty b u t v s Hb Hu Hroot Hv Hnz H16 H64.
  destruct (Hroot v Hv) as [Hleaf | Hptr].
  - exfalso. destruct Hleaf as [HL _]. destruct HL as (H1 & _).
    destruct H1 as [H0 | [Ha | Ha]];
      [exact (Hnz H0) | exact (Ha H16) | exact (Ha H64)].
  - destruct Hptr as (Hbits & Hop & Hval & Hvlo & Hvhi).
    assert (Hlow : 0 <= if_low (c_op (t v)) s < 2 ^ (c_op (t v)))
      by (unfold if_low; apply land_ones_range; lia).
    split; [exact Hbits|]. split; [exact Hop|].
    split; [lia | lia].
Qed.

(** ** 6.  Field [dyn_lcside] *)

Lemma dyn_lcside_holds : forall d q', db_ok d -> db_installed d q' ->
  LcSide (tbl_of (q_st q') (t_lencode (s_tab (q_st q')))).
Proof.
  intros d q' Hok Hin.
  pose proof (db_amb_state d q' Hok Hin) as Hamb.
  destruct Hin as (Hlc & _ & _ & _ & _).
  rewrite Hlc. unfold LcSide. cbn [tbl_of].
  split; [|split].
  - intro i. destruct (Hamb (0 + i)) as (Hb & _). lia.
  - intros i H32. destruct (Hamb (0 + i)) as (_ & _ & H3 & _).
    exact (H3 H32).
  - intros i Hnz H32 H64.
    destruct (Hamb (0 + i)) as (_ & _ & _ & H4 & _).
    exact (H4 Hnz H32 H64).
Qed.

(** ** 7.  Field [dyn_tblside_d] *)

Lemma dyn_tblside_d_holds : forall d q', db_ok d -> db_installed d q' ->
  TblSide (tbl_of (q_st q') (t_distcode (s_tab (q_st q')))).
Proof.
  intros d q' Hok Hin.
  pose proof (db_amb_state d q' Hok Hin) as Hamb.
  destruct Hin as (_ & _ & Hdc & _ & _).
  rewrite Hdc. unfold TblSide. cbn [tbl_of].
  intro i.
  destruct (Hamb ((0 + o_used (db_o1 d)) + i)) as (Hb & Hv & _).
  exact (conj Hb Hv).
Qed.

(** ** 8.  Fields [dyn_two_l] / [dyn_two_d] *)

Lemma dyn_two_l_holds : forall d q', db_ok d -> db_installed d q' ->
  lcode_two_level (if_ctx (len_args q')).
Proof.
  intros d q' Hok Hin.
  pose proof (db_cover1 d Hok) as (Hc1u & Hroot1 & Hsub1).
  pose proof (dyn_lenbits_holds d Hok) as Hb1.
  pose proof (pow2_pos_z (o_bits (db_o1 d)) ltac:(lia)) as Hp21.
  pose proof (db_view_len d q' Hin) as HV.
  destruct Hin as (Hlc & Hlb & _ & _ & _).
  unfold lcode_two_level.
  cbn [if_ctx f_lcode f_lmask len_args a_lcode a_lenbits].
  rewrite Hlc, Hlb. cbn [tbl_of].
  intros v x s Hveq Hch.
  pose proof (land_ones_range x (o_bits (db_o1 d)) ltac:(lia)) as Hvr.
  rewrite <- Hveq in Hvr.
  rewrite (HV v ltac:(lia)) in Hch |- *.
  destruct (lc_chains_true_shape _ Hch) as (Hnz & H16 & H64).
  destruct (root_chain_hop CT_LENS (o_bits (db_o1 d)) (o_used (db_o1 d))
              (o_tbl (db_o1 d)) v s Hb1 Hc1u Hroot1 Hvr Hnz H16 H64)
    as (Hbits & Hop & Htlo & Hthi).
  rewrite (HV (c_val (o_tbl (db_o1 d) v)
               + if_low (c_op (o_tbl (db_o1 d) v)) s) ltac:(lia)).
  apply leaf_lc_chains_false with (ty := CT_LENS).
  destruct (Hsub1 (c_val (o_tbl (db_o1 d) v)
                   + if_low (c_op (o_tbl (db_o1 d) v)) s) ltac:(lia))
    as [HL _]. exact HL.
Qed.

Lemma dyn_two_d_holds : forall d q', db_ok d -> db_installed d q' ->
  dcode_two_level (if_ctx (len_args q')).
Proof.
  intros d q' Hok Hin.
  pose proof (db_cover2 d Hok) as (Hc2u & Hroot2 & Hsub2).
  pose proof (dyn_distbits_holds d Hok) as Hb2.
  pose proof (pow2_pos_z (o_bits (db_o2 d)) ltac:(lia)) as Hp22.
  pose proof (db_view_dist d q' Hin) as HV.
  destruct Hin as (_ & _ & Hdc & Hdb & _).
  unfold dcode_two_level.
  cbn [if_ctx f_dcode f_dmask len_args a_dcode a_distbits].
  rewrite Hdc, Hdb. cbn [tbl_of].
  intros v x s Hveq Hch.
  pose proof (land_ones_range x (o_bits (db_o2 d)) ltac:(lia)) as Hvr.
  rewrite <- Hveq in Hvr.
  rewrite (HV v ltac:(lia)) in Hch |- *.
  destruct (dc_chains_true_shape _ Hch) as (H16 & H64).
  assert (Hnz : c_op (o_tbl (db_o2 d) v) <> 0).
  { destruct (Hroot2 v ltac:(lia)) as [Hleaf | Hptr].
    - destruct Hleaf as [HL _]. destruct HL as (_ & H2 & _).
      exact (H2 eq_refl).
    - destruct Hptr as (_ & Hop & _). lia. }
  destruct (root_chain_hop CT_DISTS (o_bits (db_o2 d)) (o_used (db_o2 d))
              (o_tbl (db_o2 d)) v s Hb2 Hc2u Hroot2 Hvr Hnz H16 H64)
    as (Hbits & Hop & Htlo & Hthi).
  rewrite (HV (c_val (o_tbl (db_o2 d) v)
               + if_low (c_op (o_tbl (db_o2 d) v)) s) ltac:(lia)).
  apply leaf_dc_chains_false.
  destruct (Hsub2 (c_val (o_tbl (db_o2 d) v)
                   + if_low (c_op (o_tbl (db_o2 d) v)) s) ltac:(lia))
    as [HL _]. exact HL.
Qed.

(** ** 9.  Field [dyn_wf_tbl] *)

Lemma dyn_wf_tbl_holds : forall d q', db_ok d -> db_installed d q' ->
  if_wf_tbl (len_args q').
Proof.
  intros d q' Hok Hin.
  pose proof (db_cover1 d Hok) as (Hc1u & Hroot1 & Hsub1).
  pose proof (db_cover2 d Hok) as (Hc2u & Hroot2 & Hsub2).
  pose proof (dyn_lenbits_holds d Hok) as Hb1.
  pose proof (dyn_distbits_holds d Hok) as Hb2.
  pose proof (pow2_pos_z (o_bits (db_o1 d)) ltac:(lia)) as Hp21.
  pose proof (pow2_pos_z (o_bits (db_o2 d)) ltac:(lia)) as Hp22.
  pose proof (db_amb_state d q' Hok Hin) as Hamb.
  pose proof (db_view_len d q' Hin) as HVl.
  pose proof (db_view_dist d q' Hin) as HVd.
  destruct Hin as (Hlc & Hlb & Hdc & Hdb & _).
  unfold if_wf_tbl, lcode_len_bounded_upto, lcode_index_range, chain_fit,
    lc_len_ok.
  cbn [if_ctx f_lcode f_dcode f_lmask f_dmask
       len_args a_lcode a_dcode a_lenbits a_distbits].
  rewrite Hlc, Hlb, Hdc, Hdb. cbn [tbl_of].
  assert (Hcase : forall i, 0 <= i < o_used (db_o1 d) ->
            (RootEntry CT_LENS (o_bits (db_o1 d)) (o_used (db_o1 d))
               (o_tbl (db_o1 d) i)
             /\ 0 <= i < 2 ^ o_bits (db_o1 d))
            \/ SubEntry CT_LENS (o_bits (db_o1 d)) (o_tbl (db_o1 d) i)).
  { intros i Hi.
    destruct (Z_lt_le_dec i (2 ^ o_bits (db_o1 d))) as [Hlt|Hge].
    - left. split; [apply Hroot1; lia | lia].
    - right. apply Hsub1. lia. }
  assert (Hleafcase : forall i, 0 <= i < o_used (db_o1 d) ->
            LeafShape CT_LENS (o_tbl (db_o1 d) i)
            \/ RootPtr (o_bits (db_o1 d)) (o_used (db_o1 d))
                 (o_tbl (db_o1 d) i)).
  { intros i Hi.
    destruct (Hcase i Hi) as [[[[HL _] | Hptr] _] | [HL _]];
      [left; exact HL | right; exact Hptr | left; exact HL]. }
  split; [|split; [|split; [|split]]].
  - (* the bundled LEN package at n := o_used (db_o1 d) *)
    exists (o_used (db_o1 d)).
    split; [|split; [|split]].
    + (* lcode_len_bounded_upto *)
      intros v Hv.
      rewrite (HVl v Hv).
      destruct (Hleafcase v Hv) as [HL | Hptr].
      * destruct HL as (_ & _ & _ & _ & _ & H6 & _).
        exact (H6 eq_refl).
      * destruct Hptr as (_ & Hop & _).
        intro Hf. exfalso. apply Hf.
        change 16 with (2 ^ 4). apply land_small_pow2; lia.
    + (* lcode_index_range *)
      split.
      * intro s.
        pose proof (land_ones_range (f_hold s) (o_bits (db_o1 d))
                      ltac:(lia)).
        lia.
      * intros v s Hv Hch.
        rewrite (HVl v Hv) in Hch |- *.
        destruct (lc_chains_true_shape _ Hch) as (Hnz & H16 & H64).
        assert (Hvr : 0 <= v < 2 ^ o_bits (db_o1 d)).
        { destruct (Z_lt_le_dec v (2 ^ o_bits (db_o1 d))) as [Hlt|Hge];
            [lia | exfalso].
          destruct (Hsub1 v ltac:(lia)) as [HL _].
          rewrite (leaf_lc_chains_false _ _ HL) in Hch.
          discriminate Hch. }
        destruct (root_chain_hop CT_LENS (o_bits (db_o1 d))
                    (o_used (db_o1 d)) (o_tbl (db_o1 d)) v s
                    Hb1 Hc1u Hroot1 Hvr Hnz H16 H64)
          as (_ & _ & Htlo & Hthi).
        lia.
    + (* 1 <= bits <= 15 on [0, n) *)
      intros i Hi.
      rewrite (HVl i Hi).
      destruct (Hcase i Hi) as [[[[_ Hbb] | Hptr] _] | [_ Hbb]];
        [lia | destruct Hptr as (Hbits & _); lia | lia].
    + (* op16 -> extra <= 5 on [0, n) *)
      intros i Hi Hf.
      rewrite (HVl i Hi) in Hf |- *.
      destruct (Hleafcase i Hi) as [HL | Hptr].
      * destruct HL as (_ & _ & _ & _ & H5 & _).
        pose proof (H5 Hf) as Hx.
        change (x15_bound CT_LENS) with 5 in Hx. exact Hx.
      * destruct Hptr as (_ & Hop & _).
        exfalso. apply Hf.
        change 16 with (2 ^ 4). apply land_small_pow2; lia.
  - (* dcode bits pointwise: ambient *)
    intro i.
    destruct (Hamb ((0 + o_used (db_o1 d)) + i)) as (Hb & _). exact Hb.
  - (* chain_fit on the LEN view *)
    intros v x s Hveq Hch.
    pose proof (land_ones_range x (o_bits (db_o1 d)) ltac:(lia)) as Hvr.
    rewrite <- Hveq in Hvr.
    assert (Hvu : 0 <= v < o_used (db_o1 d)) by lia.
    rewrite (HVl v Hvu) in Hch |- *.
    destruct (lc_chains_true_shape _ Hch) as (Hnz & H16 & H64).
    destruct (root_chain_hop CT_LENS (o_bits (db_o1 d)) (o_used (db_o1 d))
                (o_tbl (db_o1 d)) v s Hb1 Hc1u Hroot1 Hvr Hnz H16 H64)
      as (Hbits & Hop & Htlo & Hthi).
    rewrite (HVl (c_val (o_tbl (db_o1 d) v)
                  + if_low (c_op (o_tbl (db_o1 d) v)) s) ltac:(lia)).
    destruct (Hsub1 (c_val (o_tbl (db_o1 d) v)
                     + if_low (c_op (o_tbl (db_o1 d) v)) s) ltac:(lia))
      as [_ Hsb].
    lia.
  - (* chain_fit on the DIST view *)
    intros v x s Hveq Hch.
    pose proof (land_ones_range x (o_bits (db_o2 d)) ltac:(lia)) as Hvr.
    rewrite <- Hveq in Hvr.
    rewrite (HVd v ltac:(lia)) in Hch |- *.
    destruct (dc_chains_true_shape _ Hch) as (H16 & H64).
    assert (Hnz : c_op (o_tbl (db_o2 d) v) <> 0).
    { destruct (Hroot2 v ltac:(lia)) as [Hleaf | Hptr].
      - destruct Hleaf as [HL _]. destruct HL as (_ & H2 & _).
        exact (H2 eq_refl).
      - destruct Hptr as (_ & Hop & _). lia. }
    destruct (root_chain_hop CT_DISTS (o_bits (db_o2 d)) (o_used (db_o2 d))
                (o_tbl (db_o2 d)) v s Hb2 Hc2u Hroot2 Hvr Hnz H16 H64)
      as (Hbits & Hop & Htlo & Hthi).
    rewrite (HVd (c_val (o_tbl (db_o2 d) v)
                  + if_low (c_op (o_tbl (db_o2 d) v)) s) ltac:(lia)).
    destruct (Hsub2 (c_val (o_tbl (db_o2 d) v)
                     + if_low (c_op (o_tbl (db_o2 d) v)) s) ltac:(lia))
      as [_ Hsb].
    lia.
  - (* dext pointwise: ambient *)
    intros i Hf.
    destruct (Hamb ((0 + o_used (db_o1 d)) + i)) as (_ & _ & _ & _ & H5).
    exact (H5 Hf).
Qed.

(** ** 10.  THE RECORD *)

(** ** 10.  Field [dyn_root_opshape] (rootshape wave)

    (* proof by q7-decode; reviewed and endorsed by an earlier development run (owner),; g1's independent DynRootOpShape.v proof corroborates in bed *) *)

Lemma land240_small : forall a, 0 <= a < 16 -> Z.land a 240 = 0.
Proof.
  intros a Ha.
  assert (Ea : Z.land a 15 = a).
  { replace 15 with (Z.ones 4) by (rewrite Z.ones_equiv; cbn; lia).
    rewrite Z.land_ones by lia. apply Z.mod_small; lia. }
  rewrite <- Ea, <- Z.land_assoc.
  change (Z.land 15 240) with 0.
  apply Z.land_0_r.
Qed.

Lemma dyn_root_opshape_holds : forall d q', db_ok d -> db_installed d q' ->
  lcode_root_opshape (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))))
    (t_lenbits (s_tab (q_st q'))).
Proof.
  intros d q' Hok Hin.
  pose proof (db_cover1 d Hok) as (Hc1u & Hroot1 & _).
  pose proof (dyn_lenbits_holds d Hok) as Hb1.
  pose proof (db_view_len d q' Hin) as HV.
  pose proof Hin as (Hlc & Hlb & _ & _ & _).
  unfold lcode_root_opshape.
  rewrite Hlc, Hlb. cbn [tbl_of]. cbv beta.
  intros x.
  pose proof (land_ones_range x (o_bits (db_o1 d)) ltac:(lia)) as Hvr.
  rewrite (HV (Z.land x (Z.shiftl 1 (o_bits (db_o1 d)) - 1))
             ltac:(lia)).
  intros Hnz H240 H32 H64.
  destruct (Hroot1 (Z.land x (Z.shiftl 1 (o_bits (db_o1 d)) - 1))
              ltac:(lia)) as [HLeaf | HPtr].
  - destruct HLeaf as ((H1 & _) & _).
    destruct H1 as [H0 | [Ha | Ha]];
      [ exact (False_ind _ (Hnz H0)) | exact Ha
      | exact (False_ind _ (Ha H64)) ].
  - destruct HPtr as (Hbits & Hop & _ & _ & _).
    exfalso. apply H240. apply land240_small. lia.
Qed.

Theorem DynTblOk_holds : DynTblOk.
Proof.
  exact (mkDynTblOk
           dyn_codes_tblside_holds
           it_model_amb
           dyn_wf_tbl_holds
           dyn_lcside_holds
           dyn_tblside_d_holds
           dyn_two_l_holds
           dyn_two_d_holds
           dyn_lenbits_holds
           dyn_distbits_holds
           dyn_root_opshape_holds).
Qed.

(** The knot, fully discharged: [step_ok] at every reachable state,
    residual-free. *)
Corollary step_ok_everywhere : forall c q, ReachSt q -> step_ok c q.
Proof.
  exact (step_ok_reach DynTblOk_holds).
Qed.

Print Assumptions dyn_codes_tblside_holds.
Print Assumptions dyn_wf_tbl_holds.
Print Assumptions dyn_root_opshape_holds.
Print Assumptions DynTblOk_holds.
Print Assumptions step_ok_everywhere.
