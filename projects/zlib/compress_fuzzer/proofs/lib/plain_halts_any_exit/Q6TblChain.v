(** * Q6TblChain — the TABLE-chain value walk: the endpoint.

    OWNER: an earlier development run (stage-4 split; handoff in q6-inflater/DESIGN.md).
    MY half of [Q6HuffResidue.ZrHuffDynLeg]: from the ty=2 dispatch state
    ([M_TABLE]), the header chain (TABLE -> LENLENS -> CODELENS) either
    takes an absorbed arm or reaches the LEN dispatch agreeing with
    [decode_dynamic_tables], the runtime tables installed from accepted
    [it_model] builds in the [DynBuild] vocabulary.  The machine falls
    through INTO [inf_LEN_] inside ONE [inf_step], so the hand-over is
    the STEP EQUATION [inf_step c q = inf_LEN_ qL] (boundary decision
    messaged to model-rt 2026-08-20).

    Deliberately REACH-FREE: the payload is [db_installed] plus the raw
    acceptance equations ([db_acc]) — NOT [db_ok], whose [amb_ok] clause
    is a reachability fact ([rc_amb]).

    RESIDUE: [ZrCodesFetchRes] — the per-symbol fetch bridge on an
    accepted CODES build, in exactly [Q6TblChainCore.zr_codes_fetch_bridge]'s
    shape.  Producer: model-rt's generic fetch-vs-hdecode instrument or a
    discharge from ZReproQ6K's symbol class at CT_CODES (an earlier development run).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inftrees
  InflateFast Inflate InflateThy StepReach ItGTblCover InftreesBridge
  ItGModelExt DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproL0E ZReproQ6A ZReproQ6K Q6HuffResidue Q6TblChainCore
  W2Stream GtBrAlign.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The hand-over payload.
   ========================================================================== *)

(** [db_ok] minus its [amb_ok] clause: both builds accepted with the
    well-formedness the keystone consumers instantiate on.  (A consumer
    holding [ReachSt] recovers full [db_ok] from [rc_amb].) *)
Definition db_acc (d : DynBuild) : Prop :=
  it_wf CT_LENS (db_lens d) (db_nlen d) 9
  /\ it_model CT_LENS (db_lens d) (db_nlen d) 9
       (fun i => db_cs d (0 + i)) = Some (db_o1 d)
  /\ o_ret (db_o1 d) = 0
  /\ it_wf CT_DISTS (fun i => db_lens d (i + db_nlen d)) (db_ndist d) 6
  /\ it_model CT_DISTS (fun i => db_lens d (i + db_nlen d)) (db_ndist d) 6
       (fun i => codes_wb (db_cs d) 0 (o_tbl (db_o1 d))
                   ((0 + o_used (db_o1 d)) + i)) = Some (db_o2 d)
  /\ o_ret (db_o2 d) = 0.

(** The LEN dispatch, reached: the one [inf_step] at [M_TABLE] equals
    [inf_LEN_] at a state [qL] whose tables are the accepted builds of
    the DECODED length lists.  [it_pre = PreGo] is carried for both
    builds so ZReproQ6K's Section hypotheses instantiate directly. *)
Definition zr_len_dispatch (c : InfCtx) (q qL : InfSt)
           (lit dst : list nat) (d : DynBuild) : Prop :=
  inf_step c q = inf_LEN_ qL
  /\ db_acc d
  /\ db_installed d qL
  /\ db_lens d = zlens (lit ++ dst)
  /\ db_nlen d = Z.of_nat (length lit)
  /\ db_ndist d = Z.of_nat (length dst)
  (* v5 (falsifier gate-2, q6-fixedtbl): the POPULATION bound — machine-only
     (the M_TABLE TOO_MANY guard; it_wf says only <=288/<=32 and the
     declarative decoder is unguarded), so it must be EXPORTED here or the
     legs' marker-uniqueness has an undischargeable premise.  At codes=288
     the builder writes lext junk (203/77) byte-colliding with nothing only
     because this bound holds; measured at gate 2. *)
  /\ db_nlen d <= 286
  /\ db_ndist d <= 30
  /\ (exists c1 st1, it_pre CT_LENS (db_lens d) (db_nlen d) 9
                       (fun i => db_cs d (0 + i)) = PreGo c1 st1)
  /\ ((exists c2 st2, it_pre CT_DISTS (fun i => db_lens d (i + db_nlen d))
                        (db_ndist d) 6
                        (fun i => codes_wb (db_cs d) 0 (o_tbl (db_o1 d))
                                    ((0 + o_used (db_o1 d)) + i))
                      = PreGo c2 st2)
      \/ (exists t, it_pre CT_DISTS (fun i => db_lens d (i + db_nlen d))
                      (db_ndist d) 6
                      (fun i => codes_wb (db_cs d) 0 (o_tbl (db_o1 d))
                                  ((0 + o_used (db_o1 d)) + i))
                    = PreEmpty t))
  /\ q_ob qL = q_ob q
  /\ h_last (s_hdr (q_st qL)) = h_last (s_hdr (q_st q))
  /\ q_in qL = q_in q
  /\ q_out qL = q_out q
  /\ w_wsize (s_win (q_st qL)) = w_wsize (s_win (q_st q))
  /\ q_ret qL = 0
  (* v4 (dyn-round falsifier chair, q6-fixedtbl):
     the composite must thread [zr_blk_frame]'s remaining clauses through
     this handover; writer census (set_wrap/set_flags/set_whave/set_sane:
     ZERO sites in the TABLE->LENLENS->CODELENS arms) makes all four
     frame-riding.  Spellings verbatim from [Q6HuffResidue.zr_blk_frame]. *)
  /\ h_wrap (s_hdr (q_st qL)) = h_wrap (s_hdr (q_st q))
  /\ h_flags (s_hdr (q_st qL)) = h_flags (s_hdr (q_st q))
  (* amendment #11: h_check/h_total frame conjuncts — carrier q7-decode;
     g1 census; q6 pre-ruling; #10 shape *)
  /\ h_check (s_hdr (q_st qL)) = h_check (s_hdr (q_st q))
  /\ h_total (s_hdr (q_st qL)) = h_total (s_hdr (q_st q))
  /\ w_whave (s_win (q_st qL)) = w_whave (s_win (q_st q))
  /\ t_sane (s_tab (q_st qL)) = t_sane (s_tab (q_st q)).

(** THE deliverable: my half of [ZrHuffDynLeg], arm-for-arm. *)
Definition ZrTableChain : Prop :=
  forall c q,
    zr_cflush_ok c ->
    br_wf (q_br q) ->
    W2Stream.br_haligned (q_br q) ->
    0 <= o_put (q_ob q) ->
    h_mode (s_hdr (q_st q)) = M_TABLE ->
    q_ret q = 0 ->
    (exists lit dst r3 qL d,
        decode_dynamic_tables (br_stream (q_br q)) = Some (lit, dst, r3)
        /\ br_stream (q_br qL) = r3
        /\ br_wf (q_br qL)
        /\ W2Stream.br_haligned (q_br qL)
        /\ zr_len_dispatch c q qL lit dst d)
    \/ (exists k q',
        inf_iter k c q = Some q'
        /\ h_mode (s_hdr (q_st q')) = M_BAD)
    \/ (exists n s,
        inf_loop n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfCont _ => False
           | InfRet _ _ => False
           | InfDead _ => False
           | InfFuel => True
           end).

(** THE residue this walk is hypothesized on: the fetch bridge at an
    accepted (PreGo) CODES build, spelled at the machine's own view. *)
Definition ZrCodesFetchRes : Prop :=
  forall (cl : list nat) (lens : zarr) (cs : ztbl) out,
    length cl = 19%nat ->
    arr_eq_on lens (zlens cl) 0 19 ->
    (forall x, In x cl -> (x <= 7)%nat) ->
    it_model CT_CODES lens 19 7 (fun i => cs (0 + i)) = Some out ->
    o_ret out = 0 ->
    (exists c0 st0, it_pre CT_CODES lens 19 7 (fun i => cs (0 + i))
                    = PreGo c0 st0) ->
    zr_codes_fetch_bridge cl
      (fun i => codes_wb cs 0 (o_tbl out) (0 + i)) (o_bits out).

(* ==========================================================================
   2.  The PreEmpty absorber: an accepted-EMPTY CODES build's table holds
       only the two op-64 markers ([val] 0), so CODELENS writes nothing
       but zeros and the NO-EOB check catches it.
   ========================================================================== *)

Lemma fetch_marker : forall f (t : ztbl) b,
  br_wf b ->
  (forall i, 0 <= i < 2 -> t i = mkCodeT 64 1 0) ->
  match inf_fetch_go f t 1 b with
  | FetchOk h b' => h = mkCodeT 64 1 0 /\ br_wf b' /\ 1 <= br_bits b'
  | FetchLeave _ => True
  | FetchFuel => True
  end.
Proof.
  induction f as [|f IH]; intros t b Hwf Ht; cbn [inf_fetch_go];
    [exact I|].
  assert (Hh : 0 <= br_hold b) by (destruct Hwf as (_ & Hh & _); lia).
  pose proof (br_bits_of_range 1 b ltac:(lia) Hh) as Hr.
  change (Z.shiftl 1 1) with 2 in Hr.
  rewrite (Ht (br_bits_of 1 b) Hr).
  change (c_bits (mkCodeT 64 1 0)) with 1.
  destruct (Z.leb_spec 1 (br_bits b)) as [Hle|Hgt].
  - split; [reflexivity|]. split; [exact Hwf|]. exact Hle.
  - destruct (br_pullbyte b) as [b1|] eqn:EP; [|exact I].
    assert (Hwf1 : br_wf b1)
      by (apply (br_wf_pullbyte b b1); [exact Hwf | lia | exact EP]).
    exact (IH t b1 Hwf1 Ht).
Qed.

Lemma cl_loop_marker_zero : forall n (t : ztbl) tot s,
  br_wf (cl_br s) ->
  (forall i, 0 <= i < 2 -> t i = mkCodeT 64 1 0) ->
  (forall j, 0 <= j < cl_have s -> cl_lens s j = 0) ->
  0 <= cl_have s ->
  match cl_loop n t 1 tot s with
  | Some (ClDone s') =>
      tot <= cl_have s'
      /\ (forall j, 0 <= j < cl_have s' -> cl_lens s' j = 0)
  | _ => True
  end.
Proof.
  induction n as [|n IH]; intros t tot s Hwf Ht Hz Hh; cbn [cl_loop];
    [exact I|].
  unfold cl_step at 1.
  destruct (Z.leb_spec tot (cl_have s)) as [Hle|Hgt].
  { split; [exact Hle | exact Hz]. }
  unfold inf_fetch.
  pose proof (fetch_marker (S (Z.to_nat (br_have (cl_br s)))) t (cl_br s)
                Hwf Ht) as HF.
  destruct (inf_fetch_go (S (Z.to_nat (br_have (cl_br s)))) t 1 (cl_br s))
    as [h b'|b'|]; [| exact I | exact I].
  destruct HF as (-> & Hwfb & Hb1).
  change (c_val (mkCodeT 64 1 0)) with 0.
  change (c_bits (mkCodeT 64 1 0)) with 1.
  cbv beta iota.
  assert (Hwfd : br_wf (br_dropbits 1 b'))
    by (apply br_wf_dropbits; [exact Hwfb | lia]).
  apply (IH t tot
           {| cl_have := cl_have s + 1;
              cl_lens := zset (cl_lens s) (cl_have s) 0;
              cl_br := br_dropbits 1 b' |} Hwfd Ht).
  - cbn [cl_have cl_lens].
    intros j Hj.
    destruct (Z.eq_dec j (cl_have s)) as [->|Hne];
      [apply zset_same | rewrite zset_other by exact Hne; apply Hz; lia].
  - cbn [cl_have]. lia.
Qed.

(* ==========================================================================
   3.  List-window glue for the firstn/skipn split.
   ========================================================================== *)

Lemma zlens_firstn : forall n (l : list nat) i,
  0 <= i < Z.of_nat n ->
  zlens (firstn n l) i = zlens l i.
Proof.
  intros n l i Hi. unfold zlens.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hlt|Hge].
  - f_equal.
    rewrite <- (firstn_skipn n l) at 2.
    symmetry. apply app_nth1.
    rewrite length_firstn. lia.
  - rewrite !nth_overflow;
      [reflexivity | lia | rewrite length_firstn; lia].
Qed.

Lemma zlens_skipn : forall n (l : list nat) i,
  0 <= i ->
  zlens (skipn n l) i = zlens l (i + Z.of_nat n).
Proof.
  intros n l i Hi. unfold zlens.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length (skipn n l))) as [Hlt|Hge].
  - f_equal. symmetry.
    rewrite <- (firstn_skipn n l) at 1.
    rewrite app_nth2 by (rewrite length_firstn, length_skipn in *; lia).
    f_equal.
    rewrite length_firstn.
    rewrite length_skipn in Hlt. lia.
  - rewrite !nth_overflow;
      [reflexivity | rewrite length_skipn in Hge; lia | lia].
Qed.

Lemma in_firstn : forall (x : nat) n l, In x (firstn n l) -> In x l.
Proof.
  intros x n l H.
  rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H.
Qed.

Lemma in_skipn : forall (x : nat) n l, In x (skipn n l) -> In x l.
Proof.
  intros x n l H.
  rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H.
Qed.

Print Assumptions cl_loop_marker_zero.
Print Assumptions zlens_skipn.

(* ==========================================================================
   3b. Reader-alignment threading (v4, falsifier amendment): [br_haligned]
       through the two loops the GtBrAlign kit does not cover.  Placed
       BEFORE the Strategy block: these proofs cbn/destruct the loop
       bodies, which the stage lemmas later treat as opaque.
   ========================================================================== *)

Lemma ll_go_align : forall f ncode have lens b hv ls b1,
  br_wf b ->
  ll_go f ncode have lens b = LlOk hv ls b1 ->
  br_haligned b -> br_haligned b1.
Proof.
  induction f as [|f IH]; intros ncode have lens b hv ls b1 Hwf H Hal;
    cbn [ll_go] in H.
  - injection H as <- <- <-. exact Hal.
  - destruct (Z.ltb have ncode).
    + destruct (inf_nb 3 b) as [b'|b'] eqn:EN; [|discriminate].
      destruct (inf_nb_ok 3 b b' Hwf ltac:(lia) EN) as (_ & Hwf' & Hb3).
      assert (Hwfd : br_wf (br_dropbits 3 b'))
        by (apply br_wf_dropbits; [exact Hwf' | lia]).
      assert (Hald : br_haligned (br_dropbits 3 b')).
      { apply br_haligned_dropbits; [lia|].
        exact (inf_nb_align 3 b b' Hwf ltac:(lia) EN Hal). }
      exact (IH _ _ _ _ _ _ _ Hwfd H Hald).
    + injection H as <- <- <-. exact Hal.
Qed.

Lemma cl_loop_align : forall (cl : list nat) (T : ztbl) (nb : Z) n tot s,
  zr_codes_fetch_bridge cl T nb ->
  0 < nb <= 15 ->
  (forall i, 0 <= i < 2 ^ nb -> 0 <= c_bits (T i) <= nb) ->
  br_wf (cl_br s) ->
  br_haligned (cl_br s) ->
  match cl_loop n T nb tot s with
  | Some (ClDone s') => br_haligned (cl_br s')
  | _ => True
  end.
Proof.
  intros cl T nb.
  induction n as [|n IH]; intros tot s Hbr Hnb Hbits Hwf Hal;
    cbn [cl_loop]; [exact I|].
  unfold cl_step at 1.
  destruct (Z.leb tot (cl_have s)); [exact Hal|].
  unfold inf_fetch.
  pose proof (Hbr (cl_br s) Hwf) as HB.
  unfold inf_fetch in HB.
  match goal with
  | |- context [inf_fetch_go ?f T nb ?b] =>
      pose proof (zr_fetch_go_align T nb f b) as HFA;
      destruct (inf_fetch_go f T nb b) as [h b'|b'|] eqn:EF
  end; cbv beta iota; [| exact I | exact I].
  destruct HB as (Hsb & Hwf' & Hcb & Hcble & Hval & Hdec).
  specialize (HFA h b' Hwf Hnb Hbits eq_refl).
  destruct HFA as (Halimp & _ & _).
  pose proof (Halimp Hal) as Hal'.
  destruct (Z.ltb (c_val h) 16).
  { apply IH; try assumption.
    - cbn [cl_br]. apply br_wf_dropbits; [exact Hwf' | lia].
    - cbn [cl_br]. apply br_haligned_dropbits; [lia | exact Hal']. }
  cbv zeta.
  match goal with
  | |- context [inf_nb ?need b'] =>
      destruct (inf_nb need b') as [b2|b2] eqn:EN;
      [ destruct (inf_nb_ok need b' b2 Hwf'
                    ltac:(destruct (Z.eqb (c_val h) 16);
                          destruct (Z.eqb (c_val h) 17); lia) EN)
          as (Hsb2 & Hwf2 & Hbn2);
        pose proof (inf_nb_align need b' b2 Hwf'
                      ltac:(destruct (Z.eqb (c_val h) 16);
                            destruct (Z.eqb (c_val h) 17); lia) EN Hal')
          as Hal2
      | exact I ]
  end.
  assert (Hwfd : br_wf (br_dropbits (c_bits h) b2)).
  { apply br_wf_dropbits;
      [exact Hwf2
      | destruct (Z.eqb (c_val h) 16); destruct (Z.eqb (c_val h) 17); lia]. }
  assert (Hald : br_haligned (br_dropbits (c_bits h) b2)).
  { apply br_haligned_dropbits;
      [ destruct (Z.eqb (c_val h) 16); destruct (Z.eqb (c_val h) 17); lia
      | exact Hal2 ]. }
  assert (Hbd : br_bits (br_dropbits (c_bits h) b2)
                = br_bits b2 - c_bits h) by apply dropbits_bits.
  destruct (Z.eqb (c_val h) 16) eqn:E16; cbv beta iota.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota; [exact I|].
    destruct (Z.ltb tot (cl_have s + (3 + br_bits_of 2 (br_dropbits (c_bits h) b2))));
      cbv beta iota; [exact I|].
    apply IH; try assumption.
    - cbn [cl_br]. apply br_wf_dropbits; [exact Hwfd | apply Z.eqb_eq in E16; lia].
    - cbn [cl_br]. apply br_haligned_dropbits;
        [apply Z.eqb_eq in E16; lia | exact Hald]. }
  destruct (Z.eqb (c_val h) 17) eqn:E17; cbv beta iota.
  { destruct (Z.ltb tot (cl_have s + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))));
      cbv beta iota; [exact I|].
    apply IH; try assumption.
    - cbn [cl_br]. apply br_wf_dropbits;
        [exact Hwfd | apply Z.eqb_neq in E16; apply Z.eqb_eq in E17; lia].
    - cbn [cl_br]. apply br_haligned_dropbits;
        [apply Z.eqb_neq in E16; apply Z.eqb_eq in E17; lia | exact Hald]. }
  destruct (Z.ltb tot (cl_have s + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))));
    cbv beta iota; [exact I|].
  apply IH; try assumption.
  - cbn [cl_br]. apply br_wf_dropbits;
      [exact Hwfd | apply Z.eqb_neq in E16; apply Z.eqb_neq in E17; lia].
  - cbn [cl_br]. apply br_haligned_dropbits;
      [apply Z.eqb_neq in E16; apply Z.eqb_neq in E17; lia | exact Hald].
Qed.

(* Kernel-conversion oracle hints — measured (lane bisection ledger,
   2026-08-20): a Qed-time case split over an APPLICATION of one of these
   literal-fuel table constants costs ~450 s while the kernel's conversion
   oracle explores its body; [Strategy opaque] collapses it to
   milliseconds (finite level 1000 does NOT — measured).  Constants the
   proofs below explicitly [unfold] stay at a finite level ([Strategy
   opaque] blocks the unfold tactic — measured).  [it_model] is opaque
   for the stage lemmas (which destruct its applications) and drops to
   1000 at section 5, where the pure core unfolds it.  All [#[local]]:
   consumers' conversion oracles are unaffected. *)
#[local] Strategy opaque [it_pre it_model ll_go ll_zero cl_loop inf_fetch_go].
#[local] Strategy 1000 [inf_LENLENS inf_CODELENS inf_table].

(* ==========================================================================
   4.  STAGE LEMMAS (piece-lemma restructure, 2026-08-20).

       The monolithic endpoint proof's Qed replayed every in-hypothesis
       conversion over the ACCUMULATED composite-step state and capped two
       90-minute kernel runs (all tactics ~0s; the sink was Qed's
       conversion re-checking).  The repair, per the walled-tree
       discipline: cut at the machine's own named stage boundaries
       (inf_TABLE -> inf_LENLENS -> inf_CODELENS -> inf_LEN_), each stage
       lemma taking the incoming state ABSTRACT plus field equations, so
       projections never reduce into accumulated monsters and each Qed
       replays only its own short conversion chain.  States hand over
       EXISTENTIALLY with field-fact conjunctions; the endpoint chains
       the step equations by rewriting, never by conversion.
   ========================================================================== *)

(** Stage 1 — [M_TABLE]: the 14-bit header read and the TOO_MANY check. *)
Lemma tbl_stage1 : forall c q,
  br_wf (q_br q) ->
  h_mode (s_hdr (q_st q)) = M_TABLE ->
  (exists b, inf_step c q = InfLeave (qset_br q b))
  \/ (exists qb, inf_step c q = InfCont qb /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists b qA,
        inf_nb 14 (q_br q) = NBOk b
        /\ br_bits_of 5 b + 257 <= 286
        /\ br_bits_of 5 (br_dropbits 5 b) + 1 <= 30
        /\ inf_step c q = inf_LENLENS c qA
        /\ q_br qA = br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b))
        /\ b_ncode (s_bld (q_st qA))
           = br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b)) + 4
        /\ b_nlen (s_bld (q_st qA)) = br_bits_of 5 b + 257
        /\ b_ndist (s_bld (q_st qA)) = br_bits_of 5 (br_dropbits 5 b) + 1
        /\ b_have (s_bld (q_st qA)) = 0
        /\ t_codes (s_tab (q_st qA)) = t_codes (s_tab (q_st q))
        /\ q_ob qA = q_ob q
        /\ h_last (s_hdr (q_st qA)) = h_last (s_hdr (q_st q))
        /\ q_in qA = q_in q
        /\ q_out qA = q_out q
        /\ w_wsize (s_win (q_st qA)) = w_wsize (s_win (q_st q))
        /\ h_wrap (s_hdr (q_st qA)) = h_wrap (s_hdr (q_st q))
        /\ h_flags (s_hdr (q_st qA)) = h_flags (s_hdr (q_st q))
        (* amendment #11: h_check/h_total frame conjuncts — carrier
           q7-decode; g1 census; q6 pre-ruling;
           #10 shape *)
        /\ h_check (s_hdr (q_st qA)) = h_check (s_hdr (q_st q))
        /\ h_total (s_hdr (q_st qA)) = h_total (s_hdr (q_st q))
        /\ w_whave (s_win (q_st qA)) = w_whave (s_win (q_st q))
        /\ t_sane (s_tab (q_st qA)) = t_sane (s_tab (q_st q))
        /\ q_ret qA = q_ret q).
Proof.
  intros c q Hwf Hm.
  assert (Hqm : q_mode q = M_TABLE) by (unfold q_mode; exact Hm).
  assert (Hstep : inf_step c q = inf_TABLE c q)
    by (unfold inf_step; rewrite Hqm; reflexivity).
  unfold inf_TABLE in Hstep.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:E14; cbv beta iota zeta in Hstep.
  2:{ left. exists b. exact Hstep. }
  match type of Hstep with
  | context [if ?chk then _ else _] => destruct chk eqn:Echk
  end; cbv beta iota in Hstep.
  { right. left. eexists. split; [exact Hstep | reflexivity]. }
  apply orb_false_elim in Echk. destruct Echk as (Echk1 & Echk2).
  apply Z.ltb_ge in Echk1. apply Z.ltb_ge in Echk2.
  right. right.
  match type of Hstep with
  | _ = inf_LENLENS c ?X => exists b, X
  end.
  split; [reflexivity|].
  split; [exact Echk1|].
  split; [exact Echk2|].
  split; [exact Hstep|].
  repeat split; reflexivity.
Qed.

(** Stage 2 — [LENLENS]: the 19 3-bit reads, the zero fill, and the CODES
    build, over an ABSTRACT incoming state (projections of [qA] never
    reduce; the outgoing state's field facts are each one small
    conversion where the state is concrete-over-[qA]). *)
Lemma ll_stage2 : forall c qA,
  br_wf (q_br qA) ->
  br_haligned (q_br qA) ->
  b_have (s_bld (q_st qA)) = 0 ->
  0 <= b_ncode (s_bld (q_st qA)) <= 19 ->
  (exists qX, inf_LENLENS c qA = InfLeave qX /\ q_ret qX = q_ret qA)
  \/ inf_LENLENS c qA = InfFuel
  \/ (exists qb, inf_LENLENS c qA = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists b4 (ls2 : zarr) (vals : list nat) o qB,
        br_wf b4
        /\ br_haligned b4
        /\ read_3bit_vals (Z.to_nat (b_ncode (s_bld (q_st qA))))
             (br_stream (q_br qA)) = Some (vals, br_stream b4)
        /\ arr_eq_on ls2 (zlens (scatter_cl vals)) 0 19
        /\ it_model CT_CODES ls2 19 7
             (fun i => t_codes (s_tab (q_st qA)) (0 + i)) = Some o
        /\ o_ret o = 0
        /\ inf_LENLENS c qA = inf_CODELENS c qB
        /\ q_br qB = b4
        /\ b_have (s_bld (q_st qB)) = 0
        /\ b_nlen (s_bld (q_st qB)) = b_nlen (s_bld (q_st qA))
        /\ b_ndist (s_bld (q_st qB)) = b_ndist (s_bld (q_st qA))
        /\ t_codes (s_tab (q_st qB))
           = codes_wb (t_codes (s_tab (q_st qA))) 0 (o_tbl o)
        /\ t_lencode (s_tab (q_st qB)) = TRcodes 0
        /\ t_lenbits (s_tab (q_st qB)) = o_bits o
        /\ tbl_of (q_st qB) (t_lencode (s_tab (q_st qB)))
           = (fun i => codes_wb (t_codes (s_tab (q_st qA))) 0 (o_tbl o) (0 + i))
        /\ q_ob qB = q_ob qA
        /\ h_last (s_hdr (q_st qB)) = h_last (s_hdr (q_st qA))
        /\ q_in qB = q_in qA
        /\ q_out qB = q_out qA
        /\ w_wsize (s_win (q_st qB)) = w_wsize (s_win (q_st qA))
        /\ h_wrap (s_hdr (q_st qB)) = h_wrap (s_hdr (q_st qA))
        /\ h_flags (s_hdr (q_st qB)) = h_flags (s_hdr (q_st qA))
        (* amendment #11: h_check/h_total frame conjuncts — carrier
           q7-decode; g1 census; q6 pre-ruling;
           #10 shape *)
        /\ h_check (s_hdr (q_st qB)) = h_check (s_hdr (q_st qA))
        /\ h_total (s_hdr (q_st qB)) = h_total (s_hdr (q_st qA))
        /\ w_whave (s_win (q_st qB)) = w_whave (s_win (q_st qA))
        /\ t_sane (s_tab (q_st qB)) = t_sane (s_tab (q_st qA))
        /\ q_ret qB = 0).
Proof.
  intros c qA HwfA HalA Hhv Hnc.
  remember (inf_LENLENS c qA) as RES eqn:Hstep.
  unfold inf_LENLENS in Hstep. cbv beta zeta in Hstep.
  rewrite Hhv in Hstep.
  match type of Hstep with
  | context [ll_go 19 ?nc 0 ?ls ?bb] =>
      pose proof (ll_go_agree 19 nc 0 ls bb HwfA ltac:(lia) ltac:(lia)
                    ltac:(lia)) as HLL;
      destruct (ll_go 19 nc 0 ls bb) as [hv1 ls1 b4|hv1 ls1 b4] eqn:Ell
  end; cbv beta iota in Hstep.
  2:{ left. eexists. split; [exact Hstep | reflexivity]. }
  destruct HLL as (Hhv1 & Hwfb4 & vals & Hrd3 & Hlenv & Hvalk & Hfrv).
  destruct (ll_zero 19 hv1 ls1) as [hv2 ls2] eqn:EZ.
  cbv beta iota in Hstep.
  subst hv1.
  destruct (ll_zero_agree 19 (b_ncode (s_bld (q_st qA))) ls1 hv2 ls2
              ltac:(lia) ltac:(lia) EZ) as (Hhv2 & Hzk & Hzfr).
  replace (b_ncode (s_bld (q_st qA)) - 0)
    with (b_ncode (s_bld (q_st qA))) in Hrd3 by lia.
  replace (b_ncode (s_bld (q_st qA)) - 0)
    with (b_ncode (s_bld (q_st qA))) in Hlenv by lia.
  (* the LENLENS array IS the scattered list *)
  assert (Hwin19 : arr_eq_on ls2 (zlens (scatter_cl vals)) 0 19).
  { intros j Hj.
    apply (scatter_tie vals (b_ncode (s_bld (q_st qA))) ls2
             ltac:(lia)); [| | | lia].
    - exact Hlenv.
    - intros k Hk.
      rewrite (Hzfr (inf_order k))
        by (intros k' Hk' He;
            pose proof (inf_order_inj k k' ltac:(lia) ltac:(lia) He); lia).
      specialize (Hvalk k ltac:(lia)).
      replace (0 + k) with k in Hvalk by lia.
      exact Hvalk.
    - intros k Hk. apply Hzk. lia. }
  assert (Halb4 : br_haligned b4)
    by (exact (ll_go_align 19 _ 0 _ _ _ _ _ HwfA Ell HalA)).
  unfold inf_table in Hstep.
  cbn [set_lens set_have s_tab s_bld q_st] in Hstep.
  match type of Hstep with
  | context [it_model CT_CODES ?l ?cds ?rt ?t0] =>
      destruct (it_model CT_CODES l cds rt t0) as [o|] eqn:EMC
  end; cbv beta iota in Hstep.
  2:{ right. left. exact Hstep. }
  destruct (Z.eqb (o_ret o) 0) eqn:Erc;
    cbn [negb] in Hstep; cbv beta iota in Hstep.
  2:{ right. right. left. eexists. split; [exact Hstep | reflexivity]. }
  apply Z.eqb_eq in Erc.
  right. right. right.
  match type of Hstep with
  | _ = inf_CODELENS c ?X => exists b4, ls2, vals, o, X
  end.
  split; [exact Hwfb4|].
  split; [exact Halb4|].
  split; [exact Hrd3|].
  split; [exact Hwin19|].
  split; [exact EMC|].
  split; [exact Erc|].
  split; [exact Hstep|].
  repeat split. all: first [reflexivity | exact Erc].
Qed.

(** Stage 3a — [CODELENS] over the accepted-EMPTY (two-marker) CODES
    table: every decoded length is zero and the NO-EOB check absorbs. *)
Lemma cdl_stage3_empty : forall c qB (T : ztbl),
  br_wf (q_br qB) ->
  b_have (s_bld (q_st qB)) = 0 ->
  256 < b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)) ->
  t_lenbits (s_tab (q_st qB)) = 1 ->
  tbl_of (q_st qB) (t_lencode (s_tab (q_st qB))) = T ->
  (forall i, 0 <= i < 2 -> T i = mkCodeT 64 1 0) ->
  inf_CODELENS c qB = InfFuel
  \/ (exists qb, inf_CODELENS c qB = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists qX, inf_CODELENS c qB = InfLeave qX /\ q_ret qX = q_ret qB).
Proof.
  intros c qB T HwfB Hhv H256 Hnb HT Hmk.
  remember (inf_CODELENS c qB) as RES eqn:Hstep.
  unfold inf_CODELENS in Hstep. cbv beta zeta in Hstep.
  rewrite HT, Hnb, Hhv in Hstep.
  match type of Hstep with
  | context [cl_loop ?n ?t 1 ?tot ?s0] =>
      pose proof (cl_loop_marker_zero n t tot s0) as HMZ;
      destruct (cl_loop n t 1 tot s0) as [[s'|s'|s' m'|s'|]|] eqn:ECL
  end; cbv beta iota in Hstep.
  - left. exact Hstep.
  - (* ClDone: all-zero lens, NO-EOB *)
    specialize (HMZ ltac:(exact HwfB) Hmk
                  ltac:(intros j Hj; cbn [cl_have] in Hj; lia)
                  ltac:(cbn [cl_have]; lia)).
    destruct HMZ as (Hge & Hz0).
    replace (Z.eqb (cl_lens s' 256) 0) with true in Hstep
      by (symmetry; apply Z.eqb_eq; apply Hz0; lia).
    cbv beta iota in Hstep.
    right. left. eexists. split; [exact Hstep | reflexivity].
  - right. left. eexists. split; [exact Hstep | reflexivity].
  - right. right. eexists. split; [exact Hstep | reflexivity].
  - left. exact Hstep.
  - left. exact Hstep.
Qed.

(** Stage 3b — [CODELENS] over an accepted LIVE CODES table (the fetch
    bridge): the CL walk decodes [read_lengths], the LENS and DISTS
    builds install, and the step falls through into [inf_LEN_].  The
    table function, its root bits, and the codes array come in as
    EQUATION premises ([T]/[nb0]/[cs0]) so every export is spelled at
    the caller's vocabulary. *)
Lemma cdl_stage3 : forall c qB (cs0 T : ztbl) (nb0 : Z) (cl : list nat),
  zr_cflush_ok c ->
  br_wf (q_br qB) ->
  br_haligned (q_br qB) ->
  b_have (s_bld (q_st qB)) = 0 ->
  0 <= b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)) ->
  t_codes (s_tab (q_st qB)) = cs0 ->
  t_lenbits (s_tab (q_st qB)) = nb0 ->
  tbl_of (q_st qB) (t_lencode (s_tab (q_st qB))) = T ->
  0 < nb0 <= 15 ->
  (forall i, 0 <= i < 2 ^ nb0 -> 0 <= c_bits (T i) <= nb0) ->
  zr_codes_fetch_bridge cl T nb0 ->
  inf_CODELENS c qB = InfFuel
  \/ (exists qb, inf_CODELENS c qB = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists qX, inf_CODELENS c qB = InfLeave qX /\ q_ret qX = q_ret qB)
  \/ (exists s' (ls : list nat) o1 o2 qL,
        read_lengths cl
          (Z.to_nat (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB))))
          (br_stream (q_br qB))
        = Some (ls, br_stream (cl_br s'))
        /\ cl_have s' = Z.of_nat (length ls)
        /\ b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)) <= cl_have s'
        /\ arr_eq_on (cl_lens s') (zlens ls) 0 (cl_have s')
        /\ br_wf (cl_br s')
        /\ br_haligned (cl_br s')
        /\ (forall x, In x ls -> (x <= 15)%nat)
        /\ cl_lens s' 256 <> 0
        /\ it_model CT_LENS (cl_lens s') (b_nlen (s_bld (q_st qB))) 9
             (fun i => cs0 (0 + i)) = Some o1
        /\ o_ret o1 = 0
        /\ it_model CT_DISTS
             (fun i => cl_lens s' (i + b_nlen (s_bld (q_st qB))))
             (b_ndist (s_bld (q_st qB))) 6
             (fun i => codes_wb cs0 0 (o_tbl o1) ((0 + o_used o1) + i))
           = Some o2
        /\ o_ret o2 = 0
        /\ inf_CODELENS c qB = inf_LEN_ qL
        /\ t_lencode (s_tab (q_st qL)) = TRcodes 0
        /\ t_lenbits (s_tab (q_st qL)) = o_bits o1
        /\ t_distcode (s_tab (q_st qL)) = TRcodes (0 + o_used o1)
        /\ t_distbits (s_tab (q_st qL)) = o_bits o2
        /\ t_codes (s_tab (q_st qL))
           = codes_wb (codes_wb cs0 0 (o_tbl o1)) (0 + o_used o1) (o_tbl o2)
        /\ q_br qL = cl_br s'
        /\ q_ob qL = q_ob qB
        /\ h_last (s_hdr (q_st qL)) = h_last (s_hdr (q_st qB))
        /\ q_in qL = q_in qB
        /\ q_out qL = q_out qB
        /\ w_wsize (s_win (q_st qL)) = w_wsize (s_win (q_st qB))
        /\ h_wrap (s_hdr (q_st qL)) = h_wrap (s_hdr (q_st qB))
        /\ h_flags (s_hdr (q_st qL)) = h_flags (s_hdr (q_st qB))
        (* amendment #11: h_check/h_total frame conjuncts — carrier
           q7-decode; g1 census; q6 pre-ruling;
           #10 shape *)
        /\ h_check (s_hdr (q_st qL)) = h_check (s_hdr (q_st qB))
        /\ h_total (s_hdr (q_st qL)) = h_total (s_hdr (q_st qB))
        /\ w_whave (s_win (q_st qL)) = w_whave (s_win (q_st qB))
        /\ t_sane (s_tab (q_st qL)) = t_sane (s_tab (q_st qB))
        /\ q_ret qL = o_ret o2).
Proof.
  intros c qB cs0 T nb0 cl Hfl HwfB HalB Hhv Htot0 Hcs Hnb HT Hnbb Hbits Hbr.
  remember (inf_CODELENS c qB) as RES eqn:Hstep.
  unfold inf_CODELENS in Hstep. cbv beta zeta in Hstep.
  rewrite HT, Hnb, Hhv in Hstep.
  match type of Hstep with
  | context [cl_loop ?n ?t ?nb ?tot ?s0] =>
      pose proof (cl_loop_read_lengths cl t nb tot s0 Hbr
                    ltac:(exact HwfB) ltac:(reflexivity) ltac:(lia)) as HCL;
      pose proof (cl_loop_align cl t nb n tot s0 Hbr Hnbb Hbits
                    ltac:(exact HwfB) ltac:(exact HalB)) as HALW;
      destruct (cl_loop n t nb tot s0) as [[s'|s'|s' m'|s'|]|] eqn:ECL
  end; cbv beta iota in Hstep.
  - left. exact Hstep.
  - (* ClDone: the decoded lengths *)
    destruct HCL as (ls & Hrdl & Hhave & Htot & Hwin' & HwfS & Hbnd15).
    cbn [cl_br cl_have cl_lens] in Hrdl.
    destruct (Z.eqb (cl_lens s' 256) 0) eqn:Eeob; cbv beta iota in Hstep.
    { right. left. eexists. split; [exact Hstep | reflexivity]. }
    apply Z.eqb_neq in Eeob.
    unfold inf_table in Hstep.
    cbn [q_st qset_st qset_br qset_ret set_lens set_have set_codes set_next
         set_lenbits set_lencode set_distbits set_distcode s_tab s_bld
         t_codes] in Hstep.
    rewrite Hcs in Hstep.
    match type of Hstep with
    | context [it_model CT_LENS ?l ?cds ?rt ?t0] =>
        destruct (it_model CT_LENS l cds rt t0) as [o1|] eqn:EML
    end; cbv beta iota in Hstep.
    2:{ left. exact Hstep. }
    destruct (Z.eqb (o_ret o1) 0) eqn:Erl;
      cbn [negb] in Hstep; cbv beta iota in Hstep.
    2:{ right. left. eexists. split; [exact Hstep | reflexivity]. }
    apply Z.eqb_eq in Erl.
    match type of Hstep with
    | context [it_model CT_DISTS ?l ?cds ?rt ?t0] =>
        destruct (it_model CT_DISTS l cds rt t0) as [o2|] eqn:EMD
    end; cbv beta iota in Hstep.
    2:{ left. exact Hstep. }
    destruct (Z.eqb (o_ret o2) 0) eqn:Erd;
      cbn [negb] in Hstep; cbv beta iota in Hstep.
    2:{ right. left. eexists. split; [exact Hstep | reflexivity]. }
    apply Z.eqb_eq in Erd.
    rewrite (zr_eqb_nT c Hfl) in Hstep. cbv beta iota in Hstep.
    right. right. right.
    match type of Hstep with
    | _ = inf_LEN_ ?X => exists s', ls, o1, o2, X
    end.
    split; [exact Hrdl|].
    split; [exact Hhave|].
    split; [exact Htot|].
    split; [exact Hwin'|].
    split; [exact HwfS|].
    split; [exact HALW|].
    split; [exact Hbnd15|].
    split; [exact Eeob|].
    split; [exact EML|].
    split; [exact Erl|].
    split; [exact EMD|].
    split; [exact Erd|].
    split; [exact Hstep|].
    repeat split; reflexivity.
  - right. left. eexists. split; [exact Hstep | reflexivity].
  - right. right. left. eexists. split; [exact Hstep | reflexivity].
  - left. exact Hstep.
  - left. exact Hstep.
Qed.

Print Assumptions ll_stage2.
Print Assumptions cdl_stage3.

(* The pure core and endpoint [unfold it_model] (acceptance
   contradictions) and never destruct its applications — re-level. *)
#[local] Strategy 1000 [it_model].

(* ==========================================================================
   5.  THE PURE CORE — the declarative package, state-free: header reads +
       CL decode + acceptance equations IN; [decode_dynamic_tables]
       agreement + wf/lens-ext/pre payloads OUT.  No machine state occurs
       anywhere in this lemma, so its Qed replays only list/arith
       conversions.
   ========================================================================== *)

Lemma tbl_pure_core :
  forall (b0 b b4 : BR) (cs : ztbl) (vals ls : list nat) (ls2 : zarr)
         (o : ItOut) (s' : ClSt) (o1 o2 : ItOut),
  read_bits 5%nat (br_stream b0)
    = Some (br_bits_of 5 b, br_stream (br_dropbits 5 b)) ->
  read_bits 5%nat (br_stream (br_dropbits 5 b))
    = Some (br_bits_of 5 (br_dropbits 5 b),
            br_stream (br_dropbits 5 (br_dropbits 5 b))) ->
  read_bits 4%nat (br_stream (br_dropbits 5 (br_dropbits 5 b)))
    = Some (br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b)),
            br_stream (br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b)))) ->
  0 <= br_bits_of 5 b < 32 ->
  0 <= br_bits_of 5 (br_dropbits 5 b) < 32 ->
  0 <= br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b)) < 16 ->
  read_3bit_vals
    (Z.to_nat (br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b)) + 4))
    (br_stream (br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b))))
    = Some (vals, br_stream b4) ->
  arr_eq_on ls2 (zlens (scatter_cl vals)) 0 19 ->
  it_model CT_CODES ls2 19 7 (fun i => cs (0 + i)) = Some o ->
  o_ret o = 0 ->
  read_lengths (scatter_cl vals)
    (Z.to_nat (br_bits_of 5 b + 257 + (br_bits_of 5 (br_dropbits 5 b) + 1)))
    (br_stream b4)
    = Some (ls, br_stream (cl_br s')) ->
  cl_have s' = Z.of_nat (length ls) ->
  br_bits_of 5 b + 257 + (br_bits_of 5 (br_dropbits 5 b) + 1) <= cl_have s' ->
  arr_eq_on (cl_lens s') (zlens ls) 0 (cl_have s') ->
  (forall x, In x ls -> (x <= 15)%nat) ->
  cl_lens s' 256 <> 0 ->
  it_model CT_LENS (cl_lens s') (br_bits_of 5 b + 257) 9
    (fun i => codes_wb cs 0 (o_tbl o) (0 + i)) = Some o1 ->
  o_ret o1 = 0 ->
  it_model CT_DISTS (fun i => cl_lens s' (i + (br_bits_of 5 b + 257)))
    (br_bits_of 5 (br_dropbits 5 b) + 1) 6
    (fun i => codes_wb (codes_wb cs 0 (o_tbl o)) 0 (o_tbl o1)
                ((0 + o_used o1) + i)) = Some o2 ->
  o_ret o2 = 0 ->
  exists nlit,
    Z.of_nat nlit = br_bits_of 5 b + 257
    /\ decode_dynamic_tables (br_stream b0)
       = Some (firstn nlit ls, skipn nlit ls, br_stream (cl_br s'))
    /\ Z.of_nat (length (firstn nlit ls)) = br_bits_of 5 b + 257
    /\ Z.of_nat (length (skipn nlit ls))
       = br_bits_of 5 (br_dropbits 5 b) + 1
    /\ it_wf CT_LENS (zlens ls) (br_bits_of 5 b + 257) 9
    /\ it_model CT_LENS (zlens ls) (br_bits_of 5 b + 257) 9
         (fun i => codes_wb cs 0 (o_tbl o) (0 + i)) = Some o1
    /\ it_wf CT_DISTS (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
         (br_bits_of 5 (br_dropbits 5 b) + 1) 6
    /\ it_model CT_DISTS (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
         (br_bits_of 5 (br_dropbits 5 b) + 1) 6
         (fun i => codes_wb (codes_wb cs 0 (o_tbl o)) 0 (o_tbl o1)
                     ((0 + o_used o1) + i)) = Some o2
    /\ (exists cL stL,
          it_pre CT_LENS (zlens ls) (br_bits_of 5 b + 257) 9
            (fun i => codes_wb cs 0 (o_tbl o) (0 + i)) = PreGo cL stL)
    /\ ((exists cD stD,
           it_pre CT_DISTS (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
             (br_bits_of 5 (br_dropbits 5 b) + 1) 6
             (fun i => codes_wb (codes_wb cs 0 (o_tbl o)) 0 (o_tbl o1)
                         ((0 + o_used o1) + i)) = PreGo cD stD)
        \/ (exists tD,
           it_pre CT_DISTS (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
             (br_bits_of 5 (br_dropbits 5 b) + 1) 6
             (fun i => codes_wb (codes_wb cs 0 (o_tbl o)) 0 (o_tbl o1)
                         ((0 + o_used o1) + i)) = PreEmpty tD)).
Proof.
  intros b0 b b4 cs vals ls ls2 o s' o1 o2
         HrdA HrdB HrdC Hh1 Hh2 Hh3 Hrd3 Hwin19 EMC Erc
         Hrdl Hhave Htot Hwin' Hbnd15 Eeob EML Erl EMD Erd.
  pose proof (read_lengths_length _ _ _ _ _ Hrdl) as Hlsl.
  set (nlit := (Z.to_nat (br_bits_of 5 b) + 257)%nat).
  assert (Hnlit : Z.of_nat nlit = br_bits_of 5 b + 257)
    by (unfold nlit; lia).
  assert (Hlenls : Z.of_nat (length ls)
                   = br_bits_of 5 b + 257
                     + (br_bits_of 5 (br_dropbits 5 b) + 1))
    by (rewrite Hlsl; lia).
  assert (Hlitlen : Z.of_nat (length (firstn nlit ls))
                    = br_bits_of 5 b + 257)
    by (rewrite length_firstn; lia).
  assert (Hdstlen : Z.of_nat (length (skipn nlit ls))
                    = br_bits_of 5 (br_dropbits 5 b) + 1)
    by (rewrite length_skipn; lia).
  (* the machine window, split across the two halves *)
  assert (HwinL : arr_eq_on (cl_lens s') (zlens (firstn nlit ls)) 0
                    (br_bits_of 5 b + 257)).
  { intros i Hi.
    rewrite (zlens_firstn nlit ls i ltac:(lia)).
    apply Hwin'. lia. }
  assert (HwinD : arr_eq_on (fun i => cl_lens s' (i + (br_bits_of 5 b + 257)))
                    (zlens (skipn nlit ls)) 0
                    (br_bits_of 5 (br_dropbits 5 b) + 1)).
  { intros i Hi. cbv beta.
    rewrite (zlens_skipn nlit ls i ltac:(lia)).
    rewrite Hnlit.
    apply Hwin'. lia. }
  (* the full-list window, for the exhibited DynBuild *)
  assert (HwinF : arr_eq_on (cl_lens s') (zlens ls) 0
                    (br_bits_of 5 b + 257)).
  { intros i Hi. apply Hwin'. lia. }
  assert (HwinFD : arr_eq_on (fun i => cl_lens s' (i + (br_bits_of 5 b + 257)))
                     (fun i => zlens ls (i + (br_bits_of 5 b + 257))) 0
                     (br_bits_of 5 (br_dropbits 5 b) + 1)).
  { intros i Hi. cbv beta. apply Hwin'. lia. }
  (* acceptance validity at both bounds *)
  assert (Hcl_len : length (scatter_cl vals) = 19%nat)
    by apply scatter_cl_length.
  assert (Hcl_bnd : forall x, In x (scatter_cl vals) -> (x <= 7)%nat).
  { apply scatter_cl_bound.
    exact (read_3bit_vals_bound _ _ _ _ Hrd3). }
  assert (Hv7 : valid_lengths_b (scatter_cl vals) 7%nat = true).
  { eapply (accept_valid CT_CODES ls2 (scatter_cl vals) 19 7 _ o 7%nat);
      [rewrite Hcl_len; reflexivity | exact Hwin19 | exact Hcl_bnd
      | lia | exact EMC | exact Erc]. }
  assert (HvL : valid_lengths_b (firstn nlit ls) 15%nat = true).
  { eapply (accept_valid CT_LENS (cl_lens s') (firstn nlit ls)
              (br_bits_of 5 b + 257) 9 _ o1 15%nat);
      [lia | exact HwinL
      | intros x Hx; exact (Hbnd15 x (in_firstn x nlit ls Hx))
      | lia | exact EML | exact Erl]. }
  assert (HvD : valid_lengths_b (skipn nlit ls) 15%nat = true).
  { eapply (accept_valid CT_DISTS
              (fun i => cl_lens s' (i + (br_bits_of 5 b + 257)))
              (skipn nlit ls)
              (br_bits_of 5 (br_dropbits 5 b) + 1) 6 _ o2 15%nat);
      [lia | exact HwinD
      | intros x Hx; exact (Hbnd15 x (in_skipn x nlit ls Hx))
      | lia | exact EMD | exact Erd]. }
  (* the declarative header decode, assembled *)
  assert (Hdec : decode_dynamic_tables (br_stream b0)
                 = Some (firstn nlit ls, skipn nlit ls,
                         br_stream (cl_br s'))).
  { unfold decode_dynamic_tables.
    rewrite HrdA. cbv beta iota.
    rewrite HrdB. cbv beta iota.
    rewrite HrdC. cbv beta iota.
    unfold read_cl_lengths.
    replace (Z.to_nat (br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b)))
             + 4)%nat
      with (Z.to_nat (br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b))
                      + 4)) by lia.
    rewrite Hrd3. cbv beta iota.
    rewrite Hv7. cbv beta iota.
    replace ((Z.to_nat (br_bits_of 5 b) + 257)
             + (Z.to_nat (br_bits_of 5 (br_dropbits 5 b)) + 1))%nat
      with (Z.to_nat (br_bits_of 5 b + 257
                      + (br_bits_of 5 (br_dropbits 5 b) + 1))) by lia.
    rewrite Hrdl. cbv beta iota.
    fold nlit.
    rewrite HvL, HvD. cbn [andb]. cbv beta iota.
    reflexivity. }
  (* the build pair at the LIST spelling via the lens ext *)
  rewrite (it_model_lens_ext CT_LENS (cl_lens s') (zlens ls)
             (br_bits_of 5 b + 257) 9 _ ltac:(lia) HwinF) in EML.
  rewrite (it_model_lens_ext CT_DISTS
             (fun i => cl_lens s' (i + (br_bits_of 5 b + 257)))
             (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
             (br_bits_of 5 (br_dropbits 5 b) + 1) 6 _ ltac:(lia) HwinFD)
    in EMD.
  (* it_wf for both builds *)
  assert (HwfL : it_wf CT_LENS (zlens ls) (br_bits_of 5 b + 257) 9).
  { split; [lia|]. split.
    { intros i Hi. unfold zlens.
      split; [lia|].
      assert (Hin : In (nth (Z.to_nat i) ls 0%nat) ls)
        by (apply nth_In; lia).
      pose proof (Hbnd15 _ Hin). unfold MAXBITS. lia. }
    split; [unfold MAXBITS; lia|].
    right. left. split; [reflexivity | lia]. }
  assert (HwfD : it_wf CT_DISTS (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
                   (br_bits_of 5 (br_dropbits 5 b) + 1) 6).
  { split; [lia|]. split.
    { intros i Hi. cbv beta. unfold zlens.
      split; [lia|].
      assert (Hin : In (nth (Z.to_nat (i + (br_bits_of 5 b + 257))) ls 0%nat)
                      ls)
        by (apply nth_In; lia).
      pose proof (Hbnd15 _ Hin). unfold MAXBITS. lia. }
    split; [unfold MAXBITS; lia|].
    right. right. split; [reflexivity | lia]. }
  (* LENS pre-state is PreGo: the EOB symbol keeps findmax alive *)
  assert (Heobls : zlens ls 256 <> 0).
  { rewrite <- (Hwin' 256 ltac:(lia)). exact Eeob. }
  assert (HpreL : exists cL stL,
             it_pre CT_LENS (zlens ls) (br_bits_of 5 b + 257) 9
               (fun i => codes_wb cs 0 (o_tbl o) (0 + i))
             = PreGo cL stL).
  { match type of EML with
    | it_model _ _ _ _ ?t0 = _ =>
        destruct (it_pre CT_LENS (zlens ls) (br_bits_of 5 b + 257) 9 t0)
          as [ |tE| |cL stL] eqn:EPL
    end.
    - exfalso. unfold it_model in EML. rewrite EPL in EML.
      injection EML as <-. cbn [o_ret] in Erl. lia.
    - exfalso.
      pose proof (it_pre_empty_findmax _ _ _ _ _ _ EPL) as Hfz.
      assert (Hz256 : zlens ls 256 = 0).
      { pose proof (it_findmax_zero 15%nat MAXBITS _
                      ltac:(unfold MAXBITS; lia)
                      ltac:(unfold MAXBITS; lia) Hfz) as Hcz.
        destruct (Z.eq_dec (zlens ls 256) 0) as [He|Hne]; [exact He|].
        exfalso.
        set (v := nth (Z.to_nat 256) ls 0%nat).
        assert (Hvin : In v ls) by (apply nth_In; unfold v; lia).
        pose proof (Hbnd15 v Hvin) as Hv15.
        assert (Hvpos : (0 < v)%nat)
          by (unfold zlens in Hne; fold v in Hne; lia).
        pose proof (counts_of_it_count_agree (zlens ls)
                      (br_bits_of 5 b + 257) (firstn nlit ls) 15%nat
                      ltac:(lia)
                      ltac:(intros i Hi;
                            rewrite (zlens_firstn nlit ls i ltac:(lia));
                            reflexivity)
                      v ltac:(lia)) as Hcv.
        unfold it_cnt0 in Hcv.
        rewrite (Hcz (Z.of_nat v) ltac:(unfold MAXBITS; lia)) in Hcv.
        assert (Hvin' : In v (firstn nlit ls)).
        { assert (H256 : nth 256 (firstn nlit ls) 0%nat = v).
          { pose proof (zlens_firstn nlit ls 256 ltac:(lia)) as Hzf.
            unfold zlens in Hzf.
            change (Z.to_nat 256) with 256%nat in Hzf.
            unfold v. change (Z.to_nat 256) with 256%nat. lia. }
          rewrite <- H256. apply nth_In.
          rewrite length_firstn. lia. }
        unfold count_len in Hcv.
        pose proof (proj1 (count_occ_In Nat.eq_dec (firstn nlit ls) v)
                      Hvin').
        lia. }
      lia.
    - exfalso. unfold it_model in EML. rewrite EPL in EML.
      injection EML as <-. cbn [o_ret] in Erl. lia.
    - exists cL, stL. first [exact EPL | reflexivity]. }
  (* DISTS pre-state: PreGo or accepted-EMPTY *)
  assert (HpreD : (exists cD stD,
             it_pre CT_DISTS
               (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
               (br_bits_of 5 (br_dropbits 5 b) + 1) 6
               (fun i => codes_wb (codes_wb cs 0 (o_tbl o)) 0 (o_tbl o1)
                           ((0 + o_used o1) + i))
             = PreGo cD stD)
            \/ (exists tD,
             it_pre CT_DISTS
               (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
               (br_bits_of 5 (br_dropbits 5 b) + 1) 6
               (fun i => codes_wb (codes_wb cs 0 (o_tbl o)) 0 (o_tbl o1)
                           ((0 + o_used o1) + i))
             = PreEmpty tD)).
  { match type of EMD with
    | it_model _ _ _ _ ?t0 = _ =>
        destruct (it_pre CT_DISTS
                    (fun i => zlens ls (i + (br_bits_of 5 b + 257)))
                    (br_bits_of 5 (br_dropbits 5 b) + 1) 6 t0)
          as [ |tD| |cD stD] eqn:EPD
    end.
    - exfalso. unfold it_model in EMD. rewrite EPD in EMD.
      injection EMD as <-. cbn [o_ret] in Erd. lia.
    - right. exists tD. first [exact EPD | reflexivity].
    - exfalso. unfold it_model in EMD. rewrite EPD in EMD.
      injection EMD as <-. cbn [o_ret] in Erd. lia.
    - left. exists cD, stD. first [exact EPD | reflexivity]. }
  exists nlit.
  split; [exact Hnlit|].
  split; [exact Hdec|].
  split; [exact Hlitlen|].
  split; [exact Hdstlen|].
  split; [exact HwfL|].
  split; [exact EML|].
  split; [exact HwfD|].
  split; [exact EMD|].
  split; [exact HpreL|].
  exact HpreD.
Qed.

(* ==========================================================================
   6.  THE ENDPOINT — thin assembly: stage equations chained by rewriting,
       declarative payload from the pure core.  No conversion here ever
       touches a composite state.
   ========================================================================== *)

Theorem zr_table_chain_holds : ZrCodesFetchRes -> ZrTableChain.
Proof.
  intros Hres c q Hfl Hwf Hal Hput Hm Hq0.
  destruct (tbl_stage1 c q Hwf Hm) as
    [ (b & HL1)
    | [ (qb & HB1 & HBm1)
    | (b & qA & E14 & Hch1 & Hch2 & Hstep1 & HqbrA & Hbnc & Hbnl & Hbnd
       & HbhvA & HtcA & HobA & HhlA & HinA & HoutA & HwszA
       & HwrA & HfgA & HckA & HtoA & HwvA & HsnA & HretA) ] ].
  { right. right. exists 1%nat, (InfLeave (qset_br q b)).
    split; [cbn [inf_loop]; rewrite HL1; reflexivity | reflexivity]. }
  { right. left. exists 1%nat, qb.
    split; [cbn [inf_iter]; rewrite HB1; reflexivity | exact HBm1]. }
  destruct (zr_table_reads (q_br q) b Hwf E14)
    as (HrdA & HrdB & HrdC & Hwf3 & Hbits3 & Hh1 & Hh2 & Hh3).
  destruct (inf_nb_ok 14 (q_br q) b Hwf ltac:(lia) E14)
    as (Hsb & Hwfb & Hb14).
  assert (HwfA : br_wf (q_br qA)) by (rewrite HqbrA; exact Hwf3).
  assert (HalA : br_haligned (q_br qA)).
  { rewrite HqbrA.
    assert (Hd1 : br_bits (br_dropbits 5 b) = br_bits b - 5)
      by apply dropbits_bits.
    assert (Hd2 : br_bits (br_dropbits 5 (br_dropbits 5 b))
                  = br_bits b - 10)
      by (rewrite dropbits_bits, Hd1; lia).
    apply br_haligned_dropbits; [lia|].
    apply br_haligned_dropbits; [lia|].
    apply br_haligned_dropbits; [lia|].
    exact (inf_nb_align 14 (q_br q) b Hwf ltac:(lia) E14 Hal). }
  assert (HncA : 0 <= b_ncode (s_bld (q_st qA)) <= 19) by (rewrite Hbnc; lia).
  destruct (ll_stage2 c qA HwfA HalA HbhvA HncA) as
    [ (qX & HL2 & HXret)
    | [ HF2
    | [ (qb & HB2 & HBm2)
    | (b4 & ls2 & vals & o & qB & Hwfb4 & Halb4 & Hrd3 & Hwin19 & EMC & Erc
       & Hstep2 & HqbrB & HbhvB & HbnlB & HbndB & HtcB & HlcB & HnbB & HtblB
       & HobB & HhlB & HinB & HoutB & HwszB
       & HwrB & HfgB & HckB & HtoB & HwvB & HsnB & HretB) ] ] ].
  { right. right. exists 1%nat, (InfLeave qX).
    split; [cbn [inf_loop]; rewrite Hstep1, HL2; reflexivity
           | cbv beta iota; rewrite HXret; exact HretA]. }
  { right. right. exists 1%nat, InfFuel.
    split; [cbn [inf_loop]; rewrite Hstep1, HF2; reflexivity | exact I]. }
  { right. left. exists 1%nat, qb.
    split; [cbn [inf_iter]; rewrite Hstep1, HB2; reflexivity | exact HBm2]. }
  (* rebase the stage-2 exports onto q's spellings *)
  rewrite Hbnc in Hrd3. rewrite HqbrA in Hrd3.
  rewrite HtcA in EMC, HtcB, HtblB.
  rewrite Hbnl in HbnlB. rewrite Hbnd in HbndB.
  assert (HwfB2 : br_wf (q_br qB)) by (rewrite HqbrB; exact Hwfb4).
  (* the CODES pre-state decides the CODELENS table shape *)
  destruct (it_pre CT_CODES ls2 19 7
              (fun i => t_codes (s_tab (q_st q)) (0 + i)))
    as [ |temp| |c0 st0] eqn:EPC.
  { exfalso. unfold it_model in EMC. rewrite EPC in EMC.
    injection EMC as <-. cbn [o_ret] in Erc. lia. }
  { (* PreEmpty: the two-marker table; the CL walk absorbs at NO-EOB *)
    unfold it_model in EMC. rewrite EPC in EMC.
    injection EMC as <-.
    cbn [o_ret o_bits o_used o_tbl] in Erc, HnbB, HtblB.
    pose proof (it_pre_empty_shape _ _ _ _ _ _ EPC) as Htemp.
    subst temp.
    assert (H256B : 256 < b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)))
      by (rewrite HbnlB, HbndB; lia).
    match type of HtblB with
    | _ = ?TT =>
        assert (Hmk3 : forall i, 0 <= i < 2 -> TT i = mkCodeT 64 1 0)
    end.
    { intros i Hi.
      cbv beta.
      unfold codes_wb.
      replace (Z.leb 0 (0 + i)) with true
        by (symmetry; apply Z.leb_le; lia).
      replace (0 + i - 0) with i by lia.
      destruct (Z.eq_dec i 1) as [->|Hne1];
        [ apply tset_same
        | rewrite tset_other by exact Hne1;
          replace i with 0 by lia; apply tset_same ]. }
    destruct (cdl_stage3_empty c qB _ HwfB2 HbhvB H256B HnbB HtblB Hmk3) as
      [ HF3 | [ (qb & HB3 & HBm3) | (qX & HL3 & HXret3) ] ].
    - right. right. exists 1%nat, InfFuel.
      split; [cbn [inf_loop]; rewrite Hstep1, Hstep2, HF3; reflexivity
             | exact I].
    - right. left. exists 1%nat, qb.
      split; [cbn [inf_iter]; rewrite Hstep1, Hstep2, HB3; reflexivity
             | exact HBm3].
    - right. right. exists 1%nat, (InfLeave qX).
      split; [cbn [inf_loop]; rewrite Hstep1, Hstep2, HL3; reflexivity
             | cbv beta iota; rewrite HXret3, HretB; symmetry; exact Hq0]. }
  { exfalso. unfold it_model in EMC. rewrite EPC in EMC.
    injection EMC as <-. cbn [o_ret] in Erc. lia. }
  (* PreGo: the live path — the residue gives the per-symbol bridge *)
  assert (Hcl_len : length (scatter_cl vals) = 19%nat)
    by apply scatter_cl_length.
  assert (Hcl_bnd : forall x, In x (scatter_cl vals) -> (x <= 7)%nat).
  { apply scatter_cl_bound.
    exact (read_3bit_vals_bound _ _ _ _ Hrd3). }
  pose proof (Hres (scatter_cl vals) ls2 (t_codes (s_tab (q_st q))) o
                Hcl_len Hwin19 Hcl_bnd EMC Erc
                (ex_intro _ c0 (ex_intro _ st0 EPC))) as Hbr.
  assert (Htot0 : 0 <= b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)))
    by (rewrite HbnlB, HbndB; lia).
  assert (HalB : br_haligned (q_br qB)) by (rewrite HqbrB; exact Halb4).
  assert (Hls2b : forall i, 0 <= i < 19 -> 0 <= ls2 i <= 15).
  { intros i Hi. rewrite (Hwin19 i Hi). unfold zlens.
    split; [lia|].
    assert (Hin : In (nth (Z.to_nat i) (scatter_cl vals) 0%nat)
                    (scatter_cl vals))
      by (apply nth_In; rewrite Hcl_len; lia).
    pose proof (Hcl_bnd _ Hin). lia. }
  assert (Hnbb : 0 < o_bits o <= 15).
  { pose proof (it_model_bits_range CT_CODES ls2 19 7 _ o
                  ltac:(lia) Hls2b ltac:(lia) EMC Erc). lia. }
  assert (Hbits : forall i, 0 <= i < 2 ^ (o_bits o) ->
            0 <= c_bits (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o)
                           (0 + i)) <= o_bits o).
  { intros i Hi.
    pose proof (it_covers_root_pos CT_CODES ls2 19 7 _ o
                  ltac:(lia) Hls2b ltac:(lia) EMC Erc i Hi) as Hc.
    unfold codes_wb.
    replace (Z.leb 0 (0 + i)) with true
      by (symmetry; apply Z.leb_le; lia).
    replace (0 + i - 0) with i by lia.
    cbv beta iota. lia. }
  destruct (cdl_stage3 c qB _ _ _ (scatter_cl vals) Hfl HwfB2 HalB HbhvB
              Htot0 HtcB HnbB HtblB Hnbb Hbits Hbr) as
    [ HF3
    | [ (qb & HB3 & HBm3)
    | [ (qX & HL3 & HXret3)
    | (s' & ls & o1 & o2 & qL & Hrdl & Hhave & Htot & Hwin' & HwfS & HalS
       & Hbnd15 & Eeob & EML & Erl & EMD & Erd & Hstep3 & HlcL & HnbL & HdcL
       & HdbL & HtcL & HqbrL & HobL & HhlL & HinL & HoutL & HwszL
       & HwrL & HfgL & HckL & HtoL & HwvL & HsnL & HretL) ] ] ].
  { right. right. exists 1%nat, InfFuel.
    split; [cbn [inf_loop]; rewrite Hstep1, Hstep2, HF3; reflexivity
           | exact I]. }
  { right. left. exists 1%nat, qb.
    split; [cbn [inf_iter]; rewrite Hstep1, Hstep2, HB3; reflexivity
           | exact HBm3]. }
  { right. right. exists 1%nat, (InfLeave qX).
    split; [cbn [inf_loop]; rewrite Hstep1, Hstep2, HL3; reflexivity
           | cbv beta iota; rewrite HXret3, HretB; symmetry; exact Hq0]. }
  (* THE AGREEMENT ARM *)
  rewrite HqbrB in Hrdl.
  rewrite HbnlB in Hrdl, Htot, EML, EMD.
  rewrite HbndB in Hrdl, Htot, EMD.
  destruct (tbl_pure_core (q_br q) b b4 (t_codes (s_tab (q_st q))) vals ls ls2
              o s' o1 o2 HrdA HrdB HrdC Hh1 Hh2 Hh3 Hrd3 Hwin19 EMC Erc
              Hrdl Hhave Htot Hwin' Hbnd15 Eeob EML Erl EMD Erd) as
    (nlit & Hnlit & Hdec & Hlitlen & Hdstlen & HwfL & EML' & HwfD & EMD'
     & HpreL & HpreD).
  left.
  exists (firstn nlit ls), (skipn nlit ls), (br_stream (cl_br s')), qL,
    (mkDynBuild (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o))
       (zlens ls) (br_bits_of 5 b + 257)
       (br_bits_of 5 (br_dropbits 5 b) + 1) o1 o2).
  split; [exact Hdec|].
  split; [rewrite HqbrL; reflexivity|].
  split; [rewrite HqbrL; exact HwfS|].
  split; [rewrite HqbrL; exact HalS|].
  unfold zr_len_dispatch, db_acc.
  cbn [db_cs db_lens db_nlen db_ndist db_o1 db_o2].
  split.
  { rewrite Hstep1, Hstep2. exact Hstep3. }
  split.
  { split; [exact HwfL|].
    split; [exact EML'|].
    split; [exact Erl|].
    split; [exact HwfD|].
    split; [exact EMD'|].
    exact Erd. }
  split.
  { unfold db_installed.
    cbn [db_cs db_lens db_nlen db_ndist db_o1 db_o2].
    split; [exact HlcL|].
    split; [exact HnbL|].
    split; [exact HdcL|].
    split; [exact HdbL|].
    exact HtcL. }
  split.
  { rewrite (firstn_skipn nlit ls). reflexivity. }
  split; [lia|].
  split; [lia|].
  split; [exact Hch1|].
  split; [exact Hch2|].
  split; [exact HpreL|].
  split; [exact HpreD|].
  split; [rewrite HobL, HobB; exact HobA|].
  split; [rewrite HhlL, HhlB; exact HhlA|].
  split; [rewrite HinL, HinB; exact HinA|].
  split; [rewrite HoutL, HoutB; exact HoutA|].
  split; [rewrite HwszL, HwszB; exact HwszA|].
  split; [rewrite HretL; exact Erd|].
  split; [rewrite HwrL, HwrB; exact HwrA|].
  split; [rewrite HfgL, HfgB; exact HfgA|].
  split; [rewrite HckL, HckB; exact HckA|].
  split; [rewrite HtoL, HtoB; exact HtoA|].
  split; [rewrite HwvL, HwvB; exact HwvA|].
  rewrite HsnL, HsnB. exact HsnA.
Qed.

Print Assumptions zr_table_chain_holds.
