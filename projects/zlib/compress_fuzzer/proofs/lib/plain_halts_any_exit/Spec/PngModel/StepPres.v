(** * Spec.PngModel.StepPres — [ReachSt] preservation along [inf_iter]
    (2026-08-19, preservation lane).

    [StepReach.ReachSt] made [step_ok_covered]'s premises theorems AT
    reachable states; this file makes the invariant SELF-SUSTAINING:
    per-arm preservation lemmas ([pres_*], match-conclusion shape per the
    register's R10 idiom) -> [step_pres] -> [reach_iter] (indexed by the
    landed [inf_iter]) -> establishment at the reset state.

    Batched with the StepReach.v record repairs (same landing):
    - [rm_tblL] widened to the LEN-loop SCC (an earlier development run design note);
    - [rc_have24] replaced by the input-bit budget [rc_inbud] (the R9 +5
      in-overshoot: [if_finish] returns whole accumulator bytes); caps
      relaxed to the u32 give-back ceilings (avail_in <= 2^32 - 6,
      avail_out <= 2^32 - 1) — the 2^24s were headroom;
    - NEW [rm_lenub] (MATCH's successor length is [u32 (len - cw3)]);
    - [dyn_amb_wb] loses its acceptance premise (CODELENS/LENLENS install
      [codes_wb] BEFORE testing the build's return).

    The cross-call re-entry contract (InfLeave, then the next inflate()
    call) is deliberately OUT of scope — a driver-level lap.

    Ownership: pres lane (with the batched StepReach.v edits). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require CodesBuildRows.   (* T2 res-t2: the CODES-build suppliers of rm_tblCL0..3 (R2083 section 2) *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
(* (D') a5 665p (fork): TblPD lives in the header-light leaf (RE-KEY at the bits8-v1 r2 landing) *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import CfgBitsTblLeaf.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblLeafPos ItGTblLeafPosX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGSubCover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** The conclusion shape (match-conclusion; [=InfCont] corollary at
    the bottom of the file). *)
(** The leave invariant (re-entry lap G1; shape = q7-decode audit s.4):
    the full state invariant survives a leave, and — under Z_NO_FLUSH
    with the step's ret still Z_OK — the leave was input-starvation or
    out-full.  [q_ret q'] is the PRE-[inf_leave] ret: [inf_leave] only
    degrades Z_OK (to BUF_ERROR) or passes it through, so this guard is
    exactly what G2's final-ret form consumes.  Flush leaves (Z_BLOCK /
    Z_TREES at block boundaries) are excluded by the flush premise; the
    BAD/DONE ret-leaves by the ret premise. *)
Definition ReachLeave (c : InfCtx) (q' : InfSt) : Prop :=
  ReachSt q'
  /\ (n_flush c = Z_NO_FLUSH -> q_ret q' = Z_OK ->
      br_have (q_br q') = 0 \/ o_left (q_ob q') = 0).

Definition PresOk (c : InfCtx) (r : InfStep) : Prop :=
  match r with
  | InfCont q' => ReachSt q'
  | InfLeave q' => ReachLeave c q'
  (* the direct-return arms never answer Z_OK (q7 ASK3: without this a
     Z_OK InfRet would let a pump continue without re-entry knowledge) *)
  | InfRet _ rr => rr <> Z_OK
  | _ => True
  end.

(* ==========================================================================
   (D') a5 665p + a5 WORDS (fork an earlier development run, then /03): the five new [ReachMode] rows
   [rm_tblpd] / [rm_tblpdCL] (with the CODES root conjunct) / [rm_bits14] / [rm_bits0] / [rm_tblwid] threaded through every
   builder, arm, the dispatch and the re-entry.  Row homes and texts: StepReach.v; suppliers here.
   ========================================================================== *)

(** the [rm_tblpd] conclusion as one name (a Definition: [exact] converts through it) *)
Definition TblPDSide (q : InfSt) : Prop :=
  TblPD (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
  /\ TblPD (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) (t_distbits (s_tab (q_st q))).

Lemma tblpd_frame : forall q q', s_tab (q_st q') = s_tab (q_st q) -> TblPDSide q -> TblPDSide q'.
Proof. intros q q' E H. unfold TblPDSide, tbl_of in *. rewrite E. exact H. Qed.

Lemma tblwid_frame : forall q q', s_tab (q_st q') = s_tab (q_st q) -> TblWidSide q -> TblWidSide q'.
Proof. intros q q' E H. unfold TblWidSide, tbl_of in *. rewrite E. exact H. Qed.

(** cand13: the [rm_dsub] row's frame (the DIST table is read through [s_tab] only) — the [tblwid_frame] idiom. *)
Lemma dist_sub_frame : forall q q', s_tab (q_st q') = s_tab (q_st q) -> DistSubSide q -> DistSubSide q'.
Proof. intros q q' E H. unfold DistSubSide, tbl_of in *. rewrite E. exact H. Qed.

(** cand13: [LeafPosT] of the codes array transports to every table view ([TRcodes k] by shifting; the fixed tables by their own leaves). *)
Lemma leafpos_tbl_of : forall q r, LeafPosT (t_codes (s_tab (q_st q))) -> LeafPosT (tbl_of (q_st q) r).
Proof.
  intros q r H. destruct r; cbn [tbl_of].
  - apply leafpos_shift. exact H.
  - exact lenfix_leafpos.
  - exact distfix_leafpos.
Qed.

(** Packaging for the P3R leaves' [reach_mode_scc] sites (W8 sites P3RTbl.v :153 /
    P3RCodelens.v :263; fork an earlier development run): the two table premises of the three-premise builder, from the CODELENS install
    witness ([db_ok] / [db_installed] = DYNW's first two conjuncts, CfgInvDefs :36) or from the fixed-table configuration
    ([fixed_cfg], the LEN_TBL_PRE fixed disjunct).  The bit premise [br_bits (q_br q) <= 14] follows from NEITHER: it is
    [rm_bits14] at the entry state (see StepReach.[codelens_exit_bits14] for the CODELENS exit shape). *)
Lemma tblrows_of_install : forall d q, db_ok d -> db_installed d q -> TblPDSide q /\ TblWidSide q.
Proof.
  intros d q Hok Hin.
  split; [ split; [exact (tblpd_installed_len d q Hok Hin) | exact (tblpd_installed_dist d q Hok Hin)]
         | exact (tblwid_installed d q Hok Hin) ].
Qed.

Lemma tblrows_of_fixed : forall q, fixed_cfg (q_st q) -> TblPDSide q /\ TblWidSide q.
Proof.
  intros q (E1 & E2 & E3 & E4).
  unfold TblPDSide, TblWidSide, tbl_of. rewrite E1, E2, E3, E4. cbn.
  split; [exact fix_tblpd | exact fix_tblwid].
Qed.

(** cand13 packaging for the [reach_mode_scc] sites (P3RTbl / P3RCodelens / GtDecCost / GtDecTbl): the [rm_dsub] premise from the
    CODELENS install witness or from the fixed-table configuration — the two suppliers of [TblWidSide], one lemma each. *)
Lemma dsub_of_install : forall d q, db_ok d -> db_installed d q -> DistSubSide q.
Proof. intros d q Hok Hin. exact (dsub_installed d q Hok Hin). Qed.

Lemma dsub_of_fixed : forall q, fixed_cfg (q_st q) -> DistSubSide q.
Proof.
  intros q (E1 & E2 & E3 & E4).
  unfold DistSubSide, tbl_of. rewrite ?E1, ?E2, ?E3, ?E4. cbn. exact fix_dsub.
Qed.

(** [rm_bits0]'s body as one name (a5 WORDS STOP #6; text = RECEIPT-q4f-cand6.md §STOP6 verbatim, see StepReach). *)
Definition Bits0Side (q : InfSt) : Prop :=
  (q_mode q = M_HEAD -> h_wrap (s_hdr (q_st q)) = 0 -> br_bits (q_br q) = 0)
  /\ (q_mode q = M_EXLEN -> Z.land (h_flags (s_hdr (q_st q))) 1024 = 0 -> br_bits (q_br q) = 0)
  /\ (q_mode q = M_EXTRA \/ q_mode q = M_NAME \/ q_mode q = M_COMMENT -> br_bits (q_br q) = 0)
  /\ (q_mode q = M_HCRC -> Z.land (h_flags (s_hdr (q_st q))) 512 = 0 -> br_bits (q_br q) = 0)
  /\ (q_mode q = M_DICT \/ q_mode q = M_COPY_ \/ q_mode q = M_COPY -> br_bits (q_br q) = 0).

(* ---- GLUE consuming the STOP facts (provable from the loop definitions; DEFERRED in this partial) ---- *)
Lemma sub_len_240 : forall h, sub_len h = true -> Z.land (c_op h) 240 = 0.
Proof. intros h H. unfold sub_len in H. apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. exact H. Qed.
Lemma sub_len_nz : forall h, sub_len h = true -> c_op h <> 0.
Proof. intros h H. unfold sub_len in H. apply andb_prop in H as [H _]. apply negb_true_iff in H. apply Z.eqb_neq in H. exact H. Qed.
Lemma sub_dist_240 : forall h, sub_dist h = true -> Z.land (c_op h) 240 = 0.
Proof. intros h H. unfold sub_dist in H. apply Z.eqb_eq in H. exact H. Qed.
Lemma subguard_len_wid : forall t rb, TblWid t rb -> (forall i, 0 <= c_bits (t i)) -> SubGuardGen sub_len t rb.
Proof.
  intros t rb Hw Hb i Hi Hs. pose proof (sub_len_240 _ Hs) as H240. pose proof (sub_len_nz _ Hs) as Hnz.
  destruct (Hw i Hi H240 Hnz) as (Hpos & _).
  split; [exact H240 | split; [lia | intros H0; lia]].
Qed.
Lemma subguard_dist_wid : forall t rb, TblWid t rb -> (forall i, 0 <= c_bits (t i)) -> SubGuardGen sub_dist t rb.
Proof.
  intros t rb Hw Hb i Hi Hs. pose proof (sub_dist_240 _ Hs) as H240.
  split; [exact H240|]. destruct (Z.eq_dec (c_op (t i)) 0) as [Hz|Hnz].
  - split; [lia | intros _; apply Hb].
  - destruct (Hw i Hi H240 Hnz) as (Hpos & _). split; [lia | intros H0; lia].
Qed.
(* the fetch loops leave with FEWER bits than the entry the leave state selects (the last guard, verbatim) *)
Lemma inf_fetch_go_leave_lt : forall f t nb b b',
  inf_fetch_go f t nb b = FetchLeave b' -> br_bits b' < c_bits (t (br_bits_of nb b')).
Proof.
  induction f as [|f IH]; intros t nb b b' H; cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb_spec (c_bits (t (br_bits_of nb b))) (br_bits b)) as [E|E]; [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:Ep; [exact (IH _ _ _ _ H) | injection H as <-; exact E].
Qed.
Lemma inf_fetch2_go_leave_lt : forall f t lst b b',
  inf_fetch2_go f t lst b = FetchLeave b' ->
  br_bits b' < c_bits lst + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst))).
Proof.
  induction f as [|f IH]; intros t lst b b' H; cbn [inf_fetch2_go] in H; [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb_spec a bb) as [E|E]
  end; [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:Ep; [exact (IH _ _ _ _ H) | injection H as <-; exact E].
Qed.
Lemma inf_fetch_go_leave_hold : forall f t nb b b',
  0 <= br_hold b -> (forall j, 0 <= br_in b j) -> inf_fetch_go f t nb b = FetchLeave b' -> 0 <= br_hold b'.
Proof.
  induction f as [|f IH]; intros t nb b b' Hh Hin H; cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)); [discriminate|].
  unfold br_pullbyte in H. destruct (Z.eqb (br_have b) 0); [injection H as <-; exact Hh|].
  refine (IH t nb _ b' _ _ H);
    [ cbn [br_hold]; pose proof (Hin (br_next b)); pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b)); lia
    | cbn [br_in]; exact Hin ].
Qed.
Lemma inf_fetch2_go_leave_hold : forall f t lst b b',
  0 <= br_hold b -> (forall j, 0 <= br_in b j) -> inf_fetch2_go f t lst b = FetchLeave b' -> 0 <= br_hold b'.
Proof.
  induction f as [|f IH]; intros t lst b b' Hh Hin H; cbn [inf_fetch2_go] in H; [discriminate|].
  match type of H with context[Z.leb ?a ?bb] => destruct (Z.leb a bb) end; [discriminate|].
  unfold br_pullbyte in H. destruct (Z.eqb (br_have b) 0); [injection H as <-; exact Hh|].
  refine (IH t lst _ b' _ _ H);
    [ cbn [br_hold]; pose proof (Hin (br_next b)); pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b)); lia
    | cbn [br_in]; exact Hin ].
Qed.
Lemma shiftr_lt_pow2_sub : forall x cb op, 0 <= cb -> 0 <= op -> 0 <= x < 2 ^ (cb + op) -> 0 <= Z.shiftr x cb < 2 ^ op.
Proof.
  intros x cb op Hcb Hop Hx. rewrite Z.shiftr_div_pow2 by exact Hcb.
  split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
  rewrite <- Z.pow_add_r by lia. replace (cb + op) with (cb + op) by lia. lia.
Qed.
(* level-2 leave bound: bits < root width (<= rb <= 15) at a root leave, < root + sub <= 15 at a level-2 leave *)
Lemma inf_decode_leave_le14 : forall sub t rb b b',
  TblPD t rb -> rb <= 15 -> TblWid t rb ->
  (forall i, 0 <= i < 2 ^ rb -> sub (t i) = true -> c_op (t i) <> 0) ->
  (forall h, sub h = true -> Z.land (c_op h) 240 = 0) ->
  0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
  inf_decode sub t rb b = DecLeave b' -> br_bits b' <= 14.
Proof.
  intros sub t rb b b' Hpd Hrb Hw Hnz H240 Hh Hb Hin H.
  pose proof Hpd as (Hrb0 & _ & Hroot & _).
  unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; [| |discriminate].
  - destruct (fetch_root_le _ _ _ _ _ Hpd Ef) as ((i0 & Hi0 & Ei0) & Hcb0 & _).
    destruct (sub h0) eqn:Hs; [|discriminate].
    destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2; [discriminate| |discriminate].
    injection H as ->.
    unfold inf_fetch2 in Ef2.
    pose proof (inf_fetch2_go_leave_lt _ _ _ _ _ Ef2) as Hlt.
    subst h0.
    pose proof (H240 _ Hs) as H240i. pose proof (Hnz _ Hi0 Hs) as Hnzi.
    destruct (Hw i0 Hi0 H240i Hnzi) as (Hop & Hwid).
    destruct (Hroot i0 Hi0) as (Hcb1 & Hcbr).
    assert (Hh' : 0 <= br_hold b').
    { pose proof (inf_fetch_hold _ _ _ _ _ Hh Hb Hin Ef) as Fh.
      pose proof (inf_fetch_in _ _ _ _ _ Ef) as Fin.
      assert (Hin0 : forall j, 0 <= br_in b0 j) by (intros j; rewrite Fin; apply Hin).
      exact (inf_fetch2_go_leave_hold _ _ _ _ _ Fh Hin0 Ef2). }
    pose proof (br_bits_of_range (c_bits (t i0) + c_op (t i0)) b' ltac:(lia) Hh') as Hbo.
    rewrite Z.shiftl_1_l in Hbo.
    assert (Hcbnn : 0 <= c_bits (t i0)) by lia. assert (Hopnn : 0 <= c_op (t i0)) by lia.
    destruct (shiftr_lt_pow2_sub _ _ _ Hcbnn Hopnn Hbo) as (Hj0 & Hj1).
    specialize (Hwid _ (conj Hj0 Hj1)). lia.
  - injection H as ->.
    unfold inf_fetch in Ef.
    pose proof (inf_fetch_go_leave_lt _ _ _ _ _ Ef) as Hlt.
    pose proof (inf_fetch_go_leave_hold _ _ _ _ _ Hh Hin Ef) as Hh'.
    pose proof (br_bits_of_range rb b' Hrb0 Hh') as Hbo. rewrite Z.shiftl_1_l in Hbo.
    destruct (Hroot _ Hbo) as (_ & Hcbr). lia.
Qed.
(* a NEEDBITS leave holds fewer than n bits (the loop guard, no side premises) *)
Lemma inf_nb_go_leave_lt : forall f n b b', inf_nb_go f n b = NBLeave b' -> br_bits b' < n.
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb_spec (br_bits b) n) as [E|E]; [injection H as <-; exact E | discriminate].
  - destruct (Z.ltb_spec (br_bits b) n) as [E|E]; [| discriminate].
    destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ H) | injection H as <-; exact E].
Qed.
(* one CODELENS trip: a leave holds fewer bits than the selected root entry (<= nb <= 7) or than that width + 7 *)
Lemma cl_step_leave_le14 : forall t nb tot s s',
  TblPD t nb -> nb <= 7 -> 0 <= br_hold (cl_br s) -> (forall j, 0 <= br_in (cl_br s) j) ->
  cl_step t nb tot s = ClLeave s' -> br_bits (cl_br s') <= 14.
Proof.
  intros t nb tot s s' Hpd Hnb Hh Hin H.
  pose proof Hpd as (Hnb0 & _ & Hroot & _).
  unfold cl_step in H. cbv zeta in H.
  destruct (Z.leb tot (cl_have s)); [discriminate|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; [| |discriminate].
  - destruct (fetch_root_le _ _ _ _ _ Hpd Ef) as ((i0 & Hi0 & Ei0) & Hcb & _).
    destruct (Hroot i0 Hi0) as (Hc1 & Hcr). subst h.
    destruct (Z.ltb (c_val (t i0)) 16); [discriminate|].
    match type of H with
    | context[inf_nb ?need ?bb] => destruct (inf_nb need bb) as [b'|b'] eqn:Enb
    end.
    + repeat (match type of H with context[match ?x with _ => _ end] => destruct x end; cbv beta iota in H); discriminate.
    + injection H as <-. cbn [cl_br].
      unfold inf_nb in Enb. pose proof (inf_nb_go_leave_lt _ _ _ _ Enb) as Hlt.
      revert Hlt. destruct (Z.eqb (c_val (t i0)) 16); [intros Hlt; lia|].
      destruct (Z.eqb (c_val (t i0)) 17); intros Hlt; lia.
  - injection H as <-. cbn [cl_br].
    unfold inf_fetch in Ef. pose proof (inf_fetch_go_leave_lt _ _ _ _ _ Ef) as Hlt.
    pose proof (inf_fetch_go_leave_hold _ _ _ _ _ Hh Hin Ef) as Hh'.
    pose proof (br_bits_of_range nb b Hnb0 Hh') as Hbo. rewrite Z.shiftl_1_l in Hbo.
    destruct (Hroot _ Hbo) as (_ & Hcr). lia.
Qed.
(* the CODELENS loop's leaves: a root fetch leave (bits < c_bits h <= nb <= 7) or a NEEDBITS leave (bits < c_bits h + 7) *)
Lemma cl_loop_leave_le14 : forall m t nb tot s s',
  TblPD t nb -> TblSide t -> nb <= 7 -> br_bits (cl_br s) <= 14 ->
  0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) -> 0 <= br_hold (cl_br s) ->
  (forall j, 0 <= br_in (cl_br s) j) -> lens_ok (cl_lens s) ->
  cl_loop m t nb tot s = Some (ClLeave s') -> br_bits (cl_br s') <= 14.
Proof.
  induction m as [|m IH]; intros t nb tot s s' Hpd Hts Hnb Hb14 Hhave Hb Hh Hin Hlens H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_bits14 t nb tot s Hpd Hb14) as HB.
  pose proof (cl_step_env t nb tot s Hts Hhave Hb Hh Hin ltac:(lia)) as HE.
  pose proof (cl_step_walk t nb tot s Hts Hhave Hb Hlens) as HW.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES; try discriminate.
  - destruct HE as (E1 & E2 & E3 & E4). destruct HW as (W1 & W2 & W3 & W4).
    assert (Hin1 : forall j, 0 <= br_in (cl_br s1) j) by (intros j; rewrite E1; apply Hin).
    exact (IH t nb tot s1 s' Hpd Hts Hnb HB W2 W3 E2 Hin1 W4 H).
  - injection H as H; subst s1. exact (cl_step_leave_le14 t nb tot s s' Hpd Hnb Hh Hin ES).
Qed.
(* the bit-count arithmetic after bsimp/ksimp, whether or not cbn already opened br_dropbits *)
#[local] Ltac c6bits := try rewrite !br_dropbits_bits; try (cbn [br_dropbits br_bits]); lia.
(* the header chain's readers: byte consumes / INITBITS leave the bit count as it was (or 0) *)
#[local] Ltac c6hdr := try lazymatch goal with |- (_ -> _) => intros _ end; bsimp; try (cbn [br_consume br_initbits br_have br_bits br_next br_hold br_in]); lia.
(* bsimp's reduction list, usable IN a hypothesis (an Ltac name takes no `in` clause) *)
#[local] Ltac bsimp_in H := cbn [inf_budget q_mode q_br q_ob q_st q_z q_in q_out q_ret qset_st qset_z qset_br qset_ob qset_in qset_out qset_ret qmode qbad qcheck set_mode set_length set_have set_lens set_check set_total set_last set_ncode set_nlen set_ndist set_offset set_extra set_back set_was set_lencode set_distcode set_lenbits set_distbits set_next set_codes set_bits set_hold set_wbits set_wsize set_whave set_wnext set_alloc set_win set_flags set_dmax set_havedict set_head set_wrap set_work h_mode s_hdr s_win s_cur s_tab s_bld s_hold s_bits u_length u_offset u_extra u_back u_was br_have br_bits br_in br_next br_hold o_left o_put o_buf br_dropbits br_initbits br_bytebits ob_write inf_mrank] in H.
(* Bits0Side at a state whose mode is Hm's: mode-mismatch conjuncts by discrimination; the own conjunct is left to the site *)
#[local] Ltac b0_pre Hm := unfold Bits0Side; repeat apply conj; intros Hm0; try (destruct Hm0 as [Hm0|[Hm0|Hm0]]);
  unfold q_mode in Hm, Hm0; bsimp_in Hm0; rewrite Hm in Hm0; try discriminate Hm0; clear Hm0.

(** ** [ReachMode] constructors, one per successor-mode class

    Census (this lap): the modes in SOME [ReachMode] antecedent are the
    nine of [rm_active]; every other successor mode makes the whole
    block vacuous.  M_LENEXT/M_DIST/M_DISTEXT/M_LENLENS/M_CODELENS are
    never the mode of an [InfCont] SUCCESSOR inside one call (they are
    entered by fallthrough CALLS only), so at successors only the
    M_MATCH and M_LEN/M_LEN_/M_LIT constructors below fire with
    content; the other fields live for the deferred cross-call lap. *)
Definition rm_active (m : Mode) : bool :=
  match m with
  | M_MATCH | M_LENEXT | M_DIST | M_DISTEXT
  | M_LEN | M_LEN_ | M_LIT | M_CODELENS | M_LENLENS => true
  (* (D') rm_bits14's header-side modes *)
  | M_TYPE | M_TYPEDO | M_TABLE => true
  (* (D'') rm_bits0's modes *)
  | M_HEAD | M_EXLEN | M_EXTRA | M_NAME | M_COMMENT | M_HCRC | M_DICT | M_COPY_ | M_COPY => true
  | _ => false
  end.

Lemma reach_mode_inactive :
  forall q, rm_active (q_mode q) = false -> ReachMode q.
Proof.
  intros q H. constructor.
  - intros Hm; rewrite Hm in H; discriminate.
  - intros [Hm|[Hm|Hm]]; rewrite Hm in H; discriminate.
  - intros [Hm|Hm]; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - split; [intros Hm|intros [Hm|[Hm|Hm]]]; rewrite Hm in H; discriminate.
  - intros [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - intros [Hm|Hm]; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - split; [|split]; intros Hm; rewrite Hm in H; discriminate.
  - intros [Hm|Hm]; rewrite Hm in H; discriminate.
  - intros [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - intros [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]]]]]]; rewrite Hm in H; discriminate.
  - repeat apply conj; [intros Hm _|intros Hm _|intros [Hm|[Hm|Hm]]|intros Hm _|intros [Hm|[Hm|Hm]]]; rewrite Hm in H; discriminate.
  - intros [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - intros [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]; rewrite Hm in H; discriminate.
  - split; intros Hm; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros Hm; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
  - intros Hm; rewrite Hm in H; discriminate.
Qed.

(** (D') the header-side modes of [rm_bits14]'s antecedent (TYPE / TYPEDO / TABLE): only the bit row is live. *)
Lemma reach_mode_hdr :
  forall q,
    q_mode q = M_TYPE \/ q_mode q = M_TYPEDO \/ q_mode q = M_TABLE ->
    br_bits (q_br q) <= 14 -> ReachMode q.
Proof.
  intros q Hm Hb. constructor.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|[H|H]]; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|H]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - split; [intros H|intros [H|[H|H]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|H]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - split; [|split]; intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|H]; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; destruct Hm as [E|[E|E]]; congruence.
  - split; intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
Qed.

(** (D'') the nine header/copy modes of [rm_bits0]: only the bit-zero row is live there. *)
Lemma reach_mode_hdr0 :
  forall q,
    q_mode q = M_HEAD \/ q_mode q = M_EXLEN \/ q_mode q = M_EXTRA \/ q_mode q = M_NAME \/ q_mode q = M_COMMENT
    \/ q_mode q = M_HCRC \/ q_mode q = M_DICT \/ q_mode q = M_COPY_ \/ q_mode q = M_COPY ->
    Bits0Side q ->
    (q_mode q = M_HEAD -> q_out q - o_left (q_ob q) = 0) ->
    ReachMode q.
Proof.
  intros q Hm Hb0 Hw0.
  assert (D : forall m, q_mode q = m -> m <> M_HEAD -> m <> M_EXLEN -> m <> M_EXTRA -> m <> M_NAME -> m <> M_COMMENT
                -> m <> M_HCRC -> m <> M_DICT -> m <> M_COPY_ -> m <> M_COPY -> False)
    by (intros m E; rewrite E in Hm; intuition congruence).
  constructor.
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|[H|H]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|H]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - split; [intros H|intros [H|[H|H]]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|H]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - split; [|split]; intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|H]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - exact Hb0.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - split; intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - exact Hw0.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
  - intros H; exact (False_ind _ (D _ H ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
Qed.

Lemma reach_mode_scc :
  forall q,
    q_mode q = M_LEN \/ q_mode q = M_LEN_ \/ q_mode q = M_LIT ->
    LenTblSide q -> TblPDSide q -> br_bits (q_br q) <= 14 -> TblWidSide q -> DistSubSide q -> ReachMode q.
Proof.
  intros q Hm HL Htp Hb Hwd Hds. constructor.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|[H|H]]; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|H]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - split; [intros H|intros [H|[H|H]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros _; exact HL.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|H]; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - split; [|split]; intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros [H|H]; destruct Hm as [E|[E|E]]; congruence.
  - intros _; exact Htp.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; destruct Hm as [E|[E|E]]; congruence.
  - intros _; exact Hwd.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros _; exact Hds.
  - split; intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
  - intros H; destruct Hm as [E|[E|E]]; congruence.
Qed.

Lemma reach_mode_match :
  forall q,
    q_mode q = M_MATCH ->
    match_side q ->
    u_length (s_cur (q_st q)) <= 98303 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    1 <= u_offset (s_cur (q_st q)) ->
    ReachMode q.
Proof.
  intros q Hm HM Hub HL Htp Hb Hwd Hds Ho1. constructor.
  - intros _; exact HM.
  - intros [H|[H|H]]; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros H; congruence | intros _; exact Hub].
  - intros _; exact HL.
  - intros H; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [|split]; intros H; congruence.
  - intros [H|H]; congruence.
  - intros _; exact Htp.
  - intros H; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; congruence.
  - intros _; exact Hwd.
  - intros H; congruence.
  - intros _; exact Hds.
  - split; [intros H; congruence | intros _; exact Ho1].
  - intros H; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
Qed.

(** ** [LenTblSide] frame transport

    Every clause reads ONLY the table struct: [if_wf_tbl]'s conjuncts
    mention [a_lcode]/[a_dcode]/[f_lmask]/[f_dmask] of [if_ctx
    (len_args q)], all definitional functions of [s_tab (q_st q)]; the
    two side bundles read [tbl_of]; the bits ranges read
    [t_lenbits]/[t_distbits].  One equality moves the bundle across any
    br/ob/cur/win/hdr write. *)
Lemma len_tbl_side_frame :
  forall q q',
    s_tab (q_st q') = s_tab (q_st q) ->
    LenTblSide q -> LenTblSide q'.
Proof.
  intros q q' Htab HL.
  unfold LenTblSide, if_wf_tbl, lcode_two_level, dcode_two_level,
    lcode_len_bounded, lcode_len_bounded_upto, lcode_index_range,
    chain_fit, lcode_root_opshape in *.
  cbn [len_args a_lcode a_dcode a_lenbits a_distbits
       if_ctx f_lmask f_dmask f_lcode f_dcode] in *.
  unfold tbl_of in *.
  rewrite Htab. exact HL.
Qed.

(** ** Table-wide width/value bounds for ANY [tbl_of] resolution

    Dynamic tables by the ambient invariant ([rc_amb]); the two fixed
    tables by one [vm_compute] each (StepReach's below-512 width fact is
    scoped; these are table-wide, default included). *)
Lemma lenfix_tblside_chk :
  forallb (fun t => chk_tblside (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lenfix_tblside : TblSide lenfix.
Proof.
  intros i. apply chk_tblside_sound.
  apply (tbl_of_list_all _ _ lenfix_tblside_chk default_tblside).
Qed.

Lemma tbl_of_tblside :
  forall st r,
    amb_ok (t_codes (s_tab st)) ->
    TblSide (tbl_of st r).
Proof.
  intros st r Hamb. destruct r as [off| |]; cbn [tbl_of].
  - intros i.
    exact (conj (proj1 (Hamb (off + i)))
                (proj1 (proj2 (Hamb (off + i))))).
  - exact lenfix_tblside.
  - exact distfix_tblside.
Qed.

Lemma tbl_of_wid015 :
  forall st r,
    amb_ok (t_codes (s_tab st)) ->
    forall i, 0 <= c_bits (tbl_of st r i) <= 15.
Proof. intros st r Ha i. exact (proj1 (tbl_of_tblside st r Ha i)). Qed.

Lemma tbl_of_val_range :
  forall st r,
    amb_ok (t_codes (s_tab st)) ->
    forall i, 0 <= c_val (tbl_of st r i) < 65536.
Proof. intros st r Ha i. exact (proj2 (tbl_of_tblside st r Ha i)). Qed.

(** ** Small arithmetic helpers *)
Lemma u32_range : forall x, 0 <= u32 x < 4294967296.
Proof. intros x. unfold u32. apply Z.mod_pos_bound. lia. Qed.

Lemma u8_range : forall x, 0 <= u8 x < 256.
Proof. intros x. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma land7_range : forall x, 0 <= x -> 0 <= Z.land x 7 <= x.
Proof.
  intros x Hx.
  replace (Z.land x 7) with (x mod 8)
    by (replace 7 with (Z.ones 3) by reflexivity;
        symmetry; apply Z.land_ones; lia).
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod x 8 ltac:(lia)).
  pose proof (Z.div_pos x 8 Hx ltac:(lia)).
  lia.
Qed.

(** ** [ReachCore] transports

    [reach_core_conv]: the pure-frame move (mode/msg/check/ret/out/total
    writes only).  [reach_core_build]: the general move — br under the
    env-pack facts, output shrinking, and the state facts stated
    directly on the successor so table/build writes can discharge them
    from their own provenance. *)
Lemma reach_core_conv :
  forall q q',
    ReachCore q ->
    q_br q' = q_br q ->
    q_ob q' = q_ob q ->
    s_tab (q_st q') = s_tab (q_st q) ->
    s_win (q_st q') = s_win (q_st q) ->
    s_bld (q_st q') = s_bld (q_st q) ->
    s_cur (q_st q') = s_cur (q_st q) ->
    q_out q' = q_out q ->
    q_in q' = q_in q ->
    ReachCore q'.
Proof.
  intros q q' HC Ebr Eob Etab Ewin Ebld Ecur Eout Eqin.
  destruct HC as [Hpos Hbits Hbytes Hhold Hwin Hwnext Hwhave Hsane Hlen0
                  Hinbud Hleft24 Hlens Hbhave Hbnlen Hbndist Hamb Hob Hwcoup
                  Hout0 Houtcap Hnb Hhc Hlp Hwa0].
  constructor; unfold q_pos in *;
    rewrite ?Ebr, ?Eob, ?Etab, ?Ewin, ?Ebld, ?Ecur, ?Eout, ?Eqin; assumption.
Qed.

Lemma reach_core_build :
  forall q q',
    ReachCore q ->
    br_in (q_br q') = br_in (q_br q) ->
    0 <= br_have (q_br q') ->
    0 <= br_hold (q_br q') ->
    0 <= br_bits (q_br q') ->
    br_bits (q_br q') <= 39 ->
    8 * br_have (q_br q') + br_bits (q_br q')
      <= 8 * br_have (q_br q) + br_bits (q_br q) ->
    0 <= o_left (q_ob q') ->
    o_left (q_ob q') <= o_left (q_ob q) ->
    t_sane (s_tab (q_st q')) = 1 ->
    amb_ok (t_codes (s_tab (q_st q'))) ->
    (* per-field window equalities: [set_wbits] (HEAD) rebuilds [s_win]
       while touching none of the four fields the invariant reads *)
    w_win (s_win (q_st q')) = w_win (s_win (q_st q)) ->
    w_wnext (s_win (q_st q')) = w_wnext (s_win (q_st q)) ->
    w_whave (s_win (q_st q')) = w_whave (s_win (q_st q)) ->
    w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q)) ->
    lens_ok (b_lens (s_bld (q_st q'))) ->
    0 <= b_have (s_bld (q_st q')) ->
    0 <= b_nlen (s_bld (q_st q')) ->
    0 <= b_ndist (s_bld (q_st q')) ->
    0 <= u_length (s_cur (q_st q')) ->
    (forall j, 0 <= o_buf (q_ob q') j < 256) ->
    o_left (q_ob q') <= q_out q' ->
    q_out q' <= 4294967295 ->
    q_in q' = q_in q ->
    (* rc_holdclean (2026-09-03): the successor's accumulator is clean above
       its valid bits -- discharged at every site by [hc_close] below *)
    br_hold (q_br q') < 2 ^ br_bits (q_br q') ->
    (* W9 rc_leafpos: the successor's codes array is leaf-positive -- frame ([assumption] on
       [core_facts]'s Flp) except at the three [set_codes] installs, where [lp_close] derives it
       from the install's [it_model] equation and [it_wf] fact *)
    LeafPosT (t_codes (s_tab (q_st q'))) ->
    (* W9 rc_walloc0: [w_alloc] is a per-field window equality like the four above ([reflexivity]
       at every site; [uw] runs only at the leave) *)
    w_alloc (s_win (q_st q')) = w_alloc (s_win (q_st q)) ->
    ReachCore q'.
Proof.
  intros q q' HC Ein Hh Hho Hb0 Hb39 Hbud Hl0 Hlm Hsane' Hamb'
    Eww Ewn Ewh Ews Hlens' Hbh' Hbn' Hbd' Hlen' Hob' Hqo0' Hqocap' Eqin Hhc' Hlp' Ewa.
  destruct HC as [Hpos Hbits Hbytes Hhold Hwin Hwnext Hwhave Hsane Hlen0
                  Hinbud Hleft24 Hlens Hbhave Hbnlen Hbndist Hamb Hob Hwcoup
                  Hout0 Houtcap Hnb Hhc Hlp Hwa0].
  constructor.
  - split; [exact Hh|]. split; [exact Hb0|]. exact Hl0.
  - exact Hb39.
  - intros j. rewrite Ein. exact (Hbytes j).
  - exact Hho.
  - intros j. rewrite Eww. exact (Hwin j).
  - rewrite Ewn, Ews. exact Hwnext.
  - rewrite Ewh, Ews. exact Hwhave.
  - exact Hsane'.
  - exact Hlen'.
  - lia.
  - lia.
  - exact Hlens'.
  - exact Hbh'.
  - exact Hbn'.
  - exact Hbd'.
  - exact Hamb'.
  - exact Hob'.
  - rewrite Ewh, Ews, Ewn. exact Hwcoup.
  - exact Hqo0'.
  - exact Hqocap'.
  - rewrite Eqin. lia.
  - exact Hhc'.
  - exact Hlp'.
  - rewrite Ewa, Ews. exact Hwa0.
Qed.

(** The per-arm working set: every core projection as a hypothesis, so
    the closer's [assumption]/[lia] see them, whatever the goal order. *)
Ltac core_facts q HC :=
  pose proof (rc_pos q HC) as (Hh & Hb & Hl);
  pose proof (rc_bits39 q HC) as F39;
  pose proof (rc_hold q HC) as Fhold;
  pose proof (rc_inbud q HC) as Fbud;
  pose proof (rc_leftu32 q HC) as Fl24;
  pose proof (rc_sane q HC) as Fsane;
  pose proof (rc_amb q HC) as Famb;
  pose proof (rc_lens q HC) as Flens;
  pose proof (rc_bhave q HC) as Fbh;
  pose proof (rc_bnlen q HC) as Fbn;
  pose proof (rc_bndist q HC) as Fbd;
  pose proof (rc_wnext q HC) as Fwn;
  pose proof (rc_whave q HC) as Fwh;
  pose proof (rc_len0 q HC) as Flen0;
  pose proof (rc_outb q HC) as Fob;
  pose proof (rc_wcoup q HC) as Fwcoup;
  pose proof (rc_out0 q HC) as For0;
  pose proof (rc_outcap q HC) as Focap;
  pose proof (rc_leafpos q HC) as Flp;
  pose proof (rc_walloc0 q HC) as Fwa0.

(** ** The [rc_holdclean] supply

    One closer for the builder's hold-clean premise at every site: the
    goal is read back to a reader term ([br_hc X]) and the reader term is
    walked to the arm's own equations -- the [inf_nb]/[inf_decode]/
    [cl_loop]/[ll_go] result in context, the drops in between, and the
    predecessor's [ReachCore] at the base.  Bytes come from [rc_bytes],
    table widths from the [TblSide]/width fact the arm already holds. *)
Ltac hc_bytes :=
  let j := fresh "j" in intros j;
  cbn [cl_br br_in br_bytebits br_dropbits br_initbits];
  match goal with
  | HC : ReachCore ?q |- 0 <= br_in (q_br ?q) _ < 256 => exact (rc_bytes q HC j)
  end.

Ltac hc_wid :=
  match goal with
  | H : forall i, 0 <= c_bits (?t i) <= 15 |- forall i, 0 <= c_bits (?t i) =>
      exact (fun i => proj1 (H i))
  | H : TblSide ?t |- forall i, 0 <= c_bits (?t i) =>
      exact (fun i => proj1 (proj1 (H i)))
  | H : forall i, 0 <= c_bits (?t i) |- forall i, 0 <= c_bits (?t i) => exact H
  end.

Ltac hc_solve :=
  cbn [cl_br nb_br ll_br];
  repeat first
    [ match goal with
      | HC : ReachCore ?q |- br_hc (q_br ?q) => exact (hc_of_core q HC)
      end
    | assumption
    | apply initbits_hc
    | apply bytebits_hc
    | (apply dropbits_hc; [ | solve [lia] ])
    | match goal with
      | H : inf_nb ?n ?b0 = ?r |- br_hc _ =>
          refine (inf_nb_hc n b0 r _ _ H); [ hc_bytes | ]
      end
    | match goal with
      | H : inf_decode ?s ?t ?rb ?b0 = ?r |- br_hc ?X =>
          refine (inf_decode_hc s t rb b0 r _ _ _ H X eq_refl);
          [ hc_wid | hc_bytes | ]
      end
    | match goal with
      | H : cl_loop ?m ?t ?nb ?tot ?s0 = Some ?r |- br_hc ?X =>
          refine (cl_loop_hc m t nb tot s0 r _ _ _ H X eq_refl);
          [ hc_wid | hc_bytes | ]
      end
    | match goal with
      | H : ?r = ll_go ?f ?nc ?hv ?ls ?b0 |- br_hc _ =>
          let T := fresh "T" in
          pose proof (ll_go_hc f nc hv ls b0) as T;
          rewrite <- H in T; cbn [ll_br] in T; apply T; [ hc_bytes | ]
      end
    | match goal with
      | H : ll_go ?f ?nc ?hv ?ls ?b0 = ?r |- br_hc _ =>
          let T := fresh "T" in
          pose proof (ll_go_hc f nc hv ls b0) as T;
          rewrite H in T; cbn [ll_br] in T; apply T; [ hc_bytes | ]
      end
    | progress cbn [cl_br nb_br ll_br] ].

(** [db_installed]'s codes array is leaf-positive when the build record is [db_ok] and the
    caller's array was: the P3R install sites hold exactly these two facts. *)
Lemma leafpos_installed :
  forall d q', db_ok d -> db_installed d q' -> LeafPosT (db_cs d) -> LeafPosT (t_codes (s_tab (q_st q'))).
Proof.
  intros d q' (Hamb & HWF1 & EI1 & _ & HWF2 & EI2 & _) (_ & _ & _ & _ & Ecodes) Hcs.
  rewrite Ecodes.
  assert (H1 : LeafPosT (codes_wb (db_cs d) 0 (o_tbl (db_o1 d)))).
  { apply leafpos_codes_wb; [exact Hcs|].
    exact (it_model_leafpos_wf _ _ _ _ _ _ HWF1 (leafpos_shift _ _ Hcs) EI1). }
  apply leafpos_codes_wb; [exact H1|].
  exact (it_model_leafpos_wf _ _ _ _ _ _ HWF2 (leafpos_shift _ _ H1) EI2).
Qed.

(** ** The [rc_leafpos] supply

    [lp_close] closes the builder's [LeafPosT (t_codes ...)] premise: by frame ([core_facts]'s
    Flp, or the predecessor's [ReachCore]) when the codes array is untouched, and at a
    [set_codes] install by peeling [codes_wb] ([leafpos_codes_wb]) and the offset view
    ([leafpos_shift]) down to the [it_model] equation + [it_wf] fact the arm holds
    ([it_model_leafpos_wf]).  Reached from [hc_close] so every existing closer
    (`try hc_close`) covers the new premise with no text change at the callers. *)
Ltac lp_close :=
  lazymatch goal with
  | |- LeafPosT (codes_wb ?cs ?k ?t) => apply leafpos_codes_wb; [ lp_close | lp_close ]
  | |- LeafPosT (fun i => ?cs (?k + i)) => apply leafpos_shift; lp_close
  | |- LeafPosT (o_tbl ?o) =>
      first [ solve [assumption]
            | match goal with
              | H : Some ?o' = it_model ?ty ?l ?cs ?rt ?t0, W : it_wf ?ty ?l ?cs ?rt |- LeafPosT (o_tbl ?o') =>
                  refine (it_model_leafpos_wf ty l cs rt t0 o' W _ (eq_sym H)); lp_close
              | H : it_model ?ty ?l ?cs ?rt ?t0 = Some ?o', W : it_wf ?ty ?l ?cs ?rt |- LeafPosT (o_tbl ?o') =>
                  refine (it_model_leafpos_wf ty l cs rt t0 o' W _ H); lp_close
              end ]
  | |- LeafPosT tnone => exact leafpos_tnone
  | |- LeafPosT distfix => exact distfix_leafpos
  | |- LeafPosT lenfix => exact lenfix_leafpos
  | |- LeafPosT (t_codes (s_tab (q_st ?q))) =>
      first [ solve [assumption]
            | match goal with HC : ReachCore ?q0 |- LeafPosT (t_codes (s_tab (q_st ?q0))) => exact (rc_leafpos q0 HC) end
            | match goal with D : db_ok ?d, I : db_installed ?d ?q1 |- LeafPosT (t_codes (s_tab (q_st ?q1))) =>
                  refine (leafpos_installed d q1 D I _); cbn [db_cs]; lp_close end ]
  | |- LeafPosT _ => first [ solve [assumption] | (progress ksimp; lp_close) ]
  end.

Ltac hc_close :=
  lazymatch goal with
  | |- br_hold ?X < 2 ^ br_bits ?X =>
      first [ solve [assumption] | apply hc_of; solve [hc_solve] ]
  | |- Z.shiftr ?h ?n < 2 ^ (?w - ?n) =>
      apply shiftr_lt_pow2; [ hc_close | solve [lia] ]
  | |- 0 < 2 ^ 0 => reflexivity
  | |- ?h < 2 ^ ?w => solve [assumption]
  (* W9: the builder's leaf-positivity premise, routed to [lp_close] *)
  | |- LeafPosT _ => lp_close
  end.

Ltac rc_close q :=
  apply (reach_core_build q); try unfold fixedtables;
  try unfold br_consume; ksimp;
  try reflexivity; try assumption; try lia;
  try hc_close;
  repeat first [ apply dropbits_hold_nonneg
               | apply Z.shiftr_nonneg
               | assumption | lia | reflexivity ].

(* [cbn] declines to unfold a head [q_mode] whose reduction ends stuck at
   [h_mode (s_hdr (q_st q))] (the R10 "declines" wall, probed here) —
   [unfold] first, then [bsimp] walks the tower. *)
Ltac rm_off := apply reach_mode_inactive; unfold q_mode; bsimp; reflexivity.

(* [ubk] (a5 rider on the A1.2 candidate, 2026-09-02): the StepReach candidate's [ubk] is
   [#[local]] there, so StepPres carries its own file-local copy -- body identical to
   StepReach's; neither file exports it. *)
#[local] Ltac ubk :=
  cbn [q_st qset_st qset_br qset_ob qmode qbad];
  repeat first [ rewrite uback_set_back | rewrite uback_set_length
               | rewrite uback_set_offset | rewrite uback_set_extra
               | rewrite uback_set_was | rewrite uback_set_mode ].


(* ==========================================================================
   Re-entry lap, output-byte walks (pres lane, 2026-08-20; validated in
   ReentryWalks.v before splice): [bytesf] through
   [if_model_bytes] — the [rc_outb] writer-arm discharges.
   ========================================================================== *)
Definition bytesf (a : zarr) : Prop := forall j, 0 <= a j < 256.

Lemma zset_bytes : forall a i v,
  bytesf a -> 0 <= v < 256 -> bytesf (zset a i v).
Proof.
  intros a i v Ha Hv j. unfold zset. destruct (Z.eqb j i); auto.
Qed.

Lemma zcopy_bytes : forall n dst di src si,
  bytesf dst -> bytesf src -> bytesf (zcopy n dst di src si).
Proof.
  induction n as [|n IH]; intros dst di src si Hd Hs; cbn [zcopy];
    [exact Hd|].
  apply IH; [apply zset_bytes; [exact Hd | apply Hs] | exact Hs].
Qed.

Lemma zfill_bytes : forall n a i v,
  bytesf a -> 0 <= v < 256 -> bytesf (zfill n a i v).
Proof.
  induction n as [|n IH]; intros a i v Ha Hv; cbn [zfill]; [exact Ha|].
  apply IH; [apply zset_bytes; assumption | exact Hv].
Qed.

Lemma ob_write_bytes : forall o v,
  bytesf (o_buf o) -> 0 <= v < 256 -> bytesf (o_buf (ob_write o v)).
Proof.
  intros o v Ho Hv. cbn [ob_write o_buf]. apply zset_bytes; assumption.
Qed.

Lemma os_read_bytes : forall win o r,
  bytesf win -> bytesf (o_buf o) -> 0 <= os_read win o r < 256.
Proof. intros win o r Hw Ho. destruct r; cbn [os_read]; auto. Qed.

Lemma ob_copyn_bytes : forall n win o r,
  bytesf win -> bytesf (o_buf o) -> bytesf (o_buf (ob_copyn n win o r)).
Proof.
  induction n as [|n IH]; intros win o r Hw Ho; cbn [ob_copyn]; [exact Ho|].
  apply IH; [exact Hw|].
  apply ob_write_bytes; [exact Ho|].
  apply os_read_bytes; assumption.
Qed.

(** ** the inflate_fast side *)
Lemma if_put_bytes : forall v s,
  bytesf (f_buf s) -> 0 <= v < 256 -> bytesf (f_buf (if_put v s)).
Proof.
  intros v s Hs Hv. cbn [if_put f_buf]. apply zset_bytes; assumption.
Qed.

Lemma if_read_bytes : forall c s r,
  bytesf (f_window c) -> bytesf (f_buf s) -> 0 <= if_read c s r < 256.
Proof. intros c s r Hw Hs. destruct r; cbn [if_read]; auto. Qed.

Lemma if_copyn_bytes : forall n c s r,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  bytesf (f_buf (fst (if_copyn n c s r))).
Proof.
  induction n as [|n IH]; intros c s r Hw Hs; cbn [if_copyn fst];
    [exact Hs|].
  apply IH; [exact Hw|].
  apply if_put_bytes; [exact Hs|].
  apply if_read_bytes; assumption.
Qed.

Lemma if_copy3w_bytes : forall f c s r len s2 r2 l2,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  if_copy3w f c s r len = Some (s2, r2, l2) -> bytesf (f_buf s2).
Proof.
  induction f as [|f IH]; intros c s r len s2 r2 l2 Hw Hs H;
    cbn [if_copy3w] in H; [discriminate|].
  destruct (Z.ltb 2 len).
  - destruct (if_copyn 3 c s r) as [s1 r1] eqn:Ec.
    apply (IH c s1 r1 (u32 (len - 3)) s2 r2 l2 Hw); [|exact H].
    pose proof (if_copyn_bytes 3 c s r Hw Hs) as HB.
    rewrite Ec in HB. exact HB.
  - injection H as <- <- <-. exact Hs.
Qed.

Lemma if_copytail_bytes : forall c s r len,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  bytesf (f_buf (if_copytail c s r len)).
Proof.
  intros c s r len Hw Hs. unfold if_copytail.
  destruct (Z.eqb len 0); [exact Hs|].
  destruct (if_copyn 1 c s r) as [s1 r1] eqn:E1.
  pose proof (if_copyn_bytes 1 c s r Hw Hs) as HB1. rewrite E1 in HB1.
  cbn [fst] in HB1.
  destruct (Z.ltb 1 len); [|exact HB1].
  exact (if_copyn_bytes 1 c s1 r1 Hw HB1).
Qed.

Lemma if_copydirect_bytes : forall c s r len s5,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  if_copydirect c s r len = Some s5 -> bytesf (f_buf s5).
Proof.
  intros c s r len s5 Hw Hs H. unfold if_copydirect in H.
  destruct (if_copyn 3 c s r) as [s1 r1] eqn:E1.
  pose proof (if_copyn_bytes 3 c s r Hw Hs) as HB1. rewrite E1 in HB1.
  cbn [fst] in HB1.
  destruct (if_copy3w copy_fuel c s1 r1 (u32 (len - 3)))
    as [[[s2 r2] l2]|] eqn:E2; [|discriminate].
  injection H as <-.
  apply if_copytail_bytes; [exact Hw|].
  exact (if_copy3w_bytes _ _ _ _ _ _ _ _ Hw HB1 E2).
Qed.

Lemma if_winphase_bytes : forall c s dist op len s4 r4 len4,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  if_winphase c s dist op len = (s4, r4, len4) -> bytesf (f_buf s4).
Proof.
  intros c s dist op len s4 r4 len4 Hw Hs H. unfold if_winphase in H.
  destruct (Z.eqb (f_wnext c) 0).
  - destruct (Z.ltb op len).
    + destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wsize c - op)))
        as [s1 r1] eqn:E1.
      pose proof (if_copyn_bytes (Z.to_nat op) c s (SrcWin (f_wsize c - op))
                    Hw Hs) as HB. rewrite E1 in HB. cbn [fst] in HB.
      injection H as <- <- <-. exact HB.
    + injection H as <- <- <-. exact Hs.
  - destruct (Z.ltb (f_wnext c) op).
    + destruct (Z.ltb (u32 (op - f_wnext c)) len).
      * destruct (if_copyn (Z.to_nat (u32 (op - f_wnext c))) c s
                    (SrcWin (f_wsize c + f_wnext c - op))) as [s1 r1] eqn:E1.
        pose proof (if_copyn_bytes (Z.to_nat (u32 (op - f_wnext c))) c s
                      (SrcWin (f_wsize c + f_wnext c - op)) Hw Hs) as HB1.
        rewrite E1 in HB1. cbn [fst] in HB1.
        destruct (Z.ltb (f_wnext c) (u32 (len - u32 (op - f_wnext c)))).
        { destruct (if_copyn (Z.to_nat (f_wnext c)) c s1 (SrcWin 0))
            as [s2 r2] eqn:E2.
          pose proof (if_copyn_bytes (Z.to_nat (f_wnext c)) c s1 (SrcWin 0)
                        Hw HB1) as HB2. rewrite E2 in HB2. cbn [fst] in HB2.
          injection H as <- <- <-. exact HB2. }
        { injection H as <- <- <-. exact HB1. }
      * injection H as <- <- <-. exact Hs.
    + destruct (Z.ltb op len).
      * destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wnext c - op)))
          as [s1 r1] eqn:E1.
        pose proof (if_copyn_bytes (Z.to_nat op) c s (SrcWin (f_wnext c - op))
                      Hw Hs) as HB. rewrite E1 in HB. cbn [fst] in HB.
        injection H as <- <- <-. exact HB.
      * injection H as <- <- <-. exact Hs.
Qed.

Lemma if_dodist_bytes : forall f c len s h,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  match if_dodist f c len s h with
  | BodyOk s' | BodyEob s' | BodyBad s' _ => bytesf (f_buf s')
  | BodyFuel => True
  end.
Proof.
  induction f as [|f IH]; intros c len s h Hw Hs; cbn [if_dodist];
    [exact I|].
  assert (Hs1 : bytesf (f_buf (if_drop (c_bits h) s)))
    by (cbn [if_drop f_buf]; exact Hs).
  destruct (negb (Z.eqb (Z.land (c_op h) 16) 0)).
  - cbv zeta.
    match goal with
    | |- context [if_winphase ?cc ?s3 ?d ?ow ?l] => idtac
    end.
    set (s2 := if Z.ltb (f_bits (if_drop (c_bits h) s)) (Z.land (c_op h) 15)
               then _ else _).
    assert (Hs2 : bytesf (f_buf s2)).
    { unfold s2.
      destruct (Z.ltb (f_bits (if_drop (c_bits h) s)) (Z.land (c_op h) 15));
        [|exact Hs1].
      destruct (Z.ltb _ (Z.land (c_op h) 15));
        cbn [if_load1 f_buf]; exact Hs1. }
    set (s3 := if_drop (Z.land (c_op h) 15) s2).
    assert (Hs3 : bytesf (f_buf s3)) by (cbn [if_drop f_buf]; exact Hs2).
    destruct (Z.ltb (u32 (f_out s3 - f_beg c)) _).
    + destruct (Z.ltb (f_whave c) _ && negb (Z.eqb (f_sane c) 0));
        [cbv iota; exact Hs3|].
      destruct (if_winphase c s3 _ _ len) as [[s4 r4] len4] eqn:Ewp.
      pose proof (if_winphase_bytes _ _ _ _ _ _ _ _ Hw Hs3 Ewp) as HB4.
      destruct (if_copy3w copy_fuel c s4 r4 len4)
        as [[[s5 r5] l5]|] eqn:E3w; [|exact I].
      cbv iota.
      apply if_copytail_bytes; [exact Hw|].
      exact (if_copy3w_bytes _ _ _ _ _ _ _ _ Hw HB4 E3w).
    + destruct (if_copydirect c s3 _ len) as [s5|] eqn:Edir; [|exact I].
      cbv iota.
      exact (if_copydirect_bytes _ _ _ _ _ Hw Hs3 Edir).
  - destruct (Z.eqb (Z.land (c_op h) 64) 0).
    + exact (IH c len (if_drop (c_bits h) s) _ Hw Hs1).
    + cbv iota. exact Hs1.
Qed.

Lemma if_dolen_bytes : forall f c s h,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  match if_dolen f c s h with
  | BodyOk s' | BodyEob s' | BodyBad s' _ => bytesf (f_buf s')
  | BodyFuel => True
  end.
Proof.
  induction f as [|f IH]; intros c s h Hw Hs; cbn [if_dolen]; [exact I|].
  assert (Hs1 : bytesf (f_buf (if_drop (c_bits h) s)))
    by (cbn [if_drop f_buf]; exact Hs).
  destruct (Z.eqb (c_op h) 0).
  - cbv iota. apply if_put_bytes; [exact Hs1 | apply u8_range].
  - destruct (negb (Z.eqb (Z.land (c_op h) 16) 0)).
    + cbv zeta.
      destruct (Z.eqb (Z.land (c_op h) 15) 0); cbv beta iota.
      * assert (Hs3 : bytesf
                        (f_buf (if_refill15 c (if_drop (c_bits h) s)))).
        { unfold if_refill15.
          destruct (Z.ltb (f_bits (if_drop (c_bits h) s)) 15);
            cbn [if_load1 f_buf]; exact Hs1. }
        match goal with
        | |- context [if_dodist tbl_fuel c ?LEN ?S3 ?H3] =>
            pose proof (if_dodist_bytes tbl_fuel c LEN S3 H3 Hw Hs3) as HD
        end.
        destruct (if_dodist tbl_fuel c _ _ _) as [s'|s'|s' m|];
          cbv iota in HD |- *; try exact I; exact HD.
      * match goal with
        | |- context [if_refill15 c (if_drop (Z.land (c_op h) 15) ?SA)] =>
            assert (Hsa : bytesf (f_buf SA))
        end.
        { destruct (Z.ltb (f_bits (if_drop (c_bits h) s))
                      (Z.land (c_op h) 15));
            cbn [if_load1 if_drop f_buf]; exact Hs.  }
        match goal with
        | |- context [if_refill15 c (if_drop (Z.land (c_op h) 15) ?SA)] =>
            assert (Hs3 : bytesf
                            (f_buf (if_refill15 c
                                      (if_drop (Z.land (c_op h) 15) SA))))
        end.
        { unfold if_refill15.
          destruct (Z.ltb (f_bits (if_drop (Z.land (c_op h) 15) _)) 15);
            cbn [if_load1 if_drop f_buf]; exact Hsa. }
        match goal with
        | |- context [if_dodist tbl_fuel c ?LEN ?S3 ?H3] =>
            pose proof (if_dodist_bytes tbl_fuel c LEN S3 H3 Hw Hs3) as HD
        end.
        destruct (if_dodist tbl_fuel c _ _ _) as [s'|s'|s' m|];
          cbv iota in HD |- *; try exact I; exact HD.
    + destruct (Z.eqb (Z.land (c_op h) 64) 0).
      * exact (IH c (if_drop (c_bits h) s) _ Hw Hs1).
      * destruct (negb (Z.eqb (Z.land (c_op h) 32) 0)); cbv iota; exact Hs1.
Qed.

Lemma if_body_bytes : forall c s,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  match if_body c s with
  | BodyOk s' | BodyEob s' | BodyBad s' _ => bytesf (f_buf s')
  | BodyFuel => True
  end.
Proof.
  intros c s Hw Hs. unfold if_body. cbv zeta.
  assert (Hs0 : bytesf (f_buf (if_refill15 c s))).
  { unfold if_refill15.
    destruct (Z.ltb (f_bits s) 15); cbn [if_load1 f_buf]; exact Hs. }
  exact (if_dolen_bytes tbl_fuel c (if_refill15 c s) _ Hw Hs0).
Qed.

Lemma if_step_bytes : forall c s,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  match if_step c s with
  | IfCont s' | IfStop s' | IfEob s' | IfBad s' _ => bytesf (f_buf s')
  | IfFuel => True
  end.
Proof.
  intros c s Hw Hs. rewrite if_step_unfold.
  pose proof (if_body_bytes c s Hw Hs) as HB.
  destruct (if_body c s) as [s1|s1|s1 m|]; cbv beta iota in HB |- *;
    [destruct (if_guard c s1); exact HB | exact HB | exact HB | exact I].
Qed.

Lemma if_loop_bytes : forall m c s r,
  bytesf (f_window c) -> bytesf (f_buf s) ->
  if_loop m c s = Some r ->
  match r with
  | IfCont s' | IfStop s' | IfEob s' | IfBad s' _ => bytesf (f_buf s')
  | IfFuel => True
  end.
Proof.
  induction m as [|m IH]; intros c s r Hw Hs H;
    [cbn [if_loop] in H; discriminate|].
  rewrite if_loop_S in H.
  pose proof (if_step_bytes c s Hw Hs) as HS.
  destruct (if_step c s) as [s1|s1|s1|s1 m1|] eqn:ES.
  - exact (IH c s1 r Hw HS H).
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact I.
Qed.

Theorem if_model_bytes : forall a,
  (forall j, 0 <= a_window a j < 256) ->
  (forall j, 0 <= a_buf a j < 256) ->
  match if_model a with
  | Some y => forall j, 0 <= y_buf y j < 256
  | None => True
  end.
Proof.
  intros a Hw Hb. unfold if_model. cbv zeta.
  assert (Hw' : bytesf (f_window (if_ctx a))) by exact Hw.
  assert (Hb' : bytesf (f_buf (if_st0 a))) by exact Hb.
  destruct (if_loop (S (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a))))
              (if_ctx a) (if_st0 a)) as [r|] eqn:Heq; [|exact I].
  pose proof (if_loop_bytes _ _ _ _ Hw' Hb' Heq) as HL.
  destruct r as [s'|s'|s'|s' m0|]; cbv beta iota in HL |- *; try exact I;
    unfold if_finish; cbv zeta; cbn [y_buf]; exact HL.
Qed.

(* ==========================================================================
   Re-entry lap, LEAVE-side walks (pres lane, 2026-08-20; validated in
   ReentryWalks.v before splice): P1 sources
   ([br_have' = 0] at pullbyte-fail leaves), env + input-bit budget at
   every [InfLeave].  At EOF: [cl_loop_leave] consumes [cl_step_chave].
   Consumed by the G1 leave sweep (post-ACK).
   ========================================================================== *)

(** ** [inf_nb] *)
Lemma inf_nb_go_leave :
  forall f n b b',
    0 <= br_bits b ->
    0 <= br_hold b ->
    (forall j, 0 <= br_in b j) ->
    n <= 8 * Z.of_nat f + br_bits b ->
    inf_nb_go f n b = NBLeave b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < n
    /\ 8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b.
Proof.
  induction f as [|f IH]; intros n b b' Hb Hh Hin Hf H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb_spec (br_bits b) n); [|discriminate].
    cbn [Z.of_nat] in Hf. lia.
  - destruct (Z.ltb_spec (br_bits b) n); [|discriminate].
    unfold br_pullbyte in H.
    destruct (Z.eqb_spec (br_have b) 0) as [E0|E0].
    + injection H as <-.
      repeat split; try reflexivity; try assumption; lia.
    + apply IH in H;
        [| cbn [br_bits]; lia
         | cbn [br_hold];
           pose proof (Hin (br_next b));
           pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b));
           lia
         | cbn [br_in]; exact Hin
         | cbn [br_bits]; lia ].
      cbn [br_have br_in br_hold br_bits] in H.
      destruct H as (H1 & H2 & H3 & H4 & H5).
      repeat split; try assumption; lia.
Qed.

Lemma inf_nb_leave :
  forall n b b',
    0 <= n ->
    0 <= br_bits b ->
    0 <= br_hold b ->
    (forall j, 0 <= br_in b j) ->
    inf_nb n b = NBLeave b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < n
    /\ 8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b.
Proof.
  intros n b b' Hn Hb Hh Hin H.
  apply (inf_nb_go_leave (Z.to_nat n) n b b' Hb Hh Hin); [|exact H].
  rewrite Z2Nat.id by lia. lia.
Qed.

(** ** the fetch loops (leave = pullbyte-fail only; the last guard gives
    the leave-state bits bound directly) *)
Lemma inf_fetch_go_leave :
  forall f t nb b b',
    (forall i, c_bits (t i) <= 15) ->
    0 <= br_hold b ->
    0 <= br_bits b ->
    (forall j, 0 <= br_in b j) ->
    inf_fetch_go f t nb b = FetchLeave b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < 15
    /\ 8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b.
Proof.
  induction f as [|f IH]; intros t nb b b' Ht Hh Hbb Hin H;
    cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb_spec (c_bits (t (br_bits_of nb b))) (br_bits b)) as [E|E];
    [discriminate|].
  pose proof (Ht (br_bits_of nb b)) as Hw.
  unfold br_pullbyte in H.
  destruct (Z.eqb_spec (br_have b) 0) as [E0|E0].
  - injection H as <-.
    repeat split; try reflexivity; try assumption; lia.
  - apply IH in H;
      [| exact Ht
       | cbn [br_hold];
         pose proof (Hin (br_next b));
         pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b));
         lia
       | cbn [br_bits]; lia
       | cbn [br_in]; exact Hin ].
    cbn [br_have br_in br_hold br_bits] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5).
    repeat split; try assumption; lia.
Qed.

Lemma inf_fetch_leave :
  forall t nb b b',
    (forall i, c_bits (t i) <= 15) ->
    0 <= br_hold b ->
    0 <= br_bits b ->
    (forall j, 0 <= br_in b j) ->
    inf_fetch t nb b = FetchLeave b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < 15
    /\ 8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b.
Proof. intros t nb b b'; apply inf_fetch_go_leave. Qed.

Lemma inf_fetch2_go_leave :
  forall f t lst b b',
    c_bits lst <= 15 ->
    (forall i, c_bits (t i) <= 15) ->
    0 <= br_hold b ->
    0 <= br_bits b ->
    (forall j, 0 <= br_in b j) ->
    inf_fetch2_go f t lst b = FetchLeave b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < 30
    /\ 8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b.
Proof.
  induction f as [|f IH]; intros t lst b b' Hl Ht Hh Hbb Hin H;
    cbn [inf_fetch2_go] in H; [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb_spec a bb) as [E|E]
  end; [discriminate|].
  match type of E with
  | _ < c_bits lst + c_bits (t ?ix) => pose proof (Ht ix) as Hw
  end.
  unfold br_pullbyte in H.
  destruct (Z.eqb_spec (br_have b) 0) as [E0|E0].
  - injection H as <-.
    repeat split; try reflexivity; try assumption; lia.
  - apply IH in H;
      [| exact Hl
       | exact Ht
       | cbn [br_hold];
         pose proof (Hin (br_next b));
         pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b));
         lia
       | cbn [br_bits]; lia
       | cbn [br_in]; exact Hin ].
    cbn [br_have br_in br_hold br_bits] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5).
    repeat split; try assumption; lia.
Qed.

(** ** [inf_decode] (leave = a fetch leave at either stage; stage-2 rides
    stage-1's Ok facts) *)
Lemma inf_decode_leave :
  forall sub t rb b b',
    (forall i, 0 <= c_bits (t i) <= 15) ->
    0 <= br_hold b -> 0 <= br_bits b ->
    (forall j, 0 <= br_in b j) ->
    inf_decode sub t rb b = DecLeave b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < 30
    /\ 8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b.
Proof.
  intros sub t rb b b' Ht Hh Hb Hin H.
  assert (Htu : forall i, c_bits (t i) <= 15)
    by (intros i; exact (proj2 (Ht i))).
  unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef;
    [| |discriminate].
  - (* stage-1 Ok, so the leave is stage-2's *)
    destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & ->).
    destruct (sub (t i0)); [|discriminate].
    destruct (inf_fetch2 t (t i0) b0) as [h1 b1|b1|] eqn:Ef2;
      [discriminate| |discriminate].
    injection H as <-.
    pose proof (inf_fetch_in _ _ _ _ _ Ef) as Fin.
    pose proof (inf_fetch_hold _ _ _ _ _ Hh Hb Hin Ef) as Fh.
    pose proof Ef as Ef'. apply inf_fetch_bud in Ef' as (Fbud & _).
    assert (Hin0 : forall j, 0 <= br_in b0 j)
      by (intros j; rewrite Fin; apply Hin).
    assert (Hb0 : 0 <= br_bits b0)
      by (pose proof (proj1 (Ht i0)); pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef); lia).
    destruct (inf_fetch2_go_leave _ _ _ _ _ (Htu i0) Htu Fh Hb0 Hin0 Ef2)
      as (L1 & L2 & L3 & L4 & L5).
    repeat split; try assumption; try lia.
    rewrite L2. exact Fin.
  - (* stage-1 leave *)
    injection H as <-.
    destruct (inf_fetch_go_leave _ _ _ _ _ Htu Hh Hb Hin Ef)
      as (L1 & L2 & L3 & L4 & L5).
    repeat split; try assumption; lia.
Qed.

(** ** [gz_strz]: a nonzero terminating byte means the WHOLE input was
    consumed (the NAME/COMMENT partial-string leave has [have' = 0]) *)
Lemma gz_strz_full :
  forall f a i have copy cp ln,
    gz_strz f a i have copy = Some (cp, ln) ->
    ln <> 0 ->
    have <= cp.
Proof.
  induction f as [|f IH]; intros a i have copy cp ln H Hln;
    cbn [gz_strz] in H; [discriminate|].
  destruct (negb (Z.eqb (a i) 0) && Z.ltb (copy + 1) have) eqn:E.
  - exact (IH _ _ _ _ _ _ H Hln).
  - injection H as <- <-.
    apply Bool.andb_false_iff in E.
    destruct E as [E|E].
    + apply Bool.negb_false_iff, Z.eqb_eq in E. congruence.
    + apply Z.ltb_ge in E. lia.
Qed.

(** ** [cl_step] / [cl_loop] leaves (CODELENS): the state's have/lens are
    FRAMED at a leave, and the reader is exhausted. *)
Lemma cl_step_leave :
  forall t nb tot s s',
    (forall i, 0 <= c_bits (t i) <= 15) ->
    0 <= br_hold (cl_br s) -> 0 <= br_bits (cl_br s) ->
    (forall j, 0 <= br_in (cl_br s) j) ->
    cl_step t nb tot s = ClLeave s' ->
    br_have (cl_br s') = 0
    /\ br_in (cl_br s') = br_in (cl_br s)
    /\ 0 <= br_hold (cl_br s')
    /\ 0 <= br_bits (cl_br s') < 30
    /\ 8 * br_have (cl_br s') + br_bits (cl_br s')
       = 8 * br_have (cl_br s) + br_bits (cl_br s)
    /\ cl_have s' = cl_have s
    /\ cl_lens s' = cl_lens s.
Proof.
  intros t nb tot s s' Ht Hh Hb Hin H.
  assert (Htu : forall i, c_bits (t i) <= 15)
    by (intros i; exact (proj2 (Ht i))).
  unfold cl_step in H.
  destruct (Z.leb tot (cl_have s)); [discriminate|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef.
  - (* FetchOk, so the leave is inf_nb's *)
    destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & Hhe).
    assert (Hcb : 0 <= c_bits h <= 15) by (rewrite Hhe; exact (Ht i0)).
    pose proof (inf_fetch_in _ _ _ _ _ Ef) as Fin.
    pose proof (inf_fetch_hold _ _ _ _ _ Hh Hb Hin Ef) as Fh.
    pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef) as Fble.
    pose proof Ef as Ef'. apply inf_fetch_bud in Ef' as (Fbud & _).
    destruct (Z.ltb (c_val h) 16); [discriminate|].
    destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                      else if Z.eqb (c_val h) 17 then c_bits h + 3
                      else c_bits h + 7) b) as [b'|b'] eqn:Enb.
    + (* NBOk: no leave below this point *)
      exfalso. cbv zeta in H.
      destruct (Z.eqb (c_val h) 16); cbv beta iota in H.
      { destruct (Z.eqb (cl_have s) 0); cbv beta iota in H;
          [discriminate|].
        destruct (Z.ltb tot _) in H; discriminate. }
      destruct (Z.eqb (c_val h) 17); cbv beta iota in H.
      { destruct (Z.ltb tot _) in H; discriminate. }
      destruct (Z.ltb tot _) in H; discriminate.
    + (* NBLeave *)
      assert (Hneed : 0 <= (if Z.eqb (c_val h) 16 then c_bits h + 2
                            else if Z.eqb (c_val h) 17 then c_bits h + 3
                            else c_bits h + 7)
                      /\ (if Z.eqb (c_val h) 16 then c_bits h + 2
                          else if Z.eqb (c_val h) 17 then c_bits h + 3
                          else c_bits h + 7) <= 22)
        by (destruct (Z.eqb (c_val h) 16); destruct (Z.eqb (c_val h) 17);
            lia).
      assert (Hinb : forall j, 0 <= br_in b j)
        by (intros j; rewrite Fin; apply Hin).
      destruct (inf_nb_leave _ b b' (proj1 Hneed) ltac:(lia) Fh Hinb Enb)
        as (L1 & L2 & L3 & L4 & L5).
      injection H as <-.
      cbn [cl_br cl_have cl_lens].
      repeat split; try assumption; try reflexivity; try lia.
      rewrite L2. exact Fin.
  - (* FetchLeave *)
    injection H as <-.
    destruct (inf_fetch_go_leave _ _ _ _ _ Htu Hh Hb Hin Ef)
      as (L1 & L2 & L3 & L4 & L5).
    cbn [cl_br cl_have cl_lens].
    repeat split; try assumption; try reflexivity; lia.
  - discriminate.
Qed.


(** ** Same-mode leave [ReachMode] builders (G1): the starvation leaves
    resume at the CURRENT mode, so the mode block is rebuilt from the
    arm's own premises; clauses for other modes discharge by mode
    discrimination. *)
Lemma reach_mode_lenext :
  forall q,
    q_mode q = M_LENEXT ->
    1 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 65535 ->
    0 <= u_extra (s_cur (q_st q)) <= 15 ->
    0 <= u_back (s_cur (q_st q)) <= 30 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    ReachMode q.
Proof.
  intros q Hm H1 Hub He Hbk HL Htp Hb Hwd Hds. constructor.
  - intros H; congruence.
  - intros _; exact H1.
  - intros _; exact He.
  - intros H; congruence.
  - split; [intros _; exact Hub
           | intros [H|[H|H]]; congruence].
  - intros _; exact HL.
  - intros H; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros _; exact Hbk | split; [intros H; congruence | intros H; congruence]].
  - intros [H|H]; congruence.
  - intros _; exact Htp.
  - intros H; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; congruence.
  - intros _; exact Hwd.
  - intros H; congruence.
  - intros _; exact Hds.
  - split; intros H; congruence.
  - intros H; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
Qed.

Lemma reach_mode_dist :
  forall q,
    q_mode q = M_DIST ->
    1 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 98303 ->
    0 <= u_back (s_cur (q_st q)) <= 45 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    ReachMode q.
Proof.
  intros q Hm H1 Hub Hbk HL Htp Hb Hwd Hds. constructor.
  - intros H; congruence.
  - intros _; exact H1.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros H; congruence | intros _; exact Hub].
  - intros _; exact HL.
  - intros H; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros H; congruence | split; [intros _; exact Hbk | intros H; congruence]].
  - intros [H|H]; congruence.
  - intros _; exact Htp.
  - intros H; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; congruence.
  - intros _; exact Hwd.
  - intros H; congruence.
  - intros _; exact Hds.
  - split; intros H; congruence.
  - intros H; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
Qed.

Lemma reach_mode_distext :
  forall q,
    q_mode q = M_DISTEXT ->
    1 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 98303 ->
    0 <= u_extra (s_cur (q_st q)) <= 15 ->
    0 <= u_offset (s_cur (q_st q)) ->
    u_offset (s_cur (q_st q)) + Z.shiftl 1 (u_extra (s_cur (q_st q)))
      <= 4294967296 ->
    0 <= u_back (s_cur (q_st q)) <= 75 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    u_offset (s_cur (q_st q)) < 65536 ->
    DistSubSide q ->
    1 <= u_offset (s_cur (q_st q)) ->
    ReachMode q.
Proof.
  intros q Hm H1 Hub He Ho1 Ho2 Hbk HL Htp Hb Hwd Ho16 Hds Hoff1. constructor.
  - intros H; congruence.
  - intros _; exact H1.
  - intros _; exact He.
  - intros _; split; [exact Ho1 | exact Ho2].
  - split; [intros H; congruence | intros _; exact Hub].
  - intros _; exact HL.
  - intros H; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros H; congruence | split; [intros H; congruence | intros _; exact Hbk]].
  - intros [H|H]; congruence.
  - intros _; exact Htp.
  - intros H; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; congruence.
  - intros _; exact Hwd.
  - intros _; exact Ho16.
  - intros _; exact Hds.
  - split; [intros _; exact Hoff1 | intros H; congruence].
  - intros H; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
Qed.

Lemma reach_mode_codelens :
  forall q',
    q_mode q' = M_CODELENS ->
    0 < b_nlen (s_bld (q_st q')) <= 288 ->
    0 < b_ndist (s_bld (q_st q')) <= 32 ->
    257 <= b_nlen (s_bld (q_st q')) <= 286 /\ 1 <= b_ndist (s_bld (q_st q')) <= 30 ->
    TblSide (tbl_of (q_st q') (t_lencode (s_tab (q_st q')))) ->
    TblPD (tbl_of (q_st q') (t_lencode (s_tab (q_st q')))) (t_lenbits (s_tab (q_st q'))) ->
    br_bits (q_br q') <= 14 ->
    t_lenbits (s_tab (q_st q')) <= 7 ->
    t_lencode (s_tab (q_st q')) = TRcodes 0 ->
    1 <= t_lenbits (s_tab (q_st q')) ->
    2 ^ t_lenbits (s_tab (q_st q')) <= t_next (s_tab (q_st q')) ->
    (forall i, 0 <= i < 2 ^ t_lenbits (s_tab (q_st q')) -> 0 <= c_op (t_codes (s_tab (q_st q')) i) < 256) ->
    ReachMode q'.
Proof.
  intros q' Hm Hnl Hnd Hnt Htl Htp Hb Hl7 Hc0 Hc1 Hc2 Hc3. constructor.
  - intros H; congruence.
  - intros [H|[H|H]]; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros H; congruence | intros [H|[H|H]]; congruence].
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - intros _; exact Htl.
  - intros _; split; [exact Hnl | exact Hnd].
  - intros H; congruence.
  - split; [|split]; intros H; congruence.
  - intros _; exact Hnt.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - intros _; split; [exact Htp | exact Hl7].
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - intros H; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - split; intros H; congruence.
  - intros H; congruence.
  - (* rm_tblCL0 (T2) *) intros _; exact Hc0.
  - (* rm_tblCL1 (T2) *) intros _; exact Hc1.
  - (* rm_tblCL2 (T2) *) intros _; exact Hc2.
  - (* rm_tblCL3 (T2) *) intros _; exact Hc3.
Qed.

Lemma reach_mode_lenlens :
  forall q',
    q_mode q' = M_LENLENS ->
    (forall h, 0 <= h < b_have (s_bld (q_st q')) ->
       0 <= b_lens (s_bld (q_st q')) (inf_order h) <= 7) ->
    0 < b_nlen (s_bld (q_st q')) <= 288 ->
    0 < b_ndist (s_bld (q_st q')) <= 32 ->
    257 <= b_nlen (s_bld (q_st q')) <= 286 /\ 1 <= b_ndist (s_bld (q_st q')) <= 30 ->
    br_bits (q_br q') <= 14 ->
    ReachMode q'.
Proof.
  intros q' Hm Hl7 Hnl Hnd Hnt Hb. constructor.
  - intros H; congruence.
  - intros [H|[H|H]]; congruence.
  - intros [H|H]; congruence.
  - intros H; congruence.
  - split; [intros H; congruence | intros [H|[H|H]]; congruence].
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - intros H; congruence.
  - intros _; split; [exact Hnl | exact Hnd].
  - intros _; exact Hl7.
  - split; [|split]; intros H; congruence.
  - intros _; exact Hnt.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - intros H; congruence.
  - intros _; exact Hb.
  - repeat apply conj; [intros H _|intros H _|intros [H|[H|H]]|intros H _|intros [H|[H|H]]]; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - intros H; congruence.
  - intros [H|[H|[H|[H|[H|[H|H]]]]]]; congruence.
  - split; intros H; congruence.
  - intros H; congruence.
  (* T2 res-t2 (R2083 section 2): rm_tblCL0..3 are vacuous at this constructor's modes *)
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
  - intros H; congruence.
Qed.

(** ** The four arms that never [InfCont] *)
Lemma pres_MEM  : forall c q, PresOk c (inf_MEM q).
Proof. intros c q. cbv. lia. Qed.
Lemma pres_SYNC : forall c q, PresOk c (inf_SYNC q).
Proof. intros c q. cbv. lia. Qed.
Lemma pres_BAD  :
  forall c q, q_mode q = M_BAD -> ReachCore q -> PresOk c (inf_BAD q).
Proof.
  intros c q Hm HC. unfold inf_BAD. split.
  - split.
    + apply (reach_core_conv q); [exact HC|reflexivity..].
    + apply reach_mode_inactive; unfold q_mode; bsimp;
        unfold q_mode in Hm; rewrite Hm; reflexivity.
  - intros _ Hr. exfalso.
    cbv [qset_ret q_ret Z_DATA_ERROR Z_OK] in Hr. lia.
Qed.
Lemma pres_DONE :
  forall c q, q_mode q = M_DONE -> ReachCore q -> PresOk c (inf_DONE q).
Proof.
  intros c q Hm HC. unfold inf_DONE. split.
  - split.
    + apply (reach_core_conv q); [exact HC|reflexivity..].
    + apply reach_mode_inactive; unfold q_mode; bsimp;
        unfold q_mode in Hm; rewrite Hm; reflexivity.
  - intros _ Hr. exfalso.
    cbv [qset_ret q_ret Z_STREAM_END Z_OK] in Hr. lia.
Qed.

(** ** [inf_LENGTH] / [inf_CHECK] *)
Lemma pres_LENGTH :
  forall c q, q_mode q = M_LENGTH -> ReachCore q -> PresOk c (inf_LENGTH q).
Proof.
  intros c q Hm HC. unfold inf_LENGTH. cbv zeta.
  core_facts q HC.
  destruct (negb (Z.eqb (h_wrap (s_hdr (q_st q))) 0)
            && negb (Z.eqb (h_flags (s_hdr (q_st q))) 0));
    [| apply pres_DONE;
       [ unfold q_mode; bsimp; reflexivity
       | apply (reach_core_conv q); [exact HC|reflexivity..] ]].
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 32 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 32 _ b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
            && negb (Z.eqb (br_hold b)
                       (Z.land (h_total (s_hdr (q_st q))) 4294967295)));
    [| apply pres_DONE;
       [ unfold q_mode; bsimp; reflexivity | rc_close q ]].
  split; [rc_close q | rm_off].
Qed.

Lemma pres_CHECK :
  forall c q, q_mode q = M_CHECK -> ReachCore q -> PresOk c (inf_CHECK q).
Proof.
  intros c q Hm HC. unfold inf_CHECK. cbv zeta.
  core_facts q HC.
  destruct (Z.eqb (h_wrap (s_hdr (q_st q))) 0).
  { apply pres_LENGTH; [unfold q_mode; bsimp; reflexivity|].
    apply (reach_core_conv q); [exact HC|reflexivity..]. }
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 32 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 32 _ b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  (* the check-update conditional inside [q4], then the check test *)
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
            && negb (Z.eqb (q_out q - o_left (q_ob q)) 0));
    match goal with
    | |- context [if ?cond then InfCont _ else _] => destruct cond
    end.
  - split; [rc_close q | rm_off].
  - apply pres_LENGTH; [unfold q_mode; bsimp; reflexivity|]. rc_close q.
  - split; [rc_close q | rm_off].
  - apply pres_LENGTH; [unfold q_mode; bsimp; reflexivity|]. rc_close q.
Qed.

(** ** [inf_LIT] *)
Lemma pres_LIT :
  forall c q,
    q_mode q = M_LIT ->
    ReachCore q -> LenTblSide q -> TblPDSide q -> br_bits (q_br q) <= 14 -> TblWidSide q -> DistSubSide q ->
    PresOk c (inf_LIT q).
Proof.
  intros c q Hm HC HL Htp Hb14 Hwd Hds. unfold inf_LIT. cbv zeta.
  core_facts q HC.
  destruct (Z.eqb (o_left (q_ob q)) 0) eqn:El;
    [ split;
      [ split;
        [ exact HC
        | exact (reach_mode_scc q (or_intror (or_intror Hm)) HL Htp Hb14 Hwd Hds) ]
      | intros _ _; right; apply Z.eqb_eq in El; exact El ] |].
  apply Z.eqb_neq in El.
  split.
  - rc_close q.
    first [ apply zset_bytes; [exact Fob | apply u8_range]
          | apply ob_write_bytes; [exact Fob | apply u8_range] ].
  - apply reach_mode_scc.
    + left. bsimp. reflexivity.
    + apply (len_tbl_side_frame q); [reflexivity | exact HL].
    + apply (tblpd_frame q); [reflexivity | exact Htp].
    + bsimp. exact Hb14.
    + apply (tblwid_frame q); [reflexivity | exact Hwd].
    + apply (dist_sub_frame q); [reflexivity | exact Hds].
Qed.

(** ** The stored-block family: [inf_COPY] / [inf_COPY_] / [inf_STORED] *)
Lemma pres_COPY :
  forall c q,
    q_mode q = M_COPY -> ReachCore q -> br_bits (q_br q) = 0 ->
    PresOk c (inf_COPY q).
Proof.
  intros c q Hm HC Hb0. unfold inf_COPY. cbv zeta.
  core_facts q HC.
  destruct (Z.eqb (u_length (s_cur (q_st q))) 0) eqn:Ecp.
  { split.
    - apply (reach_core_conv q); [exact HC|reflexivity..].
    - apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity | change (br_bits (q_br q) <= 14); lia]. }
  remember (if Z.ltb (br_have (q_br q)) (u_length (s_cur (q_st q)))
            then br_have (q_br q) else u_length (s_cur (q_st q)))
    as c1 eqn:Ec1.
  remember (if Z.ltb (o_left (q_ob q)) c1 then o_left (q_ob q) else c1)
    as c2 eqn:Ec2.
  assert (Hc1 : 0 <= c1 <= br_have (q_br q)).
  { rewrite Ec1.
    destruct (Z.ltb_spec (br_have (q_br q)) (u_length (s_cur (q_st q))));
      lia. }
  assert (Hc2 : 0 <= c2 <= c1 /\ c2 <= o_left (q_ob q)).
  { rewrite Ec2. destruct (Z.ltb_spec (o_left (q_ob q)) c1); lia. }
  destruct (Z.eqb c2 0) eqn:Ec20;
    [ assert (Hc20 : c2 = 0) by (apply Z.eqb_eq; exact Ec20);
      assert (Hd1 : c1 = br_have (q_br q)
                    \/ c1 = u_length (s_cur (q_st q)))
        by (rewrite Ec1;
            destruct (Z.ltb_spec (br_have (q_br q))
                        (u_length (s_cur (q_st q))));
            [left|right]; reflexivity);
      assert (Hd2 : c2 = o_left (q_ob q) \/ c2 = c1)
        by (rewrite Ec2; destruct (Z.ltb_spec (o_left (q_ob q)) c1);
            [left|right]; reflexivity);
      split;
      [ split;
        [ exact HC
        | apply reach_mode_hdr0; [do 8 right; exact Hm | b0_pre Hm; exact Hb0 | rewrite Hm; intros E; discriminate E] ]
      | intros _ _; apply Z.eqb_neq in Ecp;
        destruct Hd2 as [D2|D2];
        [ right; lia
        | destruct Hd1 as [D1|D1]; [left; lia | exfalso; lia] ] ] |].
  split.
  - pose proof (u32_range (u_length (s_cur (q_st q)) - c2)).
    rc_close q.
    apply zcopy_bytes; [exact Fob | exact (rc_bytes q HC)].
  - apply reach_mode_hdr0; [do 8 right; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; first [exact Hb0 | lia] | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E].
Qed.

Lemma pres_COPY_ :
  forall c q, ReachCore q -> br_bits (q_br q) = 0 -> PresOk c (inf_COPY_ q).
Proof.
  intros c q HC Hb0. unfold inf_COPY_.
  apply pres_COPY.
  - bsimp. reflexivity.
  - apply (reach_core_conv q); [exact HC|reflexivity..].
  - exact Hb0.
Qed.

Lemma pres_STORED :
  forall c q, q_mode q = M_STORED -> ReachCore q ->
    PresOk c (inf_STORED c q).
Proof.
  intros c q Hm HC. unfold inf_STORED. cbv zeta.
  core_facts q HC.
  pose proof (land7_range (br_bits (q_br q)) Hb) as Hl7.
  destruct (inf_nb 32 (br_bytebits (q_br q))) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 32 (br_bytebits (q_br q)) b ltac:(lia)
          ltac:(cbn [br_bytebits br_dropbits br_bits]; lia)
          (dropbits_hold_nonneg _ _ Fhold)
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       cbn [br_bytebits br_dropbits br_have br_bits br_in]
         in Lh0, Lin, Lbits, Lbud;
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  cbn [br_bytebits br_dropbits br_have br_bits] in E1, E2, E3.
  specialize (E3 Hh).
  destruct (inf_nb_env 32 (br_bytebits (q_br q)) b ltac:(lia)
              (dropbits_hold_nonneg _ _ Fhold)
              ltac:(cbn [br_bytebits br_dropbits br_bits]; lia)
              (fun j => proj1 (rc_bytes q HC j))
              ltac:(cbn [br_bytebits br_dropbits br_bits]; lia) Enb)
    as (Nin & Nh & N39).
  cbn [br_bytebits br_dropbits br_in] in Nin.
  destruct (negb (Z.eqb (Z.land (br_hold b) 65535)
                    (Z.lxor (Z.shiftr (br_hold b) 16) 65535))).
  { split; [rc_close q | rm_off]. }
  assert (Hlv : 0 <= Z.land (u32 (br_hold b)) 65535)
    by (apply Z.land_nonneg; right; lia).
  destruct (Z.eqb (n_flush c) Z_TREES) eqn:Efl;
    [ split;
      [ split;
        [ rc_close q
        | apply reach_mode_hdr0;
          [ do 7 right; left; unfold q_mode; bsimp; reflexivity
          | unfold Bits0Side; repeat apply conj; intros Hm0; try (destruct Hm0 as [Hm0|[Hm0|Hm0]]);
            unfold q_mode in Hm0; bsimp_in Hm0; try discriminate Hm0; try intros _; bsimp; cbn [br_initbits br_bits]; lia
          | unfold q_mode; bsimp; intros E; discriminate E ] ]
      | intros Hf _; exfalso; rewrite Hf in Efl;
        cbv in Efl; discriminate ] |].
  apply pres_COPY_.
  - rc_close q.
  - ksimp. cbn [br_initbits br_bits]. lia.
Qed.

(** ** [inf_TYPEDO] / [inf_TYPE] / [inf_DICT] / [inf_DICTID] *)
Lemma pres_TYPEDO :
  forall c q, q_mode q = M_TYPEDO \/ q_mode q = M_TYPE -> ReachCore q ->
    br_bits (q_br q) <= 14 ->
    PresOk c (inf_TYPEDO c q).
Proof.
  intros c q Hm HC Hb14. unfold inf_TYPEDO. cbv zeta.
  core_facts q HC.
  pose proof (land7_range (br_bits (q_br q)) Hb) as Hl7.
  destruct (negb (Z.eqb (h_last (s_hdr (q_st q))) 0)).
  { (* -> CHECK, over a byte-aligned reader *)
    split; [rc_close q | rm_off]. }
  destruct (inf_nb 3 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 3 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr;
           [ unfold q_mode; bsimp; unfold q_mode in Hm;
             destruct Hm as [Hm|Hm]; rewrite Hm; [right; left | left]; reflexivity
           | bsimp; lia ] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as Eok.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  pose proof (inf_nb_ok_le _ _ _ Enb) as Ele.
  destruct (inf_nb_env 3 _ b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (Z.eqb (br_bits_of 2 (br_dropbits 1 b)) 0).
  { split; [rc_close q | rm_off]. }
  destruct (Z.eqb (br_bits_of 2 (br_dropbits 1 b)) 1).
  { (* fixed tables installed; -> LEN_ *)
    destruct (Z.eqb (n_flush c) Z_TREES) eqn:Efl;
      [ split;
        [ split;
          [ rc_close q
          | apply reach_mode_scc;
            [ right; left; bsimp; reflexivity
            | apply fixed_len_tbl_side;
              (split; [reflexivity|]); (split; [reflexivity|]);
              split; reflexivity
            | unfold TblPDSide, tbl_of, fixedtables; ksimp; exact fix_tblpd
            | bsimp; c6bits
            | unfold TblWidSide, tbl_of, fixedtables; ksimp; exact fix_tblwid
            | unfold DistSubSide, tbl_of, fixedtables; ksimp; exact fix_dsub ] ]
        | intros Hf _; exfalso; rewrite Hf in Efl;
          cbv in Efl; discriminate ] |].
    split.
    - rc_close q.
    - apply reach_mode_scc.
      + right; left. bsimp. reflexivity.
      + apply fixed_len_tbl_side.
        split; [reflexivity|]. split; [reflexivity|].
        split; reflexivity.
      + unfold TblPDSide, tbl_of, fixedtables. ksimp. exact fix_tblpd.
      + bsimp. c6bits.
      + unfold TblWidSide, tbl_of, fixedtables. ksimp. exact fix_tblwid.
      + unfold DistSubSide, tbl_of, fixedtables. ksimp. exact fix_dsub. }
  destruct (Z.eqb (br_bits_of 2 (br_dropbits 1 b)) 2).
  { split; [rc_close q | apply reach_mode_hdr; [right; right; unfold q_mode; bsimp; reflexivity | bsimp; c6bits]]. }
  split; [rc_close q | rm_off].
Qed.

Lemma pres_TYPE :
  forall c q, q_mode q = M_TYPE -> ReachCore q -> br_bits (q_br q) <= 14 -> PresOk c (inf_TYPE c q).
Proof.
  intros c q Hm HC Hb14. unfold inf_TYPE.
  destruct (Z.eqb (n_flush c) Z_BLOCK || Z.eqb (n_flush c) Z_TREES)
    eqn:Efl;
    [ split;
      [ split;
        [ exact HC
        | apply reach_mode_hdr; [left; exact Hm | exact Hb14] ]
      | intros Hf _; exfalso; rewrite Hf in Efl;
        cbv in Efl; discriminate ] |].
  apply pres_TYPEDO; [right; exact Hm | exact HC | exact Hb14].
Qed.

Lemma pres_DICT :
  forall c q, ReachCore q -> br_bits (q_br q) <= 14 -> PresOk c (inf_DICT c q).
Proof.
  intros c q HC Hb14. unfold inf_DICT.
  destruct (Z.eqb (h_havedict (s_hdr (q_st q))) 0); [cbv; lia|].
  apply pres_TYPE; [unfold q_mode; bsimp; reflexivity| | exact Hb14].
  apply (reach_core_conv q); [exact HC|reflexivity..].
Qed.

Lemma pres_DICTID :
  forall c q, q_mode q = M_DICTID -> ReachCore q ->
    PresOk c (inf_DICTID c q).
Proof.
  intros c q Hm HC. unfold inf_DICTID.
  core_facts q HC.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 32 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_in _ _ _ Enb) as Nin.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  apply pres_DICT.
  - rc_close q.
  - bsimp. cbn [br_initbits br_bits]. lia.
Qed.

(** ** [inf_HCRC] (the header chain's shared tail) *)
Lemma pres_HCRC :
  forall c q, q_mode q = M_HCRC -> ReachCore q -> (Z.land (h_flags (s_hdr (q_st q))) 512 = 0 -> br_bits (q_br q) = 0) ->
    PresOk c (inf_HCRC q).
Proof.
  intros c q Hm HC Hb0. unfold inf_HCRC. cbv zeta.
  core_facts q HC.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)) eqn:Ef.
  - destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 16 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr0;
           [ do 5 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm
           | b0_pre Hm; intros Hg0; exfalso; bsimp_in Hg0; apply Bool.negb_true_iff in Ef; apply Z.eqb_neq in Ef; exact (Ef Hg0)
           | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E ] ]
       | intros _ _; left; exact Lh0 ] ].
    pose proof Enb as Enb'.
    apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
    destruct (inf_nb_env 16 _ b ltac:(lia) Fhold Hb
                (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
      as (Nin & Nh & N39).
    destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
              && negb (Z.eqb (br_hold b)
                         (Z.land (h_check (s_hdr (q_st q))) 65535)));
      [ split; [rc_close q | rm_off]
      | split; [rc_close q | apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity | bsimp; cbn [br_initbits br_bits]; lia]] ].
  - split.
    + apply (reach_core_conv q); [exact HC|reflexivity..].
    + apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity
                            | apply Bool.negb_false_iff in Ef; apply Z.eqb_eq in Ef; pose proof (Hb0 Ef) as E0; change (br_bits (q_br q) <= 14); lia].
Qed.

(** ** The gzip header chain (br-side only: [inf_nb] env pack,
    [gz_strz_spec], [br_consume]) *)
Lemma pres_COMMENT :
  forall c q, q_mode q = M_COMMENT -> ReachCore q -> br_bits (q_br q) = 0 -> PresOk c (inf_COMMENT q).
Proof.
  intros c q Hm HC Hb0. unfold inf_COMMENT. cbv zeta.
  core_facts q HC.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 4096) 0)).
  2:{ apply pres_HCRC; [unfold q_mode; bsimp; reflexivity| | c6hdr].
      apply (reach_core_conv q); [exact HC|reflexivity..]. }
  destruct (Z.eqb (br_have (q_br q)) 0) eqn:Eh0;
    [ split;
      [ split;
        [ exact HC
        | apply reach_mode_hdr0; [do 4 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; apply Z.eqb_eq in Eh0; exact Eh0 ] |].
  apply Z.eqb_neq in Eh0.
  destruct (gz_strz (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
              (br_next (q_br q)) (br_have (q_br q)) 0)
    as [[copy len]|] eqn:Egz; [|exact I].
  pose proof (gz_strz_spec (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                (br_next (q_br q)) (br_have (q_br q)) 0 copy len
                ltac:(lia) Egz) as Hcp.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
    destruct (negb (Z.eqb len 0)) eqn:Elz;
    [ apply Bool.negb_true_iff in Elz; apply Z.eqb_neq in Elz;
      pose proof (gz_strz_full _ _ _ _ _ _ _ Egz Elz) as Hfull;
      destruct Hcp as (Hcp1 & Hcp2);
      split;
      [ split;
        [ rc_close q;
          cbn [br_consume br_have br_bits br_next br_hold br_in];
          try reflexivity; try assumption; try lia
        | apply reach_mode_hdr0; [do 4 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; ksimp; cbn [br_consume br_have]; lia ]
    | apply pres_HCRC; [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr]
    | apply Bool.negb_true_iff in Elz; apply Z.eqb_neq in Elz;
      pose proof (gz_strz_full _ _ _ _ _ _ _ Egz Elz) as Hfull;
      destruct Hcp as (Hcp1 & Hcp2);
      split;
      [ split;
        [ rc_close q;
          cbn [br_consume br_have br_bits br_next br_hold br_in];
          try reflexivity; try assumption; try lia
        | apply reach_mode_hdr0; [do 4 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; ksimp; cbn [br_consume br_have]; lia ]
    | apply pres_HCRC; [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr] ].
Qed.

Lemma pres_NAME :
  forall c q, q_mode q = M_NAME -> ReachCore q -> br_bits (q_br q) = 0 -> PresOk c (inf_NAME q).
Proof.
  intros c q Hm HC Hb0. unfold inf_NAME. cbv zeta.
  core_facts q HC.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 2048) 0)).
  2:{ apply pres_COMMENT; [unfold q_mode; bsimp; reflexivity| | c6hdr]. rc_close q. }
  destruct (Z.eqb (br_have (q_br q)) 0) eqn:Eh0;
    [ split;
      [ split;
        [ exact HC
        | apply reach_mode_hdr0; [do 3 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; apply Z.eqb_eq in Eh0; exact Eh0 ] |].
  apply Z.eqb_neq in Eh0.
  destruct (gz_strz (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
              (br_next (q_br q)) (br_have (q_br q)) 0)
    as [[copy len]|] eqn:Egz; [|exact I].
  pose proof (gz_strz_spec (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                (br_next (q_br q)) (br_have (q_br q)) 0 copy len
                ltac:(lia) Egz) as Hcp.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
    destruct (negb (Z.eqb len 0)) eqn:Elz;
    [ apply Bool.negb_true_iff in Elz; apply Z.eqb_neq in Elz;
      pose proof (gz_strz_full _ _ _ _ _ _ _ Egz Elz) as Hfull;
      destruct Hcp as (Hcp1 & Hcp2);
      split;
      [ split;
        [ rc_close q;
          cbn [br_consume br_have br_bits br_next br_hold br_in];
          try reflexivity; try assumption; try lia
        | apply reach_mode_hdr0; [do 3 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; ksimp; cbn [br_consume br_have]; lia ]
    | apply pres_COMMENT; [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr]
    | apply Bool.negb_true_iff in Elz; apply Z.eqb_neq in Elz;
      pose proof (gz_strz_full _ _ _ _ _ _ _ Egz Elz) as Hfull;
      destruct Hcp as (Hcp1 & Hcp2);
      split;
      [ split;
        [ rc_close q;
          cbn [br_consume br_have br_bits br_next br_hold br_in];
          try reflexivity; try assumption; try lia
        | apply reach_mode_hdr0; [do 3 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; ksimp; cbn [br_consume br_have]; lia ]
    | apply pres_COMMENT; [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr] ].
Qed.

Lemma pres_EXTRA :
  forall c q, q_mode q = M_EXTRA -> ReachCore q -> br_bits (q_br q) = 0 -> PresOk c (inf_EXTRA q).
Proof.
  intros c q Hm HC Hb0. unfold inf_EXTRA. cbv zeta.
  core_facts q HC.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 1024) 0)).
  2:{ apply pres_NAME; [unfold q_mode; bsimp; reflexivity| | c6hdr]. rc_close q. }
  remember (if Z.ltb (br_have (q_br q)) (u_length (s_cur (q_st q)))
            then br_have (q_br q) else u_length (s_cur (q_st q)))
    as copy eqn:Ecp.
  assert (Hcp : 0 <= copy <= br_have (q_br q)
                /\ copy <= u_length (s_cur (q_st q))).
  { rewrite Ecp.
    destruct (Z.ltb_spec (br_have (q_br q)) (u_length (s_cur (q_st q))));
      lia. }
  destruct (negb (Z.eqb copy 0)) eqn:Ecz.
  - destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      match goal with
      | |- context [if ?c then InfLeave _ else _] => destruct c eqn:Elv
      end;
      try (apply pres_NAME;
           [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr]);
      apply Bool.negb_true_iff in Elv; apply Z.eqb_neq in Elv;
      revert Elv; ksimp; intros Elv;
      assert (Hd : copy = br_have (q_br q)
                   \/ copy = u_length (s_cur (q_st q)))
        by (rewrite Ecp;
            destruct (Z.ltb_spec (br_have (q_br q))
                        (u_length (s_cur (q_st q))));
            [left|right]; reflexivity);
      destruct Hcp as (Hcp1 & Hcp2);
      (split;
       [ split;
         [ rc_close q;
           cbn [br_consume br_have br_bits br_next br_hold br_in];
           try reflexivity; try assumption; try lia
         | apply reach_mode_hdr0; [do 2 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
       | intros _ _; left; ksimp; cbn [br_consume br_have]; lia ]).
  - apply Bool.negb_false_iff, Z.eqb_eq in Ecz.
    match goal with
    | |- context [if ?c then InfLeave _ else _] => destruct c eqn:Elv
    end;
    [ apply Bool.negb_true_iff in Elv; apply Z.eqb_neq in Elv;
      revert Elv; ksimp; intros Elv;
      assert (Hd : copy = br_have (q_br q)
                   \/ copy = u_length (s_cur (q_st q)))
        by (rewrite Ecp;
            destruct (Z.ltb_spec (br_have (q_br q))
                        (u_length (s_cur (q_st q))));
            [left|right]; reflexivity);
      destruct Hcp as (Hcp1 & Hcp2);
      split;
      [ split;
        [ exact HC
        | apply reach_mode_hdr0; [do 2 right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm | b0_pre Hm; bsimp; cbn [br_consume br_bits]; lia | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E] ]
      | intros _ _; left; lia ] |].
    apply pres_NAME; [unfold q_mode; bsimp; reflexivity| | c6hdr]. rc_close q.
Qed.

Lemma pres_EXLEN :
  forall c q, q_mode q = M_EXLEN -> ReachCore q -> (Z.land (h_flags (s_hdr (q_st q))) 1024 = 0 -> br_bits (q_br q) = 0) ->
    PresOk c (inf_EXLEN q).
Proof.
  intros c q Hm HC Hb0. unfold inf_EXLEN. cbv zeta.
  core_facts q HC.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 1024) 0)) eqn:Ef.
  2:{ apply pres_EXTRA; [unfold q_mode; bsimp; reflexivity| | apply Bool.negb_false_iff in Ef; apply Z.eqb_eq in Ef; pose proof (Hb0 Ef) as E0; bsimp; lia].
      apply (reach_core_conv q); [exact HC|reflexivity..]. }
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 16 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr0;
           [ right; left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm
           | b0_pre Hm; intros Hg0; exfalso; bsimp_in Hg0; apply Bool.negb_true_iff in Ef; apply Z.eqb_neq in Ef; exact (Ef Hg0)
           | unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; intros E; discriminate E ] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 16 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
    (apply pres_EXTRA; [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr]).
Qed.

Lemma pres_OS :
  forall c q, q_mode q = M_OS -> ReachCore q -> PresOk c (inf_OS q).
Proof.
  intros c q Hm HC. unfold inf_OS. cbv zeta.
  core_facts q HC.
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 16 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 16 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
    (apply pres_EXLEN; [unfold q_mode; bsimp; reflexivity | rc_close q | c6hdr]).
Qed.

Lemma pres_TIME :
  forall c q, q_mode q = M_TIME -> ReachCore q -> PresOk c (inf_TIME q).
Proof.
  intros c q Hm HC. unfold inf_TIME. cbv zeta.
  core_facts q HC.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 32 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 32 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
    (apply pres_OS; [unfold q_mode; bsimp; reflexivity | rc_close q]).
Qed.

Lemma pres_FLAGS :
  forall c q, q_mode q = M_FLAGS -> ReachCore q -> PresOk c (inf_FLAGS q).
Proof.
  intros c q Hm HC. unfold inf_FLAGS. cbv zeta.
  core_facts q HC.
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 16 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_inactive; unfold q_mode; bsimp;
           unfold q_mode in Hm; rewrite Hm; reflexivity ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 16 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  match goal with
  | |- context [if ?c then InfCont _ else _] => destruct c
  end.
  { split; [rc_close q | rm_off]. }
  match goal with
  | |- context [if ?c then InfCont _ else _] => destruct c
  end.
  { split; [rc_close q | rm_off]. }
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (set_flags (q_st q)
                                                    (br_hold b)))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (set_flags (q_st q)
                                                     (br_hold b)))) 4) 0));
    (apply pres_TIME; [unfold q_mode; bsimp; reflexivity | rc_close q]).
Qed.

Lemma pres_HEAD :
  forall c q, q_mode q = M_HEAD -> ReachCore q -> (h_wrap (s_hdr (q_st q)) = 0 -> br_bits (q_br q) = 0) ->
    (q_mode q = M_HEAD -> q_out q - o_left (q_ob q) = 0) ->
    PresOk c (inf_HEAD c q).
Proof.
  intros c q Hm HC Hb0 Hw0. unfold inf_HEAD. cbv zeta.
  core_facts q HC.
  destruct (Z.eqb (h_wrap (s_hdr (q_st q))) 0) eqn:Ew.
  { apply pres_TYPEDO; [left; unfold q_mode; bsimp; reflexivity| | apply Z.eqb_eq in Ew; pose proof (Hb0 Ew) as E0; change (br_bits (q_br q) <= 14); lia].
    apply (reach_core_conv q); [exact HC|reflexivity..]. }
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 16 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr0;
           [ left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm
           | b0_pre Hm; intros Hg0; exfalso; bsimp_in Hg0; apply Z.eqb_neq in Ew; exact (Ew Hg0)
           | unfold q_mode; bsimp; intros _; exact (Hw0 Hm) ] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as Eok.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 16 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 2) 0)
            && Z.eqb (br_hold b) 35615).
  { (* gzip magic -> FLAGS *)
    destruct (Z.eqb (w_wbits (s_win (q_st q))) 0);
      (split; [rc_close q | rm_off]). }
  match goal with
  | |- context [if ?c then InfCont (qbad _ MSG_HEADER_CHECK) else _] =>
      destruct c
  end.
  { split; [rc_close q | rm_off]. }
  destruct (negb (Z.eqb (br_bits_of 4 b) Z_DEFLATED)).
  { split; [rc_close q | rm_off]. }
  destruct (Z.eqb (w_wbits (s_win (q_st q))) 0);
    match goal with
    | |- context [if ?c then InfCont (qbad _ MSG_WINDOW_SIZE) else _] =>
        destruct c
    end;
    try (split; [rc_close q | rm_off]);
    destruct (Z.eqb (Z.land (br_hold (br_dropbits 4 b)) 512) 0);
    (split; [rc_close q | first [ rm_off | apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity | c6hdr] ] ]).
Qed.

(** ** The LEN-loop slow arms: MATCH / DISTEXT / DIST / LENEXT

    The shared MATCH tail (both copy branches end in the same
    write-back), stated over an abstract [cw3]/[src] so the two branches
    instantiate it with their own min-chains. *)
(** The two min-chains MATCH selects its copy count with, as closed
    bound packages (destructing the nested ifs inside a lia goal
    disconnects the hypothesis-side atoms — package first instead). *)
Lemma min3_facts :
  forall len ol cw1,
    1 <= len -> 0 <= ol -> 0 <= cw1 ->
    0 <= (if Z.ltb ol (if Z.ltb len cw1 then len else cw1)
          then ol else (if Z.ltb len cw1 then len else cw1))
    /\ (if Z.ltb ol (if Z.ltb len cw1 then len else cw1)
        then ol else (if Z.ltb len cw1 then len else cw1)) <= len
    /\ (if Z.ltb ol (if Z.ltb len cw1 then len else cw1)
        then ol else (if Z.ltb len cw1 then len else cw1)) <= ol.
Proof.
  intros len ol cw1 H1 H2 H3.
  destruct (Z.ltb_spec len cw1); cbv iota;
    [destruct (Z.ltb_spec ol len) | destruct (Z.ltb_spec ol cw1)];
    cbv iota; repeat split; lia.
Qed.

Lemma min2_facts :
  forall len ol, 1 <= len -> 0 <= ol ->
    0 <= (if Z.ltb ol len then ol else len)
    /\ (if Z.ltb ol len then ol else len) <= len
    /\ (if Z.ltb ol len then ol else len) <= ol.
Proof. intros len ol H1 H2; destruct (Z.ltb_spec ol len); repeat split; lia. Qed.

Lemma match_tail_pres :
  forall c q src cw3,
    q_mode q = M_MATCH ->
    ReachCore q ->
    match_side q ->
    u_length (s_cur (q_st q)) <= 98303 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    1 <= u_offset (s_cur (q_st q)) ->
    0 <= cw3 ->
    cw3 <= u_length (s_cur (q_st q)) ->
    cw3 <= o_left (q_ob q) ->
    PresOk c
      (InfCont
         (if Z.eqb (u_length (s_cur (q_st q)) - cw3) 0
          then qmode (qset_ob (qset_st q (set_length (q_st q)
                        (u32 (u_length (s_cur (q_st q)) - cw3))))
                       (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                          (q_ob q) src)) M_LEN
          else qset_ob (qset_st q (set_length (q_st q)
                        (u32 (u_length (s_cur (q_st q)) - cw3))))
                 (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                    (q_ob q) src))).
Proof.
  intros c q src cw3 Hm HC HMS Hub HL Htp Hb14 Hwd Hds Ho1 Hc0 Hcl Hco.
  pose proof HMS as (Hlen1 & Hoffr & Hwn0).
  core_facts q HC.
  unfold q_mode in Hm.
  pose proof (ob_copyn_left (Z.to_nat cw3) (w_win (s_win (q_st q)))
                (q_ob q) src) as Hobl.
  rewrite Z2Nat.id in Hobl by exact Hc0.
  assert (Hu : u32 (u_length (s_cur (q_st q)) - cw3)
               = u_length (s_cur (q_st q)) - cw3)
    by (apply u32_id; lia).
  destruct (Z.eqb (u_length (s_cur (q_st q)) - cw3) 0) eqn:Ez;
    [apply Z.eqb_eq in Ez | apply Z.eqb_neq in Ez]; split.
  - rc_close q.
    apply ob_copyn_bytes; [exact (rc_win q HC) | exact Fob].
  - apply reach_mode_scc.
    + left. unfold q_mode. bsimp. reflexivity.
    + apply (len_tbl_side_frame q); [reflexivity | exact HL].
    + apply (tblpd_frame q); [reflexivity | exact Htp].
    + bsimp. exact Hb14.
    + apply (tblwid_frame q); [reflexivity | exact Hwd].
    + apply (dist_sub_frame q); [reflexivity | exact Hds].
  - rc_close q.
    apply ob_copyn_bytes; [exact (rc_win q HC) | exact Fob].
  - apply reach_mode_match.
    + unfold q_mode. bsimp. exact Hm.
    + unfold match_side. ksimp. rewrite Hu.
      repeat split; try assumption; try lia.
    + ksimp. rewrite Hu. lia.
    + apply (len_tbl_side_frame q); [reflexivity | exact HL].
    + apply (tblpd_frame q); [reflexivity | exact Htp].
    + bsimp. exact Hb14.
    + apply (tblwid_frame q); [reflexivity | exact Hwd].
    + apply (dist_sub_frame q); [reflexivity | exact Hds].
    + ksimp. exact Ho1.
Qed.

Lemma pres_MATCH :
  forall c q,
    q_mode q = M_MATCH ->
    ReachCore q ->
    match_side q ->
    u_length (s_cur (q_st q)) <= 98303 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    1 <= u_offset (s_cur (q_st q)) ->
    PresOk c (inf_MATCH q).
Proof.
  intros c q Hm HC HMS Hub HL Htp Hb14 Hwd Hds Ho1. unfold inf_MATCH. cbv zeta.
  pose proof HMS as (Hlen1 & Hoffr & Hwn0).
  core_facts q HC.
  destruct (Z.eqb (o_left (q_ob q)) 0) eqn:El;
    [ split;
      [ split;
        [ exact HC
        | exact (reach_mode_match q Hm HMS Hub HL Htp Hb14 Hwd Hds Ho1) ]
      | intros _ _; right; apply Z.eqb_eq in El; exact El ] |].
  apply Z.eqb_neq in El.
  pose proof (u32_range (u_offset (s_cur (q_st q))
                         - u32 (q_out q - o_left (q_ob q)))) as Hcw_r.
  pose proof (u32_range (u32 (u_offset (s_cur (q_st q))
                              - u32 (q_out q - o_left (q_ob q)))
                         - w_wnext (s_win (q_st q)))) as Hc1_r.
  destruct (Z.ltb (u32 (q_out q - o_left (q_ob q)))
                  (u_offset (s_cur (q_st q)))).
  - (* copy from the window *)
    destruct (Z.ltb (w_whave (s_win (q_st q)))
                    (u32 (u_offset (s_cur (q_st q))
                          - u32 (q_out q - o_left (q_ob q))))
              && negb (Z.eqb (t_sane (s_tab (q_st q))) 0)).
    { split;
        [apply (reach_core_conv q); [exact HC|reflexivity..] | rm_off]. }
    destruct (Z.ltb (w_wnext (s_win (q_st q)))
                    (u32 (u_offset (s_cur (q_st q))
                          - u32 (q_out q - o_left (q_ob q)))));
      cbv beta iota.
    + (* wrapped around the window *)
      destruct (min3_facts (u_length (s_cur (q_st q))) (o_left (q_ob q))
                  (u32 (u32 (u_offset (s_cur (q_st q))
                             - u32 (q_out q - o_left (q_ob q)))
                        - w_wnext (s_win (q_st q))))
                  Hlen1 Hl ltac:(lia)) as (Hc0 & Hclen & Hcol).
      apply match_tail_pres; assumption.
    + (* contiguous in the window *)
      destruct (min3_facts (u_length (s_cur (q_st q))) (o_left (q_ob q))
                  (u32 (u_offset (s_cur (q_st q))
                        - u32 (q_out q - o_left (q_ob q))))
                  Hlen1 Hl ltac:(lia)) as (Hc0 & Hclen & Hcol).
      apply match_tail_pres; assumption.
  - (* copy direct from the output *)
    destruct (min2_facts (u_length (s_cur (q_st q))) (o_left (q_ob q))
                Hlen1 Hl) as (Hc0 & Hclen & Hcol).
    apply match_tail_pres; assumption.
Qed.

Lemma pres_DISTEXT :
  forall c q,
    q_mode q = M_DISTEXT ->
    ReachCore q ->
    1 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 98303 ->
    0 <= u_extra (s_cur (q_st q)) <= 15 ->
    0 <= u_offset (s_cur (q_st q)) ->
    u_offset (s_cur (q_st q)) + Z.shiftl 1 (u_extra (s_cur (q_st q)))
      <= 4294967296 ->
    0 <= u_back (s_cur (q_st q)) <= 75 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    u_offset (s_cur (q_st q)) < 65536 ->
    DistSubSide q ->
    1 <= u_offset (s_cur (q_st q)) ->
    PresOk c (inf_DISTEXT q).
Proof.
  intros c q Hm HC Hlen1 Hub He Hoff0 Hoffe Hbk HL Htp Hb14 Hwd Hoff16 Hds Ho1.
  unfold inf_DISTEXT. cbv zeta.
  core_facts q HC.
  assert (Es : Z.shiftl 1 (u_extra (s_cur (q_st q)))
               = 2 ^ u_extra (s_cur (q_st q)))
    by apply Z.shiftl_1_l.
  destruct (Z.eqb (u_extra (s_cur (q_st q))) 0) eqn:Ee.
  { (* extra = 0: fall through to MATCH on the frame state *)
    apply Z.eqb_eq in Ee.
    assert (Hs0 : Z.shiftl 1 (u_extra (s_cur (q_st q))) = 1)
      by (rewrite Ee; reflexivity).
    apply pres_MATCH.
    - reflexivity.
    - apply (reach_core_conv q); [exact HC|reflexivity..].
    - split; [exact Hlen1|]. split; [|exact (proj1 Fwn)]. cbn. lia.
    - exact Hub.
    - apply (len_tbl_side_frame q); [reflexivity | exact HL].
    - exact Htp.
    - exact Hb14.
    - exact Hwd.
    - exact Hds.
    - exact Ho1. }
  destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave (u_extra (s_cur (q_st q))) (q_br q) b
          ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply (reach_mode_distext (qset_br q b) Hm Hlen1 Hub He
                    Hoff0 Hoffe Hbk);
           [ apply (len_tbl_side_frame q); [reflexivity | exact HL]
           | apply (tblpd_frame q); [reflexivity | exact Htp]
           | bsimp; lia
           | apply (tblwid_frame q); [reflexivity | exact Hwd]
           | exact Hoff16
           | apply (dist_sub_frame q); [reflexivity | exact Hds]
           | exact Ho1 ] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as Eok.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env (u_extra (s_cur (q_st q))) (q_br q) b
              ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  pose proof (bits_of_range (u_extra (s_cur (q_st q))) b
                ltac:(lia)) as Hbo.
  apply pres_MATCH.
  - reflexivity.
  - rc_close q.
  - split; [ksimp; exact Hlen1|]. split; [|ksimp; exact (proj1 Fwn)].
    ksimp. lia.
  - ksimp. exact Hub.
  - apply (len_tbl_side_frame q); [reflexivity | exact HL].
  - apply (tblpd_frame q); [reflexivity | exact Htp].
  - pose proof (inf_nb_ok_le _ _ _ Enb) as Ele. apply Z.eqb_neq in Ee. ksimp. c6bits.
  - apply (tblwid_frame q); [reflexivity | exact Hwd].
  - apply (dist_sub_frame q); [reflexivity | exact Hds].
  - ksimp. lia.
Qed.

Lemma pres_DIST :
  forall c q,
    q_mode q = M_DIST ->
    ReachCore q ->
    1 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 98303 ->
    0 <= u_back (s_cur (q_st q)) <= 45 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    PresOk c (inf_DIST q).
Proof.
  intros c q Hm HC Hlen1 Hub Hbk HL Htp Hb14 Hwd Hds.
  unfold inf_DIST. cbv zeta.
  core_facts q HC.
  pose proof HL as (Htbl & Hlcs & Htds & Hlt & Hdt & Hlbnd & Hlb & Hdb & Hroot0).
  destruct (inf_decode sub_dist
              (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
              (t_distbits (s_tab (q_st q))) (q_br q))
    as [h b nb|b|] eqn:Edec;
    [ | pose proof (tbl_of_wid015 (q_st q) (t_distcode (s_tab (q_st q)))
          Famb) as Lwid;
        destruct (inf_decode_leave _ _ _ _ _ Lwid Fhold Hb
            (fun j => proj1 (rc_bytes q HC j)) Edec)
            as (Lh0 & Lin & Lhold & Lbits & Lbud);
        split;
        [ split;
          [ rc_close q
          | apply (reach_mode_dist (qset_br q b) Hm Hlen1 Hub Hbk);
            [ apply (len_tbl_side_frame q); [reflexivity | exact HL]
            | apply (tblpd_frame q); [reflexivity | exact Htp]
            | bsimp;
              exact (inf_decode_leave_le14 _ _ _ _ _ (proj2 Htp) (proj2 Hdb) (proj1 (proj2 Hwd))
                       (fun i Hi _ => proj2 (proj2 Hwd) i Hi) sub_dist_240 Fhold Hb (fun j => proj1 (rc_bytes q HC j)) Edec)
            | apply (tblwid_frame q); [reflexivity | exact Hwd]
            | apply (dist_sub_frame q); [reflexivity | exact Hds] ] ]
        | intros _ _; left; exact Lh0 ]
    | exact I ].
  destruct (inf_decode_env _ _ _ _ _ _ _
              (fun i => proj1 (Htds i)) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Edec)
    as (Din & Dh & D39).
  pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Edec) as Db0.
  destruct (inf_decode_bud _ _ _ _ _ _ _ Edec) as (Dbud & Dhave).
  specialize (Dhave Hh).
  destruct (inf_decode_ok_facts _ _ _ _ _ _ _
              (fun i => proj1 (proj1 (Htds i))) Edec)
    as ((i0 & Hhe) & Hnb0).
  pose proof (inf_decode_nb_le30 _ _ _ _ _ _ _
                (fun i => proj2 (proj1 (Htds i))) Edec) as Hnb30.
  pose proof (inf_decode_le14 _ _ _ _ _ _ _ (proj2 Htp)
                (subguard_dist_wid _ _ (proj1 (proj2 Hwd)) (fun i => proj1 (proj1 (Htds i)))) Hb14 Edec) as Hb13.
  assert (Hval : 0 <= c_val h < 65536)
    by (rewrite Hhe; exact (proj2 (Htds i0))).
  destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)) eqn:E64.
  { split; [rc_close q | rm_off]. }
  apply Bool.negb_false_iff, Z.eqb_eq in E64.
  (* cand13: the OFF1 supply — a successful dist decode returns a LEAF ([rm_dsub] for the level-2 case, [sub_dist h = false] at
     the root), and [rc_leafpos] gives that leaf a positive value on the non-BAD branch (PLAN-rm_off1 §2; dist_offset_pos). *)
  assert (Hoff1 : 1 <= c_val h).
  { refine (dist_offset_pos (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) (t_distbits (s_tab (q_st q))) (q_br q) h b nb
              _ (leafpos_tbl_of q _ Flp) (fun i => proj1 (proj1 (Htds i))) _ Hds Edec E64).
    - lia.
    - intros i Hi H240. exact (proj1 (proj1 (proj2 Hwd) i Hi H240 (proj2 (proj2 Hwd) i Hi))). }
  pose proof (land15_range (c_op h)) as He15.
  assert (Hsh : Z.shiftl 1 (Z.land (c_op h) 15) <= 32768).
  { rewrite Z.shiftl_1_l.
    assert (E15 : 2 ^ 15 = 32768) by reflexivity.
    pose proof (Z.pow_le_mono_r 2 (Z.land (c_op h) 15) 15
                  ltac:(lia) ltac:(lia)).
    lia. }
  apply pres_DISTEXT.
  - unfold q_mode; bsimp; reflexivity.
  - rc_close q.
  - ksimp. exact Hlen1.
  - ksimp. exact Hub.
  - ksimp. exact He15.
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. ubk. lia.
  - apply (len_tbl_side_frame q); [reflexivity | exact HL].
  - apply (tblpd_frame q); [reflexivity | exact Htp].
  - ksimp. lia.
  - apply (tblwid_frame q); [reflexivity | exact Hwd].
  - ksimp. lia.
  - apply (dist_sub_frame q); [reflexivity | exact Hds].
  - ksimp. exact Hoff1.
Qed.

Lemma pres_LENEXT :
  forall c q,
    q_mode q = M_LENEXT ->
    ReachCore q ->
    1 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 65535 ->
    0 <= u_extra (s_cur (q_st q)) <= 15 ->
    0 <= u_back (s_cur (q_st q)) <= 30 ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    PresOk c (inf_LENEXT q).
Proof.
  intros c q Hm HC Hlen1 Hub He Hbk HL Htp Hb14 Hwd Hds.
  unfold inf_LENEXT. cbv zeta.
  core_facts q HC.
  destruct (Z.eqb (u_extra (s_cur (q_st q))) 0) eqn:Ee; cbv beta iota.
  { (* extra = 0: straight to DIST on the frame state *)
    apply pres_DIST.
    - unfold q_mode; bsimp; reflexivity.
    - rc_close q.
    - ksimp. exact Hlen1.
    - ksimp. lia.
    - ksimp. ubk. lia.
    - apply (len_tbl_side_frame q); [reflexivity | exact HL].
    - apply (tblpd_frame q); [reflexivity | exact Htp].
    - ksimp. exact Hb14.
    - apply (tblwid_frame q); [reflexivity | exact Hwd].
    - apply (dist_sub_frame q); [reflexivity | exact Hds]. }
  destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:Enb;
    cbv beta iota;
    [| destruct (inf_nb_leave (u_extra (s_cur (q_st q))) (q_br q) b
          ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply (reach_mode_lenext (qset_br q b) Hm Hlen1 Hub He Hbk);
           [ apply (len_tbl_side_frame q); [reflexivity | exact HL]
           | apply (tblpd_frame q); [reflexivity | exact Htp]
           | bsimp; lia
           | apply (tblwid_frame q); [reflexivity | exact Hwd]
           | apply (dist_sub_frame q); [reflexivity | exact Hds] ] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as Eok.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env (u_extra (s_cur (q_st q))) (q_br q) b
              ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  pose proof (bits_of_range (u_extra (s_cur (q_st q))) b
                ltac:(lia)) as Hbo.
  assert (Hp2 : 2 ^ u_extra (s_cur (q_st q)) <= 32768).
  { assert (E15 : 2 ^ 15 = 32768) by reflexivity.
    pose proof (Z.pow_le_mono_r 2 (u_extra (s_cur (q_st q))) 15
                  ltac:(lia) ltac:(lia)).
    lia. }
  apply pres_DIST.
  - unfold q_mode; bsimp; reflexivity.
  - rc_close q.
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. ubk. lia.
  - apply (len_tbl_side_frame q); [reflexivity | exact HL].
  - apply (tblpd_frame q); [reflexivity | exact Htp].
  - pose proof (inf_nb_ok_le _ _ _ Enb) as Ele. apply Z.eqb_neq in Ee. ksimp. c6bits.
  - apply (tblwid_frame q); [reflexivity | exact Hwd].
  - apply (dist_sub_frame q); [reflexivity | exact Hds].
Qed.

(** ** The inflate_fast INPUT-CONSERVATION walk (pres lane, 2026-08-19)

    [rc_inbud] survives the call node iff the loop never CREATES input
    bits: with [C s = 8 * f_in s - f_bits s] (bits taken off the
    stream), loads conserve [C] and a drop of [n >= 0] adds [n], so [C]
    is non-decreasing — and [if_finish]'s give-back algebra turns
    [C (st0) <= C (s')] into [8*avail_in' + bits' <= 8*avail_in + bits].
    The landed bud/fin walks carry the UPPER bounds (+48 per trip / +5
    loads); this walk is the missing LOWER bound, cribbed leaf-for-leaf
    from [if_dodist_fin]/[if_dolen_fin] with the same premise set. *)

Lemma if_refill15_cmono : forall c s,
  8 * f_in (if_refill15 c s) - f_bits (if_refill15 c s)
  = 8 * f_in s - f_bits s.
Proof.
  intros c s. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); [cbn [if_load1 f_in f_bits]; lia | lia].
Qed.

Lemma if_dodist_cmono :
  forall f c len s v,
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    c_bits (f_dcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ dc_chains (c_op (f_dcode c v)) = false) ->
    match if_dodist f c len s (f_dcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s - f_bits s <= 8 * f_in s' - f_bits s'
    | BodyFuel => True
    end.
Proof.
  induction f as [|f IH]; intros c len s v Hbits Hfit Htwo Hwv Hcov Hrange
    Hdisj; cbn [if_dodist]; [exact I|].
  pose proof (Hbits v) as Hv.
  pose proof (if_drop_bud c s (c_bits (f_dcode c v))
                ltac:(lia) ltac:(lia)) as (Ehd & Bhd).
  assert (Fhd : f_in (if_drop (c_bits (f_dcode c v)) s) = f_in s)
    by reflexivity.
  set (s1 := if_drop (c_bits (f_dcode c v)) s) in *.
  destruct (negb (Z.eqb (Z.land (c_op (f_dcode c v)) 16) 0)) eqn:E16.
  - set (e := Z.land (c_op (f_dcode c v)) 15).
    assert (He : 0 <= e <= 15) by (unfold e; apply land15_range).
    set (s2 := if Z.ltb (f_bits s1) e
               then let sa := if_load1 c s1 in
                    if Z.ltb (f_bits sa) e then if_load1 c sa else sa
               else s1).
    assert (Hs2 : e <= f_bits s2 /\ f_bits s2 <= 40
                  /\ 8 * f_in s2 - f_bits s2 = 8 * f_in s1 - f_bits s1).
    { unfold s2. destruct (Z.ltb_spec (f_bits s1) e) as [Hlt|Hge].
      - destruct (if_load1_bud c s1) as (_ & B1).
        destruct (Z.ltb_spec (f_bits (if_load1 c s1)) e) as [Hlt2|Hge2].
        + destruct (if_load1_bud c (if_load1 c s1)) as (_ & B2).
          cbn [if_load1 f_in] in *. repeat split; try lia.
        + cbn [if_load1 f_in] in *. repeat split; lia.
      - repeat split; lia. }
    destruct Hs2 as (Hge2 & Hb2 & Hc2).
    pose proof (if_drop_bud c s2 e ltac:(lia) ltac:(lia)) as (_ & Bhd3).
    assert (Fhd3 : f_in (if_drop e s2) = f_in s2) by reflexivity.
    set (s3 := if_drop e s2) in *.
    destruct (Z.ltb (u32 (f_out s3 - f_beg c))
                (c_val (f_dcode c v) + if_low e s2)).
    + destruct (Z.ltb (f_whave c)
                  (u32 (c_val (f_dcode c v) + if_low e s2
                        - u32 (f_out s3 - f_beg c)))
                && negb (Z.eqb (f_sane c) 0)).
      * cbv iota. lia.
      * destruct (if_winphase c s3 (c_val (f_dcode c v) + if_low e s2)
                    (u32 (c_val (f_dcode c v) + if_low e s2
                          - u32 (f_out s3 - f_beg c))) len)
          as [[s4 r4] len4] eqn:Ewp.
        pose proof (if_winphase_fin _ _ _ _ _ _ _ _ Ewp) as Fwp.
        apply if_winphase_bud in Ewp as (_ & Bwp).
        destruct (if_copy3w copy_fuel c s4 r4 len4)
          as [[[s5 r5] l5]|] eqn:E3w; [|exact I].
        pose proof (if_copy3w_fin _ _ _ _ _ _ _ _ E3w) as F3w.
        apply if_copy3w_bud in E3w as (_ & B3w).
        pose proof (if_copytail_fin c s5 r5 l5) as Ftl.
        pose proof (if_copytail_bud c s5 r5 l5) as (_ & Btl).
        cbv iota. lia.
    + destruct (if_copydirect c s3
                  (SrcOut (f_out s3 - (c_val (f_dcode c v) + if_low e s2)))
                  len) as [s5|] eqn:Edir; [|exact I].
      pose proof (if_copydirect_fin _ _ _ _ _ Edir) as Fdir.
      apply if_copydirect_bud in Edir as (_ & Bdir).
      cbv iota. lia.
  - destruct (Z.eqb (Z.land (c_op (f_dcode c v)) 64) 0) eqn:E64.
    + assert (Hch : dc_chains (c_op (f_dcode c v)) = true).
      { unfold dc_chains.
        apply Bool.negb_false_iff in E16. rewrite E16, E64. reflexivity. }
      assert (H15 : 15 <= f_bits s)
        by (destruct Hdisj as [H|H]; [exact H | congruence]).
      destruct (Hwv Hch) as (xw & Hxw).
      pose proof (Hfit v xw s1 Hxw Hch) as Hf.
      pose proof (Htwo v xw s1 Hxw Hch) as Hnc.
      pose proof (Hbits (c_val (f_dcode c v)
                         + if_low (c_op (f_dcode c v)) s1)) as Hcb.
      pose proof (IH c len s1
                    (c_val (f_dcode c v) + if_low (c_op (f_dcode c v)) s1)
                    Hbits Hfit Htwo ltac:(intros Hc; congruence)
                    ltac:(lia) ltac:(lia)
                    (or_intror Hnc)) as HR.
      destruct (if_dodist f c len s1
                  (f_dcode c (c_val (f_dcode c v)
                              + if_low (c_op (f_dcode c v)) s1)))
        as [s'|s'|s' m|]; cbv iota in HR |- *; try exact I; lia.
    + cbv iota. lia.
Qed.

Lemma if_dolen_cmono :
  forall f c s v n,
    (forall i, 0 <= i < n -> 1 <= c_bits (f_lcode c i) <= 15) ->
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit lc_chains (f_lcode c) (f_lmask c) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c ->
    0 <= v < n ->
    c_bits (f_lcode c v) <= f_bits s ->
    0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ lc_chains (c_op (f_lcode c v)) = false) ->
    match if_dolen f c s (f_lcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s - f_bits s <= 8 * f_in s' - f_bits s'
    | BodyFuel => True
    end.
Proof.
  induction f as [|f IH]; intros c s v n Hlb Hdb Hlf Hdf Hlt Hdt Hwv Hup Hir
    Hv Hcov Hrange Hdisj; cbn [if_dolen]; [exact I|].
  pose proof (Hlb v Hv) as Hvb.
  pose proof (if_drop_bud c s (c_bits (f_lcode c v))
                ltac:(lia) ltac:(lia)) as (Ehd & Bhd).
  assert (Fhd : f_in (if_drop (c_bits (f_lcode c v)) s) = f_in s)
    by reflexivity.
  set (s1 := if_drop (c_bits (f_lcode c v)) s) in *.
  destruct (Z.eqb (c_op (f_lcode c v)) 0) eqn:E0.
  - cbv iota. cbn [if_put f_bits f_in]. lia.
  - destruct (negb (Z.eqb (Z.land (c_op (f_lcode c v)) 16) 0)) eqn:E16.
    + set (e := Z.land (c_op (f_lcode c v)) 15).
      assert (He : 0 <= e <= 15) by (unfold e; apply land15_range).
      assert (He8 : e <= 8).
      { pose proof (Hup v Hv) as Hok. unfold lc_len_ok in Hok.
        apply Bool.negb_true_iff, Z.eqb_neq in E16.
        destruct (Hok E16) as (H3 & H258). fold e in H258.
        destruct (Z.le_gt_cases e 8) as [H|H]; [exact H|]. exfalso.
        assert (H29 : 2 ^ 9 <= 2 ^ e) by (apply Z.pow_le_mono_r; lia).
        rewrite Z.shiftl_1_l in H258. cbn in H29. lia. }
      destruct (Z.eqb e 0) eqn:Ee0.
      * apply Z.eqb_eq in Ee0. cbv iota.
        pose proof (if_refill15_bud c s1 ltac:(lia))
          as (_ & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s1 ltac:(lia)) as Hge15.
        pose proof (if_refill15_cmono c s1) as Crf.
        set (s3 := if_refill15 c s1) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_cmono tbl_fuel c (c_val (f_lcode c v)) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia) Hd15) as HD.
        destruct (if_dodist tbl_fuel c (c_val (f_lcode c v)) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I; lia.
      * apply Z.eqb_neq in Ee0. cbv iota.
        set (sa := if Z.ltb (f_bits s1) e then if_load1 c s1 else s1).
        assert (Hsa : e <= f_bits sa /\ f_bits sa <= 40
                      /\ 8 * f_in sa - f_bits sa = 8 * f_in s1 - f_bits s1).
        { unfold sa. destruct (Z.ltb_spec (f_bits s1) e) as [Hltb|Hgeb].
          - destruct (if_load1_bud c s1) as (_ & B1).
            cbn [if_load1 f_in] in *. repeat split; lia.
          - repeat split; lia. }
        destruct Hsa as (Hgea & Hba & Hca).
        pose proof (if_drop_bud c sa e ltac:(lia) ltac:(lia)) as (_ & Be).
        assert (Fe : f_in (if_drop e sa) = f_in sa) by reflexivity.
        set (s2 := if_drop e sa) in *.
        pose proof (if_refill15_bud c s2 ltac:(lia))
          as (_ & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s2 ltac:(lia)) as Hge15.
        pose proof (if_refill15_cmono c s2) as Crf.
        set (s3 := if_refill15 c s2) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_cmono tbl_fuel c
                      (c_val (f_lcode c v) + if_low e sa) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia) Hd15) as HD.
        destruct (if_dodist tbl_fuel c
                    (c_val (f_lcode c v) + if_low e sa) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I; lia.
    + destruct (Z.eqb (Z.land (c_op (f_lcode c v)) 64) 0) eqn:E64.
      * assert (Hch : lc_chains (c_op (f_lcode c v)) = true).
        { unfold lc_chains.
          apply Bool.negb_true_iff in E0.
          apply Bool.negb_false_iff in E16.
          rewrite E0, E16, E64. reflexivity. }
        assert (H15 : 15 <= f_bits s)
          by (destruct Hdisj as [H|H]; [exact H | congruence]).
        destruct (Hwv Hch) as (xw & Hxw).
        pose proof (Hlf v xw s1 Hxw Hch) as Hf.
        pose proof (Hlt v xw s1 Hxw Hch) as Hnc.
        destruct Hir as (Hroot & Hchain).
        pose proof (Hchain v s1 Hv Hch) as Hvin.
        pose proof (Hlb _ Hvin) as Hcb.
        pose proof (IH c s1
                      (c_val (f_lcode c v) + if_low (c_op (f_lcode c v)) s1)
                      n Hlb Hdb Hlf Hdf Hlt Hdt
                      ltac:(intros Hc; congruence) Hup
                      (conj Hroot Hchain) Hvin ltac:(lia) ltac:(lia)
                      (or_intror Hnc)) as HR.
        destruct (if_dolen f c s1
                    (f_lcode c (c_val (f_lcode c v)
                                + if_low (c_op (f_lcode c v)) s1)))
          as [s'|s'|s' m|]; cbv iota in HR |- *; try exact I; lia.
      * destruct (negb (Z.eqb (Z.land (c_op (f_lcode c v)) 32) 0));
          cbv iota; lia.
Qed.

Lemma if_body_cmono :
  forall c s n,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    match if_body c s with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s - f_bits s <= 8 * f_in s' - f_bits s'
    | BodyFuel => True
    end.
Proof.
  intros c s n Hwalk Hb. unfold if_body. cbv zeta.
  destruct Hwalk as (Hlb & Hdb & Hlf & Hdf & Hlex & Hdex & Hlt & Hdt
                     & Hup & Hir & Hwn).
  pose proof (if_refill15_cmono c s) as Crf.
  pose proof (if_refill15_bud c s Hb) as (_ & _ & _ & _ & _ & Hrng).
  pose proof (if_refill15_ge15 c s ltac:(lia)) as Hge15.
  destruct Hir as (Hroot & Hchain).
  set (s0 := if_refill15 c s) in *. clearbody s0.
  pose proof (Hroot s0) as Hv0.
  pose proof (Hlb _ Hv0) as Hw0.
  pose proof (if_dolen_cmono tbl_fuel c s0
                (Z.land (f_hold s0) (f_lmask c)) n
                Hlb Hdb Hlf Hdf Hlt Hdt
                ltac:(intros _; eexists; reflexivity)
                Hup (conj Hroot Hchain) Hv0 ltac:(lia) ltac:(lia)
                (or_introl Hge15)) as HD.
  destruct (if_dolen tbl_fuel c s0
              (f_lcode c (Z.land (f_hold s0) (f_lmask c))))
    as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I; lia.
Qed.

Lemma if_step_cmono :
  forall c s n,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    match if_step c s with
    | IfCont s' | IfStop s' | IfEob s' | IfBad s' _ =>
        8 * f_in s - f_bits s <= 8 * f_in s' - f_bits s'
    | IfFuel => True
    end.
Proof.
  intros c s n Hwalk Hb. rewrite if_step_unfold.
  pose proof (if_body_cmono c s n Hwalk Hb) as HB.
  destruct (if_body c s) as [s1|s1|s1 m|]; cbv beta iota in HB |- *;
    [destruct (if_guard c s1); exact HB | exact HB | exact HB | exact I].
Qed.

Lemma if_loop_cmono :
  forall m c s n r,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    if_loop m c s = Some r ->
    match r with
    | IfStop s' | IfEob s' | IfBad s' _ =>
        8 * f_in s - f_bits s <= 8 * f_in s' - f_bits s'
    | IfCont _ => True
    | IfFuel => True
    end.
Proof.
  induction m as [|m IH]; intros c s n r Hwalk Hb H;
    [cbn [if_loop] in H; discriminate|].
  rewrite if_loop_S in H.
  pose proof (if_step_cmono c s n Hwalk Hb) as HS.
  pose proof (if_step_bud c s n Hwalk Hb) as HT.
  destruct (if_step c s) as [s1|s1|s1|s1 m1|] eqn:ES.
  - destruct HT as (T1 & T2 & T3 & T4 & T5).
    pose proof (IH c s1 n r Hwalk T3 H) as HR.
    destruct r as [s'|s'|s'|s' m2|]; try exact I; lia.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact I.
Qed.

(** The call-node exit facts [pres_LEN] consumes, goal-side over
    [if_model] (the landed kernel discipline: never unfold the
    application hypothesis-side). *)
Theorem if_model_pres :
  forall a,
    if_wf_lax a -> if_wf_tbl a ->
    a_avail_in a <= 4294967290 -> a_avail_out a <= 4294967295 ->
    match if_model a with
    | None => True
    | Some y =>
        8 * y_avail_in y + y_bits y <= 8 * a_avail_in a + a_bits a
        /\ y_avail_out y <= a_avail_out a
        /\ 0 <= y_bits y <= 7
        /\ 0 <= y_avail_in y /\ 0 <= y_avail_out y /\ 0 <= y_hold y
    end.
Proof.
  intros a Hwf Htbl Hain Haout.
  destruct (if_wf_walk_ok a Hwf Htbl) as (n & Hwalk).
  pose proof Hwf as (Hain6 & Haout258 & Hbits & _).
  pose proof (if_walk_ok_ctx_wf _ _ Hwalk) as Hcwf.
  destruct (if_loop_total (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a)))
              (if_ctx a) (if_st0 a) Hcwf ltac:(lia)) as (r & Heq & Hd).
  assert (Hb0 : 0 <= f_bits (if_st0 a) <= 40) by (cbn [if_st0 f_bits]; lia).
  assert (Hin0 : f_in (if_st0 a) < f_last (if_ctx a))
    by (cbn [if_st0 f_in if_ctx f_last]; lia).
  assert (Hout0 : f_out (if_st0 a) < f_end (if_ctx a))
    by (cbn [if_st0 f_out if_ctx f_end]; lia).
  pose proof (if_loop_bud _ _ _ n r Hwalk Hb0 Hin0 Hout0 Heq) as HL.
  pose proof (if_loop_cmono _ _ _ n r Hwalk Hb0 Heq) as HCm.
  assert (HL0 : f_last (if_ctx a) = a_next_in a + (a_avail_in a - 5))
    by reflexivity.
  assert (HE0 : f_end (if_ctx a) = a_next_out a + (a_avail_out a - 257))
    by reflexivity.
  assert (HI0 : f_in (if_st0 a) = a_next_in a) by reflexivity.
  assert (HO0 : f_out (if_st0 a) = a_next_out a) by reflexivity.
  assert (HB0e : f_bits (if_st0 a) = a_bits a) by reflexivity.
  unfold if_model. cbv zeta. rewrite Heq.
  destruct r as [s'|s'|s'|s' m0|]; cbv beta iota in HCm |- *;
    [exact I| | | |exact I];
    destruct HL as (L1 & L2 & L3 & L4 & L5 & L6);
    (unfold if_finish; cbv zeta;
     cbn [y_avail_in y_bits y_avail_out y_hold];
     set (l := Z.shiftr (f_bits s') 3) in *;
     assert (Hl : l = f_bits s' / 8)
       by (unfold l; rewrite Z.shiftr_div_pow2 by lia; reflexivity);
     assert (Hlr : 0 <= l <= 5)
       by (rewrite Hl; split;
           [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]);
     assert (Hsh : Z.shiftl l 3 = 8 * l)
       by (rewrite Z.shiftl_mul_pow2 by lia; lia);
     assert (Hbm : 0 <= f_bits s' - Z.shiftl l 3 <= 7)
       by (rewrite Hsh, Hl;
           pose proof (Z.mod_pos_bound (f_bits s') 8 ltac:(lia));
           pose proof (Z.div_mod (f_bits s') 8 ltac:(lia)); lia);
     rewrite (u32_id (f_bits s' - Z.shiftl l 3)) by lia;
     set (i := f_in s' - l) in *;
     assert (Hi : i = f_in s' - l) by reflexivity;
     assert (Hi_hi : i <= f_last (if_ctx a) + 5)
       by (assert (H8i : 8 * i = (8 * f_in s' - f_bits s')
                                 + (f_bits s' - Z.shiftl l 3))
             by (rewrite Hsh; unfold i; lia); lia);
     assert (Hi_lo : a_next_in a - 5 <= i) by (unfold i; lia);
     assert (Havin : (if Z.ltb i (f_last (if_ctx a))
                      then 5 + (f_last (if_ctx a) - i)
                      else 5 - (i - f_last (if_ctx a)))
                     = 5 + (f_last (if_ctx a) - i))
       by (destruct (Z.ltb i (f_last (if_ctx a))); lia);
     rewrite Havin;
     rewrite (u32_id (5 + (f_last (if_ctx a) - i))) by lia;
     assert (Havout : (if Z.ltb (f_out s') (f_end (if_ctx a))
                       then 257 + (f_end (if_ctx a) - f_out s')
                       else 257 - (f_out s' - f_end (if_ctx a)))
                      = 257 + (f_end (if_ctx a) - f_out s'))
       by (destruct (Z.ltb (f_out s') (f_end (if_ctx a))); lia);
     rewrite Havout;
     rewrite (u32_id (257 + (f_end (if_ctx a) - f_out s'))) by lia;
     assert (Hhold : 0 <= Z.land (f_hold s')
                            (Z.shiftl 1 (f_bits s' - Z.shiftl l 3) - 1))
       by (apply land_nonneg_r; rewrite Z.shiftl_1_l;
           pose proof (Z.pow_pos_nonneg 2 (f_bits s' - Z.shiftl l 3)
                         ltac:(lia) ltac:(lia)); lia);
     repeat split; try lia).
Qed.

(** The fast path re-establishes [rc_holdclean] unconditionally at exit:
    [if_finish]'s mask [hold &= (1U << bits) - 1] (InflateFast.v:495 =
    inffast.c:293), with the exit [bits] in [0, 7] ([if_loop_bud]'s
    [0 <= f_bits s' <= 40] and the [len << 3] give-back).  Stated beside
    [if_model_pres] with the same premise set (an earlier development run). *)
Theorem if_model_hc :
  forall a,
    if_wf_lax a -> if_wf_tbl a ->
    match if_model a with
    | None => True
    | Some y => y_hold y < 2 ^ y_bits y
    end.
Proof.
  intros a Hwf Htbl.
  destruct (if_wf_walk_ok a Hwf Htbl) as (n & Hwalk).
  pose proof Hwf as (Hain6 & Haout258 & Hbits & _).
  pose proof (if_walk_ok_ctx_wf _ _ Hwalk) as Hcwf.
  destruct (if_loop_total (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a)))
              (if_ctx a) (if_st0 a) Hcwf ltac:(lia)) as (r & Heq & Hd).
  assert (Hb0 : 0 <= f_bits (if_st0 a) <= 40) by (cbn [if_st0 f_bits]; lia).
  assert (Hin0 : f_in (if_st0 a) < f_last (if_ctx a))
    by (cbn [if_st0 f_in if_ctx f_last]; lia).
  assert (Hout0 : f_out (if_st0 a) < f_end (if_ctx a))
    by (cbn [if_st0 f_out if_ctx f_end]; lia).
  pose proof (if_loop_bud _ _ _ n r Hwalk Hb0 Hin0 Hout0 Heq) as HL.
  unfold if_model. cbv zeta. rewrite Heq.
  destruct r as [s'|s'|s'|s' m0|]; cbv beta iota;
    [exact I| | | |exact I];
    destruct HL as (L1 & L2 & L3 & L4 & L5 & L6);
    (unfold if_finish; cbv zeta; cbn [y_bits y_hold];
     set (l := Z.shiftr (f_bits s') 3) in *;
     assert (Hl : l = f_bits s' / 8)
       by (unfold l; rewrite Z.shiftr_div_pow2 by lia; reflexivity);
     assert (Hsh : Z.shiftl l 3 = 8 * l)
       by (rewrite Z.shiftl_mul_pow2 by lia; lia);
     assert (Hbm : 0 <= f_bits s' - Z.shiftl l 3 <= 7)
       by (rewrite Hsh, Hl;
           pose proof (Z.mod_pos_bound (f_bits s') 8 ltac:(lia));
           pose proof (Z.div_mod (f_bits s') 8 ltac:(lia)); lia);
     rewrite (u32_id (f_bits s' - Z.shiftl l 3)) by lia;
     exact (proj2 (land_ones_range (f_hold s') (f_bits s' - Z.shiftl l 3)
                     ltac:(lia)))).
Qed.

(** ** The write-back piece pack [lp_norm] lacks (the s-level frame
    projections and [q_load]'s reader fields) *)
Lemma q_load_in2 : forall q, br_in (q_br (q_load q)) = br_in (q_br q).
Proof. reflexivity. Qed.
Lemma q_load_hold2 : forall q, br_hold (q_br (q_load q)) = s_hold (q_st q).
Proof. reflexivity. Qed.
Lemma stab_set_bits : forall st v, s_tab (set_bits st v) = s_tab st.
Proof. reflexivity. Qed.
Lemma stab_set_hold : forall st v, s_tab (set_hold st v) = s_tab st.
Proof. reflexivity. Qed.
Lemma stab_set_back : forall st v, s_tab (set_back st v) = s_tab st.
Proof. reflexivity. Qed.
Lemma stab_set_mode : forall st m, s_tab (set_mode st m) = s_tab st.
Proof. reflexivity. Qed.
Lemma swin_set_bits : forall st v, s_win (set_bits st v) = s_win st.
Proof. reflexivity. Qed.
Lemma swin_set_hold : forall st v, s_win (set_hold st v) = s_win st.
Proof. reflexivity. Qed.
Lemma swin_set_back : forall st v, s_win (set_back st v) = s_win st.
Proof. reflexivity. Qed.
Lemma swin_set_mode : forall st m, s_win (set_mode st m) = s_win st.
Proof. reflexivity. Qed.
Lemma sbld_set_bits : forall st v, s_bld (set_bits st v) = s_bld st.
Proof. reflexivity. Qed.
Lemma sbld_set_hold : forall st v, s_bld (set_hold st v) = s_bld st.
Proof. reflexivity. Qed.
Lemma sbld_set_back : forall st v, s_bld (set_back st v) = s_bld st.
Proof. reflexivity. Qed.
Lemma sbld_set_mode : forall st m, s_bld (set_mode st m) = s_bld st.
Proof. reflexivity. Qed.
Lemma scur_set_bits : forall st v, s_cur (set_bits st v) = s_cur st.
Proof. reflexivity. Qed.
Lemma scur_set_hold : forall st v, s_cur (set_hold st v) = s_cur st.
Proof. reflexivity. Qed.
Lemma ulen_set_back : forall st v,
  u_length (s_cur (set_back st v)) = u_length (s_cur st).
Proof. reflexivity. Qed.
Lemma scur_set_mode : forall st m, s_cur (set_mode st m) = s_cur st.
Proof. reflexivity. Qed.
Lemma shold_set_bits : forall st v, s_hold (set_bits st v) = s_hold st.
Proof. reflexivity. Qed.
Lemma shold_set_hold : forall st v, s_hold (set_hold st v) = v.
Proof. reflexivity. Qed.
Lemma shold_set_mode : forall st m, s_hold (set_mode st m) = s_hold st.
Proof. reflexivity. Qed.
Lemma sbits_set_hold : forall st v, s_bits (set_hold st v) = s_bits st.
Proof. reflexivity. Qed.

Ltac lpp :=
  repeat first
    [ rewrite q_load_in2 | rewrite q_load_hold2
    | rewrite q_load_have | rewrite q_load_bits | rewrite q_load_left
    | rewrite q_mode_q_load | rewrite q_st_q_load
    | rewrite q_br_qset_ob | rewrite q_br_qset_br | rewrite q_br_qset_st
    | rewrite q_br_qset_z | rewrite q_br_qmode
    | rewrite q_ob_qset_ob | rewrite q_ob_qset_br | rewrite q_ob_qset_st
    | rewrite q_ob_qset_z | rewrite q_ob_qmode
    | rewrite q_st_qset_ob | rewrite q_st_qset_br | rewrite q_st_qset_st
    | rewrite q_st_qset_z | rewrite q_st_qmode
    | rewrite q_mode_qset_ob | rewrite q_mode_qset_br
    | rewrite q_mode_qset_st | rewrite q_mode_qmode
    | rewrite hdr_set_bits | rewrite hdr_set_hold | rewrite hdr_set_back
    | rewrite hdr_set_mode | rewrite hdr_restore
    | rewrite sbits_set_bits | rewrite sbits_set_hold
    | rewrite sbits_set_mode | rewrite sbits_qrestore
    | rewrite shold_set_bits | rewrite shold_set_hold
    | rewrite shold_set_mode
    | rewrite stab_set_bits | rewrite stab_set_hold
    | rewrite stab_set_back | rewrite stab_set_mode
    | rewrite swin_set_bits | rewrite swin_set_hold
    | rewrite swin_set_back | rewrite swin_set_mode
    | rewrite sbld_set_bits | rewrite sbld_set_hold
    | rewrite sbld_set_back | rewrite sbld_set_mode
    | rewrite scur_set_bits | rewrite scur_set_hold
    | rewrite ulen_set_back | rewrite scur_set_mode
    | rewrite q_mode_qbad | rewrite q_br_qbad | rewrite q_ob_qbad
    | rewrite q_st_qbad ];
  cbn [br_have br_bits br_in br_next br_hold o_left o_put o_buf].

(** [s_hold (q_st (q_restore q))] and [s_bits ...] — the RESTORE leg *)
Lemma shold_qrestore : forall q, s_hold (q_st (q_restore q)) = br_hold (q_br q).
Proof. reflexivity. Qed.

(** ** [inf_LEN] / [inf_LEN_] *)
Lemma pres_LEN :
  forall c q,
    q_mode q = M_LEN ->
    ReachCore q ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    PresOk c (inf_LEN q).
Proof.
  intros c q Hm HC HL Htp Hb14 Hwd Hds.
  core_facts q HC.
  pose proof HL as (Htbl & Hlcs & Htds & Hltw & Hdtw & Hlbnd & Hlb & Hdb & Hroot0).
  rewrite inf_LEN_eq. unfold inf_LEN'. cbv zeta.
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)))
    eqn:Egate.
  - (* fast path: the inflate_fast call node *)
    apply andb_prop in Egate as (G1 & G2).
    apply Z.leb_le in G1. apply Z.leb_le in G2.
    assert (Hb40 : 0 <= a_bits (len_args q) <= 40)
      by (cbn [len_args a_bits]; lia).
    assert (Hwf : if_wf_lax (len_args q)).
    { split; [exact G1|]. split; [exact G2|].
      split; [exact Hb40|].
      split; [exact Hlb|]. split; [exact Hdb|].
      split; [exact Fsane|].
      split; [exact Fwh|]. split; [exact Fwn|].
      split; [exact (rc_bytes q HC)|]. split; [exact (rc_win q HC)|].
      split; [exact Hltw|]. split; [exact Hdtw|]. exact Hlbnd. }
    assert (Hain : a_avail_in (len_args q) <= 4294967290)
      by (cbn [len_args a_avail_in]; lia).
    assert (Haout : a_avail_out (len_args q) <= 4294967295)
      by (cbn [len_args a_avail_out]; lia).
    destruct (if_model_total_lax (len_args q) Hwf) as (y & EM).
    rewrite EM. cbv beta iota.
    pose proof (if_model_bytes (len_args q) (rc_win q HC) Fob) as HBy.
    rewrite EM in HBy. cbv beta iota in HBy.
    pose proof (if_model_pres (len_args q) Hwf Htbl Hain Haout) as HP.
    rewrite EM in HP.
    cbn [len_args a_avail_in a_bits a_avail_out] in HP.
    destruct HP as (Pbud & Pao & Pbits & Pai0 & Pao0 & Ph0).
    pose proof (if_model_hc (len_args q) Hwf Htbl) as Phc.
    rewrite EM in Phc. cbv beta iota in Phc.
    unfold len_post. cbv zeta.
    destruct (y_exit y) eqn:Eex; cbv beta iota.
    + (* ExLen: mode stays M_LEN *)
      lp_norm. rewrite Hm. cbv beta iota.
      split.
      * apply (reach_core_build q); lpp;
          try reflexivity; try assumption; try lia;
          try (cbv [q_load q_restore]; ksimp; lia).
      * apply reach_mode_scc.
        { left. lp_norm. exact Hm. }
        { apply (len_tbl_side_frame q); [reflexivity | exact HL]. }
        { apply (tblpd_frame q); [reflexivity | exact Htp]. }
        { lpp; first [ lia | (cbv [q_load q_restore]; ksimp; lia) ]. }
        { apply (tblwid_frame q); [lpp; reflexivity | exact Hwd]. }
        { apply (dist_sub_frame q); [lpp; reflexivity | exact Hds]. }
    + (* ExType *)
      lp_norm. cbv beta iota.
      split.
      * apply (reach_core_build q); lpp;
          try reflexivity; try assumption; try lia;
          try (cbv [q_load q_restore]; ksimp; lia).
      * apply reach_mode_hdr; [left; lpp; reflexivity | lpp; first [ lia | (cbv [q_load q_restore]; ksimp; lia) ] ].
    + (* ExBad *)
      lp_norm. cbv beta iota.
      split.
      * apply (reach_core_build q); lpp;
          try reflexivity; try assumption; try lia;
          try (cbv [q_load q_restore]; ksimp; lia).
      * apply reach_mode_inactive. lpp. reflexivity.
  - (* slow path: one decode on the live length table *)
    pose proof (tbl_of_wid015 (q_st q) (t_lencode (s_tab (q_st q))) Famb)
      as Hwid.
    pose proof (tbl_of_val_range (q_st q) (t_lencode (s_tab (q_st q))) Famb)
      as Hvr.
    destruct (inf_decode sub_len
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q))) (q_br q))
      as [h b' nb|b'|] eqn:Edec;
    [ | destruct (inf_decode_leave _ _ _ _ _ Hwid Fhold Hb
            (fun j => proj1 (rc_bytes q HC j)) Edec)
            as (Lh0 & Lin & Lhold & Lbits & Lbud);
        split;
        [ split;
          [ rc_close q
          | apply reach_mode_scc;
            [ left; exact Hm
            | apply (len_tbl_side_frame q); [reflexivity | exact HL]
            | apply (tblpd_frame q); [reflexivity | exact Htp]
            | bsimp;
              exact (inf_decode_leave_le14 _ _ _ _ _ (proj1 Htp) (proj2 Hlb) (proj1 Hwd)
                       (fun i _ Hs => sub_len_nz _ Hs) sub_len_240 Fhold Hb (fun j => proj1 (rc_bytes q HC j)) Edec)
            | apply (tblwid_frame q); [reflexivity | exact Hwd]
            | apply (dist_sub_frame q); [reflexivity | exact Hds] ] ]
        | intros _ _; left; exact Lh0 ]
    | exact I ].
    destruct (inf_decode_env _ _ _ _ _ _ _ Hwid Fhold Hb
                (fun j => proj1 (rc_bytes q HC j)) F39 Edec)
      as (Din & Dh & D39).
    pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Edec) as Db0.
    destruct (inf_decode_bud _ _ _ _ _ _ _ Edec) as (Dbud & Dhave).
    specialize (Dhave Hh).
    destruct (inf_decode_ok_facts _ _ _ _ _ _ _
                (fun i => proj1 (Hwid i)) Edec)
      as ((i0 & Hhe) & Hnb0).
    pose proof (inf_decode_nb_le30 _ _ _ _ _ _ _
                  (fun i => proj2 (Hwid i)) Edec) as Hnb30.
    pose proof (inf_decode_le14 _ _ _ _ _ _ _ (proj1 Htp)
                  (subguard_len_wid _ _ (proj1 Hwd) (fun i => proj1 (Hwid i))) Hb14 Edec) as Hb13.
    assert (Hval : 0 <= c_val h < 65536) by (rewrite Hhe; exact (Hvr i0)).
    destruct (Z.eqb (c_op h) 0) eqn:E0.
    + (* literal -> M_LIT *)
      split.
      * rc_close q.
      * apply reach_mode_scc.
        { right; right. unfold q_mode. bsimp. reflexivity. }
        { apply (len_tbl_side_frame q); [reflexivity | exact HL]. }
        { apply (tblpd_frame q); [reflexivity | exact Htp]. }
        { bsimp. lia. }
        { apply (tblwid_frame q); [reflexivity | exact Hwd]. }
        { apply (dist_sub_frame q); [reflexivity | exact Hds]. }
    + destruct (negb (Z.eqb (Z.land (c_op h) 32) 0)) eqn:E32.
      * (* end of block -> M_TYPE *)
        split; [rc_close q | apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity | bsimp; lia]].
      * destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)) eqn:E64.
        { (* invalid -> M_BAD *)
          split; [rc_close q | rm_off]. }
        (* length base: falls through IN-CALL to LENEXT *)
        apply Bool.negb_false_iff, Z.eqb_eq in E64.
        apply Bool.negb_false_iff, Z.eqb_eq in E32.
        apply Z.eqb_neq in E0.
        assert (Hv1 : 1 <= c_val h).
        { destruct Hlcs as (Lb0 & Leob & Lval).
          eapply inf_decode_val_pos; [exact Lval | exact Edec | | |];
            rewrite Hhe in E0, E32, E64 |- *; assumption. }
        pose proof (land15_range (c_op h)) as He15.
        apply pres_LENEXT;
          [ unfold q_mode; bsimp; reflexivity
          | rc_close q
          | ksimp; lia
          | ksimp; lia
          | ksimp; exact He15
          | ksimp; ubk; lia
          | apply (len_tbl_side_frame q); [reflexivity | exact HL]
          | apply (tblpd_frame q); [reflexivity | exact Htp]
          | ksimp; lia
          | apply (tblwid_frame q); [reflexivity | exact Hwd]
          | apply (dist_sub_frame q); [reflexivity | exact Hds] ].
Qed.

Lemma pres_LEN_ :
  forall c q, ReachCore q -> LenTblSide q -> TblPDSide q -> br_bits (q_br q) <= 14 -> TblWidSide q -> DistSubSide q ->
    PresOk c (inf_LEN_ q).
Proof.
  intros c q HC HL Htp Hb14 Hwd Hds. unfold inf_LEN_.
  apply pres_LEN.
  - reflexivity.
  - apply (reach_core_conv q); [exact HC|reflexivity..].
  - apply (len_tbl_side_frame q); [reflexivity | exact HL].
  - exact Htp.
  - exact Hb14.
  - exact Hwd.
  - apply (dist_sub_frame q); [reflexivity | exact Hds].
Qed.

(** ** [cl_have]/[ll] lower-bound walks (the build counter never
    decreases; [rc_bhave] reads these at the TABLE-chain successors) *)
Lemma cl_step_chave :
  forall t nb tot s,
    0 <= cl_have s ->
    match cl_step t nb tot s with
    | ClCont s' | ClDone s' | ClBad s' _ => 0 <= cl_have s'
    | _ => True
    end.
Proof.
  intros t nb tot s Hc. unfold cl_step.
  destruct (Z.leb tot (cl_have s)); cbv beta iota; [lia|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota;
    [|exact I|exact I].
  destruct (Z.ltb (c_val h) 16).
  { cbn [cl_have]. lia. }
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  cbv zeta.
  pose proof (bits_of_range 2 (br_dropbits (c_bits h) b') ltac:(lia)) as Hb2.
  pose proof (bits_of_range 3 (br_dropbits (c_bits h) b') ltac:(lia)) as Hb3.
  pose proof (bits_of_range 7 (br_dropbits (c_bits h) b') ltac:(lia)) as Hb7.
  destruct (Z.eqb (c_val h) 16); cbv beta iota.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota; [cbn [cl_have]; lia|].
    destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 2 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_have]; lia. }
  destruct (Z.eqb (c_val h) 17); cbv beta iota.
  { destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 3 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_have]; lia. }
  destruct (Z.ltb tot (cl_have s
              + (11 + br_bits_of 7 (br_dropbits (c_bits h) b'))));
    cbv beta iota; cbn [cl_have]; lia.
Qed.

Lemma cl_loop_chave :
  forall m t nb tot s r,
    0 <= cl_have s ->
    cl_loop m t nb tot s = Some r ->
    match r with
    | ClDone s' | ClBad s' _ => 0 <= cl_have s'
    | _ => True
    end.
Proof.
  induction m as [|m IH]; intros t nb tot s r Hc H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_chave t nb tot s Hc) as HS.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - exact (IH t nb tot s1 r HS H).
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact I.
  - injection H as H; subst r. cbv beta iota. exact I.
Qed.

Lemma ll_go_chave :
  forall f ncode have lens b,
    0 <= have ->
    match ll_go f ncode have lens b with
    | LlOk hv _ _ => 0 <= hv
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b Hc; cbn [ll_go]; [lia|].
  destruct (Z.ltb have ncode); cbv beta iota; [|lia].
  destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota; [|exact I].
  exact (IH ncode (have + 1)
           (zset lens (inf_order have) (br_bits_of 3 b'))
           (br_dropbits 3 b') ltac:(lia)).
Qed.

Lemma ll_zero_chave :
  forall f have lens, 0 <= have -> 0 <= fst (ll_zero f have lens).
Proof.
  induction f as [|f IH]; intros have lens Hc; cbn [ll_zero fst]; [lia|].
  destruct (Z.ltb have 19); cbv beta iota; [|cbn [fst]; lia].
  apply IH. lia.
Qed.

(** * The TABLE chain, under the ONE residual ([DynTblOk], as in
    StepReach's knot) *)
(* [cl_loop_leave] sits below the chave family it consumes. *)
Lemma cl_loop_leave :
  forall m t nb tot s s',
    TblSide t ->
    0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) ->
    0 <= br_hold (cl_br s) ->
    (forall j, 0 <= br_in (cl_br s) j) ->
    br_bits (cl_br s) <= 39 ->
    lens_ok (cl_lens s) ->
    0 <= cl_have s ->
    cl_loop m t nb tot s = Some (ClLeave s') ->
    br_have (cl_br s') = 0
    /\ br_in (cl_br s') = br_in (cl_br s)
    /\ 0 <= br_hold (cl_br s')
    /\ 0 <= br_bits (cl_br s') < 30
    /\ 8 * br_have (cl_br s') + br_bits (cl_br s')
       <= 8 * br_have (cl_br s) + br_bits (cl_br s)
    /\ lens_ok (cl_lens s')
    /\ 0 <= cl_have s'.
Proof.
  induction m as [|m IH]; intros t nb tot s s' Htbl Hh Hb Hhold Hin H39
    Hlens Hch H; [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_env t nb tot s Htbl Hh Hb Hhold Hin H39) as HE.
  pose proof (cl_step_walk t nb tot s Htbl Hh Hb Hlens) as HW.
  pose proof (cl_step_chave t nb tot s Hch) as HCh.
  pose proof (cl_step_inbud t nb tot s
                (fun i => proj1 (proj1 (Htbl i)))) as HBd.
  pose proof (fun s1 => cl_step_leave t nb tot s s1
                (fun i => proj1 (Htbl i)) Hhold Hb Hin) as HL.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - (* Cont: recurse *)
    destruct HE as (E1 & E2 & E3 & E4).
    destruct HW as (W1 & W2 & W3 & W4).
    cbv beta iota in HCh, HBd.
    assert (Hin1 : forall j, 0 <= br_in (cl_br s1) j)
      by (intros j; rewrite E1; apply Hin).
    destruct (IH t nb tot s1 s' Htbl W2 W3 E2 Hin1 E3 W4 HCh H)
      as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    split; [exact L1|]. split; [rewrite L2; exact E1|].
    split; [exact L3|]. split; [exact L4|].
    split; [lia|]. split; [exact L6|]. exact L7.
  - discriminate.
  - discriminate.
  - injection H as H; subst s'.
    destruct (HL s1 eq_refl) as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    split; [exact L1|]. split; [exact L2|].
    split; [exact L3|]. split; [exact L4|].
    split; [lia|].
    split; [rewrite L7; exact Hlens|].
    rewrite L6. exact Hch.
  - discriminate.
Qed.

(** ** [ll_go] leave (LENLENS): reader exhausted, lens_ok and the 3-bit
    prefix hold at the STORED have/lens (the rm_lens7 cross-call source). *)
Lemma ll_go_leave :
  forall f ncode have lens b hv ls b',
    0 <= br_have b -> 0 <= br_bits b -> 0 <= br_hold b ->
    (forall j, 0 <= br_in b j) ->
    lens_ok lens ->
    0 <= have ->
    (forall h, 0 <= h < have -> 0 <= lens (inf_order h) <= 7) ->
    ll_go f ncode have lens b = LlLeave hv ls b' ->
    br_have b' = 0
    /\ br_in b' = br_in b
    /\ 0 <= br_hold b'
    /\ 0 <= br_bits b' < 3
    /\ 8 * br_have b' + br_bits b' <= 8 * br_have b + br_bits b
    /\ lens_ok ls
    /\ 0 <= hv
    /\ (forall h, 0 <= h < hv -> 0 <= ls (inf_order h) <= 7).
Proof.
  induction f as [|f IH];
    intros ncode have lens b hv ls b' Hh Hb Hhold Hin Hlens Hhv Hpre H;
    cbn [ll_go] in H; [discriminate|].
  destruct (Z.ltb have ncode); cbv beta iota in H; [|discriminate].
  destruct (inf_nb 3 b) as [b1|b1] eqn:Enb; cbv beta iota in H.
  - (* NBOk: recurse *)
    pose proof (bits_of_range 3 b1 ltac:(lia)) as Hb3.
    change (2 ^ 3) with 8 in Hb3.
    pose proof (inf_nb_in _ _ _ Enb) as Nin.
    pose proof (inf_nb_hold _ _ _ Hhold Hb Hin Enb) as Nh.
    pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
    specialize (E3 Hh).
    assert (Hin1 : forall j, 0 <= br_in (br_dropbits 3 b1) j)
      by (intros j; cbn [br_dropbits br_in]; rewrite Nin; apply Hin).
    pose proof (inf_nb_ok _ _ _ Enb) as Eok.
    destruct (IH ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b1))
                (br_dropbits 3 b1) hv ls b'
                ltac:(cbn [br_dropbits br_have]; lia)
                ltac:(cbn [br_dropbits br_bits]; lia)
                ltac:(apply dropbits_hold_nonneg; exact Nh)
                Hin1
                ltac:(apply zset_lens_ok; [exact Hlens | lia])
                ltac:(lia)
                ltac:(intros h Hh19; unfold zset;
                      destruct (Z.eqb_spec (inf_order h) (inf_order have))
                        as [E|NE]; [lia|];
                      apply Hpre;
                      assert (h <> have) by (intro; subst; congruence);
                      lia)
                H)
      as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    cbn [br_dropbits br_have br_bits br_in] in L2, L5.
    split; [exact L1|]. split; [rewrite L2; exact Nin|].
    split; [exact L3|]. split; [exact L4|].
    split; [lia|]. split; [exact L6|]. split; [exact L7|]. exact L8.
  - (* NBLeave: the leave *)
    injection H as <- <- <-.
    destruct (inf_nb_leave 3 b b1 ltac:(lia) Hb Hhold Hin Enb)
      as (L1 & L2 & L3 & L4 & L5).
    split; [exact L1|]. split; [exact L2|].
    split; [exact L3|]. split; [lia|].
    split; [lia|]. split; [exact Hlens|]. split; [exact Hhv|]. exact Hpre.
Qed.

(** N.B. the leave hands back the CURRENT have/lens (hv = have, ls = lens
    at the failing trip), so [lens_ok ls] and the prefix are the threaded
    invariants, and [rm_lens7]'s cross-call story is exactly this fact. *)

(** * Pre-work B: OUTPUT-BYTE walks (the [rc_outb] discharge family).

    The model writes only byte-valued output — u8 literals, window
    bytes, input bytes, or its own earlier output — so a pointwise value
    invariant threads with NO table facts at all (unlike the bud/fin/
    cmono walks): the case trees are the same, the leaves are frame or
    copy-value. *)


Section PresKnot.

Variable Hdyn : DynTblOk.

(* RSS cure (b1) (ca2-b1 / F45, 2026-09-08): the Qed kernel check of this one term was measured at +6.5 GiB over a 2.24 GiB tactic
   phase; at each of the five reach_core_build sites the goal's state record is `set` as a local definition before the apply, so the premise proofs are
   built over the small name and the kernel term holds one let-bound copy per arm; statement and every other line byte-identical. *)
Lemma pres_CODELENS :
  forall c q,
    q_mode q = M_CODELENS ->
    ReachCore q ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    257 <= b_nlen (s_bld (q_st q)) <= 286 /\ 1 <= b_ndist (s_bld (q_st q)) <= 30 ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    TblPD (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q))) ->
    br_bits (q_br q) <= 14 ->
    t_lenbits (s_tab (q_st q)) <= 7 ->
    t_lencode (s_tab (q_st q)) = TRcodes 0 ->
    1 <= t_lenbits (s_tab (q_st q)) ->
    2 ^ t_lenbits (s_tab (q_st q)) <= t_next (s_tab (q_st q)) ->
    (forall i, 0 <= i < 2 ^ t_lenbits (s_tab (q_st q)) -> 0 <= c_op (t_codes (s_tab (q_st q)) i) < 256) ->
    PresOk c (inf_CODELENS c q).
Proof.
  intros c q Hm HC Hnl Hnd Hnt Htl HtpCL Hb14 Hlb7 Hc0 Hc1 Hc2 Hc3.
  core_facts q HC.
  assert (Hnlen0 : 0 <= b_nlen (s_bld (q_st q))) by lia.
  assert (Hndist0 : 0 <= b_ndist (s_bld (q_st q))) by lia.
  unfold inf_CODELENS. cbv zeta beta.
  destruct (cl_loop_at_codelens_fuel
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q)))
              (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
              {| cl_have := b_have (s_bld (q_st q));
                 cl_lens := b_lens (s_bld (q_st q));
                 cl_br := q_br q |}
              ltac:(cbn [cl_br]; lia) ltac:(cbn [cl_have]; lia))
    as (r & Hr & Hexit).
  rewrite Hr. cbv beta iota.
  pose proof (cl_loop_walk
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Flens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  pose proof (cl_loop_env
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Fhold
                (fun j => proj1 (rc_bytes q HC j)) F39 Flens Hr) as HE.
  cbn [cl_br cl_lens cl_have] in HE.
  pose proof (cl_loop_chave
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r ltac:(cbn [cl_have]; lia) Hr)
    as HCh.
  pose proof (cl_loop_bits14 (S (Z.to_nat (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q)); cl_lens := b_lens (s_bld (q_st q)); cl_br := q_br q |} r HtpCL Hb14 Hr) as HB14.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction;
    [ | |
      destruct (cl_loop_leave
          (S (Z.to_nat (b_nlen (s_bld (q_st q))
                        + b_ndist (s_bld (q_st q)))))
          (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
          (t_lenbits (s_tab (q_st q)))
          (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
          {| cl_have := b_have (s_bld (q_st q));
             cl_lens := b_lens (s_bld (q_st q));
             cl_br := q_br q |} s1
          Htl Hh Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) F39 Flens Fbh Hr)
          as (Lh0 & Lin & Lhold & Lbits & Lbud & Llens & Lch);
      cbn [cl_br cl_lens cl_have]
        in Lh0, Lin, Lhold, Lbits, Lbud, Llens, Lch;
      split;
      [ split;
        [ rc_close q
        | apply reach_mode_codelens;
          [ exact Hm | exact Hnl | exact Hnd | exact Hnt | exact Htl | exact HtpCL
          | cbn [q_br qset_br];
            exact (cl_loop_leave_le14 (S (Z.to_nat (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q)); cl_lens := b_lens (s_bld (q_st q)); cl_br := q_br q |} s1 HtpCL Htl Hlb7 Hb14 Hh Hb Fhold (fun j => proj1 (rc_bytes q HC j)) Flens Hr)
          | exact Hlb7 | exact Hc0 | exact Hc1 | exact Hc2 | exact Hc3 ] ]
      | intros _ _; left; exact Lh0 ] ].
  - (* ClDone: the two builds *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbv beta iota in HCh.
    cbv beta iota in HB14.
    destruct (Z.eqb (cl_lens s1 256) 0).
    { split.
      - match goal with |- ReachCore ?qq => set (st1 := qq) end.
        apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try hc_close;
          try (unfold st1; ksimp; lia); try (unfold st1; ksimp; hc_close).
      - rm_off. }
    unfold inf_table.
    assert (HLB1 : GtItTotal.LensBounded (cl_lens s1)
                     (b_nlen (s_bld (q_st q))))
      by (intros i _; apply W4).
    assert (HWF1 : it_wf CT_LENS (cl_lens s1) (b_nlen (s_bld (q_st q))) 9).
    { split; [lia|]. split; [intros i _; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; left; split; [reflexivity | lia]. }
    match goal with
    | |- context [it_model CT_LENS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_LENS l cs rt t0) as R1 eqn:EI1
    end.
    destruct R1 as [o1|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hnlen0 HLB1 (eq_sym EI1)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
    { (* rejected LENS build: codes_wb is INSTALLED on this qbad *)
      split.
      - match goal with |- ReachCore ?qq => set (st2 := qq) end.
        apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try hc_close;
          try (unfold st2; ksimp; lia); try (unfold st2; ksimp; hc_close).
        exact (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                 (b_nlen (s_bld (q_st q))) 9
                 (t_codes (s_tab (q_st q))) 0 o1
                 Famb HWF1
                 (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                 (eq_sym EI1)).
      - rm_off. }
    apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
    assert (HLB2 : GtItTotal.LensBounded
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))))
      by (intros i _; cbv beta; apply W4).
    assert (HWF2 : it_wf CT_DISTS
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))) 6).
    { split; [lia|]. split; [intros i _; cbv beta; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; right; split; [reflexivity | lia]. }
    match goal with
    | |- context [it_model CT_DISTS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_DISTS l cs rt t0) as R2 eqn:EI2
    end.
    destruct R2 as [o2|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hndist0 HLB2 (eq_sym EI2)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o2) 0)) eqn:Er2.
    { (* rejected DISTS build: both writes installed on this qbad *)
      split.
      - match goal with |- ReachCore ?qq => set (st3 := qq) end.
        apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try hc_close;
          try (unfold st3; ksimp; lia); try (unfold st3; ksimp; hc_close).
        exact (dyn_amb_wb Hdyn CT_DISTS
                 (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                 (b_ndist (s_bld (q_st q))) 6
                 (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
                 (0 + o_used o1) o2
                 (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                    (b_nlen (s_bld (q_st q))) 9
                    (t_codes (s_tab (q_st q))) 0 o1
                    Famb HWF1
                    (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                    (eq_sym EI1))
                 HWF2
                 (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
                 (eq_sym EI2)).
      - rm_off. }
    apply Bool.negb_false_iff in Er2. apply Z.eqb_eq in Er2.
    (* accepted: fall through IN-CALL to LEN_ at the installed state *)
    set (d := {| db_cs := t_codes (s_tab (q_st q));
                 db_lens := cl_lens s1;
                 db_nlen := b_nlen (s_bld (q_st q));
                 db_ndist := b_ndist (s_bld (q_st q));
                 db_o1 := o1; db_o2 := o2 |}).
    assert (Hdok : db_ok d).
    { split; [exact Famb|].
      split; [exact HWF1|].
      split; [exact (eq_sym EI1)|].
      split; [exact Er1|].
      split; [exact HWF2|].
      split; [exact (eq_sym EI2)|].
      exact Er2. }
    match goal with
    | |- context [if _ then InfLeave ?qq else _] =>
        assert (HRC : ReachCore qq); [ | assert (HLT : LenTblSide qq); [ | assert (HTP : TblPDSide qq); [ | assert (HWD : TblWidSide qq); [ | assert (HDS : DistSubSide qq) ] ] ] ]
    end.
    {
      match goal with |- ReachCore ?qq => set (st4 := qq) end.
      apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try hc_close;
        try (unfold st4; ksimp; lia); try (unfold st4; ksimp; hc_close).
      exact (dyn_amb_wb Hdyn CT_DISTS
               (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
               (b_ndist (s_bld (q_st q))) 6
               (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
               (0 + o_used o1) o2
               (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                  (b_nlen (s_bld (q_st q))) 9
                  (t_codes (s_tab (q_st q))) 0 o1
                  Famb HWF1
                  (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                  (eq_sym EI1))
               HWF2
               (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
               (eq_sym EI2)).
    }
    {
      match goal with
      | |- LenTblSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      split. { exact (dyn_wf_tbl Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_lcside Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_tblside_d Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_two_l Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_two_d Hdyn d _ Hdok Hinst). }
      split. { exact (wf_tbl_len_bounded _
                        (dyn_wf_tbl Hdyn d _ Hdok Hinst)). }
      split. { exact (dyn_lenbits Hdyn d Hdok). }
      split. { exact (dyn_distbits Hdyn d Hdok). }
      exact (dyn_root_opshape Hdyn d _ Hdok Hinst).
    }
    { match goal with
      | |- TblPDSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      split; [exact (tblpd_installed_len d _ Hdok Hinst) | exact (tblpd_installed_dist d _ Hdok Hinst)]. }
    { match goal with
      | |- TblWidSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      exact (tblwid_installed d _ Hdok Hinst). }
    { match goal with
      | |- DistSubSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      exact (dsub_installed d _ Hdok Hinst). }
    destruct (Z.eqb (n_flush c) Z_TREES) eqn:Efl;
      [ split;
        [ split;
          [ exact HRC
          | apply reach_mode_scc;
            [ right; left; unfold q_mode; bsimp; reflexivity
            | exact HLT
            | exact HTP
            | ksimp; exact HB14
            | exact HWD
            | exact HDS ] ]
        | intros Hf _; exfalso; rewrite Hf in Efl; cbv in Efl;
          discriminate ]
      |].
    apply pres_LEN_.
    + exact HRC.
    + exact HLT.
    + exact HTP.
    + ksimp; exact HB14.
    + exact HWD.
    + exact HDS.
  - (* ClBad: the loop's own rejection *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbv beta iota in HCh.
    split.
    + match goal with |- ReachCore ?qq => set (st5 := qq) end.
      apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try hc_close;
        try (unfold st5; ksimp; lia); try (unfold st5; ksimp; hc_close).
    + rm_off.
Qed.

Lemma pres_LENLENS :
  forall c q,
    q_mode q = M_LENLENS ->
    ReachCore q ->
    (forall h, 0 <= h < b_have (s_bld (q_st q)) ->
       0 <= b_lens (s_bld (q_st q)) (inf_order h) <= 7) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    257 <= b_nlen (s_bld (q_st q)) <= 286 /\ 1 <= b_ndist (s_bld (q_st q)) <= 30 ->
    br_bits (q_br q) <= 14 ->
    PresOk c (inf_LENLENS c q).
Proof.
  intros c q Hm HC Hpre7 Hnl Hnd Hnt Hb14.
  core_facts q HC.
  unfold inf_LENLENS. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Flens) as HW.
  pose proof (ll_go_env 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Fhold
                (fun j => proj1 (rc_bytes q HC j)) F39) as HE.
  pose proof (ll_go_chave 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Fbh) as HCh.
  pose proof (ll_go_le7 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hpre7) as HL7.
  pose proof (ll_go_bits14 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hb14) as HB14.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b];
    [| destruct (ll_go_leave _ _ _ _ _ _ _ _ Hh Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Flens Fbh Hpre7 (eq_sym ELG))
          as (Lh0 & Lin & Lhold & Lbits & Lbud & Llens & Lhv & Lp7);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_lenlens;
           [ exact Hm | exact Lp7 | exact Hnl | exact Hnd | exact Hnt | bsimp; lia ] ]
       | intros _ _; left; exact Lh0 ] ].
  destruct HW as (W1 & W2 & W3 & W4).
  destruct HE as (Ein & Ehold & E39 & E0b).
  cbv beta iota in HCh.
  cbv beta iota in HB14.
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  assert (Hhv1 : 0 <= hv1).
  { pose proof (ll_zero_chave 19 hv ls HCh) as HZ2.
    rewrite <- EZ in HZ2. cbn [fst] in HZ2. exact HZ2. }
  cbv beta iota in HL7. destruct HL7 as (Hhvge & Hp7).
  assert (Hg7 : forall h, 0 <= h < 19 -> 0 <= ls1 (inf_order h) <= 7).
  { intros h Hh19.
    pose proof (ll_zero_le7 19 hv ls Hp7
                  ltac:(cbn [Z.of_nat]; lia) h Hh19) as HZ7.
    rewrite <- EZ in HZ7. cbn [snd] in HZ7. exact HZ7. }
  assert (Hguard : CT_CODES = CT_CODES ->
                   forall i, 0 <= i < 19 -> ls1 i <= 7).
  { intros _ i Hi.
    destruct (inf_order_covers i Hi) as (h & Hh19 & E).
    rewrite <- E. exact (proj2 (Hg7 h Hh19)). }
  unfold inf_table.
  assert (HLB : GtItTotal.LensBounded ls1 19) by (intros i _; apply Hls1).
  assert (HWFC : it_wf CT_CODES ls1 19 7).
  { split; [lia|]. split; [intros i _; apply Hls1|].
    split; [unfold MAXBITS; lia|].
    left; split; [reflexivity | lia]. }
  match goal with
  | |- context [it_model CT_CODES ?l ?cs ?rt ?t0] =>
      remember (it_model CT_CODES l cs rt t0) as R1 eqn:EI1
  end.
  destruct R1 as [o1|].
  2:{ exfalso.
      assert (Hc19 : 0 <= 19) by lia.
      exact (it_model_total _ _ _ _ _ Hc19 HLB (eq_sym EI1)). }
  cbv beta iota zeta.
  destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
  { (* rejected CODES build: codes_wb installed on this qbad *)
    split.
    - apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try lia; try hc_close.
      exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
               (t_codes (s_tab (q_st q))) 0 o1
               Famb HWFC Hguard (eq_sym EI1)).
    - rm_off. }
  apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
  apply pres_CODELENS; [unfold q_mode; bsimp; reflexivity| | | | | | | | | | | |].
  - apply (reach_core_build q); ksimp;
      try reflexivity; try assumption; try lia; try hc_close.
    exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
             (t_codes (s_tab (q_st q))) 0 o1
             Famb HWFC Hguard (eq_sym EI1)).
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. lia.
  - exact (dyn_codes_tblside Hdyn ls1 19 7
             (t_codes (s_tab (q_st q))) o1 Famb HWFC (eq_sym EI1)
             Er1).
  - (* rm_tblpdCL: the CODES build's TblPD through the codes_wb view *)
    unfold tbl_of; ksimp.
    apply tblpd_codes_wb0.
    + apply (it_tblpd_wf CT_CODES ls1 19 7 (fun i => t_codes (s_tab (q_st q)) (0 + i)) o1);
        [lia | intros i _; apply Hls1 | lia | left; split; [reflexivity | lia] | exact (eq_sym EI1) | exact Er1].
    + exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7 (t_codes (s_tab (q_st q))) 0 o1 Famb HWFC Hguard (eq_sym EI1)).
  - ksimp. exact HB14.
  - (* STOP #8 fact at the CODELENS successor: the CODES build's root is <= 7 (it_model root = min root0 max_len) *)
    ksimp.
    exact (codes_build_root7 ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1).
  - (* rm_tblCL0 (T2 res-t2; R2083 section 2): the successor's lencode is the CODES table at TRcodes 0 *) ksimp. reflexivity.
  - (* rm_tblCL1 (T2) *) ksimp. exact (proj1 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1)).
  - (* rm_tblCL2 (T2) *) ksimp. pose proof (proj1 (proj2 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1))) as HU. lia.
  - (* rm_tblCL3 (T2): the op range below the root block, through the codes_wb view at offset 0 *)
    ksimp. intros i Hi. unfold codes_wb. destruct (Z.leb 0 i) eqn:Ei;
      [ rewrite Z.sub_0_r; exact (proj2 (proj2 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1)) i Hi) | apply Z.leb_gt in Ei; lia ].
Qed.

Lemma pres_TABLE :
  forall c q, q_mode q = M_TABLE -> ReachCore q -> br_bits (q_br q) <= 14 -> PresOk c (inf_TABLE c q).
Proof.
  intros c q Hm HC Hb14.
  core_facts q HC.
  unfold inf_TABLE.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 14 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr; [right; right; unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; reflexivity | bsimp; lia] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as E14.
  pose proof (inf_nb_ok_le _ _ _ Enb) as Ele.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 14 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  pose proof (bits_of_range 5 b ltac:(lia)) as B1.
  change (2 ^ 5) with 32 in B1.
  pose proof (bits_of_range 5 (br_dropbits 5 b) ltac:(lia)) as B2.
  change (2 ^ 5) with 32 in B2.
  cbv zeta.
  destruct (Z.ltb 286 (br_bits_of 5 b + 257)
            || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)) eqn:Eg.
  { split; [rc_close q | rm_off]. }
  apply Bool.orb_false_iff in Eg. destruct Eg as (Eg1 & Eg2).
  apply Z.ltb_ge in Eg1. apply Z.ltb_ge in Eg2.
  apply pres_LENLENS; [unfold q_mode; bsimp; reflexivity| | | | | |].
  - rc_close q.
  - ksimp. intros h Hh0. lia.
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. c6bits.
Qed.

(** ** The dispatch, the [=InfCont] corollary, and [reach_iter] *)
Theorem step_pres :
  forall c q, ReachSt q -> PresOk c (inf_step c q).
Proof.
  intros c q HR. pose proof HR as (HC & HM).
  destruct HM as [Hmatch Hlen1 Hextra Hoffext Hlenub HtblL HtblCL Hbldrng
                  Hlens7 Hback Hnlen257 Htblpd HtblpdCL Hbits14 Hbits0 Hwid Hoff16 Hdsub Hoff1 Hwrote0 HtblCL0 HtblCL1 HtblCL2 HtblCL3].
  unfold inf_step.
  destruct (q_mode q) eqn:Hm.
  - exact (pres_HEAD c q Hm HC (proj1 Hbits0 eq_refl) (fun _ => Hwrote0 eq_refl)).
  - exact (pres_FLAGS c q Hm HC).
  - exact (pres_TIME c q Hm HC).
  - exact (pres_OS c q Hm HC).
  - exact (pres_EXLEN c q Hm HC (proj1 (proj2 Hbits0) eq_refl)).
  - exact (pres_EXTRA c q Hm HC (proj1 (proj2 (proj2 Hbits0)) (or_introl eq_refl))).
  - exact (pres_NAME c q Hm HC (proj1 (proj2 (proj2 Hbits0)) (or_intror (or_introl eq_refl)))).
  - exact (pres_COMMENT c q Hm HC (proj1 (proj2 (proj2 Hbits0)) (or_intror (or_intror eq_refl)))).
  - exact (pres_HCRC c q Hm HC (proj1 (proj2 (proj2 (proj2 Hbits0))) eq_refl)).
  - exact (pres_DICTID c q Hm HC).
  - apply pres_DICT; [exact HC | pose proof (proj2 (proj2 (proj2 (proj2 Hbits0))) (or_introl eq_refl)) as E0; lia].
  - exact (pres_TYPE c q Hm HC (Hbits14 (or_introl eq_refl))).
  - exact (pres_TYPEDO c q (or_introl Hm) HC (Hbits14 (or_intror (or_introl eq_refl)))).
  - exact (pres_STORED c q Hm HC).
  - exact (pres_COPY_ c q HC (proj2 (proj2 (proj2 (proj2 Hbits0))) (or_intror (or_introl eq_refl)))).
  - apply pres_COPY; [exact Hm | exact HC | exact (proj2 (proj2 (proj2 (proj2 Hbits0))) (or_intror (or_intror eq_refl)))].
  - exact (pres_TABLE c q Hm HC (Hbits14 (or_intror (or_intror (or_introl eq_refl))))).
  - destruct (Hbldrng (or_introl eq_refl)) as (Bn & Bd).
    exact (pres_LENLENS c q Hm HC (Hlens7 eq_refl) Bn Bd
             (Hnlen257 (or_introl eq_refl))
             (Hbits14 (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
  - destruct (Hbldrng (or_intror eq_refl)) as (Bn & Bd).
    exact (pres_CODELENS c q Hm HC Bn Bd (Hnlen257 (or_intror eq_refl))
             (HtblCL eq_refl) (proj1 (HtblpdCL eq_refl))
             (Hbits14 (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))
             (proj2 (HtblpdCL eq_refl))
             (HtblCL0 eq_refl) (HtblCL1 eq_refl) (HtblCL2 eq_refl) (HtblCL3 eq_refl)).
  - apply pres_LEN_;
      [ exact HC | apply HtblL; right; left; reflexivity
      | apply Htblpd; right; left; reflexivity
      | apply Hbits14; do 5 right; left; reflexivity
      | apply Hwid; right; left; reflexivity
      | apply Hdsub; right; left; reflexivity ].
  - apply pres_LEN;
      [ exact Hm | exact HC | apply HtblL; left; reflexivity
      | apply Htblpd; left; reflexivity
      | apply Hbits14; do 6 right; left; reflexivity
      | apply Hwid; left; reflexivity
      | apply Hdsub; left; reflexivity ].
  - apply pres_LENEXT;
      [ exact Hm
      | exact HC
      | apply Hlen1; left; reflexivity
      | apply (proj1 Hlenub); reflexivity
      | apply Hextra; left; reflexivity
      | apply (proj1 Hback); reflexivity
      | apply HtblL; right; right; left; reflexivity
      | apply Htblpd; right; right; left; reflexivity
      | apply Hbits14; do 7 right; left; reflexivity
      | apply Hwid; right; right; left; reflexivity
      | apply Hdsub; right; right; left; reflexivity ].
  - apply pres_DIST;
      [ exact Hm
      | exact HC
      | apply Hlen1; right; left; reflexivity
      | apply (proj2 Hlenub); left; reflexivity
      | apply (proj1 (proj2 Hback)); reflexivity
      | apply HtblL; right; right; right; left; reflexivity
      | apply Htblpd; right; right; right; left; reflexivity
      | apply Hbits14; do 8 right; left; reflexivity
      | apply Hwid; right; right; right; left; reflexivity
      | apply Hdsub; right; right; right; left; reflexivity ].
  - destruct (Hoffext eq_refl) as (Ho1 & Ho2).
    apply pres_DISTEXT;
      [ exact Hm
      | exact HC
      | apply Hlen1; right; right; reflexivity
      | apply (proj2 Hlenub); right; left; reflexivity
      | apply Hextra; right; reflexivity
      | exact Ho1
      | exact Ho2
      | apply (proj2 (proj2 Hback)); reflexivity
      | apply HtblL; right; right; right; right; left; reflexivity
      | apply Htblpd; right; right; right; right; left; reflexivity
      | apply Hbits14; do 9 right; left; reflexivity
      | apply Hwid; right; right; right; right; left; reflexivity
      | exact (Hoff16 eq_refl)
      | apply Hdsub; do 4 right; left; reflexivity
      | exact (proj1 Hoff1 eq_refl) ].
  - apply pres_MATCH;
      [ exact Hm
      | exact HC
      | exact (Hmatch eq_refl)
      | apply (proj2 Hlenub); right; right; reflexivity
      | apply HtblL; right; right; right; right; right; left; reflexivity
      | apply Htblpd; right; right; right; right; right; left; reflexivity
      | apply Hbits14; do 10 right; left; reflexivity
      | apply Hwid; do 5 right; left; reflexivity
      | apply Hdsub; do 5 right; left; reflexivity
      | exact (proj2 Hoff1 eq_refl) ].
  - apply pres_LIT;
      [ exact Hm
      | exact HC
      | apply HtblL; right; right; right; right; right; right; reflexivity
      | apply Htblpd; do 6 right; reflexivity
      | apply Hbits14; do 11 right; reflexivity
      | apply Hwid; do 6 right; reflexivity
      | apply Hdsub; do 6 right; reflexivity ].
  - exact (pres_CHECK c q Hm HC).
  - exact (pres_LENGTH c q Hm HC).
  - exact (pres_DONE c q Hm HC).
  - exact (pres_BAD c q Hm HC).
  - exact (pres_MEM c q).
  - exact (pres_SYNC c q).
Qed.

Corollary step_pres_eq :
  forall c q q', ReachSt q -> inf_step c q = InfCont q' -> ReachSt q'.
Proof.
  intros c q q' HR HE.
  pose proof (step_pres c q HR) as HP.
  rewrite HE in HP. exact HP.
Qed.

(** [ReachSt] along the landed [inf_iter] (Inflate.v:1783): the state
    after ANY number of fall-through trips is reachable-invariant. *)
Theorem reach_iter :
  forall k c q q', ReachSt q -> inf_iter k c q = Some q' -> ReachSt q'.
Proof.
  induction k as [|k IH]; intros c q q' HR H.
  - cbn [inf_iter] in H. injection H as <-. exact HR.
  - rewrite inf_iter_S in H.
    pose proof (step_pres c q HR) as HP.
    destruct (inf_step c q) as [q1|q1|q1 r0|m0|] eqn:ES; try discriminate.
    cbv beta iota in HP.
    exact (IH c q1 q' HP H).
Qed.

End PresKnot.

(** * Establishment at the reset state (the driver-side contract)

    [inflateResetKeep] writes mode/hold/bits/sane/table-pointers/back but
    NOT the cursor, build or codes fields — like the C, whose ZALLOC does
    not zero ([inflate_state0]'s garbage parameter).  Their obligations
    below ([u_length]/[b_*]/[amb_ok]) are therefore the DRIVER's: a
    concrete driver instantiates the garbage state (zeros) and discharges
    them by [vm_compute].  The window triple is zeroed by [inflateReset]
    itself; [ReachMode] is vacuous at M_HEAD. *)
Lemma reach_init_keep :
  forall z s z' s' a,
    inflateResetKeep z s = (z', s') ->
    g_st a = s' ->
    w_wsize (s_win s) = 0 ->
    w_whave (s_win s) = 0 ->
    w_wnext (s_win s) = 0 ->
    (forall j, 0 <= g_inbuf a j < 256) ->
    0 <= g_avail_in a <= 4294967290 ->
    0 <= g_avail_out a <= 4294967295 ->
    (forall j, 0 <= w_win (s_win s) j < 256) ->
    0 <= u_length (s_cur s) ->
    lens_ok (b_lens (s_bld s)) ->
    0 <= b_have (s_bld s) ->
    0 <= b_nlen (s_bld s) ->
    0 <= b_ndist (s_bld s) ->
    amb_ok (t_codes (s_tab s)) ->
    LeafPosT (t_codes (s_tab s)) ->
    (forall j, 0 <= g_outbuf a j < 256) ->
    ReachSt (inf_st0 a).
Proof.
  intros z s z' s' a HR Hg Hws Hwh Hwn Hbytes Hain Haout Hwinb Hlen Hlens
    Hbh Hbn Hbd Hamb Hlp Houtb.
  unfold inflateResetKeep in HR. cbv zeta in HR.
  injection HR as HRz HRs.
  subst s'.
  unfold inf_st0. rewrite Hg.
  match goal with |- ReachSt ?qq => set (q0 := qq) end.
  assert (Em : q_mode q0 = M_HEAD) by reflexivity.
  assert (Ebits : br_bits (q_br q0) = 0) by reflexivity.
  assert (Ehold : br_hold (q_br q0) = 0) by reflexivity.
  assert (Ehave : br_have (q_br q0) = g_avail_in a) by reflexivity.
  assert (Ein : forall j, br_in (q_br q0) j = g_inbuf a j)
    by (intros j; reflexivity).
  assert (Eleft : o_left (q_ob q0) = g_avail_out a) by reflexivity.
  assert (Eobuf : forall j, o_buf (q_ob q0) j = g_outbuf a j)
    by (intros j; reflexivity).
  assert (Eqout : q_out q0 = g_avail_out a) by reflexivity.
  assert (Eqin : q_in q0 = g_avail_in a) by reflexivity.
  assert (Esane : t_sane (s_tab (q_st q0)) = 1) by reflexivity.
  assert (Ecodes : t_codes (s_tab (q_st q0)) = t_codes (s_tab s))
    by reflexivity.
  assert (Ewin : s_win (q_st q0) = s_win s) by reflexivity.
  assert (Ecur : u_length (s_cur (q_st q0)) = u_length (s_cur s))
    by reflexivity.
  assert (Ebld : s_bld (q_st q0) = s_bld s) by reflexivity.
  split.
  - constructor.
    + unfold q_pos. rewrite Ehave, Ebits, Eleft. lia.
    + rewrite Ebits. lia.
    + intros j. rewrite Ein. exact (Hbytes j).
    + rewrite Ehold. lia.
    + intros j. rewrite Ewin. exact (Hwinb j).
    + rewrite Ewin, Hws, Hwn. lia.
    + rewrite Ewin, Hws, Hwh. lia.
    + exact Esane.
    + rewrite Ecur. exact Hlen.
    + rewrite Ehave, Ebits. lia.
    + rewrite Eleft. lia.
    + rewrite Ebld. exact Hlens.
    + rewrite Ebld. exact Hbh.
    + rewrite Ebld. exact Hbn.
    + rewrite Ebld. exact Hbd.
    + rewrite Ecodes. exact Hamb.
    + intros j. rewrite Eobuf. exact (Houtb j).
    + rewrite Ewin, Hwh, Hwn. right. reflexivity.
    + rewrite Eleft, Eqout. lia.
    + rewrite Eqout. lia.
    + rewrite Ebits, Ehave, Eqin. lia.
    + rewrite Ehold, Ebits. reflexivity.
    + rewrite Ecodes. exact Hlp.
    + rewrite Ewin. intros _. exact Hws.
  - apply reach_mode_hdr0; [left; exact Em | | intros _; rewrite Eqout, Eleft; lia].
    unfold Bits0Side; repeat apply conj; intros Hm0; try (destruct Hm0 as [Hm0|[Hm0|Hm0]]);
      rewrite Em in Hm0; try discriminate Hm0; intros _; exact Ebits.
Qed.

Theorem reach_reset :
  forall z s z' s' a,
    inflateReset z s = (z', s') ->
    g_st a = s' ->
    (forall j, 0 <= g_inbuf a j < 256) ->
    0 <= g_avail_in a <= 4294967290 ->
    0 <= g_avail_out a <= 4294967295 ->
    (forall j, 0 <= w_win (s_win s) j < 256) ->
    0 <= u_length (s_cur s) ->
    lens_ok (b_lens (s_bld s)) ->
    0 <= b_have (s_bld s) ->
    0 <= b_nlen (s_bld s) ->
    0 <= b_ndist (s_bld s) ->
    amb_ok (t_codes (s_tab s)) ->
    LeafPosT (t_codes (s_tab s)) ->
    (forall j, 0 <= g_outbuf a j < 256) ->
    ReachSt (inf_st0 a).
Proof.
  intros z s z' s' a HR Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn
    Hbd Hamb Hlp Houtb.
  unfold inflateReset in HR.
  exact (reach_init_keep _ _ _ _ _ HR Hg
           eq_refl eq_refl eq_refl
           Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn Hbd Hamb Hlp Houtb).
Qed.

Theorem reach_reset2 :
  forall z s wb z' s' a,
    inflateReset2 z s wb = Some (z', s') ->
    g_st a = s' ->
    (forall j, 0 <= g_inbuf a j < 256) ->
    0 <= g_avail_in a <= 4294967290 ->
    0 <= g_avail_out a <= 4294967295 ->
    (forall j, 0 <= w_win (s_win s) j < 256) ->
    0 <= u_length (s_cur s) ->
    lens_ok (b_lens (s_bld s)) ->
    0 <= b_have (s_bld s) ->
    0 <= b_nlen (s_bld s) ->
    0 <= b_ndist (s_bld s) ->
    amb_ok (t_codes (s_tab s)) ->
    LeafPosT (t_codes (s_tab s)) ->
    (forall j, 0 <= g_outbuf a j < 256) ->
    ReachSt (inf_st0 a).
Proof.
  intros z s wb z' s' a HR Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn
    Hbd Hamb Hlp Houtb.
  unfold inflateReset2 in HR. cbv zeta in HR.
  destruct (Z.ltb wb 0).
  - destruct (Z.ltb wb (-15)); cbv beta iota in HR; [discriminate|].
    destruct (negb (Z.eqb (- wb) 0) && (Z.ltb (- wb) 8 || Z.ltb 15 (- wb)));
      [discriminate|].
    cbv zeta in HR.
    destruct (w_alloc (s_win s) && negb (Z.eqb (w_wbits (s_win s)) (- wb))).
    + injection HR as HRz HRs.
      exact (reach_reset z
               (set_wbits (set_wrap (set_alloc s false) 0) (- wb)) z' s' a
               (f_equal2 (fun u v => (u, v)) HRz HRs)
               Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn Hbd Hamb Hlp Houtb).
    + injection HR as HRz HRs.
      exact (reach_reset z (set_wbits (set_wrap s 0) (- wb)) z' s' a
               (f_equal2 (fun u v => (u, v)) HRz HRs)
               Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn Hbd Hamb Hlp Houtb).
  - cbv beta iota in HR.
    destruct (negb (Z.eqb (if Z.ltb wb 48 then Z.land wb 15 else wb) 0)
              && (Z.ltb (if Z.ltb wb 48 then Z.land wb 15 else wb) 8
                  || Z.ltb 15 (if Z.ltb wb 48 then Z.land wb 15 else wb)));
      [discriminate|].
    cbv zeta in HR.
    destruct (w_alloc (s_win s)
              && negb (Z.eqb (w_wbits (s_win s))
                         (if Z.ltb wb 48 then Z.land wb 15 else wb))).
    + injection HR as HRz HRs.
      exact (reach_reset z
               (set_wbits (set_wrap (set_alloc s false)
                             (Z.shiftr wb 4 + 5))
                  (if Z.ltb wb 48 then Z.land wb 15 else wb)) z' s' a
               (f_equal2 (fun u v => (u, v)) HRz HRs)
               Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn Hbd Hamb Hlp Houtb).
    + injection HR as HRz HRs.
      exact (reach_reset z
               (set_wbits (set_wrap s (Z.shiftr wb 4 + 5))
                  (if Z.ltb wb 48 then Z.land wb 15 else wb)) z' s' a
               (f_equal2 (fun u v => (u, v)) HRz HRs)
               Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn Hbd Hamb Hlp Houtb).
Qed.

Corollary reach_init2 :
  forall z g wb z' s' a,
    inflateInit2 z g wb = Some (z', s') ->
    g_st a = s' ->
    (forall j, 0 <= g_inbuf a j < 256) ->
    0 <= g_avail_in a <= 4294967290 ->
    0 <= g_avail_out a <= 4294967295 ->
    (forall j, 0 <= w_win (s_win g) j < 256) ->
    0 <= u_length (s_cur g) ->
    lens_ok (b_lens (s_bld g)) ->
    0 <= b_have (s_bld g) ->
    0 <= b_nlen (s_bld g) ->
    0 <= b_ndist (s_bld g) ->
    amb_ok (t_codes (s_tab g)) ->
    LeafPosT (t_codes (s_tab g)) ->
    (forall j, 0 <= g_outbuf a j < 256) ->
    ReachSt (inf_st0 a).
Proof.
  intros z g wb z' s' a HR Hg Hbytes Hain Haout Hwinb Hlen Hlens Hbh Hbn
    Hbd Hamb Hlp Houtb.
  unfold inflateInit2 in HR.
  exact (reach_reset2 _ _ _ _ _ _ HR Hg Hbytes Hain Haout Hwinb Hlen
           Hlens Hbh Hbn Hbd Hamb Hlp Houtb).
Qed.


(* ==========================================================================
   Re-entry composition (G2+G3, pres lane 2026-08-20).  A call that LEAVES
   hands its post-writeback IState to the next call, which re-enters at
   [inf_st0] with fresh buffers; [reach_reenter] is the fused statement:
   ReachSt at the leave point + the writeback ([q_restore] + [uw] + the
   totals tail) + fresh-buffer premises re-establish ReachSt at the next
   entry.  The budget premise is EXACT ([rc_inbud] has zero headroom at
   the avail_in ceiling; up to 39 carried bits ride in [s_bits]).
   ========================================================================== *)

(** Every [ReachMode] clause reads [q] only through [q_st] ([match_side]
    included), so the block transports onto ANY state with equal
    hdr-mode/cur/tab/bld and a nonneg [wnext]. *)
Lemma reach_mode_st_any :
  forall q q',
    h_mode (s_hdr (q_st q')) = h_mode (s_hdr (q_st q)) ->
    s_cur (q_st q') = s_cur (q_st q) ->
    s_tab (q_st q') = s_tab (q_st q) ->
    s_bld (q_st q') = s_bld (q_st q) ->
    0 <= w_wnext (s_win (q_st q')) ->
    br_bits (q_br q') = br_bits (q_br q) ->
    h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q)) ->
    h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q)) ->
    ReachMode q ->
    (q_mode q' = M_HEAD -> q_out q' - o_left (q_ob q') = 0) ->
    ReachMode q'.
Proof.
  intros q q' Em Ec Et Eb Hwn Ebits Ew Ef HM Hw0'.
  assert (Eqm : q_mode q' = q_mode q) by (unfold q_mode; exact Em).
  destruct HM as [M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 M16 M17 M18 M19 M20 M21 M22 M23 M24].
  constructor; rewrite ?Eqm.
  - intros H. specialize (M1 H). unfold match_side in *. rewrite Ec.
    split; [tauto|]. split; [tauto|]. exact Hwn.
  - intros H. rewrite Ec. exact (M2 H).
  - intros H. rewrite Ec. exact (M3 H).
  - intros H. rewrite Ec. exact (M4 H).
  - rewrite Ec. exact M5.
  - intros H. apply (len_tbl_side_frame q); [exact Et | exact (M6 H)].
  - intros H. specialize (M7 H). unfold tbl_of in *.
    rewrite Et. exact M7.
  - intros H. rewrite Eb. exact (M8 H).
  - intros H. rewrite Eb. exact (M9 H).
  - rewrite Ec. exact M10.
  - intros H. rewrite Eb. exact (M11 H).
  - intros H. specialize (M12 H). unfold TblPDSide, tbl_of in *. rewrite Et. exact M12.
  - intros H. specialize (M13 H). unfold tbl_of in *. rewrite Et. exact M13.
  - intros H. rewrite Ebits. exact (M14 H).
  - rewrite Ew, Ef, Ebits. exact M15.
  - intros H. specialize (M16 H). unfold TblWidSide, tbl_of in *. rewrite Et. exact M16.
  - intros H. rewrite Ec. exact (M17 H).
  - intros H. specialize (M18 H). unfold tbl_of in *. rewrite Et. exact M18.
  - rewrite Ec. exact M19.
  - intros H; apply Hw0'; rewrite Eqm; exact H.
  - (* rm_tblCL0 (T2): s_tab framed *) intros H. rewrite Et. exact (M21 H).
  - (* rm_tblCL1 (T2): s_tab framed *) intros H. rewrite Et. exact (M22 H).
  - (* rm_tblCL2 (T2): s_tab framed *) intros H. rewrite Et. exact (M23 H).
  - (* rm_tblCL3 (T2): s_tab framed *) intros H. rewrite Et. exact (M24 H).
Qed.

(** cand13: the discharge of tie-x's [MATCH_OFF1_STMT] premise (TieMATCH.tie_MATCH; TieMATCHOneShot) —
    DINV carries [ReachSt q], and [rm_off1]'s MATCH conjunct is exactly the offset row (PLAN-rm_off1 §0). *)
Lemma match_off1_of_reach : forall q, ReachSt q -> q_mode q = M_MATCH -> 1 <= u_offset (s_cur (q_st q)).
Proof. intros q HR Hm. exact (proj2 (rm_off1 q (proj2 HR)) Hm). Qed.

(** The totals tail writes only z/out/in/ret and hdr(total,check): every
    IState field the invariant reads is framed. *)
Lemma leave_tail_st :
  forall c q wrote q2 rr,
    inf_leave_tail c q wrote = (q2, rr) ->
    s_cur (q_st q2) = s_cur (q_st q)
    /\ s_tab (q_st q2) = s_tab (q_st q)
    /\ s_bld (q_st q2) = s_bld (q_st q)
    /\ s_win (q_st q2) = s_win (q_st q)
    /\ h_mode (s_hdr (q_st q2)) = h_mode (s_hdr (q_st q))
    /\ s_bits (q_st q2) = s_bits (q_st q)
    /\ s_hold (q_st q2) = s_hold (q_st q).
Proof.
  intros c q wrote q2 rr H.
  unfold inf_leave_tail in H. cbv zeta in H.
  injection H as Hq2 _. subst q2.
  repeat split;
    destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
              && negb (Z.eqb wrote 0));
    reflexivity.
Qed.

(** The tail also frames the reader, the output record, and — when the
    answer is Z_OK — the pre-tail ret (the no-progress rule only degrades
    Z_OK to BUF_ERROR). *)
Lemma leave_tail_frames :
  forall c q wrote q2 rr,
    inf_leave_tail c q wrote = (q2, rr) ->
    q_br q2 = q_br q
    /\ q_ob q2 = q_ob q
    /\ (rr = Z_OK -> q_ret q = Z_OK).
Proof.
  intros c q wrote q2 rr H.
  unfold inf_leave_tail in H. cbv zeta in H.
  injection H as Hq2 Hrr. subst q2 rr.
  refine (conj _ (conj _ _)).
  - destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
              && negb (Z.eqb wrote 0)); reflexivity.
  - destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
              && negb (Z.eqb wrote 0)); reflexivity.
  - destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
              && negb (Z.eqb wrote 0)); cbv beta iota;
      match goal with
      | |- (if ?b then _ else _) = _ -> _ => destruct b
      end; intros Hok; [exfalso; cbv in Hok; lia | exact Hok
                       |exfalso; cbv in Hok; lia | exact Hok].
Qed.

(** And the whole [inf_leave]: reader/output framed; a Z_OK answer forces
    the pre-leave ret to have been Z_OK (the MEM path answers
    Z_MEM_ERROR). *)
Lemma leave_frames :
  forall c q1 q2 rr,
    inf_leave c q1 = (q2, rr) ->
    q_br q2 = q_br q1
    /\ q_ob q2 = q_ob q1
    /\ (rr = Z_OK -> q_ret q1 = Z_OK).
Proof.
  intros c q1 q2 rr HL.
  unfold inf_leave in HL. cbv zeta in HL.
  revert HL.
  destruct (negb (Z.eqb (w_wsize (s_win (q_st (q_restore q1)))) 0)
            || (negb (Z.eqb (q_out (q_restore q1))
                        (o_left (q_ob (q_restore q1))))
                && Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q1)))))
                     (m_val M_BAD)
                && (Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q1)))))
                      (m_val M_CHECK)
                    || negb (Z.eqb (n_flush c) Z_FINISH)))) eqn:Epath;
    intros HL; cbv beta iota in HL.
  - destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q1))
                (q_ob (q_restore q1))
                (q_out (q_restore q1) - o_left (q_ob (q_restore q1))))
      as [st'|] eqn:Euw.
    + destruct (leave_tail_frames _ _ _ _ _ HL) as (Fbr & Fob & Fret).
      split; [rewrite Fbr; reflexivity|].
      split; [rewrite Fob; reflexivity|].
      intros Hok. exact (Fret Hok).
    + injection HL as Hq2 Hrr. subst q2 rr.
      split; [reflexivity|]. split; [reflexivity|].
      intros Hok. exfalso. cbv in Hok. lia.
  - destruct (leave_tail_frames _ _ _ _ _ HL) as (Fbr & Fob & Fret).
    split; [rewrite Fbr; reflexivity|].
    split; [rewrite Fob; reflexivity|].
    intros Hok. exact (Fret Hok).
Qed.

(** [uw] preserves the boundary window invariant: bytes stay bytes, the
    bounds stay, and the whave saturation disjunction closes on itself
    (the contiguous branch is where [rc_wcoup] earns its keep). *)
Lemma uw_is :
  forall (alloc : bool) (fresh : zarr) (s : IState) (o : OB)
         (copy : Z) (s' : IState),
    (forall j, 0 <= w_win (s_win s) j < 256) ->
    0 <= w_wnext (s_win s) <= w_wsize (s_win s) ->
    0 <= w_whave (s_win s) <= w_wsize (s_win s) ->
    (w_whave (s_win s) = w_wsize (s_win s)
     \/ w_whave (s_win s) = w_wnext (s_win s)) ->
    (forall j, 0 <= fresh j < 256) ->
    (forall j, 0 <= o_buf o j < 256) ->
    0 <= copy < 4294967296 ->
    uw alloc fresh s o copy = Some s' ->
    (forall j, 0 <= w_win (s_win s') j < 256)
    /\ 0 <= w_wnext (s_win s') <= w_wsize (s_win s')
    /\ 0 <= w_whave (s_win s') <= w_wsize (s_win s')
    /\ (w_whave (s_win s') = w_wsize (s_win s')
        \/ w_whave (s_win s') = w_wnext (s_win s'))
    /\ s_cur s' = s_cur s /\ s_tab s' = s_tab s /\ s_bld s' = s_bld s
    /\ h_mode (s_hdr s') = h_mode (s_hdr s)
    /\ s_bits s' = s_bits s /\ s_hold s' = s_hold s.
Proof.
  intros alloc fresh s o copy s' Hwb Hwn Hwh Hcoup Hfb Hob Hcp H.
  unfold uw in H. cbv zeta in H.
  revert H.
  destruct (if w_alloc (s_win s) then Some (w_win (s_win s))
            else if alloc then Some fresh else None)
    as [win0|] eqn:Ew0; intros H; cbv beta iota in H;
    [|discriminate].
  assert (Hw0 : forall j, 0 <= win0 j < 256).
  { revert Ew0. destruct (w_alloc (s_win s)).
    - intros E; injection E as <-; exact Hwb.
    - destruct alloc; [|discriminate].
      intros E; injection E as <-; exact Hfb. }
  set (wszv := if Z.eqb (w_wsize (s_win s)) 0
               then Z.shiftl 1 (w_wbits (s_win s))
               else w_wsize (s_win s)) in *.
  set (wnxv := if Z.eqb (w_wsize (s_win s)) 0 then 0
               else w_wnext (s_win s)) in *.
  set (whvv := if Z.eqb (w_wsize (s_win s)) 0 then 0
               else w_whave (s_win s)) in *.
  assert (Hwsz : 0 <= wszv).
  { unfold wszv. destruct (Z.eqb (w_wsize (s_win s)) 0).
    - apply Z.shiftl_nonneg. lia.
    - lia. }
  assert (Hwnx : 0 <= wnxv <= wszv).
  { unfold wnxv, wszv. destruct (Z.eqb (w_wsize (s_win s)) 0).
    - split; [lia|]. apply Z.shiftl_nonneg. lia.
    - lia. }
  assert (Hwhv : 0 <= whvv <= wszv).
  { unfold whvv, wszv. destruct (Z.eqb (w_wsize (s_win s)) 0).
    - split; [lia|]. apply Z.shiftl_nonneg. lia.
    - lia. }
  assert (Hcoupv : whvv = wszv \/ whvv = wnxv).
  { unfold whvv, wszv, wnxv.
    destruct (Z.eqb (w_wsize (s_win s)) 0); [right; reflexivity|].
    exact Hcoup. }
  clearbody wszv wnxv whvv.
  revert H; destruct (Z.leb wszv copy) eqn:Ebig;
    intros H; cbv beta iota in H.
  - (* whole-window refill *)
    injection H as <-. cbn.
    split; [intros j; apply zcopy_bytes; assumption|].
    repeat split; try reflexivity; try lia.
  - apply Z.leb_gt in Ebig.
    revert H; destruct (Z.ltb copy (wszv - wnxv)) eqn:Edist;
      intros H; cbv beta iota in H.
    + (* dist = copy: cp1 = u32 0 = 0, contiguous *)
      apply Z.ltb_lt in Edist.
      assert (Ecp1 : u32 (copy - copy) = 0)
        by (rewrite Z.sub_diag; reflexivity).
      rewrite Ecp1 in H. cbn in H.
      injection H as <-. cbn.
      split; [intros j; apply zcopy_bytes; assumption|].
      destruct (Z.eqb (wnxv + copy) wszv) eqn:Ewrapz;
        [apply Z.eqb_eq in Ewrapz | apply Z.eqb_neq in Ewrapz];
        (destruct (Z.ltb whvv wszv) eqn:Ehlt;
         [apply Z.ltb_lt in Ehlt | apply Z.ltb_ge in Ehlt]);
        repeat split; try reflexivity; try lia.
    + (* dist = wszv - wnxv *)
      apply Z.ltb_ge in Edist.
      assert (Hu : u32 (copy - (wszv - wnxv)) = copy - (wszv - wnxv))
        by (apply u32_id; lia).
      rewrite Hu in H.
      revert H;
      destruct (negb (Z.eqb (copy - (wszv - wnxv)) 0)) eqn:Ecp1;
        intros H; cbv beta iota in H; injection H as <-; cbn.
      * (* wrap: second copy from the buffer start *)
        apply Bool.negb_true_iff, Z.eqb_neq in Ecp1.
        split;
          [ intros j; apply zcopy_bytes;
            [intros j'; apply zcopy_bytes; assumption | assumption] |].
        repeat split; try reflexivity; try lia.
      * (* contiguous, exactly filling to the boundary *)
        apply Bool.negb_false_iff, Z.eqb_eq in Ecp1.
        split; [intros j; apply zcopy_bytes; assumption|].
        destruct (Z.eqb (wnxv + (wszv - wnxv)) wszv) eqn:Ewrapz;
          [apply Z.eqb_eq in Ewrapz | apply Z.eqb_neq in Ewrapz];
          (destruct (Z.ltb whvv wszv) eqn:Ehlt;
           [apply Z.ltb_lt in Ehlt | apply Z.ltb_ge in Ehlt]);
          repeat split; try reflexivity; try lia.
Qed.

(** [inf_st0]'s TYPE->TYPEDO remap changes no field the invariant reads
    except (possibly) the mode, and both TYPE and TYPEDO are inactive. *)
Lemma inf_st0_frames :
  forall a,
    s_cur (q_st (inf_st0 a)) = s_cur (g_st a)
    /\ s_tab (q_st (inf_st0 a)) = s_tab (g_st a)
    /\ s_bld (q_st (inf_st0 a)) = s_bld (g_st a)
    /\ s_win (q_st (inf_st0 a)) = s_win (g_st a)
    /\ s_hold (q_st (inf_st0 a)) = s_hold (g_st a)
    /\ s_bits (q_st (inf_st0 a)) = s_bits (g_st a).
Proof.
  intros a. unfold inf_st0.
  destruct (h_mode (s_hdr (g_st a))); repeat split; reflexivity.
Qed.

(** the sharper form: the TYPEDO rewrite happens exactly at a TYPE entry *)
Lemma inf_st0_mode2 :
  forall a,
    h_mode (s_hdr (q_st (inf_st0 a))) = h_mode (s_hdr (g_st a))
    \/ (h_mode (s_hdr (g_st a)) = M_TYPE /\ h_mode (s_hdr (q_st (inf_st0 a))) = M_TYPEDO).
Proof.
  intros a. unfold inf_st0.
  destruct (h_mode (s_hdr (g_st a))) eqn:E; try (left; exact E).
  right. split; reflexivity.
Qed.

Lemma inf_st0_mode :
  forall a,
    h_mode (s_hdr (q_st (inf_st0 a))) = h_mode (s_hdr (g_st a))
    \/ h_mode (s_hdr (q_st (inf_st0 a))) = M_TYPEDO.
Proof.
  intros a. unfold inf_st0.
  destruct (h_mode (s_hdr (g_st a))) eqn:E;
    try (left; cbn; rewrite E; reflexivity).
  right; reflexivity.
Qed.

(** The boundary pack: everything [reach_reenter] needs to know about
    the post-writeback state, exported standalone so the ASK1 composite
    can read the carried-bits bound. *)
Lemma leave_boundary :
  forall c q' q2 rr,
    ReachSt q' ->
    (forall j, 0 <= n_wfresh c j < 256) ->
    inf_leave c q' = (q2, rr) ->
    (forall j, 0 <= w_win (s_win (q_st q2)) j < 256)
    /\ 0 <= w_wnext (s_win (q_st q2)) <= w_wsize (s_win (q_st q2))
    /\ 0 <= w_whave (s_win (q_st q2)) <= w_wsize (s_win (q_st q2))
    /\ (w_whave (s_win (q_st q2)) = w_wsize (s_win (q_st q2))
        \/ w_whave (s_win (q_st q2)) = w_wnext (s_win (q_st q2)))
    /\ s_cur (q_st q2) = s_cur (q_st q')
    /\ s_tab (q_st q2) = s_tab (q_st q')
    /\ s_bld (q_st q2) = s_bld (q_st q')
    /\ (h_mode (s_hdr (q_st q2)) = h_mode (s_hdr (q_st q'))
        \/ h_mode (s_hdr (q_st q2)) = M_MEM)
    /\ 0 <= s_bits (q_st q2) <= 39
    /\ 0 <= s_hold (q_st q2).
Proof.
  intros c q' q2 rr HR Hfw HL.
  pose proof HR as (HC & HM).
  core_facts q' HC.
  { unfold inf_leave in HL. cbv zeta in HL.
    assert (Ewr : 0 <= q_out (q_restore q') - o_left (q_ob (q_restore q'))
                    < 4294967296)
      by (cbn [q_restore qset_st q_out q_ob]; lia).
    revert HL.
    destruct (negb (Z.eqb (w_wsize (s_win (q_st (q_restore q')))) 0)
              || (negb (Z.eqb (q_out (q_restore q'))
                          (o_left (q_ob (q_restore q'))))
                  && Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                       (m_val M_BAD)
                  && (Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                        (m_val M_CHECK)
                      || negb (Z.eqb (n_flush c) Z_FINISH)))) eqn:Epath;
      intros HL; cbv beta iota in HL.
    - (* window path *)
      destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                  (q_ob (q_restore q'))
                  (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
        as [st'|] eqn:Euw.
      + (* writeback succeeded; the tail runs on the new state *)
        destruct (uw_is (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                    (q_ob (q_restore q'))
                    (q_out (q_restore q') - o_left (q_ob (q_restore q')))
                    st'
                    (rc_win q' HC) Fwn Fwh Fwcoup Hfw
                    (fun j => Fob j) Ewr Euw)
          as (Uwb & Uwn & Uwh & Ucp & Ucur & Utab & Ubld & Umode
              & Ubits & Uhold).
        destruct (leave_tail_st _ _ _ _ _ HL)
          as (Tcur & Ttab & Tbld & Twin & Tmode & Tbits & Thold).
        split. { intros j. rewrite Twin. exact (Uwb j). }
        split. { rewrite Twin. exact Uwn. }
        split. { rewrite Twin. exact Uwh. }
        split. { rewrite Twin. exact Ucp. }
        split. { rewrite Tcur. exact Ucur. }
        split. { rewrite Ttab. exact Utab. }
        split. { rewrite Tbld. exact Ubld. }
        split. { left. rewrite Tmode. exact Umode. }
        split. { rewrite Tbits. cbn [qset_st q_st]. rewrite Ubits.
                 cbn [q_restore qset_st q_st set_bits set_hold s_bits].
                 lia. }
        { rewrite Thold. cbn [qset_st q_st]. rewrite Uhold.
          cbn [q_restore qset_st q_st set_bits set_hold s_hold].
          lia. }
      + (* out of memory: MEM leave, state otherwise untouched *)
        injection HL as Hq2 _; subst q2.
        split. { intros j. exact (rc_win q' HC j). }
        split. { exact Fwn. }
        split. { exact Fwh. }
        split. { exact Fwcoup. }
        split. { reflexivity. }
        split. { reflexivity. }
        split. { reflexivity. }
        split. { right. reflexivity. }
        split. { cbn [qset_ret qmode qset_st q_st q_restore set_mode
                      set_bits set_hold s_bits]. lia. }
        { cbn [qset_ret qmode qset_st q_st q_restore set_mode
               set_bits set_hold s_hold]. lia. }
    - (* no writeback: the tail runs on the restored state *)
      destruct (leave_tail_st _ _ _ _ _ HL)
        as (Tcur & Ttab & Tbld & Twin & Tmode & Tbits & Thold).
      split. { intros j. rewrite Twin. exact (rc_win q' HC j). }
      split. { rewrite Twin. exact Fwn. }
      split. { rewrite Twin. exact Fwh. }
      split. { rewrite Twin. exact Fwcoup. }
      split. { rewrite Tcur. reflexivity. }
      split. { rewrite Ttab. reflexivity. }
      split. { rewrite Tbld. reflexivity. }
      split. { left. rewrite Tmode. reflexivity. }
      split. { rewrite Tbits.
               cbn [q_restore qset_st q_st set_bits set_hold s_bits].
               lia. }
      { rewrite Thold.
        cbn [q_restore qset_st q_st set_bits set_hold s_hold].
        lia. } }
Qed.

(** The leave carries [rc_holdclean] into the IState it hands the next
    call: RESTORE copies the reader's hold/bits into [s_hold]/[s_bits]
    (Inflate.v:836), and neither the window writeback nor the totals tail
    touches them ([uw_is], [leave_tail_st]).  Standalone, so the
    [leave_boundary] pack keeps its arity (an earlier development run). *)
Lemma leave_boundary_hc :
  forall c q' q2 rr,
    ReachSt q' ->
    (forall j, 0 <= n_wfresh c j < 256) ->
    inf_leave c q' = (q2, rr) ->
    s_hold (q_st q2) < 2 ^ s_bits (q_st q2).
Proof.
  intros c q' q2 rr HR Hfw HL.
  pose proof HR as (HC & HM).
  core_facts q' HC.
  pose proof (rc_holdclean q' HC) as Fhc.
  { unfold inf_leave in HL. cbv zeta in HL.
    assert (Ewr : 0 <= q_out (q_restore q') - o_left (q_ob (q_restore q'))
                    < 4294967296)
      by (cbn [q_restore qset_st q_out q_ob]; lia).
    revert HL.
    destruct (negb (Z.eqb (w_wsize (s_win (q_st (q_restore q')))) 0)
              || (negb (Z.eqb (q_out (q_restore q'))
                          (o_left (q_ob (q_restore q'))))
                  && Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                       (m_val M_BAD)
                  && (Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                        (m_val M_CHECK)
                      || negb (Z.eqb (n_flush c) Z_FINISH)))) eqn:Epath;
      intros HL; cbv beta iota in HL.
    - (* window path *)
      destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                  (q_ob (q_restore q'))
                  (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
        as [st'|] eqn:Euw.
      + destruct (uw_is (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                    (q_ob (q_restore q'))
                    (q_out (q_restore q') - o_left (q_ob (q_restore q')))
                    st'
                    (rc_win q' HC) Fwn Fwh Fwcoup Hfw
                    (fun j => Fob j) Ewr Euw)
          as (_ & _ & _ & _ & _ & _ & _ & _ & Ubits & Uhold).
        destruct (leave_tail_st _ _ _ _ _ HL)
          as (_ & _ & _ & _ & _ & Tbits & Thold).
        rewrite Thold, Tbits. cbn [qset_st q_st]. rewrite Uhold, Ubits.
        cbn [q_restore qset_st q_st set_bits set_hold s_hold s_bits].
        exact Fhc.
      + injection HL as Hq2 _; subst q2.
        cbn [qset_ret qmode qset_st q_st q_restore set_mode
             set_bits set_hold s_hold s_bits].
        exact Fhc.
    - (* no writeback *)
      destruct (leave_tail_st _ _ _ _ _ HL)
        as (_ & _ & _ & _ & _ & Tbits & Thold).
      rewrite Thold, Tbits.
      cbn [q_restore qset_st q_st set_bits set_hold s_hold s_bits].
      exact Fhc. }
Qed.

(** ** [rc_walloc0] across the leave (MEASURE-walloc0.md)

    [uw] is the only writer of [w_alloc] inside a call boundary and its every [Some] branch sets
    it to [true], so the row is vacuous after a writeback; the no-writeback paths keep [s_win]. *)
Lemma uw_alloc_true :
  forall alloc fresh s o copy s',
    uw alloc fresh s o copy = Some s' -> w_alloc (s_win s') = true.
Proof.
  intros alloc fresh s o copy s' H. unfold uw in H. cbv zeta in H.
  destruct (if w_alloc (s_win s) then Some (w_win (s_win s))
            else if alloc then Some fresh else None) as [win0|]; [|discriminate H].
  destruct (Z.leb (if Z.eqb (w_wsize (s_win s)) 0 then Z.shiftl 1 (w_wbits (s_win s))
                   else w_wsize (s_win s)) copy); [injection H as <-; reflexivity|].
  destruct (negb (Z.eqb (u32 (copy - (if Z.ltb copy ((if Z.eqb (w_wsize (s_win s)) 0 then Z.shiftl 1 (w_wbits (s_win s)) else w_wsize (s_win s))
                                                      - (if Z.eqb (w_wsize (s_win s)) 0 then 0 else w_wnext (s_win s)))
                                         then copy
                                         else (if Z.eqb (w_wsize (s_win s)) 0 then Z.shiftl 1 (w_wbits (s_win s)) else w_wsize (s_win s))
                                              - (if Z.eqb (w_wsize (s_win s)) 0 then 0 else w_wnext (s_win s))))) 0));
    injection H as <-; reflexivity.
Qed.

Lemma leave_boundary_wa :
  forall c q' q2 rr,
    ReachSt q' ->
    (forall j, 0 <= n_wfresh c j < 256) ->
    inf_leave c q' = (q2, rr) ->
    w_alloc (s_win (q_st q2)) = false -> w_wsize (s_win (q_st q2)) = 0.
Proof.
  intros c q' q2 rr HR Hfw HL.
  pose proof HR as (HC & HM).
  pose proof (rc_walloc0 q' HC) as Fwa0.
  unfold inf_leave in HL. cbv zeta in HL.
  revert HL.
  destruct (negb (Z.eqb (w_wsize (s_win (q_st (q_restore q')))) 0)
            || (negb (Z.eqb (q_out (q_restore q'))
                        (o_left (q_ob (q_restore q'))))
                && Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                     (m_val M_BAD)
                && (Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                      (m_val M_CHECK)
                    || negb (Z.eqb (n_flush c) Z_FINISH)))) eqn:Epath;
    intros HL; cbv beta iota in HL.
  - destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                (q_ob (q_restore q'))
                (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
      as [st'|] eqn:Euw.
    + destruct (leave_tail_st _ _ _ _ _ HL) as (_ & _ & _ & Twin & _ & _ & _).
      rewrite Twin. cbn [qset_st q_st].
      rewrite (uw_alloc_true _ _ _ _ _ _ Euw). discriminate.
    + injection HL as Hq2 _; subst q2.
      cbn [qset_ret qmode qset_st q_st q_restore set_mode set_bits set_hold s_win].
      exact Fwa0.
  - destruct (leave_tail_st _ _ _ _ _ HL) as (_ & _ & _ & Twin & _ & _ & _).
    rewrite Twin. cbn [q_restore qset_st q_st set_bits set_hold s_win].
    exact Fwa0.
Qed.

(** (D'') the leave's RESTORE writes [s_bits := br_bits]; the window writeback and the totals tail keep it. *)
Lemma leave_bits_eq :
  forall c q' q2 rr,
    ReachSt q' ->
    (forall j, 0 <= n_wfresh c j < 256) ->
    inf_leave c q' = (q2, rr) ->
    s_bits (q_st q2) = br_bits (q_br q').
Proof.
  intros c q' q2 rr HR Hfw HL.
  pose proof HR as (HC & HM).
  core_facts q' HC.
  { unfold inf_leave in HL. cbv zeta in HL.
    assert (Ewr : 0 <= q_out (q_restore q') - o_left (q_ob (q_restore q'))
                    < 4294967296)
      by (cbn [q_restore qset_st q_out q_ob]; lia).
    revert HL.
    destruct (negb (Z.eqb (w_wsize (s_win (q_st (q_restore q')))) 0)
              || (negb (Z.eqb (q_out (q_restore q'))
                          (o_left (q_ob (q_restore q'))))
                  && Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                       (m_val M_BAD)
                  && (Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                        (m_val M_CHECK)
                      || negb (Z.eqb (n_flush c) Z_FINISH)))) eqn:Epath;
      intros HL; cbv beta iota in HL.
    - (* window path *)
      destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                  (q_ob (q_restore q'))
                  (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
        as [st'|] eqn:Euw.
      + destruct (uw_is (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                    (q_ob (q_restore q'))
                    (q_out (q_restore q') - o_left (q_ob (q_restore q')))
                    st'
                    (rc_win q' HC) Fwn Fwh Fwcoup Hfw
                    (fun j => Fob j) Ewr Euw)
          as (_ & _ & _ & _ & _ & _ & _ & _ & Ubits & Uhold).
        destruct (leave_tail_st _ _ _ _ _ HL)
          as (_ & _ & _ & _ & _ & Tbits & Thold).
        rewrite Tbits. cbn [qset_st q_st]. rewrite Ubits.
        cbn [q_restore qset_st q_st set_bits set_hold s_hold s_bits].
        reflexivity.
      + injection HL as Hq2 _; subst q2.
        cbn [qset_ret qmode qset_st q_st q_restore set_mode
             set_bits set_hold s_hold s_bits].
        reflexivity.
    - (* no writeback *)
      destruct (leave_tail_st _ _ _ _ _ HL)
        as (_ & _ & _ & _ & _ & Tbits & Thold).
      rewrite Tbits.
      cbn [q_restore qset_st q_st set_bits set_hold s_hold s_bits].
      reflexivity. }
Qed.

(** [uw] rewrites the window only: the header record is untouched. *)
Lemma uw_hdr : forall alloc fresh s o copy s', uw alloc fresh s o copy = Some s' -> s_hdr s' = s_hdr s.
Proof.
  intros alloc fresh s o copy s' H. unfold uw in H. cbv zeta in H.
  destruct (if w_alloc (s_win s) then Some (w_win (s_win s)) else if alloc then Some fresh else None) as [win0|];
    [| discriminate].
  repeat match type of H with
  | context [if ?x then _ else _] => destruct x; cbv beta iota in H
  end; injection H as <-; reflexivity.
Qed.
(** the totals tail writes hdr(total, check) only *)
Lemma leave_tail_hdr :
  forall c q wrote q2 rr,
    inf_leave_tail c q wrote = (q2, rr) ->
    h_wrap (s_hdr (q_st q2)) = h_wrap (s_hdr (q_st q)) /\ h_flags (s_hdr (q_st q2)) = h_flags (s_hdr (q_st q)).
Proof.
  intros c q wrote q2 rr H.
  unfold inf_leave_tail in H. cbv zeta in H.
  injection H as Hq2 _. subst q2.
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0) && negb (Z.eqb wrote 0)); split; reflexivity.
Qed.
(** (D'') [rm_bits0]'s guards read [h_wrap] / [h_flags]: the leave/writeback keeps both. *)
Lemma leave_hdr_frames :
  forall c q' q2 rr,
    inf_leave c q' = (q2, rr) ->
    h_wrap (s_hdr (q_st q2)) = h_wrap (s_hdr (q_st q')) /\ h_flags (s_hdr (q_st q2)) = h_flags (s_hdr (q_st q')).
Proof.
  intros c q' q2 rr HL.
  unfold inf_leave in HL. cbv zeta in HL. revert HL.
  destruct (negb (Z.eqb (w_wsize (s_win (q_st (q_restore q')))) 0)
            || (negb (Z.eqb (q_out (q_restore q'))
                        (o_left (q_ob (q_restore q'))))
                && Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                     (m_val M_BAD)
                && (Z.ltb (m_val (h_mode (s_hdr (q_st (q_restore q')))))
                      (m_val M_CHECK)
                    || negb (Z.eqb (n_flush c) Z_FINISH)))) eqn:Epath;
    intros HL; cbv beta iota in HL.
  - destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                (q_ob (q_restore q'))
                (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
      as [st'|] eqn:Euw.
    + pose proof (uw_hdr _ _ _ _ _ _ Euw) as Uh.
      destruct (leave_tail_hdr _ _ _ _ _ HL) as (Tw & Tf).
      rewrite Tw, Tf. cbn [qset_st q_st]. rewrite Uh.
      cbn [q_restore qset_st q_st set_bits set_hold s_hdr]. split; reflexivity.
    + injection HL as Hq2 _; subst q2.
      cbn [qset_ret qmode qset_st q_st q_restore set_mode set_bits set_hold s_hdr h_wrap h_flags]. split; reflexivity.
  - destruct (leave_tail_hdr _ _ _ _ _ HL) as (Tw & Tf).
    rewrite Tw, Tf. cbn [q_restore qset_st q_st set_bits set_hold s_hdr]. split; reflexivity.
Qed.
Lemma inf_st0_hdr : forall a,
  h_wrap (s_hdr (q_st (inf_st0 a))) = h_wrap (s_hdr (g_st a)) /\ h_flags (s_hdr (q_st (inf_st0 a))) = h_flags (s_hdr (g_st a)).
Proof. intros a. unfold inf_st0. destruct (h_mode (s_hdr (g_st a))); split; reflexivity. Qed.


(** ** G2+G3 fused: leave, write back, re-enter. *)
Theorem reach_reenter :
  forall c q' q2 rr a,
    ReachSt q' ->
    (forall j, 0 <= n_wfresh c j < 256) ->
    inf_leave c q' = (q2, rr) ->
    g_st a = q_st q2 ->
    (forall j, 0 <= g_inbuf a j < 256) ->
    (forall j, 0 <= g_outbuf a j < 256) ->
    0 <= g_avail_in a ->
    0 <= g_avail_out a <= 4294967295 ->
    8 * g_avail_in a + s_bits (q_st q2) <= 34359738320 ->
    ReachSt (inf_st0 a).
Proof.
  intros c q' q2 rr a HR Hfw HL Hg Hib Hob0 Hain Haout Hbud.
  pose proof HR as (HC & HM).
  core_facts q' HC.
  pose proof (leave_boundary c q' q2 rr HR Hfw HL) as HB.
  destruct HB as (Bwb & Bwn & Bwh & Bcp & Bcur & Btab & Bbld & Bmode
                  & Bbits & Bhold).
  destruct (inf_st0_frames a) as (Scur & Stab & Sbld & Swin & Shold & Sbits).
  rewrite Hg in Scur, Stab, Sbld, Swin, Shold, Sbits.
  (* the entry record's own projections *)
  assert (Ehave : br_have (q_br (inf_st0 a)) = g_avail_in a)
    by reflexivity.
  assert (Ebits : br_bits (q_br (inf_st0 a)) = s_bits (q_st (inf_st0 a)))
    by reflexivity.
  assert (Ein : forall j, br_in (q_br (inf_st0 a)) j = g_inbuf a j)
    by (intros j; reflexivity).
  assert (Ehold2 : br_hold (q_br (inf_st0 a)) = s_hold (q_st (inf_st0 a)))
    by reflexivity.
  assert (Eleft : o_left (q_ob (inf_st0 a)) = g_avail_out a)
    by reflexivity.
  assert (Eobuf : forall j, o_buf (q_ob (inf_st0 a)) j = g_outbuf a j)
    by (intros j; reflexivity).
  assert (Eqout : q_out (inf_st0 a) = g_avail_out a)
    by reflexivity.
  assert (Eqin : q_in (inf_st0 a) = g_avail_in a)
    by reflexivity.
  pose proof (leave_boundary_hc c q' q2 rr HR Hfw HL) as Bhc.
  split.
  - constructor.
    + unfold q_pos. rewrite Ehave, Ebits, Eleft, Sbits. lia.
    + rewrite Ebits, Sbits. lia.
    + intros j. rewrite Ein. exact (Hib j).
    + rewrite Ehold2, Shold. lia.
    + intros j. rewrite Swin. exact (Bwb j).
    + rewrite Swin. exact Bwn.
    + rewrite Swin. exact Bwh.
    + rewrite Stab, Btab. exact Fsane.
    + rewrite Scur, Bcur. exact Flen0.
    + rewrite Ehave, Ebits, Sbits. lia.
    + rewrite Eleft. lia.
    + rewrite Sbld, Bbld. exact Flens.
    + rewrite Sbld, Bbld. exact Fbh.
    + rewrite Sbld, Bbld. exact Fbn.
    + rewrite Sbld, Bbld. exact Fbd.
    + rewrite Stab, Btab. exact Famb.
    + intros j. rewrite Eobuf. exact (Hob0 j).
    + rewrite Swin. exact Bcp.
    + rewrite Eleft, Eqout. lia.
    + rewrite Eqout. lia.
    + rewrite Ebits, Sbits, Ehave, Eqin. lia.
    + rewrite Ehold2, Shold, Ebits, Sbits. exact Bhc.
    + rewrite Stab, Btab. exact Flp.
    + rewrite Swin. exact (leave_boundary_wa c q' q2 rr HR Hfw HL).
  - destruct (inf_st0_mode2 a) as [Em0 | (Eg & Em0)].
    + rewrite Hg in Em0.
      destruct Bmode as [Bm | Bm].
      * apply (reach_mode_st_any q').
        { rewrite Em0. exact Bm. }
        { rewrite Scur. exact Bcur. }
        { rewrite Stab. exact Btab. }
        { rewrite Sbld. exact Bbld. }
        { rewrite Swin. lia. }
        { rewrite Ebits, Sbits. exact (leave_bits_eq c q' q2 rr HR Hfw HL). }
        { rewrite (proj1 (inf_st0_hdr a)), Hg. exact (proj1 (leave_hdr_frames c q' q2 rr HL)). }
        { rewrite (proj2 (inf_st0_hdr a)), Hg. exact (proj2 (leave_hdr_frames c q' q2 rr HL)). }
        exact HM.
        intros _; rewrite Eqout, Eleft; lia.
      * apply reach_mode_inactive. unfold q_mode.
        rewrite Em0, Bm. reflexivity.
    + (* a TYPE leave re-enters at TYPEDO: rm_bits14 transfers through the RESTORE/LOAD bit count *)
      rewrite Hg in Eg.
      destruct Bmode as [Bm | Bm]; [| rewrite Bm in Eg; discriminate].
      apply reach_mode_hdr.
      * right; left. unfold q_mode. exact Em0.
      * rewrite Ebits, Sbits, (leave_bits_eq c q' q2 rr HR Hfw HL).
        apply (rm_bits14 q' HM). left. unfold q_mode. rewrite <- Bm. exact Eg.
Qed.

(* ==========================================================================
   Consumer exports (q7-decode's GtDecPump Variable shapes, verbatim:
   Hret = ASK3, Hshape = ASK2, and the unfolded ASK1 composite — q7 wraps
   it into EntryOk on their side).  [DynTblOk] is PresKnot's discharged
   Section variable, explicit here.
   ========================================================================== *)

Theorem step_ret_not_ok :
  forall (Hdyn : DynTblOk) c q0 q1 rr,
    ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK.
Proof.
  intros Hdyn c q0 q1 rr HR Hstep.
  pose proof (step_pres Hdyn c q0 HR) as HP.
  rewrite Hstep in HP. exact HP.
Qed.

Theorem leave_shape_ask2 :
  forall (Hdyn : DynTblOk) c q0 q1,
    ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
    0 <= br_have (q_br (fst (inf_leave c q1)))
    /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
        br_have (q_br (fst (inf_leave c q1))) = 0
        \/ o_left (q_ob (fst (inf_leave c q1))) = 0).
Proof.
  intros Hdyn c q0 q1 HR Hstep.
  pose proof (step_pres Hdyn c q0 HR) as HP.
  rewrite Hstep in HP.
  destruct HP as (HR1 & HP1).
  pose proof HR1 as (HC1 & _).
  destruct (inf_leave c q1) as [q2 rr] eqn:HL. cbn [fst snd].
  destruct (leave_frames _ _ _ _ HL) as (Fbr & Fob & Fret).
  split.
  - rewrite Fbr. exact (proj1 (rc_pos q1 HC1)).
  - intros Hf Hok.
    destruct (HP1 Hf (Fret Hok)) as [D|D].
    + left. rewrite Fbr. exact D.
    + right. rewrite Fob. exact D.
Qed.

Theorem reach_reenter_ask1 :
  forall (Hdyn : DynTblOk) c q0 q1,
    ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
    (forall j, 0 <= n_wfresh c j < 256) ->
    forall inb aout flush,
      (forall j, 0 <= zlist inb j < 256) ->
      0 <= Chunk.zlen inb <= 4294967285 ->
      0 <= aout <= 4294967295 ->
      ReachSt (inf_st0
        {| g_st := q_st (fst (inf_leave c q1)); g_state_null := false;
           g_z := q_z (fst (inf_leave c q1)); g_inbuf := zlist inb;
           g_next_in := 0; g_avail_in := Chunk.zlen inb; g_in_null := false;
           g_outbuf := zzero; g_next_out := 0; g_avail_out := aout;
           g_out_null := false; g_flush := flush; g_walloc := true;
           g_wfresh := zzero |}).
Proof.
  intros Hdyn c q0 q1 HR Hstep Hfw inb aout flush Hib Hlen Haout.
  pose proof (step_pres Hdyn c q0 HR) as HP.
  rewrite Hstep in HP.
  destruct HP as (HR1 & _).
  destruct (inf_leave c q1) as [q2 rr] eqn:HL. cbn [fst].
  destruct (leave_boundary c q1 q2 rr HR1 Hfw HL)
    as (_ & _ & _ & _ & _ & _ & _ & _ & Bbits & _).
  apply (reach_reenter c q1 q2 rr);
    [ exact HR1
    | exact Hfw
    | exact HL
    | reflexivity
    | exact Hib
    | intros j; cbn [g_outbuf]; cbv [zzero zconst]; lia
    | cbn [g_avail_in]; lia
    | cbn [g_avail_out]; exact Haout
    | cbn [g_avail_in]; lia ].
Qed.
