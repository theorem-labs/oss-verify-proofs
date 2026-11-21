(* GtDecCost.v: one-bullet cand13 re-key by q4 fork , 2026-09-05, of the W8 member GtDecCost.v (base md5 ): sites :1982 (the reach_mode_scc bracket gains one hole) and :1992 (the closing `+` bullet: rm_dsub at LEN_ transported to the LEN re-dispatch, s_tab framed) -- cand13's StepPres.reach_mode_scc gained the sixth premise DistSubSide q (rm_dsub); proof-only, statements byte-identical to the base; author (by header, owner consent of record) q7-decode. *)
(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtDecCost — the per-call
      cost/conservation sweep discharging [GtDecPump.Hcall]
      (q7-decode lane, zlib-rt, 2026-08-20)

    Per-arm facts along [inf_step], composed along [inf_loop] and
    through [inf_leave], concluding the exact [Hcall] shape:

    - M1 (budget conservation): [Wq := 8*br_have + br_bits] never
      increases.  Fetch/decode nodes: [inf_nb_bud]/[inf_fetch_bud]/
      [inf_fetch2_bud]/[inf_decode_bud]; the fast node:
      [StepPres.if_model_pres].
    - M2 (258-rate output cost): [Kq := 258*Wq + cpend + o_put] never
      increases — one output byte costs a budget unit at rate <= 258
      ([cpend] counts pending output ONLY where it is bits-backed:
      the four match modes plus the 1-byte M_LIT flag).
    - M3: [o_put + o_left] is preserved and [o_put] monotone.
    - Signs, the [cpend <= 258] cap, and the carried [CostAux]
      (selected-length-entry facts, established at LEN's decode from
      the relativised [lcode_len_bounded]).

    The bundle [CB] is stated between states and is transitive, so the
    fallthrough call chains (LEN -> LENEXT -> DIST -> DISTEXT -> MATCH,
    TABLE -> LENLENS -> CODELENS -> LEN_, gzip HEAD -> ... -> TYPE)
    compose callee-first exactly as [StepPres]'s pres_* lemmas do. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtInfTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecPump.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Quantities and the bundle.
   ========================================================================== *)

Definition Wq (q : InfSt) : Z := 8 * br_have (q_br q) + br_bits (q_br q).
Definition Kq (q : InfSt) : Z :=
  258 * Wq q + cpend (q_st q) + o_put (q_ob q).

(** The cost bundle between an entry state and a successor. *)
Definition CB (q q' : InfSt) : Prop :=
  Wq q' <= Wq q
  /\ Kq q' <= Kq q
  /\ o_put (q_ob q') + o_left (q_ob q') = o_put (q_ob q) + o_left (q_ob q)
  /\ o_put (q_ob q) <= o_put (q_ob q')
  /\ 0 <= br_have (q_br q')
  /\ 0 <= br_bits (q_br q')
  /\ 0 <= u_length (s_cur (q_st q'))
  /\ CostAux (q_st q').

Ltac cb8 :=
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).

Lemma CB_trans : forall q q1 q2, CB q q1 -> CB q1 q2 -> CB q q2.
Proof.
  intros q q1 q2 (A1&A2&A3&A4&A5&A6&A7&A8) (B1&B2&B3&B4&B5&B6&B7&B8).
  cb8; try lia; try assumption.
Qed.

Definition CostStep (q : InfSt) (r : InfStep) : Prop :=
  match r with
  | InfCont q' | InfLeave q' => CB q q'
  | InfRet q' _ => CB q q'
  | _ => True
  end.

(** [CB] out of an arm result transports through a mode change of the
    RESULT (the [qmode _ m] wrappers), provided the new mode's [cpend]
    and [CostAux] obligations are re-established.  Used implicitly: the
    per-arm lemmas conclude at concrete result terms. *)

(* ==========================================================================
   2.  Entry-side facts every arm proof draws on.
   ========================================================================== *)

(** What an arm needs of its OWN entry state (derived from ReachSt +
    CostAux at the dispatch; passed explicitly so the per-arm lemmas
    stay Section-free). *)
Record CEntry (q : InfSt) : Prop := mkCEntry {
  ce_have : 0 <= br_have (q_br q);
  ce_bits : 0 <= br_bits (q_br q);
  ce_hold : 0 <= br_hold (q_br q);
  ce_bytes : forall j, 0 <= br_in (q_br q) j;
  ce_left : 0 <= o_left (q_ob q);
  ce_len0 : 0 <= u_length (s_cur (q_st q));
  ce_aux  : CostAux (q_st q)
}.

Lemma cpend_le_258 :
  forall s, CostAux s -> 0 <= u_length (s_cur s) -> 0 <= cpend s <= 258.
Proof.
  intros s [HA HB] Hl. unfold cpend.
  destruct (h_mode (s_hdr s)) eqn:Hm; try lia.
  - (* M_LENEXT *)
    destruct (HA eq_refl) as [He Hle].
    assert (1 <= Z.shiftl 1 (u_extra (s_cur s))).
    { rewrite Z.shiftl_1_l.
      apply (Z.pow_le_mono_r 2 0 (u_extra (s_cur s))); lia. }
    lia.
  - specialize (HB (or_introl eq_refl)). lia.
  - specialize (HB (or_intror (or_introl eq_refl))). lia.
  - specialize (HB (or_intror (or_intror eq_refl))). lia.
Qed.

(* ==========================================================================
   3.  The trivial exits.
   ========================================================================== *)

Lemma cost_MEM : forall q, CEntry q -> CostStep q (inf_MEM q).
Proof.
  intros q [H1 H2 H8 H9 H5 H3 H4]. unfold inf_MEM. cbn [CostStep].
  unfold CB. cb8; try assumption; try lia.
Qed.

Lemma cost_SYNC : forall q, CEntry q -> CostStep q (inf_SYNC q).
Proof.
  intros q [H1 H2 H8 H9 H5 H3 H4]. unfold inf_SYNC. cbn [CostStep].
  unfold CB. cb8; try assumption; try lia.
Qed.

Lemma cost_BAD : forall q, CEntry q -> CostStep q (inf_BAD q).
Proof.
  intros q [H1 H2 H8 H9 H5 H3 H4]. unfold inf_BAD. cbn [CostStep].
  unfold CB, Kq, Wq. bsimp.
  cb8; try assumption; try lia.
Qed.

Lemma cost_DONE : forall q, CEntry q -> CostStep q (inf_DONE q).
Proof.
  intros q [H1 H2 H8 H9 H5 H3 H4]. unfold inf_DONE. cbn [CostStep].
  unfold CB, Kq, Wq. bsimp.
  cb8; try assumption; try lia.
Qed.

(* ==========================================================================
   4.  Node budget facts, BOTH constructors (the landed *_bud lemmas
       cover only the Ok side; the Leave side preserves the budget the
       same way — pulls are budget-neutral).
   ========================================================================== *)

(** Node carry: budget equality, input-array identity, and the three
    sign chains a dispatcher must rebuild after the node. *)
Definition brok (b0 b1 : BR) : Prop :=
  8 * br_have b1 + br_bits b1 = 8 * br_have b0 + br_bits b0
  /\ br_in b1 = br_in b0
  /\ (0 <= br_have b0 -> 0 <= br_have b1)
  /\ (0 <= br_bits b0 -> 0 <= br_bits b1)
  /\ (0 <= br_hold b0 -> 0 <= br_bits b0 -> (forall j, 0 <= br_in b0 j) ->
      0 <= br_hold b1).

Lemma brok_refl : forall b, brok b b.
Proof. intros b. repeat split; intros; try lia; try reflexivity. Qed.

Lemma brok_trans : forall a b c, brok a b -> brok b c -> brok a c.
Proof.
  intros a b c (A1&A2&A3&A4&A5) (B1&B2&B3&B4&B5).
  split; [lia|]. split; [congruence|].
  split; [intros H; apply B3, A3, H|].
  split; [intros H; apply B4, A4, H|].
  intros H1 H2 H3. apply B5; [apply A5; assumption | apply A4, H2 |].
  rewrite A2. exact H3.
Qed.

Lemma br_pullbyte_pos : forall b b', br_pullbyte b = Some b' -> br_have b <> 0.
Proof.
  intros b b' H. unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0) eqn:E; [discriminate|].
  apply Z.eqb_neq in E. exact E.
Qed.

Lemma br_pullbyte_brok : forall b b', br_pullbyte b = Some b' -> brok b b'.
Proof.
  intros b b' H. pose proof (br_pullbyte_pos _ _ H) as Hp.
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  injection H as <-. unfold brok. cbn [br_have br_bits br_in br_hold].
  split; [lia|]. split; [reflexivity|].
  split; [intros; lia|]. split; [intros; lia|].
  intros Hh0 Hb0 Hin0.
  pose proof (Hin0 (br_next b)).
  pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b)). lia.
Qed.

Lemma inf_nb_go_brok :
  forall f n b,
    match inf_nb_go f n b with
    | NBOk b' => brok b b'
    | NBLeave b' => brok b b'
    end.
Proof.
  induction f as [|f IH]; intros n b; cbn [inf_nb_go].
  - destruct (Z.ltb (br_bits b) n); apply brok_refl.
  - destruct (Z.ltb (br_bits b) n); [|apply brok_refl].
    destruct (br_pullbyte b) as [b1|] eqn:Hp; [|apply brok_refl].
    pose proof (br_pullbyte_brok _ _ Hp) as HB.
    specialize (IH n b1).
    destruct (inf_nb_go f n b1); eapply brok_trans; eauto.
Qed.

Lemma inf_nb_brok :
  forall n b,
    match inf_nb n b with
    | NBOk b' => brok b b'
    | NBLeave b' => brok b b'
    end.
Proof. intros n b. apply inf_nb_go_brok. Qed.

Lemma inf_fetch_go_brok :
  forall f t nb b,
    match inf_fetch_go f t nb b with
    | FetchOk _ b' => brok b b'
    | FetchLeave b' => brok b b'
    | FetchFuel => True
    end.
Proof.
  induction f as [|f IH]; intros t nb b; cbn [inf_fetch_go]; [exact I|].
  destruct (Z.leb _ _); [apply brok_refl|].
  destruct (br_pullbyte b) as [b1|] eqn:Hp; [|apply brok_refl].
  pose proof (br_pullbyte_brok _ _ Hp) as HB.
  specialize (IH t nb b1).
  destruct (inf_fetch_go f t nb b1); trivial; eapply brok_trans; eauto.
Qed.

Lemma inf_fetch_brok :
  forall t nb b,
    match inf_fetch t nb b with
    | FetchOk _ b' => brok b b'
    | FetchLeave b' => brok b b'
    | FetchFuel => True
    end.
Proof. intros t nb b. apply inf_fetch_go_brok. Qed.

Lemma inf_fetch2_go_brok :
  forall f t lst b,
    match inf_fetch2_go f t lst b with
    | FetchOk _ b' => brok b b'
    | FetchLeave b' => brok b b'
    | FetchFuel => True
    end.
Proof.
  induction f as [|f IH]; intros t lst b; cbn [inf_fetch2_go]; [exact I|].
  destruct (Z.leb _ _); [apply brok_refl|].
  destruct (br_pullbyte b) as [b1|] eqn:Hp; [|apply brok_refl].
  pose proof (br_pullbyte_brok _ _ Hp) as HB.
  specialize (IH t lst b1).
  destruct (inf_fetch2_go f t lst b1); trivial; eapply brok_trans; eauto.
Qed.

Lemma inf_fetch2_brok :
  forall t lst b,
    match inf_fetch2 t lst b with
    | FetchOk _ b' => brok b b'
    | FetchLeave b' => brok b b'
    | FetchFuel => True
    end.
Proof. intros t lst b. apply inf_fetch2_go_brok. Qed.

Lemma br_dropbits_bud :
  forall n b, 0 <= n <= br_bits b ->
    8 * br_have (br_dropbits n b) + br_bits (br_dropbits n b)
      = 8 * br_have b + br_bits b - n
    /\ br_have (br_dropbits n b) = br_have b
    /\ br_bits (br_dropbits n b) = br_bits b - n.
Proof. intros n b H. unfold br_dropbits. cbn. lia. Qed.

Lemma u32_nonneg : forall v, 0 <= u32 v.
Proof.
  intros v. unfold u32.
  pose proof (Z.mod_pos_bound v 4294967296 ltac:(lia)). lia.
Qed.

(* ==========================================================================
   5.  The fallthrough combinator.
   ========================================================================== *)

Lemma CostStep_pre : forall q q1 r, CB q q1 -> CostStep q1 r -> CostStep q r.
Proof.
  intros q q1 r H1 H2.
  destruct r; cbn [CostStep] in *; try exact I; eapply CB_trans; eauto.
Qed.

Ltac aux_vac :=
  split; [intros HXv; discriminate | intros [HXv|[HXv|HXv]]; discriminate].

(* ==========================================================================
   6.  Output-side arms: LIT, MATCH's copy machinery.
   ========================================================================== *)

Lemma ob_copyn_put_eq :
  forall n win o r, o_put (ob_copyn n win o r) = o_put o + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros win o r; cbn [ob_copyn]; [cbn; lia|].
  rewrite IH. cbn [ob_write o_put]. lia.
Qed.

Lemma cost_LIT :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_LIT ->
  CostStep q (inf_LIT q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_LIT.
  destruct (Z.eqb (o_left (q_ob q)) 0).
  - cbn [CostStep]. unfold CB. cb8; try assumption; try lia.
  - cbn [CostStep]. unfold CB, Kq, Wq. bsimp.
    unfold cpend. rewrite Hm. bsimp.
    cb8; bsimp; try lia.
    + unfold CostAux. bsimp. aux_vac.
Qed.

Lemma of_to_nat_id : forall x, 0 <= x -> Z.of_nat (Z.to_nat x) = x.
Proof. intros x Hx. rewrite of_to_nat_max. lia. Qed.

Lemma cost_MATCH_tail :
  forall q cw3 src,
    CEntry q -> h_mode (s_hdr (q_st q)) = M_MATCH ->
    0 <= cw3 -> cw3 <= u_length (s_cur (q_st q)) ->
    u_length (s_cur (q_st q)) <= 258 ->
    CB q (if Z.eqb (u_length (s_cur (q_st q)) - cw3) 0
          then qmode (qset_ob (qset_st q (set_length (q_st q)
                        (u32 (u_length (s_cur (q_st q)) - cw3))))
                        (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                                  (q_ob q) src)) M_LEN
          else qset_ob (qset_st q (set_length (q_st q)
                        (u32 (u_length (s_cur (q_st q)) - cw3))))
                        (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                                  (q_ob q) src)).
Proof.
  intros q cw3 src CE Hm Hc0 Hc1 H258.
  pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  assert (Hid : Z.of_nat (Z.to_nat cw3) = cw3) by (apply of_to_nat_id; lia).
  assert (Hu32 : u32 (u_length (s_cur (q_st q)) - cw3)
                 = u_length (s_cur (q_st q)) - cw3)
    by (apply u32_id; lia).
  destruct (Z.eqb_spec (u_length (s_cur (q_st q)) - cw3) 0) as [He|He].
  - unfold CB, Kq, Wq, cpend. bsimp.
    rewrite ob_copyn_put_eq, ob_copyn_left_eq, Hid.
    rewrite !Hm. cbv beta iota.
    rewrite ?Hu32.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
  - unfold CB, Kq, Wq, cpend. bsimp.
    rewrite ob_copyn_put_eq, ob_copyn_left_eq, Hid.
    rewrite !Hm. cbv beta iota.
    rewrite ?Hu32.
    cb8; try lia.
    unfold CostAux. bsimp. rewrite !Hm.
    split; [intros HXv; discriminate|].
    intros _. rewrite ?Hu32. lia.
Qed.

Lemma cost_MATCH :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_MATCH ->
  u_length (s_cur (q_st q)) <= 258 ->
  CostStep q (inf_MATCH q).
Proof.
  intros q CE Hm H258. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_MATCH. cbv zeta.
  destruct (Z.eqb (o_left (q_ob q)) 0).
  { cbn [CostStep]. unfold CB. cb8; try assumption; try lia. }
  destruct (Z.ltb (u32 (q_out q - o_left (q_ob q)))
                  (u_offset (s_cur (q_st q)))).
  - (* window branch *)
    destruct (Z.ltb (w_whave (s_win (q_st q)))
                    (u32 (u_offset (s_cur (q_st q))
                          - u32 (q_out q - o_left (q_ob q))))
              && negb (Z.eqb (t_sane (s_tab (q_st q))) 0)).
    { (* dist-too-far: qbad, mode M_BAD *)
      cbn [CostStep]. unfold CB, Kq, Wq. bsimp.
      unfold cpend. rewrite Hm. bsimp.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
    destruct (Z.ltb (w_wnext (s_win (q_st q)))
                    (u32 (u_offset (s_cur (q_st q))
                          - u32 (q_out q - o_left (q_ob q)))))
      eqn:Hwn; cbv beta iota.
    + set (cw1 := u32 (u32 (u_offset (s_cur (q_st q))
                            - u32 (q_out q - o_left (q_ob q)))
                       - w_wnext (s_win (q_st q)))).
      pose proof (u32_nonneg (u32 (u_offset (s_cur (q_st q))
                            - u32 (q_out q - o_left (q_ob q)))
                       - w_wnext (s_win (q_st q)))) as Hcw1.
      fold cw1 in Hcw1.
      set (cw2 := if Z.ltb (u_length (s_cur (q_st q))) cw1
                  then u_length (s_cur (q_st q)) else cw1).
      assert (Hcw2 : 0 <= cw2 /\ cw2 <= u_length (s_cur (q_st q))).
      { unfold cw2. destruct (Z.ltb_spec (u_length (s_cur (q_st q))) cw1); lia. }
      set (cw3 := if Z.ltb (o_left (q_ob q)) cw2
                  then o_left (q_ob q) else cw2).
      assert (Hcw3 : 0 <= cw3 /\ cw3 <= u_length (s_cur (q_st q))).
      { unfold cw3. destruct (Z.ltb_spec (o_left (q_ob q)) cw2); lia. }
      cbn [CostStep].
      apply (cost_MATCH_tail q cw3 _ CE Hm); lia.
    + set (cw1 := u32 (u_offset (s_cur (q_st q))
                       - u32 (q_out q - o_left (q_ob q)))).
      pose proof (u32_nonneg (u_offset (s_cur (q_st q))
                       - u32 (q_out q - o_left (q_ob q)))) as Hcw1.
      fold cw1 in Hcw1.
      set (cw2 := if Z.ltb (u_length (s_cur (q_st q))) cw1
                  then u_length (s_cur (q_st q)) else cw1).
      assert (Hcw2 : 0 <= cw2 /\ cw2 <= u_length (s_cur (q_st q))).
      { unfold cw2. destruct (Z.ltb_spec (u_length (s_cur (q_st q))) cw1); lia. }
      set (cw3 := if Z.ltb (o_left (q_ob q)) cw2
                  then o_left (q_ob q) else cw2).
      assert (Hcw3 : 0 <= cw3 /\ cw3 <= u_length (s_cur (q_st q))).
      { unfold cw3. destruct (Z.ltb_spec (o_left (q_ob q)) cw2); lia. }
      cbn [CostStep].
      apply (cost_MATCH_tail q cw3 _ CE Hm); lia.
  - (* direct branch *)
    set (cw3 := if Z.ltb (o_left (q_ob q)) (u_length (s_cur (q_st q)))
                then o_left (q_ob q) else u_length (s_cur (q_st q))).
    assert (Hcw3 : 0 <= cw3 /\ cw3 <= u_length (s_cur (q_st q))).
    { unfold cw3.
      destruct (Z.ltb_spec (o_left (q_ob q)) (u_length (s_cur (q_st q)))); lia. }
    cbn [CostStep].
    apply (cost_MATCH_tail q cw3 _ CE Hm); lia.
Qed.

(* ==========================================================================
   7.  Recurring shapes: a leave/step that only swaps the bit-reader.
   ========================================================================== *)

Lemma CB_qset_br :
  forall q b, brok (q_br q) b ->
    0 <= br_have (q_br q) -> 0 <= br_bits (q_br q) ->
    0 <= u_length (s_cur (q_st q)) -> CostAux (q_st q) ->
    CB q (qset_br q b).
Proof.
  intros q b (E&Ein&Sh&Sb&_) Hh Hb Hl Ha.
  unfold CB, Kq, Wq. bsimp.
  cb8; try lia; try assumption.
Qed.

(** Table entry bit-widths are nonnegative at every reachable table. *)
Lemma tbl_bits_nonneg :
  forall st r, amb_ok (t_codes (s_tab st)) ->
    forall i, 0 <= c_bits (tbl_of st r i).
Proof.
  intros st r Hamb i. destruct r; cbn [tbl_of].
  - exact (proj1 (proj1 (Hamb _))).
  - unfold lenfix.
    assert (Hc : (0 <=? c_bits (tbl_of_list lenfix_list i)) = true).
    { apply (tbl_of_list_all (fun e => 0 <=? c_bits e) lenfix_list);
        [vm_compute; reflexivity | reflexivity]. }
    apply Z.leb_le in Hc. exact Hc.
  - pose proof (distfix_wid_all i). lia.
Qed.

(** [inf_decode], both constructors: [DecOk]'s budget drop is exactly
    [nb >= 0]; [DecLeave] carries the budget. *)
Lemma inf_decode_brok :
  forall sub t rb b,
    (forall i, 0 <= c_bits (t i)) ->
    match inf_decode sub t rb b with
    | DecOk h b2 nb =>
        0 <= nb
        /\ 8 * br_have b2 + br_bits b2 = 8 * br_have b + br_bits b - nb
        /\ br_in b2 = br_in b
        /\ (0 <= br_have b -> 0 <= br_have b2)
        /\ 0 <= br_bits b2
        /\ (0 <= br_hold b -> 0 <= br_bits b ->
            (forall j, 0 <= br_in b j) -> 0 <= br_hold b2)
    | DecLeave b2 => brok b b2
    | DecFuel => True
    end.
Proof.
  intros sub t rb b Htb.
  destruct (inf_decode sub t rb b) as [h b2 nb|b2|] eqn:Ed; [| |exact I].
  - pose proof (inf_decode_ok_facts _ _ _ _ _ _ _ Htb Ed) as (_ & Hnb).
    pose proof (inf_decode_bud _ _ _ _ _ _ _ Ed) as (Ebud & Hhs).
    pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Ed) as Hb2.
    assert (Hrest : br_in b2 = br_in b
                    /\ (0 <= br_hold b -> 0 <= br_bits b ->
                        (forall j, 0 <= br_in b j) -> 0 <= br_hold b2)).
    { unfold inf_decode in Ed.
      pose proof (inf_fetch_brok t rb b) as HF.
      destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; try discriminate.
      destruct HF as (F1&F2&F3&F4&F5).
      destruct (sub h0).
      - pose proof (inf_fetch2_brok t h0 b0) as HG.
        destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2; try discriminate.
        destruct HG as (G1&G2&G3&G4&G5).
        injection Ed as E1 E2 E3. subst.
        unfold br_dropbits. cbn [br_in br_hold].
        split; [congruence|].
        intros Hh Hbb Hin.
        assert (0 <= br_hold b1).
        { apply G5; [apply F5; assumption | apply F4; assumption |].
          rewrite F2. exact Hin. }
        apply Z.shiftr_nonneg. apply Z.shiftr_nonneg. lia.
      - injection Ed as E1 E2 E3. subst.
        unfold br_dropbits. cbn [br_in br_hold].
        split; [congruence|].
        intros Hh Hbb Hin.
        apply Z.shiftr_nonneg. apply F5; assumption. }
    destruct Hrest as (Hin & Hho2).
    repeat split; try lia; try exact Hin; try exact Hhs; try exact Hho2.
  - unfold inf_decode in Ed.
    pose proof (inf_fetch_brok t rb b) as HF.
    destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; try discriminate.
    + destruct (sub h0).
      * pose proof (inf_fetch2_brok t h0 b0) as HG.
        destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2; try discriminate.
        injection Ed as E. subst. eapply brok_trans; eauto.
      * discriminate.
    + injection Ed as E. subst. exact HF.
Qed.

(* ==========================================================================
   8.  The LEN-side fallthrough chain: DISTEXT -> DIST -> LENEXT
       (callee-first; MATCH is section 6).
   ========================================================================== *)

Lemma cost_DISTEXT :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_DISTEXT ->
  0 <= u_extra (s_cur (q_st q)) ->
  CostStep q (inf_DISTEXT q).
Proof.
  intros q CE Hm He. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  assert (H258 : u_length (s_cur (q_st q)) <= 258)
    by (exact (proj2 Ha (or_intror (or_introl Hm)))).
  unfold inf_DISTEXT. cbv zeta.
  destruct (Z.eqb (u_extra (s_cur (q_st q))) 0).
  - eapply CostStep_pre with (q1 := qmode q M_MATCH).
    + unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp.
      split; [intros HXv; discriminate | intros _; exact H258].
    + apply cost_MATCH.
      2: bsimp; reflexivity.
      2: bsimp; exact H258.
      constructor; bsimp; try assumption.
      unfold CostAux. bsimp.
      split; [intros HXv; discriminate | intros _; exact H258].
  - destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:En.
    + pose proof (inf_nb_brok (u_extra (s_cur (q_st q))) (q_br q)) as HN;
        rewrite En in HN; destruct HN as (E1&E2&E3&E4&E5).
      pose proof (inf_nb_ok _ _ _ En) as Hok.
      eapply CostStep_pre with
        (q1 := qmode (qset_br (qset_st q
                  (set_back (set_offset (q_st q)
                     (u_offset (s_cur (q_st q))
                      + br_bits_of (u_extra (s_cur (q_st q))) b))
                     (u_back (s_cur (q_st q)) + u_extra (s_cur (q_st q)))))
                 (br_dropbits (u_extra (s_cur (q_st q))) b)) M_MATCH).
      * unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
        cb8; try lia.
        unfold CostAux. bsimp.
        split; [intros HXv; discriminate | intros _; exact H258].
      * apply cost_MATCH.
        2: bsimp; reflexivity.
        2: bsimp; exact H258.
        constructor; bsimp; try assumption; try lia.
        { apply Z.shiftr_nonneg. apply E5; assumption. }
        { intros j. rewrite E2. apply Hby. }
        unfold CostAux. bsimp.
        split; [intros HXv; discriminate | intros _; exact H258].
    + pose proof (inf_nb_brok (u_extra (s_cur (q_st q))) (q_br q)) as HN;
        rewrite En in HN.
      cbn [CostStep]. apply CB_qset_br; assumption.
Qed.

Lemma cost_DIST :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_DIST ->
  amb_ok (t_codes (s_tab (q_st q))) ->
  CostStep q (inf_DIST q).
Proof.
  intros q CE Hm Hamb. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  assert (H258 : u_length (s_cur (q_st q)) <= 258)
    by (exact (proj2 Ha (or_introl Hm))).
  unfold inf_DIST. cbv zeta.
  pose proof (inf_decode_brok sub_dist
                (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
                (t_distbits (s_tab (q_st q))) (q_br q)
                (tbl_bits_nonneg _ _ Hamb)) as HD.
  destruct (inf_decode sub_dist _ _ _) as [h b nb|b|] eqn:Ed; [| |exact I].
  - destruct HD as (Hnb & Ebud & Hin & Hhs & Hb2 & Hho2).
    destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)).
    + (* qbad: M_BAD *)
      cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
      rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply Hhs, Hh).
      unfold CostAux. bsimp. aux_vac.
    + eapply CostStep_pre with
        (q1 := qmode (qset_st
                 (qset_br (qset_st q
                    (set_back (q_st q) (u_back (s_cur (q_st q)) + nb))) b)
                 (set_extra (set_offset
                    (q_st (qset_br (qset_st q
                       (set_back (q_st q) (u_back (s_cur (q_st q)) + nb))) b))
                    (c_val h)) (Z.land (c_op h) 15))) M_DISTEXT).
      * unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply Hhs, Hh).
        unfold CostAux. bsimp.
        split; [intros HXv; discriminate | intros _; exact H258].
      * apply cost_DISTEXT.
        2: bsimp; reflexivity.
        2: bsimp; pose proof (land15_range (c_op h)); lia.
        constructor; bsimp; try assumption; try (apply Hhs, Hh); try lia.
        { apply Hho2; assumption. }
        { intros j. rewrite Hin. apply Hby. }
        unfold CostAux. bsimp.
        split; [intros HXv; discriminate | intros _; exact H258].
  - cbn [CostStep]. apply CB_qset_br; assumption.
Qed.

Lemma cost_LENEXT :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_LENEXT ->
  amb_ok (t_codes (s_tab (q_st q))) ->
  CostStep q (inf_LENEXT q).
Proof.
  intros q CE Hm Hamb. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  destruct (proj1 Ha Hm) as [He Hle].
  rewrite Z.shiftl_1_l in Hle.
  unfold inf_LENEXT. cbv zeta.
  destruct (Z.eqb (u_extra (s_cur (q_st q))) 0) eqn:Ez; cbv beta iota.
  - (* no extra bits *)
    apply Z.eqb_eq in Ez. rewrite Ez in Hle. cbn [Z.pow] in Hle.
    eapply CostStep_pre with
      (q1 := qmode (qset_br (qset_st q
                (set_was (q_st q) (u_length (s_cur (q_st q))))) (q_br q))
              M_DIST).
    + unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp.
      split; [intros HXv; discriminate | intros _; lia].
    + apply cost_DIST.
      2: bsimp; reflexivity.
      2: bsimp; exact Hamb.
      constructor; bsimp; try assumption.
      unfold CostAux. bsimp.
      split; [intros HXv; discriminate | intros _; lia].
  - destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:En.
    + pose proof (inf_nb_brok (u_extra (s_cur (q_st q))) (q_br q)) as HN;
        rewrite En in HN; destruct HN as (E1&E2&E3&E4&E5).
      pose proof (inf_nb_ok _ _ _ En) as Hok.
      pose proof (bits_of_range (u_extra (s_cur (q_st q))) b He) as Hg.
      assert (He1 : 1 <= u_extra (s_cur (q_st q))).
      { apply Z.eqb_neq in Ez. lia. }
      eapply CostStep_pre with
        (q1 := qmode (qset_br (qset_st q
                 (set_was (set_back (set_length (q_st q)
                    (u_length (s_cur (q_st q))
                     + br_bits_of (u_extra (s_cur (q_st q))) b))
                    (u_back (s_cur (q_st q)) + u_extra (s_cur (q_st q))))
                   (u_length (s_cur (set_back (set_length (q_st q)
                    (u_length (s_cur (q_st q))
                     + br_bits_of (u_extra (s_cur (q_st q))) b))
                    (u_back (s_cur (q_st q)) + u_extra (s_cur (q_st q))))))))
                 (br_dropbits (u_extra (s_cur (q_st q))) b)) M_DIST).
      * unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
        cb8; try lia.
        unfold CostAux. bsimp.
        split; [intros HXv; discriminate | intros _; lia].
      * apply cost_DIST.
        2: bsimp; reflexivity.
        2: bsimp; exact Hamb.
        constructor; bsimp; try assumption; try lia.
        { apply Z.shiftr_nonneg. apply E5; assumption. }
        { intros j. rewrite E2. apply Hby. }
        unfold CostAux. bsimp.
        split; [intros HXv; discriminate | intros _; lia].
    + pose proof (inf_nb_brok (u_extra (s_cur (q_st q))) (q_br q)) as HN;
        rewrite En in HN.
      cbn [CostStep]. apply CB_qset_br; assumption.
Qed.

(* ==========================================================================
   9.  The tail chain (CHECK -> LENGTH -> DONE) and the stored chain
       (STORED -> COPY_ -> COPY).
   ========================================================================== *)

Lemma cost_LENGTH :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_LENGTH ->
  CostStep q (inf_LENGTH q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_LENGTH. cbv zeta.
  destruct (negb (Z.eqb (h_wrap (s_hdr (q_st q))) 0)
            && negb (Z.eqb (h_flags (s_hdr (q_st q))) 0)).
  - destruct (inf_nb 32 (q_br q)) as [b|b] eqn:En;
      pose proof (inf_nb_brok 32 (q_br q)) as HN; rewrite En in HN.
    + destruct HN as (E1&E2&E3&E4&E5).
      destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
                && negb (Z.eqb (br_hold b)
                          (Z.land (h_total (s_hdr (q_st q))) 4294967295))).
      * (* qbad *)
        cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota.
        cb8; try lia.
        unfold CostAux. bsimp. aux_vac.
      * eapply CostStep_pre with
          (q1 := qmode (qset_br q (br_initbits b)) M_DONE).
        { unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
          cb8; try lia.
          unfold CostAux. bsimp. aux_vac. }
        apply cost_DONE.
        constructor; bsimp; try assumption; try lia.
        { intros j. rewrite E2. apply Hby. }
        unfold CostAux. bsimp. aux_vac.
    + cbn [CostStep]. apply CB_qset_br; assumption.
  - eapply CostStep_pre with (q1 := qmode q M_DONE).
    { unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
    apply cost_DONE.
    constructor; bsimp; try assumption.
    unfold CostAux. bsimp. aux_vac.
Qed.

(** Callee wrappers: [eapply] lets unification capture the caller's
    (possibly huge) intermediate state term. *)
Lemma call_DONE : forall q q1,
  CB q q1 -> CostStep q (inf_DONE q1).
Proof.
  intros q q1 HCB. eapply CostStep_pre; [exact HCB|].
  unfold inf_DONE. cbn [CostStep].
  destruct HCB as (_&_&_&_&C5&C6&C7&C8).
  unfold CB, Kq, Wq. bsimp. cb8; try lia; try assumption.
Qed.

Ltac centry :=
  constructor; bsimp; try assumption; try lia.

Lemma call_LENGTH : forall q q1,
  CB q q1 -> 0 <= o_left (q_ob q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  h_mode (s_hdr (q_st q1)) = M_LENGTH ->
  CostStep q (inf_LENGTH q1).
Proof.
  intros q q1 HCB Hlf Hho Hby Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&C5&C6&C7&C8).
  apply cost_LENGTH; [constructor; assumption | exact Hm].
Qed.

Lemma cost_CHECK :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_CHECK ->
  CostStep q (inf_CHECK q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_CHECK. cbv zeta.
  destruct (Z.eqb (h_wrap (s_hdr (q_st q))) 0).
  - eapply call_LENGTH;
      [| bsimp; exact Hleft | bsimp; exact Hho | bsimp; exact Hby
       | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
  - destruct (inf_nb 32 (q_br q)) as [b|b] eqn:En;
      pose proof (inf_nb_brok 32 (q_br q)) as HN; rewrite En in HN.
    + destruct HN as (E1&E2&E3&E4&E5).
      destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
                && negb (Z.eqb (q_out q - o_left (q_ob q)) 0));
      cbv beta iota;
      (destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
                 && negb (Z.eqb _ _));
       [ (* qbad *)
         cbn [CostStep]; unfold CB, Kq, Wq, cpend; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; aux_vac
       | eapply call_LENGTH;
         [ unfold CB, Kq, Wq, cpend; bsimp; rewrite !Hm; cbv beta iota;
           cb8; try lia;
           unfold CostAux; bsimp; aux_vac
         | bsimp; exact Hleft
         | bsimp; lia
         | bsimp; intros j; rewrite E2; apply Hby
         | bsimp; reflexivity ] ]).
    + cbn [CostStep]. apply CB_qset_br; assumption.
Qed.

Lemma cost_COPY :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_COPY ->
  CostStep q (inf_COPY q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_COPY. cbv zeta.
  destruct (Z.eqb (u_length (s_cur (q_st q))) 0).
  - (* cp = 0: to TYPE *)
    cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
    rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
  - set (c1 := if Z.ltb (br_have (q_br q)) (u_length (s_cur (q_st q)))
               then br_have (q_br q) else u_length (s_cur (q_st q))).
    assert (Hc1 : 0 <= c1 /\ c1 <= br_have (q_br q)
                  /\ c1 <= u_length (s_cur (q_st q))).
    { unfold c1.
      destruct (Z.ltb_spec (br_have (q_br q)) (u_length (s_cur (q_st q))));
        lia. }
    set (c2 := if Z.ltb (o_left (q_ob q)) c1 then o_left (q_ob q) else c1).
    assert (Hc2 : 0 <= c2 /\ c2 <= br_have (q_br q)
                  /\ c2 <= u_length (s_cur (q_st q))).
    { unfold c2. destruct (Z.ltb_spec (o_left (q_ob q)) c1); lia. }
    destruct (Z.eqb c2 0).
    + cbn [CostStep]. unfold CB. cb8; try assumption; try lia.
    + cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
      rewrite !Hm. cbv beta iota.
      pose proof (u32_nonneg (u_length (s_cur (q_st q)) - c2)).
      cb8; try lia.
      unfold CostAux. bsimp. rewrite !Hm. aux_vac.
Qed.

Lemma call_COPY : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_COPY ->
  CostStep q (inf_COPY q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_COPY; [constructor; assumption | exact Hm].
Qed.

Lemma cost_COPY_ :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_COPY_ ->
  CostStep q (inf_COPY_ q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_COPY_.
  eapply call_COPY;
    [| bsimp; exact Hh | bsimp; exact Hb | bsimp; exact Hho
     | bsimp; exact Hby | bsimp; exact Hleft | bsimp; reflexivity].
  unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
  cb8; try lia.
  unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_COPY_ : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_COPY_ ->
  CostStep q (inf_COPY_ q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_COPY_; [constructor; assumption | exact Hm].
Qed.

Lemma cost_STORED :
  forall c q, CEntry q -> h_mode (s_hdr (q_st q)) = M_STORED ->
  CostStep q (inf_STORED c q).
Proof.
  intros c q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  assert (Hk : 0 <= Z.land (br_bits (q_br q)) 7 <= br_bits (q_br q)).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
    change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    assert (br_bits (q_br q) mod 8 <= br_bits (q_br q))
      by (apply Z.mod_le; lia).
    lia. }
  unfold inf_STORED. cbv zeta.
  destruct (inf_nb 32 (br_bytebits (q_br q))) as [b|b] eqn:En;
    pose proof (inf_nb_brok 32 (br_bytebits (q_br q))) as HN;
    rewrite En in HN;
    unfold brok, br_bytebits, br_dropbits in HN;
    cbn [br_have br_bits br_in br_hold] in HN;
    destruct HN as (E1&E2&E3&E4&E5).
  - destruct (negb (Z.eqb (Z.land (br_hold b) 65535)
                    (Z.lxor (Z.shiftr (br_hold b) 16) 65535))).
    + (* qbad *)
      cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
      rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply E3; lia); try (apply E4; lia).
      unfold CostAux. bsimp. aux_vac.
    + assert (Hlen : 0 <= Z.land (u32 (br_hold b)) 65535)
        by (apply Z.land_nonneg; right; lia).
      destruct (Z.eqb (n_flush c) Z_TREES).
      * (* InfLeave q1 *)
        cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply E3; lia); try (apply E4; lia).
        unfold CostAux. bsimp. aux_vac.
      * eapply call_COPY_;
          [| bsimp; apply E3; lia | bsimp; lia | bsimp; lia
           | bsimp; intros j; rewrite E2; apply Hby
           | bsimp; exact Hleft | bsimp; reflexivity].
        unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply E3; lia); try (apply E4; lia).
        unfold CostAux. bsimp. aux_vac.
  - cbn [CostStep].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia; try (apply E3; lia); try (apply E4; lia).
    unfold CostAux. bsimp. rewrite !Hm. aux_vac.
Qed.

(* ==========================================================================
   10.  The block-header chain: TYPEDO (entered from TYPE without a mode
        write), TYPE, DICT, DICTID.
   ========================================================================== *)

Lemma cost_TYPEDO :
  forall c q, CEntry q ->
  h_mode (s_hdr (q_st q)) = M_TYPE \/ h_mode (s_hdr (q_st q)) = M_TYPEDO ->
  CostStep q (inf_TYPEDO c q).
Proof.
  intros c q CE Hm2. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  assert (Hcp : cpend (q_st q) = 0)
    by (unfold cpend; destruct Hm2 as [Hm|Hm]; rewrite Hm; reflexivity).
  assert (Hax : forall s', h_mode (s_hdr s') = h_mode (s_hdr (q_st q)) ->
            CostAux s').
  { intros s' Hs. unfold CostAux. rewrite Hs.
    destruct Hm2 as [Hm|Hm]; rewrite Hm;
      (split; [intros HXv; discriminate | intros [HXv|[HXv|HXv]]; discriminate]). }
  assert (Hk : 0 <= Z.land (br_bits (q_br q)) 7 <= br_bits (q_br q)).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
    change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    assert (br_bits (q_br q) mod 8 <= br_bits (q_br q))
      by (apply Z.mod_le; lia).
    lia. }
  unfold inf_TYPEDO. cbv zeta.
  destruct (negb (Z.eqb (h_last (s_hdr (q_st q))) 0)).
  - (* to CHECK via bytebits *)
    cbn [CostStep]. unfold CB, Kq, Wq. bsimp. rewrite Hcp.
    unfold br_bytebits, br_dropbits. bsimp.
    cb8; try lia.
    + unfold cpend. bsimp. lia.
    + unfold CostAux. bsimp. aux_vac.
  - destruct (inf_nb 3 (q_br q)) as [b|b] eqn:En;
      pose proof (inf_nb_brok 3 (q_br q)) as HN; rewrite En in HN;
      unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
    + pose proof (inf_nb_ok _ _ _ En) as Hok.
      destruct (Z.eqb (br_bits_of 2 (br_dropbits 1 b)) 0).
      * (* stored *)
        cbn [CostStep]. unfold CB, Kq, Wq. bsimp. rewrite Hcp.
        unfold br_dropbits. bsimp.
        cb8; try lia; try (apply E3; lia).
        { unfold cpend. bsimp. lia. }
        unfold CostAux. bsimp. aux_vac.
      * destruct (Z.eqb (br_bits_of 2 (br_dropbits 1 b)) 1).
        -- destruct (Z.eqb (n_flush c) Z_TREES).
           ++ cbn [CostStep]. unfold CB, Kq, Wq. bsimp. rewrite Hcp.
              unfold br_dropbits, fixedtables. bsimp.
              cb8; try lia; try (apply E3; lia).
              { unfold cpend. bsimp. lia. }
              unfold CostAux. bsimp. aux_vac.
           ++ cbn [CostStep]. unfold CB, Kq, Wq. bsimp. rewrite Hcp.
              unfold br_dropbits, fixedtables. bsimp.
              cb8; try lia; try (apply E3; lia).
              { unfold cpend. bsimp. lia. }
              unfold CostAux. bsimp. aux_vac.
        -- destruct (Z.eqb (br_bits_of 2 (br_dropbits 1 b)) 2).
           ++ cbn [CostStep]. unfold CB, Kq, Wq. bsimp. rewrite Hcp.
              unfold br_dropbits. bsimp.
              cb8; try lia; try (apply E3; lia).
              { unfold cpend. bsimp. lia. }
              unfold CostAux. bsimp. aux_vac.
           ++ cbn [CostStep]. unfold CB, Kq, Wq. bsimp. rewrite Hcp.
              unfold br_dropbits. bsimp.
              cb8; try lia; try (apply E3; lia).
              { unfold cpend. bsimp. lia. }
              unfold CostAux. bsimp. aux_vac.
    + cbn [CostStep].
      eapply CB_qset_br; try assumption.
      unfold brok. repeat split; assumption.
Qed.

Lemma cost_TYPE :
  forall c q, CEntry q -> h_mode (s_hdr (q_st q)) = M_TYPE ->
  CostStep q (inf_TYPE c q).
Proof.
  intros c q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_TYPE.
  destruct (Z.eqb (n_flush c) Z_BLOCK || Z.eqb (n_flush c) Z_TREES).
  - cbn [CostStep]. unfold CB. cb8; try assumption; try lia.
  - apply cost_TYPEDO; [exact CE | left; exact Hm].
Qed.

Lemma call_TYPE : forall c q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_TYPE ->
  CostStep q (inf_TYPE c q1).
Proof.
  intros c q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_TYPE; [constructor; assumption | exact Hm].
Qed.

Lemma cost_DICT :
  forall c q, CEntry q -> h_mode (s_hdr (q_st q)) = M_DICT ->
  CostStep q (inf_DICT c q).
Proof.
  intros c q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_DICT.
  destruct (Z.eqb (h_havedict (s_hdr (q_st q))) 0).
  - cbn [CostStep]. unfold CB, Kq, Wq, cpend, q_restore. bsimp.
    rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. rewrite !Hm. aux_vac.
  - eapply call_TYPE;
      [| bsimp; exact Hh | bsimp; exact Hb | bsimp; exact Hho
       | bsimp; exact Hby | bsimp; exact Hleft | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_DICT : forall c q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_DICT ->
  CostStep q (inf_DICT c q1).
Proof.
  intros c q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_DICT; [constructor; assumption | exact Hm].
Qed.

Lemma cost_DICTID :
  forall c q, CEntry q -> h_mode (s_hdr (q_st q)) = M_DICTID ->
  CostStep q (inf_DICTID c q).
Proof.
  intros c q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_DICTID.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:En;
    pose proof (inf_nb_brok 32 (q_br q)) as HN; rewrite En in HN;
    unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
  - eapply call_DICT;
      [| bsimp; apply E3; lia | bsimp; lia | bsimp; lia
       | bsimp; intros j; rewrite E2; apply Hby
       | bsimp; exact Hleft | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    unfold br_initbits. bsimp.
    cb8; try lia; try (apply E3; lia).
    unfold CostAux. bsimp. aux_vac.
  - cbn [CostStep].
    eapply CB_qset_br; try assumption.
    unfold brok. repeat split; assumption.
Qed.

(* ==========================================================================
   11.  The gzip header chain: HCRC <- COMMENT <- NAME <- EXTRA <- EXLEN
        <- OS <- TIME <- FLAGS <- HEAD.
   ========================================================================== *)

Lemma gz_strz_bounds :
  forall f a i have copy copy' len,
    gz_strz f a i have copy = Some (copy', len) ->
    copy < copy' /\ (copy + 1 <= have -> copy' <= have).
Proof.
  induction f as [|f IH]; intros a i have copy copy' len H;
    cbn [gz_strz] in H; [discriminate|].
  destruct (negb (Z.eqb (a i) 0) && Z.ltb (copy + 1) have) eqn:G.
  - apply andb_prop in G as [_ G2]. apply Z.ltb_lt in G2.
    apply IH in H as [IH1 IH2].
    split; [lia | intros _; apply IH2; lia].
  - injection H as <- <-. split; [lia | intros; lia].
Qed.

Lemma cost_HCRC :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_HCRC ->
  CostStep q (inf_HCRC q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_HCRC. cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)).
  - destruct (inf_nb 16 (q_br q)) as [b|b] eqn:En;
      pose proof (inf_nb_brok 16 (q_br q)) as HN; rewrite En in HN;
      unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
    + destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
                && negb (Z.eqb (br_hold b)
                          (Z.land (h_check (s_hdr (q_st q))) 65535))).
      * cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply E3; lia).
        unfold CostAux. bsimp. aux_vac.
      * cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota. unfold br_initbits. bsimp.
        cb8; try lia; try (apply E3; lia).
        unfold CostAux. bsimp. aux_vac.
    + cbn [CostStep].
      eapply CB_qset_br; try assumption.
      unfold brok. repeat split; assumption.
  - cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
    rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_HCRC : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_HCRC ->
  CostStep q (inf_HCRC q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_HCRC; [constructor; assumption | exact Hm].
Qed.

Lemma cost_COMMENT :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_COMMENT ->
  CostStep q (inf_COMMENT q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_COMMENT. cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 4096) 0)).
  - destruct (Z.eqb_spec (br_have (q_br q)) 0) as [Hv0|Hv0].
    { cbn [CostStep]. unfold CB. cb8; try assumption; try lia. }
    destruct (gz_strz (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                (br_next (q_br q)) (br_have (q_br q)) 0)
      as [[copy len]|] eqn:Es; [|exact I].
    apply gz_strz_bounds in Es as [Ec1 Ec2].
    specialize (Ec2 ltac:(lia)).
    destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      cbv beta iota;
      (destruct (negb (Z.eqb len 0));
       [ (* InfLeave q2 *)
         cbn [CostStep]; unfold CB, Kq, Wq, cpend, br_consume; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; rewrite !Hm; aux_vac
       | (* fallthrough to HCRC *)
         eapply call_HCRC;
         [ unfold CB, Kq, Wq, cpend, br_consume; bsimp;
           rewrite !Hm; cbv beta iota;
           cb8; try lia;
           unfold CostAux; bsimp; aux_vac
         | unfold br_consume; bsimp; lia
         | unfold br_consume; bsimp; exact Hb
         | unfold br_consume; bsimp; exact Hho
         | unfold br_consume; bsimp; exact Hby
         | bsimp; exact Hleft
         | bsimp; reflexivity ] ]).
  - eapply call_HCRC;
      [| bsimp; exact Hh | bsimp; exact Hb | bsimp; exact Hho
       | bsimp; exact Hby | bsimp; exact Hleft | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_COMMENT : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_COMMENT ->
  CostStep q (inf_COMMENT q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_COMMENT; [constructor; assumption | exact Hm].
Qed.

Lemma cost_NAME :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_NAME ->
  CostStep q (inf_NAME q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_NAME. cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 2048) 0)).
  - destruct (Z.eqb_spec (br_have (q_br q)) 0) as [Hv0|Hv0].
    { cbn [CostStep]. unfold CB. cb8; try assumption; try lia. }
    destruct (gz_strz (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                (br_next (q_br q)) (br_have (q_br q)) 0)
      as [[copy len]|] eqn:Es; [|exact I].
    apply gz_strz_bounds in Es as [Ec1 Ec2].
    specialize (Ec2 ltac:(lia)).
    destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      cbv beta iota;
      (destruct (negb (Z.eqb len 0));
       [ cbn [CostStep]; unfold CB, Kq, Wq, cpend, br_consume; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; rewrite !Hm; aux_vac
       | eapply call_COMMENT;
         [ unfold CB, Kq, Wq, cpend, br_consume; bsimp;
           rewrite !Hm; cbv beta iota;
           cb8; try lia;
           unfold CostAux; bsimp; aux_vac
         | unfold br_consume; bsimp; lia
         | unfold br_consume; bsimp; exact Hb
         | unfold br_consume; bsimp; exact Hho
         | unfold br_consume; bsimp; exact Hby
         | bsimp; exact Hleft
         | bsimp; reflexivity ] ]).
  - eapply call_COMMENT;
      [| bsimp; exact Hh | bsimp; exact Hb | bsimp; exact Hho
       | bsimp; exact Hby | bsimp; exact Hleft | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_NAME : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_NAME ->
  CostStep q (inf_NAME q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_NAME; [constructor; assumption | exact Hm].
Qed.

Lemma cost_EXTRA :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_EXTRA ->
  CostStep q (inf_EXTRA q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_EXTRA. cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 1024) 0)).
  - set (copy := if Z.ltb (br_have (q_br q)) (u_length (s_cur (q_st q)))
                 then br_have (q_br q) else u_length (s_cur (q_st q))).
    assert (Hcp : 0 <= copy /\ copy <= br_have (q_br q)
                  /\ copy <= u_length (s_cur (q_st q))).
    { unfold copy.
      destruct (Z.ltb_spec (br_have (q_br q)) (u_length (s_cur (q_st q))));
        lia. }
    destruct (negb (Z.eqb copy 0));
      [ destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
                  && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0))
      |];
      cbv beta iota;
      (destruct (negb (Z.eqb _ 0));
       [ (* InfLeave q2 *)
         cbn [CostStep]; unfold CB, Kq, Wq, cpend, br_consume; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; rewrite !Hm; aux_vac
       | eapply call_NAME;
         [ unfold CB, Kq, Wq, cpend, br_consume; bsimp;
           rewrite !Hm; cbv beta iota;
           cb8; try lia;
           unfold CostAux; bsimp; aux_vac
         | unfold br_consume; bsimp; lia
         | unfold br_consume; bsimp; exact Hb
         | unfold br_consume; bsimp; exact Hho
         | unfold br_consume; bsimp; exact Hby
         | bsimp; exact Hleft
         | bsimp; reflexivity ] ]).
  - eapply call_NAME;
      [| bsimp; exact Hh | bsimp; exact Hb | bsimp; exact Hho
       | bsimp; exact Hby | bsimp; exact Hleft | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_EXTRA : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) -> 0 <= u_length (s_cur (q_st q1)) ->
  h_mode (s_hdr (q_st q1)) = M_EXTRA ->
  CostStep q (inf_EXTRA q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 H4 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&_&C8).
  apply cost_EXTRA; [constructor; assumption | exact Hm].
Qed.

Lemma cost_EXLEN :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_EXLEN ->
  CostStep q (inf_EXLEN q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_EXLEN. cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 1024) 0)).
  - destruct (inf_nb 16 (q_br q)) as [b|b] eqn:En;
      pose proof (inf_nb_brok 16 (q_br q)) as HN; rewrite En in HN;
      unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
    + assert (Hhb : 0 <= br_hold b) by (apply E5; assumption).
      destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
                && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
        cbv beta iota;
        (eapply call_EXTRA;
         [ unfold CB, Kq, Wq, cpend, br_initbits; bsimp;
           rewrite !Hm; cbv beta iota;
           cb8; try lia;
           unfold CostAux; bsimp; aux_vac
         | bsimp; apply E3; lia
         | bsimp; lia
         | bsimp; lia
         | bsimp; intros j; rewrite E2; apply Hby
         | bsimp; exact Hleft
         | bsimp; lia
         | bsimp; reflexivity ]).
    + cbn [CostStep].
      eapply CB_qset_br; try assumption.
      unfold brok. repeat split; assumption.
  - eapply call_EXTRA;
      [| bsimp; exact Hh | bsimp; exact Hb | bsimp; exact Hho
       | bsimp; exact Hby | bsimp; exact Hleft | bsimp; exact Hl
       | bsimp; reflexivity].
    unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac.
Qed.

Lemma call_EXLEN : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_EXLEN ->
  CostStep q (inf_EXLEN q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_EXLEN; [constructor; assumption | exact Hm].
Qed.

Lemma cost_OS :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_OS ->
  CostStep q (inf_OS q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_OS. cbv zeta.
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:En;
    pose proof (inf_nb_brok 16 (q_br q)) as HN; rewrite En in HN;
    unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
  - destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      cbv beta iota;
      (eapply call_EXLEN;
       [ unfold CB, Kq, Wq, cpend, br_initbits; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; aux_vac
       | bsimp; apply E3; lia
       | bsimp; lia
       | bsimp; lia
       | bsimp; intros j; rewrite E2; apply Hby
       | bsimp; exact Hleft
       | bsimp; reflexivity ]).
  - cbn [CostStep].
    eapply CB_qset_br; try assumption.
    unfold brok. repeat split; assumption.
Qed.

Lemma call_OS : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_OS ->
  CostStep q (inf_OS q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_OS; [constructor; assumption | exact Hm].
Qed.

Lemma cost_TIME :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_TIME ->
  CostStep q (inf_TIME q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_TIME. cbv zeta.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:En;
    pose proof (inf_nb_brok 32 (q_br q)) as HN; rewrite En in HN;
    unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
  - destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      cbv beta iota;
      (eapply call_OS;
       [ unfold CB, Kq, Wq, cpend, br_initbits; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; aux_vac
       | bsimp; apply E3; lia
       | bsimp; lia
       | bsimp; lia
       | bsimp; intros j; rewrite E2; apply Hby
       | bsimp; exact Hleft
       | bsimp; reflexivity ]).
  - cbn [CostStep].
    eapply CB_qset_br; try assumption.
    unfold brok. repeat split; assumption.
Qed.

Lemma call_TIME : forall q q1,
  CB q q1 -> 0 <= br_have (q_br q1) -> 0 <= br_bits (q_br q1) ->
  0 <= br_hold (q_br q1) -> (forall j, 0 <= br_in (q_br q1) j) ->
  0 <= o_left (q_ob q1) ->
  h_mode (s_hdr (q_st q1)) = M_TIME ->
  CostStep q (inf_TIME q1).
Proof.
  intros q q1 HCB H1 H2 H2h H2y H3 Hm. eapply CostStep_pre; [exact HCB|].
  destruct HCB as (_&_&_&_&_&_&C7&C8).
  apply cost_TIME; [constructor; assumption | exact Hm].
Qed.

Lemma cost_FLAGS :
  forall q, CEntry q -> h_mode (s_hdr (q_st q)) = M_FLAGS ->
  CostStep q (inf_FLAGS q).
Proof.
  intros q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_FLAGS. cbv zeta.
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:En;
    pose proof (inf_nb_brok 16 (q_br q)) as HN; rewrite En in HN;
    unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
  - destruct (negb (Z.eqb (Z.land (h_flags _) 255) Z_DEFLATED)).
    { cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
      rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply E3; lia).
      unfold CostAux. bsimp. aux_vac. }
    destruct (negb (Z.eqb (Z.land (h_flags _) 57344) 0)).
    { cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
      rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply E3; lia).
      unfold CostAux. bsimp. aux_vac. }
    destruct (negb (Z.eqb (Z.land (h_flags _) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap _) 4) 0));
      cbv beta iota;
      (eapply call_TIME;
       [ unfold CB, Kq, Wq, cpend, br_initbits; bsimp;
         rewrite !Hm; cbv beta iota;
         cb8; try lia;
         unfold CostAux; bsimp; aux_vac
       | bsimp; apply E3; lia
       | bsimp; lia
       | bsimp; lia
       | bsimp; intros j; rewrite E2; apply Hby
       | bsimp; exact Hleft
       | bsimp; reflexivity ]).
  - cbn [CostStep].
    eapply CB_qset_br; try assumption.
    unfold brok. repeat split; assumption.
Qed.

Lemma cost_HEAD :
  forall c q, CEntry q -> h_mode (s_hdr (q_st q)) = M_HEAD ->
  CostStep q (inf_HEAD c q).
Proof.
  intros c q CE Hm. pose proof CE as [Hh Hb Hho Hby Hleft Hl Ha].
  unfold inf_HEAD. cbv zeta.
  destruct (Z.eqb (h_wrap (s_hdr (q_st q))) 0).
  - (* raw: to TYPEDO *)
    eapply CostStep_pre with (q1 := qmode q M_TYPEDO).
    { unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
    apply cost_TYPEDO; [| right; bsimp; reflexivity].
    constructor; bsimp; try assumption.
    unfold CostAux. bsimp. aux_vac.
  - destruct (inf_nb 16 (q_br q)) as [b|b] eqn:En;
      pose proof (inf_nb_brok 16 (q_br q)) as HN; rewrite En in HN;
      unfold brok in HN; destruct HN as (E1&E2&E3&E4&E5).
    + destruct (negb (Z.eqb (Z.land (h_wrap _) 2) 0)
                && Z.eqb (br_hold b) 35615).
      { (* gzip magic: to FLAGS *)
        destruct (Z.eqb (w_wbits (s_win (q_st q))) 0); cbv beta iota;
          (cbn [CostStep]; unfold CB, Kq, Wq, cpend, br_initbits; bsimp;
           rewrite !Hm; cbv beta iota;
           cb8; try lia; try (apply E3; lia);
           unfold CostAux; bsimp; aux_vac). }
      destruct (Z.eqb (Z.land (h_wrap _) 1) 0
                || negb (Z.eqb ((Z.shiftl (br_bits_of 8 b) 8
                                 + Z.shiftr (br_hold b) 8) mod 31) 0)).
      { cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply E3; lia).
        unfold CostAux. bsimp. aux_vac. }
      destruct (negb (Z.eqb (br_bits_of 4 b) Z_DEFLATED)).
      { cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply E3; lia).
        unfold CostAux. bsimp. aux_vac. }
      pose proof (inf_nb_ok _ _ _ En) as Hok.
      destruct (Z.eqb (w_wbits (s_win (q_st q))) 0); cbv beta iota;
        (destruct (Z.ltb 15 _ || Z.ltb _ _); cbv beta iota;
         [ (* window-size bad *)
           cbn [CostStep]; unfold CB, Kq, Wq, cpend, br_dropbits; bsimp;
           rewrite !Hm; cbv beta iota;
           cb8; try lia; try (apply E3; lia);
           unfold CostAux; bsimp; aux_vac
         | (* to TYPE or DICTID *)
           destruct (Z.eqb (Z.land (br_hold (br_dropbits 4 b)) 512) 0);
           cbv beta iota;
           (cbn [CostStep];
            unfold CB, Kq, Wq, cpend, br_initbits, br_dropbits; bsimp;
            rewrite !Hm; cbv beta iota;
            cb8; try lia; try (apply E3; lia);
            unfold CostAux; bsimp; aux_vac) ]).
    + cbn [CostStep].
      eapply CB_qset_br; try assumption.
      unfold brok. repeat split; assumption.
Qed.

(* ==========================================================================
   12.  The fast node: the 258-rate output cost of [if_model].

   Mirrors the landed cmono walk ([StepPres.if_dolen_cmono] etc.) with a
   STRICT conclusion — every symbol spends at least its root code's bits
   — and couples it with [trip_facts]'s per-trip 258-byte write cap. *)

Lemma if_dolen_cost :
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
        8 * f_in s - f_bits s + c_bits (f_lcode c v)
          <= 8 * f_in s' - f_bits s'
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

Lemma if_body_cost :
  forall c s n,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    match if_body c s with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s - f_bits s + 1 <= 8 * f_in s' - f_bits s'
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
  pose proof (if_dolen_cost tbl_fuel c s0
                (Z.land (f_hold s0) (f_lmask c)) n
                Hlb Hdb Hlf Hdf Hlt Hdt
                ltac:(intros _; eexists; reflexivity)
                Hup (conj Hroot Hchain) Hv0 ltac:(lia) ltac:(lia)
                (or_introl Hge15)) as HD.
  destruct (if_dolen tbl_fuel c s0
              (f_lcode c (Z.land (f_hold s0) (f_lmask c))))
    as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I; lia.
Qed.

Lemma if_step_cost :
  forall c s n,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    match if_step c s with
    | IfCont s' | IfStop s' | IfEob s' | IfBad s' _ =>
        8 * f_in s - f_bits s + 1 <= 8 * f_in s' - f_bits s'
    | IfFuel => True
    end.
Proof.
  intros c s n Hwalk Hb. rewrite if_step_unfold.
  pose proof (if_body_cost c s n Hwalk Hb) as HB.
  destruct (if_body c s) as [s1|s1|s1 m|]; cbv beta iota in HB |- *;
    [destruct (if_guard c s1); exact HB | exact HB | exact HB | exact I].
Qed.

Lemma if_loop_cost :
  forall m c s n r,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    if_loop m c s = Some r ->
    match r with
    | IfStop s' | IfEob s' | IfBad s' _ =>
        f_out s' - f_out s
          <= 258 * ((8 * f_in s' - f_bits s') - (8 * f_in s - f_bits s))
    | IfCont _ => True
    | IfFuel => True
    end.
Proof.
  induction m as [|m IH]; intros c s n r Hwalk Hb H;
    [cbn [if_loop] in H; discriminate|].
  rewrite if_loop_S in H.
  pose proof (if_step_cost c s n Hwalk Hb) as HS.
  pose proof (if_step_bud c s n Hwalk Hb) as HT.
  destruct (if_step c s) as [s1|s1|s1|s1 m1|] eqn:ES.
  - destruct HT as (T1 & T2 & T3 & T4 & T5).
    pose proof (IH c s1 n r Hwalk T3 H) as HR.
    destruct r as [s'|s'|s'|s' m2|]; try exact I; lia.
  - injection H as H; subst r. cbv beta iota.
    destruct HT as (T1 & T2 & T3 & T4 & T5). lia.
  - injection H as H; subst r. cbv beta iota.
    destruct HT as (T1 & T2 & T3 & T4 & T5). lia.
  - injection H as H; subst r. cbv beta iota.
    destruct HT as (T1 & T2 & T3 & T4 & T5). lia.
  - injection H as H; subst r. cbv beta iota. exact I.
Qed.

Lemma if_model_cost :
  forall a,
    if_wf_lax a -> if_wf_tbl a ->
    a_avail_in a <= 4294967290 -> a_avail_out a <= 4294967295 ->
    match if_model a with
    | None => True
    | Some y =>
        y_out y - a_next_out a
          <= 258 * ((8 * a_avail_in a + a_bits a)
                    - (8 * y_avail_in y + y_bits y))
        /\ a_next_out a <= y_out y
        /\ y_out y + y_avail_out y = a_next_out a + a_avail_out a
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
  pose proof (if_loop_cost _ _ _ n r Hwalk Hb0 Heq) as HK.
  assert (HL0 : f_last (if_ctx a) = a_next_in a + (a_avail_in a - 5))
    by reflexivity.
  assert (HE0 : f_end (if_ctx a) = a_next_out a + (a_avail_out a - 257))
    by reflexivity.
  assert (HI0 : f_in (if_st0 a) = a_next_in a) by reflexivity.
  assert (HO0 : f_out (if_st0 a) = a_next_out a) by reflexivity.
  assert (HB0e : f_bits (if_st0 a) = a_bits a) by reflexivity.
  unfold if_model. cbv zeta. rewrite Heq.
  destruct r as [s'|s'|s'|s' m0|]; cbv beta iota in HK |- *;
    [exact I| | | |exact I];
    destruct HL as (L1 & L2 & L3 & L4 & L5 & L6);
    (unfold if_finish; cbv zeta;
     cbn [y_avail_in y_bits y_avail_out y_hold y_out];
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
     repeat split; try lia).
Qed.

(* ==========================================================================
   13.  LEN and its fallthroughs, under the sweep's two named residuals.

   [Hsel] is the slow-decode selected-entry contract: the root half is
   provable today (masked index + [if_wf_tbl]'s in-range width clause);
   the chained half rides the Q1 relativisation's NAMED OPEN residual
   [SubTblPointersBelowUsed] (InflateFast.v:663, port-draft in
   LcodeRelCheck.v) — the sub-table-pointer range fact.  Parked as a
   Section premise per R6 option (a), like [DynTblOk] itself.
   ========================================================================== *)

Section CostSweep.

Variable Hdyn : DynTblOk.

Variable Hsel : forall q h b2 nb,
    ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
    inf_decode sub_len (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
    1 <= nb
    /\ 0 <= c_val h
    /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 -> Z.land (c_op h) 64 = 0 ->
        3 <= c_val h
        /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258).

Lemma cost_LEN :
  forall q, ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
  CostStep q (inf_LEN q).
Proof.
  intros q HR Hm.
  pose proof HR as (HC & HM).
  pose proof HC as [Hpos Hb39 Hbytes Hho Hwin Hwnext Hwhave Hsane
                    Hlen0 Hinbud Hleftu Hlens Hbh Hbn Hbd Hamb].
  pose proof Hpos as (Hh & Hb & Hleft).
  assert (Hby : forall j, 0 <= br_in (q_br q) j)
    by (intros j; exact (proj1 (Hbytes j))).
  assert (HL : LenTblSide q)
    by (apply (rm_tblL q HM); left; exact Hm).
  destruct HL as (Htbl & Hlcs & Htds & Hlt2 & Hdt2 & Hlbnd & Hlb & Hdb & Hroot0).
  unfold inf_LEN. cbv zeta.
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)))
    eqn:Hgate.
  - (* fast path *)
    apply andb_prop in Hgate as [G1 G2].
    apply Z.leb_le in G1. apply Z.leb_le in G2.
    assert (Hlax : if_wf_lax (len_args q)).
    { split; [exact G1|]. split; [exact G2|].
      split; [cbn [len_args a_bits]; lia|].
      split; [exact Hlb|]. split; [exact Hdb|].
      split; [exact Hsane|].
      split; [exact Hwhave|]. split; [exact Hwnext|].
      split; [exact Hbytes|]. split; [exact Hwin|].
      split; [exact Hlt2|]. split; [exact Hdt2|]. exact Hlbnd. }
    assert (Hain : a_avail_in (len_args q) <= 4294967290)
      by (cbn [len_args a_avail_in]; lia).
    assert (Haout : a_avail_out (len_args q) <= 4294967295)
      by (cbn [len_args a_avail_out]; lia).
    pose proof (if_model_pres (len_args q) Hlax Htbl Hain Haout) as HP.
    pose proof (if_model_cost (len_args q) Hlax Htbl Hain Haout) as HK.
    change (if_model
              {| a_inbuf := br_in (q_br q);
                 a_next_in := br_next (q_br q);
                 a_avail_in := br_have (q_br q);
                 a_buf := o_buf (q_ob q);
                 a_next_out := o_put (q_ob q);
                 a_avail_out := o_left (q_ob q);
                 a_start := q_out q;
                 a_wsize := w_wsize (s_win (q_st q));
                 a_whave := w_whave (s_win (q_st q));
                 a_wnext := w_wnext (s_win (q_st q));
                 a_window := w_win (s_win (q_st q));
                 a_lcode := tbl_of (q_st q) (t_lencode (s_tab (q_st q)));
                 a_dcode := tbl_of (q_st q) (t_distcode (s_tab (q_st q)));
                 a_lenbits := t_lenbits (s_tab (q_st q));
                 a_distbits := t_distbits (s_tab (q_st q));
                 a_sane := t_sane (s_tab (q_st q));
                 a_hold := s_hold (q_st (q_restore q));
                 a_bits := s_bits (q_st (q_restore q)) |})
      with (if_model (len_args q)).
    destruct (if_model (len_args q)) as [y|] eqn:EM; [|exact I].
    cbn [len_args a_avail_in a_bits a_next_out a_avail_out] in HP, HK.
    destruct HP as (P1 & P2 & P3 & P4 & P5 & P6).
    destruct HK as (K1 & K2 & K3).
    cbv zeta.
    destruct (y_exit y).
    { (* ExLen: mode stays M_LEN *)
      cbn [CostStep]. cbv beta iota.
      match goal with
      | |- CB _ (match q_mode ?t with _ => _ end) =>
          assert (Em5 : q_mode t = M_LEN)
            by (unfold q_mode, q_restore, q_load; bsimp; exact Hm);
          rewrite Em5; cbv beta iota
      end.
      unfold CB, Kq, Wq, cpend, q_restore, q_load. bsimp.
      try rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. rewrite !Hm. aux_vac. }
    { (* ExType *)
      cbn [CostStep]. cbv beta iota.
      match goal with
      | |- CB _ (match q_mode ?t with _ => _ end) =>
          assert (Em5 : q_mode t = M_TYPE)
            by (unfold q_mode, q_restore, q_load; bsimp; reflexivity);
          rewrite Em5; cbv beta iota
      end.
      unfold CB, Kq, Wq, cpend, q_restore, q_load. bsimp.
      try rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
    { (* ExBad *)
      cbn [CostStep]. cbv beta iota.
      match goal with
      | |- CB _ (match q_mode ?t with _ => _ end) =>
          assert (Em5 : q_mode t = M_BAD)
            by (unfold q_mode, q_restore, q_load, qbad; bsimp; reflexivity);
          rewrite Em5; cbv beta iota
      end.
      unfold CB, Kq, Wq, cpend, q_restore, q_load. bsimp.
      try rewrite !Hm. cbv beta iota.
      cb8; try lia.
      unfold CostAux. bsimp. aux_vac. }
  - (* slow path *)
    pose proof (inf_decode_brok sub_len
                  (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                  (t_lenbits (s_tab (q_st q))) (q_br q)
                  (tbl_bits_nonneg _ _ Hamb)) as HD.
    destruct (inf_decode sub_len _ _ _) as [h b nb|b|] eqn:Ed; [| |exact I].
    + destruct HD as (Hnb0 & Ebud & Hin & Hhs & Hb2 & Hho2).
      destruct (Hsel q h b nb HR Hm Ed) as (Hnb1 & Hcv0 & Hval).
      destruct (Z.eqb (c_op h) 0) eqn:E0.
      * (* literal: to LIT, flag +1 paid by nb >= 1 *)
        cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
        rewrite !Hm. cbv beta iota.
        cb8; try lia; try (apply Hhs, Hh).
        unfold CostAux. bsimp. aux_vac.
      * destruct (negb (Z.eqb (Z.land (c_op h) 32) 0)) eqn:E32.
        { (* end of block: to TYPE *)
          cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
          rewrite !Hm. cbv beta iota.
          cb8; try lia; try (apply Hhs, Hh).
          unfold CostAux. bsimp. aux_vac. }
        destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)) eqn:E64.
        { (* invalid code: BAD *)
          cbn [CostStep]. unfold CB, Kq, Wq, cpend. bsimp.
          rewrite !Hm. cbv beta iota.
          cb8; try lia; try (apply Hhs, Hh).
          unfold CostAux. bsimp. aux_vac. }
        (* length base: to LENEXT, pend := c_val h <= 258 *)
        apply Z.eqb_neq in E0.
        apply Bool.negb_false_iff, Z.eqb_eq in E32.
        apply Bool.negb_false_iff, Z.eqb_eq in E64.
        destruct (Hval E0 E32 E64) as (Hv3 & Hv258).
        assert (H2e : 1 <= Z.shiftl 1 (Z.land (c_op h) 15)).
        { rewrite Z.shiftl_1_l.
          pose proof (land15_range (c_op h)) as Hl15.
          apply (Z.pow_le_mono_r 2 0 (Z.land (c_op h) 15)); lia. }
        eapply CostStep_pre with
          (q1 := qmode (qset_st
                   (qset_br (qset_st (qset_st q (set_back (q_st q) 0))
                      (set_length (set_back
                         (q_st (qset_st q (set_back (q_st q) 0))) (0 + nb))
                         (c_val h))) b)
                   (set_extra (q_st (qset_br (qset_st
                      (qset_st q (set_back (q_st q) 0))
                      (set_length (set_back
                         (q_st (qset_st q (set_back (q_st q) 0))) (0 + nb))
                         (c_val h))) b)) (Z.land (c_op h) 15))) M_LENEXT).
        { unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
          cb8; try lia; try (apply Hhs, Hh).
          unfold CostAux. bsimp.
          split.
          - intros _. pose proof (land15_range (c_op h)). split; lia.
          - intros [HXv|[HXv|HXv]]; discriminate. }
        apply cost_LENEXT.
        2: bsimp; reflexivity.
        2: bsimp; exact Hamb.
        constructor; bsimp; try assumption; try lia.
        { apply Hho2; assumption. }
        { intros j. rewrite Hin. apply Hby. }
        unfold CostAux. bsimp.
        split.
        { intros _. pose proof (land15_range (c_op h)). split; lia. }
        { intros [HXv|[HXv|HXv]]; discriminate. }
    + cbn [CostStep].
      destruct HD as (E1&E2&E3&E4&E5).
      unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
      cb8; try lia; try (apply E3; lia); try (apply E4; lia).
      unfold CostAux. bsimp. rewrite !Hm. aux_vac.
Qed.

Lemma cost_LEN_ :
  forall q, ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN_ ->
  CostStep q (inf_LEN_ q).
Proof.
  intros q HR Hm.
  pose proof HR as (HC & HM).
  pose proof HC as [Hpos Hb39 Hbytes Hho Hwin Hwnext Hwhave Hsane
                    Hlen0 Hinbud Hleftu Hlens Hbh Hbn Hbd Hamb].
  pose proof Hpos as (Hh & Hb & Hleft).
  assert (HRm : ReachSt (qmode q M_LEN)).
  { split.
    - constructor; bsimp; try assumption.
    - apply reach_mode_scc; [left; bsimp; reflexivity| | | | |].
      + pose proof (rm_tblL q HM (or_intror (or_introl Hm))) as HL.
        unfold LenTblSide in HL |- *.
        bsimp. exact HL.
      + (* (D') rm_tblpd at LEN_ transports to the LEN re-dispatch (s_tab framed) -- an earlier development run proposed cure *)
        pose proof (rm_tblpd q HM (or_intror (or_introl Hm))) as HT.
        unfold StepPres.TblPDSide, tbl_of in HT |- *. bsimp. exact HT.
      + pose proof (rm_bits14 q HM (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl Hm))))))) as HB.
        bsimp. exact HB.
      + pose proof (rm_tblwid q HM (or_intror (or_introl Hm))) as HW.
        unfold TblWidSide, tbl_of in HW |- *. bsimp. exact HW.
      + (* cand13 rm_dsub at LEN_ transports to the LEN re-dispatch (s_tab framed) *)
        pose proof (rm_dsub q HM (or_intror (or_introl Hm))) as HD.
        unfold StepReach.DistSubSide. unfold tbl_of in HD |- *. bsimp. exact HD. }
  unfold inf_LEN_.
  eapply CostStep_pre with (q1 := qmode q M_LEN).
  { unfold CB, Kq, Wq, cpend. bsimp. rewrite !Hm. cbv beta iota.
    cb8; try lia.
    unfold CostAux. bsimp. aux_vac. }
  apply cost_LEN; [exact HRm | bsimp; reflexivity].
Qed.

(* ==========================================================================
   14.  The dispatch, under the THIRD parked leaf: the TABLE-chain cost
        arms (discharge route: mirror of [pres_TABLE]/[pres_LENLENS]/
        [pres_CODELENS] with the [CB] conclusion — mechanical but large;
        their fallthrough tail consumes [cost_LEN_], which is Qed above).
   ========================================================================== *)

Variable Hcost_tbl : forall c q,
    ReachSt q -> CostAux (q_st q) ->
    (h_mode (s_hdr (q_st q)) = M_TABLE -> CostStep q (inf_TABLE c q))
    /\ (h_mode (s_hdr (q_st q)) = M_LENLENS -> CostStep q (inf_LENLENS c q))
    /\ (h_mode (s_hdr (q_st q)) = M_CODELENS -> CostStep q (inf_CODELENS c q)).

Lemma centry_of_reach :
  forall q, ReachSt q -> CostAux (q_st q) -> CEntry q.
Proof.
  intros q (HC & HM) Ha.
  pose proof HC as [Hpos Hb39 Hbytes Hho Hwin Hwnext Hwhave Hsane
                    Hlen0 Hinbud Hleftu Hlens Hbh Hbn Hbd Hamb].
  pose proof Hpos as (Hh & Hb & Hleft).
  constructor; try assumption.
  intros j. exact (proj1 (Hbytes j)).
Qed.

Theorem cost_step :
  forall c q, ReachSt q -> CostAux (q_st q) -> CostStep q (inf_step c q).
Proof.
  intros c q HR Ha.
  pose proof HR as (HC & HM).
  pose proof (centry_of_reach q HR Ha) as CE.
  pose proof HC as [Hpos Hb39 Hbytes Hho Hwin Hwnext Hwhave Hsane
                    Hlen0 Hinbud Hleftu Hlens Hbh Hbn Hbd Hamb].
  unfold inf_step.
  destruct (q_mode q) eqn:Hm; unfold q_mode in Hm.
  - exact (cost_HEAD c q CE Hm).
  - exact (cost_FLAGS q CE Hm).
  - exact (cost_TIME q CE Hm).
  - exact (cost_OS q CE Hm).
  - exact (cost_EXLEN q CE Hm).
  - exact (cost_EXTRA q CE Hm).
  - exact (cost_NAME q CE Hm).
  - exact (cost_COMMENT q CE Hm).
  - exact (cost_HCRC q CE Hm).
  - exact (cost_DICTID c q CE Hm).
  - exact (cost_DICT c q CE Hm).
  - exact (cost_TYPE c q CE Hm).
  - exact (cost_TYPEDO c q CE (or_intror Hm)).
  - exact (cost_STORED c q CE Hm).
  - exact (cost_COPY_ q CE Hm).
  - exact (cost_COPY q CE Hm).
  - exact (proj1 (Hcost_tbl c q HR Ha) Hm).
  - exact (proj1 (proj2 (Hcost_tbl c q HR Ha)) Hm).
  - exact (proj2 (proj2 (Hcost_tbl c q HR Ha)) Hm).
  - exact (cost_LEN_ q HR Hm).
  - exact (cost_LEN q HR Hm).
  - apply cost_LENEXT; [exact CE | exact Hm | exact Hamb].
  - apply cost_DIST; [exact CE | exact Hm | exact Hamb].
  - apply cost_DISTEXT; [exact CE | exact Hm |].
    exact (proj1 (rm_extra q HM (or_intror Hm))).
  - apply cost_MATCH; [exact CE | exact Hm |].
    exact (proj2 Ha (or_intror (or_intror Hm))).
  - exact (cost_LIT q CE Hm).
  - exact (cost_CHECK q CE Hm).
  - exact (cost_LENGTH q CE Hm).
  - exact (cost_DONE q CE).
  - exact (cost_BAD q CE).
  - exact (cost_MEM q CE).
  - exact (cost_SYNC q CE).
Qed.

(** The loop composition: [CB] from the entry to the exit payload, with
    ReachSt threaded by [step_pres]. *)
Lemma cost_loop :
  forall n c q r,
    ReachSt q -> CostAux (q_st q) ->
    inf_loop n c q = Some r ->
    match r with
    | InfLeave q' => CB q q'
    | InfRet q' rr =>
        CB q q'
        /\ exists q0, ReachSt q0 /\ inf_step c q0 = InfRet q' rr
    | _ => True
    end.
Proof.
  induction n as [|n IH]; intros c q r HR Ha H;
    [cbn [inf_loop] in H; discriminate|].
  rewrite inf_loop_S in H.
  pose proof (cost_step c q HR Ha) as HS.
  pose proof (step_pres Hdyn c q HR) as HP.
  destruct (inf_step c q) as [q1|q1|q1 r0|m0|] eqn:ES.
  - cbv beta iota in HP. cbn [CostStep] in HS.
    pose proof (IH c q1 r HP (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
                  (proj2 HS))))))) H) as HRc.
    destruct r as [q'|q'|q' rr|m1|]; try exact I.
    + eapply CB_trans; eauto.
    + destruct HRc as (HCB & Hprov).
      split; [eapply CB_trans; eauto | exact Hprov].
  - injection H as <-. cbn [CostStep] in HS. exact HS.
  - injection H as <-. cbn [CostStep] in HS.
    split; [exact HS |].
    exists q. split; [exact HR | exact ES].
  - injection H as <-. exact I.
  - injection H as <-. exact I.
Qed.

(* ==========================================================================
   15.  Leave/entry transport and the [Hcall] discharge.
   ========================================================================== *)

Lemma uw_pres :
  forall al fr s o cp s',
    uw al fr s o cp = Some s' ->
    h_mode (s_hdr s') = h_mode (s_hdr s)
    /\ u_length (s_cur s') = u_length (s_cur s)
    /\ u_extra (s_cur s') = u_extra (s_cur s)
    /\ s_bits s' = s_bits s
    /\ s_hold s' = s_hold s.
Proof.
  intros al fr s o cp s' H. unfold uw in H. cbv zeta in H.
  destruct (if w_alloc (s_win s) then Some (w_win (s_win s))
            else if al then Some fr else None); [|discriminate].
  destruct (Z.leb _ cp).
  - injection H as <-. bsimp.
    cbn [set_whave set_wnext set_wsize set_win set_alloc
         s_hdr s_cur s_bits s_hold u_length u_extra h_mode].
    repeat split; reflexivity.
  - destruct (negb (Z.eqb _ 0)); injection H as <-;
      cbn [set_whave set_wnext set_wsize set_win set_alloc
           s_hdr s_cur s_bits s_hold u_length u_extra h_mode];
      repeat split; reflexivity.
Qed.

Lemma CostAux_transport :
  forall s s',
    h_mode (s_hdr s') = h_mode (s_hdr s) ->
    u_length (s_cur s') = u_length (s_cur s) ->
    u_extra (s_cur s') = u_extra (s_cur s) ->
    CostAux s -> CostAux s'.
Proof.
  intros s s' E1 E2 E3 HA. unfold CostAux in HA |- *.
  rewrite E1, E2, E3. exact HA.
Qed.

Lemma inf_leave_tail_facts :
  forall c q0 wrote,
    br_have (q_br (fst (inf_leave_tail c q0 wrote))) = br_have (q_br q0)
    /\ s_bits (q_st (fst (inf_leave_tail c q0 wrote))) = s_bits (q_st q0)
    /\ o_put (q_ob (fst (inf_leave_tail c q0 wrote))) = o_put (q_ob q0)
    /\ o_left (q_ob (fst (inf_leave_tail c q0 wrote))) = o_left (q_ob q0)
    /\ u_length (s_cur (q_st (fst (inf_leave_tail c q0 wrote))))
       = u_length (s_cur (q_st q0))
    /\ u_extra (s_cur (q_st (fst (inf_leave_tail c q0 wrote))))
       = u_extra (s_cur (q_st q0))
    /\ h_mode (s_hdr (q_st (fst (inf_leave_tail c q0 wrote))))
       = h_mode (s_hdr (q_st q0)).
Proof.
  intros c q0 wrote. unfold inf_leave_tail. cbv zeta.
  destruct (negb _ && negb _); cbn [fst]; bsimp;
    repeat split; reflexivity.
Qed.

Lemma inf_leave_facts :
  forall c q',
    br_have (q_br (fst (inf_leave c q'))) = br_have (q_br q')
    /\ s_bits (q_st (fst (inf_leave c q'))) = br_bits (q_br q')
    /\ o_put (q_ob (fst (inf_leave c q'))) = o_put (q_ob q')
    /\ o_left (q_ob (fst (inf_leave c q'))) = o_left (q_ob q')
    /\ u_length (s_cur (q_st (fst (inf_leave c q'))))
       = u_length (s_cur (q_st q'))
    /\ (h_mode (s_hdr (q_st (fst (inf_leave c q'))))
        = h_mode (s_hdr (q_st q'))
        \/ h_mode (s_hdr (q_st (fst (inf_leave c q')))) = M_MEM)
    /\ (CostAux (q_st q') -> CostAux (q_st (fst (inf_leave c q')))).
Proof.
  intros c q'. unfold inf_leave. cbv zeta.
  assert (Hrb : br_have (q_br (q_restore q')) = br_have (q_br q'))
    by reflexivity.
  assert (Hrbits : s_bits (q_st (q_restore q')) = br_bits (q_br q'))
    by reflexivity.
  assert (Hrmode : h_mode (s_hdr (q_st (q_restore q')))
                   = h_mode (s_hdr (q_st q'))) by reflexivity.
  assert (Hrlen : u_length (s_cur (q_st (q_restore q')))
                  = u_length (s_cur (q_st q'))) by reflexivity.
  assert (Hrext : u_extra (s_cur (q_st (q_restore q')))
                  = u_extra (s_cur (q_st q'))) by reflexivity.
  destruct (negb _ || _).
  - destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q'))
                 (q_ob (q_restore q'))
                 (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
      as [st'|] eqn:EU.
    + apply uw_pres in EU.
      destruct EU as (U1 & U2 & U3 & U4 & U5).
      pose proof (inf_leave_tail_facts c (qset_st (q_restore q') st')
                    (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
        as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
      cbn [qset_st q_br q_ob q_st] in T1, T2, T3, T4, T5, T6, T7.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * rewrite T1. exact Hrb.
      * rewrite T2, U4. exact Hrbits.
      * exact T3.
      * exact T4.
      * rewrite T5, U2. exact Hrlen.
      * left. rewrite T7, U1. exact Hrmode.
      * intros HA.
        eapply CostAux_transport;
          [rewrite T7, U1; exact Hrmode
          | rewrite T5, U2; exact Hrlen
          | rewrite T6, U3; exact Hrext
          | exact HA].
    + cbn [fst]. bsimp.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * right. reflexivity.
      * intros _. unfold CostAux. bsimp. aux_vac.
  - pose proof (inf_leave_tail_facts c (q_restore q')
                  (q_out (q_restore q') - o_left (q_ob (q_restore q'))))
      as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + rewrite T1. exact Hrb.
    + rewrite T2. exact Hrbits.
    + exact T3.
    + exact T4.
    + rewrite T5. exact Hrlen.
    + left. rewrite T7. exact Hrmode.
    + intros HA.
      eapply CostAux_transport;
        [rewrite T7; exact Hrmode
        | rewrite T5; exact Hrlen
        | rewrite T6; exact Hrext
        | exact HA].
Qed.

(** Entry transport into [inf_st0] (the M_TYPE -> M_TYPEDO rewrite is
    between two uncounted modes). *)
Lemma st0_facts :
  forall a,
    br_have (q_br (inf_st0 a)) = g_avail_in a
    /\ br_bits (q_br (inf_st0 a)) = s_bits (g_st a)
    /\ o_put (q_ob (inf_st0 a)) = g_next_out a
    /\ o_left (q_ob (inf_st0 a)) = g_avail_out a
    /\ cpend (q_st (inf_st0 a)) = cpend (g_st a)
    /\ (CostAux (g_st a) -> CostAux (q_st (inf_st0 a))).
Proof.
  intros a. unfold inf_st0.
  destruct (h_mode (s_hdr (g_st a))) eqn:E; cbv beta iota;
    (refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
     [ reflexivity | bsimp; reflexivity | reflexivity | reflexivity
     | unfold cpend; bsimp; rewrite ?E; reflexivity
     | intros HA;
       first [ exact HA
             | unfold CostAux; bsimp;
               split; [intros HXv; discriminate
                      | intros [HXv|[HXv|HXv]]; discriminate] ] ]).
Qed.

(** The same ret-code census the re-entry lap owes (an earlier development run ASK 3):
    at assembly time ONE lemma discharges both uses. *)
Variable Hret : forall c q0 q1 rr,
    ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK.

Lemma cpend_eq_transport :
  forall s s',
    h_mode (s_hdr s') = h_mode (s_hdr s) ->
    u_length (s_cur s') = u_length (s_cur s) ->
    cpend s' = cpend s.
Proof.
  intros s s' E1 E2. unfold cpend. rewrite E1, E2. reflexivity.
Qed.

(** The [GtDecPump.Hcall] discharge. *)
Theorem call_cost :
  forall a,
    ReachSt (inf_st0 a) ->
    CostAux (g_st a) ->
    g_state_null a = false -> g_out_null a = false -> g_in_null a = false ->
    g_next_out a = 0 ->
    match inflate_model a with
    | None => True
    | Some r =>
        r_ret r = Z_OK ->
        8 * br_have (q_br (r_q r)) + s_bits (q_st (r_q r))
          <= 8 * g_avail_in a + s_bits (g_st a)
        /\ o_put (q_ob (r_q r)) + cpend (q_st (r_q r))
             + 258 * (8 * br_have (q_br (r_q r)) + s_bits (q_st (r_q r)))
           <= cpend (g_st a)
             + 258 * (8 * g_avail_in a + s_bits (g_st a))
        /\ 0 <= o_put (q_ob (r_q r))
        /\ o_put (q_ob (r_q r)) + o_left (q_ob (r_q r)) = g_avail_out a
        /\ 0 <= br_have (q_br (r_q r))
        /\ 0 <= s_bits (q_st (r_q r))
        /\ 0 <= cpend (q_st (r_q r))
        /\ cpend (q_st (r_q r)) <= 258
        /\ CostAux (q_st (r_q r))
    end.
Proof.
  intros a HR Haux Hn1 Hn2 Hn3 Hno.
  destruct (st0_facts a) as (S1 & S2 & S3 & S4 & S5 & S6).
  unfold inflate_model.
  rewrite Hn1, Hn2, Hn3. cbv beta iota.
  destruct (inf_loop (Inflate.inf_fuel (inf_st0 a)) (inf_ctx a) (inf_st0 a))
    as [ri|] eqn:EL; [|exact I].
  pose proof (cost_loop _ _ _ _ HR (S6 Haux) EL) as HCL.
  destruct ri as [q1|q1|q1 rr|m0|]; try exact I.
  - (* InfLeave *)
    destruct HCL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct (inf_leave (inf_ctx a) q1) as [q2 rr] eqn:ELV.
    pose proof (inf_leave_facts (inf_ctx a) q1) as HF.
    rewrite ELV in HF. cbn [fst] in HF.
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    intros _.
    cbn [r_q r_ret].
    assert (Hc2n : 0 <= cpend (q_st q2) /\ cpend (q_st q2) <= 258).
    { apply cpend_le_258; [exact (F7 C8) |].
      rewrite F5. exact C7. }
    assert (Hc2r : cpend (q_st q2) <= cpend (q_st q1)).
    { destruct F6 as [F6|F6].
      - rewrite (cpend_eq_transport (q_st q1) (q_st q2) F6 F5). lia.
      - unfold cpend at 1. rewrite F6.
        pose proof (cpend_le_258 (q_st q1) C8 C7). lia. }
    unfold Kq in C2. unfold Wq in C1, C2.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ _)))))))).
    + rewrite F1, F2. lia.
    + rewrite F1, F2, F3. lia.
    + rewrite F3. lia.
    + rewrite F3, F4. lia.
    + rewrite F1. lia.
    + rewrite F2. lia.
    + lia.
    + lia.
    + exact (F7 C8).
  - (* InfRet: killed by the ret census *)
    destruct HCL as (_ & (q0 & HR0 & E0)).
    cbn [r_ret r_q].
    intros Hok. exfalso.
    exact (Hret _ _ _ _ HR0 E0 Hok).
Qed.

End CostSweep.

(* ==========================================================================
   16.  The faces, with the FULL leaf census in one type: what remains
        between this tree and the two decode faces is exactly the six
        premises below (three shared with the an earlier development run re-entry lap,
        three of this lane's parked leaves — see each Variable's header).
   ========================================================================== *)

Theorem decode_raw_modulo :
  forall (Hdyn : DynTblOk)
         (Hsel : forall q h b2 nb,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             inf_decode sub_len
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
             1 <= nb
             /\ 0 <= c_val h
             /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 ->
                 Z.land (c_op h) 64 = 0 ->
                 3 <= c_val h
                 /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258))
         (Htbl : forall c q,
             ReachSt q -> CostAux (q_st q) ->
             (h_mode (s_hdr (q_st q)) = M_TABLE ->
                CostStep q (inf_TABLE c q))
             /\ (h_mode (s_hdr (q_st q)) = M_LENLENS ->
                CostStep q (inf_LENLENS c q))
             /\ (h_mode (s_hdr (q_st q)) = M_CODELENS ->
                CostStep q (inf_CODELENS c q)))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_raw.
Proof.
  intros Hdyn Hsel Htbl Hret Hreenter Hshape.
  exact (decode_raw_face Hdyn Hreenter Hshape Hret
           (call_cost Hdyn Hsel Htbl Hret)).
Qed.

Theorem decode_auto_modulo :
  forall (Hdyn : DynTblOk)
         (Hsel : forall q h b2 nb,
             ReachSt q -> h_mode (s_hdr (q_st q)) = M_LEN ->
             inf_decode sub_len
               (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
               (t_lenbits (s_tab (q_st q))) (q_br q) = DecOk h b2 nb ->
             1 <= nb
             /\ 0 <= c_val h
             /\ (c_op h <> 0 -> Z.land (c_op h) 32 = 0 ->
                 Z.land (c_op h) 64 = 0 ->
                 3 <= c_val h
                 /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258))
         (Htbl : forall c q,
             ReachSt q -> CostAux (q_st q) ->
             (h_mode (s_hdr (q_st q)) = M_TABLE ->
                CostStep q (inf_TABLE c q))
             /\ (h_mode (s_hdr (q_st q)) = M_LENLENS ->
                CostStep q (inf_LENLENS c q))
             /\ (h_mode (s_hdr (q_st q)) = M_CODELENS ->
                CostStep q (inf_CODELENS c q)))
         (Hret : forall c q0 q1 rr,
             ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK)
         (Hreenter : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             (forall j, 0 <= n_wfresh c j < 256) ->
             EntryOk (q_st (fst (inf_leave c q1)))
                     (q_z (fst (inf_leave c q1))))
         (Hshape : forall c q0 q1,
             ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
             0 <= br_have (q_br (fst (inf_leave c q1)))
             /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
                 br_have (q_br (fst (inf_leave c q1))) = 0
                 \/ o_left (q_ob (fst (inf_leave c q1))) = 0)),
    ZRepro_Decode_auto.
Proof.
  intros Hdyn Hsel Htbl Hret Hreenter Hshape.
  exact (decode_auto_face Hdyn Hreenter Hshape Hret
           (call_cost Hdyn Hsel Htbl Hret)).
Qed.
