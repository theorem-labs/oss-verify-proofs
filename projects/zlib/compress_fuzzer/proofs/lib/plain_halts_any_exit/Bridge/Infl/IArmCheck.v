(** * Bridge.Infl.IArmCheck — pair I11 of PAIRS.md: CHECK, LENGTH and DONE.

    CHECK reads the Adler-32 trailer, counts this call's output into [total_out]/[total],
    folds it into the check value (S5's [iadler32_upd] against RT's [adler32_z]:
    [BrAdler.br_iadler32_upd], with the check value canonical since HEAD set it to 1),
    restarts the [out] snapshot, compares, and falls through LENGTH (no body: [flags = 0])
    to DONE, which leaves with [Z_STREAM_END] in the [ifin] state.

    The two Adler-32 spellings agree only on bytes (computed: S5's
    [iadler32_upd 1 [200000;3] = 450825585], RT's [adler32_z 1 false [200000;3] =
    450825555]), so CHECK needs the written output to be bytes: [arm_CHECK_ok_x] takes it as
    a hypothesis, and [icore]'s last conjunct (RT's output buffer holds bytes) supplies it. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtAdlerChunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields BrAdler.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmHeadKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* Values                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma land_bound : forall x m n, 0 <= n -> 0 <= m < 2 ^ n -> 0 <= Z.land x m < 2 ^ n.
Proof.
  intros x m n Hn Hm.
  assert (E : Z.land m (Z.ones n) = m) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- E, Z.land_assoc, Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(** S5's [ZSWAP32] wraps a sum of four byte lanes, below [2^32], to 64 bits. *)
Lemma zswap_eq : forall x, IS.ZSWAP32 x = RI.zswap32 x.
Proof.
  intros x. unfold IS.ZSWAP32, RI.zswap32.
  pose proof (land_bound (Z.shiftr x 24) 255 8 ltac:(lia) ltac:(cbn; lia)) as H1.
  pose proof (land_bound (Z.shiftr x 8) 65280 16 ltac:(lia) ltac:(cbn; lia)) as H2.
  pose proof (land_bound x 65280 16 ltac:(lia) ltac:(cbn; lia)) as H3.
  pose proof (land_bound x 255 8 ltac:(lia) ltac:(cbn; lia)) as H4.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
  change (2 ^ 24) with 16777216. apply wrap64_id. lia.
Qed.

Lemma adwf1 : GtAdlerChunk.AdWf 1.
Proof.
  unfold GtAdlerChunk.AdWf, Checksum.ADLER_BASE.
  change (Z.land 1 65535) with 1. change (Z.land (Z.shiftr 1 16) 65535) with 0. lia.
Qed.

(** The check value CHECK folds in: S5's [iadler32_upd] over its output array against RT's
    [adler32_z] over its output, on the [n = put] bytes written this call. *)
Lemma check_slice_eq : forall c q n,
  arr_rel (IS.ic_outbuf c) (RI.o_buf (RI.q_ob q)) 0 n -> n = RI.o_put (RI.q_ob q) -> 0 <= n ->
  (forall i, 0 <= i < n -> 0 <= RI.o_buf (RI.q_ob q) i < 256) ->
  IS.iadler32_upd 1 (arr_slice (IS.ic_outbuf c) (n - n) n)
  = RI.upd_check 0 1 (RI.ob_slice (RI.q_ob q) (RI.o_put (RI.q_ob q) - n) n).
Proof.
  intros c q n Hrel Hn Hn0 Hob.
  unfold RI.upd_check. change (0 =? 0) with true. cbv beta iota.
  rewrite <- Hn, Z.sub_diag. unfold RI.ob_slice.
  rewrite (arr_rel_slice _ _ 0 n 0 n Hrel) by lia.
  apply BrAdler.br_iadler32_upd; [exact adwf1|].
  intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq in Hk.
  apply Hob. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* LENGTH (no body for a zlib stream) and DONE                               *)
(* ------------------------------------------------------------------------- *)

Lemma s5_length_done : forall S C R, IS.is_flags S = 0 ->
  IA.arm_LENGTH (IS.mkW S C R)
  = IS.ALeave (IS.mkW (IS.iset_mode S IS.DONE) C (IS.irset_ret R Z_STREAM_END)).
Proof.
  intros S C R Hf. unfold IA.arm_LENGTH. s5run. rewrite Hf.
  change (negb (0 =? 0)) with false. rewrite andb_false_r. cbv beta iota.
  s5run. unfold IA.arm_DONE. s5run. reflexivity.
Qed.

Lemma rt_length_done : forall q, RI.h_flags (RI.s_hdr (RI.q_st q)) = 0 ->
  RI.inf_LENGTH q = RI.inf_DONE (RI.qmode q RI.M_DONE).
Proof.
  intros q Hf. unfold RI.inf_LENGTH. cbv zeta. rewrite Hf.
  change (negb (0 =? 0)) with false. rewrite andb_false_r. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* The state the trip leaves in                                              *)
(* ------------------------------------------------------------------------- *)

Ltac check_post_tac s c r Hb1 Hin1 :=
  destruct (brel_rng _ _ Hb1) as (Hbr1 & Hhr1 & Hn1 & Hv1 & Hnv1);
  unfold ifin, icore, iw_rel, ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel, zstrm_rel in *;
  cbv zeta in *; cbn [IS.w_s IS.w_c IS.w_r] in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  autorewrite with s5i_mode s5i_check s5i_total s5ic_adler s5ic_total_out s5ir_ret s5ir_bits s5ir_hold
                   s5ir_out;
  cbn [setbr IS.ir_next IS.ir_have IS.ir_put IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out IS.ir_ret];
  rt_cbn; rewrite ?Hin1;
  match goal with
  | Ht : IS.is_total s = 0, Hto : IS.ic_total_out c = 0 |- _ => rewrite Ht, Hto
  end;
  rewrite !Z.add_0_l, (wrap64_id (IS.ir_put r)) by lia;
  conjs;
  try solve [ assumption | reflexivity | lia ].

(** After LENGTH and DONE, when CHECK folded output into the check value. *)
Lemma check_post_u : forall s c r q b ck,
  icore (IS.mkW s c r) q -> brel (wbr (IS.mkW s c r) b) b ->
  RB.br_in b = RB.br_in (RI.q_br q) ->
  RB.br_next b + RB.br_have b = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q) ->
  ifin (IS.mkW (IS.iset_mode (IS.iset_mode (IS.iset_check
                   (IS.iset_total s (wrap64 (IS.is_total s + IS.ir_put r))) ck) IS.LENGTH) IS.DONE)
               (IS.icset_adler (IS.icset_total_out c (wrap64 (IS.ic_total_out c + IS.ir_put r))) ck)
               (IS.irset_ret (IS.irset_bits (IS.irset_hold
                   (IS.irset_out (IS.irset_out (setbr r b) (IS.ir_put r)) (IS.ir_left r)) 0) 0) Z_STREAM_END))
       (RI.qset_ret (RI.qmode (RI.qmode (RI.qset_br (RI.qset_out (RI.qcheck
           (RI.qset_st (RI.qset_z (RI.qset_br q b) (RI.zset_tout (RI.q_z q) (RI.z_tout (RI.q_z q) + IS.ir_put r)))
                       (RI.set_total (RI.q_st q) (RI.h_total (RI.s_hdr (RI.q_st q)) + IS.ir_put r))) ck)
           (RI.o_left (RI.q_ob q))) (RB.br_initbits b)) RI.M_LENGTH) RI.M_DONE) RBa.Z_STREAM_END).
Proof. intros s c r q b ck Hc Hb1 Hin1 Hsum1. check_post_tac s c r Hb1 Hin1. Qed.

(** The same when nothing was written ([put = 0]): the check value is not touched. *)
Lemma check_post_n : forall s c r q b,
  icore (IS.mkW s c r) q -> brel (wbr (IS.mkW s c r) b) b ->
  RB.br_in b = RB.br_in (RI.q_br q) ->
  RB.br_next b + RB.br_have b = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q) ->
  ifin (IS.mkW (IS.iset_mode (IS.iset_mode
                   (IS.iset_total s (wrap64 (IS.is_total s + IS.ir_put r))) IS.LENGTH) IS.DONE)
               (IS.icset_total_out c (wrap64 (IS.ic_total_out c + IS.ir_put r)))
               (IS.irset_ret (IS.irset_bits (IS.irset_hold
                   (IS.irset_out (IS.irset_out (setbr r b) (IS.ir_put r)) (IS.ir_left r)) 0) 0) Z_STREAM_END))
       (RI.qset_ret (RI.qmode (RI.qmode (RI.qset_br (RI.qset_out
           (RI.qset_st (RI.qset_z (RI.qset_br q b) (RI.zset_tout (RI.q_z q) (RI.z_tout (RI.q_z q) + IS.ir_put r)))
                       (RI.set_total (RI.q_st q) (RI.h_total (RI.s_hdr (RI.q_st q)) + IS.ir_put r)))
           (RI.o_left (RI.q_ob q))) (RB.br_initbits b)) RI.M_LENGTH) RI.M_DONE) RBa.Z_STREAM_END).
Proof. intros s c r q b Hc Hb1 Hin1 Hsum1. check_post_tac s c r Hb1 Hin1. Qed.

(* ------------------------------------------------------------------------- *)
(* The trip                                                                  *)
(* ------------------------------------------------------------------------- *)

(** [arm_CHECK_ok] plus the hypothesis that the written output is bytes (NEEDS.md H1). *)
Lemma arm_CHECK_ok_x : forall w q,
  inv w q -> RI.q_mode q = RI.M_CHECK ->
  (forall i, 0 <= i < IS.ir_put (IS.w_r w) -> 0 <= RI.o_buf (RI.q_ob q) i < 256) ->
  step_ok (IA.arm_CHECK w) (RI.inf_CHECK q).
Proof.
  intros w q [Hc _] Hm Hob.
  pose proof (icore_brel _ _ Hc) as Hb.
  destruct (icore_hd _ _ Hc) as (Hret & Hwr & _ & _ & Hswr & _).
  destruct w as [s c r]. cbn [IS.w_s IS.w_c IS.w_r] in Hswr, Hob.
  unfold RI.inf_CHECK. cbv zeta. rewrite Hwr. change (5 =? 0) with false. cbv beta iota.
  (* NEEDBITS(32); its input-exhaustion leave keeps [q_ret = Z_OK] *)
  destruct (RI.inf_nb 32 (RI.q_br q)) as [b|b] eqn:Hnb;
    [| cbn [step_ok RI.q_ret RI.qset_br]; rewrite Hret; intros H; exfalso; exact (ok_ne_end H)].
  destruct (needbits_sim _ _ b 32 Hb ltac:(lia) Hnb) as (E1 & Hb1 & H32 & Hin1 & Hsum1).
  rewrite wbr_mkW in E1.
  unfold IA.arm_CHECK.
  s5run.
  rewrite Hswr. change (negb (5 =? 0)) with true. cbv beta iota.
  s5run.
  rewrite (abind_ARun _ _ _ _ _ E1). cbv beta.
  s5run.
  (* facts read off icore *)
  pose proof Hc as Hc'.
  unfold icore, iw_rel, ist_core_rel, hdr_rel, zstrm_rel in Hc'. cbv zeta in Hc'.
  cbn [IS.w_s IS.w_c IS.w_r] in Hc'.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  destruct (icore_past_head _ _ Hc ltac:(rewrite Hm; discriminate)) as (Hfl & Hck & Hrfl & Hrck).
  cbn [IS.w_s] in Hfl, Hck.
  (* [out - left] is [put] on both sides *)
  cbn [setbr IS.ir_next IS.ir_have IS.ir_put IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out IS.ir_ret].
  assert (Hout : wrap32 (IS.ir_out r - IS.ir_left r) = IS.ir_put r) by (rewrite wrap32_id; lia).
  assert (Hwr2 : RI.q_out q - RI.o_left (RI.q_ob q) = IS.ir_put r) by lia.
  rewrite Hout, Hwr2.
  autorewrite with s5i_total. rewrite ?Hswr, ?Hfl, ?Hck, ?Hrfl, ?Hrck.
  change (negb (Z.land 5 4 =? 0)) with true. cbn [andb].
  destruct (IS.ir_put r =? 0) eqn:Hp0; cbn [negb].
  2:{
    (* bytes were written: fold them into the check value *)
    rewrite ab_assoc. cbn [IS.abind IS.w_c IS.w_r].
    s5run.
    rt_cbn.
    autorewrite with s5ic_total_out s5ir_out s5i_check s5i_total.
    cbn [setbr IS.ir_next IS.ir_have IS.ir_put IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out IS.ir_ret].
    unfold IA.UPDATE_CHECK_bytes. autorewrite with s5i_total. rewrite Hfl, Hswr.
    change (negb (0 =? 0)) with false. change (0 =? 0) with true. cbv beta iota.
    rewrite (check_slice_eq c q (IS.ir_put r)) by (assumption || lia).
    remember (RI.upd_check 0 1 (RI.ob_slice (RI.q_ob q) (RI.o_put (RI.q_ob q) - IS.ir_put r) (IS.ir_put r)))
      as ck eqn:Eck.
    (* the compare; a mismatch goes to BAD *)
    rewrite zswap_eq. change (negb (Z.land 5 4 =? 0)) with true. cbn [andb].
    destruct (RI.zswap32 (RB.br_hold b) =? ck) eqn:Hcmp; cbn [negb];
      [| cbn [step_ok]; intros Hbad; exfalso; apply Hbad; reflexivity].
    s5run.
    rewrite s5_length_done by (autorewrite with s5i_mode s5i_check s5i_total; exact Hfl).
    rewrite rt_length_done by (rt_cbn; exact Hrfl).
    unfold RI.inf_DONE. cbn [step_ok]. intros _. eexists. split; [reflexivity|].
    apply check_post_u; assumption.
  }
  (* nothing written: the check value stays 1 *)
  s5run. rt_cbn.
  autorewrite with s5ir_out s5i_total.
  cbn [setbr IS.ir_next IS.ir_have IS.ir_put IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out IS.ir_ret].
  rewrite Hfl, Hswr, Hck, Hrck.
  change (negb (0 =? 0)) with false. change (0 =? 0) with true. cbv beta iota.
  rewrite zswap_eq. change (negb (Z.land 5 4 =? 0)) with true. cbn [andb].
  destruct (RI.zswap32 (RB.br_hold b) =? 1) eqn:Hcmp; cbn [negb];
    [| cbn [step_ok]; intros Hbad; exfalso; apply Hbad; reflexivity].
  s5run.
  rewrite s5_length_done by (autorewrite with s5i_mode s5i_total; exact Hfl).
  rewrite rt_length_done by (rt_cbn; exact Hrfl).
  unfold RI.inf_DONE. cbn [step_ok]. intros _. eexists. split; [reflexivity|].
  apply check_post_n; assumption.
Qed.

(** [icore] now carries the bytes fact (RT's output buffer holds bytes at every index). *)
Lemma arm_CHECK_ok : forall w q,
  inv w q -> RI.q_mode q = RI.M_CHECK ->
  step_ok (IA.arm_CHECK w) (RI.inf_CHECK q).
Proof.
  intros w q Hi Hm. apply arm_CHECK_ok_x; [exact Hi | exact Hm |].
  intros i _. pose proof (proj1 Hi) as Hc. unfold icore in Hc. cbv zeta in Hc.
  repeat match type of Hc with _ /\ (_ /\ _) => apply proj2 in Hc end. exact (proj2 Hc i).
Qed.

Print Assumptions arm_CHECK_ok.
