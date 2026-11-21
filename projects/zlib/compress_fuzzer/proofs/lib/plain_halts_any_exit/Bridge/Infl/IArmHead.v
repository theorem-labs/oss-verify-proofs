(** * Bridge.Infl.IArmHead — pairs I5 (HEAD) and I6 (DICTID/DICT) of PAIRS.md.

    HEAD reads the two zlib header bytes.  The gzip branch is closed ([wrap = 5], so
    [wrap & 2 = 0]); the header checks and the window-size check go to BAD; otherwise the
    trip ends in TYPE, or in DICTID when FDICT is set.  DICTID falls through to DICT, which
    returns [Z_NEED_DICT] ([havedict = 0]): never part of a successful call, so its
    [step_ok] is the trivial case. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields BrAdler.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmHeadKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* DICTID (falls through to DICT, which returns Z_NEED_DICT)                 *)
(* ------------------------------------------------------------------------- *)

Lemma arm_DICTID_ok : forall c w q,
  ctx_rel FL c -> inv w q -> RI.q_mode q = RI.M_DICTID ->
  step_ok (IA.arm_DICTID IS.ivar_ref FL w) (RI.inf_DICTID c q).
Proof.
  intros c w q _ [Hc _] _.
  destruct (icore_hd _ _ Hc) as (Hret & _ & Hhd & _).
  unfold RI.inf_DICTID.
  destruct (RI.inf_nb 32 (RI.q_br q)) as [b|b].
  - unfold RI.inf_DICT.
    cbn [RI.qmode RI.qset_br RI.qcheck RI.qset_z RI.qset_st RI.set_mode RI.set_check RI.q_st RI.s_hdr
         RI.h_havedict].
    rewrite Hhd. cbn [step_ok Z.eqb]. discriminate.
  - cbn [step_ok RI.q_ret RI.qset_br]. rewrite Hret. intros H. exfalso. exact (ok_ne_end H).
Qed.

(* ------------------------------------------------------------------------- *)
(* HEAD                                                                      *)
(* ------------------------------------------------------------------------- *)

(** FCHECK: S5's [shl32]/[wrap64] are identities on the header's ranges. *)
Lemma head_fcheck_eq : forall hold, 0 <= hold < 2 ^ 39 ->
  wrap64 (shl32 (Z.land hold (Z.shiftl 1 8 - 1)) 8 + Z.shiftr hold 8)
  = Z.shiftl (Z.land hold (Z.shiftl 1 8 - 1)) 8 + Z.shiftr hold 8.
Proof.
  intros hold Hh.
  pose proof (land_mask_range hold 8 ltac:(lia)) as Hl.
  pose proof (shiftr_bound hold 39 8 ltac:(lia) Hh) as Hs.
  change (2 ^ 8) with 256 in Hl. change (2 ^ (39 - 8)) with 2147483648 in Hs.
  unfold shl32. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite wrap32_id by lia. apply wrap64_id. lia.
Qed.

Lemma head_fcheck_br : forall b, 0 <= RB.br_hold b < 2 ^ 39 ->
  wrap64 (shl32 (RB.br_bits_of 8 b) 8 + Z.shiftr (RB.br_hold b) 8)
  = Z.shiftl (RB.br_bits_of 8 b) 8 + Z.shiftr (RB.br_hold b) 8.
Proof. intros b H. unfold RB.br_bits_of. apply head_fcheck_eq. exact H. Qed.

(** dmax: [shl32 1 len] is [Z.shiftl 1 len] for [len <= 15]. *)
Lemma head_dmax_eq : forall len, 0 <= len <= 15 -> shl32 1 len = Z.shiftl 1 len.
Proof.
  intros len Hl. unfold shl32. rewrite Z.shiftl_1_l. apply wrap32_id.
  assert (0 < 2 ^ len) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ len <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 15) with 32768 in *. lia.
Qed.

(** The state HEAD leaves on success: dmax, flags, check, adler and mode written, the reader
    re-initialised past the two header bytes. *)
Lemma head_post : forall w q b1 d mS mR,
  icore w q -> brel (wbr w b1) b1 ->
  RB.br_in b1 = RB.br_in (RI.q_br q) ->
  RB.br_next b1 + RB.br_have b1 = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q) ->
  mS = RI.m_val mR ->
  icore (IS.mkW (IS.iset_mode (IS.iset_check (IS.iset_flags (IS.iset_dmax (IS.w_s w) d) 0)
                                             IS.iadler32_init) mS)
                (IS.icset_adler (IS.w_c w) IS.iadler32_init)
                (IS.irset_bits (IS.irset_hold (setbr (IS.w_r w) b1) 0) 0))
        (RI.qset_br (RI.qmode (RI.qcheck (RI.qset_st q (RI.set_flags (RI.set_dmax (RI.q_st q) d) 0))
                                         IS.iadler32_init) mR)
                    (RB.br_initbits b1)).
Proof.
  intros w q b1 d mS mR Hc Hb2 Hin2 Hsum2 HmS.
  destruct (brel_rng _ _ Hb2) as (Hbr2 & Hhr2 & Hn2 & Hv2 & Hnv2).
  unfold icore, iw_rel, ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel, zstrm_rel in Hc |- *.
  cbv zeta in Hc |- *. cbn [IS.w_s IS.w_c IS.w_r].
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  autorewrite with s5i_mode s5i_check s5i_flags s5i_dmax s5ic_adler s5ir_bits s5ir_hold.
  setbr_cbn; rt_cbn. rewrite ?Hin2. conjs.
  all: try solve [ assumption | reflexivity | lia | (intros _; split; reflexivity)
                 | (rewrite Z.pow_0_r; lia) ].
Qed.

Lemma arm_HEAD_ok : forall c w q,
  ctx_rel FL c -> inv w q -> RI.q_mode q = RI.M_HEAD ->
  step_ok (IA.arm_HEAD IS.ivar_ref w) (RI14.inf_HEAD14 c q).
Proof.
  intros c w q _ [Hc _] Hm.
  pose proof (icore_brel _ _ Hc) as Hb.
  destruct (icore_hd _ _ Hc) as (Hret & Hwr & _ & Hwb & Hswr & Hswb).
  unfold RI14.inf_HEAD14. cbv zeta. rewrite Hwr. change (5 =? 0) with false. cbv beta iota.
  (* NEEDBITS(16); its input-exhaustion leave keeps [q_ret = Z_OK] *)
  destruct (RI.inf_nb 16 (RI.q_br q)) as [b|b] eqn:Hnb;
    [| cbn [step_ok RI.q_ret RI.qset_br]; rewrite Hret; intros H; exfalso; exact (ok_ne_end H)].
  destruct (needbits_sim w (RI.q_br q) b 16 Hb ltac:(lia) Hnb) as (E1 & Hb1 & H16 & Hin1 & Hsum1).
  destruct (brel_rng _ _ Hb1) as (Hbr1 & Hhr1 & Hn1 & Hv1 & Hnv1).
  unfold IA.arm_HEAD.
  cbn [IS.abind IS.gs]. rewrite Hswr. change (5 =? 0) with false. cbv beta iota.
  rewrite (abind_ARun _ _ _ _ _ E1). cbv beta.
  rewrite (abind_ARun _ _ _ _ _ (hold_sim _ _ Hb1)). cbv beta.
  (* the gzip branch is closed *)
  change (negb (Z.land 5 2 =? 0)) with false. cbn [andb].
  (* FCHECK *)
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 8 Hb1 ltac:(lia))). cbv beta.
  change (Z.land 5 1 =? 0) with false. cbn [orb].
  rewrite head_fcheck_br.
  2:{ assert (2 ^ RB.br_bits b <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct ((Z.shiftl (RB.br_bits_of 8 b) 8 + Z.shiftr (RB.br_hold b) 8) mod 31 =? 0)
    eqn:Hfc; cbn [negb];
    [| cbn [step_ok]; intros H; exfalso; apply H; reflexivity].
  (* method *)
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 4 Hb1 ltac:(lia))). cbv beta.
  change Z_DEFLATED with 8. change RBa.Z_DEFLATED with 8.
  destruct (RB.br_bits_of 4 b =? 8) eqn:Hdef; cbn [negb];
    [| cbn [step_ok]; intros H; exfalso; apply H; reflexivity].
  (* window size *)
  destruct (dropbits_sim _ _ 4 Hb1 ltac:(lia)) as [E2 Hb2]. rewrite wbr_wbr in E2, Hb2.
  assert (Hin2 : RB.br_in (RB.br_dropbits 4 b) = RB.br_in (RI.q_br q)) by exact Hin1.
  assert (Hsum2 : RB.br_next (RB.br_dropbits 4 b) + RB.br_have (RB.br_dropbits 4 b)
                  = RB.br_next (RI.q_br q) + RB.br_have (RI.q_br q)) by exact Hsum1.
  assert (Hbt2 : 4 <= RB.br_bits (RB.br_dropbits 4 b)) by (cbn [RB.br_dropbits RB.br_bits]; lia).
  remember (RB.br_dropbits 4 b) as b1 eqn:Eb1. clear Eb1.
  rewrite (abind_ARun _ _ _ _ _ E2). cbv beta.
  rewrite (abind_ARun _ _ _ _ _ (bits_sim _ _ 4 Hb2 ltac:(lia))). cbv beta.
  (* zlib 1.4 (the Z side): the window-size check comes first, the wbits store after it; at wbits = 15 both
     sides test [15 <? len] twice *)
  cbn [IS.abind IS.aret IS.gs]. rewrite ?wbr_s, Hswb, Hwb. change (15 =? 0) with false. cbn [negb andb].
  cbv beta iota. rewrite ?Hwb.
  destruct ((15 <? RB.br_bits_of 4 b1 + 8) || (15 <? RB.br_bits_of 4 b1 + 8)) eqn:Hws;
    [cbn [step_ok]; intros H; exfalso; apply H; reflexivity |].
  cbn [IS.abind IS.aret].
  assert (Hlen : 0 <= RB.br_bits_of 4 b1 + 8 <= 15).
  { apply orb_false_iff in Hws. destruct Hws as [Hws _]. apply Z.ltb_ge in Hws.
    pose proof (land_mask_range (RB.br_hold b1) 4 ltac:(lia)) as Hl. change (2 ^ 4) with 16 in Hl.
    unfold RB.br_bits_of in *. lia. }
  (* success: dmax, flags, check, mode, INITBITS *)
  cbn [IS.abind IS.aret IS.gs IS.gr IS.us IS.uc IS.ur IA.set_mode IA.set_adler_check IA.aux IS.iv_aux
       IS.ivar_ref IA.HOLD].
  unfold IA.INITBITS, IS.ur.
  autorewrite with s5w. rewrite ?wbr_s, ?wbr_c, ?wbr_r.
  cbn [step_ok]. intros _. eexists. split; [reflexivity|].
  rewrite head_dmax_eq by exact Hlen.
  rewrite <- (proj2 BrAdler.br_adler32_init).
  apply inv_eta. autorewrite with s5w. rewrite ?wbr_s, ?wbr_c, ?wbr_r.
  split.
  - apply head_post; try assumption. setbr_cbn. destruct (Z.land (RB.br_hold b1) 512 =? 0); reflexivity.
  - unfold imode. rt_cbn. destruct (Z.land (RB.br_hold b1) 512 =? 0); exact I.
Qed.
