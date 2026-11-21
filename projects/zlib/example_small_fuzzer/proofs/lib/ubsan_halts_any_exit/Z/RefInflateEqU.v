(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Uncompr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.

Module InflateCongr.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Uncompr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Facts.
  Context {St : Type}.
  Variable hooks : zhooks St.

  Lemma inflateResetKeep_total0 : forall iv s z s' z' rc,
    inflateResetKeep iv s z = (s', z', rc) -> rc = Z_OK -> zs_total_out z' = 0.
  Proof.
    intros iv s z s' z' rc H Hrc. unfold inflateResetKeep in H.
    destruct (inflateStateCheck s).
    - injection H; intros <- <- <-. discriminate Hrc.
    - injection H; intros <- <- <-. destruct (negb (is_wrap s =? 0)); reflexivity.
  Qed.

  (* zlib 1.4 (zl14infl-r2): 1.3.1's pure inflateReset is now inflateReset_tail; inflateReset is monadic *)
  Lemma inflateReset_tail_total0 : forall iv s z s' z' rc,
    inflateReset_tail iv s z = (s', z', rc) -> rc = Z_OK -> zs_total_out z' = 0.
  Proof.
    intros iv s z s' z' rc H Hrc. unfold inflateReset_tail in H.
    destruct (inflateStateCheck s).
    - injection H; intros <- <- <-. discriminate Hrc.
    - eapply inflateResetKeep_total0; eassumption.
  Qed.

  Lemma inflateReset_total0 : forall iv s z st,
    mall (fun p => snd (fst p) = Z_OK -> zs_total_out (snd (fst (fst p))) = 0)
         (inflateReset iv hooks s z st).
  Proof.
    intros iv s z st. unfold inflateReset.
    destruct (inflateStateCheck s); [apply mall_sret; cbn; intros H; discriminate H|].
    apply mall_sbind_any. intros a s'. apply mall_sret. cbn [fst snd].
    destruct (inflateReset_tail iv _ z) as [[s1 z1] rc1] eqn:E. cbn. intros Hrc. eapply inflateReset_tail_total0; eassumption.
  Qed.

  Lemma inflateReset2_total0 : forall iv s z wb st,
    mall (fun p => snd (fst p) = Z_OK -> zs_total_out (snd (fst (fst p))) = 0)
         (inflateReset2 iv hooks s z wb st).
  Proof.
    intros iv s z wb st. unfold inflateReset2.
    destruct (inflateStateCheck s); [cbn; intros H; discriminate H|].
    destruct (wb <? 0).
    - destruct (wb <? -15); [cbn; intros H; discriminate H|].
      cbn -[inflateReset Z.opp]. 
      destruct (negb (- wb =? 0) && ((- wb <? 8) || (15 <? - wb))); [cbn; intros H; discriminate H|].
      apply mall_sbind_any. intros a s'. apply inflateReset_total0.
    - cbn -[inflateReset Z.shiftr Z.land Z.ltb Z.eqb andb orb negb].
      destruct (negb _ && _); [cbn; intros H; discriminate H|].
      apply mall_sbind_any. intros a s'. apply inflateReset_total0.
  Qed.

  Lemma inflateInit2_total0 : forall iv zc wb st,
    mall (fun p => zr_rc (snd (fst p)) = Z_OK -> zs_total_out (zr_strm (snd (fst p))) = 0)
         (inflateInit2_m iv hooks zc wb st).
  Proof.
    intros iv zc wb st. unfold inflateInit2_m.
    apply mall_sbind_any. intros r s'. destruct r as [[b g]|].
    - apply (mall_sbind (fun p => snd (fst p) = Z_OK -> zs_total_out (snd (fst (fst p))) = 0)); [apply inflateReset2_total0|].
      intros [[s1 z1] ret] s'' H. cbn [fst snd] in H.
      destruct (negb (ret =? Z_OK)) eqn:E.
      + apply mall_sbind_any. intros ? ?. apply mall_sret. cbn. intros Hr.
        rewrite Hr in E. discriminate E.
      + apply mall_sret. cbn. exact H.
    - apply mall_sret. cbn. intros H; discriminate H.
  Qed.


  Lemma inflateSetDictionary_nodata : forall s zc dict st,
    mall (fun p => zr_output (snd (fst p)) = [] /\
                   zs_total_out (zr_strm (snd (fst p))) = zs_total_out (zc_strm zc))
         (inflateSetDictionary_m hooks s zc dict st).
  Proof.
    intros s zc dict st. unfold inflateSetDictionary_m.
    destruct (inflateStateCheck s); [apply mall_sret; split; reflexivity|].
    destruct (negb (is_wrap s =? 0) && negb (is_mode s =? DICT)); [apply mall_sret; split; reflexivity|].
    match goal with |- mall _ ((if ?c then _ else _) _) => destruct c end; [apply mall_sret; split; reflexivity|].
    apply mall_sbind_any. intros so s'. destruct so; apply mall_sret; split; reflexivity.
  Qed.
End Facts.
End InflateCongr.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateEqU.InflateCongr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateUpdw_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateUpdw_run.RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateEqS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateEqS.RefInflateEqT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateEqS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateEqS.RefInflateEqF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma zlength_zfirstn_le {A} n (l : list A) : 0 <= n -> 0 <= zlength (zfirstn n l) <= n.
Proof.
  intros Hn. unfold zfirstn, zlength. rewrite length_firstn.
  pose proof (Nat.le_min_l (Z.to_nat n) (length l)). lia.
Qed.
Lemma bytes_ok_zfirstn n l : bytes_ok l -> bytes_ok (zfirstn n l).
Proof.
  unfold bytes_ok, zfirstn. generalize (Z.to_nat n) as k. intros k H. revert k.
  induction H as [|x l Hx H IH]; intros [|k]; cbn; constructor; auto.
Qed.
Lemma bytes_ok_zskipn n l : bytes_ok l -> bytes_ok (zskipn n l).
Proof.
  unfold bytes_ok, zskipn. generalize (Z.to_nat n) as k. intros k H. revert k.
  induction H as [|x l Hx H IH]; intros [|k]; cbn; [constructor|constructor|constructor; auto|apply IH].
Qed.
Lemma zlength_rev_append' {A} (l r : list A) : zlength (List.rev_append l r) = zlength l + zlength r.
Proof. unfold zlength. rewrite rev_append_rev, length_app, length_rev. lia. Qed.
Lemma wrap64_add_l' a b : wrap64 (wrap64 a + b) = wrap64 (a + b).
Proof. rewrite !wrap64_mod. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

Lemma srel_mall {St A B} (R : A -> B -> Prop) (P1 : A -> Prop) (P2 : B -> Prop) (m1 : SM St A) (m2 : SM St B) :
  srel R m1 m2 -> (forall g, mall (fun p => P1 (fst p)) (m1 g)) -> (forall g, mall (fun p => P2 (fst p)) (m2 g)) ->
  srel (fun a b => R a b /\ P1 a /\ P2 b) m1 m2.
Proof.
  intros HR K1 K2 g. eapply mrel_mono; [|exact (mrel_mall _ _ _ _ _ (HR g) (K1 g) (K2 g))].
  intros [a s1] [b s2] [[Rab Es] [Pa Pb]]. cbn [fst snd] in *. split; [|exact Es]. split; [exact Rab|]. exact (conj Pa Pb).
Qed.


Definition ICALL (s1 s2 : inflate_state) : Prop := IEQ s1 s2 /\ UWS s1 /\ INV s1 /\ INV s2.


Section TwoHooks.
  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).

  Lemma IEQ_init : forall g1 g2 b, IEQ (ireset_s (s_pre g1 b DEF_WBITS)) (ireset_s (s_pre g2 b DEF_WBITS)).
  Proof.
    intros g1 g2 b. unfold ireset_s, s_pre, is_of_oracle. unfold IEQ; cbv zeta; sacc. live_red. cbn [tbl_eq].
    unfold iarr_u16_of, iarr_u32_of. rewrite !arr_len_init.
    repeat match goal with |- _ /\ _ => split end; first [reflexivity | (intros X; discriminate X) | (intros i Hi; exfalso; lia) | idtac].
  Qed.

  Lemma UWS_init : forall g1 b, UWS (ireset_s (s_pre g1 b DEF_WBITS)).
  Proof.
    intros g1 b. unfold UWS, ireset_s, s_pre. sacc. split; [reflexivity|]. split; [reflexivity|]. right. split; [reflexivity|left; reflexivity].
  Qed.

  Theorem inflateInit2_cong : forall zc,
    srel (fun p1 p2 => snd p1 = snd p2 /\ opt_rel ICALL (fst p1) (fst p2) /\ (forall s, fst p1 = Some s -> zs_total_out (zr_strm (snd p1)) = 0))
         (inflateInit2_m ivar_ref H1 zc DEF_WBITS) (inflateInit2_m ivar_ref H2 zc DEF_WBITS).
  Proof.
    intros zc g. rewrite !(inflateInit2_m_eq _). revert g.
    match goal with |- forall g, mrel _ (?m1 g) (?m2 g) => change (srel _ m1 m2) with (srel _ m1 m2) || idtac end.
    eapply srel_bind; [apply HZ|]. intros r1 r2 Er.
    destruct r1 as [[b1 q1]|]; destruct r2 as [[b2 q2]|]; cbn [option_map fst] in Er; try discriminate Er.
    - injection Er; intros <-. change (ir2_bad DEF_WBITS) with false. cbv iota.
      apply srel_ret. cbn [fst snd]. split; [reflexivity|]. split.
      + cbn [opt_rel]. split; [apply IEQ_init|]. split; [apply UWS_init|]. split; apply INV_fresh; reflexivity.
      + intros s _. reflexivity.
    - apply srel_ret. cbn [fst snd opt_rel]. split; [reflexivity|]. split; [exact I|]. intros s X; discriminate X.
  Qed.

  Theorem inflateEnd_cong : forall s1 s2 zc, IEQ s1 s2 -> srel eq (inflateEnd_m H1 s1 zc) (inflateEnd_m H2 s2 zc).
  Proof.
    intros s1 s2 zc HQ. ieq_facts HQ. unfold inflateEnd_m, inflateStateCheck. rewrite Xmode, Xwblk, Xself.
    destruct (_ || _); [apply srel_eq_refl|].
    eapply (srel_bind eq); [destruct (is_window_blk s1); [apply HF|apply srel_eq_refl]|]. intros [] [] _.
    eapply (srel_bind eq); [apply HF|]. intros [] [] _. apply srel_eq_refl.
  Qed.
End TwoHooks.


Section Loop.
  Lemma inflate_m_POST {St} (H : zhooks St) : forall s zc flush g,
    INV s -> ZC zc -> mall (fun p => INV (fst (fst p)) /\ IPOST zc (fst p)) (inflate_m ivar_ref H s zc flush g).
  Proof.
    intros s zc flush g HI Hz. eapply mall_mono; [|apply (inflate_m_sim H)].
    intros [[s' zr] g'] [ch E]. cbn [fst] in E |- *. split; [exact (inflate_INV' s zc flush ch s' zr HI Hz E) | exact (inflate_m_post flush s zc ch _ HI Hz E)].
  Qed.

  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).
  Variable L0 : Z.
Variable src : list Z.
  Hypothesis HL0 : 0 <= L0 < 2 ^ 64.
  Hypothesis Hsrc : bytes_ok src.

  Record U2I (x1 x2 : u2st) : Prop := {
    uq : IEQ (u2_s x1) (u2_s x2);
    uw : UWS (u2_s x1);
    ui1 : INV (u2_s x1);
    ui2 : INV (u2_s x2);
    uz : u2_z x2 = u2_z x1;
    ulen : u2_len x2 = u2_len x1;
    uleft : u2_left x2 = u2_left x1;
    upos : u2_in_pos x2 = u2_in_pos x1;
    uain : u2_avail_in x2 = u2_avail_in x1;
    uaout : u2_avail_out x2 = u2_avail_out x1;
    uout : u2_out_rev x2 = u2_out_rev x1;
    uerr : u2_err x2 = u2_err x1;
    uain0 : 0 <= u2_avail_in x1 < 2 ^ 32;
    uaout0 : 0 <= u2_avail_out x1 < 2 ^ 32;
    uleft0 : 0 <= u2_left x1;
    usum : zlength (u2_out_rev x1) + u2_avail_out x1 + u2_left x1 = L0;
    utot : u2_err x1 = Z_OK \/ u2_err x1 = Z_STREAM_END -> zs_total_out (u2_z x1) = wrap64 (zlength (u2_out_rev x1)) }.

  Lemma uncompress2_body_cong : forall x1 x2,
    U2I x1 x2 -> u2_err x1 = Z_OK ->
    srel U2I (uncompress2_body ivar_ref H1 src x1) (uncompress2_body ivar_ref H2 src x2).
  Proof.
    intros x1 x2 I Herr. destruct I as [Iq Iw Ii1 Ii2 Iz Ilen Ileft Ipos Iain Iaout Iout Ierr Iain0 Iaout0 Ileft0 Isum Itot].
    pose proof (zlength_nonneg (u2_out_rev x1)) as Ho0.
    unfold uncompress2_body. rewrite Iz, Ilen, Ileft, Ipos, Iain, Iaout, Iout.
    remember (if u2_avail_out x1 =? 0 then _ else _) as pa eqn:Epa. destruct pa as [ao lft].
    assert (Hao : 0 <= ao < 2 ^ 32 /\ 0 <= lft /\ ao + lft = u2_avail_out x1 + u2_left x1).
    { destruct (Z.eqb_spec (u2_avail_out x1) 0) as [E0|E0].
      - destruct (Z.ltb_spec U2_MAX (u2_left x1)); injection Epa as -> ->; unfold U2_MAX in *.
        + rewrite wrap64_id by lia. lia.
        + rewrite (wrap32_id (u2_left x1)) by lia. rewrite wrap64_id by lia. lia.
      - injection Epa as -> ->. lia. }
    clear Epa.
    remember (if u2_avail_in x1 =? 0 then _ else _) as pi eqn:Epi. destruct pi as [ai len'].
    assert (Hai : 0 <= ai < 2 ^ 32).
    { destruct (Z.eqb_spec (u2_avail_in x1) 0) as [E0|E0].
      - destruct (Z.ltb_spec U2_MAX (u2_len x1)); injection Epi as -> ->; unfold U2_MAX in *; [lia|apply wrap32_range].
      - injection Epi as -> ->. lia. }
    clear Epi.
    set (zc := mkZCall (zfirstn ai (zskipn (u2_in_pos x1) src)) ao (u2_z x1)).
    assert (Hzc : ZC zc).
    { split; [subst zc; cbn [zc_avail_out]; lia|].
      split; [subst zc; cbn [zc_input]; pose proof (zlength_zfirstn_le ai (zskipn (u2_in_pos x1) src) ltac:(lia)); lia|].
      subst zc. cbn [zc_input]. apply bytes_ok_zfirstn, bytes_ok_zskipn. exact Hsrc. }
    eapply srel_bind.
    { apply (srel_mall IRES (fun p => INV (fst p) /\ IPOST zc p) (fun p => INV (fst p) /\ IPOST zc p)).
      - apply inflate_m_cong; [exact HZ | exact fastc_proof | exact Ii1 | exact Hzc | exact Iq | exact Iw].
      - intros g. apply inflate_m_POST; [exact Ii1|exact Hzc].
      - intros g. apply inflate_m_POST; [exact Ii2|exact Hzc]. }
    intros [t1 zr1] [t2 zr2] ((Ezr & HQ' & HUS') & [J1 [P1 P2]] & [J2 _]). cbn [fst snd] in Ezr, HQ', HUS', J1, J2, P1, P2. subst zr2.
    subst zc. cbn [zc_avail_out zc_strm] in P1, P2.
    apply srel_ret. constructor; cbn [u2_s u2_z u2_len u2_left u2_in_pos u2_avail_in u2_avail_out u2_out_rev u2_err]; try reflexivity; try assumption.
    - apply wrap32_range.
    - rewrite wrap32_id by lia. lia.
    - lia.
    - rewrite zlength_rev_append'. rewrite wrap32_id by lia. lia.
    - intros Hrc. rewrite (P2 Hrc), (Itot (or_introl Herr)), zlength_rev_append', wrap64_add_l'. f_equal. lia.
  Qed.

  Lemma uncompress2_loop_cong : forall fuel x1 x2,
    U2I x1 x2 -> u2_err x1 = Z_OK ->
    srel U2I (uncompress2_loop ivar_ref H1 src fuel x1) (uncompress2_loop ivar_ref H2 src fuel x2).
  Proof.
    intros fuel x1 x2 I Herr. unfold uncompress2_loop.
    apply (srel_sloopZ (fun a b => U2I a b /\ u2_err a = Z_OK) U2I).
    - intros a b [Iab Ea]. eapply srel_bind; [apply uncompress2_body_cong; [exact Iab|exact Ea]|].
      intros y1 y2 Iy. apply srel_ret. cbn [fst snd]. rewrite (uerr _ _ Iy). split; [reflexivity|].
      destruct (Z.eqb_spec (u2_err y1) Z_OK) as [E|E]; [split; [exact Iy|exact E]|exact Iy].
    - intros a b [Iab _]. exact Iab.
    - split; [exact I|exact Herr].
  Qed.
End Loop.


Section ZcHooks.
  Context {MM : MallocModel}.
End ZcHooks.


Section Final.
End Final.

