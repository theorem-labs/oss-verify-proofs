(** * Bridge.Infl.ITreeLoop — pair I15, part 3: RT's loop and RT's whole [it_model].

    [rt_loop] is the RT twin of S5's [ItSim2.loop_gen]: from [RStM k], RT's [it_loop]
    breaks exactly when S5's abstract loop completes ([first_fail = NZ - 1]) and
    overflows exactly when it fails.  [rt_model_abs] then reads RT's [it_model] off S5's
    abstract result [it_abs]: the same return code and, on success, the same [bits], the
    same advance of [next], and RT's written-back table related to S5's table on all of
    [[0, ENOUGH)]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees InftreesCoverage ItDefs ItGen ItMath ItSort ItSimPre ItSim1 ItSim2 ItShape ItCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Inftrees Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv ITreePre ITreeStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section Loop.
  Variable ty : IS.codetype.
  Variable lens : arr.
  Variable lens_ofs codes : Z.
  Variable ll wl : list Z.
  Variable table root : Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hty : ty = IS.CODES -> codes <= 19.
  Variable tc : RBa.ztbl.
  Hypothesis Htab : 0 <= table.
  Variable c : RIT.ItCtx.
  Hypothesis HCX : CtxOk ty lens lens_ofs codes wl ll root c.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hroot HM1 HK Hty Htab HCX".

  Lemma rt_loop : forall (n : nat) k st a, 0 <= k < NZ wl -> RStM wl ll root ty tc table k st a ->
    (forall j, 0 <= j < k -> fails_at wl root ty j = false) -> NZ wl - k <= Z.of_nat n ->
    match RIT.it_loop n c st with
    | Some (RIT.ItBreak st') =>
        first_fail wl root ty = NZ wl - 1 /\ RIT.s_huff st' = hf wl (NZ wl) /\
        RIT.s_len st' = len_at wl (NZ wl - 1) /\ RIT.s_drop st' = drop wl root (NZ wl - 1) /\
        RIT.s_next st' = noff wl root (NZ wl - 1) /\ RIT.s_used st' = used wl root (NZ wl - 1) /\
        TRel tc table (applyw (trips_writes wl ll root ty table (NZ wl)) a) (RIT.s_tbl st') /\ TRng (RIT.s_tbl st')
    | Some (RIT.ItOverflow _) => first_fail wl root ty < NZ wl - 1
    | _ => False
    end.
  Proof.
    induction n as [|n IH]; intros k st a Hk SM Hnf Hf; [lia|].
    cbn [RIT.it_loop].
    pose proof (rt_trip ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty
                  tc Htab c HCX k st a Hk SM) as TS.
    destruct (RIT.it_step c st) as [st'|st'|t]; cbn beta iota.
    - destruct TS as (Hk1 & Hfa & SM'). apply (IH (k + 1)); try lia; try exact SM'.
      intros j Hj. destruct (Z.eq_dec j k) as [->|NE]; [exact Hfa | apply Hnf; lia].
    - destruct TS as (Hk1 & Eh & El & Ed & En & Eu & HT & HR).
      assert (FF : first_fail wl root ty = NZ wl - 1).
      { unfold first_fail. rewrite zsearch_none; [lia|]. intros j Hj. apply Hnf. lia. }
      assert (Ek : k = NZ wl - 1) by lia. subst k.
      replace (NZ wl - 1 + 1) with (NZ wl) in HT by lia.
      exact (conj FF (conj Eh (conj El (conj Ed (conj En (conj Eu (conj HT HR))))))).
    - destruct TS as (Hk1 & Hfa).
      assert (FF : first_fail wl root ty = k).
      { unfold first_fail. apply zsearch_eq; [lia | exact Hfa | intros j Hj; apply Hnf; lia]. }
      lia.
  Qed.
End Loop.

(** The loop context [it_pre] builds satisfies [CtxOk]. *)
Lemma pre_ctx_ok : forall ty lens lens_ofs codes wl ll root lensR wk,
  (forall i, 0 <= i < codes -> lensR i = arr_get lens (lens_ofs + i)) ->
  (forall j, 0 <= j < NZ wl -> wk j = wsym wl ll j) ->
  CtxOk ty lens lens_ofs codes wl ll root
    {| RIT.x_type := rtype ty; RIT.x_codes := codes; RIT.x_lens := lensR; RIT.x_root := root;
       RIT.x_max := MAXL wl; RIT.x_mask := 2 ^ root - 1; RIT.x_work := wk;
       RIT.x_base := if rtype ty =? RIT.CT_LENS then RIT.lbase else if rtype ty =? RIT.CT_DISTS then RIT.dbase else wk;
       RIT.x_extra := if rtype ty =? RIT.CT_LENS then RIT.lext else if rtype ty =? RIT.CT_DISTS then RIT.dext else wk;
       RIT.x_match := if rtype ty =? RIT.CT_LENS then 257 else if rtype ty =? RIT.CT_DISTS then 0 else 20 |}.
Proof.
  intros ty lens lens_ofs codes wl ll root lensR wk Hlr Hwk. unfold CtxOk.
  cbn [RIT.x_type RIT.x_lens RIT.x_root RIT.x_max RIT.x_mask RIT.x_work RIT.x_match RIT.x_base RIT.x_extra].
  split; [reflexivity|]. split; [intros i Hi; apply Hlr, Hi|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hwk|]. split; [destruct ty; reflexivity|].
  intros Hnc i Hi. destruct ty; [congruence| |]; unfold rtype, RIT.CT_LENS, RIT.CT_DISTS; cbn [Z.eqb Pos.eqb].
  - unfold RIT.lbase, RIT.lext, RBa.zlist, it_base, it_extra, lbase_a, lext_a.
    rewrite !arr_get_of_list_nth by lia. split; reflexivity.
  - unfold RIT.dbase, RIT.dext, RBa.zlist, it_base, it_extra, dbase_a, dext_a.
    rewrite !arr_get_of_list_nth by lia. split; reflexivity.
Qed.

(** RT's whole [it_model] against S5's abstract [it_abs]. *)
Lemma rt_model_abs : forall ty lens lens_ofs codes lensR bits tc table tbl o,
  0 <= codes <= 288 ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
  (forall i, 0 <= i < codes -> lensR i = arr_get lens (lens_ofs + i)) ->
  (ty = IS.CODES -> codes <= 19) -> 1 <= bits <= 15 -> 0 <= table ->
  arr_len tbl = ENOUGH -> tbl_rel tbl tc 0 ENOUGH -> (forall i, code_rng (tc i)) ->
  RIT.it_model (rtype ty) lensR codes bits (fun i => tc (table + i)) = Some o ->
  let '(ret, ws, toff, bits', _) :=
    it_abs (wl_of (lens_list lens lens_ofs codes)) (lens_list lens lens_ofs codes) ty table bits in
  RIT.o_ret o = ret /\
  (ret = 0 -> RIT.o_bits o = bits' /\ toff = table + RIT.o_used o /\
              TRel tc table (applyw ws tbl) (RIT.o_tbl o) /\ TRng (RIT.o_tbl o)).
Proof.
  intros ty lens lens_ofs codes lensR bits tc table tbl o Hcodes Hlens Hlr Hty Hbits Htab Hlen Hrel Hrng Hmod.
  remember (lens_list lens lens_ofs codes) as ll eqn:Ell.
  remember (wl_of ll) as wl eqn:Ewl.
  pose proof (HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as HW0.
  pose proof (HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as HL0.
  pose proof (MAXL_spec wl HW0 HL0) as [M1 [M2 M3]].
  set (t0 := fun i => tc (table + i)) in Hmod.
  assert (HT0 : TRel tc table tbl t0).
  { split; [exact Hlen|]. intros j Hj. rewrite (Hrel j Hj). unfold RI.codes_wb, t0.
    destruct (Z.leb_spec table j); [|reflexivity]. do 2 f_equal. lia. }
  assert (HR0 : TRng t0) by (intros j; apply Hrng).
  clearbody t0.
  revert Hmod. unfold RIT.it_model, RIT.it_pre, it_abs. cbv beta zeta.
  remember (RIT.it_count (Z.to_nat codes) 0 lensR RBa.zzero) as cnt0 eqn:Ecnt.
  assert (HC : forall l, 1 <= l <= 15 -> cnt0 l = W wl l)
    by (intros l Hl; subst cnt0; apply (rt_count lens lens_ofs codes ll wl lensR Hcodes Hlens Ell Ewl Hlr); lia).
  clear Ecnt.
  rewrite (rt_findmax lens lens_ofs codes ll wl lensR Hcodes Hlens Ell Ewl Hlr cnt0 HC).
  destruct (Z.eqb_spec (MAXL wl) 0) as [HM0|HM0]; cbn beta iota.
  - (* [inftrees.c:110-118] no codes: two invalid-code markers *)
    intros H. injection H as <-. cbn [RIT.o_ret RIT.o_bits RIT.o_used RIT.o_tbl].
    split; [reflexivity|]. intros _. split; [reflexivity|]. split; [lia|].
    rewrite !applyw_cons. change (applyw [] ?x) with x. rewrite code_pack_enc.
    pose proof (TRel_set tc table tbl t0 0 (RBa.mkCodeT 64 1 0) Htab ltac:(lia) HT0) as X.
    rewrite Z.add_0_r in X.
    split.
    + apply TRel_set; [exact Htab | lia | exact X].
    + apply TRng_set; [apply code_rng_mk|]. apply TRng_set; [apply code_rng_mk | exact HR0].
  - assert (HM1 : 1 <= MAXL wl) by lia.
    rewrite (rt_findmin lens lens_ofs codes ll wl lensR Hcodes Hlens Ell Ewl Hlr cnt0 HC HM1).
    rewrite (rt_kraft lens lens_ofs codes ll wl lensR Hcodes Hlens Ell Ewl Hlr cnt0 HC).
    pose proof (LEFT_sign wl HW0 HL0) as [LS1 [LS2 LS3]].
    destruct (Z.ltb_spec (LEFT wl) 0) as [HLn|HLn]; cbn beta iota.
    + (* over-subscribed *)
      intros H. injection H as <-. cbn [RIT.o_ret]. split; [reflexivity | intros; lia].
    + assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl) by lia.
      rewrite rt_incomplete.
      destruct ((0 <? LEFT wl) && (codetype_eqb ty IS.CODES || negb (MAXL wl =? 1))) eqn:Hinc; cbn beta iota.
      * (* incomplete *)
        intros H. injection H as <-. cbn [RIT.o_ret]. split; [reflexivity | intros; lia].
      * remember (RIT.it_offs 14 1 cnt0 (RBa.zset RBa.zzero 1 0)) as offs eqn:Eoffs.
        assert (HO : forall l, 1 <= l <= 15 -> offs l = OFF wl l)
          by (intros l Hl; subst offs; apply (rt_offs lens lens_ofs codes ll wl lensR Hcodes Hlens Ell Ewl Hlr cnt0 HC); lia).
        clear Eoffs.
        remember (snd (RIT.it_sort (Z.to_nat codes) 0 lensR offs RBa.zzero)) as wk eqn:Ewk.
        assert (HWK : forall j, 0 <= j < NZ wl -> wk j = wsym wl ll j)
          by (intros j Hj; subst wk; apply (rt_work lens lens_ofs codes ll wl lensR Hcodes Hlens Ell Ewl Hlr offs HO); lia).
        clear Ewk.
        assert (ER : (if (if MAXL wl <? bits then MAXL wl else bits) <? MINL wl then MINL wl
                      else if MAXL wl <? bits then MAXL wl else bits) = ROOT wl bits).
        { pose proof (MINL_spec wl HW0 HL0 HM1) as [A _]. unfold ROOT.
          destruct (Z.ltb_spec (MAXL wl) bits);
            [destruct (Z.ltb_spec (MAXL wl) (MINL wl)) | destruct (Z.ltb_spec bits (MINL wl))]; lia. }
        rewrite ER.
        pose proof (ROOT_range ty lens lens_ofs codes ll wl bits Hcodes Hlens Ell Ewl Hty Hbits HM1) as RR.
        set (root := ROOT wl bits) in *.
        pose proof (root_range wl HW0 HL0 root RR HM1) as RR2.
        rewrite Z.shiftl_1_l, rt_enough.
        destruct (it_not_enough ty (2 ^ root)) eqn:NE0; cbn beta iota.
        -- (* the root table alone is too big *)
           intros H. injection H as <-. cbn [RIT.o_ret]. split; [reflexivity | intros; lia].
        -- match goal with |- match RIT.it_loop _ ?cc ?ss with _ => _ end = _ -> _ =>
             set (c := cc); set (st0 := ss) end.
           assert (HCX : CtxOk ty lens lens_ofs codes wl ll root c) by (apply pre_ctx_ok; assumption).
           pose proof (NZ_pos wl HW0 HL0 HM1) as NP.
           pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NC0.
           assert (SM0 : RStM wl ll root ty tc table 0 st0 tbl).
           { unfold RStM, st0.
             cbn [RIT.s_huff RIT.s_sym RIT.s_len RIT.s_next RIT.s_curr RIT.s_drop RIT.s_low RIT.s_used RIT.s_count RIT.s_tbl].
             pose proof (lay_inv wl HW0 HL0 root RR HM1 0 ltac:(lia)) as [LI _].
             assert (HS : islong wl root 0 = false).
             { unfold islong. rewrite (len_at_0 wl HW0 HL0 HM1). apply Z.ltb_ge. lia. }
             destruct (LI HS) as [N0 [C0 U0]]. rewrite N0, C0, U0. unfold drop, low. rewrite HS.
             rewrite (len_at_0 wl HW0 HL0 HM1).
             split; [reflexivity|]. do 7 (split; [reflexivity|]). split; [|split; [exact HT0 | exact HR0]].
             intros l Hl. rewrite HC by lia. unfold REM. rewrite (len_at_0 wl HW0 HL0 HM1).
             pose proof (MINL_spec wl HW0 HL0 HM1) as [A [B D]]. unfold rank_at. rewrite (len_at_0 wl HW0 HL0 HM1).
             rewrite (OFF_below_MINL wl HW0 HL0 (MINL wl)) by lia.
             destruct (Z.ltb_spec l (MINL wl)); [apply D; lia|].
             destruct (Z.eqb_spec l (MINL wl)); [subst; lia | reflexivity]. }
           pose proof (rt_loop ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty tc Htab c HCX
                         (S (Z.to_nat codes)) 0 st0 tbl ltac:(lia) SM0 ltac:(intros; lia) ltac:(lia)) as LG.
           unfold loop_abs.
           destruct (RIT.it_loop (S (Z.to_nat codes)) c st0) as [[st'|st'|t]|]; cbn beta iota in LG |- *;
             try contradiction.
           ++ (* break: success *)
              destruct LG as (FF & Eh & El & Ed & En & Eu & HT & HR).
              intros H. injection H as <-. rewrite FF, Z.ltb_irrefl. cbn beta iota.
              cbn [RIT.o_ret RIT.o_bits RIT.o_used RIT.o_tbl].
              split; [reflexivity|]. intros _. split; [unfold c; reflexivity|]. split; [rewrite Eu; reflexivity|].
              unfold RIT.it_finish, final_writes. rewrite Eh.
              destruct (Z.eqb_spec (hf wl (NZ wl)) 0) as [Z0|Z0]; cbn beta iota.
              ** rewrite app_nil_r. split; assumption.
              ** rewrite applyw_snoc, code_pack_enc, En, El, Ed.
                 replace (table + noff wl root (NZ wl - 1) + hf wl (NZ wl))
                   with (table + (noff wl root (NZ wl - 1) + hf wl (NZ wl))) by lia.
                 pose proof (curr_range wl HW0 HL0 root RR HM1 (NZ wl - 1) ltac:(lia)) as [_ [_ CR3]].
                 pose proof (hf_nonneg wl (NZ wl)) as HFN.
                 split.
                 --- apply TRel_set; [exact Htab | lia | exact HT].
                 --- apply TRng_set; [apply code_rng_mk | exact HR].
           ++ (* overflow *)
              intros H. injection H as <-.
              destruct (Z.ltb_spec (first_fail wl root ty) (NZ wl - 1)); [|lia]. cbn beta iota.
              cbn [RIT.o_ret]. split; [reflexivity | intros; lia].
Qed.
