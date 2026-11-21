(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqA2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Dispatch.
  Variable flush : Z.
  Hypothesis fastc : FASTC.

  Theorem dispatch_cong : forall s1 s2 c r,
    WINV (mkW s1 c r) -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (dispatch ivar_ref flush (mkW s1 c r)) (dispatch ivar_ref flush (mkW s2 c r)).
  Proof.
    intros s1 s2 c r HW HQ HU. pose proof HW as HW0. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & HWF & HWB).
    unfold dispatch. rstep gs_eq. cbv zeta. destruct HQ as [[Qm Qrest1] Qrest2]. rewrite Qm.
    assert (HQ : IEQ s1 s2) by (split; [split; [exact Qm|exact Qrest1]|exact Qrest2]). clear Qrest1 Qrest2.
    Ltac tryc lem ftac := lazymatch goal with |- RES2 ((if is_mode ?s =? ?M then _ else _) _) _ =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE]; [apply lem; [ftac | exact E | assumption | assumption] |] end.
    tryc (arm_HEAD_cong ivar_ref) ltac:(exact I).
    tryc (arm_gz_cong FLAGS FTrue arm_FLAGS eq_refl) ltac:(exact I).
    tryc (arm_gz_cong TIME FTrue arm_TIME eq_refl) ltac:(exact I).
    tryc (arm_gz_cong OS FTrue arm_OS eq_refl) ltac:(exact I).
    tryc (arm_gz_cong EXLEN FTrue arm_EXLEN eq_refl) ltac:(exact I).
    tryc (arm_gz_cong EXTRA FTrue arm_EXTRA eq_refl) ltac:(exact I).
    tryc (arm_gz_cong NAME FTrue arm_NAME eq_refl) ltac:(exact I).
    tryc (arm_gz_cong COMMENT FTrue arm_COMMENT eq_refl) ltac:(exact I).
    tryc (arm_gz_cong HCRC FTrue arm_HCRC eq_refl) ltac:(exact I).
    tryc (arm_DICTID_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_DICT_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_TYPE_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_TYPEDO_cong ivar_ref flush TYPEDO (or_intror eq_refl)) ltac:(exact I).
    tryc (arm_STORED_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_COPY__cong) ltac:(exact I).
    tryc (arm_COPY_cong) ltac:(exact I).
    tryc (arm_TABLE_cong flush fastc) ltac:(exact HW0).
    tryc (arm_LENLENS_cong flush fastc) ltac:(rewrite E in HMF, HWF; mred_in HMF; mred_in HWF; destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs); unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    tryc (arm_CODELENS_cong flush fastc) ltac:(rewrite E in HMF, HWF; mred_in HMF; mred_in HWF; destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT); unfold CL; repeat (split; [first [assumption | lia]|]); exact HWB).
    tryc (arm_LEN__cong fastc) ltac:(exact HC).
    tryc (arm_LEN_cong fastc) ltac:(exact HC).
    tryc (arm_LENEXT_cong) ltac:(exact HC).
    tryc (arm_DIST_cong) ltac:(exact HC).
    tryc (arm_DISTEXT_cong) ltac:(exact HC).
    tryc (arm_MATCH_cong) ltac:(exact HC).
    tryc (arm_LIT_cong) ltac:(exact I).
    tryc (arm_CHECK_cong) ltac:(exact I).
    tryc (arm_LENGTH_cong LENGTH FTrue ltac:(discriminate) ltac:(discriminate)) ltac:(exact I).
    tryc (arm_DONE_cong DONE FTrue) ltac:(exact I).
    tryc (arm_BAD_cong FTrue) ltac:(exact I).
    tryc (arm_MEM_cong FTrue) ltac:(exact I).

    destruct (Z.eqb_spec (is_mode s1) SYNC) as [E|NE'].
    - apply (arm_SYNC_cong FTrue); [exact I | exact E | exact HQ | exact HU].
    - exfalso. unfold MF in HMF.
      repeat match goal with N : is_mode s1 <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HMF; clear N end.
      cbn [orb] in HMF. exact HMF.
  Qed.
End Dispatch.

Section Loop.
  Variable flush : Z.
  Hypothesis fastc : FASTC.

  Lemma WMID_c : forall w1 w2, WMID w1 w2 -> w_c w2 = w_c w1.
  Proof. intros w1 w2 (Ec & _). exact Ec. Qed.

  Lemma iter_cong : forall m w1 w2, WINV w1 -> WMID w1 w2 ->
    let '(st1, w1') := iterZ (Z.of_nat m) (lstep flush) (fun w0 => (SLeave, w0)) w1 in
    let '(st2, w2') := iterZ (Z.of_nat m) (lstep flush) (fun w0 => (SLeave, w0)) w2 in
    st2 = st1 /\ WMID w1' w2'.
  Proof.
    induction m as [|m IH]; intros w1 w2 HW HM.
    - cbn [Z.of_nat]. rewrite !iterZ_le0 by lia. split; [reflexivity|exact HM].
    - rewrite !iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      destruct w1 as [s1 c r]. destruct w2 as [s2 c2 r2]. destruct HM as (Ec & Er & HQ & HU). cbn [w_s w_c w_r] in Ec, Er, HQ, HU. subst c2 r2.
      pose proof (dispatch_safe flush (mkW s1 c r) s1 c r HW ltac:(lia)) as D.
      pose proof (dispatch_cong flush fastc s1 s2 c r HW HQ HU) as R.
      unfold lstep at 1 3.
      destruct (dispatch ivar_ref flush (mkW s1 c r)) as [u w1'|w1'|rc w1'];
        destruct (dispatch ivar_ref flush (mkW s2 c r)) as [u2 w2'|w2'|rc2 w2']; cbn [RES2] in R; try contradiction.
      + destruct R as [-> R]. destruct D as [HW' _]. apply IH; [exact HW'|exact R].
      + split; [reflexivity|exact R].
      + destruct R as [-> R]. split; [reflexivity|exact R].
  Qed.

  Theorem inf_loop_cong : forall w1 w2, WINV w1 -> WMID w1 w2 ->
    let '(st1, w1') := inf_loop ivar_ref flush w1 in
    let '(st2, w2') := inf_loop ivar_ref flush w2 in
    st2 = st1 /\ WMID w1' w2'.
  Proof.
    intros w1 w2 HW HM. unfold inf_loop. change (fun w0 : iw => _) with (lstep flush) at 1.
    change (fun w0 : iw => match dispatch ivar_ref flush w0 with ARun _ w' => inl w' | ALeave w' => inr (SLeave, w') | ARet rc w' => inr (SRet rc, w') end) with (lstep flush).
    rewrite (WMID_c _ _ HM).
    set (n := 64 * (ic_avail_in (w_c w1) + ic_avail_out (w_c w1) + 64)).
    destruct (Z_lt_le_dec n 0) as [Hn|Hn].
    - rewrite !iterZ_le0 by lia. split; [reflexivity|exact HM].
    - rewrite <- (Z2Nat.id n) by lia. apply iter_cong; [exact HW|exact HM].
  Qed.
End Loop.

Lemma blit_agree : forall (w1 w2 src : arr) dofs sofs n j,
  arr_len w2 = arr_len w1 ->
  (arr_get w2 j = arr_get w1 j \/ (dofs <= j < dofs + n /\ 0 <= j < arr_len w1)) ->
  arr_get (arr_blit w2 dofs src sofs n) j = arr_get (arr_blit w1 dofs src sofs n) j.
Proof.
  intros w1 w2 src dofs sofs n j HL H. rewrite !arr_get_blit. unfold arr_inb. rewrite HL.
  destruct H as [H|[H1 H2]].
  - destruct ((dofs <=? j) && (j <? dofs + Z.max 0 n) && ((0 <=? j) && (j <? arr_len w1))); [reflexivity|exact H].
  - replace ((dofs <=? j) && (j <? dofs + Z.max 0 n) && ((0 <=? j) && (j <? arr_len w1))) with true; [reflexivity|].
    symmetry. rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Ltac ieq_facts HQ :=
  let HQ' := fresh "XQ" in pose proof HQ as HQ';
  unfold IEQ in HQ'; cbv zeta in HQ';
  destruct HQ' as ((Xmode & Xlast & Xwrap & Xhavedict & Xflags & Xdmax & Xtotal & Xhead & Xwbits & Xwsize & Xwhave & Xwnext
                    & Xwblk & Xhold & Xbits & Xlencode & Xdistcode & Xnext & Xsane & Xback & Xself & XLwin & XLlens & XLwork & XLcodes)
                   & Xcheck & Xlength & Xoffset & Xextra & Xlenbits & Xdistbits & Xncode & Xnlen & Xwin & Xlens1 & Xlens2 & Xctbl & Xtbls).

Ltac ieq_xfer :=
  unfold IEQ; cbv zeta; sacc;
  repeat match goal with |- _ /\ _ => split end;
  first [ assumption | reflexivity | idtac ].

Section UpdW.
  Variable t1 : inflate_state.
Variable t2 : inflate_state.
Variable src : arr.
Variable e : Z.
Variable copy : Z.
  Hypothesis HC : CORE t1.
  Hypothesis Hb : is_window_blk t1 <> None.
  Hypothesis HQ : IEQ t1 t2.
  Hypothesis Hcopy : 0 <= copy.

  Let V := wrap32 (Z.shiftl 1 (is_wbits t1)).

  Lemma sA_cong : exists u1 u2,
    updw_core t1 src e copy = updw_core u1 src e copy /\ updw_core t2 src e copy = updw_core u2 src e copy
    /\ IEQ u1 u2 /\ is_wsize u1 = V /\ 0 <= is_whave u1 <= V /\ 0 <= is_wnext u1 /\ (V <> 0 -> is_wnext u1 < V)
    /\ (is_whave u1 < V -> is_wnext u1 = is_whave u1) /\ arr_len (is_window u1) = V /\ is_wbits u1 = is_wbits t1 /\ 0 <= V.
  Proof.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
    destruct (C2 Hb) as [WL WB]. unfold shl32 in *.
    pose proof (wrap32_range (Z.shiftl 1 (is_wbits t1))) as VR. fold V in VR, WL, C3.
    ieq_facts HQ.
    destruct (Z.eqb_spec (is_wsize t1) 0) as [Z0|Z0].
    - destruct (C6 Z0) as [WH0 WN0].
      destruct (Z.eqb_spec V 0) as [V0|V0].
      +
        exists t1, t2. split; [reflexivity|]. split; [reflexivity|]. split; [exact HQ|]. rewrite Z0, WH0, WN0, V0.
        clear - WL V0. repeat split; lia.
      + exists (iset_whave (iset_wnext (iset_wsize t1 V) 0) 0), (iset_whave (iset_wnext (iset_wsize t2 V) 0) 0).
        split; [|split; [|split; [ieq_xfer; intros i Hi; exfalso; lia| sacc; clear - VR WL; repeat split; lia]]].
        * unfold updw_core, sA. unfold shl32. fold V. sacc. rewrite Z0, (proj2 (Z.eqb_neq V 0) V0). reflexivity.
        * unfold updw_core, sA. unfold shl32. rewrite Xwsize, Xwbits. fold V. sacc. rewrite Z0, (proj2 (Z.eqb_neq V 0) V0). reflexivity.
    - exists t1, t2. split; [reflexivity|]. split; [reflexivity|]. split; [exact HQ|].
      pose proof (C3 Z0) as F3. pose proof (C7 Z0) as F7. pose proof (C8 Z0) as F8.
      clear - Z0 F3 F7 F8 VR WL WB C4 C5. repeat split; lia.
  Qed.

  Lemma updw_core_cong : IEQ (updw_core t1 src e copy) (updw_core t2 src e copy).
  Proof.
    destruct sA_cong as (u1 & u2 & -> & -> & HQu & W1 & W2 & W3 & W4 & W5 & L1 & WBu & VP).
    pose proof (wrap32_range (Z.shiftl 1 (is_wbits t1))) as VR. fold V in VR.
    clear HQ HC Hb. ieq_facts HQu.
    Ltac nz W1 := sacc;
      repeat match goal with X : ?f ?b = ?f ?a |- context [?f ?b] => lazymatch f with is_window => fail | _ => rewrite !X end end;
      rewrite ?W1.
    unfold updw_core, sA. nz W1. unfold shl32. rewrite ?WBu. fold V.
    destruct (Z.eqb_spec V 0) as [V0|V0].
    {
      nz W1. rewrite V0. rewrite (proj2 (Z.leb_le 0 copy) Hcopy). ieq_xfer; try (rewrite !arr_len_blit; exact XLwin).
      intros i Hi. exfalso. lia. }
    nz W1.
    rewrite (wrap32_id (V - is_wnext u1)) by lia.
    destruct (Z.leb_spec V copy) as [LE|GT]; nz W1.
    - ieq_xfer.
      + rewrite !arr_len_blit. exact XLwin.
      + intros i Hi. apply blit_agree; [exact XLwin|]. right. rewrite L1. lia.
    - set (dist := if copy <? V - is_wnext u1 then copy else V - is_wnext u1).
      assert (Hd : 0 <= dist <= copy /\ dist <= V - is_wnext u1 /\ (dist = copy \/ dist = V - is_wnext u1))
        by (subst dist; destruct (Z.ltb_spec copy (V - is_wnext u1)); lia).
      rewrite (wrap32_id (copy - dist)) by lia.
      destruct (Z.eqb_spec (copy - dist) 0) as [CD|CD]; cbn [negb]; nz W1.
      + rewrite (wrap32_id (is_wnext u1 + dist)) by lia.
        assert (AG : forall i, 0 <= i < (if is_whave u1 <? V then is_whave u1 + dist else is_whave u1) ->
                  arr_get (arr_blit (is_window u2) (is_wnext u1) src (e - copy) dist) i = arr_get (arr_blit (is_window u1) (is_wnext u1) src (e - copy) dist) i).
        { intros i Hi. apply blit_agree; [exact XLwin|]. rewrite L1.
          destruct (Z_lt_le_dec i (is_wnext u1)) as [A|A]; [left; apply Xwin|].
          - destruct (Z.ltb_spec (is_whave u1) V); [pose proof (W5 ltac:(lia)); lia|lia].
          - destruct (Z_lt_le_dec i (is_wnext u1 + dist)) as [B|B]; [right; lia|left; apply Xwin].
            destruct (Z.ltb_spec (is_whave u1) V); [pose proof (W5 ltac:(lia)); lia|lia]. }
        destruct (Z.eqb_spec (is_wnext u1 + dist) V) as [EV|EV]; nz W1;
          (destruct (Z.ltb_spec (is_whave u1) V) as [WH|WH]; nz W1); rewrite ?(wrap32_id (is_whave u1 + dist)) by lia;
          ieq_xfer; try (rewrite !arr_len_blit; exact XLwin); intros i Hi; apply AG;
          first [rewrite (proj2 (Z.ltb_lt _ _) WH); exact Hi | rewrite (proj2 (Z.ltb_ge _ _) WH); exact Hi].
      + ieq_xfer.
        * rewrite !arr_len_blit. exact XLwin.
        * intros i Hi. apply blit_agree; [rewrite !arr_len_blit; exact XLwin|]. rewrite arr_len_blit, L1.
          destruct (Z_lt_le_dec i (copy - dist)) as [A|A]; [right; lia|left].
          apply blit_agree; [exact XLwin|]. rewrite L1.
          destruct (Z_lt_le_dec i (is_wnext u1)) as [B|B]; [left; apply Xwin|right; lia].
          destruct (Z_lt_le_dec (is_whave u1) V); [pose proof (W5 ltac:(lia)); lia|lia].
  Qed.
End UpdW.

Definition UWS (s : inflate_state) : Prop :=
  is_wrap s = 5 /\ gzb (is_mode s) = false
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD \/ is_mode s = MEM))).

Lemma UW_UWS : forall s c r, UW s c r -> UWS s.
Proof.
  intros s c r (W & G & [F|(F & M & _)]); (split; [exact W|]); (split; [exact G|]); [left; exact F|right].
  split; [exact F|]. destruct M as [M|M]; [left; exact M|right; left; exact M].
Qed.
Lemma UWS_UW : forall s c r, UWS s -> is_mode s <> MEM -> ir_put r = 0 -> ir_out r = arr_len (ic_outbuf c) -> UW s c r.
Proof.
  intros s c r (W & G & [F|[F M]]) NM Hp Ho; (split; [exact W|]); (split; [exact G|]); [left; exact F|right].
  split; [exact F|]. split; [|exact (conj Hp Ho)]. destruct M as [M|[M|M]]; [left; exact M|right; exact M|exfalso; exact (NM M)].
Qed.

Lemma lv_fin_cong : forall flush t1 t2 c r,
  IEQ t1 t2 -> UW t1 c r -> REGS c r ->
  snd (lv_fin flush t1 (c_rest c r) r) = snd (lv_fin flush t2 (c_rest c r) r)
  /\ IEQ (fst (lv_fin flush t1 (c_rest c r) r)) (fst (lv_fin flush t2 (c_rest c r) r))
  /\ UWS (fst (lv_fin flush t1 (c_rest c r) r)).
Proof.
  intros flush t1 t2 c r HQ HU HR. ieq_facts HQ.
  pose proof HR as (RN & RH & RNH & RP & RL & RPL & _).
  assert (OUT0 : is_flags t1 <> 0 -> wrap32 (ir_out r - ic_avail_out (c_rest c r)) = 0).
  { intros F. destruct HU as (_ & _ & [F0|(_ & _ & P0 & O0)]); [exfalso; exact (F F0)|].
    unfold c_rest. sacc. rewrite O0, <- RPL, P0. replace (0 + ir_left r - ir_left r) with 0 by lia. reflexivity. }
  unfold lv_fin, dt_model, UPDATE_CHECK_bytes. cbv zeta.
  sacc; rewrite ?Xwrap, ?Xtotal, ?Xflags, ?Xbits, ?Xlast, ?Xmode.
  destruct (Z.eqb_spec (is_flags t1) 0) as [F0|F0]; cbn [negb].
  - rewrite (Xcheck F0).
    match goal with |- context [if ?cnd then _ else _] => destruct cnd eqn:C end; sacc; rewrite ?Xwrap, ?Xtotal, ?Xflags, ?Xbits, ?Xlast, ?Xmode.
    + split; [reflexivity|]. split; [ieq_xfer|]. apply (UW_UWS _ c r). destruct HU as (A1 & A2 & A3). sacc. exact (conj A1 (conj A2 A3)).
    + split; [reflexivity|]. split; [ieq_xfer|]. apply (UW_UWS _ c r). destruct HU as (A1 & A2 & A3). sacc. exact (conj A1 (conj A2 A3)).
  - rewrite (OUT0 F0). rewrite Z.eqb_refl. cbn [negb]. rewrite !Bool.andb_false_r. sacc; rewrite ?Xwrap, ?Xtotal, ?Xflags, ?Xbits, ?Xlast, ?Xmode.
    split; [reflexivity|]. split; [ieq_xfer|]. apply (UW_UWS _ c r). destruct HU as (A1 & A2 & A3). sacc. exact (conj A1 (conj A2 A3)).
Qed.

Definition ZC (zc : ZCall) : Prop :=
  0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32 /\ bytes_ok (zc_input zc).

Lemma WINV_entry' : forall st zc,
  INV st -> ZC zc ->
  WINV (W0 st zc) /\ PHI (W0 st zc) < 64 * (ic_avail_in (w_c (W0 st zc)) + ic_avail_out (w_c (W0 st zc)) + 64).
Proof.
  intros st zc (HC & HBs & HM) (Hao & Hlen & Hby).
  pose proof (zlength_nonneg (zc_input zc)) as LN. destruct HBs as [B1 B2].
  assert (HR : REGS (icall_of_zcall zc) (mkIR 0 (zlength (zc_input zc)) 0 (zc_avail_out zc) (is_hold st) (is_bits st) (zlength (zc_input zc)) (zc_avail_out zc) Z_OK)).
  { unfold REGS, HB, icall_of_zcall. cbn [ic_input ic_outbuf ir_next ir_have ir_put ir_left ir_hold ir_bits].
    rewrite arr_len_of_list. unfold arr_make. rewrite arr_len_init.
    repeat (split; [first [lia | intros i; apply arr_get_of_list_byte; exact Hby] |]). lia. }
  unfold W0, s_entry. destruct (Z.eqb_spec (is_mode st) TYPE) as [ET|ET].
  - split.
    + unfold WINV. cbn [w_s w_c w_r]. sacc. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HR|].
      rewrite ET in HM. split; [revert HM; mred; intros HM; split; [common_keep (proj1 HM) | exact (proj2 HM)]|].
      split; [mred; unfold icall_of_zcall; cbn [ic_outbuf]; unfold arr_make; rewrite arr_len_init; reflexivity|].
      intros _; reflexivity.
    + unfold PHI. cbn [w_s w_c w_r]. sacc. unfold icall_of_zcall. cbn [ic_avail_in ic_avail_out]. mred. lia.
  - split.
    + unfold WINV. cbn [w_s w_c w_r]. cbn [ir_hold ir_bits ir_out ir_put]. split; [exact HC|]. split; [exact HR|]. split; [exact HM|].
      split; [|intros _; reflexivity].
      unfold WF. destruct ((is_mode st =? LENGTH) || (is_mode st =? DONE) || (is_mode st =? BAD)); [exact I|].
      unfold icall_of_zcall. cbn [ic_outbuf]. unfold arr_make. rewrite arr_len_init.
      destruct ((is_mode st =? HEAD) || (is_mode st =? FLAGS)); [split|]; reflexivity.
    + unfold PHI. cbn [w_s w_c w_r]. cbn [ir_have ir_bits ir_left]. unfold icall_of_zcall. cbn [ic_avail_in ic_avail_out].
      pose proof (rank_range (is_mode st)). lia.
Qed.

Lemma inf_loop_MEM : forall flush w,
  is_mode (w_s w) = MEM -> 0 <= ic_avail_in (w_c w) -> 0 <= ic_avail_out (w_c w) ->
  inf_loop ivar_ref flush w = (SRet Z_MEM_ERROR, w).
Proof.
  intros flush [s c r] E Hai Hao. cbn [w_s w_c] in E, Hai, Hao. unfold inf_loop. cbn [w_c].
  rewrite iterZ_step by lia. unfold dispatch at 1. unfold abind at 1. rewrite gs_eq. cbn [w_s]. cbv zeta. rewrite E.
  mred. reflexivity.
Qed.

Lemma W0_WMID : forall s1 s2 zc, IEQ s1 s2 -> UWS s1 -> is_mode s1 <> MEM -> 0 <= zc_avail_out zc ->
  WMID (W0 s1 zc) (W0 s2 zc).
Proof.
  intros s1 s2 zc HQ HUS NM Hao. ieq_facts HQ. unfold W0, s_entry. rewrite Xmode, Xhold, Xbits.
  apply WMID_mk.
  - destruct (Z.eqb_spec (is_mode s1) TYPE) as [ET|ET]; [|exact HQ].
    unfold IEQ; cbv zeta; sacc. live_red. cbn [tbl_eq].
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | (intros X; discriminate X) | idtac].
  - apply UWS_UW.
    + destruct HUS as (A1 & A2 & A3). destruct (Z.eqb_spec (is_mode s1) TYPE) as [ET|ET]; [|exact (conj A1 (conj A2 A3))].
      split; [sacc; exact A1|]. split; [reflexivity|]. sacc. destruct A3 as [F|(F & M)]; [left; exact F|exfalso].
      rewrite ET in M. destruct M as [M|[M|M]]; discriminate M.
    + destruct (Z.eqb_spec (is_mode s1) TYPE) as [ET|ET]; sacc; [intros X; discriminate X|exact NM].
    + reflexivity.
    + cbn [ir_out icall_of_zcall ic_outbuf]. unfold arr_make. rewrite arr_len_init. reflexivity.
Qed.

Section TwoHooks.
  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).

  Definition UWO (s1 : inflate_state) (o1 o2 : option inflate_state) : Prop :=
    match o1, o2 with
    | None, None => True
    | Some t1, Some t2 => IEQ t1 t2 /\ is_mode t1 = is_mode s1 /\ is_wrap t1 = is_wrap s1 /\ is_flags t1 = is_flags s1
    | _, _ => False
    end.

  Lemma updw_core_mwf : forall s src e copy,
    is_mode (updw_core s src e copy) = is_mode s /\ is_wrap (updw_core s src e copy) = is_wrap s /\ is_flags (updw_core s src e copy) = is_flags s.
  Proof.
    intros. pose proof (updw_core_fields s src e copy) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & _).
    exact (conj F1 (conj F2 F3)).
  Qed.

  Lemma updatewindow_cong : forall s1 s2 src e copy,
    CORE s1 -> is_wbits s1 <> 0 -> IEQ s1 s2 -> 0 <= copy ->
    srel (UWO s1) (updatewindow H1 s1 src e copy) (updatewindow H2 s2 src e copy).
  Proof.
    intros s1 s2 src e copy HC Hwb HQ Hcopy. ieq_facts HQ.
    rewrite !updatewindow_unfold. rewrite Xwblk, Xwbits.
    pose proof HC as (C1 & C2 & _).
    destruct (is_window_blk s1) as [b|] eqn:EB.
    - eapply (srel_bind (fun o1 o2 => o1 = Some s1 /\ o2 = Some s2)).
      + apply srel_ret. split; reflexivity.
      + intros o1 o2 [-> ->]. rewrite !updw_body_eq. apply srel_ret. cbn [UWO]. split; [|apply updw_core_mwf].
        apply updw_core_cong; [exact HC | rewrite EB; intros X; discriminate X | exact HQ | exact Hcopy].
    - eapply (srel_bind (fun o1 o2 => match o1, o2 with
                                       | None, None => True
                                       | Some t1, Some t2 => IEQ t1 t2 /\ CORE t1 /\ is_window_blk t1 <> None /\ is_wbits t1 = is_wbits s1
                                                             /\ (is_mode t1 = is_mode s1 /\ is_wrap t1 = is_wrap s1 /\ is_flags t1 = is_flags s1)
                                       | _, _ => False end)).
      + eapply srel_bind; [apply HZ|]. intros r1 r2 Er.
        destruct r1 as [[b1 g1]|]; destruct r2 as [[b2 g2]|]; cbn [option_map fst] in Er; try discriminate Er.
        * injection Er; intros <-. apply srel_ret. split; [|split; [apply CORE_fresh_window; [exact HC|first [exact EB|reflexivity]|exact Hwb]|split; [sacc; intros X; discriminate X|split; [reflexivity|sacc; repeat split; reflexivity]]]].
          pose proof (C1 ltac:(first [exact EB|reflexivity])) as Z0. pose proof HC as (_ & _ & _ & _ & _ & C6 & _). destruct (C6 Z0) as [WH0 _].
          ieq_xfer; unfold iarr_u8_of; rewrite ?arr_len_init; try reflexivity.
          intros i Hi. exfalso. rewrite WH0 in Hi. lia.
        * apply srel_ret. exact I.
      + intros o1 o2 Ho. destruct o1 as [u1|]; destruct o2 as [u2|]; try contradiction; [|apply srel_ret; exact I].
        destruct Ho as (HQ' & HC' & Hb' & Hwb' & (M1 & M2 & M3)). rewrite !updw_body_eq. apply srel_ret. cbn [UWO]. rewrite <- M1, <- M2, <- M3. split; [|apply updw_core_mwf].
        apply updw_core_cong; [exact HC' | exact Hb' | exact HQ' | exact Hcopy].
  Qed.

  Definition IRES (p1 p2 : inflate_state * ZRet) : Prop :=
    snd p1 = snd p2 /\ IEQ (fst p1) (fst p2) /\ UWS (fst p1).

  Lemma IEQ_MEM : forall a b, IEQ a b -> IEQ (iset_mode a MEM) (iset_mode b MEM).
  Proof.
    intros a b HQ. ieq_facts HQ. unfold IEQ; cbv zeta; sacc. live_red. cbn [tbl_eq].
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | (intros X; discriminate X) | idtac].
  Qed.
  Lemma UWS_MEM : forall a, UWS a -> UWS (iset_mode a MEM).
  Proof.
    intros a (A1 & A2 & A3). unfold UWS. sacc. split; [exact A1|]. split; [reflexivity|].
    destruct A3 as [F|(F & _)]; [left; exact F|right]. split; [exact F|]. right; right; reflexivity.
  Qed.

  Lemma inf_leave_cong : forall flush s1 s2 c r,
    WINV (mkW s1 c r) -> IEQ s1 s2 -> UW s1 c r ->
    srel IRES (inf_leave H1 flush (mkW s1 c r)) (inf_leave H2 flush (mkW s2 c r)).
  Proof.
    intros flush s1 s2 c r HW HQ HU. ieq_facts HQ.
    unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & HWF & HWB).
    pose proof HR as (RN & RH & RNH & RP & RL & RPL & HBr & RIN & RNI & RNO).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
    intros g. rewrite !(inf_leave_eq _). revert g.
    match goal with |- forall g, mrel _ (?m1 g) (?m2 g) => change (srel IRES m1 m2) end.
    assert (EQc : lv_cond flush (s_rest s2 r) (c_rest c r) r = lv_cond flush (s_rest s1 r) (c_rest c r) r)
      by (unfold lv_cond, s_rest; sacc; rewrite Xwsize, Xmode; reflexivity).
    rewrite EQc.
    assert (HQr : IEQ (s_rest s1 r) (s_rest s2 r)) by (unfold s_rest; ieq_xfer).
    assert (HUr : UW (s_rest s1 r) c r) by (unfold s_rest; destruct HU as (A1 & A2 & A3); split; [sacc; exact A1|]; split; [sacc; exact A2|sacc; exact A3]).
    assert (HCr : CORE (s_rest s1 r)) by (unfold s_rest; core_keep HC; apply CORE_length; exact HC).
    destruct (lv_cond flush (s_rest s1 r) (c_rest c r) r) eqn:LC.
    -
      assert (WB : is_wbits s1 <> 0).
      { intros W. destruct (C9 W) as [N _]. pose proof (C1 N) as Z0. pose proof (HWB W) as P0.
        assert (NLD : is_mode s1 <> LENGTH /\ is_mode s1 <> DONE).
        { split; intros E; rewrite E in HMF; revert HMF; mred; intros [X _]; exact (X W). }
        unfold WF in HWF.
        revert LC. unfold lv_cond, s_rest, c_rest. sacc. rewrite Z0, Z.eqb_refl. change (negb true) with false. rewrite Bool.orb_false_l.
        destruct (Z.eqb_spec (is_mode s1) BAD) as [EB'|NB].
        - rewrite EB' in *. replace (BAD <? BAD) with false by reflexivity. rewrite Bool.andb_false_r. cbn [andb]. intros X; discriminate X.
        - assert (EO : ir_out r = ir_left r).
          { destruct NLD as [N1 N2]. rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in HWF. cbn [orb] in HWF.
            destruct ((is_mode s1 =? HEAD) || (is_mode s1 =? FLAGS)); [destruct HWF as [E1 _]|rename HWF into E1]; rewrite E1, <- RPL, P0; lia. }
          rewrite EO. replace (ir_left r - ir_left r) with 0 by lia. change (wrap32 0 =? 0) with true. cbn [negb andb]. intros X; discriminate X. }
      eapply srel_bind.
      { apply updatewindow_cong; [exact HCr | unfold s_rest; sacc; exact WB | exact HQr | pose proof (wrap32_range (ir_out r - ic_avail_out (c_rest c r))); lia]. }
      intros o1 o2 Ho. destruct o1 as [t1|]; destruct o2 as [t2|]; try contradiction.
      + destruct Ho as (HQt & M1 & M2 & M3). apply srel_ret.
        assert (HUt : UW t1 c r).
        { destruct HUr as (A1 & A2 & A3). split; [rewrite M2; exact A1|]. split; [rewrite M1; exact A2|rewrite M1, M3; exact A3]. }
        destruct (lv_fin_cong flush t1 t2 c r HQt HUt HR) as (E1 & E2 & E3).
        split; [exact E1|]. split; [exact E2|exact E3].
      +
        apply srel_ret.
        destruct (lv_fin_cong flush (s_rest s1 r) (s_rest s2 r) c r HQr HUr HR) as (E1 & E2 & E3).
        rewrite (lv_fin_pre flush (s_rest s1 r)), (lv_fin_pre flush (s_rest s2 r)) in E1, E2. rewrite (lv_fin_pre flush (s_rest s1 r)) in E3.
        cbn [fst snd] in E1, E2, E3.
        unfold lv_mem. split; [| split]; cbn [fst snd].
        * unfold zret_of_icall. f_equal; [exact (f_equal zr_consumed E1) | exact (f_equal zr_output E1) | exact (f_equal zr_strm E1)].
        * exact (IEQ_MEM _ _ E2).
        * exact (UWS_MEM _ E3).
    - apply srel_ret. destruct (lv_fin_cong flush (s_rest s1 r) (s_rest s2 r) c r HQr HUr HR) as (E1 & E2 & E3).
      split; [exact E1|]. split; [exact E2|exact E3].
  Qed.

  Theorem inflate_m_cong : forall flush s1 s2 zc,
    FASTC ->
    INV s1 -> ZC zc -> IEQ s1 s2 -> UWS s1 ->
    srel IRES (inflate_m ivar_ref H1 s1 zc flush) (inflate_m ivar_ref H2 s2 zc flush).
  Proof.
    intros flush s1 s2 zc fastc I1 Hzc HQ HUS. pose proof Hzc as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    pose proof (INV_check s1 I1) as CK1.
    assert (CK2 : inflateStateCheck s2 = false) by (unfold inflateStateCheck; rewrite (proj1 (proj1 HQ)); exact CK1).
    rewrite (inflate_m_W0 H1) by exact CK1. rewrite (inflate_m_W0 H2) by exact CK2.
    destruct (Z.eq_dec (is_mode s1) MEM) as [EM|NM].
    -
      assert (EM2 : is_mode s2 = MEM) by (rewrite (proj1 (proj1 HQ)); exact EM).
      rewrite (inf_loop_MEM flush (W0 s1 zc)); cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      rewrite (inf_loop_MEM flush (W0 s2 zc)); cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM2. change (MEM =? TYPE) with false. cbv iota. exact EM2. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      apply srel_ret. split; [reflexivity|]. cbn [fst]. split; [|unfold W0, s_entry; cbn [w_s]; rewrite EM; change (MEM =? TYPE) with false; cbv iota; exact HUS].
      unfold W0, s_entry. cbn [w_s]. rewrite EM, EM2. change (MEM =? TYPE) with false. cbv iota. exact HQ.
    - destruct (WINV_entry' s1 zc I1 Hzc) as [HW HP].
      pose proof (W0_WMID s1 s2 zc HQ HUS NM ltac:(lia)) as HM.
      pose proof (inf_loop_cong flush fastc _ _ HW HM) as L. pose proof (inf_loop_post flush _ HW HP) as P.
      destruct (inf_loop ivar_ref flush (W0 s1 zc)) as [st1 w1']. destruct (inf_loop ivar_ref flush (W0 s2 zc)) as [st2 w2'].
      destruct L as [-> HM']. destruct P as [HW' Pst].
      destruct w1' as [t1 c1 r1]. destruct w2' as [t2 c2 r2]. destruct HM' as (Ec & Er & HQ' & HU'). cbn [w_s w_c w_r] in Ec, Er, HQ', HU'. subst c2 r2.
      destruct st1 as [|rc].
      + apply inf_leave_cong; [exact HW' | exact HQ' | exact HU'].
      + apply srel_ret. split; [reflexivity|]. cbn [fst]. split; [exact HQ'|exact (UW_UWS _ _ _ HU')].
  Qed.
End TwoHooks.

Lemma inflate_INV' : forall s zc flush ch s' zr,
  INV s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> INV s'.
Proof.
  intros s zc flush ch s' zr HI Hz E.
  unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
  destruct (WINV_entry' s zc HI Hz) as [HW HP].
  pose proof (inf_loop_post flush (W0 s zc) HW HP) as L.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop w'].
  destruct stop as [|rc].
  - destruct L as [HW' _]. destruct w' as [s1 c1 r1].
    destruct (inf_leave hooks_pure flush (mkW s1 c1 r1) ch) as [p| | |] eqn:EL; try discriminate E.
    destruct p as [[s2 zr2] ch']. cbn [fst] in E.
    assert (E2 : s2 = s') by (injection E; intros _ X; exact X). subst s2.
    exact (inf_leave_INV flush s1 c1 r1 ch s' zr2 ch' HW' EL).
  - destruct L as [_ HI']. unfold sret in E. cbn [fst] in E.
    assert (E2 : w_s w' = s') by (injection E; intros _ X; exact X). rewrite <- E2. exact HI'.
Qed.

