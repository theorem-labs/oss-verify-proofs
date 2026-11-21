(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall
  HarnessKit HarnessFacts InflateLeave InflateRc InflateTin.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition IRCS : list Z := [Z_OK; Z_STREAM_END; Z_NEED_DICT; Z_STREAM_ERROR; Z_DATA_ERROR; Z_MEM_ERROR; Z_BUF_ERROR].

Lemma RL_lv_rc : forall flush r, RL (ir_ret r) -> In (lv_rc flush r) IRCS.
Proof.
  intros flush r H. unfold lv_rc, IRCS.
  destruct ((((lv_in r =? 0) && (lv_out r =? 0)) || (flush =? Z_FINISH)) && (ir_ret r =? Z_OK)); [cbn; tauto|].
  destruct H as [-> | [-> | ->]]; cbn; tauto.
Qed.
Lemma RR_in : forall rc, RR rc -> In rc IRCS.
Proof. intros rc [-> | [-> | ->]]; cbn; tauto. Qed.

Definition IPOST (zc : ZCall) (z : ZRet) : Prop :=
  zret_ok z
  /\ 0 <= zr_consumed z <= zlength (zc_input zc)
  /\ 0 <= zlength (zr_output z) <= zc_avail_out zc
  /\ In (zr_rc z) IRCS
  /\ ((zr_rc z = Z_NEED_DICT \/ zr_rc z = Z_MEM_ERROR \/ zr_rc z = Z_STREAM_ERROR)
      \/ (zs_total_out (zr_strm z) = wrap64 (zs_total_out (zc_strm zc) + zlength (zr_output z))
          /\ zs_total_in (zr_strm z) = wrap64 (zs_total_in (zc_strm zc) + zr_consumed z)))
  /\ (zr_rc z = Z_OK -> 0 < zr_consumed z \/ 0 < zlength (zr_output z)).

Lemma lv_rc_OK : forall flush r, lv_rc flush r = Z_OK -> lv_in r <> 0 \/ lv_out r <> 0.
Proof.
  intros flush r. unfold lv_rc.
  destruct (Z.eqb_spec (lv_in r) 0) as [E1|E1]; [| intros _; left; exact E1].
  destruct (Z.eqb_spec (lv_out r) 0) as [E2|E2]; [| intros _; right; exact E2].
  cbn [andb orb]. destruct (Z.eqb_spec (ir_ret r) Z_OK) as [E3|E3]; [intros X; discriminate X | intros X; exfalso; exact (E3 X)].
Qed.

Section Call.
  Variable iv : ivariant.

  Lemma inflate_p_W1M : forall ans st zc flush,
    inflateStateCheck st = false ->
    inflate_p iv ans st zc flush =
      let '(stop, w) := inf_loop iv flush (W1M st (icall_of_zcall zc)) in
      match stop with
      | SRet rc => ((w_s w, zret_of_icall (w_c w) rc), None)
      | SLeave => inf_leave_p ans flush w
      end.
  Proof.
    intros ans st zc flush Hc. unfold inflate_p. rewrite Hc. unfold W1M, s_entryM, LOAD, wset_r. cbn.
    destruct (is_mode st =? TYPE); reflexivity.
  Qed.

  Theorem inflate_p_post : forall ans s zc flush,
    UI s -> zcall_ok zc ->
    let '(p, asked) := inflate_p iv ans s zc flush in
    UI (fst p) /\ IPOST zc (snd p).
  Proof.
    intros ans s zc flush U ZC.
    pose proof (zcall_NI zc ZC) as HNI. pose proof (zcall_NO zc ZC) as HNO.
    destruct (inflateStateCheck s) eqn:Hc.
    - unfold inflate_p. rewrite Hc. cbn [fst snd]. split; [exact U|].
      destruct ZC as (_ & _ & _ & Zti & Zto & Zad & Zdt). unfold IPOST, zret_ok, IRCS. cbn.
      rewrite arr_slice_length. pose proof (zlength_nonneg (zc_input zc)).
      split; [repeat split; lia|]. split; [lia|]. split; [lia|]. split; [cbn; tauto|]. split; [left; right; right; reflexivity|].
      intros X; discriminate X.
    - rewrite (inflate_p_W1M ans s zc flush Hc).
      pose proof (ui_entry s zc U ZC) as PI.
      pose proof (inf_loop_exit iv flush _ _ (arr_len (is_window s)) (zs_total_out (zc_strm zc)) HNI HNO _ PI) as X.
      pose proof (inf_loop_rc iv flush _ _ (arr_len (is_window s)) (zs_total_out (zc_strm zc)) HNI HNO _ PI ltac:(left; reflexivity)) as RC.
      cbv zeta in X, RC. destruct (inf_loop iv flush (W1M s (icall_of_zcall zc))) as [stop [s' c' r']] eqn:EQL. cbn [fst snd w_s w_c w_r] in X, RC |- *.
      destruct X as (LR & SI & BI & CK & EQ).
      pose proof (inf_loop_tin iv flush (W1M s (icall_of_zcall zc))) as TI. rewrite EQL in TI. cbn [fst snd] in TI. unfold tinw, W1M in TI. cbn [w_c] in TI.
      replace (ic_total_in (icall_of_zcall zc)) with (zs_total_in (zc_strm zc)) in TI by reflexivity.
      pose proof LR as LR'. apply LRNGq_iff in LR'. destruct LR' as (_ & CI & RI & _ & CR). unfold CROSS in CR.
      destruct CI as (ClNI & ClNO & Cni & Cai & Cnai & Cno & Cao & Cnao & _). destruct RI as (Rnx & Rhv & Rnh & Rpt & Rlf & Rpl & Rin & Rout & Rol & _).
      destruct stop as [|rc].
      + cbv iota in TI. (* 1.4: inf_loop_tin keeps total_in on a leave only *)
        pose proof (leave_p_ui ans flush _ _ _ _ s' c' r' HNI HNO (conj LR (conj SI (conj BI CK)))) as L.
        destruct (inf_leave_p ans flush (mkW s' c' r')) as [[s2 z] asked]. cbn [fst snd] in L |- *.
        destruct L as (U2 & ZR & C1 & O1 & RCZ). split; [exact U2|].
        split; [exact ZR|]. rewrite C1, O1. split; [lia|]. split; [lia|].
        destruct RCZ as [(-> & TO & TN) | ->].
        * split; [apply RL_lv_rc; exact RC|]. split.
          { right. rewrite TO, TN, TI. unfold lv_out, lv_in. rewrite CR, Rin. split; [reflexivity | f_equal; lia]. }
          intros R0. destruct (lv_rc_OK flush r' R0) as [E|E]; unfold lv_in, lv_out in E; [left; lia | right; lia].
        * split; [cbn; tauto|]. split; [left; right; left; reflexivity|]. intros X; discriminate X.
      + cbn [fst snd w_s w_c w_r]. destruct (EQ rc eq_refl) as [Eh Eb].
        destruct (ret_ui _ _ _ _ (mkW s' c' r') rc (conj LR (conj SI (conj BI CK))) Eh Eb) as [U2 ZR]. cbn [w_s w_c] in U2, ZR.
        split; [exact U2|]. split; [exact ZR|].
        unfold zret_of_icall. cbn [zr_consumed zr_output zr_rc]. rewrite arr_slice_length.
        split; [lia|]. split; [lia|]. split; [apply RR_in; exact RC|]. split; [left; exact RC|].
        intros R0. exfalso. destruct RC as [E|[E|E]]; rewrite E in R0; discriminate R0.
  Qed.
End Call.
