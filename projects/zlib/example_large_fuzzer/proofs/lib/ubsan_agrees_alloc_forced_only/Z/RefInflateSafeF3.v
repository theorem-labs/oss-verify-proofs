(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInffast_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeF1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FastLoop.
  Variable x : ffx.
Variable s : inflate_state.
Variable ON : Z.
Variable usedL : Z.
Variable usedD : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis Xend : x_end x + 257 = ON.
  Hypothesis Xdm : x_dmask x = zmask (is_distbits s).
  Hypothesis Xlm : x_lmask x = zmask (is_lenbits s).
  Hypothesis HTL : TBLg LENS (code_at s (is_lencode s)) (is_lenbits s) usedL.
  Hypothesis HTD : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) usedD.

  Definition fstep (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
    match fast_trip x s f with
    | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
    | FBreak f' mode msg => inr (f', Some (mode, msg))
    end.

  Definition LPOST (f : ffs) (res : ffs * option (Z * option Z)) : Prop :=
    let '(f', mm) := res in
    FB ON f' /\ f_in f <= f_in f' <= x_last x + 5 /\ f_out f <= f_out f' <= ON
    /\ lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold (fpull2_if x f)) <= 8 * (f_in f' - f_in f) + f_bits f - f_bits f'
    /\ (mm = None \/ exists m msg, mm = Some (m, msg) /\ break_ok m msg).

  Lemma fast_loop_nat : forall m f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= x_last x + 5 -> f_out f + 258 <= ON ->
    8 * (x_last x + 5 - f_in f) + f_bits f + (ON - f_out f) < Z.of_nat m ->
    LPOST f (iterZ (Z.of_nat m) fstep (fun f0 => (f0, None)) f).
  Proof.
    induction m as [|m IH]; intros f HF Hbeg Hin Hout HM.
    { exfalso. unfold FB in HF. cbn in HM. lia. }
    rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    pose proof (fast_trip_spec x s ON usedL usedD Xin Xwn Xbeg HON Xdm Xlm HTL HTD f HF Hbeg Hout) as TS.
    cbv zeta in TS. destruct TS as (Hmod & Hc & T1 & T2).
    unfold fstep at 1. destruct (fast_trip x s f) as [f'|f' md msg].
    - destruct T1 as (HF' & Hi' & Ho' & Hcons).
      destruct (Z.ltb_spec (f_in f') (x_last x)); destruct (Z.ltb_spec (f_out f') (x_end x)); cbn [andb].
      +
        specialize (IH f' HF' ltac:(lia) ltac:(lia) ltac:(lia)).
        assert (HM' : 8 * (x_last x + 5 - f_in f') + f_bits f' + (ON - f_out f') < Z.of_nat m) by lia.
        specialize (IH HM'). unfold LPOST in *. destruct (iterZ (Z.of_nat m) fstep _ f') as [f'' mm].
        destruct IH as (A & B & C & D & E).
        pose proof (lneedg_range _ _ _ _ HTL (f_hold (fpull2_if x f'))) as [LR _].
        split; [exact A|]. split; [lia|]. split; [lia|]. split; [lia|exact E].
      + unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
      + unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
      + unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
    - destruct T1 as (HF' & Hi' & Ho' & Hcons).
      unfold LPOST. split; [exact HF'|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exists md, msg. split; [reflexivity|exact T2].
  Qed.

  Lemma fast_loop_spec : forall n f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= x_last x + 5 -> f_out f + 258 <= ON ->
    8 * (x_last x + 5 - f_in f) + f_bits f + (ON - f_out f) < n ->
    LPOST f (iterZ n fstep (fun f0 => (f0, None)) f).
  Proof.
    intros n f HF Hbeg Hin Hout HM.
    assert (Hn : 0 <= n) by (unfold FB in HF; lia).
    rewrite <- (Z2Nat.id n) by exact Hn. apply fast_loop_nat; try assumption. rewrite Z2Nat.id by exact Hn. exact HM.
  Qed.
End FastLoop.

Lemma fpull2_if_mod : forall x ON f, (forall i, 0 <= arr_get (x_input x) i < 256) -> FB ON f ->
  f_hold (fpull2_if x f) mod 2 ^ f_bits f = f_hold f.
Proof.
  intros x ON f Xin HF. pose proof HF as (B1 & B2 & B3 & B4 & B5). unfold fpull2_if.
  destruct (Z.ltb_spec (f_bits f) 15) as [L|L].
  - destruct (FB_fpull x ON Xin f HF ltac:(lia)) as (HP1 & _ & _ & P1b & P1m & _).
    destruct (FB_fpull x ON Xin (fpull x f) HP1 ltac:(lia)) as (HP2 & _ & _ & P2b & P2m & _).
    rewrite <- P1m. rewrite <- P2m at 1. rewrite P1b. symmetry. apply (mod_down (f_bits f) (f_bits f + 8)); [lia|].
    rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
  - apply Z.mod_small. lia.
Qed.

Section LenArm.

  Lemma inflate_fast_post : forall w0 s c r,
    WINV (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r -> PHI (mkW s c r) <= PHI w0 ->
    POST w0 ((amodify (fun w => LOAD (inflate_fast (RESTORE w))) ;;
              do s0 <- gs (fun s0 => s0) ;
              if is_mode s0 =? TYPE then set_back ivar_ref (-1) else aret tt)%am (mkW s c r)).
  Proof.
    intros w0 s c r HW E Hh6 Hl258 HP.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hbx & Htb). pose proof (CORE_length s HC) as HL0.
    pose proof HC as (_ & _ & _ & _ & CW5 & _).
    destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (usedL & HTL & _).
    destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (usedD & HTD & _).
    pose proof (T_root _ _ _ _ HTL) as RL15. pose proof (T_root _ _ _ _ HTD) as RD15.
    assert (Hb14 : ir_bits r <= 14).
    { destruct Hbx as [Hbx|Hbx]; [lia|]. rewrite lneed_lneedg in Hbx. pose proof (lneedg_range _ _ _ _ HTL (ir_hold r)). lia. }
    arun amodify_eq. unfold RESTORE. cbn [w_s w_c w_r].
    set (sR := iset_bits (iset_hold s (ir_hold r)) (ir_bits r)).
    set (cR := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)).
    rewrite inflate_fast_eq.
    set (x := ffx_of sR cR r).
    assert (HX : x_input x = ic_input c /\ x_last x = ir_next r + ir_have r - 5 /\ x_beg x = 0 /\ x_end x = ir_put r + ir_left r - 257
                 /\ x_wnext x = is_wnext s /\ x_dmask x = zmask (is_distbits sR) /\ x_lmask x = zmask (is_lenbits sR)).
    { subst x sR cR. unfold ffx_of. cbn [x_input x_last x_beg x_end x_wnext x_dmask x_lmask]. sacc.
      rewrite !wrap32_id by lia. repeat split; try reflexivity; lia. }
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    assert (HTL' : TBLg LENS (code_at sR (is_lencode sR)) (is_lenbits sR) usedL) by exact HTL.
    assert (HTD' : TBLg DISTS (code_at sR (is_distcode sR)) (is_distbits sR) usedD) by exact HTD.
    assert (EsR : is_hold sR = ir_hold r /\ is_bits sR = ir_bits r /\ is_lenbits sR = is_lenbits s /\ code_at sR (is_lencode sR) = code_at s (is_lencode s))
      by (subst sR; repeat split; reflexivity).
    destruct EsR as (EsRh & EsRb & EsRl & EsRc).
    set (ON := arr_len (ic_outbuf c)).
    assert (HF0 : FB ON (ff0_of sR cR)).
    { subst sR cR. unfold ff0_of, FB. cbn [f_in f_out f_bits f_hold f_ob]. sacc. repeat split; try lia. }
    unfold ff_loop. fold x. fold (fstep x sR).
    pose proof (fast_loop_spec x sR ON usedL usedD ltac:(rewrite X1; exact RIN) ltac:(rewrite X5; exact CW5) ltac:(rewrite X3; lia)
                  ltac:(subst ON; lia) ltac:(rewrite X4; subst ON; lia) X6 X7 HTL' HTD'
                  (8 * ic_avail_in cR + ic_avail_out cR + 80) (ff0_of sR cR) HF0) as L.
    pose proof (fpull2_if_mod x ON _ ltac:(rewrite X1; exact RIN) HF0) as HM.
    subst cR. unfold ff0_of in L, HM |- *. cbn [f_in f_out f_bits f_hold] in L, HM. rewrite EsRh, EsRb in L, HM |- *.
    revert L HM. sacc. intros L HM.
    specialize (L ltac:(lia) ltac:(lia) ltac:(subst ON; lia) ltac:(subst ON; lia)).
    unfold LPOST in L.
    match goal with |- POST _ (_ (LOAD (let '(f, mm) := ?it in _))) => destruct it as [f mm] end.
    destruct L as (HFf & Hin & Hout & Hcons & Hmm). pose proof HFf as (B1 & B2 & B3 & B4 & B5).
    cbn [f_in f_out f_bits f_hold] in Hin, Hout, Hcons, HM. rewrite EsRl, EsRc in Hcons.

    lazymatch type of Hcons with lneedg ?g ?rt ?h <= _ => pose proof (lneedg_range _ _ _ _ HTL h) as [LR _] end.
    assert (Hc8 : ir_bits r - 8 < 8 * (f_in f - ir_next r) + ir_bits r - f_bits f).
    { destruct Hbx as [Hbx|Hbx]; [lia|].
      rewrite lneed_lneedg in Hbx.
      pose proof (lneedg_mono LENS _ _ usedL HTL (ir_hold r) _ (ir_bits r) ltac:(lia) ltac:(rewrite HM; symmetry; apply Z.mod_small; lia) Hbx) as MONO. lia. }
    pose proof (Z.div_mod (f_bits f) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (f_bits f) 8 ltac:(lia)) as M8.
    pose proof (Z.div_pos (f_bits f) 8 ltac:(lia) ltac:(lia)) as Q8.
    pose proof (mod_pow2_range (f_hold f) (f_bits f mod 8) ltac:(lia)) as HM8.
    rewrite ff_fin_eq by lia.
    unfold ff_post. cbn [f_in f_out f_hold f_bits f_ob].
    rewrite X2, X4.
    replace (if f_in f - f_bits f / 8 <? ir_next r + ir_have r - 5 then 5 + (ir_next r + ir_have r - 5 - (f_in f - f_bits f / 8)) else 5 - (f_in f - f_bits f / 8 - (ir_next r + ir_have r - 5)))
      with (ir_next r + ir_have r - (f_in f - f_bits f / 8)) by (destruct (_ <? _); lia).
    replace (if f_out f <? ir_put r + ir_left r - 257 then 257 + (ir_put r + ir_left r - 257 - f_out f) else 257 - (f_out f - (ir_put r + ir_left r - 257)))
      with (ir_put r + ir_left r - f_out f) by (destruct (_ <? _); lia).
    rewrite !wrap32_id by (subst ON; lia).

    assert (CASES : mm = None \/ mm = Some (TYPE, None) \/ exists mg, mm = Some (BAD, Some mg)).
    { destruct Hmm as [->|(m & msg & -> & [[-> ->]|[-> Hm]])]; [left; reflexivity|right; left; reflexivity|].
      right; right. destruct msg as [mg|]; [exists mg; reflexivity|congruence]. }
    destruct CASES as [-> | [-> | [mg ->]]]; cbv iota beta; unfold LOAD; cbn [w_s w_c w_r]; subst sR; sacc.
    - arun gs_eq. sacc. rewrite E. change (LEN =? TYPE) with false. cbv iota. rewrite aret_eq. apply POST_ARun.
      + winv_splitE E.
        * core_keep HC. exact HL0.
        * unfold REGS. sacc. rewrite B5. regs_solve RIN. all: subst ON; lia.
        * split; [common_keep HCm|]. split; [left; lia|tables_keep Htb].
        * rewrite B5. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_norm E HP. lia.
    - arun gs_eq. sacc. change (TYPE =? TYPE) with true. cbv iota. rewrite set_back_ref. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * unfold REGS. sacc. rewrite B5. regs_solve RIN. all: subst ON; lia.
        * split; [common_keep HCm|lia].
        * rewrite B5. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_norm E HP. lia.
    - arun gs_eq. sacc. change (BAD =? TYPE) with false. cbv iota. rewrite aret_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * unfold REGS. sacc. rewrite B5. regs_solve RIN. all: subst ON; lia.
        * exact (proj2 HCm).
        * exact I.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_norm E HP. lia.
  Qed.
End LenArm.

Section LenSlow.

  Lemma len_tail : forall w0 s c r here,
    CORE s -> REGS c r -> is_mode s = LEN -> common s -> tables s ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    1 <= code_bits here <= ir_bits r -> ir_bits r - code_bits here < 8 ->
    ((exists sy, 0 <= sy < nsyms LENS /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
    64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0 ->
    POST w0 ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
              us (fun s0 => iset_length s0 (code_val here)) ;;
              if code_op here =? 0 then set_mode LIT
              else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
              else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
              else us (fun s0 => iset_extra s0 (Z.land (code_op here) 15)) ;; set_mode LENEXT ;; arm_LENEXT ivar_ref)%am
             (mkW s c r)).
  Proof.
    intros w0 s c r here HC HR E HCm Htb HWF HWB Hcb Hb8 Hsh HP.
    regs_open HR. pose proof (CORE_length s HC) as HL0.
    pose proof (code_val_nonneg here) as HV0.
    assert (HV16 : code_val here < 65536) by (unfold code_val; pose proof (land_65535 (Z.shiftr here 16)); lia).
    aflat. arun DROPBITS_eq. aflat. arun add_back_ref. aflat. arun us_eq. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
    set (r1 := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)).
    assert (HRd : REGS c r1).
    { subst r1. apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia]. }
    set (s1 := iset_length (iset_back s (swrap32 (is_back s + code_bits here))) (code_val here)).
    assert (HC1 : CORE s1) by (subst s1; core_keep HC; lia).
    assert (BADc : POST w0 ((go_bad MSG_invalid_literal_length_code) (mkW s1 c r1))).
    { unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1. subst s1. sacc. lia.
        + eapply REGS_cview; [exact HRd|reflexivity|reflexivity].
        + exact (proj2 HCm).
        + exact I.
        + subst r1. sacc. exact HWB.
      - phi_goal. subst r1. sacc. lia. }
    assert (TYPEc : POST w0 ((set_back ivar_ref (-1) ;; set_mode TYPE)%am (mkW s1 c r1))).
    { arun set_back_ref. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1. subst s1. sacc. lia.
        + exact HRd.
        + split; [common_keep HCm | subst r1; sacc; exact Hb8].
        + subst r1. sacc. exact HWF.
        + subst r1. sacc. exact HWB.
      - phi_goal. subst r1. sacc. lia. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. exact BADc. }
    cbn [nsyms] in Hsy. pose proof (lens_sym_cases sy Hsy) as L.
    destruct (sym_entry LENS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop. rewrite Hv in *.
    destruct L as [[L1 L2]|[[L1 L2]|[(L1 & L2 & L3)|[L1|L1]]]].
    -
      rewrite L1. cbn [Z.eqb]. rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC1. subst s1. sacc. lia.
        * exact HRd.
        * split; [common_keep HCm|]. split; [subst r1; sacc; exact Hb8 | tables_keep Htb].
        * subst r1. sacc. exact HWF.
        * subst r1. sacc. exact HWB.
      + phi_goal. subst r1. sacc. lia.
    -
      rewrite L1. cbn [Z.land Z.eqb negb]. exact TYPEc.
    -
      destruct (len_op_facts op L1) as (F1 & F2 & F3 & F4 & F5).
      replace (op =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite F5, F2, F3. cbn [Z.eqb negb].
      pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
      aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm LENEXT (arm_LENEXT ivar_ref) _ _ _ _ arm_LENEXT_safe).
      + winv_split.
        * core_keep HC1. subst s1. sacc. lia.
        * exact HRd.
        * split; [common_keep HCm|]. split; [left; subst r1; sacc; exact Hb8|]. split; [tables_keep Htb|]. subst s1. sacc. lia.
        * subst r1. sacc. exact HWF.
        * subst r1. sacc. exact HWB.
      + reflexivity.
      + phi_goal. subst r1. sacc. lia.
    - rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
    - rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
  Qed.

  Lemma len_slow : forall w0 s c r,
    CORE s -> REGS c r -> is_mode s = LEN -> common s ->
    (ir_bits r < 8 \/ ir_bits r < lneed s (is_lencode s) (is_lenbits s) (ir_hold r)) -> tables s ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0 ->
    POST w0 ((do s0 <- gs (fun s0 => s0) ;
              do here <- DECODE1 (is_lencode s0) (is_lenbits s0) ;
              do here <- (if negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0) then
                            let last := here in
                            do here <- DECODE2 (is_lencode s0) last ;
                            DROPBITS (code_bits last) ;;
                            add_back ivar_ref (code_bits last) ;;
                            aret here
                          else aret here) ;
              DROPBITS (code_bits here) ;;
              add_back ivar_ref (code_bits here) ;;
              us (fun s1 => iset_length s1 (code_val here)) ;;
              if code_op here =? 0 then set_mode LIT
              else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
              else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
              else
                us (fun s1 => iset_extra s1 (Z.land (code_op here) 15)) ;;
                set_mode LENEXT ;; arm_LENEXT ivar_ref)%am (mkW s c r)).
  Proof.
    intros w0 s c r HC HR E HCm Hbx Htb HWF HWB HP0. arun gs_eq. regs_open HR.
    assert (HW0 : WINV (mkW s c r)).
    { unfold WINV. cbn [w_s w_c w_r]. rewrite E. mred. split; [exact HC|]. split; [exact HR|]. split; [|split; [exact HWF|exact HWB]].
      split; [exact HCm|]. split; [exact Hbx|exact Htb]. }
    destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (used & HT & _).
    pose proof (T_root _ _ _ _ HT) as HR15.
    aflat.
    destruct (DECODE1_spec c s (is_lencode s) LENS (is_lenbits s) used HT r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      destruct (root_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
      rewrite <- Eh in Hbits, RLk, RNk.
      assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
      { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
      aflat. acase Clink.
      +
        apply andb_prop in Clink as [Cnz Clink]. apply Z.eqb_eq in Clink. apply Bool.negb_true_iff in Cnz. apply Z.eqb_neq in Cnz.
        assert (HLk : is_linkb here = true).
        { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
          exact (notlink_land240 LENS here SH ltac:(discriminate) Cnz Clink). }
        destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
        aflat.
        destruct (DECODE2_spec c s (is_lencode s) LENS (is_lenbits s) used HT r1 here HR1 Eh HLk Hle)
          as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)].
        * eapply POST_bind_run; [exact EQ2|]. cbv beta iota.
          pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_phi r1 r2 HP2) as PH2.
          pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
          pose proof (sub_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s)
                        (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
          rewrite <- Eh in SC.
          specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
          unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
          aflat. arun DROPBITS_eq. aflat. arun add_back_ref. arun aret_eq. sacc.
          rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
          assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
          { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
          assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
          { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
            destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
            rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
            rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
          apply len_tail;
            first [ assumption
                  | core_keep HC; apply CORE_length; exact HC
                  | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
                  | common_keep HCm
                  | tables_keep Htb
                  | rewrite Eo2, Eo1; exact HWF
                  | rewrite Ep2, Ep1; exact HWB
                  | sacc; lia ].
        * eapply POST_bind_leave; [exact EQ2|].
          pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & _).
          apply (WINV_regs s c r r2 HW0 HR2 ltac:(rewrite Eo2; exact Eo1) ltac:(rewrite Ep2; exact Ep1)).
          rewrite E. mred. intros _. split; [exact HCm|]. split; [|exact Htb].
          right. rewrite lneed_lneedg. exact Hb2.
      +
        assert (HLk : is_linkb here = false).
        { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
          rewrite (land240_small (code_op here)) in Clink by lia.
          replace (code_op here =? 0) with false in Clink by (symmetry; apply Z.eqb_neq; lia). discriminate Clink. }
        destruct (RNk HLk) as [Hbr SH].
        arun aret_eq.
        assert (B8 : ir_bits r1 - code_bits here < 8).
        { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
          rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
          rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
        apply len_tail;
          first [ assumption
                | rewrite Eo1; exact HWF
                | rewrite Ep1; exact HWB
                | lia ].
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1).
      rewrite E. mred. intros _. split; [exact HCm|]. split; [|exact Htb].
      right. rewrite lneed_lneedg. pose proof (lneedg_range LENS _ _ used HT (ir_hold r1)) as [_ LR]. lia.
  Qed.

  Lemma arm_LEN_safe : arm_safe LEN (arm_LEN ivar_ref).
  Proof.
    intros w0 s c r HW E HP. unfold arm_LEN. arun gr_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb).
    assert (HP0 : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0).
    { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank LEN) with 0 in HP. lia. }
    acase Cfast.
    - (* zlib 1.4: the guard's extra conjunct [ir_bits r <? 8] is not needed here *)
      apply andb_prop in Cfast as [Cfast _].
      apply andb_prop in Cfast as [Cfast C2]. apply andb_prop in Cfast as [_ C1]. apply Z.leb_le in C1. apply Z.leb_le in C2.
      exact (inflate_fast_post w0 s c r HW0 E C1 C2 HP).
    - aflat. arun set_back_ref.
      apply len_slow; first [ assumption
                              | core_keep HC; apply CORE_length; exact HC
                              | common_keep HCm
                              | rewrite (lneed_keep s (iset_back s 0)) by reflexivity; exact Hbx
                              | tables_keep Htb ].
  Qed.

  Lemma arm_LEN__safe : arm_safe LEN_ (arm_LEN_ ivar_ref).
  Proof.
    intros w0 s c r HW E HP. unfold arm_LEN_. arun set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as (HCm & Hb8 & Htb).
    apply (POST_arm LEN (arm_LEN ivar_ref) _ _ _ _ arm_LEN_safe).
    - winv_split.
      + core_keep HC. apply CORE_length; exact HC.
      + exact HR.
      + split; [common_keep HCm|]. split; [left; exact Hb8|tables_keep Htb].
      + exact HWF.
      + exact HWB.
    - reflexivity.
    - phi_norm E HP. lia.
  Qed.
End LenSlow.
