(* 1.4's lext[29] is 71 where the model has 203, so the walk reads only lext[0..28].
   it_lx: every trip of a LENS table reads a work entry below 286. it_lx_intro proves it from the model's own
   sorted-work facts (RefInflateSafeH.ItSim2.trip_spec / wsym_facts) when codes <= 286. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ModelRel ItDefs ItGen.
(* in this tree RefInflateSafeH's modules are their own files *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItMath ItSort ItSimPre ItSim1 ItSim2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
Local Open Scope Z_scope.

Fixpoint it_lx (n : nat) (x : ItCtx) (st : ItSt) : Prop :=
  match n with
  | O => True
  | S n' => ((x_ty x = LENS -> arr_get (t_work st) (t_sym st) < 286) /\
             (x_ty x = CODES -> arr_get (t_work st) (t_sym st) < 19)) /\
            match it_step x st with ItCont st' => it_lx n' x st' | _ => True end
  end.

Lemma it_lx_S : forall n x st, it_lx (S n) x st =
  (((x_ty x = LENS -> arr_get (t_work st) (t_sym st) < 286) /\
    (x_ty x = CODES -> arr_get (t_work st) (t_sym st) < 19)) /\
   match it_step x st with ItCont st' => it_lx n x st' | _ => True end).
Proof. reflexivity. Qed.

Lemma it_lx_dists : forall n x st, x_ty x = DISTS -> it_lx n x st.
Proof.
  induction n as [|n IH]; intros x st HT; [exact I|]. rewrite it_lx_S.
  split; [split; intros E; rewrite HT in E; discriminate E|].
  destruct (it_step x st) as [s|s|s]; [apply IH; exact HT| exact I| exact I].
Qed.

Lemma lx_loop : forall ty lens lens_ofs codes ll wl table root,
  0 <= codes <= 288 ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
  ll = lens_list lens lens_ofs codes -> wl = wl_of ll ->
  MINL wl <= root <= MAXL wl -> 1 <= MAXL wl -> TM wl (MAXL wl) <= 2 ^ MAXL wl ->
  (ty = CODES -> codes <= 19) -> (ty = LENS -> codes <= 286) ->
  forall n k st, 0 <= k < NZ wl -> StM ll wl table root k st -> it_lx n (X ty lens lens_ofs wl table root) st.
Proof.
  intros ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty H286.
  induction n as [|n IH]; intros k st Hk SM; [exact I|].
  rewrite it_lx_S.
  pose proof (trip_spec ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k st Hk SM) as TS.
  pose proof (wsym_facts ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k Hk) as [WR _].
  pose proof SM as (_ & Es & _ & _ & _ & _ & _ & _ & _ & _ & Hw).
  split.
  - split; intros HT; unfold X in HT; cbn [x_ty] in HT; rewrite Es, (Hw k Hk).
    + specialize (H286 HT). lia.
    + specialize (Hty HT). lia.
  - destruct (it_step (X ty lens lens_ofs wl table root) st) as [st'|st'|st']; [|exact I|exact I].
    destruct TS as (Hk1 & _ & SM' & _). exact (IH (k + 1) st' ltac:(lia) SM').
Qed.

Lemma it_lx_intro : forall ty lens lens_ofs codes tbl table bits work cnt max min root,
  0 <= codes <= 288 -> (ty = CODES -> codes <= 19) -> (ty = LENS -> codes <= 286) ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) -> codes <= arr_len work ->
  cnt = itm_count lens lens_ofs codes -> itm_max cnt = max -> max <> 0 ->
  itm_reject ty max (it_left_check cnt) = false ->
  itm_min cnt max = min -> itm_root bits max min = root ->
  it_lx (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table root max)
        (itm_st0 min table root cnt tbl (itm_work lens lens_ofs codes (itm_offs cnt) work)).
Proof.
  intros ty lens lens_ofs codes tbl table bits work cnt max min root Hcodes Hty19 H286 Hlens HWN Ecnt EM NZm NR EMIN ER.
  remember (lens_list lens lens_ofs codes) as ll eqn:Ell.
  remember (wl_of ll) as wl eqn:Ewl.
  pose proof (HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as HW0.
  pose proof (HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as HL0.
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z.ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as Hll'.
  pose proof (count_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as [CL CC].
  unfold itm_count in Ecnt.
  change (it_count lens lens_ofs codes (it_zero_count (arr_make 16 0))) with (CNT lens lens_ofs codes) in Ecnt.
  subst cnt. set (C := CNT lens lens_ofs codes) in *.
  pose proof (MAXL_spec wl HW0 HL0) as [M1 [M2 M3]].
  unfold itm_max in EM. rewrite (find_max_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) in EM. subst max.
  assert (HM1 : 1 <= MAXL wl) by lia.
  unfold itm_min in EMIN. rewrite (find_min_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC HM1) in EMIN. subst min.
  unfold itm_reject in NR. rewrite (left_check_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) in NR.
  pose proof (LEFT_sign wl HW0 HL0) as [LS1 [LS2 LS3]].
  destruct (Z.ltb_spec (LEFT wl) 0) as [HLn|HLn]; [simpl in NR; discriminate NR|].
  assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl).
  { destruct (Z.le_gt_cases (TM wl (MAXL wl)) (2 ^ MAXL wl)) as [G|G]; [exact G|]. apply LS1 in G. lia. }
  assert (RR : MINL wl <= root <= MAXL wl).
  { pose proof (MINL_spec wl HW0 HL0 HM1) as [A _]. subst root. unfold itm_root.
    destruct (Z.ltb_spec (MAXL wl) bits); [destruct (Z.ltb_spec (MAXL wl) (MINL wl)) | destruct (Z.ltb_spec bits (MINL wl))]; lia. }
  pose proof (root_range wl HW0 HL0 root RR HM1) as RR2.
  pose proof (offs_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as [OL OC].
  unfold itm_offs. change (it_offs C (arr_make 16 0)) with (OFS C). set (O := OFS C) in OL, OC |- *.
  unfold itm_work. rewrite (sort_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl O work OL OC).
  unfold itm_ctx, itm_st0. rewrite itm_used_pow2 by lia.
  change (mkItCtx ty lens lens_ofs table root (MAXL wl) (2 ^ root - 1)) with (X ty lens lens_ofs wl table root).
  pose proof (NZ_pos wl HW0 HL0 HM1) as NP.
  pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
  apply (lx_loop ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty19 H286 _ 0); [lia|].
  unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
  pose proof (lay_inv wl HW0 HL0 root RR HM1 0 ltac:(lia)) as [LI _].
  assert (HS : islong wl root 0 = false).
  { unfold islong. rewrite (len_at_0 wl HW0 HL0 HM1). apply Z.ltb_ge. lia. }
  destruct (LI HS) as [N0 [C0 U0]]. rewrite N0, C0, U0. unfold ItDefs.drop, ItDefs.low. rewrite HS.
  rewrite (len_at_0 wl HW0 HL0 HM1).
  repeat split; try reflexivity; try lia.
  - intros l Hl. rewrite CC by lia. unfold REM. rewrite (len_at_0 wl HW0 HL0 HM1).
    pose proof (MINL_spec wl HW0 HL0 HM1) as [A [B D]]. unfold rank_at. rewrite (len_at_0 wl HW0 HL0 HM1).
    rewrite (OFF_below_MINL wl HW0 HL0 (MINL wl)) by lia.
    destruct (Z.ltb_spec l (MINL wl)); [apply D; lia|]. destruct (Z.eqb_spec l (MINL wl)); [subst; lia | reflexivity].
  - intros j Hj. rewrite Ewl in Hj |- *. apply (sorted_work ll Hll'); [|exact Hj].
    pose proof (NZ_le_NC ll Hll') as NN. rewrite (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in NN. lia.
Qed.
