(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_It0. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_It3. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3.S_It1. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_It3 S_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section S7IT5.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Definition rsL : list (Z * Z) := [(sp + -136, 32); (p + 1384, 5776)].

Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma cmem_mpost : forall M M' lo hi,
  CM M -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' lo hi 0 0 ->
  ((lo = p + 1384 /\ hi = p + 7160) \/ (lo = sp + -136 /\ hi = sp + -104)) -> CM M'.
Proof using C zc ret pb cf bits.
  intros M M' lo hi HM [HA HW] Hr. pose proof C as C'. open_itc C'. xaddr. unfold ZSEP in *. open_cmem HM.
  unfold cmem. split_conj.
  - apply HW. exact Wf.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact HslD | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact HslL | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hext | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hbase | lia_std | lia_std].
Qed.

Lemma cnt_mpost : forall M M' f, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 f -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 f.
Proof using C zc ret pb wf cf bits nx codes lens_ofs lf ty.
  intros M M' f H [HA HW]. pose proof C as C'. open_itc C'.
  eapply mem_arr_magree; [exact HA | exact H | lia_std | lia_std].
Qed.

Lemma mpostL_of_tbl : forall M M', mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M M M' rsL _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. right. left. lia.
Qed.
Lemma mpostL_of_cnt : forall M M', mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M M M' rsL _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. left. lia.
Qed.

Lemma spure_st1 : forall st, SP st -> SP (tr_st1 X st).
Proof using.
  intros st HP. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st1]. split_conj; try assumption.
  - apply tr_count_range0. exact HCr.
  - apply tr_tbl1_range. exact HTr.
  - unfold tr_count. rewrite arr_len_set. exact CL.
  - rewrite it_fill_len_tr. exact TL.
Qed.
Lemma spure_st3 : forall st, SP st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st -> SP (tr_st3 X st).
Proof using.
  intros st HP HL HD HN. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st3]. split_conj; try assumption.
  - unfold ZSEP. right. exact HL.
  - unfold ZSEP. right. exact HD.
  - lia_std.
  - lia_std.
  - apply tr_count_range0. exact HCr.
  - apply tr_tbl2_range. exact HTr.
  - unfold tr_count. rewrite arr_len_set. exact CL.
  - unfold tr_tbl2. rewrite arr_len_set. rewrite it_fill_len_tr. exact TL.
Qed.

Lemma trip_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> CM M -> SM st M -> SP st ->
  it_trip_ok X 288 320 1444 st = true -> 1 <= mx ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall st' R' M', it_step X st = ItCont st' -> CR R' [] -> SR st' R' [] ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96880 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItBreak st' -> CR R' [] -> SR st' R' [] -> zget_l R' [] kS8 = t_len st' - t_drop st' ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97336 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItFail st' -> CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97396 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96880 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HSM HP TOK Hmx HcB KC KB KF.
  pose proof HP as HP'. open_spure HP'. open_smem HSM.
  pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm.
  eapply here_s; try eassumption; try lia.
  intros R1 HC1 HS1 L10 L9.
  eapply fill_s; try eassumption.
  { open_cmem HM. assumption. }
  intros R2 M2 HC2 HS2 L8 HPO1 Wp2 Htbl2.
  pose proof (cmem_mpost M M2 _ _ HM HPO1 ltac:(left; split; reflexivity)) as HM2.
  pose proof (cnt_mpost M M2 _ Hcnt HPO1) as Hcnt2.
  eapply count_s; try eassumption.
  -
    intros R3 M3 HC3 HS3 L8' HPO2 HM3 HSM3 Hbrk.
    eapply sub_s; try eassumption.
    +
      intros R4 HC4 HS4 Hsub. eapply (KC (tr_st1 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * apply spure_st1. exact HP.
    +
      intros R4 M4 HC4 HS4 HPO3 HM4 HSM4 Hsub Hne HCU HLOW HDR HNX. eapply (KC (tr_st3 X st) R4 M4); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 |].
        eapply mpostL_trans; [apply mpostL_of_cnt; exact HPO2 | apply mpostL_of_tbl; exact HPO3].
      * apply spure_st3; assumption.
    +
      intros R4 HC4 LA6 Hsub Hne. eapply (KF (tr_st2 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * cbn [t_tbl tr_st2]. apply tr_tbl1_range. exact HTr.
  -
    intros R3 M3 HC3 HS3 L8' HPO2 HM3 HSM3 Hbrk.
    assert (EL : tr_len X st = t_len st).
    { unfold tr_brk in Hbrk. apply andb_prop in Hbrk as [B1 B2]. unfold tr_len. rewrite B1.
      cbn [x_max itm_ctx] in *. rewrite B2. reflexivity. }
    assert (HHF : 0 <= tr_huff st).
    { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
      pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
      rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
      destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
      assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
    eapply (KB (tr_st1 X st) R3 M3); try assumption.
    all: try (rewrite it_step_eq, Hbrk; reflexivity).
    all: try (cbn [t_len t_drop tr_st1]; rewrite EL; first [exact L8' | lia]).
    all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2]).
    all: try (apply spure_st1; exact HP).
    all: cbn [t_used t_huff tr_st1]; first [exact HHF | lia].
Qed.

Lemma main_loop_s : forall (PI : ItSt -> Prop),
  (forall st, PI st -> ty = CODES -> tr_w st < it_match ty) ->
  (forall st st', PI st -> it_step X st = ItCont st' -> PI st') ->
  forall k st Rb l M0 M MD T,
  it_loop_ok k X 288 320 1444 st = true -> 1 <= mx -> PI st ->
  m_halted MD = None -> CR Rb l -> SR st Rb l -> CM M -> SM st M -> SP st ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M rsL ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inl st' ->
      CR R' [] -> SR st' R' [] -> zget_l R' [] kS8 = t_len st' - t_drop st' ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M' rsL -> CM M' -> SM st' M' -> SP st' ->
      (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444) ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97336 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inr st' ->
      CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97396 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96880 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros PI HI1 HI2. induction k as [|k IH]; intros st Rb l M0 M MD T HOK Hmx PIs Hh HC HS HM HSM HP HPL KB KF.
  { cbn [it_loop_ok] in HOK. discriminate. }
  rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
  eapply trip_s; try eassumption.
  - exact (HI1 _ PIs).
  - intros st' R' M' Hstep HC' HS' HPO HM' HSM' HP'. rewrite Hstep in REST.
    eapply (IH st' R' [] M0 M' MD T); try eassumption.
    + eapply HI2; eassumption.
    + eapply mpostL_trans; eassumption.
    + intros st'' R'' M'' Hl. eapply KB. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
    + intros st'' R'' M'' Hl. eapply KF. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
  - intros st' R' M' Hstep HC' HS' L8 HPO HM' HSM' HP' B1 B2 B3. rewrite Hstep in REST.
    eapply KB; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
    + intros Hne. destruct (Z.eqb_spec (t_huff st') 0); [lia_std|]. cbn [negb] in REST.
      apply andb_prop in REST as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia_std.
  - intros st' R' M' Hstep HC' LA6 HPO HM' HSM' HW HTR. eapply KF; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
Qed.
End S7IT5.
