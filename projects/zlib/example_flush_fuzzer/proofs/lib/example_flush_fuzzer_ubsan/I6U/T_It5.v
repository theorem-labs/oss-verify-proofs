(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import ZTac ZMem ZCall ZCallL ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6S Require Import S_It0 S_It3 S_It4 S_It5.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6U Require Import Base T_It1 T_It2 T_It3 T_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section U7IT5.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregs_t ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs_t p).
#[local] Abbreviation CM := (cmem_t ty lf lens_ofs codes nx bits wf p sp).
#[local] Abbreviation SM := (smem_t p sp).
#[local] Abbreviation C192' := (C192 ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).



Definition rsL : list (Z * Z) := [(sp + -136, 32); (p + 1368, 5776)].
Ltac xaddr := pose proof (xaddr_facts_t _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).

Lemma cmem_mpost : forall M M' lo hi,
  CM M -> mpost R_segs M M' lo hi 0 0 ->
  ((lo = p + 1368 /\ hi = p + 7144) \/ (lo = sp + -136 /\ hi = sp + -104)) -> CM M'.
Proof using C zc ret pb cf.
  intros M M' lo hi HM [HA HW] Hr. pose proof C as C'. open_itc C'. xaddr. unfold ZSEP in *. open_cmem_t HM.
  unfold cmem_t. split_conj.
  - apply HW. exact Wf.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl0 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl8 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl16 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl24 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl32 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hext | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hbase | lia_std | lia_std].
Qed.

Lemma cnt_mpost : forall M M' f, mem_arr 2 R_segs M (sp + -136) 16 f -> mpost R_segs M M' (p + 1368) (p + 7144) 0 0 ->
  mem_arr 2 R_segs M' (sp + -136) 16 f.
Proof using C zc ret pb wf cf bits nx codes lens_ofs lf ty.
  intros M M' f H [HA HW]. pose proof C as C'. open_itc C'.
  eapply mem_arr_magree; [exact HA | exact H | lia_std | lia_std].
Qed.

Lemma mpostL_of_tbl : forall M M', mpost R_segs M M' (p + 1368) (p + 7144) 0 0 -> mpostL R_segs M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 R_segs M M M' rsL _ _ _ _ (mpostL_refl R_segs M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. right. left. lia.
Qed.
Lemma mpostL_of_cnt : forall M M', mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> mpostL R_segs M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 R_segs M M M' rsL _ _ _ _ (mpostL_refl R_segs M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. left. lia.
Qed.

Lemma trip_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kT1 = t_len st - t_drop st -> zget_l Rb l kA2 = p + 792 + 2 * t_sym st ->
  CM M -> SM st M -> SP st ->
  it_trip_ok X 288 320 1444 st = true -> 1 <= mx -> (ty = CODES -> arr_get work1Ar (t_sym st) < 20) ->
  (forall st' R' M', it_step X st = ItCont st' -> CR R' [] -> SR st' R' [] ->
      zget_l R' [] kT1 = t_len st' - t_drop st' -> zget_l R' [] kA2 = p + 792 + 2 * t_sym st' ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      realizes R_segs (zcfg R_segs 139704 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItBreak st' -> CR R' [] -> SR st' R' [] -> zget_l R' [] kT1 = 256 * (t_len st' - t_drop st') ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes R_segs (zcfg R_segs 140440 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItFail st' -> CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139704 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 LT2 HM HSM HP TOK Hmx HW0 KC KB KF.
  pose proof HP as HP'. open_spure HP'. open_smem_t HSM.
  pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm.
  eapply here_t; try eassumption; try lia.
  intros R1 HC1 HS1 L1 L2 L7.
  eapply fill_t; try eassumption.
  { open_cmem_t HM. assumption. }
  intros R2 M2 HC2 HS2 L1' L4 HPO1 Wp2 Htbl2.
  pose proof (cmem_mpost M M2 _ _ HM HPO1 ltac:(left; split; reflexivity)) as HM2.
  pose proof (cnt_mpost M M2 _ Hcnt HPO1) as Hcnt2.
  eapply count_t; try eassumption.
  -
    intros R3 M3 HC3 HS3 L4' L6 HPO2 HM3 HSM3 Hbrk.
    eapply sub_t; try eassumption.
    +
      intros R4 HC4 HS4 L1'' L2'' Hsub. eapply (KC (tr_st1 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * apply spure_st1. exact HP.
    +
      intros R4 M4 HC4 HS4 L1'' L2'' HPO3 HM4 HSM4 Hsub Hne HCU HLOW HDR HNX. eapply (KC (tr_st3 X st) R4 M4); try assumption.
      all: try (rewrite it_step_eq, Hbrk, Hsub; cbn [x_ty itm_ctx]; rewrite Hne; reflexivity).
      all: try (cbn [t_len t_drop tr_st3]; exact L1'').
      all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 |];
                eapply mpostL_trans; [apply mpostL_of_cnt; exact HPO2 | apply mpostL_of_tbl; exact HPO3]).
      all: apply spure_st3; assumption.
    +
      intros R4 HC4 LA6 Hsub Hne. eapply (KF (tr_st2 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * cbn [t_tbl tr_st2]. apply tr_tbl1_range. exact HTr.
  -
    intros R3 M3 HC3 HS3 L1'' HPO2 HM3 HSM3 Hbrk.
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
    all: try (cbn [t_len t_drop tr_st1]; rewrite EL; first [exact L1'' | lia]).
    all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2]).
    all: try (apply spure_st1; exact HP).
    all: cbn [t_used t_huff tr_st1]; first [exact HHF | lia].
Qed.

Lemma main_loop_t : forall (P : ItSt -> Prop) k st Rb l M0 M MD T,
  it_loop_ok k X 288 320 1444 st = true -> 1 <= mx ->
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kT1 = t_len st - t_drop st -> zget_l Rb l kA2 = p + 792 + 2 * t_sym st ->
  CM M -> SM st M -> SP st ->
  mpostL R_segs M0 M rsL ->
  P st -> (forall s, P s -> ty = CODES -> arr_get work1Ar (t_sym s) < 20) ->
  (forall s s', P s -> it_step X s = ItCont s' -> P s') ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inl st' ->
      CR R' [] -> SR st' R' [] -> zget_l R' [] kT1 = 256 * (t_len st' - t_drop st') ->
      mpostL R_segs M0 M' rsL -> CM M' -> SM st' M' -> SP st' ->
      (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444) ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes R_segs (zcfg R_segs 140440 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inr st' ->
      CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL R_segs M0 M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139704 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros P. induction k as [|k IH]; intros st Rb l M0 M MD T HOK Hmx Hh HC HS LT1 LT2 HM HSM HP HPL HQ0 HQw HQs KB KF.
  { cbn [it_loop_ok] in HOK. discriminate. }
  rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
  assert (HW0 : ty = CODES -> arr_get work1Ar (t_sym st) < 20) by (intro E; exact (HQw st HQ0 E)).
  eapply trip_t; try eassumption.
  - intros st' R' M' Hstep HC' HS' LT1' LT2' HPO HM' HSM' HP'. rewrite Hstep in REST.
    assert (HQ0' : P st') by (eapply HQs; [exact HQ0 | exact Hstep]).
    eapply (IH st' R' [] M0 M' MD T); try eassumption.
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
End U7IT5.
End FXG.
