(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
(* reloc-zl14tag tagged blocks: agree 6 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import ZTac ZMem ZCall ZCallL ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6S Require Import S_It0 S_It3 S_It4 S_It5 S_It6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6U Require Import Base T_It1 T_It2 T_It3 T_It4 T_It5 T_It6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require ItCovPre ItCovStep ItCovLoop.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section U7IT7.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

Definition FP : list (Z * Z) := [(sp - 208, 208); (p + 144, 8); (pb, 4); (p + 792, 576); (p + 1368, 5776)].
Definition FPS : list (Z * Z) := [(sp + -208, 104); (p + 144, 8); (pb, 4); (p + 792, 576); (p + 1368, 5776)].

Definition pf (M : mem) : Prop :=
  mem_wr R_segs M p 7160 /\ mem_arr 2 R_segs M (p + 152) 320 lf /\ mem_arr 4 R_segs M (p + 1368) 1444 cf /\
  mem_arr 2 R_segs M (p + 792) 288 wf /\ mem_u64 R_segs M (p + 144) (p + 1368 + 4 * nx) /\ mem_u32 R_segs M pb bits /\
  mem_arr 2 R_segs M 75186 31 (arr_get lbase_a) /\ mem_arr 2 R_segs M 75248 31 (arr_get lext_a) /\
  mem_arr 2 R_segs M 75310 32 (arr_get dbase_a) /\ mem_arr 2 R_segs M 75374 32 (arr_get dext_a).
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  destruct H as (a & b & c & d & e & f & g & h & i & j).

Lemma pf_frame : forall M M' lo hi, pf M -> mpost R_segs M M' lo hi 0 0 -> zc <= lo -> pf M'.
Proof using C ret sp codes lens_ofs ty.
  intros M M' lo hi HP [HA HW] Hlo. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb. open_pf HP. unfold pf. split_conj.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Htabl | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u32_magree; [exact HA | exact Hbcell | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hlb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hle | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hdb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hde | lia_std | lia_std].
Qed.

Lemma slots_fps : forall M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  slots_t sp M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> mpostL R_segs M M' FPS ->
  slots_t sp M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 HS [HA HW]. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb.
  unfold slots_t in *. destr_conj HS. split_conj.
  all: eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | rewrite two64_eq; lia_std | cbn; lia_std].
Qed.


Lemma acc2 : forall M0 M M' a1 b1 a2 b2,
  framed (fun X => mpostL R_segs M0 X FPS) M -> mpost R_segs M M' a1 b1 a2 b2 ->
  in_some a1 (b1 - a1) FPS \/ b1 <= a1 -> in_some a2 (b2 - a2) FPS \/ b2 <= a2 ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using. intros. eapply framed_mpostL_trans2; eassumption. Qed.
Lemma accL : forall M0 M M', framed (fun X => mpostL R_segs M0 X FPS) M -> mpostL R_segs M M' (rsL p sp) ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.
Lemma accT : forall M0 M M', framed (fun X => mpostL R_segs M0 X FPS) M -> mpostL R_segs M M' (rsT p pb) ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.

Lemma safe_sort : mx <> 0 -> itm_reject ty mx (it_left_check cntAr) = false ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true /\
  (it_not_enough ty (itm_used rt) = false -> it_loop_ok (Z.to_nat (codes + 1)) X 288 320 1444 st0 = true).
Proof using C zc ret sp pb p.
  intros Hmx Hrj.
  pose proof (it_safe_sort ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ (itc_old _ _ _ _ _ _ _ _ _ _ _ _ _ _ C))) as S.
  cbv zeta in S. unfold mxA, cntA, rootA, mnA, mxA, cntA, offsA, work1A, offsA, cntA in *.
  specialize (S Hmx Hrj). destruct S as [S1 S2].
  unfold workA, lensA, tblA in S1, S2 |- *. rewrite !arr_len_init in S1, S2. cbv [N_WORK N_LENS N_CODES] in S1, S2 |- *.
  split; [exact S1 | intros Hne; exact (proj2 (proj2 (S2 Hne)))].
Qed.

Lemma fin_fp : forall M M1 M', mpost R_segs M M1 (sp + -208) sp 0 0 -> mpostL R_segs M1 M' FPS -> mpostL R_segs M M' FP.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M1 M' HP [HA HW]. pose proof C as C'. open_itc C'.
  pose proof (framed_mpostL_trans2 R_segs M M M1 FP _ _ _ _ (mpostL_refl R_segs M FP) HP ltac:(left; cbn; left; lia_std) ltac:(right; lia_std)) as [A1 W1].
  split; [| intros a n Hw; apply HW; apply W1; exact Hw].
  intros x Hx. rewrite (HA x); [apply A1; exact Hx|]. cbn in Hx |- *. lia_std.
Qed.

Lemma cA_zero : codes = 0 -> forall j, arr_get cntAr j = 0.
Proof using. intros Hc j. rewrite cntA_eq, Hc. unfold cntK. rewrite itm_count_k_0 by lia_std. apply it_zero_count_spec. Qed.

Lemma tbl_max0_range : forall j, 0 <= j < 1444 ->
  0 <= arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0)) j < 4294967296.
Proof using C zc ret sp pb p wf bits codes lens_ofs lf ty.
  intros j Hj. pose proof C as C'. open_itc C'.
  rewrite !arr_get_set. destruct (_ && _); [apply code_pack_range|]. destruct (_ && _); [apply code_pack_range|].
  rewrite tblA_get. apply Hcf. exact Hj.
Qed.
Lemma tbl_brk_range : forall st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 ->
  0 <= arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st) j < 4294967296.
Proof using.
  intros st H j Hj. destruct (negb _); [|apply H; exact Hj]. rewrite arr_get_set. destruct (_ && _); [apply code_pack_range | apply H; exact Hj].
Qed.
Lemma tblA_range : forall j, 0 <= j < 1444 -> 0 <= arr_get (tblA cf) j < 4294967296.
Proof using C zc ret sp pb p wf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite tblA_get. apply Hcf. exact Hj. Qed.
Lemma workA_range : forall j, 0 <= j < 288 -> 0 <= arr_get (workA wf) j < 65536.
Proof using C zc ret sp pb p cf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite workA_get. apply Hwf. exact Hj. Qed.

(* 1.4 UBSan: for CODES the here-entry code traps when work[sym] >= 20; every visited state satisfies IS *)
Definition PW (s : ItSt) : Prop :=
  ty = CODES -> exists j, 0 <= j < ItCovPre.N (lensA lf) lens_ofs codes /\ ItCovLoop.IS ty (lensA lf) lens_ofs codes rt nx j s.

Lemma codes_inv : 1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false -> it_not_enough ty (itm_used rt) = false ->
  PW st0 /\ (forall s, PW s -> ty = CODES -> arr_get work1Ar (t_sym s) < 20) /\
  (forall s s', PW s -> it_step X s = ItCont s' -> PW s').
Proof using C zc ret sp pb p cf.
  intros Hmx1 Hrj Hne. pose proof C as C'. open_itc C'.
  assert (Hc' : 0 <= codes <= 288) by lia.
  assert (Hl' : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15).
  { intros s Hs. rewrite lensA_get. pose proof (Hlf (lens_ofs + s) ltac:(lia)). pose proof (Hlens15 s Hs). lia. }
  pose proof (mxmn_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx1) as (MM1 & MM2 & MM3 & MM4 & _).
  assert (Hroot : mn <= rt <= 15) by lia.
  assert (Hpow : itm_used rt = 2 ^ rt) by (apply itm_used_pow2; lia).
  assert (Hfit : it_not_enough ty (2 ^ rt) = false) by (rewrite <- Hpow; exact Hne).
  assert (Hcx : X = mkItCtx ty (lensA lf) lens_ofs nx rt mx (2 ^ rt - 1)) by (unfold itm_ctx; rewrite Hpow; reflexivity).
  pose proof (ItCovPre.N_range (lensA lf) lens_ofs codes Hc' Hl') as NR.
  assert (HNw : ItCovPre.N (lensA lf) lens_ofs codes <= arr_len (workA wf)) by (rewrite workA_len; lia).
  assert (HC19 : ty = CODES -> codes <= 19) by (intros E; exact (proj1 (HtyC E))).
  assert (HK : ty = CODES -> ItCovPre.kraft (lensA lf) lens_ofs codes 15 = 2 ^ 15).
  { intros E. pose proof (ItCovPre.left_check_spec (lensA lf) lens_ofs codes Hc' Hl') as LC.
    change (ItCovPre.count (lensA lf) lens_ofs codes) with cntAr in LC. rewrite LC in Hrj. rewrite E in Hrj.
    unfold itm_reject in Hrj.
    destruct (Z.ltb_spec (2 ^ 15) (ItCovPre.kraft (lensA lf) lens_ofs codes 15)) as [K|K]; [discriminate|].
    cbn [codetype_eqb orb] in Hrj. rewrite Bool.andb_true_r in Hrj. apply Z.ltb_ge in Hrj. lia. }
  split; [|split].
  - intros E. exists 0. split; [pose proof (ItCovStep.N_pos (lensA lf) lens_ofs codes Hc' Hl' Hmx1); lia|].
    unfold itm_st0. rewrite Hpow.
    exact (ItCovLoop.IS0 ty (lensA lf) lens_ofs codes Hc' Hl' Hmx1 rt Hroot nx Hfit (tblA cf) (workA wf) HNw).
  - intros s Hs E. destruct (Hs E) as (j & Hj & HIS). destruct HIS as (Hsym & _). rewrite Hsym.
    pose proof (ItCovPre.sort_spec (lensA lf) lens_ofs codes Hc' Hl' (workA wf) HNw) as (_ & L2 & _).
    cbv zeta in L2.
    assert (WJ : arr_get work1Ar j = znth 0 (ItCovPre.W (lensA lf) lens_ofs codes) j) by (rewrite <- (L2 j Hj); reflexivity).
    rewrite WJ. pose proof (ItCovStep.W_range (lensA lf) lens_ofs codes Hc' j Hj). pose proof (HC19 E). lia.
  - intros s s' Hs Hst E. destruct (Hs E) as (j & Hj & HIS).
    pose proof (ItCovLoop.trip ty (lensA lf) lens_ofs codes Hc' Hl' Hmx1 (HK E) rt Hroot nx HC19 j s Hj HIS) as TP.
    match type of TP with context [it_step ?x s] => replace (it_step x s) with (ItCont s') in TP by (rewrite <- Hst, Hcx; reflexivity) end.
    unfold ItCovLoop.trip_post in TP. destruct TP as (A & _ & HIS' & _).
    exists (j + 1). split; [lia | exact HIS'].
Qed.
End U7IT7.

End FXG.
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  destruct H as (a & b & c & d & e & f & g & h & i & j).
Ltac zkeys_all := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Theorem itable_t : itable_spec_at R_segs A_ITABLE_T 208.
Proof using.
  unfold itable_spec_at, A_ITABLE_T.
  intros Rb l M MD T ty p lens_ofs codes nx bits pb sp ret zc lf cf wf.
  intros Hh LA0 LA1 LA2 LA3 LA4 LA5 LSP LRA Hret Hret2 Hpb Hpal Hp0 Hpceil Hsp Hzrom Hsp2 Hspal Hprom
         Wf0 Wp0 Hlens0 Htab0 Hwork0 Hnext0 Hbits0 Hlb0 Hle0 Hdb0 Hde0 Rlf Rcf Rwf
         Hofs Hofs2 Hc0 Hc288 Hl15 HtyC HtyD Hb1 Hb15 Hnx Hroom K.
  cbv [o_lens o_next o_work o_codes N_LENS N_CODES N_WORK STATE_SIZE LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR
       o_lenbits o_distbits ROM_LO_ALL it_fp] in *.
  set (vgp := zget_l Rb l kGP). set (vtp := zget_l Rb l kTP).
  assert (C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc).
  { constructor; cbv [N_LENS N_CODES N_WORK STATE_SIZE o_lenbits o_distbits ROM_LO_ALL DEXT_ADDR]; try assumption; try lia_std. }
  pose proof (C192 _ _ _ _ _ _ _ _ _ _ _ _ _ C) as C192v.
  assert (PF0 : pf lf nx bits cf wf p pb M) by (unfold pf; split_conj; assumption).
  assert (FIN : forall R' M' rv (T' W' : arr) tab' b',
    resA ty lf lens_ofs codes nx bits cf wf = (rv, T', tab', b', W') ->
    zget_l R' [] kSP = sp + -208 -> zget_l R' [] kGP = vgp -> zget_l R' [] kTP = vtp -> zget_l R' [] kA6 = rv ->
    slots_t sp M' ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9)
          (zget_l Rb l kS10) (zget_l Rb l kS11) ->
    mpostL R_segs M M' (FP p pb sp) ->
    mem_arr 2 R_segs M' (p + 152) 320 lf -> mem_arr 4 R_segs M' (p + 1368) 1444 (arr_get T') -> mem_arr 2 R_segs M' (p + 792) 288 (arr_get W') ->
    (forall i, 0 <= i < 1444 -> 0 <= arr_get T' i < 4294967296) -> (forall i, 0 <= i < 288 -> 0 <= arr_get W' i < 65536) ->
    mem_u64 R_segs M' (p + 144) (p + 1368 + 4 * tab') -> mem_u32 R_segs M' pb b' ->
    realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T).
  { intros R' M' rv T' W' tab' b' ER LSP' LGP' LTP' LA6' HSL HPL Hlens' Htab' Hwork' RT RW Hnext' Hbits'.
    eapply (epilogue_t ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C R' [] M' MD T rv ret); try eassumption.
    intros R'' FA0 FSP FRA FS0 FS1 FS2 FS3 FS4 FS5 FS6 FS7 FS8 FS9 FS10 FS11 FGP FTP.
    assert (RES : it_ret (resA ty lf lens_ofs codes nx bits cf wf) = rv /\ it_tbl (resA ty lf lens_ofs codes nx bits cf wf) = T' /\
                  it_table (resA ty lf lens_ofs codes nx bits cf wf) = tab' /\ it_bits (resA ty lf lens_ofs codes nx bits cf wf) = b' /\
                  it_work (resA ty lf lens_ofs codes nx bits cf wf) = W').
    { rewrite ER. repeat split; reflexivity. }
    unfold resA, lensA, tblA, workA in RES. cbv [N_LENS N_CODES N_WORK] in RES. destruct RES as (E1 & E2 & E3 & E4 & E5).
    assert (RV3 : rv = 0 \/ rv = 1 \/ rv = -1).
    { pose proof (res_phases ty lf lens_ofs codes nx bits cf wf) as PH. rewrite ER in PH.
      destruct (mxA lf lens_ofs codes =? 0); [injection PH; intros; lia_std|].
      destruct (itm_reject _ _ _); [injection PH; intros; lia_std|].
      destruct (it_not_enough _ _); [injection PH; intros; lia_std|].
      destruct (it_loop _ _ _); injection PH; intros; lia_std. }
    eapply (K R'' M' (arr_get T') (arr_get W')); cbv zeta; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
    all: try (intros; reflexivity).
    unfold kept_eq. cbv [zget_l alookup] in FSP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FGP, FTP.
    rewrite FSP, FGP, FTP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11. subst vgp vtp.
    repeat split; first [reflexivity | symmetry; assumption | assumption]. }
  pose proof (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ (itc_old _ _ _ _ _ _ _ _ _ _ _ _ _ _ C)) as SAFE.
  eapply (it_prologue_t Rb l M MD T sp ret vgp vtp (zget_l Rb l kS0) (zget_l Rb l kS1) (cty ty) (p + 152 + 2 * lens_ofs) codes (p + 144) pb (p + 792)
            (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4) (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7)
            (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11) Hh); try assumption; try reflexivity; try lia.
  intros R1 M1 QSP QGP QTP QA0 QA1 QA2 QA3 QA4 QA5 HPO1 Wf1 S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 Hcnt0.
  assert (HSL1 : slots_t sp M1 ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11))
    by (unfold slots_t; split_conj; assumption).
  clear S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27.
  pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M M1 _ _ PF0 HPO1 ltac:(lia)) as PF1.
  assert (HAGS1 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M1) by (apply mpostL_refl).
  assert (PR1 : pregs p lens_ofs codes pb sp vgp vtp (cty ty) R1 []) by (unfold pregs; split_conj; assumption).
  assert (KC : forall Mc, pf lf nx bits cf wf p pb Mc -> mem_wr R_segs Mc (sp - 208) 208 -> mem_arr 2 R_segs Mc (sp + -136) 16 (arr_get (cntA lf lens_ofs codes)) ->
            framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) Mc ->
            T_It2.Kleft ty lf lens_ofs codes bits p pb sp vgp vtp Mc MD T /\ T_It2.Kmax0 ty lf lens_ofs codes p pb sp vgp vtp Mc MD T).
  { intros Mc PFc Wfc Hcntc HAGc. pose proof PFc as PFc'. unfold pf in PFc'.
    destruct PFc' as (Wpc & Hlens1 & Htabl0 & Hwork1 & Hnext1 & Hbcell0 & Hlb1 & Hle1 & Hdb1 & Hde1). split.
    -
      apply (left_t ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Hcntc).
      +
        unfold T_It2.Kneg. intros R' HP' LA6 Hrj Hmx1. open_pregs HP'.
        eapply (FIN R' Mc (-1) (tblA cf) (workA wf) nx bits); try eassumption.
        * rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj. reflexivity.
        * eapply slots_fps; [exact C | exact HSL1 | exact HAGc].
        * eapply fin_fp; [exact C | exact HPO1 | exact HAGc].
        * eapply mem_arr_ext; [exact Htabl0|]. intros; symmetry; apply tblA_get.
        * eapply mem_arr_ext; [exact Hwork1|]. intros; symmetry; apply workA_get.
        * apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
        * apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      +
        apply (offs_t ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Wfc).
        intros R3 M3 HP3 LT0 LT1 LA7 LT2x HPO3 Hoffs Hmx1 Hrj.
        assert (Hmx0 : mxA lf lens_ofs codes <> 0) by lia.
        destruct (safe_sort _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx0 Hrj) as [SOK LOOPOK].
        pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C Mc M3 _ _ PFc HPO3 ltac:(lia)) as PF3.
        destruct PF3 as (Wp3 & Hlens3 & Htab3 & Hwork3 & Hnext3 & Hbits3 & Hlb3 & Hle3 & Hdb3 & Hde3).
        assert (HAG3 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M3) by (eapply acc2; [exact HAGc | exact HPO3 | left; cbn; left; lia | right; lia]).
        assert (Wf3 : mem_wr R_segs M3 (sp - 208) 208) by (destruct HPO3 as [_ HW]; apply HW; exact Wfc).
        eapply (sort_phase_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M3 MD T Hh HP3 LT0 LT1 LA7 LT2x Hmx1 SOK Wf3 Wp3 Hlens3 Hoffs Hwork3).
        intros R4 M4 HP4 LT0' LT1' LA7' HPO4 Wf4 Wp4 Hlens4 Hwork4.
        destruct HPO4 as [HA4 HW4]. unfold ZSEP in Hprom, Hpb.
        assert (HAG4 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M4) by (eapply acc2; [exact HAG3 | exact (conj HA4 HW4) | left; cbn; left; lia | left; cbn; right; right; right; left; lia]).
        assert (Htab4 : mem_arr 4 R_segs M4 (p + 1368) 1444 cf) by (eapply mem_arr_magree; [exact HA4 | exact Htab3 | lia | lia]).
        assert (Hnext4 : mem_u64 R_segs M4 (p + 144) (p + 1368 + 4 * nx)) by (eapply mem_u64_magree; [exact HA4 | exact Hnext3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hbits4 : mem_u32 R_segs M4 pb bits) by (eapply mem_u32_magree; [exact HA4 | exact Hbits3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hlb4 : mem_arr 2 R_segs M4 75186 31 (arr_get lbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hlb3 | lia | lia]).
        assert (Hle4 : mem_arr 2 R_segs M4 75248 31 (arr_get lext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hle3 | lia | lia]).
        assert (Hdb4 : mem_arr 2 R_segs M4 75310 32 (arr_get dbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hdb3 | lia | lia]).
        assert (Hde4 : mem_arr 2 R_segs M4 75374 32 (arr_get dext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hde3 | lia | lia]).
        assert (Hcnt4 : mem_arr 2 R_segs M4 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
        { eapply mem_arr_magree; [exact HA4 | | lia | lia]. destruct HPO3 as [HA3 _]. eapply mem_arr_magree; [exact HA3 | exact Hcntc | lia | lia]. }
        clear HA4 HW4 Htab3 Hnext3 Hbits3 Hlb3 Hle3 Hdb3 Hde3 Hwork3 Hlens3 Wp3 Htabl0 Hnext1 Hbcell0 Hlb1 Hle1 Hdb1 Hde1 Hwork1 Hlens1 Wpc.
        eapply (switch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R4 [] M4 MD T Hh HP4 LT0' LT1' LA7' Hmx1 Wf4 Wp4 Hlens4 Hwork4 Hcnt4 Htab4 Hnext4 Hlb4 Hle4 Hdb4 Hde4).
        *
          intros R5 M5 HC5 HS5 L51 L52 HPO5 HM5 HSM5 HSP5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          assert (Hbits5 : mem_u32 R_segs M5 pb bits).
          { destruct HPO5 as [HA5 _]. eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia]. }
          specialize (LOOPOK Hne).
          destruct (codes_inv _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx1 Hrj Hne) as (PW0 & PWw & PWs).
          eapply (main_loop_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C _ (Z.to_nat (codes + 1)) _ R5 [] M5 M5 MD T LOOPOK Hmx1 Hh HC5 HS5 L51 L52 HM5 HSM5 HSP5 (mpostL_refl _ _ _) PW0 PWw PWs).
          --
             intros st' R6 M6 HL HC6 HS6 L8 HPL6 HM6 HSM6 HSP6 Hfit B1 B2 B3.
             assert (HAG6 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             eapply (break_tail_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C st' R6 [] M6 MD T Hh HC6 HS6 L8 HM6 HSM6 HSP6 B1 B2 B3 Hfit).
             intros R7 M7 HP7 LA6 HPT7 Htbl7 Hnext7 Hbits7 Wf7 Wp7 Hlens7 Hwork7.
             assert (HAG7 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M7) by (eapply accT; [exact HAG6 | exact HPT7]).
             unfold pregs3_t in HP7. destruct HP7 as (P1 & P2 & P3).
             pose proof HSP6 as HSP6'. unfold spure in HSP6'. destruct HSP6' as (WK6 & _ & _ & _ & _ & _ & HTR6 & _ & _).
             eapply (FIN R7 M7 0 _ (t_work st') (nx + t_used st') (rootA lf lens_ofs codes bits)); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG7].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG7].
             ++ rewrite WK6. exact Hwork7.
             ++ apply tbl_brk_range. exact HTR6.
             ++ rewrite WK6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192v).
          --
             intros st' R6 M6 HL HC6 LA6 HPL6 HM6 HSM6 HW6 HTR6.
             assert (HAG6 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             unfold cregs_t in HC6. destruct HC6 as (HP6 & _). unfold pregs8 in HP6. destruct HP6 as (P1 & P2 & P3 & _).
             unfold cmem_t in HM6. destruct HM6 as (Wf6 & Wp6 & Hlens6 & Hwork6 & Hnext6 & _).
             unfold smem_t in HSM6. destruct HSM6 as (Hcnt6 & Htbl6).
             assert (Hbits6 : mem_u32 R_segs M6 pb bits).
             { destruct HPL6 as [HA6 _]. eapply mem_u32_magreeL; [exact HA6 | exact Hbits5 | lia | rewrite two64_eq; lia | cbn; lia]. }
             eapply (FIN R6 M6 1 (t_tbl st') (t_work st') nx bits); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG6].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG6].
             ++ rewrite HW6. exact Hwork6.
             ++ rewrite HW6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192v).
        *
          intros R5 M5 HP5 LA6 HPO5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          destruct HPO5 as [HA5 HW5].
          unfold pregs8 in HP5. destruct HP5 as (P1 & P2 & P3 & _).
          eapply (FIN R5 M5 1 (tblA cf) (work1A lf lens_ofs codes wf) nx bits); try eassumption.
          -- rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne. reflexivity.
          -- eapply slots_fps; [exact C | exact HSL1 | exact HAG5].
          -- eapply fin_fp; [exact C | exact HPO1 | exact HAG5].
          -- eapply mem_arr_magree; [exact HA5 | exact Hlens4 | lia | lia].
          -- eapply mem_arr_magree; [exact HA5 | | lia | lia]. eapply mem_arr_ext; [exact Htab4|]. intros; symmetry; apply tblA_get.
          -- eapply mem_arr_magree; [exact HA5 | exact Hwork4 | lia | lia].
          -- apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          -- apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192v).
          -- eapply mem_u64_magree; [exact HA5 | exact Hnext4 | lia | rewrite two64_eq; lia | lia | lia].
          -- eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia].
    -
      unfold T_It2.Kmax0. intros R' HP' Hmx0.
      eapply (max0_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R' [] Mc MD T Hh HP' Hmx0 Wpc Htabl0 Hnext1 Wfc Hlens1 Hwork1).
      intros R2 M2 HP2 LA6 HPT2 Htbl2 Hnext2 Hbits2 Wf2 Wp2 Hlens2 Hwork2.
      assert (HAG2 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M2) by (eapply accT; [exact HAGc | exact HPT2]).
      unfold pregs3_t in HP2. destruct HP2 as (P1 & P2 & P3).
      eapply (FIN R2 M2 0 _ (workA wf) (nx + 2) 1); try eassumption.
      + rewrite res_phases. rewrite Hmx0. reflexivity.
      + eapply slots_fps; [exact C | exact HSL1 | exact HAG2].
      + eapply fin_fp; [exact C | exact HPO1 | exact HAG2].
      + eapply mem_arr_ext; [exact Hwork2|]. intros; symmetry; apply workA_get.
      + apply (tbl_max0_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      + apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C). }
  pose proof PF1 as PF1'. unfold pf in PF1'. destruct PF1' as (Wp1 & HlensM1 & HtabM1 & HworkM1 & HnextM1 & HbitsM1 & _).
  destruct (Z.eq_dec codes 0) as [Cz|Cnz].
  -
    assert (HcntA : mem_arr 2 R_segs M1 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
    { eapply mem_arr_ext; [exact Hcnt0|]. intros; symmetry; apply cA_zero; exact Cz. }
    destruct (KC M1 PF1 Wf1 HcntA HAGS1) as [_ KM0].
    eapply (count_phase0_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T _ Cz Hh PR1 eq_refl Hcnt0 HbitsM1 KM0).
  - eapply (count_phase_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T ltac:(lia) Hh PR1 Wf1 HlensM1 Hcnt0).
    intros R2 M2 PR2 QA7 HPO2 Wf2 Hlens2 Hcnt2.
    pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M1 M2 _ _ PF1 HPO2 ltac:(lia)) as PF2.
    assert (HAG2 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M2) by (eapply acc2; [exact HAGS1 | exact HPO2 | left; cbn; left; lia | right; lia]).
    destruct (KC M2 PF2 Wf2 Hcnt2 HAG2) as [KL KM0].
    pose proof PF2 as PF2'. unfold pf in PF2'. destruct PF2' as (_ & _ & _ & _ & _ & HbitsM2 & _).
    eapply (max_entry_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R2 [] M2 MD T _ Hh PR2 QA7 Hcnt2 HbitsM2).
    + unfold T_It2.Kmax. intros R3 HP3 LA7 LT0 LT2 Hmx2.
      eapply (rootmin_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 LT0 LT2 Hmx2 Hcnt2 KL).
    + unfold T_It2.Klow. intros R3 HP3 LA7 LT2 HZ.
      eapply (maxlow_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 LT2 HZ Hcnt2 KL KM0).
Qed.
End FXG.
