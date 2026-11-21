(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.I6S Require Import Base.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.IK Require Import ZTac ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.I6S Require Import S_It0 S_It1 S_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section S7IT4.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
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

Definition uregs (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT6 = tr_sym st /\ zget_l R l kT1 = tr_len X st /\
  zget_l R l kS1 = tr_huff st /\ zget_l R l kS0 = p + 1384 + 4 * t_next st /\ zget_l R l kA2 = 2 ^ t_curr st /\
  zget_l R l kS8 = tr_low X st.
Ltac open_uregs H :=
  unfold uregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let d := fresh "LS1" in
  let e := fresh "LS0" in let f := fresh "LT2" in let g := fresh "LS8" in
  destruct H as (a & b & d & e & f & g).
Ltac close_uregs := unfold uregs; split_conj; zreg.
Ltac kauto4 := first
  [ assumption
  | lazymatch goal with
    | |- uregs _ _ _ => close_uregs
    | |- _ => kauto
    end ].
Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma curr_loop_s : forall m curr lft n (cnt : arr) st Rb l M MD T,
  mx - (curr + rt) <= Z.of_nat m -> Z.of_nat m < n -> 1 <= mx ->
  1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
  (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kT5 = t_used st -> zget_l Rb l kS9 = rt ->
  zget_l Rb l kS10 = curr + rt -> zget_l Rb l kA6 = lft -> zget_l Rb l kS7 = mx - rt ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get cnt) ->
  (forall R', CR R' [] -> uregs st R' [] -> zget_l R' [] kT5 = t_used st -> zget_l R' [] kS9 = rt ->
     zget_l R' [] kS7 = fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     zget_l R' [] kA6 = 2 ^ fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     realizes R_segs (zcfg R_segs 128860 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 128812 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction m as [|m IH]; intros curr lft n cnt st Rb l M MD T Hm Hn Hmx Hc1 Hcm Hl HCR Hh HC HUr LT5 LS9 LS10 LA6 LS7 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs HC. open_uregs HUr. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as (RT1 & RT2 & RT3).
  assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
  pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
  zrebase.
  zstep Rfd. zstep Rfd. zsetreg (2 * (curr + rt)) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  tstep Rfd.
  zstep Rfd. zsetreg (lft - arr_get cnt (curr + rt)) ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z_lt_le_dec 0 (lft - arr_get cnt (curr + rt))) as [GT|LE].
  - zbr Rfd false.
    zstep Rfd. zsetreg (curr + rt + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zsetreg (2 * (lft - arr_get cnt (curr + rt))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    destruct (Z_lt_le_dec (curr + rt + 1) mx) as [MORE|DONE].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) cnt st Rx [] M MD T) end.
      all: try kauto4.
      all: try lia.
      * rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
      * intros R' HC' HU' L5 L9 L7 L6. eapply K; try eassumption.
        all: rewrite curr_more by lia; rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia;
             replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia; assumption.
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd. zsetreg (2 ^ (mx - rt)) ltac:(symmetry; apply sllw_1; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto4.
      * zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. lia.
      * zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. f_equal. lia.
  - zbr Rfd true.
    zstep Rfd. zsetreg curr ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd. zsetreg (2 ^ curr) ltac:(symmetry; apply sllw_1; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto4.
    * zregv. rewrite curr_stop_le by lia. reflexivity.
    * zregv. rewrite curr_stop_le by lia. reflexivity.
Qed.

Lemma ne_facts : (isL ty = 0 \/ isL ty = 1) /\ (isD ty = 0 \/ isD ty = 1) /\ isL ty + isD ty <= 1 /\
  (forall u, it_not_enough ty u = (if isL ty =? 1 then 852 <? u else if isD ty =? 1 then 592 <? u else false)).
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; repeat split; try lia_std; intros; reflexivity. Qed.
Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using. destruct b; reflexivity. Qed.
Lemma land1_b2z : forall b, Z.land 1 (Z.b2z b) = Z.b2z b.
Proof using. destruct b; reflexivity. Qed.
Lemma lowS_small : forall z, 0 <= z < 4294967295 -> lowS z = z.
Proof using. intros z Hz. unfold lowS. destruct (Z.eqb_spec z 4294967295); [lia_std | reflexivity]. Qed.

Definition Kbody3 (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', CR R' [] -> SR (tr_st3 X st) R' [] ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> CM M' -> SM (tr_st3 X st) M' ->
     tr_sub X st = true -> it_not_enough ty (tr_used X st) = false ->
     1 <= tr_curr X st <= 15 -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st ->
     realizes R_segs (zcfg R_segs 128504 (zupd R' []) M' MD) T.
Definition Kfail (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', CR R' [] -> zget_l R' [] kA6 = 1 -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = true ->
     realizes R_segs (zcfg R_segs 129020 (zupd R' []) M MD) T.

Lemma link_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kS7 = tr_curr X st ->
  zget_l Rb l kT5 = tr_used X st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = false -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3 st M MD T ->
  realizes R_segs (zcfg R_segs 128908 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LS7 LT5 HM HSM HP TOK Hbrk Hsub Hne Hmx HLOW HDR K3.
  pose proof C as C'. open_itc C'. open_cregs HC. open_uregs HU. open_cmem HM. open_smem HSM. open_spure HP. zkeys. xaddr.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  trip_facts TOK. clear Flook Fwm LOWR DROPR Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  assert (HST3 : it_step X st = ItCont (tr_st3 X st)).
  { rewrite it_step_eq. rewrite Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity. }
  unbox Fcont. destruct (Fcont (tr_st3 X st) HST3) as (Flow3 & Fcurr3 & Fnext3).
  { right. cbn [t_next tr_st3]. unfold tr_next, tr_fill. rewrite shl32_1 by lia. pose proof (pow2_le15 (t_curr st) ltac:(lia)). lia. }
  cbn [t_low t_curr t_next tr_st3] in Flow3, Fcurr3, Fnext3. clear Fcont HST3.
  assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
  pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC. pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (Hroom3 : t_next st < 1444).
  { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
    assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (4 * 2 ^ t_curr st) ltac:(symmetry; apply zext32_x4; lia).
  zstep Rfd. zsetreg (p + 1384 + 4 * tr_next st) ltac:(rewrite ENX; lia).
  zstep Rfd. zsetreg (4 * tr_low X st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (4 * (tr_next st - nx)) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (tr_next st - nx) ltac:(rewrite srli_small by lia; change (2 ^ 2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_curr X st), Hb : mem_u8 _ _ _ rt, Hv : mem_u16 _ _ _ (tr_next st - nx) |- _ =>
    pose proof (entry_write Mc (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite it_fill_len_tr; lia].
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ tr_curr X st) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (tr_low X st) ltac:(rewrite swrap32_small by lia; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K3 Rx Mx) end.
  all: try kauto4.
  all: lazymatch goal with
       | |- sregs _ _ _ _ => unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st3]; rewrite HDR;
                             rewrite (lowS_small (tr_low X st)) by lia; split_conj; zreg
       | |- cmem _ _ _ _ _ _ _ _ _ => close_cmem
       | |- smem _ _ _ _ => unfold smem; cbn [t_count t_tbl tr_st3]; split; [exact Hcnt|]; unfold tr_tbl2; cbn [x_table x_root itm_ctx]; exact Htbl
       | |- _ => lia
       end.
Qed.

Lemma enough_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kS7 = tr_curr X st -> zget_l Rb l kA6 = 2 ^ tr_curr X st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_curr X st <= 15 ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 128860 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LT5 LS7 LA6 HM HSM HP TOK Hbrk Hsub Hmx HLOW HDR HCU K3 KF.
  pose proof C as C'. open_itc C'. open_cmem HM. open_spure HP. zkeys.
  trip_facts TOK. clear Flook Fwm Fcont Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
  { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
  pose proof ne_facts as (IL & ID & ILD & NE').
  assert (JD : forall RJ, CR RJ [] -> uregs st RJ [] -> zget_l RJ [] kS9 = rt -> zget_l RJ [] kT5 = tr_used X st ->
            zget_l RJ [] kS7 = tr_curr X st -> zget_l RJ [] kA6 = 1 -> (isL ty = 1 -> tr_used X st < 853) ->
            realizes R_segs (zcfg R_segs 128888 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ J9 J5 J7 J6 HL. open_cregs HCJ. open_uregs HUJ. zkeys. zrebase.
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
    zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
    zstep Rfd.
    destruct ID as [ID0|ID1].
    - zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_s st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      + unfold cmem; split_conj; assumption.
      + unfold spure; split_conj; assumption.
      + rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [apply Z.ltb_ge; lia|]. rewrite ID0. reflexivity.
    - zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite ID1; symmetry; apply land1_b2z).
      destruct (Z.leb_spec 593 (tr_used X st)) as [GE|LT].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
        all: try kauto4. rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [destruct IL; lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
      + zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_s st Rx [] M MD T) end.
        all: try kauto4. all: try assumption. all: try lia.
        * unfold cmem; split_conj; assumption.
        * unfold spure; split_conj; assumption.
        * rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [apply Z.ltb_ge; lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_ge. lia. }
  open_cregs HC. open_uregs HU. zkeys. zrebase.
  zstep Rfd. zsetreg (tr_used X st) ltac:(rewrite EU, swrap32_small by lia; lia).
  zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
  zstep Rfd. zsetreg (Z.b2z (853 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
  zstep Rfd.
  destruct IL as [IL0|IL1].
  - zstep Rfd. zsetreg 0 ltac:(rewrite IL0; symmetry; apply Z.land_0_l).
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JD Rx) end.
    all: try kauto4. intros; lia.
  - zstep Rfd. zsetreg (Z.b2z (853 <=? tr_used X st)) ltac:(rewrite IL1; symmetry; apply land1_b2z).
    zstep Rfd.
    destruct (Z.leb_spec 853 (tr_used X st)) as [GE|LT].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
      all: try kauto4. rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JD Rx) end.
      all: try kauto4. intros; lia.
Qed.

Ltac zbr_by bv tac :=
  let pc := zpc in Rfd pc ltac:(fun F E D => eapply (zu_branch_b bv); [exact F | exact E | exact D | zhalted | znorm; tac | ]; cbv iota; znorm).

Lemma tr_count_range : forall st, (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) ->
  forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536.
Proof using.
  intros st H j Hj. unfold tr_count. rewrite arr_get_set. destruct (_ && _); [|apply H; exact Hj].
  pose proof (wrap16_range (arr_get (t_count st) (t_len st) - 1)) as W. change (2 ^ 16) with 65536 in W. unfold tr_c. lia_std.
Qed.

Lemma currsz_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kT5 = t_used st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  1 <= tr_len X st <= 15 -> rt < tr_len X st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 128792 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LT5 HM HSM HP TOK Hbrk Hsub Hmx TLR RTL HLOW HDR K3 KF.
  pose proof C as C'. open_itc C'. open_smem HSM. open_spure HP. zkeys.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  pose proof (tr_count_range st HCr) as HCr1.
  set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
  pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
  assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
  { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
    fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
  pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
  rewrite <- ETC in CR1, CR2, CR3.
  open_cregs HC. open_uregs HU. zkeys. zrebase.
  zstep Rfd. zsetreg c0 ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (2 ^ c0) ltac:(symmetry; apply sllw_1; lia).
  destruct (Z_lt_le_dec (tr_len X st) mx) as [LT|GE].
  - zbr Rfd false.
    zstep Rfd. zsetreg (mx - rt) ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (curr_loop_s 15%nat c0 (2 ^ c0) 16 (tr_count st) st Rx [] M MD T) end.
    all: try kauto4. all: try lia.
    intros R' HC' HU' L5 L9 L7 L6. rewrite <- ETC in L7, L6. specialize (CR2 ltac:(lia)).
    eapply enough_s; try eassumption; try lia.
    + unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
  - zbr Rfd true.
    assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (enough_s st Rx [] M MD T) end.
    all: try kauto4. all: try (rewrite ETC0; zreg). all: try lia.
    + unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
Qed.

Lemma sub_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR (tr_st1 X st) Rb l ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> 1 <= mx ->
  (forall R', CR R' [] -> SR (tr_st1 X st) R' [] -> tr_sub X st = false ->
     realizes R_segs (zcfg R_segs 128504 (zupd R' []) M MD) T) ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 128768 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HSM HP TOK Hbrk Hmx K1 K3 KF.
  pose proof C as C'. open_itc C'. open_spure HP. zkeys.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  trip_facts TOK. clear Fwm Fcont.
  pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  assert (TLR : 1 <= tr_len X st <= 15).
  { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
    destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
    destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
    unbox Flook. destruct (Flook E0 NEM) as (W1 & W2 & W3 & W4).
    replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). exact W4. }
  clear Flook.
  assert (HHF : 0 <= tr_huff st).
  { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
    pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
    rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
    destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
    assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
  assert (HLOW : 0 <= tr_low X st < 32768).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia.
    split; [apply Z.land_nonneg; lia|]. eapply Z.le_lt_trans; [apply land_le_r; lia | lia]. }
  assert (ELOW : Z.land (tr_huff st) (2 ^ rt - 1) = tr_low X st).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia. reflexivity. }
  assert (HDR : tr_drop X st = rt).
  { unfold tr_drop. cbn [x_root itm_ctx]. unbox DROPR. destruct DROPR as [D0|D1]; rewrite D0 || rewrite D1; [reflexivity|].
    destruct (Z.eqb_spec rt 0); lia. }
  assert (J68 : forall RJ, CR RJ [] -> uregs st RJ [] -> zget_l RJ [] kA6 = t_drop st -> zget_l RJ [] kT5 = t_used st ->
            tr_sub X st = true -> realizes R_segs (zcfg R_segs 128780 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ JA6 JT5 Hsub.
    assert (RTL : rt < tr_len X st).
    { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
    open_cregs HCJ. open_uregs HUJ. zkeys. zrebase.
    zstep Rfd.
    unbox DROPR. destruct DROPR as [D0|D1].
    - zbr Rfd true.
      eapply currsz_s; try eassumption; try lia. all: try kauto4.
      + unfold spure; split_conj; try assumption. unfold ZSEP. lia.
    - zbr Rfd false.
      zstep Rfd.
      eapply currsz_s; try eassumption; try lia. all: try kauto4.
      + unfold spure; split_conj; try assumption. unfold ZSEP. lia. }
  open_cregs HC. open_sregs HS. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LT6, LT1, LA6, LT5, LS1, LS0, LT2, LS7.
  zkeys. zrebase.
  destruct (Z_lt_le_dec rt (tr_len X st)) as [SUB1|NOSUB1].
  - zbr Rfd false.
    zstep Rfd. zsetreg (tr_low X st) ltac:(exact (eq_sym ELOW)).
    unbox LOWR. destruct LOWR as [LM|LSM].
    +
      unfold lowS in LS7. rewrite LM in LS7. cbn in LS7.
      zbr_by false ltac:(cbv beta iota delta [zcond]; rewrite (mod_small_u64 (tr_low X st)) by lia;
                         try change ((-1) mod 18446744073709551616) with 18446744073709551615; apply Z.eqb_neq; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J68 Rx) end.
      all: try kauto4.
      unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
      replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
    + rewrite (lowS_small (t_low st)) in LS7 by lia.
      destruct (Z.eq_dec (tr_low X st) (t_low st)) as [EQL|NEL].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
        all: try kauto4.
        -- unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. rewrite (lowS_small (t_low st)) by lia. split_conj; zreg.
        -- unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, EQL, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J68 Rx) end.
        all: try kauto4.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
    all: try kauto4.
    + unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
    + unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End S7IT4.
End FXG.
