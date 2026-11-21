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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import ZTac ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6S Require Import S_It0 S_It3 S_It4.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6U Require Import Base T_It1 T_It2 T_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section U7IT4.
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
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).
#[local] Abbreviation C192' := (C192 ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).

Definition uregs_t (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT4 = tr_sym st /\ zget_l R l kS11 = tr_len X st /\ zget_l R l kT6 = tr_huff st /\
  zget_l R l kS0 = Z.shiftl (tr_sym st) 32 /\ zget_l R l kS8 = tr_low X st.
Ltac open_uregs_t H :=
  unfold uregs_t in H;
  let a := fresh "LT4" in let b := fresh "LS11" in let d := fresh "LT6" in
  let e := fresh "LS0" in let g := fresh "LS8" in
  destruct H as (a & b & d & e & g).
Ltac close_uregs_t := unfold uregs_t; split_conj; zreg.
Ltac kauto4 := first
  [ assumption
  | lazymatch goal with
    | |- uregs_t _ _ _ => close_uregs_t
    | |- _ => kauto_t
    end ].
Ltac xaddr_t := pose proof (xaddr_facts_t _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).

Ltac zbr_by bv tac :=
  let pc := zpc in Rfd pc ltac:(fun F E D => eapply (zu_branch_b bv); [exact F | exact E | exact D | zhalted | znorm; tac | ]; cbv iota; znorm).

Lemma entry_write_t : forall M base n f i op hbits val a0 a1 a2,
  mem_arr 4 R_segs M base i f ->
  mem_arr 4 R_segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u8 R_segs M a0 op -> mem_u8 R_segs M a1 hbits -> mem_u16 R_segs M a2 val ->
  a0 = base + 4 * i -> a1 = a0 + 1 -> a2 = a0 + 2 ->
  0 <= i < n -> base + 4 * n <= two64 -> 0 <= base ->
  0 <= op < 256 -> 0 <= hbits < 256 -> 0 <= val < 65536 ->
  mem_arr 4 R_segs M base n (zfupd f i (code_pack op hbits val)).
Proof using.
  intros M base n f i op hbits val a0 a1 a2 H1 H2 Ho Hb Hv -> -> -> Hi Hn Hb0 Ro Rb Rv.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  apply mem_arr4_pack; try assumption; rewrite ?two64_eq in *; lia.
Qed.


Lemma curr_loop_t : forall m curr lft n (cnt : arr) st (vused vs1 vt1 : Z) Rb l M MD T,
  mx - (curr + rt) <= Z.of_nat m -> Z.of_nat m < n -> 1 <= mx ->
  1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
  (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kT5 = vused -> zget_l Rb l kS2 = vs1 -> zget_l Rb l kA2 = vt1 -> zget_l Rb l kS7 = rt ->
  zget_l Rb l kA6 = curr + rt -> zget_l Rb l kT1 = lft -> zget_l Rb l kS10 = mx - rt ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get cnt) ->
  (forall R', CR R' [] -> uregs_t st R' [] -> zget_l R' [] kT5 = vused -> zget_l R' [] kS2 = vs1 -> zget_l R' [] kA2 = vt1 -> zget_l R' [] kS7 = rt ->
     zget_l R' [] kS10 = fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     realizes R_segs (zcfg R_segs 140300 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 140248 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction m as [|m IH]; intros curr lft n cnt st vused vs1 vt1 Rb l M MD T Hm Hn Hmx Hc1 Hcm Hl HCR Hh HC HUr LT4 LS1 LT1 LRA LA6 LT2 LS9 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_uregs_t HUr. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' ltac:(lia)) as (RT1 & RT2 & RT3).
  assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
  pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
  pose proof (lnot_val_mod' (sp + -136) ltac:(lia)) as Hn8.
  zrebase.
  zstep Rfd. zsetreg (2 * (curr + rt)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zbr Rfd false.
  zstep Rfd.
  tstep Rfd.
  zstep Rfd. zsetreg (lft - arr_get cnt (curr + rt)) ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z_lt_le_dec 0 (lft - arr_get cnt (curr + rt))) as [GT|LE].
  - zbr Rfd false.
    zstep Rfd. zsetreg 0 ltac:(symmetry; rewrite srliw_small by lia; apply Z.div_small; change (2 ^ 30) with 1073741824; lia).
    zbr Rfd false.
    zstep Rfd. zsetreg (curr + rt + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zsetreg (2 * (lft - arr_get cnt (curr + rt))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    destruct (Z_lt_le_dec (curr + rt + 1) mx) as [MORE|DONE].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) cnt st vused vs1 vt1 Rx [] M MD T) end.
      all: try kauto4.
      all: try lia.
      all: try (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
      intros R' HC' HU' L4 L1 LT1' LR L9. eapply K; try eassumption.
        rewrite curr_more by lia; rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia;
          replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia; assumption.
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto4.
      zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. lia.
  - zbr Rfd true.
    zstep Rfd. zsetreg curr ltac:(rewrite swrap32_small by lia; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto4.
    zregv. rewrite curr_stop_le by lia. reflexivity.
Qed.

Definition Kbody3_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', CR R' [] -> SR (tr_st3 X st) R' [] ->
     zget_l R' [] kT1 = tr_len X st - tr_drop X st -> zget_l R' [] kA2 = p + 792 + 2 * tr_sym st ->
     mpost R_segs M M' (p + 1368) (p + 7144) 0 0 -> CM M' -> SM (tr_st3 X st) M' ->
     tr_sub X st = true -> it_not_enough ty (tr_used X st) = false ->
     1 <= tr_curr X st <= 15 -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st ->
     realizes R_segs (zcfg R_segs 139704 (zupd R' []) M' MD) T.
Definition Kfail_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', CR R' [] -> zget_l R' [] kA6 = 1 -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = true ->
     realizes R_segs (zcfg R_segs 140556 (zupd R' []) M MD) T.

Lemma link_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kS7 = rt -> zget_l Rb l kS10 = tr_curr X st ->
  zget_l Rb l kT5 = tr_used X st -> zget_l Rb l kA2 = p + 1368 + 4 * tr_next st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = false -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_len X st <= 15 ->
  Kbody3_t st M MD T ->
  realizes R_segs (zcfg R_segs 140364 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LRA LS9 LT4 LT1 HM HSM HP TOK Hbrk Hsub Hne Hmx HLOW HDR TLR K3.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_uregs_t HU. open_cmem_t HM. open_smem_t HSM. open_spure HP. zkeys. xaddr_t.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  trip_facts TOK. clear Flook Fwm LOWR DROPR Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
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
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  pose proof (lnot_val_mod' (p + 792) ltac:(lia)) as Hnw.
  destruct (arr4_hole R_segs M (p + 1368) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  pose proof (mpost_stable R_segs M (p + 1368) (p + 7144) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1368) (p + 7144) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd. zsetreg (4 * tr_low X st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zstep Rfd. zstep Rfd.
  zsetreg 1 ltac:(rewrite !Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 1368 + 4 * nx)); [|lia];
                  destruct (Z.ltb_spec (p + 1368 + 4 * nx + 4 * tr_low X st) 1); [lia|]; reflexivity).
  zbr Rfd false.
  zbr Rfd false.
  zstep Rfd. zalign.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zsetreg (4 * (tr_next st - nx)) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (tr_next st - nx) ltac:(rewrite srli_small by lia; change (2 ^ 2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_curr X st), Hb : mem_u8 _ _ _ rt, Hv : mem_u16 _ _ _ (tr_next st - nx) |- _ =>
    pose proof (entry_write_t Mc (p + 1368) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite it_fill_len_tr; lia].
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (tr_len X st - rt) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  zstep Rfd. zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K3 Rx Mx) end.
  all: try kauto4.
  all: lazymatch goal with
       | |- sregs_t _ _ _ _ => unfold sregs_t; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st3]; rewrite HDR;
                               rewrite (lowS_small (tr_low X st)) by lia; split_conj; zreg
       | |- zget_l _ _ _ = _ => zregv; rewrite ?HDR; lia
       | |- cmem_t _ _ _ _ _ _ _ _ _ _ => close_cmem_t
       | |- smem_t _ _ _ _ => unfold smem_t; cbn [t_count t_tbl tr_st3]; split; [exact Hcnt|]; unfold tr_tbl2; cbn [x_table x_root itm_ctx]; exact Htbl
       | |- _ => lia
       end.
Qed.

Lemma snez_cty1 : Z.b2z (0 <? (cty ty + -1) mod 18446744073709551616) = 1 - isL ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.
Lemma seqz_cty2 : Z.b2z ((cty ty + -2) mod 18446744073709551616 <? 1) = isD ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.

Lemma enough_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kS7 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kS10 = tr_curr X st -> zget_l Rb l kA2 = p + 1368 + 4 * tr_next st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_curr X st <= 15 -> 1 <= tr_len X st <= 15 ->
  Kbody3_t st M MD T -> Kfail_t st M MD T ->
  realizes R_segs (zcfg R_segs 140308 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LRA LT4 LS9 LT1 HM HSM HP TOK Hbrk Hsub Hmx HLOW HDR HCU TLR K3 KF.
  pose proof C as C'. open_itc C'. open_cmem_t HM. open_spure HP. zkeys.
  trip_facts TOK. clear Flook Fwm Fcont Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
  { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
  pose proof (ne_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192') as (IL & ID & ILD & NE').
  open_cregs_t HC. open_uregs_t HU. zkeys. zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (1 - isL ty) ltac:(symmetry; apply snez_cty1).
  zstep Rfd. zsetreg (2 ^ tr_curr X st) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (tr_used X st) ltac:(rewrite EU, swrap32_small by lia; lia).
  zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
  destruct IL as [IL0|IL1].
  -
    zstep Rfd. zsetreg 1 ltac:(rewrite IL0; destruct (tr_used X st <? 853); reflexivity).
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
    zstep Rfd. zsetreg (isD ty) ltac:(symmetry; apply seqz_cty2).
    zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
    destruct ID as [ID0|ID1].
    + zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_t st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      * unfold cmem_t; split_conj; assumption.
      * unfold spure; split_conj; assumption.
      * rewrite NE', IL0, ID0. reflexivity.
    + zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite ID1; symmetry; apply land1_b2z).
      destruct (Z.leb_spec 593 (tr_used X st)) as [GE|LT].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
        all: try kauto4. rewrite NE', IL0, ID1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_t st Rx [] M MD T) end.
        all: try kauto4. all: try assumption. all: try lia.
        -- unfold cmem_t; split_conj; assumption.
        -- unfold spure; split_conj; assumption.
        -- rewrite NE', IL0, ID1. cbn [Z.eqb]. apply Z.ltb_ge. lia.
  -
    assert (ID0 : isD ty = 0) by lia.
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite IL1; cbn [Z.sub Z.pos_sub]; destruct (tr_used X st <? 853); reflexivity).
    destruct (Z.ltb_spec (tr_used X st) 853) as [LT|GE].
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
      zstep Rfd. zsetreg (isD ty) ltac:(symmetry; apply seqz_cty2).
      zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
      zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_t st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      * unfold cmem_t; split_conj; assumption.
      * unfold spure; split_conj; assumption.
      * rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_ge. lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
      all: try kauto4. rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
Qed.

Lemma currsz_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kS7 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kA2 = p + 1368 + 4 * tr_next st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  1 <= tr_len X st <= 15 -> rt < tr_len X st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3_t st M MD T -> Kfail_t st M MD T ->
  realizes R_segs (zcfg R_segs 140216 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LRA LT4 LT1 HM HSM HP TOK Hbrk Hsub Hmx TLR RTL HLOW HDR K3 KF.
  pose proof C as C'. open_itc C'. open_smem_t HSM. open_spure HP. zkeys.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  pose proof (tr_count_range st HCr) as HCr1.
  set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
  pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
  assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
  { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
    fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
  pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
  rewrite <- ETC in CR1, CR2, CR3.
  open_cregs_t HC. open_uregs_t HU. zkeys. zrebase.
  zstep Rfd. zsetreg c0 ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd.
  zbr Rfd false.
  destruct (Z_lt_le_dec (tr_len X st) mx) as [LT|GE].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zsetreg (2 ^ c0) ltac:(symmetry; apply sllw_1; lia).
    zstep Rfd. zsetreg (mx - rt) ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (curr_loop_t 15%nat c0 (2 ^ c0) 16 (tr_count st) st (t_used st) _ (p + 1368 + 4 * tr_next st) Rx [] M MD T) end.
    all: try kauto4. all: try lia. all: try (zregv; reflexivity).
    clear_regs. intros R' HC' HU' L4 L1 LT1' LR L9. rewrite <- ETC in L9. specialize (CR2 ltac:(lia)).
    open_cregs_t HC'. open_uregs_t HU'. zkeys. zrebase.
    zstep Rfd.
    zbr Rfd false.
    eapply enough_t; try eassumption; try lia. all: try kauto4.
    + unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
  - zbr Rfd true.
    assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (enough_t st Rx [] M MD T) end.
    all: try kauto4. all: try (rewrite ETC0; zreg). all: try lia.
    + unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
Qed.

Lemma sub_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR (tr_st1 X st) Rb l -> zget_l Rb l kS4 = 2 ^ t_curr st -> zget_l Rb l kS0 = Z.shiftl (tr_sym st) 32 ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> 1 <= mx ->
  (forall R', CR R' [] -> SR (tr_st1 X st) R' [] ->
     zget_l R' [] kT1 = tr_len X st - t_drop st -> zget_l R' [] kA2 = p + 792 + 2 * tr_sym st ->
     tr_sub X st = false ->
     realizes R_segs (zcfg R_segs 139704 (zupd R' []) M MD) T) ->
  Kbody3_t st M MD T -> Kfail_t st M MD T ->
  realizes R_segs (zcfg R_segs 140160 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS4 LT6 HM HSM HP TOK Hbrk Hmx K1 K3 KF.
  pose proof C as C'. open_itc C'. open_spure HP. pose proof HM as HM'. open_cmem_t HM'. zkeys. xaddr_t.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  trip_facts TOK. clear Fwm Fcont.
  pose proof (pow2_le15 rt ltac:(lia)) as PRT. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC.
  assert (TLR : 1 <= tr_len X st <= 15).
  { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
    destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
    destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
    unbox Flook. destruct (Flook E0 NEM) as (W1 & W2 & W3 & W4).
    replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). exact W4. }
  clear Flook.
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
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
  assert (Hroom3 : t_next st < 1444).
  { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
    assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
  assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
  pose proof (lnot_val_mod' (p + 792) ltac:(lia)) as Hnw.
  assert (JB : forall RJ, CR RJ [] -> SR (tr_st1 X st) RJ [] -> zget_l RJ [] kS0 = Z.shiftl (tr_sym st) 32 ->
            tr_sub X st = false -> realizes R_segs (zcfg R_segs 139668 (zupd RJ []) M MD) T).
  { intros RJ HCJ HSJ JT6 Hsub. open_cregs_t HCJ. open_sregs_t HSJ.
    cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LA6, LS6, LT4, LS11, LT6, LT5, LS2, LS10. zkeys. zrebase.
    zstep Rfd. zstep Rfd.
    zstep Rfd. zsetreg (tr_len X st - t_drop st) ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).
    zstep Rfd.
    zstep Rfd. zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
    all: try kauto4.
    unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg. }
  assert (J04 : forall RJ, CR RJ [] -> uregs_t st RJ [] -> zget_l RJ [] kS6 = t_drop st -> zget_l RJ [] kT5 = t_used st ->
            zget_l RJ [] kS2 = p + 1368 + 4 * t_next st -> zget_l RJ [] kS4 = 2 ^ t_curr st ->
            tr_sub X st = true -> realizes R_segs (zcfg R_segs 140180 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ JS5 JT4 JS1 JS4 Hsub.
    assert (RTL : rt < tr_len X st).
    { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
    assert (JDC : forall RK, CR RK [] -> uregs_t st RK [] -> zget_l RK [] kS7 = rt -> zget_l RK [] kT5 = t_used st ->
              zget_l RK [] kS2 = p + 1368 + 4 * t_next st -> zget_l RK [] kS4 = 2 ^ t_curr st ->
              realizes R_segs (zcfg R_segs 140192 (zupd RK []) M MD) T).
    { intros RK HCK HUK KRA KT4 KS1 KS4. open_cregs_t HCK. open_uregs_t HUK. zkeys. zrebase.
      zbr Rfd false.
      zstep Rfd.
      zstep Rfd. zsetreg (4 * 2 ^ t_curr st) ltac:(symmetry; apply zext32_x4; lia).
      zstep Rfd. zsetreg (p + 1368 + 4 * tr_next st) ltac:(rewrite ENX; lia).
      zbr Rfd false.
      zbr Rfd false.
      eapply currsz_t; try eassumption; try lia. all: try kauto4.
      unfold spure; split_conj; try assumption. }
    open_cregs_t HCJ. open_uregs_t HUJ. zkeys. zrebase.
    zstep Rfd.
    unbox DROPR. destruct DROPR as [D0|D1].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JDC Rx) end.
      all: try kauto4.
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JDC Rx) end.
      all: try kauto4. }
  open_cregs_t HC. open_sregs_t HS. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LA6, LS6, LT4, LS11, LT6, LT5, LS2, LS10.
  zkeys. zrebase.
  destruct (Z_lt_le_dec rt (tr_len X st)) as [SUB1|NOSUB1].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zsetreg (tr_low X st) ltac:(exact (eq_sym ELOW)).
    unbox LOWR. destruct LOWR as [LM|LSM].
    +
      zstep Rfd. zsetreg (-1) ltac:(unfold lowS; rewrite LM; reflexivity).
      zbr_by false ltac:(cbv beta iota delta [zcond]; rewrite (mod_small_u64 (tr_low X st)) by lia;
                         try change ((-1) mod 18446744073709551616) with 18446744073709551615; apply Z.eqb_neq; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx) end.
      all: try kauto4.
      unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
      replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
    + zstep Rfd. zsetreg (t_low st) ltac:(rewrite (lowS_small (t_low st)) by lia; rewrite swrap32_small by lia; lia).
      destruct (Z.eq_dec (tr_low X st) (t_low st)) as [EQL|NEL].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JB Rx) end.
        all: try kauto4.
        -- unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
        -- unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, EQL, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx) end.
        all: try kauto4.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JB Rx) end.
    all: try kauto4.
    + unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
    + unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End U7IT4.
End FXG.
