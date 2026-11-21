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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6U Require Import Base T_It1 T_It2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Definition EXA (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | LENS => 75248 | DISTS => 75374 end.
Definition BSA (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | LENS => 75186 | DISTS => 75310 end.
Definition EXM (ty : codetype) (p : Z) : Z := match ty with CODES => p + 792 | LENS => 75248 | DISTS => 75374 end.
Definition BSM (ty : codetype) (p : Z) : Z := match ty with CODES => p + 792 | LENS => 75186 | DISTS => 75310 end.
Lemma EXM_EXA : forall ty p, ty <> CODES -> EXM ty p = EXA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Lemma BSM_BSA : forall ty p, ty <> CODES -> BSM ty p = BSA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Definition NEX (ty : codetype) : Z := match ty with CODES => 0 | _ => NE ty end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section U7IT3.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).

Lemma C192 : S_It0.itc ty lf lens_ofs codes nx bits cf wf p (p + 136) sp ret 192 zc.
Proof using C. destruct C; constructor; try assumption; try (left; reflexivity). lia_std. Qed.

Definition pregs8 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\ zget_l R l kA0 = cty ty /\
  zget_l R l kA1 = p + 152 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 144 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 792.
Ltac open_pregs8 H := unfold pregs8 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in destruct H as (a & b & c & d & e & g & h & i).
Ltac close_pregs8 := unfold pregs8; split_conj; zreg.

Definition cregs_t (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs8 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kT2 = it_match ty /\
  zget_l R l kS1 = sp + -136 /\ zget_l R l kS9 = - (sp + -136) + -1.
Definition sregs_t (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kA6 = lowS (t_low st) /\
  zget_l R l kS6 = t_drop st /\ zget_l R l kT4 = t_sym st /\ zget_l R l kS11 = t_len st /\ zget_l R l kT6 = t_huff st /\
  zget_l R l kT5 = t_used st /\ zget_l R l kS2 = p + 1368 + 4 * t_next st /\ zget_l R l kS10 = t_curr st.
Definition cmem_t (M : mem) : Prop :=
  mem_wr R_segs M (sp - 208) 208 /\ mem_wr R_segs M p 7160 /\
  mem_arr 2 R_segs M (p + 152) 320 lf /\
  mem_arr 2 R_segs M (p + 792) 288 (arr_get work1Ar) /\
  mem_u64 R_segs M (p + 144) (p + 1368 + 4 * nx) /\
  mem_u64 R_segs M (sp + -208) (EXA ty p) /\ mem_u64 R_segs M (sp + -200) (2 ^ rt - 1) /\
  mem_u64 R_segs M (sp + -192) (BSA ty p) /\ mem_u64 R_segs M (sp + -184) (isL ty + isD ty) /\
  mem_u64 R_segs M (sp + -176) (- (p + 792) + -1) /\
  mem_arr 2 R_segs M (EXM ty p) (NE ty) (it_extra ty work1Ar) /\
  mem_arr 2 R_segs M (BSM ty p) (NE ty) (it_base ty work1Ar).
Definition smem_t (st : ItSt) (M : mem) : Prop :=
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get (t_count st)) /\
  mem_arr 4 R_segs M (p + 1368) 1444 (arr_get (t_tbl st)).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Ltac open_cregs_t H :=
  unfold cregs_t in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LT2" in
  let h := fresh "LS1" in let i := fresh "LS9" in
  destruct H as (hp & a & b & c & h & i); open_pregs8 hp.
Ltac open_sregs_t H :=
  unfold sregs_t in H;
  let c := fresh "LA6" in let d := fresh "LS6" in
  let e := fresh "LT4" in let f := fresh "LS11" in let g := fresh "LT6" in let h := fresh "LT5" in
  let i := fresh "LS2" in let j := fresh "LS10" in
  destruct H as (c & d & e & f & g & h & i & j).
Ltac open_cmem_t H :=
  unfold cmem_t in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f0 := fresh "Hsl0" in let f1 := fresh "Hsl8" in let f2 := fresh "Hsl16" in let f3 := fresh "Hsl24" in let f4 := fresh "Hsl32" in
  let h := fresh "Hext" in let i := fresh "Hbase" in
  destruct H as (a & b & c & d & e & f0 & f1 & f2 & f3 & f4 & h & i).
Ltac open_smem_t H :=
  unfold smem_t in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in destruct H as (a & b).
Ltac close_cregs_t := unfold cregs_t; split_conj; try close_pregs8; zreg.
Ltac close_sregs_t := unfold sregs_t; split_conj; zreg.
Ltac close_cmem_t := unfold cmem_t; split_conj; assumption.
Ltac close_smem_t := unfold smem_t; split_conj; assumption.
Ltac kauto_t := first
  [ assumption
  | lazymatch goal with
    | |- cregs_t _ _ => close_cregs_t
    | |- sregs_t (tr_st1 _ _) _ _ => fail
    | |- sregs_t (tr_st3 _ _) _ _ => fail
    | |- sregs_t _ _ _ => close_sregs_t
    | |- pregs8 _ _ => close_pregs8
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].

Lemma xaddr_facts_t :
  ZSEP (p + 7144 <= EXM ty p \/ EXM ty p + 2 * NE ty <= p + 1368) /\
  ZSEP (p + 7144 <= BSM ty p \/ BSM ty p + 2 * NE ty <= p + 1368) /\
  0 < EXM ty p /\ EXM ty p + 2 * NE ty <= zc /\
  0 < BSM ty p /\ BSM ty p + 2 * NE ty <= zc /\ 0 < NE ty <= 288 /\
  EXM ty p mod 2 = 0 /\ BSM ty p mod 2 = 0.
Proof using C ret sp pb wf cf bits nx codes lens_ofs lf.
  pose proof C as C'. open_itc C'. unfold ZSEP in *.
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  destruct ty; cbn [EXM BSM NE]; repeat split; try lia_std; try reflexivity.
  all: replace (p + 792) with (p + 2 * 396) by lia_std; apply mod0_add; [lia_std | exact P2 | apply mod0_mul; lia_std].
Qed.
Ltac xaddr_t := pose proof xaddr_facts_t as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).

Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

Lemma here_t : forall st Rb l M MD T,
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kA2 = p + 792 + 2 * t_sym st -> zget_l Rb l kT1 = tr_hb st ->
  cmem_t M -> SP st ->
  0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 -> (ty = CODES -> arr_get work1Ar (t_sym st) < 20) ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  (forall R', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = tr_hb st -> zget_l R' [] kA2 = tr_op X st -> zget_l R' [] kS7 = tr_val X st ->
     realizes R_segs (zcfg R_segs 139836 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 139704 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT2 LT1 HM HU Hsym Hw HC20 Hwm K.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. open_cmem_t HM. open_spure HU. zkeys. xaddr_t.
  pose proof (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HWr. pose proof (base_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HBr.
  pose proof (ext_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HEr.
  assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
  unfold tr_w in Hw, Hwm. rewrite WK in Hw, Hwm. box Hwm. clear HtyC HtyD LOWR DROPR Hpb Hprom.
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  zrebase.
  zstep Rfd. zalign.
  zbr Rfd false.
  tstep Rfd.
  zstep Rfd.
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)) as [Cw1|Cw1'].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto_t.
    + zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
    + zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
  - zbr Rfd true.
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))) as [Cw2|Cw2'].
    + zbr Rfd true.
      unbox Hwm. specialize (Hwm Cw2).
      assert (HNC : ty <> CODES) by (intro E; pose proof (HC20 E) as H20; rewrite E in Cw2; cbn [it_match] in Cw2; lia).
      assert (HFL : isL ty + isD ty = 1) by (destruct ty; cbn [isL isD]; [congruence | lia | lia]).
      rewrite (EXM_EXA ty p HNC) in Hext. rewrite (BSM_BSA ty p HNC) in Hbase.
      rewrite (EXM_EXA ty p HNC) in XS1, XA1, XA2, XAE. rewrite (BSM_BSA ty p HNC) in XS2, XB1, XB2, XBE.
      rewrite HFL in Hsl24.
      zstep Rfd. zsetreg (arr_get work1Ar (t_sym st) - it_match ty) ltac:(symmetry; apply swrap32_small; lia).
      zstep Rfd.
      zstep Rfd. zsetreg (2 * (arr_get work1Ar (t_sym st) - it_match ty)) ltac:(symmetry; apply zext32_x2; lia).
      zstep Rfd.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd. zbool.
      zstep Rfd.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zbr Rfd false.
      zbr Rfd false.
      zstep Rfd. zsetreg (arr_get work1Ar (t_sym st) - it_match ty) ltac:(symmetry; apply zext32_id; lia).
      zstep Rfd. zsetreg (2 * (arr_get work1Ar (t_sym st) - it_match ty)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep Rfd.
      zstep Rfd.
      tstep Rfd.
      tstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto_t.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. cbn [fst]. symmetry. apply wrap8_mod.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. reflexivity.
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto_t.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
Qed.

Lemma lor_shiftl_add : forall x y k, 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y -> Z.lor x (Z.shiftl y k) = x + Z.shiftl y k.
Proof using.
  intros x y k Hk Hx Hy.
  assert (L0 : Z.land x (Z.shiftl y k) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n k).
    - rewrite Z.shiftl_spec_low by lia_std. apply Bool.andb_false_r.
    - destruct (Z.eq_dec x 0) as [->|]; [rewrite Z.bits_0; reflexivity|].
      rewrite (Z.bits_above_log2 x n); [reflexivity | lia_std |].
      apply Z.log2_lt_pow2; [lia_std|]. eapply Z.lt_le_trans; [apply (proj2 Hx) | apply Z.pow_le_mono_r; lia_std]. }
  pose proof (Z.add_lor_land x (Z.shiftl y k)). lia_std.
Qed.

Lemma entry_write2_t : forall M base n f i pk val a0 a2,
  mem_arr 4 R_segs M base i f ->
  mem_arr 4 R_segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u16 R_segs M a0 pk -> mem_u16 R_segs M a2 val ->
  a0 = base + 4 * i -> a2 = a0 + 2 -> 0 <= i < n -> base + 4 * n <= two64 -> 0 <= base -> 0 <= val < 65536 ->
  mem_arr 4 R_segs M base n (zfupd f i (pk mod 65536 + 65536 * val)).
Proof using.
  intros M base n f i pk val a0 a2 H1 H2 Hlo Hhi -> -> Hi Hn Hb Rv.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  change 4%nat with (2 + 2)%nat. rewrite Z_to_le_bytes_add. unfold mem_u16 in *.
  pose proof (Z.mod_pos_bound pk 65536 ltac:(lia)) as PM.
  apply mem_is_app; [| | rewrite two64_eq in *; lia | rewrite !length_Z_to_le_bytes; cbn; rewrite two64_eq in *; lia].
  - rewrite <- Z_to_le_bytes_2_mod. replace ((pk mod 65536 + 65536 * val) mod 65536) with (pk mod 65536); [rewrite Z_to_le_bytes_2_mod; exact Hlo|].
    rewrite Z.mul_comm, Z_mod_plus_full. rewrite Z.mod_mod by lia. reflexivity.
  - rewrite length_Z_to_le_bytes. change (Z.of_nat 2) with 2.
    replace (Z.shiftr (pk mod 65536 + 65536 * val) (8 * 2)) with val; [exact Hhi|].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 2)) with 65536. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma fill_loop_t : forall trips f t n st pk Rb l M MD T,
  f = 2 ^ tr_hb st * Z.of_nat trips -> (1 <= trips)%nat -> Z.of_nat trips <= n ->
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = 256 * tr_hb st -> zget_l Rb l kS4 = 2 ^ t_curr st ->
  zget_l Rb l kA2 = f -> zget_l Rb l kS5 = - 2 ^ tr_hb st -> zget_l Rb l kS0 = tr_hd st + (f - 2 ^ tr_hb st) ->
  zget_l Rb l kS7 = pk -> zget_l Rb l kS3 = tr_val X st -> zget_l Rb l kT3 = 1 ->
  pk mod 65536 + 65536 * tr_val X st = tr_here X st ->
  0 <= tr_hb st <= 15 -> 0 <= t_next st -> 0 <= tr_hd st -> t_next st + tr_hd st + f - 2 ^ tr_hb st < 1444 ->
  0 <= tr_val X st < 65536 ->
  mem_wr R_segs M p 7160 -> mem_arr 4 R_segs M (p + 1368) 1444 (arr_get t) -> arr_len t = 1444 ->
  (forall R' M', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = 256 * tr_hb st -> zget_l R' [] kS4 = 2 ^ t_curr st ->
     mpost R_segs M M' (p + 1368) (p + 7144) 0 0 ->
     mem_wr R_segs M' p 7160 ->
     mem_arr 4 R_segs M' (p + 1368) 1444 (arr_get (snd (loopZ n (fill_body (tr_here X st) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (f, t)))) ->
     realizes R_segs (zcfg R_segs 139960 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139900 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction trips as [|trips IH]; intros f t n st pk Rb l M MD T Hf Htr Hn Hh HC HS LT1 LS4 LT2 LT3 LT6 LS7 LS3 LS2 EPK Hhb Hnx0 Hhd Hfit Rval Wp Htbl TL K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI.
  set (I := 2 ^ tr_hb st) in *.
  pose proof (mpost_stable R_segs M (p + 1368) (p + 7144) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1368) (p + 7144) 0 0) M) by (apply mpost_refl).
  assert (Hf1 : I <= f) by (rewrite Hf; apply mul_S_ge; lia).
  assert (W1 : wrap32 (f - I) = f - I) by (apply wrap32_small; lia).
  destruct (arr4_hole R_segs M (p + 1368) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) Htbl ltac:(lia)) as [HT1 HT2].
  clear Htbl. zrebase.
  zstep Rfd.
  zstep Rfd. zsetreg (4 * (tr_hd st + (f - I))) ltac:(symmetry; apply zext32_x4; lia).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zstep Rfd.
  zsetreg 1 ltac:(rewrite Z.mod_small by lia; destruct (Z.ltb_spec (4 * (tr_hd st + (f - I)) + (p + 1368 + 4 * t_next st)) 1); [lia | reflexivity]).
  zbr Rfd false.
  zstep Rfd. zsetreg (f - I) ltac:(symmetry; apply swrap32_small; lia).
  zstep Rfd. zsetreg (tr_hd st + (f - I)) ltac:(symmetry; apply zext32_id; lia).
  zstep Rfd. zsetreg (4 * (tr_hd st + (f - I))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ pk, Hv : mem_u16 _ _ _ (tr_val X st) |- _ =>
    pose proof (entry_write2_t Mc (p + 1368) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) pk _ _ _ HT1 HT2 Hlo Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) Rval) as Htbl;
    clear Hlo Hv HT1 HT2
  end.
  rewrite EPK in Htbl.
  apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
  replace (t_next st + tr_hd st + (f - I)) with (t_next st + (tr_hd st + wrap32 (f - I))) in Htbl by lia.
  zstep Rfd. zsetreg (tr_hd st + (f - I - I)) ltac:(lia).
  destruct (Z.eq_dec (f - I) 0) as [Hz|Hnz].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
    all: try kauto_t.
    rewrite fill_last by first [lia | rewrite W1; exact Hz]. cbn [snd]. rewrite W1, Hz in Htbl. exact Htbl.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (f - I) (arr_set t (t_next st + (tr_hd st + wrap32 (f - I))) (tr_here X st)) (n - 1) st pk Rx [] Mx MD T) end.
    all: try kauto_t.
    all: try (rewrite Hf; apply mul_S_sub).
    all: try (rewrite arr_len_set; exact TL).
    all: try (zregv; subst I; lia).
    all: try (destruct trips; [cbn in Hf; exfalso; lia | lia]).
    intros R' M'. intros. eapply K; try eassumption.
    * eapply mpost_trans; [exact HAG | assumption].
    * rewrite fill_more by first [lia | rewrite W1; exact Hnz]. subst I. rewrite W1 in *. assumption.
Qed.

Lemma op_val_range_t : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  0 <= tr_op X st < 256 /\ 0 <= tr_val X st < 65536.
Proof using C zc ret sp pb p cf. intros. eapply op_val_range; try eassumption. exact C192. Qed.

Lemma fill_t : forall st Rb l M MD T,
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = tr_hb st ->
  zget_l Rb l kA2 = tr_op X st -> zget_l Rb l kS7 = tr_val X st ->
  SP st -> it_trip_ok X 288 320 1444 st = true ->
  mem_wr R_segs M p 7160 -> mem_arr 4 R_segs M (p + 1368) 1444 (arr_get (t_tbl st)) ->
  (forall R' M', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = 256 * tr_hb st -> zget_l R' [] kS4 = 2 ^ t_curr st ->
     mpost R_segs M M' (p + 1368) (p + 7144) 0 0 -> mem_wr R_segs M' p 7160 ->
     mem_arr 4 R_segs M' (p + 1368) 1444 (arr_get (tr_tbl1 X st)) ->
     realizes R_segs (zcfg R_segs 139960 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139836 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 LT2 LS7 HU TOK Wp Htbl K.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. open_spure HU. zkeys.
  trip_facts TOK.
  unbox Fwm. pose proof (op_val_range_t st WK Fw Fwm) as [Rop Rval].
  clear Fwm Flook Fcont LOWR DROPR Hprom HtyC HtyD Hlf Hcf Hwf HCr HTr Hpb Hlens15.
  assert (Ehb : tr_hb st = t_len st - t_drop st) by reflexivity.
  assert (Hhb : 0 <= tr_hb st <= 15) by lia.
  assert (Hhd : 0 <= tr_hd st <= t_huff st).
  { unfold tr_hd. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (t_drop st) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PF.
  pose proof (pow2_le15 (t_curr st - tr_hb st) ltac:(lia)) as PQ.
  assert (EQ : 2 ^ t_curr st = 2 ^ tr_hb st * 2 ^ (t_curr st - tr_hb st)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hfit' : t_next st + tr_hd st + 2 ^ t_curr st - 2 ^ tr_hb st < 1444) by (unfold tr_hd; rewrite Ehb; exact Ffit).
  assert (FI : 2 ^ tr_hb st <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
  set (pk := tr_op X st + 256 * tr_hb st + 65536 * tr_val X st).
  assert (EPK : pk mod 65536 + 65536 * tr_val X st = tr_here X st).
  { unfold tr_here. rewrite (wrap8_mod (tr_hb st)). rewrite (Z.mod_small (tr_hb st)) by lia.
    rewrite code_pack_small by lia. subst pk.
    replace (tr_op X st + 256 * tr_hb st + 65536 * tr_val X st) with (tr_op X st + 256 * tr_hb st + tr_val X st * 65536) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia. }
  zrebase.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zsetreg (- 2 ^ tr_hb st) ltac:(symmetry; apply sllw_m1; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ t_curr st) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (tr_hd st) ltac:(unfold tr_hd; symmetry; apply srlw_small; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (256 * tr_hb st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (tr_op X st + 256 * tr_hb st)
    ltac:(replace (256 * tr_hb st) with (Z.shiftl (tr_hb st) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
          rewrite lor_shiftl_add by (try (change (2 ^ 8) with 256); lia); rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  zstep Rfd.
  zstep Rfd. zsetreg pk
    ltac:(rewrite Z.lor_comm, lor_shiftl_add by (try (change (2 ^ 16) with 65536); lia); rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; subst pk; lia).
  zstep Rfd. zsetreg (tr_hd st + (2 ^ t_curr st - 2 ^ tr_hb st)) ltac:(lia).
  zstep Rfd. zsetreg 1 ltac:(rewrite Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 1368 + 4 * t_next st)); [reflexivity | lia]).
  zstep Rfd. zsetreg (tr_val X st)
    ltac:(rewrite srli_small by (subst pk; lia); change (2 ^ 16) with 65536; subst pk;
          replace (tr_op X st + 256 * tr_hb st + 65536 * tr_val X st) with (tr_val X st * 65536 + (tr_op X st + 256 * tr_hb st)) by lia;
          rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia).
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (fill_loop_t (Z.to_nat (2 ^ (t_curr st - tr_hb st))) (2 ^ t_curr st) (t_tbl st) (2 ^ t_curr st) st pk Rx [] M MD T) end.
  all: try kauto_t.
  all: try exact EPK.
  - rewrite Z2Nat.id by lia. exact EQ.
  - lia.
  - rewrite Z2Nat.id by lia. apply Z.pow_le_mono_r; lia.
  - lia.
  - intros R' M'. intros. eapply K; try eassumption.
    unfold tr_tbl1. rewrite it_fill_eq. unfold tr_incr, tr_fill. rewrite !shl32_1 by lia. assumption.
Qed.


Lemma incr_loop_t : forall m c n st Rb l M MD T,
  0 <= c < 2 ^ Z.of_nat m -> Z.of_nat m < n -> c < 65536 ->
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = 256 * tr_hb st -> zget_l Rb l kS4 = 2 ^ t_curr st ->
  zget_l Rb l kT3 = c -> 0 <= t_huff st < 65536 ->
  (forall R', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = 256 * tr_hb st -> zget_l R' [] kS4 = 2 ^ t_curr st ->
     zget_l R' [] kA2 = loopZ n (incr_body (t_huff st)) c ->
     realizes R_segs (zcfg R_segs 140000 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 139980 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  induction m as [|m IH]; intros c n st Rb l M MD T Hc Hn Hc2 Hh HC HS LT1 LS4 LT3 Hhuff K.
  - cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hc. assert (E : c = 0) by lia. rewrite E in *. clear E Hc Hc2.
    pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hpb.
    zrebase. zstep Rfd. zstep Rfd. zsetreg 0 ltac:(rewrite Z.land_0_l; reflexivity).
    zstep Rfd. zsetreg 0 ltac:(reflexivity). zstep Rfd. zsetreg 0 ltac:(reflexivity).
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto_t. zregv. symmetry. apply incr_last; [lia | apply Z.land_0_r].
  - pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hpb.
    assert (HA : 0 <= Z.land c (t_huff st) <= c) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
    pose proof (shiftr1_half c m Hc) as HH.
    assert (HH2 : Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; apply Z.div_le_upper_bound; lia).
    zrebase.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zsetreg (Z.land c (t_huff st)) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zsetreg (Z.shiftr c 1) ltac:(transitivity (c / 2 ^ 1); [rewrite Z.shiftr_div_pow2 by lia; reflexivity | symmetry; apply srliw_small; lia]).
    destruct (Z.eq_dec (Z.land c (t_huff st)) 0) as [Z0|NZ].
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto_t. zregv. symmetry. apply incr_last; [lia | rewrite Z.land_comm; exact Z0].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (Z.shiftr c 1) (n - 1) st Rx [] M MD T) end.
      all: try kauto_t. all: try lia.
      intros R' HC' HS' L1 L4 L2. eapply K; try eassumption. rewrite incr_more; [exact L2 | lia | rewrite Z.land_comm; exact NZ].
Qed.

Ltac close_sregs1_t EL := unfold sregs_t; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.

Definition Ksub_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregs_t R' [] -> sregs_t (tr_st1 X st) R' [] ->
    zget_l R' [] kS4 = 2 ^ t_curr st -> zget_l R' [] kS0 = Z.shiftl (tr_sym st) 32 ->
    mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> cmem_t M' -> smem_t (tr_st1 X st) M' ->
    tr_brk X st = false ->
    realizes R_segs (zcfg R_segs 140160 (zupd R' []) M' MD) T.
Definition Kbrk_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregs_t R' [] -> sregs_t (tr_st1 X st) R' [] ->
    zget_l R' [] kT1 = 256 * tr_hb st ->
    mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> cmem_t M' -> smem_t (tr_st1 X st) M' ->
    tr_brk X st = true ->
    realizes R_segs (zcfg R_segs 140440 (zupd R' []) M' MD) T.

Lemma count_t : forall st Rb l M MD T,
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = 256 * tr_hb st -> zget_l Rb l kS4 = 2 ^ t_curr st ->
  cmem_t M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get (t_count st)) ->
  mem_arr 4 R_segs M (p + 1368) 1444 (arr_get (tr_tbl1 X st)) ->
  Ksub_t st M MD T -> Kbrk_t st M MD T ->
  realizes R_segs (zcfg R_segs 139960 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 LS4 HM HU TOK Hcnt Htbl KS KB.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. open_cmem_t HM. open_spure HU. zkeys. xaddr_t.
  trip_facts TOK. clear Fcont Fwm Hprom HtyC HtyD Hcf Hwf DROPR.
  pose proof (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HWr.
  pose proof (mx15 lf lens_ofs codes) as MXR.
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  pose proof (lnot_val_mod' (sp + -136) ltac:(lia)) as Hn8.
  pose proof (lnot_val_mod' (p + 792) ltac:(lia)) as Hnw.
  pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL.
  zrebase.
  zstep Rfd. zsetreg (t_len st - 1) ltac:(symmetry; apply swrap32_small; lia).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ (t_len st - 1)) ltac:(symmetry; apply sllw_1; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (incr_loop_t (Z.to_nat (t_len st)) (2 ^ (t_len st - 1)) 32 st Rx [] M MD T) end.
  all: try kauto_t.
  { rewrite Z2Nat.id by lia. split; [lia|]. apply Z.pow_lt_mono_r; lia. }
  { lia. }
  { assert (2 ^ (t_len st - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  clear_regs. intros R1 HC HS L1 L4 L2.
  assert (EI : loopZ 32 (incr_body (t_huff st)) (2 ^ (t_len st - 1)) = tr_incr2 st).
  { unfold tr_incr2. rewrite it_incr_back_eq, shl32_1 by lia. reflexivity. }
  pose proof (incr_range (t_huff st) 32 (2 ^ (t_len st - 1)) ltac:(lia)) as IR.
  rewrite EI in L2, IR. clear EI.
  assert (I14 : 2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
  set (v1 := Z.land (tr_incr2 st - 1) (t_huff st) + tr_incr2 st).
  assert (HL : 0 <= Z.land (tr_incr2 st - 1) (t_huff st) <= t_huff st).
  { destruct (Z.eq_dec (tr_incr2 st) 0) as [E0|NE0].
    - rewrite E0. change (0 - 1) with (-1). rewrite Z.land_m1_l. lia.
    - split; [apply Z.land_nonneg; lia | apply land_le_r; lia]. }
  assert (EH : tr_huff st = Z.land (Z.b2z (tr_incr2 st =? 0) + -1) v1).
  { unfold tr_huff, v1. destruct (Z.eqb_spec (tr_incr2 st) 0) as [E0|NE0]; cbn [Z.b2z negb Z.add].
    - symmetry. apply Z.land_0_l.
    - rewrite Z.land_m1_l. rewrite Z.land_comm. reflexivity. }
  set (c0 := arr_get (t_count st) (t_len st)).
  pose proof (HCr (t_len st) ltac:(lia)) as HC0. fold c0 in HC0.
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  open_cregs_t HC. open_sregs_t HS. zkeys. zrebase.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zsetreg (2 * t_len st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zbr Rfd false.
  zstep Rfd. zsetreg (Z.b2z (tr_incr2 st =? 0))
    ltac:(rewrite (Z.mod_small (tr_incr2 st)) by lia; destruct (Z.eqb_spec (tr_incr2 st) 0); destruct (Z.ltb_spec (tr_incr2 st) 1); cbn [Z.b2z]; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (tr_sym st) ltac:(rewrite ESY; lia).
  zstep Rfd.
  zstep Rfd.
  tstep Rfd.
  fold c0. set (c0s := bv_swrap 16 c0) in *.
  pose proof (swrap16_cases c0 HC0) as HS16. fold c0s in HS16.
  assert (HSR : -32768 <= c0s <= c0) by (destruct HS16; lia). box HS16.
  zstep Rfd. zsetreg v1 ltac:(unfold v1; symmetry; apply swrap32_small; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (-281474976710656) ltac:(reflexivity).
  zstep Rfd.
  zstep Rfd. zsetreg (tr_huff st) ltac:(exact EH).
  zstep Rfd.
  zstep Rfd.
  tstore_arr Rfd Hcnt (t_len st).
  assert (Hcnt' : forall Mq, mem_arr 2 R_segs Mq (sp + -136) 16 (zfupd (arr_get (t_count st)) (t_len st) (c0s + -1)) ->
                             mem_arr 2 R_segs Mq (sp + -136) 16 (arr_get (tr_count st))).
  { intros Mq Hq. eapply mem_arr_ext_mod; [exact Hq|]. intros j Hj. unfold tr_count, zfupd, tr_c. fold c0.
    change (cell_mod 2) with 65536. rewrite arr_get_set. unfold arr_inb. rewrite CL.
    destruct (Z.eqb_spec j (t_len st)) as [Ej|NEj].
    - subst j. rewrite Z.eqb_refl. destruct (Z.leb_spec 0 (t_len st)); destruct (Z.ltb_spec (t_len st) 16); cbn [andb]; try lia.
      rewrite wrap16_mod. rewrite Z.mod_mod by lia. unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B; [f_equal; lia|].
      replace (c0 - 65536 + -1) with ((c0 - 1) + (-1) * 65536) by lia. rewrite Z_mod_plus_full. reflexivity.
    - destruct (Z.eqb_spec (t_len st) j); [lia|]. cbn [andb]. reflexivity. }
  apply Hcnt' in Hcnt. clear Hcnt'.
  assert (EC : tr_c st = (c0 - 1) mod 65536) by (unfold tr_c; fold c0; apply wrap16_mod).
  zstep Rfd. zsetreg ((c0s + -1) * 281474976710656) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 48) with 281474976710656; lia).
  zstep Rfd.
  destruct (Z.eq_dec c0 1) as [C1|NC1].
  - assert (C1s : c0s = 1) by (unbox HS16; destruct HS16; lia).
    zbr Rfd false.
    assert (EC0 : tr_c st = 0) by (rewrite EC, C1; reflexivity).
    destruct (Z.eq_dec (t_len st) mx) as [LM|NLM].
    + zbr Rfd true.
      assert (EL : tr_len X st = t_len st).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [reflexivity | lia]. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB Rx Mx) end.
      all: try kauto_t.
      * close_sregs1_t EL.
      * close_cmem_t.
      * unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_eq. exact LM.
    + zbr Rfd false.
      unbox Flook. destruct (Flook EC0 NLM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. rewrite <- ESY in W1, W2, W3, W4.
      zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zstep Rfd. zalign.
      zbr Rfd false.
      tstep Rfd.
      zstep Rfd. zsetreg (2 * arr_get work1Ar (tr_sym st)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd.
      zsetreg 1 ltac:(rewrite !Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 152 + 2 * lens_ofs)); [|lia];
                      destruct (Z.ltb_spec (p + 152 + 2 * lens_ofs + 2 * arr_get work1Ar (tr_sym st)) 1); [lia|]; reflexivity).
      zbr Rfd false.
      zbr Rfd false.
      zstep Rfd. zalign.
      zbr Rfd false.
      tstep Rfd.
      assert (EL : tr_len X st = lf (lens_ofs + arr_get work1Ar (tr_sym st))).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [lia|].
        cbn [andb negb]. rewrite WK. apply lensA_get. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
      all: try kauto_t.
      * close_sregs1_t EL.
      * close_cmem_t.
      * unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_neq. exact NLM.
  - assert (HNZ : ((c0s + -1) * 281474976710656) mod 18446744073709551616 <> 0).
    { unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B.
      - destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia].
      - rewrite negshift48_mod by lia. lia. }
    zbr Rfd true.
    assert (ECN : tr_c st <> 0).
    { rewrite EC. destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia]. }
    assert (EL : tr_len X st = t_len st).
    { unfold tr_len. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity]. }
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
    all: try kauto_t.
    * close_sregs1_t EL.
    * close_cmem_t.
    * unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
    * unfold tr_brk. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
Qed.
End U7IT3.

End FXG.
Ltac open_pregs8 H := unfold pregs8 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in destruct H as (a & b & c & d & e & g & h & i).
Ltac close_pregs8 := unfold pregs8; split_conj; zreg.
Ltac open_cregs_t H :=
  unfold cregs_t in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LT2" in
  let h := fresh "LS1" in let i := fresh "LS9" in
  destruct H as (hp & a & b & c & h & i); open_pregs8 hp.
Ltac open_sregs_t H :=
  unfold sregs_t in H;
  let c := fresh "LA6" in let d := fresh "LS6" in
  let e := fresh "LT4" in let f := fresh "LS11" in let g := fresh "LT6" in let h := fresh "LT5" in
  let i := fresh "LS2" in let j := fresh "LS10" in
  destruct H as (c & d & e & f & g & h & i & j).
Ltac open_cmem_t H :=
  unfold cmem_t in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f0 := fresh "Hsl0" in let f1 := fresh "Hsl8" in let f2 := fresh "Hsl16" in let f3 := fresh "Hsl24" in let f4 := fresh "Hsl32" in
  let h := fresh "Hext" in let i := fresh "Hbase" in
  destruct H as (a & b & c & d & e & f0 & f1 & f2 & f3 & f4 & h & i).
Ltac open_smem_t H :=
  unfold smem_t in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in destruct H as (a & b).
Ltac close_cregs_t := unfold cregs_t; split_conj; try close_pregs8; zreg.
Ltac close_sregs_t := unfold sregs_t; split_conj; zreg.
Ltac close_cmem_t := unfold cmem_t; split_conj; assumption.
Ltac close_smem_t := unfold smem_t; split_conj; assumption.
Ltac close_sregs1_t EL := unfold sregs_t; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.
Ltac kauto_t := first
  [ assumption
  | lazymatch goal with
    | |- cregs_t _ _ _ _ _ _ _ _ _ _ _ _ => close_cregs_t
    | |- sregs_t _ (tr_st1 _ _) _ _ => fail
    | |- sregs_t _ (tr_st3 _ _) _ _ => fail
    | |- sregs_t _ _ _ _ => close_sregs_t
    | |- pregs8 _ _ _ _ _ _ _ _ _ => close_pregs8
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].
Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.
