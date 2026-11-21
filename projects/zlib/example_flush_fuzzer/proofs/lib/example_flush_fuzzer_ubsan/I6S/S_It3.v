(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6S Require Import Base.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import ZTac ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6S Require Import S_It0 S_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Unset Lia Cache.

Definition lowS (z : Z) : Z := if z =? 4294967295 then -1 else z.

Definition EXA (ty : codetype) (p : Z) : Z := match ty with CODES => p + 808 | LENS => 75248 | DISTS => 75374 end.
Definition BSA (ty : codetype) (p : Z) : Z := match ty with CODES => p + 808 | LENS => 75186 | DISTS => 75310 end.
Definition EXAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => EXA ty p end.
Definition BSAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => BSA ty p end.
Lemma EXAn_ne : forall ty p, ty <> CODES -> EXAn ty p = EXA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Lemma BSAn_ne : forall ty p, ty <> CODES -> BSAn ty p = BSA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Definition NE (ty : codetype) : Z := match ty with CODES => 288 | LENS => 31 | DISTS => 32 end.
Definition isL (ty : codetype) : Z := match ty with LENS => 1 | _ => 0 end.
Definition isD (ty : codetype) : Z := match ty with DISTS => 1 | _ => 0 end.

Lemma NE_ext_len : forall ty, NE ty = it_ext_len ty 288.
Proof. destruct ty; reflexivity. Qed.

Lemma mem_arr2_lo8 : forall M base n f i,
  mem_arr 2 R_segs M base n f -> 0 <= i < n -> mem_u8 R_segs M (base + 2 * i) (f i).
Proof using.
  intros M base n f i H Hi. pose proof (mem_arr_get R_segs 2 M base n f i H Hi) as G.
  change (Z.to_nat 2) with (1 + 1)%nat in G. rewrite Z_to_le_bytes_add in G.
  unfold mem_u8. eapply mem_is_app_l. exact G.
Qed.

Lemma pow2_le15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof.
  intros k Hk. split. - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.
Lemma sllw_1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. pose proof (pow2_le15 k Hk). apply swrap32_small. lia.
Qed.
Lemma sllw_m1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl (-1) (k mod 32)) = - 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. pose proof (pow2_le15 k Hk).
  rewrite swrap32_small by lia. lia.
Qed.
Lemma srlw_small : forall a b, 0 <= a < 2147483648 -> 0 <= b < 32 ->
  bv_swrap 32 (Z.shiftr (a mod 4294967296) (b mod 32)) = Z.shiftr a b.
Proof.
  intros a b Ha Hb. rewrite !Z.mod_small by lia.
  assert (0 <= Z.shiftr a b <= a).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  apply swrap32_small. lia.
Qed.
Lemma mul_S_sub : forall a m, a * Z.of_nat (S m) - a = a * Z.of_nat m.
Proof. intros. rewrite Nat2Z.inj_succ. ring. Qed.
Lemma mul_S_ge : forall a m, 0 <= a -> a <= a * Z.of_nat (S m).
Proof. intros. rewrite Nat2Z.inj_succ. nia. Qed.

Lemma wrap8_mod : forall z, wrap8 z = z mod 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Section S7IT3.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).

Definition pregs6 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\
  zget_l R l kA1 = p + 168 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.
Ltac open_pregs6 H := unfold pregs6 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in destruct H as (a & b & c & e & g & h & i).
Ltac close_pregs6 := unfold pregs6; split_conj; zreg.

Definition cregs (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kA2 = it_match ty /\
  zget_l R l kT3 = EXA ty p /\ zget_l R l kT4 = BSA ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition cregsN (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kA0 = it_match ty /\
  zget_l R l kT3 = EXAn ty p /\ zget_l R l kT2 = BSAn ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition cregsB (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\
  zget_l R l kT3 = EXAn ty p /\ zget_l R l kT2 = BSAn ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition sregs (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT6 = t_sym st /\ zget_l R l kT1 = t_len st /\ zget_l R l kA6 = t_drop st /\ zget_l R l kT5 = t_used st /\
  zget_l R l kS1 = t_huff st /\ zget_l R l kS0 = p + 1384 + 4 * t_next st /\ zget_l R l kA2 = 2 ^ t_curr st /\
  zget_l R l kS7 = lowS (t_low st).
Definition cmem (M : mem) : Prop :=
  mem_wr R_segs M (sp - 192) 192 /\ mem_wr R_segs M p 7176 /\
  mem_arr 2 R_segs M (p + 168) 320 lf /\
  mem_arr 2 R_segs M (p + 808) 288 (arr_get work1Ar) /\
  mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) /\
  mem_u64 R_segs M (sp + -184) (isD ty) /\ mem_u64 R_segs M (sp + -176) (isL ty) /\
  mem_arr 2 R_segs M (EXA ty p) (NE ty) (it_extra ty work1Ar) /\ mem_arr 2 R_segs M (BSA ty p) (NE ty) (it_base ty work1Ar).
Definition smem (st : ItSt) (M : mem) : Prop :=
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get (t_count st)) /\
  mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (t_tbl st)).
Definition spure (st : ItSt) : Prop :=
  t_work st = work1Ar /\ ZSEP (t_low st = 4294967295 \/ 0 <= t_low st < 32768) /\ ZSEP (t_drop st = 0 \/ t_drop st = rt) /\
  0 <= t_next st /\ nx <= t_next st /\
  (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) /\
  (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) /\
  arr_len (t_count st) = 16 /\ arr_len (t_tbl st) = 1444.

Ltac open_cregs H :=
  unfold cregsN in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  destruct H as (hp & a & b & c & d & e & f & g & h & i); open_pregs6 hp.
Ltac open_sregs H :=
  unfold sregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let c := fresh "LA6" in let d := fresh "LT5" in
  let e := fresh "LS1" in let f := fresh "LS0" in let g := fresh "LT2" in let h := fresh "LS7" in
  destruct H as (a & b & c & d & e & f & g & h).
Ltac open_cmem H :=
  unfold cmem in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "HslD" in let g := fresh "HslL" in let h := fresh "Hext" in let i := fresh "Hbase" in
  destruct H as (a & b & c & d & e & f & g & h & i).
Ltac open_smem H :=
  unfold smem in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in destruct H as (a & b).
Ltac open_spure H :=
  unfold spure in H;
  let a := fresh "WK" in let b := fresh "LOWR" in let b2 := fresh "DROPR" in let c := fresh "NX0" in let d := fresh "NX1" in
  let e := fresh "HCr" in let f := fresh "HTr" in let g := fresh "CL" in let h := fresh "TL" in
  destruct H as (a & b & b2 & c & d & e & f & g & h).
Ltac close_cregs := unfold cregsN; split_conj; try close_pregs6; zreg.
Ltac close_sregs := unfold sregs; split_conj; zreg.
Ltac kauto := first
  [ assumption
  | lazymatch goal with
    | |- cregsN _ _ => close_cregs
    | |- sregs (tr_st1 _ _) _ _ => fail
    | |- sregs _ _ _ => close_sregs
    | |- pregs6 _ _ => close_pregs6
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].

Lemma work1_range : forall j, 0 <= j < 288 -> 0 <= arr_get work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx ty.
  intros j Hj. pose proof C as C'. open_itc C'. unfold work1A. rewrite itm_work_eq.
  apply (sort_k_work_range _ _ _ _ _ 288); [|exact Hj]. intros i Hi. rewrite workA_get. apply Hwf. exact Hi.
Qed.

Lemma rt_facts : 1 <= mx -> 1 <= rt <= 15 /\ mn <= rt <= mx /\ 1 <= mn.
Proof using C zc ret sp pb p wf cf nx ty.
  intros H. pose proof (mxmn_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C H) as (A & B & D & E & F). cbv zeta in F.
  destruct (Z.ltb_spec bits mx); [destruct (Z.ltb_spec mn bits) | destruct (Z.ltb_spec mn mx)]; lia_std.
Qed.

Lemma mx15 : 0 <= mx <= 15.
Proof using. unfold mxA. apply mx_range. Qed.

Lemma xaddr_facts :
  ZSEP (p + 7160 <= EXA ty p \/ EXA ty p + 2 * NE ty <= p + 1384) /\
  ZSEP (p + 7160 <= BSA ty p \/ BSA ty p + 2 * NE ty <= p + 1384) /\
  0 <= EXA ty p /\ EXA ty p + 2 * NE ty <= zc /\
  0 <= BSA ty p /\ BSA ty p + 2 * NE ty <= zc /\ 0 < NE ty <= 288.
Proof using C ret sp pb wf cf bits nx codes lens_ofs lf.
  pose proof C as C'. open_itc C'. unfold ZSEP in *. destruct ty; cbn [EXA BSA NE]; lia_std.
Qed.
Ltac xaddr := pose proof xaddr_facts as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma base_range : forall j, 0 <= j < NE ty -> 0 <= it_base ty work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx.
  intros j Hj. pose proof (work1_range j) as W.
  destruct ty; cbn [it_base NE] in *; [apply W; lia_std | apply lbase_range; lia_std | apply dbase_range; lia_std].
Qed.
Lemma ext_range : forall j, 0 <= j < NE ty -> 0 <= it_extra ty work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx.
  intros j Hj. pose proof (work1_range j) as W.
  destruct ty; cbn [it_extra NE] in *; [apply W; lia_std | apply lext_range; lia_std | apply dext_range; lia_std].
Qed.

Lemma here_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> cmem M -> spure st ->
  0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall R', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS10 = tr_op X st -> zget_l R' [] kS9 = tr_val X st ->
     realizes R_segs (zcfg R_segs 128580 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 128504 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HU Hsym Hw Hwm HcB K.
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. open_cmem HM. open_spure HU. zkeys. xaddr.
  pose proof work1_range as HWr. pose proof base_range as HBr. pose proof ext_range as HEr.
  assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
  unfold tr_w in Hw, Hwm. rewrite WK in Hw, Hwm. box Hwm. clear HtyC HtyD LOWR DROPR.
  zrebase.
  zstep Rfd. zstep Rfd. zsetreg (2 * t_sym st) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  tstep Rfd.
  zstep Rfd.
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)) as [Cw1|Cw1'].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto.
    + zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
    + zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
  - zbr Rfd true.
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))) as [Cw2|Cw2'].
    + zbr Rfd true.
      unbox Hwm. specialize (Hwm Cw2).
      assert (Hty : ty <> CODES) by (intro HH; specialize (HcB HH); unfold tr_w in HcB; rewrite WK in HcB; lia).
      rewrite (EXAn_ne _ _ Hty) in LT3. rewrite (BSAn_ne _ _ Hty) in LT4.
      zstep Rfd. zsetreg (arr_get work1Ar (t_sym st) - it_match ty) ltac:(symmetry; apply swrap32_small; lia).
      zstep Rfd. zstep Rfd. zsetreg (2 * (arr_get work1Ar (t_sym st) - it_match ty)) ltac:(symmetry; apply zext32_x2; lia).
      zstep Rfd. zstep Rfd.
      tstep Rfd.
      tstep Rfd.
      rewrite <- (EXAn_ne _ _ Hty) in LT3. rewrite <- (BSAn_ne _ _ Hty) in LT4.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. cbn [fst]. symmetry. apply wrap8_mod.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. reflexivity.
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
Qed.
Lemma entry_write : forall M base n f i op hbits val a0 a1 a2,
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

Lemma fill_loop_s : forall trips f t n st Rb l M MD T,
  f = 2 ^ tr_hb st * Z.of_nat trips -> (1 <= trips)%nat -> Z.of_nat trips <= n ->
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l ->
  zget_l Rb l kS6 = f -> zget_l Rb l kS11 = - 2 ^ tr_hb st -> zget_l Rb l kRA = tr_hd st - 2 ^ tr_hb st ->
  zget_l Rb l kS10 = tr_op X st -> zget_l Rb l kS8 = tr_hb st -> zget_l Rb l kS9 = tr_val X st ->
  0 <= tr_hb st <= 15 -> 0 <= t_next st -> 0 <= tr_hd st -> t_next st + tr_hd st + f - 2 ^ tr_hb st < 1444 ->
  0 <= tr_op X st < 256 -> 0 <= tr_val X st < 65536 ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 (arr_get t) -> arr_len t = 1444 ->
  (forall R' M', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 ->
     mem_wr R_segs M' p 7176 ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (snd (loopZ n (fill_body (tr_here X st) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (f, t)))) ->
     realizes R_segs (zcfg R_segs 128640 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 128600 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction trips as [|trips IH]; intros f t n st Rb l M MD T Hf Htr Hn Hh HC HS LS6 LS11 LRA LS10 LS8 LS9 Hhb Hnx0 Hhd Hfit Rop Rval Wp Htbl TL K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. zkeys.
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI.
  set (I := 2 ^ tr_hb st) in *.
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  assert (Hf1 : I <= f) by (rewrite Hf; apply mul_S_ge; lia).
  assert (W1 : wrap32 (f - I) = f - I) by (apply wrap32_small; lia).
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) Htbl ltac:(lia)) as [HT1 HT2].
  clear Htbl. zrebase.
  zstep Rfd. zsetreg (f - I) ltac:(symmetry; apply swrap32_small; lia).
  zstep Rfd. zsetreg (tr_hd st + (f - I)) ltac:(lia).
  zstep Rfd. zstep Rfd. zsetreg (4 * (tr_hd st + (f - I))) ltac:(symmetry; apply zext32_x4; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_op X st), Hb : mem_u8 _ _ _ (tr_hb st), Hv : mem_u16 _ _ _ (tr_val X st) |- _ =>
    pose proof (entry_write Mc (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) Rop ltac:(lia) Rval) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
  assert (EH : code_pack (tr_op X st) (tr_hb st) (tr_val X st) = tr_here X st).
  { unfold tr_here. rewrite (wrap8_mod (tr_hb st)). rewrite Z.mod_small by lia. reflexivity. }
  rewrite EH in Htbl. clear EH.
  replace (t_next st + tr_hd st + (f - I)) with (t_next st + (tr_hd st + wrap32 (f - I))) in Htbl by lia.
  zstep Rfd.
  destruct (Z.eq_dec (f - I) 0) as [Hz|Hnz].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
    all: try kauto.
    rewrite fill_last by first [lia | rewrite W1; exact Hz]. cbn [snd]. rewrite W1, Hz in Htbl. exact Htbl.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (f - I) (arr_set t (t_next st + (tr_hd st + wrap32 (f - I))) (tr_here X st)) (n - 1) st Rx [] Mx MD T) end.
    all: try kauto.
    all: try (rewrite Hf; apply mul_S_sub).
    all: try (rewrite arr_len_set; exact TL).
    all: try (destruct trips; [cbn in Hf; exfalso; lia | lia]).
    intros R' M'. intros. eapply K; try eassumption.
    * eapply mpost_trans; [exact HAG | assumption].
    * rewrite fill_more by first [lia | rewrite W1; exact Hnz]. subst I. rewrite W1 in *. assumption.
Qed.

Lemma op_val_range : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  0 <= tr_op X st < 256 /\ 0 <= tr_val X st < 65536.
Proof using C zc ret sp pb p cf.
  intros st WK Fw Fwm. assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia_std).
  unfold tr_op, tr_val, tr_ov. cbn [x_ty itm_ctx]. unfold tr_w in *. rewrite WK in Fw, Fwm. rewrite WK.
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [cbn [fst snd]; lia_std|].
  destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); cbn [fst snd]; [|lia_std].
  split; [rewrite wrap8_mod; apply Z.mod_pos_bound; lia_std | apply base_range; lia_std].
Qed.

Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

Lemma fill_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l ->
  zget_l Rb l kS10 = tr_op X st -> zget_l Rb l kS9 = tr_val X st ->
  spure st -> it_trip_ok X 288 320 1444 st = true ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (t_tbl st)) ->
  (forall R' M', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> mem_wr R_segs M' p 7176 ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
     realizes R_segs (zcfg R_segs 128640 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 128580 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS10 LS9 HU TOK Wp Htbl K.
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. open_spure HU. zkeys.
  trip_facts TOK.
  unbox Fwm. pose proof (op_val_range st WK Fw Fwm) as [Rop Rval].
  clear Fwm Flook Fcont LOWR DROPR Hprom HtyC HtyD Hlf Hcf Hwf HCr HTr.
  assert (Ehb : tr_hb st = t_len st - t_drop st) by reflexivity.
  assert (Hhb : 0 <= tr_hb st <= 15) by lia.
  assert (Hhd : 0 <= tr_hd st <= t_huff st).
  { unfold tr_hd. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (t_drop st) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PF.
  pose proof (pow2_le15 (t_curr st - tr_hb st) ltac:(lia)) as PQ.
  assert (EQ : 2 ^ t_curr st = 2 ^ tr_hb st * 2 ^ (t_curr st - tr_hb st)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  zrebase.
  zstep Rfd. zsetreg (tr_hb st) ltac:(rewrite Ehb; symmetry; apply swrap32_small; lia).
  zstep Rfd. zsetreg (- 2 ^ tr_hb st) ltac:(symmetry; apply sllw_m1; lia).
  zstep Rfd. zsetreg (tr_hd st) ltac:(unfold tr_hd; symmetry; apply srlw_small; lia).
  zstep Rfd. zsetreg (tr_hd st - 2 ^ tr_hb st) ltac:(lia).
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (fill_loop_s (Z.to_nat (2 ^ (t_curr st - tr_hb st))) (2 ^ t_curr st) (t_tbl st) (2 ^ t_curr st) st Rx [] M MD T) end.
  all: try kauto.
  - rewrite Z2Nat.id by lia. exact EQ.
  - lia.
  - rewrite Z2Nat.id by lia. apply Z.pow_le_mono_r; lia.
  - lia.
  - intros R' M'. intros. eapply K; try eassumption.
    unfold tr_tbl1. rewrite it_fill_eq. unfold tr_incr, tr_fill. rewrite !shl32_1 by lia. assumption.
Qed.

Lemma incr_loop_s : forall m c n st Rb l M MD T,
  0 <= c < 2 ^ Z.of_nat m -> Z.of_nat m < n -> c < 65536 ->
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> zget_l Rb l kS8 = tr_hb st ->
  zget_l Rb l kS6 = c -> 0 <= t_huff st < 65536 ->
  (forall R', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     zget_l R' [] kS9 = loopZ n (incr_body (t_huff st)) c ->
     realizes R_segs (zcfg R_segs 128668 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 128648 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  induction m as [|m IH]; intros c n st Rb l M MD T Hc Hn Hc2 Hh HC HS LS8 LS6 Hhuff K.
  -
    cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hc. assert (E : c = 0) by lia. rewrite E in *. clear E Hc Hc2.
    pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf.
    zrebase. zstep Rfd. zstep Rfd. zsetreg 0 ltac:(rewrite Z.land_0_l; reflexivity).
    zstep Rfd. zsetreg 0 ltac:(reflexivity). zstep Rfd. zsetreg 0 ltac:(reflexivity).
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto. zregv. symmetry. apply incr_last; [lia | apply Z.land_0_r].
  - pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf.
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
      all: try kauto. zregv. symmetry. apply incr_last; [lia | rewrite Z.land_comm; exact Z0].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (Z.shiftr c 1) (n - 1) st Rx [] M MD T) end.
      all: try kauto. all: try lia.
      intros R' HC' HS' L8 L9. eapply K; try eassumption. rewrite incr_more; [exact L9 | lia | rewrite Z.land_comm; exact NZ].
Qed.

Ltac close_cmem := unfold cmem; split_conj; assumption.
Ltac close_smem := unfold smem; split_conj; assumption.
Ltac close_sregs1 EL := unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.

Definition Kst1 (pc : Z) (brk : bool) (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregsN R' [] -> sregs (tr_st1 X st) R' [] -> zget_l R' [] kS8 = tr_hb st ->
    mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> cmem M' -> smem (tr_st1 X st) M' ->
    tr_brk X st = brk ->
    realizes R_segs (zcfg R_segs pc (zupd R' []) M' MD) T.

Lemma count_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> zget_l Rb l kS8 = tr_hb st ->
  cmem M -> spure st -> it_trip_ok X 288 320 1444 st = true ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get (t_count st)) ->
  mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
  Kst1 128768 false st M MD T -> Kst1 128960 true st M MD T ->
  realizes R_segs (zcfg R_segs 128640 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS8 HM HU TOK Hcnt Htbl KS KB.
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. open_cmem HM. open_spure HU. zkeys. xaddr.
  trip_facts TOK. clear Fcont Fwm Hprom HtyC HtyD Hcf Hwf DROPR.
  pose proof work1_range as HWr.
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL.
  zrebase.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ (t_len st - 1)) ltac:(symmetry; apply sllw_1; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (incr_loop_s (Z.to_nat (t_len st)) (2 ^ (t_len st - 1)) 32 st Rx [] M MD T) end.
  all: try kauto.
  { rewrite Z2Nat.id by lia. split; [lia|]. apply Z.pow_lt_mono_r; lia. }
  { lia. }
  { assert (2 ^ (t_len st - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  clear HST HAG. clear_regs. intros R1 HC HS L8 L9.
  assert (EI : loopZ 32 (incr_body (t_huff st)) (2 ^ (t_len st - 1)) = tr_incr2 st).
  { unfold tr_incr2. rewrite it_incr_back_eq, shl32_1 by lia. reflexivity. }
  pose proof (incr_range (t_huff st) 32 (2 ^ (t_len st - 1)) ltac:(lia)) as IR.
  rewrite EI in L9, IR. clear EI.
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
  pose proof mx15 as MXR.
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  open_cregs HC. open_sregs HS. zkeys. zrebase.
  zstep Rfd. zsetreg (Z.b2z (tr_incr2 st =? 0))
    ltac:(rewrite (Z.mod_small (tr_incr2 st)) by lia; destruct (Z.eqb_spec (tr_incr2 st) 0); destruct (Z.ltb_spec (tr_incr2 st) 1); cbn [Z.b2z]; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 * t_len st) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd. zsetreg v1 ltac:(unfold v1; symmetry; apply swrap32_small; lia).
  zstep Rfd.
  tstep Rfd.
  fold c0. set (c0s := bv_swrap 16 c0) in *.
  pose proof (swrap16_cases c0 HC0) as HS16. fold c0s in HS16.
  assert (HSR : -32768 <= c0s <= c0) by (destruct HS16; lia). box HS16.
  zstep Rfd. zsetreg (-281474976710656) ltac:(reflexivity).
  zstep Rfd.
  zstep Rfd. zsetreg (tr_huff st) ltac:(exact EH).
  zstep Rfd.
  zstep Rfd. zsetreg ((c0s + -1) * 281474976710656) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 48) with 281474976710656; lia).
  zstep Rfd. zsetreg (tr_sym st) ltac:(unfold tr_sym; apply wrap32_small; lia).
  zstep Rfd.
  time tstore_arr Rfd Hcnt (t_len st).
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
  destruct (Z.eq_dec c0 1) as [C1|NC1].
  - assert (C1s : c0s = 1) by (unbox HS16; destruct HS16; lia).
    zbr Rfd false.
    assert (EC0 : tr_c st = 0) by (rewrite EC, C1; reflexivity).
    destruct (Z.eq_dec (t_len st) mx) as [LM|NLM].
    + zbr Rfd true.
      assert (EL : tr_len X st = t_len st).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [reflexivity | lia]. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB Rx Mx) end.
      all: try kauto.
      * close_sregs1 EL.
      * close_cmem.
      * unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_eq. exact LM.
    + zbr Rfd false.
      unbox Flook. destruct (Flook EC0 NLM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. rewrite <- ESY in W1, W2, W3, W4.
      zstep Rfd. zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).
      zstep Rfd.
      tstep Rfd.
      zstep Rfd. zsetreg (2 * arr_get work1Ar (tr_sym st)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep Rfd.
      tstep Rfd.
      assert (EL : tr_len X st = lf (lens_ofs + arr_get work1Ar (tr_sym st))).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [lia|].
        cbn [andb negb]. rewrite WK. apply lensA_get. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
      all: try kauto.
      * close_sregs1 EL.
      * close_cmem.
      * unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
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
    all: try kauto.
    * close_sregs1 EL.
    * close_cmem.
    * unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    * unfold tr_brk. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
Qed.
End S7IT3.

End FXG.
Ltac open_pregs6 H := unfold pregs6 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in destruct H as (a & b & c & e & g & h & i).
Ltac close_pregs6 := unfold pregs6; split_conj; zreg.
Ltac open_cregs H :=
  unfold cregsN in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  destruct H as (hp & a & b & c & d & e & f & g & h & i); open_pregs6 hp.
Ltac open_sregs H :=
  unfold sregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let c := fresh "LA6" in let d := fresh "LT5" in
  let e := fresh "LS1" in let f := fresh "LS0" in let g := fresh "LT2" in let h := fresh "LS7" in
  destruct H as (a & b & c & d & e & f & g & h).
Ltac open_cmem H :=
  unfold cmem in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "HslD" in let g := fresh "HslL" in let h := fresh "Hext" in let i := fresh "Hbase" in
  destruct H as (a & b & c & d & e & f & g & h & i).
Ltac open_smem H :=
  unfold smem in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in destruct H as (a & b).
Ltac open_spure H :=
  unfold spure in H;
  let a := fresh "WK" in let b := fresh "LOWR" in let b2 := fresh "DROPR" in let c := fresh "NX0" in let d := fresh "NX1" in
  let e := fresh "HCr" in let f := fresh "HTr" in let g := fresh "CL" in let h := fresh "TL" in
  destruct H as (a & b & b2 & c & d & e & f & g & h).
Ltac open_cregsB H :=
  unfold cregsB in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  destruct H as (hp & a & b & d & e & f & g & h & i); open_pregs6 hp.
Ltac close_cregsB := unfold cregsB; split_conj; try close_pregs6; zreg.
Ltac close_cregs := unfold cregsN; split_conj; try close_pregs6; zreg.
Ltac close_sregs := unfold sregs; split_conj; zreg.
Ltac close_cmem := unfold cmem; split_conj; assumption.
Ltac close_smem := unfold smem; split_conj; assumption.
Ltac close_sregs1 EL := unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.
Ltac kauto := first
  [ assumption
  | lazymatch goal with
    | |- cregsN _ _ _ _ _ _ _ _ _ _ _ _ => close_cregs
    | |- cregsB _ _ _ _ _ _ _ _ _ _ _ _ => close_cregsB
    | |- sregs _ (tr_st1 _ _) _ _ => fail
    | |- sregs _ _ _ _ => close_sregs
    | |- pregs6 _ _ _ _ _ _ _ _ => close_pregs6
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].
Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain.

Module PIc_mod.
Definition PIc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (st : ItSt) : Prop :=
  ty = CODES -> exists j, 0 <= j < N (lensA lf) lens_ofs codes /\
    IS ty (lensA lf) lens_ofs codes (rootA lf lens_ofs codes bits) nx j st.

Section PI.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
Hypothesis Hc : 0 <= codes <= 288.
Hypothesis Hl : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15.
Hypothesis HtyC' : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (lensA lf) (lens_ofs + s) <= 7.
Hypothesis Hb : 1 <= bits <= 15.
Hypothesis Hmx : 1 <= mxA lf lens_ofs codes.
Hypothesis Hrj : itm_reject ty (mxA lf lens_ofs codes) (it_left_check (cntA lf lens_ofs codes)) = false.

Lemma Hmx' : max (lensA lf) lens_ofs codes <> 0.
Proof. intro H. change (mxA lf lens_ofs codes = 0) in H. lia. Qed.

Lemma pic_complete : ty = CODES -> kraft (lensA lf) lens_ofs codes 15 = 2 ^ 15.
Proof.
  intros Ety. pose proof (left_eq (lensA lf) lens_ofs codes Hc Hl) as LE.
  change (it_left_check (cntA lf lens_ofs codes)) with (it_left_check (count (lensA lf) lens_ofs codes)) in Hrj.
  rewrite LE in Hrj. unfold itm_reject in Hrj.
  destruct (Z.ltb_spec (2 ^ 15) (kraft (lensA lf) lens_ofs codes 15)); [discriminate|].
  rewrite Ety in Hrj. cbn [codetype_eqb orb andb] in Hrj.
  destruct (Z.ltb_spec 0 (2 ^ 15 - kraft (lensA lf) lens_ofs codes 15)); [discriminate | lia].
Qed.

Lemma pic_init : it_not_enough ty (itm_used (rootA lf lens_ofs codes bits)) = false ->
  PIc ty lf lens_ofs codes nx bits
    (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros Hne Ety. pose proof (N_range (lensA lf) lens_ofs codes Hc Hl) as NR.
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  pose proof (CN (lensA lf) lens_ofs codes Hc Hl Hmx) as N1.
  exists 0. split; [lia|].
  assert (HU : itm_used (rootA lf lens_ofs codes bits) = 2 ^ rootA lf lens_ofs codes bits).
  { exact (used_eq (lensA lf) lens_ofs codes bits Hc Hl Hb Hmx'). }
  rewrite HU in Hne.
  exact (IS0' ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) Hc Hl Hb ltac:(rewrite workA_len; lia) Hmx' Hne).
Qed.

Lemma pic_step : forall st st', PIc ty lf lens_ofs codes nx bits st ->
  it_step (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)) st = ItCont st' ->
  PIc ty lf lens_ofs codes nx bits st'.
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros st st' HP Hs Ety. destruct (HP Ety) as (j & Hj & HIS).
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  change (it_step (itm_ctx ty (lensA lf) lens_ofs nx (itm_root bits (max (lensA lf) lens_ofs codes) (min (lensA lf) lens_ofs codes)) (max (lensA lf) lens_ofs codes)) st = ItCont st') in Hs.
  rewrite (ctx_eq ty (lensA lf) lens_ofs codes nx bits Hc Hl Hb Hmx') in Hs.
  pose proof (trip ty (lensA lf) lens_ofs codes Hc Hl Hmx (pic_complete Ety) (rootA lf lens_ofs codes bits)
                (Hroot (lensA lf) lens_ofs codes bits Hc Hl Hb Hmx') nx (fun _ => C19) j st Hj HIS) as TP.
  unfold trip_post in TP. match type of TP with context [it_step ?c st] => assert (Hs2 : it_step c st = ItCont st') by exact Hs; rewrite Hs2 in TP end. destruct TP as (HjN & _ & HIS' & _).
  exists (j + 1). split; [lia | exact HIS'].
Qed.

Lemma pic_w : forall st, PIc ty lf lens_ofs codes nx bits st -> ty = CODES ->
  arr_get (t_work st) (t_sym st) < 20.
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros st HP Ety. destruct (HP Ety) as (j & Hj & HIS).
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  destruct HIS as (Hsym & _ & _ & _ & _ & Hw & _).
  rewrite Hsym, (Hw j Hj). pose proof (LWr (lensA lf) lens_ofs codes Hc j Hj). lia.
Qed.
End PI.
End PIc_mod.

