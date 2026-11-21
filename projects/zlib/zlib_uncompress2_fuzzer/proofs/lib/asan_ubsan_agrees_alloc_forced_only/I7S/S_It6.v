(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import S_It0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require S_It3. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_It3.S_It1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import S_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Section S7IT6.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation PR6 := (pregs6 lens_ofs p pb sp vgp vtp).
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
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Definition pregs3 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp.
Ltac close_pregs3 := unfold pregs3; split_conj; zreg.

Lemma ne_pow : forall k, 1 <= k <= 15 ->
  it_not_enough ty (itm_used k) = match ty with CODES => false | _ => negb (k <=? 9) end.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf.
  intros k Hk. rewrite itm_used_pow2 by lia_std. unfold it_not_enough, ENOUGH_LENS, ENOUGH_DISTS.
  assert (E : forall b : bool, (if b then true else false) = b) by (destruct b; reflexivity).
  destruct ty; [reflexivity| |].
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 9) with 512 in *. lia_std.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 10) with 1024 in *. lia_std.
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 9) with 512 in *. lia_std.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 10) with 1024 in *. lia_std.
Qed.

Lemma init_s : forall Rb l M MD T,
  m_halted MD = None -> PR6 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  zget_l Rb l kA0 = it_match ty -> zget_l Rb l kT3 = EXAn ty p -> zget_l Rb l kT2 = BSAn ty p ->
  1 <= mx -> CM M -> SM st0 M ->
  (forall R', CR R' [] -> SR st0 R' [] -> realizes R_segs (zcfg R_segs 96880 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 96828 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LA2 LT3 LT4 Hmx HM HSM K.
  pose proof C as C'. open_itc C'. open_pregs6 HP. open_cmem HM. zkeys. clear Hprom HtyC HtyD Hpb.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3). pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  zrebase.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (2 ^ rt - 1) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (-1) ltac:(reflexivity).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  - close_cregs.
  - unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low itm_st0]. rewrite itm_used_pow2 by lia.
    unfold lowS. cbn [Z.eqb Pos.eqb]. split_conj; zreg.
Qed.

Ltac kfix := unfold EXAn, BSAn, EXA, BSA; match goal with H : ty = _ |- _ => rewrite H end; cbv iota; kauto.
Lemma ty_cases :
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty p = p + 808 /\ BSA ty p = p + 808 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty p = 67232 /\ BSA ty p = 67170 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty p = 67358 /\ BSA ty p = 67294 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma spure_st0 : 1 <= mx -> SP st0.
Proof using C zc ret sp pb p ty.
  intros Hmx. pose proof C as C'. open_itc C'. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl itm_st0]. split_conj.
  - reflexivity.
  - unfold ZSEP. left. reflexivity.
  - unfold ZSEP. left. reflexivity.
  - lia_std.
  - lia_std.
  - intros j Hj. pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j). lia_std.
  - intros j Hj. rewrite tblA_get. apply Hcf. exact Hj.
  - rewrite cntA_eq. apply cntK_len.
  - unfold tblA. apply arr_len_init.
Qed.

Lemma switch_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt -> 1 <= mx ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> mem_arr 2 R_segs M (p + 808) 288 (arr_get work1Ar) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA -> mem_arr 4 R_segs M (p + 1384) 1444 cf ->
  mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) ->
  mem_arr 2 R_segs M 67170 31 (arr_get lbase_a) -> mem_arr 2 R_segs M 67232 31 (arr_get lext_a) ->
  mem_arr 2 R_segs M 67294 32 (arr_get dbase_a) -> mem_arr 2 R_segs M 67358 32 (arr_get dext_a) ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> mpost R_segs M M' (sp + -184) (sp + -168) 0 0 ->
     CM M' -> SM st0 M' -> SP st0 -> it_not_enough ty (itm_used rt) = false ->
     realizes R_segs (zcfg R_segs 96880 (zupd R' []) M' MD) T) ->
  (forall R' M', PR6 R' [] -> zget_l R' [] kA6 = 1 -> mpost R_segs M M' (sp + -184) (sp + -168) 0 0 ->
     it_not_enough ty (itm_used rt) = true ->
     realizes R_segs (zcfg R_segs 97396 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96672 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde KBODY KFAIL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. xaddr. clear HtyC HtyD.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  pose proof (spure_st0 Hmx) as HSP.
  assert (HSM : forall Mq, mem_arr 2 R_segs Mq (sp + -136) 16 cA -> mem_arr 4 R_segs Mq (p + 1384) 1444 cf -> SM st0 Mq).
  { intros Mq A B. unfold smem. cbn [t_count t_tbl itm_st0]. split; [exact A|].
    eapply mem_arr_ext; [exact B|]. intros j _. symmetry. apply tblA_get. }
  pose proof (ne_pow rt ltac:(lia)) as NE.
  pose proof (mpost_stable R_segs M (sp + -184) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -184) (sp + -168) 0 0) M) by (apply mpost_refl).
  zrebase.
  destruct ty_cases as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
    rewrite E0 in LA0.
  -
    zstep Rfd. zbr Rfd false. zstep Rfd. zbr Rfd false. zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    eapply init_s; try eassumption; try lia.
    all: try kfix.
    all: try kauto.
    all: lazymatch goal with
         | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
         | |- smem _ _ _ _ => apply HSM; assumption
         | |- _ => idtac
         end.
    intros R' HC' HS'. eapply KBODY; try assumption.
    + unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
    + apply HSM; assumption.
    + rewrite NE, Ety. reflexivity.
  -
    zstep Rfd. zbr Rfd false. zstep Rfd. zbr Rfd true. zstep Rfd.
    destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx M) end.
      all: try kauto. all: try exact HAG.
      rewrite NE, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      eapply init_s; try eassumption; try lia.
      all: try kfix.
      all: try kauto.
      all: lazymatch goal with
           | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
           | |- smem _ _ _ _ => apply HSM; assumption
           | |- _ => idtac
           end.
      intros R' HC' HS'. eapply KBODY; try assumption.
      * unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
      * apply HSM; assumption.
      * rewrite NE, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
  -
    zstep Rfd. zbr Rfd true. zstep Rfd. zstep Rfd.
    destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KFAIL Rx Mx) end.
      all: try kauto. all: try exact HAG.
      rewrite NE, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
      eapply init_s; try eassumption; try lia.
      all: try kfix.
      all: try kauto.
      all: lazymatch goal with
           | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
           | |- smem _ _ _ _ => apply HSM; assumption
           | |- _ => idtac
           end.
      intros R' HC' HS'. eapply KBODY; try assumption.
      * unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
      * apply HSM; assumption.
      * rewrite NE, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
Qed.

Lemma entry_write2 : forall M base n f i lo a0 a2,
  mem_arr 4 R_segs M base i f ->
  mem_arr 4 R_segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u16 R_segs M a0 lo -> mem_u16 R_segs M a2 0 ->
  a0 = base + 4 * i -> a2 = a0 + 2 -> 0 <= i < n -> base + 4 * n <= two64 -> 0 <= base -> 0 <= lo < 65536 ->
  mem_arr 4 R_segs M base n (zfupd f i lo).
Proof using.
  intros M base n f i lo a0 a2 H1 H2 Hlo Hhi -> -> Hi Hn Hb Rlo.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  change 4%nat with (2 + 2)%nat. rewrite Z_to_le_bytes_add. unfold mem_u16 in *.
  apply mem_is_app; [exact Hlo | | rewrite two64_eq in *; lia | rewrite !length_Z_to_le_bytes; cbn; rewrite two64_eq in *; lia].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 2) with 2.
  replace (Z.shiftr lo (8 * 2)) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia). exact Hhi.
Qed.

Definition slots (M : mem) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z) : Prop :=
  mem_u64 R_segs M (sp + -8) v1 /\ mem_u64 R_segs M (sp + -16) v8 /\ mem_u64 R_segs M (sp + -24) v9 /\
  mem_u64 R_segs M (sp + -32) v18 /\ mem_u64 R_segs M (sp + -40) v19 /\ mem_u64 R_segs M (sp + -48) v20 /\
  mem_u64 R_segs M (sp + -56) v21 /\ mem_u64 R_segs M (sp + -64) v22 /\ mem_u64 R_segs M (sp + -72) v23 /\
  mem_u64 R_segs M (sp + -80) v24 /\ mem_u64 R_segs M (sp + -88) v25 /\ mem_u64 R_segs M (sp + -96) v26 /\
  mem_u64 R_segs M (sp + -104) v27.

Lemma epilogue_s : forall Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  m_halted MD = None -> zget_l Rb l kSP = sp + -192 -> zget_l Rb l kA6 = v ->
  slots M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> Z.land v1 (-2) = v1 -> 0 <= v1 < two64 ->
  (forall R', zget_l R' [] kA0 = v -> zget_l R' [] kSP = sp -> zget_l R' [] kRA = v1 ->
     zget_l R' [] kS0 = v8 -> zget_l R' [] kS1 = v9 -> zget_l R' [] kS2 = v18 -> zget_l R' [] kS3 = v19 ->
     zget_l R' [] kS4 = v20 -> zget_l R' [] kS5 = v21 -> zget_l R' [] kS6 = v22 -> zget_l R' [] kS7 = v23 ->
     zget_l R' [] kS8 = v24 -> zget_l R' [] kS9 = v25 -> zget_l R' [] kS10 = v26 -> zget_l R' [] kS11 = v27 ->
     zget_l R' [] kGP = zget_l Rb l kGP -> zget_l R' [] kTP = zget_l Rb l kTP ->
     realizes R_segs (zcfg R_segs v1 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 97396 (zupd Rb l) M MD) T.
Proof using C zc ret pb p wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hh LSP LA6 HSL Hev Hv1 K.
  remember (zget_l Rb l kGP) as vgp' eqn:EG. remember (zget_l Rb l kTP) as vtp' eqn:ET. symmetry in EG, ET.
  pose proof C as C'. open_itc C'. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  unfold slots in HSL. dand HSL as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  all: zreg.
Qed.

Lemma setbits_s : forall Rb l M MD T rv,
  m_halted MD = None -> pregs3 Rb l -> zget_l Rb l kA4 = pb -> zget_l Rb l kA7 = rv -> mem_wr R_segs M p 7176 ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpost R_segs M M' pb (pb + 4) 0 0 -> mem_u32 R_segs M' pb rv ->
     realizes R_segs (zcfg R_segs 97396 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97388 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T rv Hh HP LA4 LA7 Wp K.
  pose proof C as C'. open_itc C'. unfold pregs3 in HP. dand HP as (LSP & LGP & LTP). zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15. unfold ZSEP in Hpb.
  pose proof (mpost_stable R_segs M pb (pb + 4) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X pb (pb + 4) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try kauto. all: try close_pregs3. all: exact HAG.
Qed.

Lemma it_room_ge : 128 <= it_room ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std. Qed.

Definition rsT : list (Z * Z) := [(p + 1384, 5776); (p + 160, 8); (pb, 4)].

Lemma break_tail_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kS8 = t_len st - t_drop st ->
  CM M -> SM st M -> SP st ->
  0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st ->
  (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1384) 1444
       (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                 else t_tbl st)) ->
     mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * (nx + t_used st)) -> mem_u32 R_segs M' pb rt ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 2 R_segs M' (p + 808) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 97396 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97336 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS8 HM HSM HP Hhb Hused Hhuff Hfit K.
  pose proof C as C'. open_itc C'. open_cmem HM. open_smem HSM. open_spure HP. zkeys. xaddr.
  clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15 LOWR DROPR.
  assert (J80 : forall RJ MJ, CRB RJ [] -> zget_l RJ [] kT5 = t_used st ->
            mpost R_segs M MJ (p + 1384) (p + 7160) 0 0 ->
            mem_arr 4 R_segs MJ (p + 1384) 1444
              (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                        else t_tbl st)) ->
            mem_wr R_segs MJ (sp - 192) 192 -> mem_wr R_segs MJ p 7176 ->
            mem_arr 2 R_segs MJ (p + 168) 320 lf -> mem_arr 2 R_segs MJ (p + 808) 288 (arr_get work1Ar) ->
            mem_u64 R_segs MJ (p + 160) (p + 1384 + 4 * nx) ->
            realizes R_segs (zcfg R_segs 97368 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HCJ JT5 HPO HtblJ WfJ WpJ HlensJ HworkJ HnextJ.
    clear Hcnt Htbl Wf Wp Hlens Hwork Hnext HslD HslL Hext Hbase. open_cregsB HCJ. zkeys.
    pose proof (mpost_stable R_segs MJ (p + 160) (p + 168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
    assert (HAG : framed (fun X => mpost R_segs MJ X (p + 160) (p + 168) 0 0) MJ) by (apply mpost_refl).
    zrebase.
    zstep Rfd.
    zstep Rfd. zstep Rfd. zsetreg (4 * t_used st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd. zsetreg (p + 1384 + 4 * (nx + t_used st)) ltac:(lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_s Rx [] Mx MD T rt Hh) end.
    all: try kauto. all: try close_pregs3.
    intros R' M' HP' LA6 HPO2 Hbits'.
    destruct HPO2 as [HA2 HW2].
    eapply K; try eassumption.
    -
      pose proof (framed_mpostL_trans2 R_segs M M MJ rsT _ _ _ _ (mpostL_refl R_segs M rsT) HPO ltac:(left; cbn; left; lia) ltac:(right; lia)) as F1.
      pose proof (framed_mpostL_trans2 R_segs M MJ _ rsT _ _ _ _ F1 HAG ltac:(left; cbn; right; left; lia) ltac:(right; lia)) as F2.
      exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ F2 (conj HA2 HW2) ltac:(left; cbn; right; right; left; lia) ltac:(right; lia)).
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_u64_magree; [exact HA2 | eassumption | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    - apply HW2. assumption.
    - apply HW2. assumption.
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia]. }
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  open_cregs HC. open_sregs HS. zkeys. zrebase.
  destruct (Z.eq_dec (t_huff st) 0) as [H0|HN0].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J80 Rx M) end.
    all: try kauto. all: try assumption.
    rewrite H0. cbn [Z.eqb negb]. exact Htbl.
  - zbr Rfd false.
    specialize (Hfit HN0).
    destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
    zstep Rfd. zstep Rfd. zsetreg (4 * t_huff st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    match goal with
    | Ho : mem_u8 _ ?Mc _ 64, Hb : mem_u8 _ _ _ (t_len st - t_drop st), Hv : mem_u16 _ _ _ 0 |- _ =>
      pose proof (entry_write Mc (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
      clear Ho Hb Hv HT1 HT2
    end.
    apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J80 Rx Mx) end.
    all: try kauto. all: try assumption.
    destruct (Z.eqb_spec (t_huff st) 0); [lia|]. cbn [negb]. exact Htbl.
Qed.

Lemma max0_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> mx = 0 ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) ->
  mem_wr R_segs M (sp - 192) 192 -> mem_arr 2 R_segs M (p + 168) 320 lf -> mem_arr 2 R_segs M (p + 808) 288 wf ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0))) ->
     mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * (nx + 2)) -> mem_u32 R_segs M' pb 1 ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 2 R_segs M' (p + 808) 288 wf ->
     realizes R_segs (zcfg R_segs 97396 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97496 (zupd Rb l) M MD) T.
Proof using C zc ret bits.
  intros Rb l M MD T Hh HP Hmx0 Wp Htbl Hnext Wf Hlens Hwork K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear Hprom HtyC HtyD Hlf Hwf Hlens15.
  pose proof it_room_ge as HRG.
  assert (Htbl' : mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (tblA cf))).
  { eapply mem_arr_ext; [exact Htbl|]. intros j _. symmetry. apply tblA_get. }
  clear Htbl.
  pose proof (mpostL_stable R_segs M rsT ltac:(cbn; unfold ZSEP in Hpb; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X rsT) M) by (apply mpostL_refl).
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (tblA cf)) nx Htbl' ltac:(lia)) as [HT1 HT2]. clear Htbl'.
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2 Mc (p + 1384) 1444 (arr_get (tblA cf)) nx 320 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  destruct (arr4_hole R_segs _ (p + 1384) 1444 _ (nx + 1) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2 Mc (p + 1384) 1444 _ (nx + 1) 320 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_s Rx [] Mx MD T 1 Hh) end.
  all: try kauto. all: try close_pregs3.
  intros R' M' HP' LA6 HPO2 Hbits'. destruct HPO2 as [HA2 HW2].
  eapply K; try eassumption.
  - exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ HAG (conj HA2 HW2) ltac:(left; cbn; right; right; left; lia) ltac:(right; lia)).
  - eapply mem_arr_magree; [exact HA2 | | unfold ZSEP in Hpb; lia | lia].
    change (code_pack 64 1 0) with 320. exact Htbl.
  - eapply mem_u64_magree; [exact HA2 | | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    match goal with H : mem_u64 _ _ (p + 160) ?v |- _ => replace (p + 1384 + 4 * (nx + 2)) with v by lia; exact H end.
  - apply HW2. assumption.
  - apply HW2. assumption.
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
Qed.
End S7IT6.
End FXG.
