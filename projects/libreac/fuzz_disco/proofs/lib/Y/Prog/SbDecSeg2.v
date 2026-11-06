(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 167 of its 196 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacBoxName.v, with its module paths and module names changed; 824 of its 864 lines of code are new or changed and 156 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC81 YC45 YC85 YCkd YC1i YCjr YCbf YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition qx (x : sv) : sv :=
  SAlu ALU_ADD (SAlu ALU_SRA (SMd M_MUL x (SLit 1717986919)) (SLit 34))
    (SAlu ALU_SRL (SMd M_MUL x (SLit 1717986919)) (SLit 63)).
Definition dx (x y : sv) : sv := SAlu ALU_ADD (SAlu ALU_SUB x (SMd M_MUL (qx y) (SLit 10))) (SLit 48).
Lemma sd2_mul_div : forall v, 0 <= v < 2 ^ 31 -> v * 1717986919 / 2 ^ 34 = v / 10.
Proof.
intros v Hv. pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as Hm. pose proof (Z.div_mod v 10 ltac:(lia)) as Hd.
symmetry. apply Z.div_unique_pos with (6 * (v / 10) + (v mod 10) * 1717986919); lia.
Qed.
Lemma U_qx : forall E x v, U E x = v -> 0 <= v < 2 ^ 31 -> U E (qx x) = v / 10.
Proof.
intros E x v Hx Hv. unfold qx. rewrite !U_SAlu, !U_SMd, !U_SLit, Hx. cbn [zalu_raw zmd_raw].
change (Z.land (zcanon 34) 63) with 34. change (Z.land (zcanon 63) 63) with 63.
change (zcanon 1717986919) with 1717986919.
assert (Hm : zcanon (v * 1717986919) = v * 1717986919) by (apply zcanon_id; unfold M64; lia).
rewrite Hm.
assert (Hs : bv_swrap 64 (v * 1717986919) = v * 1717986919).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia. lia. }
rewrite Hs, !Z.shiftr_div_pow2 by lia. rewrite sd2_mul_div by exact Hv.
rewrite (Z.div_small (v * 1717986919) (2 ^ 63)) by lia.
pose proof (Z.div_pos v 10 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound v 10 v ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (v / 10)) by (unfold M64; lia). rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_dx : forall E x y v, U E x = v -> U E y = v -> 0 <= v < 2 ^ 31 -> U E (dx x y) = 48 + v mod 10.
Proof.
intros E x y v Hx Hy Hv. unfold dx. rewrite !U_SAlu, U_SMd, (U_qx E y v Hy Hv), Hx, !U_SLit. cbn [zalu_raw zmd_raw].
pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as Hm. pose proof (Z.div_mod v 10 ltac:(lia)) as Hd.
pose proof (Z.div_pos v 10 ltac:(lia) ltac:(lia)).
change (zcanon 10) with 10. change (zcanon 48) with 48.
rewrite (zcanon_id (v / 10 * 10)) by (unfold M64; lia).
rewrite (zcanon_id (v - v / 10 * 10)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_add_lit : forall E x c, U E (SAlu ALU_ADD x (SLit c)) = zcanon (U E x + c).
Proof. intros. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. unfold zcanon. rewrite Z.add_mod_idemp_r by (unfold M64; lia). reflexivity. Qed.
Lemma sd2_br_lt10 : forall E e v, U E e = zcanon (v - 10) -> 0 <= v < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SLit 18446744073709551596)) (sv_denot E e) = (v <? 10).
Proof.
intros E e v He Hv. rewrite branch_ltu_U, U_SLit, He. unfold zcanon, M64.
destruct (Z.ltb_spec v 10) as [Hl | Hl]; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.
Lemma sd2_lsd1 : forall v, 0 <= v < 10 -> sb_dec_c.sb_dec_lsd v 3 = [48 + v].
Proof. intros v Hv. cbn [sb_dec_c.sb_dec_lsd]. rewrite Z.mod_small by lia. destruct (Z.ltb_spec v 10); [reflexivity | lia]. Qed.
Lemma sd2_lsd2 : forall v, 10 <= v < 100 -> sb_dec_c.sb_dec_lsd v 3 = [48 + v mod 10; 48 + v / 10].
Proof.
intros v Hv. cbn [sb_dec_c.sb_dec_lsd]. destruct (Z.ltb_spec v 10); [lia|]. destruct (Z.ltb_spec (v / 10) 10); [|lia].
rewrite (Z.mod_small (v / 10)) by lia. reflexivity.
Qed.
Lemma sd2_lsd3 : forall v, 100 <= v -> sb_dec_c.sb_dec_lsd v 3 = [48 + v mod 10; 48 + (v / 10) mod 10; 48 + (v / 10 / 10) mod 10].
Proof.
intros v Hv. cbn [sb_dec_c.sb_dec_lsd]. destruct (Z.ltb_spec v 10); [lia|]. destruct (Z.ltb_spec (v / 10) 10); [lia|].
destruct (v / 10 / 10 <? 10); reflexivity.
Qed.
Lemma sd2_rD : forall v md, rev (sb_dec_c.sb_dec_D v md) =
  (if Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3)) <? md then sb_dec_c.sb_dec_lsd v 3 ++ [48] else sb_dec_c.sb_dec_lsd v 3).
Proof. intros. unfold sb_dec_c.sb_dec_D. apply rev_involutive. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition sd2_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 24 32 24 32 [];
    YP09.mkRegion (Some 10%nat) 0 40 0 40 [];
    YP09.mkRegion (Some 32%nat) 0 8 0 8 [] ].
Definition sd2_facts : facts :=
  mkFacts [ (10%nat, HPTR 6); (20%nat, mkAF 1 2 0); (21%nat, mkAF 0 2147483647 0);
            (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 17592184995840) 3) ] []
    [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 22 0), SOff 32 0) ].
Definition ss_sd2 : sstate := mkSS (AF_both3_sb_dec + 0x74) sr_atoms sd2_regions None sd2_facts.
Definition sd2_extra (X : sbd_in) (pos : Z) : list word := [Z_to_bv 64 (sbd_SH X pos)].
Definition ESD2 (X : sbd_in) (pos : Z) (regs1 : bvmap 5 word) : env := Eimg (Ereg regs1 (sd2_extra X pos)).
Definition sd2_W (X : sbd_in) (pos a : Z) : Prop :=
  sbd_S1 X + 24 <= a < sbd_S1 X + 32 \/ sbd_F X pos <= a < sbd_F X pos + 40 \/ sbd_SH X pos <= a < sbd_SH X pos + 8.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma sd2_S1 : forall X, sbd_SP X mod 16 = 0 -> sbd_SP X - 160 < sbd_S1 X <= sbd_SP X - 128 /\ sbd_S1 X mod 32 = 0.
Proof.
intros X H. unfold sbd_S1. pose proof (Z.div_mod (sbd_SP X - 128) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sbd_SP X - 128) 32 ltac:(lia)).
split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma sd2_lyF : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 -> frame_addr lyc1 0 pos = sbd_F X pos /\
  (forall cid p, frame_addr lyc1 cid p = frame_addr (si_lyc X) cid p).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM.
destruct HX as ((_ & Hly1 & _) & _). destruct HM as ((_ & Hly2 & _) & _).
destruct Hly1 as (_ & _ & _ & _ & _ & E1 & _). destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _).
assert (EF : forall cid p, frame_addr lyc1 cid p = frame_addr (si_lyc X) cid p) by (intros; unfold frame_addr; rewrite E1, E2; reflexivity).
split; [unfold sbd_F; apply EF | exact EF].
Qed.
Lemma sd2_Ffacts : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 ->
  4096 <= sbd_F X pos /\ sbd_F X pos + 64 <= alloc_ceiling /\ in_app (sbd_F X pos) 64 /\ sbd_F X pos mod 64 = 0 /\
  sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8 /\
  (forall a, sbd_F X pos <= a < sbd_F X pos + 64 -> apresent (w_H W1) memc1 a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H W1) memc1 (sbd_SH X pos + i)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM.
destruct (sd2_lyF X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & _).
pose proof HM as ((HAR & _) & Hfrs & _).
assert (Hin : In (0, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (H4 & Hc & Ha).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR Hin) as (H64 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR Hin) as (_ & _ & Hp & Hsp).
change (fs_frame_bytes 0) with 64 in *. rewrite EF in *.
split; [lia|]. split; [lia|]. split; [exact Ha|]. split; [exact H64|]. split; [reflexivity|].
split; [intros a Hr; exact (proj1 (Hp a Hr))|].
intros i Hi. exact (proj1 (Hsp i ltac:(change (64 / 8) with 8; lia))).
Qed.
Lemma sd2t_hi : forall SP S1 F SH a,
  alloc_ceiling <= SP - SB_DEC_STK -> SP - 160 < S1 <= SP - 128 -> 0 <= F -> F + 64 <= alloc_ceiling ->
  SH = SHADOW_OFF + F / 8 -> alloc_ceiling <= a < 2 ^ 64 -> ~ (SP - SB_DEC_STK <= a < SP) ->
  0 <= a < 2 ^ 64 /\ ~ (S1 + 24 <= a < S1 + 32 \/ F <= a < F + 40 \/ SH <= a < SH + 8).
Proof.
intros SP S1 F SH a H1 H2 H3 H4 H5 H6 H7. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, SHADOW_OFF in *. split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_app : forall SP S1 F SH a,
  alloc_ceiling <= SP - SB_DEC_STK -> SP - 160 < S1 -> 0 <= F -> F + 64 <= alloc_ceiling ->
  SH = SHADOW_OFF + F / 8 -> app_addr a -> (a < F \/ F + 40 <= a) ->
  0 <= a < 2 ^ 64 /\ ~ (S1 + 24 <= a < S1 + 32 \/ F <= a < F + 40 \/ SH <= a < SH + 8).
Proof.
intros SP S1 F SH a H1 H2 H3 H4 H5 H6 H7. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, SHADOW_OFF, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_img : forall SP S1 F SH a,
  alloc_ceiling <= SP - SB_DEC_STK -> SP - 160 < S1 -> 0 <= F -> SH = SHADOW_OFF + F / 8 ->
  0 <= a < kLowMemEnd -> (a < F \/ F + 40 <= a) ->
  0 <= a < 2 ^ 64 /\ ~ (S1 + 24 <= a < S1 + 32 \/ F <= a < F + 40 \/ SH <= a < SH + 8).
Proof.
intros SP S1 F SH a H1 H2 H3 H4 H5 H6. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, SHADOW_OFF, kLowMemEnd in *. split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_save : forall SP S1 F SH a,
  alloc_ceiling <= SP - SB_DEC_STK -> SP <= 2 ^ 47 -> S1 <= SP - 128 -> 0 <= F -> F + 64 <= alloc_ceiling ->
  SH = SHADOW_OFF + F / 8 -> SP - 96 <= a < SP ->
  0 <= a < 2 ^ 64 /\ ~ (S1 + 24 <= a < S1 + 32 \/ F <= a < F + 40 \/ SH <= a < SH + 8).
Proof.
intros SP S1 F SH a H1 H2 H3 H4 H5 H6 H7. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, SHADOW_OFF in *. split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_sha : forall SP S1 F SH x,
  alloc_ceiling <= SP - SB_DEC_STK -> SP - 160 < S1 -> in_app F 64 -> F mod 64 = 0 -> SH = SHADOW_OFF + F / 8 ->
  0 <= x < kHighMemEnd -> ~ (F <= x < F + 64) ->
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\
  ~ (S1 + 24 <= SHADOW_OFF + x / 8 < S1 + 32 \/ F <= SHADOW_OFF + x / 8 < F + 40 \/ SH <= SHADOW_OFF + x / 8 < SH + 8).
Proof.
intros SP S1 F SH x H1 H2 H3 H4 H5 H6 H7. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *.
split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_fsh : forall SP S1 F SH fa fs a,
  alloc_ceiling <= SP - SB_DEC_STK -> SP - 160 < S1 -> in_app F 64 -> F mod 64 = 0 -> SH = SHADOW_OFF + F / 8 ->
  0 <= fa -> fa mod 64 = 0 -> 0 <= fs -> fs mod 64 = 0 -> fa + fs <= alloc_ceiling -> (F + 64 <= fa \/ fa + fs <= F) ->
  shadow_addr fa <= a < shadow_addr fa + fs / 8 ->
  0 <= a < 2 ^ 64 /\ ~ (S1 + 24 <= a < S1 + 32 \/ F <= a < F + 40 \/ SH <= a < SH + 8).
Proof.
intros SP S1 F SH fa fs a H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_rec : forall SP S1 F SH A n a,
  alloc_ceiling <= SP - SB_DEC_STK -> SP - 160 < S1 <= SP - 128 -> 0 <= F -> F + 64 <= alloc_ceiling ->
  SH = SHADOW_OFF + F / 8 -> 0 <= A -> (SP <= A \/ A + n <= SP - SB_DEC_STK) -> amem_range A n ->
  A <= a < A + n -> ~ (F <= a < F + 64) ->
  0 <= a < 2 ^ 64 /\ ~ (S1 + 24 <= a < S1 + 32 \/ F <= a < F + 40 \/ SH <= a < SH + 8).
Proof.
intros SP S1 F SH A n a H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. pose proof asan_consts as (C1 & _).
unfold SB_DEC_STK, ESTACK, SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
split; [lia|]. intros [Hw | [Hw | Hw]]; lia.
Qed.
Lemma sd2t_amem : forall A n x, 0 <= A -> amem_range A n -> A <= x < A + n -> 0 <= x < kHighMemEnd.
Proof. intros A n x H1 H2 H3. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. Qed.
Lemma sd2t_nums : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 ->
  alloc_ceiling <= sbd_SP X - SB_DEC_STK /\ sbd_SP X <= 2 ^ 47 /\ sbd_SP X - 160 < sbd_S1 X <= sbd_SP X - 128 /\
  0 <= sbd_F X pos /\ sbd_F X pos + 64 <= alloc_ceiling /\ in_app (sbd_F X pos) 64 /\ sbd_F X pos mod 64 = 0 /\
  sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM.
destruct (sd2_Ffacts X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (F1 & F2 & F3 & F4 & F5 & _).
pose proof HX as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hstk & Hsp0 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & _) & _).
split; [lia|]. split; [lia|]. split; [exact (proj1 (sd2_S1 X Hsp16))|].
split; [lia|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4 | exact F5].
Qed.
Lemma sd2t_awr_notF : forall X pos lyc1 Sc1 W1 memc1 mdc1 a,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 ->
  awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B (si_lyc X) (si_Sc X))
    (si_lyc X) (si_own X) a ->
  ~ (sbd_F X pos <= a < sbd_F X pos + 64).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM Hw.
destruct (sd2_lyF X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & EF2).
destruct (sd2_Ffacts X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (F1 & F2 & F3 & F4 & F5 & _).
pose proof HX as (HJc & _).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrc & _).
pose proof HM as ((HAR & _) & Hfrs & Hab & _).
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc Hw)
  as (_ & [[Hc _] | [(_ & b & n & Hb & Hr & _) | (cid & p & Hown & [[_ Hr] | [Hsh _]])]]).
- lia.
- rewrite <- Hab in Hb.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b n 0 pos HAR Hb Hin0) as Hd.
  rewrite EF in Hd. change (fs_frame_bytes 0) with 64 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hinc : In (cid, p) (frames (si_Sc X))) by (rewrite Hfrc; apply in_or_app; left; exact Hown).
  apply in_split in Hinc as (l2 & l3 & E).
  assert (Hd : zdisjoint (frame_rng lyc1 (0, pos)) (frame_rng lyc1 (cid, p))).
  { apply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (0, pos) (cid, p) [] l2 l3 HAR). rewrite Hfrs, E. reflexivity. }
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. rewrite EF2 in Hd.
  change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3. unfold kLowMemEnd, kHighShadowEnd in Hsh. lia.
Qed.
Lemma sd2t_imgW : forall X pos lyc1 Sc1 W1 memc1 mdc1 a,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 -> in_img SEGS a ->
  0 <= a < 2 ^ 64 /\ ~ sd2_W X pos a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM Hia.
pose proof (sd2t_nums X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
destruct (sd2_lyF X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & _).
pose proof HM as ((HAR & _) & Hfrs & _).
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof (pa_segs_low a Hia) as Hlow.
assert (HnF : a < sbd_F X pos \/ sbd_F X pos + 40 <= a).
{ destruct (Z.lt_ge_cases a (sbd_F X pos)) as [Hl | Hl]; [left; exact Hl | right].
  destruct (Z.lt_ge_cases a (sbd_F X pos + 64)) as [Hu | Hu]; [|lia].
  exfalso. apply (frm_img SEGS B LAWS _ _ _ _ _ 0 pos a HAR Hin0); [rewrite EF; change (fs_frame_bytes 0) with 64; lia | exact Hia]. }
exact (sd2t_img (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) a N1 (proj1 N3) N4 N8 Hlow HnF).
Qed.
Lemma sd2t_blkW : forall X pos lyc1 Sc1 W1 memc1 mdc1 b m j,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 -> In (b, m) (ablocks B (si_lyc X) (si_Sc X)) ->
  0 <= j < req_size m -> 0 <= b + j < 2 ^ 64 /\ ~ sd2_W X pos (b + j).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 b m j HX HM Hb Hj.
pose proof (sd2t_nums X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
destruct (sd2_lyF X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & _).
pose proof HM as ((HAR & _) & Hfrs & Hab & _).
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
rewrite <- Hab in Hb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4 & Hbc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 0 pos HAR Hb Hin0) as Hd.
rewrite EF in Hd. change (fs_frame_bytes 0) with 64 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
unfold sd2_W.
apply (sd2t_app (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) (b + j) N1 (proj1 N3) N4 N5 N8
  (in_app_addr b (req_size m) (b + j) Happ ltac:(lia))).
lia.
Qed.
Lemma sd2t_frmW : forall X pos lyc1 Sc1 W1 memc1 mdc1 cid p a,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 -> In (cid, p) (frames (si_Sc X)) ->
  (in_zr a (frame_rng (si_lyc X) (cid, p)) \/
   in_zr a (shadow_addr (frame_addr (si_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  0 <= a < 2 ^ 64 /\ ~ sd2_W X pos a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 cid p a HX HM Hcp Hz.
pose proof (sd2t_nums X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
destruct (sd2_lyF X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & EF2).
pose proof HM as ((HAR & _) & Hfrs & _).
assert (Hin : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR Hin) as (Hf4 & Hfc & Hfa).
destruct (frame_al64 SEGS B _ _ _ _ _ cid p HAR Hin) as (Ha64 & Hs64 & H64).
apply in_split in Hcp as (l2 & l3 & E).
assert (Hd : zdisjoint (frame_rng lyc1 (0, pos)) (frame_rng lyc1 (cid, p))).
{ apply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (0, pos) (cid, p) [] l2 l3 HAR). rewrite Hfrs, E. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 0) with 64 in Hd.
rewrite EF2 in Hd, Hf4, Hfc, Hfa, Ha64.
unfold sd2_W.
destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng in Hz; cbn [fst snd] in Hz.
- apply (sd2t_app (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) a N1 (proj1 N3) N4 N5 N8
    (in_app_addr _ _ a Hfa Hz)). lia.
- exact (sd2t_fsh (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) (frame_addr (si_lyc X) cid p) (fs_frame_bytes cid) a
    N1 (proj1 N3) N6 N7 N8 ltac:(lia) Ha64 (fs_frame_bytes_nonneg cid) Hs64 Hfc Hd Hz).
Qed.
Lemma sd2t_frame : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  sbd_frame X (mrestrict (w_H W1) mem2).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 HX HM HK.
pose proof (sd2t_nums X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof HM as (_ & _ & _ & _ & _ & Hfr & _).
unfold sbd_frame in Hfr |- *. intros j r Hj.
assert (Hj12 : (j < length sbd_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length sbd_saved_regs) with 12%nat in Hj12.
apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact (Hfr j r Hj)].
intros k Hk. change (Z.of_nat 8) with 8 in Hk.
destruct (sd2t_save (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) (sbd_SP X - 8 - 8 * Z.of_nat j + k)
  N1 N2 (proj2 N3) N4 N5 N8 ltac:(lia)) as (Hr64 & HnW).
exact (HK _ Hr64 HnW).
Qed.
Lemma sd2t_rng : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2 q n own1,
  sbd_cx B X -> sbd_mid0 B X pos lyc1 Sc1 W1 memc1 mdc1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) mem2) ->
  0 <= q -> amem_range q n -> (forall a, q <= a < q + n -> ~ (sbd_F X pos <= a < sbd_F X pos + 64)) ->
  range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF q n ->
  shadow_hull_vis (aview SEGS (w_H W1) memc1) q n ->
  (forall a, q <= a < q + n ->
     awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B lyc1 Sc1) lyc1 own1 a /\
     apresent (w_H W1) memc1 a) ->
  range_addressable (aview SEGS (w_H W1) mem2) SHADOW_OFF q n /\
  shadow_hull_vis (aview SEGS (w_H W1) mem2) q n /\
  (forall a, q <= a < q + n ->
     awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B lyc1 Sc1) lyc1 own1 a /\
     apresent (w_H W1) mem2 a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 q n own1 HX HM HK HG Hq Hqm Hnf Hra Hhull Hbytes.
pose proof (sd2t_nums X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
split.
{ intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in Hs |- *.
  destruct (sd2t_sha (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) x N1 (proj1 N3) N6 N7 N8
    (sd2t_amem q n x Hq Hqm Hx) (Hnf x Hx)) as (Hr64 & HnW).
  rewrite (HK _ Hr64 HnW). exact Hs. }
split.
{ intros s Hs. exact (aview_keeps_vis SEGS _ _ _ _ HG (Hhull s Hs)). }
intros a Ha. destruct (Hbytes a Ha) as (Hw & Hp). split; [exact Hw | exact (apresent_grows _ _ _ _ HG Hp)].
Qed.
Lemma sd2_mid0_kept : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 mem2 md2,
  sbd_cx B X -> sbd_stA B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W1 mem2 md2 (si_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) mem2) ->
  sbd_mid0 B X pos lyc1 Sc1 W1 mem2 md2 /\ sbd_rec X W1 mem2 0.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 mem2 md2 HX HA HJ HK HG.
destruct HA as (HM & HR & _).
pose proof (sd2t_nums X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof HM as (_ & Hfrs & Hab & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & _ & Hfl & (Hra & Hhull & Hbytes) & HoutP).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HA0 & _ & _ & HAm & _ & HAsp & _ & _ & Hn0
  & _ & _ & _ & (_ & _ & Hbc) & Houtc).
assert (Hrnw : forall a, si_A X <= a < si_A X + 28 -> 0 <= a < 2 ^ 64 /\ ~ sd2_W X pos a).
{ intros a Ha.
  exact (sd2t_rec (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) (si_A X) 28 a N1 N3 N4 N5 N8 ltac:(lia) HAsp HAm Ha
    (sd2t_awr_notF X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM (proj1 (Hbc a Ha)))). }
split.
- unfold sbd_mid0. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hab|].
  split.
  { intros a Hro0 Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    destruct (sd2t_imgW X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM Hia) as (Hr64 & HnW).
    rewrite (HK a Hr64 HnW). exact (Hro a Hro0 Ho He). }
  split.
  { unfold sbd_kept. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha Hn He.
      destruct (sd2t_hi (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) a N1 N3 N4 N5 N8 Ha Hn) as (Hr64 & HnW).
      rewrite (HK a Hr64 HnW). exact (K1 a Ha Hn He).
    + intros b m j Hb Hj He.
      destruct (sd2t_blkW X pos lyc1 Sc1 W1 memc1 mdc1 b m j HX HM Hb Hj) as (Hr64 & HnW).
      rewrite (HK _ Hr64 HnW). exact (K2 b m j Hb Hj He).
    + intros a Hia Ho He.
      destruct (sd2t_imgW X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM Hia) as (Hr64 & HnW).
      rewrite (HK a Hr64 HnW). exact (K3 a Hia Ho He).
    + intros cid p a Hcp Hz He.
      destruct (sd2t_frmW X pos lyc1 Sc1 W1 memc1 mdc1 cid p a HX HM Hcp Hz) as (Hr64 & HnW).
      rewrite (HK a Hr64 HnW). exact (K4 cid p a Hcp Hz He).
    + intros a Ha Hn Hp. exact (apresent_grows _ _ _ _ HG (K5 a Ha Hn Hp)).
    + intros a Ha. exact (apresent_grows _ _ _ _ HG (K6 a Ha)). }
  split; [exact (sd2t_frame X pos lyc1 Sc1 W1 memc1 mdc1 mem2 HX HM HK)|].
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact Hfl].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (sd2t_app (sbd_SP X) (sbd_S1 X) (sbd_F X pos) (sbd_SH X pos) (sbd_F X pos + 56 + k) N1 (proj1 N3) N4 N5 N8
      (in_app_addr (sbd_F X pos) 64 (sbd_F X pos + 56 + k) N6 ltac:(lia)) ltac:(lia)) as (Hr64 & HnW).
    exact (HK _ Hr64 HnW). }
  split.
  { exact (sd2t_rng X pos lyc1 Sc1 W1 memc1 mdc1 mem2 (si_A X) 28 _ HX HM HK HG ltac:(lia) HAm
      (fun a Ha => sd2t_awr_notF X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM (proj1 (Hbc a Ha))) Hra Hhull Hbytes). }
  intros Hroom. destruct (HoutP Hroom) as (Hra2 & Hhull2 & Hbytes2).
  destruct (Houtc Hroom) as (Hp0 & _ & Hpm & _ & _ & _ & (_ & _ & Hbc2)).
  exact (sd2t_rng X pos lyc1 Sc1 W1 memc1 mdc1 mem2 (si_p X + si_n X) (sbd_acc X) _ HX HM HK HG ltac:(lia) Hpm
    (fun a Ha => sd2t_awr_notF X pos lyc1 Sc1 W1 memc1 mdc1 a HX HM (proj1 (Hbc2 a Ha))) Hra2 Hhull2 Hbytes2).
- destruct HR as (R1 & R2 & R3 & R4 & R5). unfold sbd_rec.
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact R1].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Hrnw (si_A X + k) ltac:(lia)) as (Hr64 & HnW). exact (HK _ Hr64 HnW). }
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact R2].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Hrnw (si_A X + 8 + k) ltac:(lia)) as (Hr64 & HnW). exact (HK _ Hr64 HnW). }
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact R3].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Hrnw (si_A X + 16 + k) ltac:(lia)) as (Hr64 & HnW). exact (HK _ Hr64 HnW). }
  split.
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact R4].
    intros k Hk. change (Z.of_nat 4) with 4 in Hk.
    destruct (Hrnw (si_A X + 24 + k) ltac:(lia)) as (Hr64 & HnW). exact (HK _ Hr64 HnW). }
  intros Hroom. rewrite Z.min_l by lia. exact (garr8_nil SEGS _ _).
Qed.
Lemma sd2_entry : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  sbd_cx B X -> sbd_stA B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  st_ok_pi (fx := si_fq X) SEGS VAL (ESD2 X pos regs1) ss_sd2
    (restrict (w_H W1) (mkst (fx := si_fq X) regs1 (Z_to_bv 64 (BASE + (AF_both3_sb_dec + 0x74))) memc1 (seg_rom SEGS))).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA.
pose proof HA as (HM & _ & G2 & G3 & G4 & G8 & G9 & G10 & G19 & G20 & G21 & G22 & G27).
destruct (sd2_Ffacts X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (HF4 & HFc & HFapp & HF64 & HSH & HFp & HSp).
pose proof HM as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _) & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSP16 & Hbud & HSPle & _ & Hv & Hmd & _).
destruct (sd2_S1 X HSP16) as (HS1r & HS1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity.
set (F := sbd_F X pos) in *. set (SH := sbd_SH X pos) in *. set (S1 := sbd_S1 X) in *.
set (E := ESD2 X pos regs1).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ESD2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 S1) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (E20 : ew E 20 = Z_to_bv 64 (si_md X)) by (rewrite (EE 20%nat 20%bv eq_refl); exact G20).
assert (E21 : ew E 21 = Z_to_bv 64 (si_v X)) by (rewrite (EE 21%nat 21%bv eq_refl); exact G21).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact G22).
assert (E32 : ew E 32 = Z_to_bv 64 SH)
  by (subst E; unfold ESD2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (HF8 : F / 8 mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)). replace F with (8 * (8 * (F / 64))) by lia.
  rewrite Z.mul_comm, Z.div_mul by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
assert (HF8r : 512 <= F / 8 <= 17592184995840).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
assert (HSHr : 2147451392 <= SH <= 2147450880 + 17592184995840) by (rewrite HSH; unfold SHADOW_OFF; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv0. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv0. }
assert (Ha9 : base_val E (Some 9%nat) = S1) by (apply VB; [exact E9 | lia]).
assert (Ha10 : base_val E (Some 10%nat) = F) by (apply VB; [exact E10 | lia]).
assert (Ha32 : base_val E (Some 32%nat) = SH) by (apply VB; [exact E32 | rewrite HSH; unfold SHADOW_OFF; lia]).
rewrite restrict_mkst_fx. unfold ss_sd2. apply pa_entry_st_ok_full.
- subst E. unfold ESD2. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sd2_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite Ha9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite Ha10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HFp. lia.
  + rewrite Ha32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HSp. lia.
- apply pairwise_disjoint_of_extents. unfold sd2_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Ha9, Ha10, Ha32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  repeat split; lia.
- unfold sd2_facts. split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite E10, E20, E21, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end;
    first [lia | exact HF64 | rewrite HSH, <- Zplus_mod_idemp_r, HF8; reflexivity].
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply (shadow_decl_ok E 10 22 32 F SHADOW_OFF E10 ltac:(lia) E22). rewrite E32, HSH. reflexivity.
Qed.
Lemma sd2_env : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  sbd_cx B X -> sbd_stA B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ESD2 X pos regs1) n = getr regs1 r) /\
  ew (ESD2 X pos regs1) 10 = Z_to_bv 64 (sbd_F X pos) /\ ew (ESD2 X pos regs1) 20 = Z_to_bv 64 (si_md X) /\
  ew (ESD2 X pos regs1) 21 = Z_to_bv 64 (si_v X) /\ ew (ESD2 X pos regs1) 22 = Z_to_bv 64 SHADOW_OFF /\
  ew (ESD2 X pos regs1) 32 = Z_to_bv 64 (sbd_SH X pos) /\
  base_val (ESD2 X pos regs1) (Some 9%nat) = sbd_S1 X /\ base_val (ESD2 X pos regs1) (Some 10%nat) = sbd_F X pos /\
  base_val (ESD2 X pos regs1) (Some 32%nat) = sbd_SH X pos.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA.
pose proof HA as (HM & _ & G2 & G3 & G4 & G8 & G9 & G10 & G19 & G20 & G21 & G22 & G27).
destruct (sd2_Ffacts X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (HF4 & HFc & HFapp & HF64 & HSH & HFp & HSp).
pose proof HM as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _) & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSP16 & Hbud & HSPle & _).
destruct (sd2_S1 X HSP16) as (HS1r & HS1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4256) by reflexivity.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ESD2 X pos regs1) n = getr regs1 r)
  by (intros n r Hn; unfold ESD2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew (ESD2 X pos regs1) 9 = Z_to_bv 64 (sbd_S1 X)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (E10 : ew (ESD2 X pos regs1) 10 = Z_to_bv 64 (sbd_F X pos)) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (E32 : ew (ESD2 X pos regs1) 32 = Z_to_bv 64 (sbd_SH X pos))
  by (unfold ESD2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (HF8r : 512 <= sbd_F X pos / 8 <= 17592184995840).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
split; [exact EE|]. split; [exact E10|].
split; [rewrite (EE 20%nat 20%bv eq_refl); exact G20|]. split; [rewrite (EE 21%nat 21%bv eq_refl); exact G21|].
split; [rewrite (EE 22%nat 22%bv eq_refl); exact G22|]. split; [exact E32|].
cbn [base_val]. rewrite E9, E10, E32, !unsigned_lit_small by (rewrite ?HSH; unfold SHADOW_OFF; lia).
split; [reflexivity|]. split; reflexivity.
Qed.
Definition sd2_rs (cs1 cs2 cs3 : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some 9%nat) 24 32 24 32 cs1; YP09.mkRegion (Some 10%nat) 0 40 0 40 cs2;
   YP09.mkRegion (Some 32%nat) 0 8 0 8 cs3].
Lemma sd2_awr : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 cs1 cs2 cs3,
  sbd_cx B X -> sbd_stA B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  awr_ok (ESD2 X pos regs1) (sd2_rs cs1 cs2 cs3)
    (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X)) (ablocks B lyc1 Sc1) lyc1 ((0, pos) :: si_own X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 cs1 cs2 cs3 HX HA.
destruct (sd2_env X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA) as (_ & _ & _ & _ & _ & _ & B9 & B10 & B32).
pose proof HA as (HM & _).
destruct (sd2_lyF X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (EF & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSP16 & Hbud & HSPle & _).
destruct (sd2_S1 X HSP16) as (HS1r & HS1al).
assert (WS : SB_DEC_STK = 4256) by reflexivity.
intros a (r & Hin & Ha). unfold sd2_rs in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
- rewrite B9 in Ha. left. lia.
- rewrite B10 in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
- rewrite B32 in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8. unfold sbd_SH in Ha. lia.
Qed.
Lemma sd2_acc : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 cs1 cs2 cs3 (m m' : word -> option byte),
  sbd_cx B X -> sbd_stA B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) m a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) m) ->
  frame_of (ESD2 X pos regs1) (sd2_rs cs1 cs2 cs3) (mrestrict (w_H W1) m) (mrestrict (w_H W1) m') ->
  mem_grows (mrestrict (w_H W1) m) (mrestrict (w_H W1) m') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) /\
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) m').
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 cs1 cs2 cs3 m m' HX HA HK HG HF HG2.
destruct (sd2_env X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA) as (_ & _ & _ & _ & _ & _ & B9 & B10 & B32).
split.
- intros a Ha Hn. rewrite <- (HK a Ha Hn). apply (aview_eq_of SEGS). apply HF.
  rewrite unsigned_lit_small by lia. intros (r & Hin & Hr). apply Hn. unfold sd2_rs in Hin. cbn [In] in Hin.
  unfold sd2_W. destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
  [rewrite B9 in Hr | rewrite B10 in Hr | rewrite B32 in Hr]; lia.
- intros x Hx. apply HG2. apply HG. exact Hx.
Qed.
Lemma sd2_lsd_len : forall v, (1 <= length (sb_dec_c.sb_dec_lsd v 3))%nat.
Proof. intros v. cbn [sb_dec_c.sb_dec_lsd length]. lia. Qed.
Lemma sd2_L_pos : forall X, 1 <= sbd_L X.
Proof.
intros X. unfold sbd_L, sbd_D, sb_dec_c.sb_dec_D. rewrite length_rev. pose proof (sd2_lsd_len (si_v X)) as H.
destruct (_ <? si_md X); [rewrite length_app|]; lia.
Qed.
Lemma sd2_garr8_1 : forall m a x, val_mem SEGS m (a + 0) 1 x -> 0 <= x < 256 -> garr8 SEGS m a [x].
Proof. intros m a x H Hx j Hj. cbn [length] in Hj. destruct j as [|j]; [split; [exact H | exact Hx] | lia]. Qed.
Lemma sd2_garr8_2 : forall m a x y, val_mem SEGS m (a + 0) 1 x -> val_mem SEGS m (a + 1) 1 y ->
  0 <= x < 256 -> 0 <= y < 256 -> garr8 SEGS m a [x; y].
Proof.
intros m a x y H0 H1 Hx Hy j Hj. cbn [length] in Hj.
destruct j as [|[|j]]; [split; [exact H0 | exact Hx] | split; [exact H1 | exact Hy] | lia].
Qed.
Lemma sd2_garr8_3 : forall m a x y z, val_mem SEGS m (a + 0) 1 x -> val_mem SEGS m (a + 1) 1 y -> val_mem SEGS m (a + 2) 1 z ->
  0 <= x < 256 -> 0 <= y < 256 -> 0 <= z < 256 -> garr8 SEGS m a [x; y; z].
Proof.
intros m a x y z H0 H1 H2 Hx Hy Hz j Hj. cbn [length] in Hj.
destruct j as [|[|[|j]]]; [split; [exact H0 | exact Hx] | split; [exact H1 | exact Hy] | split; [exact H2 | exact Hz] | lia].
Qed.
Lemma sd2_finish : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 (regs2 : bvmap 5 word) mem2 md2,
  sbd_cx B X -> sbd_stA B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 W1 mem2 md2 (si_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) mem2) ->
  sbd_shadow_at W1 mem2 (sbd_SH X pos) sbd_sh ->
  garr8 SEGS (mrestrict (w_H W1) mem2) (sbd_F X pos + 32) (rev (sbd_D X)) ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 10 ->
  getr regs2 19 = getr regs1 19 -> getr regs2 20 = w64 (sbd_L X - 1) -> getr regs2 21 = w64 (-1) ->
  getr regs2 22 = getr regs1 22 -> getr regs2 23 = getr regs1 10 -> getr regs2 24 = w64 (sbd_SH X pos) ->
  getr regs2 25 = w64 (sbd_F X pos + 32) -> getr regs2 26 = w64 (- (sbd_F X pos + 32) - 1) ->
  getr regs2 27 = getr regs1 27 ->
  sbd_atL B X (sbd_L X - 1) 0 W1 (mkCfg (mkst (fx := si_fq X) regs2 (Z_to_bv 64 (BASE + 16544)) mem2 (seg_rom SEGS)) md2).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 HX HA HJ2 HK HG HSHb HBuf
  R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
pose proof HA as (HM & Hrec & G2 & G3 & G4 & G8 & G9 & G10 & G19 & G20 & G21 & G22 & G27).
destruct (sd2_mid0_kept X pos regs1 lyc1 Sc1 W1 memc1 mdc1 mem2 md2 HX HA HJ2 HK HG) as (HM2 & Hrec2).
pose proof (sd2_L_pos X) as HL.
exists pos, regs2, lyc1, Sc1, mem2, md2. split.
{ unfold sbd_cfg, cfg_at, SBD_PL, w64.
  replace (BASE + AF_both3_sb_dec + 0x184) with (BASE + 16544) by (unfold AF_both3_sb_dec; lia). reflexivity. }
split; [exact HM2|]. split; [exact HSHb|]. split.
{ unfold sbd_rbase. rewrite R2, R3, R4, R8, R9, R18, R19, R22, R23, R24, R25, R26, R27.
  repeat split; assumption. }
split; [exact R20|]. split; [exact R21|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact HBuf | exact Hrec2].
Qed.
Lemma sd2_LofD : forall X l, rev (sbd_D X) = l -> sbd_L X = Z.of_nat (length l).
Proof. intros X l H. unfold sbd_L. rewrite <- H, length_rev. reflexivity. Qed.
Lemma sd2_case1 : forall X, 0 <= si_v X < 10 -> si_md X = 1 -> sbd_L X = 1 /\ rev (sbd_D X) = [48 + si_v X mod 10].
Proof.
intros X Hv Hm. assert (HD : rev (sbd_D X) = [48 + si_v X mod 10]).
{ unfold sbd_D. rewrite sd2_rD, sd2_lsd1 by lia. rewrite Hm, (Z.mod_small (si_v X)) by lia. reflexivity. }
split; [rewrite (sd2_LofD X _ HD); reflexivity | exact HD].
Qed.
Lemma sd2_case2 : forall X, 0 <= si_v X < 10 -> si_md X = 2 -> sbd_L X = 2 /\ rev (sbd_D X) = [48 + si_v X mod 10; 48].
Proof.
intros X Hv Hm. assert (HD : rev (sbd_D X) = [48 + si_v X mod 10; 48]).
{ unfold sbd_D. rewrite sd2_rD, sd2_lsd1 by lia. rewrite Hm, (Z.mod_small (si_v X)) by lia. reflexivity. }
split; [rewrite (sd2_LofD X _ HD); reflexivity | exact HD].
Qed.
Lemma sd2_case3 : forall X, 10 <= si_v X < 100 -> (si_md X = 1 \/ si_md X = 2) ->
  sbd_L X = 2 /\ rev (sbd_D X) = [48 + si_v X mod 10; 48 + (si_v X / 10) mod 10].
Proof.
intros X Hv Hm.
assert (Hq : 0 <= si_v X / 10 < 10) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (HD : rev (sbd_D X) = [48 + si_v X mod 10; 48 + (si_v X / 10) mod 10]).
{ unfold sbd_D. rewrite sd2_rD, sd2_lsd2 by lia. rewrite (Z.mod_small (si_v X / 10)) by lia.
  destruct Hm as [Hm | Hm]; rewrite Hm; reflexivity. }
split; [rewrite (sd2_LofD X _ HD); reflexivity | exact HD].
Qed.
Lemma sd2_case4 : forall X, 100 <= si_v X -> (si_md X = 1 \/ si_md X = 2) ->
  sbd_L X = 3 /\ rev (sbd_D X) = [48 + si_v X mod 10; 48 + (si_v X / 10) mod 10; 48 + (si_v X / 10 / 10) mod 10].
Proof.
intros X Hv Hm.
assert (HD : rev (sbd_D X) = [48 + si_v X mod 10; 48 + (si_v X / 10) mod 10; 48 + (si_v X / 10 / 10) mod 10]).
{ unfold sbd_D. rewrite sd2_rD, sd2_lsd3 by lia. destruct Hm as [Hm | Hm]; rewrite Hm; reflexivity. }
split; [rewrite (sd2_LofD X _ HD); reflexivity | exact HD].
Qed.
Definition sd2_shcs : list YP09.chunk :=
  [YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 4 (CVal 1 (SLit 4))].
Lemma sd2_shadow : forall E (W1 : world SEGS) m SH,
  bv_unsigned (ew E 32) = SH ->
  region_ok SEGS E (mrestrict (w_H W1) m) (YP09.mkRegion (Some 32%nat) 0 8 0 8 sd2_shcs) ->
  sbd_shadow_at W1 m SH sbd_sh.
Proof.
intros E W1 m SH Hb HR.
assert (K : forall o c, In (YP09.mkChunk o (CVal 1 (SLit c))) sd2_shcs ->
  aview SEGS (w_H W1) m (SH + o) = Some (bv_unsigned (sv_denot E (SLit c)) mod 2 ^ (8 * Z.of_N 1))).
{ intros o c Hin. apply (aview_of_val_mem1 SEGS).
  - exact (field_of_region_any E _ 32 SH _ _ _ _ _ o 1 (SLit c) HR Hb Hin ltac:(lia)).
  - apply Z.mod_pos_bound. lia. }
intros j Hj. cbn [length sbd_sh Z.of_nat] in Hj.
assert (Hj8 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
assert (K1 : forall o, In (YP09.mkChunk o (CVal 1 (SLit 18446744073709551601))) sd2_shcs ->
  aview SEGS (w_H W1) m (SH + o) = Some 241).
{ intros o Hin. rewrite (K o _ Hin). cbn [sv_denot]. rewrite Z_to_bv_unsigned. reflexivity. }
assert (K3 : forall o, In (YP09.mkChunk o (CVal 1 (SLit 18446744073709551603))) sd2_shcs ->
  aview SEGS (w_H W1) m (SH + o) = Some 243).
{ intros o Hin. rewrite (K o _ Hin). cbn [sv_denot]. rewrite Z_to_bv_unsigned. reflexivity. }
assert (K4 : aview SEGS (w_H W1) m (SH + 4) = Some 4).
{ rewrite (K 4 4 ltac:(unfold sd2_shcs; cbn [In]; tauto)). cbn [sv_denot]. rewrite Z_to_bv_unsigned. reflexivity. }
destruct Hj8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn [nth Z.to_nat sbd_sh Pos.to_nat];
  first [exact K4 | apply K1; unfold sd2_shcs; cbn [In]; tauto | apply K3; unfold sd2_shcs; cbn [In]; tauto].
Qed.
Lemma sd2_not : forall z, 0 <= z < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 z) (Z_to_bv 64 (-1)) = Z_to_bv 64 (- z - 1).
Proof.
intros z Hz. rewrite zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id z) by (unfold M64; lia). change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia.
apply Z_to_bv64_eq_mod. replace (- z - 1) with ((2 ^ 64 - 1 - z) + (-1) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma sd2_byte : forall E m F cs od e v,
  region_ok SEGS E m (YP09.mkRegion (Some 10%nat) 0 40 0 40 cs) -> bv_unsigned (ew E 10) = F ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> U E e = v -> 0 <= v < 256 -> val_mem SEGS m (F + od) 1 v.
Proof.
intros E m F cs od e v HR Hb Hin He Hv.
exact (field_of_region E m 10 F cs 0 40 0 40 od 1 e v HR Hb Hin ltac:(rewrite denot_lit_U, He; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Ltac sd2_awr_tac HX HA :=
  lazymatch type of HA with sbd_stA _ ?X ?pos ?regs1 ?lyc1 ?Sc1 ?W1 ?memc1 ?mdc1 =>
  lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end;
  exact (sd2_awr X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX HA) end.
Ltac sd2_acc_tac HX HA KA GA HFr HG :=
  lazymatch type of HA with sbd_stA _ ?X ?pos ?regs1 ?lyc1 ?Sc1 ?W1 ?memc1 ?mdc1 =>
  lazymatch type of HFr with frame_of ?E0 ?rs ?m0 ?m1 =>
    let rs' := eval vm_compute in rs in change (frame_of E0 rs' m0 m1) in HFr end;
  let KA2 := fresh "KA" in let GA2 := fresh "GA" in
  destruct (sd2_acc X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ _ _ HX HA KA GA HFr HG) as (KA2 & GA2);
  clear KA GA HFr HG; rename KA2 into KA; rename GA2 into GA end.
Ltac sd2_close HX HA HS HJ KA GA EE E10 E32 HB32 HFb HB Q20 :=
  lazymatch type of HA with sbd_stA _ ?X ?pos ?regs1 ?lyc1 ?Sc1 ?W1 ?memc1 ?mdc1 =>
  lazymatch goal with |- sbd_atL _ _ _ _ _ {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem ?msF) _; cfg_model := ?md2 |} =>
  let R2 := fresh "R" in let R3 := fresh "R" in let R4 := fresh "R" in let R8 := fresh "R" in
  let R9 := fresh "R" in let R18 := fresh "R" in let R19 := fresh "R" in let R21 := fresh "R" in
  let R22 := fresh "R" in let R23 := fresh "R" in let R24 := fresh "R" in let R25 := fresh "R" in
  let R26 := fresh "R" in let R27 := fresh "R" in let HR2 := fresh "HR" in
  prreg HS (2%bv : bv 5) R2; rewrite (EE 2%nat 2%bv eq_refl) in R2;
  prreg HS (3%bv : bv 5) R3; rewrite (EE 3%nat 3%bv eq_refl) in R3;
  prreg HS (4%bv : bv 5) R4; rewrite (EE 4%nat 4%bv eq_refl) in R4;
  prreg HS (8%bv : bv 5) R8; rewrite (EE 8%nat 8%bv eq_refl) in R8;
  prreg HS (9%bv : bv 5) R9; rewrite (EE 9%nat 9%bv eq_refl) in R9;
  prreg HS (18%bv : bv 5) R18; rewrite (EE 10%nat 10%bv eq_refl) in R18;
  prreg HS (19%bv : bv 5) R19; rewrite (EE 19%nat 19%bv eq_refl) in R19;
  prreg HS (21%bv : bv 5) R21; rewrite lit_m1 in R21;
  prreg HS (22%bv : bv 5) R22; rewrite (EE 22%nat 22%bv eq_refl) in R22;
  prreg HS (23%bv : bv 5) R23; rewrite (EE 10%nat 10%bv eq_refl) in R23;
  prreg HS (24%bv : bv 5) R24; rewrite E32 in R24;
  prreg HS (25%bv : bv 5) R25; rewrite E10, unsigned_lit_small in R25 by lia;
  prreg HS (26%bv : bv 5) R26; rewrite E10, unsigned_lit_small, sd2_not in R26 by lia;
  prreg HS (27%bv : bv 5) R27; rewrite (EE 27%nat 27%bv eq_refl) in R27;
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HR2; cbn [ms_mem restrict] in HR2;
  exact (sd2_finish X pos regs1 lyc1 Sc1 W1 memc1 mdc1 (ms_regs msF) (ms_mem msF) md2 HX HA HJ KA GA
    (sd2_shadow _ W1 (ms_mem msF) _ HB32 HR2) HB R2 R3 R4 R8 R9 R18 R19 Q20 R21 R22 R23 R24 R25 R26 R27) end end.
Theorem sbd_seg2 : sbd_seg2_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA.
pose proof (sd2_entry X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA) as HS.
destruct (sd2_env X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA) as (EE & E10 & E20 & E21 & E22 & E32 & B9 & B10 & B32).
pose proof HA as (HM & Hrec & G2 & G3 & G4 & G8 & G9 & G10 & G19 & G20 & G21 & G22 & G27).
pose proof HM as (HJ & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSP16 & Hbud & HSPle & _ & Hv & Hmd & _).
destruct (sd2_Ffacts X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as (HF4 & HFc & _).
pose proof asan_consts as (C1 & _).
assert (HB32 : bv_unsigned (ew (ESD2 X pos regs1) 32) = sbd_SH X pos) by (cbn [base_val] in B32; exact B32).
assert (U21 : U (ESD2 X pos regs1) (SOff 21 0) = si_v X) by (apply U_atom; [exact E21 | lia]).
assert (Hq1 : 0 <= si_v X / 10 < 2 ^ 31) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Hq2 : 0 <= si_v X / 10 / 10 < 2 ^ 31) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Uq1 : U (ESD2 X pos regs1) (qx (SOff 21 0)) = si_v X / 10) by (apply U_qx; [exact U21 | exact Hv]).
assert (Ua1 : U (ESD2 X pos regs1) (SAlu ALU_ADD (qx (SOff 21 0)) (SLit 0)) = si_v X / 10)
  by (rewrite U_add_lit, Uq1, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (Uq2 : U (ESD2 X pos regs1) (qx (qx (SOff 21 0))) = si_v X / 10 / 10) by (apply U_qx; [exact Uq1 | exact Hq1]).
assert (Ua2 : U (ESD2 X pos regs1) (SAlu ALU_ADD (qx (qx (SOff 21 0))) (SLit 0)) = si_v X / 10 / 10)
  by (rewrite U_add_lit, Uq2, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (HF10 : bv_unsigned (ew (ESD2 X pos regs1) 10) = sbd_F X pos) by (rewrite E10; apply unsigned_lit_small; lia).
pose proof (Z.mod_pos_bound (si_v X) 10 ltac:(lia)) as Hm0.
pose proof (Z.mod_pos_bound (si_v X / 10) 10 ltac:(lia)) as Hm1.
pose proof (Z.mod_pos_bound (si_v X / 10 / 10) 10 ltac:(lia)) as Hm2.
pose proof (@SRr_run_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (si_fq X) _ _ _ _ _ B LAWS) as RUNC.
pose proof (@SRr_run_to_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := si_fq X) (L := lib_both3_0_listing) (PI := PI)) as BR.
assert (HEI : img_env VAL A_LIM (ESD2 X pos regs1)) by (unfold ESD2; apply Eimg_env).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ sd2_W X pos a -> aview SEGS (w_H W1) memc1 a = aview SEGS (w_H W1) memc1 a)
  by (intros; reflexivity).
assert (GA : mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) memc1)) by (intros x Hx; exact Hx).
unfold sbd_cfg, cfg_at.
replace (BASE + AF_both3_sb_dec + SBD_PA) with (BASE + (AF_both3_sb_dec + 0x74)) by (unfold SBD_PA; lia).
change (w64 (BASE + (AF_both3_sb_dec + 0x74))) with (Z_to_bv 64 (BASE + (AF_both3_sb_dec + 0x74))).
paj_run_shc RUNP RUNC HS HJ; [sd2_awr_tac HX HA|].
sd2_acc_tac HX HA KA GA HFr HG. clear HF.
psrr_branch_pi RUNP BR HS.
- assert (Hv10 : si_v X < 10).
  { rewrite (sd2_br_lt10 (ESD2 X pos regs1) (SOff 21 (-10)) (si_v X)) in Hc; [apply Z.ltb_lt in Hc; exact Hc | | lia].
    rewrite U_SOff, E21, unsigned_lit_small by lia. f_equal; lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ; [sd2_awr_tac HX HA|].
  sd2_acc_tac HX HA KA GA HFr HG. clear HF.
  psrr_branch_pi RUNP BR HS.
  + assert (Hmd1 : si_md X = 1).
    { rewrite branch_geu_U, U_SLit, (U_atom (ESD2 X pos regs1) 20 (si_md X) E20) in Hc by lia.
      change (zcanon 1) with 1 in Hc. apply negb_true_iff, Z.ltb_ge in Hc. lia. }
    clear Hc.
    paj_run_to_shc RUNTOP HS HJ 16544; [sd2_awr_tac HX HA|].
    sd2_acc_tac HX HA KA GA HFr HG. clear HF.
    destruct (sd2_case1 X ltac:(lia) Hmd1) as (HL & HD).
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
    pose proof (sd2_byte _ _ _ _ 32 (dx (SOff 21 0) (SOff 21 0)) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ U21 U21 Hv) ltac:(lia)) as V0;
    assert (HB : garr8 SEGS (mrestrict (w_H W1) (ms_mem msF)) (sbd_F X pos + 32) (rev (sbd_D X)))
      by (rewrite HD; apply sd2_garr8_1; [rewrite Z.add_0_r; exact V0 | lia]);
    prreg HS (20%bv : bv 5) R20;
    assert (Q20 : getr (ms_regs msF) 20 = w64 (sbd_L X - 1)) by (rewrite R20, HL; reflexivity) end.
    apply SRr_ret. pmkst HS.
    sd2_close HX HA HS HJ KA GA EE E10 E32 HB32 HF4 HB Q20.
  + assert (Hmd2 : si_md X = 2).
    { rewrite branch_geu_U, U_SLit, (U_atom (ESD2 X pos regs1) 20 (si_md X) E20) in Hc by lia.
      change (zcanon 1) with 1 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. lia. }
    clear Hc.
    paj_run_to_shc RUNTOP HS HJ 16544; [sd2_awr_tac HX HA|].
    sd2_acc_tac HX HA KA GA HFr HG. clear HF.
    destruct (sd2_case2 X ltac:(lia) Hmd2) as (HL & HD).
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
    pose proof (sd2_byte _ _ _ _ 32 (dx (SOff 21 0) (SOff 21 0)) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ U21 U21 Hv) ltac:(lia)) as V0;
    pose proof (sd2_byte _ _ _ _ 33 (SLit 48) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_lit _ 48 ltac:(lia)) ltac:(lia)) as V1;
    assert (HB : garr8 SEGS (mrestrict (w_H W1) (ms_mem msF)) (sbd_F X pos + 32) (rev (sbd_D X)))
      by (rewrite HD; apply sd2_garr8_2; [rewrite Z.add_0_r; exact V0 | rewrite <- Z.add_assoc; exact V1 | lia | lia]);
    prreg HS (20%bv : bv 5) R20;
    assert (Q20 : getr (ms_regs msF) 20 = w64 (sbd_L X - 1)) by (rewrite R20, HL; reflexivity) end.
    apply SRr_ret. pmkst HS.
    sd2_close HX HA HS HJ KA GA EE E10 E32 HB32 HF4 HB Q20.
- assert (Hv10 : 10 <= si_v X).
  { pose proof (eq_trans (eq_sym (sd2_br_lt10 (ESD2 X pos regs1) (SOff 21 (-10)) (si_v X)
      ltac:(rewrite U_SOff, E21, unsigned_lit_small by lia; f_equal; lia) Hv)) Hc) as H.
    apply Z.ltb_ge in H. exact H. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ; [sd2_awr_tac HX HA|].
  sd2_acc_tac HX HA KA GA HFr HG. clear HF.
  psrr_branch_pi RUNP BR HS.
  + assert (Hv100 : si_v X / 10 < 10).
    { pose proof (eq_trans (eq_sym (sd2_br_lt10 (ESD2 X pos regs1)
        (SAlu ALU_ADD (SAlu ALU_ADD (qx (SOff 21 0)) (SLit 0)) (SLit (-10))) (si_v X / 10)
        ltac:(rewrite U_add_lit, Ua1; f_equal; lia) Hq1)) Hc) as H.
      apply Z.ltb_lt in H. exact H. }
    clear Hc.
    paj_run_to_shc RUNTOP HS HJ 16544; [sd2_awr_tac HX HA|].
    sd2_acc_tac HX HA KA GA HFr HG. clear HF.
    destruct (sd2_case3 X ltac:(lia) Hmd) as (HL & HD).
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
    pose proof (sd2_byte _ _ _ _ 32 (dx (SOff 21 0) (SOff 21 0)) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ U21 U21 Hv) ltac:(lia)) as V0;
    pose proof (sd2_byte _ _ _ _ 33 (dx (SAlu ALU_ADD (qx (SOff 21 0)) (SLit 0)) (qx (SOff 21 0))) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ Ua1 Uq1 Hq1) ltac:(lia)) as V1;
    assert (HB : garr8 SEGS (mrestrict (w_H W1) (ms_mem msF)) (sbd_F X pos + 32) (rev (sbd_D X)))
      by (rewrite HD; apply sd2_garr8_2; [rewrite Z.add_0_r; exact V0 | rewrite <- Z.add_assoc; exact V1 | lia | lia]);
    prreg HS (20%bv : bv 5) R20;
    assert (Q20 : getr (ms_regs msF) 20 = w64 (sbd_L X - 1)) by (rewrite R20, HL; reflexivity) end.
    apply SRr_ret. pmkst HS.
    sd2_close HX HA HS HJ KA GA EE E10 E32 HB32 HF4 HB Q20.
  + assert (Hv100 : 10 <= si_v X / 10).
    { pose proof (eq_trans (eq_sym (sd2_br_lt10 (ESD2 X pos regs1)
        (SAlu ALU_ADD (SAlu ALU_ADD (qx (SOff 21 0)) (SLit 0)) (SLit (-10))) (si_v X / 10)
        ltac:(rewrite U_add_lit, Ua1; f_equal; lia) Hq1)) Hc) as H.
      apply Z.ltb_ge in H. exact H. }
    clear Hc.
    paj_run_shc RUNP RUNC HS HJ; [sd2_awr_tac HX HA|].
    sd2_acc_tac HX HA KA GA HFr HG. clear HF.
    destruct (sd2_case4 X ltac:(lia) Hmd) as (HL & HD).
    psrr_branch_pi RUNP BR HS; clear Hc;
    (paj_run_to_shc RUNTOP HS HJ 16544; [sd2_awr_tac HX HA|]);
    sd2_acc_tac HX HA KA GA HFr HG; clear HF;
    (lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
    pose proof (sd2_byte _ _ _ _ 32 (dx (SOff 21 0) (SOff 21 0)) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ U21 U21 Hv) ltac:(lia)) as V0;
    pose proof (sd2_byte _ _ _ _ 33 (dx (SAlu ALU_ADD (qx (SOff 21 0)) (SLit 0)) (qx (SOff 21 0))) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ Ua1 Uq1 Hq1) ltac:(lia)) as V1;
    pose proof (sd2_byte _ _ _ _ 34 (dx (SAlu ALU_ADD (qx (qx (SOff 21 0))) (SLit 0)) (qx (qx (SOff 21 0)))) _ HR1 HF10
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) (U_dx _ _ _ _ Ua2 Uq2 Hq2) ltac:(lia)) as V2;
    assert (HB : garr8 SEGS (mrestrict (w_H W1) (ms_mem msF)) (sbd_F X pos + 32) (rev (sbd_D X)))
      by (rewrite HD; apply sd2_garr8_3; [rewrite Z.add_0_r; exact V0 | rewrite <- Z.add_assoc; exact V1
          | rewrite <- Z.add_assoc; exact V2 | lia | lia | lia]);
    prreg HS (20%bv : bv 5) R20;
    assert (Q20 : getr (ms_regs msF) 20 = w64 (sbd_L X - 1)) by (rewrite R20, HL; reflexivity) end);
    apply SRr_ret; pmkst HS;
    sd2_close HX HA HS HJ KA GA EE E10 E32 HB32 HF4 HB Q20.
Qed.
End h.
End f.
End d.
