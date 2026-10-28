(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_count RF_fse_rd_zero RdChk.
Import ListNotations.
Open Scope Z_scope.
Section Loop.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac bveq := apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
  rewrite ?swrap32_eq; rewrite ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.
Ltac beq64 := lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?A) (Z_to_bv 64 ?B)] =>
  let EQ := fresh "EQ" in assert (EQ : Z_to_bv 64 A = Z_to_bv 64 B) by bveq; rewrite EQ; clear EQ; if_true end.
#[using="OK"] Lemma exit_run : forall s m1 msvw (x1 x6 x13 x14 x16 x25 x28 x29 : word),
rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> rd_brk_ok C s ->
r_remaining s = 1 -> 1 <= r_charnum s <= msv1 -> r_bitCount s <= 32 ->
evt usegs (rd_body_post C (r_nc s) (r_charnum s - 1) tl (r_ip s + (r_bitCount s + 7) / 8))
(rd_exit C s m1 x1 x6 x13 x14 x16 x25 x28 x29).
Proof.
intros s m1 msvw x1 x6 x13 x14 x16 x25 x28 x29 INV (B1 & B2 & B3 & B4 & B5) Erem Hcn Hbc.
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & (HNP & HNA) & (HVP & HVA) & (HTP & HTA) & HBP).
unfold RD_STACK in *.
unfold rd_exit, rd_lst.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR. subst rem.
destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk0 & junk16 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
assert (LWS : length (map (Z_to_bv 64) nc) = length (c_rt0 C)) by (rewrite length_map; exact LNC).
assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
change (2^31) with 2147483648 in *.
zstep. zstep. zstep. if_false.
zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
zstep. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia; [exfalso; lia|].
zstep. zstep. zstep.
rewrite (swrap32_small (bc + 7)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
set (q := (bc + 7) / 8).
assert (Q : 0 <= q < 5) by (subst q; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
rewrite (swrap32_small q) by lia.
zstep. zstep.
zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
zstep. zstep. zstep. zstep.
lazymatch goal with |- context [Z.lxor q ?k <? ?j] =>
replace (Z.lxor q k <? j) with false
by (symmetry; apply Z.ltb_ge; change k with (2^63); rewrite zb_lxor_pow2_small by lia; change (2^63) with k; lia) end.
replace (BUF + ip + q <? BUF + ip) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
zstep. if_cases K5; zify_cond K5; [exfalso; lia|].
zstep.
replace (BUF + ip + q - BUF) with (ip + q) by lia.
do 13 zstep. zstep. zstep.
release_frame FR ST (c_SP C).
apply evt_done. unfold rd_body_post, rd_W, RD_STACK.
do 14 eexists. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [exact ARR|]. split; [| exact HTL].
replace (cn - 1) with (cn + -1) by lia. exact HMSV.
Qed.
#[using="OK"] Lemma buf_h8 : 8 <= FseNCount.Zlength buf.
Proof. unfold FseNCount.Zlength. destruct OK as (HH & _). lia. Qed.
#[using="OK"] Lemma msv1_ok : 1 <= msv1 <= FseNCount.Zlength (c_rt0 C).
Proof. unfold FseNCount.Zlength. destruct OK as (_ & _ & HM0 & HM1 & _). lia. Qed.
#[using="OK Htl"] Lemma loop_run : forall f s sF m1 msvw (x1 x6 x14 x16 x28 : word),
rloop buf msv1 f s = Ok sF ->
rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evt usegs (rd_body_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8)) (rd_head C s m1 x1 x6 x14 x16 x28).
Proof.
induction f as [|f IH]; intros s sF m1 msvw x1 x6 x14 x16 x28 RL INV HC HP HB32 F1 F2 F3.
{ cbn in RL. discriminate RL. }
cbn [rloop] in RL.
set (POSTF := rd_body_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8)).
assert (CNT : forall s1 m2 (y6 y14 y16 y27 y28 : word),
rd_inv C m2 (r_nc s1) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s1 -> POS buf s1 -> r_bitCount s1 < 32 ->
y16 = Z_to_bv 64 (2 * r_threshold s1 - 1) -> y28 = Z_to_bv 64 (2 * r_threshold s1 - 1 - r_remaining s1) ->
(let! fl := rcount_block buf msv1 s1 in match fl with Brk s' => Ok s' | Cont s' => rloop buf msv1 f s' end) = Ok sF ->
evt usegs POSTF (rd_lst C 0x1425c m2 (Z_to_bv 64 (BUF + r_ip s1)) y6 (Z_to_bv 64 (r_charnum s1))
(Z_to_bv 64 (bv_swrap 32 (r_bitStream s1))) y14 y16 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1))
(Z_to_bv 64 (r_bitCount s1)) y27 y28 (Z_to_bv 64 (r_nbBits s1)))).
{ intros s1 m2 y6 y14 y16 y27 y28 INV1 HC1 HP1 HB1 E16 -> RL1.
destruct (rcount_total buf (buf_all_bytes C OK) buf_h8 msv1 (c_rt0 C) msv1_ok tl Htl s1 HC1 HP1 HB1) as (fl & EF & HF).
rewrite EF in RL1. cbn [bind] in RL1.
eapply (count_run C OK tl Htl POSTF s1 m2 msvw (Z_to_bv 64 tl) fl y6 y14 y16 y27); try eassumption.
- intros s' m3 z1 z6 z13 z14 z16 z25 z28 z29 -> INV3 BK. injection RL1 as ->.
destruct HF as ((_ & CN1 & _) & _).
eapply (exit_run sF m3 msvw); try assumption. lia.
- intros s' m3 z1 z6 z14 z16 z28 -> INV3. destruct HF as (HC3 & HP3 & HB3 & _).
eapply IH; eassumption. }
unfold rbody in RL.
destruct (r_previous0 s) eqn:EP.
-
destruct (rzero_total buf (buf_all_bytes C OK) buf_h8 msv1 (c_rt0 C) msv1_ok tl Htl s HC HP HB32) as (flz & EZ & HZ).
rewrite EZ in RL. cbn [bind] in RL.
unfold rd_head. rewrite EP.
eapply (zero_run C OK POSTF tl s m1 msvw (Z_to_bv 64 tl) flz); try eassumption.
+ intros s' z1 z6 z13 z14 z16 z25 z28 z29 -> EN BK. cbn [bind] in RL. injection RL as ->.
destruct HZ as ((_ & CN1 & _) & _).
eapply (exit_run sF m1 msvw); try assumption; try lia. rewrite EN. exact INV.
+ intros s' z6 z14 z16 z27 z28 -> EN. destruct HZ as (HC1 & HP1 & HB1 & _).
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC1 HP1) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof (CNT s' m1) as CNT'. unfold rd_lst in CNT'.
unfold rd_cnt0, rd_lst.
zstep. zstep. zstep. zstep. zstep.
chk64.
eapply CNT'; try eassumption; [rewrite EN; exact INV| bveq| bveq].
-
cbn [bind] in RL.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof (CNT s m1) as CNT'. unfold rd_lst in CNT'.
unfold rd_head, rd_lst. rewrite EP.
zstep. zstep. zstep. zstep. zstep. zstep.
beq64.
eapply CNT'; try eassumption; [bveq| bveq].
Qed.
End Loop.
