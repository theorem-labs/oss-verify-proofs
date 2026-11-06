(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from the walk of the same function of libreac's fuzz_grant (the two are the same code at other addresses); the context, the cut specifications and the tactics are restated on fuzz_disco's contract, treac_ctrl_parse_spec. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/CtrlParseCut.v, with its module paths and module names changed; 273 of its 303 lines of code are new or changed and 453 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison SnShared SnSx.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma tjs_zd_sub : forall x K sp d n w, w <= n ->
Forall (zdisjoint x) (snp_out K sp d n) -> Forall (zdisjoint x) (snp_out K sp d w).
Proof.
intros x K sp d n w Hw H. unfold snp_out in *.
apply Forall_cons_iff in H as [H1 H]. apply Forall_cons_iff in H as [H2 _].
apply Forall_cons; [exact H1|]. apply Forall_cons; [|apply Forall_nil].
unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.
Lemma tjs_pw_sub : forall K sp d n w, w <= n ->
pairwise zdisjoint (snp_out K sp d n) -> pairwise zdisjoint (snp_out K sp d w).
Proof.
intros K sp d n w Hw H. unfold snp_out in *. cbn [pairwise] in H |- *. destruct H as (H & _).
split; [|split; [apply Forall_nil | exact I]].
apply Forall_cons_iff in H as [H _]. apply Forall_cons; [|apply Forall_nil].
unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.
Lemma tjs_fmt_sub : forall rd K sp d n w f fmt, w <= n ->
fmt_at rd (snp_out K sp d n) f fmt -> fmt_at rd (snp_out K sp d w) f fmt.
Proof.
intros rd K sp d n w f fmt Hw (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact H2|]. split; [exact (tjs_zd_sub _ _ _ _ _ _ Hw H3) | exact H4].
Qed.
Lemma tjs_args_sub : forall rd K sp d n w ws args, w <= n ->
pf_args_asan rd (snp_out K sp d n) ws args -> pf_args_asan rd (snp_out K sp d w) ws args.
Proof.
intros rd K sp d n w ws args Hw. revert ws. induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
destruct ws as [|w0 ws]; [destruct H|]. cbn [pf_args_asan] in H |- *. destruct H as [Ha Hr].
split; [|exact (IH ws Hr)].
destruct a; cbn [pf_arg_asan] in Ha |- *; try exact Ha.
destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact (tjs_zd_sub _ _ _ _ _ _ Hw A6) | exact A7].
Qed.
Lemma tjs_hull_sub : forall rd d n w, 1 <= w <= n -> shadow_hull_vis rd d n -> shadow_hull_vis rd d w.
Proof.
intros rd d n w Hw H s Hs. apply H. split; [lia|].
assert (Hm : shadow_addr (d + w - 1) / 8 <= shadow_addr (d + n - 1) / 8).
{ apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
Lemma tjs_args_slack : forall rd rs ws args, pf_args_asan rd rs ws args -> pf_args_amem ws args -> pf_args_slack ws args.
Proof.
intros rd rs ws args. revert ws. induction args as [|a args IH]; intros ws Ha Hm; [destruct ws; exact I|].
destruct ws as [|w ws]; [destruct Ha|]. destruct Ha as [_ Ha].
destruct a as [v | u | s]; cbn [pf_args_slack pf_args_amem] in Hm |- *.
- exact (IH ws Ha Hm).
- exact (IH ws Ha Hm).
- destruct Hm as [Hm1 Hm2]. split; [|exact (IH ws Ha Hm2)].
pose proof (str_end_ge w s) as Hse. apply (amem_range_le w _ (Z.of_nat (length s) + 8)); [lia | exact Hm1].
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Variable STK : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tj_dest_off_globals : forall (img_lo img_hi : Z) ly S (W : world SEGS) mem md b sz d w,
IMG_LO <= img_lo -> img_hi <= IMG_TOP ->
AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) -> b <= d -> d + w <= b + req_size sz ->
zdisjoint (d, w) (img_lo, img_hi - img_lo).
Proof.
intros img_lo img_hi ly S W mem md b sz d w Hlo Hhi HAR Hin Hbd Hdw.
pose proof (blk_off_imgP _ _ _ _ _ _ b sz HAR Hin) as Hoff. unfold off_img in Hoff.
destruct Hoff as [Hoff | Hoff].
- unfold zdisjoint. cbn [fst snd]. left. lia.
- eapply dest_off_globals_of_ablocks; [exact Hin | lia | exact Hbd].
Qed.
Lemma aj_sh_snprintf_at : forall (fq : YK11.FPState) (gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z),
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK gc gv img_lo img_hi cr pc ->
forall W regsT memT sp0 FP ly S W0 mem md own lyc Sc mdc k
(d n f : Z) (fmt : list Z) (ps : list pf_piece) (xs ws : list Z) (args : list pf_arg) (T : list Z) (cval o : Z) raw
(Q : world SEGS -> config -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memT) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SNPRINTF_STK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
consts_view SEGS W memT cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out SNPRINTF_STK (sp0 + o) d n)) cr ->
rdword (aview SEGS (w_H W) memT) gc = Some gv -> rdword (aview SEGS (w_H W) memT) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out SNPRINTF_STK (sp0 + o) d n) ->
Forall (zdisjoint (gv, 8)) (snp_out SNPRINTF_STK (sp0 + o) d n) ->
fmt_at (aview SEGS (w_H W) memT) (snp_out SNPRINTF_STK (sp0 + o) d n) f fmt ->
disco_fmt_lo <= f /\ f + Z.of_nat (length fmt) + 1 <= disco_fmt_hi -> fmt <> [] ->
pf_parse fmt = Some ps -> Forall pf_disco_piece ps ->
va_words regsT (aview SEGS (w_H W) memT) (sp0 + o) xs ws ->
o + 8 * Z.of_nat (length xs) <= 0 ->
Forall (zdisjoint (sp0 + o, 8 * Z.of_nat (length xs))) (snp_out SNPRINTF_STK (sp0 + o) d n) ->
pf_args_asan (aview SEGS (w_H W) memT) (snp_out SNPRINTF_STK (sp0 + o) d n) ws args ->
pf_args_amem ws args ->
pf_text ps args = Some T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + n <= 2 ^ 63 ->
pairwise zdisjoint (snp_out SNPRINTF_STK (sp0 + o) d n) ->
(forall a, d <= a < d + n ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d (n + 8) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n ->
zdisjoint (d, n) (img_lo, img_hi - img_lo) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fq)) 5) 7 = 0 ->
(forall (fx' : YK11.FPState) regs2 mem2 md2,
(forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx') r = Sem.reg_get (@fp_regs fq) r) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k ->
aregs_preserved regsT regs2 -> getr regs2 10 = w64 (Z.of_nat (length T)) ->
(forall i, 0 <= i < Z.min (Z.of_nat (length T)) (n - 1) ->
aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) T 0)) ->
aview SEGS (w_H W) mem2 (d + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) ->
~ (sp0 + o - SNPRINTF_STK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
same_but_materialized mdc md2 ->
SRr SEGS W (mkCfg (mkst (fx := fx') regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros fq gc gv img_lo img_hi cr pc ASNP W regsT memT sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt ps xs ws args T
cval o raw Q HJ HROD Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Ha2 HCV HCB HCD HG1 HG2 HG3 HG4 HG5 HG6 HG7 HG8
HFMT HRNG HNE HPS HPD HVA HXS HXD HARGS HAMM HTXT Hn Hlt Hd0 Hdn HPW Hdest Hamr Hra_d Hhull Himg Hfrm HK.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
try eassumption; [lia | rewrite Hra; exact Hraw]. }
assert (HLO : ly_stk_lo lyc + SNPRINTF_STK <= spZ regsT) by (rewrite Eslo, Hsp; lia).
assert (HPR : forall a, spZ regsT - SNPRINTF_STK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp in Ha; lia).
set (w := sn_len (n - 1) T).
assert (Hw : w = Z.min (Z.of_nat (length T)) (n - 1) + 1).
{ unfold w, sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
assert (Hw1 : 1 <= w <= n) by (pose proof (Z.le_min_r (Z.of_nat (length T)) (n - 1)); lia).
assert (HDEST : dest_ok SEGS B lyc Sc W regsT memT d w).
{ intros a Ha. destruct (Hdest a ltac:(lia)) as (Hwb & Hns).
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hwb) as (Hp & Hno). rewrite Hsp.
split; [apply apresent_writable; exact Hp | auto]. }
assert (HCD' : Forall (fun r => Forall (zdisjoint r) (snp_out SNPRINTF_STK (spZ regsT) d w)) cr).
{ rewrite Hsp. eapply Forall_impl; [|exact HCD]. intros r Hr. exact (tjs_zd_sub _ _ _ _ _ _ (proj2 Hw1) Hr). }
assert (HG7' : Forall (zdisjoint (gc, 8)) (snp_out SNPRINTF_STK (spZ regsT) d w))
by (rewrite Hsp; exact (tjs_zd_sub _ _ _ _ _ _ (proj2 Hw1) HG7)).
assert (HG8' : Forall (zdisjoint (gv, 8)) (snp_out SNPRINTF_STK (spZ regsT) d w))
by (rewrite Hsp; exact (tjs_zd_sub _ _ _ _ _ _ (proj2 Hw1) HG8)).
assert (HVA' : va_words regsT (aview SEGS (w_H W) memT) (spZ regsT) xs ws) by (rewrite Hsp; exact HVA).
assert (HXS' : spZ regsT + 8 * Z.of_nat (length xs) <= 2 ^ 47).
{ eapply (va_slots_below_47_AR SEGS B _ _ _ _ _ _ xs HPRE). rewrite Hsp. lia. }
assert (HXD' : Forall (zdisjoint (spZ regsT, 8 * Z.of_nat (length xs))) (snp_out SNPRINTF_STK (spZ regsT) d w))
by (rewrite Hsp; exact (tjs_zd_sub _ _ _ _ _ _ (proj2 Hw1) HXD)).
assert (HFF : FF_disco disco_fmt_lo disco_fmt_hi (aview SEGS (w_H W) memT) (snp_out SNPRINTF_STK (spZ regsT) d w) f ws T).
{ rewrite Hsp. exists fmt, ps, args.
split; [exact (tjs_fmt_sub _ _ _ _ _ _ _ _ (proj2 Hw1) HFMT)|].
split; [exact HPS|]. split; [exact HPD|].
split; [exact (tjs_args_sub _ _ _ _ _ _ _ _ (proj2 Hw1) HARGS)|].
split; [exact HTXT|]. split; [exact (pf_disco_prec_pos ps args HPD)|].
split; [exact (proj1 HRNG)|]. split; [exact (proj2 HRNG)|].
split; [exact (tjs_args_slack _ _ _ _ HARGS HAMM)|].
split; [exact HNE | exact HAMM]. }
assert (HPW' : pairwise zdisjoint (snp_out SNPRINTF_STK (spZ regsT) d w))
by (rewrite Hsp; exact (tjs_pw_sub _ _ _ _ _ (proj2 Hw1) HPW)).
assert (Hamr' : amem_range d (w + 8)) by exact (amem_range_le d (w + 8) (n + 8) ltac:(lia) Hamr).
assert (Hra_d' : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d w)
by (intros x Hx; apply Hra_d; lia).
assert (Hhull' : shadow_hull_vis (aview SEGS (w_H W) memT) d w) by exact (tjs_hull_sub _ d n w Hw1 Hhull).
assert (Himg' : zdisjoint (d, w) (img_lo, img_hi - img_lo)) by (unfold zdisjoint in *; cbn [fst snd] in *; lia).
assert (Hdw : d + w <= 2 ^ 63) by lia.
eapply (srr_fx_continue (fx := fq) SEGS W _ (raZ regsT)
(fun (fx' : YK11.FPState) regs' mem' md' => AR SEGS B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\
same_but_materialized mdc md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T ->
aview SEGS (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regsT - SNPRINTF_STK <= a < spZ regsT) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a))).
{ exact (ASNP lyc Sc W regsT memT mdc d n f xs ws T cval HPRE HROD HLO HPR Ha0 Ha1 Ha2 HCV HCB HCD' HG1 HG2 HG3 HG4 HG5 HG6
HG7' HG8' HVA' HXS' HXD' HFF Hn Hlt Hd0 Hdw HPW' HDEST Hamr' Hra_d' Hhull' Himg' Hfrm). }
intros fx' regs2 mem2 md2 Hf1 Hf2 (HAR2 & HP & Hsame & Hres & Hwr & Hfr & Hpres2).
fold w in Hwr, Hfr. rewrite Hsp in Hfr.
assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) ->
~ (sp0 + o - SNPRINTF_STK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | intros H3; apply H1; lia | exact H2]. }
assert (Hwr' : forall i, 0 <= i < Z.min (Z.of_nat (length T)) (n - 1) ->
aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) T 0)).
{ intros i Hi. rewrite (Hwr i ltac:(lia)). f_equal. unfold sn_bytes.
rewrite app_nth1 by (rewrite length_firstn; lia).
rewrite <- (firstn_skipn (Z.to_nat (n - 1)) T) at 2.
rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
assert (Hnul' : aview SEGS (w_H W) mem2 (d + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0).
{ rewrite (Hwr (Z.min (Z.of_nat (length T)) (n - 1)) ltac:(pose proof (Z.le_min_r (Z.of_nat (length T)) (n - 1)); lia)).
f_equal. unfold sn_bytes. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
replace (Z.to_nat (Z.min (Z.of_nat (length T)) (n - 1)) - Nat.min (Z.to_nat (n - 1)) (length T))%nat with 0%nat by lia.
reflexivity. }
assert (HJ2 : ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k).
{ eapply (ajournal_after_write SEGS B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) \/ (sp0 + o - SNPRINTF_STK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hfr' a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; [left; exact (proj1 (Hdest a ltac:(pose proof (Z.le_min_r (Z.of_nat (length T)) (n - 1)); lia)))
| left; left; lia].
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
replace (@cfg_at fx' SEGS (raZ regsT) regs2 mem2 md2) with (mkCfg (mkst (fx := fx') regs2 raw mem2 (seg_rom SEGS)) md2)
by (unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
exact (HK fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP Hres Hwr' Hnul' Hfr' Hpres2 Hsame).
Qed.
Lemma tj_postX_fx : forall (cx : tjcx) (fx' : YK11.FPState) W' c',
(forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx') r = Sem.reg_get (@fp_regs (c_fq cx)) r) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 ->
tj_postX B (mkTJCX fx' (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) (c_t cx)
(c_now cx) (c_buf cx) (c_cap cx) (c_Nb cx) (c_T cx) (c_fpos cx) (c_sp1 cx) (c_E0 cx)) W' c' ->
tj_postX B cx W' c'.
Proof.
intros cx fx' W' c' Hf1 Hf2 H.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_postX, treac_disco_table_json_post, apost_base in *.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in H, Hf1 |- *.
destruct H as (fx2 & ly' & S' & regs' & mem' & md' & Hc & Hr & Hcsr & HR).
exists fx2, ly', S', regs', mem', md'. split; [exact Hc|]. split.
- intros r Hr0. rewrite (Hr r Hr0). exact (Hf1 r Hr0).
- split; [right; destruct Hcsr as [E | E]; [rewrite E; exact Hf2 | exact E] | exact HR].
Qed.
Lemma tj_baseX_fx : forall (cx : tjcx) (fx' : YK11.FPState),
tj_baseX B IMG cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 ->
tj_baseX B IMG (mkTJCX fx' (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) (c_t cx)
(c_now cx) (c_buf cx) (c_cap cx) (c_Nb cx) (c_T cx) (c_fpos cx) (c_sp1 cx) (c_E0 cx)).
Proof.
intros cx fx' HB Hc. unfold tj_baseX in *.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in *.
repeat match type of HB with _ /\ _ => let H := fresh "H" in destruct HB as [H HB]; split; [exact H|] end.
exact Hc.
Qed.
Lemma tj_from0_at_fx : forall ss INV, tj_from0 B IMG ss INV ->
forall (cx : tjcx) (fx' : YK11.FPState) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
(forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx') r = Sem.reg_get (@fp_regs (c_fq cx)) r) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 ->
tj_baseX B IMG cx -> tj_EX cx E ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (2, c_fpos cx) :: frames (c_S cx) ->
INV (mkTJCX fx' (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) (c_t cx)
(c_now cx) (c_buf cx) (c_cap cx) (c_Nb cx) (c_T cx) (c_fpos cx) (c_sp1 cx) (c_E0 cx)) E k ly3 S3 W3 ms3 md3 ->
st_ok_pi (fx := fx') SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (tj_postX B cx).
Proof.
intros ss INV HF cx fx' E k ly3 S3 W3 ms3 md3 Hf1 Hf2 HB HX HJ HFR HI HS.
eapply SRr_mono;
[exact (HF (mkTJCX fx' (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) (c_t cx)
(c_now cx) (c_buf cx) (c_cap cx) (c_Nb cx) (c_T cx) (c_fpos cx) (c_sp1 cx) (c_E0 cx)) E k ly3 S3 W3 ms3 md3 (tj_baseX_fx cx fx' HB Hf2) HX HJ HFR HI HS)|].
intros W' c' _ H. exact (tj_postX_fx cx fx' W' c' Hf1 Hf2 H).
Qed.
Lemma st_ok_pi_restrict_fx : forall (fx1 fx2 : YK11.FPState) (H : word -> bool) E ss regs pc mem rom,
st_ok_pi (fx := fx1) SEGS VAL E ss (restrict H (@mkst fx1 regs pc mem rom)) ->
st_ok_pi (fx := fx2) SEGS VAL E ss (restrict H (@mkst fx2 regs pc mem rom)).
Proof.
intros fx1 fx2 H E ss regs pc mem rom HS. unfold st_ok_pi in *.
destruct HS as (_ & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
End h.
End f.
End d.
