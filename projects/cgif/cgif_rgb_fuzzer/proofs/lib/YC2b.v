(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC2o YC0x YC17 YC1b YC2u YC1z YC1y YC29.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition bval (rd : Z -> option Z) (a : Z) : Z := match rd a with Some v => v | None => 0 end.

Section WS.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis TCMP : tcmp_spec B.
Definition wscr (sp1 a : Z) : Prop :=
(sp1 + 88 <= a < sp1 + 96) \/ (sp1 + 152 <= a < sp1 + 160) \/ (sp1 + 160 <= a < sp1 + 168) \/ (sp1 + 168 <= a < sp1 + 176) \/
(sp1 + 184 <= a < sp1 + 192) \/ (sp1 + 192 <= a < sp1 + 200) \/ (sp1 + 216 <= a < sp1 + 224).
Definition wkept (lyc : alayout) (Sc : astate) (W : world trasegs) (sp1 : Z) (memc m : word -> option byte) : Prop :=
acall_kept trasegs B lyc Sc W memc W m (sp1 - TCMP_STK) (sp1 + 232) (fun _ => False) /\
(forall a, sp1 <= a < sp1 + 232 -> ~ wscr sp1 a -> aview trasegs (w_H W) m a = aview trasegs (w_H W) memc a).
Lemma wkept_trans : forall lyc Sc W sp1 m0 m1 m2, wkept lyc Sc W sp1 m0 m1 -> wkept lyc Sc W sp1 m1 m2 -> wkept lyc Sc W sp1 m0 m2.
Proof.
intros lyc Sc W sp1 m0 m1 m2 [K1 X1] [K2 X2]. split; [exact (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1 K2)|].
intros a Ha Hs. rewrite (X2 a Ha Hs). exact (X1 a Ha Hs).
Qed.
Lemma wkept_refl : forall lyc Sc W sp1 m, (forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) m a) -> wkept lyc Sc W sp1 m m.
Proof.
intros lyc Sc W sp1 m Hp. split; [|intros; reflexivity].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros a _ _ H; exact H | exact Hp].
Qed.
Lemma wkept_of_run : forall E rs lyc Sc W (m m' : word -> option byte) md sp1,
AR trasegs B lyc Sc W m md ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, in_wrange E rs a -> wscr sp1 a) -> alloc_ceiling <= sp1 - TCMP_STK -> sp1 + 232 <= 2 ^ 64 ->
(forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) m a) ->
wkept lyc Sc W sp1 m m'.
Proof.
intros E rs lyc Sc W m m' md sp1 HAR HFr HG Hw Hceil Hhi Hp. assert (WSz : TCMP_STK = 4112) by reflexivity. split.
- apply (acall_kept_of_run B LAWS E rs lyc Sc W m m' md _ _ (fun _ => False) HAR HFr HG); [| intros a [] | exact Hceil | exact Hp].
intros a Ha. right. pose proof (Hw a Ha) as Hs. unfold wscr in Hs. rewrite WSz. lia.
- intros a Ha Hs. apply (aview_kept_out E rs _ m m' HFr a); [|intros Hin; exact (Hs (Hw a Hin))].
pose proof asan_consts as (C1 & _). rewrite WSz in Hceil. lia.
Qed.
Lemma wkept_of_cmp : forall lyc Sc W (m m' : word -> option byte) md md' sp1,
ajournal trasegs B TCMP_STK sp1 [] lyc Sc W m md [] lyc Sc W m' md' 0 -> AR trasegs B lyc Sc W m md ->
(forall a, sp1 <= a < sp1 + 232 -> apresent (w_H W) m' a) ->
wkept lyc Sc W sp1 m m'.
Proof.
intros lyc Sc W m m' md md' sp1 HJ HAR Hp.
pose proof (acall_kept_of_journal trasegs B tra_segs_low TCMP_STK sp1 [] [] lyc Sc W m md lyc Sc W m' md' 0 (fun _ => False) HJ HAR
ltac:(intros a (r & Hr & _); destruct Hr) ltac:(intros b mm i Hb _ _; exact Hb)) as K.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _). pose proof asan_consts as (C1 & _).
assert (WSz : TCMP_STK = 4112) by reflexivity. rewrite WSz in *.
split.
- apply (acall_kept_band B _ _ _ _ _ _ _ _ _ _ K); [lia | lia |].
intros a Ha. destruct (Z_lt_le_dec a sp1); [pose proof K as (_ & _ & _ & _ & _ & K6); apply K6; lia | apply Hp; lia].
- intros a Ha Hs. pose proof K as (K1 & _). apply K1; lia.
Qed.
Definition lkept (W : world trasegs) (sp1 : Z) (m m' : word -> option byte) : Prop :=
forall a, sp1 <= a < sp1 + 232 -> aview trasegs (w_H W) m' a = aview trasegs (w_H W) m a.
Lemma lkept_refl : forall W sp1 m, lkept W sp1 m m.
Proof. intros W sp1 m a _. reflexivity. Qed.
Lemma lkept_trans : forall W sp1 m0 m1 m2, lkept W sp1 m0 m1 -> lkept W sp1 m1 m2 -> lkept W sp1 m0 m2.
Proof. intros W sp1 m0 m1 m2 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma lkept_of_run_ro : forall E rs W (m m' : word -> option byte) sp1,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> (forall r, In r rs -> YQ0b.r_whi r <= YQ0b.r_wlo r) ->
0 <= sp1 -> sp1 + 232 <= 2 ^ 64 -> lkept W sp1 m m'.
Proof.
intros E rs W m m' sp1 HF Hro H0 H64 a Ha. apply (aview_kept_out E rs _ m m' HF a); [lia|].
intros (r & Hr & Hw). pose proof (Hro r Hr). lia.
Qed.
Lemma lkept_of_K : forall lyc Sc W (m m' : word -> option byte) slo sp1 Er,
acall_kept trasegs B lyc Sc W m W m' slo sp1 Er -> alloc_ceiling <= sp1 -> sp1 + 232 <= 2 ^ 64 -> lkept W sp1 m m'.
Proof. intros lyc Sc W m m' slo sp1 Er (K1 & _) Hc H64 a Ha. apply K1; lia. Qed.
Lemma val_mem_lkept : forall W sp1 (m m' : word -> option byte) a n v,
lkept W sp1 m m' -> sp1 <= a -> a + Z.of_nat n <= sp1 + 232 ->
val_mem trasegs (mrestrict (w_H W) m) a n v -> val_mem trasegs (mrestrict (w_H W) m') a n v.
Proof. intros W sp1 m m' a n v L H1 H2 Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview trasegs). apply L. lia. Qed.
Lemma val_mem_run_out : forall E rs (W : world trasegs) (m m' : word -> option byte) a n v,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall k, a <= k < a + Z.of_nat n -> ~ in_wrange E rs k) ->
val_mem trasegs (mrestrict (w_H W) m) a n v -> val_mem trasegs (mrestrict (w_H W) m') a n v.
Proof.
intros E rs W m m' a n v HF H0 H64 Hno Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview trasegs).
apply (aview_kept_out E rs _ m m' HF); [lia | apply Hno; lia].
Qed.
Lemma obj_at_wkept : forall lyc Sc W sp1 (m m' : word -> option byte) b sz lay vals,
wkept lyc Sc W sp1 m m' -> In (b, sz) (ablocks B lyc Sc) -> lay_inside lay (req_size sz) = true ->
obj_at trasegs (mrestrict (w_H W) m) b lay vals -> obj_at trasegs (mrestrict (w_H W) m') b lay vals.
Proof. intros lyc Sc W sp1 m m' b sz lay vals [K _] Hin Hl Ho. eapply (obj_at_keptK B _ _ _ _ _ _ _ _ b sz); [exact K | exact Hin | exact Hl | intros i _ [] | exact Ho]. Qed.
Lemma val_mem_wkept : forall lyc Sc W sp1 (m m' : word -> option byte) off v,
wkept lyc Sc W sp1 m m' -> 0 <= sp1 -> sp1 + 280 <= 2 ^ 64 -> alloc_ceiling <= sp1 ->
0 <= off -> off + 8 <= 280 -> (forall k, 0 <= k < 8 -> ~ wscr sp1 (sp1 + off + k)) ->
val_mem trasegs (mrestrict (w_H W) m) (sp1 + off) 8 v -> val_mem trasegs (mrestrict (w_H W) m') (sp1 + off) 8 v.
Proof.
intros lyc Sc W sp1 m m' off v [K X] H0 H64 Hc Ho1 Ho2 Hns Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview trasegs).
cbn [Z.of_nat] in Hkk.
destruct (Z_lt_le_dec (off + Z.of_nat kk) 232).
- apply X; [lia | replace (sp1 + off + Z.of_nat kk) with (sp1 + off + Z.of_nat kk) by lia; apply Hns; lia].
- pose proof K as (K1 & _). apply K1; lia.
Qed.
Lemma achain_wkept : forall lyc Sc W sp1 (m m' : word -> option byte) v ch,
wkept lyc Sc W sp1 m m' -> achain lyc (aview trasegs (w_H W) m) sp1 v ch -> sp1 + 248 <= v -> alloc_ceiling <= sp1 -> ly_top lyc <= 2 ^ 64 ->
achain lyc (aview trasegs (w_H W) m') sp1 v ch.
Proof. intros lyc Sc W sp1 m m' v ch [K _] Hch Hv Hc Ht. eapply (achain_keptK2 B); [exact K | exact Hch | lia | lia | lia | exact Ht]. Qed.
Lemma wimg_byte : forall lyc Sc W sp1 (memc m : word -> option byte) md b n p,
wkept lyc Sc W sp1 memc m -> AR trasegs B lyc Sc W m md -> In (b, n) (ablocks B lyc Sc) -> 0 <= p < n ->
val_mem trasegs (mrestrict (w_H W) m) (b + p) 1 (bval (aview trasegs (w_H W) memc) (b + p)) /\
0 <= bval (aview trasegs (w_H W) memc) (b + p) < 256.
Proof.
intros lyc Sc W sp1 memc m md b n p [K _] HAR Hin Hp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin) as (_ & _ & _ & _ & Hpres & _). pose proof (req_size_pos' n ltac:(lia)) as [_ Hrn].
destruct (val_mem_byte1 (w_H W) m (b + p) (proj1 (Hpres (b + p) ltac:(lia)))) as (v & Rv & Vv).
pose proof K as (_ & K2 & _). pose proof (K2 b n p Hin ltac:(lia) (fun H : False => H)) as Eq.
assert (Hb : aview trasegs (w_H W) memc (b + p) = Some v).
{ rewrite <- Eq. unfold aview. pose proof (Vv 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. rewrite V0. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. change (bv_modulus 8) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia. }
unfold bval. rewrite Hb. split; [exact Vv | exact Rv].
Qed.
Section d.
Variables (W : world trasegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z).
Definition wctx : Prop :=
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memc mdc k /\
In (fimg, Nb) (ablocks B lyc Sc) /\ In (bimg, Nb) (ablocks B lyc Sc) /\ 1 <= Nb < 2 ^ 32 /\ (fimg + Nb <= bimg \/ bimg + Nb <= fimg) /\
In (g, CGIF_SIZE) (ablocks B lyc Sc) /\ In (cfp, FRAME_SIZE) (ablocks B lyc Sc) /\ In (bfp, FRAME_SIZE) (ablocks B lyc Sc) /\ cfp <> bfp /\
obj_at trasegs (mrestrict (w_H W) memc) g LAY_CGIF gvals /\ nth_error gvals CG_pal = Some gpal /\ nth_error gvals CG_ngp = Some ngp /\
obj_at trasegs (mrestrict (w_H W) memc) cfp LAY_Frame cvals /\ nth_error cvals FR_lpal = Some cpal /\ nth_error cvals FR_attr = Some cattr /\
nth_error cvals FR_nlp = Some cnlp /\ nth_error cvals FR_ctidx = Some ctidx /\
obj_at trasegs (mrestrict (w_H W) memc) bfp LAY_Frame bvals /\ nth_error bvals FR_lpal = Some bpal /\ nth_error bvals FR_attr = Some battr /\
nth_error bvals FR_nlp = Some bnlp /\ nth_error bvals FR_ctidx = Some btidx /\
(Z.land cattr 1 <> 0 -> exists Nl, In (cpal, Nl) (ablocks B lyc Sc) /\ 3 * cnlp <= Nl) /\
(Z.land battr 1 <> 0 -> exists Nl, In (bpal, Nl) (ablocks B lyc Sc) /\ 3 * bnlp <= Nl) /\
(Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> exists Np, In (gpal, Np) (ablocks B lyc Sc) /\ 3 * ngp <= Np) /\
spZ regs = sp1 /\ sp0 - 400 <= sp1 <= sp0 - 384 /\ sp1 mod 16 = 0 /\
getr regs 9 = Z_to_bv 64 sp1 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
achain lyc (aview trasegs (w_H W) memc) sp1 (s0Z regs) ch1 /\ s0Z regs = sp0 /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 240) 8 SB /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 248) 8 bfp.
Hypothesis HC : wctx.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp).
Definition PD (p : Z) : Prop :=
~ tcmp_zero (aview trasegs (w_H W) memc) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
(bval (aview trasegs (w_H W) memc) (fimg + p)) (bval (aview trasegs (w_H W) memc) (bimg + p)).
Lemma pal_entry_kept : forall (m : word -> option byte) attr lpal nlp idx,
wkept lyc Sc W sp1 memc m ->
(Z.land attr 1 <> 0 -> exists Nl, In (lpal, Nl) (ablocks B lyc Sc) /\ 3 * nlp <= Nl) ->
(Z.land attr 1 = 0 -> exists Np, In (gpal, Np) (ablocks B lyc Sc) /\ 3 * ngp <= Np) ->
0 <= idx < tsel attr nlp ngp ->
forall i, 0 <= i < 3 -> aview trasegs (w_H W) m (tsel attr lpal gpal + 3 * idx + i) = aview trasegs (w_H W) memc (tsel attr lpal gpal + 3 * idx + i).
Proof.
intros m attr lpal nlp idx [K _] HL HG Hidx i Hi. pose proof K as (_ & K2 & _). unfold tsel in *.
destruct (Z.eqb_spec (Z.land attr 1) 0) as [E0 | E1].
- destruct (HG E0) as (Np & Hin & Hsz). pose proof (req_size_pos' Np ltac:(lia)) as [_ Hr].
replace (gpal + 3 * idx + i) with (gpal + (3 * idx + i)) by lia. apply (K2 gpal Np (3 * idx + i) Hin); [lia | intros []].
- destruct (HL E1) as (Nl & Hin & Hsz). pose proof (req_size_pos' Nl ltac:(lia)) as [_ Hr].
replace (lpal + 3 * idx + i) with (lpal + (3 * idx + i)) by lia. apply (K2 lpal Nl (3 * idx + i) Hin); [lia | intros []].
Qed.
Lemma tcmp_zero_wkept : forall (m : word -> option byte) iCur iBef,
wkept lyc Sc W sp1 memc m -> 0 <= iCur -> 0 <= iBef ->
tcmp_zero (aview trasegs (w_H W) m) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx iCur iBef <->
tcmp_zero (aview trasegs (w_H W) memc) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx iCur iBef.
Proof.
intros m iCur iBef WK RiC RiB. wctx_names. unfold tcmp_zero.
split; intros [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H | right | left; exact H | right]; repeat (split; [assumption|]); intros i Hi.
- rewrite <- (pal_entry_kept m battr bpal bnlp iBef WK HLb (fun E0 => HGp (or_intror E0)) ltac:(lia) i Hi).
rewrite <- (pal_entry_kept m cattr cpal cnlp iCur WK HLc (fun E0 => HGp (or_introl E0)) ltac:(lia) i Hi). apply H5. exact Hi.
- rewrite (pal_entry_kept m battr bpal bnlp iBef WK HLb (fun E0 => HGp (or_intror E0)) ltac:(lia) i Hi).
rewrite (pal_entry_kept m cattr cpal cnlp iCur WK HLc (fun E0 => HGp (or_introl E0)) ltac:(lia) i Hi). apply H5. exact Hi.
Qed.
Lemma cmp_callW : forall (regsT : bvmap 5 word) memT mdT (p : Z) (raw : word),
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memT mdT k -> wkept lyc Sc W sp1 memc memT ->
0 <= p < Nb ->
spZ regsT = sp1 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> s0Z regsT = sp0 ->
getr regsT 10 = Z_to_bv 64 g -> getr regsT 11 = Z_to_bv 64 cfp -> getr regsT 12 = Z_to_bv 64 bfp ->
getr regsT 13 = Z_to_bv 64 (bval (aview trasegs (w_H W) memc) (fimg + p)) ->
getr regsT 14 = Z_to_bv 64 (bval (aview trasegs (w_H W) memc) (bimg + p)) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
SRr trasegs W (mkCfg (mkst regsT (Z_to_bv 64 A_cmpPixel) memT (seg_rom trasegs)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\ (v = w64 0 <-> ~ PD p) /\
wkept lyc Sc W sp1 memc mem2 /\
acall_kept trasegs B lyc Sc W memT W mem2 (sp1 - TCMP_STK) sp1 (fun _ => False) /\ lkept W sp1 memT mem2).
Proof.
intros regsT memT mdT p raw HJT WK Hp Qsp Qgp Qtp Qs0 Q10 Q11 Q12 Q13 Q14 Qra Hraw Hra4. wctx_names.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJT as (HART & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpresT & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (FFS : TFLUSH_STK = 17440) by reflexivity. assert (WS : TCMP_STK = 4112) by reflexivity.
destruct (wimg_byte lyc Sc W sp1 memc memT mdT fimg Nb p WK HART Hfi Hp) as [_ RbC].
destruct (wimg_byte lyc Sc W sp1 memc memT mdT bimg Nb p WK HART Hbi Hp) as [_ RbB].
eapply SRr_mono.
{ eapply (aj_call_sp B LAWS W regsT memT _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc mdT k TCMP_STK [] 0 (sp1 - sp0) raw ch1
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc /\ W2 = W /\ exists v : word, getr regs2 10 = v /\
(v = w64 0 <-> tcmp_zero (aview trasegs (w_H W) memT) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
(bval (aview trasegs (w_H W) memc) (fimg + p)) (bval (aview trasegs (w_H W) memc) (bimg + p)))) HJT).
- rewrite Qsp. lia.
- rewrite Zminus_mod, Hsp1al, Hal16. reflexivity.
- lia. - rewrite WS. lia. - rewrite WS, FFS. lia.
- exact Qgp. - exact Qtp. - exact Qra. - exact Hraw. - exact Hra4.
- rewrite Qs0. replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite <- Hs0.
eapply achain_wkept; [exact WK | exact Hch | rewrite Hs0; lia | lia | lia].
- intros HPRE1. eapply SRr_mono.
+ eapply (TCMP lyc Sc W regsT memT mdT ch1 g cfp bfp _ _ gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HPRE1
Q10 Q11 Q12 Q13 Q14 RbC RbB Hg Hcf Hbf Hcb).
* eapply obj_at_wkept; [exact WK | exact Hg | vm_compute; reflexivity | exact Og].
* exact Ogpal. * exact Ongp.
* eapply obj_at_wkept; [exact WK | exact Hcf | vm_compute; reflexivity | exact Oc].
* exact Ocpal. * exact Ocattr. * exact Ocnlp. * exact Octidx.
* eapply obj_at_wkept; [exact WK | exact Hbf | vm_compute; reflexivity | exact Ob].
* exact Obpal. * exact Obattr. * exact Obnlp. * exact Obtidx.
* exact HLc. * exact HLb. * exact HGp.
+ cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJx & HPx & Hv & Hz).
exists lyc, Sc, regs2, mem2, md2. split; [rewrite Qra; reflexivity|]. split; [exact HJx|]. split; [exact HPx|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists v. split; [exact Hv | exact Hz].
- intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJx & HP2 & -> & -> & -> & v & Hv & Hz).
rewrite Z.add_0_r in HJ2. replace (sp0 + (sp1 - sp0)) with sp1 in HJx by lia.
assert (WK2 : wkept lyc Sc W sp1 memT mem2).
{ eapply wkept_of_cmp; [exact HJx | exact HART |].
intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. rewrite FFS. lia. }
split; [reflexivity|]. exists regs2, mem2, md2, v. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
pose proof (acall_kept_of_journal trasegs B tra_segs_low TCMP_STK sp1 [] [] lyc Sc W memT mdT lyc Sc W mem2 md2 0 (fun _ => False) HJx HART
ltac:(intros a (r & Hr & _); destruct Hr) ltac:(intros b mm i Hb _ _; exact Hb)) as Kc.
split; [| split; [exact (wkept_trans _ _ _ _ _ _ _ WK WK2) | split; [exact Kc | apply (lkept_of_K _ _ _ _ _ _ _ _ Kc); lia]]].
rewrite Hz. unfold PD. rewrite (tcmp_zero_wkept memT _ _ WK (proj1 RbC) (proj1 RbB)). split; [intros X Y; exact (Y X)|].
intros X. destruct (Classical_Prop.classic (tcmp_zero (aview trasegs (w_H W) memc) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
(bval (aview trasegs (w_H W) memc) (fimg + p)) (bval (aview trasegs (w_H W) memc) (bimg + p)))) as [Y|Y]; [exact Y | exfalso; exact (X Y)].
Qed.
End d.
End WS.
End c.
