(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h YG0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YE01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF09 YF0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e. Context {imgk : img}.
Variable W : world tfxsegs.
Lemma rdn_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
exists bs, rdn tfxsegs m (Z_to_bv 64 a) nn = Some bs /\ length bs = nn.
Proof.
intros m nn. induction nn as [|nn IH]; intros a Hp Ha Hnw.
- exists []. split; img_refl.
- destruct (Hp 0 ltac:(img_lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [img_try (intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by img_lia; img_apply Hp; img_lia) | img_lia | img_lia |].
exists (b :: bs). split; [|img_try (cbn; img_lia)]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [img_try (rewrite Hbs; img_refl)|].
img_apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
img_change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. img_refl.
Qed.
Lemma store_ok_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
store_ok tfxsegs m (Z_to_bv 64 a) nn = true.
Proof.
intros m nn a Hp Ha Hnw. destruct nn as [|n']; [img_refl|].
img_apply store_ok_of_all; [img_try (rewrite unsigned_lit_small by img_lia; img_lia)|].
intros x Hx. rewrite unsigned_lit_small in Hx by img_lia.
destruct (Hp (bv_unsigned x - a) ltac:(img_lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by img_lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma cpyk_stretch : forall (k : nat) (E : env) ss ms md (d src len : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = (0x3462c + D_150) ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 22 = Z_to_bv 64 src -> getr (ms_regs ms) 25 = Z_to_bv 64 d -> getr (ms_regs ms) 10 = Z_to_bv 64 (src + len) ->
4 <= len -> len mod 4 = 0 -> 0 <= d -> d + len < 2 ^ 64 -> 0 <= src -> src + len < 2 ^ 64 ->
(d + len <= src \/ src + len <= d) ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, src <= a < src + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 22; 25]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 22; 25]%bv (0x34640 + D_150))
(restrict (w_H W) (mkst regs' (Z_to_bv 64 (0x34640 + D_150)) mem' (seg_rom tfxsegs))) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall j, 0 <= j < len -> mem' (w64 (d + j)) = ms_mem ms (w64 (src + j))) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 (0x34640 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d src len Q HS Hrv Hpc Hat Hnc H22 H25 H10 Hlen Hl4 Hd Hdl Hs Hsl Hdisj Hpd Hps Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
destruct (rdn_of_presentR mr (Z.to_nat len) src) as (bs & Hbs & Hbl);
[ img_try (intros i Hi; destruct (Hps (src + i) ltac:(img_lia)) as [Hh [b Hb]]; exists b; unfold mr, mrestrict; rewrite Hh; img_exact Hb)
| img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia) | img_lia |].
assert (HOK : mcH mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs).
{ img_apply MCH; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia) | img_lia | img_try (rewrite Hbl; img_exact Hbs) | | | |]; rewrite ?unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia)); try img_lia.
rewrite Hbl. img_apply store_ok_of_presentR; [|img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia)|img_lia].
intros i Hi. destruct (Hpd (d + i) ltac:(img_lia)) as [Hh [b Hb]]. exists b. unfold mr, mrestrict. rewrite Hh. img_exact Hb. }
destruct (tfx_cpy4k_run mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs (seg_rom tfxsegs) (ms_regs ms) HOK Hl4 Hlen H22 H25
ltac:(img_try (rewrite H10; unfold at_; rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia); img_refl)))
as (regs' & Hms & R22 & R25 & R10 & Rfr).
eapply (SRr_msteps tfxsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
img_change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 (0x34640 + D_150) : word) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 (0x34640 + D_150) : word) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia)); rewrite Hbl; img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) (0x34640 + D_150) [11; 22; 25]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
img_apply Rfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H W x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros j Hj. destruct (Hpd (d + j) ltac:(img_lia)) as [Hh _]. destruct (Hps (src + j) ltac:(img_lia)) as [Hh' [b' Hb']].
(subst m1full; cbv beta). unfold munrestrict, w64. rewrite Hh. (subst m1; cbv beta).
rewrite (wbytes_inside bs mr (Z_to_bv 64 d) (Z_to_bv 64 (d + j))) by (img_try (rewrite ?unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia); rewrite ?Hbl; img_lia)).
rewrite !unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia)). replace (Z.to_nat (d + j - d)) with (Z.to_nat j) by (img_try (f_equal; img_lia)).
pose proof (rdn_nth tfxsegs mr (Z.to_nat len) (Z_to_bv 64 src) bs (Z.to_nat j) Hbs ltac:(img_lia)) as R1.
replace (Z_to_bv 64 src + nat_to_word (Z.to_nat j))%bv with (Z_to_bv 64 (src + j)) in R1
by (img_try (img_apply bv_eq; rewrite bv_add_unsigned; unfold nat_to_word; rewrite !Z_to_bv_unsigned; unfold bv_wrap; img_change (bv_modulus 64) with (2 ^ 64);
rewrite Z2Nat.id, <- Z.add_mod, !Z.mod_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia); img_refl)).
cbn [rdn] in R1. (subst mr; cbv beta). unfold mrestrict in R1. rewrite Hh', Hb' in R1. cbn in R1. injection R1 as <-. rewrite Hb'. img_refl.
Qed.
End e.
End c.
