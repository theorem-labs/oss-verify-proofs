(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AF0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable W : world tfibsegs.
Lemma rdn_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
exists bs, rdn tfibsegs m (Z_to_bv 64 a) nn = Some bs /\ length bs = nn.
Proof.
intros m nn. induction nn as [|nn IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma store_ok_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
store_ok tfibsegs m (Z_to_bv 64 a) nn = true.
Proof.
intros m nn a Hp Ha Hnw. destruct nn as [|n']; [reflexivity|].
apply store_ok_of_all; [rewrite unsigned_lit_small by lia; lia|].
intros x Hx. rewrite unsigned_lit_small in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma cpyk_stretch : forall (k : nat) (E : env) ss ms md (d src len : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x34024 ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 22 = Z_to_bv 64 src -> getr (ms_regs ms) 25 = Z_to_bv 64 d -> getr (ms_regs ms) 10 = Z_to_bv 64 (src + len) ->
4 <= len -> len mod 4 = 0 -> 0 <= d -> d + len < 2 ^ 64 -> 0 <= src -> src + len < 2 ^ 64 ->
(d + len <= src \/ src + len <= d) ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, src <= a < src + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 22; 25]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 22; 25]%bv 0x34038)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 0x34038) mem' (seg_rom tfibsegs))) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall j, 0 <= j < len -> mem' (w64 (d + j)) = ms_mem ms (w64 (src + j))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 0x34038) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d src len Q HS Hrv Hpc Hat Hnc H22 H25 H10 Hlen Hl4 Hd Hdl Hs Hsl Hdisj Hpd Hps Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
destruct (rdn_of_presentR mr (Z.to_nat len) src) as (bs & Hbs & Hbl);
[ intros i Hi; destruct (Hps (src + i) ltac:(lia)) as [Hh [b Hb]]; exists b; unfold mr, mrestrict; rewrite Hh; exact Hb
| unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia | lia |].
assert (HOK : mcH mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs).
{ split; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia | lia | rewrite Hbl; exact Hbs | | | |]; rewrite ?unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia); try lia.
rewrite Hbl. apply store_ok_of_presentR; [|unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia|lia].
intros i Hi. destruct (Hpd (d + i) ltac:(lia)) as [Hh [b Hb]]. exists b. unfold mr, mrestrict. rewrite Hh. exact Hb. }
destruct (tfib_cpy4k_run mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs (seg_rom tfibsegs) (ms_regs ms) HOK Hl4 Hlen H22 H25
ltac:(rewrite H10; unfold at_; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia); reflexivity))
as (regs' & Hms & R22 & R25 & R10 & Rfr).
replace (Z_to_bv 64 213028 : word) with (0x34024%bv : word) by (apply bv_eq; reflexivity).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (0x34038 : word) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (0x34038 : word) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia); rewrite Hbl; lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
replace (0x34038%bv : word) with (Z_to_bv 64 0x34038 : word) by (apply bv_eq; reflexivity).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) 0x34038 [11; 22; 25]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
apply Rfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros j Hj. destruct (Hpd (d + j) ltac:(lia)) as [Hh _]. destruct (Hps (src + j) ltac:(lia)) as [Hh' [b' Hb']].
subst m1full. unfold munrestrict, w64. rewrite Hh. subst m1.
rewrite (wbytes_inside bs mr (Z_to_bv 64 d) (Z_to_bv 64 (d + j))) by (rewrite ?unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia); rewrite ?Hbl; lia).
rewrite !unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia). replace (Z.to_nat (d + j - d)) with (Z.to_nat j) by (f_equal; lia).
pose proof (rdn_nth tfibsegs mr (Z.to_nat len) (Z_to_bv 64 src) bs (Z.to_nat j) Hbs ltac:(lia)) as R1.
replace (Z_to_bv 64 src + nat_to_word (Z.to_nat j))%bv with (Z_to_bv 64 (src + j)) in R1
by (apply bv_eq; rewrite bv_add_unsigned; unfold nat_to_word; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Z2Nat.id, <- Z.add_mod, !Z.mod_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia); reflexivity).
cbn [rdn] in R1. subst mr. unfold mrestrict in R1. rewrite Hh', Hb' in R1. cbn in R1. injection R1 as <-. rewrite Hb'. reflexivity.
Qed.
End e.
End c.
