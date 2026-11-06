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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e. Context {imgk : img}.
Variable W : world tfxsegs.
Lemma memset_stretch : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ img_apply store_ok_of_all; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); [img_lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(img_try (pose proof (u64_range x); unfold TFX_IMG_END in *; img_lia)) (Hpres (bv_unsigned x) ltac:(img_lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. img_exact Hw. }
destruct (tfx_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfxsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)) SOK
ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (img_try ((subst bs; cbv beta); rewrite repeat_length; img_lia)).
eapply (SRr_msteps tfxsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by img_lia. f_equal. rewrite Z.add_0_r.
img_change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by img_lia. img_change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [img_lia|]. symmetry. img_apply Znumtheory.Zdivide_mod. img_apply (Z.divide_trans _ 4); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_lia | img_try (img_exact Hrpc)]. }
img_change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [img_try (rewrite H10', H10; img_refl)|].
img_apply Hfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- img_exact H10'.
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H W x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
(subst m1full; cbv beta). unfold munrestrict. rewrite Hh. (subst m1 bs; cbv beta). rewrite wbytes_repeat_spec by (img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)).
rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [img_refl|].
symmetry. img_apply andb_true_intro. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia.
Qed.
Lemma memset_stretch_nw : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ img_apply store_ok_of_all; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); [img_lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(img_try (pose proof (u64_range x); unfold TFX_IMG_END in *; img_lia)) (Hpres (bv_unsigned x) ltac:(img_lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. img_exact Hw. }
destruct (tfx_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfxsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)) SOK
ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (img_try ((subst bs; cbv beta); rewrite repeat_length; img_lia)).
eapply (SRr_msteps tfxsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by img_lia. f_equal. rewrite Z.add_0_r.
img_change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by img_lia. img_change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [img_lia|]. symmetry. img_apply Znumtheory.Zdivide_mod. img_apply (Z.divide_trans _ 4); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_lia | img_try (img_exact Hrpc)]. }
img_change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [img_try (rewrite H10', H10; img_refl)|].
img_apply Hfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- img_exact H10'.
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H W x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
(subst m1full; cbv beta). unfold munrestrict. rewrite Hh. (subst m1 bs; cbv beta). rewrite wbytes_repeat_spec by (img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)).
rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [img_refl|].
symmetry. img_apply andb_true_intro. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia.
Qed.
End e.
End c.
