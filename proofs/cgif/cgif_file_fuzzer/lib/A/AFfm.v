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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable W : world tfibsegs.
Lemma memset_stretch : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFIB_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ apply store_ok_of_all; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); [lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(pose proof (u64_range x); unfold TFIB_IMG_END in *; lia) (Hpres (bv_unsigned x) ltac:(lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
destruct (tfib_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfibsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia) SOK
ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. f_equal. rewrite Z.add_0_r.
change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by lia. change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [lia|]. symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [lia | exact Hrpc]. }
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [rewrite H10', H10; reflexivity|].
apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact H10'.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1 bs. rewrite wbytes_repeat_spec by (rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia).
rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma memset_stretch_nw : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFIB_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ apply store_ok_of_all; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); [lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(pose proof (u64_range x); unfold TFIB_IMG_END in *; lia) (Hpres (bv_unsigned x) ltac:(lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
destruct (tfib_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfibsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia) SOK
ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. f_equal. rewrite Z.add_0_r.
change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by lia. change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [lia|]. symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [lia | exact Hrpc]. }
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [rewrite H10', H10; reflexivity|].
apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact H10'.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1 bs. rewrite wbytes_repeat_spec by (rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia).
rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
End e.
End c.
