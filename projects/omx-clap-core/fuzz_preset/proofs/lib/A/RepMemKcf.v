(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepMemKcf.v (commit eb934de95d13, blob 0c256991b509) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 6 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB15.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB14 AE38.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YE2i YK0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pres_unhidden : forall (H : word -> bool) mem a, apresent H mem a -> H (Z_to_bv 64 a) = false.
Proof. intros H mem a [Hh _]. exact Hh. Qed.
Lemma pres_wview : forall (H : word -> bool) mem a, apresent H mem a -> wview tfibsegs (mrestrict H mem) (Z_to_bv 64 a) <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma pres_store_ok : forall (H : word -> bool) mem d len, 0 <= d -> 0 <= len -> d + len < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent H mem a) ->
store_ok tfibsegs (mrestrict H mem) (Z_to_bv 64 d) (Z.to_nat len) = true.
Proof.
intros H mem d len H0 H1 H2 HP. apply store_ok_of_all; rewrite unsigned_lit_small by lia; [lia|]. intros x Hx.
pose proof (pres_wview H mem (bv_unsigned x) (HP (bv_unsigned x) ltac:(lia))) as Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
Qed.
Lemma ret_ok_of_mod2 : forall retpc, retpc mod 2 = 0 -> 0 <= retpc < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 retpc).
Proof. intros retpc H1 H2. apply YK0s.ret_ok_even. rewrite unsigned_lit_small by lia. exact H1. Qed.
Lemma rdn1_of_mbyte : forall (m : word -> option byte) a b, mbyte tfibsegs m a = Some b -> rdn tfibsegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros m a b H. cbn [rdn]. unfold mbyte in H.
destruct (m (Z_to_bv 64 a)) as [b'|]; [inversion H; reflexivity | rewrite H; reflexivity].
Qed.
Lemma imemset_stretch_gen : forall (W : world tfibsegs) (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x64ab8 ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 0 -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> 0 <= d -> d + len < 2 ^ 64 -> (forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
retpc mod 2 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr (ms_regs ms) r) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 0)) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hlen Hd Hdl HPRES Hrpc Hrpc' Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true) by (apply pres_store_ok; assumption).
assert (RET : YK0s.ret_ok (Z_to_bv 64 retpc)) by (apply ret_ok_of_mod2; assumption).
destruct (tfib_imemset mr (Z_to_bv 64 d) (Z_to_bv 64 0) len (seg_rom tfibsegs) (ms_regs ms) (Z_to_bv 64 retpc)
Hlen ltac:(rewrite unsigned_lit_small by lia; lia) SOK ltac:(intros _ _; rewrite unsigned_lit_small by lia; lia) RET H1 H10 H11 H12)
as (regs' & Hms & Hagree).
change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hms.
set (bs := repeat (Z_to_bv 8 0) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q).
{ rewrite restrict_mkst_fx. change (Z_to_bv 64 412344) with (Z_to_bv 64 (bv_unsigned tfib_imemset_entry)). rewrite Z_to_bv_bv_unsigned. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by lia; lia.
- apply wbytes_above; rewrite unsigned_lit_small by lia; lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
assert (Hfr : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr (ms_regs ms) r).
{ intros r N1 N2 N3. apply Hagree. unfold imemset_clob. cbn. intros [X|[X|[X|[]]]]; congruence. }
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr. apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact (eq_trans (Hfr 10%bv ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) H10).
- exact Hfr.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros x Hx. pose proof (pres_unhidden (w_H W) (ms_mem ms) (bv_unsigned x) (HPRES (bv_unsigned x) Hx)) as Hh. rewrite Z_to_bv_bv_unsigned in Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1 bs. rewrite wbytes_repeat_spec by (rewrite unsigned_lit_small by lia; lia).
rewrite unsigned_lit_small by lia.
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma imemcpy_stretch_gen : forall (W : world tfibsegs) (k : nat) (E : env) ss ms md (d s n retpc : Z) (bs : list byte) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x64a3c ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 s -> getr (ms_regs ms) 12 = Z_to_bv 64 n -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
Z.of_nat (length bs) = n -> 0 <= d -> d + n < 2 ^ 64 -> 0 <= s -> s + n < 2 ^ 64 -> (s + n <= d \/ d + n <= s) ->
(forall a, d <= a < d + n -> apresent (w_H W) (ms_mem ms) a) ->
(forall j, (j < length bs)%nat -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (s + Z.of_nat j) = Some (nth j bs (Z_to_bv 8 0))) ->
retpc mod 2 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + n <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr (ms_regs ms) r) ->
(forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall j, (j < length bs)%nat -> mem' (Z_to_bv 64 (d + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W k E ss ms md d s n retpc bs Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hn Hd Hdn Hs Hsn Hdisj HPRES HSRC Hrpc Hrpc' Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (CPY : cpyH tfibsegs mr (Z_to_bv 64 d) (Z_to_bv 64 s) n bs).
{ constructor.
- lia.
- lia.
- exact (YE2i.rdn_of_mbytes tfibsegs mr bs s HSRC).
- replace (length bs) with (Z.to_nat n) by lia. apply pres_store_ok; [lia | lia | lia | exact HPRES].
- rewrite !unsigned_lit_small by lia. lia.
- rewrite unsigned_lit_small by lia. lia.
- rewrite unsigned_lit_small by lia. lia. }
assert (RET : YK0s.ret_ok (Z_to_bv 64 retpc)) by (apply ret_ok_of_mod2; assumption).
destruct (AB14.tfib_imemcpy mr (Z_to_bv 64 d) (Z_to_bv 64 s) n bs (seg_rom tfibsegs) (ms_regs ms) (Z_to_bv 64 retpc) CPY RET H1 H10 H11 H12)
as (regs' & Hms & Hagree).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q).
{ rewrite restrict_mkst_fx. change (Z_to_bv 64 412220) with (Z_to_bv 64 (bv_unsigned AB14.tfib_imemcpy_entry)). rewrite Z_to_bv_bv_unsigned. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + n) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by lia; lia.
- apply wbytes_above; rewrite unsigned_lit_small by lia; lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
assert (Hfr : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr (ms_regs ms) r).
{ intros r N1 N2 N3 N4. apply Hagree. unfold AB14.imemcpy_clob. cbn. intros [X|[X|[X|[X|[]]]]]; congruence. }
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr. apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact (eq_trans (Hfr 10%bv ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) H10).
- exact Hfr.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros j Hj. pose proof (pres_unhidden (w_H W) (ms_mem ms) (d + Z.of_nat j) (HPRES (d + Z.of_nat j) ltac:(lia))) as Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1.
pose proof (YK0e.AX2S.wbytes_nth bs mr (Z_to_bv 64 d) j) as WN. rewrite unsigned_lit_small in WN by lia. apply WN; lia.
Qed.
Definition srcbyte (m : word -> option byte) (a : Z) : byte := match m (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end.
Definition srcbytes (m : word -> option byte) (s n : Z) : list byte := map (fun j => srcbyte m (s + Z.of_nat j)) (seq 0 (Z.to_nat n)).
Lemma srcbytes_length : forall m s n, length (srcbytes m s n) = Z.to_nat n.
Proof. intros m s n. unfold srcbytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma srcbytes_nth : forall m s n j, (j < Z.to_nat n)%nat -> nth j (srcbytes m s n) (Z_to_bv 8 0) = srcbyte m (s + Z.of_nat j).
Proof.
intros m s n j Hj. unfold srcbytes.
rewrite (nth_indep _ (Z_to_bv 8 0) ((fun j0 => srcbyte m (s + Z.of_nat j0)) 0%nat)) by (rewrite length_map, length_seq; exact Hj).
rewrite (map_nth (fun j0 => srcbyte m (s + Z.of_nat j0))), seq_nth by exact Hj. reflexivity.
Qed.
Lemma imemcpy_stretch_gen_pres : forall (W : world tfibsegs) (k : nat) (E : env) ss ms md (d s n retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x64a3c ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 s -> getr (ms_regs ms) 12 = Z_to_bv 64 n -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= n -> 0 <= d -> d + n < 2 ^ 64 -> 0 <= s -> s + n < 2 ^ 64 -> (s + n <= d \/ d + n <= s) ->
(forall a, d <= a < d + n -> apresent (w_H W) (ms_mem ms) a) ->
(forall i, 0 <= i < n -> apresent (w_H W) (ms_mem ms) (s + i)) ->
retpc mod 2 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + n <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr (ms_regs ms) r) ->
(forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall i, 0 <= i < n -> mem' (Z_to_bv 64 (d + i)) = ms_mem ms (Z_to_bv 64 (s + i))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W k E ss ms md d s n retpc Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hn0 Hd Hdn Hs Hsn Hdisj HPRES HSRC Hrpc Hrpc' Hext Hext64 HK.
assert (Hlen : Z.of_nat (length (srcbytes (ms_mem ms) s n)) = n) by (rewrite srcbytes_length; lia).
apply (imemcpy_stretch_gen W k E ss ms md d s n retpc (srcbytes (ms_mem ms) s n) Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hlen Hd Hdn Hs Hsn Hdisj HPRES);
[ | exact Hrpc | exact Hrpc' | exact Hext | exact Hext64 | ].
- intros j Hj. rewrite srcbytes_length in Hj. rewrite srcbytes_nth by exact Hj.
destruct (HSRC (Z.of_nat j) ltac:(lia)) as [Hh [b Hb]]. unfold mbyte, mrestrict, srcbyte. rewrite Hh, Hb. reflexivity.
- intros regs' mem' mat' HS' R10 Hfr Hout Hpres Hin. apply (HK regs' mem' mat' HS' R10 Hfr Hout Hpres).
intros i Hi. assert (Hj : (Z.to_nat i < length (srcbytes (ms_mem ms) s n))%nat) by (rewrite srcbytes_length; lia).
specialize (Hin _ Hj). rewrite srcbytes_nth in Hin by lia. rewrite Z2Nat.id in Hin by lia. rewrite Hin.
destruct (HSRC i Hi) as [_ [b Hb]]. unfold srcbyte. rewrite Hb. reflexivity.
Qed.
Lemma istrlen_stretch_gen : forall (W : world tfibsegs) (k : nat) (E : env) ss ms md (p retpc : Z) (s : list byte) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x64c0c ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 p -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= p -> p + Z.of_nat (length s) + 1 < 2 ^ 64 -> ~ In (Z_to_bv 8 0) s ->
(forall j, (j <= length s)%nat -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (p + Z.of_nat j) = Some (nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) ->
retpc mod 2 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall regs' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [10; 11; 12]%bv))
(ss_after_stretch ss (ss_mem ss) k [10; 11; 12]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) (ms_mem ms) (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s)) ->
(forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr (ms_regs ms) r) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) (ms_mem ms) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W k E ss ms md p retpc s Q HS Hrv Hpc Hat Hnc H10 H1 Hp Hpn Hnul HRD Hrpc Hrpc' HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (RD : forall j, (j <= length s)%nat -> rdn tfibsegs mr (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 p) + Z.of_nat j)) 1 = Some [nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)]).
{ intros j Hj. rewrite (unsigned_lit_small p) by lia. apply rdn1_of_mbyte. exact (HRD j Hj). }
destruct (AE38.tfib_istrlen s (Z_to_bv 64 p) mr (seg_rom tfibsegs) (ms_regs ms) H10 Hnul RD ltac:(rewrite unsigned_lit_small by lia; lia))
as (regs' & Hms & Ha0 & Hfr).
assert (RET : YK0s.ret_ok (Z_to_bv 64 retpc)) by (apply ret_ok_of_mod2; assumption).
unfold YK0s.ret_ok in RET. rewrite H1, RET in Hms.
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q).
{ rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
subst mr. rewrite unrestrict_mkst_mrestrict.
apply (HK regs' (m_vm_materialized model')).
- rewrite restrict_mkst_fx.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' (mrestrict (w_H W) (ms_mem ms)) (ss_mem ss) retpc [10; 11; 12]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr. apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. split; [intros a Ha; reflexivity | intros a Ha Hw; exact Hw].
- exact Ha0.
- exact Hfr.
Qed.
End a.
