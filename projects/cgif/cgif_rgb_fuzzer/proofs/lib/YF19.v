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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFX_IMG_END, IAL_STK, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG in *.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rw_writable {imgk : img} : forall (m : word -> option byte) a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> writable_at tfxsegs m a.
Proof.
intros m a Ha. unfold writable_at. img_apply tfx_rw_window. rewrite unsigned_lit_small by img_lia. img_exact Ha.
Qed.
Lemma rw_unhidden {imgk : img} : forall (W : world tfxsegs) a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|img_refl]. exfalso.
img_apply (tfx_rw_rom a Ha). unfold seg_rom.
rewrite (memory_read1_hidden tfxsegs (w_H W) (w_Hoff W) _ E). img_refl.
Qed.
Lemma rw_store_ok {imgk : img} : forall (m : word -> option byte) d len, (0xa1000 + D_1000) <= d -> d + len <= (0x5ff000 + D_1000) -> 0 <= len ->
store_ok tfxsegs m (Z_to_bv 64 d) (Z.to_nat len) = true.
Proof.
intros m d len H1 H2 H3. img_apply store_ok_of_all; rewrite unsigned_lit_small by img_lia; [img_lia|]. intros x Hx.
pose proof (rw_writable m (bv_unsigned x) ltac:(img_lia)) as Hw. unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. img_exact Hw.
Qed.
Lemma imemset_stretch {imgk : img} : forall (W : world tfxsegs) (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = (0x64484 + D_2c4) ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 0 -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> (0xa1000 + D_1000) <= d -> d + len <= (0x5ff000 + D_1000) -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 12; 13]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr (ms_regs ms) r) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 0)) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms md) Q.
Proof.
intros W k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true) by (img_try (img_apply rw_store_ok; img_lia)).
assert (RET : YK0s.ret_ok (Z_to_bv 64 retpc)).
{ img_apply YK0s.ret_ok_even. rewrite unsigned_lit_small by img_lia. apply Znumtheory.Zmod_divide in Hrpc; [|img_lia]. img_apply Znumtheory.Zdivide_mod.
img_apply (Z.divide_trans _ 4); [img_try (exists 2; img_refl) | img_try (img_exact Hrpc)]. }
destruct (tfx_imemset mr (Z_to_bv 64 d) (Z_to_bv 64 0) len (seg_rom tfxsegs) (ms_regs ms) (Z_to_bv 64 retpc)
Hlen ltac:(img_try (rewrite unsigned_lit_small by img_lia; img_lia)) SOK ltac:(img_try (intros _ _; rewrite unsigned_lit_small by img_lia; img_lia)) RET H1 H10 H11 H12)
as (regs' & Hms & Hagree).
img_change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hms.
set (bs := repeat (Z_to_bv 8 0) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (img_try ((subst bs; cbv beta); rewrite repeat_length; img_lia)).
eapply (SRr_msteps tfxsegs Hwx W _ _ md Q).
{ rewrite restrict_mkst_fx. img_change (Z_to_bv 64 (410756 + D_2c4)) with (Z_to_bv 64 (bv_unsigned tfx_imemset_entry)). rewrite Z_to_bv_bv_unsigned. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
img_change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by img_lia; img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by img_lia; img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
assert (Hfr : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr (ms_regs ms) r).
{ intros r N1 N2 N3. img_apply Hagree. unfold imemset_clob. cbn. intros [X|[X|[X|[]]]]; congruence. }
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr. img_apply Hfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- img_exact (eq_trans (Hfr 10%bv ltac:(img_try (discriminate)) ltac:(img_try (discriminate)) ltac:(img_try (discriminate))) H10).
- img_exact Hfr.
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H W x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros x Hx. pose proof (rw_unhidden W (bv_unsigned x) ltac:(img_lia)) as Hh. rewrite Z_to_bv_bv_unsigned in Hh.
(subst m1full; cbv beta). unfold munrestrict. rewrite Hh. (subst m1 bs; cbv beta). rewrite wbytes_repeat_spec by (img_try (rewrite unsigned_lit_small by img_lia; img_lia)).
rewrite unsigned_lit_small by img_lia.
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [img_refl|].
symmetry. img_apply andb_true_intro. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia.
Qed.
Definition aFW : nat := 32.
Definition IFF {imgk : img} : facts := mkFacts [ (2%nat, mkAF (TFX_IMG_END + IAL_STK) (2 ^ 64 - 1) 4); (aFW, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
Definition rSTK : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- IAL_STK) 0 (- IAL_STK) 0 [].
Definition rFLAG1 {imgk : img} : YQ0b.region := YQ0b.mkRegion None TFX_IAL_FLAG (TFX_IAL_FLAG + 1) 0 0 [YQ0b.mkChunk TFX_IAL_FLAG (CVal 1 (SLit 1))].
Definition rFLAGW {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None TFX_IAL_FLAG (TFX_IAL_FLAG + 4) TFX_IAL_FLAG (TFX_IAL_FLAG + 4) [YQ0b.mkChunk TFX_IAL_FLAG (CVal 4 (SOff aFW 0))].
Definition rPSP {imgk : img} : YQ0b.region := flit8 (0xa2140 + D_10f0) (0x139c60 + D_10c0).
Definition rPS {imgk : img} : YQ0b.region := flit8 (0x139c60 + D_10c0) 4096.
Definition rLO {imgk : img} : YQ0b.region := YQ0b.mkRegion None TFX_IAL_LO (TFX_IAL_LO + 8) TFX_IAL_LO (TFX_IAL_LO + 8) [YQ0b.mkChunk TFX_IAL_LO (CZero 8)].
Definition SS_T {imgk : img} : sstate := mkSS (0x5e984 + D_2c4) sr_atoms [rSTK; rFLAG1] None IFF.
Definition SS_F {imgk : img} : sstate := mkSS (0x5e984 + D_2c4) sr_atoms [rSTK; rFLAGW; rPSP; rPS; rLO] None IFF.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Lemma rw_mbyte {imgk : img} : forall (W : world tfxsegs) mem a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> exists b, mbyte tfxsegs (mrestrict (w_H W) mem) a = Some b.
Proof.
intros W mem a Ha. unfold mbyte, mrestrict. rewrite (rw_unhidden W a Ha).
destruct (mem (Z_to_bv 64 a)) as [b|]; [img_try (exists b; img_refl)|].
destruct (seg_rom tfxsegs (Z_to_bv 64 a)) as [b|] eqn:Hr; [img_try (exists b; img_refl)|].
exfalso. img_apply (tfx_rw_rom a Ha). img_exact Hr.
Qed.
Lemma le_byte_4k : forall v, 0 <= v < 4294967296 ->
YP0g.le_byte v 4 0 = v mod 256 /\ YP0g.le_byte v 4 1 = (v / 256) mod 256 /\
YP0g.le_byte v 4 2 = (v / 65536) mod 256 /\ YP0g.le_byte v 4 3 = (v / 16777216) mod 256.
Proof.
intros v Hv. unfold YP0g.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 4) = 4294967296) by img_refl. rewrite P, (Z.mod_small v 4294967296) by img_lia.
rewrite !Z.shiftr_div_pow2 by img_lia.
rewrite (eq_refl : 2 ^ (8 * Z.of_nat 0) = 1), (eq_refl : 2 ^ (8 * Z.of_nat 1) = 256), (eq_refl : 2 ^ (8 * Z.of_nat 2) = 65536), (eq_refl : 2 ^ (8 * Z.of_nat 3) = 16777216).
rewrite Z.div_1_r. repeat split; img_refl.
Qed.
Lemma flagword_bytes : forall b2 b3, 0 <= b2 < 256 -> 0 <= b3 < 256 ->
let v := 65536 * (b2 + 256 * b3) in
YP0g.le_byte v 4 0 = 0 /\ YP0g.le_byte v 4 1 = 0 /\ YP0g.le_byte v 4 2 = b2 /\ YP0g.le_byte v 4 3 = b3.
Proof.
intros b2 b3 H2 H3 v. destruct (le_byte_4k v ltac:(img_try ((subst v; cbv beta); img_lia))) as (-> & -> & -> & ->). (subst v; cbv beta).
repeat split.
- replace (65536 * (b2 + 256 * b3)) with ((256 * (b2 + 256 * b3)) * 256) by img_lia. img_apply Z_mod_mult.
- replace (65536 * (b2 + 256 * b3)) with ((256 * (b2 + 256 * b3)) * 256) by img_lia. rewrite Z_div_mult by img_lia. rewrite Z.mul_comm. img_apply Z_mod_mult.
- replace (65536 * (b2 + 256 * b3)) with ((b2 + 256 * b3) * 65536) by img_lia. rewrite Z_div_mult by img_lia. rewrite Z.mul_comm, Z_mod_plus_full. img_apply Z.mod_small. img_lia.
- replace (65536 * (b2 + 256 * b3)) with ((b2 * 65536 + b3 * 16777216)) by img_lia. rewrite Z.div_add by img_lia. rewrite Z.div_small by img_lia. rewrite Z.add_0_l. img_apply Z.mod_small. img_lia.
Qed.
Lemma flagword_val {imgk : img} : forall (m : word -> option byte) a (b2 b3 : byte),
val_mem tfxsegs m a 1 0 -> val_mem tfxsegs m (a + 1) 1 0 -> mbyte tfxsegs m (a + 2) = Some b2 -> mbyte tfxsegs m (a + 3) = Some b3 ->
val_mem tfxsegs m a 4 (65536 * (bv_unsigned b2 + 256 * bv_unsigned b3)).
Proof.
intros m a b2 b3 H0 H1 H2 H3. pose proof (bv_unsigned_in_range _ b2) as R2. pose proof (bv_unsigned_in_range _ b3) as R3.
unfold bv_modulus in R2, R3. change (2 ^ Z.of_N 8) with 256 in R2, R3.
destruct (flagword_bytes (bv_unsigned b2) (bv_unsigned b3) ltac:(img_lia) ltac:(img_lia)) as (L0 & L1 & L2 & L3).
intros k Hk. destruct k as [|[|[|[|k]]]]; [ | | | | img_lia].
- rewrite L0. specialize (H0 0%nat ltac:(img_lia)). rewrite Z.add_0_r in H0 |- *. rewrite H0. img_refl.
- rewrite L1. specialize (H1 0%nat ltac:(img_lia)). rewrite Z.add_0_r in H1. img_exact H1.
- rewrite L2, Z_to_bv_bv_unsigned. img_exact H2.
- rewrite L3, Z_to_bv_bv_unsigned. img_exact H3.
Qed.
Lemma sweep16 {imgk : img} : forall (rho : nat -> Z) t c x y, sv_only 32 t = true -> 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) ->
forallb (fun i => forallb (fun j => zev (fun _ => 65536 * (Z.of_nat i + 256 * Z.of_nat j)) t =? c) (seq 0 256)) (seq 0 256) = true ->
zev rho t = c.
Proof.
intros rho t c x y Ho Hx Hy Hr C. rewrite (zev_only 32 rho t Ho), Hr.
pose proof (forallb_seq_In _ 256 (Z.to_nat x) C ltac:(img_lia)) as H1. cbn beta in H1.
pose proof (forallb_seq_In _ 256 (Z.to_nat y) H1 ltac:(img_lia)) as H2. cbn beta in H2.
rewrite !Z2Nat.id in H2 by img_lia. apply Z.eqb_eq in H2. img_exact H2.
Qed.
Definition T_P1 : sv := SExt true 8 (SOff 32 0).
Definition T_P2 : sv := SAlu ALU_AND (SAluw ALU_SRL (SExt true 32 (SOff 32 0)) (SLit 8)) (SLit 255).
Definition T_P3 : sv := SExt true 8 (SAlu ALU_XOR (SExt true 32 (SOff 32 0)) (SAlu ALU_AND (SAlu ALU_XOR (SExt true 32 (SOff 32 0)) (SLit 256)) (SLit 65280))).
Lemma pin_P1 {imgk : img} : forall (rho : nat -> Z) x y, 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) -> zev rho T_P1 = 0.
Proof. intros rho x y Hx Hy Hr. img_apply (sweep16 rho T_P1 0 x y eq_refl Hx Hy Hr). img_case; vm_compute. all: img_refl. Qed.
Lemma pin_P2 {imgk : img} : forall (rho : nat -> Z) x y, 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) -> zev rho T_P2 = 0.
Proof. intros rho x y Hx Hy Hr. img_apply (sweep16 rho T_P2 0 x y eq_refl Hx Hy Hr). img_case; vm_compute. all: img_refl. Qed.
Lemma pin_P3 {imgk : img} : forall (rho : nat -> Z) x y, 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) -> zev rho T_P3 = 0.
Proof. intros rho x y Hx Hy Hr. img_apply (sweep16 rho T_P3 0 x y eq_refl Hx Hy Hr). img_case; vm_compute. all: img_refl. Qed.
Definition IFF2 {imgk : img} : facts := mkFacts [ (2%nat, mkAF (TFX_IMG_END + IAL_STK) (2 ^ 64 - 1) 4); (aFW, mkAF 0 (2 ^ 32 - 65536) 16) ] [] [].
Definition SS_F2 {imgk : img} : sstate := mkSS (0x5e984 + D_2c4) sr_atoms [rSTK; rFLAGW; rPSP; rPS; rLO] None IFF2.
End e.
Ltac pin32 HS r Hx Hy R32 :=
apply (st_ok_pin_regU _ _ _ r (SLit 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?rr) =>
let t := img_ev (sr_get sr rr) in img_change (sr_get sr rr) with t;
first [ img_change t with T_P1 | img_change t with T_P2 | img_change t with T_P3 ];
img_apply U_eq_by_zev; [img_refl | img_refl |];
first [ rewrite (pin_P1 (rho_of E) _ _ Hx Hy R32) | rewrite (pin_P2 (rho_of E) _ _ Hx Hy R32) | rewrite (pin_P3 (rho_of E) _ _ Hx Hy R32) ];
img_refl end ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
