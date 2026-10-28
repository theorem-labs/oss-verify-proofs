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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB15.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFIB_IMG_END, IAL_STK, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG in *.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rw_writable : forall (m : word -> option byte) a, 0x9d000 <= a < 0x5fb000 -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at. apply tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha.
Qed.
Lemma rw_unhidden : forall (W : world tfibsegs) a, 0x9d000 <= a < 0x5fb000 -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
apply (tfib_rw_rom a Ha). unfold seg_rom.
rewrite (memory_read1_hidden tfibsegs (w_H W) (w_Hoff W) _ E). reflexivity.
Qed.
Lemma rw_store_ok : forall (m : word -> option byte) d len, 0x9d000 <= d -> d + len <= 0x5fb000 -> 0 <= len ->
store_ok tfibsegs m (Z_to_bv 64 d) (Z.to_nat len) = true.
Proof.
intros m d len H1 H2 H3. apply store_ok_of_all; rewrite unsigned_lit_small by lia; [lia|]. intros x Hx.
pose proof (rw_writable m (bv_unsigned x) ltac:(lia)) as Hw. unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
Qed.
Lemma imemset_stretch : forall (W : world tfibsegs) (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x63968 ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 0 -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> 0x9d000 <= d -> d + len <= 0x5fb000 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
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
intros W k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true) by (apply rw_store_ok; lia).
assert (RET : YK0s.ret_ok (Z_to_bv 64 retpc)).
{ apply YK0s.ret_ok_even. rewrite unsigned_lit_small by lia. apply Znumtheory.Zmod_divide in Hrpc; [|lia]. apply Znumtheory.Zdivide_mod.
apply (Z.divide_trans _ 4); [exists 2; reflexivity | exact Hrpc]. }
destruct (tfib_imemset mr (Z_to_bv 64 d) (Z_to_bv 64 0) len (seg_rom tfibsegs) (ms_regs ms) (Z_to_bv 64 retpc)
Hlen ltac:(rewrite unsigned_lit_small by lia; lia) SOK ltac:(intros _ _; rewrite unsigned_lit_small by lia; lia) RET H1 H10 H11 H12)
as (regs' & Hms & Hagree).
change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hms.
set (bs := repeat (Z_to_bv 8 0) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q).
{ rewrite restrict_mkst_fx. change (Z_to_bv 64 407912) with (Z_to_bv 64 (bv_unsigned tfib_imemset_entry)). rewrite Z_to_bv_bv_unsigned. exact Hms. }
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
- intros x Hx. pose proof (rw_unhidden W (bv_unsigned x) ltac:(lia)) as Hh. rewrite Z_to_bv_bv_unsigned in Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1 bs. rewrite wbytes_repeat_spec by (rewrite unsigned_lit_small by lia; lia).
rewrite unsigned_lit_small by lia.
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition aFW : nat := 32.
Definition IFF : facts := mkFacts [ (2%nat, mkAF (TFIB_IMG_END + IAL_STK) (2 ^ 64 - 1) 4); (aFW, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
Definition rSTK : YP09.region := YP09.mkRegion (Some 2%nat) (- IAL_STK) 0 (- IAL_STK) 0 [].
Definition rFLAG1 : YP09.region := YP09.mkRegion None TFIB_IAL_FLAG (TFIB_IAL_FLAG + 1) 0 0 [YP09.mkChunk TFIB_IAL_FLAG (CVal 1 (SLit 1))].
Definition rFLAGW : YP09.region :=
YP09.mkRegion None TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) [YP09.mkChunk TFIB_IAL_FLAG (CVal 4 (SOff aFW 0))].
Definition rPSP : YP09.region := flit8 0x9df78 0x135aa0.
Definition rPS : YP09.region := flit8 0x135aa0 4096.
Definition rLO : YP09.region := YP09.mkRegion None TFIB_IAL_LO (TFIB_IAL_LO + 8) TFIB_IAL_LO (TFIB_IAL_LO + 8) [YP09.mkChunk TFIB_IAL_LO (CZero 8)].
Definition SS_T : sstate := mkSS 0x5de68 sr_atoms [rSTK; rFLAG1] None IFF.
Definition SS_F : sstate := mkSS 0x5de68 sr_atoms [rSTK; rFLAGW; rPSP; rPS; rLO] None IFF.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma rw_mbyte : forall (W : world tfibsegs) mem a, 0x9d000 <= a < 0x5fb000 -> exists b, mbyte tfibsegs (mrestrict (w_H W) mem) a = Some b.
Proof.
intros W mem a Ha. unfold mbyte, mrestrict. rewrite (rw_unhidden W a Ha).
destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|] eqn:Hr; [exists b; reflexivity|].
exfalso. apply (tfib_rw_rom a Ha). exact Hr.
Qed.
Lemma le_byte_4k : forall v, 0 <= v < 4294967296 ->
YO0f.le_byte v 4 0 = v mod 256 /\ YO0f.le_byte v 4 1 = (v / 256) mod 256 /\
YO0f.le_byte v 4 2 = (v / 65536) mod 256 /\ YO0f.le_byte v 4 3 = (v / 16777216) mod 256.
Proof.
intros v Hv. unfold YO0f.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 4) = 4294967296) by reflexivity. rewrite P, (Z.mod_small v 4294967296) by lia.
rewrite !Z.shiftr_div_pow2 by lia.
rewrite (eq_refl : 2 ^ (8 * Z.of_nat 0) = 1), (eq_refl : 2 ^ (8 * Z.of_nat 1) = 256), (eq_refl : 2 ^ (8 * Z.of_nat 2) = 65536), (eq_refl : 2 ^ (8 * Z.of_nat 3) = 16777216).
rewrite Z.div_1_r. repeat split; reflexivity.
Qed.
Lemma flagword_bytes : forall b2 b3, 0 <= b2 < 256 -> 0 <= b3 < 256 ->
let v := 65536 * (b2 + 256 * b3) in
YO0f.le_byte v 4 0 = 0 /\ YO0f.le_byte v 4 1 = 0 /\ YO0f.le_byte v 4 2 = b2 /\ YO0f.le_byte v 4 3 = b3.
Proof.
intros b2 b3 H2 H3 v. destruct (le_byte_4k v ltac:(subst v; lia)) as (-> & -> & -> & ->). subst v.
repeat split.
- replace (65536 * (b2 + 256 * b3)) with ((256 * (b2 + 256 * b3)) * 256) by lia. apply Z_mod_mult.
- replace (65536 * (b2 + 256 * b3)) with ((256 * (b2 + 256 * b3)) * 256) by lia. rewrite Z_div_mult by lia. rewrite Z.mul_comm. apply Z_mod_mult.
- replace (65536 * (b2 + 256 * b3)) with ((b2 + 256 * b3) * 65536) by lia. rewrite Z_div_mult by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
- replace (65536 * (b2 + 256 * b3)) with ((b2 * 65536 + b3 * 16777216)) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.
Lemma flagword_val : forall (m : word -> option byte) a (b2 b3 : byte),
val_mem tfibsegs m a 1 0 -> val_mem tfibsegs m (a + 1) 1 0 -> mbyte tfibsegs m (a + 2) = Some b2 -> mbyte tfibsegs m (a + 3) = Some b3 ->
val_mem tfibsegs m a 4 (65536 * (bv_unsigned b2 + 256 * bv_unsigned b3)).
Proof.
intros m a b2 b3 H0 H1 H2 H3. pose proof (bv_unsigned_in_range _ b2) as R2. pose proof (bv_unsigned_in_range _ b3) as R3.
unfold bv_modulus in R2, R3. change (2 ^ Z.of_N 8) with 256 in R2, R3.
destruct (flagword_bytes (bv_unsigned b2) (bv_unsigned b3) ltac:(lia) ltac:(lia)) as (L0 & L1 & L2 & L3).
intros k Hk. destruct k as [|[|[|[|k]]]]; [ | | | | lia].
- rewrite L0. specialize (H0 0%nat ltac:(lia)). rewrite Z.add_0_r in H0 |- *. rewrite H0. reflexivity.
- rewrite L1. specialize (H1 0%nat ltac:(lia)). rewrite Z.add_0_r in H1. exact H1.
- rewrite L2, Z_to_bv_bv_unsigned. exact H2.
- rewrite L3, Z_to_bv_bv_unsigned. exact H3.
Qed.
Lemma sweep16 : forall (rho : nat -> Z) t c x y, sv_only 32 t = true -> 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) ->
forallb (fun i => forallb (fun j => zev (fun _ => 65536 * (Z.of_nat i + 256 * Z.of_nat j)) t =? c) (seq 0 256)) (seq 0 256) = true ->
zev rho t = c.
Proof.
intros rho t c x y Ho Hx Hy Hr C. rewrite (zev_only 32 rho t Ho), Hr.
pose proof (forallb_seq_In _ 256 (Z.to_nat x) C ltac:(lia)) as H1. cbn beta in H1.
pose proof (forallb_seq_In _ 256 (Z.to_nat y) H1 ltac:(lia)) as H2. cbn beta in H2.
rewrite !Z2Nat.id in H2 by lia. apply Z.eqb_eq in H2. exact H2.
Qed.
Definition T_P1 : sv := SExt true 8 (SOff 32 0).
Definition T_P2 : sv := SAlu ALU_AND (SAluw ALU_SRL (SExt true 32 (SOff 32 0)) (SLit 8)) (SLit 255).
Definition T_P3 : sv := SExt true 8 (SAlu ALU_XOR (SExt true 32 (SOff 32 0)) (SAlu ALU_AND (SAlu ALU_XOR (SExt true 32 (SOff 32 0)) (SLit 256)) (SLit 65280))).
Lemma pin_P1 : forall (rho : nat -> Z) x y, 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) -> zev rho T_P1 = 0.
Proof. intros rho x y Hx Hy Hr. apply (sweep16 rho T_P1 0 x y eq_refl Hx Hy Hr). vm_compute. reflexivity. Qed.
Lemma pin_P2 : forall (rho : nat -> Z) x y, 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) -> zev rho T_P2 = 0.
Proof. intros rho x y Hx Hy Hr. apply (sweep16 rho T_P2 0 x y eq_refl Hx Hy Hr). vm_compute. reflexivity. Qed.
Lemma pin_P3 : forall (rho : nat -> Z) x y, 0 <= x < 256 -> 0 <= y < 256 -> rho 32%nat = 65536 * (x + 256 * y) -> zev rho T_P3 = 0.
Proof. intros rho x y Hx Hy Hr. apply (sweep16 rho T_P3 0 x y eq_refl Hx Hy Hr). vm_compute. reflexivity. Qed.
Definition IFF2 : facts := mkFacts [ (2%nat, mkAF (TFIB_IMG_END + IAL_STK) (2 ^ 64 - 1) 4); (aFW, mkAF 0 (2 ^ 32 - 65536) 16) ] [] [].
Definition SS_F2 : sstate := mkSS 0x5de68 sr_atoms [rSTK; rFLAGW; rPSP; rPS; rLO] None IFF2.
End e.
Ltac pin32 HS r Hx Hy R32 :=
apply (st_ok_pin_regU _ _ _ r (SLit 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?rr) =>
let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t;
first [ change t with T_P1 | change t with T_P2 | change t with T_P3 ];
apply U_eq_by_zev; [reflexivity | reflexivity |];
first [ rewrite (pin_P1 (rho_of E) _ _ Hx Hy R32) | rewrite (pin_P2 (rho_of E) _ _ Hx Hy R32) | rewrite (pin_P3 (rho_of E) _ _ Hx Hy R32) ];
reflexivity end ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
