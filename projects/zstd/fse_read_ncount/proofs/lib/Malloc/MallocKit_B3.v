(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocKit_B MallocModel_B.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="Type"] Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
intros Hsc. unfold usages.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=15593877433.920770172597.532746093510.548980255798.900000<00=00>00FS3Hsc2Hi1n1eSSS2Hi1e1n".
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite usage_set_usage.
destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma unmap_seq_set st i v j :
unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="Type"] Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
intros Hi. unfold unmap_seqs.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=10982408164.515593877433.935036020573.548980255798.900000100<00=00ESS2Hi2Hj1n1eSS2Hj1e1n".
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite unmap_seq_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
#[using="Type"] Lemma record_seq_eq sc st :
record_seq sc st = if sc_in_seq_range sc
then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
else st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q. Proof. intros H; exact H. Qed.
#[using="Type"] Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q. Proof. intros H; exact H. Qed.
End CANSEC2.
Section CANSEC3. Context {rc : runConstT}.
Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.
#[using="Type"] Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. Local Ltac2 Set LiaHints.tbl := fun () => "0010<8929260062.600000>S2LI2FB3SCR2ML".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
intros (LI & FB & SCR & ML).
change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "0040=22703930437.629317658818.646609756872.668569543065.6000001002003007SSSS2LI".
rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
intros (LI & FB & SCR & ML).
assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
Local Ltac2 Set LiaHints.tbl := fun () => "0090=11957551149.720114617602.72850421623.7 29311237449.746611986243.753726910787.758138981964.763969312313.768575966226.700000100200300400500600=00>00BSSSSSSS2LI2FBSS2LI".
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^6) with 64. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
intros (LI & FB & SCR & ML).
Local Ltac2 Set LiaHints.tbl := fun () => "0050=11427672333.612500182983.617210419026.618926670024.657504004860.600000100<00=00>00?SS2LI2FB3SCRSSS".
rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. Local Ltac2 Set LiaHints.tbl := fun () => "0010=12832144649.600000>S2LI2FB3SCR2ML".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447730086.4400000[S1H2H02H42H52H93H103H143H153H193H203H243H25".
mlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
intros Hf Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0010=11304907537.5000001S".
replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
rewrite <- Z.ldiff_land. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). Local Ltac2 Set LiaHints.tbl := fun () => "0010>35960435360.1000000>S2Hf2Ha1S1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
intros Hf Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>35960435360.1062759100339.5 00000>00BS2Hf2Ha1S1H2H0S2Hf".
split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
intros Hv. apply le4_congr. pose proof (sxv_range v). Local Ltac2 Set LiaHints.tbl := fun () => "0020=15569286176.429436288106.4000003007S1HS2Hv".
rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
rewrite sxv_mod32. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=38557618280.3000004S2Hz".
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
intros Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0010=63045839500.3000004S2Hi".
rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
(Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.
End CANSEC3.
Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
