(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma bounces_set st i v j :
bounces (set_bounce i v st) j = if Z.eqb j i then v else bounces st j.
Proof.
unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="Type"] Lemma bouncess_set st i v : 0 <= i < 32 ->
bouncess (set_bounce i v st) = upd (bouncess st) (Z.to_nat i) (b8 v).
Proof.
intros Hi. unfold bouncess.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=10982408164.515593877433.935036020573.548980255798.900000100<00=00ESS2Hi2Hj1n1eSS2Hj1e1n".
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite bounces_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma set_group_ai_eq st b gh ai :
get_group st b = Some gh -> set_group_active_idx b ai st = put_group b (g_meta gh) ai (del_group b st).
Proof.
intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
rewrite insert_delete_eq. reflexivity.
Qed.
#[using="Type"] Lemma put_group_del st b mo ai : put_group b mo ai (del_group b st) = put_group b mo ai st.
Proof. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.
#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "0010=29317657175.3000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_inj a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> sxv a = sxv b -> a = b.
Proof.
intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.
#[using="Type"] Lemma mask_upto_range k : 0 <= k <= 31 -> 0 < mask_upto k < 2^32.
Proof.
intros Hk. unfold mask_upto. split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0050=39181610561.341415986323.34949847201.3 58027258900.462204830865.400000400500900<00?S2HkSS2HkS1HS1H".
assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
- assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lxor_range31 a b : 0 <= a < 2^31 -> 0 <= b < 2^31 -> 0 <= Z.lxor a b < 2^31.
Proof.
intros Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "00;0=26980962951.726985714880.828262574075.531701287537.844139611275.561885899093.861889472274.867590460542.77222831367.6 7224834857.5 9668803840.9 00000600:00A00E00F00J00P00T00U00V00bS2Ha1nS2HaS2Ha2HbS2HbSS2HbS2Hb1nS2HaSSS2Ha2Hb2NE1H".
split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
intros MW. pose proof (meta_word_sc mr MW) as E. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range mr MW) as WR.
apply Z.bits_inj'. intros n Hn.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>2424960062.11 30481200869.123428856171.12 65704699225.1200000400500600=S2HnSSS2Hn2NZ".
rewrite Z.land_spec, Z.shiftr_spec by lia.
destruct (Z.eq_dec n 0) as [->|NZ].
- rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma span_loop_bounds F : forall cnt span size, cnt <= span_loop F cnt span size <= cnt + Z.of_nat F.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=25079562121.425079562121.626136020250.7000001002005SSS1H".
induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le1_mod z : le1 (Z_to_bv 64 z) = [b8 (z mod 256)].
Proof.
unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
Local Ltac2 Set LiaHints.tbl := fun () => "0020=48483662115.27110532030.2 000001002SS".
rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land31_range x : 0 <= Z.land x 31 <= 31.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0010<7227811030.2000001S".
split; [apply Z.land_nonneg; right; lia|].
apply Z.ldiff_le; [lia|].
apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma swrap32_small z : - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
intros. rewrite swrap32_eq'.
change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010=4439696873.10000009S1H2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land1_mod2 a : Z.land a 1 = a mod 2.
Proof. change 1 with (Z.ones 1) at 1. Local Ltac2 Set LiaHints.tbl := fun () => "0010<6757371245.2000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma even_of_land1 a : Z.even a = (Z.land a 1 =? 0).
Proof.
rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.
End CANSEC2.
