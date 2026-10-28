(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bounces_set st i v j :
  bounces (set_bounce i v st) j = if Z.eqb j i then v else bounces st j.
Proof.
  unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bouncess_set st i v : 0 <= i < 32 ->
  bouncess (set_bounce i v st) = upd (bouncess st) (Z.to_nat i) (b8 v).
Proof.
  intros Hi. unfold bouncess.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite bounces_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac raw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame asegs mX _ _ A bs') in FR; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write asegs mX _ _ A bs') in ST; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
    apply (wmono_write asegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv asegs mX |- _ =>
      apply (mem_inv_store asegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
Ltac raw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
    apply (wmono_write asegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv asegs mX |- _ =>
      apply (mem_inv_store asegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma set_group_ai_eq st b gh ai :
  get_group st b = Some gh -> set_group_active_idx b ai st = put_group b (g_meta gh) ai (del_group b st).
Proof.
  intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
  rewrite insert_delete_eq. reflexivity.
Qed.

Lemma put_group_del st b mo ai : put_group b mo ai (del_group b st) = put_group b mo ai st.
Proof. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sxv_inj a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> sxv a = sxv b -> a = b.
Proof.
  intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
  rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.

Lemma mask_upto_range k : 0 <= k <= 31 -> 0 < mask_upto k < 2^32.
Proof.
  intros Hk. unfold mask_upto. split.
  - assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
  - assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.


(* [comment removed for export] *)

Lemma lxor_range31 a b : 0 <= a < 2^31 -> 0 <= b < 2^31 -> 0 <= Z.lxor a b < 2^31.
Proof.
  intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
  assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.


Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
  intros MW. pose proof (meta_word_sc mr MW) as E. cps_pose MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range mr MW) as WR.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
    replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed.

Lemma span_loop_bounds F : forall cnt span size, cnt <= span_loop F cnt span size <= cnt + Z.of_nat F.
Proof.
  induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
  rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma le1_mod z : le1 (Z_to_bv 64 z) = [b8 (z mod 256)].
Proof.
  unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.

Lemma land31_range x : 0 <= Z.land x 31 <= 31.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed.

Lemma swrap32_small z : - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros. rewrite swrap32_eq'.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land1_mod2 a : Z.land a 1 = a mod 2.
Proof. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma even_of_land1 a : Z.even a = (Z.land a 1 =? 0).
Proof.
  rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS2.
