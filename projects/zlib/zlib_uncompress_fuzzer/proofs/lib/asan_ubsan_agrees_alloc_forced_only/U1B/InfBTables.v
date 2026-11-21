(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Arr Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AArr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition A_LBASE : Z := 0x246e0.  Definition A_LEXT : Z := 0x24740.
Definition A_DBASE : Z := 0x247a0.  Definition A_DEXT : Z := 0x24800.

Definition zw (l : list Z) : list word := map (Z_to_bv 64) l.
Lemma zw_length : forall l, length (zw l) = length l.
Proof. intros. unfold zw. apply length_map. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma u32s_read_sub : forall m A ws (i : Z) w (k len : nat),
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> (k + len <= 4)%nat ->
  ov_read_bytes segs m (Z_to_bv 64 (A + 4 * i + Z.of_nat k)) len = Some (firstn len (skipn k (le4 w))).
Proof.
  intros m A ws i w k len Hb Hn Hi Hk.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (A + 4 * i + Z.of_nat k) with (A + Z.of_nat (4 * Z.to_nat i + k)) by lia.
  change (Z_to_bv 64 (A + Z.of_nat (4 * Z.to_nat i + k))) with (wa (A + Z.of_nat (4 * Z.to_nat i + k))).
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i + k) len Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu. f_equal.
  rewrite skipn_app. rewrite (skipn_all2 (u32s pre)) by lia. rewrite Hlu.
  replace (4 * Z.to_nat i + k - 4 * Z.to_nat i)%nat with k by lia. rewrite app_nil_l.
  rewrite skipn_app, length_le4. replace (k - 4)%nat with 0%nat by lia. rewrite skipn_O.
  rewrite firstn_app, length_skipn, length_le4. replace (len - (4 - k))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma le4_bytes : forall c, le4 (Z_to_bv 64 c) =
  [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c)); Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 c)) 8);
   Z_to_bv 8 (Z.shiftr (Z.shiftr (bv_unsigned (Z_to_bv 64 c)) 8) 8); Z_to_bv 8 (Z.shiftr (Z.shiftr (Z.shiftr (bv_unsigned (Z_to_bv 64 c)) 8) 8) 8)].
Proof. intros c. reflexivity. Qed.

Lemma bv8_land : forall z, Z_to_bv 8 z = Z_to_bv 8 (Z.land z 255).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma code_read_op : forall m A ws (i c : Z),
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 c) -> 0 <= i -> 0 <= c < 4294967296 ->
  ov_read_bytes segs m (Z_to_bv 64 (A + 4 * i)) 1 = Some [Z_to_bv 8 (code_op c)].
Proof.
  intros m A ws i c Hb Hn Hi Hc. pose proof (u32s_read_sub m A ws i _ 0 1 Hb Hn Hi ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R, le4_bytes. cbn [firstn skipn]. rewrite unsigned_lit by lia. unfold code_op. rewrite <- bv8_land. reflexivity.
Qed.
Lemma code_read_bits : forall m A ws (i c : Z),
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 c) -> 0 <= i -> 0 <= c < 4294967296 ->
  ov_read_bytes segs m (Z_to_bv 64 (A + 4 * i + 1)) 1 = Some [Z_to_bv 8 (code_bits c)].
Proof.
  intros m A ws i c Hb Hn Hi Hc. pose proof (u32s_read_sub m A ws i _ 1 1 Hb Hn Hi ltac:(lia)) as R.
  change (Z.of_nat 1) with 1 in R. rewrite R, le4_bytes. cbn [firstn skipn]. rewrite unsigned_lit by lia. unfold code_bits. rewrite <- bv8_land. reflexivity.
Qed.
Lemma code_read_val : forall m A ws (i c : Z),
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 c) -> 0 <= i -> 0 <= c < 4294967296 ->
  ov_read_bytes segs m (Z_to_bv 64 (A + 4 * i + 2)) 2 = Some (le2 (Z_to_bv 64 (code_val c))).
Proof.
  intros m A ws i c Hb Hn Hi Hc. pose proof (u32s_read_sub m A ws i _ 2 2 Hb Hn Hi ltac:(lia)) as R.
  change (Z.of_nat 2) with 2 in R. rewrite R, le4_bytes. cbn [firstn skipn]. rewrite unsigned_lit by lia.
  unfold le2. assert (V : 0 <= code_val c < 65536).
  { unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. unfold code_val.
  f_equal. f_equal; [| f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256;
    change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; rewrite !Z.shiftr_div_pow2 by lia; change (2^8) with 256; change (2^16) with 65536;
    Z.div_mod_to_equations; lia.
Qed.

Lemma f32arr_nth : forall f n (i : Z), 0 <= i < Z.of_nat n -> nth_error (fws f n) (Z.to_nat i) = Some (Z_to_bv 64 (f i)).
Proof. intros f n i Hi. rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity. Qed.
End WithSegs.

Lemma zw_nth : forall l (i : Z), 0 <= i < Z.of_nat (length l) -> nth_error (zw l) (Z.to_nat i) = Some (Z_to_bv 64 (nth (Z.to_nat i) l 0)).
Proof. intros l i Hi. unfold zw. rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma lenfix_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 0x24860 (u32s (zw lenfix_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| lia| rewrite u32s_length, zw_length; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma distfix_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 0x25260 (u32s (zw distfix_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| lia| rewrite u32s_length, zw_length; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma order_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m 0x22840 (u16s (zw order_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| lia| rewrite u16s_length, zw_length; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lbase_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_LBASE (u16s (zw lbase_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold A_LBASE; lia| rewrite u16s_length, zw_length; unfold A_LBASE; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lext_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_LEXT (u16s (zw lext_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold A_LEXT; lia| rewrite u16s_length, zw_length; unfold A_LEXT; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma dbase_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_DBASE (u16s (zw dbase_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold A_DBASE; lia| rewrite u16s_length, zw_length; unfold A_DBASE; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma dext_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_DEXT (u16s (zw dext_l)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold A_DEXT; lia| rewrite u16s_length, zw_length; unfold A_DEXT; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.


Fixpoint allb (f : Z -> bool) (i : Z) (n : nat) : bool :=
  match n with O => true | S n' => f i && allb f (i + 1) n' end.
Lemma allb_spec : forall f n i, allb f i n = true -> forall j, i <= j < i + Z.of_nat n -> f j = true.
Proof.
  intros f n. induction n as [|n IH]; intros i H j Hj; [lia|].
  cbn [allb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec j i) as [->|Hne]; [exact H1|]. apply (IH (i + 1) H2). lia.
Qed.
Local Ltac tab_nth N := intros i Hi;
  match goal with |- ?l = ?r /\ _ =>
    pose proof (allb_spec (fun i => let c := nth (Z.to_nat i) _ 0 in (c =? arr_get _ i) && (0 <=? c) && (c <? 4294967296)) N 0
                  ltac:(vm_compute; reflexivity) i ltac:(lia)) as E end.
Lemma lenfix_nth : forall i, 0 <= i < 512 -> nth (Z.to_nat i) lenfix_l 0 = arr_get lenfix_a i /\ 0 <= arr_get lenfix_a i < 4294967296.
Proof.
  intros i Hi.
  pose proof (allb_spec (fun i => let c := nth (Z.to_nat i) lenfix_l 0 in (c =? arr_get lenfix_a i) && (0 <=? c) && (c <? 4294967296)) 512 0
                ltac:(vm_compute; reflexivity) i ltac:(lia)) as E.
  cbv zeta in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.
Lemma distfix_nth : forall i, 0 <= i < 32 -> nth (Z.to_nat i) distfix_l 0 = arr_get distfix_a i /\ 0 <= arr_get distfix_a i < 4294967296.
Proof.
  intros i Hi.
  pose proof (allb_spec (fun i => let c := nth (Z.to_nat i) distfix_l 0 in (c =? arr_get distfix_a i) && (0 <=? c) && (c <? 4294967296)) 32 0
                ltac:(vm_compute; reflexivity) i ltac:(lia)) as E.
  cbv zeta in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.

Lemma lenfix_read_op : forall m i, mem_inv bsegs m -> 0 <= i < 512 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (149600 + 4 * i)) 1 = Some [Z_to_bv 8 (code_op (arr_get lenfix_a i))].
Proof.
  intros m i MI Hi. destruct (lenfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_op bsegs m 149600 (zw lenfix_l) i); [exact (lenfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
Lemma lenfix_read_bits : forall m i, mem_inv bsegs m -> 0 <= i < 512 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (149600 + 4 * i + 1)) 1 = Some [Z_to_bv 8 (code_bits (arr_get lenfix_a i))].
Proof.
  intros m i MI Hi. destruct (lenfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_bits bsegs m 149600 (zw lenfix_l) i); [exact (lenfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
Lemma lenfix_read_val : forall m i, mem_inv bsegs m -> 0 <= i < 512 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (149600 + 4 * i + 2)) 2 = Some (le2 (Z_to_bv 64 (code_val (arr_get lenfix_a i)))).
Proof.
  intros m i MI Hi. destruct (lenfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_val bsegs m 149600 (zw lenfix_l) i); [exact (lenfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
Lemma distfix_read_op : forall m i, mem_inv bsegs m -> 0 <= i < 32 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (152160 + 4 * i)) 1 = Some [Z_to_bv 8 (code_op (arr_get distfix_a i))].
Proof.
  intros m i MI Hi. destruct (distfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_op bsegs m 152160 (zw distfix_l) i); [exact (distfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
Lemma distfix_read_bits : forall m i, mem_inv bsegs m -> 0 <= i < 32 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (152160 + 4 * i + 1)) 1 = Some [Z_to_bv 8 (code_bits (arr_get distfix_a i))].
Proof.
  intros m i MI Hi. destruct (distfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_bits bsegs m 152160 (zw distfix_l) i); [exact (distfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.
Lemma distfix_read_val : forall m i, mem_inv bsegs m -> 0 <= i < 32 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (152160 + 4 * i + 2)) 2 = Some (le2 (Z_to_bv 64 (code_val (arr_get distfix_a i)))).
Proof.
  intros m i MI Hi. destruct (distfix_nth i Hi) as [E R]. rewrite <- E in *.
  apply (code_read_val bsegs m 152160 (zw distfix_l) i); [exact (distfix_bytes m MI)| apply zw_nth; cbn; lia| lia| exact R].
Qed.

Lemma codes_read_op : forall m A n cf i, f32arr bsegs m A n cf -> 0 <= i < Z.of_nat n -> 0 <= cf i < 4294967296 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (A + 4 * i)) 1 = Some [Z_to_bv 8 (code_op (cf i))].
Proof. intros m A n cf i [HB _] Hi R. apply (code_read_op bsegs m A (fws cf n) i); [exact HB| apply f32arr_nth; exact Hi| lia| exact R]. Qed.
Lemma codes_read_bits : forall m A n cf i, f32arr bsegs m A n cf -> 0 <= i < Z.of_nat n -> 0 <= cf i < 4294967296 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (A + 4 * i + 1)) 1 = Some [Z_to_bv 8 (code_bits (cf i))].
Proof. intros m A n cf i [HB _] Hi R. apply (code_read_bits bsegs m A (fws cf n) i); [exact HB| apply f32arr_nth; exact Hi| lia| exact R]. Qed.
Lemma codes_read_val : forall m A n cf i, f32arr bsegs m A n cf -> 0 <= i < Z.of_nat n -> 0 <= cf i < 4294967296 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (A + 4 * i + 2)) 2 = Some (le2 (Z_to_bv 64 (code_val (cf i)))).
Proof. intros m A n cf i [HB _] Hi R. apply (code_read_val bsegs m A (fws cf n) i); [exact HB| apply f32arr_nth; exact Hi| lia| exact R]. Qed.

End CANSEC1.
