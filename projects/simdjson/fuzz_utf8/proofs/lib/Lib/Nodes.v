(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Exec ITree.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
Lemma in_a0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = areg ms 10.
Proof. reflexivity. Qed.
Lemma in_a1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = areg ms 11.
Proof. reflexivity. Qed.
Lemma in_a2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = areg ms 12.
Proof. reflexivity. Qed.
Lemma in_a3_si : forall segs ms x8, in_arg (sys_input segs ms x8) 3 = areg ms 13.
Proof. reflexivity. Qed.
Lemma in_a4_si : forall segs ms x8, in_arg (sys_input segs ms x8) 4 = areg ms 14.
Proof. reflexivity. Qed.
Lemma in_a5_si : forall segs ms x8, in_arg (sys_input segs ms x8) 5 = areg ms 15.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sysno_lit : forall segs ms K, 0 <= K < 2^64 ->
  bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 K))) = K.
Proof. intros. rewrite in_sysno_si. apply unsigned_lit. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
  forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.

Lemma ms_read_byte_mrd : forall segs ms a,
  ms_rom ms = seg_rom segs -> ms_read_byte ms a = mrd segs (ms_mem ms) a.
Proof. intros segs ms a H. unfold ms_read_byte, mrd. rewrite H. reflexivity. Qed.

Lemma bytes_at_in : forall segs ms a bs,
  ms_rom ms = seg_rom segs -> bytes_at segs (ms_mem ms) a bs -> bytes_in (ms_read_byte ms) a bs.
Proof.
  intros segs ms a bs Hrom (Ha & Hl & H). split; [lia|]. split; [lia|].
  intros i Hi. rewrite (ms_read_byte_mrd segs) by exact Hrom. apply H. exact Hi.
Qed.

Lemma bytes_in_app : forall mp a bs1 bs2,
  bytes_in mp a (bs1 ++ bs2) <-> bytes_in mp a bs1 /\ bytes_in mp (a + Z.of_nat (length bs1)) bs2.
Proof.
  intros mp a bs1 bs2. unfold bytes_in. rewrite length_app. split.
  - intros (Ha & Hl & H). repeat split; try lia.
    + intros i Hi. rewrite (H i) by lia. rewrite nth_error_app1 by lia. reflexivity.
    + intros i Hi. replace (a + Z.of_nat (length bs1) + Z.of_nat i) with (a + Z.of_nat (length bs1 + i)) by lia.
      rewrite (H (length bs1 + i)%nat) by lia. rewrite nth_error_app2 by lia. f_equal. lia.
  - intros ((Ha & Hl1 & H1) & (Ha2 & Hl2 & H2)). repeat split; try lia.
    intros i Hi. destruct (Nat.ltb_spec0 i (length bs1)).
    + rewrite nth_error_app1 by lia. apply H1. lia.
    + rewrite nth_error_app2 by lia. rewrite <- (H2 (i - length bs1)%nat) by lia. f_equal. f_equal. lia.
Qed.

Lemma bytes_in_cons : forall mp a b bs,
  bytes_in mp a (b :: bs) -> mp (wa a) = Some b /\ bytes_in mp (a + 1) bs.
Proof.
  intros mp a b bs H. change (b :: bs) with ([b] ++ bs) in H. apply bytes_in_app in H as [H1 H2].
  split; [|exact H2]. destruct H1 as (_ & _ & H1). specialize (H1 0%nat ltac:(cbn; lia)).
  rewrite Z.add_0_r in H1. exact H1.
Qed.

Lemma read_bytes_aux_bytes_in : forall bs mp a,
  bytes_in mp a bs -> read_bytes_aux mp (wa a) (length bs) = Some bs.
Proof.
  induction bs as [|b bs IH]; intros mp a H; [reflexivity|].
  apply bytes_in_cons in H as [Hb H]. cbn [read_bytes_aux length]. rewrite Hb.
  rewrite wa_succ, (IH _ _ H). reflexivity.
Qed.

Lemma readable_bytes_aux_bytes_in : forall bs mp a,
  bytes_in mp a bs -> readable_bytes_aux mp (wa a) (length bs) = bs.
Proof.
  intros. apply readable_bytes_aux_full, read_bytes_aux_bytes_in. assumption.
Qed.

Lemma word_to_nat_of_nat : forall n, Z.of_nat n < 2^64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof. intros. unfold word_to_nat. rewrite unsigned_lit by lia. lia. Qed.

Lemma read_bytes_map_bytes_in : forall bs mp a,
  bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
  read_bytes_map mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = Some bs.
Proof.
  intros bs mp a H Hl. rewrite read_bytes_map_eq. rewrite word_to_nat_of_nat by exact Hl.
  apply read_bytes_aux_bytes_in, H.
Qed.

Lemma readable_bytes_bytes_in : forall bs mp a,
  bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
  readable_bytes mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = bs.
Proof.
  intros. apply readable_bytes_full, read_bytes_map_bytes_in; assumption.
Qed.

(* [comment removed for export] *)
Lemma bytes_in_firstn : forall mp a bs k, bytes_in mp a bs -> bytes_in mp a (firstn k bs).
Proof.
  intros mp a bs k (Ha & Hl & H). pose proof (firstn_le_length k bs).
  split; [lia|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite (H i) by lia.
  rewrite <- (firstn_skipn k bs) at 1. rewrite nth_error_app1 by (rewrite length_firstn; lia). reflexivity.
Qed.

Lemma read_bytes_aux_prefix_bytes_in : forall bs mp a k,
  bytes_in mp a bs -> (k <= length bs)%nat -> read_bytes_aux mp (wa a) k = Some (firstn k bs).
Proof.
  intros bs mp a k H Hk. pose proof (bytes_in_firstn mp a bs k H) as H'.
  rewrite <- (read_bytes_aux_bytes_in _ _ _ H'). f_equal. rewrite length_firstn. lia.
Qed.

(* [comment removed for export] *)
Lemma read_cstr_aux_bytes_in : forall str fuel mp a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  bytes_in mp a (str ++ [Z_to_bv 8 0]) ->
  read_cstr_aux mp (wa a) fuel = CstrOk str.
Proof.
  induction str as [|b str IH]; intros fuel mp a Hf Hnz H.
  - destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb _].
    cbn [read_cstr_aux]. rewrite Hb. reflexivity.
  - destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb H].
    cbn [read_cstr_aux]. rewrite Hb.
    assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
    { destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
    rewrite Hne, wa_succ. rewrite (IH fuel mp (a + 1)); [reflexivity| cbn in Hf; lia | |exact H].
    intro Hin. apply Hnz. right. exact Hin.
Qed.

Lemma read_cstr_aux_toolong_bytes_in : forall fuel str mp a,
  (fuel <= length str)%nat -> ~ In (Z_to_bv 8 0) str ->
  bytes_in mp a str ->
  read_cstr_aux mp (wa a) fuel = CstrTooLong.
Proof.
  induction fuel as [|fuel IH]; intros str mp a Hf Hnz H; [reflexivity|].
  destruct str as [|b str]; [cbn in Hf; lia|]. apply bytes_in_cons in H as [Hb H].
  cbn [read_cstr_aux]. rewrite Hb.
  assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
  { destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
  rewrite Hne, wa_succ. rewrite (IH str mp (a + 1)); [reflexivity| cbn in Hf; lia | |exact H].
  intro Hin. apply Hnz. right. exact Hin.
Qed.

(* [comment removed for export] *)
Definition cstr_len (path : list byte) : nat := Nat.min (S (length path)) path_max.

Lemma cstr_access_len_aux_bytes_in : forall str fuel mp a,
  ~ In (Z_to_bv 8 0) str ->
  bytes_in mp a (str ++ [Z_to_bv 8 0]) ->
  cstr_access_len_aux mp (wa a) fuel = Nat.min (S (length str)) fuel.
Proof.
  induction str as [|b str IH]; intros fuel mp a Hnz H.
  - destruct fuel as [|fuel]; [reflexivity|]. cbn [app] in H. apply bytes_in_cons in H as [Hb _].
    cbn [cstr_access_len_aux]. rewrite Hb. reflexivity.
  - destruct fuel as [|fuel]; [reflexivity|]. cbn [app] in H. apply bytes_in_cons in H as [Hb H].
    cbn [cstr_access_len_aux]. rewrite Hb.
    assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
    { destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
    rewrite Hne, wa_succ. rewrite (IH fuel mp (a + 1)); [| |exact H].
    + cbn [length]. lia.
    + intro Hin. apply Hnz. right. exact Hin.
Qed.

(* [comment removed for export] *)
Definition iovec_bytes (iovs : list (word * word)) : list byte :=
  flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.

Lemma length_iovec_bytes : forall iovs, length (iovec_bytes iovs) = (16 * length iovs)%nat.
Proof.
  induction iovs as [|[b l] iovs IH]; [reflexivity|]. cbn [iovec_bytes flat_map fst snd].
  rewrite !length_app, !length_le8. unfold iovec_bytes in IH. rewrite IH. cbn [length]. lia.
Qed.

Lemma read_u64_bytes_in : forall mp a v,
  bytes_in mp a (le8 v) -> read_u64 mp (wa a) = Some v.
Proof.
  intros mp a v H. unfold read_u64.
  pose proof (read_bytes_map_bytes_in _ _ _ H ltac:(rewrite length_le8; cbn; lia)) as R. rewrite length_le8 in R.
  change (Z.of_nat 8) with 8 in R. rewrite R. rewrite le_bytes_to_word_le8. reflexivity.
Qed.

Lemma wa_add : forall a (k : word), (wa a + k)%bv = wa (a + bv_unsigned k).
Proof. intros. rewrite <- (Z_to_bv_bv_unsigned k) at 1. unfold wa. apply lit_add_lit. Qed.

(* [comment removed for export] *)
Lemma read_iovec_entry_bytes_in : forall mp a b l,
  bytes_in mp a (le8 b ++ le8 l) -> bv_unsigned l < 2^63 -> read_iovec_entry mp (wa a) = IovEntry b l.
Proof.
  intros mp a b l H Hl. apply bytes_in_app in H as [H1 H2]. rewrite length_le8 in H2.
  unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
  rewrite wa_add. change (bv_unsigned (8%bv : word)) with 8.
  replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
  destruct (Z.leb_spec0 (2^63) (bv_unsigned l)); [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Definition iov_lens_ok (iovs : list (word * word)) : Prop :=
  Forall (fun p => bv_unsigned (fst p) + bv_unsigned (snd p) <= TASK_SIZE) iovs.

Lemma TASK_SIZE_val : TASK_SIZE = 0x800000000000.
Proof. reflexivity. Qed.

Lemma copy_iovecs_aux_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) -> iov_lens_ok iovs ->
  copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros mp a H HL; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  assert (H' := H). apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2, H3. rewrite length_le8 in H3.
  cbn [copy_iovecs_aux length].
  inversion HL as [|x xs Hl HL']; subst. cbn [fst snd] in Hl. pose proof TASK_SIZE_val.
  pose proof (bv_unsigned_in_range 64 b).
  rewrite (read_iovec_entry_bytes_in mp a b l).
  2:{ rewrite app_assoc in H'. apply bytes_in_app in H' as [H' _]. exact H'. }
  2:{ lia. }
  rewrite wa_add. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH _ _ H3 HL'). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_array_accesses (a : Z) (k : nat) : list (word * nat) :=
  match k with
  | O => []
  | S k' => (wa a, 16%nat) :: iov_array_accesses (a + 16) k'
  end.

Lemma copy_iovecs_accesses_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) -> iov_lens_ok iovs ->
  copy_iovecs_accesses mp (wa a) (length iovs) = iov_array_accesses a (length iovs).
Proof.
  induction iovs as [|[b l] iovs IH]; intros mp a H HL; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  assert (H' := H). apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2, H3. rewrite length_le8 in H3.
  cbn [copy_iovecs_accesses iov_array_accesses length].
  inversion HL as [|x xs Hl HL']; subst. cbn [fst snd] in Hl. pose proof TASK_SIZE_val.
  pose proof (bv_unsigned_in_range 64 b).
  rewrite (read_iovec_entry_bytes_in mp a b l).
  2:{ rewrite app_assoc in H'. apply bytes_in_app in H' as [H' _]. exact H'. }
  2:{ lia. }
  rewrite wa_add. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH _ _ H3 HL'). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iovs_access_okb_of : forall iovs, iov_lens_ok iovs -> iovs_access_okb iovs = true.
Proof.
  intros iovs HL. unfold iovs_access_okb. induction HL as [|[b l] iovs Hl HL IH]; [reflexivity|].
  cbn [forallb fst snd]. cbn [fst snd] in Hl. rewrite IH, Bool.andb_true_r.
  unfold access_okb. pose proof (bv_unsigned_in_range 64 b). pose proof (bv_unsigned_in_range 64 l).
  apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.

Lemma MAX_RW_COUNT_val : MAX_RW_COUNT = 0x7ffff000.
Proof. reflexivity. Qed.
Lemma IOV_MAX_val : IOV_MAX = 1024.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma import_iovecs_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) -> iov_lens_ok iovs ->
  (1 <= length iovs <= 1024)%nat -> a + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
  import_iovecs mp (wa a) (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs
  /\ import_iovecs_accesses mp (wa a) (Z_to_bv 64 (Z.of_nat (length iovs))) = iov_array_accesses a (length iovs).
Proof.
  intros iovs mp a H HL Hn Ha. pose proof TASK_SIZE_val. pose proof IOV_MAX_val. pose proof MAX_RW_COUNT_val.
  pose proof H as (Ha0 & _ & _).
  unfold import_iovecs, import_iovecs_accesses. unfold bv_eqb. rewrite !unsigned_lit by lia.
  assert (Hok : forall k, 0 <= k <= 16 * Z.of_nat (length iovs) -> access_okb (wa a) k = true).
  { intros k Hk. unfold access_okb, wa. rewrite unsigned_lit by lia. apply andb_true_intro; split; apply Z.leb_le; lia. }
  destruct (Z.eqb_spec (Z.of_nat (length iovs)) 1) as [E1|E1].
  - destruct iovs as [|[b l] [|? ?]]; cbn in E1; try lia. rewrite Hok by lia. cbn [negb].
    cbn [iovec_bytes flat_map fst snd] in H. rewrite app_nil_r in H.
    inversion HL as [|x xs Hl _]; subst. cbn [fst snd] in Hl. pose proof (bv_unsigned_in_range 64 b).
    rewrite (read_iovec_entry_bytes_in mp a b l H) by lia.
    replace (access_okb b (Z.min (bv_unsigned l) MAX_RW_COUNT)) with true.
    2:{ symmetry. unfold access_okb. apply andb_true_intro; split; apply Z.leb_le; lia. }
    split; reflexivity.
  - destruct (Z.eqb_spec (Z.of_nat (length iovs)) 0); [lia|].
    replace (IOV_MAX <? Z.of_nat (length iovs)) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Hok by lia. cbn [negb]. rewrite word_to_nat_of_nat by lia.
    rewrite (copy_iovecs_aux_bytes_in iovs) by assumption.
    rewrite (copy_iovecs_accesses_bytes_in iovs) by assumption.
    rewrite (iovs_access_okb_of iovs HL). split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
  snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Lemma gather_iovecs_ok : forall mp iovs bufs,
  Forall2 (iov_ok mp) iovs bufs -> gather_iovecs mp iovs = Some (concat bufs).
Proof.
  intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
  cbn [gather_iovecs fst snd] in *. subst l.
  rewrite <- (wa_unsigned_id b). rewrite (read_bytes_map_bytes_in _ _ _ Hb Hlen). rewrite IH. reflexivity.
Qed.

Lemma iovs_total_ok : forall mp iovs bufs,
  Forall2 (iov_ok mp) iovs bufs -> iovs_total iovs = Z.of_nat (length (concat bufs)).
Proof.
  intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
  cbn [iovs_total fst snd concat] in *. subst l. rewrite length_app, IH.
  rewrite unsigned_lit by lia. lia.
Qed.


(* [comment removed for export] *)
Lemma cap_iovecs_aux_id : forall iovs left,
  iovs_total iovs <= left -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux iovs_total] in *. pose proof (iovs_total_nonneg iovs). pose proof (bv_unsigned_in_range 64 l).
  rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned. rewrite IH by lia. reflexivity.
Qed.

Lemma cap_iovecs_id : forall iovs, iovs_total iovs <= MAX_RW_COUNT -> cap_iovecs iovs = iovs.
Proof. intros. unfold cap_iovecs. apply cap_iovecs_aux_id. assumption. Qed.

(* [comment removed for export] *)
Lemma read_bytes_aux_wr_at : forall segs m a n k,
  wr_at segs m a n -> Z.of_nat k <= n ->
  read_bytes_aux (wview segs m) (wa a) k <> None.
Proof.
  intros segs m a n k W Hk. destruct W as (Ha & Hn & H). revert a n Ha Hn H Hk.
  induction k as [|k IH]; intros a n Ha Hn H Hk; cbn [read_bytes_aux]; [discriminate|].
  destruct (wview segs m (wa a)) eqn:E.
  2:{ exfalso. apply (H 0); [lia|]. rewrite Z.add_0_r. exact E. }
  rewrite wa_succ.
  assert (IH' : read_bytes_aux (wview segs m) (wa (a + 1)) k <> None).
  { apply (IH (a + 1) (n - 1)); try lia. intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
  destruct (read_bytes_aux (wview segs m) (wa (a + 1)) k); [discriminate|]. exfalso; apply IH'; reflexivity.
Qed.

Lemma read_bytes_map_wr_at : forall segs m a n (c : word),
  wr_at segs m a n -> bv_unsigned c <= n ->
  read_bytes_map (wview segs m) (wa a) c <> None.
Proof.
  intros segs m a n c W Hc. rewrite read_bytes_map_eq. apply (read_bytes_aux_wr_at segs m a n); [exact W|].
  unfold word_to_nat. pose proof (bv_unsigned_in_range 64 c). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive node : Type :=
| NWrite (fd : Z) (bs : list byte)                 (* [comment removed for export] *)
| NWritev (fd : Z) (bufs : list (list byte))       (* [comment removed for export] *)
| NOpen (path : list byte)                         (* [comment removed for export] *)
| NRead (fd : Z) (buf : Z) (count : Z)             (* [comment removed for export] *)
| NClose (fd : Z)                                  (* [comment removed for export] *)
| NIoctl (fd : Z) (req : Z)                        (* [comment removed for export] *)
| NSetTid                                          (* [comment removed for export] *)
| NExit (code : Z)                                 (* [comment removed for export] *)
| NBrk (req : Z)                                   (* [comment removed for export] *)
| NMmap (addr len prot flags : Z)                  (* [comment removed for export] *)
| NMunmap (addr len : Z)                           (* [comment removed for export] *)
| NMprotect (addr len prot : Z)                    (* [comment removed for export] *)
| NMadvise (addr len : Z).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pure_input (no : Z) (args : list word) : SyscallInput :=
  mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).

Definition node_input (n : node) : option SyscallInput :=
  match n with
  | NBrk req => Some (pure_input 214 [Z_to_bv 64 req])
  | NMmap addr len prot flags =>
      Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
  | NMunmap addr len => Some (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])
  | NMprotect addr len prot => Some (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
  | NMadvise addr len => Some (pure_input 233 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 4])
  | _ => None
  end.

(* [comment removed for export] *)
Definition max_write : Z := 67108864.
Definition max_read : Z := 16777216.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtNode.
Variable segs : list Segment.

Definition at_node (n : node) (ms : machine_state) : Prop :=
  match n with
  | NWrite fd bs =>
      ms_svc_pending ms = Some (Z_to_bv 64 64) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bs)) /\
      1 <= Z.of_nat (length bs) <= max_write /\
      bv_unsigned (areg ms 11) + Z.of_nat (length bs) <= TASK_SIZE /\   (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (1 <= length bufs <= 1024)%nat /\
      Z.of_nat (length (concat bufs)) <= max_write /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE /\   (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\   (* [comment removed for export] *)
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      path_has_slash path = false /\        (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      1 <= count <= max_read /\
      buf + count <= TASK_SIZE /\              (* [comment removed for export] *)
      wr_at segs (ms_mem ms) buf count
  | NClose fd =>
      ms_svc_pending ms = Some (Z_to_bv 64 57) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd
  | NIoctl fd req =>
      ms_svc_pending ms = Some (Z_to_bv 64 29) /\
      0 <= fd <= 2 /\ req = 21523 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 req
  | NSetTid =>
      ms_svc_pending ms = Some (Z_to_bv 64 96)
  | NExit code =>
      (ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94)) /\
      areg ms 10 = Z_to_bv 64 code
  | NBrk req =>
      ms_svc_pending ms = Some (Z_to_bv 64 214) /\
      areg ms 10 = Z_to_bv 64 req
  | NMmap addr len prot flags =>
      ms_svc_pending ms = Some (Z_to_bv 64 222) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
      areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
      areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0 /\
      mmap_noreserve_b (Z_to_bv 64 flags) = false
  | NMunmap addr len =>
      ms_svc_pending ms = Some (Z_to_bv 64 215) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
  | NMprotect addr len prot =>
      ms_svc_pending ms = Some (Z_to_bv 64 226) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot
  | NMadvise addr len =>
      (* [comment removed for export] *)
      ms_svc_pending ms = Some (Z_to_bv 64 233) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 4
  end.

End AtNode.

(* [comment removed for export] *)
Ltac at_node_red :=
  cbn [at_node]; unfold areg, max_write, max_read, TASK_SIZE;
  cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac split_spine :=
  lazymatch goal with
  | |- _ /\ _ => split; [|split_spine]
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rstrip (e : resp) : resp :=
  mkEffectU (eff_ret e) (eff_writes e) (eff_zeros e) (eff_unmaps e) (eff_copies e) [].

Lemma nret_rstrip : forall ms e, nret ms (rstrip e) = nret ms e.
Proof. intros ms [r ws zs us cs ci]. reflexivity. Qed.

Lemma rstrip_idem : forall e, rstrip (rstrip e) = rstrip e.
Proof. intros [r ws zs us cs ci]. reflexivity. Qed.

(* [comment removed for export] *)
Definition eff0 (r : word) : resp := mkEffectU r [] [] [] [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

(* [comment removed for export] *)
Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

(* [comment removed for export] *)
Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWrite fd bs =>
      exists k, 1 <= k <= Z.of_nat (length bs) /\
      eff = eff0 (Z_to_bv 64 k) /\ mo' = mo /\
      evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs)
  | NWritev fd bufs =>
      mo' = mo /\
      let total := Z.of_nat (length (concat bufs)) in
      if total =? 0 then eff = eff0 (Z_to_bv 64 0) /\ evs = []
      else exists k, 1 <= k <= total /\ eff = eff0 (Z_to_bv 64 k) /\
                     evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat bufs))
  | NOpen path =>
      evs = [] /\
      if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => eff = efferr ENOENT /\ mo' = mo
           | _ => if path_is_dirref path then open_result mo FdDir eff mo'   (* [comment removed for export] *)
                  else match fs_lookup (m_fs mo) path with
                       | None => eff = efferr ENOENT /\ mo' = mo
                       | Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
                       end
           end
  | NRead fd buf count =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some FdDir => eff = efferr EISDIR /\ mo' = mo
      | Some (FdFile p off) =>
          match fs_lookup (m_fs mo) p with
          | None => False
          | Some data =>
              let bs := file_read data off (Z_to_bv 64 count) in
              eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
          end
      | Some _ => False
      end
  | NClose fd =>
      evs = [] /\ 3 <= fd < 2^32 /\   (* [comment removed for export] *)
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some _ => eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
      end
  | NIoctl fd req => evs = [] /\ eff = efferr ENOTTY /\ mo' = mo
  | NSetTid =>
      evs = [] /\ exists t, eff = eff0 t /\
      match m_tid mo with
      | Some t0 => t = t0 /\ mo' = mo
      | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
      end
  | NExit _ => False
  | NMmap _ _ _ flags =>
      evs = [] /\ mmap_noreserve_b (Z_to_bv 64 flags) = false /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg ACFG i mo eff
      | None => False
      end
  | NBrk _ | NMprotect _ _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg ACFG i mo eff
      | None => False
      end
  | NMunmap _ _ | NMadvise _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs)
      | None => False
      end
  end.

Definition mm_ns (n : node) (mo : Model) (eff : resp) : Prop :=
  match node_input n with
  | Some i => ~ spurious_refusal_cfg ACFG i mo eff
  | None => True
  end.

Definition alloc_node (n : node) : bool :=
  match n with NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ => true | _ => false end.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

(* [comment removed for export] *)
Definition minv (mo : Model) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
  (forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
  (forall k e, fd_lookup (m_fds mo) k = Some e ->
     match e with FdChannel _ | FdFile _ _ | FdDir => True | _ => False end) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
  m_vm_lazy mo = [] /\ m_vm_materialized mo = [] /\
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi.   (* [comment removed for export] *)

Lemma minv_nolazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof. intros mo H. apply H. Qed.

(* [comment removed for export] *)
Definition alloc_ceiling : Z := sp_window_hi - stack_max_size.      (* [comment removed for export] *)
Definition alloc_ceiling_lo : Z := sp_window_lo - stack_max_size.   (* [comment removed for export] *)

Lemma alloc_ceiling_val : alloc_ceiling = 0x7FFFFF800000.
Proof. reflexivity. Qed.
Lemma alloc_ceiling_lo_val : alloc_ceiling_lo = 0x7FFF7F800000.
Proof. reflexivity. Qed.

Lemma minv_alloc_top : forall mo, minv mo ->
  alloc_ceiling_lo <= alloc_top (m_vmmaps mo) <= alloc_ceiling.
Proof.
  intros mo H. unfold alloc_top, alloc_ceiling, alloc_ceiling_lo.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HS). lia.
Qed.

(* [comment removed for export] *)
Lemma minv_init : forall reserved brk mbase sp lim inp,
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  minv (init_model reserved brk mbase sp lim inp).
Proof.
  intros reserved brk mbase sp lim inp Hsp. unfold minv.
  (* [comment removed for export] *)
  replace (vm_init_sp (m_vmmaps (init_model reserved brk mbase sp lim inp))) with (sp) by reflexivity.
  replace (m_fds (init_model reserved brk mbase sp lim inp)) with ([(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))]) by reflexivity.
  replace (m_tid (init_model reserved brk mbase sp lim inp)) with ((@None word)) by reflexivity.
  replace (m_vm_lazy (init_model reserved brk mbase sp lim inp)) with ((@nil (word * word))) by reflexivity.
  replace (m_vm_materialized (init_model reserved brk mbase sp lim inp)) with ((@nil word)) by reflexivity.
  cbn [fd_lookup].
  repeat split; try reflexivity; try (intros; discriminate); try lia.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (TASK_SIZE <? bv_unsigned addr + nZ) then true
    else
      let n := Z_to_bv 64 nZ in
      map_has (vm_maps h) addr n || munmap_free_ok h addr nZ.

Definition mprotect_safe_b (addr len prot : word) (h : VmMaps) : bool :=
  if mprotect_grows_conflict_b prot then true
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
  else if w_is0 len then true
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
  else if negb (mprotect_modeled_b prot) then false
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
    || (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n).

(* [comment removed for export] *)
Definition madvise_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
  else if w_is0 len then true
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
  else madvise_dontneed_ok h addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).

(* [comment removed for export] *)
Definition mmap_fixed_gate_b (addr : word) (nZ : Z) (h : VmMaps) : bool :=
  let n := Z_to_bv 64 nZ in
  if (two_pow_64 <=? bv_unsigned addr + nZ) then true
  else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
  else if negb (0 <? bv_unsigned addr) then false
  else (region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n)
       || region_free (vm_reserved h ++ vm_maps h) addr n
       || region_free (vm_reserved h) addr n.

Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  mmap_off_aligned_b off && mmap_anon_b flags &&
  if w_is0 len then mmap_plain_anon_b flags
  else
  mmap_modeled_b prot flags off
  || mmap_noaccess_b prot flags off
  || (mmap_fixed_noaccess_b prot flags off && mmap_fixed_gate_b addr (page_round_up_Z (bv_unsigned len)) h)
  || (mmap_fixed_rw_b prot flags off && mmap_fixed_gate_b addr (page_round_up_Z (bv_unsigned len)) h).

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
  | NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
  | NMprotect addr len prot =>
      mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
  | NMadvise addr len => madvise_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
  | _ => True
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_svc_inv : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep segs (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
                  X = SNext (mkCfg (nret ms eff) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\
                  evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  m_killed mo' = None /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))   (* [comment removed for export] *)
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. eauto.
  - right; left. eexists _, _, _. eauto 6.
  - right; right; left. eexists _, _, _, _. eauto 6.
  - right; right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; right. auto.
Qed.

(* [comment removed for export] *)
Lemma m_killed_halted : forall mo sig, m_killed mo = Some sig -> m_halted mo <> None.
Proof.
  intros mo sig Hk Hh. rewrite (m_killed_of_m_halted_none _ Hh) in Hk. discriminate.
Qed.

(* [comment removed for export] *)
Lemma node_kit : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs -> P (rstrip eff) mo' evs) ->
  (forall eff mo' evs, P eff mo' evs ->
     exists effk, check_syscall (sys_input segs ms x8) effk mo = CheckOk mo' evs /\ rstrip effk = eff) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, P eff mo' evs -> m_halted mo' = None /\ m_vm_lazy mo' = []) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
  /\ (forall eff mo' evs, P eff mo' evs -> sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, P eff mo' evs).
Proof.
  intros ms mo x8 P Hsvc Hh Hsnd Hcpl Hnu Hhalt. split; [|split].
  - intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
      as [(eff & mo' & mo'' & Hs & Hh' & Hmat & ->) | [(eff & mo' & evs1 & Hs & Hh' & Hmat & -> & ->)
         | [(eff & mo' & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & mo' & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
    + exists (rstrip eff), mo'. apply check_syscall_ok_iff in Hs. apply Hsnd in Hs.
      rewrite (materialize_model_accesses_no_lazy mo' _ (proj2 (Hhalt _ _ _ Hs))) in Hmat. inversion Hmat; subst.
      rewrite nret_rstrip. split; [reflexivity| exact Hs].
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hsnd in Hs.
      rewrite (materialize_model_accesses_no_lazy mo' _ (proj2 (Hhalt _ _ _ Hs))) in Hmat. discriminate.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hsnd in Hs. apply Hhalt in Hs. destruct Hs; congruence.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hsnd in Hs. apply Hhalt in Hs. destruct Hs as [Hh2 _].
      exact (m_killed_halted _ _ Hk' Hh2).
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
  - intros eff mo' evs HP. destruct (Hhalt _ _ _ HP) as [Hh' Hlz].
    destruct (Hcpl _ _ _ HP) as (effk & Hck & Hst). rewrite <- Hst, nret_rstrip. unfold nret.
    eapply sstep_syscall; [exact Hh|exact Hsvc| apply check_syscall_ok_iff; exact Hck |exact Hh'| apply materialize_model_accesses_no_lazy; exact Hlz].
  - pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    + exists (rstrip eff), mo', evs. apply Hsnd. apply check_syscall_ok_iff. exact Hr.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.

(* [comment removed for export] *)
Lemma node_kit_strict : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> P eff mo' evs) ->
  (forall eff mo' evs, P eff mo' evs -> rstrip eff = eff) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, P eff mo' evs -> m_halted mo' = None /\ m_vm_lazy mo' = []) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
  /\ (forall eff mo' evs, P eff mo' evs -> sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, P eff mo' evs).
Proof.
  intros ms mo x8 P Hsvc Hh Hchar Hstrip Hnu Hhalt. apply (node_kit ms mo x8 P Hsvc Hh); try assumption.
  - intros eff mo' evs Hc. apply Hchar in Hc. rewrite (Hstrip _ _ _ Hc). exact Hc.
  - intros eff mo' evs HP. exists eff. split; [apply Hchar; exact HP| apply (Hstrip _ _ _ HP)].
Qed.

Lemma exit_kit : forall ms mo x8 code,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <->
     eff = eff0 (Z_to_bv 64 0) /\ mo' = with_halted code mo /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
  /\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
  intros ms mo x8 code Hsvc Hh Hchar Hnu. split.
  - intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
      as [(eff & mo' & mo'' & Hs & Hh' & Hmat & ->) | [(eff & mo' & evs1 & Hs & Hh' & Hmat & -> & ->)
         | [(eff & mo' & evs0 & code' & Hs & Hh' & Hk' & -> & ->) | [(eff & mo' & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _). rewrite m_halted_with_halted in Hh'. discriminate.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _). rewrite m_halted_with_halted in Hh'. discriminate.
    + apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & ->). rewrite m_halted_with_halted in Hh'. inversion Hh'; subst.
      rewrite m_fs_with_halted. split; reflexivity.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _). rewrite m_killed_with_halted in Hk'. discriminate.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
  - replace [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))])
      by (rewrite m_fs_with_halted; reflexivity).
    eapply sstep_exit; [exact Hh|exact Hsvc| |apply m_halted_with_halted|apply m_killed_with_halted].
    apply check_syscall_ok_iff. apply Hchar. repeat split; reflexivity.
Qed.

Lemma node_kit_ns : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs ->
     m_halted mo' = None /\ m_vm_lazy mo' = []) ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff -> P eff mo' evs) ->
  (forall eff mo' evs, P eff mo' evs ->
     check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs
     /\ ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall evs X, sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
  /\ (forall eff mo' evs, P eff mo' evs -> sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, P eff mo' evs).
Proof.
  intros ms mo x8 P Hsvc Hh Hok Hsnd Hcpl Hnu. split; [|split].
  - intros evs X Hst. destruct (sstep_cfg_sys_inv segs ACFG ms mo x8 evs X Hsvc Hst)
      as [(eff & mo' & evs0 & Hs & Hns & Hh' & Hm) | [(eff & mo' & evs0 & code & Hs & Hh' & _ & _ & _)
         | [(eff & mo' & evs0 & sig & Hs & Hk' & _ & _) | (Hs & _ & _)]]].
    + apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as [_ Hlz].
      rewrite (materialize_model_accesses_no_lazy mo' _ Hlz) in Hm. cbv beta iota in Hm. destruct Hm as [-> ->].
      exists eff, mo'. split; [reflexivity| exact (Hsnd _ _ _ Hs Hns)].
    + exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as [Hh2 _]. congruence.
    + exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as [Hh2 _].
      exact (m_killed_halted _ _ Hk' Hh2).
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
  - intros eff mo' evs HP. destruct (Hcpl _ _ _ HP) as [Hck Hns]. destruct (Hok _ _ _ Hck) as [Hh' Hlz].
    unfold nret. eapply sstep_cfg_syscall; [exact Hh| exact Hsvc| apply check_syscall_ok_iff; exact Hck| exact Hns
      | exact Hh'| apply materialize_model_accesses_no_lazy; exact Hlz].
  - pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [effw mow evsw|] eqn:E.
    + destruct (exists_nonspurious ACFG (sys_input segs ms x8) mo effw mow evsw Hr) as (eff & mo' & evs & Hs & Hns).
      exists eff, mo', evs. apply Hsnd; [apply check_syscall_ok_iff; exact Hs| exact Hns].
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.

End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PerNode.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs -> nstep n mo (rstrip eff) mo' evs) /\
  (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists effk, check_syscall (sys_input segs ms x8) effk mo = CheckOk mo' evs /\ rstrip effk = eff) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) /\
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo').

(* [comment removed for export] *)
Lemma facts_strict : forall ms mo n x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> nstep n mo eff mo' evs) ->
  (forall eff mo' evs, nstep n mo eff mo' evs -> rstrip eff = eff) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo') ->
  node_facts ms mo n.
Proof.
  intros ms mo n x8 Hsvc Hchar Hstrip Hnu Hpres. exists x8. split; [exact Hsvc|]. split; [|split; [|split; assumption]].
  - intros eff mo' evs Hc. apply Hchar in Hc. rewrite (Hstrip _ _ _ Hc). exact Hc.
  - intros eff mo' evs HP. exists eff. split; [apply Hchar; exact HP| apply (Hstrip _ _ _ HP)].
Qed.

(* [comment removed for export] *)
Lemma facts_ret_only : forall ms mo n x8 r evs0,
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = check_ret_only eff r mo evs0) ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo /\ evs = evs0)) ->
  node_facts ms mo n.
Proof.
  intros ms mo n x8 r evs0 Hsvc Hminv Hh Hchk Hn. apply (facts_strict ms mo n x8 Hsvc).
  - intros eff mo' evs. rewrite Hchk, check_ret_only_ok_iff, Hn. unfold eff0. tauto.
  - intros eff mo' evs HP. apply Hn in HP as (-> & _). reflexivity.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - intros eff mo' evs HP. apply Hn in HP as (_ & -> & _). auto.
Qed.

(* [comment removed for export] *)
Ltac dispatch K :=
  lazymatch K with
  | 64 => rewrite check_syscall_write by (apply sysno_lit; lia)
  | 66 => rewrite check_syscall_writev by (apply sysno_lit; lia)
  | 56 => rewrite check_syscall_openat by (apply sysno_lit; lia)
  | 63 => rewrite check_syscall_read by (apply sysno_lit; lia)
  | 57 => rewrite check_syscall_close by (apply sysno_lit; lia)
  | 29 => rewrite check_syscall_ioctl by (apply sysno_lit; lia)
  | 96 => rewrite check_syscall_set_tid_address by (apply sysno_lit; lia)
  | 93 => rewrite check_syscall_exit by (apply sysno_lit; lia)
  | 94 => rewrite check_syscall_exit_group by (apply sysno_lit; lia)
  | 214 => rewrite check_syscall_brk by (apply sysno_lit; lia)
  | 222 => rewrite check_syscall_mmap by (apply sysno_lit; lia)
  | 215 => rewrite check_syscall_munmap by (apply sysno_lit; lia)
  | 226 => rewrite check_syscall_mprotect by (apply sysno_lit; lia)
  | 233 => rewrite check_syscall_madvise by (apply sysno_lit; lia)
  end;
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma std_chan : forall mo fd, minv mo -> (fd = 1 \/ fd = 2) ->
  fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd)) /\
  w_is0 (Z_to_bv 64 fd) = false.
Proof.
  intros mo fd (M0 & M1 & M2 & _) [-> | ->]; split; first [exact M1 | exact M2 | reflexivity].
Qed.

Lemma max_write_lt : max_write < MAX_RW_COUNT /\ max_read < MAX_RW_COUNT /\ MAX_RW_COUNT < TASK_SIZE /\ TASK_SIZE = 2^47.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma access_okb_below : forall (buf : word) n, 0 <= n -> bv_unsigned buf + n <= TASK_SIZE -> access_okb buf n = true.
Proof.
  intros buf n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 buf).
  apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Definition write_check (fd : Z) (buf : word) (bs : list byte) (eff : resp) (mo : Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] copyins =>
      if (1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length bs))
      then if access_ranges_eqb copyins [(buf, Z.to_nat (bv_unsigned ret))]
           then CheckOk mo (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
           else CheckReject
      else CheckReject
  | _ => CheckReject
  end.

Lemma write_check_spec : forall ms mo fd bs eff,
  at_node segs (NWrite fd bs) ms -> minv mo ->
  check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff mo = write_check fd (areg ms 11) bs eff mo.
Proof.
  intros ms mo fd bs eff (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Htop & Hrom & Hbs) Hminv.
  pose proof max_write_lt as (W1 & W2 & W3 & W4).
  dispatch 64. unfold check_write. rewrite Ha0, Ha2, in_mem_si.
  destruct (std_chan mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
  unfold modeled_rw_range. rewrite (access_okb_below (areg ms 11)) by (rewrite ?unsigned_lit by lia; lia).
  rewrite orb_true_r. cbn [negb].
  rewrite w_is0_lit by lia. replace (Z.of_nat (length bs) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold write_source. rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; lia). rewrite unsigned_lit by lia.
  rewrite <- (wa_unsigned_id (areg ms 11)).
  rewrite !(readable_bytes_bytes_in bs) by (first [eapply bytes_at_in; eassumption | lia]).
  replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Lemma write_check_ok : forall fd buf bs eff mo mo' evs,
  write_check fd buf bs eff mo = CheckOk mo' evs ->
  nstep (NWrite fd bs) mo (rstrip eff) mo' evs /\ eff_copyins eff = [(buf, Z.to_nat (bv_unsigned (eff_ret eff)))].
Proof.
  intros fd buf bs [ret ws zs us cs ci] mo mo' evs H. unfold write_check in H. cbn [nstep rstrip eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. unfold eff0.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (Z.leb_spec0 1 (bv_unsigned ret)); [|discriminate].
  destruct (Z.leb_spec0 (bv_unsigned ret) (Z.of_nat (length bs))); [|discriminate]. cbn [andb] in H.
  destruct (access_ranges_eqb ci _) eqn:E; [|discriminate]. apply access_ranges_eqb_eq in E. subst ci.
  inversion H; subst. split; [|reflexivity].
  exists (bv_unsigned ret). rewrite Z_to_bv_bv_unsigned. repeat split; try lia.
Qed.

Lemma write_check_complete : forall fd buf bs eff mo mo' evs,
  Z.of_nat (length bs) < 2^64 ->
  nstep (NWrite fd bs) mo eff mo' evs ->
  exists effk, write_check fd buf bs effk mo = CheckOk mo' evs /\ rstrip effk = eff.
Proof.
  intros fd buf bs eff mo mo' evs Hlen (k & Hk & -> & -> & ->).
  exists (mkEffectU (Z_to_bv 64 k) [] [] [] [] [(buf, Z.to_nat k)]). split; [|reflexivity].
  unfold write_check. rewrite unsigned_lit by lia.
  replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
  replace (k <=? Z.of_nat (length bs)) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma write_check_no_unmodeled : forall fd buf bs eff mo, write_check fd buf bs eff mo <> CheckUnmodeled.
Proof.
  intros fd buf bs [ret ws zs us cs ci] mo. unfold write_check.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

Lemma write_facts : forall ms mo fd bs,
  at_node segs (NWrite fd bs) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NWrite fd bs).
Proof.
  intros ms mo fd bs Hat Hminv Hh. exists (Z_to_bv 64 64). split; [exact (proj1 Hat)|].
  pose proof max_write_lt as (W1 & W2 & W3 & W4). pose proof Hat as (_ & _ & _ & _ & Hlen & _).
  split; [|split; [|split]].
  - intros eff mo' evs. rewrite (write_check_spec _ _ _ _ _ Hat Hminv). intros Hc. exact (proj1 (write_check_ok _ _ _ _ _ _ _ Hc)).
  - intros eff mo' evs HP.
    destruct (write_check_complete fd (areg ms 11) bs eff mo mo' evs ltac:(lia) HP) as (effk & Hck & Hst).
    exists effk. rewrite (write_check_spec _ _ _ _ _ Hat Hminv). auto.
  - intros eff. rewrite (write_check_spec _ _ _ _ _ Hat Hminv). apply write_check_no_unmodeled.
  - intros eff mo' evs (k & _ & _ & -> & _). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iovs_ok_of_at : forall ms iovs bufs,
  ms_rom ms = seg_rom segs ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  Forall2 (iov_ok (ms_read_byte ms)) iovs bufs /\ iov_lens_ok iovs.
Proof.
  intros ms iovs bufs Hrom H. pose proof max_write_lt as (W1 & W2 & W3 & W4).
  induction H as [|iov bs iovs bufs (Hl & Htop & Hb) _ [IH1 IH2]]; [split; constructor|].
  pose proof (bv_unsigned_in_range 64 (fst iov)).
  split; constructor.
  - split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
  - exact IH1.
  - cbn beta. rewrite Hl, unsigned_lit by lia. lia.
  - exact IH2.
Qed.

(* [comment removed for export] *)
Definition writev_check (fd : Z) (iov : word) (iovs : list (word * word)) (bufs : list (list byte)) (eff : resp) (mo : Model)
    : check_result :=
  let bs := concat bufs in
  let ci1 := iov_array_accesses (bv_unsigned iov) (length iovs) in
  if (length bs =? 0)%nat
  then check_ret_only_copyins ci1 eff (Z_to_bv 64 0) mo []
  else
    match eff with
    | mkEffectU ret [] [] [] [] copyins =>
        if (1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length bs))
           && negb (addr_is_error_b ret)
        then if access_ranges_eqb copyins (ci1 ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
             then CheckOk mo (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
             else CheckReject
        else CheckReject
    | _ => CheckReject
    end.

Lemma writev_check_spec : forall ms mo fd iovs bufs eff,
  at_node segs (NWritev fd bufs) ms -> minv mo ->
  bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  check_syscall (sys_input segs ms (Z_to_bv 64 66)) eff mo = writev_check fd (areg ms 11) iovs bufs eff mo.
Proof.
  intros ms mo fd iovs bufs eff (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Harr & Hrom & _) Hminv Hiov Hbufs.
  pose proof max_write_lt as (W1 & W2 & W3 & W4). pose proof MAX_RW_COUNT_val. pose proof IOV_MAX_val.
  destruct (iovs_ok_of_at _ _ _ Hrom Hbufs) as [Hok HL].
  pose proof (Forall2_length Hbufs) as Hleq.
  pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
  dispatch 66. unfold check_writev. rewrite Ha0, Ha2, in_mem_si.
  destruct (std_chan mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
  unfold iovcnt32. rewrite abi_low32_small by lia. rewrite <- Hleq.
  rewrite <- (wa_unsigned_id (areg ms 11)).
  destruct (import_iovecs_bytes_in iovs (ms_read_byte ms) (bv_unsigned (areg ms 11))) as [-> ->];
    [eapply bytes_at_in; eassumption | exact HL | lia | lia |].
  cbv zeta. unfold writev_gathered. rewrite cap_iovecs_id by lia. rewrite Htotal.
  rewrite (gather_prefix_full _ _ _ (gather_iovecs_ok _ _ _ Hok)).
  unfold writev_check. cbv zeta. rewrite wa_unsigned.
  2:{ pose proof (bv_unsigned_in_range 64 (areg ms 11)). unfold bv_modulus in *. lia. }
  destruct (Nat.eqb_spec (length (concat bufs)) 0) as [E|E].
  - replace (Z.of_nat (length (concat bufs)) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (Z.of_nat (length (concat bufs)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold len_word. replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat (length (concat bufs))))) with false.
    2:{ symmetry. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia. }
    reflexivity.
Qed.

Lemma addr_is_error_b_small : forall z, 0 <= z <= max_write -> addr_is_error_b (Z_to_bv 64 z) = false.
Proof.
  intros z Hz. pose proof max_write_lt as (W1 & W2 & W3 & W4). unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

Lemma writev_check_ok : forall fd iov iovs bufs eff mo mo' evs,
  writev_check fd iov iovs bufs eff mo = CheckOk mo' evs -> nstep (NWritev fd bufs) mo (rstrip eff) mo' evs.
Proof.
  intros fd iov iovs bufs eff mo mo' evs H. unfold writev_check in H. cbn [nstep]. cbv zeta in H. cbv zeta. unfold eff0.
  destruct (Nat.eqb_spec (length (concat bufs)) 0) as [E|E].
  - replace (Z.of_nat (length (concat bufs)) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->). cbn. auto.
  - replace (Z.of_nat (length (concat bufs)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct eff as [ret ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (Z.leb_spec0 1 (bv_unsigned ret)); [|discriminate].
    destruct (Z.leb_spec0 (bv_unsigned ret) (Z.of_nat (length (concat bufs)))); [|discriminate].
    destruct (addr_is_error_b ret); [discriminate|]. cbn [andb negb] in H.
    destruct (access_ranges_eqb ci _) eqn:Ea; [|discriminate].
    inversion H; subst. split; [reflexivity|].
    exists (bv_unsigned ret). cbn [rstrip eff_ret eff_writes eff_zeros eff_unmaps eff_copies]. rewrite Z_to_bv_bv_unsigned. repeat split; try lia.
Qed.

Lemma writev_check_complete : forall fd iov iovs bufs eff mo mo' evs,
  Z.of_nat (length (concat bufs)) <= max_write ->
  nstep (NWritev fd bufs) mo eff mo' evs ->
  exists effk, writev_check fd iov iovs bufs effk mo = CheckOk mo' evs /\ rstrip effk = eff.
Proof.
  intros fd iov iovs bufs eff mo mo' evs Htot [-> H]. pose proof max_write_lt as (W1 & W2 & W3 & W4). cbv zeta in H.
  unfold writev_check. cbv zeta.
  destruct (Nat.eqb_spec (length (concat bufs)) 0) as [E|E].
  - replace (Z.of_nat (length (concat bufs)) =? 0) with true in H by (symmetry; apply Z.eqb_eq; lia).
    destruct H as [-> ->].
    exists (mkEffectU (Z_to_bv 64 0) [] [] [] [] (iov_array_accesses (bv_unsigned iov) (length iovs))). split; [|reflexivity].
    apply check_ret_only_copyins_ok_iff. cbn. auto.
  - replace (Z.of_nat (length (concat bufs)) =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
    destruct H as (k & Hk & -> & ->).
    exists (mkEffectU (Z_to_bv 64 k) [] [] [] []
              (iov_array_accesses (bv_unsigned iov) (length iovs) ++ iov_prefix_accesses iovs (Z.to_nat k))). split; [|reflexivity].
    rewrite unsigned_lit by lia.
    replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
    replace (k <=? Z.of_nat (length (concat bufs))) with true by (symmetry; apply Z.leb_le; lia).
    rewrite addr_is_error_b_small by lia. cbn [andb negb].
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma writev_check_no_unmodeled : forall fd iov iovs bufs eff mo, writev_check fd iov iovs bufs eff mo <> CheckUnmodeled.
Proof.
  intros fd iov iovs bufs [ret ws zs us cs ci] mo. unfold writev_check. cbv zeta.
  destruct (length (concat bufs) =? 0)%nat.
  - unfold check_ret_only_copyins. destruct (check_ret_only _ _ _ _) eqn:Ec.
    + destruct (access_ranges_eqb _ _); discriminate.
    + discriminate.
    + exfalso. exact (check_ret_only_no_unmodeled _ _ _ _ Ec).
  - destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

Lemma writev_facts : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NWritev fd bufs).
Proof.
  intros ms mo fd bufs Hat Hminv Hh. exists (Z_to_bv 64 66). split; [exact (proj1 Hat)|].
  pose proof Hat as (_ & _ & _ & _ & _ & Htot & _ & _ & iovs & Hiov & Hbufs).
  pose proof (fun eff => writev_check_spec ms mo fd iovs bufs eff Hat Hminv Hiov Hbufs) as Hchk.
  split; [|split; [|split]].
  - intros eff mo' evs. rewrite Hchk. apply writev_check_ok.
  - intros eff mo' evs HP. destruct (writev_check_complete fd (areg ms 11) iovs bufs eff mo mo' evs Htot HP) as (effk & Hck & Hst).
    exists effk. rewrite Hchk. auto.
  - intros eff. rewrite Hchk. apply writev_check_no_unmodeled.
  - intros eff mo' evs [-> _]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb_sym : forall (a b : word), bv_eqb a b = bv_eqb b a.
Proof. intros. unfold bv_eqb. apply Z.eqb_sym. Qed.

Lemma fd_lookup_filter : forall fds fd k, bv_eqb fd k = false ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) k = fd_lookup fds k.
Proof.
  induction fds as [|[k' e] fds IH]; intros fd k Hne; [reflexivity|].
  cbn [List.filter fst]. destruct (bv_eqb k' fd) eqn:E; cbn [negb fd_lookup].
  - apply bv_eqb_eq in E; subst k'. rewrite Hne. apply IH. exact Hne.
  - rewrite IH by exact Hne. reflexivity.
Qed.

Lemma fd_lookup_insert : forall fds fd e k,
  fd_lookup (fd_insert fds fd e) k = if bv_eqb fd k then Some e else fd_lookup fds k.
Proof.
  intros. unfold fd_insert. cbn [fd_lookup]. destruct (bv_eqb fd k) eqn:E; [reflexivity|].
  apply fd_lookup_filter. exact E.
Qed.

Lemma fd_lookup_remove : forall fds fd k,
  fd_lookup (fd_remove fds fd) k = if bv_eqb fd k then None else fd_lookup fds k.
Proof.
  intros. unfold fd_remove. destruct (bv_eqb fd k) eqn:E.
  - apply bv_eqb_eq in E; subst k. induction fds as [|[k' e] fds IH]; [reflexivity|].
    cbn [List.filter fst]. destruct (bv_eqb k' fd) eqn:E'; cbn [negb fd_lookup]; [exact IH|].
    rewrite E'. exact IH.
  - apply fd_lookup_filter. exact E.
Qed.

(* [comment removed for export] *)
Lemma m_fds_with_fds : forall fds m, m_fds (with_fds fds m) = fds. Proof. reflexivity. Qed.
Lemma m_fs_with_fds : forall fds m, m_fs (with_fds fds m) = m_fs m. Proof. reflexivity. Qed.
Lemma m_tid_with_fds : forall fds m, m_tid (with_fds fds m) = m_tid m. Proof. reflexivity. Qed.
Lemma m_halted_with_fds : forall fds m, m_halted (with_fds fds m) = m_halted m. Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_fds : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_fds : forall fds m, m_vm_materialized (with_fds fds m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma m_fds_with_tid : forall t m, m_fds (with_tid t m) = m_fds m. Proof. reflexivity. Qed.
Lemma m_fs_with_tid : forall t m, m_fs (with_tid t m) = m_fs m. Proof. reflexivity. Qed.
Lemma m_tid_with_tid : forall t m, m_tid (with_tid t m) = Some t. Proof. reflexivity. Qed.
Lemma m_halted_with_tid : forall t m, m_halted (with_tid t m) = m_halted m. Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_tid : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_tid : forall t m, m_vm_materialized (with_tid t m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma m_fs_with_halted : forall c m, m_fs (with_halted c m) = m_fs m. Proof. reflexivity. Qed.
Lemma m_halted_with_halted : forall c m, m_halted (with_halted c m) = Some c. Proof. reflexivity. Qed.
Lemma m_vmmaps_with_fds : forall fds m, m_vmmaps (with_fds fds m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma m_vmmaps_with_tid : forall t m, m_vmmaps (with_tid t m) = m_vmmaps m. Proof. reflexivity. Qed.

Ltac minv_setters :=
  rewrite ?m_fds_with_fds, ?m_fs_with_fds, ?m_tid_with_fds, ?m_vm_lazy_with_fds, ?m_vm_materialized_with_fds, ?m_vmmaps_with_fds,
          ?m_fds_with_tid, ?m_fs_with_tid, ?m_tid_with_tid, ?m_vm_lazy_with_tid, ?m_vm_materialized_with_tid, ?m_vmmaps_with_tid in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_body (path : list byte) (eff : resp) (mo : Model) : check_result :=
  if (path_max <=? length path)%nat then check_ret_only eff (errno_ret ENAMETOOLONG) mo []
  else match path with
       | [] => check_ret_only eff (errno_ret ENOENT) mo []
       | _ => if path_is_dirref path
              then check_open_result eff mo (fun fd => with_fds (fd_insert (m_fds mo) fd FdDir) mo)
              else match fs_lookup (m_fs mo) path with
                   | None => check_ret_only eff (errno_ret ENOENT) mo []
                   | Some _ => check_open_result eff mo
                                 (fun fd => with_fds (fd_insert (m_fds mo) fd (FdFile path (Z_to_bv 64 0))) mo)
                   end
       end.

(* [comment removed for export] *)
Definition open_ci (pathp : word) (path : list byte) : list (word * nat) := [(pathp, cstr_len path)].

Definition open_check (pathp : word) (path : list byte) (eff : resp) (mo : Model) : check_result :=
  check_copyins_after (open_ci pathp path) eff (open_body path (clear_copyins eff) mo).

Lemma clear_rstrip : forall eff, clear_copyins eff = rstrip eff.
Proof. intros [r ws zs us cs ci]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma check_open_result_ok_iff : forall eff mo ent mo' evs,
  check_open_result eff mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) = CheckOk mo' evs <->
  (open_result mo ent eff mo' /\ evs = []).
Proof.
  intros [ret ws zs us cs ci] mo ent mo' evs.
  unfold check_open_result, check_new_fd_result, open_result, efferr, eff0. split.
  - intro H.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct ci; [|discriminate].
    destruct (errno_ret_in openat_errnos ret) eqn:Herr.
    + inversion H; subst. apply errno_ret_in_true in Herr as (e & HIn & ->). split; [|reflexivity]. left. exists e. auto.
    + destruct (fd_lookup (m_fds mo) ret) eqn:Hlk; [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds mo))) eqn:Heq; [|discriminate].
      inversion H; subst. apply bv_eqb_eq in Heq. subst ret. split; [|reflexivity]. right. auto.
  - intros [[(e & HIn & Heff & ->) | (Hlk & Heff & ->)] ->]; inversion Heff; subst.
    + rewrite (errno_ret_in_intro _ e HIn). reflexivity.
    + rewrite errno_ret_in_alloc_fd by reflexivity. rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.

Lemma check_open_result_no_unmodeled : forall eff mo mk, check_open_result eff mo mk <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs ci] mo mk. unfold check_open_result, check_new_fd_result.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct ci; [|discriminate].
  destruct (errno_ret_in openat_errnos ret); [discriminate|].
  destruct (fd_lookup (m_fds mo) ret); [discriminate|].
  destruct (bv_eqb ret (alloc_fd (m_fds mo))); discriminate.
Qed.

Lemma open_check_spec : forall ms mo path eff,
  at_node segs (NOpen path) ms ->
  check_syscall (sys_input segs ms (Z_to_bv 64 56)) eff mo = open_check (areg ms 11) path eff mo.
Proof.
  intros ms mo path eff (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hrom & Hp).
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  dispatch 56. unfold check_openat, open_check. rewrite Ha0, in_mem_si.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv zeta.
  rewrite <- (wa_unsigned_id (areg ms 11)).
  rewrite (cstr_access_len_aux_bytes_in path path_max) by assumption. unfold open_ci, cstr_len. f_equal.
  unfold Open.check_openat_body, open_body. unfold read_cstr.
  destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
  - rewrite (read_cstr_aux_toolong_bytes_in path_max path); [reflexivity|exact Hlong|exact Hnz|].
    apply bytes_in_app in Hin as [Hin _]. exact Hin.
  - rewrite (read_cstr_aux_bytes_in path path_max); [|lia|exact Hnz|exact Hin].
    destruct path as [|c path']; [reflexivity|].
    cbn [path_eqb]. change (bv_eqb (fd32 (Z_to_bv 64 (-100))) AT_FDCWD32) with true. cbn [negb].
    unfold Open.check_openat_resolved. rewrite Hsl, Hfl. cbn [Z.eqb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma open_body_ok_iff : forall path eff mo mo' evs,
  open_body path eff mo = CheckOk mo' evs <-> nstep (NOpen path) mo eff mo' evs.
Proof.
  intros path eff mo mo' evs. unfold open_body. cbn [nstep].
  destruct (path_max <=? length path)%nat. { rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  destruct path as [|c path']. { rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  destruct (path_is_dirref (c :: path')). { rewrite check_open_result_ok_iff. tauto. }
  destruct (fs_lookup (m_fs mo) (c :: path')).
  - rewrite check_open_result_ok_iff. tauto.
  - rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
Qed.

Lemma open_nstep_strip : forall path eff mo mo' evs, nstep (NOpen path) mo eff mo' evs -> rstrip eff = eff.
Proof.
  intros path eff mo mo' evs [_ H].
  assert (Hor : forall ent, open_result mo ent eff mo' -> rstrip eff = eff).
  { intros ent [(e & _ & -> & _) | (_ & -> & _)]; reflexivity. }
  destruct (path_max <=? length path)%nat. { destruct H as [-> _]; reflexivity. }
  destruct path as [|c path']. { destruct H as [-> _]; reflexivity. }
  destruct (path_is_dirref (c :: path')). { exact (Hor _ H). }
  destruct (fs_lookup (m_fs mo) (c :: path')); [exact (Hor _ H)|]. destruct H as [-> _]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma open_check_eq : forall pathp path eff mo,
  open_check pathp path eff mo = check_copyins_after (open_ci pathp path) eff (open_body path (clear_copyins eff) mo).
Proof. intros. unfold open_check. reflexivity. Qed.

Lemma open_check_ok : forall pathp path eff mo mo' evs,
  open_check pathp path eff mo = CheckOk mo' evs -> nstep (NOpen path) mo (rstrip eff) mo' evs.
Proof.
  intros pathp path eff mo mo' evs H. rewrite open_check_eq in H. apply check_copyins_after_ok_iff in H as [_ H].
  rewrite clear_rstrip in H. apply open_body_ok_iff. exact H.
Qed.

Lemma open_check_complete : forall pathp path eff mo mo' evs,
  nstep (NOpen path) mo eff mo' evs ->
  exists effk, open_check pathp path effk mo = CheckOk mo' evs /\ rstrip effk = eff.
Proof.
  intros pathp path eff mo mo' evs H. pose proof (open_nstep_strip _ _ _ _ _ H) as Hs.
  exists (with_copyins (open_ci pathp path) eff). split.
  - unfold open_check. apply check_copyins_after_ok_iff. split; [destruct eff; reflexivity|].
    rewrite clear_rstrip. replace (rstrip (with_copyins (open_ci pathp path) eff)) with (rstrip eff) by (destruct eff; reflexivity).
    rewrite Hs. apply open_body_ok_iff. exact H.
  - rewrite <- Hs at 2. destruct eff; reflexivity.
Qed.

Lemma open_check_no_unmodeled : forall pathp path eff mo, open_check pathp path eff mo <> CheckUnmodeled.
Proof.
  intros pathp path eff mo. unfold open_check, check_copyins_after, check_copyins.
  assert (Hb : open_body path (clear_copyins eff) mo <> CheckUnmodeled).
  { unfold open_body.
    destruct (path_max <=? length path)%nat; [apply check_ret_only_no_unmodeled|].
    destruct path; [apply check_ret_only_no_unmodeled|].
    destruct (path_is_dirref _); [apply check_open_result_no_unmodeled|].
    destruct (fs_lookup (m_fs mo) _); [apply check_open_result_no_unmodeled|apply check_ret_only_no_unmodeled]. }
  destruct (open_body path (clear_copyins eff) mo); [| |exact Hb]; destruct (access_ranges_eqb _ _); discriminate.
Qed.

Lemma minv_open_insert : forall mo ent,
  minv mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
  intros mo ent (M0 & M1 & M2 & MC & MF & MK & MT & ML & MM & MS) Hfree Hent. unfold minv. minv_setters.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT|split; [exact ML| split; [exact MM| exact MS]]]]]].
  - intros k c. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. destruct Hent.
    + apply MC.
  - intros k p off. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. exact Hent.
    + apply MF.
  - intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. destruct e; first [exact I | destruct Hent].
    + apply MK.
Qed.

Lemma open_result_pres : forall mo ent eff mo',
  minv mo -> m_halted mo = None ->
  open_result mo ent eff mo' ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  m_halted mo' = None /\ minv mo'.
Proof.
  intros mo ent eff mo' Hminv Hh [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
  split; [rewrite m_halted_with_fds; exact Hh|]. apply minv_open_insert; assumption.
Qed.

Lemma open_pres : forall path mo eff mo' evs,
  minv mo -> m_halted mo = None -> nstep (NOpen path) mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros path mo eff mo' evs Hminv Hh [_ H].
  destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
  destruct path as [|c path']. { destruct H as [_ ->]; auto. }
  destruct (path_is_dirref (c :: path')). { exact (open_result_pres _ FdDir _ _ Hminv Hh H I). }
  destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
  - apply (open_result_pres _ _ _ _ Hminv Hh H). cbn. congruence.
  - destruct H as [_ ->]; auto.
Qed.

Lemma open_facts : forall ms mo path,
  at_node segs (NOpen path) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NOpen path).
Proof.
  intros ms mo path Hat Hminv Hh. exists (Z_to_bv 64 56). split; [exact (proj1 Hat)|]. split; [|split; [|split]].
  - intros eff mo' evs. rewrite (open_check_spec _ _ _ _ Hat). apply open_check_ok.
  - intros eff mo' evs HP. destruct (open_check_complete (areg ms 11) path eff mo mo' evs HP) as (effk & Hck & Hst).
    exists effk. rewrite (open_check_spec _ _ _ _ Hat). auto.
  - intros eff. rewrite (open_check_spec _ _ _ _ Hat). apply open_check_no_unmodeled.
  - intros eff mo' evs. apply open_pres; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_check (fd buf count : Z) (eff : resp) (mo : Model) : check_result :=
  match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
  | None => check_ret_only eff (errno_ret EBADF) mo []
  | Some FdDir => check_ret_only eff (errno_ret EISDIR) mo []
  | Some (FdFile p off) =>
      match fs_lookup (m_fs mo) p with
      | None => CheckReject
      | Some data =>
          let bs := file_read data off (Z_to_bv 64 count) in
          let m' := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo in
          match bs, eff with
          | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
          | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
              if bv_eqb a (Z_to_bv 64 buf) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
              then CheckOk m' [] else CheckReject
          | _, _ => CheckReject
          end
      end
  | _ => CheckReject
  end.

Lemma length_file_read_le : forall data off c, (length (file_read data off c) <= word_to_nat c)%nat.
Proof. intros. rewrite file_read_unguarded. apply firstn_le_length. Qed.

Lemma read_check_spec : forall ms mo fd buf count eff,
  at_node segs (NRead fd buf count) ms -> minv mo ->
  check_syscall (sys_input segs ms (Z_to_bv 64 63)) eff mo = read_check fd buf count eff mo.
Proof.
  intros ms mo fd buf count eff (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hb & Hwr) Hminv.
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MM & MS). pose proof max_write_lt as (W1 & W2 & W3 & W4).
  pose proof Hwr as (Hb0 & Hbn & _).
  dispatch 63. unfold check_read, read_check. rewrite Ha0, Ha1, Ha2, in_wmem_si.
  unfold fd32. rewrite abi_low32_small by lia.
  assert (Hok : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { apply access_okb_below; rewrite !unsigned_lit by lia; lia. }
  assert (Hcl : rw_count_clamp (Z_to_bv 64 count) = count).
  { rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; lia). apply unsigned_lit. lia. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk; [|reflexivity].
  pose proof (MK _ _ Hlk) as HK.
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| ]; try contradiction.
  - exfalso. apply MC in Hlk. rewrite unsigned_lit in Hlk by lia. lia.
  - rewrite Hok. cbn [negb].
    destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
    rewrite Hcl. cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
    assert (Hlen : Z.of_nat (length bs) <= count).
    { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
      unfold word_to_nat in L. rewrite unsigned_lit in L by lia. lia. }
    unfold len_word at 1.
    destruct (read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length bs)))) eqn:E.
    2:{ exfalso. refine (read_bytes_map_wr_at segs (ms_mem ms) buf count _ Hwr _ E). rewrite unsigned_lit by lia. lia. }
    destruct bs; reflexivity.
  - rewrite Hok. reflexivity.
Qed.

Lemma listN_eqb_refl : forall l, listN_eqb l l = true.
Proof. intros. apply listN_eqb_eq. reflexivity. Qed.

Lemma read_check_ok_iff : forall fd buf count eff mo mo' evs,
  minv mo ->
  read_check fd buf count eff mo = CheckOk mo' evs <-> nstep (NRead fd buf count) mo eff mo' evs.
Proof.
  intros fd buf count eff mo mo' evs (_ & _ & _ & _ & MF & MK & _). unfold read_check. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  2:{ rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  pose proof (MK _ _ Hlk) as HK.
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| ]; try (split; [discriminate| tauto]).
  - destruct (fs_lookup (m_fs mo) p) as [data|]. 2:{ split; [discriminate|tauto]. }
    cbv zeta. destruct (file_read data off (Z_to_bv 64 count)) as [|b bs'] eqn:Ebs.
    + rewrite check_ret_only_ok_iff. cbn [delivered_writes]. change (len_word (@nil byte)) with (Z_to_bv 64 0). tauto.
    + cbn [delivered_writes]. destruct eff as [ret ws zs us cs ci]. split.
      * intros H. destruct ws as [|[a bs''] [|? ?]]; try discriminate. destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb a (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
        destruct (listN_eqb bs'' (b :: bs')) eqn:E2; [|discriminate].
        destruct (bv_eqb ret (len_word (b :: bs'))) eqn:E3; [|discriminate].
        cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3.
        subst. repeat split; reflexivity.
      * intros (-> & Heff & ->). inversion Heff; subst. rewrite !bv_eqb_refl, listN_eqb_refl. reflexivity.
  - rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
Qed.

Lemma read_check_no_unmodeled : forall fd buf count eff mo, read_check fd buf count eff mo <> CheckUnmodeled.
Proof.
  intros fd buf count eff mo. unfold read_check.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| ]|]; try discriminate; try apply check_ret_only_no_unmodeled.
  destruct (fs_lookup (m_fs mo) p); [|discriminate]. cbv zeta.
  destruct (file_read _ _ _); [apply check_ret_only_no_unmodeled|].
  destruct eff as [ret [|[a bs'] [|? ?]] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate.
  destruct (_ && _); discriminate.
Qed.

Lemma minv_update_file : forall mo k p off off',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros mo k p off off' (M0 & M1 & M2 & MC & MF & MK & MT & ML & MM & MS) Hk. unfold minv. minv_setters.
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT|split; [exact ML| split; [exact MM| exact MS]]]]]].
  - intros k' c. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [intros H; discriminate| apply MC].
  - intros k' p' o. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MF].
    intros H. inversion H; subst. exact (MF _ _ _ Hk).
  - intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MK]. intros H; inversion H; exact I.
Qed.

Lemma read_pres : forall fd buf count mo eff mo' evs,
  minv mo -> m_halted mo = None -> nstep (NRead fd buf count) mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros fd buf count mo eff mo' evs Hminv Hh [_ H].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| ]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
    split; [rewrite m_halted_with_fds; exact Hh|]. eapply minv_update_file; eassumption.
  - destruct H as [_ ->]. auto.
  - destruct H as [_ ->]. auto.
Qed.

Lemma read_nstep_strip : forall fd buf count mo eff mo' evs, nstep (NRead fd buf count) mo eff mo' evs -> rstrip eff = eff.
Proof.
  intros fd buf count mo eff mo' evs [_ H].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| ]|]; try contradiction.
  - destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [-> _]. reflexivity.
  - destruct H as [-> _]; reflexivity.
  - destruct H as [-> _]; reflexivity.
Qed.

Lemma read_facts : forall ms mo fd buf count,
  at_node segs (NRead fd buf count) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NRead fd buf count).
Proof.
  intros ms mo fd buf count Hat Hminv Hh. apply (facts_strict ms mo _ (Z_to_bv 64 63) (proj1 Hat)).
  - intros eff mo' evs. rewrite (read_check_spec _ _ _ _ _ _ Hat Hminv). apply read_check_ok_iff. exact Hminv.
  - apply read_nstep_strip.
  - intros eff. rewrite (read_check_spec _ _ _ _ _ _ Hat Hminv). apply read_check_no_unmodeled.
  - intros eff mo' evs. apply read_pres; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma minv_remove : forall mo fd, minv mo -> 3 <= fd < 2^32 ->
  minv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
  intros mo fd (M0 & M1 & M2 & MC & MF & MK & MT & ML & MM & MS) Hfd. unfold minv. minv_setters.
  rewrite !fd_lookup_remove.
  assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
  { intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  rewrite !Hne by lia.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT|split; [exact ML| split; [exact MM| exact MS]]]]]].
  - intros k c. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MC].
  - intros k p off. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MF].
  - intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MK].
Qed.

Lemma close_pres : forall fd mo eff mo' evs,
  minv mo -> m_halted mo = None -> nstep (NClose fd) mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros fd mo eff mo' evs Hminv Hh (_ & Hfd & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
  split; [rewrite m_halted_with_fds; exact Hh|]. apply minv_remove; assumption.
Qed.

Lemma close_facts : forall ms mo fd,
  at_node segs (NClose fd) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NClose fd).
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (Z_to_bv 64 57)) eff mo =
            match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
            | None => check_ret_only eff (errno_ret EBADF) mo []
            | Some _ => check_ret_only eff (Z_to_bv 64 0) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []
            end).
  { intros eff. dispatch 57. unfold check_close. rewrite Ha0. unfold fd32. rewrite abi_low32_small by lia. reflexivity. }
  apply (facts_strict ms mo _ (Z_to_bv 64 57) Hsvc).
  - intros eff mo' evs. rewrite Hchk. cbn [nstep]. destruct (fd_lookup _ _); rewrite check_ret_only_ok_iff; unfold efferr, eff0; tauto.
  - intros eff mo' evs (_ & _ & HP). destruct (fd_lookup _ _); destruct HP as [-> _]; reflexivity.
  - intros eff. rewrite Hchk. destruct (fd_lookup _ _); apply check_ret_only_no_unmodeled.
  - intros eff mo' evs. apply close_pres; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ioctl_facts : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NIoctl fd req).
Proof.
  intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh.
  eapply facts_ret_only; [exact Hsvc | exact Hminv | exact Hh | |].
  - intros eff. dispatch 29. unfold check_ioctl. rewrite Ha0, Ha1. subst req.
    unfold fd32, cmd32. rewrite !abi_low32_small by lia.
    destruct Hminv as (M0 & M1 & M2 & _).
    assert (Hl : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
    { assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
    destruct Hl as [c ->]. reflexivity.
  - intros eff mo' evs. cbn [nstep]. unfold efferr. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma minv_with_tid : forall mo t, minv mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minv (with_tid t mo).
Proof.
  intros mo t (M0 & M1 & M2 & MC & MF & MK & MT & ML & MM & MS) Ht. unfold minv. minv_setters.
  repeat split; try assumption; try lia. all: match goal with G : Some _ = Some _ |- _ => inversion G; subst; lia end.
Qed.

Lemma set_tid_pres : forall mo eff mo' evs,
  minv mo -> m_halted mo = None -> nstep NSetTid mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros mo eff mo' evs Hminv Hh (_ & t & _ & Ht). destruct (m_tid mo); [destruct Ht as [_ ->]; auto|].
  destruct Ht as [Hr ->]. split; [rewrite m_halted_with_tid; exact Hh|]. apply minv_with_tid; assumption.
Qed.

Lemma set_tid_facts : forall ms mo,
  at_node segs NSetTid ms -> minv mo -> m_halted mo = None -> node_facts ms mo NSetTid.
Proof.
  intros ms mo Hsvc Hminv Hh.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (Z_to_bv 64 96)) eff mo = check_set_tid_address eff mo).
  { intros eff. dispatch 96. reflexivity. }
  apply (facts_strict ms mo _ (Z_to_bv 64 96) Hsvc).
  - intros [ret ws zs us cs ci] mo' evs. rewrite Hchk. unfold check_set_tid_address. cbn [nstep]. unfold eff0. split.
    + intros H. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (m_tid mo) as [t0|].
      * destruct (bv_eqb ret t0) eqn:E; [|discriminate]. apply bv_eqb_eq in E. inversion H; subst.
        split; [reflexivity|]. exists t0. auto.
      * destruct ((0 <? bv_unsigned ret) && (bv_unsigned ret <? PID_MAX_ENVELOPE)) eqn:E; [|discriminate].
        inversion H; subst. apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
        split; [reflexivity|]. exists ret. auto.
    + intros (-> & t & Heff & Ht). inversion Heff; subst. destruct (m_tid mo) as [t0|].
      * destruct Ht as [-> ->]. rewrite bv_eqb_refl. reflexivity.
      * destruct Ht as [[H1 H2] ->]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - intros eff mo' evs (_ & t & -> & _). reflexivity.
  - intros [ret ws zs us cs ci]. rewrite Hchk. unfold check_set_tid_address.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (m_tid mo); [destruct (bv_eqb _ _); discriminate| destruct (_ && _); discriminate].
  - intros eff mo' evs. apply set_tid_pres; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma exit_check : forall ms mo c x8 eff,
  at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff mo
  = check_ret_only eff (Z_to_bv 64 0) (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) mo) [].
Proof.
  intros ms mo c x8 eff [Hsvc Ha0] Hx8.
  destruct Hsvc as [Hsvc|Hsvc]; rewrite Hsvc in Hx8; inversion Hx8; subst;
    [dispatch 93 | dispatch 94]; unfold check_exit; rewrite Ha0; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\
  m_lim m' = m_lim m /\ m_time m' = m_time m /\
  vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m) /\
  (m_vm_lazy m = [] -> m_vm_materialized m = [] -> m_vm_lazy m' = [] /\ m_vm_materialized m' = []).

Lemma vm_only_refl : forall m, vm_only m m.
Proof. intros m. unfold vm_only. do 7 (split; [reflexivity|]). tauto. Qed.

Lemma vm_only_trans : forall m1 m2 m3, vm_only m1 m2 -> vm_only m2 m3 -> vm_only m1 m3.
Proof.
  intros m1 m2 m3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A9) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B9).
  unfold vm_only. do 7 (split; [congruence|]). tauto.
Qed.

Lemma vm_only_with_vmmaps : forall h m, vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m (with_vmmaps h m).
Proof. intros h m Hsp. unfold vm_only. do 6 (split; [reflexivity|]). split; [exact Hsp|]. tauto. Qed.

Lemma maps_subtract_nil : forall lo hi, maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma vm_only_forget : forall lo hi m, vm_only m (vm_forget_range lo hi m).
Proof.
  intros lo hi m. unfold vm_only. do 7 (split; [reflexivity|]).
  intros H1 H2. unfold vm_forget_range, with_vm_backing, m_vm_lazy, m_vm_materialized in *. cbn.
  rewrite H1, H2. split; reflexivity.
Qed.

Lemma vm_only_forget_ranges : forall l m, vm_only m (forget_vm_ranges l m).
Proof.
  induction l as [|[a n] l IH]; intros m; cbn [forget_vm_ranges]; [apply vm_only_refl|].
  eapply vm_only_trans; [apply vm_only_forget| apply IH].
Qed.

Lemma vm_only_backing_off : forall flags a n m,
  mmap_noreserve_b flags = false -> vm_only m (with_mmap_backing flags a n m).
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. apply vm_only_refl. Qed.

Lemma vm_only_destroyed : forall a n h m, vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m (with_mmap_destroyed a n h m).
Proof. intros a n h m H. unfold with_mmap_destroyed. eapply vm_only_trans; [| apply vm_only_forget]. apply vm_only_with_vmmaps. exact H. Qed.

Lemma vm_only_replacement_off : forall flags a n m,
  mmap_noreserve_b flags = false -> vm_only m (with_mmap_replacement flags a n m).
Proof.
  intros. unfold with_mmap_replacement. eapply vm_only_trans; [apply vm_only_forget| apply vm_only_backing_off; assumption].
Qed.

Lemma vm_only_brk_next : forall m req r, vm_only m (with_brk_next m req r).
Proof.
  intros. unfold with_brk_next. cbv zeta. eapply vm_only_trans; [| apply vm_only_forget_ranges]. apply vm_only_with_vmmaps. reflexivity.
Qed.

Lemma vm_only_mprotect_next : forall m a n, vm_only m (mprotect_model_next m a n).
Proof. intros. unfold mprotect_model_next. apply vm_only_with_vmmaps. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vm_only_madvise_next : forall m a n, vm_only m (madvise_dontneed_next m a n).
Proof.
  intros m a n. unfold vm_only. do 7 (split; [reflexivity|]).
  intros H1 H2. unfold madvise_dontneed_next, with_vm_backing, m_vm_lazy, m_vm_materialized in *. cbn.
  rewrite H1, H2. split; reflexivity.
Qed.

(* [comment removed for export] *)
Ltac vm_only_solve :=
  lazymatch goal with
  | |- vm_only ?m ?m => apply vm_only_refl
  | |- vm_only _ (with_vmmaps _ ?X) => apply (vm_only_trans _ X); [vm_only_solve | apply vm_only_with_vmmaps; reflexivity]
  | |- vm_only _ (with_mmap_backing _ _ _ ?X) => apply (vm_only_trans _ X); [vm_only_solve | apply vm_only_backing_off; assumption]
  | |- vm_only _ (with_mmap_replacement _ _ _ ?X) => apply (vm_only_trans _ X); [vm_only_solve | apply vm_only_replacement_off; assumption]
  | |- vm_only _ (with_mmap_destroyed _ _ _ ?X) => apply (vm_only_trans _ X); [vm_only_solve | apply vm_only_destroyed; reflexivity]
  | |- vm_only _ (vm_forget_range _ _ ?X) => apply (vm_only_trans _ X); [vm_only_solve | apply vm_only_forget]
  | |- vm_only _ (forget_vm_ranges _ ?X) => apply (vm_only_trans _ X); [vm_only_solve | apply vm_only_forget_ranges]
  | |- vm_only _ (with_brk_next _ _ _) => apply vm_only_brk_next
  | |- vm_only _ (mprotect_model_next _ _ _) => apply vm_only_mprotect_next
  | |- vm_only _ (madvise_dontneed_next _ _ _) => apply vm_only_madvise_next
  end.

Ltac crush_check H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (? & ? & ?); subst
          | (match ?x with _ => _ end) = _ => destruct x
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).

Lemma check_brk_shape : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> vm_only m m' /\ rstrip eff = eff /\ evs = [].
Proof. intros req eff m m' evs H. unfold check_brk in H. crush_check H; (split; [vm_only_solve| split; reflexivity]). Qed.

Lemma check_mmap_shape : forall addr len prot flags fd off eff m m' evs,
  mmap_noreserve_b flags = false ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_only m m' /\ rstrip eff = eff /\ evs = [].
Proof. intros until evs; intros Hnr H. unfold check_mmap in H. crush_check H; (split; [vm_only_solve| split; reflexivity]). Qed.

Lemma check_munmap_shape : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> vm_only m m' /\ rstrip eff = eff /\ evs = [].
Proof. intros until evs; intros H. unfold check_munmap in H. crush_check H; (split; [vm_only_solve| split; reflexivity]). Qed.

Lemma check_mprotect_shape : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> vm_only m m' /\ rstrip eff = eff /\ evs = [].
Proof. intros until evs; intros H. unfold check_mprotect in H. crush_check H; (split; [vm_only_solve| split; reflexivity]). Qed.

Lemma check_madvise_shape : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> vm_only m m' /\ rstrip eff = eff /\ evs = [].
Proof. intros until evs; intros H. unfold check_madvise in H. crush_check H; (split; [vm_only_solve| split; reflexivity]). Qed.

Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> minv mo -> minv mo'.
Proof.
  intros mo mo' (Hf & _ & Hs & Hp & _ & _ & Hsp & Hl) Hm.
  pose proof Hm as (_ & _ & _ & _ & _ & _ & _ & ML & MM & MS). destruct (Hl ML MM) as [L1 L2].
  unfold minv in *. unfold m_fds, m_fs, m_tid in *. rewrite Hf, Hs, Hp, Hsp. rewrite L1, L2. tauto.
Qed.

Lemma halted_vm_only : forall mo mo', vm_only mo mo' -> m_halted mo' = m_halted mo.
Proof. intros mo mo' (_ & _ & _ & Hp & _). unfold m_halted. rewrite Hp. reflexivity. Qed.

Ltac no_unm :=
  repeat first [ apply check_ret_only_no_unmodeled
               | discriminate
               | match goal with |- (match ?x with _ => _ end) <> _ => destruct x end
               | progress cbv zeta beta iota ].

Lemma munmap_safe_no_unmodeled : forall addr len eff m,
  munmap_safe_b addr len (m_vmmaps m) = true -> check_munmap addr len eff m <> CheckUnmodeled.
Proof.
  intros addr len eff m. unfold munmap_safe_b, check_munmap.
  destruct (negb _ || w_is0 len); [intros _; apply check_ret_only_no_unmodeled|]. cbv zeta.
  destruct (TASK_SIZE <? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (map_has _ _ _); [intros _; no_unm|]. cbn [orb]. intros ->. apply check_ret_only_no_unmodeled.
Qed.

Lemma mprotect_safe_no_unmodeled : forall addr len prot eff m,
  mprotect_safe_b addr len prot (m_vmmaps m) = true -> check_mprotect addr len prot eff m <> CheckUnmodeled.
Proof.
  intros addr len prot eff m. unfold mprotect_safe_b, check_mprotect.
  destruct (mprotect_grows_conflict_b prot); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (w_is0 len); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (mprotect_modeled_b prot); [|discriminate]. cbn [negb]. cbv zeta.
  destruct (map_contains (vm_noaccess _) _ _ && map_contains _ _ _); [intros _; no_unm|].
  cbn [orb]. intros ->. no_unm.
Qed.

Lemma madvise_safe_no_unmodeled : forall addr len eff m,
  madvise_safe_b addr len (m_vmmaps m) = true ->
  check_madvise addr len (Z_to_bv 64 4) eff m <> CheckUnmodeled.
Proof.
  intros addr len eff m. unfold madvise_safe_b, check_madvise.
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  change (negb (madvise_dontneed_b (Z_to_bv 64 4))) with false. cbv iota.
  destruct (w_is0 len); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
  cbv zeta. intros ->. no_unm.
Qed.

Lemma mmap_fixed_gate_no_unmodeled : forall addr nZ h eff m (k1 k2 k3 : check_result),
  mmap_fixed_gate_b addr nZ h = true ->
  k1 <> CheckUnmodeled -> k2 <> CheckUnmodeled -> k3 <> CheckUnmodeled ->
  (if two_pow_64 <=? bv_unsigned addr + nZ then check_ret_only eff (errno_ret ENOMEM) m []
   else if negb (bv_unsigned addr + nZ <=? alloc_top h) then CheckUnmodeled
   else if negb (bv_unsigned addr mod page_size =? 0) then check_ret_only eff (errno_ret EINVAL) m []
   else if negb (0 <? bv_unsigned addr) then CheckUnmodeled
   else if region_free (vm_reserved h) addr (Z_to_bv 64 nZ) && map_contains (vm_maps h) addr (Z_to_bv 64 nZ) then k1
   else if region_free (vm_reserved h ++ vm_maps h) addr (Z_to_bv 64 nZ) then k2
   else if region_free (vm_reserved h) addr (Z_to_bv 64 nZ) then k3
   else CheckUnmodeled) <> CheckUnmodeled.
Proof.
  intros addr nZ h eff m k1 k2 k3 Hg H1 H2 H3. unfold mmap_fixed_gate_b in Hg. cbv zeta in Hg.
  destruct (two_pow_64 <=? _); [apply check_ret_only_no_unmodeled|].
  destruct (negb (_ <=? alloc_top _)); [discriminate|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [apply check_ret_only_no_unmodeled|].
  destruct (negb (0 <? bv_unsigned addr)); [discriminate|].
  destruct (region_free (vm_reserved h) addr _ && map_contains _ _ _); [exact H1|]. cbn [orb] in Hg.
  destruct (region_free (vm_reserved h ++ _) addr _); [exact H2|]. cbn [orb] in Hg. rewrite Hg. exact H3.
Qed.

Lemma mmap_safe_no_unmodeled : forall addr len prot flags fd off eff m,
  mmap_safe_b addr len prot flags fd off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros addr len prot flags fd off eff m. unfold mmap_safe_b, check_mmap.
  destruct (mmap_off_aligned_b off); [|discriminate].
  destruct (mmap_anon_b flags); [|discriminate]. cbn [andb negb].
  destruct (w_is0 len). { intros ->. apply check_ret_only_no_unmodeled. }
  destruct (mmap_modeled_b prot flags off); [intros _; no_unm|].
  destruct (mmap_noaccess_b prot flags off); [intros _; no_unm|]. cbn [orb].
  destruct (mmap_fixed_noaccess_b prot flags off).
  { cbn [andb]. intros Hg.
    assert (Hg2 : mmap_fixed_gate_b addr (page_round_up_Z (bv_unsigned len)) (m_vmmaps m) = true).
    { destruct (mmap_fixed_gate_b _ _ _); [reflexivity|]. rewrite Bool.andb_false_r in Hg. discriminate. }
    cbv zeta. apply mmap_fixed_gate_no_unmodeled; [exact Hg2| no_unm| no_unm| no_unm]. }
  destruct (mmap_fixed_rw_b prot flags off); [|discriminate].
  cbn [andb orb]. intros Hg. cbv zeta. apply mmap_fixed_gate_no_unmodeled; [exact Hg| no_unm| no_unm| no_unm].
Qed.

(* [comment removed for export] *)
Lemma mm_facts : forall ms mo n i x8 (chk : resp -> check_result) (G : Prop),
  node_input n = Some i ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (evs = [] /\ G /\ syscall_spec i mo (Ok eff mo' evs))) ->
  G ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_only mo mo' /\ rstrip eff = eff /\ evs = []) ->
  node_facts ms mo n.
Proof.
  intros ms mo n i x8 chk G Hi Hn HG Hsvc Hminv Hh Hc1 Hc2 Hnu Hshape.
  assert (Hstrip : forall eff mo' evs, chk eff = CheckOk mo' evs -> rstrip eff = eff).
  { intros eff mo' evs H. exact (proj1 (proj2 (Hshape _ _ _ H))). }
  apply (facts_strict ms mo n x8 Hsvc).
  - intros eff mo' evs. rewrite Hc1, Hn, <- check_syscall_ok_iff, Hc2. split; [|tauto].
    intros H. split; [exact (proj2 (proj2 (Hshape _ _ _ H)))|]. split; [exact HG| exact H].
  - intros eff mo' evs HP. apply Hn in HP as (_ & _ & HP). apply check_syscall_ok_iff in HP. rewrite Hc2 in HP. exact (Hstrip _ _ _ HP).
  - intros eff. rewrite Hc1. apply Hnu.
  - intros eff mo' evs HP. apply Hn in HP as (_ & _ & HP). apply check_syscall_ok_iff in HP. rewrite Hc2 in HP.
    apply Hshape in HP as (Hv & _ & _). split.
    + rewrite (halted_vm_only _ _ Hv). exact Hh.
    + eapply minv_vm_only; eassumption.
Qed.

Ltac dispatch_pure K :=
  lazymatch K with
  | 214 => rewrite check_syscall_brk by reflexivity
  | 222 => rewrite check_syscall_mmap by reflexivity
  | 215 => rewrite check_syscall_munmap by reflexivity
  | 226 => rewrite check_syscall_mprotect by reflexivity
  | 233 => rewrite check_syscall_madvise by reflexivity
  end; cbn [in_arg in_args nth pure_input].

Definition node_facts_ns (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs ->
     m_halted mo' = None /\ m_vm_lazy mo' = []) /\
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff -> nstep n mo eff mo' evs) /\
  (forall eff mo' evs, nstep n mo eff mo' evs ->
     check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs
     /\ ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) /\
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo').

Lemma mm_facts_ns : forall ms mo n i x8 (chk : resp -> check_result) (G : Prop),
  node_input n = Some i ->
  (forall eff mo' evs, nstep n mo eff mo' evs <->
     (evs = [] /\ G /\ (syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg ACFG i mo eff))) ->
  G ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  in_sysno (sys_input segs ms x8) = in_sysno i ->
  in_arg (sys_input segs ms x8) 0 = in_arg i 0 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_only mo mo' /\ rstrip eff = eff /\ evs = []) ->
  node_facts_ns ms mo n.
Proof.
  intros ms mo n i x8 chk G Hi Hn HG Hsvc Hminv Hh Hno Ha0 Hc1 Hc2 Hnu Hshape.
  assert (Hsp : forall eff, spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff <-> spurious_refusal_cfg ACFG i mo eff).
  { intros eff. apply spurious_refusal_transport; [exact Hno| exact Ha0|].
    intros eff' m' evs'. rewrite <- !check_syscall_ok_iff, Hc1, Hc2. reflexivity. }
  assert (Hok : forall eff mo' evs, chk eff = CheckOk mo' evs -> m_halted mo' = None /\ minv mo').
  { intros eff mo' evs H. apply Hshape in H as (Hv & _ & _). split.
    - rewrite (halted_vm_only _ _ Hv). exact Hh.
    - eapply minv_vm_only; eassumption. }
  exists x8. split; [exact Hsvc|]. split; [|split; [|split; [|split]]].
  - intros eff mo' evs H. rewrite Hc1 in H. destruct (Hok _ _ _ H) as [H1 H2].
    split; [exact H1| exact (minv_nolazy _ H2)].
  - intros eff mo' evs H Hns. rewrite Hc1 in H. apply Hn.
    split; [exact (proj2 (proj2 (Hshape _ _ _ H)))|]. split; [exact HG|].
    split; [apply check_syscall_ok_iff; rewrite Hc2; exact H| rewrite <- (Hsp eff); exact Hns].
  - intros eff mo' evs HP. apply Hn in HP as (_ & _ & Hs & Hns). split.
    + rewrite Hc1, <- Hc2. apply check_syscall_ok_iff. exact Hs.
    + rewrite (Hsp eff). exact Hns.
  - intros eff. rewrite Hc1. apply Hnu.
  - intros eff mo' evs HP. apply Hn in HP as (_ & _ & Hs & _). apply check_syscall_ok_iff in Hs. rewrite Hc2 in Hs.
    exact (Hok _ _ _ Hs).
Qed.

Lemma brk_facts : forall ms mo req,
  at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo -> node_facts_ns ms mo (NBrk req).
Proof.
  intros ms mo req (Hsvc & Ha0) Hminv Hh _.
  eapply (mm_facts_ns ms mo (NBrk req) _ _ (fun eff => check_brk (Z_to_bv 64 req) eff mo) True);
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | reflexivity
    | | | | |].
  - rewrite in_a0_si, Ha0. reflexivity.
  - intros eff. dispatch 214. rewrite Ha0. reflexivity.
  - intros eff. dispatch_pure 214. reflexivity.
  - intros [r ws zs us cs ci]. unfold check_brk. destruct ws; [|discriminate]. destruct cs; [|discriminate].
    destruct ci; [|discriminate]. destruct (_ && _); discriminate.
  - intros eff mo' evs. apply check_brk_shape.
Qed.

Lemma mmap_facts : forall ms mo addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
  node_facts_ns ms mo (NMmap addr len prot flags).
Proof.
  intros ms mo addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hnr) Hminv Hh Hsafe.
  eapply (mm_facts_ns ms mo (NMmap addr len prot flags) _ _
            (fun eff => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                   (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo) (mmap_noreserve_b (Z_to_bv 64 flags) = false));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hnr | exact Hsvc | exact Hminv | exact Hh | reflexivity
    | | | | |].
  - rewrite in_a0_si, Ha0. reflexivity.
  - intros eff. dispatch 222. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
  - intros eff. dispatch_pure 222. reflexivity.
  - intros eff. apply mmap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mmap_shape. exact Hnr.
Qed.

Lemma munmap_facts : forall ms mo addr len,
  at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
  node_facts ms mo (NMunmap addr len).
Proof.
  intros ms mo addr len (Hsvc & Ha0 & Ha1) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMunmap addr len) _ _
            (fun eff => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo) True);
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 215. rewrite Ha0, Ha1. reflexivity.
  - intros eff. dispatch_pure 215. reflexivity.
  - intros eff. apply munmap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_munmap_shape.
Qed.

Lemma mprotect_facts : forall ms mo addr len prot,
  at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
  node_facts_ns ms mo (NMprotect addr len prot).
Proof.
  intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
  eapply (mm_facts_ns ms mo (NMprotect addr len prot) _ _
            (fun eff => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo) True);
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | reflexivity
    | | | | |].
  - rewrite in_a0_si, Ha0. reflexivity.
  - intros eff. dispatch 226. rewrite Ha0, Ha1, Ha2. reflexivity.
  - intros eff. dispatch_pure 226. reflexivity.
  - intros eff. apply mprotect_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mprotect_shape.
Qed.

(* [comment removed for export] *)
Lemma int32_madv_dontneed : int32 (Z_to_bv 64 4) = Z_to_bv 64 4.
Proof. reflexivity. Qed.

Lemma madvise_facts : forall ms mo addr len,
  at_node segs (NMadvise addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMadvise addr len) mo ->
  node_facts ms mo (NMadvise addr len).
Proof.
  intros ms mo addr len (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMadvise addr len) _ _
            (fun eff => check_madvise (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 4) eff mo) True);
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 233. rewrite Ha0, Ha1, Ha2. rewrite int32_madv_dontneed. reflexivity.
  - intros eff. dispatch_pure 233. rewrite int32_madv_dontneed. reflexivity.
  - intros eff. apply madvise_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_madvise_shape.
Qed.

(* [comment removed for export] *)
Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <->
  (check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs /\ mm_ns (NBrk req) mo eff).
Proof.
  intros. cbn [nstep node_input mm_ns]. rewrite <- check_syscall_ok_iff. dispatch_pure 214.
  split; [tauto|]. intros [H Hns]. split; [exact (proj2 (proj2 (check_brk_shape _ _ _ _ _ H)))| split; assumption].
Qed.

Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  (mmap_noreserve_b (Z_to_bv 64 flags) = false /\
   check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs /\
   mm_ns (NMmap addr len prot flags) mo eff).
Proof.
  intros. cbn [nstep node_input mm_ns]. rewrite <- check_syscall_ok_iff. dispatch_pure 222.
  split; [tauto|]. intros (Hnr & H & Hns).
  split; [exact (proj2 (proj2 (check_mmap_shape _ _ _ _ _ _ _ _ _ _ Hnr H)))| split; [exact Hnr| split; assumption]].
Qed.

Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 215.
  split; [tauto|]. intros H. split; [exact (proj2 (proj2 (check_munmap_shape _ _ _ _ _ _ H)))| exact H].
Qed.

Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  (check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs /\
   mm_ns (NMprotect addr len prot) mo eff).
Proof.
  intros. cbn [nstep node_input mm_ns]. rewrite <- check_syscall_ok_iff. dispatch_pure 226.
  split; [tauto|]. intros [H Hns]. split; [exact (proj2 (proj2 (check_mprotect_shape _ _ _ _ _ _ _ H)))| split; assumption].
Qed.

Lemma nstep_madvise_iff : forall addr len mo eff mo' evs,
  nstep (NMadvise addr len) mo eff mo' evs <->
  check_madvise (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 4) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 233. rewrite int32_madv_dontneed.
  split; [tauto|]. intros H. split; [exact (proj2 (proj2 (check_madvise_shape _ _ _ _ _ _ _ H)))| exact H].
Qed.

(* [comment removed for export] *)
Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMadvise _ _ => True | _ => False end ->
  nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [].
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction.
  - apply nstep_brk_iff in H as [H _]. pose proof (check_brk_shape _ _ _ _ _ H); tauto.
  - apply nstep_mmap_iff in H as (Hnr & H & _). pose proof (check_mmap_shape _ _ _ _ _ _ _ _ _ _ Hnr H); tauto.
  - apply nstep_munmap_iff in H. pose proof (check_munmap_shape _ _ _ _ _ _ H); tauto.
  - apply nstep_mprotect_iff in H as [H _]. pose proof (check_mprotect_shape _ _ _ _ _ _ _ H); tauto.
  - apply nstep_madvise_iff in H. pose proof (check_madvise_shape _ _ _ _ _ _ _ H); tauto.
Qed.

(* [comment removed for export] *)
Lemma nsafe_mmap_rw : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hl. cbn [nsafe]. unfold mmap_safe_b. rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma nsafe_mmap_none : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hl. cbn [nsafe]. unfold mmap_safe_b. rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_fd_range : forall mo,
  minv mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096.
Proof.
  intros mo (M0 & M1 & M2 & _) Hfree. pose proof (alloc_fd_le (m_fds mo)) as Hle.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (H : forall z e, fd_lookup (m_fds mo) (Z_to_bv 64 z) = Some e -> 0 <= z < 2^64 -> bv_unsigned fd <> z).
  { intros z e Hz Hr E. rewrite <- (Z_to_bv_bv_unsigned fd), E in Hfree. congruence. }
  pose proof (H 0 _ M0 ltac:(lia)). pose proof (H 1 _ M1 ltac:(lia)). pose proof (H 2 _ M2 ltac:(lia)).
  pose proof (bv_unsigned_in_range 64 fd). lia.
Qed.

(* [comment removed for export] *)
Lemma minv_preserved : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hminv Hh H.
  destruct n.
  - destruct H as (k & _ & _ & -> & _); auto.
  - destruct H as [-> _]; auto.
  - eapply open_pres; eassumption.
  - eapply read_pres; eassumption.
  - eapply close_pres; eassumption.
  - destruct H as (_ & _ & ->); auto.
  - eapply set_tid_pres; eassumption.
  - destruct H.
  - destruct (nstep_mm_vm_only (NBrk req) mo eff mo' evs I H) as [Hv _].
    split; [rewrite (halted_vm_only _ _ Hv); exact Hh | eapply minv_vm_only; eassumption].
  - destruct (nstep_mm_vm_only (NMmap addr len prot flags) mo eff mo' evs I H) as [Hv _].
    split; [rewrite (halted_vm_only _ _ Hv); exact Hh | eapply minv_vm_only; eassumption].
  - destruct (nstep_mm_vm_only (NMunmap addr len) mo eff mo' evs I H) as [Hv _].
    split; [rewrite (halted_vm_only _ _ Hv); exact Hh | eapply minv_vm_only; eassumption].
  - destruct (nstep_mm_vm_only (NMprotect addr len prot) mo eff mo' evs I H) as [Hv _].
    split; [rewrite (halted_vm_only _ _ Hv); exact Hh | eapply minv_vm_only; eassumption].
  - destruct (nstep_mm_vm_only (NMadvise addr len) mo eff mo' evs I H) as [Hv _].
    split; [rewrite (halted_vm_only _ _ Hv); exact Hh | eapply minv_vm_only; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma all_facts : forall n ms mo,
  match n with NExit _ | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ => False | _ => True end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts ms mo n.
Proof.
  intros n ms mo Hne Hat Hminv Hh Hsafe. destruct n; try contradiction.
  - apply write_facts; assumption.
  - apply writev_facts; assumption.
  - apply open_facts; assumption.
  - apply read_facts; assumption.
  - apply close_facts; assumption.
  - apply ioctl_facts; assumption.
  - apply set_tid_facts; assumption.
  - apply munmap_facts; assumption.
  - apply madvise_facts; assumption.
Qed.

Lemma alloc_facts : forall n ms mo, alloc_node n = true ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts_ns ms mo n.
Proof.
  intros n ms mo Ha Hat Hminv Hh Hsafe. destruct n; try discriminate Ha.
  - apply brk_facts; assumption.
  - apply mmap_facts; assumption.
  - apply mprotect_facts; assumption.
Qed.

Lemma at_node_nonalloc_svc : forall n ms, alloc_node n = false -> at_node segs n ms ->
  exists x8, ms_svc_pending ms = Some x8 /\ ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros n ms Ha Hat. destruct n; try discriminate Ha; cbn [at_node] in Hat;
    match type of Hat with
    | (ms_svc_pending ms = Some _ \/ _) /\ _ => destruct Hat as [[H|H] _]
    | ms_svc_pending ms = Some _ /\ _ => destruct Hat as [H _]
    | ms_svc_pending ms = Some _ => rename Hat into H
    end;
    (eexists; split; [exact H| apply alloc_no_b_false; vm_compute; reflexivity]).
Qed.

End PerNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

Lemma exit_node_facts : forall segs ms mo c,
  at_node segs (NExit c) ms -> m_halted mo = None ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
  /\ sstep segs (mkCfg ms mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg ms (with_halted (exit_code c) mo))).
Proof.
  intros segs ms mo c Hat Hh.
  assert (Hx : exists x8, ms_svc_pending ms = Some x8).
  { destruct (proj1 Hat) as [H|H]; eexists; exact H. }
  destruct Hx as [x8 Hsvc].
  apply (exit_kit segs ms mo x8 (exit_code c) Hsvc Hh).
  - intros eff mo' evs. rewrite (exit_check segs ms mo c x8 eff Hat Hsvc). rewrite check_ret_only_ok_iff. unfold eff0, exit_code. tauto.
  - intros eff. rewrite (exit_check segs ms mo c x8 eff Hat Hsvc). apply check_ret_only_no_unmodeled.
Qed.

Lemma nonexit_node_facts : forall segs n ms mo,
  match n with NExit _ => False | _ => True end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
  (forall evs X, sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros segs n ms mo Hne Hat Hminv Hh Hsafe.
  destruct (alloc_node n) eqn:Ha.
  - destruct (alloc_facts segs n ms mo Ha Hat Hminv Hh Hsafe) as (x8 & Hsvc & Hok & Hsnd & Hcpl & Hnu & Hpres).
    destruct (node_kit_ns segs ms mo x8 (nstep n mo) Hsvc Hh Hok Hsnd Hcpl Hnu) as (Hc & Hs & Hp).
    split; [exact Hc|]. split; [|exact Hp].
    intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. auto.
  - assert (Hne' : match n with NExit _ | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ => False | _ => True end)
      by (destruct n; first [exact I | discriminate Ha | exact Hne]).
    destruct (all_facts segs n ms mo Hne' Hat Hminv Hh Hsafe) as (x8 & Hsvc & Hsnd & Hcpl & Hnu & Hpres).
    destruct (node_kit segs ms mo x8 (nstep n mo) Hsvc Hh Hsnd Hcpl Hnu) as (Hc & Hs & Hp).
    { intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. split; [exact H1| exact (minv_nolazy _ H2)]. }
    destruct (at_node_nonalloc_svc segs n ms Ha Hat) as (x8' & Hsvc' & Hnin).
    pose proof (transparent_nonalloc segs ms mo x8' Hsvc' Hnin) as Ht.
    split; [intros evs X Hst; exact (Hc _ _ (sstep_of_cfg segs _ _ _ Hst))|]. split; [|exact Hp].
    intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
    apply Ht. exact (Hs _ _ _ HP).
Qed.

Theorem nodes_sound : forall segs, node_sound node segs ACFG (at_node segs) nstep nexit minv nsafe.
Proof.
  intros segs. constructor.
  - (* [comment removed for export] *) exact minv_nolazy.
  - (* [comment removed for export] *)
    intros n ms Hat.
    assert (Hx : exists x8, ms_svc_pending ms = Some x8).
    { destruct n as [| | | | | | |c| | | | |]; cbn [at_node] in Hat;
        first [ destruct Hat as [[H|H] _]; eexists; exact H
              | destruct Hat as [H _]; eexists; exact H
              | eexists; exact Hat ]. }
    destruct Hx as [x8 ->]. discriminate.
  - (* [comment removed for export] *)
    intros n ms mo evs X Hat Hh Hminv Hsafe Hst.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + destruct (exit_node_facts segs ms mo c Hat Hh) as [Hc _]. destruct (Hc _ _ (sstep_of_cfg segs _ _ _ Hst)) as [-> ->].
      right. eexists _, _. split; [reflexivity|]. split; [split; reflexivity| reflexivity].
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (Hc & _ & _). left. exact (Hc _ _ Hst).
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs Hat Hh Hminv Hsafe HP.
    assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct HP]).
    destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & Hs & _). exact (Hs _ _ _ HP).
  - (* [comment removed for export] *)
    intros n ms mo code mo' Hat Hh Hminv Hsafe HX.
    destruct n as [| | | | | | |c| | | | |]; try contradiction. cbn [nexit] in HX. destruct HX as [-> ->].
    split; [reflexivity|].
    destruct (proj1 Hat) as [Hsvc|Hsvc];
      (eapply (transparent_nonalloc_no segs ms mo _ _ Hsvc); [reflexivity| vm_compute; reflexivity|]);
      exact (proj2 (exit_node_facts segs ms mo c Hat Hh)).
  - (* [comment removed for export] *)
    intros n ms mo Hat Hh Hminv Hsafe.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. split; reflexivity.
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & _ & Hp). left. exact Hp.
Qed.
