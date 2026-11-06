(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/simdjson/fuzz_minifyimpl/lib/Lib/Nodes.v, with its module paths changed; 46 of its 1008 lines of code are new or changed and 1028 lines of the source are left out. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import MmSpec.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
| NMprotect (addr len prot : Z).                   (* [comment removed for export] *)

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
      | Some i => syscall_spec i mo (Ok eff mo' evs)
      | None => False
      end
  | NBrk _ | NMunmap _ _ | NMprotect _ _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs)
      | None => False
      end
  end.

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
  change (vm_init_sp (m_vmmaps (init_model reserved brk mbase sp lim inp))) with sp.
  change (m_fds (init_model reserved brk mbase sp lim inp)) with
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  change (m_tid (init_model reserved brk mbase sp lim inp)) with (@None word).
  change (m_vm_lazy (init_model reserved brk mbase sp lim inp)) with (@nil (word * word)).
  change (m_vm_materialized (init_model reserved brk mbase sp lim inp)) with (@nil word).
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
  | _ => True
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PerNode.
Variable segs : list Segment.

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
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Definition open_ci (pathp : word) (path : list byte) : list (word * nat) := [(pathp, cstr_len path)].

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| ]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
    split; [rewrite m_halted_with_fds; exact Hh|]. eapply minv_update_file; eassumption.
  - destruct H as [_ ->]. auto.
  - destruct H as [_ ->]. auto.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <-> check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. match goal with |- context [syscall_spec ?i _ _] => rewrite (spec_brk_iff i mo eff mo' evs eq_refl) end. cbn [in_arg in_args nth pure_input].
  split; [tauto|]. intros H. split; [exact (proj2 (proj2 (check_brk_shape _ _ _ _ _ H)))| exact H].
Qed.

Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  (mmap_noreserve_b (Z_to_bv 64 flags) = false /\
   check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs).
Proof.
  intros. cbn [nstep node_input]. match goal with |- context [syscall_spec ?i _ _] => rewrite (spec_mmap_iff i mo eff mo' evs eq_refl) end. cbn [in_arg in_args nth pure_input].
  split; [tauto|]. intros [Hnr H]. split; [exact (proj2 (proj2 (check_mmap_shape _ _ _ _ _ _ _ _ _ _ Hnr H)))| auto].
Qed.

Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. match goal with |- context [syscall_spec ?i _ _] => rewrite (spec_munmap_iff i mo eff mo' evs eq_refl) end. cbn [in_arg in_args nth pure_input].
  split; [tauto|]. intros H. split; [exact (proj2 (proj2 (check_munmap_shape _ _ _ _ _ _ H)))| exact H].
Qed.

Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. match goal with |- context [syscall_spec ?i _ _] => rewrite (spec_mprotect_iff i mo eff mo' evs eq_refl) end. cbn [in_arg in_args nth pure_input].
  split; [tauto|]. intros H. split; [exact (proj2 (proj2 (check_mprotect_shape _ _ _ _ _ _ _ H)))| exact H].
Qed.

(* [comment removed for export] *)
Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end ->
  nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [].
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction.
  - apply nstep_brk_iff in H. pose proof (check_brk_shape _ _ _ _ _ H); tauto.
  - apply nstep_mmap_iff in H as [Hnr H]. pose proof (check_mmap_shape _ _ _ _ _ _ _ _ _ _ Hnr H); tauto.
  - apply nstep_munmap_iff in H. pose proof (check_munmap_shape _ _ _ _ _ _ H); tauto.
  - apply nstep_mprotect_iff in H. pose proof (check_mprotect_shape _ _ _ _ _ _ _ H); tauto.
Qed.

(* [comment removed for export] *)
Lemma nsafe_mmap_rw : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hl. cbn [nsafe]. unfold mmap_safe_b. rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma nsafe_mmap_none : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hl. cbn [nsafe]. unfold mmap_safe_b. rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_fd_aux_le : forall fuel fds (cand : word),
  (bv_unsigned cand + Z.of_nat fuel < 2^64)%Z ->
  (bv_unsigned (alloc_fd_aux fds cand fuel) <= bv_unsigned cand + Z.of_nat fuel)%Z.
Proof.
  induction fuel as [|f IH]; intros fds cand Hb; cbn [alloc_fd_aux].
  - lia.
  - pose proof (bv_unsigned_in_range 64 cand) as Hc. unfold bv_modulus in Hc.
    destruct (fd_lookup fds cand).
    + assert (Hu : bv_unsigned (cand + 1)%bv = (bv_unsigned cand + 1)%Z).
      { rewrite bv_add_unsigned. replace (bv_unsigned (1 : word)) with 1%Z by reflexivity.
        apply bv_wrap_small. unfold bv_modulus. lia. }
      specialize (IH fds (cand + 1)%bv). rewrite Hu in IH. lia.
    + lia.
Qed.

Lemma alloc_fd_le : forall fds, (bv_unsigned (alloc_fd fds) <= 4096)%Z.
Proof.
  intro fds. unfold alloc_fd. pose proof (alloc_fd_aux_le 4096 fds (Z_to_bv 64 0)) as H.
  rewrite Z_to_bv_small in H by (unfold bv_modulus; lia). lia.
Qed.

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
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End PerNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
