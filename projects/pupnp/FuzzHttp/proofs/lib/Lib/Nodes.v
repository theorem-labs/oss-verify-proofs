(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree RelSpec RelSpecX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

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

Lemma copy_iovecs_aux_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) ->
  Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs ->
  copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros mp a H HL; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2. rewrite !length_le8 in H3.
  apply Forall_cons_iff in HL as [Hl HL]. cbn [snd] in Hl.
  cbn [copy_iovecs_aux length]. unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
  rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  rewrite (proj2 (Z.leb_gt _ _) Hl).
  unfold iovec_bytes in IH. rewrite (IH _ _ H3 HL). reflexivity.
Qed.

Lemma iovs_access_okb_of_bounds : forall iovs,
  Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= 2^47) iovs ->
  iovs_access_okb iovs = true.
Proof.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [Hb Hr]. cbn [fst snd] in Hb.
  unfold iovs_access_okb. cbn [forallb fst snd].
  pose proof (bv_unsigned_in_range 64 n) as [Hn _].
  rewrite (access_okb_of_le b (bv_unsigned n) Hn Hb). cbn [andb]. exact (IH Hr).
Qed.

Lemma import_iovecs_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) ->
  Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs ->
  Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= 2^47) iovs ->
  (1 <= length iovs <= 1024)%nat ->
  0 <= a -> a + 16 * Z.of_nat (length iovs) <= 2^47 ->
  import_iovecs mp (wa a) (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
  intros iovs mp a Hin Hsmall Hbnd Hlen Ha0 Ha.
  pose proof (copy_iovecs_aux_bytes_in iovs mp a Hin Hsmall) as Hcopy.
  unfold import_iovecs.
  assert (Hwa : bv_unsigned (wa a) = a) by (unfold wa; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
  destruct (Nat.eq_dec (length iovs) 1) as [E1|N1].
  - rewrite E1. change (Z.of_nat 1) with 1. rewrite (bv_eqb_refl (n:=64)).
    rewrite (access_okb_of_le (wa a) 16) by lia. cbn [negb].
    destruct iovs as [|[b n] [|? ?]]; try (cbn in E1; lia).
    cbn [copy_iovecs_aux length] in Hcopy.
    destruct (read_iovec_entry mp (wa a)) as [b' n'| |]; try discriminate.
    cbn [copy_iovecs_aux] in Hcopy. injection Hcopy as -> ->.
    apply Forall_cons_iff in Hbnd as [Hb _]. cbn [fst snd] in Hb.
    pose proof (bv_unsigned_in_range 64 n) as [Hn _].
    rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT)) by (unfold MAX_RW_COUNT; lia).
    reflexivity.
  - assert (E1 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 1) = false).
    { unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul].
      rewrite !Z.mod_small by lia. apply Z.eqb_neq. lia. }
    assert (E0 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul].
      rewrite !Z.mod_small by lia. apply Z.eqb_neq. lia. }
    rewrite E1, E0.
    assert (Hn : bv_unsigned (Z_to_bv 64 (Z.of_nat (length iovs))) = Z.of_nat (length iovs)).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
    rewrite Hn. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold IOV_MAX; lia).
    rewrite (access_okb_of_le (wa a) (16 * Z.of_nat (length iovs))) by lia. cbn [negb].
    unfold word_to_nat. rewrite Hn, Nat2Z.id, Hcopy. rewrite (iovs_access_okb_of_bounds _ Hbnd). reflexivity.
Qed.

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

Inductive node : Type :=
| NWritev (fd : Z) (bufs : list (list byte))
| NOpen (path : list byte)
| NRead (fd : Z) (buf : Z) (count : Z)
| NClose (fd : Z)
| NIoctl (fd : Z) (req : Z)
| NSetTid
| NExit (code : Z)
| NBrk (req : Z)
| NMmap (addr len prot flags : Z)
| NMunmap (addr len : Z)
| NMprotect (addr len prot : Z)
| NMremap (old old_len new_len : Z)

| NOpenW (path : list byte)
| NIoctlF (fd : Z)
| NWritevF (fd : Z) (bufs : list (list byte))
| NLseek (fd off whence : Z)
| NReadv (fd a1 n1 a2 n2 : Z)
| NUnlink (path : list byte).

Definition TIOCGWINSZ : Z := 21523.

Section AtNode.
Variable segs : list Segment.

Definition at_node (n : node) (ms : machine_state) : Prop :=
  match n with
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (1 <= length bufs <= 1024)%nat /\
      Z.of_nat (length (concat bufs)) <= 2^24 /\
      ms_rom ms = seg_rom segs /\

      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= 2^47) iovs /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      path_has_slash path = false /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      0 < count <= 2^24 /\ buf + count <= 2^47 /\
      wr_at segs (ms_mem ms) buf count
  | NClose fd =>
      ms_svc_pending ms = Some (Z_to_bv 64 57) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd
  | NIoctl fd req =>
      ms_svc_pending ms = Some (Z_to_bv 64 29) /\
      0 <= fd <= 2 /\ req = TIOCGWINSZ /\
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
      w_is0 (Z_to_bv 64 len) = false /\ mmap_noreserve_b (Z_to_bv 64 flags) = false /\
      mmap_anon_b (Z_to_bv 64 flags) = true /\
      let P := Z_to_bv 64 prot in let FL := Z_to_bv 64 flags in
      (mmap_modeled_b P FL (Z_to_bv 64 0) = true
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = false /\
           mmap_noaccess_b P FL (Z_to_bv 64 0) = true)
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = false /\
           mmap_noaccess_b P FL (Z_to_bv 64 0) = false /\
           mmap_fixed_noaccess_b P FL (Z_to_bv 64 0) = true))
  | NMunmap addr len =>
      ms_svc_pending ms = Some (Z_to_bv 64 215) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
      (bv_unsigned (Z_to_bv 64 addr) mod page_size = 0) /\ w_is0 (Z_to_bv 64 len) = false /\
      bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= 2^47
  | NMprotect addr len prot =>
      ms_svc_pending ms = Some (Z_to_bv 64 226) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot /\
      mprotect_grows_conflict_b (Z_to_bv 64 prot) = false /\ mprotect_modeled_b (Z_to_bv 64 prot) = true /\
      (bv_unsigned (Z_to_bv 64 addr) mod page_size = 0) /\ w_is0 (Z_to_bv 64 len) = false /\
      bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) < two_pow_64
  | NMremap old old_len new_len =>
      ms_svc_pending ms = Some (Z_to_bv 64 216) /\
      areg ms 10 = Z_to_bv 64 old /\ areg ms 11 = Z_to_bv 64 old_len /\ areg ms 12 = Z_to_bv 64 new_len /\
      areg ms 13 = Z_to_bv 64 MREMAP_MAYMOVE /\
      (bv_unsigned (Z_to_bv 64 old) mod page_size = 0) /\
      page_align_is0_b (Z_to_bv 64 new_len) = false /\ page_align_is0_b (Z_to_bv 64 old_len) = false
  | NOpenW path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = wr_create_flags /\
      ~ In (Z_to_bv 8 0) path /\ path <> [] /\ (length path < path_max)%nat /\
      path_has_slash path = false /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NIoctlF fd =>
      ms_svc_pending ms = Some (Z_to_bv 64 29) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 TIOCGWINSZ
  | NWritevF fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (1 <= length bufs <= 8)%nat /\
      1 <= Z.of_nat (length (concat bufs)) <= 2^24 /\
      ms_rom ms = seg_rom segs /\

      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= 2^47) iovs /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NLseek fd off whence =>
      ms_svc_pending ms = Some (Z_to_bv 64 62) /\
      3 <= fd < 2^32 /\ - 2^63 <= off < 2^63 /\ 0 <= whence <= 2 /\
      areg ms 10 = Z_to_bv 64 fd /\ areg ms 11 = Z_to_bv 64 off /\ areg ms 12 = Z_to_bv 64 whence
  | NReadv fd a1 n1 a2 n2 =>
      ms_svc_pending ms = Some (Z_to_bv 64 65) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\ areg ms 12 = Z_to_bv 64 2 /\

      0 < n1 /\ 0 < n2 /\ n1 + n2 <= 2^24 /\ 0 <= a1 /\ a1 + n1 <= 2^47 /\ 0 <= a2 /\ a2 + n2 <= 2^47 /\
      bv_unsigned (areg ms 11) + 32 <= 2^47 /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11))
               (iovec_bytes [(Z_to_bv 64 a1, Z_to_bv 64 n1); (Z_to_bv 64 a2, Z_to_bv 64 n2)]) /\
      wr_at segs (ms_mem ms) a1 n1 /\ wr_at segs (ms_mem ms) a2 n2
  | NUnlink path =>
      ms_svc_pending ms = Some (Z_to_bv 64 35) /\
      areg ms 10 = Z_to_bv 64 (-100) /\ areg ms 12 = Z_to_bv 64 0 /\
      ~ In (Z_to_bv 8 0) path /\ path <> [] /\ path <> dot_path /\ path <> dotdot_path /\
      (length path <= 255)%nat /\
      path_has_slash path = false /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  end.

End AtNode.

Ltac at_node_red :=
  cbn [at_node]; unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
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

Definition strip (e : SyscallEffect) : SyscallEffect :=
  mkEffectU (eff_ret e) (eff_writes e) (eff_zeros e) (eff_unmaps e) (eff_copies e) [].

Lemma strip_mk : forall r ws zs us cs ci, strip (mkEffectU r ws zs us cs ci) = mkEffectU r ws zs us cs [].
Proof. reflexivity. Qed.

Lemma strip_with_copyins : forall R e, strip (with_copyins R e) = strip e.
Proof. intros R e. destruct e; reflexivity. Qed.

Lemma strip_strip : forall e, strip (strip e) = strip e.
Proof. intros e; destruct e; reflexivity. Qed.

Lemma nret_strip : forall ms e, nret ms (strip e) = nret ms e.
Proof. intros ms e. destruct e; reflexivity. Qed.

Lemma apply_effect_strip : forall ms e, apply_effect ms (strip e) = apply_effect ms e.
Proof. intros ms e. destruct e; reflexivity. Qed.

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ strip eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ strip eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition mmap_placed (mo : Model) (addr len flags : Z) (a : word) : Prop :=
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
  (bv_unsigned a mod page_size = 0) /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_ceiling_max /\
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true /\
  bv_unsigned a + nZ <= alloc_top h.

Definition create_result (mo : Model) (p : list byte) (eff : resp) (mo' : Model) : Prop :=
  if path_is_dirref p then strip eff = efferr EISDIR /\ mo' = mo
  else if fs_under (m_fs mo) p then strip eff = efferr EISDIR /\ mo' = mo
  else
    (exists e, In e openat_errnos /\ strip eff = efferr e /\ mo' = mo)
    \/ (let fd := alloc_fd (m_fds mo) in
        fd_lookup (m_fds mo) fd = None /\ strip eff = eff0 fd /\
        mo' = with_fds (fd_insert (m_fds mo) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) p []) mo)).

Definition scatter2 (a1 n1 a2 : Z) (bs : list byte) : list (word * list byte) :=
  let h := firstn (Z.to_nat n1) bs in
  let t := skipn (Z.to_nat n1) bs in
  (match h with [] => [] | _ => [(Z_to_bv 64 a1, h)] end) ++ (match t with [] => [] | _ => [(Z_to_bv 64 a2, t)] end).

Definition lseek_origin (whence : Z) (cur : word) (data : list byte) : word :=
  if whence =? 0 then Z_to_bv 64 0 else if whence =? 1 then cur else len_word data.

Definition reseek_ent (e : FdEntry) (r : word) : FdEntry :=
  match e with FdFile p _ => FdFile p r | FdFileW p _ => FdFileW p r | other => other end.

Definition nmmap_refusable (mo : Model) (len prot flags : Z) : bool :=
  let P := Z_to_bv 64 prot in let FL := Z_to_bv 64 flags in
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
  if mmap_modeled_b P FL (Z_to_bv 64 0) then mmap_grant_refusable FL mo nZ
  else if mmap_noaccess_b P FL (Z_to_bv 64 0) then mmap_reserve_refusable mo nZ
  else false.

Definition pure_input (no : Z) (args : list word) : SyscallInput :=
  mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWritev fd bufs =>
      let bs := concat bufs in
      mo' = mo /\
      ((bs = [] /\ strip eff = eff0 (Z_to_bv 64 0) /\ evs = [])
       \/ (exists k, (1 <= k <= length bs)%nat /\ strip eff = eff0 (Z_to_bv 64 (Z.of_nat k)) /\
                     evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k bs)))
  | NOpen path =>
      evs = [] /\
      if (path_max <=? length path)%nat then strip eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => strip eff = efferr ENOENT /\ mo' = mo
           | _ => if path_is_dirref path then open_result mo FdDir eff mo'
                  else match fs_lookup (m_fs mo) path with
                       | None => strip eff = efferr ENOENT /\ mo' = mo
                       | Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
                       end
           end
  | NRead fd buf count =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => strip eff = efferr EBADF /\ mo' = mo
      | Some FdDir => strip eff = efferr EISDIR /\ mo' = mo
      | Some (FdFile p off) =>
          match fs_lookup (m_fs mo) p with
          | None => False
          | Some data =>
              let bs := file_read data off (Z_to_bv 64 count) in
              strip eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
          end
      | Some (FdFileW _ _) => strip eff = efferr EBADF /\ mo' = mo
      | Some _ => False
      end
  | NClose fd =>
      evs = [] /\ 3 <= fd < 2^32 /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => strip eff = efferr EBADF /\ mo' = mo
      | Some _ => strip eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
      end
  | NIoctl fd req => evs = [] /\ strip eff = efferr ENOTTY /\ mo' = mo
  | NSetTid =>
      evs = [] /\ exists t, strip eff = eff0 t /\
      match m_tid mo with
      | Some t0 => t = t0 /\ mo' = mo
      | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
      end
  | NExit _ => False
  | NBrk req =>
      evs = [] /\
      (exists r, brk_r_ok mo (Z_to_bv 64 req) r = true /\
        strip eff = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo)))
                                   (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [] /\
        mo' = with_brk_next mo (Z_to_bv 64 req) r) /\
      ~ spurious_refusal_cfg ACFG (pure_input 214 [Z_to_bv 64 req]) mo eff
  | NMmap addr len prot flags =>
      evs = [] /\
      let h := m_vmmaps mo in
      let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
      let n := Z_to_bv 64 nZ in
      let P := Z_to_bv 64 prot in let FL := Z_to_bv 64 flags in
      ((exists e, In e (mmap_errnos_when (nmmap_refusable mo len prot flags)) /\ strip eff = efferr e /\ mo' = mo)
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = true /\
           exists a, mmap_placed mo addr len flags a /\ mmap_noreserve_backed_ok FL mo nZ = true /\
             strip eff = mkEffect a [] [(a, n)] /\
             mo' = with_mmap_backing FL a n
                     (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
                                     (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo))
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = false /\
           mmap_noaccess_b P FL (Z_to_bv 64 0) = true /\
           exists a, mmap_placed mo addr len flags a /\
             strip eff = mkEffectU a [] [] [(a, n)] [] [] /\
             mo' = with_mmap_backing FL a n
                     (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                                     (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo))
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = false /\
           mmap_noaccess_b P FL (Z_to_bv 64 0) = false /\
           mmap_fixed_noaccess_b P FL (Z_to_bv 64 0) = true /\
           let A := Z_to_bv 64 addr in
           ((strip eff = mkEffectU A [] [] [(A, n)] [] [] /\
             mo' = with_mmap_replacement FL A n
                     (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                        ((A, n) :: maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo))
            \/ (exists e, In e mmap_destructive_errnos /\
                  strip eff = mkEffectU (errno_ret e) [] [] [(A, n)] [] [] /\
                  mo' = with_mmap_destroyed A n
                          (mkVmMapsFull (vm_reserved h)
                             (maps_subtract (vm_maps h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                             (maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                             (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo))))
  | NMunmap addr len =>
      evs = [] /\
      let h := m_vmmaps mo in
      let A := Z_to_bv 64 addr in
      let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in
      strip eff = mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] [] /\
      mo' = with_mmap_destroyed A n
              (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) A)
                 (maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo
  | NMprotect addr len prot =>
      evs = [] /\
      let A := Z_to_bv 64 addr in
      let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in
      ((exists e, In e (mprotect_errnos_when (mprotect_refusable mo A n)) /\ strip eff = efferr e /\ mo' = mo)
       \/ (mprotect_budget_ok mo A n = true /\ strip eff = mkEffect (Z_to_bv 64 0) [] [(A, n)] /\
           mo' = mprotect_model_next mo A n))
  | NMremap old old_len new_len =>
      evs = [] /\
      (exists core, strip eff = core /\
        mremap_out mo (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) (Ok core mo' [])) /\
      ~ spurious_refusal_cfg ACFG
          (pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 old_len; Z_to_bv 64 new_len; Z_to_bv 64 MREMAP_MAYMOVE]) mo eff
  | NOpenW path => evs = [] /\ create_result mo path eff mo'
  | NIoctlF fd =>
      evs = [] /\ mo' = mo /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => strip eff = efferr EBADF
      | Some _ => strip eff = efferr ENOTTY
      end
  | NWritevF fd bufs =>
      evs = [] /\
      exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off) /\ fs_lookup (m_fs mo) p = Some data /\
        let bs := concat bufs in
        strip eff = eff0 (len_word bs) /\
        mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word bs)%bv))
                       (with_fs (fs_set (m_fs mo) p (file_write data off bs)) mo)
  | NLseek fd off whence =>
      evs = [] /\
      exists e p cur data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e /\ (e = FdFile p cur \/ e = FdFileW p cur) /\
        fs_lookup (m_fs mo) p = Some data /\
        match lseek_dest (lseek_origin whence cur data) (Z_to_bv 64 off) with
        | None => strip eff = efferr EINVAL /\ mo' = mo
        | Some r => strip eff = eff0 r /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (reseek_ent e r)) mo
        end
  | NReadv fd a1 n1 a2 n2 =>
      evs = [] /\
      exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\ fs_lookup (m_fs mo) p = Some data /\
        let bs := file_read data off (Z_to_bv 64 (n1 + n2)) in
        strip eff = mkEffect (len_word bs) (scatter2 a1 n1 a2 bs) [] /\
        mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  | NUnlink path =>
      evs = [] /\
      match fs_lookup (m_fs mo) path with
      | None => strip eff = efferr ENOENT /\ mo' = mo
      | Some _ => (exists e, In e unlinkat_errnos /\ strip eff = efferr e /\ mo' = mo)
                  \/ (fd_names_path (m_fds mo) path = false /\
                      strip eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fs (fs_remove (m_fs mo) path) mo)
      end
  end.

Definition alloc_node (n : node) : bool :=
  match n with NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ | NMremap _ _ _ => true | _ => false end.

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = exit_code c /\ mo' = with_halted code mo
  | _ => False
  end.

Definition minv (mo : Model) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
  (forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
  (forall k e, fd_lookup (m_fds mo) k = Some e ->
     match e with FdChannel _ | FdFile _ _ | FdDir => True | FdFileW p _ => fs_lookup (m_fs mo) p <> None | _ => False end) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
  m_vm_lazy mo = [] /\

  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi.

Lemma minv_nolazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof. intros mo H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.

Lemma minv_init_sp : forall mo, minv mo -> sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi.
Proof. intros mo H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.

Lemma minv_alloc_top : forall mo, minv mo -> alloc_floor <= alloc_top (m_vmmaps mo) <= alloc_ceiling_max.
Proof. intros mo H. apply alloc_top_bracket. apply minv_init_sp. exact H. Qed.

Lemma minv_init : forall reserved brk0 mbase sp lim inp,
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  minv (init_model reserved brk0 mbase sp lim inp).
Proof.
  intros reserved brk0 mbase sp lim inp Hsp. unfold minv. rewrite m_fds_init_model, m_fs_init_model, m_tid_init_model.
  repeat split; try reflexivity; try (intros; discriminate); try (rewrite m_vmmaps_init_model; cbn [vm_init_sp]; lia).
  - intros k c H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
Qed.

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
      let h := m_vmmaps mo in
      let A := Z_to_bv 64 addr in
      let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
      bv_unsigned A + nZ <= alloc_top h /\ (bv_unsigned A mod page_size = 0) /\ 0 < bv_unsigned A /\
      region_free (vm_reserved h) A (Z_to_bv 64 nZ) = true /\ map_contains (vm_maps h) A (Z_to_bv 64 nZ) = true
  | NMunmap addr len =>
      map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true
  | NMprotect addr len prot =>
      let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in
      map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) n = true /\
      map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true
  | NMremap old old_len new_len =>
      let old_nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 old_len)) in
      mremap_source_b (m_vmmaps mo) (Z_to_bv 64 old) (Z_to_bv 64 old_nZ) old_nZ = true

  | NWritevF fd bufs =>
      exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off) /\ fs_lookup (m_fs mo) p = Some data /\
        modeled_zero_fill (bv_unsigned off) data = true /\
        bv_unsigned off + Z.of_nat (length (concat bufs)) <= 2^63 - 1
  | NLseek fd off whence =>
      exists e p cur, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e /\ (e = FdFile p cur \/ e = FdFileW p cur)
  | NReadv fd a1 n1 a2 n2 =>
      exists p off, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
        bv_unsigned off + (n1 + n2) <= 2^63 - 1
  | NUnlink path =>
      fs_under (m_fs mo) path = false /\
      (forall d, fs_lookup (m_fs mo) path = Some d -> fd_names_path (m_fds mo) path = false)
  | _ => True
  end.

Section Generic.
Variable segs : list Segment.

#[using="Type"] Lemma sstep_svc_inv : forall ms mo x8 e X,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms mo) e X ->
  (exists eff mo' evs,
      syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)
      /\ ((exists mo'', m_halted mo' = None /\ e = evs
             /\ materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo''
             /\ X = SNext (mkCfg (nret ms eff) mo''))
          \/ (m_halted mo' = None /\ e = []
              /\ materialize_model_accesses mo' (syscall_effect_accesses eff) = None
              /\ X = SError)
          \/ (exists code, m_halted mo' = Some code /\ m_killed mo' = None
              /\ e = evs ++ [ExitEv code (m_fs mo')]
              /\ X = SNext (mkCfg ms mo'))
          \/ (exists sig, m_killed mo' = Some sig
              /\ e = evs ++ [KillEv sig (m_fs mo')]
              /\ X = SNext (mkCfg ms mo'))))
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ e = [] /\ X = SError).
Proof.
  intros ms mo x8 e X Hsvc Hss.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. split; [eassumption|]. left. eexists. repeat split; eauto.
  - left. eexists _, _, _. split; [eassumption|]. right; left. repeat split; auto.
  - left. eexists _, _, _. split; [eassumption|]. right; right; left. eexists. repeat split; eauto.
  - left. eexists _, _, _. split; [eassumption|]. right; right; right. eexists. repeat split; eauto.
  - right. repeat split; auto.
Qed.

Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\

  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> nstep n mo eff mo' evs) /\
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\

  (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists eff', strip eff' = strip eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)) /\

  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo') /\

  (exists eff mo' evs, nstep n mo eff mo' evs).

#[using="Type"] Lemma node_kit : forall ms mo n,
  node_facts ms mo n -> m_halted mo = None ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros ms mo n (x8 & Hsvc & Hc & Hnu & Hs & Hp & Hw) Hh. split; [|split; [|exact Hw]].
  - intros evs X Hst.
    destruct (sstep_svc_inv ms mo x8 evs X Hsvc Hst)
      as [(eff & mo' & ev & Hspec & [(mo'' & Hh' & -> & Hmat & ->) | [(Hh' & -> & Hmat & ->) | [(code & Hh' & _ & -> & ->) | (sig & Hk' & -> & ->)]]])
         | (Hspec & -> & ->)].
    + pose proof (Hc _ _ _ Hspec) as Hn. destruct (Hp _ _ _ Hn) as [_ Hminv'].
      rewrite (materialize_model_accesses_no_lazy _ _ (minv_nolazy _ Hminv')) in Hmat.
      injection Hmat as <-. exists eff, mo'. split; [reflexivity|exact Hn].
    + pose proof (Hc _ _ _ Hspec) as Hn. destruct (Hp _ _ _ Hn) as [_ Hminv'].
      rewrite (materialize_model_accesses_no_lazy _ _ (minv_nolazy _ Hminv')) in Hmat. discriminate.
    + pose proof (Hc _ _ _ Hspec) as Hn. destruct (Hp _ _ _ Hn) as [Hh0 _]. congruence.
    + pose proof (Hc _ _ _ Hspec) as Hn. destruct (Hp _ _ _ Hn) as [Hh0 _].
      rewrite (m_killed_of_m_halted_none _ Hh0) in Hk'. discriminate.
    + exfalso. exact (Hnu Hspec).
  - intros eff mo' evs Hn. destruct (Hp _ _ _ Hn) as [Hh' Hminv']. split; [exact Hh'|]. split; [exact Hminv'|].
    destruct (Hs _ _ _ Hn) as (eff' & Hstrip & Hspec).
    rewrite <- nret_strip, <- Hstrip, nret_strip. unfold nret.
    apply (sstep_syscall segs ms mo x8 eff' mo' mo' evs Hh Hsvc Hspec Hh').
    apply materialize_model_accesses_no_lazy. exact (minv_nolazy _ Hminv').
Qed.

Definition node_facts_ns (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff -> nstep n mo eff mo' evs) /\
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
  (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists eff', strip eff' = strip eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)
       /\ ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff') /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_halted mo' = None /\ minv mo') /\
  (exists eff mo' evs, nstep n mo eff mo' evs).

#[using="Type"] Lemma mk_node_facts_ns : forall ms mo n x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff -> nstep n mo eff mo' evs) ->
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) ->
  (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists eff', strip eff' = strip eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)
       /\ ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff') ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_halted mo' = None /\ minv mo') ->
  (exists eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)) ->
  node_facts_ns ms mo n.
Proof.
  intros ms mo n x8 Hsvc Hc Hnu Hs Hp (eff0 & mo0 & evs0 & H0).
  exists x8. split; [exact Hsvc|]. split; [exact Hc|]. split; [exact Hnu|]. split; [exact Hs|]. split; [exact Hp|].
  destruct (exists_nonspurious ACFG _ _ _ _ _ H0) as (eff & mo' & evs & Hs1 & Hns).
  exists eff, mo', evs. exact (Hc _ _ _ Hs1 Hns).
Qed.

#[using="Type"] Lemma node_kit_ns : forall ms mo n,
  node_facts_ns ms mo n -> m_halted mo = None ->
  (forall evs X, sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros ms mo n (x8 & Hsvc & Hc & Hnu & Hs & Hp & Hw) Hh. split; [|split; [|exact Hw]].
  - intros evs X Hst.
    destruct (sstep_cfg_sys_inv segs ACFG ms mo x8 evs X Hsvc Hst)
      as [(eff & mo' & ev & Hspec & Hns & Hh' & Hm) | [(eff & mo' & ev & code & Hspec & Hh' & _ & _ & _)
         | [(eff & mo' & ev & sig & Hspec & Hk' & _ & _) | (Hspec & _ & _)]]].
    + destruct (Hp _ _ _ Hspec) as [_ Hminv'].
      rewrite (materialize_model_accesses_no_lazy _ _ (minv_nolazy _ Hminv')) in Hm. cbv beta iota in Hm.
      destruct Hm as [-> ->]. exists eff, mo'. split; [reflexivity| exact (Hc _ _ _ Hspec Hns)].
    + destruct (Hp _ _ _ Hspec) as [Hh0 _]. congruence.
    + destruct (Hp _ _ _ Hspec) as [Hh0 _]. rewrite (m_killed_of_m_halted_none _ Hh0) in Hk'. discriminate.
    + exfalso. exact (Hnu Hspec).
  - intros eff mo' evs Hn. destruct (Hs _ _ _ Hn) as (eff' & Hstrip & Hspec & Hns).
    destruct (Hp _ _ _ Hspec) as [Hh' Hminv']. split; [exact Hh'|]. split; [exact Hminv'|].
    rewrite <- nret_strip, <- Hstrip, nret_strip. unfold nret.
    apply (sstep_cfg_syscall segs ACFG ms mo x8 eff' mo' mo' evs Hh Hsvc Hspec Hns Hh').
    apply materialize_model_accesses_no_lazy. exact (minv_nolazy _ Hminv').
Qed.

#[using="Type"] Lemma exit_kit : forall ms mo x8 code,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
     o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted code mo) []) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
  /\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
  intros ms mo x8 code Hsvc Hh Hchar. split.
  - intros evs X Hst.
    destruct (sstep_svc_inv ms mo x8 evs X Hsvc Hst)
      as [(eff & mo' & ev & Hspec & [(mo'' & Hh' & -> & Hmat & ->) | [(Hh' & -> & Hmat & ->) | [(c & Hh' & _ & -> & ->) | (sig & Hk' & -> & ->)]]])
         | (Hspec & -> & ->)];
      apply Hchar in Hspec; try (apply Ok_inj in Hspec as (-> & -> & ->)).
    + exfalso. rewrite m_halted_with_halted in Hh'. discriminate.
    + exfalso. rewrite m_halted_with_halted in Hh'. discriminate.
    + rewrite m_halted_with_halted in Hh'. injection Hh' as <-. rewrite m_fs_with_halted. split; reflexivity.
    + exfalso. rewrite m_killed_with_halted in Hk'. discriminate.
    + exfalso. exact (Unmodeled_Ok _ _ _ Hspec).
  - change [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))]).
    eapply sstep_exit; [exact Hh|exact Hsvc| apply Hchar; reflexivity | apply m_halted_with_halted | apply m_killed_with_halted].
Qed.

End Generic.

Section PerNode.
Variable segs : list Segment.

#[using="Type"] Lemma unsigned_lit64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

#[using="Type"] Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_lit64 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma fd32_small : forall z, 0 <= z < 2^32 -> fd32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros. unfold fd32. apply abi_low32_small. assumption. Qed.

#[using="Type"] Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit64 by lia. reflexivity. Qed.

#[using="Type"] Lemma sysno_of : forall ms x8 z, 0 <= z < 2^64 -> x8 = Z_to_bv 64 z ->
  bv_unsigned (in_sysno (sys_input segs ms x8)) = z.
Proof. intros ms x8 z Hz ->. rewrite in_sysno_si. apply unsigned_lit64. exact Hz. Qed.

#[using="Type"] Lemma bv_eqb_sym : forall (a b : word), bv_eqb a b = bv_eqb b a.
Proof. intros. unfold bv_eqb. apply Z.eqb_sym. Qed.

#[using="Type"] Lemma fd_lookup_filter : forall fds fd k, bv_eqb fd k = false ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) k = fd_lookup fds k.
Proof.
  induction fds as [|[k' e] fds IH]; intros fd k Hne; [reflexivity|].
  cbn [List.filter fst]. destruct (bv_eqb k' fd) eqn:E; cbn [negb fd_lookup].
  - apply bv_eqb_eq in E; subst k'. rewrite Hne. apply IH. exact Hne.
  - rewrite IH by exact Hne. reflexivity.
Qed.

#[using="Type"] Lemma fd_lookup_insert : forall fds fd e k,
  fd_lookup (fd_insert fds fd e) k = if bv_eqb fd k then Some e else fd_lookup fds k.
Proof.
  intros. unfold fd_insert. cbn [fd_lookup]. destruct (bv_eqb fd k) eqn:E; [reflexivity|].
  apply fd_lookup_filter. exact E.
Qed.

#[using="Type"] Lemma fd_lookup_remove : forall fds fd k,
  fd_lookup (fd_remove fds fd) k = if bv_eqb fd k then None else fd_lookup fds k.
Proof.
  intros. unfold fd_remove. destruct (bv_eqb fd k) eqn:E.
  - apply bv_eqb_eq in E; subst k. induction fds as [|[k' e] fds IH]; [reflexivity|].
    cbn [List.filter fst]. destruct (bv_eqb k' fd) eqn:E'; cbn [negb fd_lookup]; [exact IH|].
    rewrite E'. exact IH.
  - apply fd_lookup_filter. exact E.
Qed.

#[using="Type"] Lemma m_vm_lazy_with_fds : forall f mo, m_vm_lazy (with_fds f mo) = m_vm_lazy mo.
Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_with_tid : forall t mo, m_vm_lazy (with_tid t mo) = m_vm_lazy mo.
Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_with_halted : forall c mo, m_vm_lazy (with_halted c mo) = m_vm_lazy mo.
Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_with_vmmaps : forall h mo, m_vm_lazy (with_vmmaps h mo) = m_vm_lazy mo.
Proof. reflexivity. Qed.

#[using="Type"] Lemma minv_frame : forall mo mo',
  m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> m_tid mo' = m_tid mo -> m_vm_lazy mo' = m_vm_lazy mo ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->
  minv mo -> minv mo'.
Proof.
  intros mo mo' Hf Hs Ht Hl Hsp M. unfold minv in *. rewrite Hf, Hs, Ht, Hl, Hsp. exact M.
Qed.

#[using="Type"] Lemma minv_remove : forall mo fd, minv mo -> 3 <= fd < 2^32 ->
  minv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
  intros mo fd (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS) Hfd. unfold minv.
  rewrite m_fds_with_fds, m_fs_with_fds, m_tid_with_fds, m_vm_lazy_with_fds.
  rewrite !fd_lookup_remove.
  assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
  { intros z Hz. unfold bv_eqb. rewrite !unsigned_lit64 by lia. apply Z.eqb_neq. lia. }
  rewrite (Hne 0), (Hne 1), (Hne 2) by lia.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]]]].
  - intros k c. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate|apply MC].
  - intros k p off. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate|apply MF].
  - intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate|apply MK].
Qed.

#[using="Type"] Lemma minv_with_tid : forall mo t, minv mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minv (with_tid t mo).
Proof.
  intros mo t (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS) Ht. unfold minv.
  rewrite m_fds_with_tid, m_fs_with_tid, m_tid_with_tid, m_vm_lazy_with_tid.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|]. split; [exact MK|].
  split; [| split; [exact ML| autorewrite with model; exact MS]]. intros t' Ht'. inversion Ht'; subst. lia.
Qed.

#[using="Type"] Lemma minv_update_file : forall mo k p off off',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros mo k p off off' (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS) Hk. unfold minv.
  rewrite m_fds_with_fds, m_fs_with_fds, m_tid_with_fds, m_vm_lazy_with_fds.
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]]]].
  - intros k' c. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [discriminate|apply MC].
  - intros k' p' o'. rewrite fd_lookup_insert. destruct (bv_eqb k k').
    + intros H. inversion H; subst. eapply MF. exact Hk.
    + apply MF.
  - intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [intros H; inversion H; exact I|apply MK].
Qed.

#[using="Type"] Lemma minv_open_insert : forall mo ent,
  minv mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
  intros mo ent (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS) Hfree Hent. unfold minv.
  rewrite m_fds_with_fds, m_fs_with_fds, m_tid_with_fds, m_vm_lazy_with_fds.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]]]].
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

#[using="Type"] Lemma m_vm_lazy_with_fs : forall f mo, m_vm_lazy (with_fs f mo) = m_vm_lazy mo.
Proof. intros f mo. destruct mo; reflexivity. Qed.

#[using="Type"] Lemma fs_lookup_set_same : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof.
  induction fs as [|[q dq] fs IH]; intros p d; cbn.
  - rewrite path_eqb_refl. reflexivity.
  - destruct (path_ltb p q); cbn; [rewrite path_eqb_refl; reflexivity|].
    destruct (path_eqb p q) eqn:E; cbn; [rewrite path_eqb_refl; reflexivity|]. rewrite E. apply IH.
Qed.

#[using="Type"] Lemma fs_lookup_set_other : forall fs p q d, p <> q -> fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof.
  induction fs as [|[r dr] fs IH]; intros p q d Hne; cbn.
  - destruct (path_eqb q p) eqn:E; [apply path_eqb_eq in E; congruence| reflexivity].
  - assert (Eqp : path_eqb q p = false) by (destruct (path_eqb q p) eqn:E; [apply path_eqb_eq in E; congruence| reflexivity]).
    destruct (path_ltb p r); cbn; [rewrite Eqp; reflexivity|].
    destruct (path_eqb p r) eqn:E; cbn.
    + apply path_eqb_eq in E. subst r. rewrite Eqp. destruct (path_eqb q p) eqn:E2; [apply path_eqb_eq in E2; congruence| reflexivity].
    + destruct (path_eqb q r); [reflexivity| apply IH; exact Hne].
Qed.

#[using="Type"] Lemma fs_lookup_set_pres : forall fs p d q, fs_lookup fs q <> None -> fs_lookup (fs_set fs p d) q <> None.
Proof.
  intros fs p d q H. destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) p q) as [->|Hne].
  - rewrite fs_lookup_set_same. discriminate.
  - rewrite fs_lookup_set_other by exact Hne. exact H.
Qed.

#[using="Type"] Lemma fs_lookup_remove_other : forall fs p q, p <> q -> fs_lookup (fs_remove fs p) q = fs_lookup fs q.
Proof.
  induction fs as [|[r dr] fs IH]; intros p q Hne; cbn; [reflexivity|].
  destruct (path_eqb p r) eqn:E; cbn.
  - apply path_eqb_eq in E. subst r. destruct (path_eqb q p) eqn:E2; [apply path_eqb_eq in E2; congruence| reflexivity].
  - destruct (path_eqb q r); [reflexivity| apply IH; exact Hne].
Qed.

#[using="Type"] Lemma fd_names_path_false : forall fds p k e,
  fd_names_path fds p = false -> fd_lookup fds k = Some e ->
  match e with FdFile q _ | FdFileW q _ => q <> p | _ => True end.
Proof.
  induction fds as [|[k0 e0] fds IH]; intros p k e Hn Hlk; cbn in Hlk; [discriminate|].
  cbn in Hn. destruct (bv_eqb k0 k) eqn:Ek.
  - injection Hlk as ->. destruct e; try exact I;
      (apply Bool.orb_false_iff in Hn; destruct Hn as [E _]; intros C; subst; rewrite path_eqb_refl in E; discriminate).
  - destruct e0; try (eapply IH; eassumption);
      (apply Bool.orb_false_iff in Hn; destruct Hn as [_ Hn']; eapply IH; eassumption).
Qed.

#[using="Type"] Lemma minv_with_fs_keep : forall mo fs',
  minv mo -> (forall q, fs_lookup (m_fs mo) q <> None -> fs_lookup fs' q <> None) -> minv (with_fs fs' mo).
Proof.
  intros mo fs' (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS) HK. unfold minv.
  rewrite m_fds_with_fs, m_fs_with_fs, m_tid_with_fs, m_vm_lazy_with_fs.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|].
  split; [intros k p off H; apply HK; eapply MF; exact H|].
  split; [| split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]].
  intros k e H. specialize (MK k e H). destruct e; try exact MK. apply HK. exact MK.
Qed.

#[using="Type"] Lemma minv_reseek : forall mo k e r,
  minv mo -> fd_lookup (m_fds mo) k = Some e ->
  match e with FdFile _ _ | FdFileW _ _ => True | _ => False end ->
  minv (with_fds (fd_insert (m_fds mo) k (reseek_ent e r)) mo).
Proof.
  intros mo k e r (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS) Hk He. unfold minv.
  rewrite m_fds_with_fds, m_fs_with_fds, m_tid_with_fds, m_vm_lazy_with_fds.
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'.
    rewrite Hk in Hk'. injection Hk' as ->. destruct He. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]]]].
  - intros k' c. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [| apply MC].
    intros H. injection H as H. destruct e; try destruct He; discriminate.
  - intros k' p' o'. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [| apply MF].
    intros H. destruct e; try destruct He; cbn in H; [injection H as <- <-; eapply MF; exact Hk| discriminate].
  - intros k' e'. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [| apply MK].
    intros H. injection H as <-. specialize (MK _ _ Hk). destruct e; try destruct He; cbn; [exact I| exact MK].
Qed.

#[using="Type"] Lemma minv_write_filew : forall mo k p off off' data',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFileW p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFileW p off')) (with_fs (fs_set (m_fs mo) p data') mo)).
Proof.
  intros mo k p off off' data' HM Hk.
  assert (HM' : minv (with_fs (fs_set (m_fs mo) p data') mo)).
  { apply minv_with_fs_keep; [exact HM|]. intros q Hq. apply fs_lookup_set_pres. exact Hq. }
  pose proof (minv_reseek (with_fs (fs_set (m_fs mo) p data') mo) k (FdFileW p off) off' HM') as R.
  rewrite m_fds_with_fs in R. apply R; [exact Hk| exact I].
Qed.

#[using="Type"] Lemma minv_create : forall mo p,
  minv mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) p []) mo)).
Proof.
  intros mo p HM Hfree.
  assert (HM' : minv (with_fs (fs_set (m_fs mo) p []) mo)).
  { apply minv_with_fs_keep; [exact HM|]. intros q Hq. apply fs_lookup_set_pres. exact Hq. }
  pose proof HM' as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  rewrite m_fds_with_fs in *. rewrite m_fs_with_fs in *. unfold minv.
  rewrite m_fds_with_fds, m_fs_with_fds, m_tid_with_fds, m_vm_lazy_with_fds, m_fs_with_fs, m_tid_with_fs, m_vm_lazy_with_fs.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]]]].
  - intros k c. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [intros H; discriminate| apply MC].
  - intros k q off. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [intros H; discriminate| apply MF].
  - intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [| apply MK].
    intros H. injection H as <-. cbn. rewrite fs_lookup_set_same. discriminate.
Qed.

#[using="Type"] Lemma minv_unlink : forall mo p,
  minv mo -> fd_names_path (m_fds mo) p = false -> minv (with_fs (fs_remove (m_fs mo) p) mo).
Proof.
  intros mo p HM Hn. pose proof HM as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS). unfold minv.
  rewrite m_fds_with_fs, m_fs_with_fs, m_tid_with_fs, m_vm_lazy_with_fs.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|].
  split; [| split; [| split; [exact MT| split; [exact ML| autorewrite with model; exact MS]]]].
  - intros k q off Hk. pose proof (fd_names_path_false _ _ _ _ Hn Hk) as NE. cbn in NE.
    rewrite fs_lookup_remove_other by (intros E; apply NE; symmetry; exact E). eapply MF. exact Hk.
  - intros k e Hk. pose proof (fd_names_path_false _ _ _ _ Hn Hk) as NE. specialize (MK _ _ Hk).
    destruct e; try exact MK. cbn in NE. rewrite fs_lookup_remove_other by (intros E; apply NE; symmetry; exact E). exact MK.
Qed.

#[using="Type"] Lemma alloc_fd_aux_le : forall fds fuel cand,
  bv_unsigned cand + Z.of_nat fuel < 2^64 ->
  bv_unsigned cand <= bv_unsigned (alloc_fd_aux fds cand fuel) <= bv_unsigned cand + Z.of_nat fuel.
Proof.
  intros fds fuel. induction fuel as [|fuel IH]; intros cand Hc; cbn [alloc_fd_aux].
  - lia.
  - destruct (fd_lookup fds cand); [|lia].
    assert (E : bv_unsigned (cand + 1)%bv = bv_unsigned cand + 1).
    { rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1.
      apply bv_wrap_small. unfold bv_modulus. change (Z.of_N 64) with 64.
      pose proof (bv_unsigned_in_range 64 cand) as R. unfold bv_modulus in R. change (Z.of_N 64) with 64 in R. lia. }
    specialize (IH (cand + 1)%bv ltac:(rewrite E; lia)). rewrite E in IH. lia.
Qed.

#[using="Type"] Lemma alloc_fd_le : forall fds, bv_unsigned (alloc_fd fds) <= 4096.
Proof.
  intros fds. unfold alloc_fd.
  assert (H0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  pose proof (alloc_fd_aux_le fds 4096 (Z_to_bv 64 0)) as H. rewrite H0 in H.
  change (Z.of_nat 4096) with 4096 in H. lia.
Qed.

#[using="Type"] Lemma alloc_fd_range : forall mo,
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

#[using="Type"] Lemma close_facts : forall ms mo fd,
  at_node segs (NClose fd) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NClose fd).
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
  exists (Z_to_bv 64 57). split; [exact Hsvc|].
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 57)) mo o <->
                        close_spec (Z_to_bv 64 fd) (sys_input segs ms (Z_to_bv 64 57)) mo o).
  { intros o. rewrite (syscall_spec_57 _ _ _ (sysno_of ms _ 57 ltac:(lia) eq_refl)).
    rewrite in_a0_si, Ha0, fd32_small by lia. reflexivity. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  -
    assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 57)) mo o <->
              o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []).
    { intros o. rewrite D. apply (close_outcome _ _ _ _ _ Hlk). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->).
      cbn [nstep]. rewrite Hlk. repeat split; try lia; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & _ & Hn). rewrite Hlk in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
    + intros eff mo' evs (_ & _ & Hn). rewrite Hlk in Hn. destruct Hn as [_ ->].
      rewrite m_halted_with_fds. split; [exact Hh|]. apply minv_remove; assumption.
    + exists (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo), [].
      cbn [nstep]. rewrite Hlk. repeat split; try lia; reflexivity.
  -
    assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 57)) mo o <->
              o = Ok (mkEffect (errno_ret EBADF) [] []) mo []).
    { intros o. rewrite D. apply (close_ebadf_outcome _ _ _ _ Hlk). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->).
      cbn [nstep]. rewrite Hlk. repeat split; try lia; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & _ & Hn). rewrite Hlk in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
    + intros eff mo' evs (_ & _ & Hn). rewrite Hlk in Hn. destruct Hn as [_ ->]. auto.
    + exists (efferr EBADF), mo, []. cbn [nstep]. rewrite Hlk. repeat split; try lia; reflexivity.
Qed.

#[using="Type"] Lemma tty_only_TIOCGWINSZ : tty_only_request (cmd32 (Z_to_bv 64 TIOCGWINSZ)) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma ioctl_facts : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NIoctl fd req).
Proof.
  intros ms mo fd req (Hsvc & Hfd & -> & Ha0 & Ha1) Hminv Hh.
  exists (Z_to_bv 64 29). split; [exact Hsvc|].
  assert (He : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
  { destruct Hminv as (M0 & M1 & M2 & _).
    assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
  destruct He as [c Hlk].
  assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 29)) mo o <->
            o = Ok (mkEffect (errno_ret ENOTTY) [] []) mo []).
  { intros o. rewrite (syscall_spec_29 _ _ _ (sysno_of ms _ 29 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1, fd32_small by lia.

    apply (ioctl_tty_outcome _ _ _ _ _ _ Hlk tty_only_TIOCGWINSZ); [intros rd wr; discriminate | discriminate]. }
  split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. repeat split; reflexivity.
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff mo' evs (-> & Hs & ->). eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
  - intros eff mo' evs (_ & _ & ->). auto.
  - exists (efferr ENOTTY), mo, []. cbn [nstep]. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma set_tid_facts : forall ms mo,
  at_node segs NSetTid ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo NSetTid.
Proof.
  intros ms mo Hsvc Hminv Hh. cbn [at_node] in Hsvc.
  exists (Z_to_bv 64 96). split; [exact Hsvc|].
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 96)) mo o <->
                        set_tid_address_spec (sys_input segs ms (Z_to_bv 64 96)) mo o).
  { intros o. apply syscall_spec_96. apply (sysno_of ms _ 96 ltac:(lia) eq_refl). }
  destruct (m_tid mo) as [t0|] eqn:Htid.
  - assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 96)) mo o <-> o = Ok (mkEffect t0 [] []) mo []).
    { intros o. rewrite D. apply (set_tid_known_outcome _ _ _ _ Htid). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Htid.
      split; [reflexivity|]. exists t0. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & t & Hs & Hn). rewrite Htid in Hn. destruct Hn as [-> ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
    + intros eff mo' evs (_ & t & _ & Hn). rewrite Htid in Hn. destruct Hn as [_ ->]. auto.
    + exists (eff0 t0), mo, []. cbn [nstep]. rewrite Htid. split; [reflexivity|]. exists t0. repeat split; reflexivity.
  - assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 96)) mo o <->
              exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE) /\ o = Ok (mkEffect t [] []) (with_tid t mo) []).
    { intros o. rewrite D. apply (set_tid_fresh_outcome _ _ _ Htid). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as (t & Ht & Hs). apply Ok_inj in Hs as (-> & -> & ->).
      cbn [nstep]. rewrite Htid. split; [reflexivity|]. exists t. repeat split; try reflexivity; lia.
    + intros Hs. apply OUT in Hs. destruct Hs as (t & _ & Hs). discriminate.
    + intros eff mo' evs (-> & t & Hs & Hn). rewrite Htid in Hn. destruct Hn as [Ht ->].
      eexists. split; [|apply OUT; exists t; split; [exact Ht|reflexivity]]. rewrite Hs. reflexivity.
    + intros eff mo' evs (_ & t & _ & Hn). rewrite Htid in Hn. destruct Hn as [Ht ->].
      rewrite m_halted_with_tid. split; [exact Hh|]. apply minv_with_tid; assumption.
    + exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) mo), []. cbn [nstep]. rewrite Htid.
      split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|]. split; [|reflexivity].
      rewrite unsigned_lit64 by lia. unfold PID_MAX_ENVELOPE. lia.
Qed.

#[using="Type"] Lemma vm_forget_range_frame : forall lo hi m,
  m_fds (vm_forget_range lo hi m) = m_fds m /\ m_fs (vm_forget_range lo hi m) = m_fs m /\
  m_tid (vm_forget_range lo hi m) = m_tid m /\ m_halted (vm_forget_range lo hi m) = m_halted m /\
  (m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = []) /\
  vm_init_sp (m_vmmaps (vm_forget_range lo hi m)) = vm_init_sp (m_vmmaps m).
Proof.
  intros lo hi m. repeat split; try reflexivity. intros H. unfold vm_forget_range.
  change (m_vm_lazy (with_vm_backing ?l ?p m)) with l. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma forget_vm_ranges_frame : forall rs m,
  m_fds (forget_vm_ranges rs m) = m_fds m /\ m_fs (forget_vm_ranges rs m) = m_fs m /\
  m_tid (forget_vm_ranges rs m) = m_tid m /\ m_halted (forget_vm_ranges rs m) = m_halted m /\
  (m_vm_lazy m = [] -> m_vm_lazy (forget_vm_ranges rs m) = []) /\
  vm_init_sp (m_vmmaps (forget_vm_ranges rs m)) = vm_init_sp (m_vmmaps m).
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [repeat split; auto|].
  destruct (IH (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)) as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct (vm_forget_range_frame (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m) as (G1 & G2 & G3 & G4 & G5 & G6).
  rewrite F1, F2, F3, F4, F6, G1, G2, G3, G4, G6. repeat split; try reflexivity. intros H. apply F5, G5, H.
Qed.

#[using="Type"] Lemma with_vmmaps_frame : forall h m,
  vm_init_sp h = vm_init_sp (m_vmmaps m) ->
  m_fds (with_vmmaps h m) = m_fds m /\ m_fs (with_vmmaps h m) = m_fs m /\
  m_tid (with_vmmaps h m) = m_tid m /\ m_halted (with_vmmaps h m) = m_halted m /\
  (m_vm_lazy m = [] -> m_vm_lazy (with_vmmaps h m) = []) /\
  vm_init_sp (m_vmmaps (with_vmmaps h m)) = vm_init_sp (m_vmmaps m).
Proof. intros h m Hsp. rewrite m_vmmaps_with_vmmaps. repeat split; try reflexivity; [|exact Hsp]. intros H. exact H. Qed.

#[using="Type"] Lemma with_mmap_backing_noreserve_false : forall fl a n m,
  mmap_noreserve_b fl = false -> with_mmap_backing fl a n m = m.
Proof. intros fl a n m H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.

Definition mm_frame (mo mo' : Model) : Prop :=
  m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_tid mo' = m_tid mo /\ m_halted mo' = m_halted mo /\
  (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo).

#[using="Type"] Lemma mm_frame_refl : forall mo, mm_frame mo mo.
Proof. intros. repeat split; auto. Qed.

#[using="Type"] Lemma mm_frame_trans : forall a b c, mm_frame a b -> mm_frame b c -> mm_frame a c.
Proof. intros a b c (A1&A2&A3&A4&A5&A6) (B1&B2&B3&B4&B5&B6). repeat split; try congruence. auto. Qed.

#[using="Type"] Lemma mm_frame_minv : forall mo mo', mm_frame mo mo' -> m_halted mo = None -> minv mo ->
  m_halted mo' = None /\ minv mo'.
Proof.
  intros mo mo' (F1 & F2 & F3 & F4 & F5 & F6) Hh M. split; [congruence|].
  apply (minv_frame mo mo'); auto. rewrite (minv_nolazy _ M). apply F5. exact (minv_nolazy _ M).
Qed.

#[using="Type"] Lemma mm_frame_with_vmmaps : forall h m, vm_init_sp h = vm_init_sp (m_vmmaps m) -> mm_frame m (with_vmmaps h m).
Proof. intros h m Hsp. exact (with_vmmaps_frame h m Hsp). Qed.
#[using="Type"] Lemma mm_frame_forget_vm_ranges : forall rs m, mm_frame m (forget_vm_ranges rs m).
Proof. intros. exact (forget_vm_ranges_frame rs m). Qed.
#[using="Type"] Lemma mm_frame_vm_forget_range : forall lo hi m, mm_frame m (vm_forget_range lo hi m).
Proof. intros. exact (vm_forget_range_frame lo hi m). Qed.

#[using="Type"] Lemma mm_frame_with_brk_next : forall m req r, mm_frame m (with_brk_next m req r).
Proof.
  intros. unfold with_brk_next. eapply mm_frame_trans; [|apply mm_frame_forget_vm_ranges]. apply mm_frame_with_vmmaps. reflexivity.
Qed.

#[using="Type"] Lemma mm_frame_with_mmap_destroyed : forall a n h m,
  vm_init_sp h = vm_init_sp (m_vmmaps m) -> mm_frame m (with_mmap_destroyed a n h m).
Proof.
  intros a n h m Hsp. unfold with_mmap_destroyed. eapply mm_frame_trans; [|apply mm_frame_vm_forget_range]. apply mm_frame_with_vmmaps. exact Hsp.
Qed.

#[using="Type"] Lemma mm_frame_mprotect_model_next : forall m a n, mm_frame m (mprotect_model_next m a n).
Proof. intros. unfold mprotect_model_next. apply mm_frame_with_vmmaps. reflexivity. Qed.

#[using="Type"] Lemma mm_frame_with_mmap_backing : forall fl a n m m0,
  mmap_noreserve_b fl = false -> mm_frame m0 m -> mm_frame m0 (with_mmap_backing fl a n m).
Proof. intros. rewrite with_mmap_backing_noreserve_false by assumption. assumption. Qed.

#[using="Type"] Lemma mm_frame_with_mmap_replacement : forall fl a n m m0,
  mmap_noreserve_b fl = false -> mm_frame m0 m -> mm_frame m0 (with_mmap_replacement fl a n m).
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_noreserve_false by assumption.
  eapply mm_frame_trans; [eassumption|apply mm_frame_vm_forget_range].
Qed.

#[using="Type"] Lemma mm_frame_mremap_model_next : forall m old old_n dst new_n,
  m_vm_lazy m = [] -> mm_frame m (mremap_model_next m old old_n dst new_n).
Proof.
  intros m old old_n dst new_n Hl. unfold mremap_model_next, mremap_source_lazy_b. rewrite Hl. cbn [map_contains existsb].
  unfold vm_resize_backing. cbv zeta.
  change (m_vm_lazy (with_vmmaps ?h m)) with (m_vm_lazy m). rewrite Hl. cbn [maps_subtract app].
  repeat split; reflexivity.
Qed.

#[using="Type"] Lemma brk_r_ok_same : forall m req, brk_r_ok m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros m req. unfold brk_r_ok. cbv zeta.
  assert (E : bv_eqb (vm_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) = true) by apply bv_eqb_refl.
  destruct (_ || _); [exact E|]. destruct (Z.ltb _ _); rewrite E, ?orb_true_r; [reflexivity|].
  cbn [andb]. unfold brk_grow_ok, brk_budget_ok. cbv zeta. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma ns_ret : forall cfg i m eff eff', eff_ret eff = eff_ret eff' ->
  ~ spurious_refusal_cfg cfg i m eff -> ~ spurious_refusal_cfg cfg i m eff'.
Proof. intros cfg i m eff eff' E H (Ho & Hr & Hx). apply H. rewrite <- E in Hr. exact (conj Ho (conj Hr Hx)). Qed.

#[using="Type"] Lemma brk_facts : forall ms mo req,
  at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> node_facts_ns segs ms mo (NBrk req).
Proof.
  intros ms mo req (Hsvc & Ha0) Hminv Hh.
  assert (OUTg : forall i o, bv_unsigned (in_sysno i) = 214 -> in_arg i 0 = Z_to_bv 64 req ->
            syscall_spec i mo o <->
            exists r, brk_r_ok mo (Z_to_bv 64 req) r = true /\
              o = Ok (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo)))
                                (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
                     (with_brk_next mo (Z_to_bv 64 req) r) []).
  { intros i o Hno Ha. rewrite (syscall_spec_214 _ _ _ Hno), Ha. apply brk_outcome. }
  assert (Hno1 : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 214))) = 214) by (apply sysno_of; [lia|reflexivity]).
  assert (Hno2 : bv_unsigned (in_sysno (pure_input 214 [Z_to_bv 64 req])) = 214) by (apply unsigned_lit64; lia).
  assert (Ha1 : in_arg (sys_input segs ms (Z_to_bv 64 214)) 0 = Z_to_bv 64 req) by (rewrite in_a0_si; exact Ha0).
  pose proof (fun o => OUTg _ o Hno1 Ha1) as OUT.
  assert (Hsp : forall eff, spurious_refusal_cfg ACFG (sys_input segs ms (Z_to_bv 64 214)) mo eff <->
                            spurious_refusal_cfg ACFG (pure_input 214 [Z_to_bv 64 req]) mo eff).
  { intros eff. apply spurious_refusal_transport; [reflexivity| exact Ha1|].
    intros eff' m' evs'. rewrite OUT, (OUTg _ _ Hno2 eq_refl). reflexivity. }
  apply (mk_node_facts_ns segs ms mo _ (Z_to_bv 64 214) Hsvc).
  - intros eff mo' evs Hs Hns. apply OUT in Hs. destruct Hs as (r & Hr & Hs). apply Ok_inj in Hs as (-> & -> & ->).
    cbn [nstep]. split; [reflexivity|]. split; [exists r; repeat split; try assumption; reflexivity|].
    intros Hx. apply Hns. apply Hsp. exact Hx.
  - intros Hs. apply OUT in Hs. destruct Hs as (r & _ & Hs). discriminate.
  - intros eff mo' evs (-> & (r & Hr & Hs & ->) & Hns).
    eexists. split; [|split; [apply OUT; exists r; split; [exact Hr|reflexivity]|]].
    + rewrite Hs. reflexivity.
    + apply (ns_ret ACFG _ mo eff); [rewrite <- Hs; reflexivity|]. intros Hx. apply Hns. apply Hsp. exact Hx.
  - intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as (r & _ & Hs). apply Ok_inj in Hs as (_ & -> & _).
    apply (mm_frame_minv mo); [apply mm_frame_with_brk_next|exact Hh|exact Hminv].
  - exists (mkEffectU (vm_brk (m_vmmaps mo)) [] (brk_zeros (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)))
             (brk_unmaps (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))) [] []),
      (with_brk_next mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo))), [].
    apply OUT. exists (vm_brk (m_vmmaps mo)). split; [apply brk_r_ok_same|reflexivity].
Qed.

#[using="Type"] Lemma munmap_facts : forall ms mo addr len,
  at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
  node_facts segs ms mo (NMunmap addr len).
Proof.
  intros ms mo addr len (Hsvc & Ha0 & Ha1 & Hal & Hlen & Hnw) Hminv Hh Hsafe. cbn [nsafe] in Hsafe.
  exists (Z_to_bv 64 215). split; [exact Hsvc|].
  set (A := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) in *.
  set (h := m_vmmaps mo) in *.
  set (mo1 := with_mmap_destroyed A n
            (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) A)
               (maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo).
  assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 215)) mo o <->
            o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []) mo1 []).
  { intros o. rewrite (syscall_spec_215 _ _ _ (sysno_of ms _ 215 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1. apply (munmap_exact_outcome _ _ _ _ _ Hal Hlen Hnw Hsafe). }
  split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. repeat split; reflexivity.
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff mo' evs (-> & Hs & ->). eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
  - intros eff mo' evs (_ & _ & ->). apply (mm_frame_minv mo); [apply mm_frame_with_mmap_destroyed; reflexivity|exact Hh|exact Hminv].
  - eexists (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []), mo1, []. cbn [nstep]. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma mprotect_facts : forall ms mo addr len prot,
  at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
  node_facts_ns segs ms mo (NMprotect addr len prot).
Proof.
  intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2 & Hgc & Hmod & Hal & Hlen & Hnw) Hminv Hh [Hna Hma].
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 226))) = 226) by (apply sysno_of; [lia|reflexivity]).
  set (A := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) in *.
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 226)) mo o <->
     mprotect_spec A (Z_to_bv 64 len) (Z_to_bv 64 prot) (sys_input segs ms (Z_to_bv 64 226)) mo o).
  { intros o. rewrite (syscall_spec_226 _ _ _ Hno). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2. reflexivity. }
  pose proof (fun o => mprotect_expose_outcome A (Z_to_bv 64 len) (Z_to_bv 64 prot) (sys_input segs ms (Z_to_bv 64 226))
                         mo o Hgc Hal Hlen Hnw Hmod Hna Hma) as OUT0.
  pose proof (fun o => mprotect_expose_outcome_raw A (Z_to_bv 64 len) (Z_to_bv 64 prot) (sys_input segs ms (Z_to_bv 64 226))
                         mo o Hgc Hal Hlen Hnw Hmod Hna Hma) as RAW.
  cbv zeta in OUT0, RAW.
  assert (OUT : forall eff mo' evs,
     (syscall_spec (sys_input segs ms (Z_to_bv 64 226)) mo (Ok eff mo' evs)
      /\ ~ spurious_refusal_cfg ACFG (sys_input segs ms (Z_to_bv 64 226)) mo eff) <->
     ((exists e, In e (mprotect_errnos_when (mprotect_refusable mo A n))
                 /\ Ok eff mo' evs = Ok (mkEffect (errno_ret e) [] []) mo [])
      \/ (mprotect_budget_ok mo A n = true
          /\ Ok eff mo' evs = Ok (mkEffect (Z_to_bv 64 0) [] [(A, n)]) (mprotect_model_next mo A n) []))).
  { intros eff mo' evs. rewrite D, <- (mprotect_forced_iff_ns _ _ _ _ _ eff mo' evs Hno D). apply OUT0. }
  apply (mk_node_facts_ns segs ms mo _ (Z_to_bv 64 226) Hsvc).
  - intros eff mo' evs Hs Hns. destruct (proj1 (OUT _ _ _) (conj Hs Hns)) as [(e & He & Hs')|(Hb & Hs')];
      apply Ok_inj in Hs' as (-> & -> & ->); cbn [nstep]; (split; [reflexivity|]).
    + left. exists e. repeat split; auto.
    + right. repeat split; auto.
  - intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(_ & Hs)]; discriminate.
  - intros eff mo' evs (-> & [(e & He & Hs & ->)|(Hb & Hs & ->)]).
    + eexists. split; [|apply (proj2 (OUT _ _ _)); left; exists e; split; [exact He|reflexivity]]. rewrite Hs; reflexivity.
    + eexists. split; [|apply (proj2 (OUT _ _ _)); right; split; [exact Hb|reflexivity]]. rewrite Hs; reflexivity.
  - intros eff mo' evs Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(_ & Hs)]; apply Ok_inj in Hs as (_ & -> & _);
      [auto|].
    apply (mm_frame_minv mo); [apply mm_frame_mprotect_model_next|exact Hh|exact Hminv].
  - exists (efferr ENOMEM), mo, []. apply D, RAW. left. exists ENOMEM. split; [exact (or_introl eq_refl)| reflexivity].
Qed.

#[using="Type"] Lemma mmap_grant_unforced : forall flags mo nZ,
  mmap_grant_refusable flags mo nZ = false ->
  mmap_noreserve_backed_ok flags mo nZ = true /\
  exists a, (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps mo))%Z
            /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros flags mo nZ H. unfold mmap_grant_refusable in H. apply Bool.orb_false_iff in H as [H1 H2].
  apply Bool.negb_false_iff in H1. apply Bool.negb_false_iff in H2.
  split; [exact H1|]. apply vm_gap_available_iff. exact H2.
Qed.

#[using="Type"] Lemma mmap_reserve_unforced : forall mo nZ,
  mmap_reserve_refusable mo nZ = false ->
  exists a, (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps mo))%Z
            /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros mo nZ H. unfold mmap_reserve_refusable in H. apply Bool.negb_false_iff in H.
  apply vm_gap_available_iff. exact H.
Qed.

#[using="Type"] Lemma mmap_facts : forall ms mo addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
  node_facts_ns segs ms mo (NMmap addr len prot flags).
Proof.
  intros ms mo addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen & Hnr & Hanon & Hshape) Hminv Hh Hsafe.
  cbv zeta in Hshape. cbn [nsafe] in Hsafe.
  pose proof (minv_alloc_top _ Hminv) as [_ Htop].
  assert (Hoff : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 222))) = 222) by (apply sysno_of; [lia|reflexivity]).
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo o <->
     mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
               (sys_input segs ms (Z_to_bv 64 222)) mo o).
  { intros o. rewrite (syscall_spec_222 _ _ _ Hno).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }
  assert (ERRn : forall e, In e (mmap_errnos_when (nmmap_refusable mo len prot flags)) ->
                 nstep (NMmap addr len prot flags) mo (efferr e) mo []).
  { intros e He. cbn [nstep]. split; [reflexivity|]. left. exists e. repeat split; auto. }
  assert (RF : forall c, nmmap_refusable mo len prot flags = c ->
               forall e, In e (mmap_errnos_when c) -> In e (mmap_errnos_when (nmmap_refusable mo len prot flags))).
  { intros c <- e He. exact He. }
  destruct Hshape as [Hm | [[Hm Hna] | (Hm & Hna & Hfx)]].
  -
    assert (HC : nmmap_refusable mo len prot flags = mmap_grant_refusable (Z_to_bv 64 flags) mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))).
    { unfold nmmap_refusable. rewrite Hm. reflexivity. }
    pose proof (fun o => mmap_rw_outcome (Z_to_bv 64 addr) _ (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) _
                  (sys_input segs ms (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm) as OUT0.
    pose proof (fun o => mmap_rw_outcome_raw (Z_to_bv 64 addr) _ (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) _
                  (sys_input segs ms (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm) as RAW.
    cbv zeta in OUT0, RAW. unfold mmap_err_out_when in OUT0.
    assert (OUT := fun eff mo' evs => iff_trans (and_iff_compat_r _ (D (Ok eff mo' evs)))
      (iff_trans (and_iff_compat_l _ (iff_sym (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs Hno D))) (OUT0 (Ok eff mo' evs)))).
    apply (mk_node_facts_ns segs ms mo _ (Z_to_bv 64 222) Hsvc).
    + intros eff mo' evs Hs Hns.
      destruct (proj1 (OUT _ _ _) (conj Hs Hns)) as [(e & He & Hs')|(a & (Q1 & Q2 & Q3 & Q4 & Q5) & Hs')];
        apply Ok_inj in Hs' as (-> & -> & ->); [apply ERRn; exact (RF _ HC _ He)|].
      cbn [nstep]. split; [reflexivity|]. right; left. split; [exact Hm|]. exists a.
      split; [split; [exact Q1| split; [exact Q2| split; [lia| split; [exact Q4| exact Q3]]]]|].
      split; [exact Q5|]. split; reflexivity.
    + intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; discriminate.
    + intros eff mo' evs (-> & [(e & He & Hs & ->)|[(Hm' & a & (Q1 & Q2 & Q3 & Q4 & Q6) & Q5 & Hs & ->)|[(Hm' & _)|(Hm' & _)]]]);
        try congruence.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); left; exists e; split; [rewrite <- HC; exact He|reflexivity]].
        rewrite Hs; reflexivity.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); right; exists a; split; [repeat split; assumption|reflexivity]].
        rewrite Hs; reflexivity.
    + intros eff mo' evs Hs. apply D, RAW in Hs.
      destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; apply Ok_inj in Hs as (_ & -> & _); [auto|].
      apply (mm_frame_minv mo); [|exact Hh|exact Hminv].
      apply mm_frame_with_mmap_backing; [exact Hnr|apply mm_frame_with_vmmaps; reflexivity].
    + exists (efferr ENOMEM), mo, []. apply D, RAW. left. exists ENOMEM. split; [exact (or_introl eq_refl)| reflexivity].
  -
    assert (HC : nmmap_refusable mo len prot flags = mmap_reserve_refusable mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))).
    { unfold nmmap_refusable. rewrite Hm, Hna. reflexivity. }
    pose proof (fun o => mmap_noaccess_outcome (Z_to_bv 64 addr) _ (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) _
                  (sys_input segs ms (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm Hna) as OUT0.
    pose proof (fun o => mmap_noaccess_outcome_raw (Z_to_bv 64 addr) _ (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) _
                  (sys_input segs ms (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm Hna) as RAW.
    cbv zeta in OUT0, RAW. unfold mmap_err_out_when in OUT0.
    assert (OUT := fun eff mo' evs => iff_trans (and_iff_compat_r _ (D (Ok eff mo' evs)))
      (iff_trans (and_iff_compat_l _ (iff_sym (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs Hno D))) (OUT0 (Ok eff mo' evs)))).
    apply (mk_node_facts_ns segs ms mo _ (Z_to_bv 64 222) Hsvc).
    + intros eff mo' evs Hs Hns.
      destruct (proj1 (OUT _ _ _) (conj Hs Hns)) as [(e & He & Hs')|(a & (Q1 & Q2 & Q3 & Q4) & Hs')];
        apply Ok_inj in Hs' as (-> & -> & ->); [apply ERRn; exact (RF _ HC _ He)|].
      cbn [nstep]. split; [reflexivity|]. right; right; left. split; [exact Hm|]. split; [exact Hna|]. exists a.
      split; [split; [exact Q1| split; [exact Q2| split; [lia| split; [exact Q4| exact Q3]]]]|]. split; reflexivity.
    + intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; discriminate.
    + intros eff mo' evs (-> & [(e & He & Hs & ->)|[(Hm' & _)|[(_ & _ & a & (Q1 & Q2 & Q3 & Q4 & Q6) & Hs & ->)|(_ & Hna' & _)]]]);
        try congruence.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); left; exists e; split; [rewrite <- HC; exact He|reflexivity]].
        rewrite Hs; reflexivity.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); right; exists a; split; [repeat split; assumption|reflexivity]].
        rewrite Hs; reflexivity.
    + intros eff mo' evs Hs. apply D, RAW in Hs.
      destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; apply Ok_inj in Hs as (_ & -> & _); [auto|].
      apply (mm_frame_minv mo); [|exact Hh|exact Hminv].
      apply mm_frame_with_mmap_backing; [exact Hnr|apply mm_frame_with_vmmaps; reflexivity].
    + exists (efferr ENOMEM), mo, []. apply D, RAW. left. exists ENOMEM. split; [exact (or_introl eq_refl)| reflexivity].
  -
    destruct (Hsafe Hfx) as (S1 & S2 & S3 & S4 & S5).
    assert (HC : nmmap_refusable mo len prot flags = false).
    { unfold nmmap_refusable. rewrite Hm, Hna. reflexivity. }
    pose proof (fun o => mmap_fixed_noaccess_outcome (Z_to_bv 64 addr) _ (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) _
                  (sys_input segs ms (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm Hna Hfx S1 S2 S3 S4 S5) as OUT0.
    pose proof (fun o => mmap_fixed_noaccess_outcome_raw (Z_to_bv 64 addr) _ (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) _
                  (sys_input segs ms (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm Hna Hfx S1 S2 S3 S4 S5) as RAW.
    cbv zeta in OUT0, RAW. unfold mmap_err_out_when in OUT0.
    assert (OUT := fun eff mo' evs => iff_trans (and_iff_compat_r _ (D (Ok eff mo' evs)))
      (iff_trans (and_iff_compat_l _ (iff_sym (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs Hno D))) (OUT0 (Ok eff mo' evs)))).
    apply (mk_node_facts_ns segs ms mo _ (Z_to_bv 64 222) Hsvc).
    + intros eff mo' evs Hs Hns.
      destruct (proj1 (OUT _ _ _) (conj Hs Hns)) as [(e & He & Hs')|[Hs'|(e & He & Hs')]];
        apply Ok_inj in Hs' as (-> & -> & ->); [apply ERRn; exact (RF _ HC _ He)| |].
      * cbn [nstep]. split; [reflexivity|]. do 3 right. split; [exact Hm|]. split; [exact Hna|]. split; [exact Hfx|].
        left. split; reflexivity.
      * cbn [nstep]. split; [reflexivity|]. do 3 right. split; [exact Hm|]. split; [exact Hna|]. split; [exact Hfx|].
        right. exists e. repeat split; auto.
    + intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|[Hs|(e & _ & Hs)]]; discriminate.
    + intros eff mo' evs (-> & [(e & He & Hs & ->)|[(Hm' & _)|[(_ & Hna' & _)|(_ & _ & _ & [(Hs & ->)|(e & He & Hs & ->)])]]]);
        try congruence.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); left; exists e; split; [rewrite <- HC; exact He|reflexivity]].
        rewrite Hs; reflexivity.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); right; left; reflexivity]. rewrite Hs; reflexivity.
      * eexists. split; [|apply (proj2 (OUT _ _ _)); right; right; exists e; split; [exact He|reflexivity]].
        rewrite Hs; reflexivity.
    + intros eff mo' evs Hs. apply D, RAW in Hs.
      destruct Hs as [(e & _ & Hs)|[Hs|(e & _ & Hs)]]; apply Ok_inj in Hs as (_ & -> & _); [auto| |].
      * apply (mm_frame_minv mo); [|exact Hh|exact Hminv].
        apply mm_frame_with_mmap_replacement; [exact Hnr|apply mm_frame_with_vmmaps; reflexivity].
      * apply (mm_frame_minv mo); [apply mm_frame_with_mmap_destroyed; reflexivity|exact Hh|exact Hminv].
    + exists (efferr ENOMEM), mo, []. apply D, RAW. left. exists ENOMEM. split; [exact (or_introl eq_refl)| reflexivity].
Qed.

#[using="Type"] Lemma nstep_mmap_err_forced : forall addr len prot flags mo rsp mo' evs e,
  nstep (NMmap addr len prot flags) mo rsp mo' evs -> strip rsp = efferr e -> (1 <= e <= 4095)%Z ->
  nmmap_refusable mo len prot flags = true /\ e = ENOMEM /\ mo' = mo /\ evs = [].
Proof.
  intros addr len prot flags mo rsp mo' evs e [-> H] Hs He. cbv zeta in H.
  assert (INJ : forall e', strip rsp = efferr e' -> e' = ENOMEM -> e = ENOMEM).
  { intros e' Hs' ->. rewrite Hs in Hs'. apply (f_equal eff_ret) in Hs'. cbn [efferr eff0 eff_ret] in Hs'.
    apply (f_equal bv_unsigned) in Hs'. rewrite !errno_ret_unsigned in Hs' by (unfold ENOMEM; lia). unfold ENOMEM in *. lia. }
  destruct H as [(e' & He' & Hs' & ->)|[(_ & a & _ & _ & Hs' & _)|[(_ & _ & a & _ & Hs' & _)|(_ & _ & _ & [(Hs' & _)|(e' & He' & _)])]]].
  - destruct (mmap_errnos_when_In _ _ He') as [C E']. repeat split; auto. exact (INJ e' Hs' E').
  - exfalso. rewrite Hs in Hs'. unfold efferr, eff0 in Hs'. discriminate Hs'.
  - exfalso. rewrite Hs in Hs'. unfold efferr, eff0 in Hs'. discriminate Hs'.
  - exfalso. rewrite Hs in Hs'. unfold efferr, eff0 in Hs'. discriminate Hs'.
  - exfalso. exact (mmap_destructive_errnos_In _ He').
Qed.

#[using="Type"] Lemma nstep_mprotect_err_forced : forall addr len prot mo rsp mo' evs e,
  nstep (NMprotect addr len prot) mo rsp mo' evs -> strip rsp = efferr e -> (1 <= e <= 4095)%Z ->
  mprotect_refusable mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true
  /\ e = ENOMEM /\ mo' = mo /\ evs = [].
Proof.
  intros addr len prot mo rsp mo' evs e [-> H] Hs He. cbv zeta in H.
  destruct H as [(e' & He' & Hs' & ->)|(_ & Hs' & _)].
  - destruct (mprotect_errnos_when_In _ _ He') as [C ->]. repeat split; auto.
    rewrite Hs in Hs'. apply (f_equal eff_ret) in Hs'. cbn [efferr eff0 eff_ret] in Hs'.
    apply (f_equal bv_unsigned) in Hs'. rewrite !errno_ret_unsigned in Hs' by (unfold ENOMEM; lia). unfold ENOMEM in *. lia.
  - exfalso. rewrite Hs in Hs'. apply (f_equal eff_ret) in Hs'. cbn [efferr eff0 eff_ret] in Hs'.
    apply (f_equal bv_unsigned) in Hs'. rewrite errno_ret_unsigned in Hs' by lia.
    rewrite unsigned_lit64 in Hs' by lia. unfold two_pow_64 in Hs'. lia.
Qed.

#[using="Type"] Lemma strip_inplace_effect : forall old old_n new_n a b,
  strip (mremap_inplace_effect old old_n new_n a b) = mremap_inplace_effect old old_n new_n a b.
Proof. intros. unfold mremap_inplace_effect. destruct (b <? a); reflexivity. Qed.

#[using="Type"] Lemma mremap_out_shape : forall m old os ns eff mo' evs,
  mremap_out m old os ns (Ok eff mo' evs) -> evs = [] /\ strip eff = eff /\
  (mo' = m \/ exists dst nn, mo' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned os))) dst nn).
Proof.
  intros m old os ns eff mo' evs H. unfold mremap_out in H. cbv zeta in H.
  destruct H as [(E & H)|[(NE & e & He & H)|[(L & H)|[(L & G & H)|(L & dst & Hd & H)]]]];
    apply Ok_inj in H as (-> & -> & ->); (split; [reflexivity|]).
  - split; [reflexivity|]. left; reflexivity.
  - split; [reflexivity|]. left; reflexivity.
  - split; [apply strip_inplace_effect|]. right. eexists _, _; reflexivity.
  - split; [apply strip_inplace_effect|]. right. eexists _, _; reflexivity.
  - split; [reflexivity|]. right. eexists _, _; reflexivity.
Qed.

#[using="Type"] Lemma mremap_facts : forall ms mo old old_len new_len,
  at_node segs (NMremap old old_len new_len) ms -> minv mo -> m_halted mo = None ->
  nsafe (NMremap old old_len new_len) mo -> node_facts_ns segs ms mo (NMremap old old_len new_len).
Proof.
  intros ms mo old old_len new_len (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Hal & Hnew & Hold) Hminv Hh Hsrc. cbn [nsafe] in Hsrc.
  assert (Huni : mremap_backing_uniform_b mo (Z_to_bv 64 old)
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 old_len)))) = true).
  { unfold mremap_backing_uniform_b. rewrite (minv_nolazy _ Hminv). reflexivity. }
  assert (OUTg : forall i o, bv_unsigned (in_sysno i) = 216 ->
            in_arg i 0 = Z_to_bv 64 old -> in_arg i 1 = Z_to_bv 64 old_len -> in_arg i 2 = Z_to_bv 64 new_len ->
            in_arg i 3 = Z_to_bv 64 MREMAP_MAYMOVE ->
            syscall_spec i mo o <-> mremap_out mo (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) o).
  { intros i o Hno H0 H1 H2 H3. rewrite (syscall_spec_216 _ _ _ Hno), H0, H1, H2, H3.
    apply (mremap_outcome _ _ _ _ _ _ _ ltac:(apply unsigned_lit64; unfold MREMAP_MAYMOVE; lia) Hal Hnew Hold Hsrc Huni). }
  assert (Hno1 : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 216))) = 216) by (apply sysno_of; [lia|reflexivity]).
  assert (Hno2 : bv_unsigned (in_sysno (pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 old_len; Z_to_bv 64 new_len;
                                                        Z_to_bv 64 MREMAP_MAYMOVE])) = 216)
    by (apply unsigned_lit64; lia).
  assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 216)) mo o <->
            mremap_out mo (Z_to_bv 64 old) (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) o).
  { intros o. apply OUTg; [exact Hno1 | rewrite in_a0_si; exact Ha0 | rewrite in_a1_si; exact Ha1
                          | rewrite in_a2_si; exact Ha2 | rewrite in_a3_si; exact Ha3]. }
  assert (Hsp : forall eff, spurious_refusal_cfg ACFG (sys_input segs ms (Z_to_bv 64 216)) mo eff <->
                            spurious_refusal_cfg ACFG (pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 old_len;
                                                         Z_to_bv 64 new_len; Z_to_bv 64 MREMAP_MAYMOVE]) mo eff).
  { intros eff. apply spurious_refusal_transport; [reflexivity| rewrite in_a0_si; exact Ha0|].
    intros eff' m' evs'. rewrite OUT, (OUTg _ _ Hno2 eq_refl eq_refl eq_refl eq_refl). reflexivity. }
  apply (mk_node_facts_ns segs ms mo _ (Z_to_bv 64 216) Hsvc).
  - intros eff mo' evs Hs Hns. apply OUT in Hs. pose proof (mremap_out_shape _ _ _ _ _ _ _ Hs) as (-> & E & _).
    cbn [nstep]. split; [reflexivity|]. split; [exists eff; split; [exact E|exact Hs]|].
    intros Hx. apply Hns. apply Hsp. exact Hx.
  - intros Hs. apply OUT in Hs. unfold mremap_out in Hs. cbv zeta in Hs.
    destruct Hs as [(_ & H)|[(_ & e & _ & H)|[(_ & H)|[(_ & _ & H)|(_ & dst & _ & H)]]]]; discriminate.
  - intros eff mo' evs (-> & (core & Hs & Hout) & Hns). exists core.
    split; [rewrite <- Hs; apply strip_strip|]. split; [apply OUT; exact Hout|].
    apply (ns_ret ACFG _ mo eff); [rewrite <- Hs; reflexivity|]. intros Hx. apply Hns. apply Hsp. exact Hx.
  - intros eff mo' evs Hs. apply OUT in Hs. apply mremap_out_shape in Hs as (_ & _ & [->|(dst & nn & ->)]); [auto|].
    apply (mm_frame_minv mo); [|exact Hh|exact Hminv]. apply mm_frame_mremap_model_next. exact (minv_nolazy _ Hminv).
  - set (old_nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 old_len))).
    set (new_nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 new_len))).
    destruct (Z.eq_dec old_nZ new_nZ) as [E|NE].
    + exists (eff0 (Z_to_bv 64 old)), mo, []. apply OUT. unfold mremap_out. left. split; [exact E|reflexivity].
    + exists (efferr ENOMEM), mo, []. apply OUT. unfold mremap_out. right; left. split; [exact NE|]. exists ENOMEM.
      split; [cbn; tauto|reflexivity].
Qed.

#[using="Type"] Lemma length_file_read_le : forall data off c, (length (file_read data off c) <= word_to_nat c)%nat.
Proof. intros. rewrite file_read_unguarded. apply firstn_le_length. Qed.

#[using="Type"] Lemma read_bytes_map_wr_at : forall m buf count len,
  wr_at segs m buf count -> 0 <= bv_unsigned len <= count -> 0 <= buf -> buf < 2^64 ->
  exists w, read_bytes_map (wview segs m) (Z_to_bv 64 buf) len = Some w.
Proof.
  intros m buf count len W Hlen Hb0 Hb1. rewrite read_bytes_map_eq.
  pose proof (read_bytes_aux_wr_at segs m buf count (word_to_nat len) W ltac:(unfold word_to_nat; lia)) as H.
  unfold wa in H. destruct (read_bytes_aux (wview segs m) (Z_to_bv 64 buf) (word_to_nat len)) as [w|]; [exists w; reflexivity|].
  exfalso; apply H; reflexivity.
Qed.

#[using="Type"] Lemma read_facts : forall ms mo fd buf count,
  at_node segs (NRead fd buf count) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NRead fd buf count).
Proof.
  intros ms mo fd buf count (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hbc & Hwr) Hminv Hh.
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  exists (Z_to_bv 64 63). split; [exact Hsvc|].
  pose proof Hwr as (Hb0 & _ & _).
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 63)) mo o <->
                        read_spec (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) (sys_input segs ms (Z_to_bv 64 63)) mo o).
  { intros o. rewrite (syscall_spec_63 _ _ _ (sysno_of ms _ 63 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2, fd32_small by lia. reflexivity. }

  assert (Hcnt : bv_unsigned (Z_to_bv 64 count) = count) by (apply unsigned_lit64; lia).
  assert (ACC : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { apply access_okb_of_le; [lia|]. rewrite unsigned_lit64, Hcnt by lia. lia. }

  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  2:{
    assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 63)) mo o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) mo []).
    { intros o. rewrite D. apply (read_ebadf_outcome _ _ _ _ _ _ Hlk). }
    split; [|split; [|split; [|split]]].
    - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
    - intros Hs. apply OUT in Hs. discriminate.
    - intros eff mo' evs (-> & Hn). rewrite Hlk in Hn. destruct Hn as [Hs ->]. eexists. split; [|apply OUT; reflexivity]. rewrite Hs; reflexivity.
    - intros eff mo' evs (_ & Hn). rewrite Hlk in Hn. destruct Hn as [_ ->]. auto.
    - exists (efferr EBADF), mo, []. cbn [nstep]. rewrite Hlk. repeat split; reflexivity. }
  destruct e as [ch | p off | p off | p off | p off | | sk | pid wr | dnr dnw | ].
  9-10: exfalso; exact (MK _ _ Hlk).
  -   exfalso. apply MC in Hlk. rewrite unsigned_lit64 in Hlk by lia. lia.
  -
    destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
    set (bs := file_read data off (Z_to_bv 64 count)).
    assert (Hbs : (Z.of_nat (length bs) <= count)).
    { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as HL. subst bs. unfold word_to_nat in HL. rewrite Hcnt in HL. lia. }
    assert (Hclamp : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
    { rewrite rw_count_clamp_small by (rewrite Hcnt; unfold MAX_RW_COUNT; lia). apply Z_to_bv_bv_unsigned. }
    destruct (read_bytes_map_wr_at (ms_mem ms) buf count (len_word bs) Hwr
                ltac:(rewrite len_word_unsigned by (unfold two_pow_64; lia); lia) ltac:(lia) ltac:(lia)) as [w Hw].
    set (mo1 := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo).
    assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 63)) mo o <->
              o = Ok (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []) mo1 []).
    { intros o. rewrite D.
      pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count)
                    (sys_input segs ms (Z_to_bv 64 63)) mo o p off data w Hlk ACC Hfs) as R.
      cbv zeta in R. rewrite Hclamp in R. apply R. rewrite in_wmem_si. exact Hw. }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hlk, Hfs.
      repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & Hn). rewrite Hlk, Hfs in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite Hs; reflexivity.
    + intros eff mo' evs (_ & Hn). rewrite Hlk, Hfs in Hn. destruct Hn as [_ ->].
      rewrite m_halted_with_fds. split; [exact Hh|]. eapply minv_update_file; eassumption.
    + eexists (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []), mo1, [].
      cbn [nstep]. rewrite Hlk, Hfs. repeat split; reflexivity.
  -
    assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 63)) mo o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) mo []).
    { intros o. rewrite D. apply (read_wronly_outcome _ _ _ _ _ _ _ _ Hlk). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & Hn). rewrite Hlk in Hn. destruct Hn as [Hs ->]. eexists. split; [|apply OUT; reflexivity]. rewrite Hs; reflexivity.
    + intros eff mo' evs (_ & Hn). rewrite Hlk in Hn. destruct Hn as [_ ->]. auto.
    + exists (efferr EBADF), mo, []. cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
  -   exfalso. exact (MK _ _ Hlk).
  -   exfalso. exact (MK _ _ Hlk).
  -
    assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 63)) mo o <-> o = Ok (mkEffect (errno_ret EISDIR) [] []) mo []).
    { intros o. rewrite D. apply (read_dir_outcome _ _ _ _ _ _ Hlk ACC). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & Hn). rewrite Hlk in Hn. destruct Hn as [Hs ->]. eexists. split; [|apply OUT; reflexivity]. rewrite Hs; reflexivity.
    + intros eff mo' evs (_ & Hn). rewrite Hlk in Hn. destruct Hn as [_ ->]. auto.
    + exists (efferr EISDIR), mo, []. cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
  - exfalso. exact (MK _ _ Hlk).
  - exfalso. exact (MK _ _ Hlk).
Qed.

Local Ltac det5 OUT HN tacP W :=
  split; [|split; [|split; [|split]]];
  [ intros eff mo' evs Hs; apply OUT in Hs; apply Ok_inj in Hs as (-> & -> & ->); HN; repeat split; try reflexivity;
    rewrite ?strip_with_copyins; reflexivity
  | intros Hs; apply OUT in Hs; discriminate
  | idtac
  | idtac
  | W ].

#[using="Type"] Lemma open_facts : forall ms mo path,
  at_node segs (NOpen path) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NOpen path).
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hrom & Hpath) Hminv Hh.
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  exists (Z_to_bv 64 56). split; [exact Hsvc|].
  set (i := sys_input segs ms (Z_to_bv 64 56)) in *.
  set (pathp := areg ms 11) in *. set (flags := areg ms 12) in *.
  assert (Hmfl : modeled_open_flags flags = true).
  { unfold modeled_open_flags. rewrite Hfl. reflexivity. }
  assert (D : forall o, syscall_spec i mo o <-> openat_spec AT_FDCWD32 pathp flags i mo o).
  { intros o. subst i. rewrite (syscall_spec_56 _ _ _ (sysno_of ms _ 56 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0. unfold AT_FDCWD32, AT_FDCWD. reflexivity. }
  assert (Hin : bytes_in (in_mem i) (bv_unsigned pathp) (path ++ [Z_to_bv 8 0])).
  { subst i. rewrite in_mem_si. eapply bytes_at_in; eassumption. }
  pose proof (bytes_at_bound _ _ _ _ Hpath) as Hbnd. rewrite length_app in Hbnd. cbn [length] in Hbnd.
  assert (Hpw : wa (bv_unsigned pathp) = pathp) by apply wa_unsigned_id.

  assert (PRES : forall ent eff mo', open_result mo ent eff mo' ->
            match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            m_halted mo' = None /\ minv mo').
  { intros ent eff mo' [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
    rewrite m_halted_with_fds. split; [exact Hh|]. apply minv_open_insert; assumption. }

  assert (OPEN : forall R ent (mk := fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo),
            (forall o, syscall_spec i mo o <-> open_out R mo mk o) ->
            match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            (forall eff mo' evs, syscall_spec i mo (Ok eff mo' evs) -> evs = [] /\ open_result mo ent eff mo') /\
            (~ syscall_spec i mo Unmodeled) /\
            (forall eff mo', open_result mo ent eff mo' -> exists eff', strip eff' = strip eff /\ syscall_spec i mo (Ok eff' mo' [])) /\
            (forall eff mo', open_result mo ent eff mo' -> m_halted mo' = None /\ minv mo') /\
            (exists eff mo', open_result mo ent eff mo')).
  { intros R ent mk OUT Hent. split; [|split; [|split; [|split]]].
    - intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as [(e & He & Hs)|(Hfree & Hs)]; apply Ok_inj in Hs as (-> & -> & ->);
        (split; [reflexivity|]).
      + left. exists e. rewrite strip_with_copyins. repeat split; auto.
      + right. rewrite strip_with_copyins. repeat split; auto.
    - intros Hs. apply OUT in Hs. destruct Hs as [(e & _ & Hs)|(_ & Hs)]; discriminate.
    - intros eff mo' [(e & He & Hs & ->)|(Hfree & Hs & ->)].
      + eexists. split; [|apply OUT; left; exists e; split; [exact He|reflexivity]]. rewrite strip_with_copyins, Hs. reflexivity.
      + eexists. split; [|apply OUT; right; split; [exact Hfree|reflexivity]]. rewrite strip_with_copyins, Hs. reflexivity.
    - intros eff mo' Hor. exact (PRES ent eff mo' Hor Hent).
    - exists (efferr ENOMEM), mo. left. exists ENOMEM. split; [cbn; tauto|]. split; reflexivity. }
  destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
  {
    assert (Hc : read_cstr (in_mem i) pathp = CstrTooLong).
    { unfold read_cstr. rewrite <- Hpw. apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [H1 _]. exact H1. }
    assert (OUT : forall o, syscall_spec i mo o <->
       o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENAMETOOLONG) [] [])) mo []).
    { intros o. rewrite D. apply (openat_toolong_outcome _ _ _ _ _ Hmfl _ Hc). }
    det5 OUT ltac:(cbn [nstep]; rewrite (proj2 (Nat.leb_le _ _) Hlong)) idtac
         ltac:(exists (efferr ENAMETOOLONG), mo, []; cbn [nstep]; rewrite (proj2 (Nat.leb_le _ _) Hlong); repeat split; reflexivity).
    - intros eff mo' evs [-> Hn]. rewrite (proj2 (Nat.leb_le _ _) Hlong) in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
    - intros eff mo' evs [_ Hn]. rewrite (proj2 (Nat.leb_le _ _) Hlong) in Hn. destruct Hn as [_ ->]. auto. }
  assert (Hleb : (path_max <=? length path)%nat = false) by (apply Nat.leb_gt; lia).
  assert (Hc : read_cstr (in_mem i) pathp = CstrOk path).
  { unfold read_cstr. rewrite <- Hpw. apply read_cstr_aux_bytes_in; [exact Hshort|exact Hnz|exact Hin]. }
  destruct path as [|c path'].
  {
    assert (OUT : forall o, syscall_spec i mo o <->
       o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) mo []).
    { intros o. rewrite D. apply (openat_empty_outcome _ _ _ _ _ Hmfl _ Hc). }
    det5 OUT ltac:(cbn [nstep]) idtac
         ltac:(exists (efferr ENOENT), mo, []; cbn [nstep]; repeat split; reflexivity).
    - intros eff mo' evs [-> [Hs ->]]. eexists. split; [|apply OUT; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
    - intros eff mo' evs [_ [_ ->]]. auto. }
  assert (Hdir : AT_FDCWD32 = AT_FDCWD32) by reflexivity.
  destruct (path_is_dirref (c :: path')) eqn:Hdot.
  {
    assert (OUT : forall o, syscall_spec i mo o <->
       open_out (open_reads i pathp) mo (fun fd => with_fds (fd_insert (m_fds mo) fd FdDir) mo) o).
    { intros o. rewrite D. apply (openat_dirref_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path')); assumption. }
    destruct (OPEN _ FdDir OUT I) as (C1 & C2 & C3 & C4 & C5).
    split; [|split; [|split; [|split]]].
    - intros eff mo' evs Hs. destruct (C1 _ _ _ Hs) as [-> Hor]. cbn [nstep]. rewrite Hleb, Hdot. auto.
    - exact C2.
    - intros eff mo' evs [-> Hn]. rewrite Hleb, Hdot in Hn. exact (C3 _ _ Hn).
    - intros eff mo' evs [_ Hn]. rewrite Hleb, Hdot in Hn. exact (C4 _ _ Hn).
    - destruct C5 as (eff & mo' & Hor). exists eff, mo', []. cbn [nstep]. rewrite Hleb, Hdot. auto. }
  destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Hfs.
  {
    assert (OUT : forall o, syscall_spec i mo o <->
       open_out (open_reads i pathp) mo (fun fd => with_fds (fd_insert (m_fds mo) fd (FdFile (c :: path') (Z_to_bv 64 0))) mo) o).
    { intros o. rewrite D. apply (openat_file_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path') d); try assumption. discriminate. }
    destruct (OPEN _ (FdFile (c :: path') (Z_to_bv 64 0)) OUT ltac:(cbn; congruence)) as (C1 & C2 & C3 & C4 & C5).
    split; [|split; [|split; [|split]]].
    - intros eff mo' evs Hs. destruct (C1 _ _ _ Hs) as [-> Hor]. cbn [nstep]. rewrite Hleb, Hdot, Hfs. auto.
    - exact C2.
    - intros eff mo' evs [-> Hn]. cbn [nstep] in Hn. rewrite Hleb, Hdot, Hfs in Hn. exact (C3 _ _ Hn).
    - intros eff mo' evs [_ Hn]. cbn [nstep] in Hn. rewrite Hleb, Hdot, Hfs in Hn. exact (C4 _ _ Hn).
    - destruct C5 as (eff & mo' & Hor). exists eff, mo', []. cbn [nstep]. rewrite Hleb, Hdot, Hfs. auto. }
  {
    assert (OUT : forall o, syscall_spec i mo o <->
       o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) mo []).
    { intros o. rewrite D. apply (openat_absent_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path')); try assumption. discriminate. }
    det5 OUT ltac:(cbn [nstep]; rewrite Hleb, Hdot, Hfs) idtac
         ltac:(exists (efferr ENOENT), mo, []; cbn [nstep]; rewrite Hleb, Hdot, Hfs; repeat split; reflexivity).
    - intros eff mo' evs [-> Hn]. cbn [nstep] in Hn. rewrite Hleb, Hdot, Hfs in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
    - intros eff mo' evs [_ Hn]. cbn [nstep] in Hn. rewrite Hleb, Hdot, Hfs in Hn. destruct Hn as [_ ->]. auto. }
Qed.

#[using="Type"] Lemma iov_ok_of_bytes_at : forall ms iovs bufs,
  ms_rom ms = seg_rom segs -> Z.of_nat (length (concat bufs)) <= 2^24 ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  Forall2 (iov_ok (ms_read_byte ms)) iovs bufs /\ Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs.
Proof.
  intros ms iovs bufs Hrom Htot HF. induction HF as [|iov b iovs' bufs' [Hl Hb] HF IH]; [split; constructor|].
  cbn [concat] in Htot. rewrite length_app in Htot. destruct (IH ltac:(lia)) as [IH1 IH2].
  split; constructor; try assumption.
  - split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
  - rewrite Hl. cbn [snd]. rewrite unsigned_lit64 by lia. lia.
Qed.

#[using="Type"] Lemma writev_facts : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NWritev fd bufs).
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Harr & iovs & Hiov & Hbnd & HF) Hminv Hh.
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  exists (Z_to_bv 64 66). split; [exact Hsvc|].
  set (i := sys_input segs ms (Z_to_bv 64 66)) in *.
  set (iovp := areg ms 11) in *.
  assert (Hlen : length iovs = length bufs) by (eapply Forall2_length; exact HF).

  destruct (iov_ok_of_bytes_at ms iovs bufs Hrom Htot HF) as [HF' Hsmall].
  set (bs := concat bufs) in *.
  assert (Emem : in_mem i = ms_read_byte ms) by (subst i; apply in_mem_si). rewrite <- Emem in HF'.
  assert (Htotal : iovs_total iovs = Z.of_nat (length bs)) by (subst bs; eapply iovs_total_ok; exact HF').
  assert (Hgather : gather_iovecs (in_mem i) iovs = Some bs) by (subst bs; eapply gather_iovecs_ok; exact HF').
  assert (Hc32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  pose proof (bytes_at_bound _ _ _ _ Hiov) as Hiovb.
  assert (Himp : import_iovecs (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite Hc32, <- Hlen, <- (wa_unsigned_id iovp).
    apply import_iovecs_bytes_in; [rewrite Emem; eapply bytes_at_in; eassumption| exact Hsmall| exact Hbnd| lia| lia| lia]. }
  assert (Hch : fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd))).
  { rewrite fd32_small by lia. destruct Hfd as [-> | ->]; assumption. }
  assert (Hch0 : w_is0 (Z_to_bv 64 fd) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (Hrw : iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; lia).
  assert (D : forall o, syscall_spec i mo o <->
              writev_spec (fd32 (Z_to_bv 64 fd)) iovp (Z_to_bv 64 (Z.of_nat (length bufs))) i mo o).
  { intros o. subst i. rewrite (syscall_spec_66 _ _ _ (sysno_of ms _ 66 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2. reflexivity. }
  destruct bs as [|b0 bs'] eqn:Ebs.
  -
    assert (OUT : forall o, syscall_spec i mo o <->
       o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))
                            (mkEffect (Z_to_bv 64 0) [] [])) mo []).
    { intros o. rewrite D. apply (writev_chan_zero_outcome _ _ _ _ _ _ _ iovs Hch Hch0 Himp). rewrite Htotal; reflexivity. }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. fold bs. rewrite Ebs.
      split; [reflexivity|]. left. rewrite strip_with_copyins. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs [-> Hn]. cbn [nstep] in Hn. fold bs in Hn. rewrite Ebs in Hn.
      destruct Hn as [(_ & Hs & ->)|(k & Hk & _)]; [|cbn in Hk; lia].
      eexists. split; [|apply OUT; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
    + intros eff mo' evs [-> _]. auto.
    + exists (eff0 (Z_to_bv 64 0)), mo, []. cbn [nstep]. fold bs. rewrite Ebs. split; [reflexivity|]. left. repeat split; reflexivity.
  -
    rewrite <- Ebs in *.
    assert (Hbs1 : 1 <= Z.of_nat (length bs)) by (rewrite Ebs; cbn [length]; lia).
    assert (OUT : forall o, syscall_spec i mo o <->
       exists k, (1 <= k <= length bs)%nat /\
         o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] []
                   (import_iovecs_accesses (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                      ++ iov_prefix_accesses iovs k))
                mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))).
    { intros o. rewrite D. apply (writev_chan_outcome _ _ _ _ _ _ _ iovs bs Hch Hch0 Himp Hrw Hgather Hbs1). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as (k & Hk & Hs). apply Ok_inj in Hs as (-> & -> & ->).
      cbn [nstep]. fold bs. split; [reflexivity|]. right. exists k. split; [exact Hk|]. split; reflexivity.
    + intros Hs. apply OUT in Hs. destruct Hs as (k & _ & Hs). discriminate.
    + intros eff mo' evs [-> Hn]. cbn [nstep] in Hn. fold bs in Hn.
      destruct Hn as [(E & _ & _)|(k & Hk & Hs & ->)]; [rewrite Ebs in E; discriminate|].
      eexists. split; [|apply OUT; exists k; split; [exact Hk|reflexivity]]. rewrite Hs. reflexivity.
    + intros eff mo' evs [-> _]. auto.
    + exists (eff0 (Z_to_bv 64 1)), mo, (map (WriteEv (Z_to_bv 64 fd)) (firstn 1 bs)). cbn [nstep]. fold bs.
      split; [reflexivity|]. right. exists 1%nat. split; [rewrite Ebs; cbn [length]; lia|]. split; reflexivity.
Qed.

#[using="Type"] Lemma nstep_mm_frame : forall n mo eff mo' evs,
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end ->
  m_vm_lazy mo = [] ->
  (forall addr len prot flags, n = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false) ->
  nstep n mo eff mo' evs -> mm_frame mo mo' /\ evs = [].
Proof.
  intros n mo eff mo' evs Hn Hl Hnr H. destruct n; try contradiction; cbn [nstep] in H.
  - destruct H as (-> & (r & _ & _ & ->) & _). split; [apply mm_frame_with_brk_next|reflexivity].
  - specialize (Hnr _ _ _ _ eq_refl). destruct H as [-> H]. split; [|reflexivity]. cbv zeta in H.
    destruct H as [(e & _ & _ & ->)|[(_ & a & _ & _ & _ & ->)|[(_ & _ & a & _ & _ & ->)|(_ & _ & _ & [(_ & ->)|(e & _ & _ & ->)])]]].
    + apply mm_frame_refl.
    + apply mm_frame_with_mmap_backing; [exact Hnr|apply mm_frame_with_vmmaps; reflexivity].
    + apply mm_frame_with_mmap_backing; [exact Hnr|apply mm_frame_with_vmmaps; reflexivity].
    + apply mm_frame_with_mmap_replacement; [exact Hnr|apply mm_frame_with_vmmaps; reflexivity].
    + apply mm_frame_with_mmap_destroyed. reflexivity.
  - destruct H as (-> & _ & ->). split; [apply mm_frame_with_mmap_destroyed; reflexivity|reflexivity].
  - destruct H as [-> [(e & _ & _ & ->)|(_ & _ & ->)]]; (split; [|reflexivity]); [apply mm_frame_refl|apply mm_frame_mprotect_model_next].
  - destruct H as (-> & (core & _ & Hout) & _). split; [|reflexivity].
    apply mremap_out_shape in Hout as (_ & _ & [->|(dst & nn & ->)]); [apply mm_frame_refl|]. apply mm_frame_mremap_model_next. exact Hl.
Qed.

#[using="Type"] Lemma minv_preserved : forall n mo eff mo' evs,
  (forall addr len prot flags, n = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false) ->
  minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hnr Hminv Hh H.
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  assert (Hor : forall ent, open_result mo ent eff mo' ->
            match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            m_halted mo' = None /\ minv mo').
  { intros ent [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
    rewrite m_halted_with_fds. split; [exact Hh|]. apply minv_open_insert; assumption. }
  assert (MM : match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end ->
               m_halted mo' = None /\ minv mo').
  { intros Hn. destruct (nstep_mm_frame n mo eff mo' evs Hn ML Hnr H) as [Hfr _]. exact (mm_frame_minv _ _ Hfr Hh Hminv). }
  destruct n; cbn [nstep] in H; try (apply MM; exact I).
  - destruct H as [-> _]; auto.
  - destruct H as [_ H].
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
    destruct path as [|c path']. { destruct H as [_ ->]; auto. }
    destruct (path_is_dirref (c :: path')). { exact (Hor FdDir H I). }
    destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
    + apply (Hor _ H). cbn. congruence.
    + destruct H as [_ ->]; auto.
  - destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid wr|dnr dnw| ]|] eqn:Hlk; try contradiction.
    + destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
      rewrite m_halted_with_fds. split; [exact Hh|]. eapply minv_update_file; eassumption.
    + destruct H as [_ ->]. auto.
    + destruct H as [_ ->]. auto.
    + destruct H as [_ ->]. auto.
  - destruct H as (_ & Hfd & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
    rewrite m_halted_with_fds. split; [exact Hh|]. apply minv_remove; assumption.
  - destruct H as (_ & _ & ->); auto.
  - destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; auto.
    rewrite m_halted_with_tid. split; [exact Hh|]. apply minv_with_tid; assumption.
  - destruct H.
  -   destruct H as [_ H]. unfold create_result in H.
    destruct (path_is_dirref path); [destruct H as [_ ->]; auto|].
    destruct (fs_under (m_fs mo) path); [destruct H as [_ ->]; auto|].
    destruct H as [(e & _ & _ & ->)|(Hfree & _ & ->)]; [auto|].
    rewrite m_halted_with_fds, m_halted_with_fs. split; [exact Hh|]. apply minv_create; assumption.
  -   destruct H as (_ & -> & _). auto.
  -   destruct H as (_ & p & off & data & Hlk & Hfs & _ & ->).
    rewrite m_halted_with_fds, m_halted_with_fs. split; [exact Hh|]. eapply minv_write_filew; eassumption.
  -   destruct H as (_ & e & p & cur & data & Hlk & He & Hfs & H).
    destruct (lseek_dest _ _) as [r|]; destruct H as [_ ->]; [|auto].
    rewrite m_halted_with_fds. split; [exact Hh|]. eapply minv_reseek; [assumption| exact Hlk| destruct He as [-> | ->]; exact I].
  -   destruct H as (_ & p & off & data & Hlk & Hfs & _ & ->).
    rewrite m_halted_with_fds. split; [exact Hh|]. eapply minv_update_file; eassumption.
  -   destruct H as [_ H]. destruct (fs_lookup (m_fs mo) path).
    + destruct H as [(e & _ & _ & ->)|(Hn & _ & ->)]; [auto|].
      rewrite m_halted_with_fs. split; [exact Hh|]. apply minv_unlink; assumption.
    + destruct H as [_ ->]; auto.
Qed.

#[using="Type"] Lemma nsafe_mmap_rw : forall addr len mo,
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo. cbn [nsafe]. intros H. exfalso. revert H. vm_compute. discriminate. Qed.

#[using="Type"] Lemma nsafe_mmap_none : forall addr len mo,
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo. cbn [nsafe]. intros H. exfalso. revert H. vm_compute. discriminate. Qed.

#[using="Type"] Lemma ioctlf_facts : forall ms mo fd,
  at_node segs (NIoctlF fd) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NIoctlF fd).
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0 & Ha1) Hminv Hh.
  exists (Z_to_bv 64 29). split; [exact Hsvc|].
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 29)) mo o <->
                        ioctl_spec (Z_to_bv 64 fd) (cmd32 (Z_to_bv 64 TIOCGWINSZ)) (sys_input segs ms (Z_to_bv 64 29)) mo o).
  { intros o. rewrite (syscall_spec_29 _ _ _ (sysno_of ms _ 29 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1, fd32_small by lia. reflexivity. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 29)) mo o <-> o = Ok (mkEffect (errno_ret ENOTTY) [] []) mo []).
    { intros o. rewrite D. apply (ioctl_tty_outcome _ _ _ _ _ _ Hlk tty_only_TIOCGWINSZ).

      - intros rd wr ->. destruct Hminv as (_ & _ & _ & _ & _ & M6 & _). exact (M6 _ _ Hlk).
      - intros ->. destruct Hminv as (_ & _ & _ & _ & _ & M6 & _). exact (M6 _ _ Hlk). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & -> & Hn). rewrite Hlk in Hn. eexists. split; [|apply OUT; reflexivity]. rewrite Hn. reflexivity.
    + intros eff mo' evs (_ & -> & _). auto.
    + exists (efferr ENOTTY), mo, []. cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
  - assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 29)) mo o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) mo []).
    { intros o. rewrite D. apply (ioctl_ebadf_outcome _ _ _ _ _ Hlk). }
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & -> & Hn). rewrite Hlk in Hn. eexists. split; [|apply OUT; reflexivity]. rewrite Hn. reflexivity.
    + intros eff mo' evs (_ & -> & _). auto.
    + exists (efferr EBADF), mo, []. cbn [nstep]. rewrite Hlk. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma openw_facts : forall ms mo path,
  at_node segs (NOpenW path) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NOpenW path).
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hne & Hlen & Hsl & Hrom & Hpath) Hminv Hh.
  exists (Z_to_bv 64 56). split; [exact Hsvc|].
  set (i := sys_input segs ms (Z_to_bv 64 56)) in *.
  set (pathp := areg ms 11) in *. set (flags := areg ms 12) in *.
  assert (D : forall o, syscall_spec i mo o <-> openat_spec AT_FDCWD32 pathp flags i mo o).
  { intros o. subst i. rewrite (syscall_spec_56 _ _ _ (sysno_of ms _ 56 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0. unfold AT_FDCWD32, AT_FDCWD. reflexivity. }
  assert (Hin : bytes_in (in_mem i) (bv_unsigned pathp) (path ++ [Z_to_bv 8 0])).
  { subst i. rewrite in_mem_si. eapply bytes_at_in; eassumption. }
  assert (Hpw : wa (bv_unsigned pathp) = pathp) by apply wa_unsigned_id.
  assert (Hc : read_cstr (in_mem i) pathp = CstrOk path).
  { unfold read_cstr. rewrite <- Hpw. apply read_cstr_aux_bytes_in; [exact Hlen|exact Hnz|exact Hin]. }
  assert (OUT : forall o, syscall_spec i mo o <-> create_out (open_reads i pathp) mo path o).
  { intros o. rewrite D. apply (openat_create_outcome pathp flags i mo o path); assumption. }
  unfold create_out in OUT.

  Local Ltac det_arm OUT CR E mo :=
    split; [|split; [|split; [|split]]];
    [ intros eff mo' evs Hs; apply OUT in Hs; apply Ok_inj in Hs as (-> & -> & ->); cbn [nstep]; rewrite CR;
      split; [reflexivity|]; rewrite strip_with_copyins; split; reflexivity
    | intros Hs; apply OUT in Hs; discriminate
    | intros eff mo' evs [-> Hn]; rewrite CR in Hn; destruct Hn as [Hs ->];
      eexists; split; [|apply OUT; reflexivity]; rewrite strip_with_copyins, Hs; reflexivity
    | intros eff mo' evs [_ Hn]; rewrite CR in Hn; destruct Hn as [_ ->]; auto
    | exists (efferr E), mo, (@nil event); cbn [nstep]; rewrite CR; repeat split; reflexivity ].
  destruct (path_is_dirref path) eqn:E1.
  { assert (CR : forall eff mo', create_result mo path eff mo' = (strip eff = efferr EISDIR /\ mo' = mo))
      by (intros; unfold create_result; rewrite E1; reflexivity).
    det_arm OUT CR EISDIR mo. }
  destruct (fs_under (m_fs mo) path) eqn:E3.
  { assert (CR : forall eff mo', create_result mo path eff mo' = (strip eff = efferr EISDIR /\ mo' = mo))
      by (intros; unfold create_result; rewrite E1, E3; reflexivity).
    det_arm OUT CR EISDIR mo. }
  assert (CR : forall eff mo', create_result mo path eff mo' =
            ((exists e, In e openat_errnos /\ strip eff = efferr e /\ mo' = mo)
             \/ (let fd := alloc_fd (m_fds mo) in
                 fd_lookup (m_fds mo) fd = None /\ strip eff = eff0 fd /\
                 mo' = with_fds (fd_insert (m_fds mo) fd (FdFileW path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) path []) mo))))
    by (intros; unfold create_result; rewrite E1, E3; reflexivity).
  split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as [(e & He & Hs)|(Hfree & Hs)]; apply Ok_inj in Hs as (-> & -> & ->);
      cbn [nstep]; rewrite CR; (split; [reflexivity|]).
    + left. exists e. rewrite strip_with_copyins. repeat split; auto.
    + right. rewrite strip_with_copyins. repeat split; auto.
  - intros Hs. apply OUT in Hs. destruct Hs as [(e & _ & Hs)|(_ & Hs)]; discriminate.
  - intros eff mo' evs [-> Hn]. rewrite CR in Hn. destruct Hn as [(e & He & Hs & ->)|(Hfree & Hs & ->)].
    + eexists. split; [|apply OUT; left; exists e; split; [exact He|reflexivity]]. rewrite strip_with_copyins, Hs. reflexivity.
    + eexists. split; [|apply OUT; right; split; [exact Hfree|reflexivity]]. rewrite strip_with_copyins, Hs. reflexivity.
  - intros eff mo' evs [_ Hn]. rewrite CR in Hn. destruct Hn as [(e & _ & _ & ->)|(Hfree & _ & ->)]; [auto|].
    rewrite m_halted_with_fds, m_halted_with_fs. split; [exact Hh|]. apply minv_create; assumption.
  - exists (efferr ENOMEM), mo, []. cbn [nstep]. rewrite CR. split; [reflexivity|]. left. exists ENOMEM.
    split; [cbn; tauto|]. split; reflexivity.
Qed.

#[using="Type"] Lemma writevf_facts : forall ms mo fd bufs,
  at_node segs (NWritevF fd bufs) ms -> minv mo -> m_halted mo = None -> nsafe (NWritevF fd bufs) mo ->
  node_facts segs ms mo (NWritevF fd bufs).
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Harr & iovs & Hiov & Hbnd & HF) Hminv Hh (p & off & data & Hlk & Hfs & Hgap & Hpos).
  exists (Z_to_bv 64 66). split; [exact Hsvc|].
  set (i := sys_input segs ms (Z_to_bv 64 66)) in *.
  set (iovp := areg ms 11) in *.
  assert (Hlen : length iovs = length bufs) by (eapply Forall2_length; exact HF).
  destruct (iov_ok_of_bytes_at ms iovs bufs Hrom ltac:(lia) HF) as [HF' Hsmall].
  set (bs := concat bufs) in *.
  assert (Emem : in_mem i = ms_read_byte ms) by (subst i; apply in_mem_si). rewrite <- Emem in HF'.
  assert (Htotal : iovs_total iovs = Z.of_nat (length bs)) by (subst bs; eapply iovs_total_ok; exact HF').
  assert (Hgather : gather_iovecs (in_mem i) iovs = Some bs) by (subst bs; eapply gather_iovecs_ok; exact HF').
  assert (Hc32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  pose proof (bytes_at_bound _ _ _ _ Hiov) as Hiovb.
  assert (Himp : import_iovecs (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite Hc32, <- Hlen, <- (wa_unsigned_id iovp).
    apply import_iovecs_bytes_in; [rewrite Emem; eapply bytes_at_in; eassumption| exact Hsmall| exact Hbnd| lia| lia| lia]. }
  assert (Hfd' : fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdFileW p off)) by (rewrite fd32_small by lia; exact Hlk).
  assert (Hrw : iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; lia).
  assert (Hbs1 : 1 <= Z.of_nat (length bs)) by (subst bs; lia).
  assert (Hpos' : rw_pos_einvalb off (iovs_total iovs) = false).
  { unfold rw_pos_einvalb. apply Z.ltb_ge. rewrite Htotal. subst bs. lia. }
  assert (D : forall o, syscall_spec i mo o <->
              writev_spec (fd32 (Z_to_bv 64 fd)) iovp (Z_to_bv 64 (Z.of_nat (length bufs))) i mo o).
  { intros o. subst i. rewrite (syscall_spec_66 _ _ _ (sysno_of ms _ 66 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2. reflexivity. }
  set (mo1 := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word bs)%bv))
                       (with_fs (fs_set (m_fs mo) p (file_write data off bs)) mo)).
  assert (OUT : forall o, syscall_spec i mo o <->
     o = Ok (mkEffectU (len_word bs) [] [] [] []
               (import_iovecs_accesses (in_mem i) iovp (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                  ++ iov_prefix_accesses iovs (length bs)))
            mo1 []).
  { intros o. rewrite D. subst mo1. rewrite <- (fd32_small fd) at 2 by lia.
    apply (writev_file_outcome _ _ _ _ _ _ p off data iovs bs Hfd' Hfs Himp Hrw Hgather Hbs1 Hpos' Hgap). }
  split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->).
    cbn [nstep]. split; [reflexivity|]. exists p, off, data. split; [exact Hlk|]. split; [exact Hfs|]. fold bs. split; reflexivity.
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff mo' evs (-> & p' & off' & data' & Hlk' & Hfs' & Hs & ->). rewrite Hlk in Hlk'. injection Hlk' as <- <-.
    rewrite Hfs in Hfs'. injection Hfs' as <-. fold bs in Hs. fold bs.
    eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
  - intros eff mo' evs (_ & p' & off' & data' & Hlk' & Hfs' & _ & ->).
    rewrite m_halted_with_fds, m_halted_with_fs. split; [exact Hh|]. eapply minv_write_filew; eassumption.
  - exists (eff0 (len_word bs)), mo1, []. cbn [nstep]. split; [reflexivity|]. exists p, off, data.
    split; [exact Hlk|]. split; [exact Hfs|]. fold bs. split; reflexivity.
Qed.

#[using="Type"] Lemma lseek_facts : forall ms mo fd off whence,
  at_node segs (NLseek fd off whence) ms -> minv mo -> m_halted mo = None -> nsafe (NLseek fd off whence) mo ->
  node_facts segs ms mo (NLseek fd off whence).
Proof.
  intros ms mo fd off whence (Hsvc & Hfd & Hoff & Hwh & Ha0 & Ha1 & Ha2) Hminv Hh (e & p & cur & Hlk & He).
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  exists (Z_to_bv 64 62). split; [exact Hsvc|].
  assert (Hw32 : whence32 (Z_to_bv 64 whence) = Z_to_bv 64 whence) by (unfold whence32; apply abi_low32_small; lia).
  assert (D : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 62)) mo o <->
                        lseek_spec (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) (sys_input segs ms (Z_to_bv 64 62)) mo o).
  { intros o. rewrite (syscall_spec_62 _ _ _ (sysno_of ms _ 62 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2, fd32_small, Hw32 by lia. reflexivity. }
  assert (Hfs : exists data, fs_lookup (m_fs mo) p = Some data).
  { destruct He as [-> | ->].
    - destruct (fs_lookup (m_fs mo) p) eqn:E; [eexists; reflexivity| exfalso; exact (MF _ _ _ Hlk E)].
    - pose proof (MK _ _ Hlk) as K. cbn in K. destruct (fs_lookup (m_fs mo) p) eqn:E; [eexists; reflexivity| exfalso; exact (K eq_refl)]. }
  destruct Hfs as [data Hfs].
  assert (Hbase : lseek_base (Z_to_bv 64 whence) cur (len_word data) = Some (lseek_origin whence cur data)).
  { unfold lseek_base, lseek_origin. rewrite unsigned_lit64 by lia. unfold SEEK_SET, SEEK_CUR, SEEK_END.
    assert (whence = 0 \/ whence = 1 \/ whence = 2) as [-> | [-> | ->]] by lia; reflexivity. }
  assert (OUT : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 62)) mo o <->
                          lseek_file_out mo (Z_to_bv 64 fd) e (lseek_origin whence cur data) (Z_to_bv 64 off) o).
  { intros o. rewrite D. apply (lseek_file_outcome _ _ _ _ _ _ e p cur data); try assumption.
    rewrite unsigned_lit64 by lia. unfold SEEK_MAX. lia. }
  assert (RE : forall r, reseek e r = reseek_ent e r) by (intros r; destruct e; reflexivity).
  unfold lseek_file_out in OUT.
  destruct (lseek_dest (lseek_origin whence cur data) (Z_to_bv 64 off)) as [r|] eqn:Hd.
  - rewrite RE in OUT.
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep].
      split; [reflexivity|]. exists e, p, cur, data. rewrite Hd. repeat split; auto.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & e' & p' & cur' & data' & Hlk' & He' & Hfs' & Hn).
      rewrite Hlk in Hlk'. injection Hlk' as <-.
      assert (p' = p /\ cur' = cur) as [-> ->] by (destruct He as [-> | ->]; destruct He' as [E|E]; inversion E; auto).
      rewrite Hfs in Hfs'. injection Hfs' as <-. rewrite Hd in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
    + intros eff mo' evs (_ & e' & p' & cur' & data' & Hlk' & He' & Hfs' & Hn).
      rewrite Hlk in Hlk'. injection Hlk' as <-.
      assert (p' = p /\ cur' = cur) as [-> ->] by (destruct He as [-> | ->]; destruct He' as [E|E]; inversion E; auto).
      rewrite Hfs in Hfs'. injection Hfs' as <-. rewrite Hd in Hn. destruct Hn as [_ ->].
      rewrite m_halted_with_fds. split; [exact Hh|]. eapply minv_reseek; [exact Hminv| exact Hlk| destruct He as [-> | ->]; exact I].
    + exists (eff0 r), (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (reseek_ent e r)) mo), []. cbn [nstep].
      split; [reflexivity|]. exists e, p, cur, data. rewrite Hd. repeat split; auto.
  - split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep].
      split; [reflexivity|]. exists e, p, cur, data. rewrite Hd. repeat split; auto.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs (-> & e' & p' & cur' & data' & Hlk' & He' & Hfs' & Hn).
      rewrite Hlk in Hlk'. injection Hlk' as <-.
      assert (p' = p /\ cur' = cur) as [-> ->] by (destruct He as [-> | ->]; destruct He' as [E|E]; inversion E; auto).
      rewrite Hfs in Hfs'. injection Hfs' as <-. rewrite Hd in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite Hs. reflexivity.
    + intros eff mo' evs (_ & e' & p' & cur' & data' & Hlk' & He' & Hfs' & Hn).
      rewrite Hlk in Hlk'. injection Hlk' as <-.
      assert (p' = p /\ cur' = cur) as [-> ->] by (destruct He as [-> | ->]; destruct He' as [E|E]; inversion E; auto).
      rewrite Hfs in Hfs'. injection Hfs' as <-. rewrite Hd in Hn. destruct Hn as [_ ->]. auto.
    + exists (efferr EINVAL), mo, []. cbn [nstep]. split; [reflexivity|]. exists e, p, cur, data. rewrite Hd. repeat split; auto.
Qed.

#[using="Type"] Lemma scatter_cons_ne : forall mp base len rest (bs : list byte), bs <> [] ->
  scatter_iovecs mp ((base, len) :: rest) bs =
    (let n := word_to_nat_bounded len (length bs) in
     let here := firstn n bs in
     let later := skipn n bs in
     match here with
     | [] => scatter_iovecs mp rest later
     | _ :: _ =>
         match read_bytes_map mp base (len_word here), scatter_iovecs mp rest later with
         | Some _, Some writes => Some ((base, here) :: writes)
         | _, _ => None
         end
     end).
Proof. intros mp base len rest bs Hne. destruct bs; [congruence| reflexivity]. Qed.

#[using="Type"] Lemma scatter_nil_bs : forall mp iovs, scatter_iovecs mp iovs ([] : list byte) = Some [].
Proof. intros mp iovs. destruct iovs; reflexivity. Qed.

#[using="Type"] Lemma scatter2_ok : forall mp a1 n1 a2 n2 bs,
  0 < n1 -> 0 < n2 -> n1 < 2^63 -> n2 < 2^63 -> Z.of_nat (length bs) <= n1 + n2 ->
  (forall k, Z.of_nat k <= n1 -> exists w, read_bytes_map mp (Z_to_bv 64 a1) (Z_to_bv 64 (Z.of_nat k)) = Some w) ->
  (forall k, Z.of_nat k <= n2 -> exists w, read_bytes_map mp (Z_to_bv 64 a2) (Z_to_bv 64 (Z.of_nat k)) = Some w) ->
  scatter_iovecs mp [(Z_to_bv 64 a1, Z_to_bv 64 n1); (Z_to_bv 64 a2, Z_to_bv 64 n2)] bs = Some (scatter2 a1 n1 a2 bs).
Proof.
  intros mp a1 n1 a2 n2 bs Hn1 Hn2 Hb1 Hb2 Hlen R1 R2. unfold scatter2.
  destruct bs as [|b bs'] eqn:Ebs.
  { cbn. rewrite firstn_nil, skipn_nil. reflexivity. }
  assert (Hne : bs <> []) by (rewrite Ebs; discriminate).
  rewrite <- Ebs in Hlen. rewrite <- Ebs. clear Ebs b bs'.
  rewrite (scatter_cons_ne _ _ _ _ _ Hne). cbv zeta.
  rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. rewrite unsigned_lit64 by lia.
  rewrite firstn_min_length.
  replace (skipn (Nat.min (Z.to_nat n1) (length bs)) bs) with (skipn (Z.to_nat n1) bs).
  2:{ destruct (Nat.le_ge_cases (Z.to_nat n1) (length bs)) as [L|L].
      - rewrite Nat.min_l by exact L. reflexivity.
      - rewrite Nat.min_r by exact L. rewrite !skipn_all2 by lia. reflexivity. }
  set (h := firstn (Z.to_nat n1) bs). set (t := skipn (Z.to_nat n1) bs).
  assert (Hh : (length h <= Z.to_nat n1)%nat) by (subst h; rewrite length_firstn; lia).
  assert (Ht : Z.of_nat (length t) <= n2) by (subst t; rewrite length_skipn; lia).
  assert (Hhne : h <> []).
  { subst h. destruct bs as [|b bs']; [congruence|]. cbn. destruct (Z.to_nat n1) eqn:E; [lia| discriminate]. }
  destruct h as [|hb h'] eqn:Eh; [congruence|]. rewrite <- Eh in *. clear Eh hb h'.
  destruct (R1 (length h) ltac:(lia)) as [w1 Hw1]. unfold len_word at 1. rewrite Hw1.
  destruct t as [|tb t'] eqn:Et.
  - rewrite scatter_nil_bs. cbn [app]. reflexivity.
  - assert (Htne : t <> []) by (rewrite Et; discriminate). rewrite <- Et in *. clear Et tb t'.
    rewrite (scatter_cons_ne _ _ _ _ _ Htne). cbv zeta.
    rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. rewrite unsigned_lit64 by lia.
    rewrite Nat.min_r by lia. rewrite firstn_all, skipn_all.
    destruct t as [|tb t'] eqn:Et; [congruence|]. rewrite <- Et in *. clear Et tb t'.
    destruct (R2 (length t) ltac:(lia)) as [w2 Hw2]. unfold len_word. rewrite Hw2. cbn. reflexivity.
Qed.

#[using="Type"] Lemma readv_facts : forall ms mo fd a1 n1 a2 n2,
  at_node segs (NReadv fd a1 n1 a2 n2) ms -> minv mo -> m_halted mo = None -> nsafe (NReadv fd a1 n1 a2 n2) mo ->
  node_facts segs ms mo (NReadv fd a1 n1 a2 n2).
Proof.
  intros ms mo fd a1 n1 a2 n2 (Hsvc & Hfd & Ha0 & Ha2 & Hn1 & Hn2 & Htot & Hp1 & Hb1 & Hp2 & Hb2 & Hiovp & Hrom & Hiov & W1 & W2)
         Hminv Hh (p & off & Hlk & Hpos).
  pose proof Hminv as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MS).
  exists (Z_to_bv 64 65). split; [exact Hsvc|].
  set (i := sys_input segs ms (Z_to_bv 64 65)) in *.
  set (iovp := areg ms 11) in *.
  set (iovs := [(Z_to_bv 64 a1, Z_to_bv 64 n1); (Z_to_bv 64 a2, Z_to_bv 64 n2)]) in *.
  destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
  assert (D : forall o, syscall_spec i mo o <-> readv_spec (fd32 (Z_to_bv 64 fd)) iovp (Z_to_bv 64 2) i mo o).
  { intros o. subst i. rewrite (syscall_spec_65 _ _ _ (sysno_of ms _ 65 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2. reflexivity. }
  assert (Emem : in_mem i = ms_read_byte ms) by (subst i; apply in_mem_si).
  assert (Ewmem : in_wmem i = ms_writable_byte segs ms) by (subst i; apply in_wmem_si).
  assert (Hcopy : copy_iovecs_aux (in_mem i) iovp (word_to_nat (Z_to_bv 64 2)) = ImpOk iovs).
  { unfold word_to_nat. rewrite unsigned_lit64 by lia. change (Z.to_nat 2) with (length iovs). rewrite <- (wa_unsigned_id iovp).
    apply copy_iovecs_aux_bytes_in.
    - rewrite Emem. eapply bytes_at_in; eassumption.
    - subst iovs. constructor; [cbn; rewrite unsigned_lit64 by lia; lia|]. constructor; [cbn; rewrite unsigned_lit64 by lia; lia|]. constructor. }
  assert (Himp : import_iovecs (in_mem i) iovp (Z_to_bv 64 2) = ImpOk iovs).
  { change (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length iovs))). rewrite <- (wa_unsigned_id iovp).
    apply import_iovecs_bytes_in.
    - rewrite Emem. eapply bytes_at_in; eassumption.
    - subst iovs. constructor; [cbn; rewrite unsigned_lit64 by lia; lia|]. constructor; [cbn; rewrite unsigned_lit64 by lia; lia|]. constructor.
    - subst iovs. constructor; [cbn; rewrite !unsigned_lit64 by lia; lia|]. constructor; [cbn; rewrite !unsigned_lit64 by lia; lia|]. constructor.
    - subst iovs. cbn. lia.
    - pose proof (bv_unsigned_in_range 64 iovp). lia.
    - subst iovs. cbn [length]. lia. }
  assert (Htotal : iovs_total iovs = n1 + n2).
  { subst iovs. cbn [iovs_total fst snd]. rewrite !unsigned_lit64 by lia. lia. }
  assert (Hposb : rw_pos_einvalb off (iovs_total iovs) = false).
  { unfold rw_pos_einvalb. apply Z.ltb_ge. rewrite Htotal. lia. }
  assert (Hheap : readv_heap_iovecb (Z_to_bv 64 2) = false).
  { unfold readv_heap_iovecb, iovcnt32. rewrite abi_low32_small, unsigned_lit64 by lia. reflexivity. }
  set (bs := file_read data off (Z_to_bv 64 (n1 + n2))).
  assert (Hbs : Z.of_nat (length bs) <= n1 + n2).
  { pose proof (length_file_read_le data off (Z_to_bv 64 (n1 + n2))) as HL. subst bs. unfold word_to_nat in HL. rewrite unsigned_lit64 in HL by lia. lia. }
  assert (Hsc : scatter_iovecs (in_wmem i) iovs bs = Some (scatter2 a1 n1 a2 bs)).
  { subst iovs. rewrite Ewmem. unfold ms_writable_byte. apply scatter2_ok; try lia.
    - intros k Hk. destruct (read_bytes_map_wr_at (ms_mem ms) a1 n1 (Z_to_bv 64 (Z.of_nat k)) W1 ltac:(rewrite unsigned_lit64 by lia; lia) ltac:(lia) ltac:(lia)) as [w Hw].
      exists w. exact Hw.
    - intros k Hk. destruct (read_bytes_map_wr_at (ms_mem ms) a2 n2 (Z_to_bv 64 (Z.of_nat k)) W2 ltac:(rewrite unsigned_lit64 by lia; lia) ltac:(lia) ltac:(lia)) as [w Hw].
      exists w. exact Hw. }
  set (mo1 := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo).
  assert (OUT : forall o, syscall_spec i mo o <->
     o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iovp (Z_to_bv 64 2)) (mkEffect (len_word bs) (scatter2 a1 n1 a2 bs) [])) mo1 []).
  { intros o. rewrite D. subst mo1. rewrite <- (fd32_small fd) at 2 by lia.
    assert (Hc32 : iovcnt32 (Z_to_bv 64 2) = Z_to_bv 64 2) by (unfold iovcnt32; apply abi_low32_small; lia).
    pose proof (readv_file_outcome (fd32 (Z_to_bv 64 fd)) iovp (Z_to_bv 64 2) i mo o p off data iovs bs (scatter2 a1 n1 a2 bs)) as R.
    rewrite Hc32 in R. apply R;
      [rewrite fd32_small by lia; exact Hlk| exact Hfs| exact Hheap| exact Himp
      | rewrite Htotal; unfold MAX_RW_COUNT; lia| exact Hposb| rewrite Htotal; reflexivity| exact Hsc]. }
  split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->).
    cbn [nstep]. split; [reflexivity|]. exists p, off, data. split; [exact Hlk|]. split; [exact Hfs|]. fold bs.
    rewrite strip_with_copyins. split; reflexivity.
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff mo' evs (-> & p' & off' & data' & Hlk' & Hfs' & Hs & ->). rewrite Hlk in Hlk'. injection Hlk' as <- <-.
    rewrite Hfs in Hfs'. injection Hfs' as <-. fold bs in Hs. fold bs.
    eexists. split; [|apply OUT; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
  - intros eff mo' evs (_ & p' & off' & data' & Hlk' & Hfs' & _ & ->).
    rewrite m_halted_with_fds. split; [exact Hh|]. eapply minv_update_file; eassumption.
  - exists (mkEffect (len_word bs) (scatter2 a1 n1 a2 bs) []), mo1, []. cbn [nstep]. split; [reflexivity|]. exists p, off, data.
    split; [exact Hlk|]. split; [exact Hfs|]. fold bs. split; reflexivity.
Qed.

#[using="Type"] Lemma unlink_facts : forall ms mo path,
  at_node segs (NUnlink path) ms -> minv mo -> m_halted mo = None -> nsafe (NUnlink path) mo ->
  node_facts segs ms mo (NUnlink path).
Proof.
  intros ms mo path (Hsvc & Ha0 & Ha2 & Hnz & Hne & Hnd & Hndd & Hlen & Hsl & Hrom & Hpath) Hminv Hh (Hun & Hfn).
  exists (Z_to_bv 64 35). split; [exact Hsvc|].
  set (i := sys_input segs ms (Z_to_bv 64 35)) in *.
  set (pathp := areg ms 11) in *.
  assert (D : forall o, syscall_spec i mo o <-> unlinkat_spec AT_FDCWD32 pathp (Z_to_bv 64 0) i mo o).
  { intros o. subst i. rewrite (syscall_spec_35 _ _ _ (sysno_of ms _ 35 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2. unfold AT_FDCWD32, AT_FDCWD. reflexivity. }
  assert (Hin : bytes_in (in_mem i) (bv_unsigned pathp) (path ++ [Z_to_bv 8 0])).
  { subst i. rewrite in_mem_si. eapply bytes_at_in; eassumption. }
  assert (Hpw : wa (bv_unsigned pathp) = pathp) by apply wa_unsigned_id.
  assert (Hc : read_cstr (in_mem i) pathp = CstrOk path).
  { unfold read_cstr. rewrite <- Hpw. apply read_cstr_aux_bytes_in; [unfold path_max; lia|exact Hnz|exact Hin]. }
  assert (Hnm : Nat.ltb NAME_MAX (length path) = false) by (apply Nat.ltb_ge; unfold NAME_MAX; lia).
  assert (OUT : forall o, syscall_spec i mo o <-> unlink_out (open_reads i pathp) mo path o).
  { intros o. rewrite D. apply (unlinkat_outcome pathp i mo o path); assumption. }
  unfold unlink_out in OUT.
  destruct (fs_lookup (m_fs mo) path) as [d|] eqn:Hfs.
  - pose proof (Hfn d eq_refl) as Hnames.
    split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. destruct Hs as [(e & He & Hs)|Hs]; apply Ok_inj in Hs as (-> & -> & ->);
        cbn [nstep]; rewrite Hfs; (split; [reflexivity|]).
      * left. exists e. rewrite strip_with_copyins. repeat split; auto.
      * right. rewrite strip_with_copyins. repeat split; auto.
    + intros Hs. apply OUT in Hs. destruct Hs as [(e & _ & Hs)|Hs]; discriminate.
    + intros eff mo' evs [-> Hn]. rewrite Hfs in Hn. destruct Hn as [(e & He & Hs & ->)|(_ & Hs & ->)].
      * eexists. split; [|apply OUT; left; exists e; split; [exact He|reflexivity]]. rewrite strip_with_copyins, Hs. reflexivity.
      * eexists. split; [|apply OUT; right; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
    + intros eff mo' evs [_ Hn]. rewrite Hfs in Hn. destruct Hn as [(e & _ & _ & ->)|(_ & _ & ->)]; [auto|].
      rewrite m_halted_with_fs. split; [exact Hh|]. apply minv_unlink; assumption.
    + exists (efferr ENOMEM), mo, []. cbn [nstep]. rewrite Hfs. split; [reflexivity|]. left. exists ENOMEM.
      split; [cbn; tauto|]. split; reflexivity.
  - split; [|split; [|split; [|split]]].
    + intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [nstep]. rewrite Hfs.
      rewrite strip_with_copyins. repeat split; reflexivity.
    + intros Hs. apply OUT in Hs. discriminate.
    + intros eff mo' evs [-> Hn]. rewrite Hfs in Hn. destruct Hn as [Hs ->].
      eexists. split; [|apply OUT; reflexivity]. rewrite strip_with_copyins, Hs. reflexivity.
    + intros eff mo' evs [_ Hn]. rewrite Hfs in Hn. destruct Hn as [_ ->]. auto.
    + exists (efferr ENOENT), mo, []. cbn [nstep]. rewrite Hfs. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma all_facts : forall n ms mo,
  match n with NExit _ | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ | NMremap _ _ _ => False | _ => True end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts segs ms mo n.
Proof.
  intros n ms mo Hne Hat Hminv Hh Hsafe. destruct n; try contradiction.
  - apply writev_facts; assumption.
  - apply open_facts; assumption.
  - apply read_facts; assumption.
  - apply close_facts; assumption.
  - apply ioctl_facts; assumption.
  - apply set_tid_facts; assumption.
  - apply munmap_facts; assumption.
  - apply openw_facts; assumption.
  - apply ioctlf_facts; assumption.
  - apply writevf_facts; assumption.
  - apply lseek_facts; assumption.
  - apply readv_facts; assumption.
  - apply unlink_facts; assumption.
Qed.

#[using="Type"] Lemma alloc_facts : forall n ms mo, alloc_node n = true ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts_ns segs ms mo n.
Proof.
  intros n ms mo Ha Hat Hminv Hh Hsafe. destruct n; try discriminate Ha.
  - apply brk_facts; assumption.
  - apply mmap_facts; assumption.
  - apply mprotect_facts; assumption.
  - apply mremap_facts; assumption.
Qed.

#[using="Type"] Lemma at_node_nonalloc_svc : forall n ms, alloc_node n = false -> at_node segs n ms ->
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

Lemma exit_node_facts : forall segs ms mo c,
  at_node segs (NExit c) ms -> m_halted mo = None ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
  /\ sstep segs (mkCfg ms mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg ms (with_halted (exit_code c) mo))).
Proof.
  intros segs ms mo c [Hsvc Ha0] Hh.
  assert (Hx : exists x8, ms_svc_pending ms = Some x8 /\ (x8 = Z_to_bv 64 93 \/ x8 = Z_to_bv 64 94)).
  { destruct Hsvc as [H|H]; eexists; (split; [exact H|]); auto. }
  destruct Hx as (x8 & Hsvc' & Hx8).
  apply (exit_kit segs ms mo x8 (exit_code c) Hsvc' Hh).
  intros o. unfold exit_code. rewrite <- Ha0, <- (in_a0_si segs ms x8).
  destruct Hx8 as [-> | ->].
  - rewrite (syscall_spec_93 _ _ _ (sysno_of segs ms _ 93 ltac:(lia) eq_refl)). apply exit_outcome.
  - rewrite (syscall_spec_94 _ _ _ (sysno_of segs ms _ 94 ltac:(lia) eq_refl)). apply exit_outcome.
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
  - exact (node_kit_ns segs ms mo n (alloc_facts segs n ms mo Ha Hat Hminv Hh Hsafe) Hh).
  - assert (Hne' : match n with NExit _ | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ | NMremap _ _ _ => False | _ => True end)
      by (destruct n; first [exact I | discriminate Ha | exact Hne]).
    destruct (node_kit segs ms mo n (all_facts segs n ms mo Hne' Hat Hminv Hh Hsafe) Hh) as (Hc & Hs & Hp).
    destruct (at_node_nonalloc_svc segs n ms Ha Hat) as (x8 & Hsvc & Hnin).
    pose proof (transparent_nonalloc segs ms mo x8 Hsvc Hnin) as Ht.
    split; [intros evs X Hst; exact (Hc _ _ (sstep_of_cfg segs _ _ _ Hst))|]. split; [|exact Hp].
    intros eff mo' evs HP. destruct (Hs _ _ _ HP) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    apply Ht. exact H3.
Qed.

Theorem nodes_sound : forall segs, node_sound node segs ACFG (at_node segs) nstep nexit minv nsafe.
Proof.
  intros segs. constructor.
  -   exact minv_nolazy.
  -
    intros n ms Hat.
    assert (Hx : exists x8, ms_svc_pending ms = Some x8).
    { destruct n as [| | | | | |c| | | | | | | | | | |]; cbn [at_node] in Hat;
        first [ destruct Hat as [[H|H] _]; eexists; exact H
              | destruct Hat as [H _]; eexists; exact H
              | eexists; exact Hat ]. }
    destruct Hx as [x8 ->]. discriminate.
  -
    intros n ms mo evs X Hat Hh Hminv Hsafe Hst.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + destruct (exit_node_facts segs ms mo c Hat Hh) as [Hc _]. destruct (Hc _ _ (sstep_of_cfg segs _ _ _ Hst)) as [-> ->].
      right. eexists _, _. split; [reflexivity|]. split; [split; reflexivity| reflexivity].
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (Hc & _ & _). left. exact (Hc _ _ Hst).
  -
    intros n ms mo rsp mo' evs Hat Hh Hminv Hsafe HP.
    assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct HP]).
    destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & Hs & _). exact (Hs _ _ _ HP).
  -
    intros n ms mo code mo' Hat Hh Hminv Hsafe HX.
    destruct n as [| | | | | |c| | | | | | | | | | |]; try contradiction. cbn [nexit] in HX. destruct HX as [-> ->].
    rewrite m_halted_with_halted. split; [reflexivity|].
    destruct (proj1 Hat) as [Hsvc|Hsvc];
      (eapply (transparent_nonalloc_no segs ms mo _ _ Hsvc); [reflexivity| vm_compute; reflexivity|]);
      exact (proj2 (exit_node_facts segs ms mo c Hat Hh)).
  -
    intros n ms mo Hat Hh Hminv Hsafe.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. split; reflexivity.
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & _ & Hp). left. exact Hp.
Qed.
