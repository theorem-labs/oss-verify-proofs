(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export RelSpec.
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

Lemma word_to_nat_of_nat : forall n, Z.of_nat n < 2^64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof. intros. unfold word_to_nat. rewrite unsigned_lit by lia. lia. Qed.

Lemma read_bytes_map_bytes_in : forall bs mp a,
  bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
  read_bytes_map mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = Some bs.
Proof.
  intros bs mp a H Hl. rewrite read_bytes_map_eq. rewrite word_to_nat_of_nat by exact Hl.
  apply read_bytes_aux_bytes_in, H.
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
Lemma copy_iovecs_aux_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) ->
  Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs ->
  copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros mp a H Hl; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2. rewrite !length_le8 in H3.
  apply Forall_cons_iff in Hl as [Hl1 Hl]. cbn [snd] in Hl1.
  cbn [copy_iovecs_aux length]. unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
  rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
  replace (2 ^ 63 <=? bv_unsigned l) with false by (symmetry; apply Z.leb_gt; lia).
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH _ _ H3 Hl). reflexivity.
Qed.

(* [comment removed for export] *)
Definition iovs_of (dsts : list (Z * Z)) : list (word * word) :=
  map (fun d => (Z_to_bv 64 (fst d), Z_to_bv 64 (snd d))) dsts.

Fixpoint dsts_total (dsts : list (Z * Z)) : Z :=
  match dsts with [] => 0 | (_, l) :: r => l + dsts_total r end.

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

Lemma read_bytes_map_wr_at : forall segs m a n (cnt : word),
  wr_at segs m a n -> bv_unsigned cnt <= n ->
  exists w, read_bytes_map (wview segs m) (wa a) cnt = Some w.
Proof.
  intros segs m a n cnt W Hc. rewrite read_bytes_map_eq.
  pose proof (read_bytes_aux_wr_at segs m a n (word_to_nat cnt) W) as H.
  unfold word_to_nat in *. pose proof (bv_unsigned_in_range 64 cnt).
  destruct (read_bytes_aux (wview segs m) (wa a) (Z.to_nat (bv_unsigned cnt))) as [w|]; [exists w; reflexivity|].
  exfalso. apply H; [lia|reflexivity].
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
(* [comment removed for export] *)
| NOpenW (path : list byte) (mode : Z)             (* [comment removed for export] *)
| NWritevF (fd : Z) (bufs : list (list byte))      (* [comment removed for export] *)
| NReadv (fd : Z) (dsts : list (Z * Z))            (* [comment removed for export] *)
| NUnlink (path : list byte) (rmdir : bool)        (* [comment removed for export] *)
| NMremap (old oldlen newlen : Z)                  (* [comment removed for export] *)
| NLseek (fd : Z) (off : Z) (whence : Z)           (* [comment removed for export] *)
(* [comment removed for export] *)
| NMmapNR (addr len : Z)                          (* [comment removed for export] *)
(* [comment removed for export] *)
| NPeek (addr : Z).                                (* [comment removed for export] *)

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
  | NMremap old oldlen newlen =>
      Some (pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 oldlen; Z_to_bv 64 newlen; Z_to_bv 64 MREMAP_MAYMOVE; Z_to_bv 64 0])
  | NMmapNR addr len =>
      Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 3; Z_to_bv 64 0x4032; Z_to_bv 64 (-1); Z_to_bv 64 0])
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition max_write : Z := 67108864.
Definition max_read : Z := 16777216.

(* [comment removed for export] *)
Definition peek_rsp (v : Z) : resp := mkEffectU (Z_to_bv 64 v) [] [] [] [] [].
Definition dec_peek (rsp : resp) : Z := bv_unsigned (eff_ret rsp).

Lemma dec_peek_rsp : forall v, 0 <= v < 256 -> dec_peek (peek_rsp v) = v.
Proof. intros v Hv. unfold dec_peek, peek_rsp. cbn [eff_ret]. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. Qed.

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
      1 <= Z.of_nat (length bs) <= rw_bytes_max /\   (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (1 <= length bufs <= 1024)%nat /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 /\   (* [comment removed for export] *)
      Z.of_nat (length (concat bufs)) <= max_write /\
      ms_rom ms = seg_rom segs /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\   (* [comment removed for export] *)
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      path_has_slash path = false /\ path_eqb path dotdot_path = false /\   (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      1 <= count <= max_read /\
      buf + count <= 2^47 /\
      wr_at segs (ms_mem ms) buf count
  | NClose fd =>
      ms_svc_pending ms = Some (Z_to_bv 64 57) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd
  | NIoctl fd req =>
      ms_svc_pending ms = Some (Z_to_bv 64 29) /\
      0 <= fd < 2^32 /\ req = 21523 /\
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
      Z.testbit flags 14 = false /\                  (* [comment removed for export] *)
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
      areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
      areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
  | NMunmap addr len =>
      ms_svc_pending ms = Some (Z_to_bv 64 215) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
  | NMprotect addr len prot =>
      ms_svc_pending ms = Some (Z_to_bv 64 226) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot
  | NOpenW path mode =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = wr_create_flags /\
      areg ms 13 = Z_to_bv 64 mode /\
      ~ In (Z_to_bv 8 0) path /\
      (path_has_slash path = false \/ path = devnull_path) /\   (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NWritevF fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (1 <= length bufs <= 1024)%nat /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 /\   (* [comment removed for export] *)
      1 <= Z.of_nat (length (concat bufs)) <= max_write /\
      ms_rom ms = seg_rom segs /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\   (* [comment removed for export] *)
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NLseek fd off whence =>
      ms_svc_pending ms = Some (Z_to_bv 64 62) /\
      3 <= fd < 2^32 /\ 0 <= whence <= 2 /\
      areg ms 10 = Z_to_bv 64 fd /\ areg ms 11 = Z_to_bv 64 off /\ areg ms 12 = Z_to_bv 64 whence
  | NUnlink path rmdir =>
      ms_svc_pending ms = Some (Z_to_bv 64 35) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      areg ms 12 = Z_to_bv 64 (if rmdir then AT_REMOVEDIR else 0) /\
      ~ In (Z_to_bv 8 0) path /\ path <> [] /\ path <> dot_path /\ path <> dotdot_path /\
      path_has_slash path = false /\ (length path <= NAME_MAX)%nat /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NReadv fd dsts =>
      ms_svc_pending ms = Some (Z_to_bv 64 65) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length dsts)) /\
      (2 <= length dsts <= 8)%nat /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length dsts) <= 2^47 /\
      match dsts with (_, l0) :: _ => 1 <= l0 | [] => False end /\
      dsts_total dsts <= MAX_RW_COUNT /\
      Forall (fun d => 0 <= snd d /\ fst d + snd d <= 2^47 /\ wr_at segs (ms_mem ms) (fst d) (snd d)) dsts /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes (iovs_of dsts))
  | NMremap old oldlen newlen =>
      ms_svc_pending ms = Some (Z_to_bv 64 216) /\
      areg ms 10 = Z_to_bv 64 old /\ areg ms 11 = Z_to_bv 64 oldlen /\
      areg ms 12 = Z_to_bv 64 newlen /\ areg ms 13 = Z_to_bv 64 MREMAP_MAYMOVE
  (* [comment removed for export] *)
  | NMmapNR _ _ => False
  (* [comment removed for export] *)
  | NPeek _ => False
  end.

(* [comment removed for export] *)
Definition peek_byte (ms : machine_state) (a : Z) : Z :=
  match mrd segs (ms_mem ms) (wa a) with Some b => bv_unsigned b | None => 0 end.

Definition npeek (n : node) : option (machine_state -> resp) :=
  match n with
  | NPeek a => Some (fun ms => peek_rsp (peek_byte ms a))
  | _ => None
  end.

#[using="Type"] Lemma peek_byte_range : forall ms a, 0 <= peek_byte ms a < 256.
Proof.
  intros ms a. unfold peek_byte. destruct (mrd segs (ms_mem ms) (wa a)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. lia.
Qed.

#[using="Type"] Lemma peek_byte_mrd : forall ms a b, mrd segs (ms_mem ms) (wa a) = Some b -> peek_byte ms a = bv_unsigned b.
Proof. intros ms a b H. unfold peek_byte. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma peek_byte_read1 : forall ms a b,
  ov_read_bytes segs (ms_mem ms) (wa a) 1 = Some [b] -> peek_byte ms a = bv_unsigned b.
Proof.
  intros ms a b H. rewrite ov_rdn, rdn_unfold in H. unfold peek_byte.
  destruct (mrd segs (ms_mem ms) (wa a)) as [b0|]; [|discriminate H]. cbn in H. injection H as ->. reflexivity.
Qed.

End AtNode.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma CFG_alloc_only : CFG = alloc_only_cfg false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition alloc_no (n : Z) : bool :=
  (Z.eqb 214 n || Z.eqb 216 n || Z.eqb 222 n || Z.eqb 226 n)%bool.

Lemma injected_family_off_CFG : forall i,
  injected_family_off CFG i = alloc_no (bv_unsigned (in_sysno i)).
Proof.
  intros i. unfold injected_family_off, injected_arm, alloc_no.
  generalize (bv_unsigned (in_sysno i)) as n. intros n.
  cbn [lookup_injected injected_table ia_no ia_family family_may_fail CFG negb
       sc_alloc sc_fs sc_fd sc_net sc_cred sc_intr].
  repeat match goal with
    |- context [Z.eqb ?a n] =>
      let a' := eval cbv in a in
      change (Z.eqb a n) with (Z.eqb a' n);
      destruct (Z.eqb_spec a' n) as [<-|?]; [reflexivity|]
  end.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refusal_b_ext : forall i1 i2 m r,
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 -> refusal_b i1 m r = refusal_b i2 m r.
Proof. intros i1 i2 m r Hs Ha. unfold refusal_b. rewrite Hs, Ha. reflexivity. Qed.

Lemma spurious_ext : forall i1 i2 m eff,
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 ->
  (forall o, syscall_spec i1 m o <-> syscall_spec i2 m o) ->
  spurious_refusal_cfg CFG i1 m eff <-> spurious_refusal_cfg CFG i2 m eff.
Proof.
  intros i1 i2 m eff Hs Ha Hsp. unfold spurious_refusal_cfg.
  rewrite !injected_family_off_CFG, Hs, (refusal_b_ext i1 i2 m _ Hs Ha).
  split; intros (H1 & H2 & eff' & m' & evs' & H3 & H4); (split; [exact H1|]; split; [exact H2|]);
    exists eff', m', evs'; (split; [apply Hsp; exact H3|]).
  - rewrite <- (refusal_b_ext i1 i2 m _ Hs Ha). exact H4.
  - rewrite (refusal_b_ext i1 i2 m _ Hs Ha). exact H4.
Qed.

Lemma refusal_decided_ext : forall i1 i2 m,
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 ->
  (forall o, syscall_spec i1 m o <-> syscall_spec i2 m o) ->
  refusal_decided CFG i1 m -> refusal_decided CFG i2 m.
Proof.
  intros i1 i2 m Hs Ha Hsp Hd Hoff. rewrite injected_family_off_CFG, <- Hs, <- injected_family_off_CFG in Hoff.
  destruct (Hd Hoff) as [(eff' & m' & evs' & H3 & H4) | Hall].
  - left. exists eff', m', evs'. split; [apply Hsp; exact H3|]. rewrite <- (refusal_b_ext i1 i2 m _ Hs Ha). exact H4.
  - right. intros eff' m' evs' H. rewrite <- (refusal_b_ext i1 i2 m _ Hs Ha). apply (Hall eff' m' evs'). apply Hsp. exact H.
Qed.

(* [comment removed for export] *)
Lemma admissible_exists : forall i m eff m' evs,
  refusal_decided CFG i m -> syscall_spec i m (Ok eff m' evs) ->
  exists eff1 m1 evs1, syscall_spec i m (Ok eff1 m1 evs1) /\ ~ spurious_refusal_cfg CFG i m eff1.
Proof.
  intros i m eff m' evs Hd Hsp.
  destruct (injected_family_off CFG i) eqn:Hoff.
  - destruct (Hd Hoff) as [(eff' & m1 & evs' & H3 & H4) | Hall].
    + exists eff', m1, evs'. split; [exact H3|]. apply spurious_refusal_not_refusal. exact H4.
    + exists eff, m', evs. split; [exact Hsp|]. intros (_ & _ & eff' & m1 & evs' & H3 & H4).
      rewrite (Hall _ _ _ H3) in H4. discriminate H4.
  - exists eff, m', evs. split; [exact Hsp|]. apply spurious_refusal_family_on. exact Hoff.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

(* [comment removed for export] *)
Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

(* [comment removed for export] *)
Definition wr_range (len k : nat) : Prop := (len = 0 /\ k = 0 \/ 1 <= k <= len)%nat.

Definition write_result (fd : Z) (bs : list byte) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  mo' = mo /\
  exists k, wr_range (length bs) k /\
    eff = eff0 (Z_to_bv 64 (Z.of_nat k)) /\
    evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k bs).

(* [comment removed for export] *)
Definition openw_result (mo : Model) (path : list byte) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd (FdFileW path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) path []) mo)).

(* [comment removed for export] *)
Definition lseek_result (mo : Model) (fd : Z) (mk : word -> FdEntry) (base : option word) (off : Z)
    (eff : resp) (mo' : Model) : Prop :=
  match base with
  | None => False
  | Some b =>
      match lseek_dest b (Z_to_bv 64 off) with
      | None => eff = efferr EINVAL /\ mo' = mo
      | Some r => eff = eff0 r /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (mk r)) mo
      end
  end.

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWrite fd bs => write_result fd bs mo eff mo' evs
  | NWritev fd bufs => write_result fd (concat bufs) mo eff mo' evs
  | NOpen path =>
      evs = [] /\
      if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => eff = efferr ENOENT /\ mo' = mo
           | _ => if path_eqb path dot_path then open_result mo FdDir eff mo'
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
      | Some (FdFileW _ _) => eff = efferr EBADF /\ mo' = mo
      | Some FdNull => eff = efferr EBADF /\ mo' = mo          (* [comment removed for export] *)
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
  | NIoctl fd req =>
      evs = [] /\ mo' = mo /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF
      | Some _ => eff = efferr ENOTTY
      end
  | NSetTid =>
      evs = [] /\ exists t, eff = eff0 t /\
      match m_tid mo with
      | Some t0 => t = t0 /\ mo' = mo
      | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
      end
  | NExit _ => False
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ | NMmapNR _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs)
                  /\ ~ spurious_refusal_cfg CFG i mo eff   (* [comment removed for export] *)
      | None => False
      end
  | NOpenW path _ =>
      evs = [] /\
      if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => eff = efferr ENOENT /\ mo' = mo
           | _ => if path_eqb path devnull_path then open_result mo FdNull eff mo'   (* [comment removed for export] *)
                  else if path_has_slash path then False   (* [comment removed for export] *)
                  else if write_dirref path mo then eff = efferr EISDIR /\ mo' = mo   (* [comment removed for export] *)
                  else openw_result mo path eff mo'
           end
  | NWritevF fd bufs =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | Some (FdFileW p off) =>
          match fs_lookup (m_fs mo) p with
          | Some data =>
              let bs := concat bufs in
              eff = eff0 (Z_to_bv 64 (Z.of_nat (length bs))) /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word bs)%bv))
                      (with_fs (fs_set (m_fs mo) p (file_write data off bs)) mo)
          | None => False
          end
      | Some FdNull =>      (* [comment removed for export] *)
          eff = eff0 (Z_to_bv 64 (Z.of_nat (length (concat bufs)))) /\ mo' = mo
      | _ => False
      end
  | NLseek fd off whence =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some (FdFile p cur) =>
          match fs_lookup (m_fs mo) p with
          | Some data => lseek_result mo fd (fun r => FdFile p r) (lseek_base (Z_to_bv 64 whence) cur (len_word data)) off eff mo'
          | None => False
          end
      | Some (FdFileW p cur) =>
          match fs_lookup (m_fs mo) p with
          | Some data => lseek_result mo fd (fun r => FdFileW p r) (lseek_base (Z_to_bv 64 whence) cur (len_word data)) off eff mo'
          | None => False
          end
      | Some FdNull => eff = eff0 (Z_to_bv 64 0) /\ mo' = mo     (* [comment removed for export] *)
      | Some _ => False
      end
  | NUnlink path rmdir =>
      evs = [] /\
      if path_has_slash path then False         (* [comment removed for export] *)
      else
      if fs_under (m_fs mo) path then False     (* [comment removed for export] *)
      else match fs_lookup (m_fs mo) path with
           | None => eff = efferr ENOENT /\ mo' = mo
           | Some _ =>
               if rmdir then eff = efferr ENOTDIR /\ mo' = mo
               else (exists e, In e unlinkat_errnos /\ eff = efferr e /\ mo' = mo)
                    \/ (fd_names_path (m_fds mo) path = false   (* [comment removed for export] *)
                        /\ eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fs (fs_remove (m_fs mo) path) mo)
           end
  | NReadv fd dsts =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some FdDir => eff = efferr EISDIR /\ mo' = mo
      | Some (FdFileW _ _) => eff = efferr EBADF /\ mo' = mo
      | Some FdNull => eff = efferr EBADF /\ mo' = mo          (* [comment removed for export] *)
      | Some (FdFile p off) =>
          match fs_lookup (m_fs mo) p with
          | None => False
          | Some data =>
              let bs := file_read data off (Z_to_bv 64 (iovs_total (iovs_of dsts))) in
              eff = mkEffect (len_word bs) (scatterw (iovs_of dsts) bs) [] /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
          end
      | Some _ => False
      end
  (* [comment removed for export] *)
  | NPeek _ => mo' = mo /\ evs = [] /\ exists v, 0 <= v < 256 /\ eff = peek_rsp v
  end.

Lemma nstep_peek : forall a mo eff mo' evs,
  nstep (NPeek a) mo eff mo' evs <-> mo' = mo /\ evs = [] /\ exists v, 0 <= v < 256 /\ eff = peek_rsp v.
Proof. intros. reflexivity. Qed.

Lemma nstep_dec_peek : forall a mo eff mo' evs,
  nstep (NPeek a) mo eff mo' evs ->
  mo' = mo /\ evs = [] /\ 0 <= dec_peek eff < 256 /\ eff = peek_rsp (dec_peek eff).
Proof.
  intros a mo eff mo' evs (-> & -> & v & Hv & ->). rewrite (dec_peek_rsp v Hv). repeat split; lia || reflexivity.
Qed.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

(* [comment removed for export] *)
Definition fd_ok (mo : Model) (k : word) (e : FdEntry) : Prop :=
  match e with
  | FdChannel c => bv_unsigned k < 3
  | FdFile p _ => fs_lookup (m_fs mo) p <> None
  | FdFileW p _ => fs_lookup (m_fs mo) p <> None
  | FdDir => True
  | FdDevNull rd wr => rd = false /\ wr = true   (* [comment removed for export] *)
  | _ => False
  end.

(* [comment removed for export] *)
Definition lazyfree (mo : Model) : Prop := m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

(* [comment removed for export] *)
Definition minv (mo : Model) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k e, fd_lookup (m_fds mo) k = Some e -> fd_ok mo k e) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
  lazyfree mo /\
  fs_noabs (m_fs mo).   (* [comment removed for export] *)

Lemma minv_lazyfree : forall mo, minv mo -> lazyfree mo.
Proof. intros mo (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma minv_noabs : forall mo, minv mo -> fs_noabs (m_fs mo).
Proof. intros mo (_ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma minv_devnull_absent : forall mo, minv mo ->
  fs_lookup (m_fs mo) devnull_path = None /\ fs_under (m_fs mo) devnull_path = false.
Proof.
  intros mo H. exact (fs_noabs_devnull _ (minv_noabs mo H)).
Qed.

Lemma minv_nolazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof. intros mo H. exact (proj1 (minv_lazyfree mo H)). Qed.

Lemma minv_nomaterialized : forall mo, minv mo -> m_vm_materialized mo = [].
Proof. intros mo H. exact (proj2 (minv_lazyfree mo H)). Qed.

Lemma minv_tid : forall mo t, minv mo -> m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE.
Proof. intros mo t (_ & _ & _ & _ & H & _). apply H. Qed.

Lemma minv_chan : forall mo k c, minv mo -> fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3.
Proof. intros mo k c (_ & _ & _ & H & _) Hk. exact (H _ _ Hk). Qed.

Lemma minv_file : forall mo k p off, minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None.
Proof. intros mo k p off (_ & _ & _ & H & _) Hk. exact (H _ _ Hk). Qed.

Lemma minv_filew : forall mo k p off, minv mo -> fd_lookup (m_fds mo) k = Some (FdFileW p off) -> fs_lookup (m_fs mo) p <> None.
Proof. intros mo k p off (_ & _ & _ & H & _) Hk. exact (H _ _ Hk). Qed.

(* [comment removed for export] *)
Lemma minv_not_urandom : forall mo k e, minv mo -> fd_lookup (m_fds mo) k = Some e -> e <> FdUrandom.
Proof. intros mo k e (_ & _ & _ & H & _) Hk ->. exact (H _ _ Hk). Qed.

Lemma minv_init : forall reserved brk mbase sp lim inp,
  fs_keys_relative (in_image_fs inp) ->    (* [comment removed for export] *)
  minv (init_model reserved brk mbase sp lim inp).
Proof.
  intros reserved brk mbase sp lim inp Hrel. unfold minv, fd_ok, lazyfree. rewrite m_fds_init_model, m_tid_init_model, m_fs_init_model.
  repeat split; try reflexivity; try (intros; discriminate); try (apply in_fs_noabs; exact Hrel).
  intros k e H. cbn [fd_lookup] in H.
  destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. inversion H. vm_compute. reflexivity. }
  destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. inversion H. vm_compute. reflexivity. }
  destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. inversion H. vm_compute. reflexivity. }
  discriminate.
Qed.

(* [comment removed for export] *)
Definition spec_live (i : SyscallInput) (mo : Model) : Prop :=
  (~ syscall_spec i mo Unmodeled) /\ (exists o, syscall_spec i mo o).

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ | NMmapNR _ _ =>
      match node_input n with
      | Some i => spec_live i mo
                  /\ refusal_decided CFG i mo   (* [comment removed for export] *)
      | None => False
      end
  (* [comment removed for export] *)
  | NWritevF fd bufs =>
      (exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off) /\
        fs_lookup (m_fs mo) p = Some data /\ bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max /\
        bv_unsigned off + Z.of_nat (length (concat bufs)) <= 2^63 - 1)
      \/ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdNull
  (* [comment removed for export] *)
  | NReadv fd dsts =>
      forall p off, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) ->
                    bv_unsigned off + dsts_total dsts <= 2^63 - 1
  (* [comment removed for export] *)
  | NLseek fd _ _ => fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> Some FdDir
  (* [comment removed for export] *)
  | NUnlink path rmdir =>
      fs_under (m_fs mo) path = false /\ (rmdir = false -> fd_names_path (m_fds mo) path = false)
  | _ => True
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_svc_inv : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep_cfg segs CFG (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\
                  ~ spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
                  X = SNext (mkCfg (nret ms eff) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\
                  ~ spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\
                  evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. eauto 6.
  - right; left. eexists _, _, _. eauto 8.
  - right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; right. auto.
Qed.

(* [comment removed for export] *)
Definition node_facts (nstep_n : Model -> resp -> Model -> list event -> Prop)
           (ms : machine_state) (mo : Model) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
     exists rsp, nret ms eff = nret ms rsp /\ nstep_n mo rsp mo' evs) /\
  (forall rsp mo' evs, nstep_n mo rsp mo' evs ->
     exists eff, nret ms eff = nret ms rsp /\ syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)) /\
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
  (forall rsp mo' evs, nstep_n mo rsp mo' evs -> m_halted mo' = None /\ minv mo') /\
  (exists rsp mo' evs, nstep_n mo rsp mo' evs).

(* [comment removed for export] *)
Definition node_facts_cfg (nstep_n : Model -> resp -> Model -> list event -> Prop)
           (ms : machine_state) (mo : Model) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
     ~ spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff ->
     exists rsp, nret ms eff = nret ms rsp /\ nstep_n mo rsp mo' evs) /\
  (forall rsp mo' evs, nstep_n mo rsp mo' evs ->
     exists eff, nret ms eff = nret ms rsp /\ syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)
                 /\ ~ spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff) /\
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_halted mo' = None) /\
  (forall rsp mo' evs, nstep_n mo rsp mo' evs -> m_halted mo' = None /\ minv mo') /\
  (exists rsp mo' evs, nstep_n mo rsp mo' evs).

(* [comment removed for export] *)
#[using="Type"] Lemma facts_lift : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo,
  node_facts P ms mo ->
  (forall x8, ms_svc_pending ms = Some x8 -> alloc_no (bv_unsigned x8) = false) ->
  node_facts_cfg P ms mo.
Proof.
  intros P ms mo (x8 & Hsvc & Hc & Hs & Hnu & Hpres & Hprog) Hfam.
  assert (Hon : forall eff, ~ spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff).
  { intros eff. apply spurious_refusal_family_on. rewrite injected_family_off_CFG, in_sysno_si. exact (Hfam x8 Hsvc). }
  exists x8. split; [exact Hsvc|]. split; [|split; [|split; [|split; [|split]]]].
  - intros eff mo' evs Hsp _. exact (Hc _ _ _ Hsp).
  - intros rsp mo' evs HP. destruct (Hs _ _ _ HP) as (eff & Heq & Hsp). exists eff. split; [exact Heq|]. split; [exact Hsp| apply Hon].
  - exact Hnu.
  - intros eff mo' evs Hsp. destruct (Hc _ _ _ Hsp) as (rsp & _ & HP). exact (proj1 (Hpres _ _ _ HP)).
  - exact Hpres.
  - exact Hprog.
Qed.

#[using="Type"] Lemma node_kit : forall ms mo (P : Model -> resp -> Model -> list event -> Prop),
  m_halted mo = None -> node_facts_cfg P ms mo ->
  (forall evs X, sstep_cfg segs CFG (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P mo eff mo' evs)
  /\ (forall eff mo' evs, P mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep_cfg segs CFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, P mo eff mo' evs).
Proof.
  intros ms mo P Hh (x8 & Hsvc & Hc & Hs & Hnu & Hnh & Hpres & Hprog). split; [|split; [|exact Hprog]].
  - intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
      as [(eff & mo' & mo'' & Hsp & Hns & Hh' & Hmat & ->)
         | [(eff & mo' & evs0 & Hsp & Hns & Hh' & Hmat & -> & ->)
         | [(eff & mo' & evs0 & code & Hsp & Hh' & -> & ->)
         | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
    + destruct (Hc _ _ _ Hsp Hns) as (rsp & Heq & HP).
      rewrite (materialize_model_accesses_no_lazy _ _ (minv_nolazy _ (proj2 (Hpres _ _ _ HP)))) in Hmat.
      injection Hmat as <-. exists rsp, mo'. rewrite Heq. auto.
    + exfalso. destruct (Hc _ _ _ Hsp Hns) as (rsp & _ & HP).
      rewrite (materialize_model_accesses_no_lazy _ _ (minv_nolazy _ (proj2 (Hpres _ _ _ HP)))) in Hmat. discriminate.
    + exfalso. pose proof (Hnh _ _ _ Hsp). congruence.
    + exfalso. pose proof (m_killed_of_m_halted_none _ (Hnh _ _ _ Hsp)). congruence.
    + exfalso. exact (Hnu Hsp).
  - intros rsp mo' evs HP. destruct (Hpres _ _ _ HP) as [Hh' Hminv']. split; [exact Hh'|]. split; [exact Hminv'|].
    destruct (Hs _ _ _ HP) as (eff & Heq & Hsp & Hns). rewrite <- Heq. unfold nret.
    eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact Hsp | exact Hns | exact Hh' |].
    apply materialize_model_accesses_no_lazy. exact (minv_nolazy _ Hminv').
Qed.

#[using="Type"] Lemma exit_kit : forall ms mo x8 code,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
     o = Ok (eff0 (Z_to_bv 64 0)) (with_halted code mo) []) ->
  (forall evs X, sstep_cfg segs CFG (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
  /\ sstep_cfg segs CFG (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
  intros ms mo x8 code Hsvc Hh Hchar. split.
  - intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
      as [(eff & mo' & mo'' & Hsp & _ & Hh' & Hmat & ->)
         | [(eff & mo' & evs0 & Hsp & _ & Hh' & Hmat & -> & ->)
         | [(eff & mo' & evs0 & code' & Hsp & Hh' & -> & ->)
         | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
    + exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). cbn in Hh'. discriminate.
    + exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). cbn in Hh'. discriminate.
    + apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & ->). cbn in Hh'. inversion Hh'; subst.
      split; reflexivity.
    + exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_killed_with_halted in Hk. discriminate.
    + exfalso. apply Hchar in Hsp. exact (Unmodeled_Ok _ _ _ Hsp).
  - change [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))]).
    eapply sstep_cfg_exit; [exact Hh|exact Hsvc| |reflexivity|apply m_killed_with_halted].
    apply Hchar. reflexivity.
Qed.

End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nret_with_copyins : forall ms ci eff, nret ms (with_copyins ci eff) = nret ms eff.
Proof. intros ms ci [r ws zs us cs ci0]. reflexivity. Qed.

Lemma nret_copyins_irrel : forall ms r ws zs us cs ci ci',
  nret ms (mkEffectU r ws zs us cs ci) = nret ms (mkEffectU r ws zs us cs ci').
Proof. reflexivity. Qed.

Section PerNode.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma facts_det_gen : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo x8 (e1 r1 : resp) mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok e1 mo1 evs0) ->
  nret ms e1 = nret ms r1 ->
  (forall eff mo' evs, P mo eff mo' evs <-> (eff = r1 /\ mo' = mo1 /\ evs = evs0)) ->
  m_halted mo1 = None -> minv mo1 ->
  node_facts segs P ms mo.
Proof.
  intros P ms mo x8 e1 r1 mo1 evs0 Hsvc Hh Hchar Hnr HP Hh1 Hminv1. exists x8. split; [exact Hsvc|].
  split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hsp. apply Hchar in Hsp. apply Ok_inj in Hsp as (-> & -> & ->).
    exists r1. split; [exact Hnr|]. apply HP. auto.
  - intros rsp mo' evs H. apply HP in H as (-> & -> & ->). exists e1.
    split; [exact Hnr|]. apply Hchar. reflexivity.
  - intros Hu. apply Hchar in Hu. exact (Unmodeled_Ok _ _ _ Hu).
  - intros rsp mo' evs H. apply HP in H as (-> & -> & ->). auto.
  - exists r1, mo1, evs0. apply HP. auto.
Qed.

#[using="Type"] Lemma facts_det : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo x8 r ci mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (with_copyins ci (eff0 r)) mo1 evs0) ->
  (forall eff mo' evs, P mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo1 /\ evs = evs0)) ->
  m_halted mo1 = None -> minv mo1 ->
  node_facts segs P ms mo.
Proof.
  intros P ms mo x8 r ci mo1 evs0 Hsvc Hh Hchar HP Hh1 Hminv1.
  eapply facts_det_gen; [exact Hsvc|exact Hh|exact Hchar|apply nret_with_copyins|exact HP|exact Hh1|exact Hminv1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma facts_det0 : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo x8 (e1 : resp) mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok e1 mo1 evs0) ->
  (forall eff mo' evs, P mo eff mo' evs <-> (eff = e1 /\ mo' = mo1 /\ evs = evs0)) ->
  m_halted mo1 = None -> minv mo1 ->
  node_facts segs P ms mo.
Proof.
  intros P ms mo x8 e1 mo1 evs0 Hsvc Hh Hchar HP Hh1 Hminv1.
  eapply facts_det_gen; [exact Hsvc|exact Hh|exact Hchar|reflexivity|exact HP|exact Hh1|exact Hminv1].
Qed.

Ltac sysno K :=
  rewrite in_sysno_si; change (bv_unsigned (Z_to_bv 64 K)) with K; reflexivity.

#[using="Type"] Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="Type"] Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma fd32_small : forall z, 0 <= z < 2^32 -> fd32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros. unfold fd32. apply abi_low32_small. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma std_chan : forall mo fd, minv mo -> (fd = 1 \/ fd = 2) ->
  fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd)) /\
  w_is0 (Z_to_bv 64 fd) = false.
Proof.
  intros mo fd (M0 & M1 & M2 & _) [-> | ->]; split; first [exact M1 | exact M2 | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_family_facts : forall ms mo x8 fd bs (cis : nat -> list (word * nat)),
  ms_svc_pending ms = Some x8 -> m_halted mo = None -> minv mo ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
     exists k, (1 <= k <= length bs)%nat /\
       o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (cis k)) mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))) ->
  (1 <= length bs)%nat ->
  node_facts segs (write_result fd bs) ms mo.
Proof.
  intros ms mo x8 fd bs cis Hsvc Hh Hminv Hchar Hlen. exists x8. split; [exact Hsvc|].
  unfold write_result, wr_range. split; [|split; [|split; [|split]]].
  - intros eff mo' evs Hsp. apply Hchar in Hsp as (k & Hk & Heq). apply Ok_inj in Heq as (-> & -> & ->).
    exists (eff0 (Z_to_bv 64 (Z.of_nat k))). split; [apply nret_copyins_irrel|]. split; [reflexivity|].
    exists k. split; [right; exact Hk| auto].
  - intros rsp mo' evs (-> & k & Hk & -> & ->). eexists. split; [|apply Hchar; exists k; split; [lia|reflexivity]].
    apply nret_copyins_irrel.
  - intros Hu. apply Hchar in Hu as (k & _ & Heq). discriminate Heq.
  - intros rsp mo' evs (-> & _). auto.
  - exists (eff0 (Z_to_bv 64 (Z.of_nat (length bs)))), mo, (map (WriteEv (Z_to_bv 64 fd)) (firstn (length bs) bs)).
    split; [reflexivity|]. exists (length bs). split; [right; lia| auto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_zero_facts : forall ms mo x8 fd ci,
  ms_svc_pending ms = Some x8 -> m_halted mo = None -> minv mo ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (with_copyins ci (eff0 (Z_to_bv 64 0))) mo []) ->
  node_facts segs (write_result fd []) ms mo.
Proof.
  intros ms mo x8 fd ci Hsvc Hh Hminv Hchar.
  eapply facts_det; [exact Hsvc|exact Hh|exact Hchar| |exact Hh|exact Hminv].
  intros eff mo' evs. unfold write_result, wr_range. cbn [length firstn map]. split.
  - intros (-> & k & Hk & -> & ->). destruct Hk as [[_ ->]|Hk]; [|lia]. auto.
  - intros (-> & -> & ->). split; [reflexivity|]. exists 0%nat. auto.
Qed.

#[using="Type"] Lemma write_facts : forall ms mo fd bs,
  at_node segs (NWrite fd bs) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NWrite fd bs)) ms mo.
Proof.
  intros ms mo fd bs (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Hrom & Hbs) Hminv Hh.
  unfold max_write, rw_bytes_max in Hlen.
  pose proof (bytes_at_in _ _ _ _ Hrom Hbs) as Hin.
  destruct (std_chan mo fd Hminv Hfd) as [Hlk Hw].
  apply (write_family_facts ms mo (Z_to_bv 64 64) fd bs (fun k => [(areg ms 11, k)]) Hsvc Hh Hminv); [|lia].
  intros o. rewrite syscall_spec_64 by (sysno 64). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
  rewrite (write_chan_outcome _ _ _ _ _ _ (Z_to_bv 64 fd) bs Hlk Hw).
  - reflexivity.
  - rewrite unsigned_lit by lia. unfold rw_bytes_max. lia.
  - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - rewrite in_mem_si. rewrite <- (wa_unsigned_id (areg ms 11)). apply read_bytes_map_bytes_in; [exact Hin|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma iovs_ok_of_at : forall ms iovs bufs,
  ms_rom ms = seg_rom segs ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  Z.of_nat (length (concat bufs)) < 2^64 ->
  Forall2 (iov_ok (ms_read_byte ms)) iovs bufs.
Proof.
  intros ms iovs bufs Hrom H. induction H as [|iov bs iovs bufs (Hl & _ & Hb) _ IH]; intros Hlen; [constructor|].
  cbn [concat] in Hlen. rewrite length_app in Hlen.
  constructor.
  - split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
  - apply IH. lia.
Qed.

#[using="Type"] Lemma iovs_range_of_at : forall ms (iovs : list (word * word)) bufs,
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  Forall (fun iov : word * word => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= 2^47) iovs.
Proof.
  intros ms iovs bufs H. induction H as [|iov bs iovs bufs (Hl & Hr & _) _ IH]; constructor; [|exact IH].
  rewrite Hl. pose proof (bv_unsigned_in_range 64 (fst iov)).
  rewrite unsigned_lit by lia. exact Hr.
Qed.

#[using="Type"] Lemma iovs_len_small : forall mp iovs bufs,
  Forall2 (iov_ok mp) iovs bufs -> Z.of_nat (length (concat bufs)) < 2^63 ->
  Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs.
Proof.
  intros mp iovs bufs H. induction H as [|iov bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros Ht; [constructor|].
  cbn [concat] in Ht. rewrite length_app in Ht. constructor.
  - rewrite Hl. rewrite unsigned_lit by lia. lia.
  - apply IH. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma import_iovecs_ok : forall mp (a : word) iovs,
  (1 <= length iovs <= 1024)%nat ->
  bv_unsigned a + 16 * Z.of_nat (length iovs) <= 2^47 ->
  bytes_in mp (bv_unsigned a) (iovec_bytes iovs) ->
  Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= 2^47) iovs ->
  import_iovecs mp a (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
  intros mp a iovs Hn Ha Hin Hr. unfold import_iovecs.
  pose proof (bv_unsigned_in_range 64 a) as Har. unfold bv_modulus in Har.
  assert (Hsm : Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs).
  { apply Forall_impl with (2 := Hr). intros [b l] H. cbn [fst snd] in *. pose proof (bv_unsigned_in_range 64 b). lia. }
  pose proof (copy_iovecs_aux_bytes_in iovs mp (bv_unsigned a) Hin Hsm) as Hcopy. rewrite wa_unsigned_id in Hcopy.
  assert (Hokb : iovs_access_okb iovs = true).
  { unfold iovs_access_okb. apply forallb_forall. intros [b l] HIn. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) Hr _ HIn) as H. cbn [fst snd] in H.
    pose proof (bv_unsigned_in_range 64 l). pose proof (bv_unsigned_in_range 64 b). unfold bv_modulus in *.
    unfold access_okb, TASK_SIZE. apply andb_true_intro; split; apply Z.leb_le; lia. }
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 1)) eqn:E1.
  - (* [comment removed for export] *)
    apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !unsigned_lit in E1 by lia.
    destruct iovs as [|[b l] [|? ?]]; cbn [length] in E1; try lia. clear E1.
    replace (negb (access_okb a 16)) with false
      by (symmetry; apply negb_false_iff; unfold access_okb, TASK_SIZE; cbn [length] in Ha; apply andb_true_intro; split; apply Z.leb_le; lia).
    cbn [length copy_iovecs_aux] in Hcopy.
    destruct (read_iovec_entry mp a) as [| |b' l']; try discriminate Hcopy. injection Hcopy as -> ->.
    apply Forall_cons_iff in Hr as [Hr _]. cbn [fst snd] in Hr.
    pose proof (bv_unsigned_in_range 64 l). pose proof (bv_unsigned_in_range 64 b). unfold bv_modulus in *.
    replace (negb (access_okb b (Z.min (bv_unsigned l) MAX_RW_COUNT))) with false; [reflexivity|].
    symmetry. apply negb_false_iff. unfold access_okb, TASK_SIZE, MAX_RW_COUNT. apply andb_true_intro; split; apply Z.leb_le; lia.
  - assert (E0 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
    rewrite E0. rewrite unsigned_lit by lia.
    replace (IOV_MAX <? Z.of_nat (length iovs))%Z with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    replace (negb (access_okb a (16 * Z.of_nat (length iovs)))) with false.
    2:{ symmetry. apply negb_false_iff. unfold access_okb, TASK_SIZE. apply andb_true_intro; split; apply Z.leb_le; lia. }
    rewrite word_to_nat_of_nat by lia. rewrite Hcopy, Hokb. reflexivity.
Qed.

#[using="Type"] Lemma writev_facts : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NWritev fd bufs)) ms mo.
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Harr & Htot & Hrom & iovs & Hiov & Hbufs) Hminv Hh.
  unfold max_write in Htot.
  pose proof (iovs_ok_of_at _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_range_of_at _ _ _ Hbufs) as Hrng.
  pose proof (Forall2_length Hbufs) as Hleq.
  destruct (std_chan mo fd Hminv Hfd) as [Hlk Hw].
  pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite Hcnt32, <- Hleq. apply import_iovecs_ok; [lia| rewrite Hleq; exact Harr | eapply bytes_at_in; eassumption | exact Hrng]. }
  change (nstep (NWritev fd bufs)) with (write_result fd (concat bufs)).
  destruct (concat bufs) as [|b0 bs0] eqn:Ebs.
  { (* [comment removed for export] *)
    apply (write_zero_facts ms mo (Z_to_bv 64 66) fd
             (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))) Hsvc Hh Hminv).
    intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
    rewrite (writev_chan_zero_outcome _ _ _ _ _ _ (Z_to_bv 64 fd) iovs Hlk Hw).
    - rewrite in_mem_si. reflexivity.
    - rewrite in_mem_si. exact Himp.
    - rewrite Htotal, ?Ebs. reflexivity. }
  assert (Hpos : (1 <= length (concat bufs))%nat) by (rewrite Ebs; cbn; lia).
  rewrite <- Ebs in *. clear Ebs b0 bs0.
  apply (write_family_facts ms mo (Z_to_bv 64 66) fd (concat bufs)
           (fun k => import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                     ++ iov_prefix_accesses iovs k) Hsvc Hh Hminv); [|lia].
  intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
  rewrite (writev_chan_outcome _ _ _ _ _ _ (Z_to_bv 64 fd) iovs (concat bufs) Hlk Hw).
  - rewrite in_mem_si. reflexivity.
  - rewrite in_mem_si. exact Himp.
  - rewrite Htotal. unfold MAX_RW_COUNT. lia.
  - rewrite in_mem_si. apply gather_iovecs_ok. exact Hok.
  - lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
#[using="Type"] Lemma minv_with_fds : forall mo fds,
  minv mo ->
  fd_lookup fds (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (forall k e, fd_lookup fds k = Some e -> fd_ok mo k e) ->
  minv (with_fds fds mo).
Proof.
  intros mo fds (M0 & M1 & M2 & MF & MT & ML & MA) H0 H1 H2 HF. unfold minv.
  rewrite m_fds_with_fds, m_tid_with_fds, m_fs_with_fds. change (lazyfree (with_fds fds mo)) with (lazyfree mo).
  change (fd_ok (with_fds fds mo)) with (fd_ok mo).
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact HF|]. split; [exact MT|]. split; [exact ML|exact MA].
Qed.

#[using="Type"] Lemma minv_open_insert : forall mo ent,
  minv mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  match ent with FdDir | FdNull => True | FdFile p _ | FdFileW p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
  intros mo ent Hminv Hfree Hent. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
  - intros H. inversion H; subst. destruct e as [ch|q o|q o|q o|q o| |sk|pid w|rd wr| ]; cbn [fd_ok]; cbn in Hent; try exact Hent; try (destruct Hent; fail).
    destruct rd; [destruct Hent|]. destruct wr; [split; reflexivity|destruct Hent].
  - intros H. exact (MF _ _ H).
Qed.

#[using="Type"] Lemma minv_update_file : forall mo k p off off',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros mo k p off off' Hminv Hk. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k').
  - intros H. inversion H; subst. cbn [fd_ok]. exact (MF _ _ Hk).
  - intros H. exact (MF _ _ H).
Qed.

#[using="Type"] Lemma minv_remove : forall mo fd, minv mo -> 3 <= fd < 2^32 ->
  minv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
  intros mo fd Hminv Hfd. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
  { intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_remove; rewrite ?Hne by lia; try assumption.
  intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate|].
  intros H. exact (MF _ _ H).
Qed.

#[using="Type"] Lemma minv_with_tid : forall mo t, minv mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minv (with_tid t mo).
Proof.
  intros mo t (M0 & M1 & M2 & MF & MT & ML & MA) Ht. unfold minv. rewrite m_fds_with_tid, m_tid_with_tid.
  change (lazyfree (with_tid t mo)) with (lazyfree mo). change (fd_ok (with_tid t mo)) with (fd_ok mo).
  change (m_fs (with_tid t mo)) with (m_fs mo).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MF|]. split; [|split; [exact ML|exact MA]].
  intros t' H. inversion H; subst. exact Ht.
Qed.

(* [comment removed for export] *)
Definition fd_ok_fs (fs : Fs.Fs) (k : word) (e : FdEntry) : Prop :=
  match e with
  | FdChannel c => bv_unsigned k < 3
  | FdFile p _ => fs_lookup fs p <> None
  | FdFileW p _ => fs_lookup fs p <> None
  | FdDir => True
  | FdDevNull rd wr => rd = false /\ wr = true
  | _ => False
  end.

#[using="Type"] Lemma fd_ok_fs_eq : forall mo k e, fd_ok mo k e = fd_ok_fs (m_fs mo) k e.
Proof. intros mo k e. destruct e; reflexivity. Qed.

#[using="Type"] Lemma minv_with_fds_fs : forall mo fds fs',
  minv mo ->
  fd_lookup fds (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (forall k e, fd_lookup fds k = Some e -> fd_ok_fs fs' k e) ->
  fs_noabs fs' ->
  minv (with_fds fds (with_fs fs' mo)).
Proof.
  intros mo fds fs' (M0 & M1 & M2 & MF & MT & ML & MA) H0 H1 H2 HF HA. unfold minv.
  rewrite m_fds_with_fds, m_tid_with_fds, m_tid_with_fs. change (lazyfree (with_fds fds (with_fs fs' mo))) with (lazyfree mo).
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [|split; [exact MT|split; [exact ML|]]].
  - intros k e Hk. rewrite fd_ok_fs_eq, m_fs_with_fds, m_fs_with_fs. exact (HF _ _ Hk).
  - rewrite m_fs_with_fds, m_fs_with_fs. exact HA.
Qed.

#[using="Type"] Lemma minv_with_fs : forall mo fs',
  minv mo ->
  (forall k e, fd_lookup (m_fds mo) k = Some e -> fd_ok_fs fs' k e) ->
  fs_noabs fs' ->
  minv (with_fs fs' mo).
Proof.
  intros mo fs' (M0 & M1 & M2 & MF & MT & ML & MA) HF HA. unfold minv.
  rewrite m_fds_with_fs, m_tid_with_fs. change (lazyfree (with_fs fs' mo)) with (lazyfree mo).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [exact MT|split; [exact ML|]]].
  - intros k e Hk. rewrite fd_ok_fs_eq, m_fs_with_fs. exact (HF _ _ Hk).
  - rewrite m_fs_with_fs. exact HA.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma minv_openw_insert : forall mo p,
  minv mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  path_has_slash p = false ->     (* [comment removed for export] *)
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) p []) mo)).
Proof.
  intros mo p Hminv Hfree Hnsl. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  apply minv_with_fds_fs; [exact Hminv| | | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  - intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. cbn [fd_ok_fs]. rewrite fs_lookup_set_same. discriminate.
    + intros H. pose proof (MF _ _ H) as HF. rewrite fd_ok_fs_eq in HF.
      destruct e; cbn [fd_ok_fs] in *; try exact HF; apply fs_lookup_set_not_none; exact HF.
  - apply fs_noabs_set; [exact MA| apply no_slash_not_absolute; exact Hnsl].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma minv_write_filew : forall mo k p off off' data',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFileW p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFileW p off')) (with_fs (fs_set (m_fs mo) p data') mo)).
Proof.
  intros mo k p off off' data' Hminv Hk. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  apply minv_with_fds_fs; [exact Hminv| | | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  - intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k').
    + intros H. inversion H; subst. cbn [fd_ok_fs]. rewrite fs_lookup_set_same. discriminate.
    + intros H. pose proof (MF _ _ H) as HF. rewrite fd_ok_fs_eq in HF.
      destruct e; cbn [fd_ok_fs] in *; try exact HF; apply fs_lookup_set_not_none; exact HF.
  - apply fs_noabs_set; [exact MA|]. apply (fs_noabs_key (m_fs mo)); [exact MA|]. exact (MF _ _ Hk).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma minv_update_filew : forall mo k p off off',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFileW p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFileW p off')) mo).
Proof.
  intros mo k p off off' Hminv Hk. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k').
  - intros H. inversion H; subst. cbn [fd_ok]. exact (MF _ _ Hk).
  - intros H. exact (MF _ _ H).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma minv_remove_path : forall mo p,
  minv mo -> fd_names_path (m_fds mo) p = false ->
  minv (with_fs (fs_remove (m_fs mo) p) mo).
Proof.
  intros mo p Hminv Hnames. pose proof Hminv as (M0 & M1 & M2 & MF & MT & ML & MA).
  apply minv_with_fs; [exact Hminv| |apply fs_noabs_remove; exact MA]. intros k e Hk. pose proof (MF _ _ Hk) as HF. rewrite fd_ok_fs_eq in HF.
  destruct e as [c|q off|q off|q off|q off| |sk|pid w|rd wr| ]; cbn [fd_ok_fs] in *; try exact HF;
    rewrite fs_lookup_remove_other; try exact HF;
    eapply (fd_names_path_false _ _ _ _ _ Hnames); eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma open_out_result : forall R mo ent o,
  open_out R mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) o <->
  exists eff mo', o = Ok (with_copyins R eff) mo' [] /\ open_result mo ent eff mo'.
Proof.
  intros R mo ent o. unfold open_out, open_result, efferr, eff0. split.
  - intros [(e & He & ->) | (Hfree & ->)].
    + eexists _, _. split; [reflexivity|]. left. exists e. auto.
    + eexists _, _. split; [reflexivity|]. right. auto.
  - intros (eff & mo' & -> & [(e & He & -> & ->) | (Hfree & -> & ->)]).
    + left. exists e. auto.
    + right. auto.
Qed.

#[using="Type"] Lemma open_facts : forall ms mo path,
  at_node segs (NOpen path) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NOpen path)) ms mo.
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hp) Hminv Hh.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  assert (Hmfl : modeled_open_flags (areg ms 12) = true).
  { unfold modeled_open_flags. rewrite Hfl. reflexivity. }
  assert (Hdir : fd32 (areg ms 10) = AT_FDCWD32) by (rewrite Ha0; reflexivity).
  set (i := sys_input segs ms (Z_to_bv 64 56)).
  assert (Hsp : forall o, syscall_spec i mo o <-> openat_spec (fd32 (areg ms 10)) (areg ms 11) (areg ms 12) i mo o).
  { intros o. unfold i. rewrite syscall_spec_56 by (sysno 56). rewrite in_a0_si, in_a1_si, in_a2_si. reflexivity. }
  assert (Hmem : in_mem i = ms_read_byte ms) by reflexivity.
  set (R := open_reads i (areg ms 11)).
  (* [comment removed for export] *)
  assert (Hcstr : read_cstr (in_mem i) (areg ms 11) =
                  if (path_max <=? length path)%nat then CstrTooLong else CstrOk path).
  { rewrite Hmem. unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
    destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
    - apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [Hin _]. exact Hin.
    - apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hin]. }
  (* [comment removed for export] *)
  assert (Hchar :
    (exists r mo1, (forall o, syscall_spec i mo o <-> o = Ok (with_copyins R (eff0 r)) mo1 []) /\
                   (forall eff mo' evs, nstep (NOpen path) mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo1 /\ evs = [])) /\
                   mo1 = mo)
    \/ (exists ent, (forall o, syscall_spec i mo o <-> exists eff mo', o = Ok (with_copyins R eff) mo' [] /\ open_result mo ent eff mo') /\
                    (forall eff mo' evs, nstep (NOpen path) mo eff mo' evs <-> (evs = [] /\ open_result mo ent eff mo')) /\
                    match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end)).
  { cbn [nstep]. destruct (path_max <=? length path)%nat eqn:Elong.
    - left. exists (errno_ret ENAMETOOLONG), mo. split; [|split; [unfold efferr; tauto|reflexivity]].
      intros o. rewrite Hsp. apply (openat_toolong_outcome _ _ _ _ _ Hmfl). exact Hcstr.
    - destruct path as [|c path'].
      + left. exists (errno_ret ENOENT), mo. split; [|split; [unfold efferr; tauto|reflexivity]].
        intros o. rewrite Hsp. apply (openat_empty_outcome _ _ _ _ _ Hmfl). exact Hcstr.
      + destruct (path_eqb (c :: path') dot_path) eqn:Edot.
        * right. exists FdDir. apply path_eqb_eq in Edot. split; [|split; [tauto|exact I]].
          intros o. rewrite Hsp, <- open_out_result. apply (openat_dot_outcome _ _ _ _ _ Hmfl Hdir Hfl). rewrite Hcstr, Edot. reflexivity.
        * assert (Hnd : c :: path' <> dot_path).
          { intros E. rewrite E, path_eqb_refl in Edot. discriminate. }
          destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Efs.
          -- right. exists (FdFile (c :: path') (Z_to_bv 64 0)). split; [|split; [tauto|rewrite Efs; discriminate]].
             intros o. rewrite Hsp, <- open_out_result.
             apply (openat_file_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path') d); [exact Hcstr|discriminate|exact Hnd|exact Hsl|exact Hdd|exact Efs].
          -- left. exists (errno_ret ENOENT), mo. split; [|split; [unfold efferr; tauto|reflexivity]].
             intros o. rewrite Hsp.
             apply (openat_absent_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path')); [exact Hcstr|discriminate|exact Hnd|exact Hsl|exact Hdd|exact Efs]. }
  destruct Hchar as [(r & mo1 & Hc & Hn & ->) | (ent & Hc & Hn & Hent)].
  - eapply facts_det; [exact Hsvc|exact Hh|exact Hc|exact Hn|exact Hh|exact Hminv].
  - exists (Z_to_bv 64 56). split; [exact Hsvc|]. fold i. split; [|split; [|split; [|split]]].
    + intros eff mo' evs H. apply Hc in H as (eff' & mo'' & Heq & Hor). apply Ok_inj in Heq as (-> & -> & ->).
      exists eff'. split; [apply nret_with_copyins|]. apply Hn. auto.
    + intros rsp mo' evs H. apply Hn in H as [-> Hor]. exists (with_copyins R rsp).
      split; [apply nret_with_copyins|]. apply Hc. eexists _, _. eauto.
    + intros Hu. apply Hc in Hu as (eff' & mo'' & Heq & _). discriminate Heq.
    + intros rsp mo' evs H. apply Hn in H as [-> [(e & _ & _ & ->) | (Hfree & _ & ->)]]; [auto|].
      split; [exact Hh|]. apply minv_open_insert; [exact Hminv|exact Hfree|]. destruct ent; try (destruct Hent; fail); auto.
    + exists (efferr ENOMEM), mo, []. apply Hn. split; [reflexivity|]. left. exists ENOMEM. split; [|auto].
      unfold openat_errnos. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma length_file_read_le : forall data off c, (length (file_read data off c) <= word_to_nat c)%nat.
Proof. intros. rewrite file_read_unguarded. apply firstn_le_length. Qed.

#[using="Type"] Lemma read_facts : forall ms mo fd buf count,
  at_node segs (NRead fd buf count) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NRead fd buf count)) ms mo.
Proof.
  intros ms mo fd buf count (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hbc & Hwr) Hminv Hh.
  unfold max_read in Hc.
  pose proof Hwr as (Hb0 & Hbn & _).
  set (i := sys_input segs ms (Z_to_bv 64 63)).
  assert (Hsp : forall o, syscall_spec i mo o <-> read_spec (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) i mo o).
  { intros o. unfold i. rewrite syscall_spec_63 by (sysno 63). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_small by lia. reflexivity. }
  assert (Hwm : in_wmem i = wview segs (ms_mem ms)) by reflexivity.
  assert (Hmap : forall c, 0 <= c <= count -> exists w, read_bytes_map (in_wmem i) (Z_to_bv 64 buf) (Z_to_bv 64 c) = Some w).
  { intros c Hcc. rewrite Hwm. change (Z_to_bv 64 buf) with (wa buf). apply (read_bytes_map_wr_at segs _ buf count); [exact Hwr|].
    rewrite unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  assert (Hacc : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { rewrite !unsigned_lit by lia. unfold access_okb, TASK_SIZE. rewrite unsigned_lit by lia.
    apply andb_true_intro; split; apply Z.leb_le; lia. }
  unfold i in *; clear i. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - pose proof (proj1 (proj2 (proj2 (proj2 Hminv))) _ _ Hlk) as Hok. destruct e as [ch|p off|p off|p off|p off| |sk|pid w|rd wr| ]; cbn [fd_ok] in Hok.
    + (* [comment removed for export] *) exfalso. rewrite unsigned_lit in Hok by lia. lia.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
      assert (Hcl : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
      { rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT; lia).
        apply Z_to_bv_bv_unsigned. }
      assert (Hlen : Z.of_nat (length bs) <= count).
      { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
        unfold word_to_nat in L. rewrite unsigned_lit in L by lia. lia. }
      destruct (Hmap (Z.of_nat (length bs)) ltac:(lia)) as [w Hw].
      eapply (facts_det0 _ ms mo (Z_to_bv 64 63) (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [])
                (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo) []);
        [exact Hsvc|exact Hh| | |exact Hh|eapply minv_update_file; eassumption].
      * intros o. rewrite Hsp.
        pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) (sys_input segs ms (Z_to_bv 64 63)) mo o p off data w Hlk Hacc Hfs) as RF.
        cbv zeta in RF. rewrite Hcl in RF. fold bs in RF. rewrite RF; [unfold eff0; reflexivity|].
        unfold len_word. exact Hw.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. tauto.
    + (* [comment removed for export] *)
      eapply (facts_det0 _ ms mo (Z_to_bv 64 63) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
      * intros o. rewrite Hsp. apply (read_filew_outcome _ _ _ _ _ _ p off Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      eapply (facts_det0 _ ms mo (Z_to_bv 64 63) (efferr EISDIR) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
      * intros o. rewrite Hsp. apply (read_dir_outcome _ _ _ _ _ _ Hlk Hacc).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      destruct Hok as [-> ->].
      eapply (facts_det0 _ ms mo (Z_to_bv 64 63) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
      * intros o. rewrite Hsp. apply (read_null_outcome _ _ _ _ _ _ Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
    + destruct Hok.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    eapply (facts_det0 _ ms mo (Z_to_bv 64 63) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    * intros o. rewrite Hsp. apply (read_badfd_outcome _ _ _ _ _ _ Hlk).
    * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma close_facts : forall ms mo fd,
  at_node segs (NClose fd) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NClose fd)) ms mo.
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
  set (i := sys_input segs ms (Z_to_bv 64 57)).
  assert (Hsp : forall o, syscall_spec i mo o <-> close_spec (Z_to_bv 64 fd) i mo o).
  { intros o. unfold i. rewrite syscall_spec_57 by (sysno 57). rewrite in_a0_si, Ha0.
    rewrite fd32_small by lia. reflexivity. }
  unfold i in *; clear i. cbn [nstep]. destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - eapply (facts_det0 _ ms mo (Z_to_bv 64 57) (eff0 (Z_to_bv 64 0)) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []);
      [exact Hsvc|exact Hh| | |exact Hh|apply minv_remove; assumption].
    + intros o. rewrite Hsp. apply (close_outcome _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
  - eapply (facts_det0 _ ms mo (Z_to_bv 64 57) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    + intros o. rewrite Hsp. apply (close_badfd_outcome _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ioctl_facts : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NIoctl fd req)) ms mo.
Proof.
  intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh.
  set (i := sys_input segs ms (Z_to_bv 64 29)).
  assert (Hsp : forall o, syscall_spec i mo o <-> ioctl_spec (Z_to_bv 64 fd) (Z_to_bv 64 req) i mo o).
  { intros o. unfold i. rewrite syscall_spec_29 by (sysno 29). rewrite in_a0_si, in_a1_si, Ha0, Ha1.
    rewrite fd32_small by lia. unfold cmd32. rewrite abi_low32_small by lia. reflexivity. }
  assert (Htty : tty_only_request (Z_to_bv 64 req) = true) by (subst req; reflexivity).
  assert (Hwz : bv_eqb (Z_to_bv 64 req) TIOCGWINSZ = true) by (subst req; reflexivity).   (* [comment removed for export] *)
  unfold i in *; clear i. cbn [nstep]. destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - eapply (facts_det0 _ ms mo (Z_to_bv 64 29) (efferr ENOTTY) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    + intros o. rewrite Hsp. apply (ioctl_any_outcome _ _ _ _ _ e Hlk Htty Hwz (minv_not_urandom _ _ _ Hminv Hlk)).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
  - eapply (facts_det0 _ ms mo (Z_to_bv 64 29) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    + intros o. rewrite Hsp. apply (ioctl_badfd_outcome _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma set_tid_facts : forall ms mo,
  at_node segs NSetTid ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep NSetTid) ms mo.
Proof.
  intros ms mo Hsvc Hminv Hh.
  set (i := sys_input segs ms (Z_to_bv 64 96)).
  assert (Hsp : forall o, syscall_spec i mo o <-> set_tid_address_spec i mo o).
  { intros o. unfold i. rewrite syscall_spec_96 by (sysno 96). reflexivity. }
  unfold i in *; clear i. cbn [nstep]. destruct (m_tid mo) as [t0|] eqn:Htid.
  - eapply (facts_det0 _ ms mo (Z_to_bv 64 96) (eff0 t0) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    + intros o. rewrite Hsp. apply (set_tid_known_outcome _ _ _ _ Htid).
    + intros eff mo' evs. cbn [nstep]. rewrite Htid. split.
      * intros (-> & t & -> & -> & ->). auto.
      * intros (-> & -> & ->). split; [reflexivity|]. exists t0. auto.
  - exists (Z_to_bv 64 96). split; [exact Hsvc|]. cbn [nstep]. rewrite Htid. split; [|split; [|split; [|split]]].
    + intros eff mo' evs H. apply Hsp, (set_tid_fresh_outcome _ _ _ Htid) in H as (t & Ht & Heq).
      apply Ok_inj in Heq as (-> & -> & ->). exists (eff0 t). split; [reflexivity|]. split; [reflexivity|]. exists t. auto.
    + intros rsp mo' evs (-> & t & -> & Ht & ->). exists (eff0 t). split; [reflexivity|].
      apply Hsp, (set_tid_fresh_outcome _ _ _ Htid). exists t. auto.
    + intros Hu. apply Hsp, (set_tid_fresh_outcome _ _ _ Htid) in Hu as (t & _ & Heq). discriminate Heq.
    + intros rsp mo' evs (-> & t & -> & Ht & ->). split; [exact Hh|]. apply minv_with_tid; assumption.
    + exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) mo), []. split; [reflexivity|]. exists (Z_to_bv 64 1).
      split; [reflexivity|]. split; [|reflexivity]. rewrite unsigned_lit by lia. unfold PID_MAX_ENVELOPE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
  m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.

#[using="Type"] Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> lazyfree mo' -> minv mo -> minv mo'.
Proof.
  intros mo mo' (Hf & Hs & _ & Ht & _) Hl (M0 & M1 & M2 & MF & MT & ML & MA). unfold minv.
  rewrite Hf, Ht. split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [exact MT|split; [exact Hl|rewrite Hs; exact MA]]].
  intros k e Hk. pose proof (MF k e Hk) as H. unfold fd_ok in *. rewrite Hs. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vm_forget_range_shape : forall lo hi m,
  vm_only m (vm_forget_range lo hi m) /\ (lazyfree m -> lazyfree (vm_forget_range lo hi m)).
Proof.
  intros lo hi m. unfold vm_only, lazyfree. split; [repeat split; reflexivity|].
  intros [H1 H2].
  change (m_vm_lazy (vm_forget_range lo hi m)) with (maps_subtract (m_vm_lazy m) lo hi).
  change (m_vm_materialized (vm_forget_range lo hi m)) with (List.filter (page_outside_range lo hi) (m_vm_materialized m)).
  rewrite H1, H2. split; reflexivity.
Qed.

#[using="Type"] Lemma with_vmmaps_shape : forall h m,
  vm_only m (with_vmmaps h m) /\ (lazyfree (with_vmmaps h m) <-> lazyfree m).
Proof. intros. unfold with_vmmaps, vm_only, lazyfree. repeat split; intros; try reflexivity; tauto. Qed.

#[using="Type"] Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5) (G1 & G2 & G3 & G4 & G5). unfold vm_only.
  rewrite G1, G2, G3, G4, G5. auto.
Qed.

#[using="Type"] Lemma vm_only_refl : forall a, vm_only a a.
Proof. intros. unfold vm_only. repeat split; reflexivity. Qed.

#[using="Type"] Lemma forget_vm_ranges_shape : forall rs m,
  vm_only m (forget_vm_ranges rs m) /\ (lazyfree m -> lazyfree (forget_vm_ranges rs m)).
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges].
  - split; [apply vm_only_refl| auto].
  - destruct (vm_forget_range_shape (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m) as [V1 L1].
    destruct (IH (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)) as [V2 L2].
    split; [exact (vm_only_trans _ _ _ V1 V2)|]. intros H. apply L2, L1, H.
Qed.

#[using="Type"] Lemma with_brk_next_shape : forall m req r,
  vm_only m (with_brk_next m req r) /\ (lazyfree m -> lazyfree (with_brk_next m req r)).
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  destruct (with_vmmaps_shape (brk_model_next (m_vmmaps m) req r) m) as [V1 L1].
  destruct (forget_vm_ranges_shape (brk_unmaps r (vm_brk (m_vmmaps m))) (with_vmmaps (brk_model_next (m_vmmaps m) req r) m)) as [V2 L2].
  split; [exact (vm_only_trans _ _ _ V1 V2)|]. intros H. apply L2. apply L1. exact H.
Qed.

#[using="Type"] Lemma with_mmap_backing_id : forall flags a n m,
  Z.land (bv_unsigned flags) MAP_NORESERVE = 0 -> with_mmap_backing flags a n m = m.
Proof.
  intros flags a n m H. unfold with_mmap_backing, mmap_noreserve_b. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_spurious_iff : forall req mo r evs0 mo1,
  syscall_spec (pure_input 214 [Z_to_bv 64 req]) mo
     (Ok (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] []) mo1 evs0) ->
  spurious_refusal_cfg CFG (pure_input 214 [Z_to_bv 64 req]) mo
     (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
  <-> (brk_refusal_b mo (Z_to_bv 64 req) r = true /\ brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true).
Proof.
  intros req mo r evs0 mo1 _. unfold spurious_refusal_cfg. rewrite injected_family_off_CFG.
  change (bv_unsigned (in_sysno (pure_input 214 [Z_to_bv 64 req]))) with 214.
  change (alloc_no 214) with true.
  assert (Hrb : forall r0, refusal_b (pure_input 214 [Z_to_bv 64 req]) mo r0 = brk_refusal_b mo (Z_to_bv 64 req) r0) by reflexivity.
  cbn [eff_ret]. rewrite Hrb. split.
  - intros (_ & Hr & eff' & m' & evs' & Hsp & Hnr). split; [exact Hr|].
    rewrite syscall_spec_214 in Hsp by reflexivity. cbn [in_arg in_args pure_input nth] in Hsp.
    apply brk_outcome in Hsp as (r' & Hok' & Heq). apply Ok_inj in Heq as (-> & _ & _). rewrite Hrb in Hnr. cbn [eff_ret] in Hnr.
    unfold brk_refusal_b in Hr, Hnr. cbv zeta in Hr, Hnr.
    apply andb_true_iff in Hr as [Hr Hrb']. apply andb_true_iff in Hr as [Hr Hne]. apply andb_true_iff in Hr as [Hq1 Hq2].
    rewrite Hq1, Hq2, Hne in Hnr. cbn [andb] in Hnr.
    unfold brk_r_ok in Hok' |- *. cbv zeta in Hok' |- *.
    apply negb_true_iff in Hq1. apply negb_true_iff in Hq2. rewrite Hq1, Hq2 in Hok' |- *. cbn [orb] in Hok' |- *.
    destruct (bv_unsigned (Z_to_bv 64 req) <? bv_unsigned (vm_brk (m_vmmaps mo))).
    + rewrite bv_eqb_refl. reflexivity.
    + rewrite Hnr, orb_false_r in Hok'. apply andb_true_iff in Hok' as [He Hg]. apply bv_eqb_eq in He. subst r'.
      rewrite bv_eqb_refl. cbn [orb andb]. exact Hg.
  - intros (Hr & Hgr). split; [reflexivity|]. split; [exact Hr|].
    eexists _, _, _. split.
    + rewrite syscall_spec_214 by reflexivity. cbn [in_arg in_args pure_input nth]. apply brk_outcome.
      exists (Z_to_bv 64 req). split; [exact Hgr|reflexivity].
    + rewrite Hrb. cbn [eff_ret]. unfold brk_refusal_b in Hr |- *. cbv zeta in Hr |- *.
      apply andb_true_iff in Hr as [Hr _]. apply andb_true_iff in Hr as [_ Hne]. apply negb_true_iff in Hne.
      rewrite Hne, andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <->
  evs = [] /\ exists r, brk_r_ok mo (Z_to_bv 64 req) r = true /\
    eff = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [] /\
    mo' = with_brk_next mo (Z_to_bv 64 req) r /\
    (brk_refusal_b mo (Z_to_bv 64 req) r = true -> brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = false).
Proof.
  intros. cbn [nstep node_input]. split.
  - intros (-> & Hsp & Hns). split; [reflexivity|]. pose proof Hsp as Hsp0.
    rewrite syscall_spec_214 in Hsp by reflexivity. cbn [in_arg in_args pure_input nth] in Hsp.
    apply brk_outcome in Hsp as (r & Hr & Heq). apply Ok_inj in Heq as (-> & -> & _).
    exists r. split; [exact Hr|]. split; [reflexivity|]. split; [reflexivity|].
    intros Hrf. destruct (brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req)) eqn:E; [|reflexivity].
    exfalso. apply Hns. apply (brk_spurious_iff req mo r [] _ Hsp0). auto.
  - intros (-> & r & Hr & -> & -> & Hf). split; [reflexivity|].
    assert (Hsp : syscall_spec (pure_input 214 [Z_to_bv 64 req]) mo
              (Ok (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
                  (with_brk_next mo (Z_to_bv 64 req) r) [])).
    { rewrite syscall_spec_214 by reflexivity. cbn [in_arg in_args pure_input nth]. apply brk_outcome. exists r. auto. }
    split; [exact Hsp|]. intros Hs. apply (brk_spurious_iff req mo r [] _ Hsp) in Hs as [H1 H2]. rewrite (Hf H1) in H2. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mm_facts : forall ms mo n i x8 (spec : Sys SyscallEffect),
  node_input n = Some i ->
  (forall mo eff mo' evs, nstep n mo eff mo' evs <->
     (evs = [] /\ syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg CFG i mo eff)) ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None -> nsafe n mo ->
  in_sysno i = x8 -> in_arg i 0 = areg ms 10 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> spec (sys_input segs ms x8) mo o) ->
  (forall o, syscall_spec i mo o <-> spec i mo o) ->
  iirr spec ->
  (forall i0 eff mo' evs, spec i0 mo (Ok eff mo' evs) -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo')) ->
  node_facts_cfg segs (nstep n) ms mo.
Proof.
  intros ms mo n i x8 spec Hi Hn Hsvc Hminv Hh Hsafe Hno Ha0 Hc1 Hc2 Hirr Hshape.
  unfold nsafe in Hsafe. assert (HL : spec_live i mo /\ refusal_decided CFG i mo).
  { destruct n; cbn [node_input] in Hi; try discriminate; injection Hi as <-; exact Hsafe. }
  clear Hsafe. destruct HL as [[Hnu Hex] Hdec].
  assert (Heq : forall o, syscall_spec i mo o <-> syscall_spec (sys_input segs ms x8) mo o).
  { intros o. rewrite Hc1, Hc2. split; apply Hirr. }
  assert (Hsx : forall eff, spurious_refusal_cfg CFG i mo eff <-> spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff).
  { intros eff. apply spurious_ext; [rewrite in_sysno_si; exact Hno | rewrite in_a0_si; exact Ha0 | exact Heq]. }
  exists x8. split; [exact Hsvc|]. split; [|split; [|split; [|split; [|split]]]].
  - intros eff mo' evs Hsp Hns. exists eff. split; [reflexivity|]. apply Hn.
    split; [exact (proj1 (proj2 (Hshape _ _ _ _ (proj1 (Hc1 _) Hsp))))|]. split; [apply Heq; exact Hsp|].
    intros Hs. apply Hns. apply Hsx. exact Hs.
  - intros rsp mo' evs H. apply Hn in H as (-> & Hsp & Hns). exists rsp. split; [reflexivity|].
    split; [apply Heq; exact Hsp|]. intros Hs. apply Hns. apply Hsx. exact Hs.
  - intros Hu. apply Hnu. apply Heq. exact Hu.
  - intros eff mo' evs Hsp. destruct (Hshape _ _ _ _ (proj1 (Hc1 _) Hsp)) as (Hv & _ & _).
    destruct Hv as (_ & _ & -> & _). exact Hh.
  - intros rsp mo' evs H. apply Hn in H as (-> & Hsp & _). apply Hc2 in Hsp. destruct (Hshape _ _ _ _ Hsp) as (Hv & _ & Hl).
    split; [destruct Hv as (_ & _ & -> & _); exact Hh|]. eapply minv_vm_only; [exact Hv| apply Hl; apply minv_lazyfree; exact Hminv| exact Hminv].
  - destruct Hex as [[eff mo' evs|] Ho]; [|exfalso; exact (Hnu Ho)].
    destruct (admissible_exists i mo eff mo' evs Hdec Ho) as (eff1 & m1 & evs1 & Hsp1 & Hns1).
    exists eff1, m1, evs1. apply Hn. pose proof (Hshape _ _ _ _ (proj1 (Hc2 _) Hsp1)) as (_ & -> & _). auto.
Qed.

#[using="Type"] Lemma brk_shape : forall req i0 mo eff mo' evs,
  brk_spec req i0 mo (Ok eff mo' evs) -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo').
Proof.
  intros req i0 mo eff mo' evs H. apply brk_outcome in H as (r & Hr & Heq). apply Ok_inj in Heq as (-> & -> & ->).
  destruct (with_brk_next_shape mo req r) as [V L]. auto.
Qed.

#[using="Type"] Lemma brk_facts : forall ms mo req,
  at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo ->
  node_facts_cfg segs (nstep (NBrk req)) ms mo.
Proof.
  intros ms mo req (Hsvc & Ha0) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NBrk req) _ _ (brk_spec (Z_to_bv 64 req)));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | exact Hsafe | reflexivity | symmetry; exact Ha0 | | | | ].
  - intros o. rewrite syscall_spec_214 by (sysno 214). rewrite in_a0_si, Ha0. reflexivity.
  - intros o. rewrite syscall_spec_214 by reflexivity. reflexivity.
  - apply brk_spec_iirr.
  - intros i0 eff mo' evs. apply brk_shape.
Qed.

(* [comment removed for export] *)
Ltac shape_tac :=
  repeat first
  [ progress subst
  | match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : Ok _ _ _ = Ok _ _ _ |- _ => apply Ok_inj in H; destruct H as (? & ? & ?); subst
    | H : Ok _ _ _ = Unmodeled |- _ => exfalso; exact (Ok_Unmodeled _ _ _ H)
    | H : Unmodeled = Ok _ _ _ |- _ => exfalso; exact (Unmodeled_Ok _ _ _ H)
    | H : Some _ = Some _ |- _ => apply Some_inj' in H; subst
    | H : Some _ = None |- _ => exfalso; exact (Some_None _ H)
    | H : None = Some _ |- _ => exfalso; exact (None_Some _ H)
    | H : False |- _ => contradiction
    | H : _ \/ _ |- _ => destruct H
    | H : (if ?b then _ else _) _ _ _ |- _ => destruct b
    | H : (match ?x with _ => _ end) _ _ _ |- _ => destruct x
    | H : (match ?x with _ => _ end) |- _ => destruct x
    end
  | progress cbv beta zeta in * ].

(* [comment removed for export] *)
#[using="Type"] Lemma shape_same : forall mo, vm_only mo mo /\ ([] : list event) = [] /\ (lazyfree mo -> lazyfree mo).
Proof. intros. split; [apply vm_only_refl|auto]. Qed.

#[using="Type"] Lemma shape_vmmaps : forall mo h,
  vm_only mo (with_vmmaps h mo) /\ ([] : list event) = [] /\ (lazyfree mo -> lazyfree (with_vmmaps h mo)).
Proof. intros. destruct (with_vmmaps_shape h mo) as [V L]. split; [exact V|]. split; [reflexivity|]. apply L. Qed.

#[using="Type"] Lemma shape_forget_vmmaps : forall mo lo hi h,
  vm_only mo (vm_forget_range lo hi (with_vmmaps h mo)) /\ ([] : list event) = [] /\
  (lazyfree mo -> lazyfree (vm_forget_range lo hi (with_vmmaps h mo))).
Proof.
  intros. destruct (with_vmmaps_shape h mo) as [V1 L1]. destruct (vm_forget_range_shape lo hi (with_vmmaps h mo)) as [V2 L2].
  split; [exact (vm_only_trans _ _ _ V1 V2)|]. split; [reflexivity|]. intros E. apply L2. apply L1. exact E.
Qed.

#[using="Type"] Lemma testbit_unsigned_lit_low : forall z k, 0 <= k < 64 ->
  Z.testbit (bv_unsigned (Z_to_bv 64 z)) k = Z.testbit z k.
Proof. intros z k Hk. rewrite unsigned_lit_wrap. apply Z.mod_pow2_bits_low. lia. Qed.

#[using="Type"] Lemma noreserve_clear : forall flags, Z.testbit flags 14 = false ->
  Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE = 0.
Proof.
  intros flags H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  change MAP_NORESERVE with (2^14). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 14 k); [|apply andb_false_r]. subst k. rewrite testbit_unsigned_lit_low by lia. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma mmap_shape : forall a l p f d off i0 mo eff mo' evs,
  Z.land (bv_unsigned f) MAP_NORESERVE = 0 ->
  mmap_spec a l p f d off i0 mo (Ok eff mo' evs) -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo').
Proof.
  intros a l p f d off i0 mo eff mo' evs Hf H. unfold mmap_spec, with_mmap_replacement, with_mmap_destroyed in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r; rewrite ?(with_mmap_backing_id f) by exact Hf;
  first [ apply shape_same | apply shape_vmmaps | apply shape_forget_vmmaps ].
Qed.

#[using="Type"] Lemma mmap_facts : forall ms mo addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
  node_facts_cfg segs (nstep (NMmap addr len prot flags)) ms mo.
Proof.
  intros ms mo addr len prot flags (Hsvc & Hnr & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMmap addr len prot flags) _ _
            (mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | exact Hsafe | reflexivity | symmetry; exact Ha0 | | | | ].
  - intros o. rewrite syscall_spec_222 by (sysno 222).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
  - intros o. rewrite syscall_spec_222 by reflexivity. reflexivity.
  - apply mmap_spec_iirr.
  - intros i0 eff mo' evs. apply mmap_shape. apply noreserve_clear. exact Hnr.
Qed.

#[using="Type"] Lemma munmap_shape : forall a l i0 mo eff mo' evs,
  munmap_spec a l i0 mo (Ok eff mo' evs) -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo').
Proof.
  intros a l i0 mo eff mo' evs H. unfold munmap_spec in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r;
  first [ apply shape_same | apply shape_vmmaps | apply shape_forget_vmmaps ].
Qed.

#[using="Type"] Lemma munmap_facts : forall ms mo addr len,
  at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
  node_facts_cfg segs (nstep (NMunmap addr len)) ms mo.
Proof.
  intros ms mo addr len (Hsvc & Ha0 & Ha1) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMunmap addr len) _ _ (munmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len)));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | exact Hsafe | reflexivity | symmetry; exact Ha0 | | | | ].
  - intros o. rewrite syscall_spec_215 by (sysno 215). rewrite in_a0_si, in_a1_si, Ha0, Ha1. reflexivity.
  - intros o. rewrite syscall_spec_215 by reflexivity. reflexivity.
  - apply munmap_spec_iirr.
  - intros i0 eff mo' evs. apply munmap_shape.
Qed.

#[using="Type"] Lemma mprotect_shape : forall a l p i0 mo eff mo' evs,
  mprotect_spec a l p i0 mo (Ok eff mo' evs) -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo').
Proof.
  intros a l p i0 mo eff mo' evs H. unfold mprotect_spec, mprotect_model_next in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r;
  first [ apply shape_same | apply shape_vmmaps | apply shape_forget_vmmaps ].
Qed.

#[using="Type"] Lemma mprotect_facts : forall ms mo addr len prot,
  at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
  node_facts_cfg segs (nstep (NMprotect addr len prot)) ms mo.
Proof.
  intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMprotect addr len prot) _ _ (mprotect_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot)));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | exact Hsafe | reflexivity | symmetry; exact Ha0 | | | | ].
  - intros o. rewrite syscall_spec_226 by (sysno 226). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2. reflexivity.
  - intros o. rewrite syscall_spec_226 by reflexivity. reflexivity.
  - apply mprotect_spec_iirr.
  - intros i0 eff mo' evs. apply mprotect_shape.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shape_resize_vmmaps : forall mo o on d nn h,
  vm_only mo (vm_resize_backing (mremap_source_lazy_b mo o on) o on d nn (with_vmmaps h mo)) /\ ([] : list event) = [] /\
  (lazyfree mo -> lazyfree (vm_resize_backing (mremap_source_lazy_b mo o on) o on d nn (with_vmmaps h mo))).
Proof.
  intros mo o on d nn h. unfold vm_only, lazyfree. split; [repeat split; reflexivity|]. split; [reflexivity|].
  intros [H1 H2]. unfold mremap_source_lazy_b. rewrite H1. cbn [map_contains existsb].
  unfold vm_resize_backing. cbv zeta.
  change (m_vm_lazy (with_vmmaps h mo)) with (m_vm_lazy mo). change (m_vm_materialized (with_vmmaps h mo)) with (m_vm_materialized mo).
  rewrite H1, H2. split; reflexivity.
Qed.

#[using="Type"] Lemma mremap_shape : forall o os ns f i0 mo eff mo' evs,
  mremap_spec o os ns f i0 mo (Ok eff mo' evs) -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo').
Proof.
  intros o os ns f i0 mo eff mo' evs H. unfold mremap_spec, mremap_model_next in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r;
  first [ apply shape_same | apply shape_vmmaps | apply shape_forget_vmmaps | apply shape_resize_vmmaps ].
Qed.

#[using="Type"] Lemma mremap_facts : forall ms mo old oldlen newlen,
  at_node segs (NMremap old oldlen newlen) ms -> minv mo -> m_halted mo = None -> nsafe (NMremap old oldlen newlen) mo ->
  node_facts_cfg segs (nstep (NMremap old oldlen newlen)) ms mo.
Proof.
  intros ms mo old oldlen newlen (Hsvc & Ha0 & Ha1 & Ha2 & Ha3) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMremap old oldlen newlen) _ _
            (mremap_spec (Z_to_bv 64 old) (Z_to_bv 64 oldlen) (Z_to_bv 64 newlen) (Z_to_bv 64 MREMAP_MAYMOVE)));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | exact Hsafe | reflexivity | symmetry; exact Ha0 | | | | ].
  - intros o. rewrite syscall_spec_216 by (sysno 216). rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, Ha0, Ha1, Ha2, Ha3. reflexivity.
  - intros o. rewrite syscall_spec_216 by reflexivity. reflexivity.
  - apply mremap_spec_iirr.
  - intros i0 eff mo' evs. apply mremap_shape.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  match n with NMmap _ _ _ flags => Z.testbit flags 14 = false | NBrk _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end ->
  nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [] /\ (lazyfree mo -> lazyfree mo').
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction; cbn [nstep node_input] in H; destruct H as [_ [H _]].
  - rewrite syscall_spec_214 in H by reflexivity. eapply brk_shape. exact H.
  - rewrite syscall_spec_222 in H by reflexivity. eapply mmap_shape; [|exact H]. apply noreserve_clear. exact Hn.
  - rewrite syscall_spec_215 in H by reflexivity. eapply munmap_shape. exact H.
  - rewrite syscall_spec_226 in H by reflexivity. eapply mprotect_shape. exact H.
  - rewrite syscall_spec_216 in H by reflexivity. eapply mremap_shape. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fs : forall a l p f d off i0 mo eff mo' evs,
  mmap_spec a l p f d off i0 mo (Ok eff mo' evs) -> m_fs mo' = m_fs mo.
Proof.
  intros a l p f d off i0 mo eff mo' evs H. unfold mmap_spec, with_mmap_replacement, with_mmap_destroyed in H.
  sys_unfold. shape_tac; unfold with_mmap_backing; try destruct (mmap_noreserve_b f); reflexivity.
Qed.

#[using="Type"] Lemma nstep_mm_fs : forall n mo eff mo' evs,
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ | NMmapNR _ _ => True | _ => False end ->
  nstep n mo eff mo' evs -> m_fs mo' = m_fs mo.
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction; cbn [nstep node_input] in H; destruct H as [_ [H _]].
  - rewrite syscall_spec_214 in H by reflexivity. apply brk_shape in H. exact (proj1 (proj2 (proj1 H))).
  - rewrite syscall_spec_222 in H by reflexivity. eapply mmap_fs. exact H.
  - rewrite syscall_spec_215 in H by reflexivity. apply munmap_shape in H. exact (proj1 (proj2 (proj1 H))).
  - rewrite syscall_spec_226 in H by reflexivity. apply mprotect_shape in H. exact (proj1 (proj2 (proj1 H))).
  - rewrite syscall_spec_216 in H by reflexivity. apply mremap_shape in H. exact (proj1 (proj2 (proj1 H))).
  - rewrite syscall_spec_222 in H by reflexivity. eapply mmap_fs. exact H.
Qed.

(* [comment removed for export] *)
Definition sp_same (m m' : Model) : Prop := vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).

#[using="Type"] Lemma sp_same_refl : forall m, sp_same m m. Proof. reflexivity. Qed.
#[using="Type"] Lemma sp_same_trans : forall a b c, sp_same a b -> sp_same b c -> sp_same a c.
Proof. unfold sp_same. intros a b c H1 H2. congruence. Qed.

#[using="Type"] Lemma sp_same_forget_range : forall lo hi m, sp_same m (vm_forget_range lo hi m).
Proof. reflexivity. Qed.

#[using="Type"] Lemma sp_same_forget_ranges : forall rs m, sp_same m (forget_vm_ranges rs m).
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|].
  eapply sp_same_trans; [apply sp_same_forget_range| apply IH].
Qed.

#[using="Type"] Lemma sp_same_with_mmap_backing : forall f a n m, sp_same m (with_mmap_backing f a n m).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.

Ltac sp_tac :=
  unfold sp_same;
  repeat first
    [ reflexivity
    | rewrite sp_same_with_mmap_backing
    | match goal with
      | |- context [m_vmmaps (with_mmap_backing ?f ?a ?n ?m)] =>
          change (m_vmmaps (with_mmap_backing f a n m)) with (m_vmmaps m)
      end ].

#[using="Type"] Lemma brk_sp_same : forall req i0 mo eff mo' evs,
  brk_spec req i0 mo (Ok eff mo' evs) -> sp_same mo mo'.
Proof.
  intros req i0 mo eff mo' evs H. apply brk_outcome in H as (r & Hr & Heq). apply Ok_inj in Heq as (-> & -> & ->).
  unfold with_brk_next. cbv zeta. eapply sp_same_trans; [|apply sp_same_forget_ranges]. reflexivity.
Qed.

#[using="Type"] Lemma with_mmap_backing_vmmaps : forall f a n m, m_vmmaps (with_mmap_backing f a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.

#[using="Type"] Lemma mmap_sp_same : forall a l p f d off i0 mo eff mo' evs,
  mmap_spec a l p f d off i0 mo (Ok eff mo' evs) -> sp_same mo mo'.
Proof.
  intros a l p f d off i0 mo eff mo' evs H. unfold mmap_spec, with_mmap_replacement, with_mmap_destroyed in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r; unfold sp_same; rewrite ?with_mmap_backing_vmmaps; reflexivity.
Qed.

#[using="Type"] Lemma munmap_sp_same : forall a l i0 mo eff mo' evs,
  munmap_spec a l i0 mo (Ok eff mo' evs) -> sp_same mo mo'.
Proof.
  intros a l i0 mo eff mo' evs H. unfold munmap_spec in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r; reflexivity.
Qed.

#[using="Type"] Lemma mprotect_sp_same : forall a l p i0 mo eff mo' evs,
  mprotect_spec a l p i0 mo (Ok eff mo' evs) -> sp_same mo mo'.
Proof.
  intros a l p i0 mo eff mo' evs H. unfold mprotect_spec, mprotect_model_next in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r; reflexivity.
Qed.

#[using="Type"] Lemma mremap_sp_same : forall o os ns f i0 mo eff mo' evs,
  mremap_spec o os ns f i0 mo (Ok eff mo' evs) -> sp_same mo mo'.
Proof.
  intros o os ns f i0 mo eff mo' evs H. unfold mremap_spec, mremap_model_next in H.
  sys_unfold. shape_tac; rewrite ?app_nil_r; reflexivity.
Qed.

#[using="Type"] Lemma nstep_mm_sp_same : forall n mo eff mo' evs,
  match n with NMmap _ _ _ _ | NBrk _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end ->
  nstep n mo eff mo' evs -> sp_same mo mo'.
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction; cbn [nstep node_input] in H; destruct H as [_ [H _]].
  - rewrite syscall_spec_214 in H by reflexivity. eapply brk_sp_same. exact H.
  - rewrite syscall_spec_222 in H by reflexivity. eapply mmap_sp_same. exact H.
  - rewrite syscall_spec_215 in H by reflexivity. eapply munmap_sp_same. exact H.
  - rewrite syscall_spec_226 in H by reflexivity. eapply mprotect_sp_same. exact H.
  - rewrite syscall_spec_216 in H by reflexivity. eapply mremap_sp_same. exact H.
Qed.

#[using="Type"] Lemma sp_same_alloc_top : forall m m', sp_same m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof. intros m m' H. unfold alloc_top. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition node_static_ok (n : node) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.testbit flags 14 = false
  | NClose fd => 3 <= fd < 2^32
  | NMmapNR _ _ => False   (* [comment removed for export] *)
  | _ => True
  end.

#[using="Type"] Lemma at_node_static_ok : forall n ms, at_node segs n ms -> node_static_ok n.
Proof.
  intros n ms Hat. destruct n; cbn [at_node node_static_ok] in *; try exact I; try (exfalso; exact Hat).
  - exact (proj1 (proj2 Hat)).
  - exact (proj1 (proj2 Hat)).
Qed.

#[using="Type"] Lemma minv_preserved : forall n mo eff mo' evs,
  node_static_ok n ->
  minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hst Hminv Hh H.
  assert (Hor : forall ent, open_result mo ent eff mo' ->
            match ent with FdDir | FdNull => True | FdFile p _ | FdFileW p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            m_halted mo' = None /\ minv mo').
  { intros ent [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
    split; [exact Hh|]. apply minv_open_insert; assumption. }
  assert (Hmm : match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end ->
                m_halted mo' = None /\ minv mo').
  { intros Hn. destruct (nstep_mm_vm_only n mo eff mo' evs) as (Hv & _ & Hl); [destruct n; first [exact Hst|exact I|destruct Hn] | exact H |].
    split; [destruct Hv as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; [exact Hv| apply Hl; apply minv_lazyfree; exact Hminv | exact Hminv]]. }
  destruct n; cbn [nstep] in H; try (apply Hmm; exact I); try (exfalso; exact Hst).
  - destruct H as (-> & _); auto.
  - destruct H as (-> & _); auto.
  - destruct H as [_ H].
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
    destruct path as [|c path']. { destruct H as [_ ->]; auto. }
    destruct (path_eqb (c :: path') dot_path). { exact (Hor FdDir H I). }
    destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
    + apply (Hor _ H). cbn. congruence.
    + destruct H as [_ ->]; auto.
  - destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction;
      try (destruct H as [_ ->]; auto).
    destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
    split; [exact Hh|]. eapply minv_update_file; eassumption.
  - destruct H as (_ & Hfd & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
    split; [exact Hh|]. apply minv_remove; assumption.
  - destruct H as (_ & -> & _); auto.
  - destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; auto.
    split; [exact Hh|]. apply minv_with_tid; assumption.
  - destruct H.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
    destruct path as [|c path']. { destruct H as [_ ->]; auto. }
    destruct (path_eqb (c :: path') devnull_path). { exact (Hor FdNull H I). }
    destruct (path_has_slash (c :: path')) eqn:Hnsl. { destruct H. }
    destruct (write_dirref (c :: path') mo). { destruct H as [_ ->]; auto. }
    destruct H as [(e & _ & _ & ->) | (Hlk & _ & ->)]; [auto|].
    split; [exact Hh|]. apply minv_openw_insert; assumption.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction.
    + destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
      split; [exact Hh|]. eapply minv_write_filew; eassumption.
    + destruct H as [_ ->]; auto.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction;
      try (destruct H as [_ ->]; auto).
    destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
    split; [exact Hh|]. eapply minv_update_file; eassumption.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (path_has_slash path). { destruct H. }
    destruct (fs_under (m_fs mo) path). { destruct H. }
    destruct (fs_lookup (m_fs mo) path). 2:{ destruct H as [_ ->]; auto. }
    destruct rmdir. { destruct H as [_ ->]; auto. }
    destruct H as [(e & _ & _ & ->) | (Hnames & _ & ->)]; [auto|].
    split; [exact Hh|]. apply minv_remove_path; assumption.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p cur|p cur|p cur|p cur| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction;
      [ | | destruct H as [_ ->]; auto | destruct H as [_ ->]; auto].
    + destruct (fs_lookup (m_fs mo) p); [|contradiction]. unfold lseek_result in H.
      destruct (lseek_base _ _ _); [|contradiction]. destruct (lseek_dest _ _); destruct H as [_ ->]; [|auto].
      split; [exact Hh|]. eapply minv_update_file; eassumption.
    + destruct (fs_lookup (m_fs mo) p); [|contradiction]. unfold lseek_result in H.
      destruct (lseek_base _ _ _); [|contradiction]. destruct (lseek_dest _ _); destruct H as [_ ->]; [|auto].
      split; [exact Hh|]. eapply minv_update_filew; eassumption.
  - (* [comment removed for export] *) destruct H as (-> & _); auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_fs_under : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> forall p, fs_under (m_fs mo') p = fs_under (m_fs mo) p.
Proof.
  intros n mo eff mo' evs H p.
  assert (Hor : forall ent, open_result mo ent eff mo' -> fs_under (m_fs mo') p = fs_under (m_fs mo) p).
  { intros ent [(e & _ & _ & ->) | (_ & _ & ->)]; reflexivity. }
  assert (Hmm : match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ | NMmapNR _ _ => True | _ => False end ->
                fs_under (m_fs mo') p = fs_under (m_fs mo) p).
  { intros Hn. rewrite (nstep_mm_fs n mo eff mo' evs Hn H). reflexivity. }
  destruct n; cbn [nstep] in H; try (apply Hmm; exact I).
  - (* [comment removed for export] *) destruct H as (-> & _); reflexivity.
  - (* [comment removed for export] *) destruct H as (-> & _); reflexivity.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; reflexivity. }
    destruct path as [|c path']. { destruct H as [_ ->]; reflexivity. }
    destruct (path_eqb (c :: path') dot_path). { exact (Hor FdDir H). }
    destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
    + exact (Hor _ H).
    + destruct H as [_ ->]; reflexivity.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|q off|q off|q off|q off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction;
      try (destruct H as [_ ->]; reflexivity).
    destruct (fs_lookup (m_fs mo) q); [|contradiction]. destruct H as [_ ->]. reflexivity.
  - (* [comment removed for export] *) destruct H as (_ & _ & H). destruct (fd_lookup _ _); destruct H as [_ ->]; reflexivity.
  - (* [comment removed for export] *) destruct H as (_ & -> & _); reflexivity.
  - (* [comment removed for export] *) destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [_ ->]; reflexivity.
  - (* [comment removed for export] *) destruct H.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; reflexivity. }
    destruct path as [|c path']. { destruct H as [_ ->]; reflexivity. }
    destruct (path_eqb (c :: path') devnull_path). { exact (Hor FdNull H). }
    destruct (path_has_slash (c :: path')) eqn:Hnsl. { destruct H. }
    destruct (write_dirref (c :: path') mo). { destruct H as [_ ->]; reflexivity. }
    destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [reflexivity|].
    rewrite m_fs_with_fds, m_fs_with_fs. apply fs_under_set_no_slash. exact Hnsl.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|q off|q off|q off|q off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction.
    + destruct (fs_lookup (m_fs mo) q) eqn:Hfs; [|contradiction]. destruct H as [_ ->].
      rewrite m_fs_with_fds, m_fs_with_fs. apply fs_under_set_present. rewrite Hfs. discriminate.
    + destruct H as [_ ->]; reflexivity.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|q off|q off|q off|q off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction;
      try (destruct H as [_ ->]; reflexivity).
    destruct (fs_lookup (m_fs mo) q); [|contradiction]. destruct H as [_ ->]. reflexivity.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (path_has_slash path) eqn:Hnsl. { destruct H. }
    destruct (fs_under (m_fs mo) path). { destruct H. }
    destruct (fs_lookup (m_fs mo) path). 2:{ destruct H as [_ ->]; reflexivity. }
    destruct rmdir. { destruct H as [_ ->]; reflexivity. }
    destruct H as [(e & _ & _ & ->) | (_ & _ & ->)]; [reflexivity|].
    rewrite m_fs_with_fs. apply fs_under_remove_no_slash. exact Hnsl.
  - (* [comment removed for export] *) destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|q cur|q cur|q cur|q cur| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction;
      [ | | destruct H as [_ ->]; reflexivity | destruct H as [_ ->]; reflexivity].
    + destruct (fs_lookup (m_fs mo) q); [|contradiction]. unfold lseek_result in H.
      destruct (lseek_base _ _ _); [|contradiction]. destruct (lseek_dest _ _); destruct H as [_ ->]; reflexivity.
    + destruct (fs_lookup (m_fs mo) q); [|contradiction]. unfold lseek_result in H.
      destruct (lseek_base _ _ _); [|contradiction]. destruct (lseek_dest _ _); destruct H as [_ ->]; reflexivity.
  - (* [comment removed for export] *) destruct H as (-> & _); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma openw_facts : forall ms mo path mode,
  at_node segs (NOpenW path mode) ms -> minv mo -> m_halted mo = None ->
  node_facts segs (nstep (NOpenW path mode)) ms mo.
Proof.
  intros ms mo path mode (Hsvc & Ha0 & Hfl & Ha3 & Hnz & Hslash & Hrom & Hp) Hminv Hh.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  assert (Hmfl : modeled_open_flags (areg ms 12) = true) by (apply modeled_open_flags_wr; exact Hfl).
  assert (Hdir : fd32 (areg ms 10) = AT_FDCWD32) by (rewrite Ha0; reflexivity).
  set (i := sys_input segs ms (Z_to_bv 64 56)).
  assert (Hsp : forall o, syscall_spec i mo o <-> openat_spec (fd32 (areg ms 10)) (areg ms 11) (areg ms 12) i mo o).
  { intros o. unfold i. rewrite syscall_spec_56 by (sysno 56). rewrite in_a0_si, in_a1_si, in_a2_si. reflexivity. }
  assert (Hmem : in_mem i = ms_read_byte ms) by reflexivity.
  set (R := open_reads i (areg ms 11)).
  assert (Hcstr : read_cstr (in_mem i) (areg ms 11) =
                  if (path_max <=? length path)%nat then CstrTooLong else CstrOk path).
  { rewrite Hmem. unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
    destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
    - apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [Hin _]. exact Hin.
    - apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hin]. }
  (* [comment removed for export] *)
  assert (Hchar :
    (exists r, (forall o, syscall_spec i mo o <-> o = Ok (with_copyins R (eff0 r)) mo []) /\
               (forall eff mo' evs, nstep (NOpenW path mode) mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo /\ evs = [])))
    \/ (exists OR : resp -> Model -> Prop,
        (forall o, syscall_spec i mo o <-> exists eff mo', o = Ok (with_copyins R eff) mo' [] /\ OR eff mo') /\
        (forall eff mo' evs, nstep (NOpenW path mode) mo eff mo' evs <-> (evs = [] /\ OR eff mo')) /\
        (forall eff mo', OR eff mo' -> m_halted mo' = None /\ minv mo') /\
        OR (efferr ENOMEM) mo)).
  { cbn [nstep]. destruct (path_max <=? length path)%nat eqn:Elong.
    - left. exists (errno_ret ENAMETOOLONG). split; [|unfold efferr; tauto].
      intros o. rewrite Hsp. apply (openat_toolong_outcome _ _ _ _ _ Hmfl). exact Hcstr.
    - destruct path as [|c path'].
      + left. exists (errno_ret ENOENT). split; [|unfold efferr; tauto].
        intros o. rewrite Hsp. apply (openat_empty_outcome _ _ _ _ _ Hmfl). exact Hcstr.
      + destruct (path_eqb (c :: path') devnull_path) eqn:Edn.
        * (* [comment removed for export] *)
          apply path_eqb_eq in Edn. right. exists (open_result mo FdNull). split; [|split; [tauto|split]].
          -- intros o. rewrite Hsp, <- open_out_result.
             destruct (minv_devnull_absent mo Hminv) as [Hdl Hdu].
             apply (openat_devnull_outcome _ _ _ _ _ Hdir Hfl); [rewrite Hcstr, Edn; reflexivity|exact Hdl|exact Hdu].
          -- intros eff mo' [(e & _ & _ & ->) | (Hfree & _ & ->)]; [auto|].
             split; [exact Hh|]. apply minv_open_insert; [exact Hminv|exact Hfree|exact I].
          -- left. exists ENOMEM. split; [left; reflexivity|auto].
        * assert (Hsl : path_has_slash (c :: path') = false).
          { destruct Hslash as [Hs|Hs]; [exact Hs|]. rewrite Hs, path_eqb_refl in Edn. discriminate. }
          rewrite Hsl.
          destruct (write_dirref (c :: path') mo) eqn:Edir.
          -- left. exists (errno_ret EISDIR). split; [|unfold efferr; tauto].
             intros o. rewrite Hsp.
             apply (openat_create_dirref_outcome _ _ _ _ _ Hdir Hfl (c :: path')); [exact Hcstr|discriminate|exact Hsl|exact Edir].
          -- right. exists (openw_result mo (c :: path')). split; [|split; [tauto|split]].
             ++ intros o. rewrite Hsp. rewrite (openat_create_outcome _ _ _ _ _ Hdir Hfl (c :: path')); [|exact Hcstr|discriminate|exact Hsl|exact Edir].
                unfold open_out, openw_result, efferr, eff0. split.
                ** intros [(e & He & ->) | (Hfree & ->)]; eexists _, _; (split; [reflexivity|]); [left; exists e; auto| right; auto].
                ** intros (eff & mo' & -> & [(e & He & -> & ->) | (Hfree & -> & ->)]); [left; exists e; auto| right; auto].
             ++ intros eff mo' [(e & _ & _ & ->) | (Hfree & _ & ->)]; [auto|].
                split; [exact Hh|]. apply minv_openw_insert; [exact Hminv|exact Hfree|exact Hsl].
             ++ left. exists ENOMEM. split; [left; reflexivity|auto]. }
  destruct Hchar as [(r & Hc & Hn) | (OR & Hc & Hn & Hpres & Hprog)].
  - eapply facts_det; [exact Hsvc|exact Hh|exact Hc|exact Hn|exact Hh|exact Hminv].
  - exists (Z_to_bv 64 56). split; [exact Hsvc|]. fold i. split; [|split; [|split; [|split]]].
    + intros eff mo' evs H. apply Hc in H as (eff' & mo'' & Heq & Hor). apply Ok_inj in Heq as (-> & -> & ->).
      exists eff'. split; [apply nret_with_copyins|]. apply Hn. auto.
    + intros rsp mo' evs H. apply Hn in H as [-> Hor]. exists (with_copyins R rsp).
      split; [apply nret_with_copyins|]. apply Hc. eexists _, _. eauto.
    + intros Hu. apply Hc in Hu as (eff' & mo'' & Heq & _). discriminate Heq.
    + intros rsp mo' evs H. apply Hn in H as [-> Hor]. exact (Hpres _ _ Hor).
    + exists (efferr ENOMEM), mo, []. apply Hn. split; [reflexivity|exact Hprog].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma writevf_facts : forall ms mo fd bufs,
  at_node segs (NWritevF fd bufs) ms -> minv mo -> m_halted mo = None -> nsafe (NWritevF fd bufs) mo ->
  node_facts segs (nstep (NWritevF fd bufs)) ms mo.
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Harr & Htot & Hrom & iovs & Hiov & Hbufs) Hminv Hh Hsafe.
  unfold max_write in Htot.
  pose proof (iovs_ok_of_at _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_range_of_at _ _ _ Hbufs) as Hrng.
  pose proof (Forall2_length Hbufs) as Hleq.
  pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
  set (bs := concat bufs) in *.
  assert (Hlw : len_word bs = Z_to_bv 64 (Z.of_nat (length bs))) by reflexivity.
  assert (C1 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))) by (unfold iovcnt32; apply abi_low32_small; lia).
  assert (Himp : import_iovecs (in_mem (sys_input segs ms (Z_to_bv 64 66))) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite in_mem_si, C1, <- Hleq. apply import_iovecs_ok; [lia| rewrite Hleq; exact Harr | eapply bytes_at_in; eassumption | exact Hrng]. }
  assert (C5 : iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; subst bs; lia).
  destruct Hsafe as [(p & off & data & Hlk & Hfs & Hgap & Hpos) | Hlk].
  - (* [comment removed for export] *)
    eapply (facts_det_gen _ ms mo (Z_to_bv 64 66)
              (mkEffectU (len_word bs) [] [] [] []
                 (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                  ++ iov_prefix_accesses iovs (length bs)))
              (eff0 (Z_to_bv 64 (Z.of_nat (length bs))))
              (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word bs)%bv))
                 (with_fs (fs_set (m_fs mo) p (file_write data off bs)) mo)) []);
      [exact Hsvc|exact Hh| |reflexivity| |exact Hh|eapply minv_write_filew; eassumption].
    + intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
      rewrite fd32_small by lia.
      assert (C6 : gather_iovecs (in_mem (sys_input segs ms (Z_to_bv 64 66))) iovs = Some bs) by (rewrite in_mem_si; apply gather_iovecs_ok; exact Hok).
      assert (C7 : 1 <= Z.of_nat (length bs)) by (subst bs; lia).
      assert (C8 : bv_unsigned off + iovs_total iovs <= 2^63 - 1) by (rewrite Htotal; exact Hpos).
      pose proof (writev_file_outcome (Z_to_bv 64 fd) (areg ms 11) _ _ mo o p off data iovs bs Hlk Hfs Hgap Himp C5 C8 C6 C7) as W.
      cbv zeta in W. rewrite in_mem_si in W. exact W.
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. cbv zeta. fold bs. rewrite <- Hlw. unfold eff0. tauto.
  - (* [comment removed for export] *)
    eapply (facts_det_gen _ ms mo (Z_to_bv 64 66)
              (with_copyins (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))
                 (mkEffect (Z_to_bv 64 (iovs_total iovs)) [] []))
              (eff0 (Z_to_bv 64 (Z.of_nat (length bs))))
              mo []);
      [exact Hsvc|exact Hh| | | |exact Hh|exact Hminv].
    + intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
      rewrite fd32_small by lia.
      pose proof (writev_null_outcome (Z_to_bv 64 fd) (areg ms 11) _ _ mo o iovs Hlk Himp C5) as W.
      rewrite in_mem_si in W. exact W.
    + rewrite Htotal. reflexivity.
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. fold bs. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma lseek_facts : forall ms mo fd off whence,
  at_node segs (NLseek fd off whence) ms -> minv mo -> m_halted mo = None -> nsafe (NLseek fd off whence) mo ->
  node_facts segs (nstep (NLseek fd off whence)) ms mo.
Proof.
  intros ms mo fd off whence (Hsvc & Hfd & Hwh & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe. cbn [nsafe] in Hsafe.
  set (i := sys_input segs ms (Z_to_bv 64 62)).
  assert (Hsp : forall o, syscall_spec i mo o <-> lseek_spec (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) i mo o).
  { intros o. unfold i. rewrite syscall_spec_62 by (sysno 62). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_small by lia. unfold whence32. rewrite abi_low32_small by lia. reflexivity. }
  assert (Hbase : forall cur len, exists b, lseek_base (Z_to_bv 64 whence) cur len = Some b).
  { intros cur len. unfold lseek_base. rewrite unsigned_lit by lia. unfold SEEK_SET, SEEK_CUR, SEEK_END.
    destruct (Z.eqb_spec whence 0); [eexists; reflexivity|]. destruct (Z.eqb_spec whence 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec whence 2); [eexists; reflexivity|]. lia. }
  unfold i in *; clear i. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - pose proof (proj1 (proj2 (proj2 (proj2 Hminv))) _ _ Hlk) as Hok.
    destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid w|rd wr| ]; cbn [fd_ok] in Hok; try (destruct Hok; fail); try congruence.
    + exfalso. rewrite unsigned_lit in Hok by lia. lia.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      destruct (Hbase cur (len_word data)) as [b Hb].
      pose proof (fun o => lseek_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) (sys_input segs ms (Z_to_bv 64 62)) mo o p cur data b Hlk Hfs Hb) as Hout.
      unfold lseek_out in Hout.
      destruct (lseek_dest b (Z_to_bv 64 off)) as [r|] eqn:Hd.
      * eapply (facts_det0 _ ms mo (Z_to_bv 64 62) (eff0 r) (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p r)) mo) []);
          [exact Hsvc|exact Hh| | |exact Hh|eapply minv_update_file; eassumption].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold eff0. tauto.
      * eapply (facts_det0 _ ms mo (Z_to_bv 64 62) (efferr EINVAL) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold efferr, eff0. tauto.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      destruct (Hbase cur (len_word data)) as [b Hb].
      pose proof (fun o => lseek_filew_outcome (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) (sys_input segs ms (Z_to_bv 64 62)) mo o p cur data b Hlk Hfs Hb) as Hout.
      unfold lseek_out in Hout.
      destruct (lseek_dest b (Z_to_bv 64 off)) as [r|] eqn:Hd.
      * eapply (facts_det0 _ ms mo (Z_to_bv 64 62) (eff0 r) (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p r)) mo) []);
          [exact Hsvc|exact Hh| | |exact Hh|eapply minv_update_filew; eassumption].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold eff0. tauto.
      * eapply (facts_det0 _ ms mo (Z_to_bv 64 62) (efferr EINVAL) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold efferr, eff0. tauto.
    + (* [comment removed for export] *)
      destruct Hok as [-> ->].
      eapply (facts_det0 _ ms mo (Z_to_bv 64 62) (eff0 (Z_to_bv 64 0)) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
      * intros o. rewrite Hsp. apply (lseek_null_outcome _ _ _ _ _ _ Hlk). rewrite unsigned_lit by lia. unfold SEEK_MAX. lia.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold eff0. tauto.
  - (* [comment removed for export] *)
    eapply (facts_det0 _ ms mo (Z_to_bv 64 62) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    + intros o. rewrite Hsp. apply (lseek_badfd_outcome _ _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma unlinkat_errnos_range : forall e, In e unlinkat_errnos -> (1 <= e <= 4095).
Proof. intros e H. cbn in H. unfold ENOMEM, EACCES, EPERM, EROFS, EBUSY in H. lia. Qed.

#[using="Type"] Lemma unlink_facts : forall ms mo path rmdir,
  at_node segs (NUnlink path rmdir) ms -> minv mo -> m_halted mo = None -> nsafe (NUnlink path rmdir) mo ->
  node_facts segs (nstep (NUnlink path rmdir)) ms mo.
Proof.
  intros ms mo path rmdir (Hsvc & Ha0 & Ha2 & Hnz & Hne & Hnd & Hndd & Hsl & Hlen & Hrom & Hp) Hminv Hh Hsafe. cbn [nsafe] in Hsafe.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  set (i := sys_input segs ms (Z_to_bv 64 35)).
  assert (Hfl : modeled_unlink_flags (areg ms 12) = true).
  { rewrite Ha2. unfold modeled_unlink_flags, flag32. destruct rmdir; reflexivity. }
  assert (Hrm : unlink_rmdir (areg ms 12) = rmdir).
  { rewrite Ha2. unfold unlink_rmdir, flag32. destruct rmdir; reflexivity. }
  assert (Hdir : fd32 (areg ms 10) = AT_FDCWD32) by (rewrite Ha0; reflexivity).
  assert (Hcstr : read_cstr (in_mem i) (areg ms 11) = CstrOk path).
  { change (in_mem i) with (ms_read_byte ms). unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
    apply (read_cstr_aux_bytes_in path path_max); [unfold path_max; unfold NAME_MAX in Hlen; lia|exact Hnz|exact Hin]. }
  destruct Hsafe as [Hu Hnames].
  assert (Hsp : forall o, syscall_spec i mo o <-> unlink_out (unlink_reads i (areg ms 11)) mo path rmdir o).
  { intros o. unfold i. rewrite syscall_spec_35 by (sysno 35). rewrite in_a0_si, in_a1_si, in_a2_si. fold i. rewrite <- Hrm.
    apply (unlinkat_outcome _ _ _ i mo o path Hdir Hfl Hcstr Hne Hnd Hndd Hsl Hlen Hu). rewrite Hrm. exact Hnames. }
  set (R := unlink_reads i (areg ms 11)) in *.
  unfold unlink_out in Hsp. unfold i in *; clear i. cbn [nstep].
  destruct (fs_lookup (m_fs mo) path) as [d|] eqn:Hl.
  2:{ eapply (facts_det _ ms mo (Z_to_bv 64 35) (errno_ret ENOENT) R mo []); [exact Hsvc|exact Hh|exact Hsp| |exact Hh|exact Hminv].
      intros eff mo' evs. cbn [nstep]. rewrite Hsl, Hu, Hl. unfold efferr, eff0. tauto. }
  destruct rmdir.
  { eapply (facts_det _ ms mo (Z_to_bv 64 35) (errno_ret ENOTDIR) R mo []); [exact Hsvc|exact Hh|exact Hsp| |exact Hh|exact Hminv].
    intros eff mo' evs. cbn [nstep]. rewrite Hsl, Hu, Hl. unfold efferr, eff0. tauto. }
  specialize (Hnames eq_refl).
  exists (Z_to_bv 64 35). split; [exact Hsvc|]. split; [|split; [|split; [|split]]].
  - intros eff mo' evs H. apply Hsp in H as [(e & He & Heq) | Heq]; apply Ok_inj in Heq as (-> & -> & ->).
    + exists (efferr e). split; [apply nret_with_copyins|]. cbn [nstep]. rewrite Hsl, Hu, Hl. split; [reflexivity|]. left. exists e. auto.
    + exists (eff0 (Z_to_bv 64 0)). split; [apply nret_with_copyins|]. cbn [nstep]. rewrite Hsl, Hu, Hl. split; [reflexivity|]. right. auto.
  - intros rsp mo' evs H. cbn [nstep] in H. rewrite Hsl, Hu, Hl in H. destruct H as [-> [(e & He & -> & ->) | (_ & -> & ->)]].
    + exists (with_copyins R (efferr e)). split; [apply nret_with_copyins|]. apply Hsp. left. exists e. auto.
    + exists (with_copyins R (eff0 (Z_to_bv 64 0))). split; [apply nret_with_copyins|]. apply Hsp. right. reflexivity.
  - intros Hun. apply Hsp in Hun as [(e & _ & Heq) | Heq]; discriminate Heq.
  - intros rsp mo' evs H. cbn [nstep] in H. rewrite Hsl, Hu, Hl in H. destruct H as [-> [(e & _ & _ & ->) | (Hn & _ & ->)]]; [auto|].
    split; [exact Hh|]. apply minv_remove_path; assumption.
  - exists (eff0 (Z_to_bv 64 0)), (with_fs (fs_remove (m_fs mo) path) mo), []. cbn [nstep]. rewrite Hsl, Hu, Hl.
    split; [reflexivity|]. right. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma length_iovs_of : forall dsts, length (iovs_of dsts) = length dsts.
Proof. intros. unfold iovs_of. apply length_map. Qed.

#[using="Type"] Lemma iovs_total_of : forall dsts,
  Forall (fun d => 0 <= snd d < 2^64) dsts ->
  iovs_total (iovs_of dsts) = dsts_total dsts.
Proof.
  induction dsts as [|[b l] r IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [H1 Hr]. cbn [fst snd] in *.
  cbn [iovs_of map iovs_total dsts_total fst snd]. unfold iovs_of in IH. rewrite (IH Hr). rewrite unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma dsts_total_nonneg : forall dsts, Forall (fun d => 0 <= snd d) dsts -> 0 <= dsts_total dsts.
Proof.
  induction dsts as [|[b l] r IH]; intros H; cbn; [lia|].
  apply Forall_cons_iff in H as [H1 Hr]. cbn in H1. specialize (IH Hr). lia.
Qed.

#[using="Type"] Lemma readv_facts : forall ms mo fd dsts,
  at_node segs (NReadv fd dsts) ms -> minv mo -> m_halted mo = None -> nsafe (NReadv fd dsts) mo ->
  node_facts segs (nstep (NReadv fd dsts)) ms mo.
Proof.
  intros ms mo fd dsts (Hsvc & Hfd & Ha0 & Ha2 & Hn & Harr & Hfirst & Htot & Hdsts & Hrom & Hiov) Hminv Hh Hsafe.
  cbn [nsafe] in Hsafe.
  unfold MAX_RW_COUNT in Htot.
  pose proof (bytes_at_in _ _ _ _ Hrom Hiov) as Hin. pose proof (bv_unsigned_in_range 64 (areg ms 11)) as Ha11.
  set (iovs := iovs_of dsts) in *.
  assert (Hr3 : Forall (fun d => 0 <= snd d /\ fst d + snd d <= 2^47 /\ 0 <= fst d) dsts).
  { apply Forall_impl with (2 := Hdsts). intros [b l] (H1 & H2 & (H3 & _ & _)). cbn [fst snd] in *. lia. }
  pose proof (iovs_total_of dsts ltac:(apply Forall_impl with (2 := Hr3); intros [? ?] (? & ? & ?); cbn [fst snd] in *; lia)) as Htotal.
  fold iovs in Htotal.
  assert (Hposd : 1 <= dsts_total dsts).
  { destruct dsts as [|[b0 l0] r]; [destruct Hfirst|]. cbn. apply Forall_cons_iff in Hr3 as [_ Hr].
    pose proof (dsts_total_nonneg r ltac:(apply Forall_impl with (2 := Hr); intros [? ?] (? & ? & ?); assumption)). lia. }
  assert (Hleniovs : length iovs = length dsts) by (subst iovs; apply length_iovs_of).
  set (i := sys_input segs ms (Z_to_bv 64 65)).
  assert (Hsp : forall o, syscall_spec i mo o <-> readv_spec (Z_to_bv 64 fd) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts))) i mo o).
  { intros o. unfold i. rewrite syscall_spec_65 by (sysno 65). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
    rewrite fd32_small by lia. reflexivity. }
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length dsts))) = Z_to_bv 64 (Z.of_nat (length dsts))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  assert (Hcnt : bv_unsigned (Z_to_bv 64 (Z.of_nat (length dsts))) <= UIO_FASTIOV).
  { rewrite unsigned_lit by lia. unfold UIO_FASTIOV. lia. }
  assert (Himp : import_iovecs (in_mem i) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts))) = ImpOk iovs).
  { rewrite <- Hleniovs. apply import_iovecs_ok; [lia| lia | exact Hin |].
    subst iovs. unfold iovs_of. apply Forall_map. apply Forall_impl with (2 := Hr3).
    intros [b l] (H1 & H2 & H3). cbn [fst snd] in *. rewrite !unsigned_lit by lia. lia. }
  assert (Htotr : 1 <= iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; lia).
  assert (Hwm : in_wmem i = wview segs (ms_mem ms)) by reflexivity.
  assert (Hwr : Forall (iov_writable (in_wmem i)) iovs).
  { rewrite Hwm. subst iovs. unfold iovs_of. apply Forall_map. apply Forall_impl with (2 := Hdsts).
    intros [b l] (H1 & H2 & H3). cbn [fst snd] in H1, H2, H3. pose proof H3 as (Hb0 & _ & _). intros n Hnl. cbn [fst snd] in Hnl |- *.
    rewrite unsigned_lit in Hnl by lia.
    destruct (read_bytes_map_wr_at segs (ms_mem ms) b l (Z_to_bv 64 (Z.of_nat n)) H3 ltac:(rewrite unsigned_lit by lia; lia)) as [w Hw].
    change (Z_to_bv 64 b) with (wa b). rewrite Hw. discriminate. }
  unfold i in *; clear i. cbn [nstep]. fold iovs.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - pose proof (proj1 (proj2 (proj2 (proj2 Hminv))) _ _ Hlk) as Hok. destruct e as [ch|p off|p off|p off|p off| |sk|pid w|rd wr| ]; cbn [fd_ok] in Hok.
    + exfalso. rewrite unsigned_lit in Hok by lia. lia.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      cbv zeta. set (bs := file_read data off (Z_to_bv 64 (iovs_total iovs))).
      assert (Hpos : bv_unsigned off + iovs_total iovs <= 2^63 - 1) by (rewrite Htotal; exact (Hsafe p off eq_refl)).
      eapply (facts_det_gen _ ms mo (Z_to_bv 64 65)
                (mkEffectU (len_word bs) (scatterw iovs bs) [] [] [] (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts)))))
                (mkEffect (len_word bs) (scatterw iovs bs) [])
                (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo) []);
        [exact Hsvc|exact Hh| |reflexivity| |exact Hh|eapply minv_update_file; eassumption].
      * intros o. rewrite Hsp.
        pose proof (readv_file_outcome (Z_to_bv 64 fd) (areg ms 11) _ (sys_input segs ms (Z_to_bv 64 65)) mo o p off data iovs Hlk Hfs Hcnt32 Hcnt Himp Htotr Hpos Hwr) as W.
        cbv zeta in W. fold bs in W. rewrite in_mem_si in W. exact W.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. cbv zeta. fold iovs bs. tauto.
    + (* [comment removed for export] *)
      eapply (facts_det0 _ ms mo (Z_to_bv 64 65) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
      * intros o. rewrite Hsp. apply (readv_filew_outcome _ _ _ _ _ _ p off Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      eapply (facts_det_gen _ ms mo (Z_to_bv 64 65)
                (mkEffectU (errno_ret EISDIR) [] [] [] [] (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts)))))
                (efferr EISDIR) mo []);
        [exact Hsvc|exact Hh| |reflexivity| |exact Hh|exact Hminv].
      * intros o. rewrite Hsp.
        pose proof (readv_dir_outcome (Z_to_bv 64 fd) (areg ms 11) _ (sys_input segs ms (Z_to_bv 64 65)) mo o iovs Hlk Hcnt32 Hcnt Himp Htotr) as W.
        rewrite in_mem_si in W. exact W.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      destruct Hok as [-> ->].
      eapply (facts_det0 _ ms mo (Z_to_bv 64 65) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
      * intros o. rewrite Hsp. apply (readv_null_outcome _ _ _ _ _ _ Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
    + destruct Hok.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    eapply (facts_det0 _ ms mo (Z_to_bv 64 65) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv].
    * intros o. rewrite Hsp. apply (readv_badfd_outcome _ _ _ _ _ _ Hlk).
    * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lift_fam Hat :=
  intros x8 Hx; cbn [at_node] in Hat; rewrite (proj1 Hat) in Hx; injection Hx as <-; reflexivity.

#[using="Type"] Lemma all_facts : forall n ms mo,
  match n with NExit _ => False | _ => True end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts_cfg segs (nstep n) ms mo.
Proof.
  (* [comment removed for export] *)
  intros n ms mo Hne Hat Hminv Hh Hsafe. destruct n; try contradiction; try (cbn [at_node] in Hat; contradiction).
  - apply facts_lift; [apply write_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply writev_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply open_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply read_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply close_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply ioctl_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply set_tid_facts; assumption | intros x8 Hx; cbn [at_node] in Hat; rewrite Hat in Hx; injection Hx as <-; reflexivity].
  - apply brk_facts; assumption.
  - apply mmap_facts; assumption.
  - apply munmap_facts; assumption.
  - apply mprotect_facts; assumption.
  - apply facts_lift; [apply openw_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply writevf_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply readv_facts; assumption | lift_fam Hat].
  - apply facts_lift; [apply unlink_facts; assumption | lift_fam Hat].
  - apply mremap_facts; assumption.
  - apply facts_lift; [apply lseek_facts; assumption | lift_fam Hat].
Qed.

End PerNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

Lemma exit_node_facts : forall segs ms mo c,
  at_node segs (NExit c) ms -> m_halted mo = None ->
  (forall evs X, sstep_cfg segs CFG (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
  /\ sstep_cfg segs CFG (mkCfg ms mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg ms (with_halted (exit_code c) mo))).
Proof.
  intros segs ms mo c [Hsvc Ha0] Hh.
  assert (Hx : exists x8, ms_svc_pending ms = Some x8 /\ (bv_unsigned x8 = 93 \/ bv_unsigned x8 = 94)).
  { destruct Hsvc as [H|H]; eexists; (split; [exact H|]); [left|right]; reflexivity. }
  destruct Hx as (x8 & Hsvc' & Hno).
  apply (exit_kit segs ms mo x8 (exit_code c) Hsvc' Hh).
  intros o. unfold exit_code. rewrite <- Ha0, <- (in_a0_si segs ms x8).
  destruct Hno as [Hno|Hno];
    [rewrite syscall_spec_93 by (rewrite in_sysno_si; exact Hno) | rewrite syscall_spec_94 by (rewrite in_sysno_si; exact Hno)];
    apply exit_outcome.
Qed.

Lemma nonexit_node_facts : forall segs n ms mo,
  match n with NExit _ => False | _ => True end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
  (forall evs X, sstep_cfg segs CFG (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep_cfg segs CFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros segs n ms mo Hne Hat Hminv Hh Hsafe.
  exact (node_kit segs ms mo (nstep n) Hh (all_facts segs n ms mo Hne Hat Hminv Hh Hsafe)).
Qed.

Theorem nodes_sound : forall segs, node_sound node segs CFG (at_node segs) (npeek segs) nstep nexit minv nsafe.
Proof.
  intros segs. constructor.
  - (* [comment removed for export] *) exact minv_nolazy.
  - (* [comment removed for export] *)
    intros n ms Hat.
    assert (Hx : exists x8, ms_svc_pending ms = Some x8).
    { destruct n as [| | | | | | |c| | | | | | | | | | | |]; cbn [at_node] in Hat;
        first [ contradiction
              | destruct Hat as [[H|H] _]; eexists; exact H
              | destruct Hat as [H _]; eexists; exact H
              | eexists; exact Hat ]. }
    destruct Hx as [x8 ->]. discriminate.
  - (* [comment removed for export] *)
    intros n ms mo evs X Hat Hh Hminv Hsafe Hst.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + destruct (exit_node_facts segs ms mo c Hat Hh) as [Hc _]. destruct (Hc _ _ Hst) as [-> ->].
      right. eexists _, _. split; [reflexivity|]. split; [split; reflexivity| reflexivity].
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (Hc & _ & _). left. exact (Hc _ _ Hst).
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs Hat Hh Hminv Hsafe HP.
    assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct HP]).
    destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & Hs & _). exact (Hs _ _ _ HP).
  - (* [comment removed for export] *)
    intros n ms mo code mo' Hat Hh Hminv Hsafe HX.
    destruct n as [| | | | | | |c| | | | | | | | | | | |]; try contradiction. cbn [nexit] in HX. destruct HX as [-> ->].
    split; [reflexivity|]. exact (proj2 (exit_node_facts segs ms mo c Hat Hh)).
  - (* [comment removed for export] *)
    intros n ms mo Hat Hh Hminv Hsafe.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. split; reflexivity.
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & _ & Hp). left. exact Hp.
  - (* [comment removed for export] *)
    intros n f ms mo Hn. destruct n; cbn [npeek] in Hn; try discriminate Hn. injection Hn as <-.
    cbn [nstep]. split; [reflexivity|]. split; [reflexivity|]. exists (peek_byte segs ms addr).
    split; [apply peek_byte_range|reflexivity].
  - (* [comment removed for export] *)
    intros n f ms Hn Hat. destruct n; cbn [npeek] in Hn; try discriminate Hn. exact Hat.
Qed.
