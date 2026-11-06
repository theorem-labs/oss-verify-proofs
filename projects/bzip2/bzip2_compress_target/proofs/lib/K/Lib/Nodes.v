(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Export RelSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma copy_iovecs_aux_bytes_in : forall iovs (bufs : list (list byte)) mp a,
  bytes_in mp a (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63) iovs bufs ->
  copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros bufs mp a H HF; [reflexivity|].
  inversion HF as [|iov bs iovs' bufs' [Hl Hlen] HF' E1 E2]; subst.
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2. rewrite !length_le8 in H3.
  cbn [copy_iovecs_aux length]. unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
  rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
  cbn [snd] in Hl. subst l. rewrite unsigned_lit by lia.
  replace (2 ^ 63 <=? Z.of_nat (length bs)) with false by (symmetry; apply Z.leb_gt; lia).
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH _ _ _ H3 HF'). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iovs_access_okb_of : forall iovs (bufs : list (list byte)),
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63 /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs ->
  iovs_access_okb iovs = true.
Proof.
  intros iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
  unfold iovs_access_okb in *. cbn [forallb fst snd]. rewrite IH, andb_true_r.
  cbn [snd] in Hl. subst l. cbn [fst] in Hb. rewrite unsigned_lit by lia. apply access_okb_of_le; [lia| exact Hb].
Qed.

Lemma import_iovecs_bytes_in : forall iovs (bufs : list (list byte)) mp a,
  bytes_in mp a (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63 /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs ->
  (1 <= length iovs <= 1024)%nat ->
  a + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
  Z.of_nat (length (concat bufs)) <= MAX_RW_COUNT ->
  import_iovecs mp (wa a) (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
  intros iovs bufs mp a H HF Hn Ha Hmax. pose proof H as (Ha0 & _ & _).
  assert (HF' : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63) iovs bufs).
  { clear -HF. induction HF as [|x y l l' (H1 & H2 & _) _ IH]; constructor; auto. }
  pose proof (copy_iovecs_aux_bytes_in iovs bufs mp a H HF') as Hcopy.
  unfold import_iovecs. unfold bv_eqb. rewrite !unsigned_lit by lia.
  destruct (Z.eqb_spec (Z.of_nat (length iovs)) 1) as [E1|N1].
  - (* [comment removed for export] *)
    replace (negb (access_okb (wa a) 16)) with false
      by (symmetry; rewrite (access_okb_of_le (wa a) 16); [reflexivity|lia|]; rewrite wa_unsigned by (unfold TASK_SIZE in *; lia); lia).
    destruct iovs as [|[b l] [|? ?]]; try (cbn in E1; lia).
    inversion HF as [|iov bs iovs' bufs' (Hl & Hlen & Hb) HF2 E2 E3]; subst.
    cbn [copy_iovecs_aux length] in Hcopy.
    destruct (read_iovec_entry mp (wa a)) as [b' l'| |] eqn:Er; try discriminate.
    cbn in Hcopy. injection Hcopy as <- <-.
    cbn [fst snd] in Hl, Hb |- *. subst. rewrite unsigned_lit by lia.
    inversion HF2; subst. cbn [concat] in Hmax. rewrite app_nil_r in Hmax.
    rewrite Z.min_l by lia.
    match goal with |- context [access_okb ?bb _] =>
      rewrite (access_okb_of_le bb (Z.of_nat (length bs))); [reflexivity|lia|exact Hb]
    end.
  - replace (Z.of_nat (length iovs) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (IOV_MAX <? Z.of_nat (length iovs)) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    replace (negb (access_okb (wa a) (16 * Z.of_nat (length iovs)))) with false
      by (symmetry; rewrite (access_okb_of_le (wa a)); [reflexivity|lia|]; rewrite wa_unsigned by (unfold TASK_SIZE in *; lia); lia).
    rewrite word_to_nat_of_nat by lia. rewrite Hcopy. rewrite (iovs_access_okb_of iovs bufs HF). reflexivity.
Qed.

(* [comment removed for export] *)
Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
  snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

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
  exists w, read_bytes_aux (wview segs m) (wa a) k = Some w.
Proof.
  intros segs m a n k W Hk. destruct W as (Ha & Hn & H). revert a n Ha Hn H Hk.
  induction k as [|k IH]; intros a n Ha Hn H Hk; cbn [read_bytes_aux]; [eexists; reflexivity|].
  destruct (wview segs m (wa a)) eqn:E.
  2:{ exfalso. apply (H 0); [lia|]. rewrite Z.add_0_r. exact E. }
  rewrite wa_succ.
  destruct (IH (a + 1) (n - 1)) as [w Hw]; try lia.
  { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
  rewrite Hw. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive node : Type :=
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
(* [comment removed for export] *)
(* [comment removed for export] *)

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
      Z.of_nat (length (concat bufs)) <= MAX_RW_COUNT /\
      ms_rom ms = seg_rom segs /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 0x800000000000 /\   (* [comment removed for export] *)
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= 0x800000000000 /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      0 < count <= 0x7ffff000 /\             (* [comment removed for export] *)
      buf + count <= 0x800000000000 /\      (* [comment removed for export] *)
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
      areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
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
Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

(* [comment removed for export] *)
Definition strip (eff : resp) : resp :=
  mkEffectU (eff_ret eff) (eff_writes eff) (eff_zeros eff) (eff_unmaps eff) (eff_copies eff) [].

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWritev fd bufs =>
      mo' = mo /\
      let bs := concat bufs in
      (bs = [] /\ eff = eff0 (Z_to_bv 64 0) /\ evs = [])
      \/ (exists k, (1 <= k <= length bs)%nat /\
                    eff = eff0 (Z_to_bv 64 (Z.of_nat k)) /\
                    evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))
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
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>
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
  (forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileW p off)) /\
  (forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileA p off)) /\
  (forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileRW p off)) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
  (forall k s, fd_lookup (m_fds mo) k <> Some (FdSocket s)) /\
  (forall k i w, fd_lookup (m_fds mo) k <> Some (FdPipe i w)) /\
  (forall k rd wr, fd_lookup (m_fds mo) k <> Some (FdDevNull rd wr)) /\   (* [comment removed for export] *)
  (forall k, fd_lookup (m_fds mo) k <> Some FdUrandom) /\   (* [comment removed for export] *)
  m_vm_lazy mo = [] /\
  m_vm_materialized mo = [].

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
  else if mprotect_modeled_b prot then
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
    || (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n)
  else false.

(* [comment removed for export] *)
Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  negb (mmap_noreserve_b flags) &&   (* [comment removed for export] *)
  (if negb (mmap_off_aligned_b off) then mmap_pglen_ok_b len
   else if negb (mmap_anon_b flags) then false
   else if w_is0 len then mmap_plain_anon_b flags
   else if mmap_modeled_b prot flags off then true
   else if mmap_noaccess_b prot flags off then true
   else if mmap_fixed_noaccess_b prot flags off then      (* [comment removed for export] *)
     let nZ := page_round_up_Z (bv_unsigned len) in
     let n := Z_to_bv 64 nZ in
     if (two_pow_64 <=? bv_unsigned addr + nZ) then true
     else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
     else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
     else if negb (0 <? bv_unsigned addr) then false
     else (region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n)
          || region_free (vm_reserved h ++ vm_maps h) addr n
          || region_free (vm_reserved h) addr n
   else false).

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NOpen path => path_has_slash path = false /\ path_eqb path dotdot_path = false
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

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PerNode.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End PerNode.

Section PerNode2.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AT_FDCWD32_eq : fd32 (Z_to_bv 64 (-100)) = AT_FDCWD32.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_at_read_bytes_map : forall ms a n (len : word),
  wr_at segs (ms_mem ms) a n -> bv_unsigned len <= n ->
  exists w, read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 a) len = Some w.
Proof.
  intros ms a n len W Hlen. rewrite read_bytes_map_eq. unfold ms_writable_byte.
  pose proof (bv_unsigned_in_range 64 len).
  destruct (read_bytes_aux_wr_at segs (ms_mem ms) a n (word_to_nat len) W ltac:(unfold word_to_nat; lia)) as [w Hw].
  exists w. exact Hw.
Qed.

Lemma access_okb_wr : forall buf count,
  0 <= buf -> 0 < count -> buf + count <= TASK_SIZE ->
  access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true.
Proof.
  intros buf count Hb Hc Hbc. unfold TASK_SIZE in *. apply access_okb_of_le; rewrite ?unsigned_lit; unfold TASK_SIZE; lia.
Qed.

(* [comment removed for export] *)

End PerNode2.

Section PerNode3.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iovs_ok_of_at : forall ms iovs bufs,
  ms_rom ms = seg_rom segs ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 0x800000000000 /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
  Z.of_nat (length (concat bufs)) < 2^63 ->
  Forall2 (iov_ok (ms_read_byte ms)) iovs bufs /\
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63 /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs.
Proof.
  intros ms iovs bufs Hrom H. induction H as [|iov bs iovs bufs (Hl & Htop & Hb) _ IH]; intros Hlen; [split; constructor|].
  cbn [concat] in Hlen. rewrite length_app in Hlen.
  destruct IH as [IH1 IH2]; [lia|]. split; constructor.
  - split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
  - exact IH1.
  - split; [exact Hl|]. split; [lia| unfold TASK_SIZE; exact Htop].
  - exact IH2.
Qed.

(* [comment removed for export] *)

End PerNode3.

Section PerNode4.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End PerNode4.

(* [comment removed for export] *)
Ltac dispatch L :=
  rewrite L by reflexivity;
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

(* [comment removed for export] *)


Section PerNode5.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End PerNode5.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
