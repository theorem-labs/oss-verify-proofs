(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export RunCeiling.
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

Lemma read_iovecs_aux_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) -> read_iovecs_aux mp (wa a) (length iovs) = Some iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros mp a H; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2. rewrite !length_le8 in H3.
  cbn [read_iovecs_aux length]. rewrite (read_u64_bytes_in _ _ _ H1).
  rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH _ _ H3). reflexivity.
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
| NMremap (old old_size new_size flags : Z).       (* [comment removed for export] *)

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
  | NMremap old osz nsz flags => Some (pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 osz; Z_to_bv 64 nsz; Z_to_bv 64 flags])
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtNode.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition writev_node_max : Z := 67108864.
Lemma writev_node_max_small : writev_node_max < 2^32. Proof. unfold writev_node_max. lia. Qed.
Lemma writev_node_max_big : writev_node_max <= MAX_RW_COUNT. Proof. unfold writev_node_max, MAX_RW_COUNT. lia. Qed.

Definition at_node (n : node) (ms : machine_state) : Prop :=
  match n with
  | NWrite fd bs =>
      ms_svc_pending ms = Some (Z_to_bv 64 64) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bs)) /\
      0 < Z.of_nat (length bs) <= rw_bytes_max /\
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (length bufs <= 1024)%nat /\
      Z.of_nat (length (concat bufs)) <= writev_node_max /\     (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE /\     (* [comment removed for export] *)
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs   (* [comment removed for export] *)
  | NOpen path =>
      ms_svc_pending ms = Some (Z_to_bv 64 56) /\
      areg ms 10 = Z_to_bv 64 (-100) /\
      Z.ldiff (bv_unsigned (areg ms 12)) (O_CLOEXEC + O_LARGEFILE) = 0 /\
      ~ In (Z_to_bv 8 0) path /\
      path_has_slash path = false /\          (* [comment removed for export] *)
      ms_rom ms = seg_rom segs /\
      bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
  | NRead fd buf count =>
      ms_svc_pending ms = Some (Z_to_bv 64 63) /\
      3 <= fd < 2^32 /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 11 = Z_to_bv 64 buf /\
      areg ms 12 = Z_to_bv 64 count /\
      0 < count <= 65536 /\ buf + count <= TASK_SIZE /\      (* [comment removed for export] *)
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
  | NMremap old osz nsz flags =>
      ms_svc_pending ms = Some (Z_to_bv 64 216) /\
      areg ms 10 = Z_to_bv 64 old /\ areg ms 11 = Z_to_bv 64 osz /\
      areg ms 12 = Z_to_bv 64 nsz /\ areg ms 13 = Z_to_bv 64 flags
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
Definition ceff (eff : resp) : resp :=
  mkEffectU (eff_ret eff) (eff_writes eff) (eff_zeros eff) (eff_unmaps eff) (eff_copies eff) [].
Definition with_ci (ci : list (word * nat)) (eff : resp) : resp :=
  mkEffectU (eff_ret eff) (eff_writes eff) (eff_zeros eff) (eff_unmaps eff) (eff_copies eff) ci.

Lemma nret_ceff : forall ms eff, nret ms (ceff eff) = nret ms eff.
Proof. intros ms [r ws zs us cs ci]; reflexivity. Qed.
Lemma nret_with_ci : forall ms ci eff, nret ms (with_ci ci eff) = nret ms eff.
Proof. intros ms ci [r ws zs us cs ci']; reflexivity. Qed.
Lemma ceff_with_ci : forall ci eff, ceff (with_ci ci eff) = ceff eff.
Proof. intros ci [r ws zs us cs ci']; reflexivity. Qed.
Lemma with_ci_ceff : forall eff, with_ci (eff_copyins eff) (ceff eff) = eff.
Proof. intros [r ws zs us cs ci]; reflexivity. Qed.
Lemma ceff_eff0 : forall r, ceff (eff0 r) = eff0 r.
Proof. reflexivity. Qed.
Lemma ceff_idem : forall eff, ceff (ceff eff) = ceff eff.
Proof. intros [r ws zs us cs ci]; reflexivity. Qed.
Lemma eff_ret_ceff : forall eff, eff_ret (ceff eff) = eff_ret eff.
Proof. intros [r ws zs us cs ci]; reflexivity. Qed.

(* [comment removed for export] *)
Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

(* [comment removed for export] *)
Definition chan_write (fd : Z) (bs : list byte) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  mo' = mo /\
  ((bs = [] /\ eff = eff0 (Z_to_bv 64 0) /\ evs = [])
   \/ (exists k, 1 <= k <= Z.of_nat (length bs) /\ eff = eff0 (Z_to_bv 64 k) /\
                 evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs))).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWrite fd bs => chan_write fd bs mo eff mo' evs
  | NWritev fd bufs => chan_write fd (concat bufs) mo eff mo' evs
  | NOpen path =>
      evs = [] /\
      if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
      else match path with
           | [] => eff = efferr ENOENT /\ mo' = mo
           | _ => if path_is_dirref path then open_result mo FdDir eff mo'
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
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ _ =>
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

Section RC__1.
Context {RC__ : RunCeiling}.

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
  m_vm_lazy mo = [] /\
  alloc_top (m_vmmaps mo) = alloc_ceiling.   (* [comment removed for export] *)

Lemma minv_lazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof. intros mo H. apply H. Qed.

Lemma minv_alloc_top : forall mo, minv mo -> alloc_top (m_vmmaps mo) = alloc_ceiling.
Proof. intros mo H. apply H. Qed.

Lemma minv_init : forall reserved brk mbase sp lim inp,
  bv_unsigned sp = rc_sp -> (sp_window_lo <= rc_sp <= sp_window_hi)%Z ->
  minv (init_model reserved brk mbase sp lim inp).
Proof.
  intros * Hsp Hv. unfold minv. rewrite m_fds_init_model, m_fs_init_model, m_tid_init_model.
  repeat split; try reflexivity; try (intros; discriminate).
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
  - rewrite m_vmmaps_init_model. apply alloc_ceiling_of_sp; [exact Hsp | exact Hv].
Qed.

(* [comment removed for export] *)
Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (TASK_SIZE <? bv_unsigned addr + nZ) then true     (* [comment removed for export] *)
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

Definition mmap_safe_b (addr len prot flags off : word) (h : VmMaps) : bool :=   (* [comment removed for export] *)
  if negb (mmap_off_aligned_b off) then mmap_pglen_ok_b len
  else if negb (mmap_anon_b flags) then false
  else if w_is0 len then mmap_plain_anon_b flags
  else if mmap_modeled_b prot flags off then true
  else if mmap_noaccess_b prot flags off then true
  else if mmap_fixed_noaccess_b prot flags off || mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ) then true
    else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
    else if negb (0 <? bv_unsigned addr) then false
    else
      let n := Z_to_bv 64 nZ in
      (region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n)
      || region_free (vm_reserved h ++ vm_maps h) addr n
      || region_free (vm_reserved h) addr n
  else false.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mremap_safe_b (old old_size new_size flags : word) (m : Model) : bool :=
  if negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE) then false
  else if negb (Z.eqb (bv_unsigned old mod page_size) 0) then true
  else if page_align_is0_b new_size then true
  else if page_align_is0_b old_size then false
  else
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let old_n := Z_to_bv 64 old_nZ in
    mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n.

Definition nsafe (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_noreserve_b (Z_to_bv 64 flags) = false /\
      mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                  (Z_to_bv 64 0) (m_vmmaps mo) = true
  | NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
  | NMprotect addr len prot =>
      mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
  | NMremap old osz nsz flags =>
      mremap_safe_b (Z_to_bv 64 old) (Z_to_bv 64 osz) (Z_to_bv 64 nsz) (Z_to_bv 64 flags) mo = true
  | _ => True
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End RC__1.

Ltac macc := autorewrite with model in *.

Lemma m_vm_lazy_with_fds : forall v m, m_vm_lazy (with_fds v m) = m_vm_lazy m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_lazy_with_tid : forall v m, m_vm_lazy (with_tid v m) = m_vm_lazy m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_lazy_with_halted : forall v m, m_vm_lazy (with_halted v m) = m_vm_lazy m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : forall v m, m_vm_lazy (with_vmmaps v m) = m_vm_lazy m.
Proof. intros v m; destruct m; reflexivity. Qed.
Lemma m_vm_lazy_with_stdin : forall v m, m_vm_lazy (with_stdin v m) = m_vm_lazy m.
Proof. intros v m; destruct m; reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_fds m_vm_lazy_with_tid m_vm_lazy_with_halted
  m_vm_lazy_with_vmmaps m_vm_lazy_with_stdin : model.

Section RC__2.
Context {RC__ : RunCeiling}.

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_svc_inv : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep segs (mkCfg ms mo) evs X ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_vm_lazy mo' = []) ->
  (exists eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\ m_halted mo' = None /\
                  X = SNext (mkCfg (nret ms eff) mo'))
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  m_killed mo' = None /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))      (* [comment removed for export] *)
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Hsvc Hst Hlz. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _. split; [eassumption|]. split; [assumption|].
    match goal with Hs : syscall_spec _ _ (Ok ?e ?m' _), Hm : materialize_model_accesses ?m' _ = Some ?m'' |- _ =>
      rewrite (materialize_model_accesses_no_lazy m' _ (Hlz _ _ _ Hs)) in Hm; inversion Hm; subst end.
    reflexivity.
  - exfalso.
    match goal with Hs : syscall_spec _ _ (Ok ?e ?m' _), Hm : materialize_model_accesses ?m' _ = None |- _ =>
      rewrite (materialize_model_accesses_no_lazy m' _ (Hlz _ _ _ Hs)) in Hm; discriminate Hm end.
  - right; left. eexists _, _, _, _. eauto 6.
  - right; right; left. eexists _, _, _, _. eauto.
  - right; right; right. auto.
Qed.

(* [comment removed for export] *)
Lemma node_kit : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs -> P (ceff eff) mo' evs) ->
  (forall eff mo' evs, P eff mo' evs -> exists ci, check_syscall (sys_input segs ms x8) (with_ci ci eff) mo = CheckOk mo' evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, P eff mo' evs -> m_halted mo' = None /\ m_vm_lazy mo' = []) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
  /\ (forall eff mo' evs, P eff mo' evs -> sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, P eff mo' evs).
Proof.
  intros ms mo x8 P Hsvc Hh Hcmp Hsnd Hnu Hhalt.
  assert (Hlz : forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_vm_lazy mo' = []).
  { intros eff mo' evs Hs. apply check_syscall_ok_iff in Hs. exact (proj2 (Hhalt _ _ _ (Hcmp _ _ _ Hs))). }
  split; [|split].
  - intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst Hlz)
      as [(eff & mo' & Hs & Hh' & ->) | [(eff & mo' & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & mo' & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]].
    + exists (ceff eff), mo'. rewrite nret_ceff. split; [reflexivity|]. apply Hcmp. apply check_syscall_ok_iff. exact Hs.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hcmp in Hs. apply Hhalt in Hs. destruct Hs; congruence.
    + exfalso. apply check_syscall_ok_iff in Hs. apply Hcmp in Hs. apply Hhalt in Hs. destruct Hs as [Hh0 _].
      rewrite (m_killed_of_m_halted_none _ Hh0) in Hk'. discriminate Hk'.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
  - intros eff mo' evs HP. destruct (Hsnd _ _ _ HP) as [ci Hc].
    rewrite <- (nret_with_ci ms ci eff). unfold nret.
    eapply sstep_syscall; [exact Hh|exact Hsvc| |exact (proj1 (Hhalt _ _ _ HP))|].
    + apply check_syscall_ok_iff. exact Hc.
    + apply materialize_model_accesses_no_lazy. exact (proj2 (Hhalt _ _ _ HP)).
  - pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    + exists (ceff eff), mo', evs. apply Hcmp. apply check_syscall_ok_iff. exact Hr.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
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
  - intros evs X Hst. inversion Hst; subst; try congruence;
      match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
    + exfalso. match goal with Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
        apply check_syscall_ok_iff in Hs; apply Hchar in Hs as (_ & -> & _) end.
      match goal with H : m_halted (with_halted _ _) = None |- _ => rewrite m_halted_with_halted in H; discriminate H end.
    + exfalso. match goal with Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
        apply check_syscall_ok_iff in Hs; apply Hchar in Hs as (_ & -> & _) end.
      match goal with H : m_halted (with_halted _ _) = None |- _ => rewrite m_halted_with_halted in H; discriminate H end.
    + match goal with Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
        apply check_syscall_ok_iff in Hs; apply Hchar in Hs as (_ & -> & ->) end.
      match goal with H : m_halted (with_halted _ _) = Some _ |- _ =>
        rewrite m_halted_with_halted in H; inversion H; subst end.
      rewrite m_fs_with_halted. split; reflexivity.
    + exfalso. match goal with Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
        apply check_syscall_ok_iff in Hs; apply Hchar in Hs as (_ & -> & _) end.
      match goal with H : m_killed (with_halted _ _) = Some _ |- _ => rewrite m_killed_with_halted in H; discriminate H end.
    + exfalso. match goal with Hs : syscall_spec _ _ Unmodeled |- _ =>
        apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs; exact (Hnu _ Hs) end.
  - replace [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))])
      by (rewrite m_fs_with_halted; reflexivity).
    eapply sstep_exit; [exact Hh|exact Hsvc| |rewrite m_halted_with_halted; reflexivity|rewrite m_killed_with_halted; reflexivity].
    apply check_syscall_ok_iff. apply Hchar. repeat split; reflexivity.
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
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs -> nstep n mo (ceff eff) mo' evs) /\
  (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists ci, check_syscall (sys_input segs ms x8) (with_ci ci eff) mo = CheckOk mo' evs) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) /\
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo').

(* [comment removed for export] *)
Lemma node_facts_of_iff : forall ms mo n x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> nstep n mo eff mo' evs) ->
  (forall eff mo' evs, nstep n mo eff mo' evs -> eff_copyins eff = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo') ->
  node_facts ms mo n.
Proof.
  intros ms mo n x8 Hsvc Hiff Hci Hnu Hpres. exists x8. split; [exact Hsvc|]. split; [|split; [|split]].
  - intros eff mo' evs Hc. pose proof (proj1 (Hiff _ _ _) Hc) as HP.
    pose proof (Hci _ _ _ HP) as E. destruct eff as [r ws zs us cs ci]; cbn in E; subst ci. exact HP.
  - intros eff mo' evs HP. exists (@nil (word * nat)). apply Hiff.
    pose proof (Hci _ _ _ HP) as E. destruct eff as [r ws zs us cs ci]; cbn in E; subst ci. exact HP.
  - exact Hnu.
  - intros eff mo' evs HP. exact (Hpres _ _ _ HP).
Qed.

(* [comment removed for export] *)
Lemma facts_ret_only : forall ms mo n x8 r evs0,
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = check_ret_only eff r mo evs0) ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo /\ evs = evs0)) ->
  node_facts ms mo n.
Proof.
  intros ms mo n x8 r evs0 Hsvc Hminv Hh Hchk Hn. eapply node_facts_of_iff; [exact Hsvc| | | |].
  - intros eff mo' evs. rewrite Hchk, check_ret_only_ok_iff, Hn. unfold eff0. tauto.
  - intros eff mo' evs HP. apply Hn in HP as (-> & _). reflexivity.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - intros eff mo' evs HP. apply Hn in HP as (_ & -> & _). auto.
Qed.

Ltac dispatch K arm :=
  unfold check_syscall; rewrite in_sysno_si;
  change (bv_unsigned (Z_to_bv 64 K)) with K;
  replace (lookup_ca checked_table K) with (Some arm) by reflexivity;
  cbn [arm ca_check];
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.


(* [comment removed for export] *)
Lemma node_facts_of_char : forall ms mo n x8 (C : resp -> Model -> list event -> Prop),
  ms_svc_pending ms = Some x8 ->
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> C eff mo' evs) ->
  (forall eff mo' evs, C eff mo' evs -> nstep n mo (ceff eff) mo' evs) ->
  (forall eff mo' evs, nstep n mo eff mo' evs -> exists ci, C (with_ci ci eff) mo' evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo') ->
  node_facts ms mo n.
Proof.
  intros ms mo n x8 C Hsvc Hiff H1 H2 Hnu Hpres. exists x8. split; [exact Hsvc|].
  split; [|split; [|split]].
  - intros eff mo' evs Hc. apply H1. apply Hiff. exact Hc.
  - intros eff mo' evs HP. destruct (H2 _ _ _ HP) as [ci Hc]. exists ci. apply Hiff. exact Hc.
  - exact Hnu.
  - intros eff mo' evs HP. exact (Hpres _ _ _ HP).
Qed.

Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma fd32_small : forall z, 0 <= z < 2^32 -> fd32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros. unfold fd32. apply abi_low32_small. assumption. Qed.

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

Definition write_char (buf : word) (fd : Z) (bs : list byte) (mo : Model)
    (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  exists k ci, 1 <= k <= Z.of_nat (length bs) /\
    eff = mkEffectU (Z_to_bv 64 k) [] [] [] [] ci /\
    access_ranges_eqb ci [(buf, Z.to_nat k)] = true /\
    mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs).

Lemma rw_bytes_max_small : rw_bytes_max < 2^32.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma write_check : forall ms mo fd bs eff mo' evs,
  at_node segs (NWrite fd bs) ms -> minv mo ->
  (check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff mo = CheckOk mo' evs <->
   write_char (areg ms 11) fd bs mo eff mo' evs)
  /\ check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff mo <> CheckUnmodeled.
Proof.
  intros ms mo fd bs eff mo' evs (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Hrom & Hbs) Hminv.
  pose proof rw_bytes_max_small as HM.
  match goal with |- (?c = _ <-> _) /\ _ => cut (c = match eff with
     | mkEffectU ret [] [] [] [] ci =>
         if (1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length bs))
         then if access_ranges_eqb ci [(areg ms 11, Z.to_nat (bv_unsigned ret))]
              then CheckOk mo (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
              else CheckReject
         else CheckReject
     | _ => CheckReject end) end.
  { intros E. rewrite E. split.
    - unfold write_char. destruct eff as [ret ws zs us cs ci]. split.
      + intros H. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
        destruct (1 <=? bv_unsigned ret) eqn:E1; [|discriminate].
        destruct (bv_unsigned ret <=? Z.of_nat (length bs)) eqn:E2; [|discriminate].
        cbn [andb] in H.
        destruct (access_ranges_eqb ci _) eqn:E3; [|discriminate]. inversion H; subst.
        apply Z.leb_le in E1. apply Z.leb_le in E2.
        exists (bv_unsigned ret), ci. rewrite Z_to_bv_bv_unsigned. repeat split; auto; lia.
      + intros (k & ci' & Hk & Heff & Hci & -> & ->). inversion Heff; subst.
        rewrite unsigned_lit by lia. rewrite Hci.
        replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
        replace (k <=? Z.of_nat (length bs)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] ci]; try discriminate. destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate. }
  dispatch 64 arm_write. unfold check_write. rewrite Ha0, Ha2, in_mem_si.
  destruct (std_chan mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
  unfold modeled_rw_range, modeled_rw_count. rewrite unsigned_lit by lia.
  replace (Z.of_nat (length bs) <=? rw_bytes_max) with true by (symmetry; apply Z.leb_le; lia). cbn [negb orb].
  rewrite w_is0_lit by lia. replace (Z.of_nat (length bs) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv zeta.
  replace (write_source (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length bs)))) with bs.
  2:{ symmetry. unfold write_source. rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT, rw_bytes_max in *; lia).
      rewrite unsigned_lit by lia.
      rewrite <- (wa_unsigned_id (areg ms 11)). apply readable_bytes_bytes_in; [eapply bytes_at_in; eassumption| lia]. }
  replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Lemma write_facts : forall ms mo fd bs,
  at_node segs (NWrite fd bs) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NWrite fd bs).
Proof.
  intros ms mo fd bs Hat Hminv Hh.
  eapply (node_facts_of_char ms mo (NWrite fd bs) _ (write_char (areg ms 11) fd bs mo)); [exact (proj1 Hat)| | | | |].
  - intros eff mo' evs. exact (proj1 (write_check _ _ _ _ eff mo' evs Hat Hminv)).
  - intros eff mo' evs (k & ci & Hk & -> & _ & -> & ->). cbn [nstep chan_write ceff]. split; [reflexivity|].
    right. exists k. repeat split; auto; lia.
  - intros eff mo' evs [-> [(Hbs & _) | (k & Hk & -> & ->)]].
    { exfalso. subst bs. cbn in Hat. lia. }
    exists [(areg ms 11, Z.to_nat k)]. exists k, [(areg ms 11, Z.to_nat k)].
    split; [exact Hk|]. split; [reflexivity|]. split; [apply access_ranges_eqb_refl|]. split; reflexivity.
  - intros eff. exact (proj2 (write_check _ _ _ _ eff mo [] Hat Hminv)).
  - intros eff mo' evs [-> _]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iovs_ok_of_at : forall ms iovs bufs,
  ms_rom ms = seg_rom segs ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs ->
  Z.of_nat (length (concat bufs)) < 2^64 ->
  Forall2 (iov_ok (ms_read_byte ms)) iovs bufs.
Proof.
  intros ms iovs bufs Hrom H. induction H as [|iov bs iovs bufs (Hl & Hb & _) _ IH]; intros Hlen; [constructor|].
  cbn [concat] in Hlen. rewrite length_app in Hlen.
  constructor.
  - split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
  - apply IH. lia.
Qed.

Lemma iovs_access_okb_of_at : forall ms iovs bufs,
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs ->
  Z.of_nat (length (concat bufs)) < 2^63 ->
  iovs_access_okb iovs = true.
Proof.
  intros ms iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hb & Hok) _ IH]; intros Hlen; [reflexivity|].
  cbn [concat] in Hlen. rewrite length_app in Hlen.
  cbn [iovs_access_okb forallb fst snd] in *. subst l.
  rewrite (access_okb_intro b (Z_to_bv 64 (Z.of_nat (length bs)))) by (rewrite unsigned_lit by lia; lia).
  exact (IH ltac:(lia)).
Qed.

Lemma read_iovec_entry_bytes_in : forall mp a b l,
  bytes_in mp a (le8 b ++ le8 l) -> bv_unsigned l < 2^63 -> read_iovec_entry mp (wa a) = IovEntry b l.   (* [comment removed for export] *)
Proof.
  intros mp a b l H Hl. apply bytes_in_app in H as [H1 H2]. rewrite length_le8 in H2.
  unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
  rewrite wa_add. change (bv_unsigned (8%bv : word)) with 8. replace (a + Z.of_nat 8) with (a + 8) in H2 by lia.
  rewrite (read_u64_bytes_in _ _ _ H2).
  replace (2 ^ 63 <=? bv_unsigned l) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma copy_iovecs_aux_bytes_in : forall iovs bufs mp a,
  Forall2 (iov_ok mp) iovs bufs ->
  Z.of_nat (length (concat bufs)) < 2^63 ->
  bytes_in mp a (iovec_bytes iovs) -> copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
  intros iovs bufs mp a H. revert a. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros a Htot Hin; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in Hin. rewrite <- app_assoc in Hin.
  cbn [concat] in Htot. rewrite length_app in Htot.
  pose proof Hin as Hin'. apply bytes_in_app in Hin' as [H1 H23]. apply bytes_in_app in H23 as [H2 H3].
  rewrite !length_le8 in H2. rewrite !length_le8 in H3.
  cbn [copy_iovecs_aux length].
  cbn [fst snd] in Hl.
  rewrite (read_iovec_entry_bytes_in mp a b l).
  2:{ apply bytes_in_app. split; [exact H1|]. rewrite length_le8. exact H2. }
  2:{ subst l. rewrite unsigned_lit by lia. lia. }
  subst l.
  rewrite wa_add. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH (a + 16)); [reflexivity| lia | exact H3].
Qed.

Lemma cap_iovecs_aux_id : forall mp iovs bufs left,
  Forall2 (iov_ok mp) iovs bufs -> Z.of_nat (length (concat bufs)) <= left ->
  cap_iovecs_aux iovs left = iovs.
Proof.
  intros mp iovs bufs left H. revert left. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros left Hle; [reflexivity|].
  cbn [concat] in Hle. rewrite length_app in Hle. cbn [cap_iovecs_aux fst snd] in *. subst l.
  rewrite unsigned_lit by lia. rewrite Z.min_r by lia. rewrite IH by lia. reflexivity.
Qed.


Definition writev_char (cz : list (word * nat)) (cf : Z -> list (word * nat)) (fd : Z) (bs : list byte) (mo : Model)
    (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  mo' = mo /\
  ((bs = [] /\ eff = mkEffectU (Z_to_bv 64 0) [] [] [] [] cz /\ evs = [])
   \/ (exists k ci, 1 <= k <= Z.of_nat (length bs) /\
         eff = mkEffectU (Z_to_bv 64 k) [] [] [] [] ci /\ access_ranges_eqb ci (cf k) = true /\
         evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs))).

Lemma check_ret_only_copyins_ok_iff : forall reads eff r m evs m' evs',
  check_ret_only_copyins reads eff r m evs = CheckOk m' evs' <->
  eff = mkEffectU r [] [] [] [] reads /\ m' = m /\ evs' = evs.
Proof.
  intros reads [ret ws zs us cs ci] r m evs m' evs'. unfold check_ret_only_copyins, clear_copyins, with_copyins. cbn.
  split.
  - intros H. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (bv_eqb ret r) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst.
    destruct (access_ranges_eqb ci reads) eqn:E2; [|discriminate]. apply access_ranges_eqb_eq in E2. inversion H; subst. auto.
  - intros (H & -> & ->). inversion H; subst. rewrite bv_eqb_refl, access_ranges_eqb_refl. reflexivity.
Qed.

Lemma check_ret_only_copyins_no_unmodeled : forall reads eff r m evs,
  check_ret_only_copyins reads eff r m evs <> CheckUnmodeled.
Proof.
  intros reads eff r m evs. unfold check_ret_only_copyins.
  destruct (check_ret_only _ _ _ _) eqn:E; [destruct (access_ranges_eqb _ _); discriminate|discriminate|].
  exfalso. exact (check_ret_only_no_unmodeled _ _ _ _ E).
Qed.

Lemma IOV_MAX_val : IOV_MAX = 1024. Proof. reflexivity. Qed.
Lemma MAX_RW_COUNT_big : rw_bytes_max <= MAX_RW_COUNT. Proof. unfold rw_bytes_max, MAX_RW_COUNT. lia. Qed.

Definition writev_nf (CI : list (word * nat)) (iovs : list (word * word)) (fd : Z) (bufs : list (list byte))
    (mo : Model) (eff : resp) : check_result :=
  if (length (concat bufs) =? 0)%nat then check_ret_only_copyins CI eff (Z_to_bv 64 0) mo []
  else match eff with
       | mkEffectU ret [] [] [] [] ci =>
           if (1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length (concat bufs)))
              && negb (addr_is_error_b ret)
           then if access_ranges_eqb ci (CI ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
                then CheckOk mo (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) (concat bufs)))
                else CheckReject
           else CheckReject
       | _ => CheckReject
       end.

(* [comment removed for export] *)
Lemma import_iovecs_bytes_in : forall mp a iovs bufs,
  Forall2 (iov_ok mp) iovs bufs ->
  iovs_access_okb iovs = true ->
  Z.of_nat (length (concat bufs)) < 2^63 ->
  (length bufs <= 1024)%nat ->
  a + 16 * Z.of_nat (length bufs) <= TASK_SIZE -> 0 <= a ->
  bytes_in mp a (iovec_bytes iovs) ->
  import_iovecs mp (wa a) (Z_to_bv 64 (Z.of_nat (length bufs))) = ImpOk iovs.
Proof.
  intros mp a iovs bufs Hok Hacc Htot Hcnt Hrange Ha Hin.
  pose proof (Forall2_length Hok) as Hleq.
  unfold import_iovecs.
  destruct (Nat.eq_dec (length bufs) 1) as [E1|N1].
  - rewrite E1. rewrite bv_eqb_refl.
    replace (access_okb (wa a) 16) with true.
    2:{ symmetry. unfold access_okb. rewrite wa_unsigned by (unfold TASK_SIZE in *; lia). apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia. }
    cbn [negb].
    destruct Hok as [|[b l] bs iovs' bufs' (Hl & Hlen & Hb) Hrest]; [cbn in E1; lia|].
    destruct Hrest; [|cbn in E1; lia].
    cbn [iovec_bytes flat_map fst snd] in Hin. rewrite app_nil_r in Hin.
    cbn [fst snd] in Hl. cbn [concat] in Htot. rewrite app_nil_r in Htot.
    rewrite (read_iovec_entry_bytes_in mp a b l Hin) by (subst l; rewrite unsigned_lit by lia; lia).
    cbn [iovs_access_okb forallb fst snd] in Hacc. rewrite andb_true_r in Hacc.
    replace (access_okb b (Z.min (bv_unsigned l) MAX_RW_COUNT)) with true; [reflexivity|].
    symmetry. unfold access_okb in *. apply andb_prop in Hacc as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
    apply andb_true_intro; split; apply Z.leb_le; lia.
  - replace (bv_eqb (Z_to_bv 64 (Z.of_nat (length bufs))) (Z_to_bv 64 1)) with false.
    2:{ symmetry. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    destruct (Nat.eq_dec (length bufs) 0) as [E0|N0].
    { rewrite E0. cbn [Z.of_nat]. rewrite bv_eqb_refl. destruct Hok; [reflexivity| cbn in E0; lia]. }
    replace (bv_eqb (Z_to_bv 64 (Z.of_nat (length bufs))) (Z_to_bv 64 0)) with false.
    2:{ symmetry. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    rewrite unsigned_lit by lia.
    replace (IOV_MAX <? Z.of_nat (length bufs)) with false by (symmetry; apply Z.ltb_ge; rewrite IOV_MAX_val; lia).
    replace (access_okb (wa a) (16 * Z.of_nat (length bufs))) with true.
    2:{ symmetry. unfold access_okb. rewrite wa_unsigned by (unfold TASK_SIZE in *; lia). apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia. }
    cbn [negb]. rewrite word_to_nat_of_nat by lia. rewrite <- Hleq.
    rewrite (copy_iovecs_aux_bytes_in iovs bufs); [| exact Hok | lia | exact Hin].
    rewrite Hacc. reflexivity.
Qed.

Lemma import_iovecs_accesses_eq : forall mp a n iovs,
  import_iovecs mp a n = ImpOk iovs ->
  exists CI, import_iovecs_accesses mp a n = CI.
Proof. intros. eexists. reflexivity. Qed.

Lemma writev_check_nf : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minv mo ->
  exists CI iovs, forall eff,
    check_syscall (sys_input segs ms (Z_to_bv 64 66)) eff mo = writev_nf CI iovs fd bufs mo eff.
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Harr & iovs & Hiov & Hbufs) Hminv.
  pose proof writev_node_max_small as HM. pose proof writev_node_max_big as HM2.
  pose proof (iovs_ok_of_at _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_access_okb_of_at _ _ _ Hbufs ltac:(lia)) as Hacc.
  pose proof (Forall2_length Hbufs) as Hleq.
  pose proof (bv_unsigned_in_range 64 (areg ms 11)) as [Ha11 _].
  exists (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length bufs)))), (cap_iovecs iovs).
  intros eff. unfold writev_nf.
  dispatch 66 arm_writev.
  unfold check_writev. rewrite Ha0, Ha2, in_mem_si.
  destruct (std_chan mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
  unfold iovcnt32. rewrite abi_low32_small by lia.
  rewrite <- (wa_unsigned_id (areg ms 11)) at 1.
  rewrite (import_iovecs_bytes_in (ms_read_byte ms) (bv_unsigned (areg ms 11)) iovs bufs Hok Hacc ltac:(lia) Hcnt Harr Ha11)
    by (eapply bytes_at_in; eassumption).
  cbv zeta. rewrite iovs_total_cap, (iovs_total_ok _ _ _ Hok). rewrite Z.min_l by lia.
  assert (Hg : writev_gathered (ms_read_byte ms) iovs = concat bufs).
  { unfold writev_gathered, cap_iovecs. rewrite (cap_iovecs_aux_id _ _ _ _ Hok) by lia.
    apply gather_prefix_full. apply gather_iovecs_ok. exact Hok. }
  rewrite Hg.
  destruct (length (concat bufs) =? 0)%nat eqn:El.
  { apply Nat.eqb_eq in El. rewrite El. cbn [Z.of_nat Z.eqb]. reflexivity. }
  apply Nat.eqb_neq in El.
  replace (Z.of_nat (length (concat bufs)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold len_word. replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat (length (concat bufs))))) with false.
  2:{ symmetry. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia. }
  reflexivity.
Qed.

Lemma addr_is_error_small : forall z, 0 <= z <= rw_bytes_max -> addr_is_error_b (Z_to_bv 64 z) = false.
Proof.
  intros z Hz. pose proof rw_bytes_max_small. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.
Lemma addr_is_error_small_wv : forall z, 0 <= z <= writev_node_max -> addr_is_error_b (Z_to_bv 64 z) = false.
Proof.
  intros z Hz. pose proof writev_node_max_small. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

Lemma writev_facts : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NWritev fd bufs).
Proof.
  intros ms mo fd bufs Hat Hminv Hh.
  destruct (writev_check_nf _ _ _ _ Hat Hminv) as (CI & iovs & Hnf).
  assert (Htot : Z.of_nat (length (concat bufs)) <= writev_node_max) by (cbn in Hat; tauto).
  pose proof writev_node_max_small as HM. pose proof writev_node_max_big as HM2.
  eapply (node_facts_of_char ms mo (NWritev fd bufs) _ (fun eff mo' evs => writev_nf CI iovs fd bufs mo eff = CheckOk mo' evs));
    [exact (proj1 Hat)| | | | |].
  - intros eff mo' evs. rewrite Hnf. tauto.
  - intros eff mo' evs H. cbn [nstep]. unfold chan_write, writev_nf in *.
    destruct (length (concat bufs) =? 0)%nat eqn:E1.
    { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->). apply Nat.eqb_eq in E1.
      destruct (concat bufs); [|cbn in E1; lia]. split; [reflexivity|]. left. repeat split; reflexivity. }
    destruct eff as [ret ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (1 <=? bv_unsigned ret) eqn:E2; [|discriminate].
    destruct (bv_unsigned ret <=? Z.of_nat (length (concat bufs))) eqn:E3; [|discriminate].
    destruct (negb (addr_is_error_b ret)); [|discriminate]. cbn [andb] in H.
    destruct (access_ranges_eqb ci _); [|discriminate]. inversion H; subst.
    apply Z.leb_le in E2. apply Z.leb_le in E3.
    split; [reflexivity|]. right. exists (bv_unsigned ret). cbn. rewrite Z_to_bv_bv_unsigned. repeat split; auto; lia.
  - intros eff mo' evs [-> [(Hbs & -> & ->) | (k & Hk & -> & ->)]]; unfold writev_nf.
    + rewrite Hbs. cbn [length Nat.eqb]. exists CI. apply check_ret_only_copyins_ok_iff. repeat split; reflexivity.
    + destruct (length (concat bufs) =? 0)%nat eqn:E1.
      { exfalso. apply Nat.eqb_eq in E1. lia. }
      exists (CI ++ iov_prefix_accesses iovs (Z.to_nat k)).
      cbn [with_ci eff0 eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
      rewrite unsigned_lit by lia.
      replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
      replace (k <=? Z.of_nat (length (concat bufs))) with true by (symmetry; apply Z.leb_le; lia).
      rewrite addr_is_error_small_wv by lia. rewrite access_ranges_eqb_refl. reflexivity.
  - intros eff. rewrite Hnf. unfold writev_nf.
    destruct (length (concat bufs) =? 0)%nat; [apply check_ret_only_copyins_no_unmodeled|].
    destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] ci]; try discriminate. destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate.
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
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition open_check (path : list byte) (eff : resp) (mo : Model) : check_result :=
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
Lemma check_open_result_ok_iff : forall eff mo ent mo' evs,
  check_open_result eff mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) = CheckOk mo' evs <->
  (open_result mo ent eff mo' /\ evs = []).
Proof.
  intros [ret ws zs us cs ci] mo ent mo' evs. unfold check_open_result, check_new_fd_result, open_result, efferr, eff0. split.
  - intro H.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
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
Proof. intros. apply check_new_fd_result_no_unmodeled. Qed.

Lemma ldiff_open_flags : forall x, Z.ldiff x (O_CLOEXEC + O_LARGEFILE) = 0 -> Z.ldiff x open_ignored_flags = 0.
Proof.
  intros x H. apply Z.bits_inj'. intros k Hk. rewrite Z.ldiff_spec, Z.bits_0.
  apply (f_equal (fun z => Z.testbit z k)) in H. rewrite Z.ldiff_spec, Z.bits_0 in H.
  destruct (Z.testbit x k) eqn:E; [|reflexivity]. cbn in H |- *.
  apply negb_false_iff in H. apply negb_false_iff.
  unfold open_ignored_flags. change (O_CLOEXEC + O_LARGEFILE + O_NONBLOCK) with (Z.lor (O_CLOEXEC + O_LARGEFILE) O_NONBLOCK).
  rewrite Z.lor_spec, H. reflexivity.
Qed.

Lemma clear_copyins_ceff : forall eff, clear_copyins eff = ceff eff.
Proof. intros [r ws zs us cs ci]; reflexivity. Qed.

Lemma open_check_nf : forall ms mo path,
  at_node segs (NOpen path) ms ->
  exists CI, forall eff,
  check_syscall (sys_input segs ms (Z_to_bv 64 56)) eff mo = check_copyins_after CI eff (open_check path (ceff eff) mo).
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hrom & Hp).
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  eexists. intros eff.
  dispatch 56 arm_openat. unfold check_openat. rewrite in_mem_si.
  rewrite (modeled_open_flags_rd _ (ldiff_open_flags _ Hfl)). cbn [negb]. cbv zeta.
  rewrite clear_copyins_ceff. f_equal.
  unfold Open.check_openat_body, open_check. rewrite Ha0, in_mem_si.
  rewrite <- (wa_unsigned_id (areg ms 11)). unfold read_cstr.
  destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
  - rewrite (read_cstr_aux_toolong_bytes_in path_max path); [reflexivity|exact Hlong|exact Hnz|].
    apply bytes_in_app in Hin as [Hin _]. exact Hin.
  - rewrite (read_cstr_aux_bytes_in path path_max); [|lia|exact Hnz|exact Hin].
    destruct path as [|c path']; [reflexivity|].
    cbn [path_eqb]. change (bv_eqb (fd32 (Z_to_bv 64 (-100))) AT_FDCWD32) with true. cbn [negb].
    unfold Open.check_openat_resolved. rewrite Hsl. rewrite (ldiff_open_flags _ Hfl). cbn [Z.eqb].
    unfold Open.check_openat_read. reflexivity.
Qed.

Lemma open_check_ok_iff : forall path eff mo mo' evs,
  open_check path eff mo = CheckOk mo' evs <-> nstep (NOpen path) mo eff mo' evs.
Proof.
  intros path eff mo mo' evs. unfold open_check. cbn [nstep].
  destruct (path_max <=? length path)%nat.
  { rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  destruct path as [|c path']. { rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  destruct (path_is_dirref (c :: path')). { rewrite check_open_result_ok_iff. tauto. }
  destruct (fs_lookup (m_fs mo) (c :: path')).
  - rewrite check_open_result_ok_iff. tauto.
  - rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
Qed.

Lemma open_check_no_unmodeled : forall path eff mo, open_check path eff mo <> CheckUnmodeled.
Proof.
  intros path eff mo. unfold open_check.
  destruct (path_max <=? length path)%nat; [apply check_ret_only_no_unmodeled|].
  destruct path; [apply check_ret_only_no_unmodeled|].
  destruct (path_is_dirref _); [apply check_open_result_no_unmodeled|].
  destruct (fs_lookup (m_fs mo) _); [apply check_open_result_no_unmodeled|apply check_ret_only_no_unmodeled].
Qed.

Ltac minv_open H := destruct H as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MA).

Lemma minv_open_insert : forall mo ent,
  minv mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
  intros mo ent Hminv Hfree Hent. minv_open Hminv. unfold minv. macc.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| exact MA]]]]].
  - intros k c. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. destruct Hent.
    + apply MC.
  - intros k p off. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. exact Hent.
    + apply MF.
  - intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. destruct e; auto.
    + apply MK.
Qed.

Lemma open_pres : forall mo path eff mo' evs,
  minv mo -> m_halted mo = None -> nstep (NOpen path) mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros mo path eff mo' evs Hminv Hh [_ H].
  assert (Hor : forall ent, open_result mo ent eff mo' ->
            match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            m_halted mo' = None /\ minv mo').
  { intros ent [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
    split; [macc; exact Hh|]. apply minv_open_insert; assumption. }
  destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
  destruct path as [|c path']. { destruct H as [_ ->]; auto. }
  destruct (path_is_dirref (c :: path')). { exact (Hor FdDir H I). }
  destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
  + apply (Hor _ H). cbn. congruence.
  + destruct H as [_ ->]; auto.
Qed.

Lemma open_facts : forall ms mo path,
  at_node segs (NOpen path) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NOpen path).
Proof.
  intros ms mo path Hat Hminv Hh. destruct (open_check_nf _ mo _ Hat) as [CI Hnf].
  eapply (node_facts_of_char ms mo (NOpen path) _
            (fun eff mo' evs => eff_copyins eff = CI /\ open_check path (ceff eff) mo = CheckOk mo' evs)); [exact (proj1 Hat)| | | | |].
  - intros eff mo' evs. rewrite Hnf, check_copyins_after_ok_iff. tauto.
  - intros eff mo' evs [_ H]. apply open_check_ok_iff. exact H.
  - intros eff mo' evs H. exists CI. split; [destruct eff; reflexivity|]. rewrite ceff_with_ci.
    apply open_check_ok_iff in H.
    assert (E : eff_copyins eff = []).
    { revert H. unfold open_check. destruct (path_max <=? length path)%nat.
      { intros H. apply check_ret_only_ok_iff in H as (-> & _). reflexivity. }
      destruct path; [intros H; apply check_ret_only_ok_iff in H as (-> & _); reflexivity|].
      destruct (path_is_dirref _); [intros H; apply check_open_result_ok_iff in H as [[(e & _ & -> & _)|(_ & -> & _)] _]; reflexivity|].
      destruct (fs_lookup (m_fs mo) _); [intros H; apply check_open_result_ok_iff in H as [[(e & _ & -> & _)|(_ & -> & _)] _]; reflexivity|].
      intros H. apply check_ret_only_ok_iff in H as (-> & _). reflexivity. }
    destruct eff as [r ws zs us cs ci]; cbn in E; subst ci. cbn [ceff eff_ret eff_writes eff_zeros eff_unmaps eff_copies]. exact H.
  - intros eff. rewrite Hnf. intros U. apply check_copyins_after_unmodeled in U. exact (open_check_no_unmodeled _ _ _ U).
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
  intros ms mo fd buf count eff (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hb47 & Hwr) Hminv. minv_open Hminv.
  pose proof (proj1 Hwr) as Hb0.
  assert (Hsure : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { unfold access_okb. rewrite !unsigned_lit by (unfold TASK_SIZE in *; lia). apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia. }
  dispatch 63 arm_read. unfold check_read, read_check. rewrite Ha0, Ha1, Ha2, in_wmem_si.
  rewrite fd32_small by lia.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk; [|reflexivity].
  pose proof (MK _ _ Hlk) as HK. destruct e as [ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]; try contradiction.
  - exfalso. apply MC in Hlk. rewrite unsigned_lit in Hlk by lia. lia.
  - rewrite Hsure. cbn [negb].
    destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
    rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT; lia).
    rewrite unsigned_lit by lia.
    cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
    assert (Hlen : Z.of_nat (length bs) <= count /\ Z.of_nat (length bs) < 2^64).
    { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
      unfold word_to_nat in L. rewrite unsigned_lit in L by lia. lia. }
    rewrite read_bytes_map_eq. unfold ms_writable_byte. unfold len_word at 1. rewrite word_to_nat_of_nat by lia.
    change (Z_to_bv 64 buf) with (wa buf) at 1.
    destruct (read_bytes_aux (wview segs (ms_mem ms)) (wa buf) (length bs)) eqn:E.
    2:{ exfalso. exact (read_bytes_aux_wr_at _ _ _ _ _ Hwr (proj1 Hlen) E). }
    destruct bs; reflexivity.
  - rewrite Hsure. reflexivity.
Qed.

Lemma listN_eqb_refl : forall l, listN_eqb l l = true.
Proof. intros. apply listN_eqb_eq. reflexivity. Qed.

Lemma read_check_ok_iff : forall fd buf count eff mo mo' evs,
  minv mo ->
  read_check fd buf count eff mo = CheckOk mo' evs <-> nstep (NRead fd buf count) mo eff mo' evs.
Proof.
  intros fd buf count eff mo mo' evs Hminv. minv_open Hminv. unfold read_check. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  2:{ rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  destruct e as [ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]; try (split; [discriminate| tauto]).
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
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]|]; try discriminate; try apply check_ret_only_no_unmodeled.
  destruct (fs_lookup (m_fs mo) p); [|discriminate]. cbv zeta.
  destruct (file_read _ _ _); [apply check_ret_only_no_unmodeled|].
  destruct eff as [ret [|[a bs'] [|? ?]] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate.
  destruct (_ && _); discriminate.
Qed.

Lemma minv_update_file : forall mo k p off off',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros mo k p off off' Hminv Hk. minv_open Hminv. unfold minv. macc.
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| exact MA]]]]].
  - intros k' c. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [intros H; discriminate| apply MC].
  - intros k' p' o. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MF].
    intros H. inversion H; subst. exact (MF _ _ _ Hk).
  - intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MK]. intros H; inversion H; exact I.
Qed.

Lemma read_pres : forall mo fd buf count eff mo' evs,
  minv mo -> m_halted mo = None -> nstep (NRead fd buf count) mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros mo fd buf count eff mo' evs Hminv Hh [_ H].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]|] eqn:Hlk; try contradiction.
  + destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
    split; [macc; exact Hh|]. eapply minv_update_file; eassumption.
  + destruct H as [_ ->]. auto.
  + destruct H as [_ ->]. auto.
Qed.

Lemma read_facts : forall ms mo fd buf count,
  at_node segs (NRead fd buf count) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NRead fd buf count).
Proof.
  intros ms mo fd buf count Hat Hminv Hh. eapply node_facts_of_iff; [exact (proj1 Hat)| | | |].
  - intros eff mo' evs. rewrite (read_check_spec _ _ _ _ _ _ Hat Hminv). apply read_check_ok_iff. exact Hminv.
  - intros eff mo' evs [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]|]; try contradiction;
      try (destruct H as [-> _]; reflexivity).
    destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [-> _]; reflexivity.
  - intros eff. rewrite (read_check_spec _ _ _ _ _ _ Hat Hminv). apply read_check_no_unmodeled.
  - intros eff mo' evs. apply read_pres; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma minv_remove : forall mo fd, minv mo -> 3 <= fd < 2^32 ->
  minv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
  intros mo fd Hminv Hfd. minv_open Hminv. unfold minv. macc.
  rewrite !fd_lookup_remove.
  assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
  { intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  rewrite !Hne by lia.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| split; [exact ML| exact MA]]]]].
  - intros k c. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MC].
  - intros k p off. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MF].
  - intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MK].
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
  { intros eff. dispatch 57 arm_close. unfold check_close. rewrite Ha0. rewrite fd32_small by lia. reflexivity. }
  eapply node_facts_of_iff; [exact Hsvc| | | |].
  - intros eff mo' evs. rewrite Hchk. cbn [nstep]. destruct (fd_lookup _ _); rewrite check_ret_only_ok_iff; unfold efferr, eff0; tauto.
  - intros eff mo' evs (_ & _ & H). destruct (fd_lookup _ _); destruct H as [-> _]; reflexivity.
  - intros eff. rewrite Hchk. destruct (fd_lookup _ _); apply check_ret_only_no_unmodeled.
  - intros eff mo' evs (_ & _ & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
    split; [macc; exact Hh|]. apply minv_remove; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ioctl_facts : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NIoctl fd req).
Proof.
  intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh.
  eapply facts_ret_only; [exact Hsvc | exact Hminv | exact Hh | |].
  - intros eff. dispatch 29 arm_ioctl. unfold check_ioctl. rewrite Ha0, Ha1. subst req.
    unfold cmd32. rewrite fd32_small, abi_low32_small by lia.
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
  intros mo t Hminv Ht. minv_open Hminv. unfold minv. macc.
  repeat split; try assumption; match goal with H : Some _ = Some _ |- _ => inversion H; subst; lia end.
Qed.

Lemma set_tid_facts : forall ms mo,
  at_node segs NSetTid ms -> minv mo -> m_halted mo = None -> node_facts ms mo NSetTid.
Proof.
  intros ms mo Hsvc Hminv Hh.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (Z_to_bv 64 96)) eff mo = check_set_tid_address eff mo).
  { intros eff. dispatch 96 arm_set_tid_address. reflexivity. }
  eapply node_facts_of_iff; [exact Hsvc| | | |].
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
  - intros eff mo' evs (_ & t & _ & Ht). destruct (m_tid mo); [destruct Ht as [_ ->]; auto|].
    destruct Ht as [Hr ->]. split; [macc; exact Hh|]. apply minv_with_tid; assumption.
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
    [dispatch 93 arm_exit | dispatch 94 arm_exit_group]; unfold check_exit; rewrite Ha0; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
  m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vm_shape (m m' : Model) : Prop :=
  vm_only m m' /\ (m_vm_lazy m = [] -> m_vm_lazy m' = []) /\ alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).

Lemma vm_shape_refl : forall m, vm_shape m m.
Proof. intros m. repeat split; auto. Qed.

Lemma vm_shape_trans : forall m1 m2 m3, vm_shape m1 m2 -> vm_shape m2 m3 -> vm_shape m1 m3.
Proof.
  intros m1 m2 m3 ((A1 & A2 & A3 & A4 & A5) & L1 & T1) ((B1 & B2 & B3 & B4 & B5) & L2 & T2).
  repeat split; try congruence. auto.
Qed.

Lemma vm_shape_with_vmmaps : forall h m, alloc_top h = alloc_top (m_vmmaps m) -> vm_shape m (with_vmmaps h m).
Proof. intros h m Ht. unfold vm_shape, vm_only. macc. repeat split; auto. Qed.

Lemma vm_shape_with_vm_backing : forall l p m, (m_vm_lazy m = [] -> l = []) -> vm_shape m (with_vm_backing l p m).
Proof. intros l p m Hl. destruct m; unfold vm_shape, vm_only, with_vm_backing; cbn. unfold m_fds, m_fs, m_halted, m_tid, m_stdin, m_vm_lazy, m_vmmaps in *; cbn in *. repeat split; auto. Qed.

Lemma vm_shape_vm_forget_range : forall lo hi m, vm_shape m (vm_forget_range lo hi m).
Proof. intros. unfold vm_forget_range. apply vm_shape_with_vm_backing. intros ->. reflexivity. Qed.

Lemma vm_shape_forget_vm_ranges : forall ranges m, vm_shape m (forget_vm_ranges ranges m).
Proof.
  induction ranges as [|[a n] ranges IH]; intros m; cbn [forget_vm_ranges]; [apply vm_shape_refl|].
  eapply vm_shape_trans; [apply vm_shape_vm_forget_range| apply IH].
Qed.

Lemma vm_shape_with_brk_next : forall m req r, vm_shape m (with_brk_next m req r).
Proof.
  intros. unfold with_brk_next. cbv zeta. eapply vm_shape_trans; [| apply vm_shape_forget_vm_ranges]. apply vm_shape_with_vmmaps; reflexivity.
Qed.

Lemma vm_shape_with_mmap_backing : forall flags a n m m0,
  mmap_noreserve_b flags = false -> vm_shape m0 m -> vm_shape m0 (with_mmap_backing flags a n m).
Proof. intros flags a n m m0 Hf Hs. unfold with_mmap_backing. rewrite Hf. exact Hs. Qed.

Lemma vm_shape_with_mmap_destroyed : forall a n h m,
  alloc_top h = alloc_top (m_vmmaps m) -> vm_shape m (with_mmap_destroyed a n h m).
Proof.
  intros * Ht. unfold with_mmap_destroyed. eapply vm_shape_trans; [| apply vm_shape_vm_forget_range]. apply vm_shape_with_vmmaps; exact Ht.
Qed.

Lemma vm_shape_with_mmap_replacement : forall flags a n h m,
  mmap_noreserve_b flags = false -> alloc_top h = alloc_top (m_vmmaps m) ->
  vm_shape m (with_mmap_replacement flags a n (with_vmmaps h m)).
Proof.
  intros flags a n h m Hf Ht. unfold with_mmap_replacement. apply vm_shape_with_mmap_backing; [exact Hf|].
  eapply vm_shape_trans; [| apply vm_shape_vm_forget_range]. apply vm_shape_with_vmmaps; exact Ht.
Qed.

Lemma vm_shape_mprotect_model_next : forall m a n, vm_shape m (mprotect_model_next m a n).
Proof. intros. unfold mprotect_model_next. apply vm_shape_with_vmmaps. reflexivity. Qed.

Lemma vm_shape_mremap_model_next : forall m old old_n dst new_n,
  vm_shape m (mremap_model_next m old old_n dst new_n).
Proof.
  intros. unfold mremap_model_next, vm_resize_backing. cbv zeta.
  eapply vm_shape_trans; [apply (vm_shape_with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n)); reflexivity|].
  apply vm_shape_with_vm_backing. macc. intros Hl.
  unfold mremap_source_lazy_b. rewrite Hl. cbn. reflexivity.
Qed.

Lemma minv_vm_shape : forall mo mo', vm_shape mo mo' -> minv mo -> minv mo'.
Proof.
  intros mo mo' ((Hf & Hs & _ & Ht & _) & Hl & Htop) Hm. unfold minv in *. rewrite Hf, Hs, Ht, Htop.
  destruct Hm as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MA).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|].
  split; [exact MK|]. split; [exact MT|]. split; [exact (Hl ML)| exact MA].
Qed.

Ltac crush_check H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ =>
              let E := fresh "E" in
              apply check_ret_only_ok_iff in H as (E & ? & ?); first [subst | inversion E; subst; clear E]
          | (match ?x with _ => _ end) = _ => destruct x
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).

Ltac shape_done :=
  split; [ first [ apply vm_shape_refl | apply vm_shape_with_brk_next
                 | apply vm_shape_with_mmap_backing; [assumption| apply vm_shape_with_vmmaps; reflexivity]
                 | apply vm_shape_with_mmap_destroyed; reflexivity
                 | apply vm_shape_with_mmap_replacement; [assumption| reflexivity]
                 | apply vm_shape_mprotect_model_next | apply vm_shape_mremap_model_next ]
         | split; reflexivity ].

Lemma check_brk_shape : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> vm_shape m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros req eff m m' evs H. unfold check_brk in H. crush_check H; shape_done. Qed.

Lemma check_mmap_shape : forall addr len prot flags fd off eff m m' evs,
  mmap_noreserve_b flags = false ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_shape m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros Hf H. unfold check_mmap in H. crush_check H; shape_done. Qed.

Lemma check_munmap_shape : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> vm_shape m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros H. unfold check_munmap in H. crush_check H; shape_done. Qed.

Lemma check_mprotect_shape : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> vm_shape m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros H. unfold check_mprotect in H. crush_check H; shape_done. Qed.

Lemma check_mremap_shape : forall old osz nsz flags eff m m' evs,
  check_mremap old osz nsz flags eff m = CheckOk m' evs -> vm_shape m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros H. unfold check_mremap in H. crush_check H; shape_done. Qed.

Ltac no_unm :=
  repeat first [ apply check_ret_only_no_unmodeled
               | apply check_ret_only_copyins_no_unmodeled
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

Lemma mmap_safe_no_unmodeled : forall addr len prot flags fd off eff m,
  mmap_safe_b addr len prot flags off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros addr len prot flags fd off eff m. unfold mmap_safe_b, check_mmap.
  destruct (negb (mmap_off_aligned_b off)). { intros ->. apply check_ret_only_no_unmodeled. }
  destruct (negb (mmap_anon_b flags)). { discriminate. }
  destruct (w_is0 len). { intros ->. apply check_ret_only_no_unmodeled. }
  destruct (mmap_modeled_b prot flags off); [intros _; no_unm|].
  destruct (mmap_noaccess_b prot flags off); [intros _; no_unm|].
  destruct (mmap_fixed_noaccess_b prot flags off); cbn [orb].
  - cbv zeta. destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
    destruct (negb (_ <=? alloc_top _)); [discriminate|].
    destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
    destruct (negb (0 <? bv_unsigned addr)); [discriminate|].
    destruct (region_free (vm_reserved _) _ _ && map_contains _ _ _); [intros _; no_unm|]. cbn [orb].
    destruct (region_free (vm_reserved _ ++ vm_maps _) _ _); [intros _; no_unm|]. cbn [orb].
    intros ->. no_unm.
  - destruct (mmap_fixed_rw_b prot flags off); [|discriminate].
    cbv zeta. destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
    destruct (negb (_ <=? alloc_top _)); [discriminate|].
    destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
    destruct (negb (0 <? bv_unsigned addr)); [discriminate|].
    destruct (region_free (vm_reserved _) _ _ && map_contains _ _ _); [intros _; no_unm|]. cbn [orb].
    destruct (region_free (vm_reserved _ ++ vm_maps _) _ _); [intros _; no_unm|]. cbn [orb].
    intros ->. no_unm.
Qed.

Lemma mremap_safe_no_unmodeled : forall old osz nsz flags eff m,
  mremap_safe_b old osz nsz flags m = true -> check_mremap old osz nsz flags eff m <> CheckUnmodeled.
Proof.
  intros old osz nsz flags eff m. unfold mremap_safe_b, check_mremap.
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)); [discriminate|].
  destruct (negb (bv_unsigned old mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (page_align_is0_b nsz); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (page_align_is0_b osz); [discriminate|]. cbv zeta.
  intros ->. cbn [negb]. destruct (_ =? _); [apply check_ret_only_no_unmodeled|]. no_unm.
Qed.

(* [comment removed for export] *)
Lemma mm_facts : forall ms mo n i x8 (chk : resp -> check_result),
  node_input n = Some i ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (evs = [] /\ syscall_spec i mo (Ok eff mo' evs))) ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_shape mo mo' /\ evs = [] /\ eff_copyins eff = []) ->
  node_facts ms mo n.
Proof.
  intros ms mo n i x8 chk Hi Hn Hsvc Hminv Hh Hc1 Hc2 Hnu Hshape.
  eapply node_facts_of_iff; [exact Hsvc| | | |].
  - intros eff mo' evs. rewrite Hc1, Hn, <- check_syscall_ok_iff, Hc2. split; [|tauto].
    intros H. split; [|exact H]. exact (proj1 (proj2 (Hshape _ _ _ H))).
  - intros eff mo' evs HP. apply Hn in HP as [_ HP]. apply check_syscall_ok_iff in HP. rewrite Hc2 in HP.
    exact (proj2 (proj2 (Hshape _ _ _ HP))).
  - intros eff. rewrite Hc1. apply Hnu.
  - intros eff mo' evs HP. apply Hn in HP as [_ HP]. apply check_syscall_ok_iff in HP. rewrite Hc2 in HP.
    apply Hshape in HP as [Hv _]. split.
    + destruct Hv as [(_ & _ & -> & _) _]. exact Hh.
    + eapply minv_vm_shape; eassumption.
Qed.

Ltac dispatch_pure K arm :=
  unfold check_syscall; cbn [in_sysno pure_input];
  change (bv_unsigned (Z_to_bv 64 K)) with K;
  replace (lookup_ca checked_table K) with (Some arm) by reflexivity;
  cbn [arm ca_check in_arg in_args nth pure_input].

Lemma brk_facts : forall ms mo req,
  at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo -> node_facts ms mo (NBrk req).
Proof.
  intros ms mo req (Hsvc & Ha0) Hminv Hh _.
  eapply (mm_facts ms mo (NBrk req) _ _ (fun eff => check_brk (Z_to_bv 64 req) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 214 arm_brk. rewrite Ha0. reflexivity.
  - intros eff. dispatch_pure 214 arm_brk. reflexivity.
  - intros [r ws zs us cs ci]. unfold check_brk. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (_ && _); discriminate.
  - intros eff mo' evs. apply check_brk_shape.
Qed.

Lemma mmap_facts : forall ms mo addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
  node_facts ms mo (NMmap addr len prot flags).
Proof.
  intros ms mo addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) Hminv Hh [Hnr Hsafe].
  eapply (mm_facts ms mo (NMmap addr len prot flags) _ _
            (fun eff => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                   (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 222 arm_mmap. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
  - intros eff. dispatch_pure 222 arm_mmap. reflexivity.
  - intros eff. apply mmap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mmap_shape. exact Hnr.
Qed.

Lemma munmap_facts : forall ms mo addr len,
  at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
  node_facts ms mo (NMunmap addr len).
Proof.
  intros ms mo addr len (Hsvc & Ha0 & Ha1) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMunmap addr len) _ _
            (fun eff => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 215 arm_munmap. rewrite Ha0, Ha1. reflexivity.
  - intros eff. dispatch_pure 215 arm_munmap. reflexivity.
  - intros eff. apply munmap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_munmap_shape.
Qed.

Lemma mprotect_facts : forall ms mo addr len prot,
  at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
  node_facts ms mo (NMprotect addr len prot).
Proof.
  intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMprotect addr len prot) _ _
            (fun eff => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 226 arm_mprotect. rewrite Ha0, Ha1, Ha2. reflexivity.
  - intros eff. dispatch_pure 226 arm_mprotect. reflexivity.
  - intros eff. apply mprotect_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mprotect_shape.
Qed.

Lemma mremap_facts : forall ms mo old osz nsz flags,
  at_node segs (NMremap old osz nsz flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMremap old osz nsz flags) mo ->
  node_facts ms mo (NMremap old osz nsz flags).
Proof.
  intros ms mo old osz nsz flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3) Hminv Hh Hsafe.
  eapply (mm_facts ms mo (NMremap old osz nsz flags) _ _
            (fun eff => check_mremap (Z_to_bv 64 old) (Z_to_bv 64 osz) (Z_to_bv 64 nsz) (Z_to_bv 64 flags) eff mo));
    [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh | | | |].
  - intros eff. dispatch 216 arm_mremap. rewrite Ha0, Ha1, Ha2, Ha3. reflexivity.
  - intros eff. dispatch_pure 216 arm_mremap. reflexivity.
  - intros eff. apply mremap_safe_no_unmodeled. exact Hsafe.
  - intros eff mo' evs. apply check_mremap_shape.
Qed.

(* [comment removed for export] *)
Lemma check_mmap_evs : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> evs = [].
Proof. intros until evs; intros H. unfold check_mmap in H. crush_check H; reflexivity. Qed.

Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <-> check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 214 arm_brk.
  split; [tauto|]. intros H. split; [exact (proj1 (proj2 (check_brk_shape _ _ _ _ _ H)))| exact H].
Qed.

Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 222 arm_mmap.
  split; [tauto|]. intros H. split; [exact (check_mmap_evs _ _ _ _ _ _ _ _ _ _ H)|exact H].
Qed.

Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 215 arm_munmap.
  split; [tauto|]. intros H. split; [exact (proj1 (proj2 (check_munmap_shape _ _ _ _ _ _ H)))| exact H].
Qed.

Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 226 arm_mprotect.
  split; [tauto|]. intros H. split; [exact (proj1 (proj2 (check_mprotect_shape _ _ _ _ _ _ _ H)))| exact H].
Qed.

Lemma nstep_mremap_iff : forall old osz nsz flags mo eff mo' evs,
  nstep (NMremap old osz nsz flags) mo eff mo' evs <->
  check_mremap (Z_to_bv 64 old) (Z_to_bv 64 osz) (Z_to_bv 64 nsz) (Z_to_bv 64 flags) eff mo = CheckOk mo' evs.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 216 arm_mremap.
  split; [tauto|]. intros H. split; [exact (proj1 (proj2 (check_mremap_shape _ _ _ _ _ _ _ _ H)))| exact H].
Qed.

(* [comment removed for export] *)
Definition mm_node (n : node) : Prop :=
  match n with
  | NBrk _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ _ => True
  | NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false
  | _ => False
  end.

Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  mm_node n -> nstep n mo eff mo' evs -> vm_shape mo mo' /\ evs = [].
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction.
  - apply nstep_brk_iff in H. pose proof (check_brk_shape _ _ _ _ _ H). tauto.
  - apply nstep_mmap_iff in H. pose proof (check_mmap_shape _ _ _ _ _ _ _ _ _ _ Hn H). tauto.
  - apply nstep_munmap_iff in H. pose proof (check_munmap_shape _ _ _ _ _ _ H). tauto.
  - apply nstep_mprotect_iff in H. pose proof (check_mprotect_shape _ _ _ _ _ _ _ H). tauto.
  - apply nstep_mremap_iff in H. pose proof (check_mremap_shape _ _ _ _ _ _ _ _ H). tauto.
Qed.

(* [comment removed for export] *)
Lemma nsafe_mmap_rw : forall addr len mo,
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros. cbn [nsafe]. split; [reflexivity|]. unfold mmap_safe_b. destruct (w_is0 _); reflexivity. Qed.

Lemma nsafe_mmap_none : forall addr len mo,
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros. cbn [nsafe]. split; [reflexivity|]. unfold mmap_safe_b. destruct (w_is0 _); reflexivity. Qed.

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
Definition lazy_free_node (n : node) : Prop :=
  match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end.

Lemma minv_preserved : forall n mo eff mo' evs,
  lazy_free_node n ->
  minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hlf Hminv Hh H.
  assert (MM : mm_node n -> m_halted mo' = None /\ minv mo').
  { intros Hmm. destruct (nstep_mm_vm_only n mo eff mo' evs Hmm H) as [Hv _].
    split; [destruct Hv as [(_ & _ & -> & _) _]; exact Hh | eapply minv_vm_shape; eassumption]. }
  destruct n.
  - destruct H as [-> _]; auto.
  - destruct H as [-> _]; auto.
  - eapply open_pres; eassumption.
  - eapply read_pres; eassumption.
  - destruct H as (_ & Hfd & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
    split; [macc; exact Hh|]. apply minv_remove; assumption.
  - destruct H as (_ & _ & ->); auto.
  - destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; auto.
    split; [macc; exact Hh|]. apply minv_with_tid; assumption.
  - destruct H.
  - apply MM. exact I.
  - apply MM. exact Hlf.
  - apply MM. exact I.
  - apply MM. exact I.
  - apply MM. exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma all_facts : forall n ms mo,
  match n with NExit _ => False | _ => True end ->
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
  - apply brk_facts; assumption.
  - apply mmap_facts; assumption.
  - apply munmap_facts; assumption.
  - apply mprotect_facts; assumption.
  - apply mremap_facts; assumption.
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
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros segs n ms mo Hne Hat Hminv Hh Hsafe.
  destruct (all_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (x8 & Hsvc & Hcmp & Hsnd & Hnu & Hpres).
  destruct (node_kit segs ms mo x8 (nstep n mo) Hsvc Hh Hcmp Hsnd Hnu) as (Hc & Hs & Hp).
  { intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. split; [exact H1| exact (minv_lazy _ H2)]. }
  split; [exact Hc|]. split; [|exact Hp].
  intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. auto.
Qed.

Theorem nodes_sound : forall segs, node_sound node segs (at_node segs) nstep nexit minv nsafe.
Proof.
  intros segs. constructor.
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
    + destruct (exit_node_facts segs ms mo c Hat Hh) as [Hc _]. destruct (Hc _ _ Hst) as [-> ->].
      right. eexists _, _. split; [reflexivity|]. split; [split; reflexivity|]. rewrite m_fs_with_halted. reflexivity.
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (Hc & _ & _). left. exact (Hc _ _ Hst).
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs Hat Hh Hminv Hsafe HP.
    assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct HP]).
    destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & Hs & _). exact (Hs _ _ _ HP).
  - (* [comment removed for export] *)
    intros n ms mo code mo' Hat Hh Hminv Hsafe HX.
    destruct n as [| | | | | | |c| | | | |]; try contradiction. cbn [nexit] in HX. destruct HX as [-> ->].
    split; [rewrite m_halted_with_halted; reflexivity|].
    pose proof (proj2 (exit_node_facts segs ms mo c Hat Hh)) as E. unfold exit_code in E.
    rewrite m_fs_with_halted. exact E.
  - (* [comment removed for export] *)
    intros n ms mo Hat Hh Hminv Hsafe.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. split; reflexivity.
    + destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & _ & Hp). left. exact Hp.
  - (* [comment removed for export] *)
    exact minv_lazy.
Qed.

End RC__2.
