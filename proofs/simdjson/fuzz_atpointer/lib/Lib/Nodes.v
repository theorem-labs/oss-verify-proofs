(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState Mem Exec ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Export Zp4.
From OssFuzzTheorems.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Export Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

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

Lemma word_to_nat_of_nat : forall n, Z.of_nat n < 2^64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof. intros. unfold word_to_nat. rewrite unsigned_lit by lia. lia. Qed.

Lemma read_bytes_map_bytes_in : forall bs mp a,
  bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
  read_bytes_map mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = Some bs.
Proof.
  intros bs mp a H Hl. rewrite read_bytes_map_eq. rewrite word_to_nat_of_nat by exact Hl.
  apply read_bytes_aux_bytes_in, H.
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

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

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
  -
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
| NMprotect (addr len prot : Z).

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
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 0x800000000000 /\
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
      0 < count <= 0x7ffff000 /\
      buf + count <= 0x800000000000 /\
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

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition strip (eff : resp) : resp :=
  mkEffectU (eff_ret eff) (eff_writes eff) (eff_zeros eff) (eff_unmaps eff) (eff_copies eff) [].

Lemma nret_strip : forall ms eff, nret ms (strip eff) = nret ms eff.
Proof. reflexivity. Qed.

Lemma strip_mkEffect : forall r ws zs, strip (mkEffect r ws zs) = mkEffect r ws zs.
Proof. reflexivity. Qed.

Lemma strip_with_copyins : forall R eff, strip (with_copyins R eff) = strip eff.
Proof. reflexivity. Qed.

Lemma strip_strip : forall eff, strip (strip eff) = strip eff.
Proof. reflexivity. Qed.

Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
  (exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
  \/ (let fd := alloc_fd (m_fds mo) in
      fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
      mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition kernel_placed (flags : Z) : bool := Z.land flags MAP_FIXED =? 0.

Definition mm_ok (n : node) (i : SyscallInput) (mo : Model) (eff : resp) : Prop :=
  match n with
  | NBrk _ => ~ spurious_refusal_cfg ACFG i mo eff
  | NMmap _ _ _ flags =>
      if kernel_placed flags then ret_in_errnos mmap_errnos (eff_ret eff) = false
      else ~ spurious_refusal_cfg ACFG i mo eff
  | NMprotect _ _ _ => ret_in_errnos mprotect_errnos (eff_ret eff) = false
  | _ => True
  end.

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NWritev fd bufs =>
      mo' = mo /\
      ((concat bufs = [] /\ eff = eff0 (Z_to_bv 64 0) /\ evs = [])
       \/ (exists k, (1 <= k <= length (concat bufs))%nat /\
             eff = eff0 (Z_to_bv 64 (Z.of_nat k)) /\
             evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k (concat bufs))))
  | NOpen path =>
      evs = [] /\
      (if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
       else match path with
            | [] => eff = efferr ENOENT /\ mo' = mo
            | _ :: _ =>
                if path_eqb path dot_path then open_result mo FdDir eff mo'
                else match fs_lookup (m_fs mo) path with
                     | Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
                     | None => eff = efferr ENOENT /\ mo' = mo
                     end
            end)
  | NRead fd buf count =>
      evs = [] /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | None => eff = efferr EBADF /\ mo' = mo
      | Some FdDir => eff = efferr EISDIR /\ mo' = mo
      | Some (FdFile p off) =>
          match fs_lookup (m_fs mo) p with
          | Some d =>
              eff = mkEffect (len_word (file_read d off (Z_to_bv 64 count)))
                             (delivered_writes (Z_to_bv 64 buf) (file_read d off (Z_to_bv 64 count))) [] /\
              mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd)
                                (FdFile p (off + len_word (file_read d off (Z_to_bv 64 count)))%bv)) mo
          | None => False
          end
      | Some _ => False
      end
  | NClose fd =>
      evs = [] /\ 3 <= fd < 2^32 /\
      match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
      | Some _ => eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
      | None => eff = efferr EBADF /\ mo' = mo
      end
  | NIoctl _ _ => evs = [] /\ eff = efferr ENOTTY /\ mo' = mo
  | NSetTid =>
      evs = [] /\
      exists t, eff = eff0 t /\
        match m_tid mo with
        | Some t0 => t = t0 /\ mo' = mo
        | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
        end
  | NExit _ => False
  | NBrk req =>
      evs = [] /\ syscall_spec (pure_input 214 [Z_to_bv 64 req]) mo (Ok eff mo' evs) /\
      mm_ok n (pure_input 214 [Z_to_bv 64 req]) mo eff
  | NMmap addr len prot flags =>
      evs = [] /\
      syscall_spec (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                                    Z_to_bv 64 (-1); Z_to_bv 64 0]) mo (Ok eff mo' evs) /\
      mm_ok n (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                               Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff
  | NMunmap addr len =>
      evs = [] /\ syscall_spec (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo (Ok eff mo' evs)
  | NMprotect addr len prot =>
      evs = [] /\
      syscall_spec (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo (Ok eff mo' evs) /\
      mm_ok n (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo eff
  end.

Definition unforced (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ flags => kernel_placed flags = true -> exists eff mo' evs, nstep n mo eff mo' evs
  | NMprotect _ _ _ => exists eff mo' evs, nstep n mo eff mo' evs
  | _ => True
  end.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  match n with
  | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
  | _ => False
  end.

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
  (forall k rd wr, fd_lookup (m_fds mo) k <> Some (FdDevNull rd wr)) /\
  (forall k, fd_lookup (m_fds mo) k <> Some FdUrandom) /\
  m_vm_lazy mo = [] /\
  m_vm_materialized mo = [].

Lemma minv_init : forall reserved brk mbase sp lim inp, minv (init_model reserved brk mbase sp lim inp).
Proof.
  intros. unfold minv. rewrite m_fds_init_model, m_fs_init_model, m_tid_init_model.
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
  - intros k p off H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k p off H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k p off H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k s H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k i w H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k rd wr H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k H. cbn [fd_lookup] in H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
Qed.

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

Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  negb (mmap_noreserve_b flags) &&
  (if negb (mmap_off_aligned_b off) then mmap_pglen_ok_b len
   else if negb (mmap_anon_b flags) then false
   else if w_is0 len then mmap_plain_anon_b flags
   else if mmap_modeled_b prot flags off then true
   else if mmap_noaccess_b prot flags off then true
   else if mmap_fixed_noaccess_b prot flags off then
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

Definition nsafeU (n : node) (mo : Model) : Prop := nsafe n mo /\ unforced n mo.

Lemma nsafeU_nsafe : forall n mo, nsafeU n mo -> nsafe n mo.
Proof. intros n mo Both. exact (proj1 Both). Qed.

Section Generic.
Variable segs : list Segment.

Lemma sstep_svc_inv : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\
                  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
                  X = SNext (mkCfg (nret ms eff) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\
                  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\
                  evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Pend Stp.
  pose proof (sstep_cfg_sys_inv segs ACFG ms mo x8 evs X Pend Stp) as Cases. cbv zeta in Cases.
  destruct Cases as [Ran | [Halts | [Kills | Unm]]].
  - destruct Ran as (eff & m1 & l1 & Sp & NoSp & Run1 & Tail).
    destruct (materialize_model_accesses m1 (syscall_effect_accesses eff)) as [m2|] eqn:MatEq;
      destruct Tail as [EvEq Nx].
    + left. rewrite EvEq. exists eff, m1, m2.
      split; [exact Sp|]. split; [exact NoSp|]. split; [exact Run1|]. split; [exact MatEq|]. exact Nx.
    + right; left. exists eff, m1, l1.
      split; [exact Sp|]. split; [exact NoSp|]. split; [exact Run1|]. split; [exact MatEq|].
      split; [exact EvEq| exact Nx].
  - right; right; left. destruct Halts as (eff & m1 & l1 & code & Sp & Halt & _ & EvEq & Nx).
    exists eff, m1, l1, code. split; [exact Sp|]. split; [exact Halt|]. split; [exact EvEq| exact Nx].
  - right; right; right; left. destruct Kills as (eff & m1 & l1 & sig & Sp & Kill & EvEq & Nx).
    exists eff, m1, l1, sig. split; [exact Sp|]. split; [exact Kill|]. split; [exact EvEq| exact Nx].
  - right; right; right; right. exact Unm.
Qed.

Lemma killed_not_running : forall mo sig, m_killed mo = Some sig -> m_halted mo <> None.
Proof. intros mo sig Hk Hh. rewrite (m_killed_of_m_halted_none mo Hh) in Hk. discriminate. Qed.

Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> nstep n mo (strip eff) mo' evs) /\
  (forall rsp mo' evs, nstep n mo rsp mo' evs ->
      exists eff, strip eff = rsp /\ syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)) /\
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> m_halted mo' = None /\ minv mo').

Definition node_facts_f (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
      m_halted mo' = None /\
      (~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff -> nstep n mo (strip eff) mo' evs)) /\
  (forall rsp mo' evs, nstep n mo rsp mo' evs ->
      exists eff, strip eff = rsp /\ syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\
                  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff) /\
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
  (exists rsp mo' evs, nstep n mo rsp mo' evs) /\
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> minv mo').

Lemma minv_lazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof. intros mo H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))). Qed.

Lemma minv_materialized : forall mo, minv mo -> m_vm_materialized mo = [].
Proof. intros mo H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))))). Qed.

Definition vm_backed_bytes (h : VmMaps) : Z := live_bytes (vm_backed_maps h).

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma vm_backing_used_minv : forall mo, minv mo -> vm_backing_used mo = vm_backed_bytes (m_vmmaps mo).
Proof.
  intros mo H. unfold vm_backing_used, vm_backed_bytes. rewrite (minv_lazy mo H), (minv_materialized mo H).
  rewrite maps_subtract_all_nil. cbn [length Z.of_nat]. lia.
Qed.

Definition node_props (ms : machine_state) (mo : Model) (n : node) : Prop :=
  (forall (evs : list event) (X : step_to), sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     exists (eff : resp) (mo' : Model), X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs) /\
  (forall (eff : resp) (mo' : Model) (evs : list event), nstep n mo eff mo' evs ->
     m_halted mo' = None /\ minv mo' /\ sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo'))) /\
  (exists (eff : resp) (mo' : Model) (evs : list event), nstep n mo eff mo' evs).

Lemma node_kit_f : forall ms mo n, node_facts_f ms mo n -> m_halted mo = None -> node_props ms mo n.
Proof.
  intros ms mo n Facts Run.
  destruct Facts as (x8 & Pend & Compl & Sound & NoUnm & Prog & Keep).
  split; [|split; [|exact Prog]].
  - intros evs X Stp.
    destruct (sstep_svc_inv ms mo x8 evs X Pend Stp)
      as [(eff & m1 & m2 & Sp & NoSp & _ & Mat & Nx)
         |[(eff & m1 & l1 & Sp & NoSp & _ & Mat & _ & _)
         |[(eff & m1 & l1 & code & Sp & Halt & _ & _)
         |[(eff & m1 & l1 & sig & Sp & Kill & _ & _)
         |(Unm & _ & _)]]]].
    + assert (Step1 : nstep n mo (strip eff) m1 evs) by exact (proj2 (Compl _ _ _ Sp) NoSp).
      rewrite (materialize_model_accesses_no_lazy m1 _ (minv_lazy m1 (Keep _ _ _ Step1))) in Mat.
      injection Mat as <-.
      exists (strip eff), m1. split; [rewrite nret_strip; exact Nx| exact Step1].
    + exfalso.
      assert (Step1 : nstep n mo (strip eff) m1 l1) by exact (proj2 (Compl _ _ _ Sp) NoSp).
      rewrite (materialize_model_accesses_no_lazy m1 _ (minv_lazy m1 (Keep _ _ _ Step1))) in Mat.
      discriminate Mat.
    + exfalso. rewrite (proj1 (Compl _ _ _ Sp)) in Halt. discriminate Halt.
    + exfalso. exact (killed_not_running m1 sig Kill (proj1 (Compl _ _ _ Sp))).
    + exfalso. exact (NoUnm Unm).
  - intros rsp m1 evs Step1.
    destruct (Sound _ _ _ Step1) as (eff & Strip & Sp & NoSp).
    pose proof (Keep _ _ _ Step1) as Inv1.
    pose proof (proj1 (Compl _ _ _ Sp)) as Run1.
    split; [exact Run1|]. split; [exact Inv1|].
    rewrite <- Strip, nret_strip.
    exact (sstep_cfg_syscall segs ACFG ms mo x8 eff m1 m1 evs Run Pend Sp NoSp Run1
             (materialize_model_accesses_no_lazy m1 _ (minv_lazy m1 Inv1))).
Qed.

Lemma node_kit : forall ms mo n,
  node_facts ms mo n -> m_halted mo = None ->
  (forall x8, ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false) ->
  node_props ms mo n.
Proof.
  intros ms mo n Facts Run Transp.
  apply node_kit_f; [|exact Run].
  destruct Facts as (x8 & Pend & Compl & Sound & NoUnm & Keep).
  assert (Clean : forall eff, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo eff).
  { intros eff. apply acfg_nonspurious_b. exact (Transp x8 Pend). }
  exists x8. split; [exact Pend|].
  split; [|split; [|split; [exact NoUnm|split]]].
  - intros eff m1 evs Sp. pose proof (Compl _ _ _ Sp) as Step1.
    split; [exact (proj1 (Keep _ _ _ Step1))|]. intros _. exact Step1.
  - intros rsp m1 evs Step1. destruct (Sound _ _ _ Step1) as (eff & Strip & Sp).
    exists eff. split; [exact Strip|]. split; [exact Sp| apply Clean].
  - pose proof (receptive (sys_input segs ms x8) mo) as Wit. revert Wit.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff m1 evs|]; intros Wit.
    + exists (strip eff), m1, evs. exact (Compl _ _ _ Wit).
    + exfalso. exact (NoUnm Wit).
  - intros rsp m1 evs Step1. exact (proj2 (Keep _ _ _ Step1)).
Qed.

Lemma exit_kit : forall ms mo x8 code,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
     o = Ok (eff0 (Z_to_bv 64 0)) (with_halted code mo) []) ->
  (forall evs X, sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
  /\ sstep_cfg segs ACFG (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
  intros ms mo x8 code Pend Run Char.
  pose proof (m_halted_with_halted code mo) as Halted.
  assert (OnlyOk : forall eff m1 l1, syscall_spec (sys_input segs ms x8) mo (Ok eff m1 l1) ->
                   m1 = with_halted code mo /\ l1 = []).
  { intros eff m1 l1 Sp. apply Char in Sp. injection Sp as _ M1 L1. split; assumption. }
  split.
  - intros evs X Stp.
    destruct (sstep_svc_inv ms mo x8 evs X Pend Stp)
      as [(eff & m1 & m2 & Sp & _ & Run1 & _ & _)
         |[(eff & m1 & l1 & Sp & _ & Run1 & _ & _ & _)
         |[(eff & m1 & l1 & c1 & Sp & Halt & EvEq & Nx)
         |[(eff & m1 & l1 & sig & Sp & Kill & _ & _)
         |(Unm & _ & _)]]]].
    + exfalso. destruct (OnlyOk _ _ _ Sp) as [M1 _]. rewrite M1, Halted in Run1. discriminate Run1.
    + exfalso. destruct (OnlyOk _ _ _ Sp) as [M1 _]. rewrite M1, Halted in Run1. discriminate Run1.
    + destruct (OnlyOk _ _ _ Sp) as [M1 L1]. subst m1 l1.
      rewrite Halted in Halt. injection Halt as <-.
      rewrite m_fs_with_halted in EvEq. split; [exact Nx| exact EvEq].
    + exfalso. destruct (OnlyOk _ _ _ Sp) as [M1 _]. rewrite M1, m_killed_with_halted in Kill.
      discriminate Kill.
    + exfalso. pose proof (proj1 (Char Unmodeled) Unm) as Bad. discriminate Bad.
  - assert (Sp : syscall_spec (sys_input segs ms x8) mo (Ok (eff0 (Z_to_bv 64 0)) (with_halted code mo) [])).
    { apply Char. reflexivity. }
    pose proof (sstep_cfg_exit segs ACFG ms mo x8 _ _ _ code Run Pend Sp Halted
                  (m_killed_with_halted code mo)) as Stp.
    rewrite m_fs_with_halted in Stp. exact Stp.
Qed.

End Generic.

Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma close_ebadf_outcome : forall fd i m o,
  fd_lookup (m_fds m) fd = None ->
  close_spec fd i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd i m o Hlk. unfold close_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma ioctl_ebadf_outcome : forall fd req i m o,
  fd_lookup (m_fds m) fd = None ->
  ioctl_spec fd req i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd req i m o Hlk. unfold ioctl_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Lemma set_tid_known_outcome : forall i m t0 o,
  m_tid m = Some t0 ->
  set_tid_address_spec i m o <-> o = Ok (mkEffect t0 [] []) m [].
Proof.
  intros i m t0 o Htid. unfold set_tid_address_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Htid. split; reflexivity.
Qed.

Lemma exit_outcome : forall code i m o,
  exit_spec code i m o <-> o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [].
Proof.
  intros code i m o. unfold exit_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma syscall_spec_93 : forall i m o,
  bv_unsigned (in_sysno i) = 93%Z ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_94 : forall i m o,
  bv_unsigned (in_sysno i) = 94%Z ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma read_ebadf_outcome : forall fd buf count i m o,
  fd_lookup (m_fds m) fd = None ->
  read_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EBADF) [] []) m [].
Proof.
  intros fd buf count i m o Hlk. unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk. split; reflexivity.
Qed.

Section PerNode.
Variable segs : list Segment.

Lemma facts_det : forall ms mo n x8 E mo1 evs1,
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok E mo1 evs1) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs <-> (rsp = strip E /\ mo' = mo1 /\ evs = evs1)) ->
  m_halted mo1 = None -> minv mo1 ->
  node_facts segs ms mo n.
Proof.
  intros ms mo n x8 E mo1 evs1 Hsvc Hchar Hn Hh1 Hm1. exists x8. split; [exact Hsvc|]. split; [|split; [|split]].
  - intros eff mo' evs Hsp. apply Hchar in Hsp. apply Ok_inj in Hsp as (-> & -> & ->). apply Hn. repeat split; reflexivity.
  - intros rsp mo' evs Hns. apply Hn in Hns as (-> & -> & ->). exists E. split; [reflexivity|]. apply Hchar. reflexivity.
  - intros Hsp. apply Hchar in Hsp. discriminate Hsp.
  - intros rsp mo' evs Hns. apply Hn in Hns as (-> & -> & ->). auto.
Qed.

Lemma unsigned_sysno : forall z, 0 <= z < 2^64 -> bv_unsigned (in_sysno (pure_input z [])) = z.
Proof. intros. cbn [in_sysno pure_input]. apply unsigned_lit. assumption. Qed.

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

Lemma minv_with_fds : forall mo fds',
  minv mo ->
  fd_lookup fds' (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  fd_lookup fds' (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  fd_lookup fds' (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (forall k e, fd_lookup fds' k = Some e ->
     fd_lookup (m_fds mo) k = Some e \/
     match e with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end) ->
  minv (with_fds fds' mo).
Proof.
  intros mo fds' (M0 & M1 & M2 & MC & MF & MW & MA & MR & MT & MS & MP & MN & MU & ML & MM) H0 H1 H2 Hnew.
  unfold minv.
  change (m_fds (with_fds fds' mo)) with fds'. change (m_fs (with_fds fds' mo)) with (m_fs mo).
  change (m_tid (with_fds fds' mo)) with (m_tid mo). change (m_vm_lazy (with_fds fds' mo)) with (m_vm_lazy mo).
  change (m_vm_materialized (with_fds fds' mo)) with (m_vm_materialized mo).
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  split; [|split; [|split; [|split; [|split; [|split; [exact MT|split; [|split; [|split; [|split; [|split; [exact ML| exact MM]]]]]]]]]]].
  - intros k c Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MC _ _ H)|destruct H].
  - intros k p off Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MF _ _ _ H)|exact H].
  - intros k p off Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MW _ _ _ H)|destruct H].
  - intros k p off Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MA _ _ _ H)|destruct H].
  - intros k p off Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MR _ _ _ H)|destruct H].
  - intros k s Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MS _ _ H)|destruct H].
  - intros k i w Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MP _ _ _ H)|destruct H].
  - intros k rd wr Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MN _ _ _ H)|destruct H].
  - intros k Hk. destruct (Hnew _ _ Hk) as [H|H]; [exact (MU _ H)|destruct H].
Qed.

Lemma minv_open_insert : forall mo ent,
  minv mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
  intros mo ent Hminv Hfree Hent. pose proof Hminv as (M0 & M1 & M2 & _).
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
  - intros H. inversion H; subst. right. exact Hent.
  - intros H. left. exact H.
Qed.

Lemma minv_update_file : forall mo k p off off',
  minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
  minv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros mo k p off off' Hminv Hk. pose proof Hminv as (M0 & M1 & M2 & MC & MF & _).
  assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
  { intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_insert;
    rewrite ?(Hne _ _ M0), ?(Hne _ _ M1), ?(Hne _ _ M2); try assumption.
  intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k').
  - intros H. inversion H; subst. right. exact (MF _ _ _ Hk).
  - intros H. left. exact H.
Qed.

Lemma minv_remove : forall mo fd, minv mo -> 3 <= fd < 2^32 ->
  minv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
  intros mo fd Hminv Hfd. pose proof Hminv as (M0 & M1 & M2 & _).
  assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
  { intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  apply minv_with_fds; [exact Hminv| | | |]; rewrite ?fd_lookup_remove; rewrite ?Hne by lia; try assumption.
  intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate|]. intros H. left. exact H.
Qed.

Lemma m_fds_with_tid : forall mo t, m_fds (with_tid t mo) = m_fds mo. Proof. reflexivity. Qed.
Lemma m_fs_with_tid : forall mo t, m_fs (with_tid t mo) = m_fs mo. Proof. reflexivity. Qed.
Lemma m_tid_with_tid : forall mo t, m_tid (with_tid t mo) = Some t. Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_tid : forall mo t, m_vm_lazy (with_tid t mo) = m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma m_halted_with_tid : forall mo t, m_halted (with_tid t mo) = m_halted mo. Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_tid : forall mo t, m_vm_materialized (with_tid t mo) = m_vm_materialized mo. Proof. reflexivity. Qed.

Lemma minv_with_tid : forall mo t, minv mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minv (with_tid t mo).
Proof.
  intros mo t (M0 & M1 & M2 & MC & MF & MW & MA & MR & MT & MS & MP & MN & MU & ML & MM) Ht. unfold minv.
  rewrite m_fds_with_tid, m_fs_with_tid, m_tid_with_tid, m_vm_lazy_with_tid, m_vm_materialized_with_tid.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|].
  split; [exact MW|]. split; [exact MA|]. split; [exact MR|]. split; [|split; [exact MS| split; [exact MP| split; [exact MN| split; [exact MU| split; [exact ML| exact MM]]]]]].
  intros t' Heq. inversion Heq; subst. lia.
Qed.

Lemma std_chan : forall mo fd, minv mo -> (fd = 1 \/ fd = 2) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) /\
  w_is0 (Z_to_bv 64 fd) = false.
Proof.
  intros mo fd (M0 & M1 & M2 & _) [-> | ->]; split; first [exact M1 | exact M2 | reflexivity].
Qed.

Lemma minv_fd_cases : forall mo k e,
  minv mo -> fd_lookup (m_fds mo) k = Some e ->
  (exists c, e = FdChannel c /\ bv_unsigned k < 3) \/ e = FdDir \/
  (exists p off d, e = FdFile p off /\ fs_lookup (m_fs mo) p = Some d).
Proof.
  intros mo k e (M0 & M1 & M2 & MC & MF & MW & MA & MR & MT & MS & MP & MN & MU & ML & MM) Hk.
  destruct e as [c|p off|p off|p off|p off| |s|i w|rd wr| ].
  - left. exists c. split; [reflexivity| exact (MC _ _ Hk)].
  - right; right. destruct (fs_lookup (m_fs mo) p) as [d|] eqn:E.
    + exists p, off, d. auto.
    + exfalso. exact (MF _ _ _ Hk E).
  - exfalso. exact (MW _ _ _ Hk).
  - exfalso. exact (MA _ _ _ Hk).
  - exfalso. exact (MR _ _ _ Hk).
  - right; left. reflexivity.
  - exfalso. exact (MS _ _ Hk).
  - exfalso. exact (MP _ _ _ Hk).
  - exfalso. exact (MN _ _ _ Hk).
  - exfalso. exact (MU _ Hk).
Qed.

Lemma close_facts : forall ms mo fd,
  at_node segs (NClose fd) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NClose fd).
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
  assert (Hd : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 57)) mo o <->
                         close_spec (Z_to_bv 64 fd) (sys_input segs ms (Z_to_bv 64 57)) mo o).
  { intros o. rewrite syscall_spec_57 by reflexivity. rewrite in_a0_si, Ha0.
    rewrite fd32_id by (rewrite unsigned_lit; lia). reflexivity. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - apply (facts_det ms mo _ (Z_to_bv 64 57) (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []);
      [exact Hsvc | | | exact Hh | apply minv_remove; [exact Hminv| exact Hfd]].
    + intros o. rewrite Hd. apply (close_outcome _ _ _ _ _ Hlk).
    + intros rsp mo' evs. cbn [nstep]. rewrite Hlk. unfold eff0. rewrite strip_mkEffect. tauto.
  - apply (facts_det ms mo _ (Z_to_bv 64 57) (mkEffect (errno_ret EBADF) [] []) mo []); [exact Hsvc | | | exact Hh | exact Hminv].
    + intros o. rewrite Hd. apply (close_ebadf_outcome _ _ _ _ Hlk).
    + intros rsp mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. rewrite strip_mkEffect. tauto.
Qed.

Lemma ioctl_facts : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NIoctl fd req).
Proof.
  intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh. subst req.
  pose proof Hminv as (M0 & M1 & M2 & _).
  assert (Hl : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
  { assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
  destruct Hl as [e Hlk].
  apply (facts_det ms mo _ (Z_to_bv 64 29) (mkEffect (errno_ret ENOTTY) [] []) mo []); [exact Hsvc | | | exact Hh | exact Hminv].
  - intros o. rewrite syscall_spec_29 by reflexivity. rewrite in_a0_si, in_a1_si, Ha0, Ha1.
    rewrite fd32_id by (rewrite unsigned_lit; lia).
    apply (ioctl_tty_outcome _ _ _ _ _ _ Hlk); [discriminate|discriminate|]. vm_compute. reflexivity.
  - intros rsp mo' evs. cbn [nstep]. unfold efferr, eff0. rewrite strip_mkEffect. tauto.
Qed.

Lemma set_tid_facts : forall ms mo,
  at_node segs NSetTid ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo NSetTid.
Proof.
  intros ms mo Hsvc Hminv Hh.
  destruct (m_tid mo) as [t0|] eqn:Htid.
  - apply (facts_det ms mo _ (Z_to_bv 64 96) (mkEffect t0 [] []) mo []); [exact Hsvc | | | exact Hh | exact Hminv].
    + intros o. rewrite syscall_spec_96 by reflexivity. apply (set_tid_known_outcome _ _ _ _ Htid).
    + intros rsp mo' evs. cbn [nstep]. rewrite Htid. unfold eff0. rewrite strip_mkEffect. split.
      * intros (-> & t & -> & -> & ->). repeat split; reflexivity.
      * intros (-> & -> & ->). split; [reflexivity|]. exists t0. repeat split; reflexivity.
  - exists (Z_to_bv 64 96). split; [exact Hsvc|].
    assert (Hchar : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 96)) mo o <->
              exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE) /\ o = Ok (mkEffect t [] []) (with_tid t mo) []).
    { intros o. rewrite syscall_spec_96 by reflexivity. apply (set_tid_fresh_outcome _ _ _ Htid). }
    split; [|split; [|split]].
    + intros eff mo' evs Hsp. apply Hchar in Hsp as (t & Ht & Hsp). apply Ok_inj in Hsp as (-> & -> & ->).
      cbn [nstep]. rewrite Htid. split; [reflexivity|]. exists t. rewrite strip_mkEffect. unfold eff0. auto.
    + intros rsp mo' evs Hn. cbn [nstep] in Hn. rewrite Htid in Hn. destruct Hn as (-> & t & -> & Ht & ->).
      exists (mkEffect t [] []). split; [reflexivity|]. apply Hchar. exists t. auto.
    + intros Hsp. apply Hchar in Hsp as (t & _ & Hsp). discriminate Hsp.
    + intros rsp mo' evs Hn. cbn [nstep] in Hn. rewrite Htid in Hn. destruct Hn as (-> & t & -> & Ht & ->).
      split; [exact Hh|]. apply minv_with_tid; assumption.
Qed.

Lemma exit_char : forall ms mo c x8,
  at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 ->
  forall o, syscall_spec (sys_input segs ms x8) mo o <->
    o = Ok (eff0 (Z_to_bv 64 0)) (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) mo) [].
Proof.
  intros ms mo c x8 [Hsvc Ha0] Hx8 o.
  destruct Hsvc as [Hsvc|Hsvc]; rewrite Hsvc in Hx8; inversion Hx8; subst.
  - rewrite syscall_spec_93 by reflexivity. rewrite in_a0_si, Ha0. apply exit_outcome.
  - rewrite syscall_spec_94 by reflexivity. rewrite in_a0_si, Ha0. apply exit_outcome.
Qed.

End PerNode.

Section PerNode2.
Variable segs : list Segment.

Lemma facts_open_out : forall ms mo n x8 R ent,
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
             open_out R mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) o) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs <-> (evs = [] /\ open_result mo ent rsp mo')) ->
  m_halted mo = None -> minv mo ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  node_facts segs ms mo n.
Proof.
  intros ms mo n x8 R ent Hsvc Hchar Hn Hh Hminv Hent. exists x8. split; [exact Hsvc|].
  split; [|split; [|split]].
  - intros eff mo' evs Hsp. apply Hchar in Hsp. apply Hn.
    destruct Hsp as [(e & He & Hsp) | (Hfree & Hsp)]; apply Ok_inj in Hsp as (-> & -> & ->);
      rewrite strip_with_copyins, strip_mkEffect; split; [reflexivity| |reflexivity|].
    + left. exists e. unfold efferr, eff0. auto.
    + right. unfold eff0. auto.
  - intros rsp mo' evs Hns. apply Hn in Hns as [-> [(e & He & -> & ->) | (Hfree & -> & ->)]].
    + exists (with_copyins R (mkEffect (errno_ret e) [] [])). split; [reflexivity|]. apply Hchar. left. exists e. auto.
    + exists (with_copyins R (mkEffect (alloc_fd (m_fds mo)) [] [])). split; [reflexivity|]. apply Hchar. right. auto.
  - intros Hsp. apply Hchar in Hsp. destruct Hsp as [(e & _ & Hsp) | (_ & Hsp)]; discriminate Hsp.
  - intros rsp mo' evs Hns. apply Hn in Hns as [-> [(e & He & -> & ->) | (Hfree & -> & ->)]].
    + auto.
    + split; [exact Hh|]. apply minv_open_insert; assumption.
Qed.

Lemma AT_FDCWD32_eq : fd32 (Z_to_bv 64 (-100)) = AT_FDCWD32.
Proof. reflexivity. Qed.

Lemma open_facts : forall ms mo path,
  at_node segs (NOpen path) ms -> minv mo -> m_halted mo = None -> nsafe (NOpen path) mo ->
  node_facts segs ms mo (NOpen path).
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hrom & Hp) Hminv Hh [Hsl Hdd].
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  set (i := sys_input segs ms (Z_to_bv 64 56)).
  assert (Hmf : modeled_open_flags (areg ms 12) = true) by (apply modeled_open_flags_rd; exact Hfl).
  assert (Hsp : forall o, syscall_spec i mo o <-> openat_spec AT_FDCWD32 (areg ms 11) (areg ms 12) i mo o).
  { intros o. subst i. rewrite syscall_spec_56 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0.
    rewrite AT_FDCWD32_eq. reflexivity. }
  assert (Hmem : in_mem i = ms_read_byte ms) by reflexivity.
  rewrite <- (wa_unsigned_id (areg ms 11)) in Hsp.
  destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
  -
    assert (Hc : read_cstr (in_mem i) (wa (bv_unsigned (areg ms 11))) = CstrTooLong).
    { unfold read_cstr. rewrite Hmem. apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [Hin _]. exact Hin. }
    apply (facts_det segs ms mo _ (Z_to_bv 64 56)
             (with_copyins (open_reads i (wa (bv_unsigned (areg ms 11)))) (mkEffect (errno_ret ENAMETOOLONG) [] [])) mo []);
      [exact Hsvc | | | exact Hh | exact Hminv].
    + intros o. fold i. rewrite Hsp. apply (openat_toolong_outcome _ _ _ _ _ Hmf _ Hc).
    + intros rsp mo' evs. cbn [nstep]. replace (path_max <=? length path)%nat with true by (symmetry; apply Nat.leb_le; lia).
      rewrite strip_with_copyins, strip_mkEffect. unfold efferr, eff0. tauto.
  - assert (Hc : read_cstr (in_mem i) (wa (bv_unsigned (areg ms 11))) = CstrOk path).
    { unfold read_cstr. rewrite Hmem. apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hin]. }
    assert (Hcase : forall rsp mo' evs, nstep (NOpen path) mo rsp mo' evs <->
              (evs = [] /\ match path with
                           | [] => rsp = efferr ENOENT /\ mo' = mo
                           | _ => if path_eqb path dot_path then open_result mo FdDir rsp mo'
                                  else match fs_lookup (m_fs mo) path with
                                       | None => rsp = efferr ENOENT /\ mo' = mo
                                       | Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) rsp mo'
                                       end
                           end)).
    { intros rsp mo' evs. cbn [nstep]. replace (path_max <=? length path)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      reflexivity. }
    destruct path as [|c path'].
    +
      apply (facts_det segs ms mo _ (Z_to_bv 64 56)
               (with_copyins (open_reads i (wa (bv_unsigned (areg ms 11)))) (mkEffect (errno_ret ENOENT) [] [])) mo []);
        [exact Hsvc | | | exact Hh | exact Hminv].
      * intros o. fold i. rewrite Hsp. apply (openat_empty_outcome _ _ _ _ _ Hmf _ Hc).
      * intros rsp mo' evs. rewrite Hcase. rewrite strip_with_copyins, strip_mkEffect. unfold efferr, eff0. tauto.
    + assert (Hne : c :: path' <> []) by discriminate.
      destruct (path_eqb (c :: path') dot_path) eqn:Hdot.
      *
        apply path_eqb_eq in Hdot.
        apply (facts_open_out ms mo _ (Z_to_bv 64 56) (open_reads i (wa (bv_unsigned (areg ms 11)))) FdDir);
          [exact Hsvc | | | exact Hh | exact Hminv | exact I].
        -- intros o. fold i. rewrite Hsp. apply (openat_dot_outcome _ _ _ _ _ Hmf eq_refl Hfl). rewrite Hc, Hdot. reflexivity.
        -- intros rsp mo' evs. rewrite Hcase. reflexivity.
      * assert (Hnd : path_is_dirref (c :: path') = false).
        { unfold path_is_dirref. rewrite Hdot, Hdd. reflexivity. }
        destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Hfs.
        -- apply (facts_open_out ms mo _ (Z_to_bv 64 56) (open_reads i (wa (bv_unsigned (areg ms 11)))) (FdFile (c :: path') (Z_to_bv 64 0)));
             [exact Hsvc | | | exact Hh | exact Hminv | cbn; congruence].
           ++ intros o. fold i. rewrite Hsp. apply (openat_file_outcome _ _ _ _ _ Hmf eq_refl Hfl _ d); assumption.
           ++ intros rsp mo' evs. rewrite Hcase. reflexivity.
        -- apply (facts_det segs ms mo _ (Z_to_bv 64 56)
                   (with_copyins (open_reads i (wa (bv_unsigned (areg ms 11)))) (mkEffect (errno_ret ENOENT) [] [])) mo []);
             [exact Hsvc | | | exact Hh | exact Hminv].
           ++ intros o. fold i. rewrite Hsp. apply (openat_absent_outcome _ _ _ _ _ Hmf eq_refl Hfl (c :: path')); assumption.
           ++ intros rsp mo' evs. rewrite Hcase. rewrite strip_with_copyins, strip_mkEffect. unfold efferr, eff0. tauto.
Qed.

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

Lemma read_facts : forall ms mo fd buf count,
  at_node segs (NRead fd buf count) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NRead fd buf count).
Proof.
  intros ms mo fd buf count (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hcnt & Hbuf & W) Hminv Hh.
  pose proof W as (Hb0 & Hc0 & _).
  set (i := sys_input segs ms (Z_to_bv 64 63)).
  assert (Hsp : forall o, syscall_spec i mo o <-> read_spec (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) i mo o).
  { intros o. subst i. rewrite syscall_spec_63 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_id by (rewrite unsigned_lit; lia). reflexivity. }
  assert (Hacc : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { apply access_okb_wr; unfold TASK_SIZE; lia. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - destruct (minv_fd_cases mo _ _ Hminv Hlk) as [(c & -> & Hk) | [-> | (p & off & d & -> & Hfs)]].
    + exfalso. rewrite unsigned_lit in Hk by lia. lia.
    +
      apply (facts_det segs ms mo _ (Z_to_bv 64 63) (mkEffect (errno_ret EISDIR) [] []) mo []);
        [exact Hsvc | | | exact Hh | exact Hminv].
      * intros o. fold i. rewrite Hsp. apply (read_dir_outcome _ _ _ _ _ _ Hlk Hacc).
      * intros rsp mo' evs. cbn [nstep]. rewrite Hlk. rewrite strip_mkEffect. unfold efferr, eff0. tauto.
    +
      set (bs := file_read d off (Z_to_bv 64 count)).
      assert (Hcl : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
      { rewrite rw_count_clamp_small by (unfold MAX_RW_COUNT; rewrite unsigned_lit; lia).
        apply Z_to_bv_bv_unsigned. }
      assert (Hlen : Z.of_nat (length bs) <= count).
      { subst bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
      destruct (wr_at_read_bytes_map ms buf count (len_word bs) W) as [w Hw].
      { unfold len_word. rewrite unsigned_lit; lia. }
      apply (facts_det segs ms mo _ (Z_to_bv 64 63) (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [])
               (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo) []);
        [exact Hsvc | | | exact Hh | eapply minv_update_file; eassumption].
      * intros o. fold i. rewrite Hsp.
        pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) i mo o p off d w Hlk Hacc Hfs) as R.
        rewrite Hcl in R. apply R. subst i. rewrite in_wmem_si. exact Hw.
      * intros rsp mo' evs. cbn [nstep]. rewrite Hlk, Hfs. rewrite strip_mkEffect. fold bs. tauto.
  -
    apply (facts_det segs ms mo _ (Z_to_bv 64 63) (mkEffect (errno_ret EBADF) [] []) mo []);
      [exact Hsvc | | | exact Hh | exact Hminv].
    + intros o. fold i. rewrite Hsp. apply (read_ebadf_outcome _ _ _ _ _ _ Hlk).
    + intros rsp mo' evs. cbn [nstep]. rewrite Hlk. rewrite strip_mkEffect. unfold efferr, eff0. tauto.
Qed.

End PerNode2.

Section PerNode3.
Variable segs : list Segment.

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

Lemma writev_facts : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minv mo -> m_halted mo = None -> node_facts segs ms mo (NWritev fd bufs).
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Hiotop & iovs & Hiov & Hbufs) Hminv Hh.
  unfold MAX_RW_COUNT in Htot.
  destruct (iovs_ok_of_at _ _ _ Hrom Hbufs ltac:(lia)) as [Hok HlenT].
  pose proof (Forall2_length Hbufs) as Hleq.
  destruct (std_chan mo fd Hminv Hfd) as [Hfdl Hw].
  set (i := sys_input segs ms (Z_to_bv 64 66)).
  set (bs := concat bufs).
  assert (Hsp : forall o, syscall_spec i mo o <->
            writev_spec (Z_to_bv 64 fd) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length iovs))) i mo o).
  { intros o. subst i. rewrite syscall_spec_66 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2, Hleq.
    rewrite fd32_id by (rewrite unsigned_lit; lia). reflexivity. }
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Himp : import_iovecs (in_mem i) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs)))) = ImpOk iovs).
  { rewrite Hcnt32. subst i. rewrite in_mem_si. rewrite <- (wa_unsigned_id (areg ms 11)).
    pose proof (bytes_at_in _ _ _ _ Hrom Hiov) as Hin.
    apply (import_iovecs_bytes_in iovs bufs); [exact Hin| exact HlenT| lia | unfold TASK_SIZE; lia | unfold MAX_RW_COUNT; lia]. }
  assert (Htotal : iovs_total iovs = Z.of_nat (length bs)) by (subst bs; eapply iovs_total_ok; exact Hok).
  assert (Hg : gather_iovecs (in_mem i) iovs = Some bs) by (subst i bs; rewrite in_mem_si; apply gather_iovecs_ok; exact Hok).
  set (CA := import_iovecs_accesses (in_mem i) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))))).
  destruct bs as [|b0 bs'] eqn:Ebs.
  -
    apply (facts_det segs ms mo _ (Z_to_bv 64 66) (with_copyins CA (mkEffect (Z_to_bv 64 0) [] [])) mo []);
      [exact Hsvc | | | exact Hh | exact Hminv].
    + intros o. fold i. rewrite Hsp.
      apply (writev_chan_zero_outcome _ _ _ i mo o (Z_to_bv 64 fd) iovs Hfdl Hw Himp).
      rewrite Htotal. reflexivity.
    + intros rsp mo' evs. cbn [nstep]. fold bs. rewrite Ebs. rewrite strip_with_copyins, strip_mkEffect. unfold eff0.
      split.
      * intros [-> [(_ & -> & ->) | (k & Hk & _)]]; [repeat split; reflexivity| cbn in Hk; lia].
      * intros (-> & -> & ->). split; [reflexivity|]. left. repeat split; reflexivity.
  -
    rewrite <- Ebs in *.
    assert (Hbs1 : (1 <= Z.of_nat (length bs))) by (rewrite Ebs; cbn [length]; lia).
    assert (Hchar : forall o, syscall_spec i mo o <->
              exists k, (1 <= k <= length bs)%nat /\
                o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
                       mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))).
    { intros o. rewrite Hsp.
      apply (writev_chan_outcome _ _ _ i mo o (Z_to_bv 64 fd) iovs bs Hfdl Hw Himp); [|exact Hg|exact Hbs1].
      rewrite Htotal. unfold MAX_RW_COUNT. subst bs. lia. }
    exists (Z_to_bv 64 66). split; [exact Hsvc|]. split; [|split; [|split]].
    + intros eff mo' evs Hs. apply Hchar in Hs as (k & Hk & Hs). apply Ok_inj in Hs as (-> & -> & ->).
      cbn [nstep]. fold bs. split; [reflexivity|]. right. exists k. split; [exact Hk|]. split; reflexivity.
    + intros rsp mo' evs [-> [(Hnil & _) | (k & Hk & -> & ->)]].
      { exfalso. fold bs in Hnil. rewrite Ebs in Hnil. discriminate. }
      exists (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k)).
      split; [reflexivity|]. apply Hchar. exists k. fold bs in Hk. split; [exact Hk| reflexivity].
    + intros Hs. apply Hchar in Hs as (k & _ & Hs). discriminate Hs.
    + intros rsp mo' evs [-> _]. auto.
Qed.

End PerNode3.

Section PerNode4.
Variable segs : list Segment.

Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
  m_tid m' = m_tid m /\ m_stdin m' = m_stdin m /\ (m_vm_lazy m = [] -> m_vm_lazy m' = [])
  /\ (m_vm_materialized m = [] -> m_vm_materialized m' = [])
  /\ alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).

Lemma vm_only_refl : forall m, vm_only m m.
Proof. intros m. repeat split; auto. Qed.

Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  unfold vm_only. rewrite B1, B2, B3, B4, B5, B8. repeat split; auto.
Qed.

Lemma vm_only_alloc_top : forall m m', vm_only m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof. intros m m' H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.

Lemma vm_only_with_vmmaps : forall h m,
  vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m (with_vmmaps h m).
Proof. intros h m H. repeat split; auto. unfold alloc_top. rewrite m_vmmaps_with_vmmaps, H. reflexivity. Qed.

Lemma maps_subtract_nil : forall lo hi, maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma vm_only_vm_forget_range : forall lo hi m, vm_only m (vm_forget_range lo hi m).
Proof.
  intros lo hi m. unfold vm_only, vm_forget_range, with_vm_backing.
  cbn [m_fds m_fs m_halted m_tid m_stdin m_vm_lazy m_vm_materialized m_fd m_fsys m_proc m_io m_vm fdst_table vmst_lazy vmst_materialized].
  repeat split; try reflexivity.
  - intros H. change (vmst_lazy (m_vm m)) with (m_vm_lazy m). rewrite H. reflexivity.
  - intros H. change (vmst_materialized (m_vm m)) with (m_vm_materialized m). rewrite H. reflexivity.
Qed.

Lemma vm_only_forget_vm_ranges : forall rs m, vm_only m (forget_vm_ranges rs m).
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges].
  - apply vm_only_refl.
  - eapply vm_only_trans; [apply vm_only_vm_forget_range| apply IH].
Qed.

Lemma vm_only_with_brk_next : forall m req r, vm_only m (with_brk_next m req r).
Proof.
  intros m req r. unfold with_brk_next. eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_forget_vm_ranges]. reflexivity.
Qed.

Lemma vm_only_with_mmap_backing : forall flags a n m,
  mmap_noreserve_b flags = false -> vm_only m (with_mmap_backing flags a n m).
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. apply vm_only_refl. Qed.

Lemma vm_only_with_mmap_replacement : forall flags a n m,
  mmap_noreserve_b flags = false -> vm_only m (with_mmap_replacement flags a n m).
Proof.
  intros flags a n m H. unfold with_mmap_replacement.
  eapply vm_only_trans; [apply vm_only_vm_forget_range| apply vm_only_with_mmap_backing; exact H].
Qed.

Lemma vm_only_with_mmap_destroyed : forall a n h m,
  vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m (with_mmap_destroyed a n h m).
Proof.
  intros a n h m H. unfold with_mmap_destroyed.
  eapply vm_only_trans; [apply vm_only_with_vmmaps; exact H| apply vm_only_vm_forget_range].
Qed.

Lemma vm_only_mprotect_model_next : forall m a n, vm_only m (mprotect_model_next m a n).
Proof. intros m a n. unfold mprotect_model_next. apply vm_only_with_vmmaps. reflexivity. Qed.

Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> minv mo -> minv mo'.
Proof.
  intros mo mo' (Hf & Hs & _ & Ht & _ & Hl & Hm & _) (M0 & M1 & M2 & MC & MF & MW & MA & MR & MT & MS & MP & MN & MU & ML & MM).
  unfold minv. rewrite Hf, Hs, Ht.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|].
  split; [exact MW|]. split; [exact MA|]. split; [exact MR|]. split; [exact MT|]. split; [exact MS|]. split; [exact MP|]. split; [exact MN|]. split; [exact MU| split; [exact (Hl ML)| exact (Hm MM)]].
Qed.

Ltac crush_check H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (? & ? & ?); subst
          | (match ?x with _ => _ end) = _ => destruct x eqn:?
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).

Lemma vmo_with_vmmaps : forall m0 h m,
  vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m0 m -> vm_only m0 (with_vmmaps h m).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_with_vmmaps; assumption]. Qed.
Lemma vmo_vm_forget_range : forall m0 lo hi m, vm_only m0 m -> vm_only m0 (vm_forget_range lo hi m).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_vm_forget_range]. Qed.
Lemma vmo_forget_vm_ranges : forall m0 rs m, vm_only m0 m -> vm_only m0 (forget_vm_ranges rs m).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_forget_vm_ranges]. Qed.
Lemma vmo_with_brk_next : forall m0 m req r, vm_only m0 m -> vm_only m0 (with_brk_next m req r).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_with_brk_next]. Qed.
Lemma vmo_with_mmap_backing : forall m0 flags a n m,
  mmap_noreserve_b flags = false -> vm_only m0 m -> vm_only m0 (with_mmap_backing flags a n m).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_with_mmap_backing; assumption]. Qed.
Lemma vmo_with_mmap_replacement : forall m0 flags a n m,
  mmap_noreserve_b flags = false -> vm_only m0 m -> vm_only m0 (with_mmap_replacement flags a n m).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_with_mmap_replacement; assumption]. Qed.
Lemma vmo_with_mmap_destroyed : forall m0 a n h m,
  vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m0 m -> vm_only m0 (with_mmap_destroyed a n h m).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_with_mmap_destroyed; assumption]. Qed.
Lemma vmo_mprotect_model_next : forall m0 m a n, vm_only m0 m -> vm_only m0 (mprotect_model_next m a n).
Proof. intros. eapply vm_only_trans; [eassumption| apply vm_only_mprotect_model_next]. Qed.

Ltac vmo_sp :=
  cbv beta delta [mmap_fixed_destroyed_next mmap_fixed_noaccess_span_next mmap_fixed_rw_next
                  mmap_fixed_rw_span_next brk_model_next];
  cbn [vm_init_sp];
  first [ reflexivity
        | rewrite ?m_vmmaps_with_vmmaps; cbn [vm_init_sp]; reflexivity ].

Ltac vmo :=
  lazymatch goal with
  | |- vm_only ?m ?m => apply vm_only_refl
  | |- vm_only _ (with_vmmaps _ _) => apply vmo_with_vmmaps; [vmo_sp| vmo]
  | |- vm_only _ (vm_forget_range _ _ _) => apply vmo_vm_forget_range; vmo
  | |- vm_only _ (forget_vm_ranges _ _) => apply vmo_forget_vm_ranges; vmo
  | |- vm_only _ (with_brk_next _ _ _) => apply vmo_with_brk_next; vmo
  | |- vm_only _ (with_mmap_backing _ _ _ _) => apply vmo_with_mmap_backing; [assumption| vmo]
  | |- vm_only _ (with_mmap_replacement _ _ _ _) => apply vmo_with_mmap_replacement; [assumption| vmo]
  | |- vm_only _ (with_mmap_destroyed _ _ _ _) => apply vmo_with_mmap_destroyed; [vmo_sp| vmo]
  | |- vm_only _ (mprotect_model_next _ _ _) => apply vmo_mprotect_model_next; vmo
  | |- vm_only _ _ => apply vm_only_refl
  end.

Ltac vm_only_done := split; [ vmo | split; reflexivity ].

Lemma check_brk_shape : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> vm_only m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros req eff m m' evs H. unfold check_brk in H. crush_check H; vm_only_done. Qed.

Lemma check_mmap_shape : forall addr len prot flags fd off eff m m' evs,
  mmap_noreserve_b flags = false ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_only m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros Hnr H. unfold check_mmap in H. crush_check H; vm_only_done. Qed.

Lemma check_munmap_shape : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> vm_only m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros H. unfold check_munmap in H. crush_check H; vm_only_done. Qed.

Lemma check_mprotect_shape : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> vm_only m m' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros until evs; intros H. unfold check_mprotect in H. crush_check H; vm_only_done. Qed.

End PerNode4.

Ltac dispatch L :=
  rewrite L by reflexivity;
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

Ltac dispatch_pure L :=
  rewrite L by reflexivity; cbn [in_arg in_args nth pure_input].

Section PerNode5.
Variable segs : list Segment.

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

Lemma mmap_safe_no_unmodeled : forall addr len prot flags fd off eff m,
  mmap_safe_b addr len prot flags fd off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros addr len prot flags fd off eff m. unfold mmap_safe_b, check_mmap.
  destruct (mmap_noreserve_b flags); [discriminate|]. cbn [negb andb].
  destruct (mmap_off_aligned_b off); cbn [negb].
  2:{ intros ->. apply check_ret_only_no_unmodeled. }
  destruct (mmap_anon_b flags); cbn [negb]; [|discriminate].
  destruct (w_is0 len).
  { intros ->. apply check_ret_only_no_unmodeled. }
  destruct (mmap_modeled_b prot flags off); [intros _; no_unm|].
  destruct (mmap_noaccess_b prot flags off); [intros _; no_unm|].
  assert (Hfixed : forall X Y Z : check_result,
    X <> CheckUnmodeled -> Y <> CheckUnmodeled -> Z <> CheckUnmodeled ->
    (let nZ := page_round_up_Z (bv_unsigned len) in
     let n := Z_to_bv 64 nZ in
     if two_pow_64 <=? bv_unsigned addr + nZ then true
     else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)) then false
     else if negb (bv_unsigned addr mod page_size =? 0) then true
     else if negb (0 <? bv_unsigned addr) then false
     else region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n
          || region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
          || region_free (vm_reserved (m_vmmaps m)) addr n) = true ->
    (let nZ := page_round_up_Z (bv_unsigned len) in
     if two_pow_64 <=? bv_unsigned addr + nZ then check_ret_only eff (errno_ret ENOMEM) m []
     else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)) then CheckUnmodeled
     else if negb (bv_unsigned addr mod page_size =? 0) then check_ret_only eff (errno_ret EINVAL) m []
     else if negb (0 <? bv_unsigned addr) then CheckUnmodeled
     else let n := Z_to_bv 64 nZ in
          if region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n then X
          else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n then Y
          else if region_free (vm_reserved (m_vmmaps m)) addr n then Z
          else CheckUnmodeled) <> CheckUnmodeled).
  { intros X Y Z HX HY HZ. cbv zeta.
    destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
    destruct (negb (_ <=? alloc_top _)); [discriminate|].
    destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
    destruct (negb (0 <? bv_unsigned addr)); [discriminate|].
    destruct (region_free (vm_reserved (m_vmmaps m)) addr _ && map_contains _ _ _); [intros _; exact HX|].
    destruct (region_free (vm_reserved (m_vmmaps m) ++ _) addr _); [intros _; exact HY|].
    cbn [orb]. intros ->. exact HZ. }
  destruct (mmap_fixed_noaccess_b prot flags off); [|discriminate].
  apply Hfixed; no_unm.
Qed.

Lemma mmap_safe_noreserve : forall addr len prot flags fd off h,
  mmap_safe_b addr len prot flags fd off h = true -> mmap_noreserve_b flags = false.
Proof.
  intros. unfold mmap_safe_b in H. destruct (mmap_noreserve_b flags); [discriminate|reflexivity].
Qed.

Lemma strip_id : forall eff, eff_copyins eff = [] -> strip eff = eff.
Proof. intros [r ws zs us cs ci] H. cbn in H. subst. reflexivity. Qed.

Lemma mm_facts : forall ms mo n i x8 (chk : resp -> check_result),
  node_input n = Some i ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (evs = [] /\ syscall_spec i mo (Ok eff mo' evs))) ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_only mo mo' /\ evs = [] /\ eff_copyins eff = []) ->
  node_facts segs ms mo n.
Proof.
  intros ms mo n i x8 chk Hi Hn Hsvc Hminv Hh Hc1 Hc2 Hnu Hshape.
  exists x8. split; [exact Hsvc|]. split; [|split; [|split]].
  - intros eff mo' evs Hsp. apply check_syscall_ok_iff in Hsp. rewrite Hc1 in Hsp.
    destruct (Hshape _ _ _ Hsp) as (_ & -> & Hci). rewrite (strip_id _ Hci).
    apply Hn. split; [reflexivity|]. apply check_syscall_ok_iff. rewrite Hc2. exact Hsp.
  - intros rsp mo' evs Hns. apply Hn in Hns as [-> Hsp]. apply check_syscall_ok_iff in Hsp. rewrite Hc2 in Hsp.
    destruct (Hshape _ _ _ Hsp) as (_ & _ & Hci). exists rsp. split; [apply strip_id; exact Hci|].
    apply check_syscall_ok_iff. rewrite Hc1. exact Hsp.
  - intros Hsp. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hsp. rewrite Hc1 in Hsp.
    exact (Hnu _ Hsp).
  - intros rsp mo' evs Hns. apply Hn in Hns as [-> Hsp]. apply check_syscall_ok_iff in Hsp. rewrite Hc2 in Hsp.
    destruct (Hshape _ _ _ Hsp) as (Hv & _ & _). split.
    + destruct Hv as (_ & _ & -> & _). exact Hh.
    + eapply minv_vm_only; eassumption.
Qed.

Lemma mm_facts_f : forall ms mo n i x8 (chk : resp -> check_result),
  node_input n = Some i ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (evs = [] /\ syscall_spec i mo (Ok eff mo' evs) /\ mm_ok n i mo eff)) ->
  ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_only mo mo' /\ evs = [] /\ eff_copyins eff = []) ->
  in_sysno (sys_input segs ms x8) = in_sysno i ->
  in_arg (sys_input segs ms x8) 0 = in_arg i 0 ->
  (forall eff mo' evs, syscall_spec i mo (Ok eff mo' evs) ->
     (mm_ok n i mo eff <-> ~ spurious_refusal_cfg ACFG i mo eff)) ->
  (exists eff mo' evs, syscall_spec i mo (Ok eff mo' evs) /\ mm_ok n i mo eff) ->
  node_facts_f segs ms mo n.
Proof.
  intros ms mo n i x8 chk Inp StepIff Pend Inv Run Chk1 Chk2 Modeled Shape SameNo SameA0 OkIff Avail.
  set (si := sys_input segs ms x8) in *.
  assert (SpecEq : forall eff m1 l1, syscall_spec si mo (Ok eff m1 l1) <-> syscall_spec i mo (Ok eff m1 l1)).
  { intros eff m1 l1. split; intros Sp; apply check_syscall_ok_iff; apply check_syscall_ok_iff in Sp.
    - rewrite Chk2. rewrite Chk1 in Sp. exact Sp.
    - rewrite Chk1. rewrite Chk2 in Sp. exact Sp. }
  assert (SpurEq : forall eff, spurious_refusal_cfg ACFG si mo eff <-> spurious_refusal_cfg ACFG i mo eff).
  { intros eff. apply spurious_refusal_transport; [exact SameNo| exact SameA0| exact SpecEq]. }
  assert (OkOf : forall eff m1 l1, syscall_spec i mo (Ok eff m1 l1) ->
                 vm_only mo m1 /\ l1 = [] /\ eff_copyins eff = []).
  { intros eff m1 l1 Sp. apply Shape. rewrite <- Chk2. apply check_syscall_ok_iff. exact Sp. }
  exists x8. split; [exact Pend|].
  split; [|split; [|split; [|split]]].
  - intros eff m1 l1 Sp. apply SpecEq in Sp. destruct (OkOf _ _ _ Sp) as (Vm & L1 & Ci).
    split.
    + destruct Vm as (_ & _ & HaltEq & _). rewrite HaltEq. exact Run.
    + intros NoSp. rewrite (strip_id eff Ci). apply StepIff.
      split; [exact L1|]. split; [exact Sp|].
      apply (OkIff _ _ _ Sp). intros Bad. apply NoSp. apply SpurEq. exact Bad.
  - intros rsp m1 l1 Step1. apply StepIff in Step1. destruct Step1 as (_ & Sp & Ok1).
    destruct (OkOf _ _ _ Sp) as (_ & _ & Ci).
    exists rsp. split; [exact (strip_id rsp Ci)|]. split; [apply SpecEq; exact Sp|].
    intros Bad. apply SpurEq in Bad. exact (proj1 (OkIff _ _ _ Sp) Ok1 Bad).
  - intros Unm. apply (Modeled (eff0 (Z_to_bv 64 0))). rewrite <- Chk1.
    exact (check_syscall_complete_unmodeled _ _ _ Unm).
  - destruct Avail as (eff & m1 & l1 & Sp & Ok1). exists eff, m1, l1. apply StepIff.
    split; [exact (proj1 (proj2 (OkOf _ _ _ Sp)))|]. split; [exact Sp| exact Ok1].
  - intros rsp m1 l1 Step1. apply StepIff in Step1. destruct Step1 as (_ & Sp & _).
    exact (minv_vm_only mo m1 (proj1 (OkOf _ _ _ Sp)) Inv).
Qed.

Lemma mm_prog_nonspurious : forall i mo (chk : resp -> check_result),
  (forall eff, check_syscall i eff mo = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  exists eff mo' evs, syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg ACFG i mo eff.
Proof.
  intros i mo chk Agree Modeled.
  pose proof (receptive i mo) as Wit. revert Wit.
  destruct (syscall_spec_witness i mo) as [eff m1 evs|]; intros Wit.
  - exact (exists_nonspurious ACFG i mo eff m1 evs Wit).
  - exfalso. apply (Modeled (eff0 (Z_to_bv 64 0))). rewrite <- Agree.
    exact (check_syscall_complete_unmodeled i mo _ Wit).
Qed.

Lemma brk_facts : forall ms mo req,
  at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo -> node_facts_f segs ms mo (NBrk req).
Proof.
  intros ms mo req At Inv Run _.
  destruct At as (Pend & A0).
  assert (NoU : forall eff, check_brk (Z_to_bv 64 req) eff mo <> CheckUnmodeled).
  { intros [r ws zs us cs ci]. unfold check_brk. no_unm. }
  assert (ChkI : forall eff : SyscallEffect,
            check_syscall (pure_input 214 [Z_to_bv 64 req]) eff mo = check_brk (Z_to_bv 64 req) eff mo).
  { intros eff. dispatch_pure check_syscall_brk. reflexivity. }
  apply (mm_facts_f ms mo (NBrk req) (pure_input 214 [Z_to_bv 64 req]) (Z_to_bv 64 214)
           (fun eff => check_brk (Z_to_bv 64 req) eff mo)).
  - reflexivity.
  - intros eff m1 l1. reflexivity.
  - exact Pend.
  - exact Inv.
  - exact Run.
  - intros eff. dispatch check_syscall_brk. rewrite A0. reflexivity.
  - exact ChkI.
  - exact NoU.
  - intros eff m1 l1 Ok1. exact (check_brk_shape _ _ _ _ _ Ok1).
  - reflexivity.
  - rewrite in_a0_si, A0. reflexivity.
  - intros eff m1 l1 _. reflexivity.
  - destruct (mm_prog_nonspurious (pure_input 214 [Z_to_bv 64 req]) mo
                (fun eff => check_brk (Z_to_bv 64 req) eff mo) ChkI NoU) as (eff & m1 & l1 & Sp & NoSp).
    exists eff, m1, l1. split; [exact Sp| exact NoSp].
Qed.

Lemma unsigned_sysno_args : forall z args, 0 <= z < 2^64 -> bv_unsigned (in_sysno (pure_input z args)) = z.
Proof.
  intros z args Range. change (in_sysno (pure_input z args)) with (Z_to_bv 64 z).
  rewrite unsigned_lit; [reflexivity| exact Range].
Qed.

Lemma mmap_facts : forall ms mo addr len prot flags,
  at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
  unforced (NMmap addr len prot flags) mo ->
  node_facts_f segs ms mo (NMmap addr len prot flags).
Proof.
  intros ms mo addr len prot flags At Inv Run Safe Unf.
  destruct At as (Pend & A0 & A1 & A2 & A3 & A4 & A5).
  cbn [nsafe] in Safe.
  pose proof (mmap_safe_noreserve _ _ _ _ _ _ _ Safe) as NoRes.
  set (i := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                            Z_to_bv 64 (-1); Z_to_bv 64 0]).
  set (chk := fun eff => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                    (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).
  assert (NoU : forall eff, chk eff <> CheckUnmodeled).
  { intros eff. apply mmap_safe_no_unmodeled. exact Safe. }
  assert (ChkI : forall eff : SyscallEffect, check_syscall i eff mo = chk eff).
  { intros eff. rewrite check_syscall_mmap by reflexivity. reflexivity. }
  assert (No222 : bv_unsigned (in_sysno i) = 222) by reflexivity.
  assert (MOk : forall (eff : SyscallEffect) (m1 : Model) (l1 : list event), syscall_spec i mo (Ok eff m1 l1) ->
                mm_ok (NMmap addr len prot flags) i mo eff <-> ~ spurious_refusal_cfg ACFG i mo eff).
  { intros eff m1 l1 Sp. cbn [mm_ok].
    destruct (kernel_placed flags) eqn:Placed; cbv beta iota; [|reflexivity].
    destruct (Unf Placed) as (g & mg & lg & (_ & GSp & GOk)).
    cbn [mm_ok] in GOk. rewrite Placed in GOk. cbv beta iota in GOk.
    split.
    - intros NoRef (_ & Ref & _). rewrite (refusal_b_222 i mo _ No222), NoRef in Ref. discriminate Ref.
    - intros NoSp. destruct (ret_in_errnos mmap_errnos (eff_ret eff)) eqn:RefEq; [exfalso|reflexivity].
      apply NoSp. split; [exact (acfg_family_off_222 i No222)|]. split.
      + rewrite (refusal_b_222 i mo _ No222). exact RefEq.
      + exists g, mg, lg. split; [exact GSp|]. rewrite (refusal_b_222 i mo _ No222). exact GOk. }
  assert (Avail : exists (eff : SyscallEffect) (m1 : Model) (l1 : list event),
                    syscall_spec i mo (Ok eff m1 l1) /\ mm_ok (NMmap addr len prot flags) i mo eff).
  { destruct (kernel_placed flags) eqn:Placed.
    - destruct (Unf Placed) as (g & mg & lg & (_ & GSp & GOk)). exists g, mg, lg. split; [exact GSp| exact GOk].
    - destruct (mm_prog_nonspurious i mo chk ChkI NoU) as (eff & m1 & l1 & Sp & NoSp).
      exists eff, m1, l1. split; [exact Sp|]. cbn [mm_ok]. rewrite Placed. exact NoSp. }
  apply (mm_facts_f ms mo (NMmap addr len prot flags) i (Z_to_bv 64 222) chk).
  - reflexivity.
  - intros eff m1 l1. reflexivity.
  - exact Pend.
  - exact Inv.
  - exact Run.
  - intros eff. dispatch check_syscall_mmap. rewrite A0, A1, A2, A3, A4, A5. reflexivity.
  - exact ChkI.
  - exact NoU.
  - intros eff m1 l1 Ok1. exact (check_mmap_shape _ _ _ _ _ _ _ _ _ _ NoRes Ok1).
  - reflexivity.
  - rewrite in_a0_si, A0. reflexivity.
  - exact MOk.
  - exact Avail.
Qed.

Lemma munmap_facts : forall ms mo addr len,
  at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
  node_facts segs ms mo (NMunmap addr len).
Proof.
  intros ms mo addr len At Inv Run Safe.
  destruct At as (Pend & A0 & A1). cbn [nsafe] in Safe.
  apply (mm_facts ms mo (NMunmap addr len) (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) (Z_to_bv 64 215)
           (fun eff => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo)).
  - reflexivity.
  - intros eff m1 l1. reflexivity.
  - exact Pend.
  - exact Inv.
  - exact Run.
  - intros eff. dispatch check_syscall_munmap. rewrite A0, A1. reflexivity.
  - intros eff. dispatch_pure check_syscall_munmap. reflexivity.
  - intros eff. apply munmap_safe_no_unmodeled. exact Safe.
  - intros eff m1 l1 Ok1. exact (check_munmap_shape _ _ _ _ _ _ Ok1).
Qed.

Lemma mprotect_facts : forall ms mo addr len prot,
  at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
  unforced (NMprotect addr len prot) mo ->
  node_facts_f segs ms mo (NMprotect addr len prot).
Proof.
  intros ms mo addr len prot At Inv Run Safe Unf.
  destruct At as (Pend & A0 & A1 & A2).
  cbn [nsafe] in Safe.
  set (i := pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]).
  set (chk := fun eff => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo).
  destruct Unf as (g & mg & lg & (_ & GSp & GOk)). cbn [mm_ok] in GOk.
  assert (No226 : bv_unsigned (in_sysno i) = 226) by reflexivity.
  assert (MOk : forall (eff : SyscallEffect) (m1 : Model) (l1 : list event), syscall_spec i mo (Ok eff m1 l1) ->
                mm_ok (NMprotect addr len prot) i mo eff <-> ~ spurious_refusal_cfg ACFG i mo eff).
  { intros eff m1 l1 Sp. cbn [mm_ok]. split.
    - intros NoRef (_ & Ref & _). rewrite (refusal_b_226 i mo _ No226), NoRef in Ref. discriminate Ref.
    - intros NoSp. destruct (ret_in_errnos mprotect_errnos (eff_ret eff)) eqn:RefEq; [exfalso|reflexivity].
      apply NoSp. split; [exact (acfg_family_off_226 i No226)|]. split.
      + rewrite (refusal_b_226 i mo _ No226). exact RefEq.
      + exists g, mg, lg. split; [exact GSp|]. rewrite (refusal_b_226 i mo _ No226). exact GOk. }
  apply (mm_facts_f ms mo (NMprotect addr len prot) i (Z_to_bv 64 226) chk).
  - reflexivity.
  - intros eff m1 l1. reflexivity.
  - exact Pend.
  - exact Inv.
  - exact Run.
  - intros eff. dispatch check_syscall_mprotect. rewrite A0, A1, A2. reflexivity.
  - intros eff. rewrite check_syscall_mprotect by reflexivity. reflexivity.
  - intros eff. apply mprotect_safe_no_unmodeled. exact Safe.
  - intros eff m1 l1 Ok1. exact (check_mprotect_shape _ _ _ _ _ _ _ Ok1).
  - reflexivity.
  - rewrite in_a0_si, A0. reflexivity.
  - exact MOk.
  - exists g, mg, lg. split; [exact GSp| exact GOk].
Qed.

End PerNode5.

Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <->
  check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs
  /\ ~ spurious_refusal_cfg ACFG (pure_input 214 [Z_to_bv 64 req]) mo eff.
Proof.
  intros req mo eff mo' evs. split.
  - intros (_ & Sp & NoSp). split; [|exact NoSp].
    apply check_syscall_ok_iff in Sp. rewrite check_syscall_brk in Sp by reflexivity. exact Sp.
  - intros (Ok1 & NoSp). destruct (check_brk_shape _ _ _ _ _ Ok1) as (_ & L1 & _).
    split; [exact L1|]. split; [|exact NoSp].
    apply check_syscall_ok_iff. rewrite check_syscall_brk by reflexivity. exact Ok1.
Qed.

Lemma nstep_brk_check : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs -> check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs.
Proof. intros req mo eff mo' evs Step. apply nstep_brk_iff in Step. exact (proj1 Step). Qed.

Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs
  /\ mm_ok (NMmap addr len prot flags)
           (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
           mo eff.
Proof.
  intros addr len prot flags mo eff mo' evs NoRes. split.
  - intros (_ & Sp & MOk). split; [|exact MOk].
    apply check_syscall_ok_iff in Sp. rewrite check_syscall_mmap in Sp by reflexivity. exact Sp.
  - intros (Ok1 & MOk). destruct (check_mmap_shape _ _ _ _ _ _ _ _ _ _ NoRes Ok1) as (_ & L1 & _).
    split; [exact L1|]. split; [|exact MOk].
    apply check_syscall_ok_iff. rewrite check_syscall_mmap by reflexivity. exact Ok1.
Qed.

Lemma nstep_mmap_check : forall addr len prot flags mo eff mo' evs,
  mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs NoRes Step.
  exact (proj1 (proj1 (nstep_mmap_iff addr len prot flags mo eff mo' evs NoRes) Step)).
Qed.

Lemma nstep_mmap_nonrefusal : forall addr len prot flags mo eff mo' evs,
  kernel_placed flags = true ->
  nstep (NMmap addr len prot flags) mo eff mo' evs -> ret_in_errnos mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs Placed (_ & _ & MOk).
  cbn [mm_ok] in MOk. rewrite Placed in MOk. exact MOk.
Qed.

Lemma nstep_mmap_spec : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  (evs = [] /\ mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                         (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                         (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
                         mo (Ok eff mo' evs)
   /\ mm_ok (NMmap addr len prot flags)
            (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
            mo eff).
Proof.
  intros addr len prot flags mo eff mo' evs. split.
  - intros (L1 & Sp & MOk). rewrite syscall_spec_222 in Sp by reflexivity.
    split; [exact L1|]. split; [exact Sp| exact MOk].
  - intros (L1 & Sp & MOk). split; [exact L1|]. split; [|exact MOk].
    rewrite syscall_spec_222 by reflexivity. exact Sp.
Qed.

Lemma nstep_brk_spec : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <->
  (evs = [] /\ brk_spec (Z_to_bv 64 req) (pure_input 214 [Z_to_bv 64 req]) mo (Ok eff mo' evs)
   /\ ~ spurious_refusal_cfg ACFG (pure_input 214 [Z_to_bv 64 req]) mo eff).
Proof.
  intros req mo eff mo' evs. split.
  - intros (L1 & Sp & NoSp). rewrite syscall_spec_214 in Sp by reflexivity.
    split; [exact L1|]. split; [exact Sp| exact NoSp].
  - intros (L1 & Sp & NoSp). split; [exact L1|]. split; [|exact NoSp].
    rewrite syscall_spec_214 by reflexivity. exact Sp.
Qed.

Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof.
  intros addr len mo eff mo' evs. split.
  - intros (_ & Sp). apply check_syscall_ok_iff in Sp. rewrite check_syscall_munmap in Sp by reflexivity.
    exact Sp.
  - intros Ok1. destruct (check_munmap_shape _ _ _ _ _ _ Ok1) as (_ & L1 & _). split; [exact L1|].
    apply check_syscall_ok_iff. rewrite check_syscall_munmap by reflexivity. exact Ok1.
Qed.

Lemma nstep_munmap_check : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs -> check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof. intros addr len mo eff mo' evs Step. exact (proj1 (nstep_munmap_iff addr len mo eff mo' evs) Step). Qed.

Lemma nstep_munmap_spec : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  (evs = [] /\ munmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo (Ok eff mo' evs)).
Proof.
  intros addr len mo eff mo' evs. split.
  - intros (L1 & Sp). rewrite syscall_spec_215 in Sp by reflexivity. split; [exact L1| exact Sp].
  - intros (L1 & Sp). split; [exact L1|]. rewrite syscall_spec_215 by reflexivity. exact Sp.
Qed.

Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs
  /\ ret_in_errnos mprotect_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot mo eff mo' evs. split.
  - intros (_ & Sp & MOk). split; [|exact MOk].
    apply check_syscall_ok_iff in Sp. rewrite check_syscall_mprotect in Sp by reflexivity. exact Sp.
  - intros (Ok1 & MOk). destruct (check_mprotect_shape _ _ _ _ _ _ _ Ok1) as (_ & L1 & _).
    split; [exact L1|]. split; [|exact MOk].
    apply check_syscall_ok_iff. rewrite check_syscall_mprotect by reflexivity. exact Ok1.
Qed.

Lemma nstep_mprotect_check : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs.
Proof.
  intros addr len prot mo eff mo' evs Step.
  exact (proj1 (proj1 (nstep_mprotect_iff addr len prot mo eff mo' evs) Step)).
Qed.

Lemma nstep_mprotect_nonrefusal : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs -> ret_in_errnos mprotect_errnos (eff_ret eff) = false.
Proof. intros addr len prot mo eff mo' evs (_ & _ & MOk). exact MOk. Qed.

Lemma nstep_mprotect_spec : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  (evs = [] /\ mprotect_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot)
                             (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo (Ok eff mo' evs)
   /\ ret_in_errnos mprotect_errnos (eff_ret eff) = false).
Proof.
  intros addr len prot mo eff mo' evs. split.
  - intros (L1 & Sp & MOk). rewrite syscall_spec_226 in Sp by reflexivity.
    split; [exact L1|]. split; [exact Sp| exact MOk].
  - intros (L1 & Sp & MOk). split; [exact L1|]. split; [|exact MOk].
    rewrite syscall_spec_226 by reflexivity. exact Sp.
Qed.

Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  match n with NBrk _ | NMunmap _ _ | NMprotect _ _ _ => True
             | NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => False end ->
  nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [] /\ eff_copyins eff = [].
Proof.
  intros n mo eff mo' evs Kind Step.
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
    try contradiction.
  - exact (check_brk_shape _ _ _ _ _ (nstep_brk_check _ _ _ _ _ Step)).
  - exact (check_mmap_shape _ _ _ _ _ _ _ _ _ _ Kind (nstep_mmap_check _ _ _ _ _ _ _ _ Kind Step)).
  - exact (check_munmap_shape _ _ _ _ _ _ (nstep_munmap_check _ _ _ _ _ _ Step)).
  - exact (check_mprotect_shape _ _ _ _ _ _ _ (nstep_mprotect_check _ _ _ _ _ _ _ Step)).
Qed.

Lemma nstep_mmap_nonrefusal_of_grant : forall addr len prot flags mo eff mo' evs eff' mo2 evs2,
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk mo2 evs2 ->
  errno_ret_in mmap_errnos (eff_ret eff') = false ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs eff' mo2 evs2 Step Grant NoRef'.
  destruct Step as (_ & _ & MOk). cbn [mm_ok] in MOk.
  destruct (kernel_placed flags); cbv beta iota in MOk; [exact MOk|].
  destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:Ref; [exfalso|reflexivity].
  apply MOk. split; [apply acfg_family_off_222; reflexivity|]. split.
  - rewrite refusal_b_222 by reflexivity. exact Ref.
  - exists eff', mo2, evs2. split.
    + apply check_syscall_ok_iff. rewrite check_syscall_mmap by reflexivity. exact Grant.
    + rewrite refusal_b_222 by reflexivity. exact NoRef'.
Qed.

Lemma nstep_brk_nonrefusal_of_grant : forall req mo eff mo' evs eff' mo2 evs2,
  nstep (NBrk req) mo eff mo' evs ->
  check_brk (Z_to_bv 64 req) eff' mo = CheckOk mo2 evs2 ->
  brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff') = false ->
  brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff) = false.
Proof.
  intros req mo eff mo' evs eff' mo2 evs2 Step Grant NoRef'.
  destruct Step as (_ & _ & NoSp). cbn [mm_ok] in NoSp.
  destruct (brk_refusal_b mo (Z_to_bv 64 req) (eff_ret eff)) eqn:Ref; [exfalso|reflexivity].
  apply NoSp. split; [apply acfg_family_off_214; reflexivity|]. split.
  - rewrite refusal_b_214 by reflexivity. exact Ref.
  - exists eff', mo2, evs2. split.
    + apply check_syscall_ok_iff. rewrite check_syscall_brk by reflexivity. exact Grant.
    + rewrite refusal_b_214 by reflexivity. exact NoRef'.
Qed.

Lemma nsafe_mmap_rw : forall addr len mo,
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros. cbn [nsafe]. unfold mmap_safe_b. destruct (w_is0 (Z_to_bv 64 len)); reflexivity. Qed.

Lemma nsafe_mmap_none : forall addr len mo,
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros. cbn [nsafe]. unfold mmap_safe_b. destruct (w_is0 (Z_to_bv 64 len)); reflexivity. Qed.

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

Definition no_noreserve (n : node) : Prop :=
  match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end.

Lemma minv_preserved_gen : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> no_noreserve n -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hminv Hh Hsafe H.
  assert (Hor : forall ent, open_result mo ent eff mo' ->
            match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
            m_halted mo' = None /\ minv mo').
  { intros ent [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
    split; [exact Hh|]. apply minv_open_insert; assumption. }
  assert (Hmm : forall n', match n' with NBrk _ | NMunmap _ _ | NMprotect _ _ _ => True
                          | NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => False end ->
                nstep n' mo eff mo' evs -> m_halted mo' = None /\ minv mo').
  { intros n' Hn' H'. destruct (nstep_mm_vm_only n' mo eff mo' evs Hn' H') as [Hv _].
    split; [destruct Hv as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; eassumption]. }
  destruct n; cbn [nstep] in H.
  - destruct H as (-> & _); auto.
  - destruct H as [_ H].
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
    destruct path as [|c path']. { destruct H as [_ ->]; auto. }
    destruct (path_eqb (c :: path') dot_path). { exact (Hor FdDir H I). }
    destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
    + apply (Hor _ H). cbn. congruence.
    + destruct H as [_ ->]; auto.
  - destruct H as [_ H].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |s|pi pw|rd wr| ]|] eqn:Hlk; try contradiction.
    + destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
      split; [exact Hh|]. eapply minv_update_file; eassumption.
    + destruct H as [_ ->]. auto.
    + destruct H as [_ ->]. auto.
  - destruct H as (_ & Hfd & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
    split; [exact Hh|]. apply minv_remove; assumption.
  - destruct H as (_ & _ & ->); auto.
  - destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; auto.
    split; [exact Hh|]. apply minv_with_tid; assumption.
  - destruct H.
  - apply (Hmm (NBrk req) I). cbn [nstep]. exact H.
  - apply (Hmm (NMmap addr len prot flags)); [| cbn [nstep]; exact H]. exact Hsafe.
  - apply (Hmm (NMunmap addr len) I). cbn [nstep]. exact H.
  - apply (Hmm (NMprotect addr len prot) I). cbn [nstep]. exact H.
Qed.

Lemma nsafe_no_noreserve : forall n mo, nsafe n mo -> no_noreserve n.
Proof.
  intros n mo H. destruct n; try exact I. cbn [nsafe] in H. eapply mmap_safe_noreserve. exact H.
Qed.

Lemma minv_preserved : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> nsafe n mo -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
  intros n mo eff mo' evs Hminv Hh Hsafe H.
  exact (minv_preserved_gen n mo eff mo' evs Hminv Hh (nsafe_no_noreserve n mo Hsafe) H).
Qed.

Definition is_transparent (n : node) : Prop :=
  match n with
  | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ | NSetTid | NMunmap _ _ => True
  | NExit _ | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ => False
  end.
Definition is_filtered (n : node) : Prop :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ => True
  | _ => False
  end.

Lemma all_facts : forall segs n ms mo,
  is_transparent n ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts segs ms mo n.
Proof.
  intros segs n ms mo Tr At Inv Run Safe.
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
    cbn [is_transparent] in Tr; try contradiction.
  - exact (writev_facts segs ms mo fd bufs At Inv Run).
  - exact (open_facts segs ms mo path At Inv Run Safe).
  - exact (read_facts segs ms mo fd buf count At Inv Run).
  - exact (close_facts segs ms mo fd At Inv Run).
  - exact (ioctl_facts segs ms mo fd req At Inv Run).
  - exact (set_tid_facts segs ms mo At Inv Run).
  - exact (munmap_facts segs ms mo addr len At Inv Run Safe).
Qed.

Lemma all_facts_f : forall segs n ms mo,
  is_filtered n ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> unforced n mo -> node_facts_f segs ms mo n.
Proof.
  intros segs n ms mo Fi At Inv Run Safe Unf.
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
    cbn [is_filtered] in Fi; try contradiction.
  - exact (brk_facts segs ms mo req At Inv Run Safe).
  - exact (mmap_facts segs ms mo addr len prot flags At Inv Run Safe Unf).
  - exact (mprotect_facts segs ms mo addr len prot At Inv Run Safe Unf).
Qed.

Lemma transparent_sysno : forall segs n ms,
  is_transparent n -> at_node segs n ms ->
  forall x8, ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false.
Proof.
  intros segs n ms Tr At x8 Pend.
  assert (Code : exists k, ms_svc_pending ms = Some (Z_to_bv 64 k) /\ alloc_no_b (bv_unsigned (Z_to_bv 64 k)) = false).
  { destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
      cbn [is_transparent] in Tr; try contradiction; cbn [at_node] in At.
    - exists 66. split; [exact (proj1 At)| reflexivity].
    - exists 56. split; [exact (proj1 At)| reflexivity].
    - exists 63. split; [exact (proj1 At)| reflexivity].
    - exists 57. split; [exact (proj1 At)| reflexivity].
    - exists 29. split; [exact (proj1 At)| reflexivity].
    - exists 96. split; [exact At| reflexivity].
    - exists 215. split; [exact (proj1 At)| reflexivity]. }
  destruct Code as (k & Pk & Free). rewrite Pk in Pend. injection Pend as <-. exact Free.
Qed.

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

Lemma exit_node_facts : forall segs ms mo c,
  at_node segs (NExit c) ms -> m_halted mo = None ->
  (forall evs X, sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
  /\ sstep_cfg segs ACFG (mkCfg ms mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg ms (with_halted (exit_code c) mo))).
Proof.
  intros segs ms mo c At Run.
  destruct (proj1 At) as [Pend | Pend];
    exact (exit_kit segs ms mo _ (exit_code c) Pend Run (exit_char segs ms mo c _ At Pend)).
Qed.

Lemma nonexit_node_facts : forall segs n ms mo,
  match n with NExit _ => False | _ => True end ->
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> unforced n mo ->
  (forall evs X, sstep_cfg segs ACFG (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
        m_halted mo' = None /\ minv mo' /\ sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros segs n ms mo NotExit At Inv Run Safe Unf.
  assert (Kind : is_transparent n \/ is_filtered n).
  { destruct n; first [left; exact I | right; exact I | contradiction]. }
  destruct Kind as [Tr | Fi].
  - exact (node_kit segs ms mo n (all_facts segs n ms mo Tr At Inv Run Safe) Run (transparent_sysno segs n ms Tr At)).
  - exact (node_kit_f segs ms mo n (all_facts_f segs n ms mo Fi At Inv Run Safe Unf) Run).
Qed.

Theorem nodes_sound : forall segs, node_sound node segs ACFG (at_node segs) nstep nexit minv nsafeU.
Proof.
  intros segs. constructor.
  - exact minv_lazy.
  - intros n ms At Absent.
    assert (Busy : exists k, ms_svc_pending ms = Some k).
    { destruct n; cbn [at_node] in At;
        repeat match type of At with _ /\ _ => destruct At as [At _] end;
        try match type of At with _ \/ _ => destruct At as [At | At] end;
        eexists; exact At. }
    destruct Busy as (k & Pk). rewrite Pk in Absent. discriminate Absent.
  - intros n ms mo evs X At Run Inv [Safe Unf] Stp.
    destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
      try (left; refine (proj1 (nonexit_node_facts segs _ ms mo _ At Inv Run Safe Unf) evs X Stp); exact I).
    right. destruct (exit_node_facts segs ms mo c At Run) as [Inv1 _].
    destruct (Inv1 evs X Stp) as [Nx Ev].
    exists (exit_code c), (with_halted (exit_code c) mo).
    split; [exact Nx|]. split; [split; reflexivity|]. rewrite m_fs_with_halted. exact Ev.
  - intros n ms mo rsp mo' evs At Run Inv [Safe Unf] Step.
    destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
      try (refine (proj1 (proj2 (nonexit_node_facts segs _ ms mo _ At Inv Run Safe Unf)) rsp mo' evs Step);
           exact I).
    destruct Step.
  - intros n ms mo code mo' At Run _ _ Ex.
    destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
      try (destruct Ex; fail).
    destruct Ex as [-> ->]. split; [apply m_halted_with_halted|].
    rewrite m_fs_with_halted. exact (proj2 (exit_node_facts segs ms mo c At Run)).
  - intros n ms mo At Run Inv [Safe Unf].
    destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|addr len prot flags|addr len|addr len prot];
      try (left; refine (proj2 (proj2 (nonexit_node_facts segs _ ms mo _ At Inv Run Safe Unf))); exact I).
    right. exists (exit_code c), (with_halted (exit_code c) mo). split; reflexivity.
Qed.
