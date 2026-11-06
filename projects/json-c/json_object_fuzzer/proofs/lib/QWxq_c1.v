(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsjA QEpW QZDE QbVh QlEo_c1.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
match bs with
| [] => true
| b :: bs' =>
match seg_rom segs (wa A) with
| Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
| None => false
end
end.

#[using="Type"] Lemma ro_bytes_b_sound : forall bs A, ro_bytes_b A bs = true -> ro_bytes segs A bs.
Proof.
induction bs as [|b bs IH]; intros A H; cbn in *; [exact I|].
destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
split; [split; [exact E| exact H2]|]. apply IH. exact H3.
Qed.

#[using="Type"] Lemma ro_cells_image : forall m A bs,
mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
ro_cells segs m A [CB (length bs) bs].
Proof.
intros m A bs Hinv Hb HA Hl. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; try assumption.
apply ro_bytes_b_sound. exact Hb.
Qed.

Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
match n with
| O => Some []
| S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
| Some b, Some bs => Some (b :: bs)
| _, _ => None
end
end.

#[using="Type"] Lemma image_bytes_length : forall n A bs, image_bytes A n = Some bs -> length bs = n.
Proof.
induction n as [|n IH]; intros A bs H; cbn in H.
- inversion H. reflexivity.
- destruct (seg_rom segs (wa A)); [|discriminate]. destruct (image_bytes (A + 1) n) eqn:E; [|discriminate].
inversion H. cbn. f_equal. eapply IH. exact E.
Qed.

End WithSegs.

End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect Mremap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.LinuxProcessSem.Checks.Progress.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
#[using="Type"] Lemma in_a0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = areg ms 10.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_a1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = areg ms 11.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_a2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = areg ms 12.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_a3_si : forall segs ms x8, in_arg (sys_input segs ms x8) 3 = areg ms 13.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_a4_si : forall segs ms x8, in_arg (sys_input segs ms x8) 4 = areg ms 14.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_a5_si : forall segs ms x8, in_arg (sys_input segs ms x8) 5 = areg ms 15.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
#[using="Type"] Lemma in_wmem_si : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.

#[using="Type"] Lemma ms_read_byte_mrd : forall segs ms a,
ms_rom ms = seg_rom segs -> ms_read_byte ms a = mrd segs (ms_mem ms) a.
Proof. intros segs ms a H. unfold ms_read_byte, mrd. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma bytes_at_in : forall segs ms a bs,
ms_rom ms = seg_rom segs -> bytes_at segs (ms_mem ms) a bs -> bytes_in (ms_read_byte ms) a bs.
Proof.
intros segs ms a bs Hrom (Ha & Hl & H). split; [lia|]. split; [lia|].
intros i Hi. rewrite (ms_read_byte_mrd segs) by exact Hrom. apply H. exact Hi.
Qed.

#[using="Type"] Lemma bytes_in_app : forall mp a bs1 bs2,
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

#[using="Type"] Lemma bytes_in_cons : forall mp a b bs,
bytes_in mp a (b :: bs) -> mp (wa a) = Some b /\ bytes_in mp (a + 1) bs.
Proof.
intros mp a b bs H. change (b :: bs) with ([b] ++ bs) in H. apply bytes_in_app in H as [H1 H2].
split; [|exact H2]. destruct H1 as (_ & _ & H1). specialize (H1 0%nat ltac:(cbn; lia)).
rewrite Z.add_0_r in H1. exact H1.
Qed.

#[using="Type"] Lemma read_bytes_aux_bytes_in : forall bs mp a,
bytes_in mp a bs -> read_bytes_aux mp (wa a) (length bs) = Some bs.
Proof.
induction bs as [|b bs IH]; intros mp a H; [reflexivity|].
apply bytes_in_cons in H as [Hb H]. cbn [read_bytes_aux length]. rewrite Hb.
rewrite wa_succ, (IH _ _ H). reflexivity.
Qed.

#[using="Type"] Lemma readable_bytes_aux_bytes_in : forall bs mp a,
bytes_in mp a bs -> readable_bytes_aux mp (wa a) (length bs) = bs.
Proof.
intros. apply readable_bytes_aux_full, read_bytes_aux_bytes_in. assumption.
Qed.

#[using="Type"] Lemma word_to_nat_of_nat : forall n, Z.of_nat n < 2^64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof. intros. unfold word_to_nat. rewrite unsigned_lit by lia. lia. Qed.

#[using="Type"] Lemma read_bytes_map_bytes_in : forall bs mp a,
bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
read_bytes_map mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = Some bs.
Proof.
intros bs mp a H Hl. rewrite read_bytes_map_eq. rewrite word_to_nat_of_nat by exact Hl.
apply read_bytes_aux_bytes_in, H.
Qed.

#[using="Type"] Lemma readable_bytes_bytes_in : forall bs mp a,
bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
readable_bytes mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = bs.
Proof.
intros. apply readable_bytes_full, read_bytes_map_bytes_in; assumption.
Qed.

#[using="Type"] Lemma read_cstr_aux_bytes_in : forall str fuel mp a,
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

#[using="Type"] Lemma read_cstr_aux_toolong_bytes_in : forall fuel str mp a,
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

#[using="Type"] Lemma length_iovec_bytes : forall iovs, length (iovec_bytes iovs) = (16 * length iovs)%nat.
Proof.
induction iovs as [|[b l] iovs IH]; [reflexivity|]. cbn [iovec_bytes flat_map fst snd].
rewrite !length_app, !length_le8. unfold iovec_bytes in IH. rewrite IH. cbn [length]. lia.
Qed.

#[using="Type"] Lemma read_u64_bytes_in : forall mp a v,
bytes_in mp a (le8 v) -> read_u64 mp (wa a) = Some v.
Proof.
intros mp a v H. unfold read_u64.
pose proof (read_bytes_map_bytes_in _ _ _ H ltac:(rewrite length_le8; cbn; lia)) as R. rewrite length_le8 in R.
change (Z.of_nat 8) with 8 in R. rewrite R. rewrite le_bytes_to_word_le8. reflexivity.
Qed.

#[using="Type"] Lemma wa_add : forall a (k : word), (wa a + k)%bv = wa (a + bv_unsigned k).
Proof. intros. rewrite <- (Z_to_bv_bv_unsigned k) at 1. unfold wa. apply lit_add_lit. Qed.

#[using="Type"] Lemma read_iovecs_aux_bytes_in : forall iovs mp a,
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

Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

#[using="Type"] Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

#[using="Type"] Lemma gather_iovecs_ok : forall mp iovs bufs,
Forall2 (iov_ok mp) iovs bufs -> gather_iovecs mp iovs = Some (concat bufs).
Proof.
intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
cbn [gather_iovecs fst snd] in *. subst l.
rewrite <- (wa_unsigned_id b). rewrite (read_bytes_map_bytes_in _ _ _ Hb Hlen). rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma iovs_total_ok : forall mp iovs bufs,
Forall2 (iov_ok mp) iovs bufs -> iovs_total iovs = Z.of_nat (length (concat bufs)).
Proof.
intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
cbn [iovs_total fst snd concat] in *. subst l. rewrite length_app, IH.
rewrite unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma read_bytes_aux_wr_at : forall segs m a n k,
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
| NWrite (fd : Z) (bs : list byte)
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
| NMremap (old oldlen newlen flags : Z).

Definition pure_input (no : Z) (args : list word) : SyscallInput :=
mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).

Definition node_input (n : node) : option SyscallInput :=
match n with
| NBrk req => Some (pure_input 214 [Z_to_bv 64 req])
| NMmap addr len prot flags =>
Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
| NMunmap addr len => Some (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])
| NMprotect addr len prot => Some (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
| NMremap old oldlen newlen flags => Some (pure_input 216 [Z_to_bv 64 old; Z_to_bv 64 oldlen; Z_to_bv 64 newlen; Z_to_bv 64 flags])
| _ => None
end.

Section AtNode.
Variable segs : list Segment.

Definition at_node (n : node) (ms : machine_state) : Prop :=
match n with

| NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ => False /\ ms_rom ms = seg_rom segs
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
| NMremap old oldlen newlen flags =>
ms_svc_pending ms = Some (Z_to_bv 64 216) /\
areg ms 10 = Z_to_bv 64 old /\ areg ms 11 = Z_to_bv 64 oldlen /\ areg ms 12 = Z_to_bv 64 newlen /\
areg ms 13 = Z_to_bv 64 flags
end.

End AtNode.
End RC__1.

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
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
(exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
\/ (let fd := alloc_fd (m_fds mo) in
fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
match n with

| NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ => False
| NSetTid =>
evs = [] /\ exists t, eff = eff0 t /\
match m_tid mo with
| Some t0 => t = t0 /\ mo' = mo
| None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
end
| NExit _ => False
| NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ _ =>
evs = [] /\
match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end /\
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

Definition minv (mo : Model) : Prop :=
alloc_top (m_vmmaps mo) = alloc_ceiling /\
m_vm_lazy mo = [] /\
fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
(forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
(forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
(forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileW p off)) /\
(forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE).

#[using="Type"] Lemma minv_init : forall reserved brk mbase sp lim inp,
bv_unsigned sp - stack_max_size = alloc_ceiling ->
minv (init_model reserved brk mbase sp lim inp).
Proof.
intros reserved brk mbase sp lim inp Hsp. unfold minv.

assert (E1 : m_fds (init_model reserved brk mbase sp lim inp) = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))]) by reflexivity.
assert (E2 : m_tid (init_model reserved brk mbase sp lim inp) = None) by reflexivity.
assert (E3 : m_vm_lazy (init_model reserved brk mbase sp lim inp) = []) by reflexivity.
rewrite E1, E2, E3, alloc_top_init. clear E1 E2 E3.
split; [exact Hsp|]. split; [reflexivity|]. repeat split; try reflexivity; try (intros; discriminate).
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
Qed.

Definition nsafe (n : node) (mo : Model) : Prop :=
match n with
| NMmap addr len prot flags =>
forall eff, check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo <> CheckUnmodeled
| NMunmap addr len => forall eff, check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo <> CheckUnmodeled
| NMprotect addr len prot =>
forall eff, check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo <> CheckUnmodeled
| NMremap old oldlen newlen flags =>
forall eff, check_mremap (Z_to_bv 64 old) (Z_to_bv 64 oldlen) (Z_to_bv 64 newlen) (Z_to_bv 64 flags) eff mo <> CheckUnmodeled
| _ => True
end.

Section Generic.
Variable segs : list Segment.

#[using="Type"] Lemma m_killed_halted : forall mo sig, m_killed mo = Some sig -> m_halted mo = Some sig.
Proof.
intros mo sig. unfold m_killed, m_halted.
destruct (procst_killed (m_proc mo)); [exact (fun H => H) | discriminate].
Qed.

#[using="Type"] Lemma sstep_svc_inv : forall ms mo x8 evs X,
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
\/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some sig /\
m_killed mo' = Some sig /\
evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
\/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
- left. eexists _, _, _. eauto.
- right; left. eexists _, _, _. eauto 6.
- right; right; left. eexists _, _, _, _. eauto 6.
- right; right; right; left. eexists _, _, _, _.
split; [eassumption|]. split; [apply m_killed_halted; eassumption|]. eauto.
- right; right; right; right. auto.
Qed.

#[using="Type"] Lemma node_kit : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> P eff mo' evs) ->
(forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
(forall eff mo' evs, P eff mo' evs -> m_halted mo' = None) ->
(forall eff mo' evs, P eff mo' evs -> m_vm_lazy mo' = []) ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
/\ (forall eff mo' evs, P eff mo' evs -> sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
/\ (exists eff mo' evs, P eff mo' evs).
Proof.
intros ms mo x8 P Hsvc Hh Hchar Hnu Hhalt Hlz. split; [|split].
- intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
as [(eff & mo' & mo'' & Hs & Hh' & Hmat & ->)
| [(eff & mo' & evs0 & Hs & Hh' & Hmat & -> & ->)
| [(eff & mo' & evs0 & code & Hs & Hh' & Hk' & -> & ->)
| [(eff & mo' & evs0 & sig & Hs & Hh' & Hk' & -> & ->) | (Hs & -> & ->)]]]].
+ exists eff, mo'. apply check_syscall_ok_iff in Hs. apply Hchar in Hs.
rewrite (materialize_model_accesses_no_lazy mo' _ (Hlz _ _ _ Hs)) in Hmat. inversion Hmat; subst.
split; [reflexivity| exact Hs].
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs.
rewrite (materialize_model_accesses_no_lazy mo' _ (Hlz _ _ _ Hs)) in Hmat. discriminate.
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs. apply Hhalt in Hs. congruence.
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs. apply Hhalt in Hs. congruence.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
- intros eff mo' evs HP. unfold nret.
eapply sstep_syscall; [exact Hh|exact Hsvc| |exact (Hhalt _ _ _ HP)| apply materialize_model_accesses_no_lazy; exact (Hlz _ _ _ HP)].
apply check_syscall_ok_iff. apply Hchar. exact HP.
- pose proof (receptive (sys_input segs ms x8) mo) as Hr.
destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
+ exists eff, mo', evs. apply Hchar. apply check_syscall_ok_iff. exact Hr.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.

#[using="Type"] Lemma exit_kit : forall ms mo x8 code,
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
as [(eff & mo' & mo'' & Hs & Hh' & Hmat & ->)
| [(eff & mo' & evs0 & Hs & Hh' & Hmat & -> & ->)
| [(eff & mo' & evs0 & code' & Hs & Hh' & Hk' & -> & ->)
| [(eff & mo' & evs0 & sig & Hs & Hh' & Hk' & -> & ->) | (Hs & -> & ->)]]]].
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _).
rewrite m_halted_with_halted in Hh'. discriminate.
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _).
rewrite m_halted_with_halted in Hh'. discriminate.
+ apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & ->). rewrite m_halted_with_halted in Hh'.
inversion Hh'; subst. rewrite m_fs_with_halted. split; reflexivity.
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _).
rewrite m_killed_with_halted in Hk'. discriminate.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
- change [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs mo)]).
rewrite <- (m_fs_with_halted code mo).
eapply sstep_exit; [exact Hh|exact Hsvc| |apply m_halted_with_halted|apply m_killed_with_halted].
apply check_syscall_ok_iff. apply Hchar. repeat split; reflexivity.
Qed.

End Generic.

Section PerNode.
Variable segs : list Segment.

Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
exists x8, ms_svc_pending ms = Some x8 /\
(forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <-> nstep n mo eff mo' evs) /\
(forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) /\
(forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo').

#[using="Type"] Lemma facts_ret_only : forall ms mo n x8 r evs0,
ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
(forall eff, check_syscall (sys_input segs ms x8) eff mo = check_ret_only eff r mo evs0) ->
(forall eff mo' evs, nstep n mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo /\ evs = evs0)) ->
node_facts ms mo n.
Proof.
intros ms mo n x8 r evs0 Hsvc Hminv Hh Hchk Hn. exists x8. split; [exact Hsvc|]. split; [|split].
- intros eff mo' evs. rewrite Hchk, check_ret_only_ok_iff, Hn. unfold eff0. tauto.
- intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
- intros eff mo' evs HP. apply Hn in HP as (_ & -> & _). auto.
Qed.

Ltac dispatch_with L :=
rewrite L by (rewrite in_sysno_si; reflexivity);
rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

#[using="Type"] Lemma efault_gate_false : forall bs : list byte,
negb (w_is0 (Z_to_bv 64 (Z.of_nat (length bs)))) && (length bs =? 0)%nat = false.
Proof. intros [|b bs]; [reflexivity|]. cbn [length Nat.eqb]. apply andb_false_r. Qed.

#[using="Type"] Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="Type"] Lemma bv_eqb_sym : forall (a b : word), bv_eqb a b = bv_eqb b a.
Proof. intros. unfold bv_eqb. rewrite Z.eqb_sym. reflexivity. Qed.

#[using="Type"] Lemma minv_with_tid : forall mo t, minv mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minv (with_tid t mo).
Proof.
intros mo t (MCL & ML & M0 & M1 & M2 & MC & MF & MW & MT) Ht. unfold minv. autorewrite with model.
split; [exact MCL|]. split; [exact ML|].
repeat split; try assumption; match goal with H : Some _ = Some _ |- _ => inversion H; subst; lia end.
Qed.

#[using="Type"] Lemma set_tid_facts : forall ms mo,
at_node segs NSetTid ms -> minv mo -> m_halted mo = None -> node_facts ms mo NSetTid.
Proof.
intros ms mo Hsvc Hminv Hh.
assert (Hchk : forall eff, check_syscall (sys_input segs ms (Z_to_bv 64 96)) eff mo = check_set_tid_address eff mo).
{ intros eff. dispatch_with check_syscall_set_tid_address. reflexivity. }
exists (Z_to_bv 64 96). split; [exact Hsvc|]. split; [|split].
- intros [ret ws zs us cs cis] mo' evs. rewrite Hchk. unfold check_set_tid_address. cbn [nstep]. unfold eff0. split.
+ intros H. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (m_tid mo) as [t0|].
* destruct (bv_eqb ret t0) eqn:E; [|discriminate]. apply bv_eqb_eq in E. inversion H; subst.
split; [reflexivity|]. exists t0. auto.
* destruct ((0 <? bv_unsigned ret) && (bv_unsigned ret <? PID_MAX_ENVELOPE)) eqn:E; [|discriminate].
inversion H; subst. apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
split; [reflexivity|]. exists ret. auto.
+ intros (-> & t & Heff & Ht). inversion Heff; subst. destruct (m_tid mo) as [t0|].
* destruct Ht as [-> ->]. rewrite bv_eqb_refl. reflexivity.
* destruct Ht as [[H1 H2] ->]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
- intros [ret ws zs us cs cis]. rewrite Hchk. unfold check_set_tid_address.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (m_tid mo); [destruct (bv_eqb _ _); discriminate| destruct (_ && _); discriminate].
- intros eff mo' evs (_ & t & _ & Ht). destruct (m_tid mo); [destruct Ht as [_ ->]; auto|].
destruct Ht as [Hr ->]. split; [rewrite m_halted_with_tid; exact Hh|]. apply minv_with_tid; assumption.
Qed.

#[using="Type"] Lemma exit_check : forall ms mo c x8 eff,
at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 ->
check_syscall (sys_input segs ms x8) eff mo
= check_ret_only eff (Z_to_bv 64 0) (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) mo) [].
Proof.
intros ms mo c x8 eff [Hsvc Ha0] Hx8.
destruct Hsvc as [Hsvc|Hsvc]; rewrite Hsvc in Hx8; inversion Hx8; subst;
[dispatch_with check_syscall_exit | dispatch_with check_syscall_exit_group]; unfold check_exit; rewrite Ha0; reflexivity.
Qed.

Definition vm_only (m m' : Model) : Prop :=
(m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\
m_lim m' = m_lim m /\ m_time m' = m_time m /\
vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m))
/\ (m_vm_lazy m = [] -> m_vm_lazy m' = []).

#[using="Type"] Lemma vm_only_old : forall m m', vm_only m m' ->
m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.
Proof.
intros m m' [(Hfd & Hio & Hfs & Hpr & _) _].
unfold m_fds, m_fs, m_halted, m_tid, m_stdin. rewrite Hfd, Hio, Hfs, Hpr. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma vm_only_refl : forall m, vm_only m m.
Proof. intros m. split; [repeat split; reflexivity| tauto]. Qed.

#[using="Type"] Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
intros a b c [(A1 & A2 & A3 & A4 & A5 & A6 & A7) AL] [(B1 & B2 & B3 & B4 & B5 & B6 & B7) BL].
split; [repeat split; congruence| tauto].
Qed.

#[using="Type"] Lemma vm_only_with_vmmaps : forall h m,
vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m (with_vmmaps h m).
Proof. intros h m E. split; [repeat split; try reflexivity; exact E| intros H; exact H]. Qed.

#[local] Hint Extern 1 (vm_init_sp _ = vm_init_sp _) => reflexivity : vmonly.

#[using="Type"] Lemma maps_subtract_nil : forall lo hi, maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

#[using="Type"] Lemma vm_only_forget_range : forall lo hi m, vm_only m (vm_forget_range lo hi m).
Proof.
intros lo hi m. split; [repeat split; reflexivity|].
intros H. unfold vm_forget_range. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma vm_only_forget_vm_ranges : forall l m, vm_only m (forget_vm_ranges l m).
Proof.
induction l as [|[a n] l IH]; intros m; cbn [forget_vm_ranges].
- apply vm_only_refl.
- eapply vm_only_trans; [apply vm_only_forget_range| apply IH].
Qed.

#[using="Type"] Lemma vm_only_with_mmap_backing : forall flags a n m,
mmap_noreserve_b flags = false -> vm_only m (with_mmap_backing flags a n m).
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. apply vm_only_refl. Qed.

#[using="Type"] Lemma vm_only_with_mmap_destroyed : forall a n h m,
vm_init_sp h = vm_init_sp (m_vmmaps m) -> vm_only m (with_mmap_destroyed a n h m).
Proof.
intros. unfold with_mmap_destroyed. eapply vm_only_trans; [| apply vm_only_forget_range]. apply vm_only_with_vmmaps; assumption.
Qed.

#[using="Type"] Lemma vm_only_with_mmap_replacement : forall flags a n m,
mmap_noreserve_b flags = false -> vm_only m (with_mmap_replacement flags a n m).
Proof.
intros. unfold with_mmap_replacement.
eapply vm_only_trans; [apply vm_only_forget_range| apply vm_only_with_mmap_backing; assumption].
Qed.

#[using="Type"] Lemma vm_only_with_brk_next : forall m req r, vm_only m (with_brk_next m req r).
Proof.
intros. unfold with_brk_next. eapply vm_only_trans; [| apply vm_only_forget_vm_ranges]. apply vm_only_with_vmmaps; reflexivity.
Qed.

#[using="Type"] Lemma vm_only_mprotect_model_next : forall m a n, vm_only m (mprotect_model_next m a n).
Proof. intros. unfold mprotect_model_next. apply vm_only_with_vmmaps. reflexivity. Qed.

#[using="Type"] Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_vmmaps_forget_vm_ranges : forall l m, m_vmmaps (forget_vm_ranges l m) = m_vmmaps m.
Proof.
induction l as [|[a n] l IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|].
rewrite IH. apply m_vmmaps_vm_forget_range.
Qed.

#[using="Type"] Lemma m_vmmaps_with_brk_next : forall m req r,
m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof. intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges. apply m_vmmaps_with_vmmaps. Qed.

#[using="Type"] Lemma m_vmmaps_with_mmap_backing : forall f a n m, m_vmmaps (with_mmap_backing f a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b f); reflexivity. Qed.

#[using="Type"] Lemma m_vmmaps_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. intros. unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps. Qed.

#[using="Type"] Lemma m_vmmaps_with_mmap_replacement : forall f a n m, m_vmmaps (with_mmap_replacement f a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. apply m_vmmaps_vm_forget_range. Qed.

#[using="Type"] Lemma vm_only_backing_vmmaps : forall flags a n h m,
vm_init_sp h = vm_init_sp (m_vmmaps m) ->
mmap_noreserve_b flags = false -> vm_only m (with_mmap_backing flags a n (with_vmmaps h m)).
Proof.
intros. eapply vm_only_trans; [| apply vm_only_with_mmap_backing; assumption]. apply vm_only_with_vmmaps; assumption.
Qed.

#[using="Type"] Lemma vm_only_replacement_vmmaps : forall flags a n h m,
vm_init_sp h = vm_init_sp (m_vmmaps m) ->
mmap_noreserve_b flags = false -> vm_only m (with_mmap_replacement flags a n (with_vmmaps h m)).
Proof.
intros. eapply vm_only_trans; [| apply vm_only_with_mmap_replacement; assumption]. apply vm_only_with_vmmaps; assumption.
Qed.

#[using="Type"] Lemma vm_only_mremap_model_next : forall m old on dst nn,
vm_only m (mremap_model_next m old on dst nn).
Proof.
intros. unfold mremap_model_next.
eapply vm_only_trans; [apply (vm_only_with_vmmaps (mremap_maps_next (m_vmmaps m) old dst nn)); reflexivity|].
unfold vm_resize_backing. split; [repeat split; reflexivity|].
intros HL. unfold mremap_source_lazy_b.
assert (E : m_vm_lazy (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst nn) m) = []) by exact HL.
unfold m_vm_lazy in E |- *. cbn [m_vm with_vm_backing vmst_lazy]. rewrite E.
replace (vmst_lazy (m_vm m)) with (@nil (word * word)) by (symmetry; exact E).
cbn. reflexivity.
Qed.

#[local] Hint Resolve vm_only_refl vm_only_with_vmmaps vm_only_forget_range vm_only_with_mmap_backing
vm_only_with_mmap_destroyed vm_only_with_mmap_replacement vm_only_with_brk_next
vm_only_mprotect_model_next vm_only_backing_vmmaps vm_only_replacement_vmmaps vm_only_mremap_model_next : vmonly.

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

Ltac vm_only_done := split; [| reflexivity]; solve [auto with vmonly].

#[using="Type"] Lemma check_brk_shape : forall req eff m m' evs,
check_brk req eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof. intros req eff m m' evs H. unfold check_brk in H. crush_check H; vm_only_done. Qed.

#[using="Type"] Lemma check_mmap_shape : forall addr len prot flags fd off eff m m' evs,
mmap_noreserve_b flags = false ->
check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof. intros until evs; intros NR H. unfold check_mmap in H. crush_check H; vm_only_done. Qed.

#[using="Type"] Lemma check_munmap_shape : forall addr len eff m m' evs,
check_munmap addr len eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof. intros until evs; intros H. unfold check_munmap in H. crush_check H; vm_only_done. Qed.

#[using="Type"] Lemma check_mprotect_shape : forall addr len prot eff m m' evs,
check_mprotect addr len prot eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof. intros until evs; intros H. unfold check_mprotect in H. crush_check H; vm_only_done. Qed.

#[using="Type"] Lemma check_mremap_shape : forall old on nn fl eff m m' evs,
check_mremap old on nn fl eff m = CheckOk m' evs -> vm_only m m' /\ evs = [].
Proof. intros until evs; intros H. unfold check_mremap in H. crush_check H; vm_only_done. Qed.

#[using="Type"] Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> minv mo -> minv mo'.
Proof.
intros mo mo' Hv Hm. pose proof (vm_only_old _ _ Hv) as (Hf & Hs & _ & Ht & _).
destruct Hv as [(_ & _ & _ & _ & _ & _ & Hsp) HL]. unfold minv in *. rewrite Hf, Hs, Ht. destruct Hm as (HC & H0 & Hm).
split; [unfold alloc_top in *; rewrite Hsp; exact HC|]. split; [exact (HL H0)| exact Hm].
Qed.

#[using="Type"] Lemma mm_facts : forall ms mo n i x8 (chk : resp -> check_result) (side : Prop),
node_input n = Some i ->
(forall eff mo' evs, nstep n mo eff mo' evs <-> (evs = [] /\ side /\ syscall_spec i mo (Ok eff mo' evs))) ->
side ->
ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
(forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
(forall eff, check_syscall i eff mo = chk eff) ->
(forall eff, chk eff <> CheckUnmodeled) ->
(forall eff mo' evs, chk eff = CheckOk mo' evs -> vm_only mo mo' /\ evs = []) ->
node_facts ms mo n.
Proof.
intros ms mo n i x8 chk side Hi Hn Hside Hsvc Hminv Hh Hc1 Hc2 Hnu Hshape.
exists x8. split; [exact Hsvc|]. split; [|split].
- intros eff mo' evs. rewrite Hc1, Hn, <- check_syscall_ok_iff, Hc2. split; [|tauto].
intros H. split; [exact (proj2 (Hshape _ _ _ H))|]. split; [exact Hside| exact H].
- intros eff. rewrite Hc1. apply Hnu.
- intros eff mo' evs HP. apply Hn in HP as (_ & _ & HP). apply check_syscall_ok_iff in HP. rewrite Hc2 in HP.
apply Hshape in HP as [Hv _]. split.
+ destruct (vm_only_old _ _ Hv) as (_ & _ & -> & _). exact Hh.
+ eapply minv_vm_only; eassumption.
Qed.

Ltac dispatch_pure L :=
rewrite L by reflexivity; cbn [in_arg in_args nth pure_input].

#[using="Type"] Lemma brk_no_unmodeled : forall req eff m, check_brk req eff m <> CheckUnmodeled.
Proof.
intros req [r ws zs us cs cis] m. unfold check_brk.
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (_ && _ && _); discriminate.
Qed.

#[using="Type"] Lemma brk_facts : forall ms mo req,
at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo -> node_facts ms mo (NBrk req).
Proof.
intros ms mo req (Hsvc & Ha0) Hminv Hh _.
eapply (mm_facts ms mo (NBrk req) _ _ (fun eff => check_brk (Z_to_bv 64 req) eff mo) True);
[reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | | | |].
- intros eff. dispatch_with check_syscall_brk. rewrite Ha0. reflexivity.
- intros eff. dispatch_pure check_syscall_brk. reflexivity.
- intros eff. apply brk_no_unmodeled.
- intros eff mo' evs. apply check_brk_shape.
Qed.

#[using="Type"] Lemma mmap_facts : forall ms mo addr len prot flags,
at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
node_facts ms mo (NMmap addr len prot flags).
Proof.
intros ms mo addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hnr) Hminv Hh Hsafe.
eapply (mm_facts ms mo (NMmap addr len prot flags) _ _
(fun eff => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo)
(mmap_noreserve_b (Z_to_bv 64 flags) = false));
[reflexivity | intros; cbn [nstep node_input]; tauto | exact Hnr | exact Hsvc | exact Hminv | exact Hh | | | |].
- intros eff. dispatch_with check_syscall_mmap. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
- intros eff. dispatch_pure check_syscall_mmap. reflexivity.
- exact Hsafe.
- intros eff mo' evs. apply check_mmap_shape. exact Hnr.
Qed.

#[using="Type"] Lemma munmap_facts : forall ms mo addr len,
at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
node_facts ms mo (NMunmap addr len).
Proof.
intros ms mo addr len (Hsvc & Ha0 & Ha1) Hminv Hh Hsafe.
eapply (mm_facts ms mo (NMunmap addr len) _ _
(fun eff => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo) True);
[reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | | | |].
- intros eff. dispatch_with check_syscall_munmap. rewrite Ha0, Ha1. reflexivity.
- intros eff. dispatch_pure check_syscall_munmap. reflexivity.
- exact Hsafe.
- intros eff mo' evs. apply check_munmap_shape.
Qed.

#[using="Type"] Lemma mprotect_facts : forall ms mo addr len prot,
at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
node_facts ms mo (NMprotect addr len prot).
Proof.
intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
eapply (mm_facts ms mo (NMprotect addr len prot) _ _
(fun eff => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo) True);
[reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | | | |].
- intros eff. dispatch_with check_syscall_mprotect. rewrite Ha0, Ha1, Ha2. reflexivity.
- intros eff. dispatch_pure check_syscall_mprotect. reflexivity.
- exact Hsafe.
- intros eff mo' evs. apply check_mprotect_shape.
Qed.

#[using="Type"] Lemma mremap_facts : forall ms mo old on nn fl,
at_node segs (NMremap old on nn fl) ms -> minv mo -> m_halted mo = None -> nsafe (NMremap old on nn fl) mo ->
node_facts ms mo (NMremap old on nn fl).
Proof.
intros ms mo old on nn fl (Hsvc & Ha0 & Ha1 & Ha2 & Ha3) Hminv Hh Hsafe.
eapply (mm_facts ms mo (NMremap old on nn fl) _ _
(fun eff => check_mremap (Z_to_bv 64 old) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 fl) eff mo) True);
[reflexivity | intros; cbn [nstep node_input]; tauto | exact I | exact Hsvc | exact Hminv | exact Hh | | | |].
- intros eff. dispatch_with check_syscall_mremap. rewrite Ha0, Ha1, Ha2, Ha3. reflexivity.
- intros eff. dispatch_pure check_syscall_mremap. reflexivity.
- exact Hsafe.
- intros eff mo' evs. apply check_mremap_shape.
Qed.

#[using="Type"] Lemma nstep_brk_iff : forall req mo eff mo' evs,
nstep (NBrk req) mo eff mo' evs <-> check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs.
Proof.
intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure check_syscall_brk.
split; [tauto|]. intros H. split; [exact (proj2 (check_brk_shape _ _ _ _ _ H))|]. split; [exact I| exact H].
Qed.

#[using="Type"] Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
nstep (NMmap addr len prot flags) mo eff mo' evs <->
mmap_noreserve_b (Z_to_bv 64 flags) = false /\
check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof.
intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure check_syscall_mmap.
split; [tauto|]. intros [NR H]. split; [exact (proj2 (check_mmap_shape _ _ _ _ _ _ _ _ _ _ NR H))|]. split; [exact NR| exact H].
Qed.

#[using="Type"] Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
nstep (NMunmap addr len) mo eff mo' evs <->
check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof.
intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure check_syscall_munmap.
split; [tauto|]. intros H. split; [exact (proj2 (check_munmap_shape _ _ _ _ _ _ H))|]. split; [exact I| exact H].
Qed.

#[using="Type"] Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
nstep (NMprotect addr len prot) mo eff mo' evs <->
check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs.
Proof.
intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure check_syscall_mprotect.
split; [tauto|]. intros H. split; [exact (proj2 (check_mprotect_shape _ _ _ _ _ _ _ H))|]. split; [exact I| exact H].
Qed.

#[using="Type"] Lemma nstep_mremap_iff : forall old on nn fl mo eff mo' evs,
nstep (NMremap old on nn fl) mo eff mo' evs <->
check_mremap (Z_to_bv 64 old) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 fl) eff mo = CheckOk mo' evs.
Proof.
intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure check_syscall_mremap.
split; [tauto|]. intros H. split; [exact (proj2 (check_mremap_shape _ _ _ _ _ _ _ _ H))|]. split; [exact I| exact H].
Qed.

#[using="Type"] Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ _ => True | _ => False end ->
nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [].
Proof.
intros n mo eff mo' evs Hn H. destruct n; try contradiction.
- apply nstep_brk_iff in H. eapply check_brk_shape; exact H.
- apply nstep_mmap_iff in H as [NR H]. eapply check_mmap_shape; [exact NR| exact H].
- apply nstep_munmap_iff in H. eapply check_munmap_shape; exact H.
- apply nstep_mprotect_iff in H. eapply check_mprotect_shape; exact H.
- apply nstep_mremap_iff in H. eapply check_mremap_shape; exact H.
Qed.

Ltac no_unm :=
repeat first [ apply check_ret_only_no_unmodeled
| discriminate
| match goal with |- (match ?x with _ => _ end) <> _ => destruct x end
| progress cbv zeta beta iota ].

#[using="Type"] Lemma nsafe_mmap_rw : forall addr len mo,
nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
intros addr len mo eff. unfold check_mmap.
replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
replace (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true by (vm_compute; reflexivity).
replace (mmap_plain_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true by (vm_compute; reflexivity).
replace (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))
(Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
cbn [negb]. destruct (w_is0 _); [apply check_ret_only_no_unmodeled|]. no_unm.
Qed.

#[using="Type"] Lemma nsafe_mmap_none : forall addr len mo,
nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
intros addr len mo eff. unfold check_mmap.
replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
replace (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true by (vm_compute; reflexivity).
replace (mmap_plain_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true by (vm_compute; reflexivity).
replace (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))
(Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
replace (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))
(Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
cbn [negb]. destruct (w_is0 _); [apply check_ret_only_no_unmodeled|]. no_unm.
Qed.

#[using="Type"] Lemma nsafe_munmap_has : forall addr len mo,
(bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) < two_pow_64)%Z ->
map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true ->
nsafe (NMunmap addr len) mo.
Proof.
intros addr len mo Hb Hhas eff. unfold check_munmap.
destruct (negb _ || w_is0 _); [no_unm|]. cbv zeta.
destruct (TASK_SIZE <? _)%Z; [no_unm|].
rewrite Hhas. no_unm.
Qed.

#[using="Type"] Lemma nsafe_mprotect_contains : forall addr len prot mo,
mprotect_modeled_b (Z_to_bv 64 prot) = true ->
map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr)
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true ->
map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true ->
nsafe (NMprotect addr len prot) mo.
Proof.
intros addr len prot mo Hp Hna Hm eff. unfold check_mprotect.
destruct (mprotect_grows_conflict_b _); [no_unm|].
destruct (negb (_ =? 0)); [no_unm|]. destruct (w_is0 _); [no_unm|].
destruct (two_pow_64 <=? _); [no_unm|]. rewrite Hp. cbn [negb]. cbv zeta. rewrite Hna, Hm. cbn [andb]. no_unm.
Qed.

#[using="Type"] Lemma alloc_fd_range : forall mo,
minv mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096.
Proof.
intros mo (MC & ML & M0 & M1 & M2 & _) Hfree. pose proof (alloc_fd_le (m_fds mo)) as Hle.
set (fd := alloc_fd (m_fds mo)) in *.
assert (H : forall z e, fd_lookup (m_fds mo) (Z_to_bv 64 z) = Some e -> 0 <= z < 2^64 -> bv_unsigned fd <> z).
{ intros z e Hz Hr E. rewrite <- (Z_to_bv_bv_unsigned fd), E in Hfree. congruence. }
pose proof (H 0 _ M0 ltac:(lia)). pose proof (H 1 _ M1 ltac:(lia)). pose proof (H 2 _ M2 ltac:(lia)).
pose proof (bv_unsigned_in_range 64 fd). lia.
Qed.

#[using="Type"] Lemma minv_preserved : forall n mo eff mo' evs,
minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
intros n mo eff mo' evs Hminv Hh H.
destruct n; cbn [nstep] in H; try contradiction.
- destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; auto.
split; [rewrite m_halted_with_tid; exact Hh|]. apply minv_with_tid; assumption.
- destruct (nstep_mm_vm_only (NBrk req) mo eff mo' evs I H) as [Hv _].
split; [destruct (vm_only_old _ _ Hv) as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; eassumption].
- destruct (nstep_mm_vm_only (NMmap addr len prot flags) mo eff mo' evs I H) as [Hv _].
split; [destruct (vm_only_old _ _ Hv) as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; eassumption].
- destruct (nstep_mm_vm_only (NMunmap addr len) mo eff mo' evs I H) as [Hv _].
split; [destruct (vm_only_old _ _ Hv) as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; eassumption].
- destruct (nstep_mm_vm_only (NMprotect addr len prot) mo eff mo' evs I H) as [Hv _].
split; [destruct (vm_only_old _ _ Hv) as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; eassumption].
- destruct (nstep_mm_vm_only (NMremap old oldlen newlen flags) mo eff mo' evs I H) as [Hv _].
split; [destruct (vm_only_old _ _ Hv) as (_ & _ & -> & _); exact Hh | eapply minv_vm_only; eassumption].
Qed.

#[using="Type"] Lemma all_facts : forall n ms mo,
match n with NExit _ => False | _ => True end ->
at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts ms mo n.
Proof.
intros n ms mo Hne Hat Hminv Hh Hsafe. destruct n; try contradiction;
try (exfalso; exact (proj1 Hat)).
- apply set_tid_facts; assumption.
- apply brk_facts; assumption.
- apply mmap_facts; assumption.
- apply munmap_facts; assumption.
- apply mprotect_facts; assumption.
- apply mremap_facts; assumption.
Qed.

End PerNode.
End RC__2.

#[export] Hint Extern 1 (vm_init_sp _ = vm_init_sp _) => reflexivity : vmonly.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

#[using="Type"] Lemma exit_node_facts : forall segs ms mo c,
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

#[using="Type"] Lemma nonexit_node_facts : forall segs n ms mo,
match n with NExit _ => False | _ => True end ->
at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
/\ (forall eff mo' evs, nstep n mo eff mo' evs ->
m_halted mo' = None /\ minv mo' /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
/\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
intros segs n ms mo Hne Hat Hminv Hh Hsafe.
destruct (all_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (x8 & Hsvc & Hchar & Hnu & Hpres).
destruct (node_kit segs ms mo x8 (nstep n mo) Hsvc Hh Hchar Hnu) as (Hc & Hs & Hp).
{ intros eff mo' evs HP. exact (proj1 (Hpres _ _ _ HP)). }
{ intros eff mo' evs HP. exact (proj1 (proj2 (proj2 (Hpres _ _ _ HP)))). }
split; [exact Hc|]. split; [|exact Hp].
intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. auto.
Qed.

#[using="Type"] Theorem nodes_sound : forall segs, node_sound node segs (at_node segs) nstep nexit minv nsafe.
Proof.
intros segs. constructor.
-
intros mo HM. exact (proj1 (proj2 HM)).
-
intros n ms Hat.
assert (Hx : exists x8, ms_svc_pending ms = Some x8).
{ destruct n as [| | | | | | |c| | | | |]; cbn [at_node] in Hat;
first [ solve [destruct Hat as [F _]; destruct F]
| solve [destruct Hat as [[H|H] _]; eexists; exact H]
| solve [destruct Hat as [H _]; eexists; exact H]
| solve [eexists; exact Hat] ]. }
destruct Hx as [x8 ->]. discriminate.
-
intros n ms mo evs X Hat Hh Hminv Hsafe Hst.
assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
{ destruct n; first [left; eexists; reflexivity | right; exact I]. }
destruct Hcase as [[c ->] | Hne].
+ destruct (exit_node_facts segs ms mo c Hat Hh) as [Hc _]. destruct (Hc _ _ Hst) as [-> ->].
right. eexists _, _. split; [reflexivity|]. split; [split; reflexivity| reflexivity].
+ destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (Hc & _ & _). left. exact (Hc _ _ Hst).
-
intros n ms mo rsp mo' evs Hat Hh Hminv Hsafe HP.
assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct HP]).
destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & Hs & _). exact (Hs _ _ _ HP).
-
intros n ms mo code mo' Hat Hh Hminv Hsafe HX.
destruct n as [| | | | | | |c| | | | |]; try contradiction. cbn [nexit] in HX. destruct HX as [-> ->].
split; [apply m_halted_with_halted|]. exact (proj2 (exit_node_facts segs ms mo c Hat Hh)).
-
intros n ms mo Hat Hh Hminv Hsafe.
assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
{ destruct n; first [left; eexists; reflexivity | right; exact I]. }
destruct Hcase as [[c ->] | Hne].
+ right. eexists _, _. split; reflexivity.
+ destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & _ & Hp). left. exact Hp.
Qed.

End RC__3.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.
Import ListNotations.
Open Scope bv_scope.

Definition mkR (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : bvmap 5 word :=
TNode
(TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
(Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
None
(TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
(TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))).

Lemma mkR_spec : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
bvmap_set (Z_to_bv 5 31) x31 (bvmap_set (Z_to_bv 5 30) x30 (bvmap_set (Z_to_bv 5 29) x29 (bvmap_set (Z_to_bv 5 28) x28 (
bvmap_set (Z_to_bv 5 27) x27 (bvmap_set (Z_to_bv 5 26) x26 (bvmap_set (Z_to_bv 5 25) x25 (bvmap_set (Z_to_bv 5 24) x24 (
bvmap_set (Z_to_bv 5 23) x23 (bvmap_set (Z_to_bv 5 22) x22 (bvmap_set (Z_to_bv 5 21) x21 (bvmap_set (Z_to_bv 5 20) x20 (
bvmap_set (Z_to_bv 5 19) x19 (bvmap_set (Z_to_bv 5 18) x18 (bvmap_set (Z_to_bv 5 17) x17 (bvmap_set (Z_to_bv 5 16) x16 (
bvmap_set (Z_to_bv 5 15) x15 (bvmap_set (Z_to_bv 5 14) x14 (bvmap_set (Z_to_bv 5 13) x13 (bvmap_set (Z_to_bv 5 12) x12 (
bvmap_set (Z_to_bv 5 11) x11 (bvmap_set (Z_to_bv 5 10) x10 (bvmap_set (Z_to_bv 5 9) x9 (bvmap_set (Z_to_bv 5 8) x8 (
bvmap_set (Z_to_bv 5 7) x7 (bvmap_set (Z_to_bv 5 6) x6 (bvmap_set (Z_to_bv 5 5) x5 (bvmap_set (Z_to_bv 5 4) x4 (
bvmap_set (Z_to_bv 5 3) x3 (bvmap_set (Z_to_bv 5 2) x2 (bvmap_set (Z_to_bv 5 1) x1 bvmap_empty)))))))))))))))))))))))))))))).
Proof. intros. vm_compute. reflexivity. Qed.

Definition ivl := (Z * Z)%type.

Fixpoint outside (W : list ivl) (x : Z) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => ~ (lo <= x < hi)%Z /\ outside W' x
end.

Fixpoint inside (W : list ivl) (a : Z) (n : Z) : Prop :=
match W with
| [] => False
| (lo, hi) :: W' => (lo <= a /\ a + n <= hi)%Z \/ inside W' a n
end.

Fixpoint disjoint_from (W : list ivl) (a : Z) (n : Z) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (a + n <= lo \/ hi <= a)%Z /\ disjoint_from W' a n
end.

Lemma inside_not_outside : forall W a n x, inside W a n -> (a <= x < a + n)%Z -> ~ outside W x.
Proof.
induction W as [|[lo hi] W IH]; cbn; intros a n x Hin Hx; [tauto|].
intros [H1 H2]. destruct Hin as [Hin|Hin]; [lia|]. exact (IH _ _ _ Hin Hx H2).
Qed.

Lemma disjoint_outside : forall W a n x, disjoint_from W a n -> (a <= x < a + n)%Z -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; cbn; intros a n x Hd Hx; [exact I|].
destruct Hd as [H1 H2]. split; [lia|]. eauto.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition munch (W : list ivl) (m m' : word -> option byte) : Prop :=
forall x : word, outside W (bv_unsigned x) -> m' x = m x.
Definition wmono (m m' : word -> option byte) : Prop :=
forall x : word, wview segs m x <> None -> wview segs m' x <> None.

#[using="Type"] Lemma munch_refl : forall W m, munch W m m. Proof. intros W m x _; reflexivity. Qed.
#[using="Type"] Lemma wmono_refl : forall m, wmono m m. Proof. intros m x H; exact H. Qed.
#[using="Type"] Lemma wmono_trans : forall m1 m2 m3, wmono m1 m2 -> wmono m2 m3 -> wmono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
#[using="Type"] Lemma munch_trans : forall W m1 m2 m3, munch W m1 m2 -> munch W m2 m3 -> munch W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

Definition sub_fp (W W' : list ivl) : Prop := forall x, outside W' x -> outside W x.
#[using="Type"] Lemma munch_weaken : forall W W' m m', sub_fp W W' -> munch W m m' -> munch W' m m'.
Proof. intros W W' m m' Hs H x Hx. apply H, Hs, Hx. Qed.

#[using="Type"] Lemma munch_write : forall W m0 m a bs,
munch W m0 m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
inside W a (Z.of_nat (length bs)) ->
munch W m0 (write_to_mem m (wa a) bs).
Proof.
intros W m0 m a bs H Ha Hl Hin x Hx. rewrite write_to_mem_spec by lia.
pose proof (bv_unsigned_in_range 64 x).
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb];
try (apply H; exact Hx).
exfalso. eapply (inside_not_outside W a _ (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Type"] Lemma wmono_write : forall m0 m a bs, wmono m0 m -> wmono m0 (write_to_mem m a bs).
Proof. intros m0 m a bs H x Hx. apply wview_write_mono. apply H, Hx. Qed.

#[using="Type"] Lemma bytes_at_transport : forall W m m' A bs,
bytes_at segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) ->
bytes_at segs m' A bs.
Proof.
intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
intros i Hi. unfold mrd. rewrite Hm.
- apply H. exact Hi.
- eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma wr_at_transport : forall m m' A n, wr_at segs m A n -> wmono m m' -> wr_at segs m' A n.
Proof. intros m m' A n (Ha & Hn & H) Hw. split; [lia|]. split; [lia|]. intros i Hi. apply Hw, H, Hi. Qed.

#[using="Type"] Lemma rw_cells_transport : forall W m m' A cs,
rw_cells segs m A cs -> munch W m m' -> wmono m m' ->
disjoint_from W A (Z.of_nat (cells_size cs)) ->
rw_cells segs m' A cs.
Proof.
intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
- eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
- eapply wr_at_transport; eauto.
Qed.

#[using="Type"] Lemma ro_cells_transport : forall W m m' A cs,
ro_cells segs m A cs -> munch W m m' ->
disjoint_from W A (Z.of_nat (cells_size cs)) ->
ro_cells segs m' A cs.
Proof.
intros W m m' A cs [Hwf Hb] Hm Hd. split; [exact Hwf|].
eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

Definition stk (m : word -> option byte) (lo hi : Z) : Prop :=
(0 <= lo)%Z /\ (hi <= 2^64)%Z /\
forall a, (lo <= a < hi)%Z -> wview segs m (wa a) <> None /\ exists b, mrd segs m (wa a) = Some b.

#[using="Type"] Lemma stk_split : forall m lo mid hi, stk m lo hi -> (lo <= mid <= hi)%Z -> stk m lo mid /\ stk m mid hi.
Proof. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.

#[using="Type"] Lemma stk_merge : forall m lo mid hi, stk m lo mid -> stk m mid hi -> (lo <= mid <= hi)%Z -> stk m lo hi.
Proof.
intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B) Hm. split; [lia|]. split; [lia|].
intros a Ha. destruct (Z.ltb_spec0 a mid); [apply A | apply B]; lia.
Qed.

#[using="Type"] Lemma stk_empty : forall m lo, (0 <= lo <= 2^64)%Z -> stk m lo lo.
Proof. intros. split; [lia|]. split; [lia|]. intros a Ha. lia. Qed.

#[using="Type"] Lemma stk_bytes : forall m lo hi, stk m lo hi -> (lo <= hi)%Z ->
exists bs, length bs = Z.to_nat (hi - lo) /\ bytes_at segs m lo bs.
Proof.
intros m lo hi (H1 & H2 & H) Hle.
set (n := Z.to_nat (hi - lo)).
assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
{ induction k as [|k IH]; intros Hk.
- exists []. split; [reflexivity|]. intros i Hi; lia.
- destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
destruct (H (lo + Z.of_nat k)%Z ltac:(lia)) as [_ (b & Hb)].
exists (bs ++ [b]). split. { rewrite app_length; cbn; lia. }
intros i Hi. destruct (Nat.eqb_spec i k).
+ subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
+ rewrite nth_error_app1 by lia. apply Hbs. lia. }
destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

#[using="Type"] Lemma stk_carve : forall m lo hi (n : nat),
stk m lo hi -> (lo <= hi - Z.of_nat n)%Z ->
stk m lo (hi - Z.of_nat n) /\ exists junk, rw_cells segs m (hi - Z.of_nat n) [CB n junk].
Proof.
intros m lo hi n Hs Hle. pose proof Hs as (H1 & H2 & H).
destruct (stk_split m lo (hi - Z.of_nat n) hi Hs ltac:(lia)) as [Hlo Hhi].
split; [exact Hlo|].
destruct (stk_bytes m (hi - Z.of_nat n) hi Hhi ltac:(lia)) as (bs & Hlen & Hb).
exists bs. split.
- split. { cbn. split; [lia|exact I]. }
cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
- cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
intros i Hi. apply H. lia.
Qed.

#[using="Type"] Lemma stk_of_rw_cells : forall m A cs,
rw_cells segs m A cs -> stk m A (A + Z.of_nat (cells_size cs)).
Proof.
intros m A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)].
rewrite cells_bytes_length in Hl, Hb by assumption.
split; [lia|]. split; [lia|]. intros a Hr. split.
- replace a with (A + (a - A))%Z by lia. apply Hw. lia.
- replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
Qed.

#[using="Type"] Lemma stk_release : forall m lo A cs,
stk m lo A -> rw_cells segs m A cs -> (lo <= A)%Z ->
stk m lo (A + Z.of_nat (cells_size cs)).
Proof.
intros m lo A cs Hs Hc Hle. pose proof (rw_cells_bound segs m A cs Hc).
eapply stk_merge; [exact Hs | apply stk_of_rw_cells; exact Hc | lia].
Qed.

#[using="Type"] Lemma stk_write : forall m lo hi a bs,
stk m lo hi -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z -> stk (write_to_mem m (wa a) bs) lo hi.
Proof.
intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)]. split.
- apply wview_write_mono. exact Hw.
- unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

#[using="Type"] Lemma stk_transport : forall W m m' lo hi,
stk m lo hi -> munch W m m' -> wmono m m' ->
(forall x, (lo <= x < hi)%Z -> outside W x \/ exists b, m' (wa x) = Some b) ->
stk m' lo hi.
Proof.
intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
destruct (Hcase a Ha) as [Ho | (b' & Hb')].
- exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
- exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.

#[using="Type"] Lemma stk_transport_disjoint : forall W m m' lo hi,
stk m lo hi -> munch W m m' -> wmono m m' -> disjoint_from W lo (hi - lo) -> stk m' lo hi.
Proof.
intros. eapply stk_transport; eauto. intros x Hx. left. eapply disjoint_outside; eauto. lia.
Qed.

End WithSegs.
