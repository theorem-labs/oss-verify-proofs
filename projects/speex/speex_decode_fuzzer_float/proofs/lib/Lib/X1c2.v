(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Common Require Import CfgStep.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Export X1c7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Export X1c1.
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

Abbreviation node := X1c1.node (only parsing).
Abbreviation NWrite := X1c1.NWrite (only parsing).
Abbreviation NWritev := X1c1.NWritev (only parsing).
Abbreviation NOpen := X1c1.NOpen (only parsing).
Abbreviation NRead := X1c1.NRead (only parsing).
Abbreviation NClose := X1c1.NClose (only parsing).
Abbreviation NIoctl := X1c1.NIoctl (only parsing).
Abbreviation NSetTid := X1c1.NSetTid (only parsing).
Abbreviation NExit := X1c1.NExit (only parsing).
Abbreviation NBrk := X1c1.NBrk (only parsing).
Abbreviation NMmap := X1c1.NMmap (only parsing).
Abbreviation NMunmap := X1c1.NMunmap (only parsing).
Abbreviation NMprotect := X1c1.NMprotect (only parsing).

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
| NWrite fd bs =>
ms_svc_pending ms = Some (Z_to_bv 64 64) /\
(fd = 1 \/ fd = 2) /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 12 = Z_to_bv 64 (Z.of_nat (length bs)) /\
1 <= Z.of_nat (length bs) <= rw_bytes_max /\
ms_rom ms = seg_rom segs /\
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
| NWritev fd bufs =>
ms_svc_pending ms = Some (Z_to_bv 64 66) /\
(fd = 1 \/ fd = 2) /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
(length bufs <= 1024)%nat /\
Z.of_nat (length (concat bufs)) <= node_rw_max /\
ms_rom ms = seg_rom segs /\
bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE /\
exists iovs : list (word * word),
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
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
1 <= count <= access_ok_walk_max /\ buf + count <= TASK_SIZE /\
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
unfold TASK_SIZE, access_ok_walk_max in *;
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

Definition cfg_ok (r : SyscallEffect -> bool) (spec : Sys SyscallEffect) (i : SyscallInput) (m : Model)
(o : outcome SyscallEffect) : Prop :=
spec i m o /\ forall eff m' evs, o = Ok eff m' evs -> r eff = true ->
forall eff' m'' evs', spec i m (Ok eff' m'' evs') -> r eff' = true.

Definition mmap_r (eff : SyscallEffect) : bool := ret_in_errnos mmap_errnos (eff_ret eff).
Definition mprot_r (eff : SyscallEffect) : bool := ret_in_errnos mprotect_errnos (eff_ret eff).

Lemma cfg_ok_unmodeled : forall r spec i m, cfg_ok r spec i m Unmodeled <-> spec i m Unmodeled.
Proof. intros r spec i m. split; [intros [H _]; exact H|]. intros H. split; [exact H|]. intros eff m' evs E. discriminate E. Qed.

Lemma cfg_ok_det : forall r spec i m o0, (forall o, spec i m o <-> o = o0) -> forall o, cfg_ok r spec i m o <-> o = o0.
Proof.
intros r spec i m o0 Hd o. split; [intros [H _]; apply Hd; exact H|]. intros ->. split; [apply Hd; reflexivity|].
intros eff m' evs E Hr eff' m'' evs' Hs. apply Hd in Hs. rewrite <- Hs in E. injection E as -> _ _. exact Hr.
Qed.

Lemma ret_in_enomem_errno : forall e, In e mmap_errnos -> ret_in_errnos mmap_errnos (errno_ret e) = true.
Proof. intros e He. apply ret_in_errnos_errno. exact He. Qed.

Lemma ret_in_enomem_below : forall r, (bv_unsigned r <= 2 ^ 64 - 4096)%Z -> ret_in_errnos mmap_errnos r = false.
Proof. intros r Hr. apply ret_in_errnos_below; [exact enomem_window| exact Hr]. Qed.

Lemma grant_addr_below : forall h (a : word) nZ, (0 <= nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z ->
(bv_unsigned a <= 2 ^ 64 - 4096)%Z.
Proof. intros h a nZ Hn H. pose proof (alloc_top_room h). unfold stack_max_size, two_pow_64 in *. lia. Qed.

Lemma grant_not_refusable_of : forall flags m nZ (a : word),
(bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z -> (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
mmap_noreserve_backed_ok flags m nZ = true -> mmap_grant_refusable flags m nZ = false.
Proof.
intros flags m nZ a H1 H2 H3 H4 H5. unfold mmap_grant_refusable. rewrite H5.
rewrite (proj2 (vm_gap_available_iff _ _)); [reflexivity|]. exists a. repeat split; assumption.
Qed.

Lemma reserve_not_refusable_of : forall m nZ (a : word),
(bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z -> (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
mmap_reserve_refusable m nZ = false.
Proof.
intros m nZ a H1 H2 H3 H4. unfold mmap_reserve_refusable.
rewrite (proj2 (vm_gap_available_iff _ _)); [reflexivity|]. exists a. repeat split; assumption.
Qed.

Lemma mmap_rw_outcome : forall addr len prot flags fd off i m o,
w_is0 len = false ->
mmap_modeled_b prot flags off = true ->
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
cfg_ok mmap_r (mmap_spec addr len prot flags fd off) i m o <->
(mmap_grant_refusable flags m nZ = true /\ mmap_err_out m o)
\/ exists a, ((bv_unsigned a mod page_size = 0)%Z
/\ (0 < bv_unsigned a)%Z
/\ (bv_unsigned a + nZ <= alloc_top h)%Z
/\ region_free (vm_reserved h ++ vm_maps h) a n = true
/\ mmap_noreserve_backed_ok flags m nZ = true)
/\ o = Ok (mkEffect a [] [(a, n)])
(with_mmap_backing flags a n
(with_vmmaps
(mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
(vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
intros addr len prot flags fd off i m o Hlen Hmod. cbv zeta.
pose proof (fun o => mmap_rw_outcome_u addr len prot flags fd off i m o Hlen Hmod) as U. cbv zeta in U.
pose proof (page_round_up_Z_nonneg (bv_unsigned len) (proj1 (word_unsigned_range len))) as Hn0.
unfold cfg_ok. split.
- intros [Hs Hf]. apply U in Hs. destruct Hs as [He | Hg]; [left | right; exact Hg]. split; [| exact He].
  destruct (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len))) eqn:Hr; [reflexivity| exfalso].
  destruct (grant_witness _ _ _ Hr) as (a & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  destruct He as (e & Hin & ->).
  assert (Hg : mmap_spec addr len prot flags fd off i m (Ok (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
  (with_mmap_backing flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) :: vm_maps (m_vmmaps m))
  (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
  (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m)) [])).
  { apply U. right. exists a. split; [repeat split; assumption| reflexivity]. }
  pose proof (Hf _ _ _ eq_refl (ret_in_enomem_errno e Hin) _ _ _ Hg) as Hr'.
  unfold mmap_r in Hr'. cbn [eff_ret] in Hr'. rewrite ret_in_enomem_below in Hr'; [discriminate|].
  exact (grant_addr_below _ _ _ Hn0 Ha3).
- intros [[Hr He] | Hg].
  + split; [apply U; left; exact He|]. intros eff m' evs E _ eff' m'' evs' Hs'.
    apply U in Hs'. destruct Hs' as [(e' & Hin' & E') | (a & (H1 & H2 & H3 & H4 & H5) & E')].
    * injection E' as -> _ _. apply ret_in_enomem_errno. exact Hin'.
    * exfalso. rewrite (grant_not_refusable_of flags m _ a H1 H2 H3 H4 H5) in Hr. discriminate Hr.
  + split; [apply U; right; exact Hg|]. intros eff m' evs E Href.
    destruct Hg as (a & (H1 & H2 & H3 & H4 & H5) & E'). rewrite E' in E. injection E as <- _ _.
    unfold mmap_r in Href. cbn [eff_ret] in Href. rewrite ret_in_enomem_below in Href; [discriminate|].
    exact (grant_addr_below _ _ _ Hn0 H3).
Qed.

Lemma mmap_noaccess_outcome : forall addr len prot flags fd off i m o,
w_is0 len = false ->
mmap_modeled_b prot flags off = false ->
mmap_noaccess_b prot flags off = true ->
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
cfg_ok mmap_r (mmap_spec addr len prot flags fd off) i m o <->
(mmap_reserve_refusable m nZ = true /\ mmap_err_out m o)
\/ exists a, ((bv_unsigned a mod page_size = 0)%Z
/\ (0 < bv_unsigned a)%Z
/\ (bv_unsigned a + nZ <= alloc_top h)%Z
/\ region_free (vm_reserved h ++ vm_maps h) a n = true)
/\ o = Ok (mkEffectU a [] [] [(a, n)] [] [])
(with_mmap_backing flags a n
(with_vmmaps
(mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
(vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
intros addr len prot flags fd off i m o Hlen Hmod Hna. cbv zeta.
pose proof (fun o => mmap_noaccess_outcome_u addr len prot flags fd off i m o Hlen Hmod Hna) as U. cbv zeta in U.
pose proof (page_round_up_Z_nonneg (bv_unsigned len) (proj1 (word_unsigned_range len))) as Hn0.
unfold cfg_ok. split.
- intros [Hs Hf]. apply U in Hs. destruct Hs as [He | Hg]; [left | right; exact Hg]. split; [| exact He].
  destruct (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len))) eqn:Hr; [reflexivity| exfalso].
  destruct (reserve_witness _ _ Hr) as (a & Ha1 & Ha2 & Ha3 & Ha4).
  destruct He as (e & Hin & ->).
  assert (Hg : mmap_spec addr len prot flags fd off i m (Ok (mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [])
  (with_mmap_backing flags a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) :: vm_maps (m_vmmaps m))
  ((a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) :: vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
  (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m)) [])).
  { apply U. right. exists a. split; [repeat split; assumption| reflexivity]. }
  pose proof (Hf _ _ _ eq_refl (ret_in_enomem_errno e Hin) _ _ _ Hg) as Hr'.
  unfold mmap_r in Hr'. cbn [eff_ret] in Hr'. rewrite ret_in_enomem_below in Hr'; [discriminate|].
  exact (grant_addr_below _ _ _ Hn0 Ha3).
- intros [[Hr He] | Hg].
  + split; [apply U; left; exact He|]. intros eff m' evs E _ eff' m'' evs' Hs'.
    apply U in Hs'. destruct Hs' as [(e' & Hin' & E') | (a & (H1 & H2 & H3 & H4) & E')].
    * injection E' as -> _ _. apply ret_in_enomem_errno. exact Hin'.
    * exfalso. rewrite (reserve_not_refusable_of m _ a H1 H2 H3 H4) in Hr. discriminate Hr.
  + split; [apply U; right; exact Hg|]. intros eff m' evs E Href.
    destruct Hg as (a & (H1 & H2 & H3 & H4) & E'). rewrite E' in E. injection E as <- _ _.
    unfold mmap_r in Href. cbn [eff_ret] in Href. rewrite ret_in_enomem_below in Href; [discriminate|].
    exact (grant_addr_below _ _ _ Hn0 H3).
Qed.

Lemma mmap_fixed_noaccess_outcome : forall addr len prot flags fd off i m o,
w_is0 len = false ->
mmap_modeled_b prot flags off = false ->
mmap_noaccess_b prot flags off = false ->
mmap_fixed_noaccess_b prot flags off = true ->
let h := m_vmmaps m in
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
(bv_unsigned addr + nZ <= alloc_top h)%Z ->
(bv_unsigned addr mod page_size = 0)%Z ->
(0 < bv_unsigned addr)%Z ->
region_free (vm_reserved h) addr n = true ->
map_contains (vm_maps h) addr n = true ->
cfg_ok mmap_r (mmap_spec addr len prot flags fd off) i m o <->
o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
(with_mmap_replacement flags addr n
(with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
((addr, n) :: maps_subtract (vm_noaccess h)
(bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
intros addr len prot flags fd off i m o Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
pose proof (page_round_up_Z_nonneg (bv_unsigned len) (proj1 (word_unsigned_range len))) as Hn0.
destruct (mmap_fixed_noaccess_outcome_u addr len prot flags fd off i m o Hlen Hmod Hna Hfx Hce Hal Hpos Hrf Hmc) as [H0 Hc].
cbv zeta in H0, Hc.
assert (Hr0 : ret_in_errnos mmap_errnos addr = false) by (apply ret_in_enomem_below; exact (grant_addr_below _ _ _ Hn0 Hce)).
unfold cfg_ok. split.
- intros [Hs Hf]. destruct (Hc Hs) as [E | (e & ws & zs & us & cs & cps & m' & evs & Hin & ->)]; [exact E| exfalso].
  pose proof (Hf _ _ _ eq_refl (ret_in_enomem_errno e Hin) _ _ _ H0) as Hr'.
  unfold mmap_r in Hr'. cbn [eff_ret] in Hr'. rewrite Hr0 in Hr'. discriminate Hr'.
- intros ->. split; [exact H0|]. intros eff m' evs E Href. injection E as <- _ _.
  unfold mmap_r in Href. cbn [eff_ret] in Href. rewrite Hr0 in Href. discriminate Href.
Qed.

Lemma mprotect_expose_outcome : forall addr len prot i m o,
mprotect_grows_conflict_b prot = false ->
(bv_unsigned addr mod page_size = 0)%Z ->
w_is0 len = false ->
(bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
mprotect_modeled_b prot = true ->
let h := m_vmmaps m in
let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
map_contains (vm_noaccess h) addr n = true ->
map_contains (vm_maps h) addr n = true ->
cfg_ok mprot_r (mprotect_spec addr len prot) i m o <->
(mprotect_refusable m addr n = true
/\ exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
\/ (mprotect_budget_ok m addr n = true
/\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) []).
Proof.
intros addr len prot i m o Hgc Hal Hlen Hnw Hmod. cbv zeta. intros Hna Hma.
pose proof (fun o => mprotect_expose_outcome_u addr len prot i m o Hgc Hal Hlen Hnw Hmod Hna Hma) as U. cbv zeta in U.
assert (Hr0 : ret_in_errnos mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
unfold cfg_ok. split.
- intros [Hs Hf]. apply U in Hs. destruct Hs as [He | Hg]; [left | right; exact Hg]. split; [| exact He].
  destruct (mprotect_refusable m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hr; [reflexivity| exfalso].
  pose proof (mprotect_witness _ _ _ Hr) as Hb.
  destruct He as (e & Hin & ->).
  assert (Hg : mprotect_spec addr len prot i m (Ok (mkEffect (Z_to_bv 64 0) [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
  (mprotect_model_next m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) [])).
  { apply U. right. split; [exact Hb| reflexivity]. }
  pose proof (Hf _ _ _ eq_refl (ret_in_errnos_errno _ _ Hin) _ _ _ Hg) as Hr'.
  unfold mprot_r in Hr'. cbn [eff_ret] in Hr'. rewrite Hr0 in Hr'. discriminate Hr'.
- intros [[Hr He] | Hg].
  + split; [apply U; left; exact He|]. intros eff m' evs E _ eff' m'' evs' Hs'.
    apply U in Hs'. destruct Hs' as [(e' & Hin' & E') | (Hb & E')].
    * injection E' as -> _ _. apply ret_in_errnos_errno. exact Hin'.
    * exfalso. unfold mprotect_refusable in Hr. rewrite Hb in Hr. discriminate Hr.
  + split; [apply U; right; exact Hg|]. intros eff m' evs E Href.
    destruct Hg as (Hb & E'). rewrite E' in E. injection E as <- _ _.
    unfold mprot_r in Href. cbn [eff_ret] in Href. rewrite Hr0 in Href. discriminate Href.
Qed.

Lemma mprotect_outcome : forall addr len prot i m o,
cfg_ok mprot_r (mprotect_spec addr len prot) i m o <-> mprotect_out addr len prot m o.
Proof.
intros addr len prot i m o.
pose proof (fun o => mprotect_outcome_u addr len prot i m o) as U.
unfold mprotect_out_u in U. unfold mprotect_out. cbv zeta in *.
destruct (mprotect_grows_conflict_b prot) eqn:Hgc; rewrite ?Hgc in U; cbv iota in U; [apply cfg_ok_det; exact U|].
destruct (negb (bv_unsigned addr mod page_size =? 0)%Z) eqn:Hal; rewrite ?Hal in U; cbv iota in U; [apply cfg_ok_det; exact U|].
destruct (w_is0 len) eqn:Hlen; rewrite ?Hlen in U; cbv iota in U; [apply cfg_ok_det; exact U|].
destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z eqn:Hw; rewrite ?Hw in U; cbv iota in U;
[apply cfg_ok_det; exact U|].
destruct (mprotect_modeled_b prot) eqn:Hmod; rewrite ?Hmod in U; cbv iota in U; [| apply cfg_ok_det; exact U].
destruct (map_contains (vm_noaccess (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) &&
map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hc.
- apply andb_prop in Hc as [Hc1 Hc2].
  apply (mprotect_expose_outcome addr len prot i m o Hgc); [| exact Hlen| | exact Hmod| exact Hc1| exact Hc2].
  + apply negb_false_iff, Z.eqb_eq in Hal. exact Hal.
  + apply Z.leb_gt in Hw. exact Hw.
- rewrite ?Hc in U. cbv iota in U.
  destruct (map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) &&
  region_free (vm_noaccess (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hf;
  rewrite ?Hf in U; cbv iota in U; apply cfg_ok_det; exact U.
Qed.

Lemma spurious_ext : forall cfg i i' m eff,
in_sysno i = in_sysno i' -> in_arg i 0 = in_arg i' 0 -> (forall o, syscall_spec i m o <-> syscall_spec i' m o) ->
spurious_refusal_cfg cfg i m eff <-> spurious_refusal_cfg cfg i' m eff.
Proof.
intros cfg i i' m eff Hn Ha Hs. unfold spurious_refusal_cfg, injected_family_off, refusal_b. rewrite Hn, Ha.
split; intros (H1 & H2 & eff' & m' & evs' & H3 & H4); (split; [exact H1|]); (split; [exact H2|]);
exists eff', m', evs'; (split; [apply Hs; exact H3 | exact H4]).
Qed.

Lemma exists_not_spurious : forall cfg i m, (exists eff m' evs, syscall_spec i m (Ok eff m' evs)) ->
exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
intros cfg i m (eff & m' & evs & H).
destruct (Classical_Prop.classic (exists eff' m'' evs', syscall_spec i m (Ok eff' m'' evs') /\ refusal_b i m (eff_ret eff') = false))
as [(eff' & m'' & evs' & H' & Hr) | Hn].
- exists eff', m'', evs'. split; [exact H'|]. apply spurious_refusal_not_refusal. exact Hr.
- exists eff, m', evs. split; [exact H|]. intros (_ & _ & Hex). exact (Hn Hex).
Qed.

Lemma not_spurious_iff : forall i m eff (r : SyscallEffect -> bool) (spec : Sys SyscallEffect),
injected_family_off kit_cfg i = true ->
(forall e, refusal_b i m (eff_ret e) = r e) ->
(forall o, syscall_spec i m o <-> spec i m o) ->
(~ spurious_refusal_cfg kit_cfg i m eff <->
(r eff = true -> forall eff' m' evs', spec i m (Ok eff' m' evs') -> r eff' = true)).
Proof.
intros i m eff r spec Hoff Hrb Hspec. split.
- intros Hns Hr eff' m' evs' Hs. destruct (r eff') eqn:E; [reflexivity|]. exfalso. apply Hns.
  split; [exact Hoff|]. split; [rewrite Hrb; exact Hr|]. exists eff', m', evs'.
  split; [apply Hspec; exact Hs| rewrite Hrb; exact E].
- intros H (_ & Hr & eff' & m' & evs' & Hs & Hr'). rewrite Hrb in Hr, Hr'. apply Hspec in Hs.
  rewrite (H Hr _ _ _ Hs) in Hr'. discriminate Hr'.
Qed.

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition ecore (e : resp) : resp :=
mkEffectU (eff_ret e) (eff_writes e) (eff_zeros e) (eff_unmaps e) (eff_copies e) [].

Lemma nret_ecore : forall ms e, nret ms (ecore e) = nret ms e.
Proof. reflexivity. Qed.
Lemma ecore_ecore : forall e, ecore (ecore e) = ecore e.
Proof. reflexivity. Qed.
Lemma ecore_mk : forall r ws zs us cs cps, ecore (mkEffectU r ws zs us cs cps) = mkEffectU r ws zs us cs [].
Proof. reflexivity. Qed.
Lemma ecore_eff0 : forall r, ecore (eff0 r) = eff0 r.
Proof. reflexivity. Qed.
Lemma ecore_with_copyins : forall R e, ecore (with_copyins R e) = ecore e.
Proof. reflexivity. Qed.

Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
(exists e, In e openat_errnos /\ ecore eff = efferr e /\ mo' = mo)
\/ (let fd := alloc_fd (m_fds mo) in
fd_lookup (m_fds mo) fd = None /\ ecore eff = eff0 fd /\
mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition short_write (fd : Z) (bs : list byte) (eff : resp) (evs : list event) : Prop :=
exists k, (1 <= k <= length bs)%nat /\
ecore eff = eff0 (Z_to_bv 64 (Z.of_nat k)) /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k bs).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
match n with
| NWrite fd bs => mo' = mo /\ short_write fd bs eff evs
| NWritev fd bufs =>
mo' = mo /\
(if (length (concat bufs) =? 0)%nat
then ecore eff = eff0 (Z_to_bv 64 0) /\ evs = []
else short_write fd (concat bufs) eff evs)
| NOpen path =>
evs = [] /\
if (path_max <=? length path)%nat then ecore eff = efferr ENAMETOOLONG /\ mo' = mo
else match path with
| [] => ecore eff = efferr ENOENT /\ mo' = mo
| _ => if path_eqb path dot_path then open_result mo FdDir eff mo'
else match fs_lookup (m_fs mo) path with
| None => ecore eff = efferr ENOENT /\ mo' = mo
| Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
end
end
| NRead fd buf count =>
evs = [] /\
match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => ecore eff = efferr EBADF /\ mo' = mo
| Some FdDir => ecore eff = efferr EISDIR /\ mo' = mo
| Some (FdFile p off) =>
match fs_lookup (m_fs mo) p with
| None => False
| Some data =>
let bs := file_read data off (Z_to_bv 64 count) in
ecore eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
end
| Some (FdChannel _) | Some (FdFileW _ _) | Some (FdFileA _ _) | Some (FdFileRW _ _)
| Some (FdSocket _) | Some (FdPipe _ _) | Some (FdDevNull _ _) | Some FdUrandom => False
end
| NClose fd =>
evs = [] /\ 3 <= fd < 2^32 /\

match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => ecore eff = efferr EBADF /\ mo' = mo
| Some _ => ecore eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
end
| NIoctl fd req => evs = [] /\ ecore eff = efferr ENOTTY /\ mo' = mo
| NSetTid =>
evs = [] /\ exists t, ecore eff = eff0 t /\
match m_tid mo with
| Some t0 => t = t0 /\ mo' = mo
| None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
end
| NExit _ => False
| NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>
evs = [] /\
match node_input n with
| Some i => syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg kit_cfg i mo eff
| None => False
end
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
(forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileW p off) /\
fd_lookup (m_fds mo) k <> Some (FdFileA p off) /\
fd_lookup (m_fds mo) k <> Some (FdFileRW p off)) /\
(forall k s, fd_lookup (m_fds mo) k <> Some (FdSocket s)) /\
(forall k pid w, fd_lookup (m_fds mo) k <> Some (FdPipe pid w)) /\
(forall k rd wr, fd_lookup (m_fds mo) k <> Some (FdDevNull rd wr)) /\
(forall k, fd_lookup (m_fds mo) k <> Some FdUrandom) /\
(forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
m_vm_lazy mo = [].

Ltac minv_intro M :=
destruct M as (M0 & M1 & M2 & MC & MF & MW & MS & MP & MN & MU & MT & ML).

Lemma minv_nolazy : forall mo, minv mo -> m_vm_lazy mo = [].
Proof. intros mo H. unfold minv in H. tauto. Qed.

Lemma m_vm_lazy_init_model : forall reserved brk mbase sp lim inp,
m_vm_lazy (init_model reserved brk mbase sp lim inp) = [].
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_fds : forall v m, m_vm_lazy (with_fds v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_tid : forall v m, m_vm_lazy (with_tid v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_halted : forall v m, m_vm_lazy (with_halted v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_stdin : forall v m, m_vm_lazy (with_stdin v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_fds m_vm_lazy_with_tid m_vm_lazy_with_halted m_vm_lazy_with_stdin : model.

Lemma fd_lookup_init3 : forall reserved brk mbase sp lim inp k e,
fd_lookup (m_fds (init_model reserved brk mbase sp lim inp)) k = Some e ->
bv_unsigned k < 3 /\ e = FdChannel k.
Proof.
intros reserved brk mbase sp lim inp k e H. rewrite m_fds_init_model in H. cbn [fd_lookup] in H.
destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0.
{ apply bv_eqb_eq in E0. subst k. injection H as <-. split; [vm_compute; reflexivity| reflexivity]. }
destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1.
{ apply bv_eqb_eq in E1. subst k. injection H as <-. split; [vm_compute; reflexivity| reflexivity]. }
destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2.
{ apply bv_eqb_eq in E2. subst k. injection H as <-. split; [vm_compute; reflexivity| reflexivity]. }
discriminate H.
Qed.

Lemma minv_init : forall reserved brk mbase sp lim inp, minv (init_model reserved brk mbase sp lim inp).
Proof.
intros. unfold minv. rewrite m_tid_init_model, m_vm_lazy_init_model.
split; [rewrite m_fds_init_model; reflexivity|].
split; [rewrite m_fds_init_model; reflexivity|].
split; [rewrite m_fds_init_model; reflexivity|].
split; [intros k c H; exact (proj1 (fd_lookup_init3 _ _ _ _ _ _ _ _ H))|].
split; [intros k p off H; apply fd_lookup_init3 in H as [_ H]; discriminate H|].
split; [intros k p off; repeat split; intros H; apply fd_lookup_init3 in H as [_ H]; discriminate H|].
split; [intros k s H; apply fd_lookup_init3 in H as [_ H]; discriminate H|].
split; [intros k pid w H; apply fd_lookup_init3 in H as [_ H]; discriminate H|].
split; [intros k rd wr H; apply fd_lookup_init3 in H as [_ H]; discriminate H|].
split; [intros k H; apply fd_lookup_init3 in H as [_ H]; discriminate H|].
split; [intros t H; discriminate H| reflexivity].
Qed.

Definition nsafe (n : node) (mo : Model) : Prop :=
match n with
| NMmap _ _ _ flags =>
mmap_noreserve_b (Z_to_bv 64 flags) = false /\
match node_input n with Some i => ~ syscall_spec i mo Unmodeled | None => False end
| NBrk _ | NMunmap _ _ | NMprotect _ _ _ =>
match node_input n with Some i => ~ syscall_spec i mo Unmodeled | None => False end
| NOpen path =>

path_has_slash path = false /\ path_eqb path dotdot_path = false
| _ => True
end.

Section Generic.
Variable segs : list Segment.

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
\/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
\/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
- left. eexists _, _, _. eauto.
- right; left. eexists _, _, _. eauto.
- right; right; left. eexists _, _, _, _. eauto 6.
- right; right; right; left. eexists _, _, _, _. eauto.
- right; right; right; right. auto.
Qed.

#[using="Type"] Lemma node_kit : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> P eff mo' evs) ->
(forall eff mo' evs, P eff mo' evs ->
exists eff', ecore eff' = ecore eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)) ->
(~ syscall_spec (sys_input segs ms x8) mo Unmodeled) ->
(forall eff mo' evs, P eff mo' evs -> m_halted mo' = None /\ m_vm_lazy mo' = []) ->
(exists eff mo' evs, P eff mo' evs) ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
/\ (forall eff mo' evs, P eff mo' evs -> sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
/\ (exists eff mo' evs, P eff mo' evs).
Proof.
intros ms mo x8 P Hsvc Hh Hc Hs Hnu Hpost Hprog. split; [|split; [|exact Hprog]].
- intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
as [(eff & mo' & mo'' & Hsp & Hh' & Hmat & ->)
|[(eff & mo' & evs0 & Hsp & Hh' & Hmat & -> & ->)
|[(eff & mo' & evs0 & code & Hsp & Hh' & Hk' & -> & ->)
|[(eff & mo' & evs0 & sig & Hsp & Hk' & -> & ->)
| (Hsp & -> & ->)]]]].
+ pose proof (Hc _ _ _ Hsp) as HP. destruct (Hpost _ _ _ HP) as [_ Hl].
rewrite (materialize_model_accesses_no_lazy _ _ Hl) in Hmat. injection Hmat as <-.
exists eff, mo'. split; [reflexivity| exact HP].
+ exfalso. pose proof (Hc _ _ _ Hsp) as HP. destruct (Hpost _ _ _ HP) as [_ Hl].
rewrite (materialize_model_accesses_no_lazy _ _ Hl) in Hmat. discriminate Hmat.
+ exfalso. pose proof (Hc _ _ _ Hsp) as HP. destruct (Hpost _ _ _ HP) as [Hh'' _]. congruence.
+
exfalso. pose proof (Hc _ _ _ Hsp) as HP. destruct (Hpost _ _ _ HP) as [Hh'' _].
rewrite (m_killed_of_m_halted_none _ Hh'') in Hk'. discriminate Hk'.
+ exfalso. exact (Hnu Hsp).
- intros eff mo' evs HP. destruct (Hs _ _ _ HP) as (eff' & Heq & Hsp). destruct (Hpost _ _ _ HP) as [Hh' Hl].
rewrite <- (nret_ecore ms eff), <- Heq, nret_ecore. unfold nret.
eapply sstep_syscall; [exact Hh| exact Hsvc| exact Hsp| exact Hh'|].
apply materialize_model_accesses_no_lazy. exact Hl.
Qed.

#[using="Type"] Lemma exit_kit : forall ms mo x8 code,
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (eff0 (Z_to_bv 64 0)) (with_halted code mo) []) ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
/\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
intros ms mo x8 code Hsvc Hh Hchar. split.
- intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
as [(eff & mo' & mo'' & Hsp & Hh' & Hmat & ->)
|[(eff & mo' & evs0 & Hsp & Hh' & Hmat & -> & ->)
|[(eff & mo' & evs0 & code' & Hsp & Hh' & Hk' & -> & ->)
|[(eff & mo' & evs0 & sig & Hsp & Hk' & -> & ->)
| (Hsp & -> & ->)]]]].
+ exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_halted_with_halted in Hh'. discriminate.
+ exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_halted_with_halted in Hh'. discriminate.
+ apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & ->). rewrite m_halted_with_halted in Hh'. injection Hh' as <-.
rewrite m_fs_with_halted. split; reflexivity.
+
exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_killed_with_halted in Hk'. discriminate.
+ exfalso. apply Hchar in Hsp. exact (Unmodeled_Ok _ _ _ Hsp).
- change [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))]).
eapply sstep_exit; [exact Hh| exact Hsvc| | apply m_halted_with_halted| apply m_killed_with_halted].
apply Hchar. reflexivity.
Qed.

#[using="Type"] Lemma sstep_cfg_svc_inv : forall ms mo x8 evs X,
ms_svc_pending ms = Some x8 -> sstep_cfg segs kit_cfg (mkCfg ms mo) evs X ->
(exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\
~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
X = SNext (mkCfg (nret ms eff) mo''))
\/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = None /\
materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\
evs = [] /\ X = SError)
\/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
m_killed mo' = None /\
evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
\/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
\/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
- left. eexists _, _, _. eauto 7.
- right; left. eexists _, _, _. eauto.
- right; right; left. eexists _, _, _, _. eauto 6.
- right; right; right; left. eexists _, _, _, _. eauto.
- right; right; right; right. auto.
Qed.

#[using="Type"] Lemma node_kit_c : forall ms mo x8 (P : resp -> Model -> list event -> Prop),
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_halted mo' = None /\ m_vm_lazy mo' = []) ->
(forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) mo eff -> P eff mo' evs) ->
(forall eff mo' evs, P eff mo' evs ->
exists eff', ecore eff' = ecore eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)
/\ ~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) mo eff') ->
(~ syscall_spec (sys_input segs ms x8) mo Unmodeled) ->
(exists eff mo' evs, P eff mo' evs) ->
(forall evs X, sstep_cfg segs kit_cfg (mkCfg ms mo) evs X ->
exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ P eff mo' evs)
/\ (forall eff mo' evs, P eff mo' evs -> sstep_cfg segs kit_cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
/\ (exists eff mo' evs, P eff mo' evs).
Proof.
intros ms mo x8 P Hsvc Hh Hall Hc Hs Hnu Hprog. split; [|split; [|exact Hprog]].
- intros evs X Hst. destruct (sstep_cfg_svc_inv _ _ _ _ _ Hsvc Hst)
  as [(eff & mo' & mo'' & Hsp & Hns & Hh' & Hmat & ->)
  |[(eff & mo' & evs0 & Hsp & Hh' & Hmat & -> & ->)
  |[(eff & mo' & evs0 & code & Hsp & Hh' & Hk' & -> & ->)
  |[(eff & mo' & evs0 & sig & Hsp & Hk' & -> & ->)
  | (Hsp & -> & ->)]]]].
  + destruct (Hall _ _ _ Hsp) as [_ Hl].
    rewrite (materialize_model_accesses_no_lazy _ _ Hl) in Hmat. injection Hmat as <-.
    exists eff, mo'. split; [reflexivity| exact (Hc _ _ _ Hsp Hns)].
  + exfalso. destruct (Hall _ _ _ Hsp) as [_ Hl].
    rewrite (materialize_model_accesses_no_lazy _ _ Hl) in Hmat. discriminate Hmat.
  + exfalso. destruct (Hall _ _ _ Hsp) as [Hh'' _]. congruence.
  + exfalso. destruct (Hall _ _ _ Hsp) as [Hh'' _].
    rewrite (m_killed_of_m_halted_none _ Hh'') in Hk'. discriminate Hk'.
  + exfalso. exact (Hnu Hsp).
- intros eff mo' evs HP. destruct (Hs _ _ _ HP) as (eff' & Heq & Hsp & Hns). destruct (Hall _ _ _ Hsp) as [Hh' Hl].
  rewrite <- (nret_ecore ms eff), <- Heq, nret_ecore. unfold nret.
  eapply sstep_cfg_syscall; [exact Hh| exact Hsvc| exact Hsp| exact Hns| exact Hh'|].
  apply materialize_model_accesses_no_lazy. exact Hl.
Qed.

#[using="Type"] Lemma exit_kit_c : forall ms mo x8 code,
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (eff0 (Z_to_bv 64 0)) (with_halted code mo) []) ->
(forall evs X, sstep_cfg segs kit_cfg (mkCfg ms mo) evs X ->
X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
/\ sstep_cfg segs kit_cfg (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
intros ms mo x8 code Hsvc Hh Hchar. split.
- intros evs X Hst. destruct (sstep_cfg_svc_inv _ _ _ _ _ Hsvc Hst)
  as [(eff & mo' & mo'' & Hsp & _ & Hh' & Hmat & ->)
  |[(eff & mo' & evs0 & Hsp & Hh' & Hmat & -> & ->)
  |[(eff & mo' & evs0 & code' & Hsp & Hh' & Hk' & -> & ->)
  |[(eff & mo' & evs0 & sig & Hsp & Hk' & -> & ->)
  | (Hsp & -> & ->)]]]].
  + exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_halted_with_halted in Hh'. discriminate.
  + exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_halted_with_halted in Hh'. discriminate.
  + apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & ->). rewrite m_halted_with_halted in Hh'. injection Hh' as <-.
    rewrite m_fs_with_halted. split; reflexivity.
  + exfalso. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite m_killed_with_halted in Hk'. discriminate.
  + exfalso. apply Hchar in Hsp. exact (Unmodeled_Ok _ _ _ Hsp).
- change [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))]).
  eapply sstep_cfg_exit; [exact Hh| exact Hsvc| | apply m_halted_with_halted| apply m_killed_with_halted].
  apply Hchar. reflexivity.
Qed.

End Generic.

Section PerNode.
Variable segs : list Segment.

Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
exists x8, ms_svc_pending ms = Some x8 /\
(forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> nstep n mo eff mo' evs) /\
(forall eff mo' evs, nstep n mo eff mo' evs ->
exists eff', ecore eff' = ecore eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)) /\
(~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
(forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo') /\
(exists eff mo' evs, nstep n mo eff mo' evs).

Definition node_facts_c (ms : machine_state) (mo : Model) (n : node) : Prop :=
exists x8, ms_svc_pending ms = Some x8 /\
(forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> m_halted mo' = None /\ m_vm_lazy mo' = []) /\
(forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) mo eff -> nstep n mo eff mo' evs) /\
(forall eff mo' evs, nstep n mo eff mo' evs ->
exists eff', ecore eff' = ecore eff /\ syscall_spec (sys_input segs ms x8) mo (Ok eff' mo' evs)
/\ ~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) mo eff') /\
(~ syscall_spec (sys_input segs ms x8) mo Unmodeled) /\
(forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo') /\
(exists eff mo' evs, nstep n mo eff mo' evs).

#[using="Type"] Lemma facts_c_of_facts : forall ms mo n,
node_facts ms mo n ->
(forall x8, ms_svc_pending ms = Some x8 -> injected_family_off kit_cfg (sys_input segs ms x8) = false) ->
node_facts_c ms mo n.
Proof.
intros ms mo n (x8 & Hsvc & Hc & Hs & Hnu & Hpost & Hprog) Hoff. exists x8. split; [exact Hsvc|].
split; [|split; [|split; [|split; [|split]]]].
- intros eff mo' evs Hsp. destruct (Hpost _ _ _ (Hc _ _ _ Hsp)) as [H1 H2]. split; [exact H1| exact (minv_nolazy _ H2)].
- intros eff mo' evs Hsp _. exact (Hc _ _ _ Hsp).
- intros eff mo' evs HP. destruct (Hs _ _ _ HP) as (eff' & He & Hsp). exists eff'. split; [exact He|]. split; [exact Hsp|].
  apply spurious_refusal_family_on. exact (Hoff x8 Hsvc).
- exact Hnu.
- exact Hpost.
- exact Hprog.
Qed.

#[using="Type"] Lemma pending_on_at : forall ms K, ms_svc_pending ms = Some (Z_to_bv 64 K) -> 0 <= K < 2^64 ->
alloc_no_b K = false ->
forall x8, ms_svc_pending ms = Some x8 -> injected_family_off kit_cfg (sys_input segs ms x8) = false.
Proof.
intros ms K H HK Ha x8 Hx. rewrite H in Hx. injection Hx as <-.
rewrite (injected_family_off_alloc_only kit_cfg _ kit_cfg_alloc_only). rewrite in_sysno_si, unsigned_lit by exact HK. exact Ha.
Qed.

#[using="Type"] Lemma facts_det : forall ms mo n x8 e0 m0 evs0,
ms_svc_pending ms = Some x8 -> m_halted m0 = None -> minv m0 ->
(forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok e0 m0 evs0) ->
(forall eff mo' evs, nstep n mo eff mo' evs <-> (ecore eff = ecore e0 /\ mo' = m0 /\ evs = evs0)) ->
node_facts ms mo n.
Proof.
intros ms mo n x8 e0 m0 evs0 Hsvc Hh0 Hminv0 Hchar Hn. exists x8. split; [exact Hsvc|].
split; [|split; [|split; [|split]]].
- intros eff mo' evs Hsp. apply Hchar in Hsp. apply Ok_inj in Hsp as (-> & -> & ->). apply Hn. repeat split; reflexivity.
- intros eff mo' evs HP. apply Hn in HP as (He & -> & ->). exists e0. split; [symmetry; exact He|]. apply Hchar. reflexivity.
- intros Hsp. apply Hchar in Hsp. exact (Unmodeled_Ok _ _ _ Hsp).
- intros eff mo' evs HP. apply Hn in HP as (_ & -> & _). split; assumption.
- exists e0, m0, evs0. apply Hn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma sysno_si : forall ms K, 0 <= K < 2^64 -> bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 K))) = K.
Proof. intros ms K HK. rewrite in_sysno_si. apply unsigned_lit. exact HK. Qed.

#[using="Type"] Lemma fd32_small : forall z, 0 <= z < 2^32 -> fd32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold fd32, abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma cmd32_small : forall z, 0 <= z < 2^32 -> cmd32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold cmd32, abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

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

#[using="Type"] Lemma minv_remove : forall mo fd, minv mo -> 3 <= fd < 2^32 ->
minv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
intros mo fd M Hfd. minv_intro M. unfold minv. autorewrite with model.
rewrite !fd_lookup_remove.
assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
{ intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
rewrite !Hne by lia.
split; [exact M0|]. split; [exact M1|]. split; [exact M2|].
split; [intros k c; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [discriminate| apply MC]|].
split; [intros k p off; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [discriminate| apply MF]|].
split; [intros k p off; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [repeat split; discriminate| apply MW]|].
split; [intros k s; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [discriminate| apply MS]|].
split; [intros k pid w; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [discriminate| apply MP]|].
split; [intros k rd wr; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [discriminate| apply MN]|].
split; [intros k; rewrite fd_lookup_remove; destruct (bv_eqb _ k); [discriminate| apply MU]|].
split; [exact MT| exact ML].
Qed.

#[using="Type"] Lemma minv_with_tid : forall mo t, minv mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minv (with_tid t mo).
Proof.
intros mo t M Ht. minv_intro M. unfold minv. autorewrite with model.
split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|].
split; [exact MW|]. split; [exact MS|]. split; [exact MP|]. split; [exact MN|]. split; [exact MU|]. split; [| exact ML].
intros t' Ht'. injection Ht' as <-. exact Ht.
Qed.

#[using="Type"] Lemma close_facts : forall ms mo fd,
at_node segs (NClose fd) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NClose fd).
Proof.
intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
assert (Hdisp : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 57)) mo o <->
close_spec (Z_to_bv 64 fd) (sys_input segs ms (Z_to_bv 64 57)) mo o).
{ intros o. rewrite syscall_spec_57 by (apply sysno_si; lia). rewrite in_a0_si, Ha0, fd32_small by lia. reflexivity. }
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
- eapply (facts_det ms mo (NClose fd) _ (eff0 (Z_to_bv 64 0)) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []);
[exact Hsvc| rewrite m_halted_with_fds; exact Hh| apply minv_remove; assumption| |].
+ intros o. rewrite Hdisp. apply (close_outcome _ _ _ _ _ Hlk).
+ intros eff mo' evs. cbn [nstep]. rewrite Hlk. rewrite ecore_eff0. tauto.
- eapply (facts_det ms mo (NClose fd) _ (efferr EBADF) mo []);
[exact Hsvc| exact Hh| exact Hminv| |].
+ intros o. rewrite Hdisp. apply (close_ebadf_outcome _ _ _ _ Hlk).
+ intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr. rewrite ecore_eff0. tauto.
Qed.

#[using="Type"] Lemma ioctl_facts : forall ms mo fd req,
at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NIoctl fd req).
Proof.
intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh.
assert (He : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
{ pose proof Hminv as M. minv_intro M.
assert (Hc : fd = 0 \/ fd = 1 \/ fd = 2) by lia.
destruct Hc as [-> | [-> | ->]]; eexists; eassumption. }
destruct He as [c Hlk].
eapply (facts_det ms mo (NIoctl fd req) _ (efferr ENOTTY) mo []); [exact Hsvc| exact Hh| exact Hminv| |].
- intros o. rewrite syscall_spec_29 by (apply sysno_si; lia). rewrite in_a0_si, in_a1_si, Ha0, Ha1.
rewrite fd32_small, cmd32_small by lia.
apply (ioctl_tty_outcome _ _ _ _ _ _ Hlk); [discriminate|]. subst req. reflexivity.
- intros eff mo' evs. cbn [nstep]. unfold efferr. rewrite ecore_eff0. tauto.
Qed.

#[using="Type"] Lemma set_tid_facts : forall ms mo,
at_node segs NSetTid ms -> minv mo -> m_halted mo = None -> node_facts ms mo NSetTid.
Proof.
intros ms mo Hsvc Hminv Hh.
assert (Hdisp : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 96)) mo o <->
set_tid_address_spec (sys_input segs ms (Z_to_bv 64 96)) mo o).
{ intros o. rewrite syscall_spec_96 by (apply sysno_si; lia). reflexivity. }
destruct (m_tid mo) as [t0|] eqn:Htid.
- eapply (facts_det ms mo NSetTid _ (eff0 t0) mo []); [exact Hsvc| exact Hh| exact Hminv| |].
+ intros o. rewrite Hdisp. apply (set_tid_known_outcome _ _ _ _ Htid).
+ intros eff mo' evs. cbn [nstep]. rewrite Htid, ecore_eff0. split.
* intros (-> & t & Ht & -> & ->). repeat split; try reflexivity. exact Ht.
* intros (He & -> & ->). split; [reflexivity|]. exists t0. repeat split; try reflexivity. exact He.
- exists (Z_to_bv 64 96). split; [exact Hsvc|].
assert (Hout : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 96)) mo o <->
exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE) /\ o = Ok (mkEffect t [] []) (with_tid t mo) []).
{ intros o. rewrite Hdisp. apply (set_tid_fresh_outcome _ _ _ Htid). }
split; [|split; [|split; [|split]]].
+ intros eff mo' evs Hsp. apply Hout in Hsp as (t & Ht & E). apply Ok_inj in E as (-> & -> & ->).
cbn [nstep]. rewrite Htid. split; [reflexivity|]. exists t. split; [reflexivity|]. split; [lia| reflexivity].
+ intros eff mo' evs HP. cbn [nstep] in HP. rewrite Htid in HP. destruct HP as (-> & t & He & Ht & ->).
exists (eff0 t). split; [rewrite ecore_eff0; symmetry; exact He|]. apply Hout. exists t. split; [exact Ht| reflexivity].
+ intros Hsp. apply Hout in Hsp as (t & _ & E). exact (Unmodeled_Ok _ _ _ E).
+ intros eff mo' evs HP. cbn [nstep] in HP. rewrite Htid in HP. destruct HP as (-> & t & He & Ht & ->).
split; [rewrite m_halted_with_tid; exact Hh| apply minv_with_tid; assumption].
+ exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) mo), []. cbn [nstep]. rewrite Htid.
split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|]. split; [| reflexivity].
unfold PID_MAX_ENVELOPE. rewrite unsigned_lit by lia. lia.
Qed.

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

#[using="Type"] Lemma exit_outcome_at : forall ms mo c x8,
at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 ->
forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (eff0 (Z_to_bv 64 0)) (with_halted (exit_code c) mo) [].
Proof.
intros ms mo c x8 [Hsvc Ha0] Hx8 o.
destruct Hsvc as [Hsvc|Hsvc]; rewrite Hsvc in Hx8; injection Hx8 as <-;
[rewrite syscall_spec_93 by (apply sysno_si; lia) | rewrite syscall_spec_94 by (apply sysno_si; lia)];
rewrite in_a0_si, Ha0; apply exit_outcome.
Qed.

#[using="Type"] Lemma length_file_read_le : forall data off c, (length (file_read data off c) <= word_to_nat c)%nat.
Proof. intros. rewrite file_read_unguarded. apply firstn_le_length. Qed.

#[using="Type"] Lemma minv_update_file : forall mo k p off off',
minv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
minv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
intros mo k p off off' M Hk. minv_intro M. unfold minv. autorewrite with model.
assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
{ intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
split; [exact M0|]. split; [exact M1|]. split; [exact M2|].
split; [intros k' c; rewrite fd_lookup_insert; destruct (bv_eqb k k'); [intros H; discriminate| apply MC]|].
split. { intros k' p' o. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MF].
intros H. inversion H; subst. exact (MF _ _ _ Hk). }
split; [intros k' p' o; rewrite fd_lookup_insert; destruct (bv_eqb k k'); [repeat split; discriminate| apply MW]|].
split; [intros k' s; rewrite fd_lookup_insert; destruct (bv_eqb k k'); [discriminate| apply MS]|].
split; [intros k' pid w; rewrite fd_lookup_insert; destruct (bv_eqb k k'); [discriminate| apply MP]|].
split; [intros k' rd wr; rewrite fd_lookup_insert; destruct (bv_eqb k k'); [discriminate| apply MN]|].
split; [intros k'; rewrite fd_lookup_insert; destruct (bv_eqb k k'); [discriminate| apply MU]|].
split; [exact MT| exact ML].
Qed.

#[using="Type"] Lemma wr_at_bound : forall m a n, wr_at segs m a n -> 0 <= a /\ a + n <= 2^64.
Proof. intros m a n (Ha & Hn & _). lia. Qed.

#[using="Type"] Lemma read_dest_ok : forall ms buf count k,
wr_at segs (ms_mem ms) buf count -> 1 <= count <= access_ok_walk_max -> 0 <= k <= count ->
exists w, read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 k) = Some w.
Proof.
intros ms buf count k Hwr Hc Hk. rewrite read_bytes_map_eq. unfold ms_writable_byte.
pose proof (wr_at_bound _ _ _ Hwr) as Hb.
unfold word_to_nat. rewrite unsigned_lit by (unfold access_ok_walk_max in Hc; lia).
change (Z_to_bv 64 buf) with (wa buf).
destruct (read_bytes_aux (wview segs (ms_mem ms)) (wa buf) (Z.to_nat k)) as [w|] eqn:E; [exists w; reflexivity|].
exfalso. assert (Hk' : Z.of_nat (Z.to_nat k) <= count) by (rewrite Z2Nat.id; lia).
exact (read_bytes_aux_wr_at _ _ _ _ _ Hwr Hk' E).
Qed.

#[using="Type"] Lemma read_access_okb : forall ms buf count,
wr_at segs (ms_mem ms) buf count -> 1 <= count <= access_ok_walk_max -> buf + count <= TASK_SIZE ->
access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true.
Proof.
intros ms buf count Hwr Hc Hhi. pose proof (wr_at_bound _ _ _ Hwr) as Hb.
unfold access_ok_walk_max in Hc. unfold TASK_SIZE in Hhi.
apply access_okb_intro. unfold TASK_SIZE. rewrite !unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma read_facts : forall ms mo fd buf count,
at_node segs (NRead fd buf count) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NRead fd buf count).
Proof.
intros ms mo fd buf count (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hhi & Hwr) Hminv Hh.
pose proof Hminv as M. minv_intro M. pose proof (wr_at_bound _ _ _ Hwr) as Hb.
assert (Hdisp : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 63)) mo o <->
read_spec (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) (sys_input segs ms (Z_to_bv 64 63)) mo o).
{ intros o. rewrite syscall_spec_63 by (apply sysno_si; lia). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2, fd32_small by lia. reflexivity. }
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|nrd nwr| ]|] eqn:Hlk.
-
exfalso. apply MC in Hlk. rewrite unsigned_lit in Hlk by lia. lia.
-
destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
set (bs := file_read data off (Z_to_bv 64 count)).
assert (Hclamp : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
{ rewrite rw_count_clamp_small by (unfold MAX_RW_COUNT; unfold access_ok_walk_max in Hc; rewrite unsigned_lit by lia; lia).
apply Z_to_bv_bv_unsigned. }
assert (Hlen : Z.of_nat (length bs) <= count).
{ pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
unfold word_to_nat in L. rewrite unsigned_lit in L by (unfold access_ok_walk_max in Hc; lia). lia. }
destruct (read_dest_ok ms buf count (Z.of_nat (length bs)) Hwr Hc ltac:(lia)) as [w Hw].
eapply (facts_det ms mo (NRead fd buf count) _
(mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [])
(with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo) []);
[exact Hsvc| rewrite m_halted_with_fds; exact Hh| eapply minv_update_file; eassumption| |].
+ intros o. rewrite Hdisp.
pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count)
(sys_input segs ms (Z_to_bv 64 63)) mo o p off data w Hlk) as R.
rewrite Hclamp in R. apply R.
* apply (read_access_okb ms); assumption.
* exact Hfs.
* rewrite in_wmem_si. exact Hw.
+ intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. fold bs. cbv zeta. rewrite ecore_mk. tauto.
-   exfalso. exact (proj1 (MW _ _ _) Hlk).
-   exfalso. exact (proj1 (proj2 (MW _ _ _)) Hlk).
-   exfalso. exact (proj2 (proj2 (MW _ _ _)) Hlk).
-
eapply (facts_det ms mo (NRead fd buf count) _ (efferr EISDIR) mo []); [exact Hsvc| exact Hh| exact Hminv| |].
+ intros o. rewrite Hdisp. apply (read_dir_outcome _ _ _ _ _ _ Hlk). apply (read_access_okb ms); assumption.
+ intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr. rewrite ecore_eff0. tauto.
- exfalso. exact (MS _ _ Hlk).
- exfalso. exact (MP _ _ _ Hlk).
- exfalso. exact (MN _ _ _ Hlk).
- exfalso. exact (MU _ Hlk).
-
eapply (facts_det ms mo (NRead fd buf count) _ (efferr EBADF) mo []); [exact Hsvc| exact Hh| exact Hminv| |].
+ intros o. rewrite Hdisp. apply (read_ebadf_outcome _ _ _ _ _ _ Hlk).
+ intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr. rewrite ecore_eff0. tauto.
Qed.

#[using="Type"] Lemma minv_open_insert : forall mo ent,
minv mo ->
fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
minv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
intros mo ent M Hfree Hent. minv_intro M. unfold minv. autorewrite with model.
set (fd := alloc_fd (m_fds mo)) in *.
assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
{ intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
split; [exact M0|]. split; [exact M1|]. split; [exact M2|].
split. { intros k c. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MC].
intros H. inversion H; subst. destruct Hent. }
split. { intros k p off. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MF].
intros H. inversion H; subst. exact Hent. }
split. { intros k p off. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MW].
repeat split; intros H; inversion H; subst; exact Hent. }
split. { intros k s. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MS].
intros H. inversion H; subst. exact Hent. }
split. { intros k pid w. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MP].
intros H. inversion H; subst. exact Hent. }
split. { intros k rd wr. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MN].
intros H. inversion H; subst. exact Hent. }
split. { intros k. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MU].
intros H. inversion H; subst. exact Hent. }
split; [exact MT| exact ML].
Qed.

#[using="Type"] Lemma open_out_facts : forall ms mo x8 R ent (path : list byte),
ms_svc_pending ms = Some x8 -> m_halted mo = None -> minv mo ->
match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
(forall o, syscall_spec (sys_input segs ms x8) mo o <->
open_out R mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) o) ->
(forall eff mo' evs, nstep (NOpen path) mo eff mo' evs <-> (evs = [] /\ open_result mo ent eff mo')) ->
node_facts ms mo (NOpen path).
Proof.
intros ms mo x8 R ent path Hsvc Hh Hminv Hent Hchar Hn. exists x8. split; [exact Hsvc|].
split; [|split; [|split; [|split]]].
- intros eff mo' evs Hsp. apply Hchar in Hsp. apply Hn.
destruct Hsp as [(e & He & E) | (Hfree & E)]; apply Ok_inj in E as (-> & -> & ->); (split; [reflexivity|]).
+ left. exists e. rewrite ecore_with_copyins. repeat split; auto.
+ right. rewrite ecore_with_copyins. repeat split; auto.
- intros eff mo' evs HP. apply Hn in HP as [-> [(e & He & Hc & ->) | (Hfree & Hc & ->)]].
+ exists (with_copyins R (mkEffect (errno_ret e) [] [])). split; [rewrite ecore_with_copyins; symmetry; exact Hc|].
apply Hchar. left. exists e. auto.
+ exists (with_copyins R (mkEffect (alloc_fd (m_fds mo)) [] [])). split; [rewrite ecore_with_copyins; symmetry; exact Hc|].
apply Hchar. right. auto.
- intros Hsp. apply Hchar in Hsp. destruct Hsp as [(e & _ & E) | (_ & E)]; exact (Unmodeled_Ok _ _ _ E).
- intros eff mo' evs HP. apply Hn in HP as [_ [(e & He & Hc & ->) | (Hfree & Hc & ->)]]; [auto|].
split; [rewrite m_halted_with_fds; exact Hh| apply minv_open_insert; assumption].
- exists (efferr ENOMEM), mo, []. apply Hn. split; [reflexivity|]. left. exists ENOMEM.
split; [cbn; auto|]. split; reflexivity.
Qed.

#[using="Type"] Lemma open_facts : forall ms mo path,
at_node segs (NOpen path) ms -> minv mo -> m_halted mo = None -> nsafe (NOpen path) mo ->
node_facts ms mo (NOpen path).
Proof.
intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hrom & Hp) Hminv Hh [Hsl Hdd].
set (i := sys_input segs ms (Z_to_bv 64 56)).
pose proof (bytes_at_bound _ _ _ _ Hp) as Hb. rewrite length_app in Hb. cbn [length] in Hb.
assert (Hflm : modeled_open_flags (in_arg i 2) = true).
{ apply modeled_open_flags_rd. unfold i. rewrite in_a2_si. exact Hfl. }
assert (Hdir : fd32 (in_arg i 0) = AT_FDCWD32).
{ unfold i. rewrite in_a0_si, Ha0. reflexivity. }
assert (Hrd : Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags = 0).
{ unfold i. rewrite in_a2_si. exact Hfl. }
assert (Hdisp : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 56)) mo o <->
openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i mo o).
{ intros o. unfold i. rewrite syscall_spec_56 by (apply sysno_si; lia). reflexivity. }
assert (Hin : bytes_in (in_mem i) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])).
{ unfold i. rewrite in_mem_si. eapply bytes_at_in; eassumption. }
assert (Ha1 : in_arg i 1 = wa (bv_unsigned (areg ms 11))).
{ unfold i. rewrite in_a1_si. symmetry. apply wa_unsigned_id. }
destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
-
assert (Hc : read_cstr (in_mem i) (in_arg i 1) = CstrTooLong).
{ rewrite Ha1. unfold read_cstr. apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong| exact Hnz|].
apply bytes_in_app in Hin as [Hin _]. exact Hin. }
eapply (facts_det ms mo (NOpen path) _ (with_copyins (open_reads i (in_arg i 1)) (efferr ENAMETOOLONG)) mo []);
[exact Hsvc| exact Hh| exact Hminv| |].
+ intros o. rewrite Hdisp. apply (openat_toolong_outcome _ _ _ _ _ Hflm _ Hc).
+ intros eff mo' evs. cbn [nstep]. replace (path_max <=? length path)%nat with true by (symmetry; apply Nat.leb_le; lia).
rewrite ecore_with_copyins. unfold efferr. rewrite ecore_eff0. tauto.
- assert (Hc : read_cstr (in_mem i) (in_arg i 1) = CstrOk path).
{ rewrite Ha1. unfold read_cstr. apply read_cstr_aux_bytes_in; [lia| exact Hnz| exact Hin]. }
assert (Hleb : (path_max <=? length path)%nat = false) by (apply Nat.leb_gt; lia).
destruct path as [|c path'].
+
eapply (facts_det ms mo (NOpen []) _ (with_copyins (open_reads i (in_arg i 1)) (efferr ENOENT)) mo []);
[exact Hsvc| exact Hh| exact Hminv| |].
* intros o. rewrite Hdisp. apply (openat_empty_outcome _ _ _ _ _ Hflm _ Hc).
* intros eff mo' evs. cbn [nstep]. rewrite Hleb. rewrite ecore_with_copyins. unfold efferr. rewrite ecore_eff0. tauto.
+ destruct (path_eqb (c :: path') dot_path) eqn:Hdot.
*
apply path_eqb_eq in Hdot.
eapply (open_out_facts ms mo _ (open_reads i (in_arg i 1)) FdDir); [exact Hsvc| exact Hh| exact Hminv| exact I| |].
-- intros o. rewrite Hdisp. apply (openat_dot_outcome _ _ _ _ _ Hflm Hdir Hrd). rewrite <- Hdot. exact Hc.
-- intros eff mo' evs. cbn [nstep]. rewrite Hleb. rewrite (proj2 (path_eqb_eq _ _) Hdot). tauto.
* assert (Hnd : path_is_dirref (c :: path') = false).
{ unfold path_is_dirref. rewrite Hdot, Hdd. reflexivity. }
destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Hfs.
--
eapply (open_out_facts ms mo _ (open_reads i (in_arg i 1)) (FdFile (c :: path') (Z_to_bv 64 0)));
[exact Hsvc| exact Hh| exact Hminv| cbn; congruence| |].
++ intros o. rewrite Hdisp. apply (openat_file_outcome _ _ _ _ _ Hflm Hdir Hrd _ d); try assumption. discriminate.
++ intros eff mo' evs. cbn [nstep]. rewrite Hleb, Hdot, Hfs. tauto.
--
eapply (facts_det ms mo (NOpen (c :: path')) _ (with_copyins (open_reads i (in_arg i 1)) (efferr ENOENT)) mo []);
[exact Hsvc| exact Hh| exact Hminv| |].
++ intros o. rewrite Hdisp. apply (openat_absent_outcome _ _ _ _ _ Hflm Hdir Hrd (c :: path')); try assumption. discriminate.
++ intros eff mo' evs. cbn [nstep]. rewrite Hleb, Hdot, Hfs. rewrite ecore_with_copyins. unfold efferr. rewrite ecore_eff0. tauto.
Qed.

#[using="Type"] Lemma std_chan : forall mo fd, minv mo -> (fd = 1 \/ fd = 2) ->
fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) /\
w_is0 (Z_to_bv 64 fd) = false.
Proof.
intros mo fd M [-> | ->]; minv_intro M; split; first [exact M1 | exact M2 | reflexivity].
Qed.

#[using="Type"] Lemma short_write_facts : forall ms mo x8 n fd bs (cps : nat -> list (word * nat)),
ms_svc_pending ms = Some x8 -> m_halted mo = None -> minv mo -> (1 <= length bs)%nat ->
(forall o, syscall_spec (sys_input segs ms x8) mo o <->
exists k, (1 <= k <= length bs)%nat /\
o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (cps k)) mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))) ->
(forall eff mo' evs, nstep n mo eff mo' evs <-> (mo' = mo /\ short_write fd bs eff evs)) ->
node_facts ms mo n.
Proof.
intros ms mo x8 n fd bs cps Hsvc Hh Hminv Hlen Hchar Hn. exists x8. split; [exact Hsvc|].
split; [|split; [|split; [|split]]].
- intros eff mo' evs Hsp. apply Hchar in Hsp as (k & Hk & E). apply Ok_inj in E as (-> & -> & ->).
apply Hn. split; [reflexivity|]. exists k. split; [exact Hk|]. split; reflexivity.
- intros eff mo' evs HP. apply Hn in HP as (-> & k & Hk & Hc & ->).
exists (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (cps k)). split; [rewrite ecore_mk; symmetry; exact Hc|].
apply Hchar. exists k. split; [exact Hk| reflexivity].
- intros Hsp. apply Hchar in Hsp as (k & _ & E). exact (Unmodeled_Ok _ _ _ E).
- intros eff mo' evs HP. apply Hn in HP as (-> & _). split; assumption.
- exists (eff0 (Z_to_bv 64 (Z.of_nat (length bs)))), mo, (map (WriteEv (Z_to_bv 64 fd)) bs). apply Hn.
split; [reflexivity|]. exists (length bs). split; [lia|]. split; [reflexivity|]. rewrite firstn_all. reflexivity.
Qed.

#[using="Type"] Lemma write_facts : forall ms mo fd bs,
at_node segs (NWrite fd bs) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NWrite fd bs).
Proof.
intros ms mo fd bs (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Hrom & Hbs) Hminv Hh.
pose proof Hlen as Hlen'. unfold rw_bytes_max in Hlen'.
destruct (std_chan mo fd Hminv Hfd) as [Hlk Hw].
assert (Hfd' : 0 <= fd < 3) by lia.
eapply (short_write_facts ms mo _ (NWrite fd bs) fd bs (fun k => [(areg ms 11, k)]));
[exact Hsvc| exact Hh| exact Hminv| lia| |].
- intros o. rewrite syscall_spec_64 by (apply sysno_si; lia). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
rewrite fd32_small by lia.
apply (write_chan_outcome _ _ _ _ _ _ _ bs Hlk Hw).
+ rewrite in_mem_si, <- (wa_unsigned_id (areg ms 11)). apply read_bytes_map_bytes_in; [| lia].
eapply bytes_at_in; eassumption.
+ rewrite unsigned_lit by lia. reflexivity.
+ exact Hlen.
- intros eff mo' evs. cbn [nstep]. tauto.
Qed.

#[using="Type"] Lemma iovs_ok_of_at : forall ms iovs bufs,
ms_rom ms = seg_rom segs ->
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
Z.of_nat (length (concat bufs)) < 2^64 ->
Forall2 (iov_ok (ms_read_byte ms)) iovs bufs /\ iovs_access_okb iovs = true.
Proof.
intros ms iovs bufs Hrom H. induction H as [|iov bs iovs bufs (Hl & Hts & Hb) _ IH]; intros Hlen; [split; [constructor| reflexivity]|].
cbn [concat] in Hlen. rewrite length_app in Hlen.
destruct (IH ltac:(lia)) as [IH1 IH2].
split.
- constructor; [| exact IH1].
split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
- unfold iovs_access_okb in *. cbn [forallb]. rewrite IH2, andb_true_r.
apply access_okb_intro. rewrite Hl, unsigned_lit by lia. exact Hts.
Qed.

#[using="Type"] Lemma iovs_ok_small : forall mp iovs bufs,
Forall2 (iov_ok mp) iovs bufs -> Z.of_nat (length (concat bufs)) < 2^63 ->
Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs.
Proof.
intros mp iovs bufs H. induction H as [|iov bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros Htot; constructor.
- rewrite Hl, unsigned_lit by lia. cbn [concat] in Htot. rewrite length_app in Htot. lia.
- apply IH. cbn [concat] in Htot. rewrite length_app in Htot. lia.
Qed.

#[using="Type"] Lemma import_iovecs_bytes_in : forall iovs mp (a : word),
(1 <= length iovs <= 1024)%nat ->
bv_unsigned a + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
bytes_in mp (bv_unsigned a) (iovec_bytes iovs) ->
Forall (fun iov => bv_unsigned (snd iov) < 2^63) iovs ->
iovs_access_okb iovs = true ->
import_iovecs mp a (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
intros iovs mp a Hcnt Hts Hin Hsmall Hok. unfold import_iovecs.
pose proof (copy_iovecs_aux_bytes_in iovs mp (bv_unsigned a) Hin Hsmall) as Hcopy. rewrite wa_unsigned_id in Hcopy.
unfold TASK_SIZE in Hts.
destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
destruct r as [|[b2 n2] r2].
-
cbn [length] in *. change (Z.of_nat 1) with 1 in *.
rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
replace (access_okb a 16) with true by (symmetry; unfold access_okb, TASK_SIZE; rewrite !(proj2 (Z.leb_le _ _)) by lia; reflexivity).
cbn [copy_iovecs_aux] in Hcopy.
destruct (read_iovec_entry mp a); try discriminate Hcopy.
cbn in Hcopy. injection Hcopy as -> ->.
unfold iovs_access_okb in Hok. cbn [forallb fst snd] in Hok. rewrite andb_true_r in Hok.
apply access_okb_le in Hok. pose proof (bv_unsigned_in_range 64 n).
replace (access_okb b (Z.min (bv_unsigned n) MAX_RW_COUNT)) with true
by (symmetry; unfold access_okb, MAX_RW_COUNT, TASK_SIZE in *; rewrite !(proj2 (Z.leb_le _ _)) by lia; reflexivity).
reflexivity.
-
set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
assert (Hc2 : 2 <= cnt <= 1024) by (unfold cnt; cbn [length] in *; lia).
assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit by lia. lia. }
assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit by lia. lia. }
rewrite E1, E0. rewrite unsigned_lit by lia.
replace (IOV_MAX <? cnt) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
replace (access_okb a (16 * cnt)) with true
by (symmetry; unfold access_okb, TASK_SIZE; rewrite !(proj2 (Z.leb_le _ _)) by lia; reflexivity).
cbn [negb]. unfold word_to_nat. rewrite unsigned_lit by lia. unfold cnt. rewrite Nat2Z.id.
rewrite Hcopy, Hok. reflexivity.
Qed.

#[using="Type"] Lemma writev_facts : forall ms mo fd bufs,
at_node segs (NWritev fd bufs) ms -> minv mo -> m_halted mo = None -> node_facts ms mo (NWritev fd bufs).
Proof.
intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Harr & iovs & Hiov & Hbufs) Hminv Hh.
destruct (std_chan mo fd Hminv Hfd) as [Hlk Hw].
assert (Hfd' : 0 <= fd < 3) by lia.
destruct (iovs_ok_of_at _ _ _ Hrom Hbufs ltac:(unfold node_rw_max in Htot; lia)) as [Hok Hbok].
pose proof (Forall2_length Hbufs) as Hleq.
set (i := sys_input segs ms (Z_to_bv 64 66)).
assert (Hdisp : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 66)) mo o <->
writev_spec (Z_to_bv 64 fd) (in_arg i 1) (Z_to_bv 64 (Z.of_nat (length bufs))) i mo o).
{ intros o. unfold i. rewrite syscall_spec_66 by (apply sysno_si; lia). rewrite in_a0_si, in_a2_si, Ha0, Ha2.
rewrite fd32_small by lia. reflexivity. }
assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
{ unfold iovcnt32, abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
destruct bufs as [|b0 bufs'] eqn:Ebufs.
{
eapply (facts_det ms mo (NWritev fd []) _ (eff0 (Z_to_bv 64 0)) mo []); [exact Hsvc| exact Hh| exact Hminv| |].
- intros o. rewrite Hdisp. apply (writev_chan_cnt0_outcome _ _ _ _ _ _ _ Hlk Hw).
rewrite Hcnt32. reflexivity.
- intros eff mo' evs. cbn [nstep concat length Nat.eqb]. rewrite ecore_eff0. tauto. }
assert (Hne : (1 <= length bufs)%nat) by (rewrite Ebufs; cbn; lia).
rewrite <- Ebufs in *. clear Ebufs b0 bufs'.
assert (Himp : import_iovecs (in_mem i) (in_arg i 1) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
{ rewrite Hcnt32. unfold i. rewrite in_a1_si, in_mem_si, <- Hleq.
apply import_iovecs_bytes_in; [lia| rewrite Hleq; exact Harr| eapply bytes_at_in; eassumption| | exact Hbok].
eapply iovs_ok_small; [exact Hok| unfold node_rw_max in Htot; lia]. }
assert (Hg : gather_iovecs (in_mem i) iovs = Some (concat bufs)).
{ unfold i. rewrite in_mem_si. apply gather_iovecs_ok. exact Hok. }
pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
destruct (Nat.eqb_spec (length (concat bufs)) 0) as [Hz|Hnz].
-
eapply (facts_det ms mo (NWritev fd bufs) _
(with_copyins (import_iovecs_accesses (in_mem i) (in_arg i 1) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))
(eff0 (Z_to_bv 64 0))) mo []);
[exact Hsvc| exact Hh| exact Hminv| |].
+ intros o. rewrite Hdisp. apply (writev_chan_zero_outcome _ _ _ _ _ _ _ iovs Hlk Hw Himp). rewrite Htotal. lia.
+ intros eff mo' evs. cbn [nstep]. rewrite (proj2 (Nat.eqb_eq _ _) Hz). rewrite ecore_with_copyins, ecore_eff0. tauto.
-
eapply (short_write_facts ms mo _ (NWritev fd bufs) fd (concat bufs)
(fun k => import_iovecs_accesses (in_mem i) (in_arg i 1) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
++ iov_prefix_accesses iovs k));
[exact Hsvc| exact Hh| exact Hminv| lia| |].
+ intros o. rewrite Hdisp.
apply (writev_chan_outcome _ _ _ _ _ _ _ iovs (concat bufs) Hlk Hw Himp).
* rewrite Htotal. exact Htot.
* exact Hg.
* lia.
+ intros eff mo' evs. cbn [nstep]. rewrite (proj2 (Nat.eqb_neq _ _) Hnz). tauto.
Qed.

#[using="Type"] Lemma minv_vm_only : forall mo mo', vm_only mo mo' -> minv mo -> minv mo'.
Proof.
intros mo mo' (Hfd & Hio & Hfs & Hpr & _ & _ & Hl) M. unfold minv in *.
unfold m_fds, m_fs, m_tid in *. rewrite Hfd, Hfs, Hpr.
destruct M as (M0 & M1 & M2 & MC & MF & MW & MS & MP & MN & MU & MT & ML).
split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|].
split; [exact MW|]. split; [exact MS|]. split; [exact MP|]. split; [exact MN|]. split; [exact MU|]. split; [exact MT| exact (Hl ML)].
Qed.

#[using="Type"] Lemma halted_vm_only : forall mo mo', vm_only mo mo' -> m_halted mo' = m_halted mo.
Proof. intros mo mo' (_ & _ & _ & Hpr & _). unfold m_halted. rewrite Hpr. reflexivity. Qed.

#[using="Type"] Lemma mm_facts_c : forall ms mo n i x8,
node_input n = Some i ->
(forall eff mo' evs, nstep n mo eff mo' evs <->
(evs = [] /\ syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg kit_cfg i mo eff)) ->
ms_svc_pending ms = Some x8 -> minv mo -> m_halted mo = None ->
(forall o, syscall_spec (sys_input segs ms x8) mo o <-> syscall_spec i mo o) ->
in_sysno (sys_input segs ms x8) = in_sysno i ->
in_arg (sys_input segs ms x8) 0 = in_arg i 0 ->
(~ syscall_spec i mo Unmodeled) ->
(forall eff mo' evs, syscall_spec i mo (Ok eff mo' evs) -> evs = [] /\ vm_only mo mo') ->
((exists eff mo' evs, syscall_spec i mo (Ok eff mo' evs)) \/ syscall_spec i mo Unmodeled) ->
node_facts_c ms mo n.
Proof.
intros ms mo n i x8 Hi Hn Hsvc Hminv Hh Hind Hno Ha0 Hnu Hsp Htot.
assert (Hsx : forall eff, spurious_refusal_cfg kit_cfg (sys_input segs ms x8) mo eff <-> spurious_refusal_cfg kit_cfg i mo eff).
{ intros eff. apply spurious_ext; assumption. }
exists x8. split; [exact Hsvc|]. split; [|split; [|split; [|split; [|split]]]].
- intros eff mo' evs Hs. apply Hind in Hs. destruct (Hsp _ _ _ Hs) as [_ Hv].
  split; [rewrite (halted_vm_only _ _ Hv); exact Hh| exact (minv_nolazy _ (minv_vm_only _ _ Hv Hminv))].
- intros eff mo' evs Hs Hns. apply Hind in Hs. apply Hn. split; [exact (proj1 (Hsp _ _ _ Hs))|].
  split; [exact Hs|]. intros Hsp'. apply Hns. apply Hsx. exact Hsp'.
- intros eff mo' evs HP. apply Hn in HP as (_ & HP & Hns). exists eff. split; [reflexivity|].
  split; [apply Hind; exact HP|]. intros Hsp'. apply Hns. apply Hsx. exact Hsp'.
- intros Hs. apply Hind in Hs. exact (Hnu Hs).
- intros eff mo' evs HP. apply Hn in HP as (_ & HP & _). destruct (Hsp _ _ _ HP) as [_ Hv].
  split; [rewrite (halted_vm_only _ _ Hv); exact Hh| exact (minv_vm_only _ _ Hv Hminv)].
- destruct Htot as [Hex|Hs]; [| exfalso; exact (Hnu Hs)].
  destruct (exists_not_spurious kit_cfg i mo Hex) as (eff & mo' & evs & Hs & Hns).
  exists eff, mo', evs. apply Hn. split; [exact (proj1 (Hsp _ _ _ Hs))|]. split; [exact Hs| exact Hns].
Qed.

#[using="Type"] Lemma brk_facts_c : forall ms mo req,
at_node segs (NBrk req) ms -> minv mo -> m_halted mo = None -> nsafe (NBrk req) mo -> node_facts_c ms mo (NBrk req).
Proof.
intros ms mo req (Hsvc & Ha0) Hminv Hh Hsafe.
eapply (mm_facts_c ms mo (NBrk req)); [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh
| | rewrite in_sysno_si; reflexivity | rewrite in_a0_si, Ha0; reflexivity | exact Hsafe | |].
- intros o. rewrite syscall_spec_214 by (apply sysno_si; lia). rewrite (syscall_spec_214 (pure_input _ _)) by reflexivity.
  rewrite in_a0_si, Ha0. cbn [in_arg in_args pure_input nth]. split; apply brk_iind.
- intros eff mo' evs Hs. apply (syscall_spec_214 (pure_input _ _)) in Hs; [| reflexivity]. exact (brk_sp _ _ _ _ _ _ Hs).
- pose proof (brk_tot (in_arg (pure_input 214 [Z_to_bv 64 req]) 0) mo (pure_input 214 [Z_to_bv 64 req])) as T.
  destruct T as [(x & m' & e & T)|T]; [left; exists x, m', e| right]; apply (syscall_spec_214 (pure_input _ _)); try reflexivity; exact T.
Qed.

#[using="Type"] Lemma mmap_facts_c : forall ms mo addr len prot flags,
at_node segs (NMmap addr len prot flags) ms -> minv mo -> m_halted mo = None -> nsafe (NMmap addr len prot flags) mo ->
node_facts_c ms mo (NMmap addr len prot flags).
Proof.
intros ms mo addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) Hminv Hh [Hnr Hsafe].
set (ip := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) in *.
assert (Hip : forall o, syscall_spec ip mo o <->
mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) ip mo o).
{ intros o. unfold ip. rewrite syscall_spec_222 by reflexivity. reflexivity. }
eapply (mm_facts_c ms mo (NMmap addr len prot flags) ip); [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh
| | rewrite in_sysno_si; reflexivity | rewrite in_a0_si, Ha0; reflexivity | exact Hsafe | |].
- intros o. rewrite syscall_spec_222 by (apply sysno_si; lia). rewrite Hip.
  rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. split; apply mmap_iind.
- intros eff mo' evs Hs. apply Hip in Hs. exact (mmap_sp _ _ _ _ _ _ _ Hnr _ _ _ _ Hs).
- destruct (mmap_tot (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) mo ip)
  as [(x & m' & e & T)|T]; [left; exists x, m', e| right]; apply Hip; exact T.
Qed.

#[using="Type"] Lemma munmap_facts_c : forall ms mo addr len,
at_node segs (NMunmap addr len) ms -> minv mo -> m_halted mo = None -> nsafe (NMunmap addr len) mo ->
node_facts_c ms mo (NMunmap addr len).
Proof.
intros ms mo addr len (Hsvc & Ha0 & Ha1) Hminv Hh Hsafe.
set (ip := pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) in *.
assert (Hip : forall o, syscall_spec ip mo o <-> munmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) ip mo o).
{ intros o. unfold ip. rewrite syscall_spec_215 by reflexivity. reflexivity. }
eapply (mm_facts_c ms mo (NMunmap addr len) ip); [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh
| | rewrite in_sysno_si; reflexivity | rewrite in_a0_si, Ha0; reflexivity | exact Hsafe | |].
- intros o. rewrite syscall_spec_215 by (apply sysno_si; lia). rewrite Hip.
  rewrite in_a0_si, in_a1_si, Ha0, Ha1. split; apply munmap_iind.
- intros eff mo' evs Hs. apply Hip in Hs. exact (munmap_sp _ _ _ _ _ _ _ Hs).
- destruct (munmap_tot (Z_to_bv 64 addr) (Z_to_bv 64 len) mo ip)
  as [(x & m' & e & T)|T]; [left; exists x, m', e| right]; apply Hip; exact T.
Qed.

#[using="Type"] Lemma mprotect_facts_c : forall ms mo addr len prot,
at_node segs (NMprotect addr len prot) ms -> minv mo -> m_halted mo = None -> nsafe (NMprotect addr len prot) mo ->
node_facts_c ms mo (NMprotect addr len prot).
Proof.
intros ms mo addr len prot (Hsvc & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe.
set (ip := pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) in *.
assert (Hip : forall o, syscall_spec ip mo o <-> mprotect_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) ip mo o).
{ intros o. unfold ip. rewrite syscall_spec_226 by reflexivity. reflexivity. }
eapply (mm_facts_c ms mo (NMprotect addr len prot) ip); [reflexivity | intros; cbn [nstep node_input]; tauto | exact Hsvc | exact Hminv | exact Hh
| | rewrite in_sysno_si; reflexivity | rewrite in_a0_si, Ha0; reflexivity | exact Hsafe | |].
- intros o. rewrite syscall_spec_226 by (apply sysno_si; lia). rewrite Hip.
  rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2. split; apply mprotect_iind.
- intros eff mo' evs Hs. apply Hip in Hs. exact (mprotect_sp _ _ _ _ _ _ _ _ Hs).
- destruct (mprotect_tot (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) mo ip)
  as [(x & m' & e & T)|T]; [left; exists x, m', e| right]; apply Hip; exact T.
Qed.

#[using="Type"] Lemma nstep_brk_iff : forall req mo eff mo' evs,
nstep (NBrk req) mo eff mo' evs <->
(evs = [] /\ exists r, brk_r_ok mo (Z_to_bv 64 req) r = true /\
(brk_refusal_b mo (Z_to_bv 64 req) r = false
\/ forall r', brk_r_ok mo (Z_to_bv 64 req) r' = true -> brk_refusal_b mo (Z_to_bv 64 req) r' = true) /\
eff = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [] /\
mo' = with_brk_next mo (Z_to_bv 64 req) r).
Proof.
intros. cbn [nstep node_input].
assert (Hs : forall o, syscall_spec (pure_input 214 [Z_to_bv 64 req]) mo o <->
brk_spec (Z_to_bv 64 req) (pure_input 214 [Z_to_bv 64 req]) mo o).
{ intros o. rewrite (syscall_spec_214 (pure_input _ _)) by reflexivity. cbn [in_arg in_args pure_input nth]. reflexivity. }
rewrite (not_spurious_iff (pure_input 214 [Z_to_bv 64 req]) mo eff (fun e => brk_refusal_b mo (Z_to_bv 64 req) (eff_ret e))
(brk_spec (Z_to_bv 64 req))); [| reflexivity | intros e; rewrite refusal_b_brk by reflexivity; reflexivity | exact Hs].
rewrite Hs, brk_outcome. split.
- intros [-> [(r & Hr & E) Hf]]. apply Ok_inj in E as (-> & -> & _). split; [reflexivity|]. exists r.
  split; [exact Hr|]. split; [|split; reflexivity]. cbn [eff_ret] in Hf.
  destruct (brk_refusal_b mo (Z_to_bv 64 req) r) eqn:Er; [right| left; reflexivity].
  intros r' Hr'.
  refine (Hf eq_refl (mkEffectU r' [] (brk_zeros (Z_to_bv 64 req) r' (vm_brk (m_vmmaps mo))) (brk_unmaps r' (vm_brk (m_vmmaps mo))) [] [])
  (with_brk_next mo (Z_to_bv 64 req) r') [] _).
  apply brk_outcome. exists r'. split; [exact Hr'| reflexivity].
- intros [-> (r & Hr & Hf & -> & ->)]. split; [reflexivity|]. split; [exists r; split; [exact Hr| reflexivity]|].
  cbn [eff_ret]. intros Href eff' m' evs' Hs'. apply brk_outcome in Hs'. destruct Hs' as (r' & Hr' & E').
  apply Ok_inj in E' as (-> & _ & _). cbn [eff_ret].
  destruct Hf as [Hf | Hf]; [rewrite Hf in Href; discriminate Href| exact (Hf r' Hr')].
Qed.

#[using="Type"] Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
nstep (NMunmap addr len) mo eff mo' evs <-> (evs = [] /\ munmap_out (Z_to_bv 64 addr) (Z_to_bv 64 len) mo (Ok eff mo' evs)).
Proof.
intros. cbn [nstep node_input].
assert (Hns : ~ spurious_refusal_cfg kit_cfg (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo eff)
by (apply spurious_refusal_family_on; reflexivity).
rewrite (syscall_spec_215 (pure_input _ _)) by reflexivity.
cbn [in_arg in_args pure_input nth]. rewrite munmap_outcome. tauto.
Qed.

#[using="Type"] Lemma nstep_mmap_spec : forall addr len prot flags mo eff mo' evs,
nstep (NMmap addr len prot flags) mo eff mo' evs <->
(evs = [] /\ cfg_ok mmap_r (mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0))
(pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
mo (Ok eff mo' evs)).
Proof.
intros. cbn [nstep node_input].
set (ip := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]).
set (sp := mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)).
assert (Hs : forall o, syscall_spec ip mo o <-> sp ip mo o).
{ intros o. unfold ip, sp. rewrite syscall_spec_222 by reflexivity. reflexivity. }
rewrite (not_spurious_iff ip mo eff mmap_r sp); [| reflexivity | intros e; unfold mmap_r; apply refusal_b_mmap; reflexivity | exact Hs].
unfold cfg_ok. rewrite Hs. split.
- intros [-> [H1 H2]]. split; [reflexivity|]. split; [exact H1|]. intros eff0 m0 evs0 E. injection E as <- _ _. exact H2.
- intros [-> [H1 H2]]. split; [reflexivity|]. split; [exact H1| exact (H2 _ _ _ eq_refl)].
Qed.

#[using="Type"] Lemma nstep_mprotect_spec : forall addr len prot mo eff mo' evs,
nstep (NMprotect addr len prot) mo eff mo' evs <->
(evs = [] /\ cfg_ok mprot_r (mprotect_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot))
(pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo (Ok eff mo' evs)).
Proof.
intros. cbn [nstep node_input].
set (ip := pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]).
set (sp := mprotect_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot)).
assert (Hs : forall o, syscall_spec ip mo o <-> sp ip mo o).
{ intros o. unfold ip, sp. rewrite syscall_spec_226 by reflexivity. reflexivity. }
rewrite (not_spurious_iff ip mo eff mprot_r sp); [| reflexivity | intros e; unfold mprot_r; apply refusal_b_mprotect; reflexivity | exact Hs].
unfold cfg_ok. rewrite Hs. split.
- intros [-> [H1 H2]]. split; [reflexivity|]. split; [exact H1|]. intros eff0 m0 evs0 E. injection E as <- _ _. exact H2.
- intros [-> [H1 H2]]. split; [reflexivity|]. split; [exact H1| exact (H2 _ _ _ eq_refl)].
Qed.

#[using="Type"] Lemma nsafe_munmap_iff : forall addr len mo,
nsafe (NMunmap addr len) mo <-> ~ munmap_out (Z_to_bv 64 addr) (Z_to_bv 64 len) mo Unmodeled.
Proof.
intros. cbn [nsafe node_input]. rewrite (syscall_spec_215 (pure_input _ _)) by reflexivity.
cbn [in_arg in_args pure_input nth]. rewrite munmap_outcome. tauto.
Qed.

#[using="Type"] Lemma nsafe_brk : forall req mo, nsafe (NBrk req) mo.
Proof.
intros req mo. cbn [nsafe node_input]. rewrite (syscall_spec_214 (pure_input _ _)) by reflexivity.
rewrite brk_outcome. intros (r & _ & E). exact (Unmodeled_Ok _ _ _ E).
Qed.

#[using="Type"] Lemma nsafe_mmap_rw : forall addr len mo, (0 < len < 2^64) ->
nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
intros addr len mo Hlen. cbn [nsafe node_input]. split; [reflexivity|].
rewrite (syscall_spec_222 (pure_input _ _)) by reflexivity. cbn [in_arg in_args pure_input nth].
rewrite mmap_rw_outcome_u; [| rewrite w_is0_lit by lia; apply Z.eqb_neq; lia | reflexivity].
intros [(e & _ & E) | (a & _ & E)]; exact (Unmodeled_Ok _ _ _ E).
Qed.

#[using="Type"] Lemma nsafe_mmap_none : forall addr len mo, (0 < len < 2^64) ->
nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
intros addr len mo Hlen. cbn [nsafe node_input]. split; [reflexivity|].
rewrite (syscall_spec_222 (pure_input _ _)) by reflexivity. cbn [in_arg in_args pure_input nth].
rewrite mmap_noaccess_outcome_u; [| rewrite w_is0_lit by lia; apply Z.eqb_neq; lia | reflexivity | reflexivity].
intros [(e & _ & E) | (a & _ & E)]; exact (Unmodeled_Ok _ _ _ E).
Qed.

#[using="Type"] Lemma nsafe_mmap_fixed_none : forall addr len mo,
let h := m_vmmaps mo in
let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
(0 < len < 2^64) -> (0 < addr) -> (addr mod page_size = 0) -> (addr + nZ <= alloc_top h) ->
region_free (vm_reserved h) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
map_contains (vm_maps h) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) mo.
Proof.
intros addr len mo h nZ Hlen Hpos Hal Hce Hrf Hmc. cbn [nsafe node_input]. split; [reflexivity|].
rewrite (syscall_spec_222 (pure_input _ _)) by reflexivity. cbn [in_arg in_args pure_input nth].
assert (Ha : bv_unsigned (Z_to_bv 64 addr) = addr).
{ apply unsigned_lit. pose proof (alloc_top_room h). unfold stack_max_size, two_pow_64 in *.
pose proof (page_round_up_Z_nonneg (bv_unsigned (Z_to_bv 64 len))).
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 len)). lia. }
intros E.
destruct (mmap_fixed_noaccess_outcome_u (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_NONE)
(Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
(pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 PROT_NONE; Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED);
Z_to_bv 64 (-1); Z_to_bv 64 0]) mo Unmodeled
ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia) eq_refl eq_refl eq_refl
ltac:(rewrite Ha; exact Hce) ltac:(rewrite Ha; exact Hal) ltac:(rewrite Ha; exact Hpos) Hrf Hmc) as [_ Hc].
destruct (Hc E) as [E' | (e & ws & zs & us & cs & cps & m' & evs & _ & E')]; discriminate E'.
Qed.

#[using="Type"] Lemma nsafe_mprotect_iff : forall addr len prot mo,
nsafe (NMprotect addr len prot) mo <-> ~ mprotect_out (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) mo Unmodeled.
Proof.
intros. cbn [nsafe node_input]. rewrite (syscall_spec_226 (pure_input _ _)) by reflexivity.
cbn [in_arg in_args pure_input nth]. rewrite <- (cfg_ok_unmodeled mprot_r), mprotect_outcome. tauto.
Qed.

#[using="Type"] Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
match n with NBrk _ | NMunmap _ _ | NMprotect _ _ _ => True
| NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => False end ->
nstep n mo eff mo' evs -> vm_only mo mo' /\ evs = [].
Proof.
intros n mo eff mo' evs Hn H. destruct n; try contradiction; cbn [nstep node_input] in H; destruct H as [-> [H _]].
- apply (syscall_spec_214 (pure_input _ _)) in H; [| reflexivity]. apply brk_sp in H. tauto.
- apply (syscall_spec_222 (pure_input _ _)) in H; [| reflexivity]. apply (mmap_sp _ _ _ _ (Z_to_bv 64 (-1)) _ _ Hn) in H. tauto.
- apply (syscall_spec_215 (pure_input _ _)) in H; [| reflexivity]. apply munmap_sp in H. tauto.
- apply (syscall_spec_226 (pure_input _ _)) in H; [| reflexivity]. apply mprotect_sp in H. tauto.
Qed.

#[using="Type"] Lemma alloc_fd_aux_le : forall fuel fds cand,
(bv_unsigned cand + Z.of_nat fuel < two_pow_64)%Z ->
(bv_unsigned (alloc_fd_aux fds cand fuel) <= bv_unsigned cand + Z.of_nat fuel)%Z.
Proof.
induction fuel as [|f IH]; intros fds cand Hb; cbn [alloc_fd_aux].
- lia.
- destruct (fd_lookup fds cand).
+ assert (Hu : bv_unsigned (cand + 1) = (bv_unsigned cand + 1)%Z).
{ rewrite bv_add_unsigned.
replace (bv_unsigned (1 : word)) with 1%Z by reflexivity.
apply bv_wrap_small.
unfold bv_modulus. change (Z.of_N 64) with 64%Z.
pose proof (word_unsigned_range cand). unfold two_pow_64 in *. lia. }
specialize (IH fds (cand + 1)%bv). rewrite Hu in IH. lia.
+ pose proof (word_unsigned_range cand). lia.
Qed.

#[using="Type"] Lemma alloc_fd_le : forall fds, (bv_unsigned (alloc_fd fds) <= 4096)%Z.
Proof.
intro fds. unfold alloc_fd.
pose proof (alloc_fd_aux_le 4096 fds (Z_to_bv 64 0)) as H.
rewrite Z_to_bv_small in H
by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
unfold two_pow_64 in H. lia.
Qed.

#[using="Type"] Lemma alloc_fd_range : forall mo,
minv mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096.
Proof.
intros mo M Hfree. minv_intro M. pose proof (alloc_fd_le (m_fds mo)) as Hle.
set (fd := alloc_fd (m_fds mo)) in *.
assert (H : forall z e, fd_lookup (m_fds mo) (Z_to_bv 64 z) = Some e -> 0 <= z < 2^64 -> bv_unsigned fd <> z).
{ intros z e Hz Hr E. rewrite <- (Z_to_bv_bv_unsigned fd), E in Hfree. congruence. }
pose proof (H 0 _ M0 ltac:(lia)). pose proof (H 1 _ M1 ltac:(lia)). pose proof (H 2 _ M2 ltac:(lia)).
pose proof (bv_unsigned_in_range 64 fd). lia.
Qed.

#[using="Type"] Lemma minv_preserved : forall n mo eff mo' evs,
match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end ->
minv mo -> m_halted mo = None -> nstep n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof.
intros n mo eff mo' evs Hfl Hminv Hh H.
assert (Hor : forall ent, open_result mo ent eff mo' ->
match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
m_halted mo' = None /\ minv mo').
{ intros ent [(e & _ & _ & ->) | (Hlk & _ & ->)] Hent; [auto|].
split; [rewrite m_halted_with_fds; exact Hh|]. apply minv_open_insert; assumption. }
assert (Hmm : forall n', match n' with NBrk _ | NMunmap _ _ | NMprotect _ _ _ => True
| NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => False end ->
nstep n' mo eff mo' evs -> m_halted mo' = None /\ minv mo').
{ intros n' Hn' H'. destruct (nstep_mm_vm_only n' mo eff mo' evs Hn' H') as [Hv _].
split; [rewrite (halted_vm_only _ _ Hv); exact Hh | eapply minv_vm_only; eassumption]. }
destruct n; cbn [nstep] in H.
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
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|nrd nwr| ]|] eqn:Hlk; try contradiction.
+ destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct H as [_ ->].
split; [rewrite m_halted_with_fds; exact Hh|]. eapply minv_update_file; eassumption.
+ destruct H as [_ ->]. auto.
+ destruct H as [_ ->]. auto.
- destruct H as (_ & Hfd & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [|auto].
split; [rewrite m_halted_with_fds; exact Hh|]. apply minv_remove; assumption.
- destruct H as (_ & _ & ->); auto.
- destruct H as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; auto.
split; [rewrite m_halted_with_tid; exact Hh|]. apply minv_with_tid; assumption.
- destruct H.
- apply (Hmm (NBrk req)); [exact I| exact H].
- apply (Hmm (NMmap addr len prot flags)); [exact Hfl| exact H].
- apply (Hmm (NMunmap addr len)); [exact I| exact H].
- apply (Hmm (NMprotect addr len prot)); [exact I| exact H].
Qed.

#[using="Type"] Lemma all_facts : forall n ms mo,
match n with NExit _ => False | _ => True end ->
at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo -> node_facts_c ms mo n.
Proof.
intros n ms mo Hne Hat Hminv Hh Hsafe. destruct n; try contradiction.
- apply facts_c_of_facts; [apply write_facts; assumption| apply (pending_on_at ms 64 (proj1 Hat)); [lia| reflexivity]].
- apply facts_c_of_facts; [apply writev_facts; assumption| apply (pending_on_at ms 66 (proj1 Hat)); [lia| reflexivity]].
- apply facts_c_of_facts; [apply open_facts; assumption| apply (pending_on_at ms 56 (proj1 Hat)); [lia| reflexivity]].
- apply facts_c_of_facts; [apply read_facts; assumption| apply (pending_on_at ms 63 (proj1 Hat)); [lia| reflexivity]].
- apply facts_c_of_facts; [apply close_facts; assumption| apply (pending_on_at ms 57 (proj1 Hat)); [lia| reflexivity]].
- apply facts_c_of_facts; [apply ioctl_facts; assumption| apply (pending_on_at ms 29 (proj1 Hat)); [lia| reflexivity]].
- apply facts_c_of_facts; [apply set_tid_facts; assumption| apply (pending_on_at ms 96 Hat); [lia| reflexivity]].
- apply brk_facts_c; assumption.
- apply mmap_facts_c; assumption.
- apply munmap_facts_c; assumption.
- apply mprotect_facts_c; assumption.
Qed.

End PerNode.

Lemma exit_node_facts : forall segs ms mo c,
at_node segs (NExit c) ms -> m_halted mo = None ->
(forall evs X, sstep_cfg segs kit_cfg (mkCfg ms mo) evs X ->
X = SNext (mkCfg ms (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
/\ sstep_cfg segs kit_cfg (mkCfg ms mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg ms (with_halted (exit_code c) mo))).
Proof.
intros segs ms mo c Hat Hh.
assert (Hx : exists x8, ms_svc_pending ms = Some x8).
{ destruct (proj1 Hat) as [H|H]; eexists; exact H. }
destruct Hx as [x8 Hsvc].
apply (exit_kit_c segs ms mo x8 (exit_code c) Hsvc Hh).
exact (exit_outcome_at segs ms mo c x8 Hat Hsvc).
Qed.

Lemma nonexit_node_facts : forall segs n ms mo,
match n with NExit _ => False | _ => True end ->
at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
(forall evs X, sstep_cfg segs kit_cfg (mkCfg ms mo) evs X ->
exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ nstep n mo eff mo' evs)
/\ (forall eff mo' evs, nstep n mo eff mo' evs ->
m_halted mo' = None /\ minv mo' /\ sstep_cfg segs kit_cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo')))
/\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
intros segs n ms mo Hne Hat Hminv Hh Hsafe.
destruct (all_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (x8 & Hsvc & Hall & Hc & Hs & Hnu & Hpres & Hprog).
destruct (node_kit_c segs ms mo x8 (nstep n mo) Hsvc Hh Hall Hc Hs Hnu Hprog) as (Kc & Ks & Kp).
split; [exact Kc|]. split; [|exact Kp].
intros eff mo' evs HP. destruct (Hpres _ _ _ HP) as [H1 H2]. auto.
Qed.

Theorem nodes_sound : forall segs, node_sound node segs (at_node segs) nstep nexit minv nsafe.
Proof.
intros segs. constructor.
-
intros n ms Hat.
assert (Hx : exists x8, ms_svc_pending ms = Some x8).
{ destruct n as [| | | | | | |c| | | |]; cbn [at_node] in Hat;
first [ destruct Hat as [[H|H] _]; eexists; exact H
| destruct Hat as [H _]; eexists; exact H
| eexists; exact Hat ]. }
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
destruct n as [| | | | | | |c| | | |]; try contradiction. cbn [nexit] in HX. destruct HX as [-> ->].
split; [apply m_halted_with_halted|]. exact (proj2 (exit_node_facts segs ms mo c Hat Hh)).
-
intros n ms mo Hat Hh Hminv Hsafe.
assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
{ destruct n; first [left; eexists; reflexivity | right; exact I]. }
destruct Hcase as [[c ->] | Hne].
+ right. eexists _, _. split; reflexivity.
+ destruct (nonexit_node_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (_ & _ & Hp). left. exact Hp.
-
exact minv_nolazy.
Qed.
