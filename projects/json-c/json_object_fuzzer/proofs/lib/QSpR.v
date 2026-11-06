(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require EdBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwNp Qpox QsV0 QsRG Qnhz Qrxj QSjk QRjH QBxa Qn1e Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QwNp Qpox QsV0 QsRG Qnhz.Mq0 QsRG.Mq0 Qrxj QSjk.Mq0 QRjH QBxa.Mq4 Qn1e QBxa.Mq0 Q9ox.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof.
intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

#[using="Type"] Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.

#[using="Type"] Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma access_okb_of_le : forall (b : word) (n : Z),
(0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof.
intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

#[using="Type"] Lemma t_alt_wall_nat : forall (ch : word) (bs : list byte) (K : TSet),
K [] -> (1 <= length bs)%nat ->
t_eq (t_alt (fun k : nat =>
fun tr => (1 <= k <= length bs)%nat /\
t_emit (map (WriteEv ch) (firstn k bs)) (t_emit (map (WriteEv ch) (skipn k bs)) K) tr))
(t_emit (map (WriteEv ch) bs) K).
Proof.
intros ch bs K HK Hnb tr. rewrite <- (t_alt_wall ch bs K HK Hnb tr). unfold t_alt. split.
- intros [k [Hk Ht]]. exists (exist _ k Hk). exact Ht.
- intros [[k Hk] Ht]. exists k. split; [exact Hk | exact Ht].
Qed.

#[using="Type"] Lemma rz_wall : forall segs c (ch : word) (bs : list byte) (K : TSet),
(1 <= length bs)%nat -> K [] ->
realizes segs c (t_alt (fun i : wr_index bs =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
(t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
realizes segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
intros segs c ch bs K Hnb HK H. eapply rz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma read_u64_rdn : forall ms a v,
ms_rom ms = seg_rom segs ->
rdn segs (ms_mem ms) a 8%nat = Some (word_to_le_bytes 8 v) ->
read_u64 (ms_read_byte ms) a = Some v.
Proof.
intros ms a v Hrom H. unfold read_u64.
rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

#[using="Type"] Lemma read_bytes_map_rdn : forall ms a (n : word) bs,
ms_rom ms = seg_rom segs ->
rdn segs (ms_mem ms) a (word_to_nat n) = Some bs ->
read_bytes_map (ms_read_byte ms) a n = Some bs.
Proof.
intros ms a n bs Hrom H.
rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.

Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
match iovs with
| [] => True
| (b, n) :: r =>
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
/\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
/\ (bv_unsigned n < 2 ^ 63)%Z
/\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
end.

#[using="Type"] Lemma read_iovec_entry_of_array : forall ms b n r iov,
ms_rom ms = seg_rom segs ->
iov_array (ms_mem ms) iov ((b, n) :: r) ->
read_iovec_entry (ms_read_byte ms) iov = IovEntry b n.
Proof.
intros ms b n r iov Hrom (Hb & Hn & Hlt & _). unfold read_iovec_entry.
rewrite (read_u64_rdn ms iov b Hrom Hb).
rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
rewrite (read_u64_rdn ms _ n Hrom Hn).
rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.

#[using="Type"] Lemma copy_iovecs_of_array : forall ms iovs iov,
ms_rom ms = seg_rom segs ->
iov_array (ms_mem ms) iov iovs ->
copy_iovecs_aux (ms_read_byte ms) iov (length iovs) = ImpOk iovs.
Proof.
intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
destruct Ha as (Hb & Hn & Hlt & Hr).
cbn [length copy_iovecs_aux]. unfold read_iovec_entry.
rewrite (read_u64_rdn ms iov b Hrom Hb).
rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
rewrite (read_u64_rdn ms _ n Hrom Hn).
rewrite (proj2 (Z.leb_gt _ _) Hlt).
rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
rewrite (IH _ Hrom Hr). reflexivity.
Qed.

Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
match iovs, bss with
| [], [] => True
| (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
| _, _ => False
end.

#[using="Type"] Lemma gather_of_bufs : forall ms iovs bss,
ms_rom ms = seg_rom segs ->
iov_bufs (ms_mem ms) iovs bss ->
gather_iovecs (ms_read_byte ms) iovs = Some (concat bss).
Proof.
intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
- reflexivity.
- destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.

#[using="Type"] Lemma cap_iovecs_id : forall iovs left,
(iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
rewrite Z.min_r by lia. rewrite u64_roundtrip', IH by lia. reflexivity.
Qed.

Fixpoint iov_bufs_ok (iovs : list (word * word)) : Prop :=
match iovs with
| [] => True
| (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_bufs_ok r
end.

#[using="Type"] Lemma iovs_access_okb_of_ok : forall iovs, iov_bufs_ok iovs -> iovs_access_okb iovs = true.
Proof.
induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.

#[using="Type"] Lemma import_iovecs_of_array : forall ms iovs iov,
ms_rom ms = seg_rom segs ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array (ms_mem ms) iov iovs ->
iov_bufs_ok iovs ->
import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
intros ms iovs iov Hrom Hcnt Hok Harr Hbok. unfold import_iovecs.
destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
destruct r as [|[b2 n2] r2].
-
cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia.
rewrite (read_iovec_entry_of_array ms b n [] iov Hrom Harr).
destruct Hbok as [Hb _]. pose proof (u64_range n).
rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
by (unfold MAX_RW_COUNT in *; lia).
reflexivity.
-
set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
rewrite E1, E0. rewrite u64_lit by lia.
replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
rewrite (access_okb_of_le iov (16 * cnt)) by lia.
rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
rewrite (copy_iovecs_of_array ms _ iov Hrom Harr).
rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.

#[using="Type"] Lemma import_iovecs_accesses_of_array : forall ms (iovs : list (word * word)) iov,
ms_rom ms = seg_rom segs ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))
= copy_iovecs_accesses (ms_read_byte ms) iov (length iovs).
Proof.
intros ms iovs iov Hrom Hcnt Hok. unfold import_iovecs_accesses.
destruct iovs as [|e r]; [cbn in Hcnt; lia|].
destruct r as [|e2 r2].
- cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia. cbn [copy_iovecs_accesses].
destruct (read_iovec_entry _ _); reflexivity.
- set (cnt := Z.of_nat (length (e :: e2 :: r2))) in *.
assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
rewrite E1, E0. rewrite u64_lit by lia.
replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
rewrite (access_okb_of_le iov (16 * cnt)) by lia.
rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id. reflexivity.
Qed.

#[using="Type"] Lemma writev_outcome : forall ms x8 model (fd : Z) (iov : word) iovs bss,
ms_rom ms = seg_rom segs ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
bv_unsigned x8 = 66%Z ->
ms_gpr ms 0 = Z_to_bv 64 fd ->
ms_gpr ms 1 = iov ->
ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array (ms_mem ms) iov iovs ->
iov_bufs_ok iovs ->
iov_bufs (ms_mem ms) iovs bss ->
let bs := concat bss in
let tot := iovs_total iovs in
(1 <= tot)%Z -> (tot <= 2 ^ 30)%Z ->
let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
Z.of_nat (length bs) = tot /\
forall o, syscall_spec (sys_input segs ms x8) model o <->
exists k, (1 <= k <= length bs)%nat /\
o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
model (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs)).
Proof.
intros ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Ht30 CA.
pose proof (gather_of_bufs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
split; [exact Hlen|].
intros o.
rewrite (syscall_spec_66 (sys_input segs ms x8) model o) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
rewrite fd32_id by (rewrite u64_lit; lia).
assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
{ unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
subst CA. change (ms_read_byte ms) with (in_mem (sys_input segs ms x8)).
replace (import_iovecs_accesses (in_mem (sys_input segs ms x8)) iov (Z_to_bv 64 (Z.of_nat (length iovs))))
with (import_iovecs_accesses (in_mem (sys_input segs ms x8)) iov (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs)))))
by (rewrite Hcnt32; reflexivity).
apply (writev_chan_outcome _ _ _ _ model o (Z_to_bv 64 fd) iovs bs Hfd).
- apply w_is0_pos. rewrite u64_lit; lia.
- rewrite Hcnt32, in_mem_si. exact (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
- unfold MAX_RW_COUNT. lia.
- rewrite in_mem_si. exact Hg.
- lia.
Qed.

#[using="Type"] Lemma rz_writev_pending : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
ms_rom ms = seg_rom segs ->
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
bv_unsigned x8 = 66%Z ->
ms_gpr ms 0 = Z_to_bv 64 fd ->
ms_gpr ms 1 = iov ->
ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array (ms_mem ms) iov iovs ->
iov_bufs_ok iovs ->
iov_bufs (ms_mem ms) iovs bss ->
let bs := concat bss in
(1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
(forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
realizes segs (mkCfg ms model)
(t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
Ht1 Ht30 Hk.
destruct (writev_outcome ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
Ht1 Ht30)
as [Hlen Hchk]. fold bs in Hlen, Hchk.
set (tot := iovs_total iovs) in *.
set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
assert (Hnb : (1 <= length bs)%nat) by lia.
pose (effs := fun i : wr_index bs =>
mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
(CA ++ iov_prefix_accesses iovs (proj1_sig i))).
assert (Enx : forall i : wr_index bs,
mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
= mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
{ intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
reflexivity. }
apply (rz_node segs (mkCfg ms model) (wr_index bs)
(fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
(fun i => T (proj1_sig i)) (wr_full bs Hnb)).
2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
assert (Hnode : node_ok segs (mkCfg ms model) (wr_index bs)
(fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) model)).
{ apply (node_family segs ms model x8 (wr_index bs) effs (fun _ => model)
(fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) _ Hh Hsvc Hchk).
- intros [k Hk']. exists k. split; [exact Hk'|reflexivity].
- intros o (k & Hk' & ->). exists (exist _ k Hk'). reflexivity.
- intros _; exact Hh.
- intros _; exact Hlazy.
- intros i. apply not_spurious_sysno. rewrite in_sysno_sys_input, Hno. vm_compute. intuition discriminate. }
destruct Hnode as [Hn1 Hn2]. split.
- intros i. rewrite Enx. apply Hn1.
- intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_writev2 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr regs 17 = Z_to_bv 64 66 ->
getr regs 10 = Z_to_bv 64 fd ->
getr regs 11 = iov ->
getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
(bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
(forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
(T k)) ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
(t_alt (fun i : wr_index (bs1 ++ bs2) =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
pose proof (u64_range n1). pose proof (u64_range n2).
replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1); (b2, n2)] [bs1; bs2] T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
| | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend].
replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
rewrite at_at. reflexivity. }
repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. repeat split; assumption.
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

#[using="Type"] Lemma rz_writev1 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr regs 17 = Z_to_bv 64 66 ->
getr regs 10 = Z_to_bv 64 fd ->
getr regs 11 = iov ->
getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1)%Z ->
(bv_unsigned n1 <= 2 ^ 30)%Z ->
(forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
(T k)) ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
(t_alt (fun i : wr_index bs1 =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
pose proof (u64_range n1).
replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1)] [bs1] T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
| | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

#[using="Type"] Lemma rz_writev2_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr regs 17 = Z_to_bv 64 66 ->
getr regs 10 = Z_to_bv 64 fd ->
getr regs 11 = iov ->
getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
(bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
K [] ->
(forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
pose proof (u64_range n1). pose proof (u64_range n2).
apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

#[using="Type"] Lemma rz_writev1_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr regs 17 = Z_to_bv 64 66 ->
getr regs 10 = Z_to_bv 64 fd ->
getr regs 11 = iov ->
getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1)%Z ->
(bv_unsigned n1 <= 2 ^ 30)%Z ->
K [] ->
(forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

#[using="Type"] Lemma rz_writev2_ch : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr regs 17 = Z_to_bv 64 66 ->
getr regs 10 = Z_to_bv 64 fd ->
getr regs 11 = iov ->
getr regs 12 = Z_to_bv 64 2 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
(bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
(bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
(bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
(1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
(bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
(forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
(t_write_ch (Z_to_bv 64 fd) (bs1 ++ bs2) K).
Proof.
intros. unfold t_write_ch.
eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.

#[using="Type"] Lemma rz_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr regs 17 = Z_to_bv 64 66 ->
getr regs 10 = Z_to_bv 64 fd ->
getr regs 11 = iov ->
getr regs 12 = Z_to_bv 64 1 ->
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
(bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
(bv_unsigned b1 <= TASK_SIZE)%Z ->
(0 <= rw_bytes_max)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hmax Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
assert (Harr : iov_array (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
{ cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
{ unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia.
rewrite (read_iovec_entry_of_array ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
{ unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
eapply (rz_ret_only_copyins_silent segs ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
[exact Hh | reflexivity | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
intros o.
rewrite (syscall_spec_66 (sys_input segs ms (getr regs 17)) model o) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si.
assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
rewrite G0, G1, G2.
rewrite fd32_id by (rewrite u64_lit; lia).
rewrite <- Hacc.
change (ms_read_byte ms) with (in_mem (sys_input segs ms (getr regs 17))).
change (Z_to_bv 64 1) with (iovcnt32 (Z_to_bv 64 1)) at 2.
apply (writev_chan_zero_outcome _ _ _ _ model o (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] Hfd).
- apply w_is0_pos. rewrite u64_lit; lia.
- rewrite in_mem_si. exact Himp.
- reflexivity.
Qed.

End WithSegs.
End FPGEN1.

End Mq0.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj Qn1e.Mq1 QiVh Qn1e Q9ox.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition MS (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
(m ro : word -> option byte) : machine_state :=
{| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None;
ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

Definition MSsvc (R F : bvmap 5 word) (pc : word) (x8 : word) (fc : bv 32) (rv : option word)
(m ro : word -> option byte) : machine_state :=
{| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := Some x8;
ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

#[using="Type"] Lemma mkst_MS : forall regs pc mem rom,
mkst regs pc mem rom = MS regs fF pc fC None mem rom.
Proof. reflexivity. Qed.

#[using="Type"] Lemma epend_MSsvc : forall regs pc mem rom x8,
epend regs pc mem rom x8 = MSsvc regs fF pc x8 fC None mem rom.
Proof. reflexivity. Qed.

#[using="Type"] Lemma MS_eta : forall ms, ms_svc_pending ms = None ->
ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H; cbn in *; subst; reflexivity. Qed.

#[using="Type"] Lemma MSsvc_eta : forall ms x8, ms_svc_pending ms = Some x8 ->
ms = MSsvc (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) x8 (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] x8 H; cbn in *; subst; reflexivity. Qed.

#[using="Type"] Lemma step_ecall_MS : forall segs R F pc fc rv m ro w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step segs (MS R F pc fc rv m ro) =
MachineOk (MSsvc R F pc (getr R 17) fc rv m ro).
Proof.
intros segs R F pc fc rv m ro w Hf He.
unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
cbn [ms_pc ms_pc_val MS]. rewrite Hf. cbv beta iota.
unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses.
rewrite He. cbv beta iota. reflexivity.
Qed.

#[using="Type"] Lemma MSsvc_svc : forall R F pc x8 fc rv m ro, ms_svc_pending (MSsvc R F pc x8 fc rv m ro) = Some x8.
Proof. reflexivity. Qed.
#[using="Type"] Lemma MS_svc : forall R F pc fc rv m ro, ms_svc_pending (MS R F pc fc rv m ro) = None.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_gpr_MSsvc0 : forall R F pc x8 fc rv m ro, ms_gpr (MSsvc R F pc x8 fc rv m ro) 0 = getr R 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs MSsvc]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_MSsvc1 : forall R F pc x8 fc rv m ro, ms_gpr (MSsvc R F pc x8 fc rv m ro) 1 = getr R 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs MSsvc]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_MSsvc2 : forall R F pc x8 fc rv m ro, ms_gpr (MSsvc R F pc x8 fc rv m ro) 2 = getr R 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs MSsvc]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_MSsvc3 : forall R F pc x8 fc rv m ro, ms_gpr (MSsvc R F pc x8 fc rv m ro) 3 = getr R 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs MSsvc]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_MSsvc4 : forall R F pc x8 fc rv m ro, ms_gpr (MSsvc R F pc x8 fc rv m ro) 4 = getr R 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs MSsvc]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_MSsvc5 : forall R F pc x8 fc rv m ro, ms_gpr (MSsvc R F pc x8 fc rv m ro) 5 = getr R 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs MSsvc]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.

#[using="Type"] Lemma ms_read_byte_MSsvc : forall segs R F pc x8 fc rv m,
ms_read_byte (MSsvc R F pc x8 fc rv m (seg_rom segs)) = mrb segs m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_writable_byte_MSsvc : forall segs R F pc x8 fc rv m ro,
ms_writable_byte segs (MSsvc R F pc x8 fc rv m ro) = wview segs m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_read_byte_MS : forall segs R F pc fc rv m,
ms_read_byte (MS R F pc fc rv m (seg_rom segs)) = mrb segs m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_writable_byte_MS : forall segs R F pc fc rv m ro,
ms_writable_byte segs (MS R F pc fc rv m ro) = wview segs m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_mem_MSsvc : forall R F pc x8 fc rv m ro, ms_mem (MSsvc R F pc x8 fc rv m ro) = m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ms_mem_MS : forall R F pc fc rv m ro, ms_mem (MS R F pc fc rv m ro) = m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma in_sysno_MSsvc : forall segs R F pc x8 fc rv m ro,
in_sysno (sys_input segs (MSsvc R F pc x8 fc rv m ro) x8) = x8.
Proof. reflexivity. Qed.

Definition eff_mem (eff : SyscallEffect) (m : word -> option byte) : word -> option byte :=
apply_writes
(apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps eff)) (eff_zeros eff))
(eff_copies eff))
(eff_writes eff).

#[using="Type"] Lemma adv_MSsvc : forall R F pc x8 fc rv m ro eff,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) eff)
= MS (regupd R 10 (eff_ret eff)) F (v_addi pc 4) fc rv (eff_mem eff m) ro.
Proof.
intros R F pc x8 fc rv m ro eff.
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MSsvc].
unfold MS, regupd, eff_mem. rewrite b_npc4. reflexivity.
Qed.

#[using="Type"] Lemma adv_set_MSsvc : forall R F pc x8 fc rv m ro v,
advance_past_svc (set_gpr0 (MSsvc R F pc x8 fc rv m ro) v)
= MS (regupd R 10 v) F (v_addi pc 4) fc rv m ro.
Proof.
intros R F pc x8 fc rv m ro v.
unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota.
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MSsvc].
unfold MS, regupd. rewrite b_npc4. reflexivity.
Qed.

#[using="Type"] Lemma eff_mem_ret : forall r ca m, eff_mem (mkEffectU r [] [] [] [] ca) m = m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma eff_mem_mkEffect_nil : forall r m, eff_mem (mkEffect r [] []) m = m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma eff_mem_copyins : forall reads eff m, eff_mem (with_copyins reads eff) m = eff_mem eff m.
Proof. intros reads [r ws zs us cs ca] m. reflexivity. Qed.

#[using="Type"] Lemma eff_ret_copyins : forall reads eff, eff_ret (with_copyins reads eff) = eff_ret eff.
Proof. intros reads [r ws zs us cs ca]. reflexivity. Qed.

#[using="Type"] Lemma eff_mem_write1 : forall r buf data m,
eff_mem (mkEffect r [(buf, data)] []) m = wbytes m buf data.
Proof.
intros. unfold eff_mem. cbn [eff_writes eff_zeros eff_unmaps eff_copies apply_copies apply_zeros apply_unmaps apply_writes].
apply write_to_mem_wbytes.
Qed.

#[using="Type"] Lemma eff_mem_delivered : forall r buf data m,
eff_mem (mkEffect r (delivered_writes buf data) []) m = wbytes m buf data.
Proof.
intros r buf [|b rest] m; [reflexivity | apply eff_mem_write1].
Qed.

#[using="Type"] Lemma eff_mem_zeros1 : forall r a n m,
eff_mem (mkEffectU r [] [(a, n)] [] [] []) m = zfill a n m.
Proof.
intros. unfold eff_mem. cbn [eff_writes eff_zeros eff_unmaps eff_copies apply_copies apply_unmaps apply_writes].
unfold zfill. exact (apply_zeros_one m a n).
Qed.

#[using="Type"] Lemma eff_mem_mkEffect_zeros1 : forall r a n m,
eff_mem (mkEffect r [] [(a, n)]) m = zfill a n m.
Proof. intros. apply eff_mem_zeros1. Qed.

#[using="Type"] Lemma eff_mem_unmaps1 : forall r a n m,
eff_mem (mkEffectU r [] [] [(a, n)] [] []) m = unfill a n m.
Proof.
intros. unfold eff_mem. cbn [eff_writes eff_zeros eff_unmaps eff_copies apply_copies apply_zeros apply_writes].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma adv_ret_MSsvc : forall R F pc x8 fc rv m ro r ca,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (mkEffectU r [] [] [] [] ca))
= MS (regupd R 10 r) F (v_addi pc 4) fc rv m ro.
Proof. intros. rewrite adv_MSsvc. reflexivity. Qed.

#[using="Type"] Lemma adv_copyins_ret_MSsvc : forall R F pc x8 fc rv m ro r reads,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (with_copyins reads (mkEffect r [] [])))
= MS (regupd R 10 r) F (v_addi pc 4) fc rv m ro.
Proof. intros. rewrite adv_MSsvc, eff_ret_copyins, eff_mem_copyins. reflexivity. Qed.

#[using="Type"] Lemma adv_write1_MSsvc : forall R F pc x8 fc rv m ro r buf data,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (mkEffect r [(buf, data)] []))
= MS (regupd R 10 r) F (v_addi pc 4) fc rv (wbytes m buf data) ro.
Proof. intros. rewrite adv_MSsvc, eff_mem_write1. reflexivity. Qed.

#[using="Type"] Lemma adv_delivered_MSsvc : forall R F pc x8 fc rv m ro r buf data,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (mkEffect r (delivered_writes buf data) []))
= MS (regupd R 10 r) F (v_addi pc 4) fc rv (wbytes m buf data) ro.
Proof. intros. rewrite adv_MSsvc, eff_mem_delivered. cbn [eff_ret]. reflexivity. Qed.

#[using="Type"] Lemma adv_zeros1_MSsvc : forall R F pc x8 fc rv m ro r a n,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (mkEffectU r [] [(a, n)] [] [] []))
= MS (regupd R 10 r) F (v_addi pc 4) fc rv (zfill a n m) ro.
Proof. intros. rewrite adv_MSsvc, eff_mem_zeros1. reflexivity. Qed.

#[using="Type"] Lemma adv_unmaps1_MSsvc : forall R F pc x8 fc rv m ro r a n,
advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (mkEffectU r [] [] [(a, n)] [] []))
= MS (regupd R 10 r) F (v_addi pc 4) fc rv (unfill a n m) ro.
Proof. intros. rewrite adv_MSsvc, eff_mem_unmaps1. reflexivity. Qed.
End FPGEN1.

End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS QMz4 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QJyS QwNp QMz4 Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3 QBxa.Mq0 Q9ox.Mq0.
Import Q6q3.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Context {RC__ : Q6q3.RunConsts}.

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

#[using="Type"] Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

#[using="Type"] Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

#[using="Type"] Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. intros fds m. reflexivity. Qed.

#[using="Type"] Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. intros fds m. reflexivity. Qed.

#[using="Type"] Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

#[using="Type"] Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

#[using="Type"] Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

#[using="Type"] Lemma with_vmmaps_eta : forall m,
with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

#[using="Type"] Lemma vmmaps_eta : forall h,
mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

#[using="Type"] Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma vm_forget_range_id : forall lo hi m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
vm_forget_range lo hi m = m.
Proof.
intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
rewrite Hl, Hm. cbn [maps_subtract List.filter].
destruct m as [? [? l mt] ? ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

#[using="Type"] Lemma vm_forget_range_lazy_nil : forall lo hi m,
m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

#[using="Type"] Lemma vm_forget_range_halted : forall lo hi m,
m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Inductive three : Type := T1 | T2 | T3.

#[using="Type"] Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
node_ok segs c three (fun _ => []) nx ->
realizes segs (nx T1) A -> realizes segs (nx T2) B -> realizes segs (nx T3) C ->
realizes segs c (t_alt3 A B C).
Proof.
intros c nx A B C Hnode HA HB HC.
apply (rz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
- apply (rz_cases segs c three nx _ T1 Hnode). intros [| |]; assumption.
- intros tr. unfold t_alt3, t_alt2, t_alt. split.
+ intros [[| |] H]; tauto.
+ intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

#[using="Type"] Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
(forall i, sstep_cfg segs (alloc_only_cfg false) c (evs i) (SNext (nx i))) ->
(forall e st, sstep_cfg segs (alloc_only_cfg false) c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
node_ok segs c I evs nx.
Proof. intros; split; assumption. Qed.

#[using="Type"] Lemma adv_ret_epend : forall regs pc mem rom x8 r,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

#[using="Type"] Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
intros. unfold epend.
assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
{ cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

#[using="Type"] Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
intros. unfold epend.
assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
{ cbn [apply_writes apply_zeros].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity. }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

#[using="Type"] Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
= mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

#[using="Type"] Lemma rz_close : forall regs (pc : word) mem model w fd e K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 57 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some e ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_remove (m_fds model) fd) model)) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
- intros o. rewrite (syscall_spec_57 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
rewrite in_arg0_si, ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). exact (close_outcome fd _ model e o Hlk).
- rewrite with_fds_halted'. exact Hh.
- rewrite with_fds_lazy. exact Hlazy.
Qed.

#[using="Type"] Lemma rz_ioctl_winsz_gen : forall regs (pc : word) mem model w fd e K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 29 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some e ->
fd_ioctl_modeled e ->
getr regs 11 = Z_to_bv 64 0x5413 ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk He H11 Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros o. rewrite (syscall_spec_29 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
rewrite in_arg0_si, in_arg1_si, ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11.
apply (ioctl_tty_outcome fd _ _ model e o Hlk He). reflexivity.
Qed.

#[using="Type"] Lemma rz_ioctl_winsz : forall regs (pc : word) mem model w fd c K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 29 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some (FdChannel c) ->
getr regs 11 = Z_to_bv 64 0x5413 ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd c K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H11 Hc.
exact (rz_ioctl_winsz_gen regs pc mem model w fd _ K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk I H11 Hc).
Qed.

#[using="Type"] Lemma rz_read_dir : forall regs (pc : word) mem model w fd K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 63 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some FdDir ->
(bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= task_size_max)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros o. rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
apply (read_dir_outcome fd _ _ _ model o Hlk). apply access_okb_of_bound.
rewrite <- task_size_max_eq. exact Hdir.
Qed.

#[using="Type"] Lemma read_file_outcome_si : forall ms x8 model fd p off data wv,
bv_unsigned x8 = 63%Z ->
ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some wv ->
(0 < bv_unsigned (ms_gpr ms 2))%Z -> (bv_unsigned (ms_gpr ms 2) <= access_ok_walk_max)%Z ->
(bv_unsigned (ms_gpr ms 1) + bv_unsigned (ms_gpr ms 2) <= task_size_max)%Z ->
let bs := file_read data off (ms_gpr ms 2) in
let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
forall o, syscall_spec (sys_input segs ms x8) model o <->
o = Ok (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []) m' [].
Proof.
intros ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs Hw Hpos HcntW Hover. cbv zeta. intros o.
pose proof access_ok_walk_max_le_rw as Hwr.
assert (Hcnt : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by lia.
assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
<= bv_unsigned (ms_gpr ms 2))%Z).
{ unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (u64_range (ms_gpr ms 2)) as Hc.
rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
rewrite Z.mod_small; lia. }
rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, (fd32_id fd Hfd32).
assert (Hcl : Z_to_bv 64 (rw_count_clamp (ms_gpr ms 2)) = ms_gpr ms 2).
{ rewrite (rw_count_clamp_of_rw _ Hcnt). apply Z_to_bv_bv_unsigned. }
rewrite (read_file_outcome fd (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o p off data
(firstn (word_to_nat (len_word (file_read data off (ms_gpr ms 2)))) wv) Hlk).
- rewrite Hcl. reflexivity.
- apply access_okb_of_bound. rewrite <- task_size_max_eq. exact Hover.
- exact Hfs.
- rewrite Hcl, in_wmem_si. exact (read_bytes_map_prefix _ _ _ _ _ HL Hw).
Qed.

#[using="Type"] Lemma rz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 63 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
getr regs 12 = Z_to_bv 64 cnt ->
(1 <= cnt)%Z -> (cnt <= access_ok_walk_max)%Z -> (cnt < 2 ^ 64)%Z ->
(bv_unsigned (getr regs 11) + cnt <= task_size_max)%Z ->
store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
let bs := file_read data off (getr regs 12) in
realizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
(wbytes mem (getr regs 11) bs) (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hok bs Hc.
assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
rewrite Z2Nat.id in Hw by lia.
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
{ unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
pose proof (read_file_outcome_si ms (getr regs 17) model fd p off data wv Hno
ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Hover)) as Hchk.
unfold ms in Hchk. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
subst bs. revert Hc Hchk.
generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
eapply (rz_det segs _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
[exact Hh | reflexivity | exact Hchk
| rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
destruct bs as [|b bsr]; cbn [delivered_writes].
- unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
- unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

Section Openat.
Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
Variable w : bv 32.
Hypothesis HF : fetch_word segs pc = Some w.
Hypothesis HE : is_ecall w = true.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
Hypothesis H10 : getr regs 10 = AT_FDCWD.

Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
Let fds := m_fds model.

#[using="H17"] Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
Proof. rewrite H17. apply u64_lit. lia. Qed.

#[using="H17 H10"] Lemma openat_spec_head : forall o,
syscall_spec (sys_input segs ms (getr regs 17)) model o <->
openat_spec AT_FDCWD32 (getr regs 11) (getr regs 12) (sys_input segs ms (getr regs 17)) model o.
Proof.
intros o. cbv delta [ms].
rewrite (syscall_spec_56 _ model o) by (rewrite in_sysno_si; exact Hno56).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
reflexivity.
Qed.

#[using="Type"] Lemma open_in_mem : in_mem (sys_input segs ms (getr regs 17)) = mrb segs mem.
Proof. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend. reflexivity. Qed.

#[using="Hfl"] Lemma open_flags_modeled : modeled_open_flags (getr regs 12) = true.
Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

#[using="Type"] Lemma open_reads_ms : open_reads (sys_input segs ms (getr regs 17)) (getr regs 11) = open_copyins ms.
Proof. cbv delta [ms]. unfold open_reads, open_copyins. rewrite in_mem_si, ms_gpr_epend1. reflexivity. Qed.

#[using="w HF HE Hh Hlazy H17 H10 Hfl ms"] Lemma rz_openat_toolong : forall bs K,
rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
realizes segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros bs K Hrd Hnz Hc. cbv delta [post] in *.
pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros o. fold ms. rewrite openat_spec_head.
apply (openat_toolong_outcome _ _ _ _ model open_flags_modeled). rewrite open_in_mem. exact Hp.
Qed.

Definition path_at (p : list byte) : Prop :=
(length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
/\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

#[using="Type"] Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

#[using="w HF HE Hh Hlazy H17 H10 Hfl ms"] Lemma rz_openat_empty : forall K,
path_at [] ->
realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros K Hp Hc. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros o. fold ms. rewrite openat_spec_head.
apply (openat_empty_outcome _ _ _ _ model open_flags_modeled). rewrite open_in_mem. exact (path_at_cstr [] Hp).
Qed.

#[using="w HF HE Hh Hlazy H17 H10 Hfl ms"] Lemma rz_openat_absent : forall p K,
path_at p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
fs_lookup (m_fs model) p = None ->
realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros p K Hp Hne Hsl Hnd Hfs Hc. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros o. fold ms. rewrite openat_spec_head.
apply (openat_absent_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p);
[rewrite open_in_mem; exact (path_at_cstr p Hp) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
Qed.

Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

#[using="w HF HE Hh Hlazy H17 H10 Hfl ms Hfree"] Lemma rz_openat_dot : forall KA KB,
path_at dot_path ->
(forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
realizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
intros KA KB Hp HA HB. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_open; [exact Hh | exact Hlazy | reflexivity | rewrite H17; vm_compute; intuition discriminate | | | | exact Hfree | |].
- intros o. fold ms. rewrite openat_spec_head.
apply (openat_dot_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl).
rewrite open_in_mem. exact (path_at_cstr _ Hp).
- intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
- intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
- intros e He. rewrite adv_set_epend. apply HA. exact He.
- rewrite adv_set_epend. exact HB.
Qed.

#[using="w HF HE Hh Hlazy H17 H10 Hfl ms Hfree"] Lemma rz_openat_file : forall p d KA KB,
path_at p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
fs_lookup (m_fs model) p = Some d ->
(forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
realizes segs (mkCfg (post (alloc_fd fds))
(with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
intros p d KA KB Hp Hne Hsl Hnd Hfs HA HB. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_open; [exact Hh | exact Hlazy | reflexivity | rewrite H17; vm_compute; intuition discriminate | | | | exact Hfree | |].
- intros o. fold ms. rewrite openat_spec_head.
apply (openat_file_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p d);
[rewrite open_in_mem; exact (path_at_cstr p Hp) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
- intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
- intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
- intros e He. rewrite adv_set_epend. apply HA. exact He.
- rewrite adv_set_epend. exact HB.
Qed.
End Openat.

#[using="Type"] Lemma alloc_fd_init : forall e0 e1 e2,
alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma fd_lookup_init_3 : forall e0 e1 e2,
fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma rz_munmap : forall regs (pc : word) mem model w (a : word) (len : Z) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 215 ->
getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned a + page_round_up_Z len <= task_size_max)%Z ->
map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
(munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
rewrite task_size_max_eq in Hnw.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
eapply (QRjH.rz_munmap segs ms model (getr regs 17));
[exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

#[using="Type"] Lemma munmap_model_simple : forall (a n : word) m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
munmap_model a n m
= with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.

#[using="Type"] Lemma node_brk : forall ms model x8,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
(forall r, brk_resolution_ok model (ms_gpr ms 0) r ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model
(mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [])) ->
node_ok segs (mkCfg ms model)
{r : word | brk_resolution_ok model (ms_gpr ms 0) r}
(fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms
(mkEffectU (proj1_sig i) []
(brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
(brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
(brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Hns. split.
- intros [r Hr]. cbn [proj1_sig].
pose proof (brk_ok_intro segs ms x8 model r Hno Hr) as Hspec.
destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec) as (_ & Hh' & _ & _ & Hlazy').
apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms model x8 _ _ _ [] Hh Hsvc Hspec (Hns r Hr) Hh').
apply materialize_model_accesses_no_lazy. rewrite Hlazy'. exact Hlazy.
- intros e st Hss. apply sstep_cfg_sub in Hss.
destruct (sstep_brk_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hss) as (eff & model' & Hspec & -> & ->).
apply (brk_ok_iff segs ms x8 model eff model' [] Hno) in Hspec.
destruct Hspec as (Heff & _ & Hok & ->).
exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. split; reflexivity.
Qed.

#[using="Type"] Lemma sstep_cfg_brk_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 214%Z ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms model) evs st ->
exists eff model',
syscall_spec (sys_input segs ms x8) model (Ok eff model' [])
/\ ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff
/\ evs = []
/\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
inversion Hss; subst; try congruence.
- match goal with
| Hp : ms_svc_pending ms = Some ?x,
Hs : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?m' ?evs0),
Hns : ~ spurious_refusal_cfg _ _ _ _,
Hmat : materialize_model_accesses ?m' _ = Some ?m'' |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape segs ms x8 model eff m' evs0 Hh Hlazy Hno Hs) as (He & _ & _ & _ & Hlazy');
subst evs0;
rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
injection Hmat as Hm; subst;
eexists _, _; split; [exact Hs | split; [exact Hns | split; reflexivity]]
end.
- exfalso. match goal with
| Hp : ms_svc_pending ms = Some ?x,
Hs : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?m' ?evs0),
Hmat : materialize_model_accesses ?m' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape segs ms x8 model eff m' evs0 Hh Hlazy Hno Hs) as (_ & _ & _ & _ & Hlazy');
rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat; discriminate
end.
- exfalso. match goal with
| Hp : ms_svc_pending ms = Some ?x,
Hs : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?m' ?evs0),
Hhalt : m_halted ?m' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape segs ms x8 model eff m' evs0 Hh Hlazy Hno Hs) as (_ & Hm & _ & _); congruence
end.
- exfalso. match goal with
| Hp : ms_svc_pending ms = Some ?x,
Hs : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?m' ?evs0),
Hkill : m_killed ?m' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape segs ms x8 model eff m' evs0 Hh Hlazy Hno Hs) as (_ & Hm & _ & _);
rewrite (m_killed_of_m_halted_none _ Hm) in Hkill; discriminate
end.
- exfalso. match goal with
| Hp : ms_svc_pending ms = Some ?x,
Hs : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (brk_no_unmodeled segs ms x8 model Hno Hs)
end.
Qed.

#[using="Type"] Lemma node_brk_grow : forall ms model x8,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
EdBridge.ed_brk_grow model (ms_gpr ms 0) ->
Mmap.brk_grow_ok model (ms_gpr ms 0) (ms_gpr ms 0) = true ->
node_ok segs (mkCfg ms model) unit (fun _ => [])
(fun _ => mkCfg (advance_past_svc (apply_effect ms (EdBridge.ed_brk_eff model (ms_gpr ms 0) (ms_gpr ms 0))))
(brk_model (ms_gpr ms 0) (ms_gpr ms 0) model)).
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Hg HG.
assert (Hc : EdBridge.ed_brk_call (sys_input segs ms x8) (ms_gpr ms 0)) by (split; [exact Hno | reflexivity]).
destruct (EdBridge.ed_brk_grow_grant_nonspurious _ _ _ Hc Hg HG) as [Hspec Hns].
unfold brk_model. split.
- intros [].
destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec) as (_ & Hh' & _ & _ & Hlazy').
apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms model x8 _ _ _ [] Hh Hsvc Hspec Hns Hh').
apply materialize_model_accesses_no_lazy. rewrite Hlazy'. exact Hlazy.
- intros e st Hss.
destruct (sstep_cfg_brk_inv ms model x8 e st Hh Hlazy Hsvc Hno Hss) as (eff & model' & Hs & Hns' & -> & ->).
destruct (EdBridge.ed_brk_grow_inversion _ _ _ _ _ _ Hc Hg Hs Hns') as (r & -> & -> & _ & [[-> _] | [_ HF]]).
+ exists tt. split; reflexivity.
+ rewrite HG in HF. discriminate HF.
Qed.

#[using="Type"] Lemma brk_r_ok_grow_cases : forall m req r,
let h := m_vmmaps m in
(0 < bv_unsigned req)%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
(bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
brk_resolution_ok m req r <->
(r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
intros m req r h Hpos Hs Hb.
unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
assert (E0 : w_is0 req = false).
{ unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
rewrite E0. unfold min_brk.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
rewrite (proj2 (Z.ltb_ge _ _)) by lia.
rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
- intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
- intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma brk_model_keep : forall m req,
brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
intros m req. unfold brk_model, with_brk_next. cbv zeta.
rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next.
rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

#[using="Type"] Lemma brk_model_grow_eq : forall m (d : Z),
let h := m_vmmaps m in
let b := vm_brk h in
(0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
= with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h)
(Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
intros m d h b Hd Hb0 Hnw Hbal Hdal.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)).
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next. fold b.
rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
cbn [app maps_subtract_ranges fold_left].
replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
apply bv_eq. rewrite bv_sub_unsigned, Hureq.
rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

Definition noaccess_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
((a, n) :: vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

#[using="Type"] Lemma grant_ok_grant_ok_na : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
intros hint m a n H. unfold grant_ok in H. unfold grant_ok_na.
apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma grant_ok_na_not_refusable : forall hint m a n,
grant_ok_na hint m a n = true -> mmap_reserve_refusable m n = false.
Proof.
intros hint m a n Hg. unfold grant_ok_na in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[G1 G2] G3] G4]. unfold mmap_reserve_refusable. apply Bool.negb_false_iff.
apply (proj2 (vm_gap_available_iff _ _)). exists a.
split; [apply Z.eqb_eq; exact G1|]. split; [apply Z.ltb_lt; exact G2|].
split; [apply Z.leb_le; exact G3| exact G4].
Qed.

Lemma not_refusable_grant_ok_na : forall hint m n,
mmap_reserve_refusable m n = false -> exists a, grant_ok_na hint m a n = true.
Proof.
intros hint m n H. unfold mmap_reserve_refusable in H. apply Bool.negb_false_iff in H.
apply (proj1 (vm_gap_available_iff _ _)) in H as (a & A1 & A2 & A3 & A4).
exists a. unfold grant_ok_na.
rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3), A4. reflexivity.
Qed.

Lemma mprotect_refusable_budget : forall m addr n,
mprotect_refusable m addr n = negb (mprotect_budget_ok m addr n).
Proof. reflexivity. Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.

#[using="Type"] Lemma mmap_noaccess_outcome_si : forall ms x8 model,
bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
forall o, syscall_spec (sys_input segs ms x8) model o <->
(exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
\/ (exists a, grant_ok_na (ms_gpr ms 0) model a n = true
/\ o = Ok (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) (noaccess_model a (Z_to_bv 64 n) model) []).
Proof.
intros ms x8 model Hno (H1 & H2 & H3 & H4 & H5) n o.
rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
rewrite H2, H3, H4, H5.
assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
rewrite (mmap_noaccess_outcome (ms_gpr ms 0) (ms_gpr ms 1) (Z_to_bv 64 0) (Z_to_bv 64 34)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs ms x8) model o
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) E1
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
unfold mmap_err_out, grant_ok_na, noaccess_model, with_mmap_backing.
replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity). fold n.
split; (intros [H | (a & Hg & ->)]; [left; exact H | right; exists a; split; [|reflexivity]]).
- destruct Hg as (G1 & G2 & G3 & G4).
rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4. reflexivity.
- rewrite !andb_true_iff in Hg. destruct Hg as [[[G1 G2] G3] G4].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. auto 10.
Qed.

Definition mprotect_model (addr n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

#[using="Type"] Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
bv_unsigned x8 = 226%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
ms_gpr ms 2 = Z_to_bv 64 3 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
forall o, syscall_spec (sys_input segs ms x8) model o <->
(exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
\/ (mprotect_budget_ok model addr n = true
/\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
intros ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma o.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
rewrite (syscall_spec_226 _ model o) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H2.
rewrite <- mprotect_model_next_eq. subst n. rewrite <- Hu1.
apply (mprotect_expose_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) _ model o);
[vm_compute; reflexivity | exact Hal | | rewrite Hu1; exact Hnw | vm_compute; reflexivity
| rewrite Hu1; exact Hna | rewrite Hu1; exact Hma].
unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia.
Qed.

#[using="Type"] Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
(maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

#[using="Type"] Lemma fixed_noaccess_model_simple : forall addr n m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
fixed_noaccess_model addr n m
= with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

#[using="Type"] Lemma fixed_destroyed_model_simple : forall addr n m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
fixed_destroyed_model addr n m
= with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
(maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
/\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.

#[using="Type"] Lemma mmap_fixed_outcome_si : forall ms x8 model (addr : word) (len : Z),
bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
alloc_top (m_vmmaps model) = alloc_ceiling ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
forall o, syscall_spec (sys_input segs ms x8) model o <->
o = Ok (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) []
\/ (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
\/ (exists e, In e mmap_errnos /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
(with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []).
Proof.
intros ms x8 model addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H1' Hlen Hce Hceil n Hrf Hmc o.
assert (Hlen' : (len < 2 ^ 64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
rewrite H2, H3, H4, H5, H0.
assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
subst n. rewrite <- Hu1.
rewrite (mmap_fixed_noaccess_outcome addr (ms_gpr ms 1) (Z_to_bv 64 0) (Z_to_bv 64 50)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) (sys_input segs ms x8) model o
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) E1
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(rewrite Hu1, Hceil; exact Hce) Hal Hpos ltac:(rewrite Hu1; exact Hrf) ltac:(rewrite Hu1; exact Hmc)).
unfold mmap_err_out, fixed_noaccess_model, with_mmap_replacement, with_mmap_backing.
replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
split; intros [H|[H|H]]; [right; left| left| right; right| right; left| left| right; right]; exact H.
Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

#[using="Type"] Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

#[using="Type"] Lemma node_set_tid : forall ms model x8,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
node_ok segs (mkCfg ms model) tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Htid.
assert (Hchk : forall o, syscall_spec (sys_input segs ms x8) model o <->
exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
{ intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_si; exact Hno).
apply set_tid_fresh_outcome. exact Htid. }
pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
assert (Enx : forall i : tid_I,
mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
= mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
{ intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
assert (Hnode : node_ok segs (mkCfg ms model) tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
{ apply (node_family segs ms model x8 tid_I effs (fun i => with_tid (proj1_sig i) model) (fun _ => []) _
Hh Hsvc Hchk).
- intros [t Ht]. exists t. split; [exact Ht|reflexivity].
- intros o (t & Ht & ->). exists (exist _ t Ht). reflexivity.
- intros i. rewrite with_tid_halted. exact Hh.
- intros i. rewrite with_tid_lazy. exact Hlazy.
- intros i. apply not_spurious_sysno. rewrite in_sysno_sys_input, Hno. vm_compute. intuition discriminate. }
destruct Hnode as [Hn1 Hn2]. split.
- intros i. rewrite Enx. apply Hn1.
- intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_set_tid : forall regs (pc : word) mem rom model K w,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
apply (rz_conseq segs _ (t_alt (fun _ : tid_I => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
| eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

#[using="Type"] Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
(getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
getr regs 10 = code ->
realizes segs (mkCfg (mkst regs pc mem rom) model)
(t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply rz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

#[using="Type"] Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
(getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
realizes segs (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

#[using="Type"] Lemma vm_backing_used_simple : forall m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

#[using="Type"] Lemma vm_backed_bytes_no_noaccess : forall h,
vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma brk_grow_ok_aligned_intro : forall m d,
let h := m_vmmaps m in
let b := vm_brk h in
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned b)%Z ->
(bv_unsigned b + d <= alloc_top h)%Z ->
region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
(vm_backing_used m + d <= vm_limit h)%Z ->
Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
intros m d h b Hbal Hdal Hd Hb0 Hce Hrf Hlive.
pose proof (u64_range b) as Hbr. pose proof (alloc_top_lt h) as Htl. unfold two_pow_64 in Htl.
assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z)
by (apply u64_lit; lia).
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
rewrite (proj2 (Z.leb_le _ _) Hce).
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d.
2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

#[using="Type"] Lemma brk_grow_admissible_init : forall model reserved (brk0 mbase sp : word) lim d,
m_vmmaps model = mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp ->
m_vm_lazy model = [] -> m_vm_materialized model = [] ->
alloc_top (m_vmmaps model) = alloc_ceiling ->
(reserved_top reserved <= bv_unsigned brk0)%Z ->
(bv_unsigned brk0 mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned brk0)%Z ->
(bv_unsigned brk0 + d <= alloc_ceiling)%Z ->
(d <= lim)%Z ->
Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned brk0 + d)) (Z_to_bv 64 (bv_unsigned brk0 + d)) = true.
Proof.
intros model reserved brk0 mbase sp lim d Hvm Hlz Hmt Hceil Htop Hbal Hdal Hd Hb0 Hce Hlim.
pose proof (brk_grow_ok_aligned_intro model d) as H. cbv zeta in H. rewrite Hvm in H.
cbn [vm_brk vm_reserved vm_maps vm_limit] in H.
apply H; try assumption; try lia.
- rewrite Hvm in Hceil. rewrite Hceil. exact Hce.
- rewrite app_nil_r. apply region_free_above_top. exact Htop.
- rewrite vm_backing_used_simple by assumption. rewrite Hvm. cbn. lia.
Qed.

End WithSegs.
End FPGEN1.

Local Open Scope Z_scope.
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.
Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma region_free_app : forall l1 l2 (lo n : word),
region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

#[using="Type"] Lemma region_free_In : forall l (lo n b s : word),
region_free l lo n = true -> In (b, s) l ->
bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
apply region_free_cons in Hrf as [Hd Hrf].
destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

#[using="Type"] Lemma region_free_intro : forall l (lo n : word),
(forall b s, In (b, s) l ->
bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
region_free l lo n = true.
Proof.
induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

#[using="Type"] Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

#[using="Type"] Lemma map_contains_head : forall (a sz lo n : word) l,
bv_unsigned a <= bv_unsigned lo ->
bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
map_contains ((a, sz) :: l) lo n = true.
Proof.
intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

#[using="Type"] Lemma map_contains_cons : forall p (lo n : word) l,
map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

#[using="Type"] Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

#[using="Type"] Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma map_remove_skip : forall (b s a : word) l,
b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

#[using="Type"] Lemma map_remove_notin : forall l (a : word),
(forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
induction l as [|[b s] l IH]; intros a H; [reflexivity|].
rewrite map_remove_skip by (apply (H b s); left; reflexivity).
rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

#[using="Type"] Lemma disjoint_base_ne : forall (lo n b s : word),
0 < bv_unsigned n -> 0 < bv_unsigned s ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

#[using="Type"] Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

#[using="Type"] Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

#[using="Type"] Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

#[using="Type"] Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
induction l as [|[b s] l IH]; intros a; [cbn; lia|].
unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

#[using="Type"] Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

#[using="Type"] Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

#[using="Type"] Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
iv_subtract a sz lo hi = [].
Proof.
intros a sz lo hi H1 H2. unfold iv_subtract.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

#[using="Type"] Lemma iv_subtract_self : forall (a sz : word),
iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

#[using="Type"] Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
0 < bv_unsigned sz -> lo <= hi ->
(hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
iv_subtract a sz lo hi = [(a, sz)].
Proof.
intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
destruct Hd as [Hd | Hd].
- rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
rewrite Z.max_l by lia. rewrite u64_roundtrip.
replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite u64_roundtrip. reflexivity.
- rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

#[using="Type"] Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
bv_unsigned a + bv_unsigned sz <= hi ->
iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
intros a sz lo hi H1 H2 H3. unfold iv_subtract.
rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
rewrite Z.min_r by lia. reflexivity.
Qed.

#[using="Type"] Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
lo <= bv_unsigned a -> bv_unsigned a <= hi ->
hi < bv_unsigned a + bv_unsigned sz ->
iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
intros a sz lo hi H1 H2 H3. unfold iv_subtract.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
rewrite Z.max_r by lia. reflexivity.
Qed.

#[using="Type"] Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
0 <= lo -> hi < 2 ^ 64 ->
bv_unsigned sz <= N ->
Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_subtract. apply Forall_app. split.
- destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
rewrite u64_lit by lia. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
rewrite u64_lit by lia. lia.
Qed.

#[using="Type"] Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
0 <= lo -> hi < 2 ^ 64 ->
Forall (fun p => bv_unsigned (snd p) <= N) l ->
Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
- apply iv_subtract_sizes; assumption.
- apply IH; assumption.
Qed.

#[using="Type"] Lemma map_remove_sizes : forall l (a : word) N,
Forall (fun p => bv_unsigned (snd p) <= N) l ->
Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
apply List.incl_filter.
Qed.

#[using="Type"] Lemma maps_subtract_length : forall l (lo hi : Z),
(length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
cbn [maps_subtract]. rewrite length_app. cbn [length].
assert (length (iv_subtract a sz lo hi) <= 2)%nat.
{ unfold iv_subtract. rewrite length_app.
destruct (_ <? _); destruct (_ <? _); cbn; lia. }
specialize (IH lo hi). lia.
Qed.

#[using="Type"] Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
induction l as [|[b s] l IH]; intros a; [cbn; lia|].
unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
fold (map_remove l a); specialize (IH a); lia.
Qed.

#[using="Type"] Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
lo <= hi ->
live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_subtract.
destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
cbn [app live_bytes];
first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
rewrite ?u64_lit by lia; lia.
Qed.

#[using="Type"] Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

#[using="Type"] Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

#[using="Type"] Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
maps_subtract_all maps ((a, n) :: cuts)
= maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

#[using="Type"] Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

#[using="Type"] Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

#[using="Type"] Lemma vm_backing_used_le_live : forall m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

#[using="Type"] Lemma grant_budget_intro : forall m n,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

#[using="Type"] Lemma mprotect_budget_ok_intro : forall m addr n,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
mprotect_budget_ok m addr n = true.
Proof.
intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
rewrite mprotect_model_next_eq. apply Z.leb_le.
etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

#[using="Type"] Lemma file_read_length_eq : forall data (off count : word),
length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

#[using="Type"] Lemma file_read_length_le : forall data (off count : word),
(length (file_read data off count) <= word_to_nat count)%nat
/\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

Definition bottomup_floor : Z := 0x2aaaaaaab000.
#[using="Type"] Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
(a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

#[using="Type"] Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

#[using="Type"] Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand. rewrite bottomup_floor_val. nia. Qed.

#[using="Type"] Lemma conflict_unique : forall N n p j k,
0 <= n <= N -> bv_unsigned (snd p) <= N ->
zconflict (cand N j) n p -> zconflict (cand N k) n p -> j = k.
Proof.
intros N n p j k Hn Hs [A1 A2] [B1 B2].
destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
- pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
- pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

#[using="Type"] Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
List.NoDup js ->
(forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
(length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
inversion Hnd as [|x l Hnotin Hnd']; subst.
cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
-
assert (Hall : forall k, In k js -> P k = false).
{ intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
subst k. exact (Hnotin Hk). }
assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
{ clear -Hall. induction js as [|k js IH]; [reflexivity|].
cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
intros k' Hk'. apply Hall. right. exact Hk'. }
rewrite Hid. lia.
- cbn [List.length].
assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
{ apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
lia.
Qed.

#[using="Type"] Lemma pick_candidate : forall (N n : Z) (l : list (word * word)) (js : list nat),
0 <= n <= N ->
Forall (fun p => bv_unsigned (snd p) <= N) l ->
List.NoDup js -> (length l < length js)%nat ->
exists j, In j js /\ forall p, In p l -> ~ zconflict (cand N j) n p.
Proof.
intros N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
- destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
- inversion Hsz as [|p' l' Hp Hl]; subst.
set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js).
assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
assert (Hlen' : (length js <= S (length js'))%nat).
{ apply filter_keep_all_but_one; [exact Hnd|].
intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
eapply (conflict_unique N n p); eassumption. }
destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
intros q [<- | Hq].
+ intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
+ apply Hfree. exact Hq.
Qed.

#[using="Type"] Lemma region_free_of_noconflict : forall l (a n : Z),
0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
(forall p, In p l -> ~ zconflict a n p) ->
region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
rewrite !u64_lit by lia.
specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
- right. apply Z.ltb_ge. lia.
- left. apply Z.ltb_ge. lia.
Qed.

#[using="Type"] Lemma grant_exists_na_gen : forall hint (m : Model) (N n C : Z),
0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
bottomup_floor + C * (2 * N) + N <= alloc_ceiling ->
alloc_top (m_vmmaps m) = alloc_ceiling ->
exists a, grant_ok_na hint m a n = true.
Proof.
intros hint m N n C HN HNal Hn Hsz Hcnt Hband Hceil.
set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
as (j & Hj & Hfree).
apply in_seq in Hj.
exists (Z_to_bv 64 (cand N j)).
pose proof alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
assert (Hc : bottomup_floor <= cand N j <= bottomup_floor + C * (2 * N)) by (unfold cand; nia).
unfold grant_ok_na. rewrite !u64_lit by lia.
assert (E1 : cand N j mod page_size = 0).
{ unfold cand. rewrite Hfv. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
rewrite Z.mul_0_r. reflexivity. }
rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
rewrite Hceil. rewrite (proj2 (Z.leb_le _ _)) by lia.
fold l. rewrite (region_free_of_noconflict l (cand N j) n) by (first [lia | exact Hfree]).
reflexivity.
Qed.

#[using="Type"] Lemma grant_exists_gen : forall hint (m : Model) (N n C : Z),
0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
bottomup_floor + C * (2 * N) + N <= alloc_ceiling ->
alloc_top (m_vmmaps m) = alloc_ceiling ->
vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
exists a, grant_ok hint m a n = true.
Proof.
intros hint m N n C HN HNal Hn Hsz Hcnt Hband Hceil Hlive.
destruct (grant_exists_na_gen hint m N n C HN HNal Hn Hsz Hcnt Hband Hceil) as [a Ha].
exists a. unfold grant_ok. unfold grant_ok_na in Ha. rewrite Ha.
rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

#[using="Type"] Lemma grant_exists : forall hint (m : Model) (n : Z),
0 <= n <= 2 ^ 30 ->
Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
alloc_top (m_vmmaps m) = alloc_ceiling ->
vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
exists a, grant_ok hint m a n = true.
Proof.
intros hint m n Hn Hsz Hcnt Hceil Hlive. pose proof alloc_ceiling_ge as Hge.
apply (grant_exists_gen hint m (2 ^ 30) n 40000); try assumption; try lia.
- reflexivity.
- rewrite bottomup_floor_val. lia.
Qed.

#[using="Type"] Lemma grant_exists_na : forall hint (m : Model) (n : Z),
0 <= n <= 2 ^ 30 ->
Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
alloc_top (m_vmmaps m) = alloc_ceiling ->
exists a, grant_ok_na hint m a n = true.
Proof.
intros hint m n Hn Hsz Hcnt Hceil. pose proof alloc_ceiling_ge as Hge.
apply (grant_exists_na_gen hint m (2 ^ 30) n 40000); try assumption; try lia.
- reflexivity.
- rewrite bottomup_floor_val. lia.
Qed.

#[using="Type"] Lemma grant_exists_big : forall hint (m : Model) (n : Z),
0 <= n <= 2 ^ 35 ->
Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000 ->
alloc_top (m_vmmaps m) = alloc_ceiling ->
vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
exists a, grant_ok hint m a n = true.
Proof.
intros hint m n Hn Hsz Hcnt Hceil Hlive. pose proof alloc_ceiling_ge as Hge.
apply (grant_exists_gen hint m (2 ^ 35) n 1000); try assumption; try lia.
- reflexivity.
- rewrite bottomup_floor_val. lia.
Qed.

#[using="Type"] Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
vm_limit (m_vmmaps m) < vm_backing_used m + n ->
grant_ok hint m a n = false.
Proof.
intros hint m a n H. unfold grant_ok.
destruct (bv_unsigned a mod page_size =? 0); [|reflexivity].
destruct (0 <? bv_unsigned a); [|reflexivity].
destruct (bv_unsigned a + n <=? alloc_top (m_vmmaps m)); [|reflexivity].
destruct (region_free _ a (Z_to_bv 64 n)); [|reflexivity].
rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
Qed.
End FPGEN2.

End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Export QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QBxa.Mq2 Q9ox.Mq3 Q9ox.Mq4.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Ltac pin :=
repeat match goal with
| H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
end.

Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [Z_to_bv 64 _] => fail
| _ => rewrite (u_Z2bv z) by lia
end
end.

Ltac zlit :=
repeat match goal with
| |- context [Z_to_bv 64 ?z] =>
lazymatch z with
| Z0 => fail | Zpos _ => fail | Zneg _ => fail
| _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
end
end.

Ltac len_rw :=
repeat match goal with
| |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
| |- context [length (zeros ?n)] => rewrite (length_zeros n)
| |- context [length (repeat ?x ?n)] => rewrite (repeat_length x n)
end.

Ltac region_side :=
unfold win_lo;
match goal with |- context [stack_max_size] => rewrite ?stack_max_size_val | _ => idtac end;
len_rw;
cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

Ltac addr_norm :=
gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

Ltac vclose_fin :=
first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
| apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
gres; pin; imm_norm;
first [ reflexivity
| unfold v_addi, v_add; unorm; zlit; vclose_fin
| rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
| rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

Ltac with_mem_hidden tac :=
lazymatch goal with
| |- msteps _ (mkst _ _ ?m _) _ =>
let M := fresh "MEMH" in set (M := m); tac (); subst M
| |- _ => tac ()
end.

Ltac sn F D := with_mem_hidden ltac:(fun _ => stepn F D; pin).
Ltac sv F D v := stepiv F D v vclose.

Ltac stepb_tk F D tac := with_mem_hidden ltac:(fun _ => QRjH.Mq4.stepb_tk F D tac).
Ltac stepb_ft F D tac := with_mem_hidden ltac:(fun _ => QRjH.Mq4.stepb_ft F D tac).

Ltac blit :=
repeat match goal with
| |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
lazymatch z with
| Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
| Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
end
end.

Ltac push_store :=
blit;
first [ rewrite wbytes_cmem_win by region_side
| rewrite wbytes_cmem_data by region_side
| idtac ].

Ltac stw F D aa vv oktac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Store SZ8 _ _ _, _) =>
eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | vclose | vclose | oktac ]
| decode_any _ = Some (Store SZ4 _ _ _, _) =>
eapply step_sw_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | vclose | vclose | oktac ]
| decode_any _ = Some (Store SZ2 _ _ _, _) =>
eapply step_sh_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | vclose | vclose | oktac ]
| decode_any _ = Some (Store SZ1 _ _ _, _) =>
eapply Qn1e.Mq1.step_sb_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
end
| step_simpl; push_store ].

Ltac ok_sub Hok :=
store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

Ltac ok_win HJ :=
apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

Ltac ok_data :=
apply store_ok_cmem_data;
lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

Ltac ld_step F D bsv vv rdtac valtac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
end;
[ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
| step_simpl ]; vnorm; pin.

Ltac lb_step F D bb rdtac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
| decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
end;
[ exact F | reflexivity | exact D | addr_norm; rdtac ]
| step_simpl ]; vnorm; pin.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
(0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
zb + Z.of_nat (length bs) <= 2^64 /\
(za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
intros segs bs m zb za n (Ha & Han & Hb & Hbn & Hd).
apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
End FPGEN1.

Ltac len_simpl :=
len_rw; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul Pos.add Pos.mul].

Ltac peel :=
repeat first [ rewrite rdn_wbytes_out_Z by (len_simpl; lia)
| rewrite rdn_wbytes_out by region_side ].

Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

Ltac rd_hit8 :=
addr_norm; peel;
lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
apply rdn_wbytes_hit8; unorm; lia.

Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

Ltac incl_list :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbn [In] in Hr;
repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

Ltac carry Hag H r T :=
pose proof (Hag r ltac:(notin_list)) as T;
repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
rewrite ?H in T.

Ltac ra_chain :=
first [ apply regs_agree_refl
| apply regs_agree_upd; [ in_list | ]; ra_chain
| match goal with
| Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
end ].
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
forall st st', msteps segs st st' -> G st' -> G st.

#[using="Type"] Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof. intros segs tgt st st' H1 H2. eapply msteps_trans; eassumption. Qed.
End FPGEN2.

Ltac gsteps HG := eapply HG.

Section FPGEN3.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma Z_to_le_bytes_mod8n : forall n z,
Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n))%Z = Z_to_le_bytes n z.
Proof.
intros n z.
pose proof (Z_to_le_bytes_wrap n (N.of_nat (8 * n)) z ltac:(rewrite nat_N_Z; lia)) as H.
unfold bv_wrap, bv_modulus in H. rewrite nat_N_Z in H.
replace (Z.of_nat (8 * n))%Z with (8 * Z.of_nat n)%Z in H by lia. exact H.
Qed.

#[using="Type"] Lemma u_le_bytes_to_word' : forall bs : list byte, (length bs <= 8)%nat ->
bv_unsigned (le_bytes_to_word bs) = bytes_le_to_Z bs.
Proof.
intros bs Hl. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs).
unfold bv_modulus.
assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

#[using="Type"] Lemma Z_to_le_bytes_to_Z' : forall bs : list byte,
Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
rewrite (Z.land_ones (bv_unsigned b) 8) by lia. rewrite Z.mod_small by lia.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z; [apply Z.lor_0_r|].
symmetry. rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
apply Z_mod_mult.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8) by lia. rewrite Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

#[using="Type"] Lemma w2lb4_lw : forall bs : list byte, length bs = 4%nat ->
word_to_le_bytes 4 (v_lw (le_bytes_to_word bs)) = bs.
Proof.
intros bs Hl.
unfold word_to_le_bytes, v_lw. rewrite Z_to_bv_unsigned.
rewrite u_le_bytes_to_word' by lia.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
transitivity (Z_to_le_bytes 4 (bytes_le_to_Z bs)); [| rewrite <- Hl; apply Z_to_le_bytes_to_Z'].
rewrite <- (Z_to_le_bytes_mod8n 4 (bv_wrap 64 _)), <- (Z_to_le_bytes_mod8n 4 (bytes_le_to_Z bs)).
f_equal. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
unfold bv_swrap. unfold bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z.
rewrite Z.mod_mod_divide by (exists (2^32)%Z; reflexivity).
rewrite Zminus_mod, Z.mod_mod by lia.
rewrite <- Zminus_mod. f_equal. lia.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_of_word : forall bs : list byte, (length bs <= 8)%nat ->
bytes_le_to_Z bs = bv_unsigned (le_bytes_to_word bs).
Proof. intros bs Hl. symmetry. apply u_le_bytes_to_word'. exact Hl. Qed.

#[using="Type"] Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
(bv_unsigned a + 4 <= 2^64)%Z ->
rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
intros segs m a v Hnw.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

#[using="Type"] Lemma rdn_app_at : forall segs mem n1 n2 (a : Z) bs1 bs2,
(0 <= a)%Z -> (a + Z.of_nat n1 < 2^64)%Z ->
rdn segs mem (Z_to_bv 64 a) n1 = Some bs1 ->
rdn segs mem (Z_to_bv 64 (a + Z.of_nat n1)) n2 = Some bs2 ->
rdn segs mem (Z_to_bv 64 a) (n1 + n2)%nat = Some (bs1 ++ bs2).
Proof.
intros segs mem n1 n2 a bs1 bs2 Ha Hn H1 H2.
apply rdn_app; [exact H1|]. rewrite word_add_nat, u_Z2bv by lia. exact H2.
Qed.

#[using="Type"] Lemma rdn_guard3 : forall segs D (g : Z) (b0 b1 b2 b3 b4 b5 b6 b7 z : byte),
(0 <= g)%Z -> (g + 8 <= 2^64)%Z ->
rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) [b0; b1; b2; b3])
(Z_to_bv 64 (g + 4)) [b4; b5; b6; b7])
(Z_to_bv 64 (g + 1)) [z])
(Z_to_bv 64 g) 8%nat
= Some [b0; z; b2; b3; b4; b5; b6; b7].
Proof.
intros segs D g b0 b1 b2 b3 b4 b5 b6 b7 z Hg0 Hg8.
set (m := wbytes (wbytes (wbytes D _ _) _ _) _ _).
assert (HL : rdn segs (wbytes D (Z_to_bv 64 g) [b0; b1; b2; b3]) (Z_to_bv 64 g) 4 = Some [b0; b1; b2; b3]).
{ apply (rdn_wbytes_hit segs [b0; b1; b2; b3]). cbn. rewrite u_Z2bv by lia. lia. }
assert (R0 : rdn segs m (Z_to_bv 64 g) 1 = Some [b0]).
{ subst m. rewrite rdn_wbytes_out_Z by (cbn; lia). rewrite rdn_wbytes_out_Z by (cbn; lia).
exact (rdn_firstn segs _ 4 (Z_to_bv 64 g) _ 1 HL ltac:(lia)). }
assert (R1 : rdn segs m (Z_to_bv 64 (g + 1)) 1 = Some [z]).
{ subst m. apply (rdn_wbytes_hit segs [z]). cbn. rewrite u_Z2bv by lia. lia. }
assert (R2 : rdn segs m (Z_to_bv 64 (g + 2)) 2 = Some [b2; b3]).
{ subst m. rewrite rdn_wbytes_out_Z by (cbn; lia). rewrite rdn_wbytes_out_Z by (cbn; lia).
pose proof (rdn_skipn segs _ 4 (Z_to_bv 64 g) _ 2 HL ltac:(lia)) as H2.
rewrite word_add_nat, u_Z2bv in H2 by lia. exact H2. }
assert (R4 : rdn segs m (Z_to_bv 64 (g + 4)) 4 = Some [b4; b5; b6; b7]).
{ subst m. rewrite rdn_wbytes_out_Z by (cbn; lia).
apply (rdn_wbytes_hit segs [b4; b5; b6; b7]). cbn. rewrite u_Z2bv by lia. lia. }
change 8%nat with (1 + (1 + (2 + 4)))%nat.
apply (rdn_app_at segs m 1 7 g [b0] [z; b2; b3; b4; b5; b6; b7]); [lia | cbn; lia | exact R0 |].
apply (rdn_app_at segs m 1 6 (g + Z.of_nat 1) [z] [b2; b3; b4; b5; b6; b7]); [lia | cbn; lia | exact R1 |].
replace (g + Z.of_nat 1 + Z.of_nat 1)%Z with (g + 2)%Z by lia.
apply (rdn_app_at segs m 2 4 (g + 2) [b2; b3] [b4; b5; b6; b7]); [lia | cbn; lia | exact R2 |].
replace (g + 2 + Z.of_nat 2)%Z with (g + 4)%Z by lia. exact R4.
Qed.
End FPGEN3.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 QO3A.
Import Q7m0.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.

Module SX2S.
Import SX2.
Export SX2.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.

#[using="Type"] Lemma mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.

#[using="Type"] Lemma expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
induction x; destruct y; cbn; intros H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
| H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_eq in H
| H : mulop_eqb _ _ = true |- _ => apply mulop_eqb_eq in H
| H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
end; subst; reflexivity.
Qed.

#[using="Type"] Lemma saddr_eqb_eq : forall a b, saddr_eqb a b = true -> a = b.
Proof.
intros [ab ak] [bb bk] H. unfold saddr_eqb in H. cbn [a_base a_off] in H.
apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2.
subst. reflexivity.
Qed.

#[using="Type"] Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma alu64_add_0_r : forall v : word, alu64 ALU_ADD v (Z_to_bv 64 0) = v.
Proof.
intro v. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

#[using="Type"] Lemma alu64_add_comm : forall a b : word, alu64 ALU_ADD a b = alu64 ALU_ADD b a.
Proof. intros. rewrite !alu_add. apply v_add_comm. Qed.

#[using="Type"] Lemma alu64_sub_as_add : forall (v : word) y,
alu64 ALU_SUB v (Z_to_bv 64 y) = alu64 ALU_ADD v (Z_to_bv 64 (- y)).
Proof.
intros v y. rewrite alu_sub, alu_add, v_sub_lit, v_add_lit. f_equal.
Qed.

Definition eqm (a b : Z) : Prop := exists q, (a = b + q * 2 ^ 64)%Z.

#[using="Type"] Lemma eqm_refl : forall a, eqm a a. Proof. intros; exists 0%Z; lia. Qed.
#[using="Type"] Lemma eqm_sym : forall a b, eqm a b -> eqm b a. Proof. intros a b [q H]; exists (-q)%Z; lia. Qed.
#[using="Type"] Lemma eqm_trans : forall a b c, eqm a b -> eqm b c -> eqm a c.
Proof. intros a b c [q H] [r H']; exists (q + r)%Z; lia. Qed.
#[using="Type"] Lemma eqm_add : forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof. intros a b c d [q H] [r H']; exists (q + r)%Z; lia. Qed.
#[using="Type"] Lemma eqm_mul_l : forall k a b, eqm a b -> eqm (k * a) (k * b).
Proof. intros k a b [q H]; exists (k * q)%Z. subst a. ring. Qed.
#[using="Type"] Lemma eqm_mul_r : forall k a b, eqm a b -> eqm (a * k) (b * k).
Proof. intros k a b [q H]; exists (q * k)%Z. subst a. ring. Qed.
#[using="Type"] Lemma eqm_mod : forall a, eqm (a mod 2 ^ 64) a.
Proof. intros a. exists (- (a / 2 ^ 64))%Z. pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). lia. Qed.
#[using="Type"] Lemma two64z_eq : two64z = (2 ^ 64)%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma eqm_snorm : forall k, eqm (snorm k) k.
Proof.
intros k. unfold snorm. rewrite two64z_eq. pose proof (Z.div_mod k (2 ^ 64) ltac:(lia)).
destruct (Z.leb (2 ^ 63) (k mod 2 ^ 64)).
- exists (- (k / 2 ^ 64) - 1)%Z. lia.
- exists (- (k / 2 ^ 64))%Z. lia.
Qed.
#[using="Type"] Lemma eqm_Z_to_bv : forall a b, eqm a b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
intros a b [q H]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. subst a. apply Z.mod_add. lia.
Qed.
#[using="Type"] Lemma u_lit64a : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod 2 ^ 64)%Z.
Proof. intros. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.
#[using="Type"] Lemma eqm_u_lit : forall z, eqm (bv_unsigned (Z_to_bv 64 z)) z.
Proof. intros. rewrite u_lit64a. apply eqm_mod. Qed.

Section LinDenot.
Variable E : env.
Definition uE (e : expr) : Z := bv_unsigned (edenot E e).

Fixpoint tden (ts : list (Z * expr)) : Z :=
match ts with [] => 0 | (k, a) :: rest => k * uE a + tden rest end.
Definition lden (x : lin) : Z := (fst x + tden (snd x))%Z.

#[using="Type"] Lemma lins_sound : forall k a ts, eqm (tden (lins k a ts)) (k * uE a + tden ts).
Proof.
intros k a ts. induction ts as [|[k' a'] rest IH]; cbn [lins tden].
- pose proof (eqm_snorm k) as [q Hq].
destruct (Z.eqb (snorm k) 0) eqn:Hz; cbn [tden].
+ apply Z.eqb_eq in Hz. exists (q * uE a)%Z. nia.
+ exists (q * uE a)%Z. nia.
- destruct (expr_eqb a a') eqn:Heq.
+ apply expr_eqb_eq in Heq. subst a'. pose proof (eqm_snorm (k + k')) as [q Hq].
destruct (Z.eqb (snorm (k + k')) 0) eqn:Hz.
* apply Z.eqb_eq in Hz. exists (q * uE a)%Z. nia.
* cbn [tden]. exists (q * uE a)%Z. nia.
+ pose proof (eqm_snorm k) as [q Hq].
destruct (expr_cmp a a'); cbn [tden].
* destruct IH as [r Hr]. exists r. lia.
* destruct (Z.eqb (snorm k) 0) eqn:Hz; cbn [tden].
-- apply Z.eqb_eq in Hz. exists (q * uE a)%Z. nia.
-- exists (q * uE a)%Z. nia.
* destruct IH as [r Hr]. exists r. lia.
Qed.

#[using="Type"] Lemma ladd_sound : forall x y, eqm (lden (ladd x y)) (lden x + lden y).
Proof.
intros [c ts] [d us]. unfold ladd, lden. cbn [fst snd].
assert (Hf : forall l acc, eqm (tden (fold_right (fun t acc => lins (fst t) (snd t) acc) acc l)) (tden l + tden acc)).
{ induction l as [|[k a] l IH]; intros acc; cbn [fold_right tden].
- exists 0%Z. lia.
- eapply eqm_trans; [apply lins_sound|]. cbn [fst snd].
destruct (IH acc) as [r Hr]. exists r. lia. }
pose proof (eqm_snorm (c + d)) as [q Hq]. destruct (Hf ts us) as [r Hr]. exists (q + r)%Z. lia.
Qed.

#[using="Type"] Lemma lscale_terms_sound : forall m ts, eqm (tden (lscale_terms m ts)) (m * tden ts).
Proof.
intros m ts. induction ts as [|[k a] rest IH]; cbn [lscale_terms tden].
- exists 0%Z. lia.
- pose proof (eqm_snorm (m * k)) as [q Hq]. destruct IH as [r Hr].
destruct (Z.eqb (snorm (m * k)) 0) eqn:Hz; cbn [tden].
+ apply Z.eqb_eq in Hz. exists (r + q * uE a)%Z. nia.
+ exists (r + q * uE a)%Z. nia.
Qed.

#[using="Type"] Lemma lscale_sound : forall m x, eqm (lden (lscale m x)) (m * lden x).
Proof.
intros m [c ts]. unfold lscale, lden. cbn [fst snd].
pose proof (eqm_snorm (m * c)) as [q Hq]. destruct (lscale_terms_sound m ts) as [r Hr].
exists (q + r)%Z. nia.
Qed.

#[using="Type"] Lemma u_add_eqm : forall x y : word, eqm (bv_unsigned (alu64 ALU_ADD x y)) (bv_unsigned x + bv_unsigned y).
Proof. intros. rewrite alu_add. unfold v_add. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_sub_eqm : forall x y : word, eqm (bv_unsigned (alu64 ALU_SUB x y)) (bv_unsigned x - bv_unsigned y).
Proof. intros. rewrite alu_sub. unfold v_sub. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_mul_eqm : forall x y : word, eqm (bv_unsigned (mul_div M_MUL x y)) (bv_unsigned x * bv_unsigned y).
Proof. intros. rewrite m_mul. unfold v_mul. apply eqm_u_lit. Qed.
#[using="Type"] Lemma u_sll_eqm : forall (x : word) s,
eqm (bv_unsigned (alu64 ALU_SLL x (Z_to_bv 64 s))) (2 ^ (s mod 64) * bv_unsigned x).
Proof.
intros. rewrite alu_sll. unfold v_sll. rewrite (u_lit64a s).
replace ((s mod 2 ^ 64) mod 64)%Z with (s mod 64)%Z by (symmetry; apply Z.mod_mod_divide; exists (2^58)%Z; reflexivity).
rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). rewrite Z.mul_comm. apply eqm_u_lit.
Qed.

#[using="Type"] Lemma lin_of_sound : forall e, eqm (lden (lin_of e)) (uE e).
Proof.
induction e; cbn [lin_of]; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
- unfold lden; cbn [fst snd tden]. pose proof (eqm_snorm z) as [q Hq]. unfold uE. cbn [edenot].
pose proof (eqm_u_lit z) as [r Hr]. exists (q - r)%Z. lia.
- destruct op; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
+ eapply eqm_trans; [apply ladd_sound|]. unfold uE. cbn [edenot].
eapply eqm_trans; [| apply eqm_sym; apply u_add_eqm]. apply eqm_add; assumption.
+ eapply eqm_trans; [apply ladd_sound|]. unfold uE. cbn [edenot].
eapply eqm_trans; [| apply eqm_sym; apply u_sub_eqm].
replace (bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2))%Z
with (bv_unsigned (edenot E e1) + (-1) * bv_unsigned (edenot E e2))%Z by lia.
apply eqm_add; [assumption|]. eapply eqm_trans; [apply lscale_sound|]. apply eqm_mul_l. assumption.
+ destruct e2; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
eapply eqm_trans; [apply lscale_sound|]. unfold uE. cbn [edenot].
eapply eqm_trans; [| apply eqm_sym; apply u_sll_eqm]. apply eqm_mul_l. assumption.
- destruct op; try (unfold lden; cbn [fst snd tden]; exists 0%Z; lia).
destruct e1;
[ eapply eqm_trans; [apply lscale_sound|]; unfold uE; cbn [edenot];
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]; cbn [edenot];
eapply eqm_trans; [apply eqm_mul_l; exact IHe2|]; apply eqm_mul_r; apply eqm_sym; apply eqm_u_lit | ..];
(destruct e2;
[ eapply eqm_trans; [apply lscale_sound|]; unfold uE; cbn [edenot];
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]; cbn [edenot]; rewrite Z.mul_comm;
eapply eqm_trans; [apply eqm_mul_r; exact IHe1|]; apply eqm_mul_l; apply eqm_sym; apply eqm_u_lit
| unfold lden; cbn [fst snd tden]; exists 0%Z; lia .. ]).
Qed.

#[using="Type"] Lemma lterm_sound : forall t, eqm (uE (lterm t)) (fst t * uE (snd t)).
Proof.
intros [k a]. unfold lterm. cbn [fst snd]. destruct (Z.eqb k 1) eqn:Hk.
- apply Z.eqb_eq in Hk. subst. exists 0%Z. lia.
- unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_mul_eqm|]. cbn [edenot].
apply eqm_mul_r. apply eqm_u_lit.
Qed.

#[using="Type"] Lemma lterms_sound : forall ts, eqm (uE (lterms ts)) (tden ts).
Proof.
induction ts as [|t rest IH]; cbn [lterms tden].
- unfold uE. cbn [edenot]. rewrite u_lit64a. exists 0%Z. reflexivity.
- destruct rest as [|t' rest'].
+ destruct t as [k a]. cbn [tden]. rewrite Z.add_0_r. apply lterm_sound.
+ destruct t as [k a]. unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_add_eqm|].
apply eqm_add; [apply (lterm_sound (k, a)) | exact IH].
Qed.

#[using="Type"] Lemma unlin_sound : forall x, eqm (uE (unlin x)) (lden x).
Proof.
intros [c ts]. unfold unlin, lden. cbn [fst snd].
destruct ts as [|t rest].
- cbn [tden]. unfold uE. cbn [edenot]. rewrite Z.add_0_r. apply eqm_u_lit.
- destruct (Z.eqb c 0) eqn:Hc.
+ apply Z.eqb_eq in Hc. subst c. rewrite Z.add_0_l. apply lterms_sound.
+ unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_add_eqm|]. rewrite Z.add_comm.
apply eqm_add; [cbn [edenot]; apply eqm_u_lit | apply lterms_sound].
Qed.

#[using="Type"] Lemma unlin_ladd : forall a b,
edenot E (unlin (ladd (lin_of a) (lin_of b))) = alu64 ALU_ADD (edenot E a) (edenot E b).
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply ladd_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_add_eqm]. apply eqm_add; apply lin_of_sound.
Qed.

#[using="Type"] Lemma unlin_lsub : forall a b,
edenot E (unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))) = alu64 ALU_SUB (edenot E a) (edenot E b).
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply ladd_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_sub_eqm].
replace (bv_unsigned (edenot E a) - bv_unsigned (edenot E b))%Z
with (bv_unsigned (edenot E a) + (-1) * bv_unsigned (edenot E b))%Z by lia.
apply eqm_add; [apply lin_of_sound|]. eapply eqm_trans; [apply lscale_sound|]. apply eqm_mul_l. apply lin_of_sound.
Qed.

#[using="Type"] Lemma unlin_lsll : forall a s,
edenot E (unlin (lscale (2 ^ (s mod 64)) (lin_of a))) = alu64 ALU_SLL (edenot E a) (Z_to_bv 64 s).
Proof.
intros a s. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (alu64 _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_sll_eqm]. apply eqm_mul_l. apply lin_of_sound.
Qed.

#[using="Type"] Lemma unlin_lmul_l : forall x b,
edenot E (unlin (lscale x (lin_of b))) = mul_div M_MUL (Z_to_bv 64 x) (edenot E b).
Proof.
intros x b. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (mul_div _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]. rewrite u_lit64a.
eapply eqm_trans; [apply eqm_mul_l; apply lin_of_sound|]. apply eqm_mul_r. apply eqm_sym. apply eqm_mod.
Qed.

#[using="Type"] Lemma unlin_lmul_r : forall a y,
edenot E (unlin (lscale y (lin_of a))) = mul_div M_MUL (edenot E a) (Z_to_bv 64 y).
Proof.
intros a y. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))), <- (Z_to_bv_bv_unsigned 64 (mul_div _ _ _)).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
eapply eqm_trans; [| apply eqm_sym; apply u_mul_eqm]. rewrite u_lit64a. rewrite (Z.mul_comm (bv_unsigned _)).
eapply eqm_trans; [apply eqm_mul_l; apply lin_of_sound|]. apply eqm_mul_r. apply eqm_sym. apply eqm_mod.
Qed.
End LinDenot.

#[using="Type"] Lemma coeffs_div_sound : forall E m ts, (0 < m)%Z -> coeffs_div m ts = true -> (tden E ts mod m = 0)%Z.
Proof.
intros E m ts Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_div tden]; intros H.
- apply Z.mod_0_l. lia.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. specialize (IH H2).
rewrite Z.add_mod, Z.mul_mod, H1, Z.mul_0_l, Z.mod_0_l, Z.add_0_l, IH by lia. apply Z.mod_0_l. lia.
Qed.

#[using="Type"] Lemma pow2_div_64 : forall k, (0 <= k <= 64)%Z -> (2 ^ k | 2 ^ 64)%Z.
Proof. intros k Hk. exists (2 ^ (64 - k))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

#[using="Type"] Lemma eqm_mod_pow2 : forall a b k, (0 <= k <= 64)%Z -> eqm a b -> (a mod 2 ^ k = b mod 2 ^ k)%Z.
Proof.
intros a b k Hk [q Hq]. subst a. destruct (pow2_div_64 k Hk) as [r Hr]. rewrite Hr.
replace (b + q * (r * 2 ^ k))%Z with (b + (q * r) * 2 ^ k)%Z by ring. apply Z.mod_add.
assert (0 < 2 ^ k)%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

#[using="Type"] Lemma lin_lowbits_sound : forall E e k v, (0 <= k <= 64)%Z ->
lin_lowbits e k = Some v -> (bv_unsigned (edenot E e) mod 2 ^ k = v)%Z /\ (0 <= v < 2 ^ k)%Z.
Proof.
intros E e k v Hk H. unfold lin_lowbits in H.
assert (Hp : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
destruct (lin_of e) as [c ts] eqn:Hl. cbn [fst snd] in H.
destruct (coeffs_div (2 ^ k) ts) eqn:Hd; [|discriminate]. injection H as <-.
pose proof (lin_of_sound E e) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs. unfold uE in Hs.
split; [|apply Z.mod_pos_bound; lia].
rewrite <- (eqm_mod_pow2 _ _ k Hk Hs). rewrite Z.add_mod, (coeffs_div_sound E _ ts Hp Hd), Z.add_0_r, Z.mod_mod by lia.
reflexivity.
Qed.

#[using="Type"] Lemma shamt_of_sound : forall E e bits s, (0 <= bits <= 64)%Z ->
shamt_of e bits = Some s -> (bv_unsigned (edenot E e) mod 2 ^ bits = s)%Z /\ (0 <= s < 2 ^ bits)%Z.
Proof.
intros E e bits s Hb H. assert (Hp : (0 < 2 ^ bits)%Z) by (apply Z.pow_pos_nonneg; lia).
unfold shamt_of in H. destruct e; try (apply lin_lowbits_sound; assumption).
injection H as <-. cbn [edenot]. rewrite u_lit64a. split; [|apply Z.mod_pos_bound; lia].
apply Z.mod_mod_divide. apply pow2_div_64. lia.
Qed.

#[using="Type"] Lemma alu_sll_amt : forall (x y : word) s, (bv_unsigned y mod 64 = s)%Z ->
alu64 ALU_SLL x y = Z_to_bv 64 (bv_unsigned x * 2 ^ s).
Proof.
intros x y s Hs. rewrite alu_sll. unfold v_sll.
pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as Hr. rewrite Hs in Hr. rewrite Hs.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

#[using="Type"] Lemma alu_srl_amt : forall (x y y' : word), (bv_unsigned y mod 64 = bv_unsigned y' mod 64)%Z ->
alu64 ALU_SRL x y = alu64 ALU_SRL x y'.
Proof. intros x y y' H. rewrite !alu_srl. unfold v_srl. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma alu_sra_amt : forall (x y y' : word), (bv_unsigned y mod 64 = bv_unsigned y' mod 64)%Z ->
alu64 ALU_SRA x y = alu64 ALU_SRA x y'.
Proof. intros x y y' H. rewrite !alu_sra. unfold v_sra. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma w_shift_amt : forall op (x y y' : word),
(op = ALU_SLL \/ op = ALU_SRL \/ op = ALU_SRA) ->
(bv_unsigned y mod 32 = bv_unsigned y' mod 32)%Z ->
(sext 64 (alu32 op (low32 x) (low32 y)) : word) = sext 64 (alu32 op (low32 x) (low32 y')).
Proof.
intros op x y y' Hop H. destruct Hop as [-> | [-> | ->]].
- rewrite !w_sllw. unfold v_sllw. rewrite H. reflexivity.
- rewrite !w_srlw. unfold v_srlw. rewrite H. reflexivity.
- rewrite !w_sraw. unfold v_sraw. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma u_lit_mod : forall s m, (0 <= s < 2 ^ 6)%Z -> (m = 64 \/ m = 32)%Z -> (s < m)%Z ->
(bv_unsigned (Z_to_bv 64 s) mod m = s)%Z.
Proof. intros s m Hs Hm Hsm. rewrite u_lit64a. rewrite (Z.mod_small s (2 ^ 64)) by lia. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma unlin_lsll_amt : forall E a (y : word) s, (bv_unsigned y mod 64 = s)%Z ->
edenot E (unlin (lscale (2 ^ s) (lin_of a))) = alu64 ALU_SLL (edenot E a) y.
Proof.
intros E a y s Hs. rewrite (alu_sll_amt _ _ s Hs).
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))).
apply eqm_Z_to_bv. eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
rewrite Z.mul_comm. apply eqm_mul_r. apply lin_of_sound.
Qed.

#[using="Type"] Lemma and_lowmask_val : forall (v : word) j, (0 <= j)%Z -> (j <= 64)%Z ->
alu64 ALU_AND v (Z_to_bv 64 (2 ^ j - 1)) = Z_to_bv 64 (bv_unsigned v mod 2 ^ j).
Proof.
intros v j Hj Hj64. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j <= 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite (Z.mod_small (2 ^ j - 1)) by lia.
replace (2 ^ j - 1)%Z with (Z.ones j) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. reflexivity.
Qed.

#[using="Type"] Lemma is_lit_some : forall e z, is_lit e = Some z -> e = ELit z.
Proof. intros e w H; destruct e; cbn in H; try discriminate. congruence. Qed.

#[using="Type"] Lemma mkAlu_denot : forall E op a b,
edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b).
Proof.
intros E op a b. unfold mkAlu.
assert (Hsll : edenot E (match shamt_of b 6 with
| Some s => unlin (lscale (2 ^ s) (lin_of a))
| None => EAlu ALU_SLL a b
end) = alu64 ALU_SLL (edenot E a) (edenot E b)).
{ destruct (shamt_of b 6) as [s|] eqn:Hs; [|reflexivity].
destruct (shamt_of_sound E b 6 s ltac:(lia) Hs) as [Hm Hr].
apply unlin_lsll_amt. change (2 ^ 6)%Z with 64%Z in Hm. exact Hm. }
assert (Hsr : forall op', (op' = ALU_SRL \/ op' = ALU_SRA) ->
edenot E (match is_lit b with
| Some _ => EAlu op' a b
| None => match shamt_of b 6 with
| Some s => EAlu op' a (ELit s)
| None => EAlu op' a b
end
end) = alu64 op' (edenot E a) (edenot E b)).
{ intros op' Hop. destruct (is_lit b); [reflexivity|]. destruct (shamt_of b 6) as [s|] eqn:Hs; [|reflexivity].
destruct (shamt_of_sound E b 6 s ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 6)%Z with 64%Z in Hm, Hr.
cbn [edenot].
destruct Hop as [-> | ->];
[ apply alu_srl_amt | apply alu_sra_amt ]; rewrite (u_lit_mod s 64) by lia; symmetry; exact Hm. }
destruct (is_lit a) as [x|] eqn:Ha.
- apply is_lit_some in Ha. subst a.
destruct (is_lit b) as [y|] eqn:Hb.
+ apply is_lit_some in Hb. subst b. cbn [edenot]. unfold zalu. apply Z_to_bv_bv_unsigned.
+ destruct op; try reflexivity.
* apply unlin_ladd.
* apply unlin_lsub.
* apply Hsll.
* apply Hsr. left; reflexivity.
* apply Hsr. right; reflexivity.
- destruct op; try (destruct (is_lit b); reflexivity).
+ destruct (is_lit b); apply unlin_ladd.
+ destruct (is_lit b); apply unlin_lsub.
+ destruct (is_lit b); apply Hsll.
+ destruct (is_lit b); apply Hsr; left; reflexivity.
+ destruct (is_lit b); apply Hsr; right; reflexivity.
Qed.

#[using="Type"] Lemma mkAluw_denot : forall E op a b,
edenot E (mkAluw op a b) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))).
Proof.
intros E op a b. unfold mkAluw.
assert (Hsh : (op = ALU_SLL \/ op = ALU_SRL \/ op = ALU_SRA) ->
edenot E (match is_lit b with
| Some _ => EAluw op a b
| None => match shamt_of b 5 with
| Some s => match is_lit a with
| Some x => ELit (zaluw op x s)
| None => EAluw op a (ELit s)
end
| None => EAluw op a b
end
end) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))).
{ intros Hop. destruct (is_lit b); [reflexivity|]. destruct (shamt_of b 5) as [s|] eqn:Hs; [|reflexivity].
destruct (shamt_of_sound E b 5 s ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 5)%Z with 32%Z in Hm, Hr.
assert (Heq : forall x : word, (sext 64 (alu32 op (low32 x) (low32 (Z_to_bv 64 s))) : word)
= sext 64 (alu32 op (low32 x) (low32 (edenot E b)))).
{ intros x. apply w_shift_amt; [exact Hop|]. rewrite (u_lit_mod s 32) by lia. symmetry. exact Hm. }
destruct (is_lit a) as [x|] eqn:Ha;
[ apply is_lit_some in Ha; subst a; cbn [edenot]; unfold zaluw; rewrite Z_to_bv_bv_unsigned; apply Heq
| cbn [edenot]; apply Heq ]. }
destruct (is_lit a) as [x|] eqn:Ha.
- destruct (is_lit b) as [y|] eqn:Hb.
+ apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zaluw.
apply Z_to_bv_bv_unsigned.
+ destruct op; try reflexivity; apply Hsh; tauto.
- destruct (is_lit b); (destruct op; try reflexivity; apply Hsh; tauto).
Qed.

#[using="Type"] Lemma mkMd_denot : forall E op a b,
edenot E (mkMd op a b) = mul_div op (edenot E a) (edenot E b).
Proof.
intros E op a b. unfold mkMd.
destruct (is_lit a) as [x|] eqn:Ha; [apply is_lit_some in Ha; subst a|];
(destruct (is_lit b) as [y|] eqn:Hb; [apply is_lit_some in Hb; subst b|]).
- cbn [edenot]. unfold zmd. apply Z_to_bv_bv_unsigned.
- destruct op; try reflexivity. cbn [edenot]. apply unlin_lmul_l.
- destruct op; try reflexivity. cbn [edenot]. apply unlin_lmul_r.
- reflexivity.
Qed.

#[using="Type"] Lemma mkMdw_denot : forall E op a b,
edenot E (mkMdw op a b) = sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b))).
Proof.
intros E op a b. unfold mkMdw.
destruct (is_lit a) as [x|] eqn:Ha; [|reflexivity].
destruct (is_lit b) as [y|] eqn:Hb; [|reflexivity].
apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zmdw.
apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma slice_mod : forall a m k j, (0 <= k)%Z -> (0 <= j)%Z -> (k + j <= m)%Z ->
(((a mod 2 ^ m) / 2 ^ k) mod 2 ^ j = (a / 2 ^ k) mod 2 ^ j)%Z.
Proof.
intros a m k j Hk Hj Hm. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia.
rewrite !Z.div_pow2_bits by lia.
rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma Z_to_bv64_swrap64 : forall u, Z_to_bv 64 (bv_swrap 64 u) = Z_to_bv 64 u.
Proof.
intro u. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_swrap.
unfold bv_wrap. change (bv_half_modulus 64) with (2^63)%Z.
change (bv_modulus 64) with (2^64)%Z.
rewrite <- Zminus_mod_idemp_l.
rewrite Z.mod_mod by lia.
rewrite Zminus_mod_idemp_l.
f_equal. lia.
Qed.

#[using="Type"] Lemma ext_val_full : forall sx (v : word), ext_val sx 0 8 v = v.
Proof.
intros sx v. unfold ext_val, ext_Z.
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
change (8 * Z.of_nat 8)%Z with 64%Z. change (8 * N.of_nat 8)%N with 64%N.
pose proof (bv_unsigned_in_range 64 v) as Hr. change (bv_modulus 64) with (2^64)%Z in Hr.
rewrite Z.mod_small by lia.
destruct sx; [rewrite Z_to_bv64_swrap64|]; apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma ext_Z_range : forall lo n z, (n <= 8)%nat ->
(0 <= ext_Z false lo n z < 2 ^ 64)%Z.
Proof.
intros lo n z Hn. unfold ext_Z.
pose proof (Z.mod_pos_bound (z / 2 ^ (8 * Z.of_nat lo)) (2 ^ (8 * Z.of_nat n)) ltac:(apply Z.pow_pos_nonneg; lia)) as H.
assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
lia.
Qed.

#[using="Type"] Lemma ext_val_compose : forall sx lo n lo' n' (v : word),
(lo + n <= n')%nat -> (n' <= 8)%nat ->
ext_val sx lo n (ext_val false lo' n' v) = ext_val sx (lo' + lo) n v.
Proof.
intros sx lo n lo' n' v Hle Hn'. unfold ext_val.
f_equal.
rewrite Z_to_bv_unsigned.
rewrite (bv_wrap_small 64) by
(pose proof (ext_Z_range lo' n' (bv_unsigned v) Hn'); change (bv_modulus 64) with (2^64)%Z; lia).
unfold ext_Z. cbv beta iota.
assert (Hs : (((bv_unsigned v / 2 ^ (8 * Z.of_nat lo')) mod 2 ^ (8 * Z.of_nat n') /
2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n) =
(bv_unsigned v / 2 ^ (8 * Z.of_nat (lo' + lo))) mod 2 ^ (8 * Z.of_nat n))%Z).
{ rewrite slice_mod by lia.
rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
rewrite <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia. }
rewrite Hs. reflexivity.
Qed.

#[using="Type"] Lemma mkExt_denot : forall E sx lo n e, (n <= 8)%nat ->
edenot E (mkExt sx lo n e) = ext_val sx lo n (edenot E e).
Proof.
intros E sx lo n e Hn. unfold mkExt.
destruct e as [x|v|op a b|op a b|op a b|op a b|sx' lo' n' e'|sx' k i n'].
1: { cbn [edenot]. unfold zext_lit. apply Z_to_bv_bv_unsigned. }
all: destruct (Nat.eqb lo 0 && Nat.eqb n 8)%bool eqn:Hfull;
[ apply andb_prop in Hfull as [H0 H8]; apply Nat.eqb_eq in H0; apply Nat.eqb_eq in H8;
subst; symmetry; apply ext_val_full
| ]; try reflexivity.
destruct sx'; [reflexivity|].
destruct (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool eqn:Hc; [|reflexivity].
apply andb_prop in Hc as [Hc1 Hc2]. apply Nat.leb_le in Hc1. apply Nat.leb_le in Hc2.
cbn [edenot]. symmetry. apply ext_val_compose; assumption.
Qed.

#[using="Type"] Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
intros r r' H. apply bv_eq. unfold ridx in H.
pose proof (u5_range r). pose proof (u5_range r'). lia.
Qed.

#[using="Type"] Lemma nth_sr_upd : forall n sr e i,
nth i (sr_upd sr n e) (ELit 0) = if Nat.eqb i n then e else nth i sr (ELit 0).
Proof.
induction n as [|n IH]; intros sr e i.
- destruct sr; destruct i; cbn; try reflexivity; destruct i; reflexivity.
- destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
+ rewrite IH. destruct (Nat.eqb i n); [reflexivity|]. destruct i; reflexivity.
+ apply IH.
Qed.

Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop :=
forall r : reg, getr regs r = edenot E (sr_get sr r).

#[using="Type"] Lemma regs_ok_upd : forall E sr regs rd v e,
regs_ok E sr regs -> edenot E e = v ->
regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
(if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
intros E sr regs rd v e Hr Hv.
destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
assert (Hne : rd <> 0).
{ intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
rewrite getr_same by exact Hne. exact (eq_sym Hv).
+ assert (Hrr : r <> rd).
{ intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
rewrite getr_other by exact Hrr.
specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

#[using="Type"] Lemma regs_ok_pin : forall E sr regs (r : reg) e,
regs_ok E sr regs -> getr regs r = edenot E e ->
regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_get.
destruct (bv_eqb r' 0) eqn:Hr0.
- assert (r' = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r'. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
+ specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

#[using="Type"] Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.

#[using="Type"] Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
pose proof (u5_range r). rewrite Z2Nat.id by lia.
apply bv_wrap_bv_unsigned.
Qed.

Definition reg_ev (regs : bvmap 5 word) (rest : nat -> word) : nat -> word :=
fun n => if Nat.ltb n 32 then getr regs (Z_to_bv 5 (Z.of_nat n)) else rest n.

#[using="Type"] Lemma regs_ok_id : forall regs rest ebs, regs_ok (Env (reg_ev regs rest) ebs) sr_id regs.
Proof.
intros regs rest ebs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r. unfold getr. rewrite Hr0. reflexivity.
- unfold reg_ev. cbn [ev]. rewrite <- (ridx_roundtrip r) at 1.
pose proof (ridx_range r) as Hlt.
set (n := ridx r) in *. clearbody n.
cbn [edenot ev].
do 32 (destruct n as [|n]; [reflexivity|]).
exfalso. lia.
Qed.

Fixpoint mem_denot (E : env) (base : word -> option byte) (log : list sentry)
: word -> option byte :=
match log with
| [] => base
| SE a w v :: rest =>
wbytes (mem_denot E base rest) (adenot E a) (word_to_le_bytes w (edenot E v))
end.

#[using="Type"] Lemma mem_denot_grows : forall E base log, mem_grows base (mem_denot E base log).
Proof.
intros E base log. induction log as [|[a w v] rest IH]; cbn [mem_denot].
- apply mem_grows_refl.
- eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

Definition estart (E : env) (a : saddr) : Z := (bv_unsigned (edenot E (a_base a)) + a_off a)%Z.
Definition elenZ (E : env) (n : expr) : Z := bv_unsigned (edenot E n).

Definition flat (E : env) (a : saddr) (n : Z) : Prop :=
(0 <= estart E a)%Z /\ (estart E a < 2^64)%Z /\ (0 <= n)%Z /\ (estart E a + n <= 2^64)%Z.

#[using="Type"] Lemma flat_u : forall E a n, flat E a n -> bv_unsigned (adenot E a) = estart E a.
Proof.
intros E a n (H1 & H2 & H3 & H4). unfold adenot, v_addi, estart in *.
rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma flat_mono : forall E a n m, flat E a n -> (0 <= m <= n)%Z -> flat E a m.
Proof. intros E a n m (H1 & H2 & H3 & H4) Hm. unfold flat. lia. Qed.

Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
match log with
| [] => True
| SE a w _ :: rest => (w <= 8)%nat /\ flat E a (Z.of_nat w) /\ log_flat E rest
end.

Definition extz (sx : bool) (n : nat) (u : Z) : Z :=
if sx then bv_swrap (8 * N.of_nat n) u else u.

Definition kentry_ok (segs : list Segment) (E : env) (base : word -> option byte) (K : kentry) : Prop :=
match K with
| KWord a w v =>
(w <= 8)%nat /\ flat E a (Z.of_nat w)
/\ rdn segs base (adenot E a) w = Some (word_to_le_bytes w (edenot E v))
| KZero a n =>
flat E a (elenZ E n)
/\ forall i, (0 <= i < elenZ E n)%Z -> base (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0)
| KBlob a n k =>
flat E a (elenZ E n)
/\ Z.of_nat (length (eb E k)) = elenZ E n
/\ forall i, (0 <= i < elenZ E n)%Z ->
base (Z_to_bv 64 (estart E a + i)) = Some (nth (Z.to_nat i) (eb E k) (Z_to_bv 8 0))
| KImg lo hi =>
(0 <= lo)%Z /\ (hi <= 2^64)%Z /\ forall i, (lo <= i < hi)%Z -> base (Z_to_bv 64 i) = None
| KAlign e m => (0 < m)%Z /\ (bv_unsigned (edenot E e) mod m = 0)%Z
| KRange e lo hi => (lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z
| KWr a n => flat E a n /\ forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z ->
RiscvSemantics.store_ok segs base (Z_to_bv 64 (estart E a + d)) m = true
| KDisj a1 n1 a2 n2 => (estart E a1 + n1 <= estart E a2)%Z \/ (estart E a2 + n2 <= estart E a1)%Z
end.

Definition know_ok (segs : list Segment) (E : env) (base : word -> option byte) (kn : list kentry) : Prop :=
Forall (kentry_ok segs E base) kn.

Definition sc_denot (segs : list Segment) (base : word -> option byte) (E : env) (s : sidecond) : Prop :=
match s with
| SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
| SCFlat a n => flat E a (elenZ E n)
| SCDisj a1 n1 a2 n2 =>
flat E a1 (elenZ E n1) /\ flat E a2 (elenZ E n2)
/\ ((estart E a1 + elenZ E n1 <= estart E a2)%Z \/ (estart E a2 + elenZ E n2 <= estart E a1)%Z)
| SCInside a1 n1 a2 n2 =>
flat E a2 (elenZ E n2) /\ (0 <= elenZ E n1)%Z
/\ (estart E a2 <= estart E a1)%Z /\ (estart E a1 + elenZ E n1 <= estart E a2 + elenZ E n2)%Z
| SCStoreOk a n => RiscvSemantics.store_ok segs base (adenot E a) n = true
| SCReadBase a n sx e =>
exists bs, rdn segs base (adenot E a) n = Some bs
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E e
| SCEq a b => edenot E a = edenot E b
end.

Definition scs_denot (segs : list Segment) (base : word -> option byte) (E : env) (l : list sidecond) : Prop :=
Forall (sc_denot segs base E) l.

#[using="Type"] Lemma w_add_nat : forall (a : word) (n : nat),
a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
intros a n. apply bv_eq. unfold nat_to_word.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. apply bv_wrap_add_idemp_r.
Qed.

#[using="Type"] Lemma w_add_1 : forall (a : word), a + 1 = Z_to_bv 64 (bv_unsigned a + 1).
Proof.
intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
change (bv_unsigned (1 : word)) with 1%Z. reflexivity.
Qed.

#[using="Type"] Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

#[using="Type"] Lemma elenZ_elen : forall E n, (n <= 8)%nat -> elenZ E (elen n) = Z.of_nat n.
Proof.
intros E n Hn. unfold elenZ, elen. cbn [edenot]. apply u_small. lia.
Qed.

#[using="Type"] Lemma rdn_skipn : forall segs mem n (a : word) bs k,
rdn segs mem a n = Some bs -> (k <= n)%nat ->
rdn segs mem (a + nat_to_word k) (n - k)%nat = Some (skipn k bs).
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
- assert (k = 0)%nat by lia. subst k. rewrite word_add_0. cbn in H |- *. exact H.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct k as [|k].
+ rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
+ cbn [skipn]. replace (S n - S k)%nat with (n - k)%nat by lia.
replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest k Er). lia.
Qed.

#[using="Type"] Lemma rdn_slice : forall segs mem n (a : word) bs d k,
rdn segs mem a n = Some bs -> (d + k <= n)%nat ->
rdn segs mem (a + nat_to_word d) k = Some (firstn k (skipn d bs)).
Proof.
intros segs mem n a bs d k H Hdk.
eapply rdn_firstn; [eapply rdn_skipn; [exact H | lia] | lia].
Qed.

#[using="Type"] Lemma skipn_Z_to_le_bytes : forall w d z, (d <= w)%nat ->
skipn d (Z_to_le_bytes w z) = Z_to_le_bytes (w - d) (z / 2 ^ (8 * Z.of_nat d)).
Proof.
induction w as [|w IH]; intros d z Hd.
- assert (d = 0)%nat by lia. subst. cbn. reflexivity.
- destruct d as [|d].
+ cbn [skipn Nat.sub]. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. reflexivity.
+ cbn [Z_to_le_bytes skipn Nat.sub]. rewrite IH by lia.
rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
rewrite <- Z.pow_add_r by lia.
replace (8 + 8 * Z.of_nat d)%Z with (8 * Z.of_nat (S d))%Z by lia. reflexivity.
Qed.

#[using="Type"] Lemma firstn_Z_to_le_bytes : forall m n z, (n <= m)%nat ->
firstn n (Z_to_le_bytes m z) = Z_to_le_bytes n z.
Proof.
induction m as [|m IH]; intros n z Hn.
- assert (n = 0)%nat by lia. subst. reflexivity.
- destruct n as [|n]; [reflexivity|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma slice_word_bytes : forall w d n (v : word), (d + n <= w)%nat ->
bytes_le_to_Z (firstn n (skipn d (word_to_le_bytes w v)))
= ((bv_unsigned v / 2 ^ (8 * Z.of_nat d)) mod 2 ^ (8 * Z.of_nat n))%Z.
Proof.
intros w d n v H. unfold word_to_le_bytes.
rewrite skipn_Z_to_le_bytes by lia. rewrite firstn_Z_to_le_bytes by lia.
apply bytes_le_Z_to_le. apply Z.div_pos; [apply u64_range | apply Z.pow_pos_nonneg; lia].
Qed.

#[using="Type"] Lemma length_firstn_skipn : forall {A} (l : list A) d n,
(d + n <= length l)%nat -> length (firstn n (skipn d l)) = n.
Proof. intros A l d n H. rewrite length_firstn, length_skipn. lia. Qed.

#[using="Type"] Lemma bytes_le_to_Z_bound : forall bs,
(0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length].
- change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. lia.
- pose proof (u8_range b) as Hb.
replace (8 * Z.of_nat (S (length bs)))%Z with (8 * Z.of_nat (length bs) + 8)%Z by lia.
rewrite Z.pow_add_r by lia.
assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)
= (bv_unsigned b + bytes_le_to_Z bs * 2 ^ 8)%Z).
{ rewrite Z.shiftl_mul_pow2 by lia.
rewrite <- Z.lxor_lor by
(apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8];
[ rewrite (Z.mul_pow2_bits_low) by lia; apply andb_false_r
| rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia; reflexivity ]).
rewrite Z.add_nocarry_lxor by
(apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8];
[ rewrite (Z.mul_pow2_bits_low) by lia; apply andb_false_r
| rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia; reflexivity ]).
reflexivity. }
rewrite Hlor. change (2^8)%Z with 256%Z. nia.
Qed.

#[using="Type"] Lemma Z_to_bv_u_plus0 : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intro a. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

#[using="Type"] Lemma rdn_pointwise : forall segs mem n (a : word) bs,
length bs = n ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
(forall j, (j < n)%nat ->
mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
rdn segs mem a n = Some bs.
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
- destruct bs; [reflexivity | cbn in Hlen; lia].
- destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
cbn [rdn].
pose proof (Hpt 0%nat ltac:(lia)) as H0. cbn [nth Z.of_nat] in H0.
rewrite Z_to_bv_u_plus0 in H0. rewrite H0.
destruct n as [|n'].
+ destruct bs'; [reflexivity | cbn in Hlen; lia].
+ assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) bs'); [reflexivity | lia | lia |].
intros j Hj. rewrite Hu1.
replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
rewrite (Hpt (S j)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rdn_img : forall segs mem n (a : word) zs,
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
(forall j, (j < n)%nat -> mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
img_bytes segs (bv_unsigned a) n = Some zs ->
exists bs, rdn segs mem a n = Some bs /\ map bv_unsigned bs = zs.
Proof.
intros segs mem n. induction n as [|n IH]; intros a zs Hnw Hpt Himg.
- cbn in Himg. injection Himg as <-. exists []. split; reflexivity.
- cbn [img_bytes] in Himg. rewrite Z_to_bv_bv_unsigned in Himg.
destruct (seg_rom segs a) as [b|] eqn:Hrom; [|discriminate].
destruct (img_bytes segs (bv_unsigned a + 1) n) as [zr|] eqn:Hrest; [|discriminate].
injection Himg as <-.
pose proof (Hpt 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z_to_bv_u_plus0 in H0.
cbn [rdn]. rewrite H0, Hrom.
destruct n as [|n'].
+ cbn in Hrest. injection Hrest as <-. cbn. exists [b]. split; reflexivity.
+ assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
destruct (IH (a + 1) zr) as (bs & Hbs & Hmap); [lia | | rewrite Hu1; exact Hrest |].
{ intros j Hj. rewrite Hu1.
replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
apply Hpt. lia. }
rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; rewrite Hmap; reflexivity].
Qed.

#[using="Type"] Lemma zbytes_map : forall bs, zbytes_le_to_Z (map bv_unsigned bs) = bytes_le_to_Z bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

#[using="Type"] Lemma bytes_le_to_Z_repeat0 : forall n, bytes_le_to_Z (repeat (Z_to_bv 8 0) n) = 0%Z.
Proof.
induction n as [|n IH]; cbn [repeat bytes_le_to_Z]; [reflexivity|].
rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma extz_0 : forall sx n, extz sx n 0 = 0%Z.
Proof.
intros sx n. unfold extz. destruct sx; [|reflexivity].
unfold bv_swrap, bv_wrap. rewrite Z.add_0_l.
rewrite Z.mod_small; [lia|].
unfold bv_half_modulus. split.
- apply Z.div_pos; [apply Z.lt_le_incl, bv_modulus_pos | lia].
- apply Z.div_lt_upper_bound; [lia|]. pose proof (bv_modulus_pos (8 * N.of_nat n)). lia.
Qed.

Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
match sz with
| SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
| SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
| SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
| SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
end.

Definition eff_sx (sz : msize) (sx : bool) : bool :=
match sz with SZ8 => false | _ => sx end.

#[using="Type"] Lemma step_load : forall segs regs pc mem rom w sz sx rd rs (imm : bv 12) bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma bv_extract0_lit : forall (m : N) (u : Z),
bv_extract 0 m (Z_to_bv 64 u) = Z_to_bv m u ->  True.
Proof. auto. Qed.

#[using="Type"] Lemma extract0_Z_to_bv64 : forall (m : N) (u : Z), (m <= 64)%N ->
bv_extract 0 m (Z_to_bv 64 u) = Z_to_bv m u.
Proof.
intros m u Hm. apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned.
rewrite Z.shiftr_0_r. unfold bv_wrap.
unfold bv_modulus.
rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
- reflexivity.
- exists (2 ^ (Z.of_N 64 - Z.of_N m))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma zext64_small : forall (m : N) (u : Z), (m <= 64)%N -> (0 <= u < 2 ^ Z.of_N m)%Z ->
zext 64 (Z_to_bv m u) = Z_to_bv 64 u.
Proof.
intros m u Hm Hu. rewrite zext64_lit. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. lia.
Qed.

#[using="Type"] Lemma sext64_small : forall (m : N) (u : Z), (m <= 64)%N -> (0 <= u < 2 ^ Z.of_N m)%Z ->
sext 64 (Z_to_bv m u) = Z_to_bv 64 (bv_swrap m u).
Proof.
intros m u Hm Hu. rewrite sext64_lit. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
rewrite bv_wrap_small; [reflexivity | unfold bv_modulus; lia].
Qed.

#[using="Type"] Lemma load_result_val : forall sz sx bs,
length bs = msize_bytes sz ->
load_result sz sx bs = Z_to_bv 64 (extz (eff_sx sz sx) (msize_bytes sz) (bytes_le_to_Z bs)).
Proof.
intros sz sx bs Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
unfold load_result, le_bytes_to_word, extz, eff_sx.
destruct sz; cbn [msize_bytes] in *.
- rewrite extract0_Z_to_bv64 by lia. destruct sx.
+ rewrite sext64_small by (cbn; lia). reflexivity.
+ rewrite zext64_small by (cbn; lia). reflexivity.
- rewrite extract0_Z_to_bv64 by lia. destruct sx.
+ rewrite sext64_small by (cbn; lia). reflexivity.
+ rewrite zext64_small by (cbn; lia). reflexivity.
- rewrite extract0_Z_to_bv64 by lia. destruct sx.
+ rewrite sext64_small by (cbn; lia). reflexivity.
+ rewrite zext64_small by (cbn; lia). reflexivity.
- rewrite extract0_Z_to_bv64 by lia. reflexivity.
Qed.

#[using="Type"] Lemma step_store : forall segs regs pc mem rom w sz (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w sz rs1 rs2 imm Hf He Hd Hok.
destruct sz; cbn [msize_bytes] in *.
- eapply step_sb; eassumption.
- eapply step_sh_val; eassumption.
- eapply Qrxj.step_sw_val; eassumption.
- eapply step_sd_val; eassumption.
Qed.

#[using="Type"] Lemma scs_denot_cons : forall segs base E s l,
scs_denot segs base E (s :: l) <-> sc_denot segs base E s /\ scs_denot segs base E l.
Proof.
intros. unfold scs_denot. split.
- intros H. inversion H; auto.
- intros [A B]. constructor; auto.
Qed.

#[using="Type"] Lemma scs_denot_app : forall segs base E l1 l2,
scs_denot segs base E (l1 ++ l2) <-> scs_denot segs base E l1 /\ scs_denot segs base E l2.
Proof. intros. unfold scs_denot. apply Forall_app. Qed.

#[using="Type"] Lemma log_lookup_acc : forall kn log rb rk n sx hints acc,
match log_lookup kn log rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof.
intros kn. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc; cbn [log_lookup].
- exists []. reflexivity.
- destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |].
+ exists []. reflexivity.
+ apply IH.
+ exact I.
+ destruct (ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH|].
destruct hints as [|[|] hs].
* specialize (IH rb rk n sx (tl (@nil bool)) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)).
destruct (log_lookup kn rest rb rk n sx (tl []) _) as [v0 scs h|scs h|]; try exact I;
destruct IH as [pre ->]; exists (pre ++ [SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w)]);
rewrite <- app_assoc; reflexivity.
* specialize (IH rb rk n sx (tl (true :: hs)) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)).
destruct (log_lookup kn rest rb rk n sx (tl (true :: hs)) _) as [v0 scs h|scs h|]; try exact I;
destruct IH as [pre ->]; exists (pre ++ [SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w)]);
rewrite <- app_assoc; reflexivity.
* exact I.
Qed.

#[using="Type"] Lemma find_range_sound : forall segs E M kn e lo hi,
know_ok segs E M kn -> find_range kn e = Some (lo, hi) ->
(lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z.
Proof.
intros segs E M kn e lo hi Hkn. induction kn as [|K rest IH]; cbn [find_range]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | |e' lo' hi'| |]; try (apply IH; assumption).
destruct (expr_eqb e e') eqn:Heq.
- injection H as <- <-. apply expr_eqb_eq in Heq. subst e'. exact HK.
- apply IH; assumption.
Qed.

#[using="Type"] Lemma u_lit64 : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod two64)%Z.
Proof. intros. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.

#[using="Type"] Lemma two64_eq : two64 = (2 ^ 64)%Z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma u_add64 : forall x y : word,
bv_unsigned (alu64 ALU_ADD x y) = ((bv_unsigned x + bv_unsigned y) mod 2 ^ 64)%Z.
Proof. intros. rewrite alu_add. unfold v_add. apply u_lit64. Qed.

#[using="Type"] Lemma u_sub64 : forall x y : word,
bv_unsigned (alu64 ALU_SUB x y) = ((bv_unsigned x - bv_unsigned y) mod 2 ^ 64)%Z.
Proof. intros. rewrite alu_sub. unfold v_sub. apply u_lit64. Qed.

#[using="Type"] Lemma u_and64 : forall x y : word,
bv_unsigned (alu64 ALU_AND x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof.
intros. rewrite alu_and. unfold v_and. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_land_range; lia.
Qed.

#[using="Type"] Lemma u_or64 : forall x y : word,
bv_unsigned (alu64 ALU_OR x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof.
intros. rewrite alu_or. unfold v_or. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_lor_range; lia.
Qed.

#[using="Type"] Lemma u_xor64 : forall x y : word,
bv_unsigned (alu64 ALU_XOR x y) = Z.lxor (bv_unsigned x) (bv_unsigned y).
Proof.
intros. rewrite alu_xor. unfold v_xor. rewrite u_lit64, two64_eq. apply Z.mod_small.
pose proof (u64_range x). pose proof (u64_range y). apply Z_lxor_range; lia.
Qed.

#[using="Type"] Lemma u_sltu64 : forall x y : word,
bv_unsigned (alu64 ALU_SLTU x y) = (if (bv_unsigned x <? bv_unsigned y)%Z then 1 else 0)%Z.
Proof.
intros. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu.
destruct (bv_unsigned x <? bv_unsigned y)%Z; reflexivity.
Qed.

#[using="Type"] Lemma u_slt64 : forall x y : word,
bv_unsigned (alu64 ALU_SLT x y) = (if (bv_signed x <? bv_signed y)%Z then 1 else 0)%Z.
Proof.
intros. rewrite alu_slt. unfold v_slt, c_lts, bv_lts.
destruct (bv_signed x <? bv_signed y)%Z; reflexivity.
Qed.

#[using="Type"] Lemma lit_shamt_sound : forall E b s, lit_shamt b = Some s ->
(bv_unsigned (edenot E b) mod 64 = s)%Z /\ (0 <= s < 64)%Z.
Proof.
intros E b s H. destruct b; cbn [lit_shamt] in H; try discriminate. injection H as <-.
cbn [edenot]. rewrite u_lit64, two64_eq. split; [|apply Z.mod_pos_bound; lia].
apply Z.mod_mod_divide. exists (2 ^ 58)%Z. reflexivity.
Qed.

#[using="Type"] Lemma u_srl64 : forall x y : word,
bv_unsigned (alu64 ALU_SRL x y) = (bv_unsigned x / 2 ^ (bv_unsigned y mod 64))%Z.
Proof.
intros. rewrite alu_srl. unfold v_srl. rewrite u_lit64, two64_eq, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (u64_range x). apply Z.mod_small.
assert (0 < 2 ^ (bv_unsigned y mod 64))%Z by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

#[using="Type"] Lemma u_sll64 : forall x y : word,
bv_unsigned (alu64 ALU_SLL x y) = ((bv_unsigned x * 2 ^ (bv_unsigned y mod 64)) mod 2 ^ 64)%Z.
Proof.
intros. rewrite alu_sll. unfold v_sll. rewrite u_lit64, two64_eq, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
reflexivity.
Qed.

#[using="Type"] Lemma u_sra64_nonneg : forall x y : word, (bv_unsigned x < 2 ^ 63)%Z ->
bv_unsigned (alu64 ALU_SRA x y) = (bv_unsigned x / 2 ^ (bv_unsigned y mod 64))%Z.
Proof.
intros x y Hx. rewrite alu_sra. unfold v_sra. rewrite bv_signed_small by exact Hx.
rewrite u_lit64, two64_eq, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
pose proof (u64_range x). apply Z.mod_small.
assert (0 < 2 ^ (bv_unsigned y mod 64))%Z by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

#[using="Type"] Lemma swrap32_small : forall t, (0 <= t < 2 ^ 31)%Z -> bv_swrap 32 t = t.
Proof.
intros t Ht. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.

#[using="Type"] Lemma swrap32_shift : forall t k, bv_swrap 32 (t + k * 2 ^ 32) = bv_swrap 32 t.
Proof.
intros t k. unfold bv_swrap. f_equal. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32)%Z.
replace (t + k * 2 ^ 32 + bv_half_modulus 32)%Z with (t + bv_half_modulus 32 + k * 2 ^ 32)%Z by lia.
apply Z.mod_add. lia.
Qed.

#[using="Type"] Lemma u_small_id : forall t, (0 <= t < 2 ^ 64)%Z -> (t mod two64 = t)%Z.
Proof. intros. rewrite two64_eq. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma u_addw_small : forall (x y : word) (t : Z),
(0 <= t < 2 ^ 31)%Z ->
(exists k, bv_unsigned x + bv_unsigned y = t + k * 2 ^ 32)%Z ->
bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) (low32 y)) : word) = t.
Proof.
intros x y t Ht [k Hk]. rewrite w_addw. unfold v_addw. rewrite u_lit64, Hk, swrap32_shift, swrap32_small by lia.
apply u_small_id. lia.
Qed.

#[using="Type"] Lemma u_subw_small : forall (x y : word) (t : Z),
(0 <= t < 2 ^ 31)%Z ->
(bv_unsigned x - bv_unsigned y = t)%Z ->
bv_unsigned (sext 64 (alu32 ALU_SUB (low32 x) (low32 y)) : word) = t.
Proof.
intros x y t Ht Hk. rewrite w_subw. unfold v_subw. rewrite u_lit64, Hk, swrap32_small by lia.
apply u_small_id. lia.
Qed.

#[using="Type"] Lemma mod32_of_mod64 : forall z, ((z mod 64) mod 32 = z mod 32)%Z.
Proof. intros. apply Z.mod_mod_divide. exists 2%Z. reflexivity. Qed.

#[using="Type"] Lemma u_sllw_small : forall (x y : word) s,
(bv_unsigned y mod 64 = s)%Z ->
(bv_unsigned x * 2 ^ (s mod 32) < 2 ^ 31)%Z ->
bv_unsigned (sext 64 (alu32 ALU_SLL (low32 x) (low32 y)) : word) = (bv_unsigned x * 2 ^ (s mod 32))%Z.
Proof.
intros x y s Hs Hb. rewrite w_sllw. unfold v_sllw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
assert (0 <= bv_unsigned x * 2 ^ (s mod 32))%Z by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.

#[using="Type"] Lemma u_srlw_small : forall (x y : word) s,
(bv_unsigned y mod 64 = s)%Z ->
(bv_unsigned x < 2 ^ 32)%Z ->
(bv_unsigned x / 2 ^ (s mod 32) < 2 ^ 31)%Z ->
bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) (low32 y)) : word) = (bv_unsigned x / 2 ^ (s mod 32))%Z.
Proof.
intros x y s Hs Hx Hb. rewrite w_srlw. unfold v_srlw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
rewrite bv_wrap32_mod, (Z.mod_small (bv_unsigned x)) by lia.
assert (0 <= bv_unsigned x / 2 ^ (s mod 32))%Z by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.

#[using="Type"] Lemma u_sraw_small : forall (x y : word) s,
(bv_unsigned y mod 64 = s)%Z ->
(bv_unsigned x < 2 ^ 31)%Z ->
bv_unsigned (sext 64 (alu32 ALU_SRA (low32 x) (low32 y)) : word) = (bv_unsigned x / 2 ^ (s mod 32))%Z.
Proof.
intros x y s Hs Hx. rewrite w_sraw. unfold v_sraw. pose proof (u64_range x).
assert (Hs' : (bv_unsigned y mod 32 = s mod 32)%Z) by (rewrite <- Hs; symmetry; apply mod32_of_mod64).
rewrite Hs', Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
rewrite (swrap32_small (bv_unsigned x)) by lia.
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
assert (0 <= bv_unsigned x / 2 ^ (s mod 32))%Z by (apply Z.div_pos; lia).
assert (bv_unsigned x / 2 ^ (s mod 32) <= bv_unsigned x)%Z by (apply Z.div_le_upper_bound; [lia|nia]).
rewrite u_lit64, swrap32_small by lia. apply u_small_id. lia.
Qed.

#[using="Type"] Lemma u_mul64 : forall x y : word,
bv_unsigned (mul_div M_MUL x y) = ((bv_unsigned x * bv_unsigned y) mod 2 ^ 64)%Z.
Proof. intros. rewrite m_mul. unfold v_mul. apply u_lit64. Qed.

#[using="Type"] Lemma u_mulhu64 : forall x y : word,
bv_unsigned (mul_div M_MULHU x y) = (bv_unsigned x * bv_unsigned y / 2 ^ 64)%Z.
Proof.
intros. rewrite m_mulhu. unfold v_mulhu. rewrite u_lit64, Z.shiftr_div_pow2 by lia.
pose proof (u64_range x). pose proof (u64_range y). apply u_small_id.
split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

#[using="Type"] Lemma u_divu64 : forall x y : word, (0 < bv_unsigned y)%Z ->
bv_unsigned (mul_div M_DIVU x y) = (bv_unsigned x / bv_unsigned y)%Z.
Proof.
intros x y Hy. unfold mul_div. replace (bv_unsigned y =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_divu_unsigned.
Qed.

#[using="Type"] Lemma u_remu64 : forall x y : word, (0 < bv_unsigned y)%Z ->
bv_unsigned (mul_div M_REMU x y) = (bv_unsigned x mod bv_unsigned y)%Z.
Proof.
intros x y Hy. unfold mul_div. replace (bv_unsigned y =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_modu_unsigned.
Qed.

#[using="Type"] Lemma u_ext_zx : forall lo n (v : word),
bv_unsigned (ext_val false lo n v) = ((bv_unsigned v / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n))%Z
/\ (bv_unsigned (ext_val false lo n v) <= 2 ^ (8 * Z.of_nat n) - 1)%Z
/\ (bv_unsigned (ext_val false lo n v) <= two64 - 1)%Z.
Proof.
intros lo n v. unfold ext_val, ext_Z. pose proof (u64_range v) as Hv.
set (q := (bv_unsigned v / 2 ^ (8 * Z.of_nat lo))%Z).
assert (Hw : (0 < 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.mod_pos_bound q _ Hw) as Hm.
assert (Hq : (0 <= q)%Z) by (subst q; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
assert (Hle : (q mod 2 ^ (8 * Z.of_nat n) <= bv_unsigned v)%Z).
{ apply Z.le_trans with q; [apply Z.mod_le; lia|]. subst q. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
rewrite <- (Z.mul_1_l (bv_unsigned v)) at 1. apply Z.mul_le_mono_nonneg_r; [lia|].
assert (0 < 2 ^ (8 * Z.of_nat lo))%Z by (apply Z.pow_pos_nonneg; lia). lia. }
rewrite u_lit64. rewrite u_small_id by lia. rewrite two64_eq. lia.
Qed.

#[using="Type"] Lemma u_ext_zx0_small : forall n (v : word),
(bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> bv_unsigned (ext_val false 0 n v) = bv_unsigned v.
Proof.
intros n v Hv. destruct (u_ext_zx 0 n v) as (H & _ & _). rewrite H.
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

#[using="Type"] Lemma u_ext_sx0_small : forall n (v : word),
(bv_unsigned v < 2 ^ (8 * Z.of_nat n) / 2)%Z -> bv_unsigned (ext_val true 0 n v) = bv_unsigned v.
Proof.
intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
assert (Hw : (0 < 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hhalf : (2 ^ (8 * Z.of_nat n) / 2 <= 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.div_le_upper_bound; lia).
rewrite (Z.mod_small (bv_unsigned v)) by lia.
rewrite bv_swrap_small.
- rewrite u_lit64. apply u_small_id. lia.
- unfold bv_half_modulus, bv_modulus. replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia. lia.
Qed.

#[using="Type"] Lemma u_blob_zx : forall bs i n,
(bv_unsigned (blob_val false bs i n) <= 2 ^ (8 * Z.of_nat n) - 1)%Z
/\ (bv_unsigned (blob_val false bs i n) <= two64 - 1)%Z.
Proof.
intros bs i n. unfold blob_val. pose proof (bytes_le_to_Z_bound (blob_bytes bs i n)) as Hb.
assert (Hlen : (length (blob_bytes bs i n) <= n)%nat) by (unfold blob_bytes; rewrite firstn_length; apply Nat.le_min_l).
assert (Hp : (2 ^ (8 * Z.of_nat (length (blob_bytes bs i n))) <= 2 ^ (8 * Z.of_nat n))%Z) by (apply Z.pow_le_mono_r; lia).
rewrite u_lit64. pose proof (Z.mod_pos_bound (bytes_le_to_Z (blob_bytes bs i n)) two64 ltac:(rewrite two64_eq; lia)).
pose proof (Z.mod_le (bytes_le_to_Z (blob_bytes bs i n)) two64 ltac:(lia) ltac:(rewrite two64_eq; lia)). lia.
Qed.

#[using="Type"] Lemma clampi_sound : forall (v : word) lo hi lo' hi',
(lo <= bv_unsigned v <= hi)%Z -> clampi (lo, hi) = (lo', hi') -> (lo' <= bv_unsigned v <= hi')%Z.
Proof.
intros v lo hi lo' hi' H Hc. unfold clampi in Hc. injection Hc as <- <-. pose proof (u64_range v). rewrite two64_eq. lia.
Qed.
#[using="Type"] Lemma mod_wrap_hi : forall t, (2 ^ 64 <= t < 2 ^ 64 + 2 ^ 64)%Z -> (t mod 2 ^ 64 = t - 2 ^ 64)%Z.
Proof. intros t Ht. symmetry. apply (Z.mod_unique_pos t (2 ^ 64) 1); lia. Qed.
#[using="Type"] Lemma mod_wrap_neg : forall t, (- 2 ^ 64 <= t < 0)%Z -> (t mod 2 ^ 64 = t + 2 ^ 64)%Z.
Proof. intros t Ht. symmetry. apply (Z.mod_unique_pos t (2 ^ 64) (-1)); lia. Qed.
#[using="Type"] Lemma mask_cover_sound : forall h x, (0 <= x <= h)%Z -> (x <= mask_cover h)%Z.
Proof.
intros h x Hx. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eq_dec h 0) as [->|Hne].
- replace (2 ^ Z.log2_up (0 + 1) - 1)%Z with 0%Z by reflexivity. lia.
- pose proof (Z.log2_up_spec (h + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma pow_cover : forall h, (0 <= h)%Z -> (h + 1 <= 2 ^ Z.log2_up (h + 1))%Z /\ (0 <= Z.log2_up (h + 1))%Z.
Proof.
intros h Hh. split; [|apply Z.log2_up_nonneg].
destruct (Z.eq_dec h 0) as [->|Hne].
- replace (2 ^ Z.log2_up (0 + 1))%Z with 1%Z by reflexivity. lia.
- pose proof (Z.log2_up_spec (h + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma lor_cover : forall h x y, (0 <= x <= h)%Z -> (0 <= y <= h)%Z -> (Z.lor x y <= mask_cover h)%Z.
Proof.
intros h x y Hx Hy. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (pow_cover h ltac:(lia)) as [Hh Hk]. set (k := Z.log2_up (h + 1)) in *.
enough (Z.lor x y < 2 ^ k)%Z by lia.
apply (Z_bounded_by_bits k); [lia | apply Z.lor_nonneg; lia |].
intros i Hi. rewrite Z.lor_spec.
rewrite (Z_testbit_high k x i) by lia. rewrite (Z_testbit_high k y i) by lia. reflexivity.
Qed.
#[using="Type"] Lemma lxor_cover : forall h x y, (0 <= x <= h)%Z -> (0 <= y <= h)%Z -> (0 <= Z.lxor x y <= mask_cover h)%Z.
Proof.
intros h x y Hx Hy. unfold mask_cover. replace (h <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
destruct (pow_cover h ltac:(lia)) as [Hh Hk]. set (k := Z.log2_up (h + 1)) in *.
assert (Hnn : (0 <= Z.lxor x y)%Z) by (apply Z.lxor_nonneg; lia).
enough (Z.lxor x y < 2 ^ k)%Z by lia.
apply (Z_bounded_by_bits k); [lia | exact Hnn |].
intros i Hi. rewrite Z.lxor_spec.
rewrite (Z_testbit_high k x i) by lia. rewrite (Z_testbit_high k y i) by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_le_l : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.land a b <= a)%Z.
Proof.
intros a b Ha Hb.
pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as Hal.
rewrite Z.lor_ldiff_and in Hal.
assert (Hand : Z.land (Z.ldiff a b) (Z.land a b) = 0%Z).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite Hand in Hal.
assert (0 <= Z.ldiff a b)%Z by (apply Z.ldiff_nonneg; lia). lia.
Qed.
#[using="Type"] Lemma land_le_r : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.land a b <= b)%Z.
Proof. intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.
#[using="Type"] Lemma lor_ge_l : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (x <= Z.lor x y)%Z.
Proof. intros. pose proof (Z.add_lor_land x y). pose proof (land_le_r x y H H0). lia. Qed.
#[using="Type"] Lemma lor_ge_r : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (y <= Z.lor x y)%Z.
Proof. intros. rewrite Z.lor_comm. apply lor_ge_l; assumption. Qed.
End FPGEN1.

Ltac fr_case Hkn H :=
lazymatch type of H with
| match find_range ?kn ?e with _ => _ end = _ =>
destruct (find_range kn e) as [[flo fhi]|] eqn:Hfr;
[ pose proof (find_range_sound _ _ _ _ _ _ _ Hkn Hfr) as Hb; unfold clampi in H;
injection H as <- <-; lazymatch goal with |- context [bv_unsigned ?v] => pose proof (u64_range v) end; unfold two64 in *; lia
| clear Hfr ]
end.

Ltac er_both IHe1 IHe2 Hkn H :=
destruct (erange _ _) as [[al ah]|] eqn:He1 in H; [|try discriminate];
destruct (erange _ _) as [[bl bh]|] eqn:He2 in H; [|try discriminate];
try (specialize (IHe1 al ah Hkn eq_refl)); try (specialize (IHe2 bl bh Hkn eq_refl)).
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma lin_range_sound : forall E rng,
(forall a lo hi, rng a = Some (lo, hi) -> (lo <= bv_unsigned (edenot E a) <= hi)%Z) ->
forall c ts lo hi, lin_range rng c ts = Some (lo, hi) -> (lo <= c + tden E ts <= hi)%Z.
Proof.
intros E rng Hrng c ts. induction ts as [|[k a] rest IHts]; intros lo hi H; cbn [lin_range tden] in H |- *.
- injection H as <- <-. lia.
- destruct (rng a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (lin_range rng c rest) as [[lo' hi']|] eqn:Hr; [|discriminate].
pose proof (Hrng a al ah Ha) as Hb. pose proof (IHts lo' hi' eq_refl) as Hrest. unfold uE.
destruct (Z.leb 0 k) eqn:Hk; injection H as <- <-.
+ apply Z.leb_le in Hk. nia.
+ apply Z.leb_gt in Hk. nia.
Qed.

#[using="Type"] Lemma erange_f_sound : forall segs E M kn fuel e rlo rhi,
know_ok segs E M kn -> erange_f fuel kn e = Some (rlo, rhi) ->
(rlo <= bv_unsigned (edenot E e) <= rhi)%Z.
Proof.
intros segs E M kn fuel. induction fuel as [|fuel IH]; intros e rlo rhi Hkn H; [discriminate|].
cbn [erange_f] in H. fr_case Hkn H.

lazymatch type of H with
| match ?X with _ => _ end = _ =>
destruct X as [[llo lhi]|] eqn:Hlin;
[ injection H as <- <-;
destruct (lin_trivial (lin_of e)) eqn:Htriv; [discriminate|];
destruct (lin_range (erange_f fuel kn) (fst (lin_of e)) (snd (lin_of e))) as [[lo1 hi1]|] eqn:Hlr; [|discriminate];
destruct (Z.leb 0 lo1 && Z.ltb hi1 two64)%bool eqn:Hc; [|discriminate];
injection Hlin as <- <-; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2;
unfold two64 in Hc2;
pose proof (lin_range_sound E (erange_f fuel kn) (fun a lo hi Ha => IH a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb;
pose proof (lin_of_sound E e) as [q Hq]; unfold lden in Hq;
destruct (lin_of e) as [c ts]; cbn [fst snd] in *; unfold uE in Hq;
pose proof (u64_range (edenot E e)); nia
| clear Hlin ]
end.
pose proof (fun a => IH a) as IHe1. pose proof (fun a => IH a) as IHe2. pose proof (fun a => IH a) as IHe.
destruct e; cbn [edenot]; unfold two64 in *.
-  injection H as <- <-. rewrite u_lit64. unfold two64. lia.
-  discriminate.
-
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op.
+  rewrite u_add64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
destruct (ah + bh <? 2 ^ 64)%Z eqn:C1.
* injection H as <- <-. rewrite Z.mod_small by lia. lia.
* destruct (2 ^ 64 <=? al + bl)%Z eqn:C2; [|discriminate]. injection H as <- <-.
rewrite mod_wrap_hi by lia. lia.
+  rewrite u_sub64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
destruct (bh <=? al)%Z eqn:C1.
* injection H as <- <-. rewrite Z.mod_small by lia. lia.
* destruct (ah <? bl)%Z eqn:C2; [|discriminate]. injection H as <- <-.
rewrite mod_wrap_neg by lia. lia.
+  rewrite u_sll64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr]. rewrite Hsv.
destruct (ah * 2 ^ s <? 2 ^ 64)%Z eqn:C1; [|discriminate]. injection H as <- <-.
assert (Hp : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
rewrite Z.mod_small by nia. nia.
+  rewrite u_slt64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1;
[destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2|];
[ specialize (IHe1 e1 al ah Hkn He1); specialize (IHe2 e2 bl bh Hkn He2)
| injection H as <- <-; destruct (bv_signed (edenot E e1) <? bv_signed (edenot E e2))%Z; lia
| injection H as <- <-; destruct (bv_signed (edenot E e1) <? bv_signed (edenot E e2))%Z; lia ].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C0 end.
* apply andb_prop in C0 as [Ca Cb].
rewrite (bv_signed_small (edenot E e1)) by lia. rewrite (bv_signed_small (edenot E e2)) by lia.
set (x := bv_unsigned (edenot E e1)) in *. set (y := bv_unsigned (edenot E e2)) in *.
destruct (ah <? bl)%Z eqn:C1; [injection H as <- <-; destruct (x <? y)%Z eqn:C; lia|].
destruct (bh <=? al)%Z eqn:C2; injection H as <- <-; destruct (x <? y)%Z eqn:C; lia.
* injection H as <- <-. destruct (bv_signed (edenot E e1) <? bv_signed (edenot E e2))%Z; lia.
+  rewrite u_sltu64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1;
[destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2|];
[ specialize (IHe1 e1 al ah Hkn He1); specialize (IHe2 e2 bl bh Hkn He2)
| injection H as <- <-; destruct (bv_unsigned (edenot E e1) <? bv_unsigned (edenot E e2))%Z; lia
| injection H as <- <-; destruct (bv_unsigned (edenot E e1) <? bv_unsigned (edenot E e2))%Z; lia ].
set (x := bv_unsigned (edenot E e1)) in *. set (y := bv_unsigned (edenot E e2)) in *.
destruct (ah <? bl)%Z eqn:C1; [injection H as <- <-; destruct (x <? y)%Z eqn:C; lia|].
destruct (bh <=? al)%Z eqn:C2; injection H as <- <-; destruct (x <? y)%Z eqn:C; lia.
+  rewrite u_xor64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
injection H as <- <-. apply lxor_cover; lia.
+  rewrite u_srl64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr]. rewrite Hsv.
injection H as <- <-.
assert (Hp : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
split; apply Z.div_le_mono; lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
destruct (ah <? 2 ^ 63)%Z eqn:C1; [|discriminate]. injection H as <- <-.
rewrite u_sra64_nonneg by lia. rewrite Hsv.
assert (Hp : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
split; apply Z.div_le_mono; lia.
+  rewrite u_or64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
injection H as <- <-. split.
* apply Z.max_lub; [eapply Z.le_trans; [|apply lor_ge_l; lia] | eapply Z.le_trans; [|apply lor_ge_r; lia]]; lia.
* apply lor_cover; lia.
+  rewrite u_and64.
pose proof (Z.land_nonneg (bv_unsigned (edenot E e1)) (bv_unsigned (edenot E e2))) as Hnn.
pose proof (land_le_l _ _ (proj1 R1) (proj1 R2)) as Hl1.
pose proof (land_le_r _ _ (proj1 R1) (proj1 R2)) as Hl2.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1;
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; try discriminate;
try specialize (IHe1 e1 al ah Hkn He1); try specialize (IHe2 e2 bl bh Hkn He2);
injection H as <- <-; lia.
-
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op; try discriminate.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
revert H. unfold zsigned64, two64.
destruct (bl =? bh)%Z eqn:Ceq;
[destruct (2 ^ 63 <=? bl)%Z eqn:Chi; destruct (2 ^ 63 <=? bh)%Z eqn:Chi2|]; intros H;
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end;
injection H as <- <-; apply andb_prop in C1 as [Ca Cb];
first
[ rewrite (u_addw_small _ _ (bv_unsigned (edenot E e1) + (bv_unsigned (edenot E e2) - 2 ^ 64))%Z);
[lia | lia | exists (2 ^ 32)%Z; lia]
| rewrite (u_addw_small _ _ (bv_unsigned (edenot E e1) + bv_unsigned (edenot E e2))%Z);
[lia | lia | exists 0%Z; lia]
| exfalso; lia ].
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
rewrite (u_subw_small _ _ (bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2))%Z); lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-.
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
rewrite (u_sllw_small _ _ s Hsv) by nia. nia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
assert (Hsm : (bv_unsigned (edenot E e1) / 2 ^ (s mod 32) < 2 ^ 31)%Z).
{ apply orb_prop in Cb as [Cb|Cb].
- apply Z.div_lt_upper_bound; [lia|].
assert (2 <= 2 ^ (s mod 32))%Z.
{ replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
nia.
- apply Z.le_lt_trans with (bv_unsigned (edenot E e1)); [|lia].
apply Z.div_le_upper_bound; [lia|]. nia. }
rewrite (u_srlw_small _ _ s Hsv) by lia.
split; apply Z.div_le_mono; lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (lit_shamt e2) as [s|] eqn:Hs; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-.
assert (Hp : (0 < 2 ^ (s mod 32))%Z) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
rewrite (u_sraw_small _ _ s Hsv) by lia.
split; apply Z.div_le_mono; lia.
-
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op; try discriminate.
+  rewrite u_mul64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [C1 Cc]. apply andb_prop in C1 as [Ca Cb].
assert (bv_unsigned (edenot E e1) * bv_unsigned (edenot E e2) <= ah * bh)%Z by nia.
rewrite Z.mod_small by nia. nia.
+  rewrite u_mulhu64.
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
destruct (erange_f fuel kn e2) as [[bl bh]|] eqn:He2; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1). specialize (IHe2 e2 bl bh Hkn He2).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
split; apply Z.div_le_mono; nia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct e2; try discriminate. cbn [edenot] in *.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. rewrite u_lit64 in *. unfold two64 in *.
rewrite u_divu64 by (rewrite u_lit64; unfold two64; lia). rewrite u_lit64. unfold two64.
split; apply Z.div_le_mono; lia.
+
destruct (erange_f fuel kn e1) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe1 e1 al ah Hkn He1).
destruct e2; try discriminate. cbn [edenot] in *.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-.
rewrite u_remu64 by (rewrite u_lit64; unfold two64; lia). rewrite u_lit64. unfold two64.
pose proof (Z.mod_pos_bound (bv_unsigned (edenot E e1)) (z mod 2 ^ 64) ltac:(lia)).
pose proof (Z.mod_le (bv_unsigned (edenot E e1)) (z mod 2 ^ 64) ltac:(lia) ltac:(lia)). lia.
-  discriminate.
-
pose proof (u64_range (edenot E e)) as R1.
destruct sx.
+ destruct lo; [|discriminate].
destruct (erange_f fuel kn e) as [[al ah]|] eqn:He1; [|discriminate].
specialize (IHe e al ah Hkn He1).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
injection H as <- <-. apply andb_prop in C1 as [Ca Cb].
rewrite u_ext_sx0_small by lia. lia.
+ destruct (u_ext_zx lo n (edenot E e)) as (_ & Hb1 & Hb2). unfold two64 in Hb2.
pose proof (u64_range (ext_val false lo n (edenot E e))) as R0.
destruct lo.
* destruct (erange_f fuel kn e) as [[al ah]|] eqn:He1.
-- specialize (IHe e al ah Hkn He1).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
++ injection H as <- <-. apply andb_prop in C1 as [Ca Cb]. rewrite u_ext_zx0_small by lia. lia.
++ injection H as <- <-. lia.
-- injection H as <- <-. lia.
* injection H as <- <-. lia.
-
destruct sx; [discriminate|]. injection H as <- <-.
destruct (u_blob_zx (eb E k) i n) as [Hb1 Hb2]. unfold two64 in Hb2.
pose proof (u64_range (blob_val false (eb E k) i n)). lia.
Qed.

#[using="Type"] Lemma erange_sound : forall segs E M kn e rlo rhi,
know_ok segs E M kn -> erange kn e = Some (rlo, rhi) ->
(rlo <= bv_unsigned (edenot E e) <= rhi)%Z.
Proof. intros. eapply erange_f_sound; eassumption. Qed.

#[using="Type"] Lemma base_range_sound : forall segs E M kn e lo hi,
know_ok segs E M kn -> base_range kn e = Some (lo, hi) ->
(lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z.
Proof.
intros segs E M kn e lo hi Hkn H. unfold base_range in H.
exact (erange_sound segs E M kn e lo hi Hkn H).
Qed.

#[using="Type"] Lemma sub_itv_sound : forall E b k n c m,
sub_itv b k n c m = true ->
(estart E c <= estart E (SA b k))%Z /\ (estart E (SA b k) + n <= estart E c + m)%Z.
Proof.
intros E b k n [cb ck] m H. unfold sub_itv in H. cbn [a_base a_off] in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply expr_eqb_eq in H1. subst cb. apply Z.leb_le in H2. apply Z.leb_le in H3.
unfold estart. cbn [a_base a_off]. lia.
Qed.

#[using="Type"] Lemma kdisj_apart_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
know_ok segs E M kn -> kdisj_apart kn b1 k1 n1 b2 k2 n2 = true ->
((estart E (SA b1 k1) + n1 <= estart E (SA b2 k2))%Z
\/ (estart E (SA b2 k2) + n2 <= estart E (SA b1 k1))%Z).
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn. induction kn as [|K rest IH]; cbn [kdisj_apart]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | | | | |c1 m1 c2 m2]; try (apply IH; assumption).
apply orb_prop in H as [H|H]; [|apply IH; assumption].
cbn [kentry_ok] in HK.
apply orb_prop in H as [H|H]; apply andb_prop in H as [Ha Hb];
apply (sub_itv_sound E) in Ha as [Ha1 Ha2]; apply (sub_itv_sound E) in Hb as [Hb1 Hb2]; lia.
Qed.

#[using="Type"] Lemma ranges_apart_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
know_ok segs E M kn -> ranges_apart kn b1 k1 n1 b2 k2 n2 = true ->
((estart E (SA b1 k1) + n1 <= estart E (SA b2 k2))%Z
\/ (estart E (SA b2 k2) + n2 <= estart E (SA b1 k1))%Z).
Proof.
intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold ranges_apart in H.
apply orb_prop in H as [H|H]; [|eapply kdisj_apart_sound; eassumption].
destruct (base_range kn b1) as [[lo1 hi1]|] eqn:H1; [|discriminate].
destruct (base_range kn b2) as [[lo2 hi2]|] eqn:H2; [|discriminate].
pose proof (base_range_sound segs E M kn b1 lo1 hi1 Hkn H1) as [A1 B1].
pose proof (base_range_sound segs E M kn b2 lo2 hi2 Hkn H2) as [A2 B2].
unfold estart. cbn [a_base a_off].
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

#[using="Type"] Lemma know_lookup_acc : forall segs kn rb rk n sx hints acc,
match know_lookup segs kn rb rk n sx hints acc with
| LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
| LStuck => True
end.
Proof.
induction kn as [|K rest IH]; intros rb rk n sx hints acc; cbn [know_lookup].
- exists []. reflexivity.
- assert (Hnil : exists pre : list sidecond, acc = pre ++ acc) by (exists []; reflexivity).
assert (Hone : forall s, exists pre : list sidecond, s :: acc = pre ++ acc)
by (intros s; exists [s]; reflexivity).
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2]; [ | | | | apply IH | apply IH | apply IH | apply IH].
+ destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); first [exact I | apply IH | apply Hnil | apply Hone].
+ destruct len; first [ destruct (rel_lit rb rk (Z.of_nat n) kb kk (z mod 2^64)%Z); first [exact I | apply IH | apply Hnil | apply Hone | destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone]]
| destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ].
+ destruct (expr_eqb rb kb); [|apply IH].
destruct (Z.leb kk rk); [|apply IH].
destruct len; first [ destruct (Z.leb (rk + Z.of_nat n) (kk + (z mod 2^64)%Z)); [apply Hnil|]; destruct (Z.leb (kk + (z mod 2^64)%Z) rk); [apply IH | exact I]
| destruct hints as [|[|] hs]; first [exact I | apply IH | apply Hnil | apply Hone] ].
+ destruct rb; try apply IH. destruct z; try apply IH.
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool; [|apply IH].
destruct (img_bytes segs rk n); [apply Hnil | exact I].
Qed.

#[using="Type"] Lemma rel_lit_inside : forall E rb rk rn kb kk kn d,
rel_lit rb rk rn kb kk kn = RInside d ->
rb = kb /\ d = (rk - kk)%Z /\ (kk <= rk)%Z /\ (rk + rn <= kk + kn)%Z /\
estart E (SA rb rk) = (estart E (SA kb kk) + d)%Z.
Proof.
intros E rb rk rn kb kk kn d H. unfold rel_lit in H.
destruct (expr_eqb rb kb) eqn:Heq; [|discriminate].
apply expr_eqb_eq in Heq. subst kb.
destruct (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool eqn:Hin.
- injection H as <-. apply andb_prop in Hin as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold estart. cbn [a_base a_off]. repeat split; lia.
- destruct (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool; discriminate.
Qed.

#[using="Type"] Lemma rel_lit_disjoint : forall E rb rk rn kb kk kn,
rel_lit rb rk rn kb kk kn = RDisjoint ->
rb = kb /\ ((estart E (SA rb rk) + rn <= estart E (SA kb kk))%Z
\/ (estart E (SA kb kk) + kn <= estart E (SA rb rk))%Z).
Proof.
intros E rb rk rn kb kk kn H. unfold rel_lit in H.
destruct (expr_eqb rb kb) eqn:Heq; [|discriminate].
apply expr_eqb_eq in Heq. subst kb.
destruct (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool; [discriminate|].
destruct (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool eqn:Hd; [|discriminate].
split; [reflexivity|]. unfold estart. cbn [a_base a_off].
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.

#[using="Type"] Lemma rdn_inside_wbytes : forall segs E M (ka : saddr) w (V : word) (ra : saddr) n d,
flat E ka (Z.of_nat w) -> flat E ra (Z.of_nat n) ->
estart E ra = (estart E ka + d)%Z -> (0 <= d)%Z -> (d + Z.of_nat n <= Z.of_nat w)%Z ->
rdn segs (wbytes M (adenot E ka) (word_to_le_bytes w V)) (adenot E ra) n
= Some (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w V))).
Proof.
intros segs E M ka w V ra n d Hfk Hfr Hst Hd Hdn.
pose proof (flat_u E ka _ Hfk) as Huk. pose proof (flat_u E ra _ Hfr) as Hur.
assert (Haddr : adenot E ra = adenot E ka + nat_to_word (Z.to_nat d)).
{ rewrite w_add_nat. apply bv_eq. rewrite Hur, u_small; [lia|].
destruct Hfk as (?&?&?&?). destruct Hfr as (?&?&?&?). rewrite Huk. lia. }
rewrite Haddr.
eapply rdn_slice.
- apply rdn_wbytes_hit. rewrite length_N_to_le_bytes. rewrite Huk.
destruct Hfk as (?&?&?&?). lia.
- rewrite length_N_to_le_bytes. lia.
Qed.

#[using="Type"] Lemma ext_hit_value : forall sx d n w (V : word),
(0 <= d)%Z -> (Z.to_nat d + n <= w)%nat -> (n <= 8)%nat ->
Z_to_bv 64 (extz sx n (bytes_le_to_Z (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w V)))))
= ext_val sx (Z.to_nat d) n V.
Proof.
intros sx d n w V Hd Hdn Hn.
rewrite slice_word_bytes by lia. unfold ext_val, ext_Z, extz. reflexivity.
Qed.

Section Lookups.
Variable segs : list Segment.

#[using="Type"] Lemma log_lookup_sound : forall E base kn log rb rk n sx hints acc,
know_ok segs E base kn ->
log_flat E log -> (1 <= n)%nat -> (n <= 8)%nat ->
match log_lookup kn log rb rk n sx hints acc with
| LHit v scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n = Some bs
/\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
| LMiss scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n
= rdn segs base (adenot E (SA rb rk)) n
| LStuck => True
end.
Proof.
intros E base kn log. induction log as [|[[kb kk] w v] rest IH]; intros rb rk n sx hints acc Hkn Hlf Hn1 Hn8.
{ cbn. intros _ _. reflexivity. }
cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfk & Hlf').
cbn [log_lookup mem_denot].
destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel.
-
intros Hscs Hfr.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
exists (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w (edenot E v)))).
split; [|split].
+ apply rdn_inside_wbytes; auto; lia.
+ apply length_firstn_skipn. rewrite length_N_to_le_bytes. lia.
+ rewrite mkExt_denot by exact Hn8. apply ext_hit_value; lia.
-
destruct (rel_lit_disjoint E _ _ _ _ _ _ Hrel) as [<- Hdis].
specialize (IH rb rk n sx hints acc Hkn Hlf' Hn1 Hn8).
destruct (log_lookup kn rest rb rk n sx hints acc) as [v' scs h|scs h|]; [ | | exact I];
intros Hscs Hfr;
(rewrite rdn_wbytes_out;
[ exact (IH Hscs Hfr)
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ]).
- exact I.
-
destruct (ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)) eqn:Hap.
{ pose proof (ranges_apart_sound segs E base kn _ _ _ _ _ _ Hkn Hap) as Hdis.
specialize (IH rb rk n sx hints acc Hkn Hlf' Hn1 Hn8).
destruct (log_lookup kn rest rb rk n sx hints acc) as [v' scs h|scs h|]; [ | | exact I];
intros Hscs Hfr;
(rewrite rdn_wbytes_out;
[ exact (IH Hscs Hfr)
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ]). }
assert (Hgen : forall hs,
match log_lookup kn rest rb rk n sx hs (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) with
| LHit v0 scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs (wbytes (mem_denot E base rest) (adenot E (SA kb kk)) (word_to_le_bytes w (edenot E v)))
(adenot E (SA rb rk)) n = Some bs
/\ length bs = n /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v0
| LMiss scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
rdn segs (wbytes (mem_denot E base rest) (adenot E (SA kb kk)) (word_to_le_bytes w (edenot E v)))
(adenot E (SA rb rk)) n = rdn segs base (adenot E (SA rb rk)) n
| LStuck => True
end).
{ intros hs.
specialize (IH rb rk n sx hs (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) Hkn Hlf' Hn1 Hn8).
pose proof (log_lookup_acc kn rest rb rk n sx hs (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)) as Hacc.
destruct (log_lookup kn rest rb rk n sx hs _) as [v' scs h|scs h|]; [ | | exact I];
intros Hscs Hfr; destruct Hacc as [pre ->];
(assert (Hd : sc_denot segs base E (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w)))
by (apply scs_denot_app in Hscs as [_ Hscs]; apply scs_denot_cons in Hscs as [Hd _]; exact Hd));
cbn [sc_denot] in Hd; destruct Hd as (Hf1 & Hf2 & Hdis);
rewrite (elenZ_elen E n) in Hf1, Hdis by lia; rewrite (elenZ_elen E w) in Hf2, Hdis by lia;
(rewrite rdn_wbytes_out;
[ exact (IH Hscs Hfr)
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk), (flat_u E _ _ Hfr); exact Hdis
| rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia
| rewrite length_N_to_le_bytes, (flat_u E _ _ Hfk); destruct Hfk as (?&?&?&?); lia ]). }
destruct hints as [|[|] hs0]; [apply Hgen | apply Hgen | exact I].
Qed.

End Lookups.

#[using="Type"] Lemma u_lit0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma estart_lit0 : forall E rk, estart E (SA (ELit 0) rk) = rk.
Proof. intros E rk. unfold estart. cbn [a_base a_off edenot]. rewrite u_lit0. lia. Qed.

#[using="Type"] Lemma adenot_shift : forall E (ka ra : saddr) nk nr d,
flat E ka nk -> flat E ra nr -> estart E ra = (estart E ka + d)%Z -> (0 <= d)%Z ->
adenot E ra = adenot E ka + nat_to_word (Z.to_nat d).
Proof.
intros E ka ra nk nr d Hfk Hfr Hst Hd.
rewrite w_add_nat. rewrite Z2Nat.id by exact Hd. apply bv_eq. rewrite (flat_u E _ _ Hfr).
rewrite (flat_u E _ _ Hfk).
destruct Hfk as (?&?&?&?). destruct Hfr as (?&?&?&?).
rewrite u_small by lia. exact Hst.
Qed.

#[using="Type"] Lemma elenZ_lit : forall E l0, elenZ E (ELit l0) = (l0 mod 2 ^ 64)%Z.
Proof. intros E l0. unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Section KLookup.
Variable segs : list Segment.

#[using="Type"] Lemma know_lookup_sound : forall E base kn rb rk n sx hints acc,
know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
match know_lookup segs kn rb rk n sx hints acc with
| LHit v scs _ =>
scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
/\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
| _ => True
end.
Proof.
intros E base kn. induction kn as [|K rest IH]; intros rb rk n sx hints acc Hkn Hn1 Hn8.
{ cbn. exact I. }
apply Forall_cons_iff in Hkn as [HK Hrest].
cbn [know_lookup].
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2].
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
5: { apply IH; assumption. }
-
cbn [kentry_ok] in HK. destruct HK as (Hkw8 & Hfk & Hrd).
destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel;
try (apply IH; assumption).
intros Hscs Hfr.
destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
exists (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w (edenot E v)))).
split; [|split].
+ rewrite (adenot_shift E (SA rb kk) (SA rb rk) _ _ d Hfk Hfr Hst ltac:(lia)).
eapply rdn_slice; [exact Hrd | lia].
+ apply length_firstn_skipn. rewrite length_N_to_le_bytes. lia.
+ rewrite mkExt_denot by exact Hn8. apply ext_hit_value; lia.
-
cbn [kentry_ok] in HK. destruct HK as [Hfk Hz].
assert (Hin : flat E (SA rb rk) (Z.of_nat n) ->
(estart E (SA kb kk) <= estart E (SA rb rk))%Z ->
(estart E (SA rb rk) + Z.of_nat n <= estart E (SA kb kk) + elenZ E len)%Z ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (ELit 0)).
{ intros Hfr Hlo Hhi. exists (repeat (Z_to_bv 8 0) n). split; [|split].
- apply rdn_pointwise; [apply repeat_length | rewrite (flat_u E _ _ Hfr); destruct Hfr as (?&?&?&?); lia |].
intros j Hj. rewrite (flat_u E _ _ Hfr). rewrite nth_repeat.
replace (estart E (SA rb rk) + Z.of_nat j)%Z
with (estart E (SA kb kk) + (estart E (SA rb rk) - estart E (SA kb kk) + Z.of_nat j))%Z by lia.
apply Hz. lia.
- apply repeat_length.
- cbn [edenot]. rewrite bytes_le_to_Z_repeat0, extz_0. reflexivity. }
destruct len as [l0| | | | | | |];
first
[ destruct (rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel;
[ intros Hscs Hfr; destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst);
apply Hin; [exact Hfr | lia | rewrite elenZ_lit; unfold estart in *; cbn [a_base a_off] in *; subst; lia]
| apply IH; assumption
| apply IH; assumption
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ]
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin; assumption
| apply IH; assumption ] ].
-
cbn [kentry_ok] in HK. destruct HK as (Hfk & Hlen & Hb).
destruct (expr_eqb rb kb) eqn:Heqb; [|apply IH; assumption].
apply expr_eqb_eq in Heqb. subst kb.
destruct (Z.leb kk rk) eqn:Hkk; [|apply IH; assumption].
apply Z.leb_le in Hkk.
assert (Hst : estart E (SA rb rk) = (estart E (SA rb kk) + (rk - kk))%Z).
{ unfold estart. cbn [a_base a_off]. lia. }
assert (Hin : flat E (SA rb rk) (Z.of_nat n) ->
(rk - kk + Z.of_nat n <= elenZ E len)%Z ->
exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (EBlob sx k (rk - kk) n)).
{ intros Hfr Hhi. exists (firstn n (skipn (Z.to_nat (rk - kk)) (eb E k))). split; [|split].
- apply rdn_pointwise.
+ apply length_firstn_skipn. lia.
+ rewrite (flat_u E _ _ Hfr). destruct Hfr as (?&?&?&?). lia.
+ intros j Hj. rewrite (flat_u E _ _ Hfr), Hst.
replace (estart E (SA rb kk) + (rk - kk) + Z.of_nat j)%Z
with (estart E (SA rb kk) + (rk - kk + Z.of_nat j))%Z by lia.
rewrite Hb by lia.
rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. f_equal. f_equal. lia.
- apply length_firstn_skipn. lia.
- cbn [edenot]. unfold blob_val, blob_bytes, extz. reflexivity. }
destruct len as [l0| | | | | | |];
first
[ destruct (Z.leb (rk + Z.of_nat n) (kk + l0 mod 2 ^ 64)) eqn:Hle;
[ intros Hscs Hfr; apply Hin; [exact Hfr | apply Z.leb_le in Hle; rewrite elenZ_lit; lia]
| destruct (Z.leb (kk + l0 mod 2 ^ 64) rk); [apply IH; assumption | exact I] ]
| destruct hints as [|[|] hs];
[ apply IH; assumption
| intros Hscs Hfr; apply scs_denot_cons in Hscs as [Hsc _]; cbn [sc_denot] in Hsc;
rewrite elenZ_elen in Hsc by lia; destruct Hsc as (_ & _ & Hlo & Hhi); apply Hin;
[assumption | unfold estart in Hhi, Hlo |- *; cbn [a_base a_off] in Hhi, Hlo |- *; lia]
| apply IH; assumption ] ].
-
cbn [kentry_ok] in HK. destruct HK as (Hlo0 & Hhi64 & Hnone).
destruct rb as [z| | | | | | |]; try (apply IH; assumption).
destruct z; try (apply IH; assumption).
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool eqn:Hr; [|apply IH; assumption].
apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
destruct (img_bytes segs rk n) as [zs|] eqn:Himg; [|exact I].
intros Hscs Hfr.
pose proof (flat_u E _ _ Hfr) as Hu. rewrite estart_lit0 in Hu.
destruct (rdn_img segs base n (adenot E (SA (ELit 0) rk)) zs) as (bs & Hbs & Hmap).
+ rewrite Hu. destruct Hfr as (?&?&?&?). rewrite estart_lit0 in *. lia.
+ intros j Hj. rewrite Hu. apply Hnone. lia.
+ rewrite Hu. exact Himg.
+ exists bs. split; [exact Hbs | split].
* exact (rdn_length _ _ _ _ _ Hbs).
* cbn [edenot]. unfold lit_of_bytes. rewrite <- Hmap, zbytes_map. unfold extz. reflexivity.
Qed.

End KLookup.

#[using="Type"] Lemma Z_to_bv64_u : forall z, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 z.
Proof. intros z. apply Z_to_bv_bv_unsigned. Qed.

#[using="Type"] Lemma Z_to_bv64_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.

#[using="Type"] Lemma to_saddr_denot : forall E e imm,
adenot E (to_saddr e imm) = v_addi (edenot E e) imm.
Proof.
intros E e imm. unfold to_saddr.
assert (Hgen : forall b k, split_lit e = (b, k) ->
adenot E (SA b (k + imm)) = v_addi (edenot E e) imm).
{ intros b k Hs. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
destruct e as [z|v|op a1 a2|op a1 a2|op a1 a2|op a1 a2|sx lo n a1|sx kk i n]; cbn [split_lit] in Hs;
try (injection Hs as <- <-; f_equal; lia).
- injection Hs as <- <-. cbn [edenot]. rewrite u_lit0, Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.add_0_l, Zplus_mod_idemp_l. reflexivity.
- destruct op; try (injection Hs as <- <-; f_equal; lia).
destruct a2 as [z| | | | | | |]; try (injection Hs as <- <-; f_equal; lia).
injection Hs as <- <-. cbn [edenot]. rewrite alu_add, v_add_lit, Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Zplus_mod_idemp_l. f_equal. lia. }
destruct (split_lit e) as [b k]. apply Hgen. reflexivity.
Qed.

#[using="Type"] Lemma step_fence : forall segs regs pc mem rom w a b c d e,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fence a b c d e, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w a b c d e Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

#[using="Type"] Lemma step_fencei : forall segs regs pc mem rom w a b c,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (FenceI a b c, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w a b c Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

#[using="Type"] Lemma testbit_mask : forall j i, (0 <= j)%Z -> (j < 64)%Z -> (0 <= i)%Z ->
Z.testbit (2 ^ 64 - 2 ^ j) i = ((j <=? i) && (i <? 64))%Z.
Proof.
intros j i Hj Hj64 Hi.
assert (Heq : (2 ^ 64 - 2 ^ j)%Z = Z.shiftl (Z.ones (64 - j)) j).
{ rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l.
rewrite <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia.
replace (64 - j + j)%Z with 64%Z by lia. lia. }
rewrite Heq.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite Z.shiftl_spec_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
- rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones by lia.
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia).
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
+ replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.

#[using="Type"] Lemma land_align_mask : forall x j, (0 <= j)%Z -> (j < 64)%Z -> (0 <= x < 2 ^ 64)%Z ->
(x mod 2 ^ j = 0)%Z -> Z.land x (2 ^ 64 - 2 ^ j) = x.
Proof.
intros x j Hj Hj64 Hx Hmod.
assert (Hx' : x = ((x / 2 ^ j) * 2 ^ j)%Z).
{ pose proof (Z.div_mod x (2 ^ j) ltac:(apply Z.pow_nonzero; lia)) as Hdm. lia. }
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask by lia.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia).
rewrite andb_false_r. rewrite Hx'. symmetry. apply Z.mul_pow2_bits_low. lia.
- replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). apply andb_true_r.
+ replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
symmetry. apply (Z_testbit_high 64 x i); lia.
Qed.
End FPGEN2.

Section ZBits.
Local Open Scope Z_scope.
#[using="Type"] Lemma testbit_drop_low : forall q r j i, 0 <= j -> 0 <= r < 2 ^ j -> j <= i ->
Z.testbit (q * 2 ^ j + r) i = Z.testbit (q * 2 ^ j) i.
Proof.
intros q r j i Hj Hr Hi.
replace i with ((i - j) + j) by lia.
rewrite <- !Z.div_pow2_bits by lia.
f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
rewrite Z_div_mult by lia. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[using="Type"] Lemma land_highmask : forall x j, 0 <= j < 64 -> 0 <= x < 2 ^ 64 ->
Z.land x (2 ^ 64 - 2 ^ j) = x - x mod 2 ^ j.
Proof.
intros x j Hj Hx.
assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hmb.
set (q := x / 2 ^ j) in *. set (r := x mod 2 ^ j) in *.
replace (x - r) with (q * 2 ^ j) by lia. rewrite Hdm.
replace (2 ^ j * q + r) with (q * 2 ^ j + r) by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
pose proof (testbit_mask j i ltac:(lia) ltac:(lia) ltac:(lia)) as Hmask.
rewrite Hmask. destruct (Z.lt_ge_cases i j) as [Hij|Hij].
- replace (j <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r.
symmetry. apply Z.mul_pow2_bits_low. lia.
- replace (j <=? i) with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
+ replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r.
apply testbit_drop_low; lia.
+ replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
assert (0 <= q) by (subst q; apply Z.div_pos; lia).
assert (0 <= q * 2 ^ j < 2 ^ 64) by nia.
destruct (Z.testbit (q * 2 ^ j) i) eqn:Ht; [|reflexivity]. exfalso.
assert (Hb : forall n a, 0 <= n -> 0 <= a < 2 ^ n -> forall k, n <= k -> Z.testbit a k = false).
{ intros n a Hn Ha k Hk. destruct (Z.testbit a k) eqn:E; [|reflexivity]. exfalso.
apply Z.testbit_true in E; [|lia].
assert (Hpk : 2 ^ n <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
assert (Hsmall : a / 2 ^ k = 0) by (apply Z.div_small; lia). rewrite Hsmall in E. cbn in E. lia. }
rewrite (Hb 64 (q * 2 ^ j)) in Ht by lia. discriminate.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End ZBits.
Section FPGEN3.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma and_highmask_val : forall (v : word) j, (0 <= j)%Z -> (j < 64)%Z ->
alu64 ALU_AND v (Z_to_bv 64 (- 2 ^ j)) = Z_to_bv 64 (bv_unsigned v - bv_unsigned v mod 2 ^ j).
Proof.
intros v j Hj Hj64. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j < 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
assert (Hm : ((- 2 ^ j) mod 2 ^ 64 = 2 ^ 64 - 2 ^ j)%Z).
{ rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
rewrite Hm. f_equal. apply land_highmask; lia.
Qed.

#[using="Type"] Lemma and_mask_id : forall (v : word) j,
(0 <= j)%Z -> (j < 64)%Z -> (bv_unsigned v mod 2 ^ j = 0)%Z ->
alu64 ALU_AND v (Z_to_bv 64 (- 2 ^ j)) = v.
Proof.
intros v j Hj Hj64 Hmod. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
pose proof (u64_range v) as Hv.
assert (Hm : ((- 2 ^ j) mod 2 ^ 64 = 2 ^ 64 - 2 ^ j)%Z).
{ assert (0 < 2 ^ j <= 2 ^ 64)%Z.
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
rewrite Hm, land_align_mask by lia. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma find_align_sound : forall segs E base kn a m,
know_ok segs E base kn -> find_align kn a = Some m ->
(0 < m)%Z /\ (bv_unsigned (edenot E a) mod m = 0)%Z.
Proof.
intros segs E base kn a m Hkn. induction kn as [|K rest IH]; cbn [find_align]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| | | |e' m'| | |]; try (apply IH; assumption).
destruct (expr_eqb a e') eqn:Heq.
- injection H as <-. apply expr_eqb_eq in Heq. subst e'. exact HK.
- apply IH; assumption.
Qed.

#[using="Type"] Lemma ctz_fuel_sound : forall f z, (0 <= ctz_fuel f z)%Z /\ (2 ^ ctz_fuel f z | z)%Z /\ (ctz_fuel f z <= Z.of_nat f)%Z.
Proof.
induction f as [|f IH]; intros z; cbn [ctz_fuel].
- split; [lia|]. split; [exists z; lia | lia].
- destruct (z mod 2 =? 0)%Z eqn:E.
+ destruct (IH (z / 2)%Z) as (A & [q Hq] & C). split; [lia|]. split; [|lia].
exists q. rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z.
apply Z.eqb_eq in E. pose proof (Z.div_mod z 2 ltac:(lia)). lia.
+ split; [lia|]. split; [exists z; rewrite Z.pow_0_r; lia | lia].
Qed.

#[using="Type"] Lemma ctz64_sound : forall z, (0 <= ctz64 z <= 64)%Z /\ (2 ^ ctz64 z | z)%Z.
Proof. intros z. unfold ctz64. destruct (ctz_fuel_sound 64 z) as (A & B & C). cbn [Z.of_nat] in C. split; [lia | exact B]. Qed.

#[using="Type"] Lemma pow2_divide_le : forall a b, (0 <= a <= b)%Z -> (2 ^ a | 2 ^ b)%Z.
Proof. intros a b H. exists (2 ^ (b - a))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

#[using="Type"] Lemma divide_mod64 : forall k t, (0 <= k <= 64)%Z -> (2 ^ k | t)%Z -> (2 ^ k | t mod 2 ^ 64)%Z.
Proof.
intros k t Hk Hd. rewrite Z.mod_eq by lia.
apply Z.divide_sub_r; [exact Hd|]. apply Z.divide_mul_l. apply pow2_divide_le. lia.
Qed.

#[using="Type"] Lemma ealign_sound : forall segs E M kn e,
know_ok segs E M kn ->
(0 <= ealign kn e <= 64)%Z /\ (2 ^ ealign kn e | bv_unsigned (edenot E e))%Z.
Proof.
intros segs E M kn e Hkn. induction e; cbn [ealign];
lazymatch goal with
| |- context [find_align kn ?e0] =>
destruct (find_align kn e0) as [m|] eqn:Hfa;
[ destruct (find_align_sound segs E M kn e0 m Hkn Hfa) as [Hm0 Hmod];
destruct (0 <? m)%Z eqn:Hp; [|split; [lia | apply Z.divide_1_l]];
destruct (ctz64_sound m) as [A B]; split; [exact A|];
eapply Z.divide_trans; [exact B|]; apply Z.mod_divide; [lia | exact Hmod]
| clear Hfa ]
end; cbn [edenot].
-  destruct (ctz64_sound (z mod two64)) as [A B]. split; [exact A|]. rewrite u_lit64. exact B.
- split; [lia | apply Z.divide_1_l].
- destruct IHe1 as [A1 B1], IHe2 as [A2 B2].
pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
destruct op; try (split; [lia | apply Z.divide_1_l]).
+  split; [lia|]. rewrite u_add64. apply divide_mod64; [lia|].
apply Z.divide_add_r; (eapply Z.divide_trans; [apply pow2_divide_le|]; [|eassumption]; lia).
+  split; [lia|]. rewrite u_sub64. apply divide_mod64; [lia|].
apply Z.divide_sub_r; (eapply Z.divide_trans; [apply pow2_divide_le|]; [|eassumption]; lia).
+  destruct (lit_shamt e2) as [s|] eqn:Hs; [|split; [lia | apply Z.divide_1_l]].
destruct (lit_shamt_sound E e2 s Hs) as [Hsv Hsr]. split; [lia|].
rewrite u_sll64, Hsv. apply divide_mod64; [lia|].
eapply Z.divide_trans; [apply (pow2_divide_le _ (ealign kn e1 + s)); lia|].
rewrite Z.pow_add_r by lia. apply Z.mul_divide_mono_r. exact B1.
+  split; [lia|]. rewrite u_or64.
set (k := Z.min (ealign kn e1) (ealign kn e2)).
assert (D1 : (2 ^ k | bv_unsigned (edenot E e1))%Z) by (eapply Z.divide_trans; [apply pow2_divide_le|exact B1]; lia).
assert (D2 : (2 ^ k | bv_unsigned (edenot E e2))%Z) by (eapply Z.divide_trans; [apply pow2_divide_le|exact B2]; lia).
destruct D1 as [q1 Hq1], D2 as [q2 Hq2]. exists (Z.lor q1 q2).
rewrite Hq1, Hq2. rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity.
+  split; [lia|]. rewrite u_and64.
set (k := Z.max (ealign kn e1) (ealign kn e2)).
assert (Hk : (0 <= k)%Z) by lia.

assert (Hlow : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (2 ^ k | x)%Z -> (2 ^ k | Z.land x y)%Z).
{ intros x y Hx Hy [q Hq]. exists (Z.land q (Z.shiftr y k)).
rewrite Hq. rewrite <- !Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
- rewrite !Z.shiftl_spec_low by lia. reflexivity.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
f_equal. f_equal. lia. }
destruct (Z.le_ge_cases (ealign kn e2) (ealign kn e1)) as [Hc|Hc].
* replace k with (ealign kn e1) in * by lia. apply Hlow; [lia | lia | exact B1].
* replace k with (ealign kn e2) in * by lia. rewrite Z.land_comm. apply Hlow; [lia | lia | exact B2].
- split; [lia | apply Z.divide_1_l].
- destruct IHe1 as [A1 B1], IHe2 as [A2 B2].
destruct op; try (split; [lia | apply Z.divide_1_l]).
split; [lia|]. rewrite u_mul64. apply divide_mod64; [lia|].
eapply Z.divide_trans; [apply (pow2_divide_le _ (ealign kn e1 + ealign kn e2)); lia|].
rewrite Z.pow_add_r by lia. destruct B1 as [p1 Hp1], B2 as [p2 Hp2]. exists (p1 * p2)%Z. rewrite Hp1, Hp2. ring.
- split; [lia | apply Z.divide_1_l].
- split; [lia | apply Z.divide_1_l].
- split; [lia | apply Z.divide_1_l].
Qed.

#[using="Type"] Lemma and_lowmask_zero : forall (v : word) j,
(0 <= j)%Z -> (j <= 64)%Z -> (2 ^ j | bv_unsigned v)%Z ->
alu64 ALU_AND v (Z_to_bv 64 (2 ^ j - 1)) = Z_to_bv 64 0.
Proof.
intros v j Hj Hj64 Hd. rewrite alu_and. unfold v_and. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. pose proof (u64_range v) as Hv.
assert (Hp : (0 < 2 ^ j <= 2 ^ 64)%Z).
{ split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
rewrite (Z.mod_small (2 ^ j - 1)) by lia.
replace (2 ^ j - 1)%Z with (Z.ones j) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. rewrite (Znumtheory.Zdivide_mod _ _ Hd). reflexivity.
Qed.

#[using="Type"] Lemma mkAnd_denot : forall segs E base kn a b,
know_ok segs E base kn ->
edenot E (mkAnd kn a b) = alu64 ALU_AND (edenot E a) (edenot E b).
Proof.
intros segs E base kn a b Hkn. unfold mkAnd.
destruct b as [k| | | | | | |]; try apply mkAlu_denot.
destruct (ealign_sound segs E base kn a Hkn) as [Hal Hdiv].
set (k' := (k mod two64)%Z). set (j := Z.log2 (two64 - k')).
assert (Hk' : (0 <= k' < 2 ^ 64)%Z) by (subst k'; unfold two64; apply Z.mod_pos_bound; lia).
assert (Hbk : Z_to_bv 64 k = Z_to_bv 64 k').
{ apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. subst k'. unfold two64. rewrite Z.mod_mod by lia. reflexivity. }
pose proof (u64_range (edenot E a)) as Hua.
destruct (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool eqn:Hc.
- apply andb_prop in Hc as [Hpow Hj64]. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
assert (Hj0 : (0 <= j)%Z) by (subst j; apply Z.log2_nonneg).
cbn [edenot]. rewrite Hbk. replace k' with (2 ^ 64 - 2 ^ j)%Z by (unfold two64 in Hpow; lia).
assert (Hneg : Z_to_bv 64 (2 ^ 64 - 2 ^ j) = Z_to_bv 64 (- 2 ^ j)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- (Z.mod_add (- 2 ^ j) 1) by lia. f_equal. lia. }
rewrite Hneg.
destruct (Z.leb j (ealign kn a)) eqn:Hle.
+ apply Z.leb_le in Hle. symmetry. apply and_mask_id; [lia | lia |].
apply Znumtheory.Zdivide_mod. eapply Z.divide_trans; [apply pow2_divide_le | exact Hdiv]. lia.
+ destruct (lin_of a) as [c ts] eqn:Hl. cbn [fst snd].
destruct (coeffs_div (2 ^ j) ts) eqn:Hcd; [| rewrite <- Hneg; replace (2 ^ 64 - 2 ^ j)%Z with k' by (unfold two64 in Hpow; lia); rewrite <- Hbk; apply mkAlu_denot].
rewrite and_highmask_val by lia.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (lin_of_sound E a) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs. unfold uE in Hs.
assert (Hmod : (bv_unsigned (edenot E a) mod 2 ^ j = c mod 2 ^ j)%Z).
{ rewrite <- (eqm_mod_pow2 _ _ j ltac:(lia) Hs). rewrite Z.add_mod, (coeffs_div_sound E _ ts Hp Hcd), Z.add_0_r, Z.mod_mod by lia. reflexivity. }
rewrite Hmod. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
destruct Hs as [q Hq]. exists q. lia.
- set (j2 := Z.log2 (k' + 1)).
destruct (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool eqn:Hc2; [|apply mkAlu_denot].
apply andb_prop in Hc2 as [Hpow Hj64]. apply Z.eqb_eq in Hpow. apply Z.ltb_lt in Hj64.
assert (Hj0 : (0 <= j2)%Z) by (subst j2; apply Z.log2_nonneg).
cbn [edenot]. rewrite Hbk. replace k' with (2 ^ j2 - 1)%Z by lia.
destruct (Z.leb j2 (ealign kn a)) eqn:Hle.
+ apply Z.leb_le in Hle. symmetry. apply and_lowmask_zero; [lia | lia |].
eapply Z.divide_trans; [apply pow2_divide_le | exact Hdiv]. lia.
+ destruct (lin_lowbits a j2) as [v|] eqn:Hlb;
[| replace (2 ^ j2 - 1)%Z with k' by lia; rewrite <- Hbk; apply mkAlu_denot].
destruct (lin_lowbits_sound E a j2 v ltac:(lia) Hlb) as [Hv Hvr].
rewrite and_lowmask_val by lia. cbn [edenot]. rewrite Hv. reflexivity.
Qed.

#[using="Type"] Lemma itv_ltu_sound : forall al ah bl bh x y t,
(al <= x <= ah)%Z -> (bl <= y <= bh)%Z -> itv_ltu al ah bl bh = Some t -> (x <? y)%Z = t.
Proof.
intros al ah bl bh x y t Hx Hy H. unfold itv_ltu in H.
destruct (ah <? bl)%Z eqn:C1; [injection H as <-; apply Z.ltb_lt; lia|].
destruct (bh <=? al)%Z eqn:C2; [injection H as <-; apply Z.ltb_ge; lia| discriminate].
Qed.

#[using="Type"] Lemma itv_lts_sound : forall al ah bl bh (x y : word) t,
(al <= bv_unsigned x <= ah)%Z -> (bl <= bv_unsigned y <= bh)%Z ->
itv_lts al ah bl bh = Some t -> (bv_signed x <? bv_signed y)%Z = t.
Proof.
intros al ah bl bh x y t Hx Hy H. unfold itv_lts in H.
pose proof (u64_range x) as Rx. pose proof (u64_range y) as Ry.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
- apply orb_prop in C1 as [C1|C1]; apply andb_prop in C1 as [Ca Cb].
+ rewrite (bv_signed_small x) by lia. rewrite (bv_signed_small y) by lia.
eapply itv_ltu_sound; [exact Hx | exact Hy | exact H].
+ rewrite (bv_signed_hi x) by lia. rewrite (bv_signed_hi y) by lia.
pose proof (itv_ltu_sound al ah bl bh (bv_unsigned x) (bv_unsigned y) t Hx Hy H) as Hl.
destruct t; [apply Z.ltb_lt in Hl; apply Z.ltb_lt | apply Z.ltb_ge in Hl; apply Z.ltb_ge]; lia.
- match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2 end.
+ injection H as <-. apply andb_prop in C2 as [Ca Cb].
rewrite (bv_signed_hi x) by lia. rewrite (bv_signed_small y) by lia. apply Z.ltb_lt. lia.
+ match type of H with (if ?c then _ else _) = _ => destruct c eqn:C3 end; [|discriminate].
injection H as <-. apply andb_prop in C3 as [Ca Cb].
rewrite (bv_signed_small x) by lia. rewrite (bv_signed_hi y) by lia. apply Z.ltb_ge. lia.
Qed.

#[using="Type"] Lemma range_branch_sound : forall c al ah bl bh (x y : word) t,
(al <= bv_unsigned x <= ah)%Z -> (bl <= bv_unsigned y <= bh)%Z ->
range_branch c al ah bl bh = Some t -> branch_taken c x y = t.
Proof.
intros c al ah bl bh x y t Hx Hy H. destruct c; cbn [range_branch branch_taken] in *;
unfold bv_eqb, bv_ltu, bv_lts.
- match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
+ injection H as <-. apply Z.eqb_neq. apply orb_prop in C1 as [C1|C1]; apply Z.ltb_lt in C1; lia.
+ match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2 end; [|discriminate].
injection H as <-. apply Z.eqb_eq. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3]. lia.
- match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1 end.
+ injection H as <-. apply Bool.negb_true_iff. apply Z.eqb_neq. apply orb_prop in C1 as [C1|C1]; apply Z.ltb_lt in C1; lia.
+ match type of H with (if ?c then _ else _) = _ => destruct c eqn:C2 end; [|discriminate].
injection H as <-. apply Bool.negb_false_iff. apply Z.eqb_eq. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3]. lia.
- eapply itv_lts_sound; eassumption.
- destruct (itv_lts al ah bl bh) as [t'|] eqn:Hi; [|discriminate]. cbn [option_map] in H. injection H as <-.
f_equal. eapply itv_lts_sound; eassumption.
- eapply itv_ltu_sound; eassumption.
- destruct (itv_ltu al ah bl bh) as [t'|] eqn:Hi; [|discriminate]. cbn [option_map] in H. injection H as <-.
f_equal. eapply itv_ltu_sound; eassumption.
Qed.

#[using="Type"] Lemma cond_on_eq_sound : forall c (v : word), branch_taken c v v = cond_on_eq c.
Proof.
intros c v. destruct c; cbn [branch_taken cond_on_eq]; unfold bv_eqb, bv_lts, bv_ltu;
rewrite ?Z.eqb_refl, ?Z.ltb_irrefl; reflexivity.
Qed.

#[using="Type"] Lemma decide_branch_sound : forall segs E M kn c a b t,
know_ok segs E M kn -> decide_branch kn c a b = Some t ->
branch_taken c (edenot E a) (edenot E b) = t.
Proof.
intros segs E M kn c a b t Hkn H.
assert (Hrest : (if expr_eqb a b then Some (cond_on_eq c)
else match erange kn a, erange kn b with
| Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
| _, _ => None
end) = Some t ->
branch_taken c (edenot E a) (edenot E b) = t).
{ clear H. intros H. destruct (expr_eqb a b) eqn:Heq.
- apply expr_eqb_eq in Heq. subst b. injection H as <-. apply cond_on_eq_sound.
- destruct (erange kn a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (erange kn b) as [[bl bh]|] eqn:Hb; [|discriminate].
eapply range_branch_sound; [eapply erange_sound; [exact Hkn | exact Ha] | eapply erange_sound; [exact Hkn | exact Hb] | exact H]. }
unfold decide_branch in H.
destruct a; try exact (Hrest H). destruct b; try exact (Hrest H).
injection H as <-. reflexivity.
Qed.

#[using="Type"] Lemma lin_nowrap_sound : forall segs E M kn e,
know_ok segs E M kn -> lin_nowrap kn e = true ->
bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof.
intros segs E M kn e Hkn H. unfold lin_nowrap in H.
destruct (lin_range (erange kn) (fst (lin_of e)) (snd (lin_of e))) as [[lo hi]|] eqn:Hlr; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
pose proof (u64_range (edenot E e)). nia.
Qed.

#[using="Type"] Lemma ldiv_terms_sound : forall E m ts, (0 < m)%Z -> coeffs_div m ts = true ->
tden E ts = (m * tden E (ldiv_terms m ts))%Z.
Proof.
intros E m ts Hm. induction ts as [|[k a] rest IH]; cbn [coeffs_div ldiv_terms tden]; intros H.
- lia.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH H2).
pose proof (Z.div_mod k m ltac:(lia)). nia.
Qed.

#[using="Type"] Lemma mkSrl_denot : forall segs E M kn a sh (y : word),
know_ok segs E M kn -> (bv_unsigned y mod 64 = sh)%Z ->
edenot E (mkSrl kn a sh) = alu64 ALU_SRL (edenot E a) y.
Proof.
intros segs E M kn a sh y Hkn Hy. unfold mkSrl.
pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as Hsr. rewrite Hy in Hsr.
assert (Hlit : edenot E (mkAlu ALU_SRL a (ELit sh)) = alu64 ALU_SRL (edenot E a) y).
{ rewrite mkAlu_denot. cbn [edenot]. apply alu_srl_amt. rewrite (u_lit_mod sh 64) by lia. symmetry; exact Hy. }
match goal with |- edenot E (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|exact Hlit].
apply andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hc Hc3]. apply andb_prop in Hc as [Hc Hc2].
apply andb_prop in Hc as [Htriv Hdiv]. apply Z.leb_le in Hc2. apply Z.ltb_lt in Hc3.
assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (lin_nowrap_sound segs E M kn a Hkn Hnw) as Hval.
destruct (lin_of a) as [c ts] eqn:Hl. cbn [fst snd] in *.
rewrite (ldiv_terms_sound E (2 ^ sh) ts Hp Hdiv) in Hval.
rewrite alu_srl. unfold v_srl. rewrite Hy, Z.shiftr_div_pow2, Hval by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
exists 0%Z.
replace (c + 2 ^ sh * tden E (ldiv_terms (2 ^ sh) ts))%Z
with (tden E (ldiv_terms (2 ^ sh) ts) * 2 ^ sh + c)%Z by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small c) by lia. lia.
Qed.

#[using="Type"] Lemma land_aligned_small : forall x b k, (0 <= k)%Z -> (0 <= x)%Z -> (2 ^ k | x)%Z -> (0 <= b < 2 ^ k)%Z ->
Z.land x b = 0%Z.
Proof.
intros x b k Hk Hx [q Hq] Hb. subst x.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply andb_false_r.
Qed.

#[using="Type"] Lemma or_disjoint_sound : forall segs E M kn a b,
know_ok segs E M kn -> or_disjoint kn a b = true ->
Z.lor (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b))%Z.
Proof.
intros segs E M kn a b Hkn H. unfold or_disjoint in H.
destruct (erange kn b) as [[lo hi]|] eqn:Hr; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (erange_sound segs E M kn b lo hi Hkn Hr) as Hb.
destruct (ealign_sound segs E M kn a Hkn) as [Hk Hdiv].
pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
pose proof (Z.add_lor_land (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))) as Hal.
rewrite (land_aligned_small _ _ (ealign kn a)) in Hal by (try lia; exact Hdiv). lia.
Qed.

#[using="Type"] Lemma mkOr_denot : forall segs E M kn a b,
know_ok segs E M kn -> edenot E (mkOr kn a b) = alu64 ALU_OR (edenot E a) (edenot E b).
Proof.
intros segs E M kn a b Hkn. unfold mkOr.
destruct (is_lit a) as [x|] eqn:Ha; [destruct (is_lit b) as [y|] eqn:Hb|].
- apply is_lit_some in Ha. apply is_lit_some in Hb. subst. cbn [edenot]. unfold zalu. apply Z_to_bv_bv_unsigned.
- destruct (or_disjoint kn a b) eqn:H1; [|destruct (or_disjoint kn b a) eqn:H2; [|reflexivity]];
rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry.
+ eapply or_disjoint_sound; eassumption.
+ rewrite Z.lor_comm, Z.add_comm. eapply or_disjoint_sound; eassumption.
- destruct (or_disjoint kn a b) eqn:H1; [|destruct (or_disjoint kn b a) eqn:H2; [|reflexivity]];
rewrite mkAlu_denot, alu_add, alu_or; unfold v_add, v_or; f_equal; symmetry.
+ eapply or_disjoint_sound; eassumption.
+ rewrite Z.lor_comm, Z.add_comm. eapply or_disjoint_sound; eassumption.
Qed.

#[using="Type"] Lemma mkAluK_denot : forall segs E base kn op a b,
know_ok segs E base kn ->
edenot E (mkAluK kn op a b) = alu64 op (edenot E a) (edenot E b).
Proof.
intros segs E base kn op a b Hkn. unfold mkAluK. destruct op; try apply mkAlu_denot.
-  destruct (is_lit a); [apply mkAlu_denot|].
destruct (shamt_of b 6) as [sh|] eqn:Hs; [|apply mkAlu_denot].
destruct (shamt_of_sound E b 6 sh ltac:(lia) Hs) as [Hm Hr]. change (2 ^ 6)%Z with 64%Z in Hm.
eapply mkSrl_denot; [exact Hkn | exact Hm].
-  eapply mkOr_denot. exact Hkn.
-
assert (Hcomm : alu64 ALU_AND (edenot E b) (edenot E a) = alu64 ALU_AND (edenot E a) (edenot E b)).
{ rewrite !alu_and. unfold v_and. rewrite Z.land_comm. reflexivity. }
destruct a; destruct b; try (eapply mkAnd_denot; exact Hkn);
rewrite <- Hcomm; eapply mkAnd_denot; exact Hkn.
Qed.

#[using="Type"] Lemma flat_sc_sound : forall segs E base kn a n rest,
know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
scs_denot segs base E (flat_sc kn a n ++ rest) ->
flat E a (Z.of_nat n) /\ scs_denot segs base E rest.
Proof.
intros segs E base kn a n rest Hkn Hn1 Hn8 H. unfold flat_sc in H.
destruct (base_range kn (a_base a)) as [[lo hi]|] eqn:Hb.
- destruct (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool eqn:Hc.
+ split; [|exact H]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (base_range_sound segs E base kn _ _ _ Hkn Hb) as [A B].
unfold flat, estart. lia.
+ apply scs_denot_cons in H as [Hf Hr]. cbn [sc_denot] in Hf. rewrite elenZ_elen in Hf by exact Hn8. auto.
- apply scs_denot_cons in H as [Hf Hr]. cbn [sc_denot] in Hf. rewrite elenZ_elen in Hf by exact Hn8. auto.
Qed.

#[using="Type"] Lemma eval_closed_sound : forall E e v, eval_closed e = Some v -> edenot E e = Z_to_bv 64 v.
Proof.
intros E e. induction e; intros v H; cbn [eval_closed] in H; cbn [edenot]; try discriminate.
- injection H as <-. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64. rewrite Z.mod_mod by lia. reflexivity.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zalu. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zaluw. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zmd. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e1) as [x|] eqn:H1; [|discriminate]. destruct (eval_closed e2) as [y|] eqn:H2; [|discriminate].
injection H as <-. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl). unfold zmdw. symmetry. apply Z_to_bv_bv_unsigned.
- destruct (eval_closed e) as [x|] eqn:H1; [|discriminate].
injection H as <-. rewrite (IHe x eq_refl). unfold zext_lit. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma esubst_sound : forall E s r e, edenot E r = edenot E s -> edenot E (esubst s r e) = edenot E e.
Proof.
intros E s r e Hr. induction e; cbn [esubst];
(destruct (expr_eqb _ s) eqn:Heq;
[ apply expr_eqb_eq in Heq; rewrite Hr, <- Heq; reflexivity
| cbn [edenot]; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity ]).
Qed.

#[using="Type"] Lemma all_eval_to_sound : forall s e v lo cnt, all_eval_to s e v lo cnt = true ->
forall z, (lo <= z < lo + Z.of_nat cnt)%Z -> eval_closed (esubst s (ELit z) e) = Some v.
Proof.
intros s e v lo cnt. revert lo. induction cnt as [|c IH]; intros lo H z Hz; [lia|].
cbn [all_eval_to] in H. destruct (eval_closed (esubst s (ELit lo) e)) as [w|] eqn:Hw; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst w.
destruct (Z.eq_dec z lo) as [->|Hne]; [exact Hw|].
apply (IH (lo + 1)%Z H2). lia.
Qed.

#[using="Type"] Lemma conc_try_sound : forall segs E M kn e cands v,
know_ok segs E M kn -> conc_try kn e cands = Some v -> edenot E e = Z_to_bv 64 v.
Proof.
intros segs E M kn e cands v Hkn. induction cands as [|c rest IH]; cbn [conc_try]; intros H; [discriminate|].
destruct (closedb c); [apply IH; exact H|].
destruct (erange kn c) as [[lo hi]|] eqn:Hr; [|apply IH; exact H].
destruct (Z.leb (hi - lo) conc_limit); [|apply IH; exact H].
destruct (eval_closed (esubst c (ELit lo) e)) as [v0|] eqn:Hv0; [|apply IH; exact H].
destruct (all_eval_to c e v0 lo (Z.to_nat (hi - lo + 1))) eqn:Hall; [|apply IH; exact H].
injection H as <-.
pose proof (erange_sound segs E M kn c lo hi Hkn Hr) as Hb.
pose proof (all_eval_to_sound c e v0 lo _ Hall (bv_unsigned (edenot E c)) ltac:(rewrite Z2Nat.id by lia; lia)) as He.
rewrite <- (esubst_sound E c (ELit (bv_unsigned (edenot E c))) e) by (cbn [edenot]; apply Z_to_bv_bv_unsigned).
apply eval_closed_sound. exact He.
Qed.

#[using="Type"] Lemma concretize_sound : forall segs E M kn e v,
know_ok segs E M kn -> concretize kn e = Some v -> edenot E e = Z_to_bv 64 v.
Proof.
intros segs E M kn e v Hkn H. unfold concretize in H.
destruct (closedb e); [apply eval_closed_sound; exact H | eapply conc_try_sound; eassumption].
Qed.

#[using="Type"] Lemma conc_expr_sound : forall segs E M kn e,
know_ok segs E M kn -> edenot E (conc_expr kn e) = edenot E e.
Proof.
intros segs E M kn e Hkn. unfold conc_expr.
assert (Hg : forall e', edenot E (match concretize kn e' with Some v => ELit v | None => e' end) = edenot E e').
{ intros e'. destruct (concretize kn e') as [v|] eqn:Hc; [|reflexivity].
symmetry. exact (concretize_sound segs E M kn e' v Hkn Hc). }
destruct e; try reflexivity; apply Hg.
Qed.

#[using="Type"] Lemma to_saddrK_denot : forall segs E M kn e imm,
know_ok segs E M kn -> adenot E (to_saddrK kn e imm) = v_addi (edenot E e) imm.
Proof.
intros segs E M kn e imm Hkn. unfold to_saddrK.
destruct (split_lit e) as [b k] eqn:Hs.
destruct b; try (destruct (concretize kn (mkAlu ALU_ADD e (ELit imm))) as [v|] eqn:Hc;
[ unfold adenot; cbn [a_base a_off edenot];
pose proof (concretize_sound segs E M kn _ v Hkn Hc) as Hv; rewrite mkAlu_denot in Hv; cbn [edenot] in Hv;
unfold v_addi; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; rewrite Z.mod_0_l by lia; rewrite Z.add_0_l;
apply (f_equal bv_unsigned) in Hv; rewrite Z_to_bv_unsigned, bv_wrap64_mod in Hv; rewrite <- Hv;
rewrite alu_add; unfold v_add; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod;
rewrite Zplus_mod_idemp_r; reflexivity
| apply to_saddr_denot ]).
apply to_saddr_denot.
Qed.
End FPGEN3.

Section StepSound.
Context {fF : FPF} {fC : FPC}.
Variable segs : list Segment.

Definition st_ok (E : env) (base rom : word -> option byte)
(ss : sym_state) (ms : machine_state) : Prop :=
exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
/\ regs_ok E (s_regs ss) regs
/\ log_flat E (s_log ss)
/\ know_ok segs E base (s_know ss).

#[using="Type"] Lemma msize_bytes_range : forall sz, (1 <= msize_bytes sz)%nat /\ (msize_bytes sz <= 8)%nat.
Proof. destruct sz; cbn; lia. Qed.

#[using="Type"] Lemma sym_step_sound_load : forall E base rom ss regs sz sx rd rs imm ss' scs scr scr' w,
fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
is_ecall w = false ->
decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
sym_step segs (Load sz sx rd rs imm) ss scr = SOk ss' scs scr' ->
scs_denot segs base E scs ->
regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom) = MachineOk ms'
/\ st_ok E base rom ss' ms'.
Proof.
intros E base rom ss regs sz sx rd rs imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
set (n := msize_bytes sz) in Hs.
set (sx' := match sz with SZ8 => false | _ => sx end) in Hs.
set (a := to_saddrK (s_know ss) (sr_get (s_regs ss) rs) (bv_signed imm)) in Hs.
pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = v_addi (getr regs rs) (bv_signed imm)).
{ subst a. rewrite (to_saddrK_denot segs E base _ _ _ Hkn), Hregs. reflexivity. }
assert (Hsx : sx' = eff_sx sz sx) by (subst sx'; destruct sz; reflexivity).
assert (Hfin : forall v bs,
rdn segs mem (adenot E a) n = Some bs -> length bs = n ->
Z_to_bv 64 (extz sx' n (bytes_le_to_Z bs)) = edenot E v ->
exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) mem rom) = MachineOk ms'
/\ st_ok E base rom (sset ss rd v (s_pc ss + 4)) ms').
{ intros v bs Hrd Hlen Hval.
rewrite Hadr in Hrd.
eexists; split; [exact (step_load segs regs _ mem rom w sz sx rd rs imm bs Hf He Hd Hrd)|].
eexists; split; [f_equal; cbn [s_pc sset]; apply v_addi_lit|].
cbn [s_regs s_log s_know sset]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|].
rewrite load_result_val by (subst n; exact Hlen). rewrite <- Hsx. fold n. symmetry. exact Hval. }
destruct (log_lookup (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [v lscs lh|lscs lh|] eqn:Hll;
[ | | discriminate].
-
injection Hs as <- <- <-.
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
pose proof (log_lookup_sound segs E base (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] Hkn Hlf Hn1 Hn8) as HL.
rewrite Hll in HL.
destruct (HL Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
apply (Hfin v bs); [destruct a; exact Hrd | exact Hlen | exact Hval].
-
pose proof (log_lookup_sound segs E base (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] Hkn Hlf Hn1 Hn8) as HL.
rewrite Hll in HL.
pose proof (know_lookup_sound segs E base (s_know ss) (a_base a) (a_off a) n sx' lh lscs Hkn Hn1 Hn8) as HK.
pose proof (know_lookup_acc segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as HKacc.
destruct (know_lookup segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as [v kscs kh|kscs kh|] eqn:Hkl;
[ | | discriminate].
+
injection Hs as <- <- <-.
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
destruct HKacc as [pre ->].
assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
destruct (HK Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
apply (Hfin v bs); [| exact Hlen | exact Hval].
destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd.
+
injection Hs as <- <- <-.
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
apply scs_denot_cons in Hsc as [Hrb Hsc]. cbn [sc_denot] in Hrb.
destruct Hrb as (bs & Hrd & Hval).
destruct HKacc as [pre ->].
assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
assert (Hrd' : rdn segs mem (adenot E a) n = Some bs).
{ destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd. }
pose proof (rdn_length _ _ _ _ _ Hrd') as Hlen.
rewrite Hadr in Hrd'.
eexists; split; [exact (step_load segs regs _ mem rom w sz sx rd rs imm bs Hf He Hd Hrd')|].
eexists; split; [f_equal; cbn [s_pc]; apply v_addi_lit|].
cbn [s_regs s_log s_know]. split; [|split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|].
rewrite load_result_val by (subst n; exact Hlen). rewrite <- Hsx. fold n. symmetry. exact Hval.
Qed.

#[using="Type"] Lemma sym_step_sound_store : forall E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w,
fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
is_ecall w = false ->
decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
sym_step segs (Store sz rs1 rs2 imm) ss scr = SOk ss' scs scr' ->
scs_denot segs base E scs ->
regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom) = MachineOk ms'
/\ st_ok E base rom ss' ms'.
Proof.
intros E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
set (mem := mem_denot E base (s_log ss)) in *.
cbn [sym_step] in Hs.
injection Hs as <- <- <-.
set (n := msize_bytes sz) in *.
set (a := to_saddrK (s_know ss) (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm)).
{ subst a. rewrite (to_saddrK_denot segs E base _ _ _ Hkn), Hregs. reflexivity. }
apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc].
assert (Hok : RiscvSemantics.store_ok segs base (adenot E a) n = true).
{ unfold storeok_sc in Hsc.
destruct (wr_covered (s_know ss) a n) eqn:Hw.
- clear Hsc. revert Hw. generalize Hkn. generalize (s_know ss) as kn. intros kn Hkn0 Hw.
induction kn as [|K rest IH]; cbn [wr_covered] in Hw; [discriminate|].
apply Forall_cons_iff in Hkn0 as [HK Hrest].
destruct K as [| | | | | |[kb kk] len|]; try (apply IH; assumption).
destruct (expr_eqb (a_base a) kb && Z.leb kk (a_off a) && Z.leb (a_off a + Z.of_nat n) (kk + len))%bool eqn:Hc;
[|apply IH; assumption].
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
cbn [kentry_ok] in HK. destruct HK as [Hfk Hs0].
replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (a_off a - kk))).
+ apply Hs0; lia.
+ apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite <- H1.
destruct Hfl as (?&?&?&?). unfold estart in *. rewrite u_small by lia. lia.
- apply scs_denot_cons in Hsc as [Hok _]. cbn [sc_denot] in Hok. exact Hok. }
assert (Hok' : RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) n = true).
{ rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
eexists; split; [exact (step_store segs regs _ mem rom w sz rs1 rs2 imm Hf He Hd Hok')|].
eexists; split.
- f_equal; [cbn [s_pc]; apply v_addi_lit|].
cbn [s_log mem_denot]. fold n. rewrite Hadr, (Hregs rs2). reflexivity.
- cbn [s_regs s_log s_know]. split; [exact Hregs|]. split; [|exact Hkn].
cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
Qed.

Ltac alu_case STEP DEN :=
match goal with
| Hs : SOk _ _ _ = SOk _ _ _ |- _ =>
injection Hs as <- <- <-;
eexists; split; [ STEP |];
eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |];
cbn [s_regs s_log s_know sset];
match goal with
| Hregs : regs_ok _ _ _, Hlf : log_flat _ _, Hkn : know_ok _ _ _ _ |- _ =>
split; [ apply regs_ok_upd; [exact Hregs|]; DEN | split; [exact Hlf | exact Hkn] ]
end
end.

#[using="Type"] Lemma sym_step_sound : forall E base rom ss ms i ss' scs scr scr' w,
fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
is_ecall w = false ->
decode_any w = Some (i, 4%Z) ->
sym_step segs i ss scr = SOk ss' scs scr' ->
scs_denot segs base E scs ->
st_ok E base rom ss ms ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms'
/\ st_ok E base rom ss' ms'.
Proof.
intros E base rom ss ms i ss' scs scr scr' w Hf He Hd Hs Hsc (regs & -> & Hregs & Hlf & Hkn).
destruct i;
try (eapply sym_step_sound_load; eassumption);
try (eapply sym_step_sound_store; eassumption);
set (mem := mem_denot E base (s_log ss)) in *;
cbn [sym_step] in Hs; try discriminate.
-
alu_case ltac:(exact (step_lui segs regs _ mem rom w rd imm Hf He Hd))
ltac:(cbn [edenot]; unfold v_lui; apply Z_to_bv64_u).
-
alu_case ltac:(exact (step_auipc segs regs _ mem rom w rd imm Hf He Hd))
ltac:(cbn [edenot]; rewrite Z_to_bv64_u; symmetry; apply v_auipc_lit).
-
injection Hs as <- <- <-.
eexists; split; [ exact (step_jal_link segs regs _ mem rom w rd imm Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sset]; rewrite btgt_lit; symmetry; apply Z_to_bv64_u |].
cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
-
pose proof (conc_expr_sound segs E base (s_know ss) (sr_get (s_regs ss) rs1) Hkn) as Hce.
destruct (conc_expr (s_know ss) (sr_get (s_regs ss) rs1)) as [z| | | | | | |] eqn:Hg; try discriminate.
injection Hs as <- <- <-.
eexists; split; [ exact (step_jalr segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
eexists; split.
+ f_equal. cbn [s_pc sset]. unfold v_jalr.
specialize (Hregs rs1) as Hg1. rewrite <- Hce in Hg1. cbn [edenot] in Hg1.
rewrite Hg1. rewrite Z_to_bv64_mod. exact (jalr_tgt_lit z (bv_signed imm)).
+ cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
-
set (tk := bv_unsigned (Z_to_bv 64 (s_pc ss + bv_signed imm))) in Hs.
assert (Hcond : forall t, branch_taken c (getr regs rs1) (getr regs rs2) = t ->
exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) mem rom) = MachineOk ms'
/\ st_ok E base rom (sjump ss (if t then tk else (s_pc ss + 4)%Z)) ms').
{ intros t Ht. destruct t.
- eexists; split; [exact (step_branch_tk_gen segs regs _ mem rom w c rs1 rs2 imm Hf He Hd Ht)|].
eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
f_equal. cbn [s_pc sjump]. rewrite btgt_lit. subst tk. symmetry. apply Z_to_bv64_u.
- eexists; split; [exact (step_branch_ft_gen segs regs _ mem rom w c rs1 rs2 imm Hf He Hd Ht)|].
eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
f_equal. cbn [s_pc sjump]. apply v_addi_lit. }
destruct (decide_branch (s_know ss) c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) as [t|] eqn:Hdb.
+
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
eapply decide_branch_sound; [exact Hkn | exact Hdb].
+ destruct (decide_branch (s_know ss) c (conc_expr (s_know ss) (sr_get (s_regs ss) rs1))
(conc_expr (s_know ss) (sr_get (s_regs ss) rs2))) as [t|] eqn:Hdb2.
*
injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
rewrite <- (conc_expr_sound segs E base (s_know ss) (sr_get (s_regs ss) rs1) Hkn).
rewrite <- (conc_expr_sound segs E base (s_know ss) (sr_get (s_regs ss) rs2) Hkn).
eapply decide_branch_sound; [exact Hkn | exact Hdb2].
*
destruct (sc_dirs scr) as [|t dirs'] eqn:Hdirs; [discriminate|].
injection Hs as <- <- <-. apply Hcond.
apply scs_denot_cons in Hsc as [Hbr _]. cbn [sc_denot] in Hbr.
rewrite (Hregs rs1), (Hregs rs2). exact Hbr.
-
alu_case ltac:(exact (step_opimm_gen segs regs _ mem rom w op rd rs1 imm Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hkn); cbn [edenot]; rewrite <- Hregs, sext64_lit; reflexivity).
-
alu_case ltac:(exact (step_shiftimm_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hkn); cbn [edenot]; rewrite <- Hregs, zext64_lit; reflexivity).
-
alu_case ltac:(exact (step_op_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hkn); rewrite <- !Hregs; reflexivity).
-
alu_case ltac:(exact (step_opimm32_gen segs regs _ mem rom w rd rs1 imm Hf He Hd))
ltac:(rewrite mkAluw_denot; cbn [edenot]; rewrite <- Hregs, sext32_low32; reflexivity).
-
alu_case ltac:(exact (step_shiftimm32_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd))
ltac:(rewrite mkAluw_denot; cbn [edenot]; rewrite <- Hregs, zext32_low32; reflexivity).
-
alu_case ltac:(exact (step_op32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkAluw_denot; rewrite <- !Hregs; reflexivity).
-
injection Hs as <- <- <-.
eexists; split; [ exact (step_fence segs regs _ mem rom w _ _ _ _ _ Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
-
injection Hs as <- <- <-.
eexists; split; [ exact (step_fencei segs regs _ mem rom w _ _ _ Hf He Hd) |].
eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
-
alu_case ltac:(exact (step_mul_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkMd_denot; rewrite <- !Hregs; reflexivity).
-
alu_case ltac:(exact (step_mul32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd))
ltac:(rewrite mkMdw_denot; rewrite <- !Hregs; reflexivity).
Qed.

End StepSound.
Section FPGEN4.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma sidecond_eqb_eq : forall x y, sidecond_eqb x y = true -> x = y.
Proof.
intros x y H. destruct x, y; cbn [sidecond_eqb] in H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
| H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
end; subst; reflexivity.
Qed.

#[using="Type"] Lemma sc_mem_In : forall x l, sc_mem x l = true -> In x l.
Proof.
induction l as [|y t IH]; cbn [sc_mem]; intros H; [discriminate|].
apply orb_prop in H as [H|H].
- left. symmetry. apply sidecond_eqb_eq. exact H.
- right. apply IH. exact H.
Qed.

#[using="Type"] Lemma sc_add_denot : forall segs base E news acc,
scs_denot segs base E (sc_add news acc) ->
scs_denot segs base E news /\ scs_denot segs base E acc.
Proof.
intros segs base E news. induction news as [|x t IH]; intros acc H; cbn [sc_add] in H.
- split; [constructor | exact H].
- destruct (sc_mem x acc) eqn:Hm.
+ destruct (IH acc H) as [Ht Hacc]. split; [|exact Hacc].
constructor; [|exact Ht].
apply sc_mem_In in Hm. unfold scs_denot in Hacc. rewrite Forall_forall in Hacc. apply Hacc. exact Hm.
+ destruct (IH (x :: acc) H) as [Ht Hxa]. apply scs_denot_cons in Hxa as [Hx Hacc].
split; [constructor; assumption | exact Hacc].
Qed.

Section ExecSound.
Variable segs : list Segment.

#[using="Type"] Lemma sym_exec_acc : forall fuel first stops scr ss acc E base,
match sym_exec segs fuel first stops scr ss acc with
| (ss', scs, scr') => scs_denot segs base E scs -> scs_denot segs base E acc
end.
Proof.
induction fuel as [|f IH]; intros first stops scr ss acc E base; cbn [sym_exec].
- intros H; exact H.
- destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [intros H; exact H|].
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|intros H; exact H].
destruct (is_ecall w); [intros H; exact H|].
destruct (decode_any w) as [[i sz]|]; [|intros H; exact H].
destruct (negb (Z.eqb sz 4)); [intros H; exact H|].
destruct (sym_step segs i ss scr) as [ss2 scs2 scr2|]; [|intros H; exact H].
specialize (IH false stops scr2 ss2 (sc_add scs2 acc) E base).
destruct (sym_exec segs f false stops scr2 ss2 (sc_add scs2 acc)) as [[ss' scs] scr'].
intros H. apply IH in H. apply sc_add_denot in H as [_ H]. exact H.
Qed.

#[using="Type"] Theorem sym_exec_sound : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
scs_denot segs base E scs ->
st_ok segs E base rom ss ms ->
exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof.
induction fuel as [|f IH]; intros first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
{ cbn in Hex. injection Hex as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
assert (Hstop : (ss, acc, scr) = (ss', scs, scr') ->
exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms').
{ intro HX. injection HX as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
cbn [sym_exec] in Hex.
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (Hstop Hex)|].
destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hstop Hex)].
destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
apply Z.eqb_eq in Hsz. subst sz.
destruct (sym_step segs i ss scr) as [ss2 scs2 scr2|] eqn:Hstep; [|exact (Hstop Hex)].
pose proof (sym_exec_acc f false stops scr2 ss2 (sc_add scs2 acc) E base) as Hacc.
rewrite Hex in Hacc. specialize (Hacc Hsc). apply sc_add_denot in Hacc as [Hsc2 _].
destruct (sym_step_sound segs E base rom ss ms i ss2 scs2 scr scr2 w Hf He Hd Hstep Hsc2 Hst)
as (msA & HstepA & HstA).
destruct (IH false stops scr2 ss2 (sc_add scs2 acc) ss' scs scr' E base rom msA Hex Hsc HstA)
as (msB & HmsB & HstB).
exists msB. split; [|exact HstB].
eapply mst_step; [ destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact HmsB ].
Qed.

#[using="Type"] Theorem sym_exec_ex : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
scs_denot segs base E scs ->
st_ok segs E base rom ss ms ->
exists R, regs_ok E (s_regs ss') R
/\ log_flat E (s_log ss')
/\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
destruct (sym_exec_sound fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
as (ms' & Hms & (R & Heq & Hregs & Hlf & _)).
exists R. split; [exact Hregs|]. split; [exact Hlf|]. rewrite <- Heq. exact Hms.
Qed.

End ExecSound.

#[using="Type"] Lemma wbytes_out : forall bs m (a x : word),
(bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
wbytes m a bs x = m x.
Proof.
intros bs m a x Hnw [H|H].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.

Section CarrySound.
Variable segs : list Segment.

#[using="Type"] Lemma kentry_ok_frame : forall E M (wa : saddr) w (V : word) K (ka : saddr) (kl : expr),
flat E wa (Z.of_nat w) ->
kentry_ok segs E M K ->
match K with
| KWord a w' _ => ka = a /\ kl = elen w' /\ (w' <= 8)%nat
| KZero a n => ka = a /\ kl = n
| KBlob a n _ => ka = a /\ kl = n
| KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
| KAlign _ _ => True
| KRange _ _ _ => True
| KWr _ _ => True
| KDisj _ _ _ _ => True
end ->
((estart E wa + Z.of_nat w <= estart E ka)%Z \/ (estart E ka + elenZ E kl <= estart E wa)%Z) ->
kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K.
Proof.
intros E M wa w V K ka kl Hfw HK Hshape Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2]; cbn [kentry_ok] in *;
[ | | | | exact HK | exact HK
| destruct HK as [Hf0 Hs0]; split; [exact Hf0|]; intros d m Hd Hm;
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]
| exact HK ].
- destruct Hshape as (-> & -> & Hw8). destruct HK as (Hkw8 & Hfk & Hrd). split; [exact Hkw8|]. split; [exact Hfk|].
rewrite elenZ_elen in Hdis by exact Hw8.
rewrite rdn_wbytes_out; [exact Hrd | | |].
+ rewrite length_N_to_le_bytes, Huw, (flat_u E _ _ Hfk). lia.
+ rewrite (flat_u E _ _ Hfk). destruct Hfk as (?&?&?&?). lia.
+ rewrite length_N_to_le_bytes, Huw. lia.
- destruct Hshape as (-> & ->). destruct HK as [Hfk Hz]. split; [exact Hfk|].
intros i Hi. rewrite wbytes_out; [apply Hz; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
- destruct Hshape as (-> & ->). destruct HK as (Hfk & Hlen & Hb). split; [exact Hfk|]. split; [exact Hlen|].
intros i Hi. rewrite wbytes_out; [apply Hb; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. destruct Hfk as (?&?&?&?). rewrite u_small by lia. lia.
- destruct Hshape as (-> & -> & Hsz). destruct HK as (Hlo & Hhi & Hnone). split; [exact Hlo|]. split; [exact Hhi|].
intros i Hi. rewrite estart_lit0, elenZ_lit in Hdis.
rewrite wbytes_out; [apply Hnone; exact Hi | rewrite length_N_to_le_bytes, Huw; lia |].
rewrite length_N_to_le_bytes, Huw. rewrite u_small by lia.
assert ((hi - lo) mod 2 ^ 64 = hi - lo)%Z by (apply Z.mod_small; lia). lia.
Qed.

#[using="Type"] Lemma Forall_app_intro : forall {A} (P : A -> Prop) l1 l2,
Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros. apply Forall_app. auto. Qed.

#[using="Type"] Lemma kzero_piece : forall E M (wb : expr) (wk : Z) w (V : word) (kk l0 i0 len : Z),
flat E (SA wb wk) (Z.of_nat w) ->
kentry_ok segs E M (KZero (SA wb kk) (ELit l0)) ->
(0 <= i0)%Z -> (0 < len)%Z -> (i0 + len <= l0 mod 2 ^ 64)%Z ->
((kk + i0 + len <= wk)%Z \/ (wk + Z.of_nat w <= kk + i0)%Z) ->
kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
(KZero (SA wb (kk + i0)) (ELit len)).
Proof.
intros E M wb wk w V kk l0 i0 len Hfw [Hfk Hz] Hi0 Hlen Hil Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
rewrite elenZ_lit in Hfk, Hz. cbn [kentry_ok]. rewrite elenZ_lit.
unfold flat, estart in *; cbn [a_base a_off] in *.
destruct Hfk as (Hk1 & Hk2 & Hk3 & Hk4).
pose proof (Z.mod_pos_bound l0 (2 ^ 64) ltac:(lia)) as Hl.
rewrite (Z.mod_small len) by lia.
split; [lia|].
intros i Hi.
rewrite wbytes_out.
- replace (bv_unsigned (edenot E wb) + (kk + i0) + i)%Z
with (bv_unsigned (edenot E wb) + kk + (i0 + i))%Z by lia.
apply Hz. lia.
- rewrite length_N_to_le_bytes, Huw. lia.
- rewrite length_N_to_le_bytes, Huw. rewrite u_small by lia. lia.
Qed.

#[using="Type"] Lemma kimg_piece : forall E M (wa : saddr) w (V : word) (lo hi lo' hi' : Z),
flat E wa (Z.of_nat w) ->
kentry_ok segs E M (KImg lo hi) ->
(lo <= lo')%Z -> (hi' <= hi)%Z ->
((hi' <= estart E wa)%Z \/ (estart E wa + Z.of_nat w <= lo')%Z) ->
kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) (KImg lo' hi').
Proof.
intros E M wa w V lo hi lo' hi' Hfw (Hlo & Hhi & Hnone) H1 H2 Hdis.
pose proof (flat_u E _ _ Hfw) as Huw. destruct Hfw as (Hw1 & Hw2 & Hw3 & Hw4).
cbn [kentry_ok]. split; [lia|]. split; [lia|].
intros i Hi. rewrite wbytes_out.
- apply Hnone. lia.
- rewrite length_N_to_le_bytes, Huw. lia.
- rewrite length_N_to_le_bytes, Huw. rewrite u_small by lia. lia.
Qed.

#[using="Type"] Lemma Forall_one : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros. constructor; [assumption | constructor]. Qed.

#[using="Type"] Lemma prune1_sound : forall E (anybase : word -> option byte) M0 allkn M wa w V K hints kept scs hs',
prune1 allkn wa w K hints = (kept, scs, hs') ->
know_ok segs E M0 allkn ->
(w <= 8)%nat ->
flat E wa (Z.of_nat w) ->
kentry_ok segs E M K ->
match K with KWord _ w' _ => (w' <= 8)%nat | _ => True end ->
scs_denot segs anybase E scs ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept.
Proof.
intros E anyb M0 allkn M wa w V K hints kept scs hs' Hp Hall Hw8 Hfw HK Hkw Hscs.
pose proof (flat_u E _ _ Hfw) as Huw.
assert (Hfw' := Hfw). destruct Hfw' as (Hw1 & Hw2 & Hw3 & Hw4).
unfold prune1 in Hp.
assert (Hdiff : forall ka kl,
(let apart := match kl with
| ELit l => ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64)%Z
| _ => false
end in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end) = (kept, scs, hs') ->
match K with
| KWord a w' _ => ka = a /\ kl = elen w' /\ (w' <= 8)%nat
| KZero a n => ka = a /\ kl = n
| KBlob a n _ => ka = a /\ kl = n
| KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
| KAlign _ _ => True
| KRange _ _ _ => True
| KWr _ _ => True
| KDisj _ _ _ _ => True
end ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept).
{ intros ka kl Hm Hshape. cbv zeta in Hm.
assert (Hkl : forall l, kl = ELit l ->
ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64) = true ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) [K]).
{ intros l -> Hap. apply Forall_one.
pose proof (ranges_apart_sound segs E M0 allkn _ _ _ _ _ _ Hall Hap) as Hdis.
eapply kentry_ok_frame; eauto;
rewrite elenZ_lit; destruct wa, ka; cbn [a_base a_off] in *; exact Hdis. }
destruct kl as [l| | | | | | |];
[ destruct (ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (a_base ka) (a_off ka) (l mod 2 ^ 64)) eqn:Hap;
[ injection Hm as <- <- <-; apply (Hkl l eq_refl Hap) | ]
| .. ];
(destruct hints as [|[|] hs]; try (injection Hm as <- <- <-);
[ constructor | | constructor ];
(apply scs_denot_cons in Hscs as [Hd _]; cbn [sc_denot] in Hd;
destruct Hd as (_ & _ & Hd); rewrite elenZ_elen in Hd by exact Hw8;
constructor; [ eapply kentry_ok_frame; eauto | constructor ])). }

destruct K as [[kb kk] w' v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2].
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
5: { injection Hp as <- <- <-. apply Forall_one. cbn [kentry_ok] in HK |- *.
destruct HK as [Hf0 Hs0]. split; [exact Hf0|]. intros d m Hd Hm.
eapply store_ok_mono; [apply wbytes_grows | apply Hs0; assumption]. }
5: { injection Hp as <- <- <-. apply Forall_one. exact HK. }
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb; [|eapply Hdiff; [exact Hp | cbn; auto]].
apply expr_eqb_eq in Heqb.
destruct (Z.leb (kk + Z.of_nat w') (a_off wa) || Z.leb (a_off wa + Z.of_nat w) kk)%bool eqn:Hd;
injection Hp as <- <- <-; [|constructor].
apply Forall_one.
eapply (kentry_ok_frame E M wa w V _ (SA kb kk) (elen w') Hfw HK); [cbn; auto|].
rewrite elenZ_elen by exact Hkw. unfold estart. cbn [a_base a_off]. subst kb.
destruct wa as [wb wk]; cbn [a_base a_off] in *.
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb; [|eapply Hdiff; [exact Hp | cbn; auto]].
apply expr_eqb_eq in Heqb.
destruct wa as [wb wk]; cbn [a_base a_off] in *. subst kb.
destruct n as [l0| | | | | | |];
[
injection Hp as <- <- <-;
assert (HK' := HK); destruct HK' as [Hfk _]; rewrite elenZ_lit in Hfk;
destruct Hfk as (Hk1 & Hk2 & Hk3 & Hk4); unfold estart in Hk1, Hk2, Hk4; cbn [a_base a_off] in Hk1, Hk2, Hk4;
lazymatch goal with |- Forall ?P (?A ++ ?B) =>
assert (H1 : Forall P A);
[ destruct (Z.ltb kk (Z.min wk (kk + l0 mod 2 ^ 64))) eqn:Hlt; [|constructor];
apply Z.ltb_lt in Hlt; apply Forall_one;
replace kk with (kk + 0)%Z at 1 by lia;
eapply kzero_piece; [exact Hfw | exact HK | lia | lia | lia | lia]
| assert (H2 : Forall P B);
[ destruct (Z.ltb (Z.max kk (wk + Z.of_nat w)) (kk + l0 mod 2 ^ 64)) eqn:Hlt; [|constructor];
apply Z.ltb_lt in Hlt; apply Forall_one;
replace (Z.max kk (wk + Z.of_nat w)) with (kk + (Z.max kk (wk + Z.of_nat w) - kk))%Z at 1 by lia;
eapply kzero_piece; [exact Hfw | exact HK | lia | lia | lia | lia]
| exact (Forall_app_intro _ _ _ H1 H2) ] ]
end
| .. ];
(destruct (Z.leb (wk + Z.of_nat w) kk) eqn:Hle; injection Hp as <- <- <-; [|constructor];
apply Z.leb_le in Hle; apply Forall_one;
eapply (kentry_ok_frame E M (SA wb wk) w V _ (SA wb kk) _ Hfw HK); [cbn; auto|];
unfold estart; cbn [a_base a_off]; lia).
-
destruct (expr_eqb kb (a_base wa)) eqn:Heqb; [|eapply Hdiff; [exact Hp | cbn; auto]].
apply expr_eqb_eq in Heqb.
destruct wa as [wb wk]; cbn [a_base a_off] in *. subst kb.
destruct n as [l0| | | | | | |];
[ destruct (Z.leb (kk + l0 mod 2 ^ 64) wk || Z.leb (wk + Z.of_nat w) kk)%bool eqn:Hd;
injection Hp as <- <- <-; [|constructor];
apply Forall_one;
eapply (kentry_ok_frame E M (SA wb wk) w V _ (SA wb kk) (ELit l0) Hfw HK); [cbn; auto|];
rewrite elenZ_lit; unfold estart; cbn [a_base a_off];
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia
| .. ];
(destruct (Z.leb (wk + Z.of_nat w) kk) eqn:Hle; injection Hp as <- <- <-; [|constructor];
apply Z.leb_le in Hle; apply Forall_one;
eapply (kentry_ok_frame E M (SA wb wk) w V _ (SA wb kk) _ Hfw HK); [cbn; auto|];
unfold estart; cbn [a_base a_off]; lia).
-
assert (Hdb : (if (hi - lo <? 2 ^ 64)%Z
then (if ranges_apart allkn (a_base wa) (a_off wa) (Z.of_nat w) (ELit 0) lo ((hi - lo) mod 2 ^ 64)%Z
then ([KImg lo hi], [], hints) else
match hints with
| true :: hs => ([KImg lo hi], [SCDisj wa (elen w) (SA (ELit 0) lo) (ELit (hi - lo))], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end)
else ([], [], hints)) = (kept, scs, hs') ->
Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept).
{ intros Hq. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt.
- apply Z.ltb_lt in Hlt. eapply Hdiff; [exact Hq | cbn; auto].
- injection Hq as <- <- <-. constructor. }
destruct (a_base wa) as [z| | | | | | |] eqn:Hwb; try (apply Hdb; exact Hp).
destruct z; try (apply Hdb; exact Hp).
injection Hp as <- <- <-.
assert (Hws : estart E wa = a_off wa).
{ unfold estart. rewrite Hwb. cbn [edenot]. rewrite u_lit0. lia. }
assert (HK' := HK). destruct HK' as (Hlo & Hhi & _).
lazymatch goal with |- Forall ?P (?A ++ ?B) =>
assert (H1 : Forall P A);
[ destruct (Z.ltb lo (Z.min (a_off wa) hi)) eqn:Hlt; [|constructor]; apply Z.ltb_lt in Hlt;
apply Forall_one; eapply kimg_piece; [exact Hfw | exact HK | lia | lia | lia]
| assert (H2 : Forall P B);
[ destruct (Z.ltb (Z.max lo (a_off wa + Z.of_nat w)) hi) eqn:Hlt; [|constructor]; apply Z.ltb_lt in Hlt;
apply Forall_one; eapply kimg_piece; [exact Hfw | exact HK | lia | lia | lia]
| exact (Forall_app_intro _ _ _ H1 H2) ] ]
end.
Qed.

Fixpoint kn_words_le8 (kn : list kentry) : Prop :=
match kn with
| [] => True
| KWord _ w' _ :: r => (w' <= 8)%nat /\ kn_words_le8 r
| _ :: r => kn_words_le8 r
end.

#[using="Type"] Lemma know_ok_words_le8 : forall E M kn, know_ok segs E M kn -> kn_words_le8 kn.
Proof.
intros E M kn H. induction kn as [|K r IH]; [exact I|].
apply Forall_cons_iff in H as [HK Hr].
destruct K as [a w' v| | | | | | |]; cbn [kn_words_le8]; auto.
cbn [kentry_ok] in HK. split; [exact (proj1 HK) | apply IH; exact Hr].
Qed.

#[using="Type"] Lemma prune_sound : forall E (anybase : word -> option byte) M0 allkn M wa w V kn hints kn' scs hs',
prune allkn wa w kn hints = (kn', scs, hs') ->
know_ok segs E M0 allkn ->
(w <= 8)%nat -> flat E wa (Z.of_nat w) ->
know_ok segs E M kn ->
scs_denot segs anybase E scs ->
know_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) kn'.
Proof.
intros E anyb M0 allkn M wa w V kn. induction kn as [|K rest IH]; intros hints kn' scs hs' Hp Hall Hw8 Hfw Hkn Hscs.
- cbn in Hp. injection Hp as <- <- <-. constructor.
- cbn [prune] in Hp.
destruct (prune1 allkn wa w K hints) as [[kept scs1] hs1] eqn:Hp1.
destruct (prune allkn wa w rest hs1) as [[r scs2] hs2] eqn:Hpr.
injection Hp as <- <- <-.
apply Forall_cons_iff in Hkn as [HK Hrest].
apply scs_denot_app in Hscs as [Hs1 Hs2].
apply Forall_app. split.
+ eapply prune1_sound; eauto.
destruct K as [a w' v| | | | | | |]; try exact I. exact (proj1 HK).
+ eapply IH; eauto.
Qed.

#[using="Type"] Lemma carry_sound : forall E (anybase : word -> option byte) base log kn hints kn' scs hs',
carry log kn hints = (kn', scs, hs') ->
log_flat E log -> know_ok segs E base kn -> scs_denot segs anybase E scs ->
know_ok segs E (mem_denot E base log) kn'.
Proof.
intros E anyb base log. induction log as [|[a w v] older IH]; intros kn hints kn' scs hs' Hc Hlf Hkn Hscs.
- cbn in Hc. injection Hc as <- <- <-. exact Hkn.
- cbn [carry] in Hc. cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
destruct (carry older kn hints) as [[kn1 scs1] hs1] eqn:Hco.
destruct (prune kn1 a w kn1 hs1) as [[kn2 scs2] hs2] eqn:Hpr.
injection Hc as <- <- <-.
apply scs_denot_app in Hscs as [Hs1 Hs2].
cbn [mem_denot].
constructor.
+ cbn [kentry_ok]. split; [exact Hw8|]. split; [exact Hfa|].
pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E base older) (adenot E a)) as Hh.
rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite (flat_u E _ _ Hfa).
destruct Hfa as (?&?&?&?). lia.
+ eapply prune_sound; eauto.
Qed.

End CarrySound.
End FPGEN4.

End SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5.

Import ListNotations.

Lemma evs_kill_free_W : forall ch s, evs_kill_free (W ch s).
Proof. intros ch s. unfold W. apply evs_kill_free_writes. Qed.

Lemma kill_free_die : forall msg fs, kill_free (t_die msg fs).
Proof.
intros msg fs. unfold t_die. apply kill_free_emit; [apply evs_kill_free_W | apply kill_free_exit].
Qed.

Lemma kill_free_body : forall data fs, kill_free (t_body data fs).
Proof.
intros data fs. unfold t_body.
destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply kill_free_die|].
destruct (length data <? 6)%nat; [apply kill_free_die|].
cbv zeta.
destruct (length data <? 6 + _)%nat; [apply kill_free_die|].
destruct (length data - 6 - _)%nat;
(apply kill_free_emit; [apply evs_kill_free_W | apply kill_free_exit]).
Qed.

Lemma kill_free_opened : forall data fs, kill_free (t_opened data fs).
Proof. intros. unfold t_opened. apply kill_free_body. Qed.

Lemma kill_free_opened_dir : forall path fs, kill_free (t_opened_dir path fs).
Proof. intros. unfold t_opened_dir. apply kill_free_die. Qed.

Theorem spec_kill_free : forall argv fs, kill_free (spec argv fs).
Proof.
intros argv fs. unfold spec.
destruct argv as [|a0 [|path [|x l]]]; try apply kill_free_die.
destruct (4096 <=? length path)%nat; [apply kill_free_die|].
destruct (list_byte_eqb path []); [apply kill_free_die|].
destruct (list_byte_eqb path dot_path).
- apply kill_free_alt2; [apply kill_free_die | apply kill_free_opened_dir].
- destruct (fs_lookup fs path); [| apply kill_free_die].
apply kill_free_alt2; [apply kill_free_die | apply kill_free_opened].
Qed.

Corollary spec_kill_free_inp : forall inp : ProcInput,
kill_free (spec (in_argv inp) (in_fs inp)).
Proof. intros inp. apply spec_kill_free. Qed.
