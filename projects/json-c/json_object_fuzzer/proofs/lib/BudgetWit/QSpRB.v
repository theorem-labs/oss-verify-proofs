(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QSpR.v: rz_wall and the writev lemmas of module Mq0, over BudgetWit.QRjHB.realizes; the writev node takes its budget check. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise m_channel_reader model = true on writev_outcome and the rz_writev lemmas; RomBase.sys_rob at the writev system-call nodes, from RomWrite.writev_rob). *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require EdBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomBase RomWrite RomWritev.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwNp Qpox QsV0 QsRG Qnhz Qrxj QSjk QRjH QBxa Qn1e Q9ox.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB QBxaB Q9oxB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QwNp Qpox QsV0 QsRG Qnhz.Mq0 QsRG.Mq0 Qrxj QSjk.Mq0 QRjH QBxa.Mq4 Qn1e QBxa.Mq0 Q9ox.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import QRjHB QBxaB.Mq4 Q9oxB.Mq0.
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
cbn [negb]. rewrite ?app_nil_r.
first [reflexivity
| lazymatch goal with |- context [read_iovec_entry ?m ?a] => destruct (read_iovec_entry m a) end;
  rewrite ?app_nil_r; reflexivity].
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
(* carried for writev_chan_outcome's #38 SIGPIPE arm (75d69e00 ReadWrite.v:2865); the six
   rz_* lemmas below already take this premise in this exact form (:281 and after). *)
m_channel_reader model = true ->
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
intros ms x8 model fd iov iovs bss Hrom Hfd Hcr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Ht30 CA.
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
- exact Hcr.
- rewrite Hcnt32, in_mem_si. exact (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
- unfold MAX_RW_COUNT. lia.
- rewrite in_mem_si. exact Hg.
- lia.
Qed.

Lemma rz_writev_pending : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
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
  intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Ht30 Hk.
  assert (Hrob : RomBase.sys_rob segs (mkCfg ms model)).
  { assert (Hc32 : iovcnt32 (ms_gpr ms 2) = Z_to_bv 64 (Z.of_nat (length iovs))).
    { rewrite H2. unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
    apply (RomWrite.writev_rob segs ms model x8 (Z_to_bv 64 fd) iovs bs Hsvc Hno).
    - rewrite H0, fd32_id by (rewrite u64_lit; lia). exact Hfd.
    - rewrite Hc32, H1. exact (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
    - unfold cap_iovecs. rewrite cap_iovecs_id by (unfold MAX_RW_COUNT; lia).
      exact (gather_of_bufs ms iovs bss Hrom Hbufs). }
  (* the outcomes of the call, by the spec ([writev_outcome]), as main's proof *)
  destruct (writev_outcome ms x8 model fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
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
  2:{ exact Hrob. }
  2:{ exact (budget_ok_num ms model x8 66 Hsvc Hno eq_refl). }
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

Lemma rz_writev2 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
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
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma rz_writev1 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
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
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma rz_writev2_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
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
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
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
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Lemma rz_writev2_ch : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
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

Lemma rz_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
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
rewrite (access_okb_of_le iov 16) by lia. cbn [negb].
pose proof Harr as (Hb1r & Hn1r & _ & _). unfold iovec_entry_accesses.
rewrite (read_u64_rdn ms iov b1 eq_refl Hb1r).
rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
rewrite (read_u64_rdn ms _ (Z_to_bv 64 0) eq_refl Hn1r). reflexivity. }
(* LPS 727298f3: [RomBase.sys_rob] at the node: the call reads only the iovec array (its buffer is empty) *)
assert (Hrob : RomBase.sys_rob segs (mkCfg ms model)).
{ apply (RomWrite.writev_rob segs ms model (getr regs 17) (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] [] eq_refl Hno).
  - unfold ms; rewrite ms_gpr_epend0, H10, fd32_id by (rewrite u64_lit; lia). exact Hfd.
  - unfold ms; rewrite ms_gpr_epend1, ms_gpr_epend2, H11, H12.
    change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). exact Himp.
  - unfold cap_iovecs; cbn [cap_iovecs_aux iovs_total].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
    reflexivity. }
eapply (rz_ret_only_copyins_silent segs ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
[exact Hh | reflexivity | exact (nalloc_lit (getr regs 17) 66 Hno eq_refl) | | exact Hh | exact Hlazy | exact Hrob
| unfold ms; rewrite adv_set_epend; exact Hc].
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS QMz4 Q6q3.

(* From module Mq2 of QSpR.v: rz_exit_at, which the exit walk of Q1oC.v uses. *)
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
Import QRjHB Q9oxB.Mq0.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.
Section WithSegs.
Variable segs : list Segment.

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

End WithSegs.
End FPGEN1.
End Mq2.
