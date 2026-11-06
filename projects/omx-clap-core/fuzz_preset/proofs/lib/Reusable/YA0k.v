(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0k.v, with its module paths changed; relocated to fuzz_preset asan-ubsan (pin f8f98a95bc52), map sha256 40ba3a40933d, checker port_addr_check.py 5033540ba83b; 1 numeral(s) of it stay cgif_file_fuzzer's (UNMAPPED / NOT RELOCATED in dry run sha256 d62a4bb8656b). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0n YK04 YA0i YA0m.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section a.
Context {fx : FPState}.
Section b.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
Lemma ledgers_with_fds_fs : forall f g (m : Model),
m_vmmaps (with_fds f (with_fs g m)) = m_vmmaps m /\ m_vm_lazy (with_fds f (with_fs g m)) = m_vm_lazy m
/\ m_vm_materialized (with_fds f (with_fs g m)) = m_vm_materialized m.
Proof. intros f g m. repeat split; reflexivity. Qed.
Lemma writev_file_chk_canon : forall regs pc mem rom model fd p off data iovs bs,
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + iovs_total iovs <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins
(writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (length bs))
eff (len_word bs)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
[].
Proof.
intros regs pc mem rom model fd p off data iovs bs Hno Hlk H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hfs Hpos Hgap eff.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
assert (Hiov : (IOV_MAX <? bv_unsigned (getr regs 12))%Z = false) by (apply Z.ltb_ge; lia).
assert (E32 : iovcnt32 (getr regs 12) = getr regs 12)
by (apply iovcnt32_small; unfold IOV_MAX in Hmax; lia).
rewrite E32 in Hcnt, Himp.
assert (Himp' : import_iovecs (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) = ImpOk iovs).
{ unfold import_iovecs.
destruct (bv_eqb (getr regs 12) (Z_to_bv 64 1)) eqn:E1.
- apply bv_eqb_eq in E1. rewrite E1 in Himp, Hiok.
change (16 * bv_unsigned (Z_to_bv 64 1))%Z with 16%Z in Hiok. rewrite Hiok. cbn [negb].
change (word_to_nat (Z_to_bv 64 1)) with 1%nat in Himp. cbn [copy_iovecs_aux] in Himp.
destruct (read_iovec_entry (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)) as [base len| |] eqn:Er;
try discriminate.
injection Himp as <-. cbn [iovs_access_okb forallb fst snd] in Hbok. rewrite andb_true_r in Hbok.
cbn [iovs_total] in Htot.
rewrite Z.min_l by lia. rewrite Hbok. reflexivity.
- destruct (bv_eqb (getr regs 12) (Z_to_bv 64 0)) eqn:E0.
+ apply bv_eqb_eq in E0. rewrite E0 in Hcnt. discriminate.
+ rewrite Hiov, Hiok. cbn [negb]. rewrite Himp, Hbok. reflexivity. }
rewrite chk66 by exact Hno. rewrite Hfd, H32. unfold check_writev.
rewrite ?E32, Hlk, si_mem, Himp'.
rewrite cap_iovecs_id by lia. cbv zeta.
replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
unfold rw_pos_einvalb. replace (2 ^ 63 - 1 <? bv_unsigned off + iovs_total iovs)%Z with false by (symmetry; apply Z.ltb_ge; lia).
unfold writev_gathered. rewrite cap_iovecs_id by lia. rewrite (gather_prefix_full _ _ _ Hg).
replace (Nat.eqb (length bs) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
rewrite Hfs. rewrite (file_gap_in_range data off bs Hgap).
assert (Herr : addr_is_error_b (len_word bs) = false).
{ unfold addr_is_error_b. apply Z.ltb_ge. rewrite len_word_unsigned; unfold two_pow_64; lia. }
rewrite Herr. unfold writev_copyins. rewrite ?E32. reflexivity.
Qed.
Lemma node_writev_file_lazy : forall regs pc mem rom model fd p off data iovs bs,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + iovs_total iovs <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (length bs)) ->
let m' := with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model) in
let accs := writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (length bs) in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) mem rom) (materialized_succ m' accs))
/\ AI segs H A (materialized_succ m' accs) /\ same_but_materialized m' (materialized_succ m' accs).
Proof.
intros regs pc mem rom model fd p off data iovs bs HAI Hno Hlk H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hfs Hpos Hgap Hav m' accs.
apply (node_ret_only_copyins_lazy segs H A regs pc mem rom model accs (len_word bs) m' [] HAI).
- intro eff. exact (writev_file_chk_canon regs pc mem rom model fd p off data iovs bs Hno Hlk H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hfs Hpos Hgap eff).
- subst m'. rewrite with_fds_halted, with_fs_halted. exact (AI_halted segs H A model HAI).
- subst m'. apply ledgers_with_fds_fs.
- exact Hav.
Qed.
Lemma node_writev_file2_lazy : forall regs pc mem rom model fd p off data (b0 l0 b1 l1 : word) bs0 bs1,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 2 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
access_okb (getr regs 11) 32 = true ->
access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
(1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT)%Z ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + (bv_unsigned l0 + bv_unsigned l1) <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) [(b0, l0); (b1, l1)] (length (bs0 ++ bs1))) ->
let bs := bs0 ++ bs1 in
let m' := with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model) in
let accs := writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) [(b0, l0); (b1, l1)] (length bs) in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) mem rom) (materialized_succ m' accs))
/\ AI segs H A (materialized_succ m' accs) /\ same_but_materialized m' (materialized_succ m' accs).
Proof.
intros regs pc mem rom model fd p off data b0 l0 b1 l1 bs0 bs1
HAI Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hfs Hpos Hgap Hav.
rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
unfold MAX_RW_COUNT in Htot.
apply (node_writev_file_lazy regs pc mem rom model fd p off data [(b0, l0); (b1, l1)] (bs0 ++ bs1) HAI Hno Hlk H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
apply copy_iovecs_2; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hfs.
- cbn [iovs_total]. lia.
- exact Hgap.
- exact Hav.
Qed.
Lemma node_writev_file1_lazy : forall regs pc mem rom model fd p off data (b0 l0 : word) bs0,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 (bv_unsigned l0) = true ->
(1 <= bv_unsigned l0 <= MAX_RW_COUNT)%Z ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + bv_unsigned l0 <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) [(b0, l0)] (length bs0)) ->
let m' := with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs0)))
(with_fs (fs_set (m_fs model) p (file_write data off bs0)) model) in
let accs := writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) [(b0, l0)] (length bs0) in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (len_word bs0)) (v_addi pc 4) mem rom) (materialized_succ m' accs))
/\ AI segs H A (materialized_succ m' accs) /\ same_but_materialized m' (materialized_succ m' accs).
Proof.
intros regs pc mem rom model fd p off data b0 l0 bs0
HAI Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hfs Hpos Hgap Hav.
rewrite <- read_bytes_map_read_byte in Hbs0.
pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0).
unfold MAX_RW_COUNT in Htot.
apply (node_writev_file_lazy regs pc mem rom model fd p off data [(b0, l0)] bs0 HAI Hno Hlk H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
apply copy_iovecs_1; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hfs.
- cbn [iovs_total]. lia.
- exact Hgap.
- exact Hav.
Qed.
End b.
End a.
