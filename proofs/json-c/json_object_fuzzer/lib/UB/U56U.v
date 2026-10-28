(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import ListNotations.
Open Scope Z_scope.

Definition ECALL_PC : Z := 0x60868.

Lemma ecall_fetch : fetch_word rsegs (Z_to_bv 64 ECALL_PC) = Some (Z_to_bv 32 0x73).
Proof. vm_compute. reflexivity. Qed.
Lemma ecall_is : is_ecall (Z_to_bv 32 0x73) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ecall_next : v_addi (Z_to_bv 64 ECALL_PC) 4 = Z_to_bv 64 0x6086c.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section GetR.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
Notation R := (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
#[using="Type"] Lemma getr_10 : getr R 10 = x10. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_11 : getr R 11 = x11. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_12 : getr R 12 = x12. Proof. reflexivity. Qed.
#[using="Type"] Lemma getr_17 : getr R 17 = x17. Proof. reflexivity. Qed.
#[using="Type"] Lemma regupd_10 : forall v, regupd R 10 v = QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. intros v. reflexivity. Qed.
End GetR.

Lemma cps_read_file :
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (K : TSet)
(fd : word) (p : list byte) (off : word) (data : list byte) (cnt : Z),
model_ok md ->
x17 = Z_to_bv 64 63 -> x10 = fd -> bv_unsigned fd < 2^32 ->
fd_lookup (m_fds md) fd = Some (FdFile p off) ->
fs_lookup (m_fs md) p = Some data ->
x12 = Z_to_bv 64 cnt -> 1 <= cnt <= 65536 ->
bv_unsigned x11 + cnt <= task_size_max ->
store_ok rsegs m x11 (Z.to_nat cnt) = true ->
(let bs := file_read data off (Z_to_bv 64 cnt) in
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (len_word bs) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x6086c) fc None (write_to_mem m x11 bs) (seg_rom rsegs))
(with_fds (fd_insert (m_fds md) fd (FdFile p (bv_add off (len_word bs)))) md)) K) ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 ECALL_PC) fc None m (seg_rom rsegs)) md) K.
Proof.
intros until cnt. intros [Hh Hl] H17 H10 Hfd Hlk Hfs H12 Hcnt Htask Hok HK. cbv zeta in HK. subst x10 x12 x17.
change (QEpW.MS ?R F (Z_to_bv 64 ECALL_PC) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 ECALL_PC) m (seg_rom rsegs)).
eapply (QSpR.Mq2.rz_read_file (fF:=F) (fC:=fc) rsegs _ _ m md _ fd p off data cnt K ecall_fetch ecall_is Hh Hl);
rewrite ?getr_10, ?getr_11, ?getr_12, ?getr_17, ?regupd_10; try eassumption; try lia; try reflexivity.
all: unfold access_ok_walk_max; try lia.
all: rewrite ecall_next, <- write_to_mem_wbytes;
match goal with |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?ro) ?mdl) _ =>
change (mkst R pc mm ro) with (QEpW.MS R F pc fc None mm ro) end; exact HK.
Qed.

Lemma cps_close :
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (K : TSet) (fd : word) (e : FdEntry),
model_ok md ->
x17 = Z_to_bv 64 57 -> x10 = fd -> bv_unsigned fd < 2^32 ->
fd_lookup (m_fds md) fd = Some e ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x6086c) fc None m (seg_rom rsegs))
(with_fds (fd_remove (m_fds md) fd) md)) K ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 ECALL_PC) fc None m (seg_rom rsegs)) md) K.
Proof.
intros until e. intros [Hh Hl] H17 H10 Hfd Hlk HK.
change (QEpW.MS ?R F (Z_to_bv 64 ECALL_PC) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 ECALL_PC) m (seg_rom rsegs)).
eapply (QSpR.Mq2.rz_close (fF:=F) (fC:=fc) rsegs _ _ m md _ fd e K ecall_fetch ecall_is Hh Hl);
rewrite ?getr_10, ?getr_11, ?getr_12, ?getr_17, ?regupd_10; try eassumption; try lia; try reflexivity.
all: rewrite ecall_next;
match goal with |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?ro) ?mdl) _ =>
change (mkst R pc mm ro) with (QEpW.MS R F pc fc None mm ro) end; exact HK.
Qed.

Definition READ_SYM : Z := 0x61520.

Lemma rw_cells_fill0 : forall (m : word -> option byte) a n junk bs,
rw_cells rsegs m a [CB n junk] -> (length bs <= n)%nat ->
rw_cells rsegs (write_to_mem m (wa a) bs) a [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
intros m a n junk bs RW LE. pose proof RW as [[WF BA] WR]. cbn in WF.
split; [split|].
- cbn. rewrite length_skipn. lia.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
pose proof (bytes_at_write_inside rsegs m a junk 0 bs BA ltac:(lia) ltac:(cbn; lia)) as BA'.
rewrite Z.add_0_r in BA'. unfold upd_bytes in BA'. cbn [firstn app Nat.add] in BA'. exact BA'.
- cbn [cells_size csize Nat.add]. cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in *.
replace (length bs + (n - length bs))%nat with n by lia. apply wr_at_write. exact WR.
Qed.

Lemma length_file_read_le : forall data off cnt, 0 <= cnt -> (length (file_read data off (Z_to_bv 64 cnt)) <= Z.to_nat cnt)%nat.
Proof.
intros data off cnt Hc. rewrite file_read_unguarded. rewrite length_firstn. unfold word_to_nat.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
pose proof (Z.mod_le cnt (2 ^ Z.of_N 64) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma read_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (K : TSet)
(p : list byte) (off : word) (data junk : list byte) (dst cnt lo : Z),
model_ok md ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
fd_lookup (m_fds md) (Z_to_bv 64 3) = Some (FdFile p off) ->
fs_lookup (m_fs md) p = Some data ->
1 <= cnt <= 65536 -> 0 < dst -> dst + cnt <= lo ->
rw_cells rsegs m dst [CB (Z.to_nat cnt) junk] ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
let bs := file_read data off (Z_to_bv 64 cnt) in
munch [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
stk rsegs m' lo (bv_unsigned sp) ->
rw_cells rsegs m' dst [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (len_word bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs))
(with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile p (bv_add off (len_word bs)))) md)) K) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READ_SYM) fc None m (seg_rom rsegs)) md) K.
Proof.
intros until lo. intros MOK -> -> -> Hfd Hfs Hcnt Hdst Hlo DST ST LOS SPH MI RA HK. cbv zeta in HK.
word_range sp SPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m) as MU.
apply rz_evt; [exact MOK|]. unfold READ_SYM.
carve_frame 16%nat ST.
do 10 step. step.
do 7 step.
apply evt_RZ_done.
pose proof (wr_at_store_ok rsegs m0 dst _ 0 (Z.to_nat cnt) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK.
rewrite Z.add_0_r in SOK.
eapply cps_read_file; [exact MOK| reflexivity| reflexivity| rewrite unsigned_lit by lia; lia| exact Hfd| exact Hfs| reflexivity| lia
| rewrite unsigned_lit by lia; unfold task_size_max; lia| exact SOK|].
cbv zeta. set (bs := file_read data off (Z_to_bv 64 cnt)).
pose proof (length_file_read_le data off cnt ltac:(lia)) as LENB. fold bs in LENB.
pose proof (wr_at_store_ok rsegs m0 dst _ 0 (length bs) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK2.
rewrite Z.add_0_r in SOK2.
pose proof (mem_inv_store rsegs m0 (wa dst) bs MI SOK2) as MI2.
assert (MU2 : munch [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m (write_to_mem m0 (wa dst) bs)).
{ apply munch_write; [exact MU| lia| lia| cbn [inside]; right; left; lia]. }
assert (MU1 : munch [(dst, dst + cnt)] m0 (write_to_mem m0 (wa dst) bs)).
{ apply munch_write; [apply munch_refl| lia| lia| cbn [inside]; left; lia]. }
pose proof (wmono_write rsegs m m0 (wa dst) bs WM) as WM2.
pose proof (wmono_write rsegs m0 m0 (wa dst) bs (wmono_refl rsegs m0)) as WM1.
pose proof (rw_cells_fill0 m0 dst (Z.to_nat cnt) junk bs DST LENB) as DST2.
pose proof (stk_write rsegs m0 lo _ dst bs ST ltac:(lia) ltac:(lia)) as ST2.
assert (FR2 : rw_cells rsegs (write_to_mem m0 (wa dst) bs) (bv_unsigned sp + -16) [CB 8 (firstn 8 junk0); C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia| exact I]. }
change (write_to_mem m0 (Z_to_bv 64 dst) bs) with (write_to_mem m0 (wa dst) bs).
clear SOK SOK2 MU MU1 WM WM1 DST ST FR MI.
set (m2 := write_to_mem m0 (wa dst) bs) in *. clearbody m2.
reenter MOK.
step.
do 5 step.
unfold len_word. step. if_truex.
step.
apply evt_RZ_done. release_frame FR2 ST2 (bv_unsigned sp).
eapply HK; [exact MU2| exact WM2| exact MI2| exact ST2| exact DST2].
Qed.

Definition CLOSE_SYM : Z := 0x614c0.

Lemma close_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (K : TSet)
(e : FdEntry) (lo : Z),
model_ok md ->
a0 = Z_to_bv 64 3 ->
fd_lookup (m_fds md) (Z_to_bv 64 3) = Some e ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
stk rsegs m' lo (bv_unsigned sp) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs))
(with_fds (fd_remove (m_fds md) (Z_to_bv 64 3)) md)) K) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 CLOSE_SYM) fc None m (seg_rom rsegs)) md) K.
Proof.
intros until lo. intros MOK -> Hfd ST LOS SPH MI RA HK.
word_range sp SPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold CLOSE_SYM.
carve_frame 16%nat ST.
do 3 step. step.
do 8 step. step.
do 7 step.
apply evt_RZ_done.
eapply cps_close; [exact MOK| reflexivity| reflexivity| rewrite unsigned_lit by lia; lia| exact Hfd|].
reenter MOK.
step.
do 5 step. step.
do 2 step. step. if_truex. step.
do 3 step. step.
apply evt_RZ_done. release_frame FR ST (bv_unsigned sp).
eapply HK; [exact MU| exact WM| exact MI| exact ST].
Qed.

Lemma cps_read_dir :
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (K : TSet) (fd : word) (cnt : Z),
model_ok md ->
x17 = Z_to_bv 64 63 -> x10 = fd -> bv_unsigned fd < 2^32 ->
fd_lookup (m_fds md) fd = Some FdDir ->
x12 = Z_to_bv 64 cnt -> 1 <= cnt <= 65536 ->
bv_unsigned x11 + cnt <= task_size_max ->
store_ok rsegs m x11 (Z.to_nat cnt) = true ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (errno_ret EISDIR) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x6086c) fc None m (seg_rom rsegs)) md) K ->
realizes rsegs (mkCfg (QEpW.MS (QWxq.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 ECALL_PC) fc None m (seg_rom rsegs)) md) K.
Proof.
intros until cnt. intros [Hh Hl] H17 H10 Hfd Hlk H12 Hcnt Htask Hok HK. subst x10 x12 x17.
change (QEpW.MS ?R F (Z_to_bv 64 ECALL_PC) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 ECALL_PC) m (seg_rom rsegs)).
eapply (QuJV.Mq2.rz_read_dir_mapped (fF:=F) (fC:=fc) rsegs _ _ m md _ fd cnt K ecall_fetch ecall_is Hh Hl);
rewrite ?getr_10, ?getr_11, ?getr_12, ?getr_17, ?regupd_10; try eassumption; try lia; try reflexivity.
all: rewrite ecall_next;
match goal with |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?ro) ?mdl) _ =>
change (mkst R pc mm ro) with (QEpW.MS R F pc fc None mm ro) end; exact HK.
Qed.

Lemma read_dir_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (K : TSet)
(dst cnt lo : Z) (errv : word),
model_ok md ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
fd_lookup (m_fds md) (Z_to_bv 64 3) = Some FdDir ->
1 <= cnt <= 65536 -> 0 < dst -> dst + cnt <= lo -> 0x99000 <= lo ->
(exists junk, rw_cells rsegs m dst [CB (Z.to_nat cnt) junk]) ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] -> 0x66000 <= bv_unsigned tp - 164 -> bv_unsigned tp <= 0x99000 ->
mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 160)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
stk rsegs m' lo (bv_unsigned sp) ->
rw_cells rsegs m' (bv_unsigned tp - 164) [C4 (Z_to_bv 64 EISDIR)] ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)) md) K) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READ_SYM) fc None m (seg_rom rsegs)) md) K.
Proof.
intros until errv. intros MOK -> -> -> Hfd Hcnt Hdst Hlo Hlo2 (junk & DST) ST LOS SPH ERR TPL TPH MI RA HK.
word_range sp SPR. word_range tp TPR.
replace (bv_unsigned tp - 164) with (bv_unsigned tp + -164) in ERR by lia.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 160)] m) as MU.
apply rz_evt; [exact MOK|]. unfold READ_SYM.
carve_frame 16%nat ST.
do 10 step. step.
do 7 step.
apply evt_RZ_done.
pose proof (wr_at_store_ok rsegs m0 dst _ 0 (Z.to_nat cnt) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK.
rewrite Z.add_0_r in SOK.
eapply cps_read_dir; [exact MOK| reflexivity| reflexivity| rewrite unsigned_lit by lia; lia| exact Hfd| reflexivity| lia
| rewrite unsigned_lit by lia; unfold task_size_max; lia| exact SOK|].
reenter MOK.
step.
do 5 step.
unfold errno_ret, EISDIR. step.
replace (bv_ltu (Z_to_bv 64 (- (21))) (Z_to_bv 64 (-4095))) with false by (vm_compute; reflexivity). cbv iota.
step. step. step.
step.
step. step. step. step.
step.
replace (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- (21)))))) with (Z_to_bv 64 21 : word) in * by (apply bv_eq; vm_compute; reflexivity).
do 4 step. step.
apply evt_RZ_done. release_frame FR ST (bv_unsigned sp).
replace (bv_unsigned tp + -164) with (bv_unsigned tp - 164) in ERR by lia.
eapply HK; [exact MU| exact WM| exact MI| exact ST| unfold EISDIR; exact ERR].
Qed.
