(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg F_memset F_memcpy.
Import ListNotations.
Open Scope Z_scope.
Definition rd_memsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
Lemma rd_memset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells usegs m A [CB (Z.to_nat n) junk] ->
mem_inv usegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
(0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
evt usegs (rd_memsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c534) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros DST MI -> -> -> Hc Hn Hl.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>28807598860.413748405345.43 55345754776.4361929834785.4200000600<00B00HS2Hl1BS2Hc1BS2Hc1BS2Hn1B".
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rd_memcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' A [CB (Z.to_nat n) src]
/\ bytes_at usegs m' S src.
Lemma rd_memcpy_specZ : forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at usegs m S src ->
length src = Z.to_nat n ->
rw_cells usegs m A [CB (Z.to_nat n) junk] ->
(S + n <= A \/ A + n <= S)%Z ->
mem_inv usegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
(0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
evt usegs (rd_memcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c130) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>28813896508.4661929833015.4863007907991.4964303092213.4700000:00D00O00\S3LEN2HA1BS3LEN2Hn1BS3LEN3SEP1BS3LEN2HS1B2B2".
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rd_wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). Local Ltac2 Set LiaHints.tbl := fun () => "00>0>15538427734.1216044545734.1017101216130.1220927221579.1026981515745.1026983613675.134844197302.16 51508892605.1654736999318.1354743291548.1057036176010.1661783614061.1063513398541.127651745753.13 00000700>00E00L00P00T00Z00`00a00b00c00g00h00mS2H22HiS2H22HbS2H12HiS2H12HaS2HaS2HaS2Hi1HS2Hi1HFFSS2HbSS3Hb'".
repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rd_rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite rd_wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.
