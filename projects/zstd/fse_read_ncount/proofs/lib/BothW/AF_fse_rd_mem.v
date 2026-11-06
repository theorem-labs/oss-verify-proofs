(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells I_asan_memset I_asan_memcpy.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition amemsetZ_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPz A n c lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(SPz - 2208, SPz); (A, A + n)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo SPz
/\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
#[using="Type"] Lemma amemset_specZ : forall (A n c SPz : Z) RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
mem_inv bsegs m -> 0 <= SPz < 2^64 ->
stk bsegs m lo SPz -> lo <= SPz - 2208 -> KHIGH <= lo ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
(A + n <= lo \/ SPz <= A) ->
app_blk A (A + n) -> unpoisoned m A (A + n) ->
0 <= n <= 2^40 -> 0 <= c < 256 ->
(RLO2 <= A /\ A + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (SPz - lo) -> rng RNG A n ->
rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
evtF bsegs RNG (amemsetZ_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz A n c lo m)
(MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x52308) fc None m (seg_rom bsegs)).
Proof.
intros until RHI2. intros MI SPR ST LO KLO GOT RIC SHB INI LAY REAL DST SEP APP UN Hn Hc R2 WR2 RI RSTK RD RSH2 -> -> ->.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>19034430240.6328813939843.6630680875574.693748405345.68 55345754776.6861929834785.6764296279515.6600000500>00D00J00P00V00^S3SPRS2Hn1B2AKS2Hn1BS2Hc1BS2Hc1BS2Hn1BS1H2H01B".
assert (ESP : bv_unsigned (Z_to_bv 64 SPz) = SPz) by (apply unsigned_lit; lia).
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
assert (AK : 0 <= A /\ A + n + 8 <= KEND) by (destruct APP as (_ & [(? & ?)|(? & ?)]); unfold KLOW, KHIGH, KEND in *; lia).
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold KEND in *; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (Ec : bv_unsigned (Z_to_bv 64 c) mod 256 = c) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
eapply evtF_mono.
{ eapply (asan_memset_spec RNG ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 c) (Z_to_bv 64 n));
rewrite ?EA, ?En, ?ESP; first [eassumption | lia]. }
intros ms' PO. unfold asan_memset_post in PO. rewrite EA, En, Ec, ESP in PO. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition amemcpyZ_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPz A S n lo : Z) (src : list byte) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(SPz - 2224, SPz); (A, A + n)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo SPz
/\ rw_cells bsegs m' A [CB (Z.to_nat n) src]
/\ bytes_at bsegs m' S src.
#[using="Type"] Lemma amemcpy_specZ : forall (A S n SPz : Z) RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
mem_inv bsegs m -> 0 <= SPz < 2^64 ->
stk bsegs m lo SPz -> lo <= SPz - 2224 -> KHIGH <= lo ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
bytes_at bsegs m S src -> length src = Z.to_nat n ->
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
(S + n <= A \/ A + n <= S) ->
(S + n <= SPz - 2224 \/ SPz <= S) ->
(A + n <= lo \/ SPz <= A) ->
app_blk S (S + n) -> app_blk A (A + n) ->
unpoisoned m S (S + n) -> unpoisoned m A (A + n) ->
0 <= n <= 2^40 ->
(RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
(RLO2 <= A /\ A + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (SPz - lo) -> rng RNG S n -> rng RNG A n ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
evtF bsegs RNG (amemcpyZ_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz A S n lo src m)
(MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51e6c) fc None m (seg_rom bsegs)).
Proof.
intros until RHI2. intros MI SPR ST LO KLO GOT RIC SHB INI LAY REAL SRC LEN DST SEP1 SEP2 SEP3 APPS APPD US UD Hn R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2 -> -> ->.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>15083264959.7719034430240.7528811842698.7830680876989.8161929833015.8064292100684.7864303092213.7900000:00C00O00W00_00i015S3LEN1H2H0S3SPR3LENS3LEN2Hn3AKDS3LEN2HnS3LEN2HnS3LEN1H2H0S3LEN2Hn3AKS".
assert (ESP : bv_unsigned (Z_to_bv 64 SPz) = SPz) by (apply unsigned_lit; lia).
assert (AKS : 0 <= S /\ S + n + 8 <= KEND) by (destruct APPS as (_ & [(? & ?)|(? & ?)]); unfold KLOW, KHIGH, KEND in *; lia).
assert (AKD : 0 <= A /\ A + n + 8 <= KEND) by (destruct APPD as (_ & [(? & ?)|(? & ?)]); unfold KLOW, KHIGH, KEND in *; lia).
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold KEND in *; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; unfold KEND in *; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evtF_mono.
{ eapply (asan_memcpy_spec RNG ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 n));
rewrite ?EA, ?ES, ?En, ?ESP; first [eassumption | lia]. }
intros ms' PO. unfold asan_memcpy_post in PO. rewrite EA, ES, En, ESP in PO. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rd_wr_at_appA : forall segs m a n1 n2, 0 <= n1 -> 0 <= n2 ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). Local Ltac2 Set LiaHints.tbl := fun () => "00>0>15538427734.1316044545734.1117101216130.1320927221579.1126981515745.1126983613675.144844197302.17 51508892605.1754736999318.1454743291548.1157036176010.1761783614061.1163513398541.137651745753.14 00000700>00E00L00P00T00Z00`00a00b00c00g00h00mS2H22HiS2H22HbS2H12HiS2H12HaS2HaS2HaS2Hi1HS2Hi1HFFSS2HbSS3Hb'".
repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rd_rw_cells_appA : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite rd_wr_at_appA by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.
End CANSEC1.
