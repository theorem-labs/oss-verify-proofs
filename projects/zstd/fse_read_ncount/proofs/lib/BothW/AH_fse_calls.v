(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells F_memset F_asetshadow I_asan_memset I_asan_memcpy.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition ss_post (v : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(A, A + n)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
#[using="Type"] Lemma ss_f8_z : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A n : Z) (junk : list byte),
0 <= A -> A + n < 2^64 -> 0 <= n ->
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
mem_inv bsegs m ->
rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)] -> rt_real_mem m ->
rng RNG A n -> rng_aimg RNG ->
evtF bsegs RNG (ss_post 248 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54e4c) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros A0 AH N0 DST MI GOT REAL RR RIMG.
eapply evtF_mono.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0040>28813907462.6728818347399.4661929933994.6761933850411.4600000:00D00N00XS2A02AH2N0S2A02AH2N0S2A02AH2N0S2A02AH2N0".
eapply set_shadow_f8_spec; rewrite ?unsigned_lit by lia; eassumption. }
cbv beta. intros ms' (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & E & MU & WM & MI' & CH).
rewrite ?unsigned_lit in MU, CH by lia. change (248 mod 256) with 248 in CH.
exists x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'. repeat (split; [eassumption|]). exact CH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ss_00_z : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A n : Z) (junk : list byte),
0 <= A -> A + n < 2^64 -> 0 <= n ->
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
mem_inv bsegs m ->
rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)] -> rt_real_mem m ->
rng RNG A n -> rng_aimg RNG ->
evtF bsegs RNG (ss_post 0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54d2c) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros A0 AH N0 DST MI GOT REAL RR RIMG.
eapply evtF_mono.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0040>28813907462.6728818347399.4661929933994.6761933850411.4600000:00D00N00XS2A02AH2N0S2A02AH2N0S2A02AH2N0S2A02AH2N0".
eapply set_shadow_00_spec; rewrite ?unsigned_lit by lia; eassumption. }
cbv beta. intros ms' (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & E & MU & WM & MI' & CH).
rewrite ?unsigned_lit in MU, CH by lia. change (0 mod 256) with 0 in CH.
exists x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'. repeat (split; [eassumption|]). exact CH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition amemset_postz (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV A v n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(SPV - 2208, SPV); (A, A + n)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo SPV
/\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
#[using="Type"] Lemma amemset_z : forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (SPV A v n lo RLO RHI : Z) (junk : list byte),
0 <= SPV < 2^64 -> 0 <= A -> A + n < 2^64 -> 0 <= n <= 2^40 -> 0 <= v < 256 ->
mem_inv bsegs m ->
stk bsegs m lo SPV -> lo <= SPV - 2208 -> KHIGH <= lo ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
(A + n <= lo \/ SPV <= A) ->
app_blk A (A + n) -> unpoisoned m A (A + n) ->
(RLO <= A /\ A + n <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) ->
wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
rng_aimg RNG -> rng RNG lo (SPV - lo) -> rng RNG A n -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
evtF bsegs RNG (amemset_postz ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV A v n lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 v) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x52308) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros RSP A0 AH N0 V0 MI ST LO KL GOT RIC SHB INI LAY REAL DST SEP APB UNP HULL WRH RIMG RSTK RDST RHUL.
eapply evtF_mono.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0090>28813907462.8728818348418.6529442497642.8730676933471.6535049946798.6535062804778.8744956571891.8761929933994.8761933847342.6500000:00D00H00L00Q00V00Z00^00bS2A02AH2N0S2A02AH2N0S2V0S2N0S3RSPS3RSPS2V0S2N0S2N0".
eapply asan_memset_spec; rewrite ?unsigned_lit by lia; first [eassumption | lia]. }
cbv beta. intros ms' (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & E & MU & WM & MI' & ST' & CH).
rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in CH by lia. rewrite ?unsigned_lit in ST' by lia. rewrite ?(Z.mod_small v 256) in CH by lia.
exists x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'. repeat (split; [eassumption|]). exact CH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition amemcpy_postz (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SPV A0 A1 n : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A0) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(SPV - 2224, SPV); (A0, A0 + n)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo SPV
/\ rw_cells bsegs m' A0 [CB (Z.to_nat n) src]
/\ bytes_at bsegs m' A1 src.
#[using="Type"] Lemma amemcpy_z : forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (SPV A0 A1 n lo RLO1 RHI1 RLO2 RHI2 : Z) (src junk : list byte),
0 <= SPV < 2^64 -> 0 <= A0 -> A0 + n < 2^64 -> 0 <= A1 -> A1 + n < 2^64 -> 0 <= n <= 2^40 ->
mem_inv bsegs m ->
stk bsegs m lo SPV -> lo <= SPV - 2224 -> KHIGH <= lo ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
bytes_at bsegs m A1 src -> length src = Z.to_nat n ->
rw_cells bsegs m A0 [CB (Z.to_nat n) junk] ->
(A1 + n <= A0 \/ A0 + n <= A1) -> (A1 + n <= SPV - 2224 \/ SPV <= A1) -> (A0 + n <= lo \/ SPV <= A0) ->
app_blk A1 (A1 + n) -> app_blk A0 (A0 + n) ->
unpoisoned m A1 (A1 + n) -> unpoisoned m A0 (A0 + n) ->
(RLO1 <= A1 /\ A1 + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
(RLO2 <= A0 /\ A0 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (SPV - lo) -> rng RNG A1 n -> rng RNG A0 n ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF bsegs RNG (amemcpy_postz ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV A0 A1 n src lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51e6c) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros RSP P0 PH Q0 QH N0 MI ST LO KL GOT RIC SHB INI LAY REAL SRC LSRC DST SEP1 SEP2 SEP3 AP1 AP0 UN1 UN0 H1 H2 W1 W2 RIMG RSTK R1 R0 RH1 RH2.
eapply evtF_mono.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0090?30679028961.79 31093611504.79 31095690960.10235060429072.79 35062545456.10253586866460.79 53588982844.10261929669040.10261931752592.79 00000900H00W00a00k01:01I01R01[S2N04LSRCS2P02PH2N04LSRCS2P02PH2N04LSRCS3RSP4LSRCS3RSP4LSRCS2Q02QH2N04LSRCS2Q02QH2N04LSRCS2N04LSRCS2N04LSRC".
eapply asan_memcpy_spec; rewrite ?unsigned_lit by lia; first [eassumption | lia]. }
cbv beta. intros ms' (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & E & MU & WM & MI' & ST' & CH & SR).
rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in CH by lia. rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in SR by lia.
exists x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'.
split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact CH| exact SR].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
