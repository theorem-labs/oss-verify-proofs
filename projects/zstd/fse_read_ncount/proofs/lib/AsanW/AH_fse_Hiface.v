(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AH_fse_kit AF_fse_iface AF_fse_rd_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Section CANSEC1. Context {rc : runConstT}.
Definition fz_restA (pl : list Z) (producer : option AsanCtrl.aptr) : MA Z :=
buff <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) (buff_size pl) ;;
Harness.free_opt afree_M buff ;;;
Harness.free_opt afree_M producer ;;;
mret 0.
#[using="Type"] Lemma fuzz_oneA_split_fse : forall pl,
fuzz_oneA AAllocAsan pl =
(producer <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) PRODUCER_SIZE ;; fz_restA pl producer).
Proof. reflexivity. Qed.
Section Halves.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition fzB_state (L : alayout) (RNG0 : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem)
(pP : AsanCtrl.aptr) (s1' : APS) (RNG1 : footprint) (ms : machine_state) : Prop :=
exists (P F SPA tl msv : Z) (nc data : list Z) (dsz bsz rem : Z) (buf' : list Z) (jd : list byte) (j0 j1 j2 : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x26 t3 t4 t5 t6 : word) (m : amem),
SPA = (bv_unsigned sp - 192) - (bv_unsigned sp - 192) mod 32
/\ fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem)
/\ ms = MS (mkR (Z_to_bv 64 0x811a4) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 bsz) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 1760)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dsz) (Z_to_bv 64 (F + 608)) (Z_to_bv 64 (F + 32))
(Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 msv) x26 (Z_to_bv 64 (SHF F)) t3 t4 t5 t6)
FR (Z_to_bv 64 0x827d8) fc None m (seg_rom asegs)
/\ AHEAP AI L RNG1 (aps_m s1') (HB pP P PRODUCER_SIZE :: FB5 F :: LB) m
/\ aps_rest s1' = aps_rest s /\ fp_le RNG0 RNG1
/\ magree asegs (aclient_addr CI LB (bv_unsigned sp)) m0 m
/\ P mod 16 = 0 /\ ablk P (P + 16) /\ rng RNG1 P 16 /\ rng RNG1 (shad P) 2
/\ prod_atA m P D rem /\ unpoisoned m P (P + 16)
/\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP /\ rng RNG1 F 2048 /\ rng RNG1 (shad F) 256
/\ wr_at asegs m F 2048
/\ rw_cells asegs m F [C8 j0; C8 j1; C8 j2]
/\ rw_cells asegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]
/\ u8arr asegs m (F + 32) (map (Z_to_bv 8) buf') /\ length buf' = 512%nat /\ firstn (Z.to_nat dsz) buf' = data
/\ u8arr asegs m (F + 608) (u16s (map (Z_to_bv 64) nc))
/\ rw_cells asegs m (F + 1760) [C4 (Z_to_bv 64 255)]
/\ rw_cells asegs m (SHF F) (FSH Z64 Z64 Z64 B04 B04)
/\ stk asegs m lo SPA
/\ rw_cells asegs m SPA [C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); CB 24 jd; C8 (Z_to_bv 64 F)]
/\ stk asegs m (SPA + 88) (bv_unsigned sp + -104)
/\ rw_cells asegs m (bv_unsigned sp + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
/\ mem_inv asegs m
/\ bytes_at asegs m D (map (Z_to_bv 8) pl) /\ unpoisoned m D (D + zlen pl).
Definition fzD_stmt : Prop :=
(forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
stack_free_5_stmt AI fflag rng_fs ->
fse_read_stmtA AI rng_fs ->
forall (L : alayout) (RNG0 : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem)
(pP : AsanCtrl.aptr) (s1' : APS) (RNG1 : footprint) (ms : machine_state),
(forall b, In b LB -> exists p A n, b = HB p A n) ->
AHarness_iface.payload_atA LB D pl -> Forall (fun c => 0 <= c < 256) pl -> D mod 16 = 0 -> zlength pl < 2^26 ->
ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
s0 = Z_to_bv 64 (zlength pl) -> frm0 fc -> tp = Z_to_bv 64 ATP -> ra = Z_to_bv 64 ATRUN_RET ->
HU L ->
rng RNG0 lo (al_top L - lo) -> rng_aimg RNG0 -> rng_aimg_sh RNG0 -> rng_fs L RNG0 ->
aps_ok L s ->
fzB_state L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms ->
implMA RNG1 (fz_restA pl (Some pP)) s1'
(fuzz_oneA_post AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0) ms.
End Halves.
End CANSEC1.
