(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit Stdio_kit.
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
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_ENTRY : Z := 0x80d20.
Definition ATRUN_RET : Z := 0x80c1c.
Definition ATRUN_DEPTH : Z := 208.
Definition AEMPTY : Z := 0x5d4ba0.
Definition AHARNESS_STACK : Z := 16384.
Definition harness_invA (m : amem) : Prop := True.
End CANSEC1.
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xbce00).
Section CANSEC1b. Context {rc : runConstT}.
Definition AFMALLOC_RET : Z := 0x82984.
Definition AFREEB_RET : Z := 0x81248.
Definition AFREEP_RET : Z := 0x81268.
Definition HU (L : alayout) : Prop :=
In [AMALLOC_PC; AFMALLOC_RET] (al_U L)
/\ In [AFREE_PC; AFREEB_RET; ATRUN_RET] (al_U L) /\ In [AFREE_PC; AFREEB_RET] (al_U L)
/\ In [AFREE_PC; AFREEP_RET; ATRUN_RET] (al_U L) /\ In [AFREE_PC; AFREEP_RET] (al_U L).
Section FuzzOneA.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.
Definition astk_shadow_pres (SP : Z) (m m' : amem) : Prop :=
forall a, shad ATOP <= a < shad SP -> m' (wa a) = m (wa a).
Definition payload_atA (LB : list ablock) (D : Z) (payload : list Z) : Prop :=
(exists p, In (HB p D (zlength payload)) LB /\ 0 < zlength payload) \/ (payload = [] /\ D = AEMPTY).
Definition fuzz_oneA_post (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : APS) (LB : list ablock) (lo : Z) (m : amem)
(r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
fun ms' => fp_le RNG RNG' /\
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ -2^31 <= r < 2^31
/\ mem_inv bsegs m' /\ frm0 fc'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ astk_shadow_pres (bv_unsigned sp) m m'
/\ AHEAP AI L RNG' (aps_m s') LB m'
/\ harness_invA m'
/\ aps_rest s' = aps_rest s.
Definition fuzz_oneA_stmt : Prop :=
forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem)
(s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
AHEAP AI L RNG (aps_m s) LB m ->
(forall b, In b LB -> exists p A n, b = HB p A n) ->
payload_atA LB D payload ->
bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
D mod 16 = 0 -> zlength payload < 2^26 ->
harness_invA m ->
stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
s0 = Z_to_bv 64 (zlength payload) ->
mem_inv bsegs m -> frm0 fc ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
HU L ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
aps_ok L s ->
implMA RNG (fuzz_oneA AAllocAsan payload) s
(fuzz_oneA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
End FuzzOneA.
End CANSEC1b.
