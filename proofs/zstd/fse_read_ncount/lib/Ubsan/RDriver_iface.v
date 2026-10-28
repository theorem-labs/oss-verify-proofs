(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls StdioFiles Startup F_atexit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Malloc Monad Stdio Driver Adapter Harness Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.
Definition PMAIN : Z := 0x13088.
Definition PSTAGE2_RET : Z := 0x14a68.
Definition PEXIT : Z := 0x14fb0.
Definition PTARGET_ALLOC_INIT : Z := 0x1334c.
Definition PTARGET_ALLOC_COUNT : Z := 0x13350.
Definition PTARGET_RUN : Z := 0x13358.
Definition PFUZZ_INIT : Z := 0.
Definition PGOT_FUZZ_INIT : Z := 0x1db78.
Definition PINIT_FLAG : Z := 0x2ee30.
Definition PTARGET_RUN_STACK : Z := 80 + HARNESS_STACK.
Definition pat_exit (code : Z) (s : PState) (ms : machine_state) : Prop :=
exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (td0 td1 td2 td3 guard : word)
(cdt thr sec : byte) (tm1 : word),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PEXIT) fc None m (seg_rom usegs)
/\ stk usegs m lo (bv_unsigned sp)
/\ rw_cells usegs m 0x2ee68 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
/\ rw_cells usegs m 0x4f198 [C4 (Z_to_bv 64 0)]
/\ rw_cells usegs m 0x1dbb8 [C8 (Z_to_bv 64 0x1db20); C8 (Z_to_bv 64 0x1db18)]
/\ rw_cells usegs m 0x1db18 [C8 (Z_to_bv 64 0x12ff8)]
/\ rw_cells usegs m 0x1ee28 [C1 (Z_to_bv 8 0)]
/\ rw_cells usegs m 0x1db60 [C8 (Z_to_bv 64 0x14e94); C8 (Z_to_bv 64 0)]
/\ rw_cells usegs m 0x4f1c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
/\ rw_cells usegs m 0x1ebc8 [C8 (Z_to_bv 64 0x1ebc8)]
/\ (exists reg : bool, atx_state reg m)
/\ rw_cells usegs m 0x4f5f0 [C8 (Z_to_bv 64 0)] /\ rw_cells usegs m 0x4f5e0 [C8 (Z_to_bv 64 0)]
/\ rw_cells usegs m 0x1edc8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells usegs m 0x1ecd8 [C8 (Z_to_bv 64 RSTDERR)]
/\ stdout_file m (ps_so s) /\ stderr_file m
/\ rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 guard]
/\ mem_inv usegs m
/\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
/\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x50000 <= lo
/\ bv_unsigned sp < 2^47.
Definition STG (m : mem) : Prop := exists sj, rw_cells usegs m UREAD_STAGE [CB PSTAGE_LEN sj].
Definition dvalid_sp (sp0 : word) (argv envp : list (list byte)) : Prop :=
valid_sp sp0 /\ ATOP = bv_unsigned sp0 - 8388608 /\ entry_stack_fits sp0 argv envp.
Definition pmain_stmt : Prop :=
forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (ms : machine_state),
dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
Startup.pat_main sp0 argv envp uid hw draw CAN ms ->
implM usegs
(main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
(ps_init (reservedZ usegs) ATOP)
(fun code s' ms' => pat_exit code s' ms') ms.
#[using="Type"] Lemma ptarget_alloc_init_spec : forall (bitmap : Z) (s : PState)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
implM usegs (Prog.alloc_init bitmap) s
(fun _ s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs) /\ s' = s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PTARGET_ALLOC_INIT) fc None m (seg_rom usegs)).
Proof.
intros. unfold Prog.alloc_init, Adapter.target_alloc_init, PTARGET_ALLOC_INIT. apply implM_ret.
step. apply evt_done. split; reflexivity.
Qed.
#[using="Type"] Lemma ptarget_alloc_count_spec : forall (s : PState)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
implM usegs Prog.alloc_count s
(fun r s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs) /\ s' = s /\ r = 0)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PTARGET_ALLOC_COUNT) fc None m (seg_rom usegs)).
Proof.
intros. unfold Prog.alloc_count, Adapter.target_alloc_count, PTARGET_ALLOC_COUNT. apply implM_ret.
step. step. apply evt_done. split; [reflexivity|]. split; reflexivity.
Qed.
Definition trun_cells0 (m : mem) : Prop :=
rw_cells usegs m PINIT_FLAG [C1 (Z_to_bv 8 0)]
/\ rw_cells usegs m PGOT_FUZZ_INIT [C8 (wz PFUZZ_INIT)]
/\ rw_cells usegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
/\ rw_cells usegs m PSTDERR_PTR [C8 (wz RSTDERR)]
/\ atx_state false m.
Definition pstdout_ivs : list (Z * Z) :=
[(0x1ece0, 0x1ece0 + 232); (0x4f608, 0x4f608 + 1024); (PINIT_FLAG, PINIT_FLAG + 1);
(PAEF_INCB, PAEF_INCB + 1); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90); (0x4ef98, 0x4efa0); (0x4f098, 0x4f0a0)].
Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
match ivs with [] => False | (lo, hi) :: ivs' => (lo <= a < hi) \/ rin_ivs ivs' a end.
Definition pdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ rin_ivs pstdout_ivs a ->
m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).
#[using="Type"] Lemma pdrv_pres_trans : forall LB SP m1 m2 m3, pdrv_pres LB SP m1 m2 -> pdrv_pres LB SP m2 m3 -> pdrv_pres LB SP m1 m3.
Proof.
intros LB SP m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
split; [congruence| auto].
Qed.
#[using="Type"] Lemma pdrv_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> pdrv_pres LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc _. apply H; [exact Ha| exact Hc]. Qed.
#[using="Type"] Lemma pdrv_pres_agree : forall LB SP m m', pdrv_pres LB SP m m' ->
magree usegs (fun a => rclient_addr LB SP a /\ ~ rin_ivs pstdout_ivs a) m m'.
Proof. intros LB SP m m' H a Ha [Hc Hx]. apply H; assumption. Qed.
Definition ptarget_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (m : mem)
(r : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom usegs)
/\ 0 <= r <= 2
/\ mem_inv usegs m' /\ frm0 fc' /\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ pdrv_pres LB (bv_unsigned sp) m m'
/\ RHEAP s' LB m'
/\ stdout_file m' (ps_so s')
/\ atx_state true m'.
Definition ptarget_run_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z) (errv : word),
RHEAP s LB m -> In (p, A, cap) LB ->
bytes_at usegs m A (zbytes content) -> Forall (fun c => 0 <= c < 256) content ->
zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
trun_cells0 m -> stderr_file0 m ->
rauxv_ok m AB -> bv_unsigned sp <= AB -> AB <= 2^47 ->
stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PTARGET_RUN_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m -> frm0 fc ->
stdout_file m (ps_so s) ->
tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
implM usegs (Prog.run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
(ptarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz PTARGET_RUN) fc None m (seg_rom usegs)).
End CANSEC1.
