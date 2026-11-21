(* reloc-zl14c f8de2d53735fe1c42786b28fa49b4390 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg F_syscalls StdioFiles Startup.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Export F_atexit.              (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Malloc Monad Stdio Driver Adapter Harness Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import CMonad CMonadX ProgC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require AdapterC DriverC HarnessC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {rl : runLaunchT}.
Definition PMAIN : Z := 0x148d4.
Definition PSTAGE2_RET : Z := 0x18cd4.      (* [comment removed for export] *)
Definition PEXIT : Z := 0x1916c.
Definition PTARGET_ALLOC_INIT : Z := 0x14b98.
Definition PTARGET_ALLOC_COUNT : Z := 0x14b9c.
Definition PTARGET_RUN : Z := 0x14ba4.
Definition PEMIT_PRINTF : Z := 0x14d2c.
Definition PFUZZ_INIT : Z := 0.             (* [comment removed for export] *)
Definition PGOT_FUZZ_INIT : Z := 0x21c78.   (* [comment removed for export] *)
Definition PINIT_FLAG : Z := 0x32f30.       (* [comment removed for export] *)
Definition PAEF_ARGC : Z := 0x22cd8.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PTARGET_RUN_STACK : Z := 80 + HARNESS_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pat_exit (code : Z) (s : PState) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PEXIT) fc None m (seg_rom psegs)
    /\ stk psegs m lo (bv_unsigned sp)
    /\ rw_cells psegs m 0x72f68 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m 0x93290 [C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x21cb8 [C8 (Z_to_bv 64 0x21c20); C8 (Z_to_bv 64 0x21c18)]
    /\ rw_cells psegs m 0x21c18 [C8 (Z_to_bv 64 0x14844)]
    /\ rw_cells psegs m 0x22f28 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0x21c60 [C8 (Z_to_bv 64 0x19050); C8 (Z_to_bv 64 0)]      (* [comment removed for export] *)
    /\ rw_cells psegs m 0x22cc8 [C8 (Z_to_bv 64 0x22cc8)]                      (* [comment removed for export] *)
    /\ rw_cells psegs m 0x932b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ (atx_cells0 m \/ atx_cellsR m)                          (* [comment removed for export] *)
    /\ rw_cells psegs m 0x936e8 [C8 (Z_to_bv 64 0)] /\ rw_cells psegs m 0x936d8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x22ec8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells psegs m 0x22dd8 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_file m
    /\ rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 guard]
    /\ mem_inv psegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x94000 <= lo
    /\ bv_unsigned sp < 2^47.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STG (m : mem) : Prop := exists sj, rw_cells psegs m PREAD_STAGE [CB PSTAGE_LEN sj].

(* [comment removed for export] *)
Definition dvalid_sp (sp0 : word) (argv envp : list (list byte)) : Prop :=
  valid_sp sp0 /\ ATOP = bv_unsigned sp0 - 8388608 /\ entry_stack_fits sp0 argv envp   (* [comment removed for export] *)
  /\ InitMem.launch_ok RL_la sp0 RL_top argv envp RL_execfn.

(* [comment removed for export] *)
Definition pmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (ms : machine_state),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    Startup.pat_main sp0 argv envp uid hw draw CAN ms ->
    implMC psegs
      (DriverC.main_model Prog.io raw_malloc raw_free PREAD_STAGE Prog.alloc_init ProgC.runC Prog.alloc_count (argv_Z argv))
      (ps_init (reservedZ psegs) ATOP)
      (fun code s' ms' => pat_exit code s' ms') ms.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ptarget_alloc_init_spec : forall (bitmap : Z) (s : PState)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  implM psegs (Prog.alloc_init bitmap) s
        (fun _ s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom psegs) /\ s' = s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PTARGET_ALLOC_INIT) fc None m (seg_rom psegs)).
Proof.
  intros. unfold Prog.alloc_init, Adapter.target_alloc_init, PTARGET_ALLOC_INIT. apply implM_ret.
  step. apply evt_done. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ptarget_alloc_count_spec : forall (s : PState)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  implM psegs Prog.alloc_count s
        (fun r s' ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom psegs) /\ s' = s /\ r = 0)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PTARGET_ALLOC_COUNT) fc None m (seg_rom psegs)).
Proof.
  intros. unfold Prog.alloc_count, Adapter.target_alloc_count, PTARGET_ALLOC_COUNT. apply implM_ret.
  step. step. apply evt_done. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition trun_cells0 (m : mem) : Prop :=
  rw_cells psegs m PINIT_FLAG [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ rw_cells psegs m PGOT_FUZZ_INIT [C8 (wz PFUZZ_INIT)]
  /\ rw_cells psegs m PGOT_ZALLOC [C8 (wz PZCALLOC); C8 (wz PZCFREE)]
  /\ atx_cells0 m.                                                                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pstdout_ivs : list (Z * Z) :=
  [(0x22de0, 0x22de0 + 232); (0x93700, 0x93700 + 1024); (PINIT_FLAG, PINIT_FLAG + 5); (PATX, PATX + 544); (HBUF, HBUF + HBUF_N)].

Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
  match ivs with [] => False | (lo, hi) :: ivs' => (lo <= a < hi) \/ rin_ivs ivs' a end.

(* [comment removed for export] *)
Definition pdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ rin_ivs pstdout_ivs a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

Lemma pdrv_pres_refl : forall LB SP m, pdrv_pres LB SP m m.
Proof. intros LB SP m a _ _ _. auto. Qed.

Lemma pdrv_pres_trans : forall LB SP m1 m2 m3, pdrv_pres LB SP m1 m2 -> pdrv_pres LB SP m2 m3 -> pdrv_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma pdrv_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> pdrv_pres LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc _. apply H; [exact Ha| exact Hc]. Qed.

Lemma pdrv_pres_agree : forall LB SP m m', pdrv_pres LB SP m m' ->
  magree psegs (fun a => rclient_addr LB SP a /\ ~ rin_ivs pstdout_ivs a) m m'.
Proof. intros LB SP m m' H a Ha [Hc Hx]. apply H; assumption. Qed.

(* [comment removed for export] *)
Definition ptarget_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (AB lo : Z) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ 0 <= r <= 78                                                         (* [comment removed for export] *)
    /\ mem_inv psegs m' /\ frm0 fc' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' AB
    /\ pdrv_pres LB (bv_unsigned sp) m m'
    /\ RHEAP s' LB m'
    /\ stdout_file m' (ps_so s')
    /\ atx_cellsR m'.                                                        (* [comment removed for export] *)

Definition ptarget_run_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z) (errv : word),
  RHEAP s LB m -> In (p, A, cap) LB ->
  bytes_at psegs m A (zbytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  trun_cells0 m -> stderr_file0 m ->
  rauxv_ok m AB -> bv_unsigned sp <= AB -> AB <= 2^47 ->          (* [comment removed for export] *)
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PTARGET_RUN_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m -> frm0 fc ->
  stdout_file m (ps_so s) ->
  tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implMC psegs (ProgC.runC (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (ptarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz PTARGET_RUN) fc None m (seg_rom psegs)).
End CANSEC1.
