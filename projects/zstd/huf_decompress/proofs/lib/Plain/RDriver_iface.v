(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (ptarget_alloc_init_spec, ptarget_alloc_count_spec, pdrv_pres_refl and 3 more); adds dvalid_padok; the launch values; dvalid_sp restated for the revision's model). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg F_syscalls StdioFiles Startup F_atexit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Malloc Monad Stdio Driver Adapter Harness Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RDriver_iface () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog:alloc_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c59OSSVerify5KrLib5Plain=RDriver_ifaceBPTARGET_ALLOC_INITC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;alloc_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RDriver_ifaceCPTARGET_ALLOC_COUNTC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5Plain=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RDriver_iface7rin_ivsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc59OSSVerify5KrLib5Plain=RDriver_iface9pdrv_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RDriver_iface;pstdout_ivsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib5Plain=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {lx : launchT}.
Definition PMAIN : Z := 0x12d30.
Definition PSTAGE2_RET : Z := 0x1d368.      (* [comment removed for export] *)
Definition PEXIT : Z := 0x1d8b0.
Definition PTARGET_ALLOC_INIT : Z := 0x12ff4.
Definition PTARGET_ALLOC_COUNT : Z := 0x12ff8.
Definition PTARGET_RUN : Z := 0x13000.
Definition PEMIT_PRINTF : Z := 0x13188.
Definition PFUZZ_INIT : Z := 0.             (* [comment removed for export] *)
Definition PGOT_FUZZ_INIT : Z := 0x26478.   (* [comment removed for export] *)
Definition PINIT_FLAG : Z := 0x37730.       (* [comment removed for export] *)
Definition PAEF_ARGC : Z := 0x274d8.        (* [comment removed for export] *)

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
    /\ rw_cells psegs m 0x37768 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m 0x57a98 [C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x264b8 [C8 (Z_to_bv 64 0x26420); C8 (Z_to_bv 64 0x26418)]
    /\ rw_cells psegs m 0x26418 [C8 (Z_to_bv 64 0x12ca0)]
    /\ rw_cells psegs m 0x27728 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0x26460 [C8 (Z_to_bv 64 0x1d794); C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x57ac0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells psegs m 0x274c8 [C8 (Z_to_bv 64 0x274c8)]                   (* [comment removed for export] *)
    /\ (exists reg : bool, atx_state reg m)                                 (* [comment removed for export] *)
    /\ rw_cells psegs m 0x57ef0 [C8 (Z_to_bv 64 0)] /\ rw_cells psegs m 0x57ee0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs m 0x276c8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells psegs m 0x275d8 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_file m
    /\ rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 guard]
    /\ mem_inv psegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x59000 <= lo
    /\ bv_unsigned sp < 2^47.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STG (m : mem) : Prop := exists sj, rw_cells psegs m PREAD_STAGE [CB PSTAGE_LEN sj].

(* [comment removed for export] *)
Definition dvalid_sp (sp0 : word) (argv envp : list (list byte)) : Prop :=
  valid_sp sp0 /\ ATOP = bv_unsigned sp0 - 8388608 /\ entry_stack_fits sp0 argv envp
  (* 08b1429: the block runs from sp0 to the stack VMA's end L_TOP. *)
  /\ (bv_unsigned sp0 + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)
  /\ (bv_unsigned L_TOP - bv_unsigned sp0 <= 2101782)
  /\ (bv_unsigned L_TOP <= 0x800000000000).

(* [comment removed for export] *)
Lemma dvalid_padok : forall sp0 argv envp, dvalid_sp sp0 argv envp ->
  (bv_unsigned sp0 + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP).
Proof. intros sp0 argv envp (_ & _ & _ & H & _). exact H. Qed.   (* [comment removed for export] *)

Definition pmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (ms : machine_state),
    dvalid_sp sp0 argv envp -> valid_argv argv -> valid_envp envp -> SECRET = InitMem.draw_secret draw ->
    Startup.pat_main sp0 argv envp uid hw draw CAN ms ->
    implM psegs
      (main_model Prog.io raw_malloc raw_free PREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
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
  rw_cells psegs m PINIT_FLAG [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m PGOT_FUZZ_INIT [C8 (wz PFUZZ_INIT)]
  /\ rw_cells psegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
  /\ rw_cells psegs m PSTDERR_PTR [C8 (wz RSTDERR)]
  /\ atx_state false m.

(* [comment removed for export] *)
Definition pstdout_ivs : list (Z * Z) :=
  [(0x275e0, 0x275e0 + 232); (0x57f08, 0x57f08 + 1024); (PINIT_FLAG, PINIT_FLAG + 1);
   (PAEF_INCB, PAEF_INCB + 1); (0x57880, 0x57884); (0x57888, 0x57890); (0x57898, 0x578a0); (0x57998, 0x579a0)].

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
    /\ 0 <= r <= 2
    /\ mem_inv psegs m' /\ frm0 fc' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
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
  implM psegs (Prog.run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (ptarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz PTARGET_RUN) fc None m (seg_rom psegs)).
End CANSEC1.
