(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3 AD_main_B4 AD_main_C AD_main_D AD_target_run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Main.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).
  Notation ABASE' j8 := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 RSTK canary).
  Notation AMFRAME' j8 := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 j8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  (* [comment removed for export] *)
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x825dc] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x82630] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x82654] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x82784] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x828bc] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x82950] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).
  Notation AENTRY' := (AENTRY AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AP1' := (AP1 AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation POSTB' j8 := (POSTB AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 j8).
  Hypothesis HUL : HU L.

  (* [comment removed for export] *)
  Let TRUN : atarget_run_stmtA AI rng_fs :=
    atarget_run_proofA AI rng_fs rng_fs_mono DRV_CI CLI_CI CI_WF DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN.

  (* [comment removed for export] *)
  Lemma amain_from_P1 : argc = 2 -> forall RNG st ms, AP1' RNG st ms ->
    implMA RNG (ra <- read_all ioS amalloc_M afree_M ASTAGE arg1 ;;
                match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end) st RQEXIT ms.
  Proof.
    intros E2 RNG st ms HP1.
    destruct HP1 as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & fc & mm & j8 & -> & BA & SOI & RK & AH & ARG & RG & U8 & FRM & SJ).
    eapply implMA_bind with (Q1 := POSTB' j8).
    { eapply (amain_read_all AI rng_fs); eassumption. }
    cbv beta. intros ra s' RNG' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
    - apply implMA_ret. apply evtF_done. exact PB.
    - eapply (phaseC AI rng_fs); try eassumption.
      intros DATA A cap cw Lc cfg sc s1 RNG1 ms1 HC R0. rewrite HC.
      eapply (phaseDE AI rng_fs); eassumption.
  Qed.

  (* [comment removed for export] *)
  Theorem amain_proofA : forall RNG st ms, AENTRY' RNG st ms ->
    implMA RNG (main_model ioS amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan) (alloc_countA AAllocAsan) (argv_Z argv)) st
           (fun code s' RNG' ms' => aat_exit code s' RNG' ms') ms.
  Proof.
    intros RNG st ms AM.
    destruct (Z.eq_dec argc 2) as [E2|NE2].
    2: { eapply (amain_usage AI rng_fs); eassumption. }
    rewrite (main_model_eq argv E2).
    eapply implMA_mono with (Q := RQEXIT); [| intros code s' RNG' ms' H; exact H].
    eapply implMA_evtF with (P := AP1' RNG st).
    { eapply (amain_to_P1 AI rng_fs); try eassumption. intros ms' H. apply evtF_done. exact H. }
    cbv beta. intros ms' H. exact (amain_from_P1 E2 RNG st ms' H).
  Qed.
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition apat_mainA (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop)
    (L : alayout) (RNG : footprint) (inp : ProcInput) (s : APS) (ms : machine_state) : Prop :=
  exists (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word)
         (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region),
       r_lo RSTK <= ALO usp /\ usp + -128 <= r_hi RSTK /\ ATOP <= r_rlo RSTK
    /\ usp mod 16 = 0 /\ ATOP + 8388608 <= usp /\ usp + 24 <= 2^47
    /\ 0 < TID < 4194304 /\ usp = al_sp0 L /\ ATOP + 4096 <= ALO usp
    /\ In [AMALLOC_PC; 0x825dc] (al_U L) /\ In [AMALLOC_PC; 0x82630] (al_U L) /\ In [AFREE_PC; 0x82654] (al_U L)
    /\ In [AFREE_PC; 0x82784] (al_U L) /\ In [AMALLOC_PC; 0x828bc] (al_U L) /\ In [AFREE_PC; 0x82950] (al_U L)
    /\ In [AMALLOC_PC] (al_U L) /\ In [AFREE_PC] (al_U L) /\ HU L
    /\ valid_argv (in_argv inp)
    /\ AENTRY AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L (in_argv inp) P0 P1 slack0 slack1 RA0 RA1 RNG s ms.

Section Packed.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
  Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.

  (* [comment removed for export] *)
  Theorem amain_packed : forall L RNG inp s0 ms,
    apat_mainA AI rng_fs L RNG inp s0 ms ->
    implMA RNG (main_model (ioA AAllocAsan) amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan)
                           (alloc_countA AAllocAsan) (argv_Z (in_argv inp))) s0
           (fun code s' RNG' ms' => aat_exit code s' RNG' ms') ms.
  Proof.
    intros L RNG inp s0 ms HP.
    destruct HP as (usp & TID & S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & RSTK & canary & P0 & P1 & slack0 & slack1 & RA0 & RA1
                    & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & HUL & VARGV & AM).
    eapply (amain_proofA AI rng_fs); eassumption.
  Qed.

  (* [comment removed for export] *)
End Packed.
End CANSEC1.
