(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread I_printf_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA.
From Stdlib Require String Ascii.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_fmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module I_fopen.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition fopen_i_entry := 0x49674%Z.
Definition FOPEN_I_RA : Z := 0x49778%Z.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fopen_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x12 x13 x14 x15 x16 x17 x19 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x49778) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp a1 a0 a1 x12 x13 x14 x15 x16 x17
                  a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9a7c4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144) /\ stk asegs m' (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section FOPEN_PRE.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (pstr prest mstr mrest : list byte) (RLOp RHIp RLOm RHIm : Z).
  Notation PA := (bv_unsigned a0).
  Notation MA := (bv_unsigned a1).
  Notation LP := (Z.of_nat (length pstr)).
  Notation NP := (Z.of_nat (length pstr) + 1)%Z.
  Notation LM := (Z.of_nat (length mstr)).
  Notation NM := (Z.of_nat (length mstr) + 1)%Z.
  Notation pfull := (pstr ++ Z_to_bv 8 0 :: prest).
  Notation mfull := (mstr ++ Z_to_bv 8 0 :: mrest).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis ENV : icptenv m.
  Hypothesis PNZ : (0 < PA)%Z.
  Hypothesis STRP : bytes_at asegs m PA pfull.
  Hypothesis NONULP : ~ In (Z_to_bv 8 0) pstr.
  Hypothesis SEPP : (PA + Z.of_nat (length pfull) <= lo \/ bv_unsigned sp <= PA)%Z.
  Hypothesis STRM : bytes_at asegs m MA mfull.
  Hypothesis NONULM : ~ In (Z_to_bv 8 0) mstr.
  Hypothesis SEPM : (MA + Z.of_nat (length mfull) <= lo \/ bv_unsigned sp <= MA)%Z.
  (* [comment removed for export] *)
  Hypothesis APPp : app_blk PA (PA + NP).
  Hypothesis UNPp : unpoisoned m PA (PA + NP).
  Hypothesis NSZp : (NP <= 2^40)%Z.
  Hypothesis R1p : (RLOp <= PA /\ PA + NP <= RHIp /\ RLOp mod 64 = 0 /\ RHIp mod 64 = 0 /\ 0 <= RLOp /\ RHIp <= KEND)%Z.
  Hypothesis WR1p : wr_at asegs m (shad RLOp) (shad RHIp - shad RLOp).
  Hypothesis APPm : app_blk MA (MA + NM).
  Hypothesis UNPm : unpoisoned m MA (MA + NM).
  Hypothesis NSZm : (NM <= 2^40)%Z.
  Hypothesis R1m : (RLOm <= MA /\ MA + NM <= RHIm /\ RLOm mod 64 = 0 /\ RHIm mod 64 = 0 /\ 0 <= RLOm /\ RHIm <= KEND)%Z.
  Hypothesis WR1m : wr_at asegs m (shad RLOm) (shad RHIm - shad RLOm).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RBp : rng RNG PA NP.
  Hypothesis RBm : rng RNG MA NM.
  Hypothesis RSH1p : rng RNG (shad RLOp) (shad RHIp - shad RLOp).
  Hypothesis RSH1m : rng RNG (shad RLOm) (shad RHIm - shad RLOm).

  Notation POST := (fopen_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc PA (PA + NP) /\ wr_at asegs mc (shad RLOp) (shad RHIp - shad RLOp) /\ bytes_at asegs mc PA pfull
    /\ unpoisoned mc MA (MA + NM) /\ wr_at asegs mc (shad RLOm) (shad RHIm - shad RLOm) /\ bytes_at asegs mc MA mfull
    /\ icptenv mc.

  Definition SBND1 (S N RLO RHI : Z) : Prop :=
    (1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64)%Z /\ SBND1 PA NP RLOp RHIp /\ SBND1 MA NM RLOm RHIm.
  Lemma SBND_ok : SBND.
  Proof using APPm APPp KLO LO NSZm NSZp PNZ R1m R1p SEPM SEPP ST.
    unfold SBND, SBND1. destruct ST as (LOW & _). destruct APPp as [LESp ASp]. destruct APPm as [LESm ASm]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    pose proof (bv_unsigned_in_range 64 a1) as SR1. unfold bv_modulus in SR1. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR1.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    split; [lia|]. split; (Z.div_mod_to_equations; (keep_hyps sp a0 a1 lo pstr prest mstr mrest RLOp RHIp r7 r8 q r q0 r0 q1 r1 q2 r2 q3 r3 q4 r4 q5 r5 q6 r6 q7 q8 NSZp R1p ASp H H0 H4 H5 H9 H10 H14 H15 H19 H20 H24 H25 H29 H30 H34 H35 H39 H44 RLOm RHIm NSZm R1m ASm; lia)).
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, SBND1, KHIGH, KEND in B.

  Definition SBL1 (S N RLO RHI : Z) : Prop :=
    (1 <= N /\ N <= 2^40 /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64)%Z /\ SBL1 PA NP RLOp RHIp /\ SBL1 MA NM RLOm RHIm.
  Lemma SBL_ok : SBL. Proof using APPm APPp KLO LO NSZm NSZp PNZ R1m R1p SEPM SEPP ST. pose proof SBND_ok as B. unfold SBND, SBND1, KHIGH, KEND in B. unfold SBL, SBL1. repeat split; (keep_hyps sp a0 a1 lo pstr prest mstr mrest RLOp RHIp RLOm RHIm B LO NSZp PNZ NSZm; lia). Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNPp1 & WRp1 & STRP1 & UNPm1 & WRm1 & STRM1 & ENV1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1p; change (?P) with (sf_hide P) in R1m; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPP; change (?P) with (sf_hide P) in SEPM;
    change (?P) with (sf_hide P) in UNPp; change (?P) with (sf_hide P) in WR1p; change (?P) with (sf_hide P) in UNPm; change (?P) with (sf_hide P) in WR1m;
    change (?P) with (sf_hide P) in STRP; change (?P) with (sf_hide P) in STRM.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL, SBL1 in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO ENV PNZ STRP SEPP STRM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1. pose proof SBND_ok as B. unfold SBND, SBND1, KHIGH, KEND in B.
    assert (ENV1 : icptenv mc) by (eapply icptenv_transport; [exact ENV| exact MU1| exact WM1| solve_iesafe]).
    repeat (split; [assumption|]).
    split; [exact (ie_got _ ENV1)|]. split; [exact (ie_shb _ ENV1)|]. split; [exact (ie_lay _ ENV1)|].
    assert (SSp : (shad (PA + NP - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (SSm : (shad (MA + NM - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    rewrite !length_app in SEPP, SEPM. cbn [length] in SEPP, SEPM.
    pose proof (bytes_at_bound _ _ _ _ STRP) as BBp. pose proof (bytes_at_bound _ _ _ _ STRM) as BBm.
    split. { eapply unpoisoned_munch; [exact UNPp | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split. { eapply bytes_at_transport; [exact STRP | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    split. { eapply unpoisoned_munch; [exact UNPm | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split; [| exact ENV1].
    eapply bytes_at_transport; [exact STRM | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (N : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 N) s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO PNZ SEPP SEPM APPp NSZp R1p APPm NSZm R1m RI RSTK"] Lemma SXB : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49764) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    pose proof (ie_fopen _ ENV1) as RFO1.
    do 4 zstep. zstep.
    apply evtF_done. unfold fopen_i_mid.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO PNZ SEPP SEPM APPp NSZp R1p APPm NSZm R1m RI RSTK RSH1m"] Lemma SLB : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    SINV mc -> (1 <= NM <= 64)%Z -> Z.to_nat (shad (MA + NM - 1) - c) = k -> (shad MA <= c < shad (MA + NM - 1))%Z ->
    evtF asegs RNG POST (MS (sregs NM x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (MA + NM + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49878) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (MA + NM - 1) = 2147450880 + Z.shiftr (MA + NM + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc MA (MA + NM) c UNPm1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SXB; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma SEB : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31, SINV mc -> (1 <= NM <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs NM x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr MA 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (MA + NM + -1) 3))
                                   (Z_to_bv 64 (MA + NM + -1)) x13 x14 x15 x16 x17 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4985c) fc None mc (seg_rom asegs)).
  Proof using APPm APPp KLO LO NSZm NSZp PNZ R1m R1p RI RSH1m RSTK SEPM SEPP ST.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc MA (MA + NM) (MA + NM + -1) 1 UNPm1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((MA + NM + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; (keep_hyps pstr mstr r H0 b2 CK2; lia)).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SXB; eassumption.
    - eapply (SLB mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SCB : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 LM) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49718) fc None mc (seg_rom asegs)).
  Proof using APPm APPp ENV KLO LO NSZm NSZp PNZ R1m R1p RI RSH1m RSTK SEPM SEPP ST STRM STRP UNPm UNPp WR1m WR1p.
    intros until x31. intros IV. sprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm LO; lia) | unfold KHIGH; (keep_hyps sp a0 a1 lo pstr mstr RLOp RHIp RLOm RHIm BL0; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPm | zsimp; exact UNPm1
        | zsimp; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; (keep_hyps pstr mstr RLOp RHIp RLOm RHIm NSZm; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SXB. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= NM <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (LM + MA)%Z with (MA + NM + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1m.
      destruct (shadow_probe8 asegs mc RLOm RHIm MA WRm1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1m; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLOm RHIm (MA + NM + -1) WRm1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1m; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SEB; eassumption.
      + eapply SXB; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO ENV PNZ STRP SEPP STRM NONULM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m RI RSTK RBm RSH1m"] Lemma SXA : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49710) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    zstep. zstep.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) mstr).
    { apply Forall_forall. intros b Hb E. apply NONULM. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    call istrlen_spec; [ eassumption | exact STRM1 | exact NZ | ].
    eapply SCB. eapply sinv_of; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO ENV PNZ STRP SEPP STRM NONULM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m RI RSTK RBm RSH1p RSH1m"] Lemma SLA : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    SINV mc -> (1 <= NP <= 64)%Z -> Z.to_nat (shad (PA + NP - 1) - c) = k -> (shad PA <= c < shad (PA + NP - 1))%Z ->
    evtF asegs RNG POST (MS (sregs NP x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (PA + NP + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x28 x29 x30 x31)
                            F (Z_to_bv 64 0x499bc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (PA + NP - 1) = 2147450880 + Z.shiftr (PA + NP + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc PA (PA + NP) c UNPp1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SXA; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma SEA : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31, SINV mc -> (1 <= NP <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs NP x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr PA 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (PA + NP + -1) 3))
                                   (Z_to_bv 64 (PA + NP + -1)) x13 x14 x15 x16 x17 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x499a0) fc None mc (seg_rom asegs)).
  Proof using APPm APPp ENV KLO LO NONULM NSZm NSZp PNZ R1m R1p RBm RI RSH1m RSH1p RSTK SEPM SEPP ST STRM STRP UNPm UNPp WR1m WR1p.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc PA (PA + NP) (PA + NP + -1) 1 UNPp1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((PA + NP + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; (keep_hyps pstr mstr r H0 b2 CK2; lia)).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SXA; eassumption.
    - eapply (SLA mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SCA : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 LP) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x496c4) fc None mc (seg_rom asegs)).
  Proof using APPm APPp ENV KLO LO NONULM NSZm NSZp PNZ R1m R1p RBm RI RSH1m RSH1p RSTK SEPM SEPP ST STRM STRP UNPm UNPp WR1m WR1p.
    intros until x31. intros IV. sprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm LO; lia) | unfold KHIGH; (keep_hyps sp a0 a1 lo pstr mstr RLOp RHIp RLOm RHIm BL0; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPp | zsimp; exact UNPp1
        | zsimp; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; (keep_hyps pstr mstr RLOp RHIp RLOm RHIm NSZp; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SXA. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= NP <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (LP + PA)%Z with (PA + NP + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1p.
      destruct (shadow_probe8 asegs mc RLOp RHIp PA WRp1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1p; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLOp RHIp (PA + NP + -1) WRp1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1p; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SEA; eassumption.
      + eapply SXA; eassumption.
  Qed.

  #[using="pstr prest mstr mrest RLOp RHIp RLOm RHIm MI ST LO KLO ENV PNZ STRP NONULP SEPP STRM NONULM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m RI RSTK RBp RBm RSH1p RSH1m"] Lemma fopen_i_pre_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x49674) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL, SBL1 in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0.
    pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 13 zstep.
    zstep. call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 PNZ. lia. } clear K2.
    zstep. zstep.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) pstr).
    { apply Forall_forall. intros b Hb E. apply NONULP. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STRn : bytes_at asegs mm PA pfull) by
        (unfold sf_hide in STRP, SEPP, LO; pose proof (bytes_at_bound _ _ _ _ STRP) as BBn;
         eapply bytes_at_transport; [exact STRP | exact MU |]; cbn [disjoint_from]; clear -SEPP LO BL0 BBn; lia) end.
    call istrlen_spec; [ eassumption | exact STRn | exact NZ | ].
    eapply SCA. eapply sinv_of; eassumption.
  Qed.
End FOPEN_PRE.

(* [comment removed for export] *)
#[using="Type"] Lemma fopen_i_pre : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (pstr prest mstr mrest : list byte),
  let PA := bv_unsigned a0 in let MA := bv_unsigned a1 in
  let NP := (Z.of_nat (length pstr) + 1)%Z in let NM := (Z.of_nat (length mstr) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> (0 < PA)%Z ->
  bytes_at asegs m PA (pstr ++ Z_to_bv 8 0 :: prest) -> ~ In (Z_to_bv 8 0) pstr ->
  (PA + Z.of_nat (length (pstr ++ Z_to_bv 8 0 :: prest)) <= lo \/ bv_unsigned sp <= PA)%Z ->
  bytes_at asegs m MA (mstr ++ Z_to_bv 8 0 :: mrest) -> ~ In (Z_to_bv 8 0) mstr ->
  (MA + Z.of_nat (length (mstr ++ Z_to_bv 8 0 :: mrest)) <= lo \/ bv_unsigned sp <= MA)%Z ->
  sobj RNG m PA (PA + NP) -> sobj RNG m MA (MA + NM) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG PA NP -> rng RNG MA NM ->
  evtF asegs RNG (fopen_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444d4) fc None m (seg_rom asegs)).
Proof.
  intros until mrest. intros PA MA NP NM MI ST LO KLO ENV PNZ STRP NONULP SEPP STRM NONULM SEPM
    (APPp & UNPp & NSZp & RLOp & RHIp & R1p & WR1p & RSH1p) (APPm & UNPm & NSZm & RLOm & RHIm & R1m & WR1m & RSH1m) RI RSTK RBp RBm.
  zstep. eapply (fopen_i_pre_body RNG) with (RLOp := RLOp) (RHIp := RHIp) (RLOm := RLOm) (RHIm := RHIm); try eassumption; subst NP NM PA MA; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fopen_i_post : forall RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp + -2144) -> stk asegs m (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  (lo <= bv_unsigned sp + -2144)%Z ->
  rng RNG (bv_unsigned sp + -64) 64 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v res a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc rav) fc None m (seg_rom asegs)
                              /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp x9 res a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x49778) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST1 STM1 FR1 SPLO RFR. pose proof (proj1 ST1) as LO0. cbv beta in LO0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  do 10 zstep.
  pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
  pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
  replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
  zstep.
  apply evtF_done. split; [reflexivity | exact SK2].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition fopen_i_entry := 0x496dc%Z.
Definition FOPEN_I_RA : Z := 0x497e0%Z.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fopen_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x12 x13 x14 x15 x16 x17 x19 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x497e0) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp a1 a0 a1 x12 x13 x14 x15 x16 x17
                  a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9aba8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144) /\ stk asegs m' (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section FOPEN_PRE.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (pstr prest mstr mrest : list byte) (RLOp RHIp RLOm RHIm : Z).
  Notation PA := (bv_unsigned a0).
  Notation MA := (bv_unsigned a1).
  Notation LP := (Z.of_nat (length pstr)).
  Notation NP := (Z.of_nat (length pstr) + 1)%Z.
  Notation LM := (Z.of_nat (length mstr)).
  Notation NM := (Z.of_nat (length mstr) + 1)%Z.
  Notation pfull := (pstr ++ Z_to_bv 8 0 :: prest).
  Notation mfull := (mstr ++ Z_to_bv 8 0 :: mrest).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis ENV : icptenv m.
  Hypothesis PNZ : (0 < PA)%Z.
  Hypothesis STRP : bytes_at asegs m PA pfull.
  Hypothesis NONULP : ~ In (Z_to_bv 8 0) pstr.
  Hypothesis SEPP : (PA + Z.of_nat (length pfull) <= lo \/ bv_unsigned sp <= PA)%Z.
  Hypothesis STRM : bytes_at asegs m MA mfull.
  Hypothesis NONULM : ~ In (Z_to_bv 8 0) mstr.
  Hypothesis SEPM : (MA + Z.of_nat (length mfull) <= lo \/ bv_unsigned sp <= MA)%Z.
  (* [comment removed for export] *)
  Hypothesis APPp : app_blk PA (PA + NP).
  Hypothesis UNPp : unpoisoned m PA (PA + NP).
  Hypothesis NSZp : (NP <= 2^40)%Z.
  Hypothesis R1p : (RLOp <= PA /\ PA + NP <= RHIp /\ RLOp mod 64 = 0 /\ RHIp mod 64 = 0 /\ 0 <= RLOp /\ RHIp <= KEND)%Z.
  Hypothesis WR1p : wr_at asegs m (shad RLOp) (shad RHIp - shad RLOp).
  Hypothesis APPm : app_blk MA (MA + NM).
  Hypothesis UNPm : unpoisoned m MA (MA + NM).
  Hypothesis NSZm : (NM <= 2^40)%Z.
  Hypothesis R1m : (RLOm <= MA /\ MA + NM <= RHIm /\ RLOm mod 64 = 0 /\ RHIm mod 64 = 0 /\ 0 <= RLOm /\ RHIm <= KEND)%Z.
  Hypothesis WR1m : wr_at asegs m (shad RLOm) (shad RHIm - shad RLOm).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RBp : rng RNG PA NP.
  Hypothesis RBm : rng RNG MA NM.
  Hypothesis RSH1p : rng RNG (shad RLOp) (shad RHIp - shad RLOp).
  Hypothesis RSH1m : rng RNG (shad RLOm) (shad RHIm - shad RLOm).

  Notation POST := (fopen_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc PA (PA + NP) /\ wr_at asegs mc (shad RLOp) (shad RHIp - shad RLOp) /\ bytes_at asegs mc PA pfull
    /\ unpoisoned mc MA (MA + NM) /\ wr_at asegs mc (shad RLOm) (shad RHIm - shad RLOm) /\ bytes_at asegs mc MA mfull
    /\ icptenv mc.

  Definition SBND1 (S N RLO RHI : Z) : Prop :=
    (1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64)%Z /\ SBND1 PA NP RLOp RHIp /\ SBND1 MA NM RLOm RHIm.
  Lemma SBND_ok : SBND.
  Proof using APPm APPp KLO LO NSZm NSZp PNZ R1m R1p SEPM SEPP ST.
    unfold SBND, SBND1. destruct ST as (LOW & _). destruct APPp as [LESp ASp]. destruct APPm as [LESm ASm]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    pose proof (bv_unsigned_in_range 64 a1) as SR1. unfold bv_modulus in SR1. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR1.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    split; [lia|]. split; (Z.div_mod_to_equations; (keep_hyps sp a0 a1 lo pstr prest mstr mrest RLOp RHIp r7 r8 q r q0 r0 q1 r1 q2 r2 q3 r3 q4 r4 q5 r5 q6 r6 q7 q8 NSZp R1p ASp H H0 H4 H5 H9 H10 H14 H15 H19 H20 H24 H25 H29 H30 H34 H35 H39 H44 RLOm RHIm NSZm R1m ASm; lia)).
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, SBND1, KHIGH, KEND in B.

  Definition SBL1 (S N RLO RHI : Z) : Prop :=
    (1 <= N /\ N <= 2^40 /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64)%Z /\ SBL1 PA NP RLOp RHIp /\ SBL1 MA NM RLOm RHIm.
  Lemma SBL_ok : SBL. Proof using APPm APPp KLO LO NSZm NSZp PNZ R1m R1p SEPM SEPP ST. pose proof SBND_ok as B. unfold SBND, SBND1, KHIGH, KEND in B. unfold SBL, SBL1. repeat split; (keep_hyps sp a0 a1 lo pstr prest mstr mrest RLOp RHIp RLOm RHIm B LO NSZp PNZ NSZm; lia). Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNPp1 & WRp1 & STRP1 & UNPm1 & WRm1 & STRM1 & ENV1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1p; change (?P) with (sf_hide P) in R1m; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPP; change (?P) with (sf_hide P) in SEPM;
    change (?P) with (sf_hide P) in UNPp; change (?P) with (sf_hide P) in WR1p; change (?P) with (sf_hide P) in UNPm; change (?P) with (sf_hide P) in WR1m;
    change (?P) with (sf_hide P) in STRP; change (?P) with (sf_hide P) in STRM.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL, SBL1 in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO ENV PNZ STRP SEPP STRM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1. pose proof SBND_ok as B. unfold SBND, SBND1, KHIGH, KEND in B.
    assert (ENV1 : icptenv mc) by (eapply icptenv_transport; [exact ENV| exact MU1| exact WM1| solve_iesafe]).
    repeat (split; [assumption|]).
    split; [exact (ie_got _ ENV1)|]. split; [exact (ie_shb _ ENV1)|]. split; [exact (ie_lay _ ENV1)|].
    assert (SSp : (shad (PA + NP - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (SSm : (shad (MA + NM - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    rewrite !length_app in SEPP, SEPM. cbn [length] in SEPP, SEPM.
    pose proof (bytes_at_bound _ _ _ _ STRP) as BBp. pose proof (bytes_at_bound _ _ _ _ STRM) as BBm.
    split. { eapply unpoisoned_munch; [exact UNPp | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split. { eapply bytes_at_transport; [exact STRP | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    split. { eapply unpoisoned_munch; [exact UNPm | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split; [| exact ENV1].
    eapply bytes_at_transport; [exact STRM | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (N : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 N) s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO PNZ SEPP SEPM APPp NSZp R1p APPm NSZm R1m RI RSTK"] Lemma SXB : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x497cc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    pose proof (ie_fopen _ ENV1) as RFO1.
    do 4 zstep. zstep.
    apply evtF_done. unfold fopen_i_mid.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO PNZ SEPP SEPM APPp NSZp R1p APPm NSZm R1m RI RSTK RSH1m"] Lemma SLB : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    SINV mc -> (1 <= NM <= 64)%Z -> Z.to_nat (shad (MA + NM - 1) - c) = k -> (shad MA <= c < shad (MA + NM - 1))%Z ->
    evtF asegs RNG POST (MS (sregs NM x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (MA + NM + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x28 x29 x30 x31)
                            F (Z_to_bv 64 0x498e0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (MA + NM - 1) = 2147450880 + Z.shiftr (MA + NM + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc MA (MA + NM) c UNPm1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SXB; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO PNZ SEPP SEPM APPp NSZp R1p APPm NSZm R1m RI RSTK RSH1m"] Lemma SEB : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31, SINV mc -> (1 <= NM <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs NM x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr MA 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (MA + NM + -1) 3))
                                   (Z_to_bv 64 (MA + NM + -1)) x13 x14 x15 x16 x17 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x498c4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc MA (MA + NM) (MA + NM + -1) 1 UNPm1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((MA + NM + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SXB; eassumption.
    - eapply (SLB mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SCB : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 LM) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49780) fc None mc (seg_rom asegs)).
  Proof using APPm APPp ENV KLO LO NSZm NSZp PNZ R1m R1p RI RSH1m RSTK SEPM SEPP ST STRM STRP UNPm UNPp WR1m WR1p.
    intros until x31. intros IV. sprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm LO; lia) | unfold KHIGH; (keep_hyps sp a0 a1 lo pstr mstr RLOp RHIp RLOm RHIm BL0; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPm | zsimp; exact UNPm1
        | zsimp; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; (keep_hyps pstr mstr RLOp RHIp RLOm RHIm NSZm; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SXB. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= NM <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (LM + MA)%Z with (MA + NM + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1m.
      destruct (shadow_probe8 asegs mc RLOm RHIm MA WRm1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1m; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLOm RHIm (MA + NM + -1) WRm1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1m; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SEB; eassumption.
      + eapply SXB; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO ENV PNZ STRP SEPP STRM NONULM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m RI RSTK RBm RSH1m"] Lemma SXA : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49778) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    zstep. zstep.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) mstr).
    { apply Forall_forall. intros b Hb E. apply NONULM. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    call istrlen_spec; [ eassumption | exact STRM1 | exact NZ | ].
    eapply SCB. eapply sinv_of; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO ENV PNZ STRP SEPP STRM NONULM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m RI RSTK RBm RSH1p RSH1m"] Lemma SLA : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    SINV mc -> (1 <= NP <= 64)%Z -> Z.to_nat (shad (PA + NP - 1) - c) = k -> (shad PA <= c < shad (PA + NP - 1))%Z ->
    evtF asegs RNG POST (MS (sregs NP x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (PA + NP + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49a24) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (PA + NP - 1) = 2147450880 + Z.shiftr (PA + NP + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc PA (PA + NP) c UNPp1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SXA; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma SEA : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31, SINV mc -> (1 <= NP <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs NP x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr PA 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (PA + NP + -1) 3))
                                   (Z_to_bv 64 (PA + NP + -1)) x13 x14 x15 x16 x17 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x49a08) fc None mc (seg_rom asegs)).
  Proof using APPm APPp ENV KLO LO NONULM NSZm NSZp PNZ R1m R1p RBm RI RSH1m RSH1p RSTK SEPM SEPP ST STRM STRP UNPm UNPp WR1m WR1p.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc PA (PA + NP) (PA + NP + -1) 1 UNPp1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((PA + NP + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; (keep_hyps pstr mstr r H0 b2 CK2; lia)).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SXA; eassumption.
    - eapply (SLA mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SCA : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 LP) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4972c) fc None mc (seg_rom asegs)).
  Proof using APPm APPp ENV KLO LO NONULM NSZm NSZp PNZ R1m R1p RBm RI RSH1m RSH1p RSTK SEPM SEPP ST STRM STRP UNPm UNPp WR1m WR1p.
    intros until x31. intros IV. sprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm LO; lia) | unfold KHIGH; (keep_hyps sp a0 a1 lo pstr mstr RLOp RHIp RLOm RHIm BL0; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPp | zsimp; exact UNPp1
        | zsimp; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; (keep_hyps pstr mstr RLOp RHIp RLOm RHIm NSZp; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo pstr mstr RLOp RHIp RLOm RHIm; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SXA. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= NP <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (LP + PA)%Z with (PA + NP + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1p.
      destruct (shadow_probe8 asegs mc RLOp RHIp PA WRp1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1p; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLOp RHIp (PA + NP + -1) WRp1 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND, SBND1 in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1p; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SEA; eassumption.
      + eapply SXA; eassumption.
  Qed.

  #[using="pstr prest mstr mrest RLOp RHIp RLOm RHIm MI ST LO KLO ENV PNZ STRP NONULP SEPP STRM NONULM SEPM APPp UNPp NSZp R1p WR1p APPm UNPm NSZm R1m WR1m RI RSTK RBp RBm RSH1p RSH1m"] Lemma fopen_i_pre_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x496dc) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL, SBL1 in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0.
    pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 13 zstep.
    zstep. call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 PNZ. lia. } clear K2.
    zstep. zstep.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) pstr).
    { apply Forall_forall. intros b Hb E. apply NONULP. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STRn : bytes_at asegs mm PA pfull) by
        (unfold sf_hide in STRP, SEPP, LO; pose proof (bytes_at_bound _ _ _ _ STRP) as BBn;
         eapply bytes_at_transport; [exact STRP | exact MU |]; cbn [disjoint_from]; clear -SEPP LO BL0 BBn; lia) end.
    call istrlen_spec; [ eassumption | exact STRn | exact NZ | ].
    eapply SCA. eapply sinv_of; eassumption.
  Qed.
End FOPEN_PRE.

(* [comment removed for export] *)
#[using="Type"] Lemma fopen_i_pre : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (pstr prest mstr mrest : list byte),
  let PA := bv_unsigned a0 in let MA := bv_unsigned a1 in
  let NP := (Z.of_nat (length pstr) + 1)%Z in let NM := (Z.of_nat (length mstr) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> (0 < PA)%Z ->
  bytes_at asegs m PA (pstr ++ Z_to_bv 8 0 :: prest) -> ~ In (Z_to_bv 8 0) pstr ->
  (PA + Z.of_nat (length (pstr ++ Z_to_bv 8 0 :: prest)) <= lo \/ bv_unsigned sp <= PA)%Z ->
  bytes_at asegs m MA (mstr ++ Z_to_bv 8 0 :: mrest) -> ~ In (Z_to_bv 8 0) mstr ->
  (MA + Z.of_nat (length (mstr ++ Z_to_bv 8 0 :: mrest)) <= lo \/ bv_unsigned sp <= MA)%Z ->
  sobj RNG m PA (PA + NP) -> sobj RNG m MA (MA + NM) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG PA NP -> rng RNG MA NM ->
  evtF asegs RNG (fopen_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4453c) fc None m (seg_rom asegs)).
Proof.
  intros until mrest. intros PA MA NP NM MI ST LO KLO ENV PNZ STRP NONULP SEPP STRM NONULM SEPM
    (APPp & UNPp & NSZp & RLOp & RHIp & R1p & WR1p & RSH1p) (APPm & UNPm & NSZm & RLOm & RHIm & R1m & WR1m & RSH1m) RI RSTK RBp RBm.
  zstep. eapply (fopen_i_pre_body RNG) with (RLOp := RLOp) (RHIp := RHIp) (RLOm := RLOm) (RHIm := RHIm); try eassumption; subst NP NM PA MA; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fopen_i_post : forall RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp + -2144) -> stk asegs m (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  (lo <= bv_unsigned sp + -2144)%Z ->
  rng RNG (bv_unsigned sp + -64) 64 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v res a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc rav) fc None m (seg_rom asegs)
                              /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp x9 res a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x497e0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST1 STM1 FR1 SPLO RFR. pose proof (proj1 ST1) as LO0. cbv beta in LO0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  do 10 zstep.
  pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
  pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
  replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
  zstep.
  apply evtF_done. split; [reflexivity | exact SK2].
Qed.
End CANSEC1.
End TwB.
End I_fopen.

(* [comment removed for export] *)
Module I_vfprintf.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread I_printf_common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation rt_ckpf m := (rw_cells asegs m 0x140178 [C8 (Z_to_bv 64 4294967296)]).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pstr_okL (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (AQ Sa : Z) (sstr : list byte) : Prop :=
  rw_cells asegs m AQ [C8 (Z_to_bv 64 Sa)] /\ (bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)
  /\ bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
  /\ (Sa + (Z.of_nat (length sstr) + 1) <= lo \/ bv_unsigned sp <= Sa) /\ 0 < Sa
  /\ sobj RNG m Sa (Sa + (Z.of_nat (length sstr) + 1))
  /\ rng RNG AQ 8 /\ rng RNG Sa (Z.of_nat (length sstr) + 1).
Fixpoint pargs_okL (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (its : list pitem) (aq : word) : Prop :=
  match its with
  | [] => True
  | PLit _ :: r => pargs_okL RNG lo sp m r aq
  | PStr Sa sstr :: r => pstr_okL RNG lo sp m (bv_unsigned aq) Sa sstr /\ pargs_okL RNG lo sp m r (Z_to_bv 64 (bv_unsigned aq + 8))
  | _ :: r => pargs_okL RNG lo sp m r (Z_to_bv 64 (bv_unsigned aq + 8))
  end.
(* [comment removed for export] *)
Fixpoint pargs_sep (W : list (Z * Z)) (its : list pitem) (aq : word) : Prop :=
  match its with
  | [] => True
  | PLit _ :: r => pargs_sep W r aq
  | PStr Sa sstr :: r => disjoint_from W (bv_unsigned aq) 8 /\ disjoint_from W Sa (Z.of_nat (length sstr) + 1)
                         /\ pargs_sep W r (Z_to_bv 64 (bv_unsigned aq + 8))
  | _ :: r => pargs_sep W r (Z_to_bv 64 (bv_unsigned aq + 8))
  end.

#[using="Type"] Lemma pargs_okL_ok : forall RNG lo sp m its aq, lo <= bv_unsigned sp - 2320 -> pargs_okL RNG lo sp m its aq -> pargs_ok RNG sp m its aq.
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros aq LO H; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL pargs_ok] in H |- *; try (apply IH; assumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR]. split; [| apply IH; assumption].
  unfold pstr_ok. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [lia|]. split; [exact H6|]. split; [exact H7|]. split; assumption.
Qed.

#[using="Type"] Lemma disjoint_from_window : forall (W : list (Z * Z)) lo hi a n,
  Forall (fun iv => lo <= fst iv /\ snd iv <= hi) W -> (a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros W lo hi a n H D. induction H as [|[u v] W Huv _ IH]; cbn [disjoint_from]; [exact I|]. cbn [fst snd] in Huv. split; [lia| exact IH].
Qed.
#[using="Type"] Lemma disjoint_from_app : forall (W1 W2 : list (Z * Z)) a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[u v] W1 IH]; intros W2 a n H1 H2; [exact H2|]. cbn [app disjoint_from] in *. destruct H1 as [H1 H1']. split; [exact H1| apply IH; assumption]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pargs_sep_stack : forall RNG lo sp m its aq W,
  pargs_okL RNG lo sp m its aq -> Forall (fun iv => lo <= fst iv /\ snd iv <= bv_unsigned sp) W -> pargs_sep W its aq.
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros aq W H HW; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL pargs_sep] in H |- *; try (eapply IH; eassumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR].
  split; [eapply disjoint_from_window; [exact HW| lia]|]. split; [eapply disjoint_from_window; [exact HW| lia]|]. eapply IH; eassumption.
Qed.
#[using="Type"] Lemma pargs_sep_app : forall W1 W2 its aq, pargs_sep W1 its aq -> pargs_sep W2 its aq -> pargs_sep (W1 ++ W2) its aq.
Proof.
  intros W1 W2 its. induction its as [|it its IH]; intros aq H1 H2; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_sep] in H1, H2 |- *; try (apply IH; assumption).
  destruct H1 as (A1 & A2 & A3). destruct H2 as (B1 & B2 & B3).
  split; [apply disjoint_from_app; assumption|]. split; [apply disjoint_from_app; assumption| apply IH; assumption].
Qed.

Definition pargs_okL_transport__stmt : Prop := forall RNG lo sp sp' m m' W its aq,
  pargs_okL RNG lo sp m its aq -> munch W m m' -> wmono asegs m m' -> appW W -> pargs_sep W its aq ->
  bv_unsigned sp' <= bv_unsigned sp ->
  pargs_okL RNG lo sp' m' its aq.
Section Sz6.
Variables RNG lo sp sp' m m' W : ltac2:(SecDiet.SzSec.tyM 'pargs_okL_transport__stmt "vvvvvvvk" @RNG).
#[using="Type"] Lemma pargs_okL_transport__body : ltac2:(SecDiet.SzSec.bodyP 'pargs_okL_transport__stmt "vvvvvvvk").
Proof.
  intros its.
 induction its as [|it its IH]; intros aq H MU WM AW SEP LE; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL pargs_sep] in H, SEP |- *; try (apply IH; assumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR]. destruct SEP as (S1 & S2 & S3).
  split; [| apply IH; assumption].
  unfold pstr_okL. split; [eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact S1]|]. split; [lia|].
  split; [eapply bytes_at_transport; [exact H3| exact MU|]; rewrite length_app; cbn [length];
          replace (Z.of_nat (length sstr + 1)) with (Z.of_nat (length sstr) + 1) by lia; exact S2|].
  split; [exact H4|]. split; [lia|]. split; [exact H6|]. split; [eapply sobj_transport; eassumption|]. split; assumption.
Qed.
End Sz6.
#[using="Type"] Lemma pargs_okL_transport : ltac:(let t := eval cbv delta [pargs_okL_transport__stmt] in pargs_okL_transport__stmt in exact t).
Proof. intros RNG lo sp sp' m m' W its. ltac2:(SecDiet.SzSec.closeP 'pargs_okL_transport__body "vvvvvvvk"). Qed.
#[using="Type"] Lemma fp_le_pargs_okL : forall RNG RNG' lo sp m its aq, ITreeA.fp_le RNG RNG' -> pargs_okL RNG lo sp m its aq -> pargs_okL RNG' lo sp m its aq.
Proof.
  intros RNG RNG' lo sp m its. induction its as [|it its IH]; intros aq FP H; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL] in H |- *; try (apply IH; assumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR]. split; [| apply IH; assumption].
  unfold pstr_okL. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [eapply fp_le_sobj; eassumption|]. split; eapply ITreeA.rng_fp_le; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47dd4) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vfprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j16,
    ms' = MS (mkR (Z_to_bv 64 0x47dd4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  a1 a0 a0 a1 a2 x13 x14 x15 x16 x17
                  a2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9aee0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra].

Definition vfprintf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2368 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a1 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a2 ->
  evtF asegs RNG (vfprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444a0) fc None m (seg_rom asegs)).
Section Sz9.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'vfprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma vfprintf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO ENV CKP A1 FB NOZ SEPF SO RI RSTK RFM EF OK AOK.
  pose proof (munch_refl [(bv_unsigned sp + -2368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 9 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -48)) m0 its a2).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply pargs_okL_transport; [exact AOK | exact MU | exact WM | solve_appW
                                | eapply pargs_sep_stack; [exact AOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 5 zstep. zstep.
  apply evtF_done. unfold vfprintf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz9.
#[using="Type"] Lemma vfprintf_i_pre : ltac:(let t := eval cbv delta [vfprintf_i_pre__stmt] in vfprintf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'vfprintf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation rt_ckpf m := (rw_cells asegs m 0x140578 [C8 (Z_to_bv 64 4294967296)]).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pstr_okL (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (AQ Sa : Z) (sstr : list byte) : Prop :=
  rw_cells asegs m AQ [C8 (Z_to_bv 64 Sa)] /\ (bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)
  /\ bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
  /\ (Sa + (Z.of_nat (length sstr) + 1) <= lo \/ bv_unsigned sp <= Sa) /\ 0 < Sa
  /\ sobj RNG m Sa (Sa + (Z.of_nat (length sstr) + 1))
  /\ rng RNG AQ 8 /\ rng RNG Sa (Z.of_nat (length sstr) + 1).
Fixpoint pargs_okL (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (its : list pitem) (aq : word) : Prop :=
  match its with
  | [] => True
  | PLit _ :: r => pargs_okL RNG lo sp m r aq
  | PStr Sa sstr :: r => pstr_okL RNG lo sp m (bv_unsigned aq) Sa sstr /\ pargs_okL RNG lo sp m r (Z_to_bv 64 (bv_unsigned aq + 8))
  | _ :: r => pargs_okL RNG lo sp m r (Z_to_bv 64 (bv_unsigned aq + 8))
  end.
(* [comment removed for export] *)
Fixpoint pargs_sep (W : list (Z * Z)) (its : list pitem) (aq : word) : Prop :=
  match its with
  | [] => True
  | PLit _ :: r => pargs_sep W r aq
  | PStr Sa sstr :: r => disjoint_from W (bv_unsigned aq) 8 /\ disjoint_from W Sa (Z.of_nat (length sstr) + 1)
                         /\ pargs_sep W r (Z_to_bv 64 (bv_unsigned aq + 8))
  | _ :: r => pargs_sep W r (Z_to_bv 64 (bv_unsigned aq + 8))
  end.

#[using="Type"] Lemma pargs_okL_ok : forall RNG lo sp m its aq, lo <= bv_unsigned sp - 2320 -> pargs_okL RNG lo sp m its aq -> pargs_ok RNG sp m its aq.
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros aq LO H; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL pargs_ok] in H |- *; try (apply IH; assumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR]. split; [| apply IH; assumption].
  unfold pstr_ok. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [lia|]. split; [exact H6|]. split; [exact H7|]. split; assumption.
Qed.

#[using="Type"] Lemma disjoint_from_window : forall (W : list (Z * Z)) lo hi a n,
  Forall (fun iv => lo <= fst iv /\ snd iv <= hi) W -> (a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros W lo hi a n H D. induction H as [|[u v] W Huv _ IH]; cbn [disjoint_from]; [exact I|]. cbn [fst snd] in Huv. split; [lia| exact IH].
Qed.
#[using="Type"] Lemma disjoint_from_app : forall (W1 W2 : list (Z * Z)) a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[u v] W1 IH]; intros W2 a n H1 H2; [exact H2|]. cbn [app disjoint_from] in *. destruct H1 as [H1 H1']. split; [exact H1| apply IH; assumption]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pargs_sep_stack : forall RNG lo sp m its aq W,
  pargs_okL RNG lo sp m its aq -> Forall (fun iv => lo <= fst iv /\ snd iv <= bv_unsigned sp) W -> pargs_sep W its aq.
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros aq W H HW; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL pargs_sep] in H |- *; try (eapply IH; eassumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR].
  split; [eapply disjoint_from_window; [exact HW| lia]|]. split; [eapply disjoint_from_window; [exact HW| lia]|]. eapply IH; eassumption.
Qed.
#[using="Type"] Lemma pargs_sep_app : forall W1 W2 its aq, pargs_sep W1 its aq -> pargs_sep W2 its aq -> pargs_sep (W1 ++ W2) its aq.
Proof.
  intros W1 W2 its. induction its as [|it its IH]; intros aq H1 H2; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_sep] in H1, H2 |- *; try (apply IH; assumption).
  destruct H1 as (A1 & A2 & A3). destruct H2 as (B1 & B2 & B3).
  split; [apply disjoint_from_app; assumption|]. split; [apply disjoint_from_app; assumption| apply IH; assumption].
Qed.

Definition pargs_okL_transport__stmt : Prop := forall RNG lo sp sp' m m' W its aq,
  pargs_okL RNG lo sp m its aq -> munch W m m' -> wmono asegs m m' -> appW W -> pargs_sep W its aq ->
  bv_unsigned sp' <= bv_unsigned sp ->
  pargs_okL RNG lo sp' m' its aq.
Section Sz6.
Variables RNG lo sp sp' m m' W : ltac2:(SecDiet.SzSec.tyM 'pargs_okL_transport__stmt "vvvvvvvk" @RNG).
#[using="Type"] Lemma pargs_okL_transport__body : ltac2:(SecDiet.SzSec.bodyP 'pargs_okL_transport__stmt "vvvvvvvk").
Proof.
  intros its.
 induction its as [|it its IH]; intros aq H MU WM AW SEP LE; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL pargs_sep] in H, SEP |- *; try (apply IH; assumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR]. destruct SEP as (S1 & S2 & S3).
  split; [| apply IH; assumption].
  unfold pstr_okL. split; [eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact S1]|]. split; [lia|].
  split; [eapply bytes_at_transport; [exact H3| exact MU|]; rewrite length_app; cbn [length];
          replace (Z.of_nat (length sstr + 1)) with (Z.of_nat (length sstr) + 1) by lia; exact S2|].
  split; [exact H4|]. split; [lia|]. split; [exact H6|]. split; [eapply sobj_transport; eassumption|]. split; assumption.
Qed.
End Sz6.
#[using="Type"] Lemma pargs_okL_transport : ltac:(let t := eval cbv delta [pargs_okL_transport__stmt] in pargs_okL_transport__stmt in exact t).
Proof. intros RNG lo sp sp' m m' W its. ltac2:(SecDiet.SzSec.closeP 'pargs_okL_transport__body "vvvvvvvk"). Qed.
#[using="Type"] Lemma fp_le_pargs_okL : forall RNG RNG' lo sp m its aq, ITreeA.fp_le RNG RNG' -> pargs_okL RNG lo sp m its aq -> pargs_okL RNG' lo sp m its aq.
Proof.
  intros RNG RNG' lo sp m its. induction its as [|it its IH]; intros aq FP H; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pargs_okL] in H |- *; try (apply IH; assumption).
  destruct H as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HR]. split; [| apply IH; assumption].
  unfold pstr_okL. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [eapply fp_le_sobj; eassumption|]. split; eapply ITreeA.rng_fp_le; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47e3c) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vfprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j16,
    ms' = MS (mkR (Z_to_bv 64 0x47e3c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  a1 a0 a0 a1 a2 x13 x14 x15 x16 x17
                  a2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9b2c4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra].

Definition vfprintf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2368 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a1 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a2 ->
  evtF asegs RNG (vfprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44508) fc None m (seg_rom asegs)).
Section Sz9.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'vfprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma vfprintf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO ENV CKP A1 FB NOZ SEPF SO RI RSTK RFM EF OK AOK.
  pose proof (munch_refl [(bv_unsigned sp + -2368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 9 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -48)) m0 its a2).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply pargs_okL_transport; [exact AOK | exact MU | exact WM | solve_appW
                                | eapply pargs_sep_stack; [exact AOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 5 zstep. zstep.
  apply evtF_done. unfold vfprintf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz9.
#[using="Type"] Lemma vfprintf_i_pre : ltac:(let t := eval cbv delta [vfprintf_i_pre__stmt] in vfprintf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'vfprintf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End I_vfprintf.

(* [comment removed for export] *)
Module I_printf_words.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition pstrL (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (Sa : Z) (sstr : list byte) : Prop :=
  bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
  /\ (Sa + (Z.of_nat (length sstr) + 1) <= lo \/ bv_unsigned sp <= Sa) /\ 0 < Sa
  /\ sobj RNG m Sa (Sa + (Z.of_nat (length sstr) + 1)) /\ rng RNG Sa (Z.of_nat (length sstr) + 1).
(* [comment removed for export] *)
Fixpoint pwords_ok (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (its : list pitem) (ws : list word) : Prop :=
  match its with
  | [] => True
  | PLit _ :: r => pwords_ok RNG lo sp m r ws
  | PStr Sa sstr :: r => match ws with w :: ws' => w = Z_to_bv 64 Sa /\ pstrL RNG lo sp m Sa sstr /\ pwords_ok RNG lo sp m r ws' | [] => False end
  | _ :: r => match ws with _ :: ws' => pwords_ok RNG lo sp m r ws' | [] => False end
  end.
(* [comment removed for export] *)
Fixpoint pstrs_sep (W : list (Z * Z)) (its : list pitem) : Prop :=
  match its with
  | [] => True
  | PStr Sa sstr :: r => disjoint_from W Sa (Z.of_nat (length sstr) + 1) /\ pstrs_sep W r
  | _ :: r => pstrs_sep W r
  end.

#[using="Type"] Lemma pwords_ok_more : forall RNG lo sp m its ws more, pwords_ok RNG lo sp m its ws -> pwords_ok RNG lo sp m its (ws ++ more).
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros ws more H; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok] in H |- *; try (apply IH; exact H);
    (destruct ws as [|w ws]; [destruct H|]); cbn [app]; try (apply IH; exact H).
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2| apply IH; exact H3].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pargs_okL_of_words : forall RNG lo sp m its ws VA,
  pwords_ok RNG lo sp m its ws -> rw_cells asegs m VA (map C8 ws) ->
  bv_unsigned sp <= VA -> VA + 8 * Z.of_nat (length ws) <= 2^64 -> rng RNG VA (8 * Z.of_nat (length ws)) ->
  pargs_okL RNG lo sp m its (Z_to_bv 64 VA).
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros ws VA H CE HV HH RG; [exact I|].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (STEP : forall w ws', ws = w :: ws' ->
            bv_unsigned (Z_to_bv 64 VA) = VA /\ rw_cells asegs m VA [C8 w] /\ rw_cells asegs m (VA + 8) (map C8 ws')
            /\ bv_unsigned sp <= VA + 8 /\ VA + 8 + 8 * Z.of_nat (length ws') <= 2^64 /\ rng RNG VA 8 /\ rng RNG (VA + 8) (8 * Z.of_nat (length ws'))).
  { intros w ws' ->. cbn [map length] in *.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in CE. destruct CE as [C1 C2]. cbn [cells_size csize Nat.add] in C2.
    split; [apply unsigned_lit; lia|]. split; [exact C1|]. split; [exact C2|]. split; [lia|]. split; [lia|].
    split; (eapply rng_sub'; [exact RG | lia]). }
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pargs_okL] in H |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); destruct (STEP w ws' eq_refl) as (EV & C1 & C2 & S1 & S2 & R1 & R2); rewrite EV;
    try (eapply IH; eassumption).
  destruct H as (-> & (B1 & B2 & B3 & B4 & B5 & B6) & HR).
  split; [| eapply IH; eassumption].
  unfold pstr_okL. split; [exact C1|]. split; [lia|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [exact B5|]. split; [exact R1 | exact B6].
Qed.
#[using="Type"] Lemma pargs_sep_of_words : forall RNG lo sp m W its ws VA,
  pwords_ok RNG lo sp m its ws -> pstrs_sep W its -> disjoint_from W VA (8 * Z.of_nat (length ws)) -> 0 <= VA -> VA + 8 * Z.of_nat (length ws) <= 2^64 ->
  pargs_sep W its (Z_to_bv 64 VA).
Proof.
  intros RNG lo sp m W its. induction its as [|it its IH]; intros ws VA H HS HD HV HH; [exact I|].
  assert (SUB : forall a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n').
  { clear. induction W as [|[u v] W IHW]; intros a n a' n' Hd H1 H2; cbn [disjoint_from] in *; [exact I|]. destruct Hd as [Hd1 Hd2]. split; [lia| eapply IHW; eassumption]. }
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pargs_sep pstrs_sep] in H, HS |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); cbn [length] in HD, HH;
    assert (EV : bv_unsigned (Z_to_bv 64 VA) = VA) by (apply unsigned_lit; lia); rewrite EV;
    try (eapply IH; [eassumption | eassumption | eapply SUB; [exact HD | lia | lia] | lia | lia]).
  destruct H as (-> & HP & HR). destruct HS as [HS1 HS2].
  split; [eapply SUB; [exact HD | lia | lia]|]. split; [exact HS1|].
  eapply IH; [exact HR | exact HS2 | eapply SUB; [exact HD | lia | lia] | lia | lia].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma pwords_ok_transport : forall RNG lo sp sp' m m' W its ws,
  pwords_ok RNG lo sp m its ws -> munch W m m' -> wmono asegs m m' -> appW W -> pstrs_sep W its ->
  bv_unsigned sp' <= bv_unsigned sp ->
  pwords_ok RNG lo sp' m' its ws.
Proof.
  intros RNG lo sp sp' m m' W its. induction its as [|it its IH]; intros ws H MU WM AW SEP LE; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pstrs_sep] in H, SEP |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); try (eapply IH; eassumption).
  destruct H as (-> & (B1 & B2 & B3 & B4 & B5 & B6) & HR). destruct SEP as [S1 S2].
  split; [reflexivity|]. split; [| eapply IH; eassumption].
  unfold pstrL. split; [eapply bytes_at_transport; [exact B1 | exact MU |]; rewrite length_app; cbn [length];
                        replace (Z.of_nat (length sstr + 1)) with (Z.of_nat (length sstr) + 1) by lia; exact S1|].
  split; [exact B2|]. split; [lia|]. split; [exact B4|]. split; [eapply sobj_transport; eassumption | exact B6].
Qed.
#[using="Type"] Lemma pstrs_sep_stack : forall RNG lo sp m its ws W,
  pwords_ok RNG lo sp m its ws -> Forall (fun iv => lo <= fst iv /\ snd iv <= bv_unsigned sp) W -> pstrs_sep W its.
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros ws W H HW; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pstrs_sep] in H |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); try (eapply IH; eassumption).
  destruct H as (-> & (B1 & B2 & B3 & B4 & B5 & B6) & HR).
  split; [eapply disjoint_from_window; [exact HW | lia] | eapply IH; eassumption].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition pstrL (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (Sa : Z) (sstr : list byte) : Prop :=
  bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
  /\ (Sa + (Z.of_nat (length sstr) + 1) <= lo \/ bv_unsigned sp <= Sa) /\ 0 < Sa
  /\ sobj RNG m Sa (Sa + (Z.of_nat (length sstr) + 1)) /\ rng RNG Sa (Z.of_nat (length sstr) + 1).
(* [comment removed for export] *)
Fixpoint pwords_ok (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (its : list pitem) (ws : list word) : Prop :=
  match its with
  | [] => True
  | PLit _ :: r => pwords_ok RNG lo sp m r ws
  | PStr Sa sstr :: r => match ws with w :: ws' => w = Z_to_bv 64 Sa /\ pstrL RNG lo sp m Sa sstr /\ pwords_ok RNG lo sp m r ws' | [] => False end
  | _ :: r => match ws with _ :: ws' => pwords_ok RNG lo sp m r ws' | [] => False end
  end.
(* [comment removed for export] *)
Fixpoint pstrs_sep (W : list (Z * Z)) (its : list pitem) : Prop :=
  match its with
  | [] => True
  | PStr Sa sstr :: r => disjoint_from W Sa (Z.of_nat (length sstr) + 1) /\ pstrs_sep W r
  | _ :: r => pstrs_sep W r
  end.

#[using="Type"] Lemma pwords_ok_more : forall RNG lo sp m its ws more, pwords_ok RNG lo sp m its ws -> pwords_ok RNG lo sp m its (ws ++ more).
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros ws more H; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok] in H |- *; try (apply IH; exact H);
    (destruct ws as [|w ws]; [destruct H|]); cbn [app]; try (apply IH; exact H).
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2| apply IH; exact H3].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pargs_okL_of_words : forall RNG lo sp m its ws VA,
  pwords_ok RNG lo sp m its ws -> rw_cells asegs m VA (map C8 ws) ->
  bv_unsigned sp <= VA -> VA + 8 * Z.of_nat (length ws) <= 2^64 -> rng RNG VA (8 * Z.of_nat (length ws)) ->
  pargs_okL RNG lo sp m its (Z_to_bv 64 VA).
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros ws VA H CE HV HH RG; [exact I|].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (STEP : forall w ws', ws = w :: ws' ->
            bv_unsigned (Z_to_bv 64 VA) = VA /\ rw_cells asegs m VA [C8 w] /\ rw_cells asegs m (VA + 8) (map C8 ws')
            /\ bv_unsigned sp <= VA + 8 /\ VA + 8 + 8 * Z.of_nat (length ws') <= 2^64 /\ rng RNG VA 8 /\ rng RNG (VA + 8) (8 * Z.of_nat (length ws'))).
  { intros w ws' ->. cbn [map length] in *.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in CE. destruct CE as [C1 C2]. cbn [cells_size csize Nat.add] in C2.
    split; [apply unsigned_lit; lia|]. split; [exact C1|]. split; [exact C2|]. split; [lia|]. split; [lia|].
    split; (eapply rng_sub'; [exact RG | lia]). }
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pargs_okL] in H |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); destruct (STEP w ws' eq_refl) as (EV & C1 & C2 & S1 & S2 & R1 & R2); rewrite EV;
    try (eapply IH; eassumption).
  destruct H as (-> & (B1 & B2 & B3 & B4 & B5 & B6) & HR).
  split; [| eapply IH; eassumption].
  unfold pstr_okL. split; [exact C1|]. split; [lia|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [exact B5|]. split; [exact R1 | exact B6].
Qed.
#[using="Type"] Lemma pargs_sep_of_words : forall RNG lo sp m W its ws VA,
  pwords_ok RNG lo sp m its ws -> pstrs_sep W its -> disjoint_from W VA (8 * Z.of_nat (length ws)) -> 0 <= VA -> VA + 8 * Z.of_nat (length ws) <= 2^64 ->
  pargs_sep W its (Z_to_bv 64 VA).
Proof.
  intros RNG lo sp m W its. induction its as [|it its IH]; intros ws VA H HS HD HV HH; [exact I|].
  assert (SUB : forall a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n').
  { clear. induction W as [|[u v] W IHW]; intros a n a' n' Hd H1 H2; cbn [disjoint_from] in *; [exact I|]. destruct Hd as [Hd1 Hd2]. split; [lia| eapply IHW; eassumption]. }
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pargs_sep pstrs_sep] in H, HS |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); cbn [length] in HD, HH;
    assert (EV : bv_unsigned (Z_to_bv 64 VA) = VA) by (apply unsigned_lit; lia); rewrite EV;
    try (eapply IH; [eassumption | eassumption | eapply SUB; [exact HD | lia | lia] | lia | lia]).
  destruct H as (-> & HP & HR). destruct HS as [HS1 HS2].
  split; [eapply SUB; [exact HD | lia | lia]|]. split; [exact HS1|].
  eapply IH; [exact HR | exact HS2 | eapply SUB; [exact HD | lia | lia] | lia | lia].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma pwords_ok_transport : forall RNG lo sp sp' m m' W its ws,
  pwords_ok RNG lo sp m its ws -> munch W m m' -> wmono asegs m m' -> appW W -> pstrs_sep W its ->
  bv_unsigned sp' <= bv_unsigned sp ->
  pwords_ok RNG lo sp' m' its ws.
Proof.
  intros RNG lo sp sp' m m' W its. induction its as [|it its IH]; intros ws H MU WM AW SEP LE; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pstrs_sep] in H, SEP |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); try (eapply IH; eassumption).
  destruct H as (-> & (B1 & B2 & B3 & B4 & B5 & B6) & HR). destruct SEP as [S1 S2].
  split; [reflexivity|]. split; [| eapply IH; eassumption].
  unfold pstrL. split; [eapply bytes_at_transport; [exact B1 | exact MU |]; rewrite length_app; cbn [length];
                        replace (Z.of_nat (length sstr + 1)) with (Z.of_nat (length sstr) + 1) by lia; exact S1|].
  split; [exact B2|]. split; [lia|]. split; [exact B4|]. split; [eapply sobj_transport; eassumption | exact B6].
Qed.
#[using="Type"] Lemma pstrs_sep_stack : forall RNG lo sp m its ws W,
  pwords_ok RNG lo sp m its ws -> Forall (fun iv => lo <= fst iv /\ snd iv <= bv_unsigned sp) W -> pstrs_sep W its.
Proof.
  intros RNG lo sp m its. induction its as [|it its IH]; intros ws W H HW; [exact I|].
  destruct it as [l|bc|bc| |Sa sstr]; cbn [pwords_ok pstrs_sep] in H |- *; try (eapply IH; eassumption);
    (destruct ws as [|w ws']; [destruct H|]); try (eapply IH; eassumption).
  destruct H as (-> & (B1 & B2 & B3 & B4 & B5 & B6) & HR).
  split; [eapply disjoint_from_window; [exact HW | lia] | eapply IH; eassumption].
Qed.
End CANSEC1.
End TwB.
End I_printf_words.

(* [comment removed for export] *)
Module I_printf_icpt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread I_printf_common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47264) fc None m (seg_rom asegs)).
Proof.
  intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma printf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (va : list cell) (rav s0v s1v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) ([CB 24 j24; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 64%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x481d0) fc None m (seg_rom asegs)).
Proof.
  intros until s1v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x482cc) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j32,
    ms' = MS (mkR (Z_to_bv 64 0x482cc) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2
                  a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
                  (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9aee0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2432, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells asegs m' (bv_unsigned sp + -112)
         [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Definition fprintf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2432 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a1 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pwords_ok RNG lo sp m its [a2; a3; a4; a5; a6; a7] ->
  evtF asegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444ac) fc None m (seg_rom asegs)).
Section Sz4.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'fprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fprintf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV CKP A1 FB NOZ SEPF SO RI RSTK RFM EF OK PWOK.
  pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 112%nat ST.
  do 15 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  zstep. zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  pose proof FR as FRc.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
  replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAc by lia.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -112)) m0 its (Z_to_bv 64 (bv_unsigned sp + -48))).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply (pargs_okL_of_words RNG lo _ m0 its [a2; a3; a4; a5; a6; a7]); [| exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia | cbn [length]; eapply rng_sub'; [exact RSTK | lia]].
    eapply pwords_ok_transport; [exact PWOK | exact MU | exact WM | solve_appW
                                | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 3 zstep. zstep. zstep. zstep. zstep. zstep.
  apply evtF_done. unfold fprintf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3; c4] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz4.
#[using="Type"] Lemma fprintf_i_pre : ltac:(let t := eval cbv delta [fprintf_i_pre__stmt] in fprintf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'fprintf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition printf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j8,
    ms' = MS (mkR (Z_to_bv 64 0x481d0) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2
                  a0 (Z_to_bv 64 (bv_unsigned sp + -56)) a0 (Z_to_bv 64 (bv_unsigned sp + -56)) x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9dff0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2432, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells asegs m' (bv_unsigned sp + -112)
         ([CB 24 j24; C8 s1; C8 s0; C8 ra] ++ [CB 8 j8; C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).

Definition printf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2432 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a0 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pwords_ok RNG lo sp m its [a1; a2; a3; a4; a5; a6; a7] ->
  evtF asegs RNG (printf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444a8) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'printf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma printf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'printf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV CKP A0 FB NOZ SEPF SO RI RSTK RFM EF OK PWOK.
  pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 112%nat ST.
  do 14 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  zstep. zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  pose proof FR as FRc.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
  replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -56) in VAc by lia.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -112)) m0 its (Z_to_bv 64 (bv_unsigned sp + -56))).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply (pargs_okL_of_words RNG lo _ m0 its [a1; a2; a3; a4; a5; a6; a7]);
      [| exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia | cbn [length]; eapply rng_sub'; [exact RSTK | lia]].
    eapply pwords_ok_transport; [exact PWOK | exact MU | exact WM | solve_appW
                                | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 3 zstep. zstep. zstep. zstep.
  apply evtF_done. unfold printf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz5.
#[using="Type"] Lemma printf_i_pre : ltac:(let t := eval cbv delta [printf_i_pre__stmt] in printf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'printf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24,
    ms' = MS (mkR (Z_to_bv 64 0x47264) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  a0 a1 a0 a1 x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9dff0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 24 j24; C8 s1; C8 s0; C8 ra].

Definition vprintf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2368 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a0 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a1 ->
  evtF asegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4449c) fc None m (seg_rom asegs)).
Section Sz6.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'vprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma vprintf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV CKP A0 FB NOZ SEPF SO RI RSTK RFM EF OK AOK.
  pose proof (munch_refl [(bv_unsigned sp + -2368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 7 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -48)) m0 its a1).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply pargs_okL_transport; [exact AOK | exact MU | exact WM | solve_appW
                                | eapply pargs_sep_stack; [exact AOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 4 zstep. zstep.
  apply evtF_done. unfold vprintf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz6.
#[using="Type"] Lemma vprintf_i_pre : ltac:(let t := eval cbv delta [vprintf_i_pre__stmt] in vprintf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'vprintf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x472cc) fc None m (seg_rom asegs)).
Proof.
  intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma printf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (va : list cell) (rav s0v s1v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) ([CB 24 j24; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 64%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x48238) fc None m (seg_rom asegs)).
Proof.
  intros until s1v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x48334) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j32,
    ms' = MS (mkR (Z_to_bv 64 0x48334) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2
                  a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
                  (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9b2c4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2432, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells asegs m' (bv_unsigned sp + -112)
         [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Definition fprintf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2432 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a1 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pwords_ok RNG lo sp m its [a2; a3; a4; a5; a6; a7] ->
  evtF asegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44514) fc None m (seg_rom asegs)).
Section Sz4.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'fprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fprintf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV CKP A1 FB NOZ SEPF SO RI RSTK RFM EF OK PWOK.
  pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 112%nat ST.
  do 15 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  zstep. zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  pose proof FR as FRc.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
  replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAc by lia.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -112)) m0 its (Z_to_bv 64 (bv_unsigned sp + -48))).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply (pargs_okL_of_words RNG lo _ m0 its [a2; a3; a4; a5; a6; a7]); [| exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia | cbn [length]; eapply rng_sub'; [exact RSTK | lia]].
    eapply pwords_ok_transport; [exact PWOK | exact MU | exact WM | solve_appW
                                | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 3 zstep. zstep. zstep. zstep. zstep. zstep.
  apply evtF_done. unfold fprintf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3; c4] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz4.
#[using="Type"] Lemma fprintf_i_pre : ltac:(let t := eval cbv delta [fprintf_i_pre__stmt] in fprintf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'fprintf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition printf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j8,
    ms' = MS (mkR (Z_to_bv 64 0x48238) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2
                  a0 (Z_to_bv 64 (bv_unsigned sp + -56)) a0 (Z_to_bv 64 (bv_unsigned sp + -56)) x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e3d4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2432, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells asegs m' (bv_unsigned sp + -112)
         ([CB 24 j24; C8 s1; C8 s0; C8 ra] ++ [CB 8 j8; C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).

Definition printf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2432 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a0 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pwords_ok RNG lo sp m its [a1; a2; a3; a4; a5; a6; a7] ->
  evtF asegs RNG (printf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44510) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'printf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma printf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'printf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV CKP A0 FB NOZ SEPF SO RI RSTK RFM EF OK PWOK.
  pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 112%nat ST.
  do 14 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  zstep. zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  pose proof FR as FRc.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
  replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -56) in VAc by lia.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -112)) m0 its (Z_to_bv 64 (bv_unsigned sp + -56))).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply (pargs_okL_of_words RNG lo _ m0 its [a1; a2; a3; a4; a5; a6; a7]);
      [| exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia | cbn [length]; eapply rng_sub'; [exact RSTK | lia]].
    eapply pwords_ok_transport; [exact PWOK | exact MU | exact WM | solve_appW
                                | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 3 zstep. zstep. zstep. zstep.
  apply evtF_done. unfold printf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz5.
#[using="Type"] Lemma printf_i_pre : ltac:(let t := eval cbv delta [printf_i_pre__stmt] in printf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'printf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24,
    ms' = MS (mkR (Z_to_bv 64 0x472cc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  a0 a1 a0 a1 x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e3d4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -2368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 24 j24; C8 s1; C8 s0; C8 ra].

Definition vprintf_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2368 -> KHIGH <= lo ->
  icptenv m -> rt_ckpf m -> a0 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT) ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a1 ->
  evtF asegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44504) fc None m (seg_rom asegs)).
Section Sz6.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'vprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma vprintf_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV CKP A0 FB NOZ SEPF SO RI RSTK RFM EF OK AOK.
  pose proof (munch_refl [(bv_unsigned sp + -2368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_printf _ ENV) as RPFc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  zstep. (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 7 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -48)) m0 its a1).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply pargs_okL_transport; [exact AOK | exact MU | exact WM | solve_appW
                                | eapply pargs_sep_stack; [exact AOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 4 zstep. zstep.
  apply evtF_done. unfold vprintf_i_mid.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
    lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
      pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3] rest FRa) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
  do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed.
End Sz6.
#[using="Type"] Lemma vprintf_i_pre : ltac:(let t := eval cbv delta [vprintf_i_pre__stmt] in vprintf_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'vprintf_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End I_printf_icpt.

(* [comment removed for export] *)
Module I_vsnprintf.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen I_fread I_printf_common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition VSNPRINTF_I_RA : Z := 0x47eac%Z.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vsnprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x14 x15 x16 x17 t3 t4 t5 t6 (j8 : list byte) m',
    ms' = MS (mkR (Z_to_bv 64 0x47eac) (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2
                  sp a2 a0 a1 a2 a3 x14 x15 x16 x17
                  a0 a1 (Z_to_bv 64 0x140128) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e00c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -4480, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2160) /\ stk asegs m' (bv_unsigned sp + -2160) (bv_unsigned sp + -96)
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [C8 a3; C8 a3; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition vsnprintf_i_pre_e__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4480)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> rt_ckpf m -> a2 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT)%Z ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a3 ->
  evtF asegs RNG (vsnprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47e18) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_i_pre_e__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma vsnprintf_i_pre_e__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_i_pre_e__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO ENV CKP A2 FB NOZ SEPF SO RI RSTK RFM EF OK AOK.
  pose proof (munch_refl [(bv_unsigned sp + -4480, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_vsnprintf _ ENV) as RVSc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  carve_frame 96%nat ST.
  destruct (stk_split _ _ lo (bv_unsigned sp + -2160)%Z _ ST ltac:(lia)) as [ST1 STM]. clear ST.
  do 17 zstep.
  zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -2160)) m0 its a3).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply pargs_okL_transport; [exact AOK | exact MU | exact WM | solve_appW
                                | eapply pargs_sep_stack; [exact AOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  apply evtF_done. unfold vsnprintf_i_mid.
  do 13 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  exact FR.
Qed.
End Sz1.
#[using="Type"] Lemma vsnprintf_i_pre_e : ltac:(let t := eval cbv delta [vsnprintf_i_pre_e__stmt] in vsnprintf_i_pre_e__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_i_pre_e__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vsnprintf_i_pre : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4480)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> rt_ckpf m -> a2 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT)%Z ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a3 ->
  evtF asegs RNG (vsnprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444a4) fc None m (seg_rom asegs)).
Proof. intros. zstep. eapply vsnprintf_i_pre_e; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VSN_POST.
  Variables (RNG : footprint) (sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (lo D n r RLO RHI : Z) (j24 : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word).
  Notation SAVES := [CB 24 j24; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST1 : stk asegs m lo (bv_unsigned sp + -2160).
  Hypothesis STM : stk asegs m (bv_unsigned sp + -2160) (bv_unsigned sp + -96).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -96) SAVES.
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis HN : (1 <= n < 2^31)%Z.
  Hypothesis HR : (0 <= r <= 2^31 - 1)%Z.
  (* [comment removed for export] *)
  Hypothesis APP : app_blk D (D + n).
  Hypothesis UNP : unpoisoned m D (D + n).
  Hypothesis R1 : (RLO <= D /\ D + n <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis DPOS : (0 < D)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Definition vsnprintf_i_post_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).
  Notation POST := vsnprintf_i_post_post.

  Definition VINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -96) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2160) /\ stk asegs mc (bv_unsigned sp + -2160) (bv_unsigned sp + -96)
    /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc D (D + n) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition VBND (N : Z) : Prop :=
    ((0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64)
     /\ 1 <= N /\ N <= n /\ n < 2^31
     /\ 0 < D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad D /\ shad (D + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= D /\ D + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m ST1 LO KLO HN APP R1 DPOS"] Lemma VBND_ok : forall N, (1 <= N <= n)%Z -> VBND N.
  Proof.
    intros N HNN. unfold VBND. destruct ST1 as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    split; [lia|]. Z.div_mod_to_equations; lia.
  Qed.
  Ltac acc_facts B ::=
    first [ match goal with HNN : (1 <= ?N <= n)%Z |- _ => pose proof (VBND_ok N HNN) as B end
          | pose proof (VBND_ok 1%Z ltac:(clear - HN; lia)) as B ];
    unfold VBND, KHIGH, KEND in B.

  Definition VBL (N : Z) : Prop :=
    ((0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64)
     /\ 1 <= N /\ N <= n /\ n < 2^31 /\ 0 < D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad D /\ shad (D + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m ST1 LO KLO HN APP R1 DPOS"] Lemma VBL_ok : forall N, (1 <= N <= n)%Z -> VBL N.
  Proof. intros N HNN. pose proof (VBND_ok N HNN) as B. unfold VBND, KHIGH, KEND in B. unfold VBL. repeat split; lia. Qed.

  Ltac vinv_open H := destruct H as (FR1 & ST1' & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11).
  Ltac vhide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST1; change (?P) with (sf_hide P) in STM; change (?P) with (sf_hide P) in FR;
    change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in LAY.
  Ltac vbl_facts B :=
    first [ match goal with HNN : (1 <= ?N <= n)%Z |- _ => pose proof (VBL_ok N HNN) as B end
          | pose proof (VBL_ok 1%Z ltac:(clear - HN; lia)) as B ];
    unfold VBL in B.
  Ltac vprep IV :=
    pose proof IV as IV0; vinv_open IV;
    vbl_facts ident:(BL0);
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]);
    vhide_all.

  #[using="ST1 LO KLO HN APP UNP R1 WR1 DPOS"] Lemma vinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -96) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2160) -> stk asegs mc (bv_unsigned sp + -2160) (bv_unsigned sp + -96) ->
    munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> VINV mc.
  Proof.
    intros mc FR1 ST1' STM1 MU1 WM1 MI1 GOT1 SHB1 LAY1. pose proof (VBND_ok 1%Z ltac:(clear - HN; lia)) as B. unfold VBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (D + n - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition vregs (N : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp (Z_to_bv 64 N) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 D) (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Definition VX__stmt : Prop := forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31, VINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47f14) fc None mc (seg_rom asegs)).
  Section Sz6.
  Variables mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VX__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @mc).
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK"] Lemma VX__body : ltac2:(SecDiet.SzSec.bodyP 'VX__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros IV. vprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1' STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -96 + Z.of_nat 96)%Z with (bv_unsigned sp) in SK2 by lia.
    zstep.
    apply evtF_done. unfold vsnprintf_i_post_post.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
  End Sz6.
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK"] Lemma VX : ltac:(let t := eval cbv delta [VX__stmt] in VX__stmt in exact t).
  Proof. intros mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VX__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VL__stmt : Prop := forall N mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    VINV mc -> (1 <= N <= n)%Z -> (N <= 64)%Z -> Z.to_nat (shad (D + N - 1) - c) = k -> (shad D <= c < shad (D + N - 1))%Z ->
    evtF asegs RNG POST (MS (vregs N x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
                                   x20 x21 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x48034) fc None mc (seg_rom asegs)).
  Section Sz7.
  Variables N mc c x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VL__stmt "vvkvvvvvvvvvvvvvvvvv" @N).
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VL__body : ltac2:(SecDiet.SzSec.bodyP 'VL__stmt "vvkvvvvvvvvvvvvvvvvv").
  Proof.
    intros k.
 intros IV HNN N64 Hk Hc. unfold vregs. vprep IV.
    assert (UNPN : unpoisoned mc D (D + N)) by (eapply unpoisoned_sub; [exact UNP1 | lia | lia]).
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (D + N - 1) = 2147450880 + Z.shiftr (D + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + N) c UNPN ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply VX; eassumption.
  Qed.
  End Sz7.
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VL : ltac:(let t := eval cbv delta [VL__stmt] in VL__stmt in exact t).
  Proof. intros N mc k c x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VL__body "vvkvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition VE__stmt : Prop := forall N mc x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31, VINV mc -> (1 <= N <= n)%Z -> (N <= 64)%Z ->
    evtF asegs RNG POST (MS (vregs N x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + N + -1) 3))
                                   (Z_to_bv 64 (D + N + -1)) x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x48018) fc None mc (seg_rom asegs)).
  Section Sz8.
  Variables N mc x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VE__stmt "vvvvvvvvvvvvvvvvvv" @N).
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VE__body : ltac2:(SecDiet.SzSec.bodyP 'VE__stmt "vvvvvvvvvvvvvvvvvv").
  Proof.
 intros IV HNN N64. unfold vregs. vprep IV.
    assert (UNPN : unpoisoned mc D (D + N)) by (eapply unpoisoned_sub; [exact UNP1 | lia | lia]).
    destruct (unpoisoned_check_rd asegs mc D (D + N) (D + N + -1) 1 UNPN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply VX; eassumption.
    - eapply (VL N mc); [exact IV0 | exact HNN | exact N64 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.
  End Sz8.
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VE : ltac:(let t := eval cbv delta [VE__stmt] in VE__stmt in exact t).
  Proof. intros N mc x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VE__body "vvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition VC__stmt : Prop := forall N mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31, VINV mc -> (1 <= N <= n)%Z ->
    evtF asegs RNG POST (MS (vregs N x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47ecc) fc None mc (seg_rom asegs)).
  Section Sz9.
  Variables N mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VC__stmt "vvvvvvvvvvvvvvvvvvvvv" @N).
  #[using="ST1 LO KLO HN APP UNP R1 WR1 DPOS RI RSTK RSH1"] Lemma VC__body : ltac2:(SecDiet.SzSec.bodyP 'VC__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros IV HNN. unfold vregs. vprep IV.
    assert (UNPN : unpoisoned mc D (D + N)) by (eapply unpoisoned_sub; [exact UNP1 | lia | lia]).
    assert (APPN : app_blk D (D + N)) by (eapply app_blk_sub; [exact APP | lia | lia | lia]).
    zstep. zstep. zstep.
    if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (NB : (64 < N)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
        destruct (Z_le_gt_dec N 64) as [LE|GT]; [exfalso | lia].
        replace ((N + -65) mod 2 ^ 64)%Z with (N + -65 + 2^64)%Z in K2; [lia|].
        symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
      clear K2.
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 HN. lia. } clear K3.
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec.
      1: exact MI1. 1: exact ST1'. 1: lia. 1: (unfold KHIGH; lia). 1: exact GOT1. 1: exact SHB1. 1: exact LAY1.
      1: (zsimp; exact APPN). 1: (zsimp; exact UNPN). 1: (zsimp; lia). 1: (eapply rng_sub'; [exact RSTK | lia]).
      zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply VX. eapply vinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N64 : (N <= 64)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
        destruct (Z_le_gt_dec N 64) as [LE|GT]; [exact LE | exfalso].
        rewrite Z.mod_small in K2 by lia. lia. }
      clear K2.
      do 4 zstep.
      do 7 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI D WR11 ltac:(apply no_image_asan; pose proof (VBND_ok N HNN) as B9; unfold VBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (D + N + -1) WR11 ltac:(apply no_image_asan; pose proof (VBND_ok N HNN) as B9; unfold VBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 3 zstep. zstep. if_cases K5; zify_cond K5.
      + eapply VE; eassumption.
      + eapply VX; eassumption.
  Qed.
  End Sz9.
  #[using="ST1 LO KLO HN APP UNP R1 WR1 DPOS RI RSTK RSH1"] Lemma VC : ltac:(let t := eval cbv delta [VC__stmt] in VC__stmt in exact t).
  Proof. intros N mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VC__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="RLO RHI j24 MI ST1 STM FR LO KLO GOT SHB LAY HN HR APP UNP R1 WR1 DPOS RI RSTK RSH1"] Lemma vsnprintf_i_post_body : forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                                 (Z_to_bv 64 D) (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47eac) fc None m (seg_rom asegs)).
  Proof.
    intros.
    pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (IV : VINV m) by (eapply vinv_of; eassumption).
    vprep IV.
    zstep.
    if_cases K0; zify_cond K0.
    { exfalso. clear - K0 HR. lia. } clear K0.
    zstep. zstep. zstep.
    destruct (Z.eq_dec r 2147483647) as [EM | NM].
    - (* [comment removed for export] *)
      replace (bv_swrap 32 (r + 1)) with (-2147483648)%Z by (rewrite EM; reflexivity).
      if_cases K1; zify_cond K1. { exfalso. clear - K1 HN. lia. } clear K1.
      zstep. zstep. zstep. zstep.
      rewrite zb_lxor_ones by lia. if_cases K2; zify_cond K2. { exfalso. clear -K2 BL0. lia. } clear K2.
      unfold sf_hide in *.
      eapply (VC n); [exact IV0 | clear - HN; lia].
    - replace (bv_swrap 32 (r + 1)) with (r + 1)%Z by (rewrite swrap32_eq; rewrite Z.mod_small by lia; lia).
      if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        rewrite zb_lxor_ones by lia. if_cases K2; zify_cond K2. 2:{ exfalso. clear -K2 K1 BL0 HR. lia. } clear K2.
        unfold sf_hide in *.
        eapply (VC (r + 1)); [exact IV0 | clear - HN HR K1; lia].
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        rewrite zb_lxor_ones by lia. if_cases K2; zify_cond K2. { exfalso. clear -K2 BL0. lia. } clear K2.
        unfold sf_hide in *.
        eapply (VC n); [exact IV0 | clear - HN; lia].
  Qed.
End VSN_POST.

(* [comment removed for export] *)
#[using="Type"] Lemma vsnprintf_i_post : forall RNG x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D n r : Z) (j24 : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp + -2160) -> stk asegs m (bv_unsigned sp + -2160) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j24; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z -> icptenv m ->
  (1 <= n < 2^31)%Z -> (0 <= r <= 2^31 - 1)%Z -> (0 < D)%Z -> sobj RNG m D (D + n) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (vsnprintf_i_post_post sp gp tp s8 s9 s10 s11 F fc m lo r rav s0v s1v s2v s3v s4v s5v s6v s7v)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 D) (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x47eac) fc None m (seg_rom asegs)).
Proof.
  intros until s7v. intros MI ST1 STM FR LO KLO ENV HN HR DPOS (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK.
  eapply (vsnprintf_i_post_body RNG) with (RLO := RLO) (RHI := RHI) (j24 := j24);
    first [ eassumption | exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_lay _ ENV) ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition VSNPRINTF_I_RA : Z := 0x47f14%Z.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vsnprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x14 x15 x16 x17 t3 t4 t5 t6 (j8 : list byte) m',
    ms' = MS (mkR (Z_to_bv 64 0x47f14) (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2
                  sp a2 a0 a1 a2 a3 x14 x15 x16 x17
                  a0 a1 (Z_to_bv 64 0x140528) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e3f0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -4480, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2160) /\ stk asegs m' (bv_unsigned sp + -2160) (bv_unsigned sp + -96)
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [C8 a3; C8 a3; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition vsnprintf_i_pre_e__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4480)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> rt_ckpf m -> a2 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT)%Z ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a3 ->
  evtF asegs RNG (vsnprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47e80) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_i_pre_e__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma vsnprintf_i_pre_e__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_i_pre_e__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO ENV CKP A2 FB NOZ SEPF SO RI RSTK RFM EF OK AOK.
  pose proof (munch_refl [(bv_unsigned sp + -4480, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_vsnprintf _ ENV) as RVSc. pose proof CKP as CKPc.
  recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
  carve_frame 96%nat ST.
  destruct (stk_split _ _ lo (bv_unsigned sp + -2160)%Z _ ST ltac:(lia)) as [ST1 STM]. clear ST.
  do 17 zstep.
  zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  sobj_now SO MU WM as SOn.
  assert (AOKn : pargs_ok RNG (Z_to_bv 64 (bv_unsigned sp + -2160)) m0 its a3).
  { apply (pargs_okL_ok RNG lo); [rewrite unsigned_lit by lia; lia|].
    eapply pargs_okL_transport; [exact AOK | exact MU | exact WM | solve_appW
                                | eapply pargs_sep_stack; [exact AOK | constructor; [cbn [fst snd]; lia| constructor]]
                                | rewrite unsigned_lit by lia; lia]. }
  call_sp printf_common_spec.
  all: try (icpt_prem RSTK).
  1: exact EF. 1: exact OK. 1: exact AOKn.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  apply evtF_done. unfold vsnprintf_i_mid.
  do 13 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  exact FR.
Qed.
End Sz1.
#[using="Type"] Lemma vsnprintf_i_pre_e : ltac:(let t := eval cbv delta [vsnprintf_i_pre_e__stmt] in vsnprintf_i_pre_e__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr its. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_i_pre_e__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vsnprintf_i_pre : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4480)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> rt_ckpf m -> a2 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= lo \/ bv_unsigned sp <= FMT)%Z ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_okL RNG lo sp m its a3 ->
  evtF asegs RNG (vsnprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4450c) fc None m (seg_rom asegs)).
Proof. intros. zstep. eapply vsnprintf_i_pre_e; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VSN_POST.
  Variables (RNG : footprint) (sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (lo D n r RLO RHI : Z) (j24 : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word).
  Notation SAVES := [CB 24 j24; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST1 : stk asegs m lo (bv_unsigned sp + -2160).
  Hypothesis STM : stk asegs m (bv_unsigned sp + -2160) (bv_unsigned sp + -96).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -96) SAVES.
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis HN : (1 <= n < 2^31)%Z.
  Hypothesis HR : (0 <= r <= 2^31 - 1)%Z.
  (* [comment removed for export] *)
  Hypothesis APP : app_blk D (D + n).
  Hypothesis UNP : unpoisoned m D (D + n).
  Hypothesis R1 : (RLO <= D /\ D + n <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis DPOS : (0 < D)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Definition vsnprintf_i_post_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).
  Notation POST := vsnprintf_i_post_post.

  Definition VINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -96) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2160) /\ stk asegs mc (bv_unsigned sp + -2160) (bv_unsigned sp + -96)
    /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc D (D + n) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition VBND (N : Z) : Prop :=
    ((0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64)
     /\ 1 <= N /\ N <= n /\ n < 2^31
     /\ 0 < D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad D /\ shad (D + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= D /\ D + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m ST1 LO KLO HN APP R1 DPOS"] Lemma VBND_ok : forall N, (1 <= N <= n)%Z -> VBND N.
  Proof.
    intros N HNN. unfold VBND. destruct ST1 as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    split; [lia|]. Z.div_mod_to_equations; lia.
  Qed.
  Ltac acc_facts B ::=
    first [ match goal with HNN : (1 <= ?N <= n)%Z |- _ => pose proof (VBND_ok N HNN) as B end
          | pose proof (VBND_ok 1%Z ltac:(clear - HN; lia)) as B ];
    unfold VBND, KHIGH, KEND in B.

  Definition VBL (N : Z) : Prop :=
    ((0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64)
     /\ 1 <= N /\ N <= n /\ n < 2^31 /\ 0 < D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad D /\ shad (D + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m ST1 LO KLO HN APP R1 DPOS"] Lemma VBL_ok : forall N, (1 <= N <= n)%Z -> VBL N.
  Proof. intros N HNN. pose proof (VBND_ok N HNN) as B. unfold VBND, KHIGH, KEND in B. unfold VBL. repeat split; lia. Qed.

  Ltac vinv_open H := destruct H as (FR1 & ST1' & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11).
  Ltac vhide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST1; change (?P) with (sf_hide P) in STM; change (?P) with (sf_hide P) in FR;
    change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in LAY.
  Ltac vbl_facts B :=
    first [ match goal with HNN : (1 <= ?N <= n)%Z |- _ => pose proof (VBL_ok N HNN) as B end
          | pose proof (VBL_ok 1%Z ltac:(clear - HN; lia)) as B ];
    unfold VBL in B.
  Ltac vprep IV :=
    pose proof IV as IV0; vinv_open IV;
    vbl_facts ident:(BL0);
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]);
    vhide_all.

  #[using="ST1 LO KLO HN APP UNP R1 WR1 DPOS"] Lemma vinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -96) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2160) -> stk asegs mc (bv_unsigned sp + -2160) (bv_unsigned sp + -96) ->
    munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> VINV mc.
  Proof.
    intros mc FR1 ST1' STM1 MU1 WM1 MI1 GOT1 SHB1 LAY1. pose proof (VBND_ok 1%Z ltac:(clear - HN; lia)) as B. unfold VBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (D + n - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition vregs (N : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp (Z_to_bv 64 N) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 D) (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Definition VX__stmt : Prop := forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31, VINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47f7c) fc None mc (seg_rom asegs)).
  Section Sz6.
  Variables mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VX__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @mc).
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK"] Lemma VX__body : ltac2:(SecDiet.SzSec.bodyP 'VX__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros IV. vprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1' STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -96 + Z.of_nat 96)%Z with (bv_unsigned sp) in SK2 by lia.
    zstep.
    apply evtF_done. unfold vsnprintf_i_post_post.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
  End Sz6.
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK"] Lemma VX : ltac:(let t := eval cbv delta [VX__stmt] in VX__stmt in exact t).
  Proof. intros mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VX__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VL__stmt : Prop := forall N mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    VINV mc -> (1 <= N <= n)%Z -> (N <= 64)%Z -> Z.to_nat (shad (D + N - 1) - c) = k -> (shad D <= c < shad (D + N - 1))%Z ->
    evtF asegs RNG POST (MS (vregs N x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
                                   x20 x21 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4809c) fc None mc (seg_rom asegs)).
  Section Sz7.
  Variables N mc c x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VL__stmt "vvkvvvvvvvvvvvvvvvvv" @N).
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VL__body : ltac2:(SecDiet.SzSec.bodyP 'VL__stmt "vvkvvvvvvvvvvvvvvvvv").
  Proof.
    intros k.
 intros IV HNN N64 Hk Hc. unfold vregs. vprep IV.
    assert (UNPN : unpoisoned mc D (D + N)) by (eapply unpoisoned_sub; [exact UNP1 | lia | lia]).
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (D + N - 1) = 2147450880 + Z.shiftr (D + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + N) c UNPN ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply VX; eassumption.
  Qed.
  End Sz7.
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VL : ltac:(let t := eval cbv delta [VL__stmt] in VL__stmt in exact t).
  Proof. intros N mc k c x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VL__body "vvkvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition VE__stmt : Prop := forall N mc x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31, VINV mc -> (1 <= N <= n)%Z -> (N <= 64)%Z ->
    evtF asegs RNG POST (MS (vregs N x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + N + -1) 3))
                                   (Z_to_bv 64 (D + N + -1)) x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x48080) fc None mc (seg_rom asegs)).
  Section Sz8.
  Variables N mc x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VE__stmt "vvvvvvvvvvvvvvvvvv" @N).
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VE__body : ltac2:(SecDiet.SzSec.bodyP 'VE__stmt "vvvvvvvvvvvvvvvvvv").
  Proof.
 intros IV HNN N64. unfold vregs. vprep IV.
    assert (UNPN : unpoisoned mc D (D + N)) by (eapply unpoisoned_sub; [exact UNP1 | lia | lia]).
    destruct (unpoisoned_check_rd asegs mc D (D + N) (D + N + -1) 1 UNPN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply VX; eassumption.
    - eapply (VL N mc); [exact IV0 | exact HNN | exact N64 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.
  End Sz8.
  #[using="ST1 LO KLO HN APP R1 DPOS RSTK RSH1"] Lemma VE : ltac:(let t := eval cbv delta [VE__stmt] in VE__stmt in exact t).
  Proof. intros N mc x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VE__body "vvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition VC__stmt : Prop := forall N mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31, VINV mc -> (1 <= N <= n)%Z ->
    evtF asegs RNG POST (MS (vregs N x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47f34) fc None mc (seg_rom asegs)).
  Section Sz9.
  Variables N mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'VC__stmt "vvvvvvvvvvvvvvvvvvvvv" @N).
  #[using="ST1 LO KLO HN APP UNP R1 WR1 DPOS RI RSTK RSH1"] Lemma VC__body : ltac2:(SecDiet.SzSec.bodyP 'VC__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros IV HNN. unfold vregs. vprep IV.
    assert (UNPN : unpoisoned mc D (D + N)) by (eapply unpoisoned_sub; [exact UNP1 | lia | lia]).
    assert (APPN : app_blk D (D + N)) by (eapply app_blk_sub; [exact APP | lia | lia | lia]).
    zstep. zstep. zstep.
    if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (NB : (64 < N)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
        destruct (Z_le_gt_dec N 64) as [LE|GT]; [exfalso | lia].
        replace ((N + -65) mod 2 ^ 64)%Z with (N + -65 + 2^64)%Z in K2; [lia|].
        symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
      clear K2.
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 HN. lia. } clear K3.
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec.
      1: exact MI1. 1: exact ST1'. 1: lia. 1: (unfold KHIGH; lia). 1: exact GOT1. 1: exact SHB1. 1: exact LAY1.
      1: (zsimp; exact APPN). 1: (zsimp; exact UNPN). 1: (zsimp; lia). 1: (eapply rng_sub'; [exact RSTK | lia]).
      zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply VX. eapply vinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N64 : (N <= 64)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
        destruct (Z_le_gt_dec N 64) as [LE|GT]; [exact LE | exfalso].
        rewrite Z.mod_small in K2 by lia. lia. }
      clear K2.
      do 4 zstep.
      do 7 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI D WR11 ltac:(apply no_image_asan; pose proof (VBND_ok N HNN) as B9; unfold VBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (D + N + -1) WR11 ltac:(apply no_image_asan; pose proof (VBND_ok N HNN) as B9; unfold VBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 3 zstep. zstep. if_cases K5; zify_cond K5.
      + eapply VE; eassumption.
      + eapply VX; eassumption.
  Qed.
  End Sz9.
  #[using="ST1 LO KLO HN APP UNP R1 WR1 DPOS RI RSTK RSH1"] Lemma VC : ltac:(let t := eval cbv delta [VC__stmt] in VC__stmt in exact t).
  Proof. intros N mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'VC__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="RLO RHI j24 MI ST1 STM FR LO KLO GOT SHB LAY HN HR APP UNP R1 WR1 DPOS RI RSTK RSH1"] Lemma vsnprintf_i_post_body : forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                                 (Z_to_bv 64 D) (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47f14) fc None m (seg_rom asegs)).
  Proof.
    intros.
    pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (IV : VINV m) by (eapply vinv_of; eassumption).
    vprep IV.
    zstep.
    if_cases K0; zify_cond K0.
    { exfalso. clear - K0 HR. lia. } clear K0.
    zstep. zstep. zstep.
    destruct (Z.eq_dec r 2147483647) as [EM | NM].
    - (* [comment removed for export] *)
      replace (bv_swrap 32 (r + 1)) with (-2147483648)%Z by (rewrite EM; reflexivity).
      if_cases K1; zify_cond K1. { exfalso. clear - K1 HN. lia. } clear K1.
      zstep. zstep. zstep. zstep.
      rewrite zb_lxor_ones by lia. if_cases K2; zify_cond K2. { exfalso. clear -K2 BL0. lia. } clear K2.
      unfold sf_hide in *.
      eapply (VC n); [exact IV0 | clear - HN; lia].
    - replace (bv_swrap 32 (r + 1)) with (r + 1)%Z by (rewrite swrap32_eq; rewrite Z.mod_small by lia; lia).
      if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        rewrite zb_lxor_ones by lia. if_cases K2; zify_cond K2. 2:{ exfalso. clear -K2 K1 BL0 HR. lia. } clear K2.
        unfold sf_hide in *.
        eapply (VC (r + 1)); [exact IV0 | clear - HN HR K1; lia].
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        rewrite zb_lxor_ones by lia. if_cases K2; zify_cond K2. { exfalso. clear -K2 BL0. lia. } clear K2.
        unfold sf_hide in *.
        eapply (VC n); [exact IV0 | clear - HN; lia].
  Qed.
End VSN_POST.

(* [comment removed for export] *)
#[using="Type"] Lemma vsnprintf_i_post : forall RNG x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D n r : Z) (j24 : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp + -2160) -> stk asegs m (bv_unsigned sp + -2160) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j24; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z -> icptenv m ->
  (1 <= n < 2^31)%Z -> (0 <= r <= 2^31 - 1)%Z -> (0 < D)%Z -> sobj RNG m D (D + n) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (vsnprintf_i_post_post sp gp tp s8 s9 s10 s11 F fc m lo r rav s0v s1v s2v s3v s4v s5v s6v s7v)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 D) (Z_to_bv 64 n) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x47f14) fc None m (seg_rom asegs)).
Proof.
  intros until s7v. intros MI ST1 STM FR LO KLO ENV HN HR DPOS (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK.
  eapply (vsnprintf_i_post_body RNG) with (RLO := RLO) (RHI := RHI) (j24 := j24);
    first [ eassumption | exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_lay _ ENV) ].
Qed.
End CANSEC1.
End TwB.
End I_vsnprintf.

(* [comment removed for export] *)
Module Printf_pitems.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_fmtA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pitems_aux (fuel : nat) (s : list Z) (args : list farg) (ws : list word) : list pitem :=
  match fuel with
  | O => []
  | S f =>
    match s with
    | [] => []
    | c :: s0 =>
      if c =? 37 then
        match parse_conv s0 with
        | Some (cv, r') =>
            (match cv with
             | Cs => match args, ws with AStr cs :: _, w :: _ => PStr (bv_unsigned w) (zb cs) | _, _ => PLit [] end
             | C08x => P08x
             | Czu => PZu (Z_to_bv 8 117)
             | _ => PInt (Z_to_bv 8 (hd 0 s0))
             end) :: pitems_aux f r' (tl args) (tl ws)
        | None => []
        end
      else let (l, r) := take_lit s in PLit (zb l) :: pitems_aux f r args ws
    end
  end.
Definition pitems (fs : string) (args : list farg) (ws : list word) : list pitem := pitems_aux (List.length (str fs)) (str fs) args ws.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma b8_unsigned : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c : byte) = c.
Proof. intros c Hc. apply unsigned_lit8. exact Hc. Qed.

(* [comment removed for export] *)
Lemma pitems_step : forall f c s0 args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (S f) (c :: s0)) args = true ->
  (c = 37 /\ exists cv r' a args', parse_conv s0 = Some (cv, r') /\ args = a :: args' /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.conv_ok cv a = true
            /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux f r') args' = true /\ (List.length r' < S (List.length s0))%nat
            /\ parse_fmt_aux (S f) (c :: s0) = FConv cv :: parse_fmt_aux f r')
  \/ (c <> 37 /\ exists l r, take_lit (c :: s0) = (l, r) /\ c :: s0 = l ++ r /\ ~ In 37 l /\ (1 <= List.length l)%nat
            /\ forallb (fun c => negb (c =? 0) && negb (c =? 37)) l = true
            /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux f r) args = true).
Proof.
  intros f c s0 args OK. destruct (Z.eqb_spec c 37) as [E37|N37].
  - left. split; [exact E37|]. subst c. rewrite parse_pct_shape in OK.
    destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
    cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
    exists cv, r', a, args'. split; [reflexivity|]. split; [reflexivity|]. split; [exact OKc|]. split; [exact OK|].
    split; [| rewrite parse_pct_shape, PC; reflexivity].
    pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia.
  - right. split; [exact N37|]. rewrite (parse_lit_shape f c s0 N37) in OK.
    destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
    cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
    exists l, r. split; [reflexivity|]. split; [exact E1|]. split; [exact N1|]. split; [| split; [exact OKl | exact OK]].
    destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E).
Qed.

(* [comment removed for export] *)
Lemma pitems_render : forall fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> List.length ws = List.length args ->
  prender (pitems_aux fuel s args ws) = zb s.
Proof.
  induction fuel as [|f IH]; intros s args ws Hlen OK LW.
  - destruct s as [|c s0]; [reflexivity | cbn in Hlen; lia].
  - destruct s as [|c s0]; [reflexivity|]. cbn [List.length] in Hlen.
    destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
    + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC.
      destruct ws as [|w ws']; [cbn in LW; lia|]. cbn [tl]. cbn [List.length] in LW.
      unfold prender. cbn [map concat]. fold (prender (pitems_aux f r' args' ws')). rewrite (IH r' args' ws') by (first [lia | exact OK']).
      pose proof (parse_conv_cases _ _ _ PC) as SH.
      destruct cv; destruct a as [v|sv]; try discriminate OKc;
        repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; reflexivity.
    + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL.
      unfold prender. cbn [map concat pbytes]. fold (prender (pitems_aux f r args ws)).
      pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      rewrite (IH r args ws) by (first [lia | exact OK' | exact LW]). rewrite E1, zb_app. reflexivity.
Qed.

Lemma pitems_ok : forall fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall (fun c => 0 <= c < 256) s ->
  Forall pitem_ok (pitems_aux fuel s args ws).
Proof.
  induction fuel as [|f IH]; intros s args ws Hlen OK RG; [constructor|].
  destruct s as [|c s0]; [constructor|]. cbn [List.length] in Hlen.
  destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
  + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC. cbn [tl].
    pose proof (parse_conv_cases _ _ _ PC) as SH.
    assert (RG' : Forall (fun c => 0 <= c < 256) r').
    { inversion RG as [|? ? _ RG0]; subst. destruct cv;
        repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0;
        repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end; assumption. }
    constructor; [| apply IH; first [lia | exact OK' | exact RG']].
    destruct cv; destruct a as [v|sv]; try discriminate OKc;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [hd pitem_ok];
      first [ exact I
            | (destruct ws as [|w ws']; cbn [pitem_ok]; [apply Forall_nil | exact I])
            | (unfold intconv; rewrite b8_unsigned by lia; auto) ].
  + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL.
    pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
    rewrite E1 in RG. apply Forall_app in RG. destruct RG as [RGl RGr].
    constructor; [| apply IH; first [lia | exact OK' | exact RGr]].
    cbn [pitem_ok]. unfold zb. apply Forall_map. apply Forall_forall. intros x Hx.
    pose proof (proj1 (Forall_forall _ _) RGl x Hx) as Rx. cbv beta in Rx. rewrite b8_unsigned by lia.
    intros E. apply N1. rewrite <- E. exact Hx.
Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition pword_ok (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (a : farg) (w : word) : Prop :=
  match a with AStr cs => pstrL RNG lo sp m (bv_unsigned w) (zb cs) | AInt _ => True end.
Definition pword_sep (W : list (Z * Z)) (a : farg) (w : word) : Prop :=
  match a with AStr cs => disjoint_from W (bv_unsigned w) (Z.of_nat (List.length (zb cs)) + 1) | AInt _ => True end.

#[using="Type"] Lemma pitems_words : forall RNG lo sp m fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall2 (pword_ok RNG lo sp m) args ws ->
  pwords_ok RNG lo sp m (pitems_aux fuel s args ws) ws.
Proof.
  intros RNG lo sp m. induction fuel as [|f IH]; intros s args ws Hlen OK FW; [exact I|].
  destruct s as [|c s0]; [exact I|]. cbn [List.length] in Hlen.
  destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
  + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC.
    inversion FW as [|a0 w args0 ws' FA FW']; subst. cbn [tl].
    pose proof (IH r' args' ws' ltac:(lia) OK' FW') as IHr.
    destruct cv; destruct a as [v|sv]; try discriminate OKc; cbn [pwords_ok]; try exact IHr.
    split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact FA | exact IHr].
  + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL. cbn [pwords_ok].
    pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
    apply IH; first [lia | exact OK' | exact FW].
Qed.

#[using="Type"] Lemma pitems_sep : forall W fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall2 (pword_sep W) args ws ->
  pstrs_sep W (pitems_aux fuel s args ws).
Proof.
  intros W. induction fuel as [|f IH]; intros s args ws Hlen OK FW; [exact I|].
  destruct s as [|c s0]; [exact I|]. cbn [List.length] in Hlen.
  destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
  + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC.
    inversion FW as [|a0 w args0 ws' FA FW']; subst. cbn [tl].
    pose proof (IH r' args' ws' ltac:(lia) OK' FW') as IHr.
    destruct cv; destruct a as [v|sv]; try discriminate OKc; cbn [pstrs_sep]; try exact IHr.
    split; [exact FA | exact IHr].
  + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL. cbn [pstrs_sep].
    pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
    apply IH; first [lia | exact OK' | exact FW].
Qed.
End CANSEC1.

(* [comment removed for export] *)
Lemma fmt_nonzero : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall (fun c => c <> 0) s.
Proof.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [constructor | cbn in Hlen; lia].
  - destruct s as [|c s0]; [constructor|]. cbn [List.length] in Hlen.
    destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & OKl & OK')].
    + pose proof (IH r' args' ltac:(lia) OK') as IHr.
      pose proof (parse_conv_cases _ _ _ PC) as SH.
      destruct cv; repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0;
        repeat (constructor; [lia|]); exact IHr.
    + pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      rewrite E1. apply Forall_app. split; [| apply (IH r args); [lia | exact OK']].
      apply Forall_forall. intros x Hx. pose proof (proj1 (forallb_forall _ _) OKl x Hx) as Bx. cbv beta in Bx.
      apply andb_prop in Bx as [B0 _]. apply negb_true_iff in B0. apply Z.eqb_neq in B0. exact B0.
Qed.

(* [comment removed for export] *)
Lemma pitems_facts : forall fs args ws, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> List.length ws = List.length args ->
  zb (str fs ++ [0]) = zb (str fs) ++ [Z_to_bv 8 0]
  /\ Forall (fun b : byte => bv_unsigned b <> 0) (zb (str fs))
  /\ zb (str fs) = prender (pitems fs args ws)
  /\ Forall pitem_ok (pitems fs args ws).
Proof.
  intros fs args ws IOK LWS.
  assert (LSTR : (List.length (str fs) <= List.length (str fs))%nat) by lia.
  assert (IOK' : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (List.length (str fs)) (str fs)) args = true) by exact IOK.
  pose proof (str_range fs) as SRG. apply Forall_app in SRG. destruct SRG as [SRG _].
  pose proof (fmt_nonzero _ _ _ LSTR IOK') as FNZ.
  split; [apply zb_app|]. split.
  { unfold zb. apply Forall_map. apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) SRG c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) FNZ c Hc) as Nc. cbv beta in Rc, Nc.
    rewrite b8_unsigned by lia. exact Nc. }
  split; [symmetry; exact (pitems_render _ _ _ ws LSTR IOK' LWS) | exact (pitems_ok _ _ _ ws LSTR IOK' SRG)].
Qed.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma pitems_words_fs : forall RNG lo sp m fs args ws,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> Forall2 (pword_ok RNG lo sp m) args ws -> pwords_ok RNG lo sp m (pitems fs args ws) ws.
Proof. intros RNG lo sp m fs args ws IOK FW. unfold pitems. apply pitems_words; [apply Nat.le_refl | exact IOK | exact FW]. Qed.
#[using="Type"] Lemma pitems_sep_fs : forall W fs args ws,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> Forall2 (pword_sep W) args ws -> pstrs_sep W (pitems fs args ws).
Proof. intros W fs args ws IOK FW. unfold pitems. apply pitems_sep; [apply Nat.le_refl | exact IOK | exact FW]. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pitems_aux (fuel : nat) (s : list Z) (args : list farg) (ws : list word) : list pitem :=
  match fuel with
  | O => []
  | S f =>
    match s with
    | [] => []
    | c :: s0 =>
      if c =? 37 then
        match parse_conv s0 with
        | Some (cv, r') =>
            (match cv with
             | Cs => match args, ws with AStr cs :: _, w :: _ => PStr (bv_unsigned w) (zb cs) | _, _ => PLit [] end
             | C08x => P08x
             | Czu => PZu (Z_to_bv 8 117)
             | _ => PInt (Z_to_bv 8 (hd 0 s0))
             end) :: pitems_aux f r' (tl args) (tl ws)
        | None => []
        end
      else let (l, r) := take_lit s in PLit (zb l) :: pitems_aux f r args ws
    end
  end.
Definition pitems (fs : string) (args : list farg) (ws : list word) : list pitem := pitems_aux (List.length (str fs)) (str fs) args ws.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma b8_unsigned : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c : byte) = c.
Proof. intros c Hc. apply unsigned_lit8. exact Hc. Qed.

(* [comment removed for export] *)
Lemma pitems_step : forall f c s0 args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (S f) (c :: s0)) args = true ->
  (c = 37 /\ exists cv r' a args', parse_conv s0 = Some (cv, r') /\ args = a :: args' /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.conv_ok cv a = true
            /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux f r') args' = true /\ (List.length r' < S (List.length s0))%nat
            /\ parse_fmt_aux (S f) (c :: s0) = FConv cv :: parse_fmt_aux f r')
  \/ (c <> 37 /\ exists l r, take_lit (c :: s0) = (l, r) /\ c :: s0 = l ++ r /\ ~ In 37 l /\ (1 <= List.length l)%nat
            /\ forallb (fun c => negb (c =? 0) && negb (c =? 37)) l = true
            /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux f r) args = true).
Proof.
  intros f c s0 args OK. destruct (Z.eqb_spec c 37) as [E37|N37].
  - left. split; [exact E37|]. subst c. rewrite parse_pct_shape in OK.
    destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
    cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
    exists cv, r', a, args'. split; [reflexivity|]. split; [reflexivity|]. split; [exact OKc|]. split; [exact OK|].
    split; [| rewrite parse_pct_shape, PC; reflexivity].
    pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia.
  - right. split; [exact N37|]. rewrite (parse_lit_shape f c s0 N37) in OK.
    destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
    cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
    exists l, r. split; [reflexivity|]. split; [exact E1|]. split; [exact N1|]. split; [| split; [exact OKl | exact OK]].
    destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E).
Qed.

(* [comment removed for export] *)
Lemma pitems_render : forall fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> List.length ws = List.length args ->
  prender (pitems_aux fuel s args ws) = zb s.
Proof.
  induction fuel as [|f IH]; intros s args ws Hlen OK LW.
  - destruct s as [|c s0]; [reflexivity | cbn in Hlen; lia].
  - destruct s as [|c s0]; [reflexivity|]. cbn [List.length] in Hlen.
    destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
    + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC.
      destruct ws as [|w ws']; [cbn in LW; lia|]. cbn [tl]. cbn [List.length] in LW.
      unfold prender. cbn [map concat]. fold (prender (pitems_aux f r' args' ws')). rewrite (IH r' args' ws') by (first [lia | exact OK']).
      pose proof (parse_conv_cases _ _ _ PC) as SH.
      destruct cv; destruct a as [v|sv]; try discriminate OKc;
        repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; reflexivity.
    + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL.
      unfold prender. cbn [map concat pbytes]. fold (prender (pitems_aux f r args ws)).
      pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      rewrite (IH r args ws) by (first [lia | exact OK' | exact LW]). rewrite E1, zb_app. reflexivity.
Qed.

Lemma pitems_ok : forall fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall (fun c => 0 <= c < 256) s ->
  Forall pitem_ok (pitems_aux fuel s args ws).
Proof.
  induction fuel as [|f IH]; intros s args ws Hlen OK RG; [constructor|].
  destruct s as [|c s0]; [constructor|]. cbn [List.length] in Hlen.
  destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
  + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC. cbn [tl].
    pose proof (parse_conv_cases _ _ _ PC) as SH.
    assert (RG' : Forall (fun c => 0 <= c < 256) r').
    { inversion RG as [|? ? _ RG0]; subst. destruct cv;
        repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0;
        repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end; assumption. }
    constructor; [| apply IH; first [lia | exact OK' | exact RG']].
    destruct cv; destruct a as [v|sv]; try discriminate OKc;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [hd pitem_ok];
      first [ exact I
            | (destruct ws as [|w ws']; cbn [pitem_ok]; [apply Forall_nil | exact I])
            | (unfold intconv; rewrite b8_unsigned by lia; auto) ].
  + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL.
    pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
    rewrite E1 in RG. apply Forall_app in RG. destruct RG as [RGl RGr].
    constructor; [| apply IH; first [lia | exact OK' | exact RGr]].
    cbn [pitem_ok]. unfold zb. apply Forall_map. apply Forall_forall. intros x Hx.
    pose proof (proj1 (Forall_forall _ _) RGl x Hx) as Rx. cbv beta in Rx. rewrite b8_unsigned by lia.
    intros E. apply N1. rewrite <- E. exact Hx.
Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition pword_ok (RNG : footprint) (lo : Z) (sp : word) (m : word -> option byte) (a : farg) (w : word) : Prop :=
  match a with AStr cs => pstrL RNG lo sp m (bv_unsigned w) (zb cs) | AInt _ => True end.
Definition pword_sep (W : list (Z * Z)) (a : farg) (w : word) : Prop :=
  match a with AStr cs => disjoint_from W (bv_unsigned w) (Z.of_nat (List.length (zb cs)) + 1) | AInt _ => True end.

#[using="Type"] Lemma pitems_words : forall RNG lo sp m fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall2 (pword_ok RNG lo sp m) args ws ->
  pwords_ok RNG lo sp m (pitems_aux fuel s args ws) ws.
Proof.
  intros RNG lo sp m. induction fuel as [|f IH]; intros s args ws Hlen OK FW; [exact I|].
  destruct s as [|c s0]; [exact I|]. cbn [List.length] in Hlen.
  destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
  + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC.
    inversion FW as [|a0 w args0 ws' FA FW']; subst. cbn [tl].
    pose proof (IH r' args' ws' ltac:(lia) OK' FW') as IHr.
    destruct cv; destruct a as [v|sv]; try discriminate OKc; cbn [pwords_ok]; try exact IHr.
    split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact FA | exact IHr].
  + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL. cbn [pwords_ok].
    pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
    apply IH; first [lia | exact OK' | exact FW].
Qed.

#[using="Type"] Lemma pitems_sep : forall W fuel s args ws,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall2 (pword_sep W) args ws ->
  pstrs_sep W (pitems_aux fuel s args ws).
Proof.
  intros W. induction fuel as [|f IH]; intros s args ws Hlen OK FW; [exact I|].
  destruct s as [|c s0]; [exact I|]. cbn [List.length] in Hlen.
  destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & _ & OK')].
  + cbn [pitems_aux]. change (37 =? 37) with true. cbv iota. rewrite PC.
    inversion FW as [|a0 w args0 ws' FA FW']; subst. cbn [tl].
    pose proof (IH r' args' ws' ltac:(lia) OK' FW') as IHr.
    destruct cv; destruct a as [v|sv]; try discriminate OKc; cbn [pstrs_sep]; try exact IHr.
    split; [exact FA | exact IHr].
  + cbn [pitems_aux]. replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact N37). rewrite TL. cbn [pstrs_sep].
    pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
    apply IH; first [lia | exact OK' | exact FW].
Qed.
End CANSEC1.

(* [comment removed for export] *)
Lemma fmt_nonzero : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true -> Forall (fun c => c <> 0) s.
Proof.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [constructor | cbn in Hlen; lia].
  - destruct s as [|c s0]; [constructor|]. cbn [List.length] in Hlen.
    destruct (pitems_step f c s0 args OK) as [(-> & cv & r' & a & args' & PC & -> & OKc & OK' & LR & _) | (N37 & l & r & TL & E1 & N1 & Hl & OKl & OK')].
    + pose proof (IH r' args' ltac:(lia) OK') as IHr.
      pose proof (parse_conv_cases _ _ _ PC) as SH.
      destruct cv; repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0;
        repeat (constructor; [lia|]); exact IHr.
    + pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      rewrite E1. apply Forall_app. split; [| apply (IH r args); [lia | exact OK']].
      apply Forall_forall. intros x Hx. pose proof (proj1 (forallb_forall _ _) OKl x Hx) as Bx. cbv beta in Bx.
      apply andb_prop in Bx as [B0 _]. apply negb_true_iff in B0. apply Z.eqb_neq in B0. exact B0.
Qed.

(* [comment removed for export] *)
Lemma pitems_facts : forall fs args ws, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> List.length ws = List.length args ->
  zb (str fs ++ [0]) = zb (str fs) ++ [Z_to_bv 8 0]
  /\ Forall (fun b : byte => bv_unsigned b <> 0) (zb (str fs))
  /\ zb (str fs) = prender (pitems fs args ws)
  /\ Forall pitem_ok (pitems fs args ws).
Proof.
  intros fs args ws IOK LWS.
  assert (LSTR : (List.length (str fs) <= List.length (str fs))%nat) by lia.
  assert (IOK' : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (List.length (str fs)) (str fs)) args = true) by exact IOK.
  pose proof (str_range fs) as SRG. apply Forall_app in SRG. destruct SRG as [SRG _].
  pose proof (fmt_nonzero _ _ _ LSTR IOK') as FNZ.
  split; [apply zb_app|]. split.
  { unfold zb. apply Forall_map. apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) SRG c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) FNZ c Hc) as Nc. cbv beta in Rc, Nc.
    rewrite b8_unsigned by lia. exact Nc. }
  split; [symmetry; exact (pitems_render _ _ _ ws LSTR IOK' LWS) | exact (pitems_ok _ _ _ ws LSTR IOK' SRG)].
Qed.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma pitems_words_fs : forall RNG lo sp m fs args ws,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> Forall2 (pword_ok RNG lo sp m) args ws -> pwords_ok RNG lo sp m (pitems fs args ws) ws.
Proof. intros RNG lo sp m fs args ws IOK FW. unfold pitems. apply pitems_words; [apply Nat.le_refl | exact IOK | exact FW]. Qed.
#[using="Type"] Lemma pitems_sep_fs : forall W fs args ws,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> Forall2 (pword_sep W) args ws -> pstrs_sep W (pitems fs args ws).
Proof. intros W fs args ws IOK FW. unfold pitems. apply pitems_sep; [apply Nat.le_refl | exact IOK | exact FW]. Qed.
End CANSEC2.
End TwB.
End Printf_pitems.

(* [comment removed for export] *)
Module Strnlen_ifaceA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition STRNLEN_I_DEPTH : Z := 4384.

(* [comment removed for export] *)
Definition strnlen_rl (n : Z) (buf : list byte) : Z :=
  match find_byte 0 (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.
#[using="Type"] Lemma hitlen0_strnlen_rl : forall n buf, hitlen 0 n buf = strnlen_rl n buf.
Proof. reflexivity. Qed.

#[using="Type"] Lemma strnlen_rl_res : forall n buf, 0 <= n -> strnlen_rl n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
  intros n buf Hn. unfold strnlen_rl, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
  pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed.
#[using="Type"] Lemma strnlen_rl_range : forall n buf, 0 <= n -> 0 <= strnlen_rl n buf <= n.
Proof.
  intros n buf Hn. unfold strnlen_rl. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
  pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strnlen_rl_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> 0 <= n ->
  strnlen_rl n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str) + 1) n.
Proof.
  intros n str slack NONUL Hn. unfold strnlen_rl. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
  - rewrite (find_byte_cstr 0 n str slack NONUL) by lia. lia.
  - rewrite (find_byte_cstr_short 0 n str slack NONUL) by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strnlen_wb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte) (lo : Z),
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n -> 0 < P -> 0 <= n < 2^64 ->
  bytes_at asegs m P buf -> memchr_ok P 0 n buf ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STRNLEN_I_DEPTH -> KHIGH <= lo ->
  (P + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= P) ->
  icptenv m -> sobj RNG m P (P + strnlen_rl n buf) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG P (Z.of_nat (length buf)) ->
  evtF asegs RNG (strnlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4446c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> PPOS Hn BUF OK MI ST LO KLO SEPB ENV (AB & U & SZ & RLO & RHI & HULL & WR & RSH) RI RSTK RB.
  pose proof (strnlen_rl_range n buf ltac:(lia)) as RL0.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P).
  { apply unsigned_lit. pose proof AB as [AB1 AB2]. unfold KLOW, KHIGH, KEND in AB2. lia. }
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold STRNLEN_I_DEPTH in LO.
  assert (RI' : rng_aimg RNG) by assumption.
  zstep.
  pose proof (strnlen_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m lo buf RLO RHI) as SP. cbv zeta in SP. rewrite ?UP, ?UN, ?hitlen0_strnlen_rl in SP.
  apply SP; try assumption; try lia;
    first [ exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_ini _ ENV) | exact (ie_lay _ ENV) | exact (ie_memchr _ ENV)
          | exact (ie_strnlen _ ENV) | exact (ie_isl _ ENV) ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition STRNLEN_I_DEPTH : Z := 4384.

(* [comment removed for export] *)
Definition strnlen_rl (n : Z) (buf : list byte) : Z :=
  match find_byte 0 (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.
#[using="Type"] Lemma hitlen0_strnlen_rl : forall n buf, hitlen 0 n buf = strnlen_rl n buf.
Proof. reflexivity. Qed.

#[using="Type"] Lemma strnlen_rl_res : forall n buf, 0 <= n -> strnlen_rl n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
  intros n buf Hn. unfold strnlen_rl, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
  pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed.
#[using="Type"] Lemma strnlen_rl_range : forall n buf, 0 <= n -> 0 <= strnlen_rl n buf <= n.
Proof.
  intros n buf Hn. unfold strnlen_rl. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
  pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strnlen_rl_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> 0 <= n ->
  strnlen_rl n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str) + 1) n.
Proof.
  intros n str slack NONUL Hn. unfold strnlen_rl. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
  - rewrite (find_byte_cstr 0 n str slack NONUL) by lia. lia.
  - rewrite (find_byte_cstr_short 0 n str slack NONUL) by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strnlen_wb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte) (lo : Z),
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n -> 0 < P -> 0 <= n < 2^64 ->
  bytes_at asegs m P buf -> memchr_ok P 0 n buf ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STRNLEN_I_DEPTH -> KHIGH <= lo ->
  (P + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= P) ->
  icptenv m -> sobj RNG m P (P + strnlen_rl n buf) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG P (Z.of_nat (length buf)) ->
  evtF asegs RNG (strnlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444d4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> PPOS Hn BUF OK MI ST LO KLO SEPB ENV (AB & U & SZ & RLO & RHI & HULL & WR & RSH) RI RSTK RB.
  pose proof (strnlen_rl_range n buf ltac:(lia)) as RL0.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P).
  { apply unsigned_lit. pose proof AB as [AB1 AB2]. unfold KLOW, KHIGH, KEND in AB2. lia. }
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold STRNLEN_I_DEPTH in LO.
  assert (RI' : rng_aimg RNG) by assumption.
  zstep.
  pose proof (strnlen_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m lo buf RLO RHI) as SP. cbv zeta in SP. rewrite ?UP, ?UN, ?hitlen0_strnlen_rl in SP.
  apply SP; try assumption; try lia;
    first [ exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_ini _ ENV) | exact (ie_lay _ ENV) | exact (ie_memchr _ ENV)
          | exact (ie_strnlen _ ENV) | exact (ie_isl _ ENV) ].
Qed.
End CANSEC1.
End TwB.
End Strnlen_ifaceA.
