(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Atp_setcapA Sj_h_setmd Atp_fzwA Sj_h_deldtor Atp_pdtorA Sj_h_layout Atp_hkit3A Sj_stage2_iface Sj_h_parsew Atp_parseA Atp_createA Atp_activewA Atp_activeA Atp_pidwA Atp_pidw2A Atp_pidw3A Atp_hkit4A Atp_hkit5A Atp_hkit6A Atp_pid1A Atp_pidiA Atp_pid3A Atp_pid4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pid_costA_split : forall len, pid_costA len = pid_cost6 (Z.max len 32) + S2A_COST len.
Proof. intros len. reflexivity. Qed.

Section Pid.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis PARSE : parse_cps RT.
Hypothesis ALLOC : allocate_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.

Local Ltac ul := unfold PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem pid_ok : pid_cps RT sj_lib.
Proof using AF RTF PARSE ALLOC CREATE AFV AFI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES BUF bs p1 p17 p57 jr lo
    FDO MST -> -> -> -> -> -> -> BSL BUFB INB B16 FOBJ0 PINIT RLO RHI RC0 LVPOS LVB FRB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  set (len := Z.of_nat (length bs)) in *. set (cap := Z.max len 32).
  assert (LEN0 : 0 <= len) by (subst len; lia).
  rewrite (pid_costA_split len) in CR0. fold cap in CR0.
  assert (PC6 : 0 <= pid_cost6 cap /\ 0 <= S2A_COST len).
  { assert (C : 32 <= cap <= 2^26) by (subst cap; change (2^26) with 67108864; lia).
    pose proof (al_sbuf_bounds _ C) as B1. pose proof (al_tape_bounds _ C) as B2. pose proof (sc_idx_bounds cap ltac:(lia)) as B3.
    unfold pid_cost6, S2A_COST, Sj_num_iface.NUMA_CREDIT.
    pose proof (mcost_nonneg (al_sbuf cap) ltac:(lia)). pose proof (mcost_nonneg (al_tape cap) ltac:(lia)). pose proof (mcost_nonneg 96 ltac:(lia)).
    pose proof (mcost_nonneg (sc_idx cap) ltac:(lia)). pose proof (mcost_nonneg 8192 ltac:(lia)). pose proof (mcost_nonneg 1024 ltac:(lia)).
    pose proof (mcost_nonneg (len + 64) ltac:(lia)). lia. }
  pose proof (af_live_range RT AF Σ m BUF _ ART0 INB) as (B0 & B1 & _).

  assert (BS : bytes_at bsegs m BUF (firstn (length bs) (padded_bytes (map bv_unsigned bs)))).
  { pose proof BUFB as X. rewrite <- (firstn_skipn (length bs) (padded_bytes (map bv_unsigned bs))) in X. apply bytes_at_app in X. exact (proj1 X). }
  assert (LBS : length (firstn (length bs) (padded_bytes (map bv_unsigned bs))) = length bs).
  { apply firstn_length_le. pose proof (padded_bytes_blen (map bv_unsigned bs)). rewrite blen_unsigned in H. lia. }
  intros T c HcF Hk.
  pose proof (pid_front RT AF ALLOC (getact_ok RT AF) CREATE AFI Σ PMc ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES BUF
                (firstn (length bs) (padded_bytes (map bv_unsigned bs))) p1 p17 p57 jr lo FDO MST) as PF.
  rewrite LBS in PF. fold len in PF. fold cap in PF.
  apply (PF ltac:(lia) BS ltac:(left; exists BUF, (len + 64); split; [exact INB| lia]) FOBJ0 PINIT RLO ltac:(ul) RC0
           ltac:(unfold LIVE_MAX in *; lia) ltac:(lia) LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM T c HcF). clear PF.
  intros c2 ((Σ2 & impl & idx & oc & ia & tape & sbuf & Hc2 & LV2 & FRS2 & SP2 & CR2 & (IM0 & IM16) & (IX0 & IX16) & (OC0 & OC16) & (IA0 & IA16) & (TP0 & TP16) & (SB0 & SB16)) & FC2).
  destruct (ASTA_unpack_f RT Σ2 _ _ c2 Hc2 FC2) as (ms2 & (m2 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & j & q1 & q17 & q57 & q12 & q28 & q50
                                                    & -> & ART2 & MI2 & ST2 & FR2 & PC2 & FOBJ2 & IC2 & RC2 & BS2 & LIB2 & CH2) & FRM2 & Hc2'). clear Hc2.
  cbn [ms_fcsr] in FRM2. rewrite LBS in Hc2'. fold len in Hc2'. fold cap in Hc2', PC2, IC2, LV2, CR2.
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).

  pose proof FOBJ0 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & FLV). specialize (FLV BUF _ INB).
  assert (BUFB2 : bytes_at bsegs m2 BUF (padded_bytes (map bv_unsigned bs))).
  { apply (bytes_at_agree bsegs m m2 _ _ BUFB). intros a Ha. cbv beta in Ha. rewrite padded_bytes_blen, blen_unsigned in Ha. fold len in Ha.
    apply CH2; [right; right; left; exists BUF, (len + 64); split; [exact INB| lia]|].
    unfold pid_X. cbn [outside]. split; [clear - Ha FLV FLO FHI; lia|]. split; [clear - Ha B1 LOW LOR RLO; ul|].
    pose proof (af_live_range RT AF Σ m BUF _ ART0 INB) as (R0 & R1 & R2). unfold SJ_W. cbn [outside].
    clear - Ha R0 R1 R2. unfold SEGTOP_A in *. repeat (split; [lia|]). exact I. }
  apply (pid_main RT AF (rf_asan_memset RT RTF) (rf_memcmp RT RTF) PARSE AFV
           Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 lo RES P BUF cap impl idx oc ia tape sbuf bs
           (rt_live RT Σ) jr j q1 q17 q57 q12 q28 q50 FDO MST BSL eq_refl B0 BUFB2 INB B16 ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LVPOS IM16 IX16 OC16 IA16 TP16 SB16);
    [rewrite FRS2; unfold S2A_FRAMES, Sj_num_iface.NUMA_FRAMES, PID_FRAMES in *; lia| rewrite CR2; fold len; lia
    | rewrite LV2; cbn [length]; unfold LIVE_MAX in *; lia| exact RLO| exact RHI| exact LOW2| exact LOR| exact SPT| exact SPA| exact FRM2
    | split; [exact Hc2'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c2 Hc2'); intros ms0 <-; exact FRM2] |].
  intros c' ((Σ' & Hc' & LV' & FRS' & SP' & CR') & FC'). apply Hk. split; [| exact FC'].
  exists Σ', impl, idx, oc, ia, tape, sbuf.
  split; [| split; [rewrite LV'; exact LV2| split; [repeat split; assumption| split; [rewrite FRS'; exact FRS2| split; [rewrite SP'; exact SP2|
            rewrite CR2 in CR'; rewrite pid_costA_split; unfold cap, len in *; lia]]]]].
  eapply ASTA_conseq; [exact Hc'|]. intros ms (v & m' & RS' & AFT' & PRES' & RC' & LIB' & PD' & ST'). exists v, m'.
  split; [exact RS'|]. split; [exact AFT'|]. split; [| split; [exact RC'| split; [exact LIB'| split; [exact PD'| exact ST']]]].
  intros a Ha Hout. rewrite (PRES' a); [exact (CH2 a Ha Hout)| rewrite FRS2; exact Ha| exact Hout].
Qed.

End Pid.
