(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits
  Sj_num_lm_pro Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_c3 Sj_num_lm_tkit Sj_num_lm_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section LMTOP2.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Variables (Σ0 Σ1 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g len0 : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := B_P5LARGE.
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis EC : rt_credit RT Σ1 = (rt_credit RT Σ0 - 1)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 224 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6cd000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6cd000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis L0 : (0 <= len0 <= 62)%Z.

  Hypothesis HK : big_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo 1 (lmb_G len0).
  Collection TOPH := AF RTF FDO MST ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP L0 HK.

  Notation Q := (fun ms' => aevt RT PMc Σ1 K ms').
  Notation MREL := (lm_mrel RT Σ0 sp X me).
  Notation PARK := (lm_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d spq f).
  Notation TKA := (RT AF Σ0 Σ1 sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP) (only parsing).

  Notation T1 L := (L RT AF RTF PMc FDO MST Σ0 Σ1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g len0 kg me ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP L0 HK) (only parsing).
  Notation lm_ctx := (lm_ctx RT Σ0 Σ1 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X d spq f me).

  Ltac top_env :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 5 = 2048%Z) as FS5;
    pose proof (proj1 XG) as HinG0; pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2;
    assert (HinG : In (g, kg) (rt_frames RT Σ1)) by (rewrite EF; right; exact HinG0);
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof L0 as L0'.

  Lemma top_shpy : forall mb, ART RT Σ1 mb -> forall m', munch (lm_WL X spq f) mb m' -> wmono bsegs mb m' -> shz m' Y 40.
  Proof using TOPH.
    intros mb HA m' MU WM. unfold B_P5LARGE.
    assert (H : shz m' 0x2b080 (8 * (640 / 8))).
    { eapply (shzp_lits RT AF Σ1 mb lo (lm_WL X spq f) 0x2b080 640 (num_lits_of_af RT AF) HA (T1 top_lor1) ((T1 top_fpok) _ (T1 top_wfWL)));
        [unfold NUM_LITS; right; left; reflexivity | exact MU | exact WM]. }
    eapply shz_sub; [exact H| lia| cbn; lia].
  Qed.
  Lemma top_bcp : forall mb, ART RT Σ1 mb -> forall m', munch (lm_WL X spq f) mb m' -> wmono bsegs mb m' -> b_consts m'.
  Proof using TOPH. intros mb HA m' MU WM. exact (b_consts_of m' (af_client_consts RT AF Σ1 m' ((T1 top_art) _ mb m' (T1 top_wfWL) HA MU WM))). Qed.

  Notation EVA L F fc ybs YL mb HA := (L sp gp tp F fc X lo d spq f len0 ybs mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP YL
                               (top_shpy mb HA) (top_bcp mb HA) L0) (only parsing).

  Lemma lm_ctx_call : forall fc fc' (mm m' : mem) D N, lm_ctx fc mm -> frm0 fc' -> rt_after RT Σ1 spq lo mm m' ->
    rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq D N mm m' ->
    (f + 608 <= D /\ D + N <= f + 1104)%Z -> lm_ctx fc' m'.
  Proof using TOPH.
    intros fc fc' mm m' D N (FRM & HA & MR & PK) FRM' (ART' & MI' & WM' & ST') PR HD.
    split; [exact FRM'|]. split; [exact ART'|].
    split; [eapply (lm_mrel_ex RT AF Σ0 Σ1 sp X lo d spq f g kg me ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP mm m' D N HA MR WM' PR); lia|].
    destruct PK as ((jh & P2) & P3 & (h & P4) & (zbs & P5 & L5) & P6).
    top_env.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x /\ ~ (D <= x < D + N)%Z) PR (fun x H => H)) as AG.
    unfold LM_SAVED in P3.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?L5 in Hx; cbv beta; split; [aclient_tac| lia]).
    split; [exists jh; exact P2|]. split; [exact P3|]. split; [exists h; exact P4|].
    split; [exists zbs; split; [exact P5| exact L5]| exact P6].
  Qed.

  Lemma lm_kcpy2 : forall (fu : nat) F fc (mb : mem) ybs, lm_ctx fc mb -> length ybs = 40%nat ->
    lm_cpy2_k sp gp tp F fc X lo spq f len0 ybs mb Q (5 - Z.of_nat fu).
  Proof using TOPH.
    induction fu as [|fu IH]; intros F fc mb ybs CTX YL; unfold lm_cpy2_k; intros until mm; intros INV Hj HB; [exfalso; lia|].
    destruct INV as (SPILL & (bs & XA & XL & NB) & XN & LEN & ZR & (zibs & ZIA & ZIL) & ZIC & ZSH & YB & MI & MU & WM & ST).
    destruct ((T1 top_ctx_step) fc mb mm CTX MU WM) as (FRM & ARTm & MRm & PKm). clear CTX MU WM.
    pose proof PKm as ((jh & HIGHc) & SAVED & (h & HDR) & (zbs & ZA & ZL) & ZZC).
    top_env.
    apply evt_done.
    assert (ZRU : bytes_at bsegs mm ((f + 608) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)).
    { replace ((f + 608) / 8 + 2147450880)%Z with (f / 8 + 2147450956)%Z by (replace (f + 608)%Z with (f + 8 * 76)%Z by lia; rewrite (f64_div f 76 N1); lia).
      exact (zero_run_of_CB mm _ 63 ZSH). }
    assert (ZRV : bytes_at bsegs mm ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)).
    { replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; rewrite (f64_div f 4 N1); lia).
      exact (zero_run_of_CB mm _ 63 ZZC). }
    assert (UFR : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= f + 608)%Z /\ (f + 608 + Z.of_nat (length zibs) <= f0 + fs_size c - 8)%Z)
      by (exists f, 5%nat; split; [exact HinF| rewrite ZIL; lia]).
    assert (VFR : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length zbs) <= f0 + fs_size c - 8)%Z)
      by (exists f, 5%nat; split; [exact HinF| rewrite ZL; lia]).
    eapply (aevt_memcpy_u8 RT AF RTF PMc FDO MST Σ1 K mm lo (Z_to_bv 64 spq)
              (f + 608)%Z zibs 63 ZIA ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite ZIL; lia) ltac:(rewrite ZIL; lia) ltac:(rewrite ZIL; lia) ZRU UFR
              (f + 32)%Z zbs 63 ZA ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite ZL; lia) ltac:(rewrite ZL; lia) ZRV VFR
              ARTm MI ((T1 top_cok) mm ST)) with (nz := (8 * len0)%Z);
      [reflexivity | reflexivity | reflexivity | lia | rewrite ZIL; lia | rewrite ZL; lia | lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' zibs' FRM' RA PR ZIA' ZIL'.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (lm_ctx_call fc fc' mm m' _ _ (conj FRM (conj ARTm (conj MRm PKm))) FRM' RA PR ltac:(lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x /\ ~ (f + 608 <= x < f + 608 + 8 * len0)%Z) PR (fun x H => H)) as AG.
    clear ZIA ZRU ZRV ST MI HIGHc SAVED HDR ZA ZZC YB PKm.
    unfold lm_spillL in SPILL.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL in Hx; cbv beta; split; [aclient_tac| lia]).
    destruct (image_readable_b bsegs m' 40 Y ltac:(vm_compute; reflexivity) ltac:(unfold B_P5LARGE; lia) ltac:(unfold B_P5LARGE; cbn; lia)) as (ybs' & YL' & YB').
    assert (INV' : lm_inv X spq f lo ybs' m' (lm_spillL X f len0 a0 a96 a104) (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 0) m' len False).
    { unfold lm_inv, lm_spillL. split; [exact SPILL|]. split; [exists bs; split; [exact XA| split; [exact XL| exact NB]]|]. split; [exact XN|]. split; [exact LEN|].
      split; [exact ZR|]. split; [exists zibs'; split; [exact ZIA'| lia]|]. split; [exact ZIC|]. split; [exact ZSH|]. split; [exact YB'|]. split; [exact MI'|].
      split; [apply munch_refl|]. split; [apply wmono_refl| exact ST']. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply (EVA lm_after_cpy2 F' fc' ybs' YL' m' (proj1 (proj2 CTX')) Q ((T1 lm_kexit) F' fc' m' CTX') (5 - Z.of_nat fu)%Z (IH F' fc' m' ybs' CTX' YL') j ltac:(lia) ltac:(lia));
      [exact INV' | exact HB].
  Qed.
End LMTOP2.
