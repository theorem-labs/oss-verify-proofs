(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx I_lkit Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqa Zq7 Zq8 Zq9 Zqb Zt9
  Zt5 Ztr Zsv Zs4 Zr5 Zr6 Zr0 Zr1 Zr2 Zr7 Zr8
  Zrq Zs2 Zrt Zru Zrv Zrw Zs1 Zr3 Zs6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FCTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HPDC : pdca_stmt RT PMc.
  Hypothesis HNDC : ndca_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (OUT lo d spq f p n A FIRST LAST : Z) (txt : list byte) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis ETP : tp = Z_to_bv 64 0x646eb0.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFA_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFA_CREDIT <= rt_credit RT Σ0)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 192 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x669000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis OUTR : (OUT mod 8 = 0 /\ SP <= OUT /\ OUT + 8 <= USTACK_TOP)%Z.

  Hypothesis PIN : In (p, n) (rt_live RT Σ0).
  Hypothesis PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + TL <= p + n)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis FLR : (A <= FIRST /\ FIRST < LAST /\ LAST <= A + TL)%Z.
  Hypothesis TSEP : ((A + TL <= f \/ f + 1024 <= A) /\ (A + TL <= S \/ S + 128 <= A))%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_ex (rt_live RT Σ0) (rt_frames RT Σ0) SP OUT 8 me m' ->
     rw_cells asegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - FFA_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection TOPH := AF RTF FDO MST HPDC HNDC ETP ROOM TOP SP16 LOR FRL CRD SPQ NF OUTR PIN PCH TXR FLR TSEP HK.

  Notation MREL := (fc_mrel RT Σ0 sp OUT me).
  Notation PARK := (fc_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d spq f).
  Notation W := (fc_W lo spq f OUT).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').

  Definition fc_srel (Σ : rts RT) (used : Z) : Prop :=
    rt_frames RT Σ = (f, 4%nat) :: rt_frames RT Σ0 /\ rt_live RT Σ = rt_live RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0
    /\ (rt_credit RT Σ0 - 1 - used <= rt_credit RT Σ)%Z.

  Definition fc_ctx (Σ : rts RT) (used : Z) (fc : bv 32) (mb : mem) : Prop :=
    fc_srel Σ used /\ (0 <= used <= 9)%Z /\ frm0 fc /\ ART RT Σ mb /\ MREL mb /\ PARK mb.

  Notation TK L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).

  Lemma top_spq : (0 <= d <= 16 /\ spq = SP - 192 - d)%Z.
  Proof using TOPH. destruct SPQ as [[->| ->] ->]; lia. Qed.
  Lemma top_spq8 : (spq mod 8 = 0)%Z.
  Proof using TOPH. destruct SPQ as [[->| ->] ->]; Z.div_mod_to_equations; lia. Qed.
  Lemma top_lor1 : forall Σ used, fc_srel Σ used -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z.
  Proof using TOPH. intros Σ used (_ & _ & ES & _). rewrite ES. exact LOR. Qed.
  Lemma top_inF : forall Σ used, fc_srel Σ used -> In (f, 4%nat) (rt_frames RT Σ).
  Proof using TOPH. intros Σ used (EF & _). rewrite EF. left. reflexivity. Qed.
  Lemma top_inP : forall Σ used, fc_srel Σ used -> In (p, n) (rt_live RT Σ).
  Proof using TOPH. intros Σ used (_ & EL & _). rewrite EL. exact PIN. Qed.
  Lemma top_fpok : forall Σ used, fc_srel Σ used -> fp_ok RT Σ lo W.
  Proof using TOPH. intros Σ used SR. exact (TK tk_fpok Σ SR _ (TK tk_wf_W Σ SR)). Qed.
  Lemma top_art : forall Σ used W' (mb mm : mem), fc_srel Σ used -> tk_wf sp OUT lo f W' -> ART RT Σ mb -> munch W' mb mm -> wmono asegs mb mm -> ART RT Σ mm.
  Proof using TOPH. intros Σ used W' mb mm SR HW HA MU WM. exact (art_of_munch RT AF Σ mb mm lo W' HA (top_lor1 Σ used SR) (TK tk_fpok Σ SR W' HW) MU WM). Qed.
  Lemma top_mrel : forall Σ used W' (mb mm : mem), fc_srel Σ used -> tk_wf sp OUT lo f W' -> ART RT Σ mb -> MREL mb -> munch W' mb mm -> wmono asegs mb mm -> MREL mm.
  Proof using TOPH. intros Σ used W' mb mm SR. exact (TKm fc_mrel_munch Σ SR W' mb mm). Qed.

  Lemma top_ctx_step : forall Σ used fc (mb mm : mem), fc_ctx Σ used fc mb -> munch W mb mm -> wmono asegs mb mm -> fc_ctx Σ used fc mm.
  Proof using TOPH.
    intros Σ used fc mb mm (SR & HU & FRM & HA & MR & PK) MU WM. split; [exact SR|]. split; [exact HU|]. split; [exact FRM|].
    split; [exact (top_art Σ used _ mb mm SR (TK tk_wf_W Σ SR) HA MU WM)|].
    split; [exact (top_mrel Σ used _ mb mm SR (TK tk_wf_W Σ SR) HA MR MU WM)|].
    exact (fc_park_munch RT AF Σ0 Σ ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo d spq f ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR
             _ mb mm (TK tk_wfp_W Σ SR) PK MU WM).
  Qed.
  Lemma top_cok : forall Σ used (mm : mem), fc_srel Σ used -> stk asegs mm lo spq -> call_ok RT Σ mm (Z_to_bv 64 spq) lo.
  Proof using TOPH.
    intros Σ used mm SR ST. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (stk_lo_nonneg asegs _ _ _ ST) as LO0. destruct SPQ as [Hd Hs]. unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *.
    unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [exact (top_lor1 Σ used SR)|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia].
  Qed.

  Lemma top_F64 : (f mod 64 = 0)%Z. Proof using TOPH. exact (proj1 NF). Qed.
  Lemma top_FLO : (0x669000 <= f /\ f + 1016 <= lo)%Z. Proof using TOPH. destruct NF as (_ & N2 & N3 & _). split; assumption. Qed.
  Lemma top_FSH : (f + 1016 <= S \/ S + 127 <= f)%Z. Proof using TOPH. exact (proj1 (proj2 (proj2 (proj2 NF)))). Qed.
  Lemma top_FS0 : (0 <= S /\ S + 127 <= lo)%Z. Proof using TOPH. exact (proj2 (proj2 (proj2 (proj2 NF)))). Qed.
  Lemma top_shpt : forall Σ used (mb : mem), fc_srel Σ used -> ART RT Σ mb ->
    forall m', munch W mb m' -> wmono asegs mb m' -> shz m' (8 * (FIRST / 8)) (LAST - 8 * (FIRST / 8)).
  Proof using TOPH.
    intros Σ used mb SR HA m' MU WM. destruct PCH as (P8 & PA & PL & PT). destruct FLR as (R1 & R2 & R3).
    pose proof (shzp_live RT AF Σ mb lo W p n HA (top_lor1 Σ used SR) (top_fpok Σ used SR) (top_inP Σ used SR) P8 m' MU WM) as H.
    eapply shz_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
  Qed.
  Lemma top_shpo : forall Σ used (mb : mem), fc_srel Σ used -> ART RT Σ mb ->
    forall m', munch W mb m' -> wmono asegs mb m' -> shz m' OUT 8.
  Proof using TOPH.
    intros Σ used mb SR HA m' MU WM. destruct OUTR as (O8 & O1 & O2).
    pose proof (af_sp0_range RT AF Σ mb HA) as SP0R. pose proof (top_lor1 Σ used SR) as L1.
    unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP, STACK_WIN in *.
    exact (shzp_stack RT AF Σ mb lo W OUT 8 HA (top_lor1 Σ used SR) (top_fpok Σ used SR) ltac:(unfold STACK_WIN; lia) ltac:(unfold USTACK_TOP; lia) O8 m' MU WM).
  Qed.
  Lemma top_shpd : forall Σ used (mb : mem), fc_srel Σ used -> ART RT Σ mb ->
    forall m', munch W mb m' -> wmono asegs mb m' -> shz m' (spq + 80) 8.
  Proof using TOPH.
    intros Σ used mb SR HA m' MU WM. pose proof top_spq8 as Q8. pose proof top_spq as [Hd Hs].
    pose proof (top_lor1 Σ used SR) as L1. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP, STACK_WIN in *.
    exact (shzp_stack RT AF Σ mb lo W (spq + 80) 8 HA (top_lor1 Σ used SR) (top_fpok Σ used SR) ltac:(unfold STACK_WIN; lia) ltac:(unfold USTACK_TOP; lia)
             ltac:(Z.div_mod_to_equations; lia) m' MU WM).
  Qed.
  Lemma top_shpl : forall Σ used (mb : mem) a k, fc_srel Σ used -> ART RT Σ mb -> In (a, k) NUM_LITS -> (k mod 8 = 0)%Z ->
    forall m', munch W mb m' -> wmono asegs mb m' -> shz m' a k.
  Proof using TOPH.
    intros Σ used mb a k SR HA Hin K8 m' MU WM.
    pose proof (shzp_lits RT AF Σ mb lo W a k (num_lits_of_af RT AF) HA (top_lor1 Σ used SR) (top_fpok Σ used SR) Hin m' MU WM) as H.
    replace (8 * (k / 8))%Z with k in H by (Z.div_mod_to_equations; lia). exact H.
  Qed.
  Lemma top_shpl3 : forall Σ used (mb : mem), fc_srel Σ used -> ART RT Σ mb ->
    forall m', munch W mb m' -> wmono asegs mb m' -> shz m' 0x2ae60 160.
  Proof using TOPH.
    intros Σ used mb SR HA m' MU WM.
    pose proof (art_of_munch RT AF Σ mb m' lo W HA (top_lor1 Σ used SR) (top_fpok Σ used SR) MU WM) as HA'.
    change 160%Z with (8 * (160 / 8))%Z. apply shz_of_acc; [| reflexivity | lia].
    apply (acc_lit RT AF Σ m' _ _ HA'). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
  Qed.
  Lemma top_ccp : forall Σ used (mb : mem), fc_srel Σ used -> ART RT Σ mb ->
    forall m', munch W mb m' -> wmono asegs mb m' -> client_consts m'.
  Proof using TOPH.
    intros Σ used mb SR HA m' MU WM.
    exact (af_client_consts RT AF Σ m' (art_of_munch RT AF Σ mb m' lo W HA (top_lor1 Σ used SR) (top_fpok Σ used SR) MU WM)).
  Qed.
End FCTOP.
