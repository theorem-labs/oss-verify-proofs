(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lm_pro
  Sj_num_lm_kit Sj_num_nd_defs Sj_num_lits Sj_num_fc_stmt Sj_num_fc_kit Sj_num_fc_kit2 Sj_num_fc_defs Sj_num_fc_defs2 Sj_num_fc_defs3 Sj_num_fc_kit3 Sj_num_fc_kit4
  Sj_num_fc_pro Sj_num_fc_rel Sj_num_fc_q1 Sj_num_fc_q2a Sj_num_fc_q2b Sj_num_fc_q2c Sj_num_fc_q7 Sj_num_fc_ev Sj_num_fc_tkit Sj_num_fc_top1 Sj_num_fc_top2.
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
  Hypothesis ETP : tp = Z_to_bv 64 0x6a7e68.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFA_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFA_CREDIT <= rt_credit RT Σ0)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 192 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6ca000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
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

  Notation T1 L := (L RT AF RTF PMc FDO MST HPDC HNDC Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo d spq f p n A FIRST LAST txt me
                      ETP ROOM TOP SP16 LOR FRL CRD SPQ NF OUTR PIN PCH TXR FLR TSEP HK) (only parsing).
  Notation fc_srel := (Sj_num_fc_top1.fc_srel RT Σ0 f).
  Notation fc_ctx := (Sj_num_fc_top1.fc_ctx RT Σ0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT d spq f me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).

  Notation EVP L F fc mb Σ used SR HA :=
    (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)) (only parsing).
  Notation EVQ L mb Σ used SR HA :=
    (L sp gp tp lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)
       (T1 top_shpl Σ used mb 0x2a2e0%Z 10416%Z SR HA ltac:(left; reflexivity) eq_refl) (T1 top_shpl Σ used mb 0x2cc60%Z 640%Z SR HA ltac:(right; left; reflexivity) eq_refl)) (only parsing).

  Ltac top_env Σ SR :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof OUTR as (O1 & O2 & O3);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (T1 top_inP Σ _ SR) as HinP; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4.

  Section MSET.

  Hypothesis KPDCP : forall Σ fc mb, fc_ctx Σ 0 fc mb -> fc_pdc_k sp gp tp lo spq f A OUT txt mb (QΣ Σ).
  Hypothesis KNDCP : forall Σ fc mb, fc_ctx Σ 0 fc mb -> fc_ndc_k sp gp tp lo spq f A OUT txt mb (QΣ Σ).

  Lemma fc_kmset : forall Σ fc mb, fc_ctx Σ 0 fc mb -> fc_mset_k sp gp tp lo spq f A FIRST LAST OUT txt mb (QΣ Σ).
  Proof using TOPH KPDCP KNDCP.
    intros Σ fc mb CTX. unfold fc_mset_k. intros until mm. intros INV FRM1 PFp Hq.
    fc_open3 INV.
    pose proof (T1 top_ctx_step Σ 0%Z fc mb mm CTX MU WM) as CTXm. pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm). clear CTX MU WM.
    pose proof PKm as (_ & _ & _ & _ & BGW).
    top_env Σ SR. pose proof SR as (EF & EL & ES & EC).
    apply evt_done.
    destruct (wr_at_rw_CB mm (f + 32) 504 BGW ltac:(lia)) as [jb BIGC]. change (Z.to_nat 504) with 504%nat in BIGC.
    assert (JL : length jb = 504%nat) by exact (proj1 (proj1 (proj1 BIGC))).
    pose proof (u8arr_of_rw_cells asegs mm _ _ _ BIGC) as UA. clear BIGC.
    assert (ZRT : bytes_at asegs mm ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63))
      by (replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia; exact (zero_run_of_CB mm _ 63 BSH)).
    assert (TFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length jb) <= f0 + fs_size c - 8)%Z)
      by (exists f, 4%nat; split; [exact HinF| rewrite JL; lia]).
    destruct (obj_chk RT Σ mm (f + 32)%Z jb 63 lo (Z_to_bv 64 spq) UA ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite JL; lia) ltac:(rewrite JL; lia) ZRT TFR
                (f + 32)%Z 504%Z ltac:(lia) ltac:(lia) ltac:(rewrite JL; lia)) as [_ CD].
    eapply (aevt_memset RT RTF PMc FDO MST Σ K) with (d := (f + 32)%Z) (n := 504%Z) (cb := Z_to_bv 8 0) (lo := lo);
      [reflexivity | reflexivity | reflexivity | lia | lia | exact CD | exact ARTm | exact MI | exact (T1 top_cok Σ 0%Z mm SR ST) | exact FRM1 |].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (T1 fc_ctx_call Σ 0%Z fc fc' mm m' _ _ CTXm FRM' RA PR ltac:(lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' _ PR (fun x H => H)) as AG.
    assert (BIG' : rw_cells asegs m' (f + 32) [CB 504 (repeat (Z_to_bv 8 0) 504)]).
    { change (Z.to_nat 504) with 504%nat in BY. pose proof (rw_cells_CB_intro m' (f + 32)%Z (repeat (Z_to_bv 8 0) 504) BY) as H. rewrite repeat_length in H. apply H.
      exact (wr_at_transport asegs mm m' _ _ BGW WM'). }
    clear UA ST MI ZRT BGW PKm.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; cbv beta; split; [aclient_tac| lia]).
    pose proof CTX' as (SR' & HU' & FRMc' & ARTc' & MRc' & PKc').
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVQ fc_648 m' Σ 0%Z SR' ARTc' (KPDCP Σ fc' m' CTX') (KNDCP Σ fc' m' CTX') (T1 top_shpd Σ 0%Z m' SR' ARTc') (T1 top_shpl3 Σ 0%Z m' SR' ARTc')
                          (T1 top_ccp Σ 0%Z m' SR' ARTc') (T1 top_spq8) qe IP IL FPT FL);
                        [ pose proof (munch_refl (fc_W lo spq f OUT) m') as MU'; pose proof (wmono_refl asegs m') as WMr; fc_close3 | exact FRM' | exact PFp | exact Hq | exact BIG']].
    num_st_eq.
  Qed.
  End MSET.
End FCTOP.
