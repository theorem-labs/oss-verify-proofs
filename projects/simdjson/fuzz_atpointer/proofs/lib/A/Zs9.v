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
  Zrq Zs2 Zrt Zru Zrv Zrw Zs1 Zr3 Zs6 Zs7.
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

  Notation T1 L := (L RT AF RTF PMc FDO MST HPDC HNDC Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo d spq f p n A FIRST LAST txt me
                      ETP ROOM TOP SP16 LOR FRL CRD SPQ NF OUTR PIN PCH TXR FLR TSEP HK) (only parsing).
  Notation fc_srel := (Zs7.fc_srel RT Σ0 f).
  Notation fc_ctx := (Zs7.fc_ctx RT Σ0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT d spq f me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).

  Notation EVP L F fc mb Σ used SR HA :=
    (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)) (only parsing).
  Notation EVQ L mb Σ used SR HA :=
    (L sp gp tp lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)
       (T1 top_shpl Σ used mb 0x285a0%Z 10416%Z SR HA ltac:(left; reflexivity) eq_refl) (T1 top_shpl Σ used mb 0x2af20%Z 640%Z SR HA ltac:(right; left; reflexivity) eq_refl)) (only parsing).

  Ltac top_env Σ SR :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof OUTR as (O1 & O2 & O3);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4.

  Lemma fc_k7f4 : forall Σ used fc mb, fc_ctx Σ used fc mb -> fc_7f4_k sp gp tp lo spq f A OUT txt mb (QΣ Σ).
  Proof using TOPH.
    intros Σ used fc mb CTX. unfold fc_7f4_k. intros until mm. intros INV FRM1.
    fc_popen INV.
    destruct (T1 top_ctx_step Σ used fc mb mm CTX MU WM) as (SR & HU & FRM & ARTm & MRm & PKm). clear CTX MU WM.
    destruct PKm as ((jh & HIGHc) & SAVED & (h & HDR) & SHW & BGW).
    top_env Σ SR. pose proof SR as (EF & EL & ES & EC).
    assert (HL : length h = 32%nat) by exact (proj1 (proj1 (proj1 HDR))).
    apply (rw_cells_split_CB asegs mm f [] 32 h [] [8; 24]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app] in HDR.
    eapply (fc_rel1 f mm (proj1 NF) ltac:(lia) N4 ltac:(lia) _); [exact HDR | exact PSH | exact MI | apply munch_refl | apply wmono_refl |].
    clear HDR MI PSH. intros jp' mm2 HDR2 PSH2 MI2 MU2 WM2.
    apply evt_done.
    transport_after_call asegs mm mm2 MU2 WM2.
    pose proof (T1 top_art Σ used _ mm mm2 SR (TK tk_wf_WR Σ SR) ARTm MU2 WM2) as ART2.
    pose proof (T1 top_mrel Σ used _ mm mm2 SR (TK tk_wf_WR Σ SR) ARTm MRm MU2 WM2) as MR2.
    clear HDR2 MU2 WM2.
    eapply (aevt_set_shadow RT RTF PMc FDO MST Σ K 0xf5%Z) with (d := S) (n := 128%Z) (lo := lo);
      [unfold set_shadow_vals; cbn [In]; do 11 right; left; reflexivity | reflexivity | reflexivity | lia
      | intros i Hi; exists f, 4%nat; split; [exact HinF|]; unfold shad, SHB; rewrite FS4; replace (f + 1024)%Z with (f + 128 * 8)%Z by lia; rewrite Z.div_add by lia; lia
      | exact SHW | exact ART2 | exact MI2 | exact (T1 top_cok Σ used mm2 SR ST) | exact FRM1 |].
    intros v0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m3 FRM' RA PR _.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART3 & MI3 & WM3 & ST3).
    pose proof (TKm fc_mrel_ex Σ SR mm2 m3 S 128%Z ART2 MR2 WM3 PR ltac:(right; lia)) as MR3.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm2 m3 (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (S <= x < S + 128)%Z) PR (fun x H => H)) as AG.
    unfold LM_SAVED in SAVED. clear ST MI2 SHW BSH PSH2 TXT PNS BGW.
    rt_transport_with mm2 m3 AG WM3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| lia]).

    destruct (af_frame_release RT AF Σ m3 f 4%nat (rt_frames RT Σ0) ART3 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1 & LAST' & REL).
    rewrite FS4 in LAST'. replace (f + 1024 - 8)%Z with (f + 1016)%Z in LAST' by lia.
    pose proof (af_sp0_range RT AF Σ m3 ART3) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof (T1 top_lor1 Σ used SR) as LOR1. unfold STACK_WIN in LOR1, FL1.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply (fc_rel2 f fl m3 (proj1 NF) ltac:(lia) N4 ltac:(lia) ltac:(lia) _); [exact LAST' | exact FLAG | exact MI3 | apply munch_refl | apply wmono_refl |].
    clear LAST' FLAG MI3. intros mm4 FLAG0 MI4 MU4 WM4.
    destruct (REL mm4 MU4 WM4 FLAG0) as (ART4 & EF4 & EL4 & ES4 & EC4 & EA4 & EM4).
    apply evt_done. apply (aevt_frame_release RT PMc Σ Σ2 K _ EA4 EM4).
    assert (FLO' : (fl < OUT \/ OUT + 8 <= fl)%Z).
    { destruct (Z_lt_le_dec fl OUT) as [H|H]; [left; exact H|]. destruct (Z_lt_le_dec fl (OUT + 8)) as [H2|H2]; [| right; exact H2].
      exfalso. apply NAC. left. unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *. lia. }
    transport_after_call asegs m3 mm4 MU4 WM4.
    assert (MR4 : MREL mm4).
    { destruct MR3 as [WMa PRa]. split; [exact (wmono_trans asegs _ _ _ WMa WM4)|]. eapply pres_fp_trans; [exact PRa|].
      apply (pres_fp_of_munch _ _ _ _ [(fl, (fl + 1)%Z)] _ _ MU4). intros a Ha _. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
      assert (a = fl) by lia. subst a. unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK in *.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [left; lia | right; left; exact Ha | right; right; left; rewrite EL; exact Ha
        | right; right; right; left; destruct Ha as (f1 & k1 & Hin & Hr); exists f1, k1; split; [rewrite EF; right; exact Hin| exact Hr]
        | right; right; right; right; destruct Ha as (f1 & k1 & Hin & Hr); exists f1, k1; split; [rewrite EF; right; exact Hin| exact Hr]]. }
    destruct (rw_cells_forget asegs _ _ _ SPILL) as [jsp SPILLf]. cbn [cells_size csize Nat.add] in SPILLf.
    apply (aevt_evt RT AF PMc MST).
    eapply (fc_leave ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo d spq SPQ ROOM TOP (fun ms' => aevt RT PMc Σ2 K ms'));
      [exact SPILLf | exact HIGHc | exact SAVED | exact ST3 |].
    intros zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 STF.
    apply evt_done.
    eapply HK; [exact FRM' | | | exact OUTC | exact EF4 | rewrite EL4; exact EL | rewrite ES4; exact ES | rewrite EC4; unfold FFA_CREDIT; lia].
    - split; [exact ART4|]. split; [exact MI4|]. split; [exact (proj1 MR4)| exact STF].
    - intros a Ha Hn. apply (proj2 MR4 a Ha). cbn [outside]. split; [lia| exact I].
  Qed.

  Lemma fc_ctx_call2 : forall Σ Σ' used used' fc fc' (mm m' : mem) D N, fc_ctx Σ used fc mm -> fc_srel Σ' used' -> (0 <= used' <= 9)%Z -> frm0 fc' ->
    rt_after RT Σ' spq lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq D N mm m' ->
    (f + 32 <= D /\ D + N <= f + 1016)%Z -> fc_ctx Σ' used' fc' m'.
  Proof using TOPH.
    intros Σ Σ' used used' fc fc' mm m' D N (SR & HU & FRM & HA & MR & PK) SR' HU' FRM' (ART' & MI' & WM' & ST') PR HD.
    split; [exact SR'|]. split; [exact HU'|]. split; [exact FRM'|]. split; [exact ART'|].
    split; [eapply (TKm fc_mrel_ex Σ SR mm m' D N HA MR WM' PR); left; lia|].
    destruct PK as ((jh & P2) & P3 & (h & P4) & P6 & P7).
    top_env Σ SR.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (D <= x < D + N)%Z) PR (fun x H => H)) as AG.
    unfold LM_SAVED in P3.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| lia]).
    split; [exists jh; exact P2|]. split; [exact P3|]. split; [exists h; exact P4|].
    split; [exact P6| exact P7].
  Qed.
  Lemma fc_ctx_call : forall Σ used fc fc' (mm m' : mem) D N, fc_ctx Σ used fc mm -> frm0 fc' -> rt_after RT Σ spq lo mm m' ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq D N mm m' -> (f + 32 <= D /\ D + N <= f + 1016)%Z -> fc_ctx Σ used fc' m'.
  Proof using TOPH.
    intros Σ used fc fc' mm m' D N CTX FRM' RA PR HD. pose proof CTX as (SR & HU & _).
    exact (fc_ctx_call2 Σ Σ used used fc fc' mm m' D N CTX SR HU FRM' RA PR HD).
  Qed.
End FCTOP.
