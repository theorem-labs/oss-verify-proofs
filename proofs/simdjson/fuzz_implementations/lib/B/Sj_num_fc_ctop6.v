(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit
  Sj_num_fc_stmt Sj_num_fc_defs Sj_num_fc_rel Sj_num_fc_pro Sj_num_fc_pro2 Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_dc Sj_num_fc_top14 Sj_num_fc_tkit Sj_num_fc_ctop1 Sj_num_fc_ctop2 Sj_num_fc_ctop3 Sj_num_fc_ctop4 Sj_num_fc_pp1 Sj_num_fc_ctop5 Sj_num_fc_pstmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac fcb_at_simpl :=
  repeat match goal with
  | H : context [fcb_W (fcb_at ?E0 ?m0)] |- _ => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0) in H
  | |- context [fcb_W (fcb_at ?E0 ?m0)] => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0)
  | H : context [fcb_saved (fcb_at ?E0 ?m0)] |- _ => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0) in H
  | |- context [fcb_saved (fcb_at ?E0 ?m0)] => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0)
  end;
  cbn [fcb_at q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0] in *.

Ltac fc_close_at :=
  unfold FCINV; fcb_at_simpl;
  split; [unfold fcb_spill; fcb_at_simpl; eassumption|]; split; [do 4 eexists; unfold fcb_pns; eassumption|]; split; [lia|]; split; [lia|];
  split; [fcp_forget_obj|]; split; [fcp_forget_obj|];
  split; [first [ intros BGF; discriminate BGF | intros _; fcp_forget_obj ]|];
  split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Section FCTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HPDC : pdcb_stmt RT PMc.
  Hypothesis HNDC : ndcb_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).

  Variable E : fcbenv.
  Variables (p n : Z) (me : mem).
  Notation SP := (q_SP E).
  Notation S := (q_S E).
  Notation f := (q_f E).
  Notation lo := (q_lo E).
  Notation spq := (q_spq E).
  Notation OUT := (q_OUT E).
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation TL := (q_TL E).
  Hypothesis OK : fcb_ok E.
  Hypothesis ETP : q_tp E = Z_to_bv 64 B_TP.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFB_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFB_CREDIT <= rt_credit RT Σ0)%Z.

  Hypothesis PIN : In (p, n) (rt_live RT Σ0).
  Hypothesis PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + TL <= p + n)%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_ex (rt_live RT Σ0) (rt_frames RT Σ0) SP OUT 8 me m' ->
     rw_cells bsegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - FFB_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0' t1' t2' (q_s0 E) (q_s1 E) a0' a1' a2' a3' a4' a5' a6' a7'
                               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3' t4' t5' t6')
                          F' (ret_pc (q_ra E)) fc' None m' (seg_rom bsegs)).
  Collection TOPH := AF RTF FDO MST HPDC HNDC OK ETP SP16 LOR FRL CRD PIN PCH HK.

  Notation MREL := (fc_mrel RT Σ0 E me).
  Notation PARK := (fc_park E).
  Notation W := (fcb_W E).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').
  Notation EB mb := (fcb_at E mb).

  Notation T1 L := (L RT AF RTF PMc FDO MST HPDC HNDC Σ0 K E p n me OK ETP SP16 LOR FRL CRD PIN PCH HK) (only parsing).
  Notation fc_srel := (Sj_num_fc_ctop1.fc_srel RT Σ0 E).
  Notation fc_ctx := (Sj_num_fc_ctop1.fc_ctx RT Σ0 E me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ E OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ E me OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).

  Ltac top_env Σ SR :=
    pose proof OK as OK'; destruct OK' as [ROOM TOP [SPQ1 SPQ2] (F64 & FLO1 & FLO2) FSH FS0 (TX1 & TX2 & TX3) (FL1 & FL2 & FL3) (TS1 & TS2) (O1 & O2 & O3)];
    unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, FCB_GTOP, NUM_TXT_MAX, USTACK_TOP in *;
    pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (T1 top_inP Σ _ SR) as HinP; pose proof PCH as (PC1 & PC2 & PC3 & PC4);
    pose proof (f64_8 f F64) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4.

  Section BODY.
  Hypothesis HPARSE : forall (E' : fcbenv) (Q : machine_state -> Prop), fcb_ok E' -> fcb_prov E' -> fcb_kf14 E' Q -> fcb_kerr1 E' Q -> fcb_parse_stmt E' Q.

  Lemma fc_bodyc : forall Σ fc mb, fc_ctx Σ 0 fc mb -> fcb_parse_stmt (EB mb) (QΣ Σ).
  Proof using TOPH HPARSE.
    intros Σ fc mb CTX. pose proof CTX as (SR & HU & FRM & HA & MRb & PKb).
    apply (HPARSE (EB mb) (QΣ Σ) (T1 top_okb mb) (T1 top_prov Σ 0%Z mb SR HA)).
    - exact (fcb_f14 (EB mb) (T1 top_okb mb) (T1 top_prov Σ 0%Z mb SR HA) (QΣ Σ) (T1 fc_kf5 Σ 0%Z fc mb CTX) (T1 fc_kmset Σ fc mb CTX)).
    - exact (T1 fc_kerr1 Σ fc mb CTX).
  Qed.
  End BODY.
End FCTOP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_num_kclosed Sj_num_kclosed2.

Lemma fcb_cb8s_c8s : forall segs (m : mem) A (bss : list (list byte)) pre,
  rw_cells segs m A (pre ++ map (CB 8) bss) -> rw_cells segs m A (pre ++ map (fun b => C8 (le_bytes_to_word b)) bss).
Proof.
  intros segs m A bss. induction bss as [| b bss IH]; intros pre H; [exact H|].
  cbn [map] in *. apply num_cb8_c8 in H.
  replace (pre ++ C8 (le_bytes_to_word b) :: map (CB 8) bss) with ((pre ++ [C8 (le_bytes_to_word b)]) ++ map (CB 8) bss) in H by (rewrite <- app_assoc; reflexivity).
  apply IH in H. rewrite <- app_assoc in H. exact H.
Qed.

Lemma fcb_spq_ex : forall SP, (SP mod 16 = 0)%Z -> exists spq, (SP - 272 <= spq <= SP - 256 /\ spq mod 32 = 0)%Z.
Proof.
  intros SP H. destruct (Z.eq_dec ((SP - 256) mod 32) 0) as [E|E]; [exists (SP - 256)%Z| exists (SP - 272)%Z]; Z.div_mod_to_equations; lia.
Qed.

Theorem fcb_ok_gen :
  (forall (E' : fcbenv) (Q : machine_state -> Prop), fcb_ok E' -> fcb_prov E' -> fcb_kf14 E' Q -> fcb_kerr1 E' Q -> fcb_parse_stmt E' Q) ->
  forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> pdcb_stmt RT PMc -> ndcb_stmt RT PMc -> fcb_stmt RT PMc.
Proof.
  intros HPARSE RT AF RTF PMc FDO MST HPDC HNDC. unfold fcb_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A FIRST LAST OUT lo p n txt v0
    ETP FRM FRL FNZ CRD ART0 MI ST LOR ROOM TOP SP16 PIN P8 PA PL PT TXT TLR FL1 FL2 FL3 OUTC O8 OSP OTOP HK.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
  pose proof (af_live_range RT AF Σ m p n ART0 PIN) as (LR1 & LR2 & _). unfold STACK_WIN in LR2.
  unfold USTACK_TOP in OTOP. unfold FFB_FRAMES in FRL. unfold FFB_CREDIT in CRD.
  destruct (fcb_spq_ex (bv_unsigned sp) SP16) as (spq & SPQ0).
  apply (aevt_evt RT AF PMc MST).
  eapply (fcb_pro1 (mkFcbEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo spq 0 txt m) ROOM TOP SPQ0 ltac:(unfold FCB_GTOP; cbn [q_lo]; lia) SP16 F fc _);
    [| exact MI | exact ST | exact (af_client_consts RT AF Σ m ART0)].

  unfold fcb_call1_k, FCBREAL.
  cbn [q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0].
  intros xt0 xt1 ya1 ya2 xa6 xa7 xs4 xs7 xs11 xt3 xt4 xt5 xt6 mm REAL MI1 MU1 WM1 ST1.
  destruct REAL as ((jsp & SPILLc) & (jh & HIGHc) & SAVED). unfold fcb_saved in SAVED.
  cbn [q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11] in SAVED.
  apply evt_done.
  destruct SPQ0 as [SPQ1 SPQ2].
  apply (bytes_at_transport bsegs [((bv_unsigned sp - 272)%Z, bv_unsigned sp)] m mm) in TXT; [| exact MU1 | cbn [disjoint_from]; split; [lia| exact I]].
  apply (rw_cells_transport bsegs [((bv_unsigned sp - 272)%Z, bv_unsigned sp)] m mm) in OUTC; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]].
  assert (FP1 : fp_ok RT Σ lo [((bv_unsigned sp - 272)%Z, bv_unsigned sp)]) by (constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia| constructor]).
  pose proof (art_of_munch RT AF Σ m mm lo _ ART0 LOR FP1 MU1 WM1) as ART1.
  assert (COK : call_ok RT Σ mm (Z_to_bv 64 spq) lo).
  { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [exact LOR|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
  eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ K 4%nat); [left; reflexivity | exact ETP | unfold FRAMES_MAX in *; lia | lia | exact ART1 | exact MI1 | exact COK | intros Efr0; exact (False_ind _ (FNZ Efr0)) | exact FRM |].
  intros Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' FRM' RA PR W1 W2 EF EL ES EC F0 F64 FTOP.
  rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').

  pose proof (agree_pres _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x) PR (fun x H => H)) as AG.
  rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; aclient_tac).

  assert (MREL : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(OUT, (OUT + 8)%Z)] m m').
  { eapply pres_fp_trans.
    - apply (pres_fp_of_munch _ _ _ _ _ _ _ MU1). intros a Ha _. pose proof (aclient_split_c RT AF Σ m _ a ART0 Ha) as SPL.
      cbn [outside]. split; [lia| exact I].
    - intros a Ha _. apply PR. eapply aclient_mono; [exact Ha| auto| auto| lia]. }
  assert (MRb : fc_mrel RT Σ (mkFcbEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo spq f txt m) m m')
    by (split; [exact (wmono_trans bsegs _ _ _ WM1 WM')| exact MREL]).

  assert (HinF : In (f, 4%nat) (rt_frames RT Σ')) by (rewrite EF; left; reflexivity).
  pose proof (new_frame_facts RT AF Σ' m' f 4 1016 lo ART' ltac:(rewrite ES; exact LOR) HinF eq_refl eq_refl ltac:(lia)) as NF.
  change (1016 / 8)%Z with 127%Z in NF.
  pose proof (af_frames_range RT AF Σ' m' f 4%nat ART' HinF) as (_ & _ & _ & FR4). specialize (FR4 p n ltac:(rewrite EL; exact PIN)).
  pose proof (proj1 (af_fshadow_apart RT AF Σ' m' f 4%nat ART' HinF) p n ltac:(rewrite EL; exact PIN)) as FS4.
  change (fs_size 4) with 1024%Z in FR4, FS4. unfold shad, SHB in FS4.
  replace ((f + 1024) / 8)%Z with (f / 8 + 128)%Z in FS4 by (clear - F64; Z.div_mod_to_equations; lia).
  change (fs_size 4 - 8)%Z with 1016%Z in W1. change (fs_size 4 / 8)%Z with 128%Z in W2. unfold shad, SHB in W2.
  destruct NF as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).
  assert (OKE : forall mb, fcb_ok (mkFcbEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo spq f txt mb)).
  { intros mb. constructor; cbn [q_sp q_lo q_spq q_f q_A q_txt q_FIRST q_LAST q_OUT]; unfold FCB_GTOP, NUM_TXT_MAX, USTACK_TOP; repeat split; try assumption; lia. }
  destruct (wr_at_rw_CB m' f 1016 W1 ltac:(lia)) as [jf FRD]. destruct (wr_at_rw_CB m' _ 128 W2 ltac:(lia)) as [js FRS].
  change (Z.to_nat 1016) with 1016%nat in FRD. change (Z.to_nat 128) with 128%nat in FRS.
  apply (rw_cells_split_CB bsegs m' f [] 1016 jf [] [32; 504; 480]%nat) in FRD; [| reflexivity]. cbn [mk_CB_cells app] in FRD.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 32 _] _) FRD) as [HDR0 FD1]. clear FRD.
  cbn [cells_size csize Nat.add] in FD1. change (Z.of_nat 32) with 32%Z in FD1.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 504 _] _) FD1) as [BIG0 _]. clear FD1.
  apply (rw_cells_split_CB bsegs m' f [] 32 _ [] [8;8;8;8]%nat) in HDR0; [| reflexivity]. cbn [app] in HDR0. rewrite app_nil_r in HDR0.
  apply (rw_cells_split_CB bsegs m' _ [] 128 js [] [4; 63; 9; 52]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 4 _] _) FRS) as [S0 FRS1]. clear FRS. cbn [cells_size csize Nat.add] in FRS1. change (Z.of_nat 4) with 4%Z in FRS1.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 63 _] _) FRS1) as [SZ FRS2]. clear FRS1. cbn [cells_size csize Nat.add] in FRS2. change (Z.of_nat 63) with 63%Z in FRS2.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 9 _] _) FRS2) as [S1 _]. clear FRS2.
  replace (f / 8 + 2147450880 + 4)%Z with (f / 8 + 2147450884)%Z in SZ, S1 by lia.
  replace (f / 8 + 2147450884 + 63)%Z with (f / 8 + 2147450947)%Z in S1 by lia.

  apply (rw_cells_split_CB bsegs m' spq [] 152 jsp [] [64; 8; 72; 8]%nat) in SPILLc; [| reflexivity]. cbn [mk_CB_cells app] in SPILLc.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 64 _] _) SPILLc) as [SP64 WK1]. clear SPILLc. cbn [cells_size csize Nat.add] in WK1. change (Z.of_nat 64) with 64%Z in WK1.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 8 _] _) WK1) as [SLOT WK2]. clear WK1. cbn [cells_size csize Nat.add] in WK2. change (Z.of_nat 8) with 8%Z in WK2.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 72 _] _) WK2) as [PNS0 DG0]. clear WK2. cbn [cells_size csize Nat.add] in DG0. change (Z.of_nat 72) with 72%Z in DG0.
  replace (spq + 64 + 8)%Z with (spq + 72)%Z in PNS0, DG0 by lia. replace (spq + 72 + 72)%Z with (spq + 144)%Z in DG0 by lia.

  apply (aevt_evt RT AF PMc MST).
  replace (ret_pc (Z_to_bv 64 1009864)) with (Z_to_bv 64 1009864) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (fcb_poison (mkFcbEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo spq f txt m') (OKE m') _);
    [| exact HDR0 | exact SLOT | exact S0 | exact SZ | exact S1 | exact MI' | exact (munch_refl _ m') | exact (wmono_refl bsegs m')].
  cbn [q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0].
  intros a0' a1' a2' a3' h' j0' jz' j1' mm2 HDR2 SLOT2 S0' SZ' S1' MI2 MU2 WM2.
  apply evt_done.
  clear HDR0 SLOT S0 SZ S1 MI' AG.
  transport_after_call bsegs m' mm2 MU2 WM2.

  pose (E1 := mkFcbEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo spq f txt m).
  assert (SR : Sj_num_fc_ctop1.fc_srel RT Σ E1 Σ' 0) by (unfold Sj_num_fc_ctop1.fc_srel; cbn [E1 q_f]; repeat split; try assumption; lia).
  assert (HW2 : tk_wf E1 [((spq + 64)%Z, (spq + 72)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 76)%Z)])
    by exact (tk_wf_W2 RT AF Σ Σ' E1 (OKE m) LOR EF EL ES).
  apply (rw_cells_split_CB bsegs mm2 f [] 32 h' [] [8; 24]%nat) in HDR2; [| reflexivity]. cbn [mk_CB_cells app] in HDR2.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 8 _] _) HDR2) as [H0 H24]. clear HDR2. cbn [cells_size csize Nat.add] in H24. change (Z.of_nat 8) with 8%Z in H24.
  assert (CTX : Sj_num_fc_ctop1.fc_ctx RT Σ E1 m Σ' 0 fc' mm2).
  { split; [exact SR|]. split; [lia|]. split; [exact FRM'|].
    split; [exact (art_of_munch RT AF Σ' m' mm2 lo _ ART' ltac:(rewrite ES; exact LOR) (tk_fpok RT AF Σ Σ' E1 (OKE m) LOR EF EL ES _ HW2) MU2 WM2)|].
    split; [exact (fc_mrel_munch RT AF Σ Σ' E1 m (OKE m) LOR EF EL ES _ m' mm2 HW2 ART' MRb MU2 WM2)|].
    split; [exists jh; exact HIGHc|]. split; [exact SAVED|]. split; [eexists; exact H24| exact W2]. }

  apply (rw_cells_split_CB bsegs mm2 _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in SP64; [| reflexivity]. cbn [mk_CB_cells app] in SP64.
  repeat match type of SP64 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in SP64; clearbody j end.
  lazymatch type of SP64 with rw_cells _ _ _ [CB 8 ?b0; CB 8 ?b1; CB 8 ?b2; CB 8 ?b3; CB 8 ?b4; CB 8 ?b5; CB 8 ?b6; CB 8 ?b7] =>
    change [CB 8 b0; CB 8 b1; CB 8 b2; CB 8 b3; CB 8 b4; CB 8 b5; CB 8 b6; CB 8 b7] with ([] ++ map (CB 8) [b0; b1; b2; b3; b4; b5; b6; b7]) in SP64 end.
  apply fcb_cb8s_c8s in SP64. cbn [map app] in SP64.
  lazymatch type of SP64 with rw_cells _ _ _ ?l =>
    assert (SPILL : rw_cells bsegs mm2 spq (l ++ [C8 (Z_to_bv 64 f)]))
      by (apply (proj2 (num_rw_cells_app bsegs mm2 spq l [C8 (Z_to_bv 64 f)])); split; [exact SP64| cbn [cells_size csize Nat.add]; change (Z.of_nat 64) with 64%Z; exact SLOT2]) end.
  cbn [app] in SPILL.
  pose proof (fc_bodyc RT AF RTF PMc FDO MST HPDC HNDC Σ K E1 p n m (OKE m) ETP SP16 LOR FRL CRD PIN (conj P8 (conj PA (conj PL PT))) HK HPARSE Σ' fc' mm2 CTX) as BODY.
  unfold fcb_parse_stmt in BODY.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_eq; [| eapply BODY; [| exact FRM']].
  - num_st_eq.
  - unfold FCPINV, fcb_spill. cbn [fcb_at E1 q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0].
    split; [exact SPILL|]. split; [eexists; exact PNS0|]. split; [eexists; exact DG0|]. split; [eexists; exact H0|]. split; [eexists; exact BIG0|].
    split; [eexists; exact SZ'|]. split; [exists v0; exact OUTC|]. split; [exact TXT|]. split; [exact MI2|].
    split; [exact (munch_refl _ mm2)|]. split; [exact (wmono_refl bsegs mm2)| exact ST'].
Qed.

Theorem fcb_closed_gen :
  (forall (E' : fcbenv) (Q : machine_state -> Prop), fcb_ok E' -> fcb_prov E' -> fcb_kf14 E' Q -> fcb_kerr1 E' Q -> fcb_parse_stmt E' Q) ->
  forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc.
Proof.
  intros HPARSE RT AF RTF PMc FDO MST.
  exact (fcb_ok_gen HPARSE RT AF RTF PMc FDO MST (pdcb_closed RT AF RTF PMc FDO MST) (ndcb_closed RT AF RTF PMc FDO MST)).
Qed.
