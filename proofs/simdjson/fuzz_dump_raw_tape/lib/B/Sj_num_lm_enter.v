(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_aframe Sj_num_lm_pro Sj_num_lm_pro2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section LMENTER.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Definition lm_body_k (Σ : rts RT) (K : config -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (X lo : Z) (m : mem) (bs : list byte) (n : Z) : Prop :=
    forall (Σ' : rts RT) (d spq f : Z) xt0 xt2 xa7 xt3 xt4 xt5 xt6 F' fc' ja jb jm jh h jz jzi jd (mb mm : mem),
      rt_frames RT Σ' = (f, 5%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ' = (rt_credit RT Σ - 1)%Z ->
      frm0 fc' -> ART RT Σ' mb -> wmono bsegs m mb ->
      rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 504)%Z] m mb ->
      ((d = 0 \/ d = 16) /\ spq = bv_unsigned sp - 224 - d)%Z ->
      rw_cells bsegs mm spq [CB 40 ja; C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f); CB 32 jb; C8 (Z_to_bv 64 5); CB 24 jm] ->
      rw_cells bsegs mm (spq + 120) [CB (Z.to_nat d) jh] ->
      rw_cells bsegs mm (bv_unsigned sp + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs mm f [CB 32 h] ->
      rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
      rw_cells bsegs mm (f / 8 + 2147450956) [CB 63 jzi] ->
      rw_cells bsegs mm (f + 32) [CB 2008 jd] ->
      abig_raw RT Σ mm X bs n ->
      mem_inv bsegs mm -> munch [(spq, (spq + 120)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] mb mm -> wmono bsegs mb mm ->
      stk bsegs mm lo spq ->
      (f mod 64 = 0 /\ 0x6ce000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 255 <= f)
       /\ 0 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 255 <= lo)%Z ->
      ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 256 <= X / 8 + 2147450880))%Z ->
      aevt RT PMc Σ' K
        (MS (mkR (Z_to_bv 64 0xed0d4) (Z_to_bv 64 spq) gp tp xt0 (Z_to_bv 64 5) xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-14))
                 (Z_to_bv 64 92814) (Z_to_bv 64 970840) (Z_to_bv 64 f) xa7 s2 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 X) (Z_to_bv 64 ((X + 496) / 8)) s6
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 B_P5LARGE) s9 s10 s11 xt3 xt4 xt5 xt6)
            F' (Z_to_bv 64 0xed3a8) fc' None mm (seg_rom bsegs)).

  Lemma lm_enter : forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X lo : Z) bs n,
    tp = Z_to_bv 64 B_TP -> frm0 fc ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> (1 <= rt_credit RT Σ)%Z ->
    ART RT Σ m -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + LMB_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    abig_raw RT Σ m X bs n ->
    lm_body_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo m bs n ->
    aevt RT PMc Σ K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 B_P5LARGE) (Z_to_bv 64 5) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_LM) fc None m (seg_rom bsegs)).
  Proof using AF RTF FDO MST.
    intros until n. intros ETP FRM FRL CRD ART0 MI ST LOR ROOM TOP SP16 RAW KB.
    pose proof (abig_facts RT AF Σ m X bs n lo ART0 LOR RAW) as (XN0 & XN1 & XN2 & XN3 & XN4).
    destruct RAW as (XA & XL & XN & LEN & ZR & X8 & (g & kg & Hg & G1 & G2)).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    apply (aevt_evt RT AF PMc MST).
    eapply (lm_pro1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m ROOM TOP SP16 ltac:(lia) _); [| exact MI | exact ST | exact (af_client_consts RT AF Σ m ART0)].

    unfold lm_call1_k.
    intros d spq xt0 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm REAL MI1 MU1 WM1 ST1.
    destruct REAL as (Hd & Hspq & (jl & LOWc) & YLc & (jm & MIDc) & (jh & HIGHc) & SAVED).
    apply evt_done.
    apply (u8arr_transport bsegs [((bv_unsigned sp - 240)%Z, bv_unsigned sp)] m mm X bs) in XA; [| exact MU1 | exact WM1 | cbn [disjoint_from]; split; [lia| exact I]].
    apply (rw_cells_transport bsegs [((bv_unsigned sp - 240)%Z, bv_unsigned sp)] m mm) in XN; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]].
    apply (bytes_at_transport bsegs [((bv_unsigned sp - 240)%Z, bv_unsigned sp)] m mm) in ZR; [| exact MU1 | cbn [disjoint_from]; split; [lia| exact I]].
    assert (FP1 : fp_ok RT Σ lo [((bv_unsigned sp - 240)%Z, bv_unsigned sp)]) by (constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia| constructor]).
    pose proof (art_of_munch RT AF Σ m mm lo _ ART0 LOR FP1 MU1 WM1) as ART1.
    assert (COK : call_ok RT Σ mm (Z_to_bv 64 spq) lo).
    { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [exact LOR|]. unfold RT_STACK, USTACK_TOP.
      split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
    eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ K 5%nat); [right; right; reflexivity | exact ETP | exact FRL | exact CRD | exact ART1 | exact MI1 | exact COK | intros Efr0; exfalso; rewrite Efr0 in Hg; exact Hg | exact FRM |].
    intros Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' FRM' RA PR W1 W2 EF EL ES EC F0 F64 FTOP.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').

    pose proof (agree_pres _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x) PR (fun x H => H)) as AG.
    unfold LM_SAVED in SAVED.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; cbv beta; aclient_tac).

    assert (MREL : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, (X + 504)%Z)] m m').
    { eapply pres_fp_trans.
      - apply (pres_fp_of_munch _ _ _ _ _ _ _ MU1). intros a Ha _. pose proof (aclient_split_c RT AF Σ m _ a ART0 Ha) as SPL.
        cbn [outside]. split; [lia| exact I].
      - intros a Ha _. apply PR. eapply aclient_mono; [exact Ha| auto| auto| lia]. }

    assert (HinF : In (f, 5%nat) (rt_frames RT Σ')) by (rewrite EF; left; reflexivity).
    pose proof (new_frame_facts RT AF Σ' m' f 5 2040 lo ART' ltac:(rewrite ES; exact LOR) HinF eq_refl eq_refl ltac:(lia)) as NF.
    change (2040 / 8)%Z with 255%Z in NF.
    pose proof (frames_sep RT AF Σ' m' f 5 (rt_frames RT Σ) X 504 ART' EF X8 ltac:(lia) eq_refl ltac:(exists g, kg; split; [exact Hg| lia])) as SEP.
    cbv zeta in SEP. change (fs_size 5) with 2048%Z in SEP. change (2048 / 8)%Z with 256%Z in SEP. change (504 / 8)%Z with 63%Z in SEP.
    change (fs_size 5 - 8)%Z with 2040%Z in W1. change (fs_size 5 / 8)%Z with 256%Z in W2. unfold shad, SHB in W2.
    destruct (wr_at_rw_CB m' f 2040 W1 ltac:(lia)) as [jf FRD]. destruct (wr_at_rw_CB m' _ 256 W2 ltac:(lia)) as [js FRS].
    change (Z.to_nat 2040) with 2040%nat in FRD. change (Z.to_nat 256) with 256%nat in FRS.
    apply (rw_cells_split_CB bsegs m' f [] 2040 jf [] [32; 2008]%nat) in FRD; [| reflexivity]. cbn [mk_CB_cells app] in FRD.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 32 _] _) FRD) as [HDR0 FDAT]. clear FRD.
    cbn [cells_size csize Nat.add] in FDAT. change (Z.of_nat 32) with 32%Z in FDAT.
    apply (rw_cells_split_CB bsegs m' f [] 32 _ [] [8;8;8;8]%nat) in HDR0; [| reflexivity]. cbn [app] in HDR0. rewrite app_nil_r in HDR0.
    apply (rw_cells_split_CB bsegs m' _ [] 256 js [] [4; 63; 9; 72; 108]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 4 _] _) FRS) as [S0 FRS1]. clear FRS. cbn [cells_size csize Nat.add] in FRS1. change (Z.of_nat 4) with 4%Z in FRS1.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 63 _] _) FRS1) as [SZ FRS2]. clear FRS1. cbn [cells_size csize Nat.add] in FRS2. change (Z.of_nat 63) with 63%Z in FRS2.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 9 _] _) FRS2) as [S1 FRS3]. clear FRS2. cbn [cells_size csize Nat.add] in FRS3. change (Z.of_nat 9) with 9%Z in FRS3.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 72 _] _) FRS3) as [SZI _]. clear FRS3.
    replace (f / 8 + 2147450880 + 4)%Z with (f / 8 + 2147450884)%Z in SZ, S1, SZI by lia.
    replace (f / 8 + 2147450884 + 63)%Z with (f / 8 + 2147450947)%Z in S1, SZI by lia.
    replace (f / 8 + 2147450947 + 9)%Z with (f / 8 + 2147450956)%Z in SZI by lia.
    apply (rw_cells_split_CB bsegs m' _ [] 4 _ [] (repeat 1%nat 4)) in S0; [| reflexivity]. cbn [app] in S0. rewrite app_nil_r in S0.
    apply (rw_cells_split_CB bsegs m' _ [] 9 _ [] (repeat 1%nat 9)) in S1; [| reflexivity]. cbn [app] in S1. rewrite app_nil_r in S1.

    apply (rw_cells_split_CB bsegs m' _ [] 88 jl [] [40;8;8;32]%nat) in LOWc; [| reflexivity]. cbn [mk_CB_cells app] in LOWc.
    assert (LOW1 : rw_cells bsegs m' spq (([CB 40 (firstn 40 jl); CB 8 (firstn 8 (skipn 40 jl)); CB 8 (firstn 8 (skipn 8 (skipn 40 jl))); CB 32 (firstn 32 (skipn 8 (skipn 8 (skipn 40 jl))))]
                                           ++ [C8 (Z_to_bv 64 5)]) ++ [CB 24 jm])).
    { apply (proj2 (num_rw_cells_app bsegs _ spq _ _)). split.
      - apply (proj2 (num_rw_cells_app bsegs _ spq _ _)). split; [exact LOWc|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 88) with 88%Z. exact YLc.
      - cbn [app cells_size csize Nat.add]. change (Z.of_nat 96) with 96%Z. exact MIDc. }
    cbn [app] in LOW1. clear LOWc YLc MIDc.

    pose proof (munch_refl [(spq, (spq + 120)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] m') as MU2.
    pose proof (wmono_refl bsegs m') as WM2.
    destruct NF as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).
    apply (aevt_evt RT AF PMc MST).
    replace (ret_pc (Z_to_bv 64 970964)) with (Z_to_bv 64 970964) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (lm_poison sp gp tp s2 s3 s5 s6 s9 s10 s11 F' fc' X lo d spq f m' (conj Hd Hspq) ROOM TOP NF1 (conj NF2 NF3) NF4 (conj NF5 NF6) ltac:(lia) _);
      [| exact LOW1 | exact HDR0 | exact S0 | exact SZ | exact S1 | exact SZI | exact MI' | exact MU2 | exact WM2].
    unfold lm_fa4_k.
    intros yt0 yt2 ya7 yt3 yt4 yt5 yt6 ja jb jm2 h jz jzi mm2 LOW2 HDR2 SHZ2 SHZI2 MI2 MU3 WM3.
    apply evt_done.
    destruct SEP as (SEP1 & SEP2 & SEP3 & SEP4).
    assert (DJX : forall a k, (X <= a)%Z -> (a + k <= X + 504)%Z -> (0 <= k)%Z ->
              disjoint_from [(spq, (spq + 120)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] a k)
      by (intros a k A1 A2 A3; cbn [disjoint_from]; repeat split; lia).
    assert (DJS : disjoint_from [(spq, (spq + 120)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] (X / 8 + 2147450880) 63)
      by (cbn [disjoint_from]; repeat split; lia).
    assert (HdK : (d = 0 \/ d = 16)%Z) by exact Hd.
    eapply (KB Σ' d spq f); try eassumption;
      [ exact (wmono_trans bsegs _ _ _ WM1 WM')
      | split; [exact HdK| exact Hspq]
      | eapply rw_cells_transport; [exact HIGHc| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia]
      | eapply rw_cells_transport; [exact SAVED| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia]
      | eapply rw_cells_transport; [exact FDAT| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia]
      | split; [eapply u8arr_transport; [exact XA| exact MU3| exact WM3| apply DJX; lia]|]; split; [exact XL|];
        split; [eapply rw_cells_transport; [exact XN| exact MU3| exact WM3| cbn [cells_size csize Nat.add]; apply DJX; lia]|]; split; [exact LEN|];
        split; [eapply bytes_at_transport; [exact ZR| exact MU3| rewrite RL; exact DJS]|]; split; [exact X8|]; exists g, kg; split; [exact Hg| lia]
      | eapply stk_transport_disjoint; [exact ST'| exact MU3| exact WM3| cbn [disjoint_from]; repeat split; lia]
      | repeat split; assumption
      | repeat split; assumption ].
  Qed.
End LMENTER.
