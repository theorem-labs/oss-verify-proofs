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
  Zqc Zqd Zsl Zqa Zq7 Zqb Zt9 Zta.
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

  Definition lm_body_k (Σ : rts RT) (K : config -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (X lo : Z) (m : mem) : Prop :=
    forall (Σ' : rts RT) (d spq f : Z) xra xt0 xt1 xt2 xa4 xa5 xa7 xt3 xt5 xt6 F' fc' ja0 ja1 jb0 jb1 jb2 jl jh h jz jzi jd bs' n' (mb mm : mem),
      rt_frames RT Σ' = (f, 5%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ' = (rt_credit RT Σ - 1)%Z ->
      frm0 fc' -> ART RT Σ' mb -> wmono asegs m mb ->
      rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 504)%Z] m mb ->
      ((d = 0 \/ d = 16) /\ spq = bv_unsigned sp - 256 - d)%Z ->
      rw_cells asegs mm spq [CB 16 jl] ->
      rw_cells asegs mm (spq + 16) [CB 56 ja0; C8 (Z_to_bv 64 f); CB 40 ja1; C8 (Z_to_bv 64 X); CB 8 jb0; CB 8 jb1; CB 8 jb2] ->
      rw_cells asegs mm (spq + 152) [CB (Z.to_nat d) jh] ->
      rw_cells asegs mm (bv_unsigned sp + -104) (LM_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells asegs mm f [CB 32 h] ->
      rw_cells asegs mm (f / 8 + 2147450884) (mk_CB_cells (repeat 1%nat 63) jz) ->
      rw_cells asegs mm (f / 8 + 2147450956) (mk_CB_cells (repeat 1%nat 63) jzi) ->
      rw_cells asegs mm (f + 32) [CB 2008 jd] ->
      abig_raw RT Σ mm X bs' n' ->
      mem_inv asegs mm -> munch [((spq + 16)%Z, (spq + 152)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] mb mm -> wmono asegs mb mm ->
      stk asegs mm lo spq ->
      (f mod 64 = 0 /\ 0x669000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 255 <= f)
       /\ 0 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 255 <= lo)%Z ->
      ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 256 <= X / 8 + 2147450880))%Z ->
      aevt RT PMc Σ' K
        (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-13)) (Z_to_bv 64 ((X + 496) / 8)) (Z_to_bv 64 (-14))
                 xa4 xa5 (Z_to_bv 64 (-8)) xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) s4 (Z_to_bv 64 0x2af20) s6 s7 s8 (Z_to_bv 64 5) (Z_to_bv 64 2147450880) s11
                 xt3 (Z_to_bv 64 X) xt5 xt6)
            F' (Z_to_bv 64 0xc9a70) fc' None mm (seg_rom asegs)).

  Lemma lm_enter : forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X lo : Z) bs n,
    tp = Z_to_bv 64 0x646eb0 -> frm0 fc ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> (1 <= rt_credit RT Σ)%Z ->
    ART RT Σ m -> mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp) -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + LMA_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    abig_raw RT Σ m X bs n ->
    lm_body_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo m ->
    aevt RT PMc Σ K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 0x2af20) (Z_to_bv 64 5) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc9724) fc None m (seg_rom asegs)).
  Proof using AF RTF FDO MST.
    intros until n. intros ETP FRM FRL CRD ART0 MI ST LOR ROOM TOP SP16 RAW KB.
    pose proof (abig_facts RT AF Σ m X bs n lo ART0 LOR RAW) as (XN0 & XN1 & XN2 & XN3 & XN4).
    destruct RAW as (XA & XL & XN & LEN & ZR & X8 & (g & kg & Hg & G1 & G2)).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    apply (aevt_evt RT AF PMc MST).
    eapply (lm_pro1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m ROOM TOP SP16 ltac:(lia) _); [| exact MI | exact ST | exact (af_client_consts RT AF Σ m ART0)].

    unfold lm_call1_k.
    intros d spq xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ja jb mm REAL MI1 MU1 WM1 ST1.
    destruct REAL as (Hd & Hspq & (jl & LOWc) & SPILL & (jh & HIGHc) & SAVED).
    apply evt_done.
    apply (u8arr_transport asegs [((bv_unsigned sp - 272)%Z, bv_unsigned sp)] m mm X bs) in XA; [| exact MU1 | exact WM1 | cbn [disjoint_from]; split; [lia| exact I]].
    apply (rw_cells_transport asegs [((bv_unsigned sp - 272)%Z, bv_unsigned sp)] m mm) in XN; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]].
    apply (bytes_at_transport asegs [((bv_unsigned sp - 272)%Z, bv_unsigned sp)] m mm) in ZR; [| exact MU1 | cbn [disjoint_from]; split; [lia| exact I]].
    assert (FP1 : fp_ok RT Σ lo [((bv_unsigned sp - 272)%Z, bv_unsigned sp)]) by (constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia| constructor]).
    pose proof (art_of_munch RT AF Σ m mm lo _ ART0 LOR FP1 MU1 WM1) as ART1.
    assert (COK : call_ok RT Σ mm (Z_to_bv 64 spq) lo).
    { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [exact LOR|]. unfold RT_STACK, USTACK_TOP.
      split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
    eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ K 5%nat); [right; right; reflexivity | exact ETP | exact FRL | exact CRD | exact ART1 | exact MI1 | exact COK | exact FRM |].
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
    apply (rw_cells_split_CB asegs m' f [] 2040 jf [] [32; 2008]%nat) in FRD; [| reflexivity]. cbn [mk_CB_cells app] in FRD.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 32 _] _) FRD) as [HDR0 FDAT]. clear FRD.
    cbn [cells_size csize Nat.add] in FDAT. change (Z.of_nat 32) with 32%Z in FDAT.
    apply (rw_cells_split_CB asegs m' f [] 32 _ [] [8;8;8;8]%nat) in HDR0; [| reflexivity]. cbn [app] in HDR0. rewrite app_nil_r in HDR0.
    apply (rw_cells_split_CB asegs m' _ [] 256 js [] [4; 63; 9; 63; 9; 108]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 4 _] _) FRS) as [S0 FRS1]. clear FRS. cbn [cells_size csize Nat.add] in FRS1. change (Z.of_nat 4) with 4%Z in FRS1.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 63 _] _) FRS1) as [SZ FRS2]. clear FRS1. cbn [cells_size csize Nat.add] in FRS2. change (Z.of_nat 63) with 63%Z in FRS2.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 9 _] _) FRS2) as [S1 FRS3]. clear FRS2. cbn [cells_size csize Nat.add] in FRS3. change (Z.of_nat 9) with 9%Z in FRS3.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 63 _] _) FRS3) as [SZI FRS4]. clear FRS3. cbn [cells_size csize Nat.add] in FRS4. change (Z.of_nat 63) with 63%Z in FRS4.
    destruct (proj1 (num_rw_cells_app asegs _ _ [CB 9 _] _) FRS4) as [S2 _]. clear FRS4.
    replace (f / 8 + 2147450880 + 4)%Z with (f / 8 + 2147450884)%Z in SZ, S1, SZI, S2 by lia.
    replace (f / 8 + 2147450884 + 63)%Z with (f / 8 + 2147450947)%Z in S1, SZI, S2 by lia.
    replace (f / 8 + 2147450947 + 9)%Z with (f / 8 + 2147450956)%Z in SZI, S2 by lia.
    replace (f / 8 + 2147450956 + 63)%Z with (f / 8 + 2147451019)%Z in S2 by lia.
    apply (rw_cells_split_CB asegs m' _ [] 4 _ [] (repeat 1%nat 4)) in S0; [| reflexivity]. cbn [app] in S0. rewrite app_nil_r in S0.
    apply (rw_cells_split_CB asegs m' _ [] 63 _ [] (repeat 1%nat 63)) in SZ; [| reflexivity]. cbn [app] in SZ. rewrite app_nil_r in SZ.
    apply (rw_cells_split_CB asegs m' _ [] 9 _ [] (repeat 1%nat 9)) in S1; [| reflexivity]. cbn [app] in S1. rewrite app_nil_r in S1.
    apply (rw_cells_split_CB asegs m' _ [] 63 _ [] (repeat 1%nat 63)) in SZI; [| reflexivity]. cbn [app] in SZI. rewrite app_nil_r in SZI.
    apply (rw_cells_split_CB asegs m' _ [] 9 _ [] (repeat 1%nat 9)) in S2; [| reflexivity]. cbn [app] in S2. rewrite app_nil_r in S2.
    apply (rw_cells_split_CB asegs m' _ [CB 104 ja; C8 (Z_to_bv 64 X)] 24 jb [] [8;8;8]%nat) in SPILL; [| reflexivity]. cbn [mk_CB_cells app] in SPILL.

    pose proof (munch_refl [((spq + 16)%Z, (spq + 152)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] m') as MU2.
    pose proof (wmono_refl asegs m') as WM2.
    destruct NF as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).
    apply (aevt_evt RT AF PMc MST).
    replace (ret_pc (Z_to_bv 64 825244)) with (Z_to_bv 64 825244) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (lm_poison sp gp tp s2 s3 s4 s6 s7 s8 s11 F' fc' X lo d spq f m' (conj Hd Hspq) ROOM TOP NF1 (conj NF2 NF3) NF4 (conj NF5 NF6) ltac:(lia) _);
      [| exact SPILL | exact HDR0 | exact S0 | exact SZ | exact S1 | exact SZI | exact S2 | exact MI' | exact MU2 | exact WM2].
    unfold lm_c34_k.
    intros xra yt0 yt1 yt2 ya4 ya5 ya7 yt3 yt5 yt6 ja0 ja1 jb0 jb1 jb2 h jz jzi mm2 SPILL2 HDR2 SHZ2 SHZI2 MI2 MU3 WM3.
    apply evt_done.
    destruct SEP as (SEP1 & SEP2 & SEP3 & SEP4).
    assert (DJX : forall a k, (X <= a)%Z -> (a + k <= X + 504)%Z -> (0 <= k)%Z ->
              disjoint_from [((spq + 16)%Z, (spq + 152)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] a k)
      by (intros a k A1 A2 A3; cbn [disjoint_from]; repeat split; lia).
    assert (DJS : disjoint_from [((spq + 16)%Z, (spq + 152)%Z); (f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 148)%Z)] (X / 8 + 2147450880) 63)
      by (cbn [disjoint_from]; repeat split; lia).
    assert (HdK : (d = 0 \/ d = 16)%Z) by exact Hd.
    eapply (KB Σ' d spq f); try eassumption;
      [ exact (wmono_trans asegs _ _ _ WM1 WM')
      | split; [exact HdK| exact Hspq]
      | eapply rw_cells_transport; [exact LOWc| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia]
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
