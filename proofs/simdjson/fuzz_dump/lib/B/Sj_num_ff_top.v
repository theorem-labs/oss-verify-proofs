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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_fc_stmt Sj_num_ff_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Definition ffb_body_stmt : Prop :=
  forall (E : ffenv) (m0 : mem), ff_ok E -> (0 < f_FIRST E)%Z ->
    (forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' (f_p E) (8 * (f_n E / 8))) ->
    (forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x28700 10416) ->
    (forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x2b080 640) ->
    forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc ->
    evt bsegs (ff_mid E m0) (FFS E 0xb221c xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (f_FIRST E)) (Z_to_bv 64 (f_LAST E)) xa2 xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

Section FFTAIL.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.

  Lemma ff_exit_post : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> evt bsegs (ff_post E m0) (FFS E 0xb2bf0 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. ff_open INV. ff_env OK.
    do 13 zstep. zstep. zstep. zstep.
    release_frame FR ST (f_SP E).
    apply evt_done. unfold ff_post. do 17 eexists. exists mm.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Lemma ff_d14 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> evt bsegs (ff_post E m0) (FFS E 0xb2d28 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. pose proof INV as INV0. ff_open INV0. ff_env OK.
    zstep. zstep. zstep. zstep.
    let KB := fresh "KB" in if_cases KB; clear KB.
    - zstep. eapply ff_exit_post; [exact INV | assumption].
    - zstep. eapply ff_exit_post; [exact INV | assumption].
  Qed.
End FFTAIL.

Section FFTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis NLA : num_lits_acc RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HFC : fcb_stmt RT PMc.
  Hypothesis BODY : ffb_body_stmt.

  Theorem ffb_walk : ffb_stmt RT PMc.
  Proof using AF NLA FDO MST HFC BODY.
    unfold ffb_stmt.
    intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A FIRST LAST lo p n txt
      ETP FRM FRL FNZ CRD ART0 MI ST LOR ROOM TOP SP16 HIN P8 PA PL PT TXT TMAX HF HL HK.
    set (E := mkFfEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST lo p n txt).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    pose proof (af_live_range RT AF Σ m p n ART0 HIN) as (P0 & PHI & _).
    unfold FFB_STACK, SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK in ROOM.
    assert (OK : ff_ok E).
    { unfold E. constructor; cbn [f_lo f_sp f_txt f_A f_FIRST f_LAST f_p f_n]; unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; try assumption; lia. }
    assert (FPOK : forall Σ0, fp_ok RT Σ0 lo (FF_W E)).
    { intros Σ0. unfold E. cbn [f_sp]. constructor; [left; cbn [fst snd]; unfold USTACK_TOP, STACK_WIN in *; lia| constructor]. }
    pose proof (shzp_live RT AF Σ m lo (FF_W E) p n ART0 LOR (FPOK Σ) HIN P8) as SHPT.
    pose proof (shzp_lits RT AF Σ m lo (FF_W E) 0x28700 10416 NLA ART0 LOR (FPOK Σ) ltac:(left; reflexivity)) as SHL1.
    pose proof (shzp_lits RT AF Σ m lo (FF_W E) 0x2b080 640 NLA ART0 LOR (FPOK Σ) ltac:(right; left; reflexivity)) as SHL2.
    change (8 * (10416 / 8))%Z with 10416%Z in SHL1. change (8 * (640 / 8))%Z with 640%Z in SHL2.
    destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold USTACK_TOP in TOP. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R, LOR, PHI.

    assert (SPLIT : forall Σ0 (m1 : mem) a, ART RT Σ0 m1 -> rt_live RT Σ0 = rt_live RT Σ -> rt_frames RT Σ0 = rt_frames RT Σ -> rt_sp0 RT Σ0 = rt_sp0 RT Σ ->
              aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a -> outside (FF_W E) a).
    { intros Σ0 m1 a HA0 E1 E2 E3 Ha. rewrite <- E1, <- E2 in Ha. pose proof (aclient_split_c RT AF Σ0 m1 _ a HA0 Ha) as SPL. rewrite E3 in SPL.
      unfold E. cbn [f_sp outside]. unfold STACK_WIN in SPL. split; [lia | exact I]. }
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl (FF_W E) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    set (mb := m) in MU at 1, WM at 1, SHPT, SHL1, SHL2.
    unfold E in MU; cbn [f_sp] in MU.
    step.
    carve_frame 128%nat ST.
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jj] =>
      apply (rw_cells_split_CB bsegs m _ [] 128 jj [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 14 step. do 3 zstep. clear G1 G2. nstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : FFINV E mb m1) by
      (unfold FFINV, ff_saved, E; cbn [f_sp f_A f_txt f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7 f_s8 f_s9 f_s10 f_s11 f_ra f_lo];
       split; [eexists _, _, _; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption) end.
    eapply evt_cut.
    { eapply evt_eq; [| eapply (BODY E mb OK ltac:(unfold E; cbn [f_FIRST]; lia) SHPT SHL1 SHL2); [exact INV | exact FRM]].
      unfold E; cbn [f_sp f_gp f_tp f_FIRST f_LAST]; num_st_eq. }
    clear INV. cbv beta. intros ms' [POST | CALL].
    -
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & -> & FRM' & MU' & WM' & MI' & ST').
      unfold E in MU', ST'; cbn [f_sp f_lo f_ra f_gp f_tp f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7 f_s8 f_s9 f_s10 f_s11] in MU', ST' |- *.
      apply evt_done.
      eapply HK; [exact FRM' | | | reflexivity | reflexivity | reflexivity | unfold FFB_CREDIT; lia].
      + split; [exact (art_of_munch RT AF Σ mb m' lo _ ART0 LOR (FPOK Σ) MU' WM')|]. split; [exact MI'|]. split; [exact WM' | exact ST'].
      + intros a Ha. apply MU'. exact (SPLIT Σ m (bv_unsigned a) ART0 eq_refl eq_refl eq_refl Ha).
    -
      destruct CALL as (t0' & t1' & t2' & s0' & s1' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6' & F' & fc' & m1 & -> & FRM1 & INV1 & HLT).
      destruct INV1 as ((jc & v & vf & FR1) & TXT1 & MI1 & MU1 & WM1 & ST1).
      unfold E, ff_saved in FR1, TXT1, MU1, ST1, HLT |- *;
        cbn [f_sp f_lo f_ra f_gp f_tp f_A f_txt f_FIRST f_LAST f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7 f_s8 f_s9 f_s10 f_s11] in FR1, TXT1, MU1, ST1, HLT |- *.
      lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in FR1 end.
      apply num_rw_cells_app in FR1. destruct FR1 as [FR0 FR1]. apply num_rw_cells_app in FR1. destruct FR1 as [VAL SAVED].
      cbn [cells_size csize Nat.add] in VAL, SAVED.
      replace (bv_unsigned sp + -128 + Z.of_nat 8)%Z with (bv_unsigned sp + -120)%Z in * by lia.
      replace (bv_unsigned sp + -120 + Z.of_nat 8)%Z with (bv_unsigned sp + -112)%Z in * by lia.
      assert (ART1 : ART RT Σ m1) by exact (art_of_munch RT AF Σ mb m1 lo _ ART0 LOR (FPOK Σ) MU1 WM1).
      apply evt_done.
      eapply (HFC Σ K) with (A := A) (FIRST := FIRST) (LAST := LAST) (OUT := (bv_unsigned sp + -120)%Z) (lo := lo) (p := p) (n := n) (txt := txt) (v0 := v);
        rewrite ?unsigned_lit by lia; unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in *;
        [ exact ETP | exact FRM1 | exact FRL | exact FNZ | exact CRD | exact ART1 | exact MI1 | exact ST1 | unfold STACK_WIN; lia | lia | lia
        | Z.div_mod_to_equations; lia | exact HIN | exact P8 | lia | lia | lia | exact TXT1 | lia | lia | lia | lia | exact VAL
        | Z.div_mod_to_equations; lia | lia | lia | ].

      intros Σ' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m'' v' FRM'' RA PR OUTC EF EL ES EC.
      rewrite ?unsigned_lit in RA, PR by lia.
      destruct RA as (ART'' & MI'' & WM'' & ST'').
      assert (AG : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -128) x /\ ~ (bv_unsigned sp + -120 <= x < bv_unsigned sp + -120 + 8)%Z) m1 m'')
        by (intros a [H1 H2]; exact (PR a H1 H2)).
      clear VAL ST1.
      rt_transport_with m1 m'' AG WM'' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac | lia]).

      assert (INV2 : FFINV E m'' m'').
      { unfold FFINV, ff_saved, E; cbn [f_sp f_A f_txt f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7 f_s8 f_s9 f_s10 f_s11 f_ra f_lo].
        split.
        { exists jc, v', vf.
          lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) end.
          apply num_rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add].
          replace (bv_unsigned sp + -128 + Z.of_nat 8)%Z with (bv_unsigned sp + -120)%Z by lia.
          apply num_rw_cells_app. split; [exact OUTC|]. cbn [cells_size csize Nat.add].
          replace (bv_unsigned sp + -120 + Z.of_nat 8)%Z with (bv_unsigned sp + -112)%Z by lia. exact SAVED. }
        split; [exact TXT1|]. split; [exact MI''|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact ST'']. }
      apply (aevt_evt RT AF PMc MST). num_ret_pc.
      eapply evt_cut.
      { eapply evt_eq; [| eapply (ff_d14 E OK m''); [exact INV2 | exact FRM'']].
        unfold E; cbn [f_sp f_gp f_tp]; num_st_eq. }
      cbv beta. intros ms3 POST.
      destruct POST as (t0_3 & t1_3 & t2_3 & a0_3 & a1_3 & a2_3 & a3_3 & a4_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & F3 & fc3 & m3 & -> & FRM3 & MU3 & WM3 & MI3 & ST3).
      unfold E in MU3, ST3; cbn [f_sp f_lo f_ra f_gp f_tp f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7 f_s8 f_s9 f_s10 f_s11] in MU3, ST3 |- *.
      assert (LOR' : (rt_sp0 RT Σ' - 8388608 <= lo)%Z) by (rewrite ES; exact LOR).
      apply evt_done.
      eapply HK; [exact FRM3 | | | exact EF | exact EL | exact ES | exact EC].
      + split; [exact (art_of_munch RT AF Σ' m'' m3 lo _ ART'' ltac:(unfold STACK_WIN; exact LOR') (FPOK Σ') MU3 WM3)|]. split; [exact MI3|].
        split; [exact (wmono_trans bsegs _ _ _ WM1 (wmono_trans bsegs _ _ _ WM'' WM3)) | exact ST3].
      + intros a Ha.
        pose proof (SPLIT Σ m (bv_unsigned a) ART0 eq_refl eq_refl eq_refl Ha) as OUTa.
        rewrite (MU3 a OUTa).
        rewrite (PR a); [exact (MU1 a OUTa) | eapply aclient_mono; [exact Ha | auto | auto | lia] |].
        unfold E in OUTa. cbn [f_sp outside] in OUTa. lia.
  Qed.
End FFTOP.

Theorem ffb_of_body : forall RT, art_facts RT -> num_lits_acc RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RT PMc -> ffb_body_stmt -> ffb_stmt RT PMc.
Proof. intros RT AF NLA PMc FDO MST HFC BODY. exact (ffb_walk RT AF NLA PMc FDO MST HFC BODY). Qed.

