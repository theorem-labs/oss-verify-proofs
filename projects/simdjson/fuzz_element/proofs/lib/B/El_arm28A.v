(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA El_arratA El_arm28wA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Arm28.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem arm28_okA : forall W, arm_cpsA RT PMc W 28.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. destruct AL as (ALT & ALS & ALP & ALF & WLO).
  pose proof (conj ALT (conj ALS (conj ALP (conj ALF WLO)))) as AL.
  change (el_arm_pcA 28) with 0xb2680. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  pose proof OKE as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ _ LOW' [HL HT]].
  assert (EU : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (ES96 : bv_unsigned (wz (sp' + -96)) = sp' + -96) by (apply unsigned_lit; ul).
  assert (ES192 : bv_unsigned (wz (sp' + -96 + -96)) = sp' + -96 + -96) by (rewrite unsigned_lit; ul).
  assert (FLO208 : f + 1024 <= sp' - 208) by (clear - FLO LOR SPR; ul).
  assert (SLO : shad f + 128 <= sp' - 208) by (clear - SHT LOR SPR; ul).
  assert (NEED' : lo + 1024 + RT_STACK <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold RT_STACK, EL_DUMP_STACK_A, EL_THROW_STACK_A, ATP_ROOT_STACK_A in *; lia).
  assert (STAT : forall x, client_static x -> x < sp' - 208) by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO LOR SPR; ul).
  assert (NBELOW : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x -> ~ (sp' + -208 <= x < sp')).
  { intros x [H|[H|[H|[H|H]]]] Hin.
    - clear - H Hin. lia.
    - pose proof (STAT _ H). clear - H0 Hin. lia.
    - destruct H as (p & k & Hp & Hr). pose proof (af_live_range RT AF Σ m p k ARTg Hp) as (_ & Y & _). clear - Hr Y WLO Hin ELO LOR SPR. subst. ul.
    - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-. change (fs_size 4) with 1024 in Hr. clear - Hr Hin FLO208. lia.
    - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-.
      replace (shad (f + fs_size 4)) with (shad f + 128) in Hr by (change (fs_size 4) with 1024; unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
      clear - Hr Hin SLO. lia. }

  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (w28_W sp')) by (intros Σx; unfold w28_W; apply (fp_client_stack2 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) [(sp' + 128, sp' + 152)]) by (intros Σx; apply (fp_client_stack1 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul).
  assert (ARTM : forall m', munch (w28_W sp') m m' -> wmono bsegs m m' -> ART RT Σ m') by (intros m' MU WM; exact (lvl_art_munch RT AF E Σ _ m m' ARTg AL (FPW Σ) MU WM)).
  assert (SZN : forall m', munch (w28_W sp') m m' -> wmono bsegs m m' -> shz m' (f + 208) 16).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)). apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64].
    eapply rw_cells_agree_nw; [exact CS|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold el_shadow_armA in Hx. rewrite el_shadowA_size in Hx. unfold w28_W. cbn [outside].
    clear - Hx SLO. repeat split; lia. }
  assert (HWlo : Forall (fun r => ae_lo E <= fst r) (w28_W sp')) by (unfold w28_W; rewrite ELO; constructor; [cbn; clear - LOR SPR; ul|]; constructor; [cbn; clear - LOR SPR; ul| constructor]).
  assert (HWOlo : Forall (fun r => ae_lo E <= fst r) [(sp' + 128, sp' + 152)]) by (rewrite ELO; constructor; [cbn; clear - LOR SPR; ul| constructor]).
  assert (AIM : forall m', munch (w28_W sp') m m' -> AINV_A E m') by (intros m' MU; exact (AINV_A_munch E _ m m' OKE AI MU HWlo)).
  assert (SZD : forall m', munch (w28_W sp') m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) by (intros m' MU WM; exact (lvl_shz_doc E OKE m' (AIM m' MU))).
  assert (SZT : forall m', munch (w28_W sp') m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) by (intros m' MU WM; exact (lvl_shz_tape RT AF E OKE Σ m' (ARTM m' MU WM) AL)).
  assert (SZOa : forall m', ART RT Σ m' -> shz m' (sp' + 128) 24).
  { intros m' HA. apply (lvl_shz_rec RT AF E OKE Σ m' (sp' + 128) 24 HA AL); rewrite ?ELO, ?EHI; [clear - LOR SPR; ul| clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  assert (SZQa : forall m', ART RT Σ m' -> shz m' (sp' + -88) 16).
  { intros m' HA. apply (lvl_shz_rec RT AF E OKE Σ m' (sp' + -88) 16 HA AL); rewrite ?ELO, ?EHI; [clear - LOR SPR; ul| clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  assert (FIN : forall (m' : mem) (fc' : bv 32) (F' : bvmap 5 word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word) (jr' : list byte),
    ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo sp' -> frm0 fc' ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> ~ (sp' + 128 <= bv_unsigned a < sp' + 152) -> m' a = m a) ->
    rw_cells bsegs m' (sp' + 128) [CB 24 jr'] ->
    aevt RT PMc Σ K (MS (mkR (wz 0xb2690) (wz sp') gp (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') a0' a1' a2' a3' a4' a5' a6' a7'
                          (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
                     F' (wz 0xb2690) fc' None m' (seg_rom bsegs))).
  { intros m' fc' F' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' jr' ART' MI' ST' FRM' AGm OUT'.
    apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
    assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' + 128 <= x < sp' + 152)) -> agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H N]. exact (AGm a H N). }
    assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; clear - Hx SPT; ul).
    assert (INF : forall x, f <= x < f + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
    { intros x Hx. right; right; right; left. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
    assert (INSH : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
    { intros x Hx. right; right; right; right. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]. }
    apply (POST false (rt_credit RT Σ) Σ m' fc' F'). unfold arm_postA, artxA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [split; [exact ART'| reflexivity]|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold arm_costA; cbn -[rt_credit]; lia|].
    split; [intros a Ha Ho; apply (AGm a Ha); unfold arm_WA in Ho; cbn [outside app lf_usp lf_S1 lf_F lf_lo] in Ho; clear - Ho; lia|].
    split; [| intros X; discriminate X].
    exists jr', jos. unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [eapply rw_cells_agree_nw; [exact C16|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INS; lia| lia]|].
    split; [eapply rw_cells_agree_nw; [exact C100|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INS; lia| lia]|].
    split; [exact OUT'|].
    split; [eapply rw_cells_agree_nw; [exact CE|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INF; lia| lia]|].
    split; [eapply rw_cells_agree_nw; [exact CO|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INF; lia| lia]|].
    split; [eapply rw_cells_agree_nw; [exact CS|]; apply AG; intros x Hx; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; split; [apply INSH; lia| clear - Hx SLO; lia]|].
    split; [apply (AINV_A_agree E m m' AI); apply AG; intros x Hx; split; [exact (ainv_rng_aclient RT Σ E sp' x AL OKE Hx)| pose proof (ainv_rng_lo E x OKE Hx); clear - H ELO LOR SPR; ul]|].
    split; [apply (el_libA_agree m m' LIB); apply AG; intros x Hx; pose proof (el_lib_rng_static x Hx) as [CSx _]; split; [right; left; exact CSx| pose proof (STAT _ CSx); lia]|].
    split; [apply (libc_nl_agree m m' NL); apply AG; intros x Hx; pose proof (libc_nl_static _ Hx) as CSx; split; [right; left; exact CSx| pose proof (STAT _ CSx); lia]|].
    destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σ m' ART'))|]. apply (ro_cells_agree bsegs m m' _ _ G2). apply AG. intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply client_static_intro; lia| clear - Hx LLO LOR SPR; ul]. }

  apply (aevt_evt RT AF PMc MST).
  eapply (w28_walk1 E OKE _ m F fc sp' f usp idx jr ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3 t4 t5 t6);
    [rewrite ELO; exact STg| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| exact SPA'| exact MIg| exact IDX| exact C16| exact CE| exact FPOS
    | rewrite ELO; clear - FLO; lia| exact C128| exact AIM| intros m' MU WM; exact (shb_cells_of_art RT AF Σ m' (ARTM m' MU WM))| exact SZN| exact SZD| exact SZT| |].
  -
    intros m1 xa3 xa4 j0 j8 j16 j24 j28 MU1 WM1 MI1 ST1 FR1 OUT1 NA. apply evt_done.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    pose proof OUT1 as [_ WRO1]. cbn [cells_size csize Nat.add] in WRO1. change (Z.of_nat 24) with 24 in WRO1.
    pose proof (call_ok_lvl RT E OKE Σ m1 (sp' + -96) AL ST1 ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)) as COK1.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sp' + 128) 16 z8 (ae_lo E) eq_refl eq_refl eq_refl
              ltac:(clear - SPR SPT LLO LOR; ul) ltac:(clear; lia)
              (checked_dst_stack RT AF Σ m1 (wz (sp' + -96)) (sp' + 128) 16 ART1 ltac:(rewrite ELO in WLO; clear - WLO LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(rewrite ES96; lia)
                 (wr_at_sub m1 (sp' + 128) 24 (sp' + 128) 16 WRO1 ltac:(lia) ltac:(lia) ltac:(lia))) ART1 MI1 COK1).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite ES96 in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even 0xb5ac0) by lia.
    assert (AG12 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (sp' + -96) x /\ ~ (sp' + 128 <= x < sp' + 128 + 16)) -> agree_on P m1 m2).
    { intros P HP a Ha. destruct (HP _ Ha) as [H N]. exact (PRES2 a H N). }
    unfold w28_frame in FR1.
    pose proof (rw_cells_merge bsegs m1 (sp' + -96) [] [CB 8 j0; CB 8 j8; CB 8 j16; CB 4 j24; CB 4 j28] _ FR1) as FRj1. cbn [app cells_size csize Nat.add cells_bytes] in FRj1.
    lazymatch type of FRj1 with rw_cells _ _ _ (CB _ ?bs :: _) => set (j32 := bs) in FRj1; clearbody j32 end.
    assert (FR2 : rw_cells bsegs m2 (sp' + -96) (w28_frame [CB 32 j32] s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2690))).
    { unfold w28_frame. cbn [app]. eapply rw_cells_agree_nw; [exact FRj1|]. apply AG12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.
    lazymatch type of OUT1' with rw_cells _ _ _ [CB 16 ?a; CB 4 ?b; CB 4 ?c] =>
      pose proof (rec_copy16 m1 m2 (sp' + 128) [CB 16 a] (CB 4 b) c (repeat z8 16) _ _ _ OUT1' eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(clear - SPT SPR; ul)) as OUT2 end.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_eq; [| eapply (w28_after_set E OKE _ m2 F2 fc sp' (sp' + 128));
      [exact FR2| exact ST2| rewrite ELO; clear - LOR SPR; ul| rewrite EHI; clear - SPR; lia| exact MI2| clear; lia| reflexivity| exact OUT2| clear; lia| rewrite EHI; clear - SPR; lia| exact (SZOa m2 ART2)|]];
      [atp_st_eq|].
    intros m3 MU3 WM3 MI3 ST3 OUT3. rewrite ELO in ST3. replace (sp' + 128 + 24) with (sp' + 152) in MU3 by lia.
    assert (OUTm : rw_cells bsegs m3 (sp' + 128) ([] ++ [CB 16 (repeat z8 16); C4 (wz 17); CB 4 (firstn 4 (skipn 4 (skipn 16 jr)))] ++ [])) by (cbn [app]; exact OUT3).
    pose proof (rw_cells_merge bsegs m3 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
    lazymatch type of OUTj with rw_cells _ _ _ [CB _ ?bs] =>
      apply (FIN m3 fc F2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs (lvl_art_munch RT AF E Σ _ m2 m3 ART2 AL (FPO Σ) MU3 WM3) MI3 ST3 FRM) end; [| exact OUTj].
    intros a Ha Hn. rewrite (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
    + unfold w28_W. cbn [outside]. split; [exact (NBELOW _ Ha)| split; [clear - Hn; lia| exact I]].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia].
    + clear - Hn. lia.
    + cbn [outside]. split; [clear - Hn; lia| exact I].
  -
    intros m1 d' e c xa3 xa4 j0 j28 MU1 WM1 MI1 ST1 FR1 OUT1 TY NXT TILES EN.
    pose proof (ARTM m1 MU1 WM1) as ART1.
    assert (ND1 : rw_cells bsegs m1 (sp' + -88) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
    { assert (X : rw_cells bsegs m1 (sp' + -96) ([CB 8 j0] ++ [C8 (wz (ae_DOC E)); C8 (wz 1)] ++ ([C4 (wz 0); CB 4 j28] ++
                 [C8 s6; C8 (wz (f + 96)); C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb2690)])))
        by (cbn [app]; unfold w28_frame in FR1; cbn [app] in FR1; exact FR1).
      apply Sj_stage1_kit.rw_cells_app in X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X as [X _]. cbn [cells_size csize Nat.add] in X.
      replace (sp' + -96 + Z.of_nat 8) with (sp' + -88) in X by lia. exact X. }
    pose proof OUT1 as OUT1'. apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in OUT1'; [| reflexivity]. cbn [mk_CB_cells app] in OUT1'.
    assert (TRW : forall mx, munch (arrat_W (sp' + -96) (sp' + 128)) m1 mx -> munch (w28_W sp') m mx)
      by (intros mx MU; exact (munch_trans _ _ _ _ MU1 (munch_weaken _ _ _ _ (sub_fp_w28_arrat sp') MU))).

    assert (FRW : forall mx, munch (arrat_W (sp' + -96) (sp' + 128)) m1 mx ->
      rw_cells bsegs mx (sp' + -96) (w28_frame [CB 8 j0; C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j28] s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2690))).
    { intros mx MU. eapply rw_cells_agree_nw; [exact FR1|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold w28_frame in Hx. cbn [cells_size csize Nat.add app] in Hx.
      unfold arrat_W. cbn [outside]. clear - Hx. lia. }
    eapply (arrat_walkN E OKE d' _ m1 F fc 1 e c (sp' + -96) (sp' + -88) (sp' + 128) 0xb5aa4);
      [exact TY| exact NXT| exact TILES| clear; lia| exact EN| exact ND1| clear; lia| clear; lia| clear - SPA'; Z.div_mod_to_equations; lia
      | exact OUT1'| clear; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia
      | intros mx MU WM; exact (AIM mx (TRW mx MU))
      | intros mx MU WM; exact (shb_cells_of_art RT AF Σ mx (ARTM mx (TRW mx MU) (wmono_trans bsegs _ _ _ WM1 WM)))
      | intros mx MU WM; exact (SZD mx (TRW mx MU) (wmono_trans bsegs _ _ _ WM1 WM))
      | intros mx MU WM; exact (SZT mx (TRW mx MU) (wmono_trans bsegs _ _ _ WM1 WM))
      | intros mx MU WM; exact (SZQa mx (ARTM mx (TRW mx MU) (wmono_trans bsegs _ _ _ WM1 WM)))
      | intros mx MU WM; exact (SZOa mx (ARTM mx (TRW mx MU) (wmono_trans bsegs _ _ _ WM1 WM)))
      | exact ST1| rewrite ELO; clear - NEED'; ul| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| exact MI1| clear; lia| reflexivity| |].
    +
      intros m2 x5 x6 x7 xa3' xa4' xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 x28 x29 x30 x31 jj0 MU2 WM2 MI2 ST2 FRA2 OUT2. apply evt_done.
      pose proof (ARTM m2 (TRW m2 MU2) (wmono_trans bsegs _ _ _ WM1 WM2)) as ART2.
      pose proof OUT2 as [_ WRO2]. cbn [cells_size csize Nat.add] in WRO2. change (Z.of_nat 24) with 24 in WRO2.
      pose proof (call_ok_lvl RT E OKE Σ m2 (sp' + -96 + -96) AL ST2 ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)) as COK2.
      eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (sp' + 128) 16 z8 (ae_lo E) eq_refl eq_refl eq_refl
                ltac:(clear - SPR SPT LLO LOR; ul) ltac:(clear; lia)
                (checked_dst_stack RT AF Σ m2 (wz (sp' + -96 + -96)) (sp' + 128) 16 ART2 ltac:(rewrite ELO in WLO; clear - WLO LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(rewrite ES192; lia)
                   (wr_at_sub m2 (sp' + 128) 24 (sp' + 128) 16 WRO2 ltac:(lia) ltac:(lia) ltac:(lia))) ART2 MI2 COK2).
      intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F3 m3 (ART3 & MI3 & WM3 & ST3) PRES3 BY3. rewrite ES192 in ST3, PRES3. change (Z.to_nat 16) with 16%nat in BY3.
      rewrite (ret_pc_even 0xb97ac) by lia.
      assert (AG23 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (sp' + -96 + -96) x /\ ~ (sp' + 128 <= x < sp' + 128 + 16)) -> agree_on P m2 m3).
      { intros P HP a Ha. destruct (HP _ Ha) as [H N]. exact (PRES3 a H N). }
      assert (FRA3 : rw_cells bsegs m3 (sp' + -96 + -96) (arrat_frame (wz 0xb5aa4) (wz idx) (wz (sp' + 128)) (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) s7 (wz (ae_PTR E)) (wz 0) jj0)).
      { eapply rw_cells_agree_nw; [exact FRA2|]. apply AG23. intros x Hx. unfold arrat_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
      pose proof (FRW m2 MU2) as FRW2.
      assert (FRW3 : rw_cells bsegs m3 (sp' + -96) (w28_frame [CB 8 j0; C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j28] s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2690))).
      { eapply rw_cells_agree_nw; [exact FRW2|]. apply AG23. intros x Hx. unfold w28_frame in Hx. cbn [cells_size csize Nat.add app] in Hx. split; [left; clear - Hx SPT SPR; ul| lia]. }
      pose proof OUT2 as OUT2'.
      apply (rw_cells_merge bsegs m2 (sp' + 128) [] [CB 8 (firstn 8 jr); CB 8 (firstn 8 (skipn 8 jr))] _) in OUT2'. cbn [app cells_size csize Nat.add cells_bytes] in OUT2'.
      lazymatch type of OUT2' with rw_cells _ _ _ [CB 16 ?a; CB 4 ?b; CB 4 ?cc] =>
        pose proof (rec_copy16 m2 m3 (sp' + 128) [CB 16 a] (CB 4 b) cc (repeat z8 16) _ _ _ OUT2' eq_refl eq_refl BY3 eq_refl WM3 PRES3 ltac:(lia) ltac:(clear - SPT SPR; ul)) as OUT3 end.
      apply (aevt_evt RT AF PMc MST).
      eapply (arrat_after_set E OKE _ m3 F3 fc (sp' + -96) (sp' + 128) 0xb5aa4);
        [exact FRA3| exact ST3| exact MI3| rewrite ELO; clear - NEED'; ul| exact OUT3| clear; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia
        | exact (SZOa m3 ART3)| clear; lia| reflexivity|].
      intros m4 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 MU4 WM4 MI4 ST4 OUT4. replace (sp' + 128 + 24) with (sp' + 152) in MU4 by lia.
      pose proof (lvl_art_munch RT AF E Σ _ m3 m4 ART3 AL (FPO Σ) MU4 WM4) as ART4.
      assert (FRW4 : rw_cells bsegs m4 (sp' + -96) (w28_frame [CB 8 j0; C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j28] s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2690))).
      { eapply rw_cells_agree_nw; [exact FRW3|]. apply (agree_of_munch _ _ _ _ MU4). intros x Hx. unfold w28_frame in Hx. cbn [cells_size csize Nat.add app] in Hx. cbn [outside]. clear - Hx. lia. }
      unfold w28_frame in FRW4.
      pose proof (rw_cells_merge bsegs m4 (sp' + -96) [] [CB 8 j0; C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j28] _ FRW4) as FRj4. cbn [app cells_size csize Nat.add cells_bytes] in FRj4.
      eapply (w28_epi E OKE true _ m4 F3 fc sp');
        [unfold w28_frame; cbn [app]; exact FRj4| exact ST4| rewrite ELO; clear - LOR SPR; ul| rewrite EHI; clear - SPR; lia| exact MI4| clear; lia| reflexivity|].
      intros ST4'. rewrite ELO in ST4'.
      assert (OUTm : rw_cells bsegs m4 (sp' + 128) ([] ++ [CB 16 (repeat z8 16); C4 (wz 19); CB 4 (firstn 4 (skipn 4 (skipn 8 (skipn 8 jr))))] ++ [])) by (cbn [app]; exact OUT4).
      pose proof (rw_cells_merge bsegs m4 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
      lazymatch type of OUTj with rw_cells _ _ _ [CB _ ?bs] =>
        apply (FIN m4 fc F3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs ART4 MI4 ST4' FRM) end; [| exact OUTj].
      intros a Ha Hn. rewrite (MU4 a), (PRES3 a), (MU2 a), (MU1 a); [reflexivity| | | | |].
      * unfold w28_W. cbn [outside]. split; [exact (NBELOW _ Ha)| split; [clear - Hn; lia| exact I]].
      * unfold arrat_W. cbn [outside]. split; [pose proof (NBELOW _ Ha); clear - H; lia| split; [clear - Hn; lia| exact I]].
      * apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ee He; exact He| intros ee He; exact He| lia].
      * clear - Hn. lia.
      * cbn [outside]. split; [clear - Hn; lia| exact I].
    +
      intros m2 it j' x5 x6 x7 xa0 xa1 xa2 xa3' xa4' xa5 xa6 xa7 x28 x29 x30 x31 MU2 WM2 MI2 ST2 EL IT0 JE OUT2.
      pose proof (ARTM m2 (TRW m2 MU2) (wmono_trans bsegs _ _ _ WM1 WM2)) as ART2.
      pose proof (FRW m2 MU2) as FRW2. unfold w28_frame in FRW2.
      pose proof (rw_cells_merge bsegs m2 (sp' + -96) [] [CB 8 j0; C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j28] _ FRW2) as FRj2. cbn [app cells_size csize Nat.add cells_bytes] in FRj2.
      eapply (w28_epi E OKE true _ m2 F fc sp');
        [unfold w28_frame; cbn [app]; exact FRj2| exact ST2| rewrite ELO; clear - LOR SPR; ul| rewrite EHI; clear - SPR; lia| exact MI2| clear; lia| reflexivity|].
      intros ST2'. rewrite ELO in ST2'.
      assert (OUTm : rw_cells bsegs m2 (sp' + 128) ([] ++ [C8 (wz (ae_DOC E)); C8 (wz it); C4 (wz 0); CB 4 (firstn 4 (skipn 4 (skipn 8 (skipn 8 jr))))] ++ [])) by (cbn [app]; exact OUT2).
      pose proof (rw_cells_merge bsegs m2 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
      lazymatch type of OUTj with rw_cells _ _ _ [CB _ ?bs] =>
        apply (FIN m2 fc F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs ART2 MI2 ST2' FRM) end; [| exact OUTj].
      intros a Ha Hn. rewrite (MU2 a), (MU1 a); [reflexivity| |].
      * unfold w28_W. cbn [outside]. split; [exact (NBELOW _ Ha)| split; [clear - Hn; lia| exact I]].
      * unfold arrat_W. cbn [outside]. split; [pose proof (NBELOW _ Ha); clear - H; lia| split; [clear - Hn; lia| exact I]].
Qed.
End Arm28.
