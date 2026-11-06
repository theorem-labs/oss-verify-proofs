(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_scanner_get_token H_presp_B.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require StrFun ScanInt Prelim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require H_presp_seg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 AWUb FakeKit HObjK HObjF FsEnvKit H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X H_vfm_GX H_match_shell H_match_A H_match_X H_map_str_to_int H_puri H_pparse_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Section RQ.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis POK : pq_okA FI q lo P st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 5.
  Hypothesis FE0 : FSENV FI m0.
  Variable canary : word.
  Notation F := (qF FI st). Notation FL := (qFL FI st). Notation SF := (qSF FI st).
  Ltac pqokA V := destruct V as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
  Ltac tokA V := destruct V as (ALO & AHI & LENC & AAL & TFS & TBAND & CAPB).

  Ltac chkbQ r APP HS k SHR Hk :=
    let a := reg_val r in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (acc_load mm APP a (proj1 HS APP ltac:(lia)) ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.

Local Notation pq_okA := (H_pparse_seg.pq_okA FI q lo P st).
Local Notation qF := (H_pparse_seg.qF FI st).

Local Notation pscrQ := (H_pparse_seg.pscrQ FI P st).
Local Notation prestQ := (H_pparse_seg.prestQ FI q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pinvQS := (H_pparse_seg.pinvQS FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pregsQ := (H_pparse_seg.pregsQ FI q P st gp tp).
Local Notation loopstQ := (H_pparse_seg.loopstQ FI q P st gp tp F_ fc).
Local Notation exitstQ := (H_pparse_seg.exitstQ FI q P st gp tp F_ fc).
Local Notation prologueQ := (H_pparse_seg.prologueQ FI STACK_MALLOC_1 q lo P st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO FE0).
Local Notation ajcallstQ := (H_pparse_seg.ajcallstQ FI q P st gp tp F_ fc).
Local Notation retstQ := (H_pparse_seg.retstQ FI q P st gp tp F_ fc).
Local Notation reqlstQ := (H_pparse_seg.reqlstQ FI q P st gp tp F_ fc).
Local Notation loopQ := (H_pparse_seg.loopQ FI q lo P st gp tp F_ fc POK).
Local Notation retQ := (H_pparse_seg.retQ FI q P st gp tp F_ fc).
Local Notation epostQ := (H_pparse_seg.epostQ FI q lo st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation pWQ := (H_pparse_seg.pWQ FI q lo st).
Local Notation rframeQ := (H_pparse_seg.rframeQ FI q lo st).
Local Notation exitFQ := (H_pparse_seg.exitFQ FI q lo P st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation exitQ := (H_pparse_seg.exitQ FI q lo P st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation pinvQ_stepSh := (H_pparse_seg.pinvQ_stepSh FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation unpoisonQ := (H_pparse_seg.unpoisonQ FI q lo P st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation rejoinQ := (H_pparse_seg.rejoinQ FI q lo P st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation inP := (H_pparse_seg.inP P).
Local Notation dj_inP := (H_pparse_seg.dj_inP P).
Local Notation pinv_stepP := (H_pparse_seg.pinv_stepP FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation outX := (H_pparse_seg.outX FI).
Local Notation clsX := (H_pparse_seg.clsX FI).
Local Notation dj_inPX := (H_pparse_seg.dj_inPX FI P).
Local Notation pinv_stepX := (H_pparse_seg.pinv_stepX FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation epostQ_mono := (H_pparse_seg.epostQ_mono FI q lo st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation xobj_rframe := (H_pparse_seg.xobj_rframe FI q lo P st m0 POK RF0).
Local Notation eframe_facts := (H_pparse_seg.eframe_facts FI q lo P st m0 POK RF0).
Local Notation elive := (H_pparse_seg.elive FI P st).
Local Notation elive_of := (H_pparse_seg.elive_of FI q lo P st m0 POK RF0).
Local Notation pinv_rf := (H_pparse_seg.pinv_rf FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation inFJ := (H_pparse_seg.inFJ FI st).
Local Notation inW3 := (H_pparse_seg.inW3 FI P st).
Local Notation dj_W3 := (H_pparse_seg.dj_W3 FI P st).
Local Notation app_W3 := (H_pparse_seg.app_W3 FI q lo P st m0 POK RF0).
Local Notation fsw_W3 := (H_pparse_seg.fsw_W3 FI q lo P st m0 POK RF0).
Local Notation out_W3 := (H_pparse_seg.out_W3 FI q lo P st m0 POK RF0).
Local Notation pinv_stepF := (H_pparse_seg.pinv_stepF FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation fj_split := (H_pparse_seg.fj_split FI st).
Local Notation fj_join := (H_pparse_seg.fj_join FI st).
Local Notation txt_okA := (H_pparse_seg.txt_okA FI).
Local Notation pctx := (H_pparse_seg.pctx q lo P canary).
Local Notation clow_stepW := (H_pparse_seg.clow_stepW canary).
Local Notation low_fsW := (H_pparse_seg.low_fsW FI q lo P st POK).
Local Notation pctx_stepF := (H_pparse_seg.pctx_stepF FI q lo P st m0 POK RF0 canary).
Local Notation pctx_stepP := (H_pparse_seg.pctx_stepP FI q lo P st m0 POK RF0 canary).
Local Notation dj_FJER := (H_pparse_seg.dj_FJER FI st).
Local Notation evf_ok := (H_pparse_seg.evf_ok FI q lo P st m0 POK RF0).

  Definition rWS (q' : Z) : list ivl := [(lo, q'); (P + 480 + 8, P + 480 + 16); (q' + 264, q' + 264 + 16); (q' + 260, q' + 260 + 4)]%Z.

  #[using="HC FI P st POK"] Lemma tok_shwQ : forall q' m X n, shz m (sh lo) (sh q) -> q + -400 <= q' <= q + -384 -> q' + 8 <= X -> X + n <= q' + 280 -> 0 <= n -> shw m X n.
  Proof.
    intros q' m X n SHZ QB H1 H2 Hn. pose proof POK as POK'. pqokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    eapply (shw_of_shz m (sh lo) (sh q) X n SHZ).
    - unfold win_ok. split; [exact Hn|]. right. change (2^47) with 140737488355328 in *. lia.
    - unfold sh, SHADOW_OFF. clear - H1 QB LO. Z.div_mod_to_equations. lia.
    - unfold sh, SHADOW_OFF. clear - H2 QB. Z.div_mod_to_equations. lia.
  Qed.

  Definition pscrT (q' : Z) (ty tb tl : word) (m : mem) : Prop :=
    exists j0 j224 j256,
      rw_cells asegs m q' [CB 48 j0; C8 (wz (Z.land (P + 4) 7 + 3)); C8 (wz (Z.land (P + 440) 7 + 3)); C8 (wz (Z.land (P + 448) 7 + 3));
                           C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (qSH (P + 4))); C8 (wz (P + 4)); C8 (wz (P + 8));
                           C8 (wz 18446744073708833343); C8 (wz F); C8 (wz F); C8 (wz (qSH (P + 432))); C8 (wz (P + 432));
                           C8 (wz (qSH (P + 440))); C8 (wz (P + 440)); C8 (wz (F + 64)); C8 (wz METHOD_TAB_A); C8 (wz (qSH (P + 488)));
                           C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32)); C8 (wz 2147450880);
                           CB 24 j224; C8 (wz F); CB 4 j256; C4 ty; C8 tb; C8 tl].
  #[using="Type"] Lemma pscr_split : forall q' m, pscrQ q' m -> exists ty tb tl, pscrT q' ty tb tl m.
  Proof.
    intros q' m (j0 & j224 & j256 & QC). unfold pscrT.
    splitcb QC 25%nat [4; 4; 8; 8]%nat. recell QC 26%nat. recell QC 27%nat. recell QC 28%nat. name_junk QC.
    do 6 eexists. exact QC.
  Qed.
  #[using="Type"] Lemma pscr_join : forall q' ty tb tl m, pscrT q' ty tb tl m -> pscrQ q' m.
  Proof.
    intros q' ty tb tl m (j0 & j224 & j256 & QC). unfold pscrQ.
    pose proof (rw_cells_merge asegs m q' [CB 48 j0; C8 (wz (Z.land (P + 4) 7 + 3)); C8 (wz (Z.land (P + 440) 7 + 3)); C8 (wz (Z.land (P + 448) 7 + 3));
                           C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (qSH (P + 4))); C8 (wz (P + 4)); C8 (wz (P + 8));
                           C8 (wz 18446744073708833343); C8 (wz F); C8 (wz F); C8 (wz (qSH (P + 432))); C8 (wz (P + 432));
                           C8 (wz (qSH (P + 440))); C8 (wz (P + 440)); C8 (wz (F + 64)); C8 (wz METHOD_TAB_A); C8 (wz (qSH (P + 488)));
                           C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32)); C8 (wz 2147450880);
                           CB 24 j224; C8 (wz F)] [CB 4 j256; C4 ty; C8 tb; C8 tl] [] QC) as M.
    cbn [app cells_size csize Nat.add] in M. do 3 eexists. exact M.
  Qed.

  #[using="m0 POK RF0"] Lemma pinv_stepT : forall shd, Z.of_nat (cells_size shd) = 16 -> forall q' m m' (W : list ivl),
    pinvQS shd q' m -> munch ((lo, q' + 280) :: W) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall inP W ->
    stk asegs m' lo q' -> pscrQ q' m' -> pinvQS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & _ & MI & AE & (QB & QAL) & VR) MU WM MI' HW ST' QC'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { unfold qSF, sh, SHADOW_OFF. clear - FLO FHI FSB4. Z.div_mod_to_equations. lia. }
    assert (SH2 : sh (FSB FI) + A0_FS_SHSIZE <= lo).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 FSB5 ACR CLO. Z.div_mod_to_equations. lia. }
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PS.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as PL.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJ : forall X n, (X + n <= P \/ P + 504 <= X) -> (X + n <= lo \/ q' + 280 <= X) -> disjoint_from ((lo, q' + 280) :: W) X n).
    { intros X n HX HY. cbn [disjoint_from]. split; [lia| exact (dj_inP W X n HW HX)]. }
    split; [exact ST'|]. split; [exact QC'|]. split; [exact MI'|].
    split. { apply (asan_env_frame asegs m m' _ AE MU WM). unfold env_safe. constructor; [left; cbn [fst snd]; lia|].
             eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2 & H3). cbn [fst snd] in *. left. lia. }
    split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM| apply DJ; right; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
    split; [exists w0; eapply rw_cells_transport; [exact FH| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PF; lia| left; clear - FHI FSB2 CLO; lia]]|].
    split; [exists jf; eapply rw_cells_transport; [exact FT1| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PF; lia| left; clear - FHI FSB2 CLO; lia]]|].
    split; [eapply rw_cells_transport; [exact FT2| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PF; lia| left; clear - FHI FSB2 CLO; lia]]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MU| exact WM| apply DJ; rewrite HSZ; [clear - PS; lia| left; clear - SH1 SH2; lia]]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PL; lia| left; clear - FLHI FSB2 CLO; lia]]|].
    exists stc. split; [| exact LIVE1].
    apply (rfake_frame FI stc m m' _ RF MU WM). constructor.
    - left. cbn [fst snd]. split; [right; clear - FSB2 CLO; lia| right; clear - SH2; lia].
    - eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2 & H3). cbn [fst snd] in *.
      right; left. apply (lb_mono (fs_live FI st)); [apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact LSUB].
  Qed.

  #[using="st m0 POK RF0"] Lemma pctx_stepT : forall (W : list ivl) q' A len cap cur cur' bs m m',
    pctx A len cap cur bs m -> txt_okA A len cap -> q + -400 <= q' <= q + -384 -> munch ((lo, q' + 280) :: W) m m' -> wmono asegs m m' -> Forall inP W ->
    disjoint_from W (P + 400) 32 ->
    rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur'); C4 (wz 0)] ->
    pctx A len cap cur' bs m'.
  Proof.
    intros W q' A len cap cur cur' bs m m' (_ & MBC & TXT & SHP & SHA & SHSEP & SHF1 & SHF2 & SHZ & SHR & (ev & CLOW) & SHE) TOK QB MU WM HW DJM SC'.
    tokA TOK. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (AW : app_ivs ((lo, q' + 280) :: W)).
    { constructor; [unfold app_iv, SH_HI; cbn [fst snd]; right; clear - CLO ACR; lia|].
      eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 PF1 PF2 B1 B2 B5. lia. }
    unfold pctx.
    split; [exact SC'|].
    split; [eapply rw_cells_transport; [exact MBC| exact MU| exact WM| unfold mbuf_cells; simpl_sizes; cbn [disjoint_from]; split; [left; clear - PHI CLO; lia| unfold mbuf_cells in DJM; simpl_sizes; exact DJM]]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MU| exact WM| cbn [disjoint_from]; split; [left; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - AHI CLO; lia|
              apply dj_inP; [exact HW| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - TFS PF1 PF2; lia]]]|].
    split; [exact (shw_frame _ _ _ _ _ SHP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHA MU AW)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF1 MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF2 MU AW)|].
    assert (FW : Forall (fsw_iv FI) ((lo, q' + 280) :: W)) by (eapply Forall_impl; [| exact AW]; intros iv H; left; exact H).
    split; [exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exists ev; apply (clow_stepW _ ev m m' CLOW MU WM); constructor; [cbn [fst]; clear - CLO ACR; lia|]; eapply Forall_impl; [| exact HW]; intros [x y] (H1 & _); cbn [fst] in *; clear - H1 PLO; lia|].
    exact (shw_frame _ _ _ _ _ SHE MU AW).
  Qed.

  #[using="Type"] Lemma rWS_sub : forall q', lo <= q' -> sub_fp (rWS q') ((lo, q' + 280) :: [(P + 488, P + 496)])%Z.
  Proof. intros q' LQ x Hx. unfold rWS. cbn [outside] in *. destruct Hx as (H1 & H2 & _). repeat split; try exact I; lia. Qed.

  #[using="IC m0 POK RF0"] Lemma sgt_callQ : forall shd, Z.of_nat (cells_size shd) = 16 -> forall (q' A len cap cur : Z) (bs : list byte) (ty tb tl : word) (m : mem)
      (ra' gp' tp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    pinvQS shd q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> 0 <= cur <= len -> pscrT q' ty tb tl m ->
    (forall m' (tlz ty' : Z) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS shd q' m' -> pctx A len cap (cur + tlz) bs m' -> pscrT q' (wz ty') (wz (A + cur)) (wz tlz) m' ->
       munch ((lo, q' + 280) :: [(P + 488, P + 496)])%Z m m' -> wmono asegs m m' ->
       1 <= tlz -> cur + tlz <= len -> 0 <= ty' <= 5 ->
       evt asegs Q (MS (mkR ra' (wz q') gp' tp' y5 y6 y7 s0' s1' (wz 4) y11 y12 y13 y14 y15 y16 y17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' y28 y29 y30 y31)
                       F_ (ret_pc ra') fc None m' (seg_rom asegs))) ->
    (forall m' (r : Z) (tb' tl' : word) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS shd q' m' -> pctx A len cap cur bs m' -> pscrT q' ty tb' tl' m' ->
       munch ((lo, q' + 280) :: [(P + 488, P + 496)])%Z m m' -> wmono asegs m m' ->
       (r = 1 \/ r = 3) ->
       evt asegs Q (MS (mkR ra' (wz q') gp' tp' y5 y6 y7 s0' s1' (wz r) y11 y12 y13 y14 y15 y16 y17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' y28 y29 y30 y31)
                       F_ (ret_pc ra') fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra' (wz q') gp' tp' t0 t1 t2 s0' s1' (wz (P + 480)) (wz (q' + 264)) (wz (q' + 260)) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                    F_ (wz sgt_entryA) fc None m (seg_rom asegs)).
  Proof.
    intros shd HSZ q' A len cap cur bs ty tb tl m ra' gp' tp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 Q INV CTX TOK CR SCR KOK KERR.
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & _).
    pose proof CTX as (SC & MBC & TXT & SHP & SHA & SHSEP & _ & _ & SHZ & SHR & _ & _).
    pose proof TOK as TOK'. tokA TOK'. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (H_pparse_seg.text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct SCR as (j0 & j224 & j256 & QC).
    split_chunk QC 26%nat QLOW TOKC. split_chunk TOKC 1%nat TYC TKC.
    change (q' + Z.of_nat 196) with (q' + 260) in TYC.
    eapply evt_cut.
    { eapply (scanner_get_token_spec_A IC (P + 480) (q' + 264) (q' + 260) (P + 400) A cur len cap lo bs tb tl ty q');
        [exact SC| exact MBC| exact BUF| lia| exact CR| lia| lia| exact TKC| exact TYC| exact AE
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | eapply (tok_shwQ q'); [exact SHZ| exact QB| lia| lia| lia]
        | eapply (tok_shwQ q'); [exact SHZ| exact QB| lia| lia| lia]
        | intros _; apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact SHSEP
        | lia| lia| clear - PAL; Z.div_mod_to_equations; lia
        | lia| lia| clear - PAL; Z.div_mod_to_equations; lia
        | lia| left; lia| clear - QAL; Z.div_mod_to_equations; lia
        | lia| lia| clear - QAL; Z.div_mod_to_equations; lia
        | lia| lia| (intros _; clear - ALO; lia)| lia| right; lia| right; lia| right; lia| clear - TFS PF1 PF2 BL; lia
        | exact ST| exact CLO| lia| unfold A0_RT_STACK in *; lia| exact MI| reflexivity| reflexivity| reflexivity]. }
    intros ms' POST. unfold sgt_post_A in POST.
    destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & cur' & tb' & tl' & tyw' & -> & MUS & WMS & MI' & ST' & AE' & SC' & TKC' & TYC' & RES).
    assert (MUT : munch ((lo, q' + 280) :: [(P + 488, P + 496)])%Z m m') by (eapply munch_weaken; [exact (rWS_sub q' ltac:(clear - LO QB; lia))| exact MUS]).
    assert (QLOW' : rw_cells asegs m' q' [CB 48 j0; C8 (wz (Z.land (P + 4) 7 + 3)); C8 (wz (Z.land (P + 440) 7 + 3)); C8 (wz (Z.land (P + 448) 7 + 3));
                           C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (qSH (P + 4))); C8 (wz (P + 4)); C8 (wz (P + 8));
                           C8 (wz 18446744073708833343); C8 (wz F); C8 (wz F); C8 (wz (qSH (P + 432))); C8 (wz (P + 432));
                           C8 (wz (qSH (P + 440))); C8 (wz (P + 440)); C8 (wz (F + 64)); C8 (wz METHOD_TAB_A); C8 (wz (qSH (P + 488)));
                           C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32)); C8 (wz 2147450880);
                           CB 24 j224; C8 (wz F); CB 4 j256]).
    { eapply rw_cells_transport; [exact QLOW| exact MUS| exact WMS|]. unfold rWS. cbn [disjoint_from]. simpl_sizes. repeat split; try exact I; lia. }
    assert (SCRT : forall ty2 tb2 tl2, rw_cells asegs m' (q' + 260) [C4 ty2] -> rw_cells asegs m' (q' + 264) [C8 tb2; C8 tl2] -> pscrT q' ty2 tb2 tl2 m').
    { intros ty2 tb2 tl2 H1 H2. exists j0, j224, j256.
      replace (q' + 264) with (q' + 260 + 4) in H2 by lia. join_chunks H1 H2 H12.
      replace (q' + 260) with (q' + 260) in H12 by lia. join_chunks QLOW' H12 HA. exact HA. }
    assert (HWc : Forall inP [(P + 488, P + 496)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJM : disjoint_from [(P + 488, P + 496)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
    destruct RES as [(tlz & ty' & -> & -> & -> & -> & TL1 & -> & CL & TY5 & _)|(HRr & -> & ->)].
    - pose proof (SCRT _ _ _ TYC' TKC') as SCR'.
      eapply (KOK m' tlz ty'); [| | exact SCR'| exact MUT| exact WMS| exact TL1| exact CL| exact TY5].
      + exact (pinv_stepT shd HSZ q' m m' _ INV MUT WMS MI' HWc ST' (pscr_join q' _ _ _ m' SCR')).
      + exact (pctx_stepT _ q' A len cap cur (cur + tlz) bs m m' CTX TOK QB MUT WMS HWc DJM SC').
    - pose proof (SCRT _ _ _ TYC' TKC') as SCR'.
      eapply (KERR m' r tb' tl'); [| | exact SCR'| exact MUT| exact WMS| unfold PARSE_INCOMPLETE, PARSE_FAILURE in HRr; lia].
      + exact (pinv_stepT shd HSZ q' m m' _ INV MUT WMS MI' HWc ST' (pscr_join q' _ _ _ m' SCR')).
      + exact (pctx_stepT _ q' A len cap cur cur bs m m' CTX TOK QB MUT WMS HWc DJM SC').
  Qed.

  Definition rWT (q' : Z) : list ivl := [(lo, q' + 280); (P + 488, P + 496)]%Z.
  #[using="IC m0 POK RF0"] Lemma skipQ : forall (k : nat) (q' A len cap cur : Z) (bs : list byte) (ty tb tl : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    len - cur < Z.of_nat k -> pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> 0 <= cur <= len -> pscrT q' ty tb tl m ->
    (forall r cur' m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       (r = 1 \/ r = 3) -> cur <= cur' <= len -> pinvQS qshadowU q' m' -> pctx A len cap cur' bs m' -> munch (rWT q') m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz r) y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    (forall cur1 m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31,
       cur <= cur1 <= len -> pinvQS qshadowU q' m' -> pctx A len cap cur1 bs m' -> munch (rWT q') m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31) F_ (wz 0x8b21c) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31) F_ (wz 0x8b1dc) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until Q; intros HK INV CTX TOK CR SCR KF KT; [lia|].
    unfold H_pparse_seg.pregsQ.
    zstep. zstep. zstep. step.
    eapply (sgt_callQ qshadowU eq_refl q' A len cap cur bs ty tb tl m); [exact INV| exact CTX| exact TOK| exact CR| exact SCR| |].
    -
      intros m' tlz ty' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV1 CTX1 SCR1 MU1 WM1 TL1 CL TY5.
      replace (ret_pc (Z_to_bv 64 0x8b1ec)) with (Z_to_bv 64 0x8b1ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof SCR1 as (j0 & j224 & j256 & QC1).
      step. lit_branch.
      step. rewrite (sx32_lit ty') by lia. zstep. step.
      if_cases K2; zify_cond K2.
      +
        eapply (IH q' A len cap (cur + tlz) bs (wz ty') (wz (A + cur)) (wz tlz)); [lia| exact INV1| exact CTX1| exact TOK| lia| exact SCR1| |].
        * intros r0 cur'0 m'0 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RN CR0 INV0 CTX0 MU0 WM0.
          eapply (KF r0 cur'0 m'0); [exact RN| lia| exact INV0| exact CTX0| exact (munch_trans _ _ _ _ MU1 MU0)| exact (wmono_trans _ _ _ _ WM1 WM0)].
        * intros cur1 m'1 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z25 z28 z29 z30 z31 C1 INV0 CTX0 MU0 WM0.
          eapply (KT cur1 m'1); [lia| exact INV0| exact CTX0| exact (munch_trans _ _ _ _ MU1 MU0)| exact (wmono_trans _ _ _ _ WM1 WM0)].
      +
        pose proof CTX1 as (SC1 & _ & _ & SHP1 & _).
        pose proof POK as POK'. pqokA POK'. clear PLB.
        assert (HACC : acc m' (P + 488 + 8 - 1)) by (apply (proj1 SHP1); lia).
        unfold H_pparse_seg.qSH in *.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          let a := reg_val 10 in
          destruct (AWAuto2.acc_loadw mm (P + 488) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
        destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
        step. step. lit_branch. clear SHR8 HACC.
        pose proof INV1 as (_ & _ & MI1 & _ & (QB & _) & _).
        pose proof (munch_refl [(P + 488, P + 496)]%Z m') as MU2. pose proof (wmono_refl asegs m') as WM2.
        hide MU1. hide WM1.
        step. step. step. zstep. step. fix_lit_store.
        unhide MU1. unhide WM1.
        assert (HWc : Forall inP [(P + 488, P + 496)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
        assert (DJM : disjoint_from [(P + 488, P + 496)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
        pose proof TOK as TOK'. tokA TOK'.
        replace (Z.land (cur + tlz) 18446744073709551615 - Z.land tlz 18446744073709551615) with cur in SC1
          by (change 18446744073709551615 with (Z.ones 64); rewrite !Z.land_ones by lia; rewrite !Z.mod_small by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in CAPB; lia); lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (pinv_stepP qshadowU eq_refl q' m' mm _ INV1 MU2 WM2 MI1 HWc) as INV2;
          pose proof (pctx_stepP _ A len cap (cur + tlz) cur bs m' mm CTX1 TOK MU2 WM2 HWc DJM SC1) as CTX2 end.
        eapply (KT cur _); [lia| exact INV2| exact CTX2| | exact (wmono_trans _ _ _ _ WM1 WM2)].
        eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold rWT. intros x Hx. cbn [outside] in *. destruct Hx as (_ & H2 & _). split; [exact H2| exact I].
    -
      intros m' r tb' tl' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV1 CTX1 SCR1 MU1 WM1 RR.
      replace (ret_pc (Z_to_bv 64 0x8b1ec)) with (Z_to_bv 64 0x8b1ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. if_cases K1; zify_cond K1. 2:{ exfalso. destruct RR as [-> | ->]; revert K1; rewrite ?unsigned_lit by lia; lia. }
      step. step.
      eapply (KF r cur m'); [exact RR| lia| exact INV1| exact CTX1| exact MU1| exact WM1].
  Qed.

  #[using="q lo P m0 POK RF0"] Lemma qouts_shw : forall m, rw_cells asegs m SF qshadowU -> shw m (F + 32) 16 /\ shw m (F + 64) 16 /\ shw m (F + 96) 16.
  Proof.
    intros m SHF. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct eframe_facts as (FLO & FHI & FAL & _). pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    assert (F8 : F mod 8 = 0) by (clear - FAL; Z.div_mod_to_equations; lia).
    unfold qshadowU in SHF.
    change [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)]
      with (shadow_cells [241; 241; 241; 241; 0; 0; 242; 242; 0; 0; 242; 242; 0; 0; 243; 243]) in SHF.
    assert (WK : forall X, F + 32 <= X -> X + 16 <= F + 128 -> win_ok X 16).
    { intros X H1 H2. unfold win_ok. split; [lia|]. clear - H1 H2 FLO FHI B1 B2 B5 ACR. change (2^47) with 140737488355328. lia. }
    split; [| split].
    - split; [| split; [| apply WK; lia]].
      + eapply (accessible_of_chunk m F _ (F + 32) 16 SHF F8); [lia| cbn [length]; lia|].
        intros i Hi H1 H2. cbn [length] in Hi. assert (Ei : i = 4%nat \/ i = 5%nat) by lia. destruct Ei as [-> | ->]; reflexivity.
      + eapply (sh_readable_of_chunk m F _ (F + 32) 16 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
    - split; [| split; [| apply WK; lia]].
      + eapply (accessible_of_chunk m F _ (F + 64) 16 SHF F8); [lia| cbn [length]; lia|].
        intros i Hi H1 H2. cbn [length] in Hi. assert (Ei : i = 8%nat \/ i = 9%nat) by lia. destruct Ei as [-> | ->]; reflexivity.
      + eapply (sh_readable_of_chunk m F _ (F + 64) 16 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
    - split; [| split; [| apply WK; lia]].
      + eapply (accessible_of_chunk m F _ (F + 96) 16 SHF F8); [lia| cbn [length]; lia|].
        intros i Hi H1 H2. cbn [length] in Hi. assert (Ei : i = 12%nat \/ i = 13%nat) by lia. destruct Ei as [-> | ->]; reflexivity.
      + eapply (sh_readable_of_chunk m F _ (F + 96) 16 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
  Qed.

  Definition plocQ (mb ml vb vl ub ul : word) (m : mem) : Prop :=
    exists j1 j2 j3, rw_cells asegs m (F + 32) [C8 mb; C8 ml; CB 16 j1; C8 vb; C8 vl; CB 16 j2; C8 ub; C8 ul; CB 8 j3].
  #[using="Type"] Lemma ploc_split : forall m j, rw_cells asegs m (F + 32) [CB 88 j] -> exists mb ml vb vl ub ul, plocQ mb ml vb vl ub ul m.
  Proof.
    intros m j FR. unfold plocQ.
    splitcb FR 0%nat [8; 8; 16; 8; 8; 16; 8; 8; 8]%nat. recell FR 0%nat. recell FR 1%nat. recell FR 3%nat. recell FR 4%nat. recell FR 6%nat. recell FR 7%nat. name_junk FR.
    do 9 eexists. exact FR.
  Qed.
  #[using="Type"] Lemma ploc_junk : forall mb ml vb vl ub ul m, plocQ mb ml vb vl ub ul m -> exists j, rw_cells asegs m (F + 32) [CB 88 j].
  Proof.
    intros mb ml vb vl ub ul m (j1 & j2 & j3 & HA).
    pose proof (rw_cells_merge asegs m (F + 32) [] [C8 mb; C8 ml; CB 16 j1; C8 vb; C8 vl; CB 16 j2; C8 ub; C8 ul; CB 8 j3] [] HA) as M.
    eexists. exact M.
  Qed.

  #[using="Type"] Lemma ploc_cells : forall mb ml vb vl ub ul m, plocQ mb ml vb vl ub ul m ->
    rw_cells asegs m (F + 32) [C8 mb; C8 ml] /\ rw_cells asegs m (F + 64) [C8 vb; C8 vl] /\ rw_cells asegs m (F + 96) [C8 ub; C8 ul]
    /\ exists j1 j2 j3, rw_cells asegs m (F + 48) [CB 16 j1] /\ rw_cells asegs m (F + 80) [CB 16 j2] /\ rw_cells asegs m (F + 112) [CB 8 j3].
  Proof.
    intros mb ml vb vl ub ul m (j1 & j2 & j3 & HA).
    split_chunk HA 2%nat H1 R1. split_chunk R1 1%nat G1 R2. split_chunk R2 2%nat H2 R3. split_chunk R3 1%nat G2 R4. split_chunk R4 2%nat H3 G3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists j1, j2, j3. split; [exact G1|]. split; [exact G2| exact G3].
  Qed.
  #[using="Type"] Lemma ploc_of_cells : forall mb ml vb vl ub ul m j1 j2 j3,
    rw_cells asegs m (F + 32) [C8 mb; C8 ml] -> rw_cells asegs m (F + 64) [C8 vb; C8 vl] -> rw_cells asegs m (F + 96) [C8 ub; C8 ul] ->
    rw_cells asegs m (F + 48) [CB 16 j1] -> rw_cells asegs m (F + 80) [CB 16 j2] -> rw_cells asegs m (F + 112) [CB 8 j3] ->
    plocQ mb ml vb vl ub ul m.
  Proof.
    intros mb ml vb vl ub ul m j1 j2 j3 H1 H2 H3 G1 G2 G3. exists j1, j2, j3.
    join_chunks H3 G3 R4. join_chunks G2 R4 R3. join_chunks H2 R3 R2. join_chunks G1 R2 R1. join_chunks H1 R1 HA. exact HA.
  Qed.

  Definition rW09 : list ivl := [(P + 480 + 8, P + 480 + 16); (F + 32, F + 32 + 16); (F + 96, F + 96 + 16)]%Z.
  Definition rWRQ : list ivl := [(P + 480 + 8, P + 480 + 16); (F + 32, F + 32 + 16); (F + 96, F + 96 + 16); (F + 64, F + 64 + 16)]%Z.
  #[using="Type"] Lemma rW09_ok : Forall inW3 rW09.
  Proof.
    unfold rW09, H_pparse_seg.inW3, H_pparse_seg.inP, H_pparse_seg.inFJ.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia| constructor].
  Qed.
  #[using="Type"] Lemma rWRQ_ok : Forall inW3 rWRQ.
  Proof.
    unfold rWRQ, H_pparse_seg.inW3, H_pparse_seg.inP, H_pparse_seg.inFJ.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|].
    constructor; [right; left; cbn [fst snd]; lia| constructor].
  Qed.
  #[using="q lo m0 POK RF0"] Lemma rW09_fcls : Forall (fsenv_cls (FSB FI)) rW09.
  Proof.
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). unfold rW09.
    constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia| constructor].
  Qed.
  #[using="q lo m0 POK RF0"] Lemma rWRQ_fcls : Forall (fsenv_cls (FSB FI)) rWRQ.
  Proof.
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). unfold rWRQ.
    constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia| constructor].
  Qed.
  #[using="st m0 POK RF0"] Lemma rWT_fcls : forall q', q + -400 <= q' -> Forall (fsenv_cls (FSB FI)) (rWT q').
  Proof.
    intros q' QB. pose proof POK as POK'. pqokA POK'. destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). unfold rWT.
    constructor; [apply fcls_stack; exact CLO|]. constructor; [apply fcls_in_fs; lia| constructor].
  Qed.

  #[using="q m0 POK RF0"] Lemma low_fsW3 : forall (W : list ivl) q', Forall (fun iv => inP iv \/ inFJ iv) W -> Forall (fun iv : ivl => 0x609000 <= fst iv) ((lo, q') :: FSIV W).
  Proof.
    intros W q' HW. pose proof POK as POK'. pqokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _). destruct eframe_facts as (FLO & _).
    constructor; [cbn [fst]; clear - CLO ACR; lia|]. constructor; [cbn [fst]; exact B1|].
    constructor; [cbn [fst]; unfold sh, SHADOW_OFF; clear - B1; Z.div_mod_to_equations; lia|].
    eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold H_pparse_seg.inP, H_pparse_seg.inFJ in HO. cbn [fst snd] in *.
    destruct HO as [HO|HO]; [clear - HO PLO; lia| clear - HO FLO B1; lia].
  Qed.

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 m0 POK RF0 FCO"] Lemma m09Q : forall (q' A len cap cur : Z) (bs : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> 0 <= cur <= len -> FSENV FI m ->
    (forall m' cur' o1 l1 o2 l2 vb vl y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur' bs m' -> plocQ (wz (A + o1)) (wz l1) vb vl (wz (A + o2)) (wz l2) m' -> FSENV FI m' ->
       cur <= o1 -> 1 <= l1 -> o1 + l1 < o2 -> 1 <= l2 -> o2 + l2 < len -> o2 + l2 < cur' -> cur' <= len ->
       munch ((lo, q) :: FSIV rW09) m m' -> wmono asegs m m' -> fkeep FI rW09 st m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz 4) y11 y12 y13 y14 y15 y16 y17 (wz (F + 32)) y28 y29 y30 y31) F_ (wz 0x8b238) fc None m' (seg_rom asegs))) ->
    (forall m' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       r <> 4 -> 0 <= r <= 5 -> pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> FSENV FI m' ->
       munch ((lo, q) :: FSIV rW09) m m' -> wmono asegs m m' -> fkeep FI rW09 st m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz r) y11 y12 y13 y14 y15 y16 y17 (wz (F + 32)) y28 y29 y30 y31) F_ (wz 0x8b350) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31) F_ (wz 0x8b21c) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur bs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m Q INV CTX TOK CR FE KOK KNO.
    pose proof INV as INV0. destruct INV as (ST & (j0 & j224 & j256 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & SHF & _ & (stc & RF & LIVE1)).
    pose proof CTX as CTX0. destruct CTX as (SC & MBC & TXT & SHP & SHA & SHSEP & SHF09 & SHFRQ & SHZ & SHR & (ev & CLOW) & SHE).
    pose proof POK as POK'. pqokA POK'. pose proof TOK as TOK'. tokA TOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (H_pparse_seg.text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    destruct (qouts_shw m SHF) as (SHO1 & SHOV & SHO2).
    destruct (ploc_split m jf FT1) as (mb & ml & vb & vl & ub & ul & PL0).
    destruct (ploc_cells _ _ _ _ _ _ m PL0) as (O1 & OV & O2 & (j1 & j2 & j3 & J1 & J2 & J3)).
    pose proof (elive_of stc LIVE1) as EL. pose proof EL as (LVF & LVS & LVL & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (NUM : alloc_ceiling <= lo /\ lo <= q' /\ 0x609000 <= FSB FI /\ FSB FI + A0_FS_FRAMES <= F /\ F + 128 <= FSB FI + A0_FS_SIZE
                  /\ FSB FI + A0_FS_FRAMES <= P /\ P + 504 <= FSB FI + A0_FS_SIZE /\ FSB FI + A0_FS_SIZE <= alloc_ceiling
                  /\ (P + 504 <= F \/ F + 128 <= P)) by (clear - CLO LO QB B1 B2 FLO FHI PF1 PF2 PAF; lia).
    hide QAL. hide AL16. hide PAL. hide AAL. hide FAL. hide TFS. hide TBAND. hide PAF. hide PAFL.
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    zstep. step. step. zstep. zstep. step.
    eapply evt_cut.
    { eapply (match_req09A IC FI STACK_MALLOC_0 STACK_MALLOC_1) with (S := P + 480) (MB := P + 400) (A := A) (len := len) (cap := cap) (cur0 := cur)
                           (P1 := F + 32) (P2 := F + 96) (lo := lo) (q := q') (bs := bs) (st := stc) (pw1 := mb) (pw2 := ml) (pw3 := ub) (pw4 := ul);
        [ unhide QAL; apply (evf_ok q' A len cap cur bs stc _ EL QB QAL TOK BL CR);
          constructor; [left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia|]; constructor; [left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia| constructor]
        | clear - LO QB; lia | change (2^47) with 140737488355328 in *; clear - QHI QB; lia | exact RF
        | exact (fs_call_ok_le FI _ _ _ 2%nat (fs_call_ok_push FI st stc tp 4%nat _ FCO LIVE1) ltac:(lia)) | exact FE
        | exact ST | exact MI | exact AE | exact SC | exact MBC | exact BUF
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | intros _; apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact SHSEP | exact SHF09
        | apply (shz_sub _ _ _ _ _ SHZ); [lia| apply sh_mono; clear - QB; lia]
        | intros a Ha; apply SHR; pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia
        | exact O1 | exact SHO1 | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia
        | exact O2 | exact SHO2 | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia
        | left; clear; lia ]. }
    intros ms' POST. unfold match_postXA in POST.
    destruct POST as (r & cur' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MUF & WMF & MI' & FKc & LIVE' & RF' & ST' & AE' & SC' & RR & CR' & ROK & RNOK & XF).
    destruct XF as (pa & pb & pc & pd & O1' & O2' & XOK).
    replace (ret_pc (Z_to_bv 64 0x8b234)) with (Z_to_bv 64 0x8b234) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (KEEPF : forall X cs, rw_cells asegs m X cs -> F + 32 <= X -> X + Z.of_nat (cells_size cs) <= F + 120 ->
                     (X + Z.of_nat (cells_size cs) <= F + 32 \/ F + 48 <= X) -> (X + Z.of_nat (cells_size cs) <= F + 96 \/ F + 112 <= X) -> rw_cells asegs m' X cs).
    { intros X cs HC1 H1 H2 H3 H4. eapply (rw_cells_fkeep FI _ stc); [exact HC1| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia|].
      cbn [disjoint_from]. repeat split; try exact I; clear - NUM H1 H2 H3 H4; lia. }
    pose proof (KEEPF _ _ J1 ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as J1'.
    pose proof (KEEPF _ _ OV ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as OV'.
    pose proof (KEEPF _ _ J2 ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as J2'.
    pose proof (KEEPF _ _ J3 ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as J3'.
    pose proof (ploc_of_cells pa pb vb vl pc pd m' j1 j2 j3 O1' OV' O2' J1' J2' J3') as PL1.
    pose proof (ploc_junk _ _ _ _ _ _ m' PL1) as FT1'.
    pose proof (pinv_stepF qshadowU eq_refl _ q' m m' stc st' INV0 LIVE1 MUF WMF FKc LIVE' RF' ST' MI' AE' rW09_ok FT1') as INV1.
    assert (DJM : disjoint_from rW09 (P + 400) 32) by (unfold rW09; cbn [disjoint_from]; repeat split; try exact I; clear - NUM; lia).
    assert (DJT : disjoint_from rW09 A (cap + 1)) by (unfold rW09; cbn [disjoint_from]; repeat split; try exact I; unhide TFS; clear - NUM TFS ALO; lia).
    assert (CLOW' : clow canary ev m').
    { apply (clow_stepW _ ev m m' CLOW MUF WMF). apply (low_fsW3 rW09 q'). unfold rW09, H_pparse_seg.inP, H_pparse_seg.inFJ.
      constructor; [left; cbn [fst snd]; lia|]. constructor; [right; cbn [fst snd]; lia|]. constructor; [right; cbn [fst snd]; lia| constructor]. }
    pose proof (pctx_stepF _ q' A len cap cur cur' bs m m' stc CTX0 TOK QB RF LIVE1 MUF WMF FKc rW09_ok DJM DJT SC' (ex_intro _ ev CLOW')) as CTX1.
    assert (MUa : munch ((lo, q) :: FSIV rW09) m m').
    { clear - MUF QB. eapply munch_weaken; [| exact MUF]. unfold rW09. sub_fp_solve. }
    assert (FKa : fkeep FI rW09 st m m').
    { eapply (fkeep_weaken FI _ rW09 stc st m m' FKc); [unfold rW09; sub_fp_solve| exact LSUB]. }
    pose proof (fsenv_FSIV FI rW09 lo q m m' FE MUa CLO rW09_fcls) as FEa.
    step. if_cases KB; zify_cond KB.
    -
      assert (cur' = cur) by (apply RNOK; exact KB). subst cur'.
      eapply (KNO m' r); [exact KB| exact RR| exact INV1| exact CTX1| exact FEa| exact MUa| exact WMF| exact FKa].
    - assert (r = 4) by lia. subst r.
      destruct (XOK eq_refl) as (o1 & l1 & o2 & l2 & -> & -> & -> & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7).
      eapply (KOK m' cur' o1 l1 o2 l2 vb vl); try eassumption.
  Qed.

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 m0 POK RF0 FCO"] Lemma mrqQ : forall (q' A len cap cur : Z) (bs : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> 0 <= cur <= len -> FSENV FI m ->
    (forall m' cur' o1 l1 o2 l2 o3 l3 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur' bs m' -> plocQ (wz (A + o1)) (wz l1) (wz (A + o3)) (wz l3) (wz (A + o2)) (wz l2) m' -> FSENV FI m' ->
       cur <= o1 -> 1 <= l1 -> o1 + l1 < o2 -> 1 <= l2 -> o2 + l2 < o3 -> 0 <= l3 -> o3 + l3 < cur' -> cur' <= len ->
       munch ((lo, q) :: FSIV rWRQ) m m' -> wmono asegs m m' -> fkeep FI rWRQ st m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz 4) y11 y12 y13 y14 y15 y16 y17 (wz 4) y28 y29 y30 y31) F_ (wz 0x8b374) fc None m' (seg_rom asegs))) ->
    (forall m' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       r <> 4 -> 0 <= r <= 5 -> pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> FSENV FI m' ->
       munch ((lo, q) :: FSIV rWRQ) m m' -> wmono asegs m m' -> fkeep FI rWRQ st m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz r) y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz (F + 32)) x28 x29 x30 x31) F_ (wz 0x8b350) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur bs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV CTX TOK CR FE KOK KNO.
    pose proof INV as INV0. destruct INV as (ST & (j0 & j224 & j256 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & SHF & _ & (stc & RF & LIVE1)).
    pose proof CTX as CTX0. destruct CTX as (SC & MBC & TXT & SHP & SHA & SHSEP & SHF09 & SHFRQ & SHZ & SHR & (ev & CLOW) & SHE).
    pose proof POK as POK'. pqokA POK'. pose proof TOK as TOK'. tokA TOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (H_pparse_seg.text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    destruct (qouts_shw m SHF) as (SHO1 & SHOV & SHO2).
    destruct (ploc_split m jf FT1) as (mb & ml & vb & vl & ub & ul & PL0).
    destruct (ploc_cells _ _ _ _ _ _ m PL0) as (O1 & OV & O2 & (j1 & j2 & j3 & J1 & J2 & J3)).
    pose proof (elive_of stc LIVE1) as EL. pose proof EL as (LVF & LVS & LVL & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (NUM : alloc_ceiling <= lo /\ lo <= q' /\ 0x609000 <= FSB FI /\ FSB FI + A0_FS_FRAMES <= F /\ F + 128 <= FSB FI + A0_FS_SIZE
                  /\ FSB FI + A0_FS_FRAMES <= P /\ P + 504 <= FSB FI + A0_FS_SIZE /\ FSB FI + A0_FS_SIZE <= alloc_ceiling
                  /\ (P + 504 <= F \/ F + 128 <= P)) by (clear - CLO LO QB B1 B2 FLO FHI PF1 PF2 PAF; lia).
    hide QAL. hide AL16. hide PAL. hide AAL. hide FAL. hide TFS. hide TBAND. hide PAF. hide PAFL.
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    zstep. zstep. zstep. zstep. zstep. step. step.
    eapply evt_cut.
    { eapply (match_reqA IC FI STACK_MALLOC_0 STACK_MALLOC_1) with (S := P + 480) (MB := P + 400) (A := A) (len := len) (cap := cap) (cur0 := cur)
                           (P1 := F + 32) (P2 := F + 96) (P3 := F + 64) (lo := lo) (q := q') (bs := bs) (st := stc) (pw1 := mb) (pw2 := ml) (pw3 := ub) (pw4 := ul) (pw5 := vb) (pw6 := vl);
        [ unhide QAL; apply (evf_ok q' A len cap cur bs stc _ EL QB QAL TOK BL CR);
          constructor; [left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia|]; constructor; [left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia|]; constructor; [left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia| constructor]
        | clear - LO QB; lia | change (2^47) with 140737488355328 in *; clear - QHI QB; lia | exact RF
        | exact (fs_call_ok_le FI _ _ _ 2%nat (fs_call_ok_push FI st stc tp 4%nat _ FCO LIVE1) ltac:(lia)) | exact FE
        | exact ST | exact MI | exact AE | exact SC | exact MBC | exact BUF
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | intros _; apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact SHSEP | exact SHFRQ
        | apply (shz_sub _ _ _ _ _ SHZ); [lia| apply sh_mono; clear - QB; lia]
        | intros a Ha; apply SHR; pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia
        | exact O1 | exact SHO1 | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia
        | exact O2 | exact SHO2 | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia
        | exact OV | exact SHOV | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia
        | left; clear; lia | left; clear; lia | right; clear; lia ]. }
    intros ms' POST. unfold match_postXA in POST.
    destruct POST as (r & cur' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MUF & WMF & MI' & FKc & LIVE' & RF' & ST' & AE' & SC' & RR & CR' & ROK & RNOK & XF).
    destruct XF as (pa & pb & pc & pd & pe & pf & O1' & O2' & OV' & XOK).
    replace (ret_pc (Z_to_bv 64 0x8b36c)) with (Z_to_bv 64 0x8b36c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (KEEPF : forall X cs, rw_cells asegs m X cs -> F + 32 <= X -> X + Z.of_nat (cells_size cs) <= F + 120 ->
                     (X + Z.of_nat (cells_size cs) <= F + 32 \/ F + 48 <= X) -> (X + Z.of_nat (cells_size cs) <= F + 96 \/ F + 112 <= X) ->
                     (X + Z.of_nat (cells_size cs) <= F + 64 \/ F + 80 <= X) -> rw_cells asegs m' X cs).
    { intros X cs HC1 H1 H2 H3 H4 H5. eapply (rw_cells_fkeep FI _ stc); [exact HC1| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia|].
      cbn [disjoint_from]. repeat split; try exact I; clear - NUM H1 H2 H3 H4 H5; lia. }
    pose proof (KEEPF _ _ J1 ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as J1'.
    pose proof (KEEPF _ _ J2 ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as J2'.
    pose proof (KEEPF _ _ J3 ltac:(lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as J3'.
    pose proof (ploc_of_cells pa pb pe pf pc pd m' j1 j2 j3 O1' OV' O2' J1' J2' J3') as PL1.
    pose proof (ploc_junk _ _ _ _ _ _ m' PL1) as FT1'.
    pose proof (pinv_stepF qshadowU eq_refl _ q' m m' stc st' INV0 LIVE1 MUF WMF FKc LIVE' RF' ST' MI' AE' rWRQ_ok FT1') as INV1.
    assert (DJM : disjoint_from rWRQ (P + 400) 32) by (unfold rWRQ; cbn [disjoint_from]; repeat split; try exact I; clear - NUM; lia).
    assert (DJT : disjoint_from rWRQ A (cap + 1)) by (unfold rWRQ; cbn [disjoint_from]; repeat split; try exact I; unhide TFS; clear - NUM TFS ALO; lia).
    assert (CLOW' : clow canary ev m').
    { apply (clow_stepW _ ev m m' CLOW MUF WMF). apply (low_fsW3 rWRQ q'). unfold rWRQ, H_pparse_seg.inP, H_pparse_seg.inFJ.
      constructor; [left; cbn [fst snd]; lia|]. constructor; [right; cbn [fst snd]; lia|]. constructor; [right; cbn [fst snd]; lia|]. constructor; [right; cbn [fst snd]; lia| constructor]. }
    pose proof (pctx_stepF _ q' A len cap cur cur' bs m m' stc CTX0 TOK QB RF LIVE1 MUF WMF FKc rWRQ_ok DJM DJT SC' (ex_intro _ ev CLOW')) as CTX1.
    assert (MUa : munch ((lo, q) :: FSIV rWRQ) m m').
    { clear - MUF QB. eapply munch_weaken; [| exact MUF]. unfold rWRQ. sub_fp_solve. }
    assert (FKa : fkeep FI rWRQ st m m').
    { eapply (fkeep_weaken FI _ rWRQ stc st m m' FKc); [unfold rWRQ; sub_fp_solve| exact LSUB]. }
    pose proof (fsenv_FSIV FI rWRQ lo q m m' FE MUa CLO rWRQ_fcls) as FEa.
    zstep. step. if_cases KB; zify_cond KB.
    -
      assert (cur' = cur) by (apply RNOK; exact KB). subst cur'.
      eapply (KNO m' r); [exact KB| exact RR| exact INV1| exact CTX1| exact FEa| exact MUa| exact WMF| exact FKa].
    - assert (r = 4) by lia. subst r.
      destruct (XOK eq_refl) as (o1 & l1 & o2 & l2 & o3 & l3 & -> & -> & -> & -> & -> & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _).
      eapply (KOK m' cur' o1 l1 o2 l2 o3 l3); try eassumption.
  Qed.

  Variable mws : list word.
  Hypothesis MWL : length mws = 22%nat.
  Hypothesis MID : forall i, 0 <= i < 11 -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id <= 11.
  Definition pstatR (m : mem) : Prop := u64arr asegs m METHOD_TAB_A mws /\ shw m METHOD_TAB_A 176 /\ table_strings_A m mws 11.

  Definition hiER (iv : ivl) : Prop := 0x609000 <= fst iv \/ inER iv.
  #[using="Type"] Lemma dj_hiER : forall (W : list ivl) X n, Forall hiER W -> X + n <= 0x5e7508 -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. unfold hiER, H_pparse_seg.inER in HO. cbn [fst snd] in HO. split; [left; clear - HO HX; lia| exact (IH X n HW' HX)].
  Qed.
  #[using="MWL"] Lemma pstatR_step : forall (W : list ivl) m m', pstatR m -> munch W m m' -> wmono asegs m m' -> Forall (fsw_iv FI) W -> Forall hiER W -> pstatR m'.
  Proof.
    intros W m m' (TB & SHT & TS) MU WM HF HA. pose proof (fsb_ok FI) as (B1 & _).
    split; [| split].
    - eapply u64arr_transport; [exact TB| exact MU| exact WM|]. apply dj_hiER; [exact HA| rewrite MWL; lia].
    - apply (shw_frame_fs FI W m m' _ _ SHT MU HF). left. lia.
    - intros i Hi. destruct (TS i Hi) as (Sx & str & slack & E1 & E2 & E3 & E4 & E5 & E6 & E7).
      exists Sx, str, slack. repeat (split; [assumption|]).
      apply (shw_frame_fs FI W m m' _ _ E7 MU HF). left. lia.
  Qed.
  #[using="q m0 POK RF0"] Lemma hiER_fsW3 : forall (W : list ivl) q', Forall inW3 W -> Forall hiER ((lo, q') :: FSIV W).
  Proof.
    intros W q' HW. pose proof POK as POK'. pqokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct eframe_facts as (FLO & _).
    constructor; [left; cbn [fst]; clear - CLO ACR; lia|]. constructor; [left; cbn [fst]; exact B1|].
    constructor; [left; cbn [fst]; unfold sh, SHADOW_OFF; clear - B1; Z.div_mod_to_equations; lia|].
    eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold H_pparse_seg.inW3, H_pparse_seg.inP, H_pparse_seg.inFJ, H_pparse_seg.outX in HO. unfold hiER. cbn [fst snd] in *.
    destruct HO as [HO|[HO|[HO|HO]]]; [left; clear - HO PLO; lia| left; clear - HO FLO B1; lia| right; exact HO| left; clear - HO; lia].
  Qed.
  #[using="q m0 POK RF0 MWL"] Lemma pstatR_stepF : forall (W : list ivl) q' m m', pstatR m -> munch ((lo, q') :: FSIV W) m m' -> wmono asegs m m' -> Forall inW3 W -> pstatR m'.
  Proof. intros W q' m m' PS MU WM HW. exact (pstatR_step _ m m' PS MU WM (fsw_W3 W q' HW) (hiER_fsW3 W q' HW)). Qed.
  #[using="HC FI q lo st m0 POK RF0 MWL"] Lemma pstatR_stepP : forall (W : list ivl) m m', pstatR m -> munch W m m' -> wmono asegs m m' -> Forall inP W -> pstatR m'.
  Proof.
    intros W m m' PS MU WM HW. pose proof POK as POK'. pqokA POK'. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    apply (pstatR_step W m m' PS MU WM).
    - eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. left. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 PF1 PF2 B1 B2 B5. lia.
    - eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. left. cbn [fst]. clear - H1 PLO. lia.
  Qed.

  #[using="mws MWL"] Lemma u64arr_read4Q : forall m X (xs : list word) (i : Z) w a,
    u64arr asegs m X xs -> nth_error xs (Z.to_nat i) = Some w -> 0 <= i -> a = wa (X + 8 * i) ->
    ov_read_bytes asegs m a 4 = Some (le4 w).
  Proof.
    intros m X xs i w a [Hb _] Hn Hi ->.
    destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
    replace (8 * i) with (Z.of_nat (8 * Z.to_nat i)) by lia.
    rewrite (bytes_at_ov_read asegs m X (u64s xs) (8 * Z.to_nat i) 4 Hb).
    2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite firstn_app. replace (firstn 4 (le8 w)) with (le4 w) by reflexivity.
    rewrite length_le8. replace (4 - 8)%nat with 0%nat by reflexivity. rewrite firstn_O, app_nil_r. reflexivity.
  Qed.

  Definition keepFP (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.
  #[using="mws MWL"] Lemma ploc_keep : forall mb ml vb vl ub ul m m', plocQ mb ml vb vl ub ul m -> keepFP m m' -> plocQ mb ml vb vl ub ul m'.
  Proof. intros mb ml vb vl ub ul m m' (j1 & j2 & j3 & HA) K. exists j1, j2, j3. apply (K _ _ HA). left. simpl_sizes. lia. Qed.
  #[using="mws MWL"] Lemma bytes_skipnQ : forall m a (bs : list byte) k, bytes_at asegs m a bs -> 0 <= k <= Z.of_nat (length bs) ->
    bytes_at asegs m (a + k) (skipn (Z.to_nat k) bs).
  Proof.
    intros m a bs k H Hk. rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite length_firstn, Nat.min_l, Z2Nat.id in H by lia. exact H.
  Qed.

  Definition keepS (q' : Z) (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs -> q' <= X -> X + Z.of_nat (cells_size cs) <= q -> rw_cells asegs m' X cs.
  #[using="m0 POK RF0"] Lemma keepS_of_munch : forall (W : list ivl) q' m m', munch ((lo, q') :: FSIV W) m m' -> wmono asegs m m' -> Forall inW3 W -> q + -400 <= q' -> keepS q' m m'.
  Proof.
    intros W q' m m' MU WM HW QB X cs HC1 H1 H2. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    eapply rw_cells_transport; [exact HC1| exact MU| exact WM|]. cbn [disjoint_from].
    split; [right; exact H1|]. split; [right; clear - H1 B2 CLO LO QB; lia|].
    assert (SH2 : sh (FSB FI) + A0_FS_SHSIZE <= lo) by (unfold sh, SHADOW_OFF; clear - B1 B2 B5 ACR CLO; Z.div_mod_to_equations; lia).
    split; [right; clear - SH2 H1 LO QB; lia|].
    apply (dj_W3 W X _ HW); [right; clear - H1 PHI CLO LO QB; lia| right; destruct eframe_facts as (_ & FHI & _); clear - H1 FHI B2 CLO LO QB; lia| right; clear - H1 CLO LO QB ACR; lia|].
    unfold H_pparse_seg.clsX. left. clear - H1 CLO LO QB. lia.
  Qed.

  #[using="IC STACK_MALLOC_0 m0 POK RF0 FCO MWL"] Lemma map_callQ : forall (q' A len cap cur o1 l1 : Z) (bs : list byte) (m : mem)
      (ra' gp' t0 t1 t2 s0' s1' a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatR m -> FSENV FI m -> 0 <= o1 -> 1 <= l1 -> o1 + l1 <= cap + 1 ->
    (forall m' (r : Z) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> pstatR m' -> FSENV FI m' -> keepFP m m' -> keepS q' m m' -> (r = -1 \/ 0 <= r < 11) ->
       munch ((lo, q) :: FSIV []) m m' -> wmono asegs m m' -> fkeep FI [] st m m' ->
       evt asegs Q (MS (mkR ra' (wz q') gp' tp y5 y6 y7 s0' s1' (wz r) y11 y12 y13 y14 y15 y16 y17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' y28 y29 y30 y31)
                       F_ (ret_pc ra') fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra' (wz q') gp' tp t0 t1 t2 s0' s1' (wz (A + o1)) (wz l1) (wz METHOD_TAB_A) (wz 11) (wz 1) a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                    F_ (wz map_str_to_int_entryA) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur o1 l1 bs m ra' gp' t0 t1 t2 s0' s1' a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 Q INV CTX TOK PS FE O0 L1 OL KK.
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & VR).
    destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & _ & _ & (stc & RF & LIVE1)).
    pose proof CTX as (SC & MBC & TXT & SHP & SHA & _ & _ & _ & _ & _ & (ev & CLOW) & _).
    pose proof PS as (TB & SHT & TS).
    pose proof POK as POK'. pqokA POK'. pose proof TOK as TOK'. tokA TOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (H_pparse_seg.text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    pose proof (bytes_skipnQ m A bs o1 BUF ltac:(lia)) as TOKB.
    assert (TKL : Z.of_nat (length (skipn (Z.to_nat o1) bs)) = cap + 1 - o1) by (rewrite length_skipn; lia).
    eapply evt_cut.
    { eapply (map_str_to_int_spec_A IC FI STACK_MALLOC_0 (A + o1) l1 METHOD_TAB_A 11 1 lo (skipn (Z.to_nat o1) bs) mws stc);
        [ exact TOKB | lia | change (2^43) with 8796093022208; change (2^40) with 1099511627776 in CAPB; lia | lia | lia
        | apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | clear - TFS TKL O0; lia | clear - TBAND TKL O0; lia
        | exact TB | rewrite MWL; reflexivity | lia | lia | lia | reflexivity | exact SHT | exact TS
        | exact ST | exact CLO | unfold A0_RT_STACK; lia | exact QAL | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia
        | exact MI | exact AE | exact RF | exact (fs_call_ok_le FI _ _ _ 1%nat (fs_call_ok_push FI st stc tp 4%nat _ FCO LIVE1) ltac:(lia)) | exact FE | lia
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    intros ms' POST. unfold map_str_to_int_post_A in POST.
    destruct POST as (r & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MU0 & WM' & MI' & FK0 & LIVE' & RF' & ST' & AE' & RES).
    destruct (elive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (KEEP : keepFP m m').
    { intros X cs HC1 HX. eapply (rw_cells_fkeep FI [] stc m m'); [exact HC1| exact FK0| exact WM'| | exact I].
      destruct HX as [HX|HX]; left; [apply (Contracts.lb_sub _ _ _ _ _ LVF); lia| apply (Contracts.lb_sub _ _ _ _ _ LVP); lia]. }
    assert (FT1' : exists j, rw_cells asegs m' (F + 32) [CB 88 j]) by (exists jf; apply (KEEP _ _ FT1); left; simpl_sizes; lia).
    pose proof (pinv_stepF qshadowU eq_refl [] q' m m' stc st' INV LIVE1 MU0 WM' FK0 LIVE' RF' ST' MI' AE' (Forall_nil _) FT1') as INV1.
    assert (SC' : rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]) by (apply (KEEP _ _ SC); right; simpl_sizes; lia).
    assert (CLOW' : clow canary ev m') by (apply (clow_stepW _ ev m m' CLOW MU0 WM'); apply (low_fsW3 [] q'); constructor).
    pose proof (pctx_stepF [] q' A len cap cur cur bs m m' stc CTX TOK QB RF LIVE1 MU0 WM' FK0 (Forall_nil _) I I SC' (ex_intro _ ev CLOW')) as CTX1.
    pose proof (pstatR_stepF [] q' m m' PS MU0 WM' (Forall_nil _)) as PS1.
    assert (MUa : munch ((lo, q) :: FSIV []) m m') by (clear - MU0 QB; eapply munch_weaken; [| exact MU0]; sub_fp_solve).
    assert (FKa : fkeep FI [] st m m') by (eapply (fkeep_weaken FI [] [] stc st m m' FK0); [intros xo Ho; exact Ho| exact LSUB]).
    pose proof (fsenv_FSIV FI [] lo q m m' FE MUa CLO (Forall_nil _)) as FEa.
    pose proof (keepS_of_munch [] q' m m' MU0 WM' (Forall_nil _) ltac:(clear - QB; lia)) as KS.
    eapply (KK m' r); try eassumption.
  Qed.

  #[using="q lo m0 POK RF0"] Lemma ploc_stepP : forall mb ml vb vl ub ul (W : list ivl) m m', plocQ mb ml vb vl ub ul m -> munch W m m' -> wmono asegs m m' -> Forall inP W ->
    plocQ mb ml vb vl ub ul m'.
  Proof.
    intros mb ml vb vl ub ul W m m' (j1 & j2 & j3 & HA) MU WM HW. exists j1, j2, j3.
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PAF & _).
    eapply rw_cells_transport; [exact HA| exact MU| exact WM| apply dj_inP; [exact HW| simpl_sizes; clear - PAF; lia]].
  Qed.

  Definition rWM : list ivl := [(P + 4, P + 8); (P + 440, P + 444)]%Z.
  #[using="mws MWL"] Lemma rWM_inP : Forall inP rWM.
  Proof. unfold rWM, H_pparse_seg.inP. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. Qed.
  #[using="IC STACK_MALLOC_0 m0 POK RF0 FCO MWL MID"] Lemma map09Q : forall (q' A len cap cur o1 l1 o2 l2 meth : Z) (bs : list byte) (vb vl e : word)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatR m -> FSENV FI m ->
    plocQ (wz (A + o1)) (wz l1) vb vl (wz (A + o2)) (wz l2) m -> 0 <= o1 -> 1 <= l1 -> o1 + l1 <= cap + 1 ->
    rw_cells asegs m (P + 440) [C4 e] -> rw_cells asegs m (P + 4) [C4 (wz meth)] ->
    (forall m' e' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> (e' = 501 \/ e' = 400) -> rw_cells asegs m' (P + 440) [C4 (wz e')] -> rw_cells asegs m' (P + 4) [C4 (wz meth)] ->
       munch ((lo, q) :: FSIV rWM) m m' -> wmono asegs m m' -> fkeep FI rWM st m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    (forall m' y1 y5 y6 y7 y10 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> pstatR m' -> FSENV FI m' -> plocQ (wz (A + o1)) (wz l1) vb vl (wz (A + o2)) (wz l2) m' ->
       rw_cells asegs m' (P + 440) [C4 e] -> rw_cells asegs m' (P + 4) [C4 (wz 12)] ->
       munch ((lo, q) :: FSIV rWM) m m' -> wmono asegs m m' -> fkeep FI rWM st m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 (wz 12) (wz l2) y13 y14 y15 y16 y17 (wz (F + 32)) y28 y29 y30 y31) F_ (wz 0x8b2b0) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz 4) x11 x12 x13 x14 x15 x16 x17 (wz (F + 32)) x28 x29 x30 x31) F_ (wz 0x8b238) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur o1 l1 o2 l2 meth bs vb vl e x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV CTX TOK PS FE PL O0 L1 OL EC MC KF KO.
    pose proof (ploc_cells _ _ _ _ _ _ m PL) as (O1 & _ & _ & _).
    pose proof INV as (_ & (j0 & j224 & j256 & QC) & _).
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    step. step. zstep. zstep. step. step.
    clear QC O1.
    eapply (map_callQ q' A len cap cur o1 l1 bs m); [exact INV| exact CTX| exact TOK| exact PS| exact FE| exact O0| exact L1| exact OL|].
    intros m' r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV1 CTX1 PS1 FE1 KEEP _ RES MUa WMa FKa.
    replace (ret_pc (Z_to_bv 64 0x8b250)) with (Z_to_bv 64 0x8b250) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ploc_keep _ _ _ _ _ _ m m' PL KEEP) as PL1.
    assert (EC1 : rw_cells asegs m' (P + 440) [C4 e]) by (apply (KEEP _ _ EC); right; simpl_sizes; lia).
    assert (MC1 : rw_cells asegs m' (P + 4) [C4 (wz meth)]) by (apply (KEEP _ _ MC); right; simpl_sizes; lia).
    pose proof INV1 as (_ & (j0' & j224' & j256' & QC) & MI1 & _).
    unfold H_pparse_seg.qSH in QC.
    pose proof CTX1 as (_ & _ & _ & SHP1 & _).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    assert (MUW : munch ((lo, q) :: FSIV rWM) m m') by (clear - MUa; eapply munch_weaken; [| exact MUa]; unfold rWM; sub_fp_solve).
    assert (FKW : fkeep FI rWM st m m') by (eapply (fkeep_weaken FI [] rWM st st m m' FKa); [intros xo Ho; exact I| intros g Hg; exact Hg]).
    clear MUa FKa KEEP PL EC MC INV CTX PS FE.
    step. if_cases KB; zify_cond KB.
    -
      assert (r = -1) by (destruct RES as [RES|RES]; [exact RES| exfalso; change 18446744073709551615 with (Z.ones 64) in KB; rewrite Z.land_ones in KB by lia; rewrite Z.mod_small in KB by lia; lia]).
      subst r. clear KB RES.
      assert (HACC : acc m' (P + 440 + 8 - 1)) by (apply (proj1 SHP1); lia).
      pose proof (munch_refl [(P + 440, P + 444)]%Z m') as MU2. pose proof (wmono_refl asegs m') as WM2.
      hide MUW. hide WMa.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 10 in
        destruct (AWAuto2.acc_loadw mm (P + 440) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR8 HACC.
      step. clear QC. hide MC1.
      zstep. step. step. fix_lit_store. zstep.
      unhide MC1. unhide MUW. unhide WMa.
      assert (HWc : Forall inP [(P + 440, P + 444)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
      assert (DJM : disjoint_from [(P + 440, P + 444)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
      assert (MC2 : rw_cells asegs m1 (P + 4) [C4 (wz meth)]) by (eapply rw_cells_transport; [exact MC1| exact MU2| exact WM2| cbn [disjoint_from]; simpl_sizes; split; [lia| exact I]]).
      assert (SC2 : rw_cells asegs m1 (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)])
        by (eapply rw_cells_transport; [exact (proj1 CTX1)| exact MU2| exact WM2| cbn [disjoint_from]; simpl_sizes; split; [lia| exact I]]).
      pose proof (pinv_stepP qshadowU eq_refl q' m' m1 _ INV1 MU2 WM2 MI1 HWc) as INV2.
      pose proof (pctx_stepP _ A len cap cur cur bs m' m1 CTX1 TOK MU2 WM2 HWc DJM SC2) as CTX2.
      destruct (pinv_rf _ q' m' INV1) as (stc1 & RF1 & LIVE1').
      eapply (KF m1 501); [exact INV2| exact CTX2| left; reflexivity| exact EC1| exact MC2| | exact (wmono_trans _ _ _ _ WMa WM2)|].
      + eapply munch_trans; [exact MUW|]. eapply munch_weaken; [| exact MU2]. unfold rWM. sub_fp_solve.
      + eapply fkeep_trans; [exact FKW|]. eapply (fkeep_of_munch FI rWM _ st stc1 m' m' _ RF1); [intros g Hg; rewrite LIVE1'; right; exact Hg| exact MU2|].
        unfold rWM. constructor; [| constructor]. left. cbn [fst snd inside]. clear. lia.
    -
      assert (RR : 0 <= r < 11) by (destruct RES as [RES|RES]; [exfalso; subst r; revert KB; change (Z.land (-1) 18446744073709551615) with 18446744073709551615; lia| exact RES]).
      clear KB RES.
      destruct (MID r RR) as (id & HN & IDR).
      pose proof PS1 as (TB1 & SHT1 & _).
      assert (HACCT : acc m' (METHOD_TAB_A + 16 * r + 8 + 8 - 1)) by (apply (proj1 SHT1); lia).
      zstep. step. ubr. zstep.
      replace (Z.shiftl r 4) with (16 * r) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      step. step. ubr.
      zstep. step. zstep. zstep. zstep. step. zstep.
      replace (Z.shiftl r 4) with (16 * r) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (Z.land (718272 + 16 * r + 8) 18446744073709551615) with (718272 + 16 * r + 8)
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 11 in
        destruct (AWAuto2.acc_loadw mm (METHOD_TAB_A + 16 * r + 8) 8 a ltac:(lia) ltac:(clear; Z.div_mod_to_equations; lia) ltac:(lia) HACCT ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR8 HACCT.
      pose proof (u64arr_read4Q m' METHOD_TAB_A mws (2 * r + 1) (wz id) (Z_to_bv 64 (718272 + 16 * r + 8)) TB1 HN ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. rewrite (sx32_lit id) by lia. clear RD.
      step. if_cases K0; zify_cond K0.
      +
        assert (HACC : acc m' (P + 440 + 8 - 1)) by (apply (proj1 SHP1); lia).
        pose proof (munch_refl [(P + 440, P + 444)]%Z m') as MU2. pose proof (wmono_refl asegs m') as WM2.
        hide MUW. hide WMa.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          let a := reg_val 10 in
          destruct (AWAuto2.acc_loadw mm (P + 440) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
        destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
        step. step. lit_branch. clear SHR8 HACC.
        step. clear QC. hide MC1.
        zstep. step. step. fix_lit_store. zstep.
        unhide MC1. unhide MUW. unhide WMa.
        assert (HWc : Forall inP [(P + 440, P + 444)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
        assert (DJM : disjoint_from [(P + 440, P + 444)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
        assert (MC2 : rw_cells asegs m1 (P + 4) [C4 (wz meth)]) by (eapply rw_cells_transport; [exact MC1| exact MU2| exact WM2| cbn [disjoint_from]; simpl_sizes; split; [lia| exact I]]).
        assert (SC2 : rw_cells asegs m1 (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)])
          by (eapply rw_cells_transport; [exact (proj1 CTX1)| exact MU2| exact WM2| cbn [disjoint_from]; simpl_sizes; split; [lia| exact I]]).
        pose proof (pinv_stepP qshadowU eq_refl q' m' m1 _ INV1 MU2 WM2 MI1 HWc) as INV2.
        pose proof (pctx_stepP _ A len cap cur cur bs m' m1 CTX1 TOK MU2 WM2 HWc DJM SC2) as CTX2.
        destruct (pinv_rf _ q' m' INV1) as (stc1 & RF1 & LIVE1').
        eapply (KF m1 400); [exact INV2| exact CTX2| right; reflexivity| exact EC1| exact MC2| | exact (wmono_trans _ _ _ _ WMa WM2)|].
        * eapply munch_trans; [exact MUW|]. eapply munch_weaken; [| exact MU2]. unfold rWM. sub_fp_solve.
        * eapply fkeep_trans; [exact FKW|]. eapply (fkeep_of_munch FI rWM _ st stc1 m' m' _ RF1); [intros g Hg; rewrite LIVE1'; right; exact Hg| exact MU2|].
          unfold rWM. constructor; [| constructor]. left. cbn [fst snd inside]. clear. lia.
      +
        assert (id = 2) by lia. subst id.
        assert (HACC : acc m' (P + 4 + 4 - 1)) by (apply (proj1 SHP1); lia).
        pose proof (munch_refl [(P + 4, P + 8)]%Z m') as MU2. pose proof (wmono_refl asegs m') as WM2.
        pose proof (ploc_cells _ _ _ _ _ _ m' PL1) as (_ & _ & O2c & _).
        hide MUW. hide WMa.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          let a := reg_val 10 in
          destruct (AWAuto2.acc_loadw mm (P + 4) 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
        destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
        step. step. lit_branch. clear SHR8 HACC.
        step. step. clear QC O2c. hide EC1.
        zstep. step. fix_lit_store.
        unhide EC1. unhide MUW. unhide WMa.
        assert (HWc : Forall inP [(P + 4, P + 8)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
        assert (DJM : disjoint_from [(P + 4, P + 8)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
        assert (EC2 : rw_cells asegs m1 (P + 440) [C4 e]) by (eapply rw_cells_transport; [exact EC1| exact MU2| exact WM2| cbn [disjoint_from]; simpl_sizes; split; [lia| exact I]]).
        assert (SC2 : rw_cells asegs m1 (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)])
          by (eapply rw_cells_transport; [exact (proj1 CTX1)| exact MU2| exact WM2| cbn [disjoint_from]; simpl_sizes; split; [lia| exact I]]).
        pose proof (pinv_stepP qshadowU eq_refl q' m' m1 _ INV1 MU2 WM2 MI1 HWc) as INV2.
        pose proof (pctx_stepP _ A len cap cur cur bs m' m1 CTX1 TOK MU2 WM2 HWc DJM SC2) as CTX2.
        pose proof (pstatR_stepP _ m' m1 PS1 MU2 WM2 HWc) as PS2.
        pose proof (ploc_stepP _ _ _ _ _ _ _ m' m1 PL1 MU2 WM2 HWc) as PL2.
        destruct (pinv_rf _ q' m' INV1) as (stc1 & RF1 & LIVE1').
        assert (FE2 : FSENV FI m1).
        { refine (fsenv_munch FI _ m' m1 FE1 MU2 _). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
          constructor; [apply fcls_in_fs; lia| constructor]. }
        eapply (KO m1); [exact INV2| exact CTX2| exact PS2| exact FE2| exact PL2| exact EC2| exact MC1| | exact (wmono_trans _ _ _ _ WMa WM2)|].
        * eapply munch_trans; [exact MUW|]. eapply munch_weaken; [| exact MU2]. unfold rWM. sub_fp_solve.
        * eapply fkeep_trans; [exact FKW|]. eapply (fkeep_of_munch FI rWM _ st stc1 m' m' _ RF1); [intros g Hg; rewrite LIVE1'; right; exact Hg| exact MU2|].
          unfold rWM. constructor; [| constructor]. left. cbn [fst snd inside]. clear. lia.
  Qed.

  #[using="mws MWL"] Lemma dj_inFJ : forall (W : list ivl) X n, Forall inFJ W -> (X + n <= F + 32 \/ F + 120 <= X) -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? (H1 & H2 & H3) HW']; subst. cbn [fst snd] in *. split; [lia| exact (IH X n HW' HX)].
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma pinv_stepJ : forall shd, Z.of_nat (cells_size shd) = 16 -> forall q' m m' (W : list ivl),
    pinvQS shd q' m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall inFJ W ->
    (exists j, rw_cells asegs m' (F + 32) [CB 88 j]) -> pinvQS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & (j0 & j224 & j256 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' HW FT1'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & _ & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (SH2 : FSB FI + A0_FS_SIZE <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= FSB FI).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 FSB5 ACR. Z.div_mod_to_equations. lia. }
    pose proof (elive_of stc LIVE1) as (LVF & _).
    assert (DJ : forall X n, (X + n <= F + 32 \/ F + 120 <= X) -> disjoint_from W X n) by (intros X n HX; exact (dj_inFJ W X n HW HX)).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; right; clear - FHI FSB2 CLO LO QB; lia]|].
    split; [exists j0, j224, j256; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; right; simpl_sizes; clear - FHI FSB2 CLO LO QB; lia]|].
    split; [exact MI'|].
    split. { apply (asan_env_frame asegs m m' W AE MU WM). unfold env_safe. eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2 & H3). cbn [fst snd] in *. left. clear - H1 FLO FSB1. lia. }
    split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM| apply DJ; right; clear - FHI FSB2 CLO LO QB; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MU| exact WM| apply DJ; right; simpl_sizes; clear - FHI FSB2 CLO LO QB; lia]|].
    split; [exists w0; eapply rw_cells_transport; [exact FH| exact MU| exact WM| apply DJ; simpl_sizes; left; clear; lia]|].
    split; [exact FT1'|].
    split; [eapply rw_cells_transport; [exact FT2| exact MU| exact WM| apply DJ; simpl_sizes; right; clear; lia]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MU| exact WM| apply DJ; rewrite HSZ; clear - SHF1 SHF2 SH2 FLO FHI; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| apply DJ; simpl_sizes; left; clear - FLHI FLO; lia]|].
    exists stc. split; [| exact LIVE1].
    apply (rfake_frame FI stc m m' W RF MU WM). eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2 & H3). cbn [fst snd] in *.
    right; left. apply (Contracts.lb_sub _ _ _ _ _ LVF); lia.
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma pctx_stepJ : forall (W : list ivl) A len cap cur bs m m',
    pctx A len cap cur bs m -> txt_okA A len cap -> munch W m m' -> wmono asegs m m' -> Forall inFJ W -> pctx A len cap cur bs m'.
  Proof.
    intros W A len cap cur bs m m' (SC & MBC & TXT & SHP & SHA & SHSEP & SHF1' & SHF2' & SHZ & SHR & (ev & CLOW) & SHE) TOK MU WM HW.
    tokA TOK. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _ & PF1 & PF2).
    assert (AW : app_ivs W).
    { eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 FLO FHI B1 B2 B5. lia. }
    assert (DJ : forall X n, (X + n <= F + 32 \/ F + 120 <= X) -> disjoint_from W X n) by (intros X n HX; exact (dj_inFJ W X n HW HX)).
    unfold H_pparse_seg.pctx.
    split; [eapply rw_cells_transport; [exact SC| exact MU| exact WM| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MU| exact WM| apply DJ; unfold mbuf_cells; simpl_sizes; clear - PAF; lia]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MU| exact WM| apply DJ; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - TFS FLO FHI; lia]|].
    split; [exact (shw_frame _ _ _ _ _ SHP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHA MU AW)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF1' MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF2' MU AW)|].
    assert (FW : Forall (fsw_iv FI) W) by (eapply Forall_impl; [| exact AW]; intros iv H; left; exact H).
    split; [exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exists ev; apply (clow_stepW W ev m m' CLOW MU WM); eapply Forall_impl; [| exact HW]; intros [x y] (H1 & _); cbn [fst] in *; clear - H1 FLO B1; lia|].
    exact (shw_frame _ _ _ _ _ SHE MU AW).
  Qed.
  #[using="q lo P m0 POK RF0 MWL"] Lemma pstatR_stepJ : forall (W : list ivl) m m', pstatR m -> munch W m m' -> wmono asegs m m' -> Forall inFJ W -> pstatR m'.
  Proof.
    intros W m m' PS MU WM HW. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct eframe_facts as (FLO & FHI & _).
    apply (pstatR_step W m m' PS MU WM).
    - eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. left. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 FLO FHI B1 B2 B5. lia.
    - eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. left. cbn [fst]. clear - H1 FLO B1. lia.
  Qed.

  Definition rWU : list ivl := [(F + 96, F + 112)]%Z.
  #[using="mws MWL"] Lemma rWU_inFJ : Forall inFJ rWU.
  Proof. unfold rWU, H_pparse_seg.inFJ. constructor; [cbn [fst snd]; lia| constructor]. Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma slash1Q : forall (k : nat) (q' A len cap cur o l : Z) (bs : list byte) (mb ml vb vl : word)
      x1 x5 x6 x7 x11 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    l < Z.of_nat k -> pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> plocQ mb ml vb vl (wz (A + o)) (wz l) m ->
    0 <= o -> 2 <= l -> o + l <= cap + 1 ->
    (forall m' o' l' y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> plocQ mb ml vb vl (wz (A + o')) (wz l') m' ->
       o' + l' = o + l -> o <= o' -> 1 <= l' -> munch rWU m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 (wz l') y12 y13 y14 y15 y16 y17 (wz (F + 32)) y28 y29 y30 y31) F_ (wz 0x8b610) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz (A + o)) x11 (wz l) (wz (A + o + 1)) x14 x15 x16 x17 (wz (F + 32)) x28 x29 x30 x31) F_ (wz 0x8b2bc) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until Q; intros HK INV CTX TOK PL O0 L2 OL KK; [lia|].
    pose proof CTX as (_ & _ & TXT & _ & SHA & _).
    pose proof TOK as TOK'. tokA TOK'. pose proof POK as POK'. pqokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (H_pparse_seg.text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    assert (HB0 : exists b, nth_error bs (Z.to_nat o) = Some b) by (destruct (nth_error bs (Z.to_nat o)) as [b|] eqn:E; [exists b; reflexivity| apply nth_error_None in E; lia]).
    assert (HB1 : exists b, nth_error bs (Z.to_nat (o + 1)) = Some b) by (destruct (nth_error bs (Z.to_nat (o + 1))) as [b|] eqn:E; [exists b; reflexivity| apply nth_error_None in E; lia]).
    destruct HB0 as (b0 & Hb0). destruct HB1 as (b1 & Hb1).
    pose proof (P0.H_presp_A.byte_range b0) as BR0. pose proof (P0.H_presp_A.byte_range b1) as BR1.
    pose proof (u8ro_read asegs m A bs o b0 (Z_to_bv 64 (A + o)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
    pose proof (u8ro_read asegs m A bs (o + 1) b1 (Z_to_bv 64 (A + o + 1)) BUF Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
    pose proof INV as (_ & (j0 & j224 & j256 & QC) & _).
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    zstep. step. ubr. zstep. step. zstep.
    gen2 CONT 0x8b2d8 14%nat 15%nat.
    { intros y14 y15.
      replace (Z_to_bv 64 (A + o)) with (Z_to_bv 64 (A + o + 1 + -1)) in RD0 by (f_equal; lia).
      zstep. clear RD0. zstep. step. if_cases KS0; zify_cond KS0.
      -
        zstep.
        eapply (KK m o l); [exact INV| exact CTX| exact PL| reflexivity| lia| lia| apply munch_refl| apply wmono_refl].
      -
        zstep. step. ubr. zstep. zstep. step. zstep.
        gen2 CONT2 0x8b304 11%nat 15%nat.
        { intros z11 z15.
          zstep. clear RD1. zstep. step. if_cases KS1; zify_cond KS1.
          -
            zstep.
            eapply (KK m o l); [exact INV| exact CTX| exact PL| reflexivity| lia| lia| apply munch_refl| apply wmono_refl].
          -
            pose proof (ploc_cells _ _ _ _ _ _ m PL) as (O1c & OVc & O2c & (j1 & j2 & j3 & J1 & J2 & J3)).
            pose proof INV as (_ & _ & MI & _).
            pose proof (munch_refl [(F + 96, F + 112)]%Z m) as MU2. pose proof (wmono_refl asegs m) as WM2.
            clear BUF QC. hide O1c. hide OVc. hide J1. hide J2. hide J3.
            zstep. zstep. step. fix_lit_store. step. fix_lit_store.
            unhide O1c. unhide OVc. unhide J1. unhide J2. unhide J3.
            assert (TR : forall X cs, rw_cells asegs m X cs -> (X + Z.of_nat (cells_size cs) <= F + 96 \/ F + 112 <= X) -> rw_cells asegs m2 X cs).
            { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU2| exact WM2| cbn [disjoint_from]; split; [exact HX| exact I]]. }
            pose proof (TR _ _ O1c ltac:(simpl_sizes; lia)) as O1c'. pose proof (TR _ _ OVc ltac:(simpl_sizes; lia)) as OVc'.
            pose proof (TR _ _ J1 ltac:(simpl_sizes; lia)) as J1'. pose proof (TR _ _ J2 ltac:(simpl_sizes; lia)) as J2'. pose proof (TR _ _ J3 ltac:(simpl_sizes; lia)) as J3'.
            replace (l + -1) with (l - 1) in O2c by lia.
            pose proof (ploc_of_cells _ _ _ _ _ _ m2 j1 j2 j3 O1c' OVc' O2c J1' J2' J3') as PL2.
            pose proof (pinv_stepJ qshadowU eq_refl q' m m2 _ INV MU2 WM2 MI rWU_inFJ (ploc_junk _ _ _ _ _ _ m2 PL2)) as INV2.
            pose proof (pctx_stepJ _ A len cap cur bs m m2 CTX TOK MU2 WM2 rWU_inFJ) as CTX2.
            clear O1c OVc J1 J2 J3 O1c' OVc' J1' J2' J3' O2c TR.
            zstep. zstep. step. if_cases KL; zify_cond KL.
            +
              replace (Z_to_bv 64 (A + o + 2)) with (Z_to_bv 64 (A + (o + 1) + 1)) by (f_equal; lia).
              replace (Z_to_bv 64 (A + o + 1)) with (Z_to_bv 64 (A + (o + 1))) by (f_equal; lia).
              replace (l + -1) with (l - 1) by lia.
              eapply (IH q' A len cap cur (o + 1) (l - 1) bs mb ml vb vl); [lia| exact INV2| exact CTX2| exact TOK| | lia| lia| lia|].
              * replace (A + (o + 1)) with (A + o + 1) by lia. exact PL2.
              * intros m' o' l' w1 w5 w6 w7 w10 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV3 CTX3 PL3 E3 O3 L3 MU3 WM3.
                eapply (KK m' o' l'); [exact INV3| exact CTX3| exact PL3| lia| lia| lia| exact (munch_trans _ _ _ _ MU2 MU3)| exact (wmono_trans _ _ _ _ WM2 WM3)].
            +
              step.
              assert (l = 2) by lia. subst l. change (2 + -1) with 1. change (2 - 1) with 1 in PL2.
              eapply (KK m2 (o + 1) 1); [exact INV2| exact CTX2| | lia| lia| lia| exact MU2| exact WM2].
              replace (A + (o + 1)) with (A + o + 1) by lia. exact PL2. }
        chkbQ 11 (A + o + 1) SHA kk SHRk Hk.
        destruct Hk as [-> | [G1 G2]].
        + step. step. lit_branch. apply CONT2.
        + step. rewrite (sxb_small kk) by lia.
          step. if_cases G3; zify_cond G3; [| exfalso; lia].
          zstep.
          step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
          apply CONT2. }
    chkbQ 14 (A + o) SHA kk SHRk Hk.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
  Qed.

  #[using="m0 POK RF0 mws MWL"] Lemma slash2Q : forall (k : nat) (q' A len cap cur o l : Z) (bs : list byte) (mb ml vb vl : word)
      x1 x5 x6 x7 x11 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    l < Z.of_nat k -> pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> plocQ mb ml vb vl (wz (A + o)) (wz l) m ->
    0 <= o -> 2 <= l -> o + l <= cap + 1 ->
    (forall m' o' l' y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> plocQ mb ml vb vl (wz (A + o')) (wz l') m' ->
       o' + l' = o + l -> o <= o' -> 1 <= l' -> munch rWU m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 (wz l') y12 y13 y14 y15 y16 y17 (wz 4) y28 y29 y30 y31) F_ (wz 0x8b414) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz (A + o)) x11 (wz l) (wz (A + o + 1)) x14 x15 x16 x17 (wz 4) x28 x29 x30 x31) F_ (wz 0x8b384) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until Q; intros HK INV CTX TOK PL O0 L2 OL KK; [lia|].
    pose proof CTX as (_ & _ & TXT & _ & SHA & _).
    pose proof TOK as TOK'. tokA TOK'. pose proof POK as POK'. pqokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (H_pparse_seg.text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    assert (HB0 : exists b, nth_error bs (Z.to_nat o) = Some b) by (destruct (nth_error bs (Z.to_nat o)) as [b|] eqn:E; [exists b; reflexivity| apply nth_error_None in E; lia]).
    assert (HB1 : exists b, nth_error bs (Z.to_nat (o + 1)) = Some b) by (destruct (nth_error bs (Z.to_nat (o + 1))) as [b|] eqn:E; [exists b; reflexivity| apply nth_error_None in E; lia]).
    destruct HB0 as (b0 & Hb0). destruct HB1 as (b1 & Hb1).
    pose proof (P0.H_presp_A.byte_range b0) as BR0. pose proof (P0.H_presp_A.byte_range b1) as BR1.
    pose proof (u8ro_read asegs m A bs o b0 (Z_to_bv 64 (A + o)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
    pose proof (u8ro_read asegs m A bs (o + 1) b1 (Z_to_bv 64 (A + o + 1)) BUF Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
    pose proof INV as (_ & (j0 & j224 & j256 & QC) & _).
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    zstep. step. ubr. zstep. step. zstep.
    gen2 CONT 0x8b3a0 14%nat 15%nat.
    { intros y14 y15.
      replace (Z_to_bv 64 (A + o)) with (Z_to_bv 64 (A + o + 1 + -1)) in RD0 by (f_equal; lia).
      zstep. clear RD0. zstep. step. if_cases KS0; zify_cond KS0.
      -
        zstep.
        eapply (KK m o l); [exact INV| exact CTX| exact PL| reflexivity| lia| lia| apply munch_refl| apply wmono_refl].
      -
        zstep. step. ubr. zstep. zstep. step. zstep.
        gen2 CONT2 0x8b3cc 11%nat 15%nat.
        { intros z11 z15.
          zstep. clear RD1. zstep. step. if_cases KS1; zify_cond KS1.
          -
            zstep.
            eapply (KK m o l); [exact INV| exact CTX| exact PL| reflexivity| lia| lia| apply munch_refl| apply wmono_refl].
          -
            pose proof (ploc_cells _ _ _ _ _ _ m PL) as (O1c & OVc & O2c & (j1 & j2 & j3 & J1 & J2 & J3)).
            pose proof INV as (_ & _ & MI & _).
            pose proof (munch_refl [(F + 96, F + 112)]%Z m) as MU2. pose proof (wmono_refl asegs m) as WM2.
            clear BUF QC. hide O1c. hide OVc. hide J1. hide J2. hide J3.
            zstep. zstep. step. fix_lit_store. step. fix_lit_store.
            unhide O1c. unhide OVc. unhide J1. unhide J2. unhide J3.
            assert (TR : forall X cs, rw_cells asegs m X cs -> (X + Z.of_nat (cells_size cs) <= F + 96 \/ F + 112 <= X) -> rw_cells asegs m2 X cs).
            { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU2| exact WM2| cbn [disjoint_from]; split; [exact HX| exact I]]. }
            pose proof (TR _ _ O1c ltac:(simpl_sizes; lia)) as O1c'. pose proof (TR _ _ OVc ltac:(simpl_sizes; lia)) as OVc'.
            pose proof (TR _ _ J1 ltac:(simpl_sizes; lia)) as J1'. pose proof (TR _ _ J2 ltac:(simpl_sizes; lia)) as J2'. pose proof (TR _ _ J3 ltac:(simpl_sizes; lia)) as J3'.
            replace (l + -1) with (l - 1) in O2c by lia.
            pose proof (ploc_of_cells _ _ _ _ _ _ m2 j1 j2 j3 O1c' OVc' O2c J1' J2' J3') as PL2.
            pose proof (pinv_stepJ qshadowU eq_refl q' m m2 _ INV MU2 WM2 MI rWU_inFJ (ploc_junk _ _ _ _ _ _ m2 PL2)) as INV2.
            pose proof (pctx_stepJ _ A len cap cur bs m m2 CTX TOK MU2 WM2 rWU_inFJ) as CTX2.
            clear O1c OVc J1 J2 J3 O1c' OVc' J1' J2' J3' O2c TR.
            zstep. zstep. step. if_cases KL; zify_cond KL.
            +
              replace (Z_to_bv 64 (A + o + 2)) with (Z_to_bv 64 (A + (o + 1) + 1)) by (f_equal; lia).
              replace (Z_to_bv 64 (A + o + 1)) with (Z_to_bv 64 (A + (o + 1))) by (f_equal; lia).
              replace (l + -1) with (l - 1) by lia.
              eapply (IH q' A len cap cur (o + 1) (l - 1) bs mb ml vb vl); [lia| exact INV2| exact CTX2| exact TOK| | lia| lia| lia|].
              * replace (A + (o + 1)) with (A + o + 1) by lia. exact PL2.
              * intros m' o' l' w1 w5 w6 w7 w10 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV3 CTX3 PL3 E3 O3 L3 MU3 WM3.
                eapply (KK m' o' l'); [exact INV3| exact CTX3| exact PL3| lia| lia| lia| exact (munch_trans _ _ _ _ MU2 MU3)| exact (wmono_trans _ _ _ _ WM2 WM3)].
            +
              step.
              assert (l = 2) by lia. subst l. change (2 + -1) with 1. change (2 - 1) with 1 in PL2.
              eapply (KK m2 (o + 1) 1); [exact INV2| exact CTX2| | lia| lia| lia| exact MU2| exact WM2].
              replace (A + (o + 1)) with (A + o + 1) by lia. exact PL2. }
        chkbQ 11 (A + o + 1) SHA kk SHRk Hk.
        destruct Hk as [-> | [G1 G2]].
        + step. step. lit_branch. apply CONT2.
        + step. rewrite (sxb_small kk) by lia.
          step. if_cases G3; zify_cond G3; [| exfalso; lia].
          zstep.
          step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
          apply CONT2. }
    chkbQ 14 (A + o) SHA kk SHRk Hk.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
  Qed.

  Definition rWA : list ivl :=
    [(P + 4, P + 8); (P + 440, P + 444); (P + 480 + 8, P + 480 + 16); (F + 32, F + 32 + 16); (F + 96, F + 96 + 16); (F + 64, F + 64 + 16)]%Z.
  #[using="m0 RF0 mws MWL"] Lemma fk_ok_own : forall (W : list ivl) (iv : ivl), fst iv <= snd iv ->
    (F <= fst iv /\ snd iv <= F + 128) \/ (SF <= fst iv /\ snd iv <= SF + 16) -> fk_ok FI W st iv.
  Proof.
    intros W [a b] AB HIV. cbn [fst snd] in *. right; right.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in *.
    pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in *. intros g Hg.
    destruct (APART g Hg) as (A1 & A2 & A3). destruct (LN g Hg) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { unfold H_pparse_seg.qSF, sh, SHADOW_OFF. clear - FLO FHI B4. Z.div_mod_to_equations. lia. }
    assert (SH2 : FSB FI + A0_FS_SIZE <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= FSB FI).
    { unfold sh, SHADOW_OFF. clear - B1 B2 B5 ACR. Z.div_mod_to_equations. lia. }
    cbn [fst snd]. clear - AB HIV A1 A2 A3 L1 L2 L4 L5 L8 L9 FLO FHI FLLO FLHI SH1 SH2. lia.
  Qed.
  #[using="m0 RF0 mws MWL"] Lemma fkeep_own : forall (W Ws : list ivl) m m' shd q', pinvQS shd q' m -> munch Ws m m' ->
    Forall (fun iv => fst iv <= snd iv /\ ((alloc_ceiling <= fst iv) \/ inside W (fst iv) (snd iv - fst iv)
                                          \/ (F <= fst iv /\ snd iv <= F + 128) \/ (SF <= fst iv /\ snd iv <= SF + 16))) Ws ->
    fkeep FI W st m m'.
  Proof.
    intros W Ws m m' shd q' INV MU HWs. destruct (pinv_rf _ q' m INV) as (stc & RF & LIVE1).
    eapply (fkeep_of_munch FI W Ws st stc m m m' RF); [intros g Hg; rewrite LIVE1; right; exact Hg| exact MU|].
    eapply Forall_impl; [| exact HWs]. intros [a b] (AB & HIV). cbn [fst snd] in *.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct HIV as [HIV|[HIV|HIV]].
    - right; left. cbn [fst snd]. unfold sh, SHADOW_OFF. split; [right; clear - HIV B2; lia|]. right. clear - HIV B1 B2 ACR. Z.div_mod_to_equations. lia.
    - left. exact HIV.
    - apply fk_ok_own; [exact AB| exact HIV].
  Qed.

  Definition rmove (m m' : mem) : Prop := munch ((lo, q) :: FSIV rWA) m m' /\ wmono asegs m m' /\ fkeep FI rWA st m m'.
  #[using="Type"] Lemma rmove_refl : forall m, rmove m m.
  Proof. intros m. split; [apply munch_refl|]. split; [apply wmono_refl| apply fkeep_refl]. Qed.
  #[using="Type"] Lemma rmove_trans : forall m1 m2 m3, rmove m1 m2 -> rmove m2 m3 -> rmove m1 m3.
  Proof.
    intros m1 m2 m3 (A1 & A2 & A3) (B1 & B2 & B3).
    split; [exact (munch_trans _ _ _ _ A1 B1)|]. split; [exact (wmono_trans _ _ _ _ A2 B2)| exact (fkeep_trans FI _ _ _ _ _ A3 B3)].
  Qed.
  #[using="Type"] Lemma rmove_fk : forall (W : list ivl) m m', munch ((lo, q) :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W st m m' -> sub_fp W rWA -> rmove m m'.
  Proof.
    intros W m m' MU WM FK SUB. split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & H4). repeat split; try assumption. apply SUB. exact H4.
    - eapply (fkeep_weaken FI W rWA st st m m' FK SUB). intros g Hg; exact Hg.
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma rmove_T : forall shd q' m m', pinvQS shd q' m -> munch (rWT q') m m' -> wmono asegs m m' -> rmove m m'.
  Proof.
    intros shd q' m m' INV MU WM. pose proof INV as (_ & _ & _ & _ & (QB & _) & _).
    pose proof POK as POK'. pqokA POK'. destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. unfold rWT. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _). repeat split; try exact I; clear - H1 H2 QB PF1 PF2 LO; lia.
    - apply (fkeep_own rWA (rWT q') m m' shd q' INV MU). unfold rWT, rWA.
      constructor; [cbn [fst snd]; split; [clear - LO QB; lia| left; exact CLO]|].
      constructor; [cbn [fst snd]; split; [clear; lia| right; left; cbn [inside]; right; right; left; clear; lia]| constructor].
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma rmove_U : forall shd q' m m', pinvQS shd q' m -> munch rWU m m' -> wmono asegs m m' -> rmove m m'.
  Proof.
    intros shd q' m m' INV MU WM. destruct eframe_facts as (FLO & FHI & _).
    split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. unfold rWU. intros x Hx. cbn [outside] in *. destruct Hx as (_ & H2 & _). split; [clear - H2 FLO FHI; lia| exact I].
    - apply (fkeep_own rWA rWU m m' shd q' INV MU). unfold rWU.
      constructor; [cbn [fst snd]; split; [clear; lia| right; right; left; clear; lia]| constructor].
  Qed.

  #[using="HC FI q st POK"] Lemma pcell_T : forall q' m m' X cs, munch (rWT q') m m' -> wmono asegs m m' -> P <= X -> X + Z.of_nat (cells_size cs) <= P + 488 ->
    rw_cells asegs m X cs -> rw_cells asegs m' X cs.
  Proof.
    intros q' m m' X cs MU WM H1 H2 HC1. pose proof POK as POK'. pqokA POK'.
    eapply rw_cells_transport; [exact HC1| exact MU| exact WM|]. unfold rWT. cbn [disjoint_from]. split; [left; clear - H2 PHI CLO; lia|]. split; [left; exact H2| exact I].
  Qed.
  #[using="q lo POK mws MWL"] Lemma pcell_fk : forall (W : list ivl) m m' X cs, fkeep FI W st m m' -> wmono asegs m m' -> P <= X -> X + Z.of_nat (cells_size cs) <= P + 504 ->
    disjoint_from W X (Z.of_nat (cells_size cs)) -> rw_cells asegs m X cs -> rw_cells asegs m' X cs.
  Proof.
    intros W m m' X cs FK WM H1 H2 DJ HC1. pose proof POK as POK'. pqokA POK'.
    eapply (rw_cells_fkeep FI W st); [exact HC1| exact FK| exact WM| left; apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact DJ].
  Qed.
  #[using="q lo m0 POK RF0"] Lemma pcell_U : forall m m' X cs, munch rWU m m' -> wmono asegs m m' -> P <= X -> X + Z.of_nat (cells_size cs) <= P + 504 ->
    rw_cells asegs m X cs -> rw_cells asegs m' X cs.
  Proof.
    intros m m' X cs MU WM H1 H2 HC1. destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PAF & _).
    eapply rw_cells_transport; [exact HC1| exact MU| exact WM|]. unfold rWU. cbn [disjoint_from]. split; [clear - H1 H2 PAF; lia| exact I].
  Qed.

  #[using="HC FI st m0 POK RF0 MWL"] Lemma pstatR_T : forall q' m m', q + -400 <= q' -> pstatR m -> munch (rWT q') m m' -> wmono asegs m m' -> pstatR m'.
  Proof.
    intros q' m m' QB PS MU WM. pose proof POK as POK'. pqokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    apply (pstatR_step (rWT q') m m' PS MU WM); unfold rWT.
    - constructor; [left; apply app_iv_stack; exact CLO|]. constructor; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 B1 B2 B5; lia| constructor].
    - constructor; [left; cbn [fst]; clear - CLO ACR; lia|]. constructor; [left; cbn [fst]; clear - PLO; lia| constructor].
  Qed.
  #[using="Type"] Lemma rW09_sub : sub_fp rW09 rWA.
  Proof. unfold rW09, rWA. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; assumption. Qed.
  #[using="Type"] Lemma rWRQ_sub : sub_fp rWRQ rWA.
  Proof. unfold rWRQ, rWA. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; assumption. Qed.
  #[using="Type"] Lemma rWM_sub : sub_fp rWM rWA.
  Proof. unfold rWM, rWA. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; assumption. Qed.

  Definition strcallstQ (ret q' ao l : Z) (x25 : word) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (pregsQ q' (wz ret) x5 x6 x7 (wz ao) (wz l) x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31) F_ (wz str_alloc_entryA) fc None m (seg_rom asegs).

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 m0 POK RF0 FCO MWL MID"] Lemma segAQ : forall (q' A len cap cur meth err : Z) (bs : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatR m -> FSENV FI m -> 0 <= cur <= len ->
    rw_cells asegs m (P + 440) [C4 (wz err)] -> rw_cells asegs m (P + 4) [C4 (wz meth)] ->
    (forall m' r cur' (e' : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       0 <= r <= 5 -> r <> 4 -> cur <= cur' <= len -> (e' = err \/ e' = 501 \/ e' = 400) ->
       pinvQS qshadowU q' m' -> pctx A len cap cur' bs m' -> rw_cells asegs m' (P + 440) [C4 (wz e')] -> rw_cells asegs m' (P + 4) [C4 (wz meth)] -> rmove m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    (forall m' cur' o l (mb ml vb vl : word) y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       cur <= cur' <= len -> cur <= o -> 1 <= l -> o + l < len ->
       pinvQS qshadowU q' m' -> pctx A len cap cur' bs m' -> pstatR m' -> FSENV FI m' -> plocQ mb ml vb vl (wz (A + o)) (wz l) m' ->
       rw_cells asegs m' (P + 440) [C4 (wz err)] -> rw_cells asegs m' (P + 4) [C4 (wz 12)] -> rmove m m' ->
       evt asegs Q (strcallstQ 0x8b618 q' (A + o) l (wz (F + 32)) y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m')) ->
    (forall m' cur' o1 l1 o l o3 l3 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       cur <= cur' <= len -> cur <= o1 -> 1 <= l1 -> o1 + l1 < len -> cur <= o -> 1 <= l -> o + l < o3 -> 0 <= l3 -> o3 + l3 < cur' ->
       pinvQS qshadowU q' m' -> pctx A len cap cur' bs m' -> pstatR m' -> FSENV FI m' ->
       plocQ (wz (A + o1)) (wz l1) (wz (A + o3)) (wz l3) (wz (A + o)) (wz l) m' ->
       rw_cells asegs m' (P + 440) [C4 (wz err)] -> rw_cells asegs m' (P + 4) [C4 (wz meth)] -> rmove m m' ->
       evt asegs Q (strcallstQ 0x8b41c q' (A + o) l (wz 4) y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31) F_ (wz 0x8b1dc) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur meth err bs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m Q INV CTX TOK PS FE CR EC MC KR KA1 KA2.
    pose proof INV as (_ & SCRQ & _ & _ & (QB & _) & _).
    destruct (pscr_split q' m SCRQ) as (ty0 & tb0 & tl0 & SCR).
    pose proof TOK as TOK'. tokA TOK'.
    eapply (skipQ (Datatypes.S (Z.to_nat (len - cur))) q' A len cap cur bs ty0 tb0 tl0); [lia| exact INV| exact CTX| exact TOK| exact CR| exact SCR| |].
    -
      intros r cur' m1 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RR CR1 INV1 CTX1 MU1 WM1.
      eapply (KR m1 r cur' err); [lia| lia| exact CR1| left; reflexivity| exact INV1| exact CTX1
        | exact (pcell_T q' m m1 (P + 440) [C4 (wz err)] MU1 WM1 ltac:(lia) ltac:(simpl_sizes; lia) EC)| exact (pcell_T q' m m1 (P + 4) [C4 (wz meth)] MU1 WM1 ltac:(lia) ltac:(simpl_sizes; lia) MC)
        | exact (rmove_T _ q' m m1 INV MU1 WM1)].
    -
      intros cur1 m1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31 CR1 INV1 CTX1 MU1 WM1.
      pose proof (pcell_T q' m m1 (P + 440) [C4 (wz err)] MU1 WM1 ltac:(lia) ltac:(simpl_sizes; lia) EC) as EC1.
      pose proof (pcell_T q' m m1 (P + 4) [C4 (wz meth)] MU1 WM1 ltac:(lia) ltac:(simpl_sizes; lia) MC) as MC1.
      pose proof (pstatR_T q' m m1 ltac:(lia) PS MU1 WM1) as PS1.
      pose proof (fsenv_munch FI _ m m1 FE MU1 (rWT_fcls q' ltac:(lia))) as FE1.
      pose proof (rmove_T _ q' m m1 INV MU1 WM1) as MV1.
      clear INV CTX PS FE EC MC MU1 WM1 SCR SCRQ.
      eapply (m09Q q' A len cap cur1 bs); [exact INV1| exact CTX1| exact TOK| lia| exact FE1| |].
      +
        intros m2 cur2 o1 l1 o2 l2 vb vl z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 INV2 CTX2 PL2 FE2 X1 X2 X3 X4 X5 X6 X7 MU2 WM2 FK2.
        destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _ & PF1 & PF2).
        assert (DJ9 : forall X n, P <= X -> X + n <= P + 488 -> disjoint_from rW09 X n)
          by (intros X n H1 H2; unfold rW09; cbn [disjoint_from]; repeat split; try exact I; clear - H1 H2 PAF; lia).
        pose proof (pcell_fk rW09 m1 m2 (P + 440) [C4 (wz err)] FK2 WM2 ltac:(lia) ltac:(simpl_sizes; lia) (DJ9 (P + 440) 4 ltac:(lia) ltac:(lia)) EC1) as EC2.
        pose proof (pcell_fk rW09 m1 m2 (P + 4) [C4 (wz meth)] FK2 WM2 ltac:(lia) ltac:(simpl_sizes; lia) (DJ9 (P + 4) 4 ltac:(lia) ltac:(lia)) MC1) as MC2.
        pose proof (pstatR_stepF rW09 q m1 m2 PS1 MU2 WM2 rW09_ok) as PS2.
        assert (MV2 : rmove m m2).
        { apply (rmove_trans _ _ _ MV1). exact (rmove_fk rW09 m1 m2 MU2 WM2 FK2 rW09_sub). }
        clear INV1 CTX1 PS1 FE1 EC1 MC1 MU2 WM2 FK2 MV1 DJ9.
        eapply (map09Q q' A len cap cur2 o1 l1 o2 l2 meth bs vb vl (wz err)); [exact INV2| exact CTX2| exact TOK| exact PS2| exact FE2| exact PL2| lia| lia| lia| exact EC2| exact MC2| |].
        *
          intros m3 e' w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV3 CTX3 E3 EC3 MC3 MU3 WM3 FK3.
          eapply (KR m3 3 cur2 e'); [lia| lia| lia| right; exact E3| exact INV3| exact CTX3| exact EC3| exact MC3|].
          apply (rmove_trans _ _ _ MV2). exact (rmove_fk rWM m2 m3 MU3 WM3 FK3 rWM_sub).
        *
          intros m3 w1 w5 w6 w7 w10 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV3 CTX3 PS3 FE3 PL3 EC3 MC3 MU3 WM3 FK3.
          assert (MV3 : rmove m m3).
          { apply (rmove_trans _ _ _ MV2). exact (rmove_fk rWM m2 m3 MU3 WM3 FK3 rWM_sub). }
          clear INV2 CTX2 PS2 FE2 PL2 EC2 MC2 MU3 WM3 FK3 MV2.
          assert (TAIL : forall m4 o' l' u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31,
                    pinvQS qshadowU q' m4 -> pctx A len cap cur2 bs m4 -> pstatR m4 -> FSENV FI m4 -> plocQ (wz (A + o1)) (wz l1) vb vl (wz (A + o')) (wz l') m4 ->
                    rw_cells asegs m4 (P + 440) [C4 (wz err)] -> rw_cells asegs m4 (P + 4) [C4 (wz 12)] -> rmove m m4 -> o' + l' = o2 + l2 -> o2 <= o' -> 1 <= l' ->
                    evt asegs Q (MS (pregsQ q' u1 u5 u6 u7 u10 (wz l') u12 u13 u14 u15 u16 u17 (wz (F + 32)) u28 u29 u30 u31) F_ (wz 0x8b610) fc None m4 (seg_rom asegs))).
          { intros m4 o' l' u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 INV4 CTX4 PS4 FE4 PL4 EC4 MC4 MV4 E4 O4 L4.
            pose proof (ploc_cells _ _ _ _ _ _ m4 PL4) as (_ & _ & O2c & _).
            unfold H_pparse_seg.pregsQ. step. step.
            eapply (KA1 m4 cur2 o' l'); try eassumption; lia. }
          unfold H_pparse_seg.pregsQ. step. if_cases KL; zify_cond KL.
          --
             zstep. eapply (TAIL m3 o2 l2); try eassumption; lia.
          -- pose proof (ploc_cells _ _ _ _ _ _ m3 PL3) as (_ & _ & O2c & _).
             step. zstep. clear O2c.
             eapply (slash1Q (Datatypes.S (Z.to_nat l2)) q' A len cap cur2 o2 l2 bs); [lia| exact INV3| exact CTX3| exact TOK| exact PL3| lia| lia| lia|].
             intros m4 o' l' u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 INV4 CTX4 PL4 E4 O4 L4 MU4 WM4.
             eapply (TAIL m4 o' l'); [exact INV4| exact CTX4| exact (pstatR_stepJ _ m3 m4 PS3 MU4 WM4 rWU_inFJ)| | exact PL4
               | exact (pcell_U m3 m4 (P + 440) [C4 (wz err)] MU4 WM4 ltac:(lia) ltac:(simpl_sizes; lia) EC3)
               | exact (pcell_U m3 m4 (P + 4) [C4 (wz 12)] MU4 WM4 ltac:(lia) ltac:(simpl_sizes; lia) MC3)
               | exact (rmove_trans _ _ _ MV3 (rmove_U _ q' m3 m4 INV3 MU4 WM4))| lia| lia| lia].
             refine (fsenv_munch FI _ m3 m4 FE3 MU4 _). unfold rWU. constructor; [apply fcls_in_fs; lia| constructor].
      +
        intros m2 r z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RN RR INV2 CTX2 FE2 MU2 WM2 FK2.
        destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _ & PF1 & PF2).
        assert (DJ9 : forall X n, P <= X -> X + n <= P + 488 -> disjoint_from rW09 X n)
          by (intros X n H1 H2; unfold rW09; cbn [disjoint_from]; repeat split; try exact I; clear - H1 H2 PAF; lia).
        assert (DJR : forall X n, P <= X -> X + n <= P + 488 -> disjoint_from rWRQ X n)
          by (intros X n H1 H2; unfold rWRQ; cbn [disjoint_from]; repeat split; try exact I; clear - H1 H2 PAF; lia).
        pose proof (pcell_fk rW09 m1 m2 (P + 440) [C4 (wz err)] FK2 WM2 ltac:(lia) ltac:(simpl_sizes; lia) (DJ9 (P + 440) 4 ltac:(lia) ltac:(lia)) EC1) as EC2.
        pose proof (pcell_fk rW09 m1 m2 (P + 4) [C4 (wz meth)] FK2 WM2 ltac:(lia) ltac:(simpl_sizes; lia) (DJ9 (P + 4) 4 ltac:(lia) ltac:(lia)) MC1) as MC2.
        pose proof (pstatR_stepF rW09 q m1 m2 PS1 MU2 WM2 rW09_ok) as PS2.
        assert (MV2 : rmove m m2) by (apply (rmove_trans _ _ _ MV1); exact (rmove_fk rW09 m1 m2 MU2 WM2 FK2 rW09_sub)).
        clear INV1 CTX1 PS1 FE1 EC1 MC1 MU2 WM2 FK2 MV1 DJ9.
        eapply (mrqQ q' A len cap cur1 bs); [exact INV2| exact CTX2| exact TOK| lia| exact FE2| |].
        * intros m3 cur3 o1 l1 o2 l2 o3 l3 w1 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV3 CTX3 PL3 FE3 X1 X2 X3 X4 X5 X6 X7 X8 MU3 WM3 FK3.
          pose proof (pcell_fk rWRQ m2 m3 (P + 440) [C4 (wz err)] FK3 WM3 ltac:(lia) ltac:(simpl_sizes; lia) (DJR (P + 440) 4 ltac:(lia) ltac:(lia)) EC2) as EC3.
          pose proof (pcell_fk rWRQ m2 m3 (P + 4) [C4 (wz meth)] FK3 WM3 ltac:(lia) ltac:(simpl_sizes; lia) (DJR (P + 4) 4 ltac:(lia) ltac:(lia)) MC2) as MC3.
          pose proof (pstatR_stepF rWRQ q m2 m3 PS2 MU3 WM3 rWRQ_ok) as PS3.
          assert (MV3 : rmove m m3) by (apply (rmove_trans _ _ _ MV2); exact (rmove_fk rWRQ m2 m3 MU3 WM3 FK3 rWRQ_sub)).
          clear INV2 CTX2 PS2 FE2 EC2 MC2 MU3 WM3 FK3 MV2 DJR.
          assert (TAIL : forall m4 o' l' u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31,
                    pinvQS qshadowU q' m4 -> pctx A len cap cur3 bs m4 -> pstatR m4 -> FSENV FI m4 ->
                    plocQ (wz (A + o1)) (wz l1) (wz (A + o3)) (wz l3) (wz (A + o')) (wz l') m4 ->
                    rw_cells asegs m4 (P + 440) [C4 (wz err)] -> rw_cells asegs m4 (P + 4) [C4 (wz meth)] -> rmove m m4 -> o' + l' = o2 + l2 -> o2 <= o' -> 1 <= l' ->
                    evt asegs Q (MS (pregsQ q' u1 u5 u6 u7 u10 (wz l') u12 u13 u14 u15 u16 u17 (wz 4) u28 u29 u30 u31) F_ (wz 0x8b414) fc None m4 (seg_rom asegs))).
          { intros m4 o' l' u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 INV4 CTX4 PS4 FE4 PL4 EC4 MC4 MV4 E4 O4 L4.
            pose proof (ploc_cells _ _ _ _ _ _ m4 PL4) as (_ & _ & O2c & _).
            unfold H_pparse_seg.pregsQ. step. step.
            eapply (KA2 m4 cur3 o1 l1 o' l' o3 l3); try eassumption; lia. }
          pose proof (ploc_cells _ _ _ _ _ _ m3 PL3) as (_ & _ & O2c & _).
          pose proof INV3 as (_ & (j0 & j224 & j256 & QC) & _).
          unfold H_pparse_seg.pregsQ. step. step. if_cases KL; zify_cond KL.
          --
             zstep. eapply (TAIL m3 o2 l2); try eassumption; lia.
          -- step. zstep. clear O2c QC.
             eapply (slash2Q (Datatypes.S (Z.to_nat l2)) q' A len cap cur3 o2 l2 bs); [lia| exact INV3| exact CTX3| exact TOK| exact PL3| lia| lia| lia|].
             intros m4 o' l' u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 INV4 CTX4 PL4 E4 O4 L4 MU4 WM4.
             eapply (TAIL m4 o' l'); [exact INV4| exact CTX4| exact (pstatR_stepJ _ m3 m4 PS3 MU4 WM4 rWU_inFJ)| | exact PL4
               | exact (pcell_U m3 m4 (P + 440) [C4 (wz err)] MU4 WM4 ltac:(lia) ltac:(simpl_sizes; lia) EC3)
               | exact (pcell_U m3 m4 (P + 4) [C4 (wz meth)] MU4 WM4 ltac:(lia) ltac:(simpl_sizes; lia) MC3)
               | exact (rmove_trans _ _ _ MV3 (rmove_U _ q' m3 m4 INV3 MU4 WM4))| lia| lia| lia].
             refine (fsenv_munch FI _ m3 m4 FE3 MU4 _). unfold rWU. constructor; [apply fcls_in_fs; lia| constructor].
        *
          intros m3 r3 w1 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 RN3 RR3 INV3 CTX3 FE3 MU3 WM3 FK3.
          eapply (KR m3 r3 cur1 err); [lia| exact RN3| lia| left; reflexivity| exact INV3| exact CTX3
            | exact (pcell_fk rWRQ m2 m3 (P + 440) [C4 (wz err)] FK3 WM3 ltac:(lia) ltac:(simpl_sizes; lia) (DJR (P + 440) 4 ltac:(lia) ltac:(lia)) EC2)
            | exact (pcell_fk rWRQ m2 m3 (P + 4) [C4 (wz meth)] FK3 WM3 ltac:(lia) ltac:(simpl_sizes; lia) (DJR (P + 4) 4 ltac:(lia) ltac:(lia)) MC2)
            | exact (rmove_trans _ _ _ MV2 (rmove_fk rWRQ m2 m3 MU3 WM3 FK3 rWRQ_sub))].
  Qed.

  Definition rWP : list ivl := [(P + 8, P + 8 + 216); (ERRNO_A, ERRNO_A + 4)]%Z.
  #[using="mws MWL"] Lemma rWP_ok : Forall inW3 rWP.
  Proof.
    unfold rWP, H_pparse_seg.inW3, H_pparse_seg.inP, H_pparse_seg.inER.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [right; right; left; cbn [fst snd]; lia| constructor].
  Qed.
  #[using="q lo st m0 POK RF0 mws MWL"] Lemma rWP_fcls : Forall (fsenv_cls (FSB FI)) rWP.
  Proof.
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). unfold rWP.
    constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_errno; lia| constructor].
  Qed.
  Definition pstatU (m : mem) : Prop :=
    shw m 0x21c40 6 /\ shw m 0xaf6a0 4 /\ shw m 0x21c20 10 /\ shw m 0x21c60 13
    /\ rw_cells asegs m 0xab9a8 [C8 (wz 0xaf6a0)] /\ (exists gv, rw_cells asegs m 0xaf6a0 [C4 gv]).
  #[using="mws MWL"] Lemma pstatU_step : forall (W : list ivl) m m', pstatU m -> munch W m m' -> wmono asegs m m' -> Forall (fsw_iv FI) W -> Forall hiER W -> pstatU m'.
  Proof.
    intros W m m' (S1 & S2 & S3 & S4 & G1 & (gv & G2)) MU WM HF HA. pose proof (fsb_ok FI) as (B1 & _).
    split; [apply (shw_frame_fs FI W m m' _ _ S1 MU HF); left; lia|]. split; [apply (shw_frame_fs FI W m m' _ _ S2 MU HF); left; lia|].
    split; [apply (shw_frame_fs FI W m m' _ _ S3 MU HF); left; lia|]. split; [apply (shw_frame_fs FI W m m' _ _ S4 MU HF); left; lia|].
    split; [eapply rw_cells_transport; [exact G1| exact MU| exact WM| apply dj_hiER; [exact HA| simpl_sizes; lia]]|].
    exists gv. eapply rw_cells_transport; [exact G2| exact MU| exact WM| apply dj_hiER; [exact HA| simpl_sizes; lia]].
  Qed.

  Definition keepU (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 8)
       \/ (P + 224 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.

  #[using="IC STACK_MALLOC_3 SET_SHADOW_F5 m0 POK RF0 FCO mws MWL"] Lemma puri_callQ : forall (q' A len cap cur U ulen : Z) (bs ustr slack junk : list byte) (m : mem)
      (ra' gp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatU m -> FSENV FI m -> tp = Z_to_bv 64 6190512 ->
    rw_cells asegs m (P + 8) [CB 216 junk] ->
    Z.of_nat (length ustr) = ulen -> 0 <= ulen < 2^31 -> (- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack) ->
    0x609000 <= U -> U + ulen + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
    (U + ulen + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U) ->
    (U + ulen + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U) ->
    shw m U (ulen + 1) -> bytes_at asegs m U (ustr ++ Z_to_bv 8 0 :: slack) ->
    (forall m' (r : Z) (junk' : list byte) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> pstatU m' -> FSENV FI m' -> (r = 1 \/ r = -108) ->
       rw_cells asegs m' (P + 8) [CB 216 junk'] -> keepU m m' ->
       munch ((lo, q) :: FSIV rWP) m m' -> wmono asegs m m' -> fkeep FI rWP st m m' ->
       evt asegs Q (MS (mkR ra' (wz q') gp' tp y5 y6 y7 s0' s1' (wz r) y11 y12 y13 y14 y15 y16 y17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' y28 y29 y30 y31)
                       F_ (ret_pc ra') fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra' (wz q') gp' tp t0 t1 t2 s0' s1' (wz U) (wz ulen) (wz (P + 8)) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                    F_ (wz H_puri_seg1.puri_entryA) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur U ulen bs ustr slack junk m ra' gp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 Q
           INV CTX TOK PU FE TPV UC UL ULR SLK ULO UHI UFS UBAND SHU UB KK.
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & VR).
    destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & _ & _ & (stc & RF & LIVE1)).
    pose proof CTX as (SC & MBC & TXT & SHP & SHA & _ & _ & _ & SHZ & SHR & (ev & (CE & CG & CS)) & _).
    pose proof PU as (S1 & S2 & S3 & S4 & G1 & G2).
    pose proof POK as POK'. pqokA POK'. pose proof TOK as TOK'. tokA TOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (elive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    eapply evt_cut.
    { eapply (parse_uri_spec_A FI IC STACK_MALLOC_3 SET_SHADOW_F5 U (P + 8) ulen lo q' ustr slack junk canary stc);
        [ exact CLO | clear - LO QB; lia | exact QAL | change (2^63) with 9223372036854775808; change (2^47) with 140737488355328 in *; clear - QB QHI; lia | exact ST
        | change (2^47) with 140737488355328 in *; clear - QB QHI; lia
        | apply (shz_sub _ _ _ _ _ SHZ); [lia| apply sh_mono; clear - QB; lia]
        | intros a Ha; apply SHR; pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia
        | exact MI | exact AE | exact RF
        | exact (fs_call_ok_le FI _ _ _ 1%nat (fs_call_ok_push FI st stc tp 4%nat _ FCO LIVE1) ltac:(lia)) | exact FE | exact TPV
        | clear - PAL; Z.div_mod_to_equations; lia | lia | lia | apply (Contracts.lb_sub _ _ _ _ _ LVP); lia
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia] | exact UC
        | exact UL | exact ULR | exact SLK | exact ULO | exact UHI | exact UFS | exact UBAND | exact SHU | exact UB
        | exact S1 | exact S2 | exact S3 | exact S4 | exists ev; exact CE | exact CG | exact CS | exact G1 | exact G2 ]. }
    intros ms' POST. unfold parse_uri_post_A in POST.
    destruct POST as (r & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MU0 & WM' & MI' & FK0 & LIVE' & RF' & ST' & AE' & RES & XF).
    destruct XF as (junk' & UC' & UB' & (ev' & CE') & CG' & CS' & G1' & G2').
    assert (KEEP : keepU m m').
    { intros X cs HC1 HX. eapply (rw_cells_fkeep FI _ stc m m'); [exact HC1| exact FK0| exact WM'| |].
      - destruct HX as [HX|[HX|HX]]; left; [apply (Contracts.lb_sub _ _ _ _ _ LVF); lia| apply (Contracts.lb_sub _ _ _ _ _ LVP); lia| apply (Contracts.lb_sub _ _ _ _ _ LVP); lia].
      - unfold puri_WA. cbn [disjoint_from]. split; [clear - HX PAF; lia|]. split; [| exact I]. right. clear - HX FLO PF1 PLO. pose proof (fsb_ok FI) as (B1 & _). lia. }
    assert (FT1' : exists j, rw_cells asegs m' (F + 32) [CB 88 j]) by (exists jf; apply (KEEP _ _ FT1); left; simpl_sizes; lia).
    assert (HW3 : Forall inW3 (puri_WA (P + 8))) by exact rWP_ok.
    pose proof (pinv_stepF qshadowU eq_refl _ q' m m' stc st' INV LIVE1 MU0 WM' FK0 LIVE' RF' ST' MI' AE' HW3 FT1') as INV1.
    assert (SC' : rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]) by (apply (KEEP _ _ SC); right; right; simpl_sizes; lia).
    assert (DJM : disjoint_from (puri_WA (P + 8)) (P + 400) 32) by (unfold puri_WA; cbn [disjoint_from]; repeat split; try exact I; clear - PLO; lia).
    assert (DJT : disjoint_from (puri_WA (P + 8)) A (cap + 1)) by (unfold puri_WA; cbn [disjoint_from]; repeat split; try exact I; clear - TFS PF1 PF2 ALO; lia).
    pose proof (pctx_stepF _ q' A len cap cur cur bs m m' stc CTX TOK QB RF LIVE1 MU0 WM' FK0 HW3 DJM DJT SC' (ex_intro _ ev' (conj CE' (conj CG' CS')))) as CTX1.
    assert (PU1 : pstatU m').
    { split; [apply (shw_frame_fs FI _ m m' _ _ S1 MU0 (fsw_W3 _ q' HW3)); left; pose proof (fsb_ok FI) as (B1 & _); lia|].
      split; [apply (shw_frame_fs FI _ m m' _ _ S2 MU0 (fsw_W3 _ q' HW3)); left; pose proof (fsb_ok FI) as (B1 & _); lia|].
      split; [apply (shw_frame_fs FI _ m m' _ _ S3 MU0 (fsw_W3 _ q' HW3)); left; pose proof (fsb_ok FI) as (B1 & _); lia|].
      split; [apply (shw_frame_fs FI _ m m' _ _ S4 MU0 (fsw_W3 _ q' HW3)); left; pose proof (fsb_ok FI) as (B1 & _); lia|].
      split; [exact G1'| exact G2']. }
    assert (MUa : munch ((lo, q) :: FSIV rWP) m m') by (clear - MU0 QB; eapply munch_weaken; [| exact MU0]; unfold rWP, puri_WA; sub_fp_solve).
    assert (FKa : fkeep FI rWP st m m') by (eapply (fkeep_weaken FI _ rWP stc st m m' FK0); [intros xo Ho; exact Ho| exact LSUB]).
    pose proof (fsenv_FSIV FI rWP lo q m m' FE MUa CLO rWP_fcls) as FEa.
    eapply (KK m' r junk'); try eassumption.
  Qed.

  Definition wmove (W : list ivl) (m m' : mem) : Prop := munch ((lo, q) :: FSIV W) m m' /\ wmono asegs m m' /\ fkeep FI W st m m'.
  #[using="Type"] Lemma wmove_refl : forall W m, wmove W m m.
  Proof. intros W m. split; [apply munch_refl|]. split; [apply wmono_refl| apply fkeep_refl]. Qed.
  #[using="Type"] Lemma wmove_trans : forall W m1 m2 m3, wmove W m1 m2 -> wmove W m2 m3 -> wmove W m1 m3.
  Proof.
    intros W m1 m2 m3 (A1 & A2 & A3) (B1 & B2 & B3).
    split; [exact (munch_trans _ _ _ _ A1 B1)|]. split; [exact (wmono_trans _ _ _ _ A2 B2)| exact (fkeep_trans FI _ _ _ _ _ A3 B3)].
  Qed.
  #[using="Type"] Lemma wmove_fk : forall (W0 W : list ivl) m m', munch ((lo, q) :: FSIV W0) m m' -> wmono asegs m m' -> fkeep FI W0 st m m' -> sub_fp W0 W -> wmove W m m'.
  Proof.
    intros W0 W m m' MU WM FK SUB. split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & H3 & H4). repeat split; try assumption. apply SUB. exact H4.
    - eapply (fkeep_weaken FI W0 W st st m m' FK SUB). intros g Hg; exact Hg.
  Qed.

  #[using="m0 POK RF0 mws MWL"] Lemma wmove_P : forall (W : list ivl) shd q' a b m m', pinvQS shd q' m -> munch [(a, b)]%Z m m' -> wmono asegs m m' ->
    P <= a -> a <= b -> b <= P + 504 -> inside W a (b - a) -> wmove W m m'.
  Proof.
    intros W shd q' a b m m' INV MU WM H1 H2 H3 HIN. destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (_ & HF & _). split; [clear - HF H1 H3 PF1 PF2; lia| exact I].
    - apply (fkeep_own W [(a, b)]%Z m m' shd q' INV MU). constructor; [cbn [fst snd]; split; [exact H2| right; left; exact HIN]| constructor].
  Qed.

  #[using="q lo st m0 POK RF0"] Lemma utext_stepP : forall (W : list ivl) m m' U n (ub : list byte), munch W m m' -> wmono asegs m m' -> Forall inP W ->
    0x609000 <= U -> (U + Z.of_nat (length ub) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U) -> shw m U n -> bytes_at asegs m U ub ->
    shw m' U n /\ bytes_at asegs m' U ub.
  Proof.
    intros W m m' U n ub MU WM HW ULO UFS SHU UB. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (AW : app_ivs W).
    { eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 PF1 PF2 B1 B2 B5. lia. }
    split; [exact (shw_frame _ _ _ _ _ SHU MU AW)|].
    eapply bytes_at_transport; [exact UB| exact MU|]. apply dj_inP; [exact HW| clear - UFS PF1 PF2; lia].
  Qed.

  Definition rWB : list ivl := [(P + 8, P + 8 + 216); (ERRNO_A, ERRNO_A + 4); (P + 432, P + 440); (P + 448, P + 452)]%Z.
  #[using="Type"] Lemma rWP_subB : sub_fp rWP rWB.
  Proof. unfold rWP, rWB. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _). repeat split; assumption. Qed.
  #[using="IC STACK_MALLOC_3 SET_SHADOW_F5 m0 POK RF0 FCO mws MWL"] Lemma segBQ : forall (q' A len cap cur U l pos : Z) (bs ustr slack junk : list byte) (mb ml vb vl ub ub0 : word)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatU m -> FSENV FI m -> tp = Z_to_bv 64 6190512 ->
    plocQ mb ml vb vl ub (wz l) m ->
    rw_cells asegs m (P + 432) [C8 ub0] -> rw_cells asegs m (P + 8) [CB 216 junk] -> rw_cells asegs m (P + 448) [C4 (wz pos)] ->
    Z.of_nat (length ustr) = l -> 0 <= l < 2^31 -> (- (U + l + 1)) mod 8 <= Z.of_nat (length slack) ->
    0x609000 <= U -> U + l + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
    (U + l + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U) ->
    (U + l + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U) ->
    shw m U (l + 1) -> bytes_at asegs m U (ustr ++ Z_to_bv 8 0 :: slack) ->
    (forall m' r pos' (junk' : list byte) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       ((r = 3 /\ pos' = pos) \/ (r = 0 /\ pos' = 4)) ->
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' ->
       rw_cells asegs m' (P + 432) [C8 (wz U)] -> rw_cells asegs m' (P + 8) [CB 216 junk'] -> rw_cells asegs m' (P + 448) [C4 (wz pos')] -> wmove rWB m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz U) x11 x12 x13 x14 x15 x16 x17 (wz (F + 32)) x28 x29 x30 x31) F_ (wz 0x8b618) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur U l pos bs ustr slack junk mb ml vb vl ub ub0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q
           INV CTX TOK PU FE TPV PL UBC UC PC UL ULR SLK ULO UHI UFS UBAND SHU UB KK.
    pose proof INV as (_ & (j0 & j224 & j256 & QC) & MI & _ & (QB & _) & _).
    pose proof CTX as (SC & _ & _ & SHP & _).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    assert (HACC : acc m (P + 432 + 8 - 1)) by (apply (proj1 SHP); lia).
    pose proof (munch_refl [(P + 432, P + 440)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    hide UC. hide PC. hide SC. hide UB.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 11 in
      destruct (AWAuto2.acc_loadw mm (P + 432) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
    destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR8 HACC.
    step. step. fix_lit_store.
    unhide UC. unhide PC. unhide SC. unhide UB.
    assert (HWc : Forall inP [(P + 432, P + 440)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJM : disjoint_from [(P + 432, P + 440)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
    assert (TR : forall X cs, rw_cells asegs m X cs -> (X + Z.of_nat (cells_size cs) <= P + 432 \/ P + 440 <= X) -> rw_cells asegs m1 X cs).
    { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU1| exact WM1| cbn [disjoint_from]; split; [exact HX| exact I]]. }
    pose proof (TR _ _ UC ltac:(simpl_sizes; lia)) as UC1. pose proof (TR _ _ PC ltac:(simpl_sizes; lia)) as PC1. pose proof (TR _ _ SC ltac:(simpl_sizes; lia)) as SC1.
    pose proof (pinv_stepP qshadowU eq_refl q' m m1 _ INV MU1 WM1 MI HWc) as INV1.
    pose proof (pctx_stepP _ A len cap cur cur bs m m1 CTX TOK MU1 WM1 HWc DJM SC1) as CTX1.
    pose proof (ploc_stepP _ _ _ _ _ _ _ m m1 PL MU1 WM1 HWc) as PL1.
    destruct (utext_stepP _ m m1 U (l + 1) (ustr ++ Z_to_bv 8 0 :: slack) MU1 WM1 HWc ULO ltac:(rewrite length_app; cbn [length]; clear - UFS UL; lia) SHU UB) as [SHU1 UB1].
    assert (PU1 : pstatU m1).
    { pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
      apply (pstatU_step _ m m1 PU MU1 WM1); (constructor; [| constructor]); [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 B1 B2 B5; lia| left; cbn [fst]; clear - PLO; lia]. }
    assert (FE1 : FSENV FI m1).
    { refine (fsenv_munch FI _ m m1 FE MU1 _). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). constructor; [apply fcls_in_fs; lia| constructor]. }
    pose proof (wmove_P rWB _ q' _ _ m m1 INV MU1 WM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold rWB; cbn [inside]; right; right; left; clear; lia)) as MV1.
    pose proof (ploc_cells _ _ _ _ _ _ m1 PL1) as (_ & _ & O2c & _).
    clear INV CTX PL UC PC SC SHU UB PU FE TR MU1 WM1.
    step. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ ULO. lia. }
    step. step. step.
    clear QC O2c.
    eapply (puri_callQ q' A len cap cur U l bs ustr slack junk m1); [exact INV1| exact CTX1| exact TOK| exact PU1| exact FE1| exact TPV| exact UC1
      | exact UL| exact ULR| exact SLK| exact ULO| exact UHI| exact UFS| exact UBAND| exact SHU1| exact UB1|].
    intros m2 r junk' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 CTX2 PU2 FE2 RES UC2 KEEP MU2 WM2 FK2.
    replace (ret_pc (Z_to_bv 64 0x8b63c)) with (Z_to_bv 64 0x8b63c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (UBC2 : rw_cells asegs m2 (P + 432) [C8 (wz U)]) by (apply (KEEP _ _ UBC); right; right; simpl_sizes; lia).
    assert (PC2 : rw_cells asegs m2 (P + 448) [C4 (wz pos)]) by (apply (KEEP _ _ PC1); right; right; simpl_sizes; lia).
    assert (MV2 : wmove rWB m m2) by (apply (wmove_trans _ _ _ _ MV1); exact (wmove_fk rWP rWB m1 m2 MU2 WM2 FK2 rWP_subB)).
    clear INV1 CTX1 PU1 FE1 UC1 SHU1 UB1 UBC PC1 SC1 PL1 KEEP MU2 WM2 FK2 MV1 MI.
    zstep. step. if_cases KR; zify_cond KR.
    -
      zstep.
      eapply (KK m2 3 pos junk'); [left; split; reflexivity| exact INV2| exact CTX2| exact UBC2| exact UC2| exact PC2| exact MV2].
    -
      assert (r = 1) by (destruct RES as [RES|RES]; [exact RES| exfalso; subst r; revert KR; change (Z.land (-108) 18446744073709551615) with 18446744073709551508; lia]). subst r. clear KR RES.
      pose proof CTX2 as (SC2 & _ & _ & SHP2 & _). pose proof INV2 as (_ & _ & MI2 & _).
      assert (HACC : acc m2 (P + 448 + 8 - 1)) by (apply (proj1 SHP2); lia).
      pose proof (munch_refl [(P + 448, P + 452)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 24 in
        destruct (AWAuto2.acc_loadw mm (P + 448) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR8 HACC.
      hide UBC2. hide UC2. hide SC2.
      zstep. step. fix_lit_store. step.
      unhide UBC2. unhide UC2. unhide SC2.
      assert (HWd : Forall inP [(P + 448, P + 452)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
      assert (DJN : disjoint_from [(P + 448, P + 452)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
      assert (TR2 : forall X cs, rw_cells asegs m2 X cs -> (X + Z.of_nat (cells_size cs) <= P + 448 \/ P + 452 <= X) -> rw_cells asegs m3 X cs).
      { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU3| exact WM3| cbn [disjoint_from]; split; [exact HX| exact I]]. }
      pose proof (TR2 _ _ UBC2 ltac:(simpl_sizes; lia)) as UBC3. pose proof (TR2 _ _ UC2 ltac:(simpl_sizes; lia)) as UC3. pose proof (TR2 _ _ SC2 ltac:(simpl_sizes; lia)) as SC3.
      pose proof (pinv_stepP qshadowU eq_refl q' m2 m3 _ INV2 MU3 WM3 MI2 HWd) as INV3.
      pose proof (pctx_stepP _ A len cap cur cur bs m2 m3 CTX2 TOK MU3 WM3 HWd DJN SC3) as CTX3.
      pose proof (wmove_P rWB _ q' _ _ m2 m3 INV2 MU3 WM3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold rWB; cbn [inside]; right; right; right; left; clear; lia)) as MV3.
      eapply (KK m3 0 4 junk'); [right; split; reflexivity| exact INV3| exact CTX3| exact UBC3| exact UC3| exact PC2| exact (wmove_trans _ _ _ _ MV2 MV3)].
  Qed.

  Definition pscrC (q' : Z) (w8 w16 w24 : word) (m : mem) : Prop :=
    exists j0 j224 j256,
      rw_cells asegs m q' [CB 24 j0; C8 w8; C8 w24; C8 w16; C8 (wz (Z.land (P + 4) 7 + 3)); C8 (wz (Z.land (P + 440) 7 + 3)); C8 (wz (Z.land (P + 448) 7 + 3));
                           C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (qSH (P + 4))); C8 (wz (P + 4)); C8 (wz (P + 8));
                           C8 (wz 18446744073708833343); C8 (wz F); C8 (wz F); C8 (wz (qSH (P + 432))); C8 (wz (P + 432));
                           C8 (wz (qSH (P + 440))); C8 (wz (P + 440)); C8 (wz (F + 64)); C8 (wz METHOD_TAB_A); C8 (wz (qSH (P + 488)));
                           C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32)); C8 (wz 2147450880);
                           CB 24 j224; C8 (wz F); CB 24 j256].
  #[using="Type"] Lemma pscrC_split : forall q' m, pscrQ q' m -> exists w8 w16 w24, pscrC q' w8 w16 w24 m.
  Proof.
    intros q' m (j0 & j224 & j256 & QC). unfold pscrC.
    splitcb QC 0%nat [24; 8; 8; 8]%nat. recell QC 1%nat. recell QC 2%nat. recell QC 3%nat. name_junk QC.
    do 6 eexists. exact QC.
  Qed.
  #[using="Type"] Lemma pscrC_join : forall q' w8 w16 w24 m, pscrC q' w8 w16 w24 m -> pscrQ q' m.
  Proof.
    intros q' w8 w16 w24 m (j0 & j224 & j256 & QC). unfold H_pparse_seg.pscrQ.
    pose proof (rw_cells_merge asegs m q' [] [CB 24 j0; C8 w8; C8 w24; C8 w16]
                  [C8 (wz (Z.land (P + 4) 7 + 3)); C8 (wz (Z.land (P + 440) 7 + 3)); C8 (wz (Z.land (P + 448) 7 + 3));
                           C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (qSH (P + 4))); C8 (wz (P + 4)); C8 (wz (P + 8));
                           C8 (wz 18446744073708833343); C8 (wz F); C8 (wz F); C8 (wz (qSH (P + 432))); C8 (wz (P + 432));
                           C8 (wz (qSH (P + 440))); C8 (wz (P + 440)); C8 (wz (F + 64)); C8 (wz METHOD_TAB_A); C8 (wz (qSH (P + 488)));
                           C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32)); C8 (wz 2147450880);
                           CB 24 j224; C8 (wz F); CB 24 j256] QC) as M.
    cbn [app cells_size csize Nat.add] in M. do 3 eexists. exact M.
  Qed.

  Definition pslk (A cap : Z) (sl : list byte) (m : mem) : Prop :=
    bytes_at asegs m (A + (cap + 1)) sl /\ Z.of_nat (length sl) <= 7 /\ exists kE, A + (cap + 1) + Z.of_nat (length sl) = 8 * kE.
  #[using="Type"] Lemma pslk_step : forall (W : list ivl) A cap sl m m', pslk A cap sl m -> munch W m m' ->
    disjoint_from W (A + (cap + 1)) (Z.of_nat (length sl)) -> pslk A cap sl m'.
  Proof. intros W A cap sl m m' (B & L7 & KE) MU DJ. split; [| exact (conj L7 KE)]. eapply bytes_at_transport; [exact B| exact MU| exact DJ]. Qed.

  #[using="q P st POK"] Lemma slk_apart : forall A len cap (sl : list byte), txt_okA A len cap -> Z.of_nat (length sl) <= 7 -> (exists kE, A + (cap + 1) + Z.of_nat (length sl) = 8 * kE) ->
    let X := A + (cap + 1) in let n := Z.of_nat (length sl) in
    X + n <= lo /\ (X + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= X) /\ (X + n <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= X) /\ 0x5e7510 <= X.
  Proof.
    intros A len cap sl TOK L7 (kE & KE) X n. subst X n. tokA TOK. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    assert (FSB8 : FSB FI mod 8 = 0) by (clear - B4; Z.div_mod_to_equations; lia).
    split; [clear - AHI CLO L7; lia|].
    split; [destruct TFS as [T1|T1]; [left; clear - T1 FSB8 KE L7; Z.div_mod_to_equations; lia| right; clear - T1 LENC; lia]|].
    split; [| clear - ALO LENC; lia].
    unfold sh, SHADOW_OFF. clear - TBAND B1 B2 B5 ACR L7 LENC ALO AHI. Z.div_mod_to_equations. lia.
  Qed.

  #[using="st m0 POK RF0 mws MWL"] Lemma pctx_stepTx : forall A len cap cur (bs bs' : list byte) k m m',
    pctx A len cap cur bs m -> txt_okA A len cap -> munch [(A + k, A + k + 1)]%Z m m' -> wmono asegs m m' -> 0 <= k <= cap ->
    rw_cells asegs m' A [CB (Z.to_nat (cap + 1)) bs'] -> pctx A len cap cur bs' m'.
  Proof.
    intros A len cap cur bs bs' k m m' (SC & MBC & _ & SHP & SHA & SHSEP & SHF1' & SHF2' & SHZ & SHR & (ev & CLOW) & SHE) TOK MU WM HK TXT'.
    tokA TOK. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (AW : app_ivs [(A + k, A + k + 1)]%Z).
    { constructor; [| constructor]. unfold app_iv, SH_HI. cbn [fst snd]. clear - TBAND HK ALO. lia. }
    assert (DJ : forall X n, P <= X -> X + n <= P + 504 -> disjoint_from [(A + k, A + k + 1)]%Z X n).
    { intros X n H1 H2. cbn [disjoint_from]. split; [clear - H1 H2 TFS PF1 PF2 HK; lia| exact I]. }
    unfold H_pparse_seg.pctx.
    split; [eapply rw_cells_transport; [exact SC| exact MU| exact WM| apply DJ; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MU| exact WM| apply DJ; unfold mbuf_cells; simpl_sizes; lia]|].
    split; [exact TXT'|].
    split; [exact (shw_frame _ _ _ _ _ SHP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHA MU AW)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF1' MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF2' MU AW)|].
    assert (FW : Forall (fsw_iv FI) [(A + k, A + k + 1)]%Z) by (eapply Forall_impl; [| exact AW]; intros iv H; left; exact H).
    split; [exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exists ev; apply (clow_stepW _ ev m m' CLOW MU WM); constructor; [cbn [fst]; clear - ALO HK; lia| constructor]|].
    exact (shw_frame _ _ _ _ _ SHE MU AW).
  Qed.
  #[using="mws MWL"] Lemma outX_text : forall A len cap k, txt_okA A len cap -> 0 <= k <= cap -> outX (A + k, A + k + 1).
  Proof.
    intros A len cap k TOK HK. tokA TOK. unfold H_pparse_seg.outX. cbn [fst snd].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - TFS HK; lia| clear - TBAND HK; lia].
  Qed.

  Definition inW2 (iv : ivl) : Prop := inP iv \/ inFJ iv \/ inER iv.
  #[using="q lo m0 POK RF0"] Lemma dj_slk : forall (W : list ivl) A len cap (sl : list byte), txt_okA A len cap -> Z.of_nat (length sl) <= 7 ->
    (exists kE, A + (cap + 1) + Z.of_nat (length sl) = 8 * kE) -> Forall inW2 W -> disjoint_from W (A + (cap + 1)) (Z.of_nat (length sl)).
  Proof.
    intros W A len cap sl TOK L7 KE HW. destruct (slk_apart A len cap sl TOK L7 KE) as (S1 & S2 & S3 & S4).
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    induction W as [|[a b] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold inW2, H_pparse_seg.inP, H_pparse_seg.inFJ, H_pparse_seg.inER in HO. cbn [fst snd] in HO.
    destruct HO as [HO|[HO|HO]]; [clear - HO S2 PF1 PF2| clear - HO S2 FLO FHI| clear - HO S4]; lia.
  Qed.
  #[using="q lo m0 POK RF0"] Lemma pslk_stepW : forall (W : list ivl) A len cap sl m m', txt_okA A len cap -> pslk A cap sl m -> munch W m m' -> Forall inW2 W -> pslk A cap sl m'.
  Proof. intros W A len cap sl m m' TOK SLK MU HW. pose proof SLK as (_ & L7 & KE). exact (pslk_step W A cap sl m m' SLK MU (dj_slk W A len cap sl TOK L7 KE HW)). Qed.
  #[using="q m0 POK RF0"] Lemma pslk_stepF : forall (W : list ivl) qx A len cap sl m m', txt_okA A len cap -> pslk A cap sl m -> munch ((lo, qx) :: FSIV W) m m' -> Forall inW2 W -> pslk A cap sl m'.
  Proof.
    intros W qx A len cap sl m m' TOK SLK MU HW. pose proof SLK as (_ & L7 & KE). destruct (slk_apart A len cap sl TOK L7 KE) as (S1 & S2 & S3 & S4).
    apply (pslk_step _ A cap sl m m' SLK MU). cbn [disjoint_from]. split; [left; exact S1|]. split; [exact S2|]. split; [exact S3|]. exact (dj_slk W A len cap sl TOK L7 KE HW).
  Qed.
  #[using="mws MWL"] Lemma rWP_W2 : Forall inW2 rWP.
  Proof.
    unfold rWP, inW2, H_pparse_seg.inP, H_pparse_seg.inER.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [right; right; cbn [fst snd]; lia| constructor].
  Qed.
  #[using="Type"] Lemma inP_W2 : forall (W : list ivl), Forall inP W -> Forall inW2 W.
  Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv Hiv. left. exact Hiv. Qed.

  Definition keepC (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 8)
       \/ (P + 224 <= X /\ X + Z.of_nat (cells_size cs) <= P + 432) \/ (P + 440 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.
  Definition rWC (A cap : Z) : list ivl :=
    [(P + 4, P + 8); (P + 8, P + 8 + 216); (ERRNO_A, ERRNO_A + 4); (P + 276, P + 280); (P + 280, P + 284); (P + 432, P + 440); (P + 440, P + 444);
     (P + 448, P + 452); (A, A + (cap + 1))]%Z.
  #[using="Type"] Lemma rWP_subC : forall A cap, sub_fp rWP (rWC A cap).
  Proof. intros A cap. unfold rWP, rWC. intros x Hx. cbn [outside] in *. destruct Hx as (_ & H2 & H3 & _). repeat split; assumption. Qed.

  #[using="IC STACK_MALLOC_3 SET_SHADOW_F5 m0 POK RF0 FCO MWL"] Lemma urlCQ : forall (q' A len cap cur U l : Z) (bs ustr slack junk sl : list byte) (mb ml vb vl ub ub0 : word)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatU m -> pstatR m -> pslk A cap sl m -> FSENV FI m -> tp = Z_to_bv 64 6190512 ->
    plocQ mb ml vb vl ub (wz l) m ->
    rw_cells asegs m (P + 432) [C8 ub0] -> rw_cells asegs m (P + 8) [CB 216 junk] ->
    Z.of_nat (length ustr) = l -> 0 <= l < 2^31 -> (- (U + l + 1)) mod 8 <= Z.of_nat (length slack) ->
    0x609000 <= U -> U + l + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
    (U + l + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U) ->
    (U + l + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U) ->
    shw m U (l + 1) -> bytes_at asegs m U (ustr ++ Z_to_bv 8 0 :: slack) ->
    (forall m' (junk' : list byte) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' ->
       rw_cells asegs m' (P + 432) [C8 (wz U)] -> rw_cells asegs m' (P + 8) [CB 216 junk'] -> keepC m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    (forall m' (junk' : list byte) y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> pstatR m' -> pslk A cap sl m' -> FSENV FI m' ->
       rw_cells asegs m' (P + 432) [C8 (wz U)] -> rw_cells asegs m' (P + 8) [CB 216 junk'] -> keepC m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz 1) (wz 1) y12 y13 y14 y15 y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz 0x8b44c) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz U) x11 x12 x13 x14 x15 x16 x17 (wz 4) x28 x29 x30 x31) F_ (wz 0x8b41c) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur U l bs ustr slack junk sl mb ml vb vl ub ub0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q
           INV CTX TOK PU PS SLKF FE TPV PL UBC UC UL ULR SLK ULO UHI UFS UBAND SHU UB KF KO.
    pose proof INV as (_ & (j0 & j224 & j256 & QC) & MI & _ & (QB & _) & _).
    pose proof CTX as (SC & _ & _ & SHP & _).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    assert (HACC : acc m (P + 432 + 8 - 1)) by (apply (proj1 SHP); lia).
    pose proof (munch_refl [(P + 432, P + 440)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    hide UC. hide SC. hide UB.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 11 in
      destruct (AWAuto2.acc_loadw mm (P + 432) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
    destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR8 HACC.
    step. step. fix_lit_store.
    unhide UC. unhide SC. unhide UB.
    assert (HWc : Forall inP [(P + 432, P + 440)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJM : disjoint_from [(P + 432, P + 440)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
    assert (TR : forall X cs, rw_cells asegs m X cs -> (X + Z.of_nat (cells_size cs) <= P + 432 \/ P + 440 <= X) -> rw_cells asegs m1 X cs).
    { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU1| exact WM1| cbn [disjoint_from]; split; [exact HX| exact I]]. }
    pose proof (TR _ _ UC ltac:(simpl_sizes; lia)) as UC1. pose proof (TR _ _ SC ltac:(simpl_sizes; lia)) as SC1.
    pose proof (pinv_stepP qshadowU eq_refl q' m m1 _ INV MU1 WM1 MI HWc) as INV1.
    pose proof (pctx_stepP _ A len cap cur cur bs m m1 CTX TOK MU1 WM1 HWc DJM SC1) as CTX1.
    pose proof (ploc_stepP _ _ _ _ _ _ _ m m1 PL MU1 WM1 HWc) as PL1.
    pose proof (pstatR_stepP _ m m1 PS MU1 WM1 HWc) as PS1.
    pose proof (pslk_stepW _ A len cap sl m m1 TOK SLKF MU1 (inP_W2 _ HWc)) as SLK1.
    destruct (utext_stepP _ m m1 U (l + 1) (ustr ++ Z_to_bv 8 0 :: slack) MU1 WM1 HWc ULO ltac:(rewrite length_app; cbn [length]; clear - UFS UL; lia) SHU UB) as [SHU1 UB1].
    assert (PU1 : pstatU m1).
    { pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
      apply (pstatU_step _ m m1 PU MU1 WM1); (constructor; [| constructor]); [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 B1 B2 B5; lia| left; cbn [fst]; clear - PLO; lia]. }
    assert (FE1 : FSENV FI m1).
    { refine (fsenv_munch FI _ m m1 FE MU1 _). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). constructor; [apply fcls_in_fs; lia| constructor]. }
    pose proof (wmove_P (rWC A cap) _ q' _ _ m m1 INV MU1 WM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold rWC; cbn [inside]; do 5 right; left; clear; lia)) as MV1.
    pose proof (ploc_cells _ _ _ _ _ _ m1 PL1) as (_ & _ & O2c & _).
    clear INV CTX PL UC SC SHU UB PU PS SLKF FE MU1 WM1.
    step. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ ULO. lia. }
    step. step. step.
    clear QC O2c.
    eapply (puri_callQ q' A len cap cur U l bs ustr slack junk m1); [exact INV1| exact CTX1| exact TOK| exact PU1| exact FE1| exact TPV| exact UC1
      | exact UL| exact ULR| exact SLK| exact ULO| exact UHI| exact UFS| exact UBAND| exact SHU1| exact UB1|].
    intros m2 r junk' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 CTX2 PU2 FE2 RES UC2 KEEP MU2 WM2 FK2.
    replace (ret_pc (Z_to_bv 64 0x8b440)) with (Z_to_bv 64 0x8b440) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (UBC2 : rw_cells asegs m2 (P + 432) [C8 (wz U)]) by (apply (KEEP _ _ UBC); right; right; simpl_sizes; lia).
    assert (MV2 : wmove (rWC A cap) m m2) by (apply (wmove_trans _ _ _ _ MV1); exact (wmove_fk rWP (rWC A cap) m1 m2 MU2 WM2 FK2 (rWP_subC A cap))).
    assert (KC : keepC m m2).
    { destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PAF & _).
      intros X cs HC1 HX. apply KEEP; [apply TR; [exact HC1| clear - HX PAF; lia]| clear - HX; lia]. }
    pose proof (pstatR_stepF rWP q m1 m2 PS1 MU2 WM2 rWP_ok) as PS2.
    pose proof (pslk_stepF rWP q A len cap sl m1 m2 TOK SLK1 MU2 rWP_W2) as SLK2.
    clear INV1 CTX1 PU1 FE1 UC1 SHU1 UB1 UBC SC1 PL1 PS1 SLK1 KEEP TR MU2 WM2 FK2 MV1 MI.
    zstep. zstep. step. if_cases KR; zify_cond KR.
    -
      eapply (KF m2 junk'); [exact INV2| exact CTX2| exact UBC2| exact UC2| exact KC| exact MV2].
    - assert (r = 1) by (destruct RES as [RES|RES]; [exact RES| exfalso; subst r; revert KR; change (Z.land (-108) 18446744073709551615) with 18446744073709551508; lia]). subst r.
      eapply (KO m2 junk'); [exact INV2| exact CTX2| exact PS2| exact SLK2| exact FE2| exact UBC2| exact UC2| exact KC| exact MV2].
  Qed.

  #[using="m0 POK RF0 mws MWL"] Lemma wmove_S : forall (W : list ivl) shd q' a b m m', pinvQS shd q' m -> munch [(a, b)]%Z m m' -> wmono asegs m m' -> q' <= a -> a <= b -> b <= q -> wmove W m m'.
  Proof.
    intros W shd q' a b m m' INV MU WM H1 H2 H3. pose proof INV as (_ & _ & _ & _ & (QB & _) & _). pose proof POK as POK'. pqokA POK'.
    split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (HS & _). split; [clear - HS H1 H3 LO QB; lia| exact I].
    - apply (fkeep_own W [(a, b)]%Z m m' shd q' INV MU). constructor; [cbn [fst snd]; split; [exact H2| left; clear - H1 CLO LO QB; lia]| constructor].
  Qed.
  #[using="mws MWL"] Lemma sstore_T : forall q' a b m m', munch [(a, b)]%Z m m' -> q' <= a -> b <= q' + 280 -> lo <= q' -> munch ((lo, q' + 280) :: []) m m'.
  Proof. intros q' a b m m' MU H1 H2 H3. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (HS & _). split; [lia| exact I]. Qed.
  #[using="mws MWL"] Lemma sstore_rWT : forall q' a b m m', munch [(a, b)]%Z m m' -> q' <= a -> b <= q' + 280 -> lo <= q' -> munch (rWT q') m m'.
  Proof. intros q' a b m m' MU H1 H2 H3. eapply munch_weaken; [| exact MU]. unfold rWT. intros x Hx. cbn [outside] in *. destruct Hx as (HS & _). split; [lia| exact I]. Qed.

  #[using="FI q P st POK mws MWL"] Lemma fcell_S : forall a b m m' X cs, munch [(a, b)]%Z m m' -> wmono asegs m m' -> lo <= a -> X + Z.of_nat (cells_size cs) <= alloc_ceiling ->
    rw_cells asegs m X cs -> rw_cells asegs m' X cs.
  Proof.
    intros a b m m' X cs MU WM H1 H2 HC1. pose proof POK as POK'. pqokA POK'.
    eapply rw_cells_transport; [exact HC1| exact MU| exact WM|]. cbn [disjoint_from]. split; [left; lia| exact I].
  Qed.
  #[using="q P m0 POK RF0 mws MWL"] Lemma ploc_S : forall mb ml vb vl ub ul a b m m', plocQ mb ml vb vl ub ul m -> munch [(a, b)]%Z m m' -> wmono asegs m m' -> lo <= a -> plocQ mb ml vb vl ub ul m'.
  Proof.
    intros mb ml vb vl ub ul a b m m' (j1 & j2 & j3 & HA) MU WM H1. exists j1, j2, j3.
    destruct eframe_facts as (_ & FHI & _). pose proof (fsb_ok FI) as (_ & B2 & _).
    apply (fcell_S a b m m' _ _ MU WM H1); [simpl_sizes; clear - FHI B2; lia| exact HA].
  Qed.
  #[using="q P st POK"] Lemma pslk_S : forall a b A len cap sl m m', txt_okA A len cap -> pslk A cap sl m -> munch [(a, b)]%Z m m' -> lo <= a -> pslk A cap sl m'.
  Proof.
    intros a b A len cap sl m m' TOK SLK MU H1. pose proof SLK as (_ & L7 & KE). destruct (slk_apart A len cap sl TOK L7 KE) as (S1 & _).
    apply (pslk_step _ A cap sl m m' SLK MU). cbn [disjoint_from]. split; [left; clear - S1 H1; lia| exact I].
  Qed.

  Definition keepM (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 440)
       \/ (P + 444 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.

  #[using="m0 RF0 mws MWL"] Lemma wmove_In : forall (W : list ivl) shd q' a b m m', pinvQS shd q' m -> munch [(a, b)]%Z m m' -> wmono asegs m m' -> a <= b -> inside W a (b - a) -> wmove W m m'.
  Proof.
    intros W shd q' a b m m' INV MU WM H2 HIN.
    split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (_ & _ & _ & HW). split; [| exact I].
      intros Hr. exact (inside_not_outside W a (b - a) x HIN ltac:(lia) HW).
    - apply (fkeep_own W [(a, b)]%Z m m' shd q' INV MU). constructor; [cbn [fst snd]; split; [exact H2| right; left; exact HIN]| constructor].
  Qed.

  #[using="IC STACK_MALLOC_0 m0 POK RF0 FCO MWL"] Lemma mapCQ : forall (q' A len cap cur o1 l1 : Z) (bs sl : list byte) (vb vl ub ul e : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatR m -> pslk A cap sl m -> FSENV FI m ->
    plocQ (wz (A + o1)) (wz l1) vb vl ub ul m -> 0 <= o1 -> 1 <= l1 -> o1 + l1 <= cap + 1 ->
    rw_cells asegs m (P + 440) [C4 e] ->
    (forall m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> rw_cells asegs m' (P + 440) [C4 (wz 501)] -> keepM m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    (forall m' idx (w24 : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       0 <= idx < 11 -> pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> pstatR m' -> pslk A cap sl m' -> pscrC q' (wz idx) (wz METHOD_TAB_A) w24 m' ->
       rw_cells asegs m' (P + 440) [C4 e] -> keepM m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz idx) y11 y12 y13 y14 y15 y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz 0x8b478) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz 0x8b44c) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur o1 l1 bs sl vb vl ub ul e x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV CTX TOK PS SLK FE PL O0 L1 OL EC KF KO.
    pose proof INV as (ST & SCRQ & MI & _ & (QB & _) & _).
    destruct (pscrC_split q' m SCRQ) as (w8 & w16 & w24 & (j0 & j224 & j256 & QC)).
    pose proof (ploc_cells _ _ _ _ _ _ m PL) as (O1c & _).
    pose proof CTX as (SC & _).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    pose proof (munch_refl [(q' + 40, q' + 48)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    hide EC.
    step. step. step. zstep. zstep. zstep. zstep. step. fix_lit_store.
    unhide EC.
    assert (LQ : lo <= q') by (clear - LO QB; lia).
    assert (SCR1 : pscrC q' w8 (wz METHOD_TAB_A) w24 m1) by (exists j0, j224, j256; exact QC).
    pose proof (pinv_stepT qshadowU eq_refl q' m m1 [] INV (sstore_T q' _ _ m m1 MU1 ltac:(lia) ltac:(lia) LQ) WM1 MI (Forall_nil _) ST (pscrC_join q' _ _ _ m1 SCR1)) as INV1.
    pose proof (pctx_stepT [] q' A len cap cur cur bs m m1 CTX TOK QB (sstore_T q' _ _ m m1 MU1 ltac:(lia) ltac:(lia) LQ) WM1 (Forall_nil _) I SC) as CTX1.
    pose proof (pstatR_T q' m m1 ltac:(lia) PS (sstore_rWT q' _ _ m m1 MU1 ltac:(lia) ltac:(lia) LQ) WM1) as PS1.
    pose proof (pslk_S _ _ A len cap sl m m1 TOK SLK MU1 ltac:(lia)) as SLK1.
    pose proof (ploc_S _ _ _ _ _ _ _ _ m m1 PL MU1 WM1 ltac:(lia)) as PL1.
    pose proof (fcell_S _ _ m m1 (P + 440) [C4 e] MU1 WM1 ltac:(lia) ltac:(simpl_sizes; lia) EC) as EC1.
    assert (FE1 : FSENV FI m1) by (refine (fsenv_munch FI _ m m1 FE MU1 _); constructor; [apply fcls_stack; clear - CLO LQ; lia| constructor]).
    pose proof (wmove_S (rWC A cap) _ q' _ _ m m1 INV MU1 WM1 ltac:(lia) ltac:(lia) ltac:(lia)) as MV1.
    assert (KM1 : keepM m m1).
    { destruct eframe_facts as (_ & FHI & _). pose proof (fsb_ok FI) as (_ & B2 & _).
      intros X cs HC1 HX. apply (fcell_S _ _ m m1 X cs MU1 WM1 ltac:(lia)); [clear - HX FHI B2 PHI; lia| exact HC1]. }
    clear INV CTX PS SLK PL EC FE ST SC MI SCRQ.
    step.
    eapply (map_callQ q' A len cap cur o1 l1 bs m1); [exact INV1| exact CTX1| exact TOK| exact PS1| exact FE1| exact O0| exact L1| exact OL|].
    intros m2 r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 CTX2 PS2 FE2 KEEP KS RES MUa WMa FKa.
    replace (ret_pc (Z_to_bv 64 0x8b470)) with (Z_to_bv 64 0x8b470) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (KS _ _ QC ltac:(lia) ltac:(simpl_sizes; lia)) as QC2.
    assert (EC2 : rw_cells asegs m2 (P + 440) [C4 e]) by (apply (KEEP _ _ EC1); right; simpl_sizes; lia).
    pose proof (pslk_stepF [] q A len cap sl m1 m2 TOK SLK1 MUa (Forall_nil _)) as SLK2.
    assert (MV2 : wmove (rWC A cap) m m2) by (apply (wmove_trans _ _ _ _ MV1); apply (wmove_fk [] (rWC A cap) m1 m2 MUa WMa FKa); intros x _; exact I).
    assert (KM2 : keepM m m2).
    { intros X cs HC1 HX. apply KEEP; [apply KM1; [exact HC1| exact HX]|]. clear - HX. lia. }
    clear INV1 CTX1 PS1 FE1 SLK1 PL1 EC1 KEEP KS MUa WMa FKa MV1 KM1 QC MU1 WM1.
    step. if_cases KB; zify_cond KB.
    -
      assert (r = -1) by (destruct RES as [RES|RES]; [exact RES| exfalso; change 18446744073709551615 with (Z.ones 64) in KB; rewrite Z.land_ones in KB by lia; rewrite Z.mod_small in KB by lia; lia]).
      subst r. clear KB RES.
      pose proof CTX2 as (SC2 & _ & _ & SHP2 & _). pose proof INV2 as (_ & _ & MI2 & _).
      assert (HACC : acc m2 (P + 440 + 8 - 1)) by (apply (proj1 SHP2); lia).
      pose proof (munch_refl [(P + 440, P + 444)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 10 in
        destruct (AWAuto2.acc_loadw mm (P + 440) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR8 HACC.
      step. clear QC2. hide SC2.
      zstep. step. fix_lit_store. step.
      unhide SC2.
      assert (HWc : Forall inP [(P + 440, P + 444)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
      assert (DJM : disjoint_from [(P + 440, P + 444)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
      assert (TR : forall X cs, rw_cells asegs m2 X cs -> (X + Z.of_nat (cells_size cs) <= P + 440 \/ P + 444 <= X) -> rw_cells asegs m3 X cs).
      { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU3| exact WM3| cbn [disjoint_from]; split; [exact HX| exact I]]. }
      pose proof (TR _ _ SC2 ltac:(simpl_sizes; lia)) as SC3.
      pose proof (pinv_stepP qshadowU eq_refl q' m2 m3 _ INV2 MU3 WM3 MI2 HWc) as INV3.
      pose proof (pctx_stepP _ A len cap cur cur bs m2 m3 CTX2 TOK MU3 WM3 HWc DJM SC3) as CTX3.
      pose proof (wmove_P (rWC A cap) _ q' _ _ m2 m3 INV2 MU3 WM3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold rWC; cbn [inside]; do 6 right; left; clear; lia)) as MV3.
      eapply (KF m3); [exact INV3| exact CTX3| exact EC2| | exact (wmove_trans _ _ _ _ MV2 MV3)].
      destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PAF & _).
      intros X cs HC1 HX. apply TR; [apply KM2; [exact HC1| exact HX]| clear - HX PAF; lia].
    -
      assert (RR : 0 <= r < 11) by (destruct RES as [RES|RES]; [exfalso; subst r; revert KB; change (Z.land (-1) 18446744073709551615) with 18446744073709551615; lia| exact RES]).
      clear KB RES.
      pose proof INV2 as (ST2 & _ & MI2 & _). pose proof CTX2 as (SC2 & _).
      pose proof (munch_refl [(q' + 24, q' + 32)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
      hide EC2.
      step. fix_lit_store.
      unhide EC2.
      assert (SCR3 : pscrC q' (wz r) (wz METHOD_TAB_A) w24 m3) by (exists j0, j224, j256; exact QC2).
      pose proof (pinv_stepT qshadowU eq_refl q' m2 m3 [] INV2 (sstore_T q' _ _ m2 m3 MU3 ltac:(lia) ltac:(lia) LQ) WM3 MI2 (Forall_nil _) ST2 (pscrC_join q' _ _ _ m3 SCR3)) as INV3.
      pose proof (pctx_stepT [] q' A len cap cur cur bs m2 m3 CTX2 TOK QB (sstore_T q' _ _ m2 m3 MU3 ltac:(lia) ltac:(lia) LQ) WM3 (Forall_nil _) I SC2) as CTX3.
      pose proof (pstatR_T q' m2 m3 ltac:(lia) PS2 (sstore_rWT q' _ _ m2 m3 MU3 ltac:(lia) ltac:(lia) LQ) WM3) as PS3.
      pose proof (pslk_S _ _ A len cap sl m2 m3 TOK SLK2 MU3 ltac:(lia)) as SLK3.
      pose proof (fcell_S _ _ m2 m3 (P + 440) [C4 e] MU3 WM3 ltac:(lia) ltac:(simpl_sizes; lia) EC2) as EC3.
      pose proof (wmove_S (rWC A cap) _ q' _ _ m2 m3 INV2 MU3 WM3 ltac:(lia) ltac:(lia) ltac:(lia)) as MV3.
      eapply (KO m3 r w24); [exact RR| exact INV3| exact CTX3| exact PS3| exact SLK3| exact SCR3| exact EC3| | exact (wmove_trans _ _ _ _ MV2 MV3)].
      destruct eframe_facts as (_ & FHI & _). pose proof (fsb_ok FI) as (_ & B2 & _).
      intros X cs HC1 HX. apply (fcell_S _ _ m2 m3 X cs MU3 WM3 ltac:(lia)); [clear - HX FHI B2 PHI; lia| apply KM2; [exact HC1| exact HX]].
  Qed.

  Definition inPE (iv : ivl) : Prop := inP iv \/ inER iv.
  #[using="Type"] Lemma dj_inPE : forall (W : list ivl) X n, Forall inPE W -> (X + n <= P \/ P + 504 <= X) -> 0x5e7510 <= X -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX HE; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. split; [| exact (IH X n HW' HX HE)].
    unfold inPE, H_pparse_seg.inP, H_pparse_seg.inER in HO. cbn [fst snd] in HO. destruct HO as [HO|HO]; [clear - HO HX| clear - HO HE]; lia.
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma pinv_stepE : forall shd, Z.of_nat (cells_size shd) = 16 -> forall q' m m' (W : list ivl),
    pinvQS shd q' m -> munch ((lo, q') :: W) m m' -> wmono asegs m m' -> mem_inv asegs m' -> asan_env asegs m' -> Forall inPE W ->
    stk asegs m' lo q' -> pinvQS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & (j0 & j224 & j256 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' AE' HW ST'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (SH2 : sh (FSB FI) + A0_FS_SHSIZE <= lo /\ 0x609000 <= sh (FSB FI)).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 FSB5 ACR CLO. Z.div_mod_to_equations. lia. }
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJ : forall X n, (X + n <= P \/ P + 504 <= X) -> (X + n <= lo \/ q' <= X) -> 0x5e7510 <= X -> disjoint_from ((lo, q') :: W) X n).
    { intros X n HX HY HE. cbn [disjoint_from]. split; [exact HY| exact (dj_inPE W X n HW HX HE)]. }
    split; [exact ST'|].
    split; [exists j0, j224, j256; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; [right; clear - PHI CLO LO QB; lia| right; lia| clear - CLO LO QB ACR; lia]]|].
    split; [exact MI'|]. split; [exact AE'|].
    split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM| apply DJ; [right; clear - PHI CLO LO QB; lia| right; lia| clear - CLO LO QB ACR; lia]]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MU| exact WM| apply DJ; simpl_sizes; [right; clear - PHI CLO LO QB; lia| right; clear - QB; lia| clear - CLO LO QB ACR; lia]]|].
    split; [exists w0; eapply rw_cells_transport; [exact FH| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PAF; lia| left; clear - FHI FSB2 CLO; lia| clear - FLO FSB1; lia]]|].
    split; [exists jf; eapply rw_cells_transport; [exact FT1| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PAF; lia| left; clear - FHI FSB2 CLO; lia| clear - FLO FSB1; lia]]|].
    split; [eapply rw_cells_transport; [exact FT2| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PAF; lia| left; clear - FHI FSB2 CLO; lia| clear - FLO FSB1; lia]]|].
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PSx.
    split; [eapply rw_cells_transport; [exact SHF| exact MU| exact WM| apply DJ; rewrite ?HSZ; [clear - PSx; lia| left; clear - SHF2 SH2; lia| clear - SHF1 SH2; lia]]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| apply DJ; simpl_sizes; [clear - PAFL; lia| left; clear - FLHI FSB2 CLO; lia| clear - FLLO FSB1; lia]]|].
    exists stc. split; [| exact LIVE1].
    apply (rfake_frame FI stc m m' _ RF MU WM). constructor.
    - left. cbn [fst snd]. split; [right; clear - FSB2 CLO; lia| right; clear - SH2; lia].
    - eapply Forall_impl; [| exact HW]. intros [a b] HO. unfold inPE, H_pparse_seg.inP, H_pparse_seg.inER in HO. cbn [fst snd] in *.
      destruct HO as [(H1 & H2 & H3)|(H1 & H2 & H3)].
      + right; left. apply (lb_mono (fs_live FI st)); [apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact LSUB].
      + left. split; [left; clear - H3 FSB1; lia| left; clear - H3 SH2; lia].
  Qed.
  #[using="st m0 POK RF0 mws MWL"] Lemma pctx_stepE : forall (W : list ivl) q' A len cap cur bs m m',
    pctx A len cap cur bs m -> txt_okA A len cap -> q + -400 <= q' <= q + -384 -> munch ((lo, q') :: W) m m' -> wmono asegs m m' -> Forall inPE W ->
    disjoint_from W (P + 400) 32 ->
    rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)] -> (exists ev', clow canary ev' m') ->
    pctx A len cap cur bs m'.
  Proof.
    intros W q' A len cap cur bs m m' (_ & MBC & TXT & SHP & SHA & SHSEP & SHF1 & SHF2 & SHZ & SHR & _ & SHE) TOK QB MU WM HW DJM SC' CLOW'.
    tokA TOK. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (AW : app_ivs ((lo, q') :: W)).
    { constructor; [unfold app_iv, SH_HI; cbn [fst snd]; right; clear - CLO ACR; lia|].
      eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold inPE, H_pparse_seg.inP, H_pparse_seg.inER in HO. cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd].
      destruct HO as [(H1 & H2 & H3)|(H1 & H2 & H3)]; [clear - H1 H2 H3 PF1 PF2 B1 B2 B5| clear - H1 H2 H3]; lia. }
    unfold H_pparse_seg.pctx.
    split; [exact SC'|].
    split; [eapply rw_cells_transport; [exact MBC| exact MU| exact WM| unfold mbuf_cells; simpl_sizes; cbn [disjoint_from]; split; [left; clear - PHI CLO; lia| unfold mbuf_cells in DJM; simpl_sizes; exact DJM]]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MU| exact WM| cbn [disjoint_from]; split; [left; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - AHI CLO; lia|
              apply dj_inPE; [exact HW| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - TFS PF1 PF2; lia| clear - ALO; lia]]]|].
    split; [exact (shw_frame _ _ _ _ _ SHP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHA MU AW)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF1 MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF2 MU AW)|].
    assert (FW : Forall (fsw_iv FI) ((lo, q') :: W)) by (eapply Forall_impl; [| exact AW]; intros iv H; left; exact H).
    split; [exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exact CLOW'|].
    exact (shw_frame _ _ _ _ _ SHE MU AW).
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma wmove_E : forall (W W0 : list ivl) shd q' m m', pinvQS shd q' m -> munch ((lo, q') :: W0) m m' -> wmono asegs m m' ->
    Forall (fun iv : ivl => fst iv <= snd iv /\ inside W (fst iv) (snd iv - fst iv)) W0 -> wmove W m m'.
  Proof.
    intros W W0 shd q' m m' INV MU WM HW. pose proof INV as (_ & _ & _ & _ & (QB & _) & _). pose proof POK as POK'. pqokA POK'.
    split; [| split; [exact WM|]].
    - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (HS & _ & _ & HWx). split; [clear - HS QB; lia|].
      clear - HW HWx. induction W0 as [|[a b] W0 IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? (H1 & H2) HW']; subst. cbn [fst snd] in *.
      split; [intros Hr; exact (inside_not_outside W a (b - a) x H2 ltac:(lia) HWx)| exact (IH HW')].
    - apply (fkeep_own W ((lo, q') :: W0) m m' shd q' INV MU). constructor; [cbn [fst snd]; split; [clear - LO QB; lia| left; exact CLO]|].
      eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2). cbn [fst snd] in *. split; [exact H1| right; left; exact H2].
  Qed.

  Definition keepV (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 276)
       \/ (P + 284 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.
  Notation zb := (Z_to_bv 8 0).
  Notation set_byte := P0.H_presp_B.set_byte.
  #[using="IC m0 POK RF0 MWL"] Lemma vpokeQ : forall (q' A len cap cur o3 l3 idx : Z) (bs sl : list byte) (mb ml ub ul w24 v1 v2 : word) (bcr : byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> cap + 1 <= 2^26 + 16 -> pstatR m -> pslk A cap sl m ->
    tp = Z_to_bv 64 6190512 -> shw m A0_FMT_SSCANF_VER 8 ->
    plocQ mb ml (wz (A + o3)) (wz l3) ub ul m -> 0 <= o3 -> 0 <= l3 -> o3 + l3 < len -> nth_error bs (Z.to_nat (o3 + l3)) = Some bcr ->
    pscrC q' (wz idx) (wz METHOD_TAB_A) w24 m ->
    rw_cells asegs m (P + 276) [C4 v1] -> rw_cells asegs m (P + 280) [C4 v2] ->
    (forall m' r (v1' v2' w24' : word) y1 y5 y6 y7 y11 y12 y13 y14 y16 y17 y28 y29 y30 y31,
       (r = -1 \/ 0 <= r <= 2) -> pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> pstatR m' ->
       pscrC q' (wz idx) (wz METHOD_TAB_A) w24' m' -> rw_cells asegs m' (P + 276) [C4 v1'] -> rw_cells asegs m' (P + 280) [C4 v2'] ->
       keepV m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz r) y11 y12 y13 y14 (wz (P + 276)) y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz 0x8b528) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz 0x8b478) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur o3 l3 idx bs sl mb ml ub ul w24 v1 v2 bcr x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q
           INV CTX TOK BNMAX PS SLK TPV SHFV PL O0 L0 OL Hbcr SCR PMJ PMN KK.
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & _).
    pose proof CTX as (SC & MBC & TXC & SHP & SHA & _ & _ & _ & SHZ & SHR & (ev & (CE & CG & CS)) & _).
    pose proof TOK as TOK'. tokA TOK'. pose proof POK as POK'. pqokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ : lo <= q') by (clear - LO QB; lia).
    destruct SCR as (j0 & j224 & j256 & QC).
    pose proof (ploc_cells _ _ _ _ _ _ m PL) as (_ & OVc & _).
    assert (LBSn : length bs = Z.to_nat (cap + 1)) by (destruct TXC as [[W _] _]; cbn in W; LiaTuning.ctauto).
    destruct (H_pparse_seg.cb_split1E ra m A (Z.to_nat (cap + 1)) bs (Z.to_nat (o3 + l3)) TXC ltac:(lia) ltac:(clear - ALO; lia)) as [TX1 TX23].
    assert (E1 : firstn 1 (skipn (Z.to_nat (o3 + l3)) bs) = [bcr]).
    { clear - Hbcr. revert Hbcr. generalize (Z.to_nat (o3 + l3)). intros n. revert bs. induction n as [|n IH]; intros [|b bs] H; cbn in *; try discriminate; [injection H as ->; reflexivity| exact (IH bs H)]. }
    rewrite E1 in TX23. rewrite Z2Nat.id in TX23 by lia.
    remember (Z.to_nat (cap + 1) - Z.to_nat (o3 + l3) - 1)%nat as nr eqn:Enr.
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.
    hide PMJ. hide PMN. hide SC. hide MBC. hide TX1.
    step. step. step. zstep.
    replace (Z_to_bv 64 (A + o3 + l3)) with (Z_to_bv 64 (A + (o3 + l3))) by (f_equal; lia).
    step. step. ubr.
    zstep. zstep. zstep. ub_b2z. step. lit_branch.
    step. ubr.
    zstep. step. zstep.
    pose proof (munch_refl [(q' + 32, q' + 40)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    gen2 CONT 0x8b4b8 11%nat 12%nat.
    { intros yi yj.
      remember (A + (o3 + l3)) as V eqn:EV.
      zstep.
      hide TX23.
      step; fix_lit_store.
      unhide TX23. unhide SC. unhide TX1. unhide MBC. unhide PMJ. unhide PMN.

      assert (SCR1 : pscrC q' (wz idx) (wz METHOD_TAB_A) (Z_to_bv 64 (bv_unsigned bcr)) m1) by (exists j0, j224, j256; exact QC).
      pose proof (pinv_stepT qshadowU eq_refl q' m m1 [] INV (sstore_T q' _ _ m m1 MU1 ltac:(lia) ltac:(lia) LQ) WM1 MI (Forall_nil _) ST (pscrC_join q' _ _ _ m1 SCR1)) as INV1.
      assert (KS1 : forall X cs, rw_cells asegs m X cs -> X + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells asegs m1 X cs)
        by (intros X cs HC1 HX; exact (fcell_S _ _ m m1 X cs MU1 WM1 ltac:(lia) HX HC1)).
      pose proof (pctx_stepT [] q' A len cap cur cur bs m m1 CTX TOK QB (sstore_T q' _ _ m m1 MU1 ltac:(lia) ltac:(lia) LQ) WM1 (Forall_nil _) I
                    (KS1 _ _ SC ltac:(simpl_sizes; lia))) as CTX1.
      pose proof (pstatR_T q' m m1 ltac:(lia) PS (sstore_rWT q' _ _ m m1 MU1 ltac:(lia) ltac:(lia) LQ) WM1) as PS1.
      pose proof (pslk_S _ _ A len cap sl m m1 TOK SLK MU1 ltac:(lia)) as SLK1.
      pose proof (ploc_S _ _ _ _ _ _ _ _ m m1 PL MU1 WM1 ltac:(lia)) as PL1.
      pose proof (wmove_S (rWC A cap) _ q' _ _ m m1 INV MU1 WM1 ltac:(lia) ltac:(lia) ltac:(lia)) as MV1.
      assert (SHFV1 : shw m1 A0_FMT_SSCANF_VER 8).
      { refine (shw_frame _ _ _ _ _ SHFV MU1 _). constructor; [unfold app_iv, SH_HI; cbn [fst snd]; right; clear - CLO ACR LQ; lia| constructor]. }
      assert (NRV : Z.of_nat nr = cap - (o3 + l3)) by (subst nr; lia).
      pose proof (KS1 _ _ TX23 ltac:(simpl_sizes; subst V; clear - NRV AHI; lia)) as TX23a.
      pose proof (KS1 _ _ TX1 ltac:(simpl_sizes; clear - OL LENC AHI O0 L0; lia)) as TX1a.
      pose proof (KS1 _ _ PMJ ltac:(simpl_sizes; lia)) as PMJ1. pose proof (KS1 _ _ PMN ltac:(simpl_sizes; lia)) as PMN1.
      clear TX23 TX1 PMJ PMN CE SC MBC TXC.
      pose proof INV1 as (ST1 & _ & MI1 & _).
      pose proof (munch_refl [(V, V + 1)]%Z m1) as MU2. pose proof (wmono_refl asegs m1) as WM2.
      hide MU1. hide WM1. hide TX1a. hide PMJ1. hide PMN1. clear ST MI.
      step; fix_lit_store.
      unhide MU1. unhide WM1. unhide TX1a. unhide PMJ1. unhide PMN1.
      assert (HKV : 0 <= o3 + l3 <= cap) by (clear - O0 L0 OL LENC; lia).
      assert (TR2 : forall X cs, rw_cells asegs m1 X cs -> (X + Z.of_nat (cells_size cs) <= V \/ V + 1 <= X) -> rw_cells asegs m2 X cs).
      { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU2| exact WM2| cbn [disjoint_from]; split; [exact HX| exact I]]. }
      destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _ & PF1 & PF2).
      pose proof (TR2 _ _ TX1a ltac:(left; simpl_sizes; subst V; clear - O0 L0; lia)) as TX1b.
      pose proof (TR2 _ _ PMJ1 ltac:(simpl_sizes; subst V; clear - TFS PF1 PF2 HKV; lia)) as PMJ2.
      pose proof (TR2 _ _ PMN1 ltac:(simpl_sizes; subst V; clear - TFS PF1 PF2 HKV; lia)) as PMN2.
      subst V.
      apply (rw_cells_reshape asegs _ _ _ [CB 1 [zb]; CB nr (skipn (Z.to_nat (o3 + l3) + 1) bs)]) in TX23a;
        [| destruct TX23a as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
      subst nr.
      pose proof (H_pparse_seg.cb_join1E _ A (Z.to_nat (cap + 1)) bs (Z.to_nat (o3 + l3)) zb TX1b ltac:(rewrite Z2Nat.id by lia; exact TX23a) ltac:(lia) LBSn) as TXC2.
      clear TX1a TX1b TX23a.
      remember (set_byte bs (Z.to_nat (o3 + l3)) zb) as bs1 eqn:Ebs1.
      assert (HX : Forall (fun iv => inP iv \/ outX iv) [(A + (o3 + l3), A + (o3 + l3) + 1)]%Z) by (constructor; [right; exact (outX_text A len cap _ TOK HKV)| constructor]).
      pose proof (pinv_stepX qshadowU eq_refl q' m1 m2 _ INV1 MU2 WM2 MI1 HX) as INV2.
      pose proof (pctx_stepTx A len cap cur bs bs1 (o3 + l3) m1 m2 CTX1 TOK MU2 WM2 HKV TXC2) as CTX2.
      assert (AWX : app_ivs [(A + (o3 + l3), A + (o3 + l3) + 1)]%Z) by (constructor; [unfold app_iv, SH_HI; cbn [fst snd]; clear - TBAND HKV ALO; lia| constructor]).
      assert (PS2 : pstatR m2).
      { apply (pstatR_step _ m1 m2 PS1 MU2 WM2); [eapply Forall_impl; [| exact AWX]; intros iv H; left; exact H|]. constructor; [left; cbn [fst]; clear - ALO HKV; lia| constructor]. }
      assert (SLK2 : pslk A cap sl m2) by (apply (pslk_step _ A cap sl m1 m2 SLK1 MU2); cbn [disjoint_from]; split; [right; clear - HKV; lia| exact I]).
      assert (PL2 : plocQ mb ml (wz (A + o3)) (wz l3) ub ul m2).
      { destruct PL1 as (j1 & j2 & j3 & HA). exists j1, j2, j3. apply (TR2 _ _ HA). simpl_sizes. clear - TFS FLO FHI HKV. lia. }
      pose proof (shw_frame _ _ _ _ _ SHFV1 MU2 AWX) as SHFV2.
      pose proof (wmove_In (rWC A cap) _ q' _ _ m1 m2 INV1 MU2 WM2 ltac:(lia) ltac:(unfold rWC; cbn [inside]; do 8 right; left; clear - HKV; lia)) as MV2.
      assert (KV2 : keepV m m2).
      { intros X cs HC1 HXc. apply TR2; [apply KS1; [exact HC1| clear - HXc FHI PHI; pose proof (fsb_ok FI) as (_ & B2 & _); lia]| clear - HXc TFS FLO FHI PF1 PF2 HKV; lia]. }
      pose proof SLK2 as (SLB & SL7 & (kE & SLAL)).
      destruct (H_presp_seg.line_rtext FI A len (cap + 1) kE bs sl st ltac:(clear - LBSn LENC; lia) BNMAX SL7 SLAL o3 l3 O0 L0 ltac:(clear - OL LENC; lia)) as (s & rr & SPLIT & NIN & TXT & LS).
      rewrite <- Ebs1 in SPLIT, TXT.
      assert (LB1 : length bs1 = Z.to_nat (cap + 1)) by (subst bs1; rewrite P0.H_presp_B.set_byte_length; [exact LBSn| clear - LBSn HKV; lia]).
      assert (BYT : bytes_at asegs m2 (A + o3) (P0.F_shgetc_A.zbytes (map bv_unsigned (skipn (Z.to_nat o3) bs1 ++ sl)))).
      { rewrite H_presp_seg.zbytes_bytesA. apply bytes_at_app. split.
        - pose proof (proj2 (proj1 TXC2)) as BB1. cbn [cells_bytes cbytes] in BB1. rewrite app_nil_r in BB1.
          rewrite <- (firstn_skipn (Z.to_nat o3) bs1) in BB1. apply bytes_at_app in BB1. destruct BB1 as [_ BB1].
          rewrite firstn_length_le in BB1 by lia. replace (A + Z.of_nat (Z.to_nat o3))%Z with (A + o3)%Z in BB1 by lia. exact BB1.
        - rewrite length_skipn. replace (A + o3 + Z.of_nat (length bs1 - Z.to_nat o3))%Z with (A + (cap + 1))%Z by lia. exact SLB. }
      assert (LTXT : Prelim.zlength (map bv_unsigned (skipn (Z.to_nat o3) bs1 ++ sl)) = cap + 1 - o3 + Z.of_nat (length sl)).
      { unfold Prelim.zlength. rewrite ?length_map, ?length_app, ?length_skipn. lia. }
      assert (LPRE : Prelim.zlength (map bv_unsigned s) = Z.of_nat (length s)) by (unfold Prelim.zlength; rewrite length_map; reflexivity).
      pose proof CTX2 as (_ & _ & _ & SHP2 & SHA2 & _ & _ & _ & SHZ2 & SHR2 & (ev2 & (CE2 & CG2 & CS2)) & _).
      pose proof INV2 as (ST2 & _ & MI2 & AE2 & _).
      assert (SHT1 : shw m2 (A + o3) (Prelim.zlength (map bv_unsigned s) + 1)) by (rewrite LPRE; eapply shw_sub; [exact SHA2| lia| lia| lia]).
      assert (SHP1 : shw m2 (P + 276) 4) by (apply (shw_sub _ P 504); [exact SHP2| lia| lia| lia]).
      assert (SHP2' : shw m2 (P + 280) 4) by (apply (shw_sub _ P 504); [exact SHP2| lia| lia| lia]).
      assert (SHWS : shw m2 lo (q' - lo)).
      { apply (shw_of_shz_shr m2 (sh lo) (sh q) (sh lo - sh lo mod 8) (sh q + 8) lo (q' - lo) SHZ2 SHR2).
        - unfold win_ok. split; [lia|]. right. change (2^47) with 140737488355328 in *. lia.
        - lia.
        - unfold sh, SHADOW_OFF. clear - QB LO. Z.div_mod_to_equations. lia.
        - lia.
        - unfold sh, SHADOW_OFF. clear - QB LO. Z.div_mod_to_equations. lia. }
      pose proof (ploc_cells _ _ _ _ _ _ m2 PL2) as (_ & OVc2 & _).
      clear MU1 WM1 MU2 WM2 INV CTX PS SLK PL INV1 CTX1 PS1 SLK1 PL1 ST1 MI1 SHFV SHFV1 SHP SHA SHZ SHR AE KS1 TR2 SCR1.
      step. step. zstep. zstep. zstep. step. step.
      eapply evt_cut.
      { eapply (ic_sscanf_version IC) with (T := A + o3) (txt := map bv_unsigned (skipn (Z.to_nat o3) bs1 ++ sl)) (pre := map bv_unsigned s) (post := map bv_unsigned (rr ++ sl))
          (P1 := P + 276) (P2 := P + 280) (lox := lo) (qx := q');
        [ exact TXT | exact BYT
        | exact (proj1 SHT1) | exact (proj1 (proj2 SHT1)) | exact (proj2 (proj2 SHT1))
        | rewrite LPRE; change (2^43) with 8796093022208; change (2^26) with 67108864 in BNMAX; clear - LS O0 OL LENC BNMAX; lia
        | exact (proj1 SHFV2) | exact (proj1 (proj2 SHFV2))
        | exact (proj1 SHP1) | exact (proj1 (proj2 SHP1)) | exact (proj2 (proj2 SHP1))
        | exact (proj1 SHP2') | exact (proj1 (proj2 SHP2')) | exact (proj2 (proj2 SHP2'))
        | exact ST2 | exact MI2 | exact AE2
        | exact CLO | unfold A0_SSCANF_DEPTH; clear - LO QB; lia | exact QAL | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; clear - QB QHI; lia
        | change (2^47) with 140737488355328 in *; clear - QB QHI; lia | exact (proj1 SHWS) | exact (proj1 (proj2 SHWS))
        | exact TPV
        | clear - ALO O0; lia | rewrite LTXT; clear - AHI SL7 O0; lia
        | clear - PLO PHI; lia | clear - PLO PHI; lia
        | rewrite LTXT; clear - TFS PF1 PF2 SLAL SL7 O0 LENC AAL; pose proof (fsb_ok FI) as (_ & _ & _ & B4 & _); Z.div_mod_to_equations; lia
        | rewrite LTXT; clear - TFS PF1 PF2 SLAL SL7 O0 LENC AAL; pose proof (fsb_ok FI) as (_ & _ & _ & B4 & _); Z.div_mod_to_equations; lia
        | left; clear; lia
        | exact CG2 | exact CS2 | exact CE2
        | exact PMJ2 | exact PMN2
        | reflexivity | reflexivity | reflexivity | reflexivity ]. }
      intros ms' PO. unfold sscanf2_post_A in PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & ev' & v1' & v2' & r & -> & MU3 & WM3 & MI3 & ST3 & AE3 & _ & _ & SM & RR & CG3 & CS3 & CE3 & PC1 & PC2).
      replace (ret_pc (Z_to_bv 64 0x8b4e0)) with (Z_to_bv 64 0x8b4e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (HWE : Forall inPE [(P + 276, P + 276 + 4); (P + 280, P + 280 + 4); (A0_ERRNO, A0_ERRNO + 4)]%Z).
      { unfold inPE, H_pparse_seg.inP, H_pparse_seg.inER, A0_ERRNO. constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|].
        constructor; [right; cbn [fst snd]; lia| constructor]. }
      assert (TR3 : forall X cs, rw_cells asegs m2 X cs -> 0x5e7510 <= X -> (X + Z.of_nat (cells_size cs) <= lo \/ q' <= X) ->
                      (X + Z.of_nat (cells_size cs) <= P + 276 \/ P + 284 <= X) -> rw_cells asegs m3 X cs).
      { intros X cs HC1 H1 H2 H3. eapply rw_cells_transport; [exact HC1| exact MU3| exact WM3|]. unfold A0_ERRNO. cbn [disjoint_from].
        split; [exact H2|]. split; [clear - H3; lia|]. split; [clear - H3; lia|]. split; [right; clear - H1; lia| exact I]. }
      pose proof (proj1 CTX2) as SC2.
      pose proof (TR3 _ _ SC2 ltac:(clear - PLO; lia) ltac:(left; simpl_sizes; clear - PHI CLO; lia) ltac:(simpl_sizes; lia)) as SC3.
      pose proof (pinv_stepE qshadowU eq_refl q' m2 m3 _ INV2 MU3 WM3 MI3 AE3 HWE ST3) as INV3.
      assert (DJM : disjoint_from [(P + 276, P + 276 + 4); (P + 280, P + 280 + 4); (A0_ERRNO, A0_ERRNO + 4)]%Z (P + 400) 32)
        by (unfold A0_ERRNO; cbn [disjoint_from]; repeat split; try exact I; clear - PLO; lia).
      pose proof (pctx_stepE _ q' A len cap cur bs1 m2 m3 CTX2 TOK QB MU3 WM3 HWE DJM SC3 (ex_intro _ ev' (conj CE3 (conj CG3 CS3)))) as CTX3.
      assert (PS3 : pstatR m3).
      { apply (pstatR_step _ m2 m3 PS2 MU3 WM3).
        - constructor; [left; apply app_iv_stack; exact CLO|]. unfold A0_ERRNO.
          constructor; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 PLO PHI; pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5); lia|].
          constructor; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 PLO PHI; pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5); lia|].
          constructor; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear; lia| constructor].
        - constructor; [left; cbn [fst]; clear - CLO ACR; lia|]. unfold A0_ERRNO.
          constructor; [left; cbn [fst]; clear - PLO; lia|]. constructor; [left; cbn [fst]; clear - PLO; lia|].
          constructor; [right; unfold H_pparse_seg.inER; cbn [fst snd]; clear; lia| constructor]. }
      pose proof (TR3 _ _ QC ltac:(clear - CLO LO QB ACR; lia) ltac:(right; clear; lia) ltac:(right; simpl_sizes; clear - PHI CLO LO QB; lia)) as QC3.
      assert (PL3 : plocQ mb ml (wz (A + o3)) (wz l3) ub ul m3).
      { destruct PL2 as (j1 & j2 & j3 & HA). exists j1, j2, j3.
        apply (TR3 _ _ HA); [clear - FLO; pose proof (fsb_ok FI) as (B1 & _); lia| left; simpl_sizes; clear - FHI CLO; pose proof (fsb_ok FI) as (_ & B2 & _); lia| simpl_sizes; clear - PAF; lia]. }
      pose proof (proj1 (proj2 (proj2 CTX3))) as TXC3.
      assert (MV3 : wmove (rWC A cap) m m3).
      { apply (wmove_trans _ _ _ _ MV1). apply (wmove_trans _ _ _ _ MV2).
        apply (wmove_E (rWC A cap) _ _ q' m2 m3 INV2 MU3 WM3). unfold rWC, A0_ERRNO.
        constructor; [cbn [fst snd inside]; split; [clear; lia| do 3 right; left; clear; lia]|].
        constructor; [cbn [fst snd inside]; split; [clear; lia| do 4 right; left; clear; lia]|].
        constructor; [cbn [fst snd inside]; split; [clear; lia| do 2 right; left; clear; lia]| constructor]. }
      assert (KV3 : keepV m m3).
      { intros X cs HC1 HXc. apply TR3; [apply KV2; [exact HC1| exact HXc]| | |].
        - clear - HXc FLO PLO. pose proof (fsb_ok FI) as (B1 & _). lia.
        - left. clear - HXc FHI PHI CLO. pose proof (fsb_ok FI) as (_ & B2 & _). lia.
        - clear - HXc PAF. lia. }
      pose proof (ploc_cells _ _ _ _ _ _ m3 PL3) as (_ & OVc3 & _).
      pose proof INV3 as (_ & _ & _ & _ & _ & _). clear MI2 ST2 AE2 INV2 CTX2 PS2 SLK2 PL2 SC2 SHT1 SHP1 SHP2' SHWS BYT TXC2 PMJ2 PMN2 OVc2 CE2 CG2 CS2 SHA2 SHP2 SHZ2 SHR2 SHFV2 KV2 MV1 MV2 QC MU3 WM3 TR3 SLB.
      assert (LBS1 : length bs1 = Z.to_nat (cap + 1)) by exact LB1.
      assert (Hz : nth_error bs1 (Z.to_nat (o3 + l3)) = Some zb) by (subst bs1; apply P0.H_presp_B.set_byte_same; clear - LBSn HKV; lia).
      destruct (H_pparse_seg.cb_split1E ra m3 A (Z.to_nat (cap + 1)) bs1 (Z.to_nat (o3 + l3)) TXC3 ltac:(clear - HKV; lia) ltac:(clear - ALO; lia)) as [TY1 TY23].
      assert (E2 : firstn 1 (skipn (Z.to_nat (o3 + l3)) bs1) = [zb]).
      { clear - Hz. revert Hz. generalize (Z.to_nat (o3 + l3)). intros n. generalize bs1. induction n as [|n IH]; intros [|b l] H; cbn in *; try discriminate; [injection H as ->; reflexivity| exact (IH l H)]. }
      rewrite E2 in TY23. rewrite Z2Nat.id in TY23 by lia.
      remember (Z.to_nat (cap + 1) - Z.to_nat (o3 + l3) - 1)%nat as nr eqn:Enr.
      hide TY1. hide SC3. hide PC1. hide PC2.
      step. step. step. step. zstep.
      replace (Z_to_bv 64 (A + o3 + l3)) with (Z_to_bv 64 (A + (o3 + l3))) by (f_equal; lia).
      step. ubr.
      zstep. zstep. zstep. ub_b2z. step. lit_branch.
      step. ubr.
      zstep. step. zstep.
      pose proof INV3 as (ST3' & _ & MI3' & _).
      pose proof (munch_refl [(A + (o3 + l3), A + (o3 + l3) + 1)]%Z m3) as MU4. pose proof (wmono_refl asegs m3) as WM4.
      gen2 CONT2 0x8b520 12%nat 13%nat.
      { intros zi zj.
        step.
        remember (A + (o3 + l3)) as V eqn:EV.
        step. rewrite (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec.StrFun.le1_zxb bcr). mem_after_store.
        unhide TY1. unhide SC3. unhide PC1. unhide PC2.
        assert (TR4 : forall X cs, rw_cells asegs m3 X cs -> (X + Z.of_nat (cells_size cs) <= V \/ V + 1 <= X) -> rw_cells asegs m4 X cs).
        { intros X cs HC1 HXc. eapply rw_cells_transport; [exact HC1| exact MU4| exact WM4| cbn [disjoint_from]; split; [exact HXc| exact I]]. }
        pose proof (TR4 _ _ TY1 ltac:(left; simpl_sizes; subst V; clear - O0 L0; lia)) as TY1b.
        pose proof (TR4 _ _ PC1 ltac:(simpl_sizes; subst V; clear - TFS PF1 PF2 HKV; lia)) as PC1b.
        pose proof (TR4 _ _ PC2 ltac:(simpl_sizes; subst V; clear - TFS PF1 PF2 HKV; lia)) as PC2b.
        subst V.
        apply (rw_cells_reshape asegs _ _ _ [CB 1 [bcr]; CB nr (skipn (Z.to_nat (o3 + l3) + 1) bs1)]) in TY23;
          [| destruct TY23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
        subst nr.
        pose proof (H_pparse_seg.cb_join1E _ A (Z.to_nat (cap + 1)) bs1 (Z.to_nat (o3 + l3)) bcr TY1b ltac:(rewrite Z2Nat.id by lia; exact TY23) ltac:(lia) LBS1) as TXC4.
        assert (RESTORE : set_byte bs1 (Z.to_nat (o3 + l3)) bcr = bs) by (subst bs1; apply P0.H_presp_B.set_byte_restore; exact Hbcr).
        rewrite RESTORE in TXC4. clear RESTORE TY1 TY1b TY23.
        pose proof (pinv_stepX qshadowU eq_refl q' m3 m4 _ INV3 MU4 WM4 MI3' HX) as INV4.
        pose proof (pctx_stepTx A len cap cur bs1 bs (o3 + l3) m3 m4 CTX3 TOK MU4 WM4 HKV TXC4) as CTX4.
        assert (PS4 : pstatR m4).
        { apply (pstatR_step _ m3 m4 PS3 MU4 WM4); [eapply Forall_impl; [| exact AWX]; intros iv H; left; exact H|]. constructor; [left; cbn [fst]; clear - ALO HKV; lia| constructor]. }
        assert (SCR4 : pscrC q' (wz idx) (wz METHOD_TAB_A) (Z_to_bv 64 (bv_unsigned bcr)) m4) by (exists j0, j224, j256; exact QC3).
        pose proof (wmove_In (rWC A cap) _ q' _ _ m3 m4 INV3 MU4 WM4 ltac:(lia) ltac:(unfold rWC; cbn [inside]; do 8 right; left; clear - HKV; lia)) as MV4.
        eapply (KK m4 r v1' v2' (Z_to_bv 64 (bv_unsigned bcr))); [exact RR| exact INV4| exact CTX4| exact PS4| exact SCR4| exact PC1b| exact PC2b| | exact (wmove_trans _ _ _ _ MV3 MV4)].
        intros X cs HC1 HXc. apply TR4; [apply KV3; [exact HC1| exact HXc]| clear - HXc TFS FLO FHI PF1 PF2 HKV; lia]. }
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 CTX3))))) as SHA3.
      chkbQ 12 (A + (o3 + l3)) SHA3 kk SHRk Hk.
      destruct Hk as [-> | [G1 G2]].
      - step. step. lit_branch. apply CONT2.
      - step. rewrite (sxb_small kk) by lia.
        step. if_cases G3; zify_cond G3; [| exfalso; lia].
        zstep.
        step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
        apply CONT2. }
    chkbQ 11 (A + (o3 + l3)) SHA kk SHRk Hk.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
  Qed.

  Definition keepD (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 4)
       \/ (P + 8 <= X /\ X + Z.of_nat (cells_size cs) <= P + 440) \/ (P + 444 <= X /\ X + Z.of_nat (cells_size cs) <= P + 448)
       \/ (P + 452 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.
  #[using="m0 POK RF0 MWL MID"] Lemma decQ : forall (q' A len cap cur idx r meth pos : Z) (bs : list byte) (w24 v1 v2 e : word)
      x1 x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    (r = -1 \/ 0 <= r <= 2) -> 0 <= idx < 11 ->
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatR m -> pscrC q' (wz idx) (wz METHOD_TAB_A) w24 m ->
    rw_cells asegs m (P + 276) [C4 v1] -> rw_cells asegs m (P + 280) [C4 v2] ->
    rw_cells asegs m (P + 440) [C4 e] -> rw_cells asegs m (P + 4) [C4 (wz meth)] -> rw_cells asegs m (P + 448) [C4 (wz pos)] ->
    (forall m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' -> rw_cells asegs m' (P + 440) [C4 (wz 505)] ->
       rw_cells asegs m' (P + 4) [C4 (wz meth)] -> rw_cells asegs m' (P + 448) [C4 (wz pos)] -> keepD m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz 3) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    (forall m' id y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       0 <= id <= 11 -> pinvQS qshadowU q' m' -> pctx A len cap cur bs m' ->
       rw_cells asegs m' (P + 4) [C4 (wz id)] -> rw_cells asegs m' (P + 448) [C4 (wz 2)] -> rw_cells asegs m' (P + 440) [C4 e] -> keepD m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz 4) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz r) x11 x12 x13 x14 (wz (P + 276)) x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz 0x8b528) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur idx r meth pos bs w24 v1 v2 e x1 x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 x31 m Q RR IDX INV CTX TOK PS SCR PMJ PMN EC MC PC K505 KOK.
    pose proof INV as (_ & _ & MI & _ & (QB & _) & _).
    pose proof CTX as (SC & _ & _ & SHP & _).
    pose proof PS as (TB & SHT & _).
    destruct (MID idx IDX) as (id & HN & IDR).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    destruct SCR as (j0 & j224 & j256 & QC).
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _ & PF1 & PF2).
    unfold H_pparse_seg.pregsQ, H_pparse_seg.qSH in *.

    assert (E505 : forall u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31,
              evt asegs Q (MS (mkR u1 (wz q') gp tp u5 u6 u7 (wz q) (wz q') u10 u11 u12 u13 u14 u15 u16 u17
                                   (wz 3) (wz P) (wz (P + 448)) (wz 2) (wz 4) (wz SF) (wz (Z.shiftr (P + 448) 3 + 2147450880)) (wz (F + 96)) (Z_to_bv 64 (-8)) (wz (P + 480)) u28 u29 u30 u31)
                              F_ (wz 0x8b710) fc None m (seg_rom asegs))).
    { intros u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31.
      assert (HACC : acc m (P + 440 + 8 - 1)) by (apply (proj1 SHP); lia).
      pose proof (munch_refl [(P + 440, P + 444)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 10 in
        destruct (AWAuto2.acc_loadw mm (P + 440) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR8 HACC.
      step.
      clear QC. hide SC. hide PMJ. hide PMN. hide MC. hide PC.
      zstep. step. fix_lit_store. step.
      unhide SC.
      assert (HWc : Forall inP [(P + 440, P + 444)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
      assert (DJM : disjoint_from [(P + 440, P + 444)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
      assert (TR : forall X cs, rw_cells asegs m X cs -> (X + Z.of_nat (cells_size cs) <= P + 440 \/ P + 444 <= X) -> rw_cells asegs m1 X cs).
      { intros X cs HC1 HX. eapply rw_cells_transport; [exact HC1| exact MU1| exact WM1| cbn [disjoint_from]; split; [exact HX| exact I]]. }
      pose proof (TR _ _ SC ltac:(simpl_sizes; lia)) as SC1.
      pose proof (pinv_stepP qshadowU eq_refl q' m m1 _ INV MU1 WM1 MI HWc) as INV1.
      pose proof (pctx_stepP _ A len cap cur cur bs m m1 CTX TOK MU1 WM1 HWc DJM SC1) as CTX1.
      unhide MC. unhide PC.
      eapply (K505 m1); [exact INV1| exact CTX1| exact EC| exact (TR _ _ MC ltac:(simpl_sizes; lia))| exact (TR _ _ PC ltac:(simpl_sizes; lia))| | exact (wmove_P (rWC A cap) _ q' _ _ m m1 INV MU1 WM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold rWC; cbn [inside]; do 6 right; left; clear; lia))].
      intros X cs HC1 HX. apply TR; [exact HC1| clear - HX PAF; lia]. }

    assert (EOK : forall u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31,
              evt asegs Q (MS (mkR u1 (wz q') gp tp u5 u6 u7 (wz q) (wz q') u10 (wz (16 * idx)) u12 u13 u14 u15 u16 u17
                                   (wz 3) (wz P) (wz (P + 448)) (wz 2) (wz 4) (wz SF) (wz (Z.shiftr (P + 448) 3 + 2147450880)) (wz (F + 96)) (Z_to_bv 64 (-8)) (wz (P + 480)) u28 u29 u30 u31)
                              F_ (wz 0x8b590) fc None m (seg_rom asegs))).
    { intros u1 u5 u6 u7 u10 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31.
      assert (HACCT : acc m (METHOD_TAB_A + 16 * idx + 8 + 8 - 1)) by (apply (proj1 SHT); lia).
      assert (HACCM : acc m (P + 4 + 4 - 1)) by (apply (proj1 SHP); lia).
      assert (HACCP : acc m (P + 448 + 8 - 1)) by (apply (proj1 SHP); lia).
      pose proof (munch_refl [(P + 4, P + 8); (P + 448, P + 452)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
      step. zstep. zstep. zstep. step. zstep.
      replace (Z.land (718272 + 16 * idx + 8) 18446744073709551615) with (718272 + 16 * idx + 8)
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 11 in
        destruct (AWAuto2.acc_loadw mm (METHOD_TAB_A + 16 * idx + 8) 8 a ltac:(lia) ltac:(clear; Z.div_mod_to_equations; lia) ltac:(lia) HACCT ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR8 HACCT.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 11 in
        destruct (AWAuto2.acc_loadw mm (P + 4) 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACCM ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
      destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
      step.
      pose proof (u64arr_read4Q m METHOD_TAB_A mws (2 * idx + 1) (wz id) (Z_to_bv 64 (718272 + 16 * idx + 8)) TB HN ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. rewrite (sx32_lit id) by lia. clear RD.
      step. lit_branch. clear SHR8 HACCM.
      step.
      clear QC. hide SC. hide PMJ. hide PMN. hide EC.
      step. fix_lit_store.
      assert (AWc : app_ivs [(P + 4, P + 8); (P + 448, P + 452)]%Z).
      { pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). constructor; [unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 B1 B2 B5; lia|].
        constructor; [unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 B1 B2 B5; lia| constructor]. }
      assert (HACCP1 : acc m1 (P + 448 + 8 - 1)) by (apply (proj1 (shw_frame _ _ _ _ _ SHP MU1 AWc)); lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 24 in
        destruct (AWAuto2.acc_loadw mm (P + 448) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACCP1 ltac:(shadow_addr_tac)) as (k9 & SHR9 & Hk9) end.
      destruct Hk9 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
      step. step. lit_branch. clear SHR9 HACCP1 HACCP.
      step. fix_lit_store. zstep. step.
      unhide SC. unhide EC.
      assert (HWc : Forall inP [(P + 4, P + 8); (P + 448, P + 452)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
      assert (DJM : disjoint_from [(P + 4, P + 8); (P + 448, P + 452)]%Z (P + 400) 32) by (cbn [disjoint_from]; repeat split; try exact I; clear; lia).
      assert (TR : forall X cs, rw_cells asegs m X cs -> (X + Z.of_nat (cells_size cs) <= P + 4 \/ P + 8 <= X) -> (X + Z.of_nat (cells_size cs) <= P + 448 \/ P + 452 <= X) -> rw_cells asegs m2 X cs).
      { intros X cs HC1 HX1 HX2. eapply rw_cells_transport; [exact HC1| exact MU1| exact WM1| cbn [disjoint_from]; split; [exact HX1| split; [exact HX2| exact I]]]. }
      pose proof (TR _ _ SC ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as SC2.
      pose proof (TR _ _ EC ltac:(simpl_sizes; lia) ltac:(simpl_sizes; lia)) as EC2.
      pose proof (pinv_stepP qshadowU eq_refl q' m m2 _ INV MU1 WM1 MI HWc) as INV2.
      pose proof (pctx_stepP _ A len cap cur cur bs m m2 CTX TOK MU1 WM1 HWc DJM SC2) as CTX2.
      eapply (KOK m2 id); [exact IDR| exact INV2| exact CTX2| exact MC| exact PC| exact EC2| |].
      - intros X cs HC1 HX. apply TR; [exact HC1| clear - HX PAF; lia| clear - HX PAF; lia].
      - destruct (pinv_rf _ q' m INV) as (stc & RF & LIVE1).
        split; [| split; [exact WM1|]].
        + eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in *. destruct Hx as (_ & HF & _). repeat split; try exact I; clear - HF PF1 PF2; lia.
        + apply (fkeep_own (rWC A cap) _ m m2 qshadowU q' INV MU1). unfold rWC.
          constructor; [cbn [fst snd inside]; split; [clear; lia| right; left; left; clear; lia]|].
          constructor; [cbn [fst snd inside]; split; [clear; lia| right; left; do 7 right; left; clear; lia]| constructor]. }

    assert (EOK1 : forall u1 u5 u6 u7 u10 u12 u13 u15 u16 u17 u28 u29 u30 u31,
              evt asegs Q (MS (mkR u1 (wz q') gp tp u5 u6 u7 (wz q) (wz q') u10 (wz (16 * idx)) u12 u13 (wz idx) u15 u16 u17
                                   (wz 3) (wz P) (wz (P + 448)) (wz 2) (wz 4) (wz SF) (wz (Z.shiftr (P + 448) 3 + 2147450880)) (wz (F + 96)) (Z_to_bv 64 (-8)) (wz (P + 480)) u28 u29 u30 u31)
                              F_ (wz 0x8b578) fc None m (seg_rom asegs))).
    { intros u1 u5 u6 u7 u10 u12 u13 u15 u16 u17 u28 u29 u30 u31.
      zstep. step. ubr. step. zstep. zstep.
      ub_b2z. step. lit_branch. apply EOK. }

    assert (HACCJ : acc m (P + 276 + 4 - 1)) by (apply (proj1 SHP); lia).
    assert (HACCN : acc m (P + 280 + 8 - 1)) by (apply (proj1 SHP); lia).
    assert (HACCT : acc m (METHOD_TAB_A + 16 * idx + 8 + 8 - 1)) by (apply (proj1 SHT); lia).
    step. if_cases KN; zify_cond KN; [apply E505|].
    zstep. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 10 in
      destruct (AWAuto2.acc_loadw mm (P + 276) 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACCJ ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
    destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR8 HACCJ.
    step. step. if_cases KJ; [apply E505|].
    step. zstep. zstep. step. if_cases KJ1.
    { replace (Z.shiftl idx 4) with (16 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia). apply EOK1. }
    step. zstep. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 12 in
      destruct (AWAuto2.acc_loadw mm (P + 280) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACCN ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
    destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR8 HACCN.
    step. step. if_cases KM.
    2:{ replace (Z.shiftl idx 4) with (16 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia). apply EOK1. }
    replace (Z.shiftl idx 4) with (16 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. step. ubr. step. zstep. step. ubr.
    step. zstep. step. zstep. zstep. zstep. step. zstep.
    replace (Z.shiftl idx 4) with (16 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z.land (718272 + 16 * idx + 8) 18446744073709551615) with (718272 + 16 * idx + 8)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 12 in
      destruct (AWAuto2.acc_loadw mm (METHOD_TAB_A + 16 * idx + 8) 8 a ltac:(lia) ltac:(clear; Z.div_mod_to_equations; lia) ltac:(lia) HACCT ltac:(shadow_addr_tac)) as (k8 & SHR8 & Hk8) end.
    destruct Hk8 as [-> | [K1' K2']]; [| exfalso; clear - K1' K2'; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR8 HACCT.
    pose proof (u64arr_read4Q m METHOD_TAB_A mws (2 * idx + 1) (wz id) (Z_to_bv 64 (718272 + 16 * idx + 8)) TB HN ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. rewrite (sx32_lit id) by lia. clear RD.
    zstep. step. if_cases K9.
    { step. lit_branch. apply EOK. }
    apply E505.
  Qed.

  #[using="st m0 POK RF0"] Lemma rWC_fsw : forall A len cap, txt_okA A len cap -> Forall (fsw_iv FI) ((lo, q) :: FSIV (rWC A cap)).
  Proof.
    intros A len cap TOK. tokA TOK. pose proof POK as POK'. pqokA POK'. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    apply fsw_cons_app; [apply app_iv_stack; exact CLO|]. apply fsw_FSIV. unfold rWC, app_ivs.
    repeat (constructor; [unfold app_iv, SH_HI; cbn [fst snd]; clear - PF1 PF2 B1 B2 B5 ALO TBAND LENC; lia|]). constructor.
  Qed.
  #[using="m0 POK RF0 mws MWL"] Lemma shwlow_wmove : forall A len cap m m' X n, txt_okA A len cap -> shw m X n -> X + n <= 0x609000 -> wmove (rWC A cap) m m' -> shw m' X n.
  Proof.
    intros A len cap m m' X n TOK SH HX (MU & _ & _). pose proof (fsb_ok FI) as (B1 & _).
    apply (shw_frame_fs FI _ m m' X n SH MU (rWC_fsw A len cap TOK)). left. lia.
  Qed.
  Definition keepZ (m m' : mem) : Prop :=
    forall X cs, rw_cells asegs m X cs ->
      ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 4)
       \/ (P + 224 <= X /\ X + Z.of_nat (cells_size cs) <= P + 276) \/ (P + 284 <= X /\ X + Z.of_nat (cells_size cs) <= P + 432)
       \/ (P + 444 <= X /\ X + Z.of_nat (cells_size cs) <= P + 448) \/ (P + 452 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m' X cs.

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_3 SET_SHADOW_F5 m0 POK RF0 FCO MWL MID"] Lemma segCQ : forall (q' A len cap cur U l o1 l1 o3 l3 meth pos : Z) (bs ustr slack junk sl : list byte) (ub ub0 e v1 v2 : word) (bcr : byte)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> cap + 1 <= 2^26 + 16 -> pstatU m -> pstatR m -> pslk A cap sl m -> FSENV FI m ->
    tp = Z_to_bv 64 6190512 -> shw m A0_FMT_SSCANF_VER 8 ->
    plocQ (wz (A + o1)) (wz l1) (wz (A + o3)) (wz l3) ub (wz l) m ->
    0 <= o1 -> 1 <= l1 -> o1 + l1 <= cap + 1 -> 0 <= o3 -> 0 <= l3 -> o3 + l3 < len -> nth_error bs (Z.to_nat (o3 + l3)) = Some bcr ->
    rw_cells asegs m (P + 432) [C8 ub0] -> rw_cells asegs m (P + 8) [CB 216 junk] ->
    rw_cells asegs m (P + 276) [C4 v1] -> rw_cells asegs m (P + 280) [C4 v2] ->
    rw_cells asegs m (P + 440) [C4 e] -> rw_cells asegs m (P + 4) [C4 (wz meth)] -> rw_cells asegs m (P + 448) [C4 (wz pos)] ->
    Z.of_nat (length ustr) = l -> 0 <= l < 2^31 -> (- (U + l + 1)) mod 8 <= Z.of_nat (length slack) ->
    0x609000 <= U -> U + l + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
    (U + l + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U) ->
    (U + l + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U) ->
    shw m U (l + 1) -> bytes_at asegs m U (ustr ++ Z_to_bv 8 0 :: slack) ->
    (forall m' r meth' pos' (junk' : list byte) (v1' v2' e' : word) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       ((r = 3 /\ pos' = pos /\ meth' = meth /\ (e' = e \/ e' = wz 501 \/ e' = wz 505)) \/ (r = 4 /\ pos' = 2 /\ 0 <= meth' <= 11 /\ e' = e)) ->
       pinvQS qshadowU q' m' -> pctx A len cap cur bs m' ->
       rw_cells asegs m' (P + 432) [C8 (wz U)] -> rw_cells asegs m' (P + 8) [CB 216 junk'] ->
       rw_cells asegs m' (P + 276) [C4 v1'] -> rw_cells asegs m' (P + 280) [C4 v2'] ->
       rw_cells asegs m' (P + 440) [C4 e'] -> rw_cells asegs m' (P + 4) [C4 (wz meth')] -> rw_cells asegs m' (P + 448) [C4 (wz pos')] ->
       keepZ m m' -> wmove (rWC A cap) m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 (wz U) x11 x12 x13 x14 x15 x16 x17 (wz 4) x28 x29 x30 x31) F_ (wz 0x8b41c) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur U l o1 l1 o3 l3 meth pos bs ustr slack junk sl ub ub0 e v1 v2 bcr x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q
           INV CTX TOK BNMAX PU PS SLKF FE TPV SHFV PL O0 L1 OL O3 L3 OL3 Hbcr UBC UC PMJ PMN EC MC PC UL ULR SLK ULO UHI UFS UBAND SHU UB KK.
    eapply (urlCQ q' A len cap cur U l bs ustr slack junk sl); [exact INV| exact CTX| exact TOK| exact PU| exact PS| exact SLKF| exact FE| exact TPV| exact PL| exact UBC| exact UC
      | exact UL| exact ULR| exact SLK| exact ULO| exact UHI| exact UFS| exact UBAND| exact SHU| exact UB| |].
    -
      intros m1 junk' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV1 CTX1 UBC1 UC1 KC MV1.
      eapply (KK m1 3 meth pos junk' v1 v2 e); [left; repeat split; left; reflexivity| exact INV1| exact CTX1| exact UBC1| exact UC1
        | apply (KC _ _ PMJ); simpl_sizes; lia| apply (KC _ _ PMN); simpl_sizes; lia| apply (KC _ _ EC); simpl_sizes; lia| apply (KC _ _ MC); simpl_sizes; lia
        | apply (KC _ _ PC); simpl_sizes; lia| | exact MV1].
      intros X cs HC1 HX. apply (KC _ _ HC1). clear - HX. lia.
    - intros m1 junk' y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV1 CTX1 PS1 SLK1 FE1 UBC1 UC1 KC MV1.
      assert (PL1 : plocQ (wz (A + o1)) (wz l1) (wz (A + o3)) (wz l3) ub (wz l) m1).
      { destruct PL as (j1 & j2 & j3 & HA). exists j1, j2, j3. apply (KC _ _ HA). left. simpl_sizes. lia. }
      assert (PMJ1 : rw_cells asegs m1 (P + 276) [C4 v1]) by (apply (KC _ _ PMJ); simpl_sizes; lia).
      assert (PMN1 : rw_cells asegs m1 (P + 280) [C4 v2]) by (apply (KC _ _ PMN); simpl_sizes; lia).
      assert (EC1 : rw_cells asegs m1 (P + 440) [C4 e]) by (apply (KC _ _ EC); simpl_sizes; lia).
      assert (MC1 : rw_cells asegs m1 (P + 4) [C4 (wz meth)]) by (apply (KC _ _ MC); simpl_sizes; lia).
      assert (PC1 : rw_cells asegs m1 (P + 448) [C4 (wz pos)]) by (apply (KC _ _ PC); simpl_sizes; lia).
      pose proof (shwlow_wmove A len cap m m1 _ _ TOK SHFV ltac:(unfold A0_FMT_SSCANF_VER; lia) MV1) as SHFV1.
      eapply (mapCQ q' A len cap cur o1 l1 bs sl); [exact INV1| exact CTX1| exact TOK| exact PS1| exact SLK1| exact FE1| exact PL1| exact O0| exact L1| exact OL| exact EC1| |].
      +
        intros m2 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 INV2 CTX2 EC2 KM MV2.
        eapply (KK m2 3 meth pos junk' v1 v2 (wz 501)); [left; repeat split; right; left; reflexivity| exact INV2| exact CTX2
          | apply (KM _ _ UBC1); simpl_sizes; lia| apply (KM _ _ UC1); simpl_sizes; lia| apply (KM _ _ PMJ1); simpl_sizes; lia| apply (KM _ _ PMN1); simpl_sizes; lia
          | exact EC2| apply (KM _ _ MC1); simpl_sizes; lia| apply (KM _ _ PC1); simpl_sizes; lia| | exact (wmove_trans _ _ _ _ MV1 MV2)].
        intros X cs HC1 HX. apply KM; [apply (KC _ _ HC1); clear - HX; lia| clear - HX; lia].
      + intros m2 idx w24 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 IDX INV2 CTX2 PS2 SLK2 SCR2 EC2 KM MV2.
        assert (PL2 : plocQ (wz (A + o1)) (wz l1) (wz (A + o3)) (wz l3) ub (wz l) m2).
        { destruct PL1 as (j1 & j2 & j3 & HA). exists j1, j2, j3. apply (KM _ _ HA). left. simpl_sizes. lia. }
        pose proof (shwlow_wmove A len cap m1 m2 _ _ TOK SHFV1 ltac:(unfold A0_FMT_SSCANF_VER; lia) MV2) as SHFV2.
        eapply (vpokeQ q' A len cap cur o3 l3 idx bs sl); [exact INV2| exact CTX2| exact TOK| exact BNMAX| exact PS2| exact SLK2| exact TPV| exact SHFV2| exact PL2| exact O3| exact L3| exact OL3| exact Hbcr
          | exact SCR2| apply (KM _ _ PMJ1); simpl_sizes; lia| apply (KM _ _ PMN1); simpl_sizes; lia|].
        intros m3 r v1' v2' w24' u1 u5 u6 u7 u11 u12 u13 u14 u16 u17 u28 u29 u30 u31 RR INV3 CTX3 PS3 SCR3 PMJ3 PMN3 KV MV3.
        assert (K13 : forall X cs, rw_cells asegs m1 X cs -> ((F + 32 <= X /\ X + Z.of_nat (cells_size cs) <= F + 120) \/ (P <= X /\ X + Z.of_nat (cells_size cs) <= P + 276)
                        \/ (P + 284 <= X /\ X + Z.of_nat (cells_size cs) <= P + 440) \/ (P + 444 <= X /\ X + Z.of_nat (cells_size cs) <= P + 504)) -> rw_cells asegs m3 X cs).
        { intros X cs HC1 HX. apply KV; [apply (KM _ _ HC1); clear - HX; lia| clear - HX; lia]. }
        assert (EC3 : rw_cells asegs m3 (P + 440) [C4 e]) by (apply (KV _ _ EC2); simpl_sizes; lia).
        eapply (decQ q' A len cap cur idx r meth pos bs w24' v1' v2' e); [exact RR| exact IDX| exact INV3| exact CTX3| exact TOK| exact PS3| exact SCR3| exact PMJ3| exact PMN3| exact EC3
          | apply (K13 _ _ MC1); simpl_sizes; lia| apply (K13 _ _ PC1); simpl_sizes; lia| |].
        *
          intros m4 t1 t5 t6 t7 t10 t11 t12 t13 t14 t15 t16 t17 t28 t29 t30 t31 INV4 CTX4 EC4 MC4 PC4 KD MV4.
          eapply (KK m4 3 meth pos junk' v1' v2' (wz 505)); [left; repeat split; right; right; reflexivity| exact INV4| exact CTX4
            | apply KD; [apply (K13 _ _ UBC1); simpl_sizes; lia| simpl_sizes; lia]| apply KD; [apply (K13 _ _ UC1); simpl_sizes; lia| simpl_sizes; lia]
            | apply (KD _ _ PMJ3); simpl_sizes; lia| apply (KD _ _ PMN3); simpl_sizes; lia| exact EC4| exact MC4| exact PC4
            | | exact (wmove_trans _ _ _ _ MV1 (wmove_trans _ _ _ _ MV2 (wmove_trans _ _ _ _ MV3 MV4)))].
          intros X cs HC1 HX. apply KD; [apply K13; [apply (KC _ _ HC1); clear - HX; lia| clear - HX; lia]| clear - HX; lia].
        * intros m4 id t1 t5 t6 t7 t10 t11 t12 t13 t14 t15 t16 t17 t28 t29 t30 t31 IDR INV4 CTX4 MC4 PC4 EC4 KD MV4.
          eapply (KK m4 4 id 2 junk' v1' v2' e); [right; repeat split; [lia| lia]| exact INV4| exact CTX4
            | apply KD; [apply (K13 _ _ UBC1); simpl_sizes; lia| simpl_sizes; lia]| apply KD; [apply (K13 _ _ UC1); simpl_sizes; lia| simpl_sizes; lia]
            | apply (KD _ _ PMJ3); simpl_sizes; lia| apply (KD _ _ PMN3); simpl_sizes; lia| exact EC4| exact MC4| exact PC4
            | | exact (wmove_trans _ _ _ _ MV1 (wmove_trans _ _ _ _ MV2 (wmove_trans _ _ _ _ MV3 MV4)))].
          intros X cs HC1 HX. apply KD; [apply K13; [apply (KC _ _ HC1); clear - HX; lia| clear - HX; lia]| clear - HX; lia].
  Qed.

  #[using="IC m0 POK RF0 mws MWL"] Lemma skip0Q : forall (q' : Z) (ty tb tl : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz 0); C4 (wz 0)] -> rw_cells asegs m (P + 400) (mbuf_cells 0 0 0) ->
    shw m P 504 -> shw m SEPTAB_A 20 -> shz m (sh lo) (sh q) -> pscrT q' ty tb tl m ->
    (forall r m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       (r = 1 \/ r = 3) -> pinvQS qshadowU q' m' -> rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz 0); C4 (wz 0)] -> munch (rWT q') m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregsQ q' y1 y5 y6 y7 (wz r) y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz PQ_REJOIN) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31) F_ (wz 0x8b1dc) fc None m (seg_rom asegs)).
  Proof.
    intros q' ty tb tl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m Q INV SC MBC SHP SHSEP SHZ SCR KF.
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & _).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct SCR as (j0 & j224 & j256 & QC).
    split_chunk QC 26%nat QLOW TOKC. split_chunk TOKC 1%nat TYC TKC.
    change (q' + Z.of_nat 196) with (q' + 260) in TYC.
    unfold H_pparse_seg.pregsQ.
    zstep. zstep. zstep. step.
    assert (B0 : bytes_at asegs m 0 []) by (apply bytes_at_nil; lia).
    eapply evt_cut.
    { eapply (scanner_get_token_spec_A IC (P + 480) (q' + 264) (q' + 260) (P + 400) 0 0 0 0 lo [] tb tl ty q');
        [exact SC| exact MBC| exact B0| cbn [length Z.of_nat]; lia| lia| lia| lia| exact TKC| exact TYC| exact AE
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | eapply (tok_shwQ q'); [exact SHZ| exact QB| lia| lia| lia]
        | eapply (tok_shwQ q'); [exact SHZ| exact QB| lia| lia| lia]
        | intros HL; exfalso; lia
        | exact SHSEP
        | lia| lia| clear - PAL; Z.div_mod_to_equations; lia
        | lia| lia| clear - PAL; Z.div_mod_to_equations; lia
        | lia| left; lia| clear - QAL; Z.div_mod_to_equations; lia
        | lia| lia| clear - QAL; Z.div_mod_to_equations; lia
        | lia| cbn [length Z.of_nat]; lia| lia| lia| right; lia| right; lia| right; cbn [length Z.of_nat]; lia| left; cbn [length Z.of_nat]; lia
        | exact ST| exact CLO| lia| unfold A0_RT_STACK in *; lia| exact MI| reflexivity| reflexivity| reflexivity]. }
    intros ms' POST. unfold sgt_post_A in POST.
    destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & cur' & tb' & tl' & tyw' & -> & MUS & WMS & MI' & ST' & AE' & SC' & TKC' & TYC' & RES).
    assert (MUT : munch ((lo, q' + 280) :: [(P + 488, P + 496)])%Z m m') by (eapply munch_weaken; [exact (rWS_sub q' ltac:(clear - LO QB; lia))| exact MUS]).
    assert (QLOW' : rw_cells asegs m' q' [CB 48 j0; C8 (wz (Z.land (P + 4) 7 + 3)); C8 (wz (Z.land (P + 440) 7 + 3)); C8 (wz (Z.land (P + 448) 7 + 3));
                           C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (qSH (P + 4))); C8 (wz (P + 4)); C8 (wz (P + 8));
                           C8 (wz 18446744073708833343); C8 (wz F); C8 (wz F); C8 (wz (qSH (P + 432))); C8 (wz (P + 432));
                           C8 (wz (qSH (P + 440))); C8 (wz (P + 440)); C8 (wz (F + 64)); C8 (wz METHOD_TAB_A); C8 (wz (qSH (P + 488)));
                           C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32)); C8 (wz 2147450880);
                           CB 24 j224; C8 (wz F); CB 4 j256]).
    { eapply rw_cells_transport; [exact QLOW| exact MUS| exact WMS|]. unfold rWS. cbn [disjoint_from]. simpl_sizes. repeat split; try exact I; lia. }
    assert (SCR' : pscrT q' tyw' tb' tl' m').
    { exists j0, j224, j256. replace (q' + 264) with (q' + 260 + 4) in TKC' by lia. join_chunks TYC' TKC' H12. join_chunks QLOW' H12 HA. exact HA. }
    assert (HWc : Forall inP [(P + 488, P + 496)]%Z) by (unfold H_pparse_seg.inP; repeat constructor; cbn [fst snd]; lia).
    pose proof (pinv_stepT qshadowU eq_refl q' m m' _ INV MUT WMS MI' HWc ST' (pscr_join q' _ _ _ m' SCR')) as INV1.
    replace (ret_pc (Z_to_bv 64 0x8b1ec)) with (Z_to_bv 64 0x8b1ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RES as [(tlz & ty' & _ & _ & _ & _ & TL1 & -> & CL & _)|(HRr & -> & _)]; [exfalso; clear - TL1 CL; lia|].
    assert (RR : r = 1 \/ r = 3) by (unfold PARSE_INCOMPLETE, PARSE_FAILURE in HRr; lia).
    step. if_cases K1; zify_cond K1. 2:{ exfalso. destruct RR as [-> | ->]; revert K1; rewrite ?unsigned_lit by lia; lia. }
    step. step.
    eapply (KF r m'); [exact RR| exact INV1| exact SC'| exact MUT| exact WMS].
  Qed.
End RQ.
End W.
