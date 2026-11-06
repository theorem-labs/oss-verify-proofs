(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac MState Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit XA_leaves X8_A_kit X8_A_kit2 X8_A_kit3 X8_A_kit4 X8_A_kit5 X8_A_kit6 X8_A_kit13 X8_S_kit3 X8_M_kit2 X8_M_put4 AXImgKit X8_cobj X8_rsfree X8_SC4
     X8_asio_stmt_alloc X8_asio_stmt_reg X8_asio_stmt_reg2 X8_asio_stmt_reg3 X8_asio_stmt_sched3 X8_asio_stmt_sched4 X8_asio_stmt_sp2 X8_asio_stmt_use X8_A_shut X8_A_alloc X8_A_dobj X8_A_dsch
     X8_stream_stmt X8_stream_stmt2 X8_stream_stmt3 X8_sct_stmt X8_S_place X8_P_ftab_rep X8_pst X8_read_stmt X8_sro_stmt X8_bsd_stmt X8_dss_stmt
     AXFuzz_stmt X8_H_stmt X8_H_C X8_H_D X8_H_E X8_H_F X8_H_G X8_H_G2 X8_H_H X8_H_I0 X8_H_kit X8_H_kit2 X8_H_I X8_H_J X8_H_K X8_H_L X8_H_M X8_H_N0 X8_H_N X8_H_O X8_H_O2 X8_H_P0 X8_H_T0 X8_H_kit3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac uSZ := unfold NEWSZ_SCH, NEWSZ_CFG, NEWSZ_REG, NEWSZ_SSVC, SZ_SPCI_IMPL, SZ_SCH, SZ_ALLOCIMPL.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis ATR : incl TRLIST (as_TR H).
  Variable MA : Z.

  Lemma hz_E9 : forall (gp s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z))
      (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (m0 : mem) (mo : Model) (msF : machine_state) (mo9 : Model),
    hz_pure H sp ra D N lo B shi LB LF -> hz_cost9 H MA N <= as_AL H s ->
    as_chain H m0 (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
    trace_ok (as_TR H) APC0_FREE (P_HZ_RET_ADS :: bv_unsigned ra :: map snd CH) ->
    hzK9 H MA gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo (mkCfg msF mo9) ->
    as_SR H (hzK11 H MA gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo) (mkCfg msF mo9).
  Proof.
    intros until mo9. intros PU COST9 CHN CHB TRK2 K.
    pose proof PU as (SPAL & CEIL & LO & SPB & BHI & SP47 & RAE & NR & DAL & D0 & DNH & SHI & INB & DEMP & LFN & BUD & BUDC).
    unfold AFUZZ_STACK in LO. unfold AFUZZ_FRAMES in LFN.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (bv_unsigned_in_range 64 ra) as RAR. unfold bv_modulus in RAR. change (2 ^ Z.of_N 64) with (2^64) in RAR.
    pose proof (bv_unsigned_in_range 64 s0) as S0R. unfold bv_modulus in S0R. change (2 ^ Z.of_N 64) with (2^64) in S0R.
    pose proof aceil_facts as (AF1 & AF2 & AF3).
    assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; lia).
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & _).
    unfold hzK9 in K. cbn [cfg_ms cfg_model] in K.
    destruct K as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m9 & errv & s9' & spa & ff & fp & gap & p1 & allocb & p2 & regb & p3 & cfgb & p4 & schedb & j8 & j4 & j16 & j40 & j40b & j472 & XS & stb & L & FBB & FB & fds
 & VIS & SPA & FF & KREL & MP & HP0 & HP & PERM & FOK & FBU & CPM & FRF & HZF & REG & AI & XI & CA & HS & ERR & AUX & MI & ST & RF & AC & SK & FXS & X0 & AL).
    assert (SPAR : bv_unsigned sp + -208 <= spa <= bv_unsigned sp + -192) by (clear - SPA; lia).
    assert (SPA16 : spa mod 16 = 0) by (clear - SPA SPAL SPR; Z.div_mod_to_equations; lia).
    assert (CEIL' : aceil <= spa) by (clear - CEIL LO SPAR; lia).
    pose proof (ff_facts _ _ _ _ _ FF) as (_ & _ & _ & _ & F1 & F2 & F3 & F3' & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & APF & APP1 & SHFF & SF1 & SF2 & SF3 & NSB).
    fs_nums_in F2. fs_nums_in F9. fs_nums_in SF2. fs_nums_in SF3. fs_nums_in APF.
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO in F1, F2, F4, F5, F6, F7, F8, F9, F10, F11, SF1, SF2, SF3, NSB.
    pose proof (aapp_not_shadowland _ _ APF) as NSF. unfold ALOWSH_LO, AHI_LO in NSF.
    set (OURS := [(p2, regb, NEWSZ_REG); (p1, allocb, SZ_ALLOCIMPL)]) in *.
    assert (INr : forall b, In b (OURS ++ FBB ++ LB) -> In b L) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
    assert (JN1 : In (p1, allocb, SZ_ALLOCIMPL) L) by (apply INr; apply in_or_app; left; subst OURS; right; left; reflexivity).
    assert (JN2 : In (p2, regb, NEWSZ_REG) L) by (apply INr; apply in_or_app; left; subst OURS; left; reflexivity).
    assert (SUB0 : forall b, In b LB -> In b L) by (intros b Hb; apply INr; apply in_or_app; right; apply in_or_app; right; exact Hb).
    pose proof (ah_nodup H HH _ _ _ HP) as NDL. pose proof (NoDup_ids_perm _ _ PERM NDL) as NDO.
    pose proof (NoDup_ids_app_l _ _ NDO) as ND4. subst OURS. cbn [map blk_id fst snd] in ND4.
    pose proof (NoDup_nth_neq _ 1 0 p1 p2 ND4 eq_refl eq_refl ltac:(discriminate)) as N12.
    pose proof (ah_blocks H HH _ _ _ _ HP JN2) as (R1 & _ & R3 & R4 & R5 & R6 & R7). pose proof (ah_blocks H HH _ _ _ _ HP JN1) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    cbn [blk_addr blk_size fst snd] in R1, R3, R4, R5, R6, R7, A1, A2, A3, A4, A5, A6, A7. unfold NEWSZ_REG, SZ_ALLOCIMPL, AIMG_TOP, AFS_SIZE in R3, R4, R5, R6, A3, A4, A5, A6.
    destruct HZF as (LOC & BS & GAP & GSZ & SAVED & SSZ & FRMh & FRMi & FRMB & SH & SHSZ & FL).
    pose proof FRMi as IOC. apply (proj1 (rw_cells_app asegs m9 _ [_] _)) in IOC. destruct IOC as [_ IOC]. cbn [cells_size csize Nat.add length] in IOC.
    apply (proj1 (rw_cells_app asegs m9 _ [_; _; _] _)) in IOC. destruct IOC as [IOC _]. replace (ff + 88 + Z.of_nat 40) with (ff + 128) in IOC by (clear; lia).
    uSZ.
    idtac "E9 start".
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| |].
    { eapply hz_G5; [exact IOC| exact BS| clear - F1; lia| clear - F2 AF1; lia| exact CEIL'| clear - SPAR SP47; lia| exact SPA16| exact MI]. }
    intros msF10 mo10 KREL10 MP10 PO. destruct PO as (m10 & VIS10 & MU10 & WM10 & MI10 & BS10).
    idtac "E9 after G5".
    set (W10 := [(spa + 16, spa + 24)]%Z) in *.
    pose proof (stack_window_ok H L ((4, ff, fp) :: LF) (spa + 16) (spa + 24) ltac:(clear - CEIL'; lia) ltac:(pose proof (RFS_fsb H HH _ _ RF) as (_ & K & _); exact K)) as (CW1 & CW2 & CW3).
    assert (CW10 : Forall (aclient_write_ok H L) W10) by (subst W10; apply Forall_cons; [exact CW1| apply Forall_nil]).
    pose proof (ah_RHEAP_frame H HH _ _ _ _ _ HP MU10 WM10 CW10) as HP10. pose proof (ah_rauxv_frame H HH L _ _ _ _ AUX MU10 WM10 CW10) as AUX10.
    assert (RF10 : as_RFS H ((4, ff, fp) :: LF) m10) by (eapply (ah_RFS_frame H HH); [exact RF| exact MU10| exact WM10| subst W10; apply Forall_cons; [exact CW2| apply Forall_nil]]).
    assert (AC10 : ACONST m10) by (eapply ACONST_frame; [exact AC| exact MU10| exact WM10| subst W10; apply Forall_cons; [exact CW3| apply Forall_nil]]).
    assert (SK10 : stack0 m10 lo shi) by (eapply stack0_transport; [exact SK| exact MU10| exact WM10| subst W10; apply Forall_cons; [apply stack0_ok_app; cbn [fst snd]; unfold AHI_LO; clear - CEIL' AF1; lia| apply Forall_nil]]).
    assert (ST10 : stk asegs m10 lo spa) by (eapply stk_transport_disjoint; [exact ST| exact MU10| exact WM10| subst W10; cbn [disjoint_from fst snd]; clear - LO SPAR; lia]).
    assert (LOC10 : rw_cells asegs m10 spa [CB 8 j8; C8 (Z_to_bv 64 ff)]) by (eapply rw_cells_transport; [exact LOC| exact MU10| exact WM10| subst W10; cbn; clear; lia]).
    pose proof (rw_cells_bound _ _ _ _ GAP) as GB.
    assert (GAP10 : rw_cells asegs m10 (spa + 96) gap) by (eapply rw_cells_transport; [exact GAP| exact MU10| exact WM10| subst W10; rewrite GSZ; cbn; clear - SPAR; lia]).
    assert (SAVED10 : rw_cells asegs m10 (bv_unsigned sp + -96) (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      by (eapply rw_cells_transport; [exact SAVED| exact MU10| exact WM10| subst W10; unfold hz_saved; cbn; clear - SPAR; lia]).
    assert (FRMh10 : rw_cells asegs m10 ff (hz_hdr spa ++ [C8 (Z_to_bv 64 AVP_CFGMAKER); C4 (wz 4294967295); CB 4 j4] ++ [CB 16 j16]))
      by (eapply rw_cells_transport; [exact FRMh| exact MU10| exact WM10| subst W10; unfold hz_hdr; cbn; clear - F2 CEIL' AF1; lia]).
    assert (FRMi10 : rw_cells asegs m10 (ff + 88) ([CB 40 j40] ++ [C8 (Z_to_bv 64 allocb); C8 (Z_to_bv 64 regb); C8 (Z_to_bv 64 schedb)] ++ [CB 40 j40b]))
      by (eapply rw_cells_transport; [exact FRMi| exact MU10| exact WM10| subst W10; cbn; clear - F2 CEIL' AF1; lia]).
    assert (FRMB10 : rw_cells asegs m10 (ff + 544) [CB 472 j472; C8 (Z_to_bv 64 fp)])
      by (eapply rw_cells_transport; [exact FRMB| exact MU10| exact WM10| subst W10; cbn; clear - F2 CEIL' AF1; lia]).
    assert (SH10 : rw_cells asegs m10 (Z.shiftr ff 3 + 2147450880) hz_sh2)
      by (eapply rw_cells_transport; [exact SH| exact MU10| exact WM10| subst W10; rewrite SHSZ; cbn [disjoint_from fst snd]; rewrite SHFF; clear - SF2 CEIL' AF1; lia]).
    assert (FL10 : rw_cells asegs m10 fp [C1 (b8 1)]) by (eapply rw_cells_transport; [exact FL| exact MU10| exact WM10| subst W10; cbn; clear - F5 F6 F7 F10 F2 F1 CEIL' AF1; lia]).
    assert (FW : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W10) by (subst W10; unfold AIMG_TOP; apply Forall_cons; [cbn [fst snd]; clear - CEIL' AF1; lia| apply Forall_nil]).
    pose proof (HS_munch_lo (AHStat FT) (AHStat_local FT FT_local) _ _ _ HS MU10 FW) as HS10. pose proof (AXImg_munch_lo _ _ _ XI MU10 FW) as XI10.
    pose proof (acanary_munch_lo _ _ _ CA MU10 WM10 FW) as CA10.
    assert (ERR10 : rw_cells asegs m10 AERRNO [C4 errv]) by (eapply rw_cells_transport; [exact ERR| exact MU10| exact WM10| subst W10; cbn; unfold AERRNO, ATP; clear - CEIL' AF1; lia]).
    assert (AW : Forall awin W10) by (subst W10; apply Forall_cons; [apply awin_stack; clear - CEIL'; lia| apply Forall_nil]).
    assert (REG10 : ARegistry L m10 regb (ff + 128) 0 0) by (eapply ARegistry_transport_awin; [exact REG| exact MU10| exact WM10| exact AW| subst W10; cbn [disjoint_from fst snd]; uSZ; clear - R5 CEIL'; lia]).
    assert (AI10 : AAllocImpl L m10 allocb) by (eapply AAllocImpl_transport_awin; [exact AI| exact MU10| exact WM10| exact AW| subst W10; cbn [disjoint_from fst snd]; uSZ; clear - A5 CEIL'; lia]).
    assert (FBU10 : AFlatBuf L m10 (spa + 48) FB fds).
    { eapply AFlatBuf_transport_awin; [exact FBU| exact MU10| exact WM10| exact AW| subst W10; cbn [disjoint_from fst snd]; unfold SZ_FB; clear; lia|].
      intros NE. destruct FBU as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & RBF & CAP & _)]; [exfalso; exact (NE E0)|].
      pose proof (ah_blocks H HH _ _ _ _ HP INp) as (_ & _ & _ & _ & K5 & _). cbn [blk_addr blk_size fst snd] in K5. subst W10. cbn [disjoint_from fst snd]. unfold fb_cap in K5 |- *. clear - K5 CEIL'. lia. }
    assert (XP10 : xpres H L spa (W10 ++ []) m9 m10).
    { rewrite app_nil_r. eapply (xpres_of_munch H); [exact HH| exact HP| exact MU10| exact WM10|]. subst W10. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. intros a Q. cbn. clear - Q. lia. }
    pose proof (rw_cells_ro_cell asegs m10 _ _ 0 _ BS10 eq_refl) as ATR0. rewrite Z.add_0_r in ATR0.
    clear LOC BS GAP SAVED FRMh FRMi FRMB SH FL XI CA HS ERR REG AI FBU MI ST RF AC SK AUX.
    idtac "E9 at dreg".
    (* [comment removed for export] *)
    pose proof (dealloc_obj_registry_spec H HH ATR) as SD. unfold dealloc_obj_registry_stmt in SD.
    eapply (ah_seq H HH).
    { eapply SD with (AT := spa + 16) (r := regb) (allocb := allocb) (owner := ff + 128) (first := 0) (lk := 0) (lo := lo) (B := B) (shi := shi) (LB := L)
                     (LF := (4, ff, fp) :: LF) (s := s9') (errv := errv);
        [ exact VIS10 | reflexivity | reflexivity
        | unfold wz; exact ATR0
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); clear; lia
        | clear - SHI SPAR; lia | clear - SPA16; Z.div_mod_to_equations; lia
        | exact REG10 | exact AI10 | exact (AXStatics2_of_AXImg _ XI10) | exact HP10 | exact KREL10 | exact AUX10
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); clear - SPB SPAR; lia
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); exact ST10 | exact CEIL
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); unfold ADOBJ_STACK, ADEALLOCATE_STACK, AFREE_STACK; clear - LO SPAR; lia
        | rewrite EA; exact ERR10 | exact MI10 | reflexivity
        | unfold P_HZ_RET_DRG; rewrite unsigned_lit by (clear; lia); reflexivity
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); exact SPA16
        | exact RF10 | exact AC10 | exact SK10
        | unfold hz_cost9, hz_cost8 in COST9; pose proof (CF0 SZ_ALLOCIMPL ltac:(uSZ; clear; lia)) as K0; clear - AL COST9 K0; lia ]. }
    idtac "E9 after dreg".
    intros [msF11 mo11] PO. unfold dealloc_obj_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m11 & s11' & bp & VIS11 & KREL11 & MP11 & MI11 & ST11 & ERR11 & AUX11
                    & INs & HP11 & AI11 & XS11s & APC & RF11 & AC11 & SK11 & AL11).
    rewrite (unsigned_lit spa) in ST11, APC by (clear - SPAR SPR CEIL LO AF1; lia). rewrite EA in ERR11. clear SD.
    pose proof (proj1 (in_pin H HH _ _ _ _ _ _ _ _ HP10 JN2 INs)) as ->.
    set (L11 := as_lb_remove H p2 L) in *.
    pose (XS11 := ([] : list (Z * Z))). assert (FXS11 : Forall (fs_scratch H ((4, ff, fp) :: LF)) XS11) by (subst XS11; apply Forall_nil).
    set (X := [(regb, regb + NEWSZ_REG)]%Z) in *.
    assert (XPC : xpres H L11 spa (X ++ XS11) m10 m11) by (eapply (xpres_of_apres H); exact APC).
    assert (PN11 : Permutation L11 ([(p1, allocb, SZ_ALLOCIMPL)] ++ FBB ++ LB) /\ (forall b, In b L11 -> In b L)).
    { subst L11. destruct (bperm_free H HH _ _ _ NDL PERM) as [PE1 ND1]. cbn [blk_id fst snd app] in PE1. split; [exact PE1|].
      intros b Hb. exact ((proj2 (proj2 (ah_lb_remove H HH))) _ _ _ Hb). }
    destruct PN11 as [PERM11 SUB11].
    assert (INr11 : forall b, In b ([(p1, allocb, SZ_ALLOCIMPL)] ++ FBB ++ LB) -> In b L11).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM11| exact Hb]. }
    assert (FBX : Forall (blockish L) X) by (subst X; apply Forall_cons; [eapply blockish_blk; [exact JN2| clear; lia| clear; lia]| apply Forall_nil]).
    assert (FLX : Forall (fun iv : Z * Z => fst iv < snd iv) X) by (subst X; apply Forall_cons; [cbn; uSZ; clear; lia| apply Forall_nil]).
    pose proof (hz_frame2_keep H HH _ _ _ _ _ _ _ _ _ X XS11 m10 m11 spa (bv_unsigned sp) allocb regb schedb stb j8 j4 j16 j40 j40b j472 gap (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) hz_sh2
                  HP10 HP11 RF10 FF CEIL' ltac:(clear - SPAR; lia) FBX FLX FXS11 XPC
                  (conj LOC10 (conj BS10 (conj GAP10 (conj GSZ (conj SAVED10 (conj SSZ (conj FRMh10 (conj FRMi10 (conj FRMB10 (conj SH10 (conj SHSZ FL10)))))))))))) as HZF11.
    pose proof (hz_statics_keep H HH _ _ _ _ _ _ _ X XS11 m10 m11 spa errv HP10 RF10 FF FBX FLX FXS11 XPC (conj XI10 (conj CA10 (conj HS10 ERR10)))) as (XI11 & CA11 & HS11 & _).
    idtac "E9 frame kept".
    assert (KP : forall b0, In b0 L11 -> keeps_at L L11 (blk_addr b0)) by (intros b0 Hb0; eapply (reix_sub H HH); [exact HP10| exact SUB11| exact Hb0]).
    assert (JN1' : In (p1, allocb, SZ_ALLOCIMPL) L11) by (apply INr11; left; reflexivity).
    assert (FBU11 : AFlatBuf L11 m11 (spa + 48) FB fds).
    { pose proof (Forall_blockish_lo H HH _ _ _ _ _ _ _ HP FF FBX FLX) as XLO.
      eapply (AFlatBuf_xpres H); [| exact XPC| | |].
      { eapply (AFlatBuf_reix L L11); [| exact FBU10]. destruct FOK as [[-> ->]|(NE & pf0 & ->)].
        - intros p n IN. exfalso. pose proof (ah_blocks H HH _ _ _ _ HP IN) as (K1 & _). cbn in K1. clear - K1. lia.
        - exact (KP (pf0, fb_begin FB, fb_cap FB) ltac:(apply INr11; apply in_or_app; right; apply in_or_app; left; left; reflexivity)). }
      - split; [left; clear; lia|]. apply Forall_app. split.
        + eapply Forall_impl; [| exact XLO]. intros [l h'] [_ Q]. cbn [fst snd] in *. unfold SZ_FB. clear - Q CEIL'. lia.
        + subst XS11. apply Forall_nil.
      - intros NE. destruct FOK as [[E0 _]|(_ & pf0 & EFBB)]; [exfalso; exact (NE E0)|].
        destruct FBU10 as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & _ & CAP & _)]; [exfalso; exact (NE E0)|].
        assert (INf : In (pf0, fb_begin FB, fb_cap FB) L) by (apply INr; apply in_or_app; right; apply in_or_app; left; rewrite EFBB; left; reflexivity).
        pose proof (proj1 (in_pin H HH _ _ _ _ _ _ _ _ HP INf INp)) as ->.
        assert (NF : pf0 <> p2). { intros E. rewrite EFBB in NDO. rewrite map_app in NDO. cbn [map blk_id fst snd app] in NDO. apply (NoDup_app_disjoint [p2; p1] (pf0 :: map blk_id LB) pf0 NDO); [rewrite E; left; reflexivity| left; reflexivity]. }
        pose proof (blocks_neq_disjoint H HH _ _ _ _ _ HP INp JN2 ltac:(intros E; injection E; intros; exact (NF ltac:(assumption)))) as D1. cbn [blk_addr blk_size fst snd] in D1. unfold NEWSZ_REG in D1.
        apply Forall_app. split; [| subst XS11; apply Forall_nil].
        subst X. apply Forall_cons; [cbn [fst snd]; unfold fb_cap in D1 |- *; uSZ; clear - D1; lia| apply Forall_nil].
      - intros NE. destruct FOK as [[E0 _]|(_ & pf0 & EFBB)]; [exfalso; exact (NE E0)|].
        destruct FBU10 as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & RBF & CAP & _)]; [exfalso; exact (NE E0)|].
        pose proof (rblock_bounds _ _ RBF) as (B0 & _ & B2 & _).
        pose proof (aapp_disjoint_sh regb NEWSZ_REG (fb_begin FB) (fb_cap FB) R7 B0 B2 ltac:(clear - CAP; lia)) as U2. unfold NEWSZ_REG in U2.
        apply Forall_app. split; [| subst XS11; apply Forall_nil].
        subst X. apply Forall_cons; [cbn [fst snd]; uSZ; clear - U2; lia| apply Forall_nil]. }
    idtac "E9 world 11".
    (* [comment removed for export] *)
    set (XALL := ((fr4_XS H ff fp ++ [(AERRNO, AERRNO + 4); (AXH_LO, AXH_HI)]%Z) ++ XS)) in *.
    assert (X011 : xpres H LB (bv_unsigned sp) XALL m0 m11).
    { eapply (xpres_trans H); [exact X0|]. eapply (xpres_trans H).
      - eapply (xpres_of_munch H); [exact HH| exact HP0| exact MU10| exact WM10|]. subst W10. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear - CEIL' SPAR; lia.
      - eapply xpres_reLB; [exact XPC|]. intros a Ha C NX. split.
        + eapply aclient_addr_weaken; [exact C| clear - SPAR; lia| intros b Hb; apply INr11; apply in_or_app; right; apply in_or_app; right; exact Hb].
        + intros K0. apply rin_ivs_app in K0. destruct K0 as [K0|K0]; [| subst XS11; exact K0].
          subst X. cbn [rin_ivs fst snd] in K0.
          assert (C' : aclient_addr H LB spa a) by (eapply aclient_addr_weaken; [exact C| clear - SPAR; lia| intros b Hb; exact Hb]).
          assert (FR : forall b', In b' LB -> blk_id b' <> p2).
          { intros b' Hb' E. rewrite map_app in NDO. eapply (NoDup_app_disjoint _ _ p2 NDO); [left; reflexivity|]. rewrite map_app. apply in_or_app. right. rewrite <- E. apply in_map. exact Hb'. }
          pose proof (X8_A_kit6.new_block_outside H HH _ _ _ _ _ _ LB spa a HP JN2 SUB0 FR CEIL' C') as W1. unfold NEWSZ_REG in W1, K0. clear - K0 W1. lia. }
    idtac "E9 xpres 11".
    (* [comment removed for export] *)
    pose proof HZF11 as (LOC11 & BS11 & GAP11 & _ & SAVED11 & _ & FRMh11 & FRMi11 & FRMB11 & SH11 & _ & FL11).
    assert (CHN11 : as_chain H m11 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { apply (ah_chain_cons H HH) with (cur := bv_unsigned s0); [| clear - S0R; lia| clear - RAR; lia| exact SPAL| clear - CEIL LO; lia| clear - SPR; lia|].
      - eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a IN Ha. pose proof (CHB _ _ IN) as FPB.
        pose proof (ah_chain_range H HH _ _ _ _ _ CHN IN) as (CR1 & _).
        assert (XC : xclient H LB (bv_unsigned sp) XALL a).
        { split; [left; clear - Ha FPB; lia|]. apply not_rin_of_Forall. subst XALL. apply Forall_app. split.
          + unfold fr4_XS. fs_nums. repeat apply Forall_cons; [| | | | | | apply Forall_nil]; cbn [fst snd]; unfold AERRNO, ATP, AXH_LO, AXH_HI; rewrite ?SHFF;
              clear - Ha FPB F2 F4 F5 F6 F7 F10 F11 SF1 SF2 CEIL LO AF1 AF2 AF3; lia.
          + eapply Forall_impl; [| exact FXS]. intros iv SC. pose proof (scratch_facts H HH _ _ [] iv RF11 SC) as (_ & _ & K3). right. clear - K3 Ha FPB CEIL LO. lia. }
        exact (proj1 (X011 a ltac:(clear - Ha CR1 AF1; lia) XC)).
      - rewrite !Z_to_bv_bv_unsigned. pose proof SAVED11 as K0. unfold hz_saved in K0.
        apply (proj1 (rw_cells_app asegs m11 _ [_; _; _; _; _; _; _; _; _; _] [_; _])) in K0. destruct K0 as [_ K0].
        cbn [cells_size csize Nat.add length] in K0. replace (bv_unsigned sp + -96 + Z.of_nat 80) with (bv_unsigned sp - 16) in K0 by (clear; lia). exact K0. }
    idtac "E9 chain".
    (* [comment removed for export] *)
    pose proof FRMi11 as IOC11. apply (proj1 (rw_cells_app asegs m11 _ [_] _)) in IOC11. destruct IOC11 as [_ IOC11]. cbn [cells_size csize Nat.add length] in IOC11.
    apply (proj1 (rw_cells_app asegs m11 _ [_; _; _] _)) in IOC11. destruct IOC11 as [IOC11 _]. replace (ff + 88 + Z.of_nat 40) with (ff + 128) in IOC11 by (clear; lia).
    pose proof AI11 as (pa & junk & INa & OBJ & RBA & ADA).
    pose proof (proj1 (in_pin H HH _ _ _ _ _ _ _ _ HP11 JN1' INa)) as ->.
    eapply (ahh_evt_then H HH); [exact KREL11| exact VIS11| |].
    { eapply hz_G6 with (junk := junk); [exact IOC11| exact OBJ| exact ADA| exact A1| uSZ; clear - A5; lia| exact A2| exact XS11s| exact AC11| exact MI11]. }
    intros msF12 mo12 KREL12 MP12 (a2v & VIS12).
    idtac "E9 at ads".
    (* [comment removed for export] *)
    pose proof (allocimpl_destroy_spec H HH) as SD. unfold allocimpl_destroy_stmt in SD.
    eapply (ah_seq H HH).
    { eapply SD with (p := p1) (a := allocb) (lo := lo) (B := B) (LB := L11) (s := s11') (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH) (junk := junk);
        [ exact VIS12 | reflexivity | exact JN1' | exact OBJ | exact ADA | exact XS11s | exact HP11 | exact KREL12 | exact AUX11
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); clear - SPB SPAR; lia
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); exact ST11 | exact CEIL
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); unfold AALLOCIMPL_DESTROY_STACK, AFREE_STACK; clear - LO SPAR; lia
        | rewrite EA; exact ERR11 | exact MI11 | reflexivity
        | unfold P_HZ_RET_ADS; rewrite unsigned_lit by (clear; lia); reflexivity
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); exact SPA16
        | exact AC11
        | exact CHN11
        | unfold P_HZ_RET_ADS; rewrite unsigned_lit by (clear; lia); cbn [map snd]; exact TRK2
        | rewrite unsigned_lit by (clear - SPAR SPR CEIL LO AF1; lia); intros fp' ra' [E|IN]; [injection E; intros <- <-; clear - SPAR; lia| pose proof (CHB _ _ IN); clear - H0 SPAR; lia]
        | unfold hz_cost9, hz_cost8 in COST9; clear - AL AL11 COST9; lia ]. }
    idtac "E9 after ads".
    intros [msF13 mo13] PO. unfold free_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (g0 & g1 & g2 & k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & g3 & g4 & g5 & g6 & m13 & s13' &
                    VIS13 & KREL13 & MP13 & MI13 & ST13 & ERR13 & AUX13 & RP13 & HP13 & AC13 & AL13).
    rewrite (unsigned_lit spa) in ST13, RP13 by (clear - SPAR SPR CEIL LO AF1; lia). rewrite EA in ERR13. clear SD.
    set (L13 := as_lb_remove H p1 L11) in *.
    pose proof (RFS_via_apres H HH _ _ _ _ _ RF11 RP13) as RF13.
    assert (SK13 : stack0 m13 lo shi) by (eapply (stack0_xpres H); [eapply xpres_of_apres; exact RP13| exact SK11| constructor]).
    set (X3 := [(allocb, allocb + SZ_ALLOCIMPL)]%Z) in *.
    assert (XPC3 : xpres H L13 spa (X3 ++ XS11) m11 m13) by (eapply (xpres_of_apres H); exact RP13).
    pose proof (NoDup_ids_perm _ _ PERM11 (ah_nodup H HH _ _ _ HP11)) as NDO11.
    assert (PN13 : Permutation L13 (FBB ++ LB) /\ (forall b, In b L13 -> In b L11)).
    { subst L13. destruct (bperm_free H HH _ _ _ (ah_nodup H HH _ _ _ HP11) PERM11) as [PE1 ND1]. cbn [blk_id fst snd app] in PE1. split; [exact PE1|].
      intros b Hb. exact ((proj2 (proj2 (ah_lb_remove H HH))) _ _ _ Hb). }
    destruct PN13 as [PERM13 SUB13].
    assert (INr13 : forall b, In b (FBB ++ LB) -> In b L13).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM13| exact Hb]. }
    assert (FBX3 : Forall (blockish L11) X3) by (subst X3; apply Forall_cons; [eapply blockish_blk; [exact JN1'| clear; lia| clear; lia]| apply Forall_nil]).
    assert (FLX3 : Forall (fun iv : Z * Z => fst iv < snd iv) X3) by (subst X3; apply Forall_cons; [cbn; uSZ; clear; lia| apply Forall_nil]).
    pose proof (hz_frame2_keep H HH _ _ _ _ _ _ _ _ _ X3 XS11 m11 m13 spa (bv_unsigned sp) allocb regb schedb stb j8 j4 j16 j40 j40b j472 gap (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) hz_sh2
                  HP11 HP13 RF11 FF CEIL' ltac:(clear - SPAR; lia) FBX3 FLX3 FXS11 XPC3 HZF11) as HZF13.
    pose proof (hz_statics_keep H HH _ _ _ _ _ _ _ X3 XS11 m11 m13 spa errv HP11 RF11 FF FBX3 FLX3 FXS11 XPC3 (conj XI11 (conj CA11 (conj HS11 ERR11)))) as (XI13 & CA13 & HS13 & _).
    idtac "E9 frame kept 13".
    assert (KP3 : forall b0, In b0 L13 -> keeps_at L11 L13 (blk_addr b0)) by (intros b0 Hb0; eapply (reix_sub H HH); [exact HP11| exact SUB13| exact Hb0]).
    assert (FBU13 : AFlatBuf L13 m13 (spa + 48) FB fds).
    { pose proof (Forall_blockish_lo H HH _ _ _ _ _ _ _ HP11 FF FBX3 FLX3) as XLO.
      eapply (AFlatBuf_xpres H); [| exact XPC3| | |].
      { eapply (AFlatBuf_reix L11 L13); [| exact FBU11]. destruct FOK as [[-> ->]|(NE & pf0 & ->)].
        - intros p n IN. exfalso. pose proof (ah_blocks H HH _ _ _ _ HP11 IN) as (K1 & _). cbn in K1. clear - K1. lia.
        - exact (KP3 (pf0, fb_begin FB, fb_cap FB) ltac:(apply INr13; apply in_or_app; left; left; reflexivity)). }
      - split; [left; clear; lia|]. apply Forall_app. split.
        + eapply Forall_impl; [| exact XLO]. intros [l h'] [_ Q]. cbn [fst snd] in *. unfold SZ_FB. clear - Q CEIL'. lia.
        + subst XS11. apply Forall_nil.
      - intros NE. destruct FOK as [[E0 _]|(_ & pf0 & EFBB)]; [exfalso; exact (NE E0)|].
        destruct FBU11 as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & _ & CAP & _)]; [exfalso; exact (NE E0)|].
        assert (INf : In (pf0, fb_begin FB, fb_cap FB) L11) by (apply INr11; apply in_or_app; right; apply in_or_app; left; rewrite EFBB; left; reflexivity).
        pose proof (proj1 (in_pin H HH _ _ _ _ _ _ _ _ HP11 INf INp)) as ->.
        assert (NF : pf0 <> p1). { intros E. rewrite EFBB in NDO11. cbn [map blk_id fst snd app] in NDO11. exact (NoDup_hd_ne _ _ _ NDO11 ltac:(left; exact E) eq_refl). }
        pose proof (blocks_neq_disjoint H HH _ _ _ _ _ HP11 INp JN1' ltac:(intros E; injection E; intros; exact (NF ltac:(assumption)))) as D1. cbn [blk_addr blk_size fst snd] in D1. unfold SZ_ALLOCIMPL in D1.
        apply Forall_app. split; [| subst XS11; apply Forall_nil].
        subst X3. apply Forall_cons; [cbn [fst snd]; unfold fb_cap in D1 |- *; uSZ; clear - D1; lia| apply Forall_nil].
      - intros NE. destruct FOK as [[E0 _]|(_ & pf0 & EFBB)]; [exfalso; exact (NE E0)|].
        destruct FBU11 as (_ & FOK' & _). destruct FOK' as [E0|(pf' & INp & RBF & CAP & _)]; [exfalso; exact (NE E0)|].
        pose proof (rblock_bounds _ _ RBF) as (B0 & _ & B2 & _).
        pose proof (aapp_disjoint_sh allocb SZ_ALLOCIMPL (fb_begin FB) (fb_cap FB) A7 B0 B2 ltac:(clear - CAP; lia)) as U2. unfold SZ_ALLOCIMPL in U2.
        apply Forall_app. split; [| subst XS11; apply Forall_nil].
        subst X3. apply Forall_cons; [cbn [fst snd]; uSZ; clear - U2; lia| apply Forall_nil]. }
    idtac "E9 world 13".
    assert (X013 : xpres H LB (bv_unsigned sp) XALL m0 m13).
    { eapply (xpres_trans H); [exact X011|]. eapply xpres_reLB; [exact XPC3|]. intros a Ha C NX. split.
      + eapply aclient_addr_weaken; [exact C| clear - SPAR; lia| intros b Hb; apply INr13; apply in_or_app; right; exact Hb].
      + intros K0. apply rin_ivs_app in K0. destruct K0 as [K0|K0]; [| subst XS11; exact K0].
        subst X3. cbn [rin_ivs fst snd] in K0.
        assert (C' : aclient_addr H LB spa a) by (eapply aclient_addr_weaken; [exact C| clear - SPAR; lia| intros b Hb; exact Hb]).
        assert (FR : forall b', In b' LB -> blk_id b' <> p1).
        { intros b' Hb' E. rewrite map_app in NDO. eapply (NoDup_app_disjoint _ _ p1 NDO); [right; left; reflexivity|]. rewrite map_app. apply in_or_app. right. rewrite <- E. apply in_map. exact Hb'. }
        pose proof (X8_A_kit6.new_block_outside H HH _ _ _ _ _ _ LB spa a HP JN1 SUB0 FR CEIL' C') as W1. unfold SZ_ALLOCIMPL in W1, K0. clear - K0 W1. lia. }
    idtac "E9 xpres 13".
    apply (ah_done H HH). unfold hzK11. cbn [cfg_ms cfg_model].
    exists g0, g1, g2, k0, k1, k2, k3, k4, k5, k6, k7, g3, g4, g5, g6, m13, errv, s13', spa, ff, fp, gap.
    exists allocb, regb, schedb, j8, j4, j16, j40, j40b, j472, XS, stb, L13, FBB, FB, fds.
    split; [exact VIS13|]. split; [exact SPA|]. split; [exact FF|]. split; [exact KREL13|].
    split; [exact (ah_mpres_trans H HH _ _ _ MP (ah_mpres_trans H HH _ _ _ MP10 (ah_mpres_trans H HH _ _ _ MP11 (ah_mpres_trans H HH _ _ _ MP12 MP13))))|]. split; [exact HP0|].
    split; [exact HP13|]. split; [exact PERM13|]. split; [exact FOK|].
    split; [exact FBU13|]. split; [exact CPM|]. split; [exact FRF|]. split; [exact HZF13|].
    split; [exact XI13|]. split; [exact CA13|]. split; [exact HS13|].
    split; [exact ERR13|]. split; [exact AUX13|]. split; [exact MI13|]. split; [exact ST13|].
    split; [exact RF13|]. split; [exact AC13|]. split; [exact SK13|].
    split; [exact FXS|]. split; [subst XALL; exact X013|].
    unfold hz_cost9, hz_cost8. clear - AL AL11 AL13. lia.
  Qed.
End HCW.
