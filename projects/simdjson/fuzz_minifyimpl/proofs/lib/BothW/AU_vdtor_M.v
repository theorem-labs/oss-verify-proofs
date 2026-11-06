(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase MonadF AMalloc_iface ABytes F_apoison F_annot AAnnot_iface APoisonR_iface Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface AU_consts AHarnessU_iface AU_parts_iface AU_client_kit AU_h_kit AU_fuzz_kit AU_first_A AU_first_C AU_first_M AU_vdtor_A AH_opdelete_top.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Ltac ag_of_hpr H := lazymatch type of H with aheap_pres ?CI ?LB ?SP ?m ?m' => change (aheap_pres CI LB SP m m') with (magree bsegs (aclient_addr CI LB SP) m m') in H end.
Ltac pick_in := (left; reflexivity) + (right; pick_in).
(* [comment removed for export] *)
Ltac xall MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    repeat match goal with
    | H : rw_cells _ mo ?A ?cs |- _ =>
        apply (rw_cells_transport bsegs W mo mn A cs) in H;
        [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul fst snd]; lia]
    | H : stk _ mo ?loq ?hiq |- _ =>
        apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia]
    end end.

(* [comment removed for export] *)
Definition bx (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?P => change P with (bx P) in H end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma aannotate_grow_prim : forall st p ch cap,
  (a_live st) !! p = Some ch -> achunk_kind_ok ch cap -> is_primary cap = true -> 0 < cap <= 2^40 -> cap mod 8 = 0 -> aannotate st p cap 0 cap = aret st.
Proof.
  intros st p ch cap L K PR HC C8. unfold aannotate. rewrite L.
  replace ((0 <=? 0) && (0 <=? cap) && (0 <=? cap) && (cap <=? cap))%bool with true by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le; lia).
  cbn [negb]. replace (2 ^ 40 <? cap) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 =? cap) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.land cap 7 =? 0) with true by (symmetry; apply Z.eqb_eq; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact C8).
  cbn [negb andb]. replace (0 <? cap) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct ch as [? ?|? ? ?]; [reflexivity|]. cbn in K. congruence.
Qed.

Section VD.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis OPDEL : opdelete_dataA AI.          (* [comment removed for export] *)
  Hypothesis AGROW : annot_grow_stmtA.
  Hypothesis AI_kind : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.

  Theorem avdtor_proof : avdtor_stmt AI.
  Proof.
    unfold avdtor_stmt, AVDTOR_STACK. intros until rstk.
    intros AH HIN HLB [IG USH] VEC VB MI FRM ST BOT LOS TOP SP16 RC RLO RHI RRLO TP -> -> RA4 RA2 HUL HUL1 RSTKTOP RSTK RI RISH RR ROK.
    set (SP := bv_unsigned sp) in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. fold SP in RSP. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (L1 & L2 & L3 & L4 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & BR & RP & RSHP & BSH & BWR & _ & ARENA).
    pose proof BR as (VH & _ & VTOP & V16). pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    destruct ARENA as (RLO' & RHI' & RL4 & RH4 & RLA & RHA & RRNG & RWR).
    destruct (AI_kind _ _ _ _ _ _ _ _ AH HIN) as (ch & CHL & CHS & CHU & CHK).
    (* [comment removed for export] *)
    assert (SV3 : shv3 m).
    { unfold shv3, shz. split; [| split]; (apply c1_of_byte; [vm_compute; discriminate| vm_compute; discriminate| apply USH; unfold client_sh_addrs; cbn [In]; tauto]). }
    assert (T0 : shc (SP + -16) m /\ rng RNG (Z.shiftr (SP + -16) 3 + 2147450880) 1).
    { destruct RC as [(UN & (HL1 & HL2 & HL3 & HL4 & HL5 & HL6) & _ & _) RLT]. split.
      - unfold shc. change 2147450880 with ASHOFF. eapply (fun U A B => proj1 (unpoisoned8_c1 m (SP + -16) U A B));
          [eapply unpoisoned_sub; [exact UN| lia| lia]| clear - SP16; fold SP in SP16; Z.div_mod_to_equations; lia| unfold KEND; lia].
      - eapply rng_sub'; [exact RR|]. rewrite !shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        clear - HL1 HL2 HL3 HL4 RLO RHI LOS RSP. Z.div_mod_to_equations. lia. }
    destruct T0 as [T0 RSS].
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT0 & _ & _ & SHB0 & _).
      eapply vd_a with (lo := lo) (V := V);
        first [exact ST| exact MI| exact GOT0| exact SHB0| exact VEC| exact SV3| exact T0| exact VH| exact V16| exact RI| exact RISH| exact RSS
              | fold SP; lia| (eapply rng_sub'; [exact RSTK| fold SP; lia])]. }
    cbv beta. fold SP. intros ms1 (m1 & y5 & y6 & y7 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU1 & WM1 & MI1 & ST1 & FRA1 & FRD1 & FRT1 & VEC1 & SV1 & T1).
    unfold AVEC in MU1.
    assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      left; right; left. exists (0x6afb00, 0x6afb40). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]. }
    pose proof (poison_cells_of_aheap AI _ _ _ _ _ AH1) as PC1.
    pose proof (annot_cells_of_aheap AI _ _ _ _ _ AH1 (hrt_cells_of_aheap AI _ _ _ _ _ AH1)) as AC1.
    pose proof (AI_rtcells AI _ _ _ _ _ AH1) as ARTC1. pose proof (AI_premap _ _ _ _ _ AH1) as PRM1. pose proof (arelro_of_aheap AI _ _ _ _ _ AH1) as REL1.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH1 HIN) as (_ & _ & _ & _ & BSH1 & _ & _ & ARENA1).
    destruct ARENA1 as (RLO1 & RHI1 & RL41 & RH41 & RLA1 & RHA1 & RRNG1 & RWR1).
    assert (SWR1 : wr_at bsegs m1 (shad V) (shlen (8 + 7))).
    { eapply (wr_at_sub bsegs _ _ _ _ _ RWR1); rewrite ?shad_div, ?shlenE; unfold ASHOFF; clear - RLA1 RHA1 RL41 VH1 VH2 VH4; Z.div_mod_to_equations; lia. }
    destruct (ablock_shadow_chunks m1 V 8 ltac:(lia) ltac:(clear - V16; Z.div_mod_to_equations; lia) ltac:(lia) BSH1 SWR1) as [BODY1 _].
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { eapply (annot_shrink_spec RNG) with (beg := V) (cap := 8) (lo := lo) (sb := Z_to_bv 8 0);
        rewrite ?unsigned_lit by lia;
        first [exact MI1| exact ST1| exact PC1| exact AC1| exact RI| exact BODY1| reflexivity
              | (change (rup8 8) with 8; exact VH) | (change (shlen (rup8 8)) with (shlen (8 + 7)); exact RSHP)
              | (intros NE; exfalso; apply NE; reflexivity)
              | (eapply rng_sub'; [exact RSTK| unfold ANNOT_STACK; lia]) | (clear - V16; Z.div_mod_to_equations; lia)
              | (change (rup8 8) with 8; lia) | unfold ANNOT_STACK; lia ]. }
    cbv beta. intros ms2 PO. destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SHK2).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in ST2 by lia. retlit.
    unfold ANNOT_STACK in MU2. change (shlen (rup8 8)) with 1 in MU2, SHK2. unfold shad, ASHOFF in MU2.
    destruct SV1 as (S5 & S6 & S7). unfold shz, shc, THFR, DVFR in *. unfold AVEC in *.
    change (shad 0x6afb08) with 2148327265 in *. change (shad 0x6afb10) with 2148327266 in *. change (shad 0x6afb00) with 2148327264 in *.
    assert (BSV : 2148345856 <= 2147450880 + Z.shiftr V 3 /\ 2147450880 + Z.shiftr V 3 + 1 <= 17594333495296
                  /\ 2147450880 + Z.shiftr V 3 + 1 <= Z.shiftr (SP + -16) 3 + 2147450880 /\ Z.shiftr (SP + -16) 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite !Z.shiftr_div_pow2 by lia; clear - VH1 VH3 VH4 LOS BOT H RSP TOP L3; Z.div_mod_to_equations; lia).
    clear BODY1. xall MU2 WM2. box MU1. box WM1. box MU2. box WM2.
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { eapply vd_b with (lo := lo) (V := V) (ra := ra);
        try first [exact ST2| exact MI2| exact FRA1| exact FRT1| exact VEC1| (split; [exact S5| split; [exact S6| exact S7]])| exact T1| exact VH| exact V16| exact RI| exact RISH| exact RSS
              | fold SP; lia| (eapply rng_sub'; [exact RSTK| fold SP; lia])].
      - pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & GOT1 & _). unfold bx in MU1, WM1, MU2, WM2.
        eapply rw_cells_transport; [exact GOT1| exact MU2| exact WM2| cbn; lia].
      - pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & _ & _ & _ & SHB1 & _). unfold bx in MU1, WM1, MU2, WM2.
        eapply rw_cells_transport; [exact SHB1| exact MU2| exact WM2| cbn; lia]. }
    cbv beta. fold SP. intros ms3 (m3 & z5 & z6 & z7 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & MU3 & WM3 & MI3 & ST3 & FRA3 & FRT3 & VEC3 & SV3' & T3).
    (* [comment removed for export] *)
    set (WS := [(lo, SP); (2147450880 + Z.shiftr V 3, 2147450880 + Z.shiftr V 3 + 1)]).
    assert (MUs : munch WS m1 m3).
    { unfold bx in MU2. eapply munch_trans; [eapply munch_weaken; [| exact MU2]; intros xx; unfold WS; cbn; lia|].
      eapply munch_weaken; [| exact MU3]. intros xx. unfold WS. cbn. lia. }
    assert (WMs : wmono bsegs m1 m3) by (unfold bx in WM2; eapply wmono_trans; [exact WM2| exact WM3]).
    assert (HWs : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) WS) by (unfold WS, AIMG_HI; apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia| apply Forall_nil]).
    assert (PC3 : poison_cells m3) by (eapply poison_cells_frame; [exact PC1| exact MUs| exact WMs| exact HWs]).
    assert (AC3 : annot_cells m3) by (eapply annot_cells_frame; [exact AC1| exact MUs| exact WMs| exact HWs]).
    assert (ART3 : artcells m3) by (eapply artcells_frame; [exact ARTC1| exact MUs| exact WMs| exact HWs]).
    assert (PRM3 : premap_cells m3) by (eapply premap_cells_frameA; [exact PRM1| exact MUs| exact WMs| exact HWs]).
    assert (REL3 : forall i, ARELRO_LO <= i < ARELRO_HI -> m3 (wa i) = None) by (eapply arelro_munchA; [exact REL1| exact MUs| exact HWs]).
    assert (RWR3 : wr_at bsegs m3 (shad RLO1) (shlen (RHI1 - RLO1))) by (eapply wr_at_transport; [exact RWR1| exact WMs]).
    destruct (poisoned_chunks m2 V 8 ltac:(lia) SHK2) as [BODY2 _].
    assert (BODY3 : rw_cells bsegs m3 (shad V) [CB (Z.to_nat (8 / 8)) (repeat (Z_to_bv 8 252) (Z.to_nat (8 / 8)))])
      by (eapply rw_cells_transport; [exact BODY2| exact MU3| exact WM3| cbn; unfold shad, ASHOFF; lia]).
    (* [comment removed for export] *)
    assert (PR8 : is_primary 8 = true) by reflexivity.
    lazymatch goal with |- implMA _ _ _ _ ?ms3 =>
      assert (G : implS bsegs RNG (aembed ATOP (aannotate (aps_m s) p 8 0 8))
                    (epostF (annot_grow_postA (Z_to_bv 64 0xb4bdc) (Z_to_bv 64 (SP + -64)) gp tp (Z_to_bv 64 (SP + -16)) (Z_to_bv 64 2147450880)
                               (Z_to_bv 64 (Z.shiftr (SP + -16) 3 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc V 8 lo m3 (aps_m s) RNG)) ms3)
    end.
    { eapply AGROW with (lo := lo) (p := p) (ch := ch) (sb := Z_to_bv 8 0);
        rewrite ?unsigned_lit by lia;
        first [exact MI3| exact ST3| exact PC3| exact AC3| exact ART3| exact PRM3| exact REL3| exact BR| exact CHL| exact CHS| exact CHU| exact CHK| exact RI| exact BODY3| reflexivity
              | (change (shlen (rup8 8)) with (shlen (8 + 7)); exact RSHP)
              | (intros NE; exfalso; apply NE; reflexivity)
              | (exists RLO1, RHI1; split; [exact RL41|]; split; [exact RH41|]; split; [exact RLA1|]; split; [exact RHA1|]; split; [exact RRNG1| exact RWR3])
              | (eapply rng_sub'; [exact RSTK| unfold ANNOT_STACK; lia]) | unfold ANNOT_STACK, AREQMAX; lia ]. }
    rewrite (aannotate_grow_prim _ _ _ _ CHL CHK PR8 ltac:(lia) ltac:(reflexivity)) in G.
    eapply implMA_evtF; [exact G|].
    cbv beta. intros ms4 PO. destruct PO as (_ & _ & w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & BODY4 & _).
    rewrite !unsigned_lit in MU4 by lia. rewrite !unsigned_lit in ST4 by lia. retlit.
    unfold ANNOT_STACK in MU4. change (shlen (rup8 8)) with 1 in MU4. unfold shad, ASHOFF in MU4.
    destruct SV3' as (S5' & S6' & S7'). unfold shz, shc, THFR, DVFR in *. unfold AVEC in *.
    change (shad 0x6afb08) with 2148327265 in *. change (shad 0x6afb10) with 2148327266 in *. change (shad 0x6afb00) with 2148327264 in *.
    clear S5 S6 S7 T1 FRA1 FRT1 VEC1 ST2 BODY2 SHK2. xall MU3 WM3.
    assert (MUs4 : munch WS m1 m4).
    { eapply munch_trans; [exact MUs|]. eapply munch_weaken; [| exact MU4]. intros xx. unfold WS. cbn. lia. }
    assert (WMs4 : wmono bsegs m1 m4) by (eapply wmono_trans; [exact WMs| exact WM4]).
    pose proof (artcells_frame _ _ _ ARTC1 MUs4 WMs4 HWs) as (_ & GOT4 & _ & _ & SHB4 & _).
    clear BODY3 ST3. xall MU4 WM4.
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { eapply vd_c with (lo := lo) (V := V) (ra := ra) (s0 := Z_to_bv 64 AFOE_S0) (s1 := s1) (s2 := s2);
        first [exact ST4| exact MI4| exact GOT4| exact SHB4| exact FRA3| exact FRD1| exact FRT3| exact VEC3| (split; [exact S5'| split; [exact S6'| exact S7']])| exact T3
              | exact VH| exact V16| exact RI| exact RISH| exact RSS| fold SP; lia| (eapply rng_sub'; [exact RSTK| fold SP; lia])]. }
    cbv beta. fold SP. intros ms5 (m5 & q5 & q6 & q7 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & -> & MU5 & WM5 & MI5 & ST5 & FRT5 & VEC5).
    (* [comment removed for export] *)
    assert (BODY5 : rw_cells bsegs m5 (shad V) [CB (Z.to_nat (8 / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (8 / 8)))])
      by (eapply rw_cells_transport; [exact BODY4| exact MU5| exact WM5| cbn; unfold shad, ASHOFF; lia]).
    assert (BSH5 : ablock_shadow m5 V 8).
    { eapply chunks_ablock_shadow; [lia| clear - V16; Z.div_mod_to_equations; lia| lia| lia| exact BODY5| intros NE; exfalso; apply NE; reflexivity]. }
    assert (MUf : munch [(lo, SP); (7011072, 7011072 + 24)] m m5).
    { unfold bx in MU1, MU2. eapply (annot_pair_munch _ m m5 V 8); [lia| clear - V16; Z.div_mod_to_equations; lia| lia| lia| exact BSH| exact BSH5|].
      intros x OUT NSH. cbn in OUT. change (shlen (rup8 8)) with 1 in NSH. unfold shad, ASHOFF in NSH.
      rewrite (MU5 x), (MU4 x), (MU3 x), (MU2 x), (MU1 x); cbn; try reflexivity; lia. }
    assert (WMf : wmono bsegs m m5).
    { unfold bx in WM1, WM2. eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3|]. eapply wmono_trans; [exact WM4| exact WM5]. }
    assert (AH5 : AHEAP AI L RNG (aps_m s) LB m5).
    { eapply (AI_frame AI); [exact AH| exact MUf| exact WMf|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      left; right; left. exists (0x6afb00, 0x6afb40). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]. }
    assert (IG5 : client_img m5) by (eapply client_img_munch_gen; [exact IG| exact MUf| exact WMf| cbn; lia| cbn; lia| unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn; lia| unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn; lia| unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn; lia| unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn; lia| unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT; cbn; lia | unfold AREAL_STRLEN; cbn; lia]).   (* [comment removed for export] *)
    assert (USH5 : client_sh m5).
    { eapply client_sh_munch_gen; [exact USH| exact MUf|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    (* [comment removed for export] *)
    eapply implMA_post_evtF.
    { eapply (proj1 OPDEL) with (lo := lo) (A := V) (n := 8);
        rewrite ?unsigned_lit by (unfold AFOE_S0; lia);
        first [exact AH5| exact HIN| exact MI5| exact ST5| exact BOT| exact TP| reflexivity| exact HUL| exact HUL1| exact RSTKTOP| exact ROK
              | (eapply rng_sub'; [exact RSTK| fold SP; lia])
              | (clear - SP16; fold SP in SP16; Z.div_mod_to_equations; lia)
              | unfold AFREE_STACK, AFOE_S0, AFREE_PC in *; lia ]. }
    cbv beta. intros [] s' RNG' ms' [SO PO].
    destruct PO as (LE & k0 & k1 & k2 & n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & k3 & k4 & k5 & k6 & m6 & -> & MI6 & ST6 & HPR6 & AH6).
    rewrite ?unsigned_lit in ST6, HPR6 by lia. retlit.
    assert (FRT6 : rw_cells bsegs m6 (SP + -16) [C8 (Z_to_bv 64 7011072); C8 ra]).
    { eapply aheap_pres_rw_cells; [exact HPR6| exact FRT5|]. left; left. cbn. lia. }
    assert (VEC6 : rw_cells bsegs m6 7011072 [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))]).
    { eapply aheap_pres_rw_cells; [exact HPR6| exact VEC5|]. left; right; left. exists (0x6afb00, 0x6afb40). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]. }
    eapply evtF_cut.
    { eapply vd_d with (lo := lo) (ra := ra); first [exact ST6| exact MI6| exact FRT6| exact RI| fold SP; lia| (eapply rng_fp_le; [exact LE|]; eapply rng_sub'; [exact RSTK| fold SP; lia])| exact 0]. }
    cbv beta. fold SP. intros ms7 (-> & ST7).
    apply evtF_done. unfold avdtor_post. split; [exact LE|]. do 15 eexists. exists m6. split; [reflexivity|]. split; [exact MI6|]. split; [exact ST7|].
    split.
    { intros a Ha [Hc NV]. destruct (HPR6 a Ha ltac:(eapply aclient_addr_mono_sp; [exact Hc| lia])) as [E6 W6].
      pose proof (cl_outside_stack AI _ _ _ _ _ SP lo a AH6 BOT Hc) as OUTa. unfold AVEC in NV.
      split.
      - rewrite E6. apply MUf. rewrite wa_unsigned by lia. cbn. lia.
      - intros Hw. apply W6. apply WMf. exact Hw. }
    split; [exact AH6|]. split; [exact SO|].
    split. { split; [eapply (client_img_pres AI IMG_CI); [exact IG5| exact HPR6| exact AH6| exact MI6]| eapply (client_sh_pres AI IMG_CI); [exact HPR6| exact USH5]]. }
    exact VEC6.
  Qed.
End VD.
End CANSEC1.
