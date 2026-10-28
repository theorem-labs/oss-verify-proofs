(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA Atp_arratA El_sitesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
#[warnings="-notation-for-abbreviation"] Notation wz z := (Z_to_bv 64 z) (only parsing).

Section H24.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma h24_walkB : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q node : Z),
    stk asegs m (ae_lo E) q -> ae_lo E + 64 <= q -> SEGTOP_A <= ae_lo E -> q <= ae_hi E -> ae_hi E < 2^47 -> q mod 16 = 0 ->
    (forall m', munch [(q + -64, q)] m m' -> wmono asegs m m' -> shb_cells m') ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> node + 16 <= q - 64 -> node mod 8 = 0 ->
    (forall m', munch [(q + -64, q)] m m' -> wmono asegs m m' -> shz m' node 16) -> AINV_A E m ->
    (forall m', munch [(q + -64, q)] m m' -> AINV_A E m') ->
    (forall m', munch [(q + -64, q)] m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch [(q + -64, q)] m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    mem_inv asegs m -> 0 <= bv_unsigned ra < 2^64 -> bv_unsigned ra mod 2 = 0 ->
    evt asegs (fun ms => exists (m0 : mem), munch [(q + -64, q)] m m0 /\ wmono asegs m m0 /\ mem_inv asegs m0 /\
        ( (exists a1' a2' a3' a4' a5' t0' t1' t2' t3' t4' t5' t6', stk asegs m0 (ae_lo E) q /\ ttype (ae_T E 1) = 91 /\
             ms = MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (ae_DOC E)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m0 (seg_rom asegs))
       \/ (exists (j : list byte) a1' a2' a3' a4' a5' t0' t1' t2' t3' t4' t5' t6', length j = 8%nat /\ stk asegs m0 (ae_lo E) (q + -32) /\ ttype (ae_T E 1) <> 91 /\
             rw_cells asegs m0 (q + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] /\
             ms = MS (mkR ra (wz (q + -32)) gp (wz TPV_A) t0' t1' t2' s0 (wz SHB) (wz node) a1' a2' a3' a4' a5' a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz 0xb3170) fc None m0 (seg_rom asegs)) ))
      (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb304c) fc None m (seg_rom asegs)).
  Proof.
    intros until node. intros ST LO GLO QH HI47 Q16 SHBM NODE N0 NQ N8 SZN AI AIM SZD SZT MI RA0 RA2.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP, SHB in *.
    pose proof (ael_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q + -64, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

    zstep. carve_frame 32%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    hide AI. do 3 lstep. unhide AI.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step.
    name_mem m1.
    assert (AI1 : AINV_A E m1) by exact (AIM m1 MU).
    pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.

    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. step. step.
    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep.
    destruct (Z.eq_dec (ttype (ae_T E 1)) 91) as [TY|TY].
    -
      rewrite TY. step. if_false.
      shz_pose SZN node. step. shz_norm. step. if_false.
      step. chk0 SZD (ae_DOC E). step. if_false.
      step. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
      step. step. rewrite (unsigned_lit (ae_T E 1) TIR), Z.shiftr_div_pow2 by lia. change (ae_T E 1 / 2 ^ 56) with (ttype (ae_T E 1)).
      rewrite TY. astep. step. step. if_false. astep. astep. astep. astep. step. if_true.
      astep. astep. astep. astep. astep. step. if_false.
      step. step. step. step.
      step. step. step. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (STq : stk asegs mx (ae_lo E) q)
          by (pose proof (stk_release asegs mx (ae_lo E) _ _ ST FR ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (q + -32 + Z.of_nat 32) with q in X by lia; exact X) end.
      step.
      apply evt_done. exists m1. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. left. do 12 eexists.
      split; [exact STq|]. split; [reflexivity|]. replace (q + -32 + 32) with q by lia. atp_st_eq_goal.
    -
      step; if_cases KB; zify_cond KB; [| exfalso; rewrite ?land64_mod, ?Z.mod_small in KB by lia; lia].
      pose proof FR as [[WFj _] _]. cbn [cells_wf cell_wf] in WFj.
      apply evt_done. exists m1. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. right.
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jj :: _) => exists jj end. do 12 eexists.
      split; [tauto|]. split; [exact ST|]. split; [exact TY|]. split; [exact FR|]. atp_st_eq_goal.
  Qed.
End H24.

Section Arm24.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH in *; lia.

Theorem arm24_okA : forall W, throw_siteB RT PMc W 24 EL_SITE_END_B -> arm_cpsA RT PMc W 24.
Proof using AF RC.
  intros W SITE Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED64 : lf_lo X + 16 <= lf_S1 X - 64) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 24 sel idx jr jos t m 64 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED64) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 24 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  change (el_arm_pcA 24) with 0xb1c70. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO64 : f + 1024 <= sp' - 64) by (clear - FLO NEED64; lia).
  apply (aevt_evt RT AF PMc MST).

  zstep. zstep.
  eapply evt_cut.
  { eapply (h24_walkB E OKE (wz 0xb1c78) gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7
              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120)) t3 t4 t5 t6 F fc m sp' (f + 208));
      [rewrite ELO; exact STg| rewrite ELO; clear - NEED64; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| exact SHBM| exact CE| clear - FPOS; lia| exact FLO64 || (clear - FLO64; lia)| clear - F64; Z.div_mod_to_equations; lia
      | exact SZN| exact AI| exact AIM| exact SZD| exact SZT| exact MIg| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity]. }
  cbv beta. intros ms1 (m0 & MU0 & WM0 & MI0 & [(a1' & a2' & a3' & a4' & a5' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & ST0 & TY & ->)
                                              |(j & a1' & a2' & a3' & a4' & a5' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & LJ & ST0 & TY & FR0 & ->)]).
  -
    rewrite (ret_pc_even 0xb1c78) by lia. zstep. apply evt_done.
    rewrite ELO in ST0.
    apply (POST false (rt_credit RT Σ) Σ m0 fc F).
    exact (arm_post_below_le RT AF W 24 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m0 fc 64 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED64
             MU0 WM0 MI0 ST0 FRM ltac:(unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; pose proof (mcost_nonneg EXC_SIZE ltac:(unfold EXC_SIZE; lia)); lia)).
  -
    destruct (CTX m0 64 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED64 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    rewrite ELO in ST0.
    apply evt_done. replace (sp' + -32) with (sp' - 32) by lia.
    eapply (SITE Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E sel idx jr jos t j 0
              (wz 0xb1c78) gp t0' t1' t2' (wz usp) (wz SHB) (wz (f + 208)) a1' a2' a3' a4' a5' a6 a7 (wz f) (wz (shad f)) (wz (f + 32))
              (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120)) t3' t4' t5' t6' F fc m0);
      cbn [lf_usp lf_S1 lf_F lf_lo site_fszB site_frameB site_jlenB site_cvB site_regsB el_site_pcsB EL_SITE_END_B Z.eqb Pos.eqb orb andb app];
      [left; reflexivity| exact FDO| exact MST| exact LK| exact OKE| exact LE| exact SEL| exact IDX| exact AL| exact FRS| exact LPA
      | clear - LVB; unfold arm_xliveA in LVB; cbn [Z.eqb Pos.eqb orb] in LVB; lia
      | clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; lia
      | exact ART0| exact MI0| replace (sp' - 32) with (sp' + -32) by lia; exact ST0
      | clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; lia
      | exact AM0| exact FRM| exact XD0| exact AUX0| exact SPB| exact LJ| exact I
      | replace (sp' - 32) with (sp' + -32) by lia; exact FR0| repeat split|].
    intros c Σ' m' fc' F' ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6' a7' s6' s7' s8' s9' s10' s11' t3'' t4'' t5'' t6'' LP.
    unfold lf_st, EL_LRET_A. cbn [lf_usp lf_S1 lf_F lf_lo].
    destruct LP as (AX & MI' & ST' & FRM' & LV' & FRS' & SP' & CR' & PRES' & MEM' & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ST', PRES', MEM'.
    apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
    apply (POST true c Σ' m' fc' F'). unfold arm_postA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [exact AX|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|]. split; [exact LV'|]. split; [exact FRS'|]. split; [exact SP'|].
    split; [exact CR'|].
    split; [intros a Ha Ho; rewrite (PRES' a Ha Ho); apply MU0; cbn [outside]; split; [exact (NBELOW _ Ha)| exact I]|].
    split; [exact MEM'| intros _; right; lia].
Qed.
End Arm24.
