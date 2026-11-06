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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA El_sitesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
#[warnings="-notation-for-abbreviation"] Notation wz z := (Z_to_bv 64 z) (only parsing).

Section H23.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma h23_walkB : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q node : Z),
    stk bsegs m (ae_lo E) q -> ae_lo E + 64 <= q -> SEGTOP_A <= ae_lo E -> q <= ae_hi E -> ae_hi E < 2^47 -> q mod 16 = 0 ->
    (forall m', munch [(q + -64, q)] m m' -> wmono bsegs m m' -> shb_cells m') ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> node + 16 <= q - 64 -> node mod 8 = 0 ->
    (forall m', munch [(q + -64, q)] m m' -> wmono bsegs m m' -> shz m' node 16) -> AINV_A E m ->
    (forall m', munch [(q + -64, q)] m m' -> AINV_A E m') ->
    (forall m', munch [(q + -64, q)] m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch [(q + -64, q)] m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    mem_inv bsegs m -> 0 <= bv_unsigned ra < 2^64 -> bv_unsigned ra mod 2 = 0 ->
    evt bsegs (fun ms => exists (m0 : mem), munch [(q + -64, q)] m m0 /\ wmono bsegs m m0 /\ mem_inv bsegs m0 /\
        ( (exists a1' a2' a3' a4' a5' t0' t1' t2' t3' t4' t5' t6', stk bsegs m0 (ae_lo E) q /\ ttype (ae_T E 1) = 91 /\
             ms = MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (ae_DOC E)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m0 (seg_rom bsegs))
       \/ (exists a0' a1' a2' a3' a4' a5' t0' t1' t2' t3' t4' t5' t6', stk bsegs m0 (ae_lo E) (q + -48) /\ ttype (ae_T E 1) <> 91 /\
             rw_cells bsegs m0 (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
             ms = MS (mkR (wz 0xb53c8) (wz (q + -48)) gp (wz TPV_A) t0' t1' t2' (wz node) (wz (node + 8)) a0' a1' a2' a3' a4' a5' a6 a7
                          (wz SHB) (wz (shad node)) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz 0xb5420) fc None m0 (seg_rom bsegs)) ))
      (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H23_A) fc None m (seg_rom bsegs)).
  Proof.
    intros until node. intros ST LO GLO QH HI47 Q16 SHBM NODE N0 NQ N8 SZN AI AIM SZD SZT MI RA0 RA2.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP, EL_H23_A, SHB in *.
    pose proof (ael_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q + -64, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

    zstep. carve_frame 48%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    hide AI. do 6 lstep. unhide AI.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step. step.
    name_mem m1.
    assert (AI1 : AINV_A E m1) by exact (AIM m1 MU).
    pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.

    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.

    astep. chk0 SZN (node + 8). step. if_false.
    step. zstep.

    assert (SUB : sub_fp [(q + -48 + -16, q + -48)] [(q + -64, q)]) by (intros x Hx; cbn [outside] in *; lia).
    eapply (tix_cps E OK _ m1 F fc (q + -48) 1 0xb53c8);
      [exact (AIM m1 MU)| lia| exact (SHBM m1 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | exact ST| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2.
    assert (MU' : munch [(q + -64, q)] m m2) by exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU2)).
    assert (WM' : wmono bsegs m m2) by exact (wmono_trans _ _ _ _ WM WM2).
    assert (FR2 : rw_cells bsegs m2 (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_agree bsegs m1 m2); [exact FR| | exact WM2]. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. lia. }
    assert (NODE2 : rw_cells bsegs m2 node [C8 (wz (ae_DOC E)); C8 (wz 1)]).
    { eapply (rw_cells_agree bsegs m1 m2); [exact NODE| | exact WM2]. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. lia. }
    clear MU WM MU2 WM2 FR NODE. rename MU' into MU. rename WM' into WM. rename FR2 into FR. rename NODE2 into NODE.
    assert (AI2 : AINV_A E m2) by exact (AIM m2 MU).
    pose proof AI2 as (TAPEB & _ & _ & _ & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT2. rewrite Z.mul_1_r in RDT2.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY2. rewrite Z.mul_1_r in RDTY2.
    clear TAPEB AI2 RDT RDTY.
    replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep.
    destruct (Z.eq_dec (ttype (ae_T E 1)) 91) as [TY|TY].
    -
      rewrite TY. step. if_false.

      shz_pose SZN (node + 8). step. shz_norm. step. if_false.
      shz_pose SZN node. step. shz_norm. step. if_false.

      step. step. astep.
      step. step. step. step. step. step. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (STq : stk bsegs mx (ae_lo E) q)
          by (pose proof (stk_release bsegs mx (ae_lo E) _ _ ST2 FR ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (q + -48 + Z.of_nat 48) with q in X by lia; exact X) end.
      step.
      apply evt_done. exists m2. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. left. do 12 eexists.
      split; [exact STq|]. split; [reflexivity|]. replace (q + -48 + 48) with q by lia. atp_st_eq_goal.
    -
      step; if_cases KB; zify_cond KB; [| exfalso; rewrite ?land64_mod, ?Z.mod_small in KB by lia; lia].
      apply evt_done. exists m2. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. right. do 13 eexists.
      split; [exact ST2|]. split; [exact TY|]. split; [exact FR|]. unfold shad. atp_st_eq_goal.
  Qed.
End H23.

Section Arm23.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH in *; lia.

Theorem arm23_okA : forall W, throw_siteB RT PMc W 23 0xb5420 -> arm_cpsA RT PMc W 23.
Proof using AF.
  intros W SITE Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED64 : lf_lo X + 16 <= lf_S1 X - 64) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 23 sel idx jr jos t m 64 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED64) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 23 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  change (el_arm_pcA 23) with 0xb23c4. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO64 : f + 1024 <= sp' - 64) by (clear - FLO NEED64; lia).
  apply (aevt_evt RT AF PMc MST).

  zstep. zstep.
  eapply evt_cut.
  { eapply (h23_walkB E OKE (wz 0xb23cc) gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7
              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3 t4 t5 t6 F fc m sp' (f + 208));
      [rewrite ELO; exact STg| rewrite ELO; clear - NEED64; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| exact SHBM| exact CE| clear - FPOS; lia| exact FLO64 || (clear - FLO64; lia)| clear - F64; Z.div_mod_to_equations; lia
      | exact SZN| exact AI| exact AIM| exact SZD| exact SZT| exact MIg| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity]. }
  cbv beta. intros ms1 (m0 & MU0 & WM0 & MI0 & [(a1' & a2' & a3' & a4' & a5' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & ST0 & TY & ->)
                                              |(a0' & a1' & a2' & a3' & a4' & a5' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & ST0 & TY & FR0 & ->)]).
  -
    rewrite (ret_pc_even 0xb23cc) by lia. zstep. apply evt_done.
    rewrite ELO in ST0.
    apply (POST false (rt_credit RT Σ) Σ m0 fc F).
    exact (arm_post_below_le RT AF W 23 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m0 fc 64 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED64
             MU0 WM0 MI0 ST0 FRM ltac:(unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; pose proof (mcost_nonneg EXC_SIZE ltac:(unfold EXC_SIZE; lia)); lia)).
  -
    destruct (CTX m0 64 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED64 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    rewrite ELO in ST0.
    apply evt_done. replace (f + 208 + 8) with (f + 216) by lia. replace (sp' + -48) with (sp' - 48) by lia.
    eapply (SITE Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E sel idx jr jos t [] 0
              (wz 0xb53c8) gp t0' t1' t2' (wz (f + 208)) (wz (f + 216)) a0' a1' a2' a3' a4' a5' a6 a7 (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216)))
              s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3' t4' t5' t6' F fc m0);
      cbn [lf_usp lf_S1 lf_F lf_lo site_fszB site_frameB site_jlenB site_cvB site_regsB lftoi_savedB el_site_pcsB EL_SITE_END_B EL_SITE_CSTR_B EL_SITE_SV_B Z.eqb Pos.eqb orb andb app];
      [left; reflexivity| exact FDO| exact MST| exact LK| exact OKE| exact LE| exact SEL| exact IDX| exact AL| exact FRS| exact LPA
      | clear - LVB; unfold arm_xliveA in LVB; cbn [Z.eqb Pos.eqb orb] in LVB; lia
      | clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; lia
      | exact ART0| exact MI0| replace (sp' - 48) with (sp' + -48) by lia; exact ST0
      | clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; lia
      | exact AM0| exact FRM| exact XD0| exact AUX0| exact SPB| reflexivity| exact I
      | replace (sp' - 48) with (sp' + -48) by lia; exact FR0| reflexivity|].
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
End Arm23.
