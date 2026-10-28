From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_kitu El_defs El_acc_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_acc_3c9d4 El_acc_3ccd8.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).

Local Ltac sw A l :=
  astep; step; step; if_lia; astep; astep; astep; astep;
  lazymatch goal with H : mem_inv usegs ?mc |- _ =>
    pose proof (acc_jt_read mc A l H ltac:(lia) ltac:(lia) eq_refl ltac:(vm_compute; reflexivity)) as JT end;
  astep; astep; step;
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
    let v := eval vm_compute in (bv_unsigned pc) in
    replace pc with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.

Section Acc.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma acc_3d3ac_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node S sel : Z),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - 112 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    rw_cells usegs m S [C4 (Z_to_bv 64 sel)] -> 0 <= sel < 8 -> q <= S -> node mod 8 = 0 ->
    evt usegs (acc_post 112 ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 node) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3d3ac) fc None m (seg_rom usegs)).
  Proof.
    intros until sel. intros AI ROOT HEAP MI FRM ST LOQ QN NB QD SC SEL QS N8.
    destruct (acc_facts E OK s m HEAP) as ((T0 & TH & T8) & (S0 & SH) & (NR & SNR) & (CEIL & DB & B63 & D8) & TIR & EL).
    pose proof alloc_ceiling_range as CR. assert (LO0 : 0 <= ae_lo E) by lia.
    pose proof (length_map (Z_to_bv 64) (ae_tws E)) as LMT. pose proof (length_map (Z_to_bv 8) (ae_sbs E)) as LMS.
    pose proof (munch_refl [(q - 112, q)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof AI as AI0. pose proof ROOT as ROOT0. pose proof HEAP as HEAP0. hide AI0. hide ROOT0. hide HEAP0.
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. clear PTRB.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [40; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. name_mem m1.

    assert (TAIL : forall (i : Z) (xra xs0 xs1 xa2 xa3 xa4 : word), 0 <= i <= 2 ->
      evt usegs (acc_post 112 ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
        (MS (mkR xra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) xa2 xa3 xa4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d4e4) fc None m1 (seg_rom usegs))).
    { intros i xra xs0 xs1 xa2 xa3 xa4 HI. astep. astep. astep. step. release_frame FR ST q. step.
      eapply tix_tail; [exact DOCC| lia| lia| lia| lia| exact T8| lia| lia|]. intros. acc_fin. }

    assert (SELC : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia.
    destruct SELC as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
    - sw 0x14188 [36; 147; 2; 0].
      astep. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      astep. step. step. step. acc_tix E 0x3d4cc.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT.
      astep. step. astep. step. if_cases K; zify_cond K.
      + astep. astep. astep. step. release_frame FR ST q. step. acc_fin.
      + step. step. eapply TAIL; lia.
    - sw 0x1418c [112; 147; 2; 0].
      apply (rw_cells_split_CB usegs _ _ [] 40 _ _ [16; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      clear TAIL. remember (Z_to_bv 64 1) as w1 eqn:EW1. remember (Z_to_bv 64 (ae_DOC E)) as wd eqn:EWD.
      astep. step. astep. step. subst w1 wd. step. step.
      apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
      replace (q + -64 + Z.of_nat 16) with (q + -48) in FR by lia.
      apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRN FR]. cbn [cells_size csize Nat.add] in FR.
      replace (q + -48 + Z.of_nat 16) with (q + -32) in FR by lia.
      name_mem m2. unhide AI0. unhide ROOT0. unhide HEAP0.
      destruct (acc_reget E OK s m m2 node (q - 112) q AI0 ROOT0 HEAP0 MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & _ & HP1).
      try replace (q + -64 + 16) with (q + -48) by lia.
      eapply evt_cut.
      { eapply (acc_3ccd8_spec E OK); [exact AI1| exact FRN| exact HP1| exact MI| exact FRM| exact ST| lia| lia| lia| lia]. }
      clear AI1 HP1. intros ms' PO. unfold acc_3ccd8_post in PO.
      destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m3 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A0R & _).
      acc_tr FR0 MU2 WM2. acc_tr FRN MU2 WM2.
      acc_ret 0x3d510 FR MU WM MI FRM ST MU2 WM2 MI2 FC2 ST2.
      destruct (acc_word_small ya0 64 A0R) as (e1 & -> & E1). clear A0R.
      astep. rewrite ?sextw_small by lia. step. step. if_lia.
      astep. astep. astep. step. release_frame FR0 ST (q + -48). release_frame FRN ST (q + -32). release_frame FR ST q. step. acc_fin.
    - sw 0x14190 [152; 146; 2; 0].
      astep. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      astep. step. step. step. acc_tix E 0x3d440.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT.
      astep. step. astep. step. if_cases K; zify_cond K.
      + step. step. step. eapply TAIL; lia.
      + step. step. step. acc_tix E 0x3d45c.
        astep. step. astep. step. if_cases K2; zify_cond K2.
        * step. step. step. eapply TAIL; lia.
        * step. astep. astep. astep. step. release_frame FR ST q. step. acc_fin.
    - sw 0x14194 [232; 146; 2; 0].
      astep. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      astep. step. step. step. acc_tix E 0x3d490.
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT.
      astep. step. astep. step. if_cases K; zify_cond K.
      + step. step. step. acc_tix E 0x3d59c.
        astep. step. astep. step. if_cases K2; zify_cond K2.
        * step. step. step. eapply TAIL; lia.
        * step. astep. astep. astep. step. release_frame FR ST q. step. acc_fin.
      + step. step. step. eapply TAIL; lia.
    - sw 0x14198 [116; 146; 2; 0].
      apply (rw_cells_split_CB usegs _ _ [] 40 _ _ [8; 8; 24]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      clear TAIL. remember (Z_to_bv 64 1) as w1 eqn:EW1. remember (Z_to_bv 64 (ae_DOC E)) as wd eqn:EWD.
      astep. step. astep. step. subst w1 wd. step. step. step.
      apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRN FR]. cbn [cells_size csize Nat.add] in FR.
      replace (q + -64 + Z.of_nat 16) with (q + -48) in FR by lia.
      apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FRR FR]. cbn [cells_size csize Nat.add] in FR.
      replace (q + -48 + Z.of_nat 24) with (q + -24) in FR by lia.
      name_mem m2. unhide AI0. unhide ROOT0. unhide HEAP0.
      destruct (acc_reget E OK s m m2 node (q - 112) q AI0 ROOT0 HEAP0 MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & _ & HP1).
      try replace (q + -64 + 16) with (q + -48) by lia.
      eapply evt_cut.
      { eapply (acc_3c9d4_spec E OK); [exact AI1| exact FRN| exact HP1| exact MI| exact FRM| exact ST| lia| lia| lia| lia| exact FRR| lia]. }
      clear AI1 HP1. intros ms' PO. unfold acc_3c9d4_post in PO.
      destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m3 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & (j1 & j2 & err & SLOT & ERR & _)).
      acc_tr FRN MU2 WM2. clear FRR.
      acc_ret 0x3d418 FR MU WM MI FRM ST MU2 WM2 MI2 FC2 ST2.
      astep. step. step. step. if_lia.
      astep. astep. astep. step. release_frame FRN ST (q + -48). release_frame SLOT ST (q + -24). release_frame FR ST q. step. acc_fin.
    - sw 0x1419c [168; 147; 2; 0].
      astep. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      astep. step. step. step. acc_tix E 0x3d550.
      pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDB.
      astep. step. step. if_cases K; zify_cond K.
      + astep. astep. astep. step. release_frame FR ST q. step. acc_fin.
      + rewrite ?a_u8_small in K by lia. destruct (acc_root_str E OK K) as (O0 & OS & KM).
        step. step. step. acc_tix E 0x3d568.
        pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT.
        astep. step. if_lia.
        astep. astep. astep. rewrite KM. astep. astep.
        step. if_lia. step. if_lia.
        astep. astep. astep. step. release_frame FR ST q. step. acc_fin.
    - sw 0x141a0 [92; 146; 2; 0].
      astep. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      astep. step. eapply TAIL; lia.
    - sw 0x141a4 [92; 146; 2; 0].
      astep. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      astep. step. eapply TAIL; lia.
  Qed.
End Acc.
End WithCeiling0.
