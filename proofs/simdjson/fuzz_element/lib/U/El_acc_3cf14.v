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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_acc_3cb20 El_acc_3cbfc El_acc_3ccd8.
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

Section Acc.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma acc_3cf14_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node : Z),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - 48 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    evt usegs (acc_post 48 ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 node) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3cf14) fc None m (seg_rom usegs)).
  Proof.
    intros until node. intros AI ROOT HEAP MI FRM ST LOQ QN NB QD.
    destruct (acc_facts E OK s m HEAP) as (_ & _ & _ & (CEIL & DB & B63 & D8) & _ & _).
    pose proof alloc_ceiling_range as CR. assert (LO0 : 0 <= ae_lo E) by lia.
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide AI. hide ROOT. hide HEAP.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step.

    name_mem m1. unhide AI. unhide ROOT. unhide HEAP.
    destruct (acc_reget E OK s m m1 node (q - 48) q AI ROOT HEAP MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & RT1 & HP1).
    hide AI. hide ROOT. hide HEAP.
    eapply evt_cut.
    { eapply (acc_3cb20_spec E OK); [exact AI1| exact RT1| exact HP1| exact MI| exact FRM| exact ST| lia| lia| lia| lia]. }
    clear AI1 RT1 HP1. intros ms' PO. unfold acc_3cb20_post in PO.
    destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A1R & _).
    acc_ret 0x3cf2c FR MU WM MI FRM ST MU2 WM2 MI2 FC2 ST2.
    destruct (acc_word_small ya1 64 A1R) as (e1 & -> & E1). clear A1R.
    astep. rewrite ?sextw_small by lia. step. step. if_lia.
    step. step. if_cases K1; zify_cond K1.
    { step. astep. astep. astep. step. release_frame FR ST q. step. acc_fin. }
    step. step.

    name_mem m3. unhide AI. unhide ROOT. unhide HEAP.
    destruct (acc_reget E OK s m m3 node (q - 48) q AI ROOT HEAP MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & RT1 & HP1).
    hide AI. hide ROOT. hide HEAP.
    eapply evt_cut.
    { eapply (acc_3cbfc_spec E OK); [exact AI1| exact RT1| exact HP1| exact MI| exact FRM| exact ST| lia| lia| lia| lia]. }
    clear AI1 RT1 HP1. intros ms' PO. unfold acc_3cbfc_post in PO.
    destruct PO as (y0' & y1' & y2' & yb0 & yb1 & yb2 & yb3 & yb4 & yb5 & yb6 & yb7 & y3' & y4' & y5' & y6' & F4 & fc4 & m4 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A1R & _).
    acc_ret 0x3cf48 FR MU WM MI FRM ST MU2 WM2 MI2 FC2 ST2.
    destruct (acc_word_small yb1 64 A1R) as (e2 & -> & E2). clear A1R.
    astep. rewrite ?sextw_small by lia. step. step. if_lia.
    step. if_cases K2; zify_cond K2.
    { step. astep. astep. astep. step. release_frame FR ST q. step. acc_fin. }
    step. step.

    name_mem m5. unhide AI. unhide ROOT. unhide HEAP.
    destruct (acc_reget E OK s m m5 node (q - 48) q AI ROOT HEAP MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & RT1 & HP1).
    hide AI. hide ROOT. hide HEAP.
    eapply evt_cut.
    { eapply (acc_3ccd8_spec E OK); [exact AI1| exact RT1| exact HP1| exact MI| exact FRM| exact ST| lia| lia| lia| lia]. }
    clear AI1 RT1 HP1. intros ms' PO. unfold acc_3ccd8_post in PO.
    destruct PO as (y0'' & y1'' & y2'' & yc0 & yc1 & yc2 & yc3 & yc4 & yc5 & yc6 & yc7 & y3'' & y4'' & y5'' & y6'' & F6 & fc6 & m6 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A0R & _).
    acc_ret 0x3cf60 FR MU WM MI FRM ST MU2 WM2 MI2 FC2 ST2.
    destruct (acc_word_small yc0 64 A0R) as (e3 & -> & E3). clear A0R.
    astep. rewrite ?sextw_small by lia. step. step. if_lia.
    astep.
    step. astep. astep. astep. step. release_frame FR ST q. step. acc_fin.
  Qed.
End Acc.
End WithCeiling0.
