From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjLeaves SjStage1 SjStage1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_tables Sj_stage2_iface Atp_pid Atp_defs Atp_kitu Atp_h_defs El_defs El_hdr El_h2 El_h3 El_act.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_acc_kit El_acc_3c74c El_acc_3c7d4 El_acc_3c85c El_acc_3c900 El_acc_3ce04 El_acc_3ce94 El_acc_3ced4.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_acc_3cf14 El_acc_3cf8c El_acc_3d00c El_acc_3d054 El_acc_3d200 El_acc_3d3ac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_acc_3c9d4 El_acc_3cb20 El_acc_3cbfc El_acc_3ccd8.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
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

Lemma land_low6 : forall e c, 0 <= e < 64 -> c mod 64 = 0 -> Z.land e c = 0.
Proof.
  intros e c He Hc.
  replace e with (Z.land e (Z.ones 6)) by (rewrite Z.land_ones by lia; apply Z.mod_small; change (2^6) with 64; lia).
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 6) c), Z.land_ones by lia. change (2^6) with 64. rewrite Hc. apply Z.land_0_r.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma act_env_acc {E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc} :
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  aenv_ok E /\ AINV E m /\ el_root E m (sp0 + 296) /\ RHEAP st (ae_LB E) m /\ mem_inv usegs m /\ frm0 fc /\
  stk usegs m (ae_lo E) sp0 /\ ae_lo E <= sp0 - 112 /\ sp0 + 312 <= ae_B E /\ ae_DOC E = sp0 + 336 /\ (sp0 + 296) mod 8 = 0 /\
  rw_cells usegs m (sp0 + 8) [CB 24 jres] /\ sp0 + 32 <= ae_B E /\
  rw_cells usegs m (sp0 + 420) [C4 (Z_to_bv 64 (el_sel d))] /\ 0 <= el_sel d < 8 /\ alloc_ceiling <= ae_lo E.
Proof.
  intros AE.
  destruct AE as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                  & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof alloc_ceiling_range as CR.
  pose proof PL as (_ & PRNG & _).
  apply (proj1 (rw_cells_app _ _ _ [_] _)) in XSEL. destruct XSEL as [_ XSEL]. cbn [cells_size csize Nat.add] in XSEL.
  replace (sp0 + 416 + Z.of_nat 4) with (sp0 + 420) in XSEL by lia.
  rewrite <- ELO in ST, CEIL, LO. rewrite <- EB in QB.
  split; [exact OK|]. split; [exact AI|]. split; [exact ROOT|]. split; [exact HEAP|]. split; [exact MI|]. split; [exact FRM|].
  split; [exact ST|]. split; [lia|]. split; [lia|]. split; [exact EDOC|]. split; [lia|].
  split; [exact RES|]. split; [lia|]. split; [exact XSEL|]. split; [apply el_sel_range; exact PRNG| lia].
Qed.

Lemma act_env_slot {E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc}
    {W : list (Z * Z)} {m' : mem} {fc' : bv 32} {jres' : list byte} :
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  munch W m m' -> sub_fp W [(sp0 - 112, sp0); (sp0 + 8, sp0 + 32)] -> wmono usegs m m' -> mem_inv usegs m' ->
  stk usegs m' (ae_lo E) sp0 -> rw_cells usegs m' (sp0 + 8) [CB 24 jres'] -> frm0 fc' ->
  act_env E m0 m' s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres' jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc'.
Proof.
  intros AE MU SUB WM MI' ST' RES' FRM'.
  pose proof (munch_weaken _ _ _ _ SUB MU) as MU0.
  pose proof AE as AE0.
  destruct AE0 as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                  & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof alloc_ceiling_range as CR.
  assert (MU1 : munch [(lo, sp0); (sp0 + 8, sp0 + 296)] m m').
  { eapply munch_weaken; [| exact MU0]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
  assert (HEAP' : RHEAP st (ae_LB E) m').
  { eapply LH_frame; [exact HEAP| exact MU0| exact WM|]. constructor; [apply W_ok_stack; lia|]. constructor; [apply W_ok_stack; lia| constructor]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ ERR MU0 WM ltac:(unfold LX_ERRNO, RATP in *; cbn; lia)) as ERR'.
  pose proof (rw_cells_transport _ _ _ _ _ _ OS MU0 WM ltac:(cbn; lia)) as OS'.
  rewrite ELO in ST'.
  eapply proj1. eapply act_env_call;
    [exact AE| exact MU1| exact WM| exact MI'| exact ST'| exact HEAP'| reflexivity| reflexivity| exact ERR'| exact RES'| exact OS'| exact FRM'].
Qed.

Local Ltac fix_ret :=
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Local Ltac arm_open N :=
  unfold arm_stmt; intros until p50; intros EA AE HK;
  rewrite (el_act_dead N _ EA ltac:(lia) eq_refl); apply implM_ret_bind;
  let t := eval vm_compute in (el_target N) in change (el_target N) with t;
  pose proof (act_env_acc AE) as (OK & AI & ROOT & HEAP & MI & FRM & ST & LOQ & NB & EDOC & N8 & RES & RB & SC & SEL & CEIL);
  pose proof alloc_ceiling_range as CR;
  unfold implM; iprefix.

Local Ltac arm_exit HK AE2 := ihere; to_implM; apply HK; eapply act_post_here; [exact AE2| reflexivity| reflexivity].

Local Ltac fin_slot AE HK MU2 WM2 MI2 ST2 SLOT FC2 :=
  let AE2 := fresh "AE2" in
  pose proof (act_env_slot AE MU2 ltac:(unfold sub_fp; cbn [outside]; intros ? ?; lia) WM2 MI2 ST2 SLOT FC2) as AE2;
  arm_exit HK AE2.

Local Ltac fin_node AE HK RES MU2 WM2 MI2 ST2 FC2 :=
  let SL := fresh "SL" in
  pose proof (rw_cells_transport _ _ _ _ _ _ RES MU2 WM2 ltac:(cbn; lia)) as SL;
  fin_slot AE HK MU2 WM2 MI2 ST2 SL FC2.

Local Ltac gen_arm N SPEC PRE UNF :=
  unfold arm_stmt; intros until p50; intros EA AE HK;
  rewrite (el_act_dead N _ EA ltac:(lia) eq_refl); apply implM_ret_bind;
  let t := eval vm_compute in (el_target N) in change (el_target N) with t;
  pose proof (act_env_acc AE) as (OK & AI & ROOT & HEAP & MI & FRM & ST & LOQ & NB & EDOC & N8 & RES & RB & SC & SEL & CEIL);
  pose proof alloc_ceiling_range as CR;
  unfold implM; iprefix; PRE;
  eapply evt_cut; [eapply SPEC; first [eassumption| lia]|];
  let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO;
  lazymatch UNF with
  | true =>
      unfold acc_post_r in PO;
      destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & (jr' & SLOT));
      fix_ret; step; fin_slot AE HK MU2 WM2 MI2 ST2 SLOT FC2
  | false =>
      unfold acc_post in PO;
      destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2);
      fix_ret; step; fin_node AE HK RES MU2 WM2 MI2 ST2 FC2
  end.

Local Ltac node_arm N SPEC := gen_arm N SPEC ltac:(step; step) false.
Local Ltac sel_arm N SPEC := gen_arm N SPEC ltac:(step; step; step) false.
Local Ltac slot_arm N SPEC := gen_arm N SPEC ltac:(step; step; step) true.

Section Arms.

  Lemma arm_d0 : arm_stmt 0 (el_target 0).
  Proof.
    arm_open 0.
    destruct (acc_facts E OK st m HEAP) as ((T0 & TH & T8) & _ & _ & (CEIL' & DB & B63 & D8) & _ & _).
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT.
    astep. step. if_lia.
    zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
    astep. step. acc_tix E 0x3c2f8.
    step. arm_exit HK AE.
  Qed.

  Lemma arm_d1 : arm_stmt 1 (el_target 1).
  Proof. slot_arm 1 acc_3c74c_spec. Qed.

  Lemma arm_d2 : arm_stmt 2 (el_target 2).
  Proof. slot_arm 2 acc_3c7d4_spec. Qed.

  Lemma arm_d3 : arm_stmt 3 (el_target 3).
  Proof. node_arm 3 acc_3c85c_spec. Qed.

  Lemma arm_d4 : arm_stmt 4 (el_target 4).
  Proof. node_arm 4 acc_3c900_spec. Qed.

  Lemma arm_d5 : arm_stmt 5 (el_target 5).
  Proof.
    arm_open 5. step. step. step.
    eapply evt_cut; [eapply (acc_3c9d4_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia| exact RES| lia]|].
    intros ms' PO. unfold acc_3c9d4_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & (j1 & j2 & err & SLOT & ERR & _)).
    fix_ret. step.
    destruct (rw_cells_forget _ _ _ _ SLOT) as [jr' SLOT']. cbn [cells_size csize Nat.add] in SLOT'.
    fin_slot AE HK MU2 WM2 MI2 ST2 SLOT' FC2.
  Qed.

  Lemma arm_d6 : arm_stmt 6 (el_target 6).
  Proof.
    arm_open 6. step. step.
    eapply evt_cut; [eapply (acc_3cb20_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia]|].
    intros ms' PO. unfold acc_3cb20_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & _).
    fix_ret. step. fin_node AE HK RES MU2 WM2 MI2 ST2 FC2.
  Qed.

  Lemma arm_d7 : arm_stmt 7 (el_target 7).
  Proof.
    arm_open 7. step. step.
    eapply evt_cut; [eapply (acc_3cbfc_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia]|].
    intros ms' PO. unfold acc_3cbfc_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & _).
    fix_ret. step. fin_node AE HK RES MU2 WM2 MI2 ST2 FC2.
  Qed.

  Lemma arm_d9 : arm_stmt 9 (el_target 9).
  Proof. node_arm 9 acc_3ce04_spec. Qed.

  Lemma arm_d10 : arm_stmt 10 (el_target 10).
  Proof. node_arm 10 acc_3ce94_spec. Qed.

  Lemma arm_d11 : arm_stmt 11 (el_target 11).
  Proof. node_arm 11 acc_3ced4_spec. Qed.

  Lemma arm_d12 : arm_stmt 12 (el_target 12).
  Proof.
    arm_open 12. step. step. step.
    eapply evt_cut; [eapply (acc_3c9d4_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia| exact RES| lia]|].
    intros ms' PO. unfold acc_3c9d4_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & (j1 & j2 & err & SLOT & ERR & _)).
    fix_ret. astep. step. step. step. if_lia.
    destruct (rw_cells_forget _ _ _ _ SLOT) as [jr' SLOT']. cbn [cells_size csize Nat.add] in SLOT'.
    fin_slot AE HK MU2 WM2 MI2 ST2 SLOT' FC2.
  Qed.

  Lemma arm_d13 : arm_stmt 13 (el_target 13).
  Proof.
    arm_open 13. step. step.
    eapply evt_cut; [eapply (acc_3cb20_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia]|].
    intros ms' PO. unfold acc_3cb20_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A1R & _).
    fix_ret. destruct (acc_word_small za1 64 A1R) as (e1 & -> & E1). clear A1R.
    step. astep. rewrite (land_low6 e1) by first [lia| reflexivity]. step. if_lia.
    fin_node AE HK RES MU2 WM2 MI2 ST2 FC2.
  Qed.

  Lemma arm_d14 : arm_stmt 14 (el_target 14).
  Proof.
    arm_open 14. step. step.
    eapply evt_cut; [eapply (acc_3cbfc_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia]|].
    intros ms' PO. unfold acc_3cbfc_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A1R & _).
    fix_ret. destruct (acc_word_small za1 64 A1R) as (e1 & -> & E1). clear A1R.
    astep. rewrite (land_low6 e1) by first [lia| reflexivity]. step. if_lia.
    fin_node AE HK RES MU2 WM2 MI2 ST2 FC2.
  Qed.

  Lemma arm_d15 : arm_stmt 15 (el_target 15).
  Proof.
    arm_open 15. step. step.
    eapply evt_cut; [eapply (acc_3ccd8_spec E OK); [exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact ST| lia| lia| lia| lia]|].
    intros ms' PO. unfold acc_3ccd8_post in PO.
    destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & A0R & _).
    fix_ret. destruct (acc_word_small za0 64 A0R) as (e1 & -> & E1). clear A0R.
    astep. rewrite ?sextw_small by lia. step. step. if_lia.
    fin_node AE HK RES MU2 WM2 MI2 ST2 FC2.
  Qed.

  Lemma arm_d16 : arm_stmt 16 (el_target 16).
  Proof. node_arm 16 acc_3cf14_spec. Qed.

  Lemma arm_d17 : arm_stmt 17 (el_target 17).
  Proof. node_arm 17 acc_3cf8c_spec. Qed.

  Lemma arm_d18 : arm_stmt 18 (el_target 18).
  Proof. node_arm 18 acc_3d00c_spec. Qed.

  Lemma arm_d19 : arm_stmt 19 (el_target 19).
  Proof. sel_arm 19 acc_3d054_spec. Qed.

  Lemma arm_d20 : arm_stmt 20 (el_target 20).
  Proof. sel_arm 20 acc_3d200_spec. Qed.

  Lemma arm_d21 : arm_stmt 21 (el_target 21).
  Proof. sel_arm 21 acc_3d3ac_spec. Qed.

End Arms.

Lemma arm_dead : forall a, 0 <= a < 22 -> a <> 8 -> arm_stmt a (el_target a).
Proof.
  intros a Ha H8.
  assert (C : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/
              a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]].
  - exact arm_d0.
  - exact arm_d1.
  - exact arm_d2.
  - exact arm_d3.
  - exact arm_d4.
  - exact arm_d5.
  - exact arm_d6.
  - exact arm_d7.
  - exact arm_d9.
  - exact arm_d10.
  - exact arm_d11.
  - exact arm_d12.
  - exact arm_d13.
  - exact arm_d14.
  - exact arm_d15.
  - exact arm_d16.
  - exact arm_d17.
  - exact arm_d18.
  - exact arm_d19.
  - exact arm_d20.
  - exact arm_d21.
Qed.
End WithCeiling0.
