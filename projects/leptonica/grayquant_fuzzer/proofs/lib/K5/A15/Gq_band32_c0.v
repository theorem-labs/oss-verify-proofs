(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs Gq_iface Gq_opcase Gq_rgb Gq_band32_loop Ed_fpkit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Lept_fuzzkit Gm_kit Gm_livekit Gm_livekit2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Gq_band32_exit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Ltac subfp_tac ::= clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; cbn [outside]; lia.
Lemma EVQ_exit : forall (P : machine_state -> Prop) ms ms', evt asegs P ms' -> ms' = ms -> evt asegs P ms.
Proof. intros P ms ms' H E. subst. exact H. Qed.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ ?m ?B ?cs2 =>
    let J := fresh "J" in
    assert (J : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split;
          [ exact H1
          | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?X _ => replace X with B by (clear; lia) end; exact H2 ]);
    clear H1 H2; cbn [app] in J; rename J into H1 end end.

Section BAND32C.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GG : gq_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

Lemma band32_c0 : gq_op_case RT 0 e_pixGenerateMaskByBand32 RA_FUZZ_OP4 7 4 2 BAND32_COST
    (fun a1 a2 a3 _ _ F => wZ a1 1 /\ wZ a2 1 /\ wZ a3 1 /\ freg_is F fa0 FZERO_W /\ freg_is F fa1 FZERO_W).
Proof using AF GP GG RERR PCS PCR PCI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> (A1 & A2 & A3 & FA0 & FA1) POBJ VDATA CNZ UC RAF RAS ENV RES AL.
  unfold wZ in A1, A2, A3. subst a1 a2 a3.
  unfold freg_is, fa0, fa1 in FA0, FA1.
  unfold lpost_f, lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold BAND32_COST, OP_COST, is_d32, MSG_COST in *.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGenerateMaskByBand32, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  hide POBJ.
  carve_frame 224%nat ST.
  walk_to AF MST [(usp - 224, usp)] [0xa07d0].
  (* [comment removed for export] *)
  step.
  repeat match goal with |- context [reg_get F ?r] => replace (reg_get F r) with FZERO_W by (symmetry; exact FA1) end.
  replace (nan_box (sgnj_val F_SGNJ (unbox_s FZERO_W) (unbox_s FZERO_W))) with FZERO_W by (vm_compute; reflexivity).
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v F) _ _ _ _ _) => remember (bvmap_set k v F) as F1 eqn:EF1 end.
  step.
  assert (RF10 : reg_get F1 (Z_to_bv 5 10) = FZERO_W) by (rewrite EF1, freg_get_other by reflexivity; exact FA0).
  repeat match goal with |- context [reg_get F1 ?r] => replace (reg_get F1 r) with FZERO_W by (symmetry; exact RF10) end.
  replace (nan_box (sgnj_val F_SGNJ (unbox_s FZERO_W) (unbox_s FZERO_W))) with FZERO_W by (vm_compute; reflexivity).
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v F1) _ _ _ _ _) => remember (bvmap_set k v F1) as F2 eqn:EF2 end.
  assert (RF8 : reg_get F2 (Z_to_bv 5 8) = FZERO_W) by (rewrite EF2, freg_get_other by reflexivity; rewrite EF1; apply freg_get_same; reflexivity).
  assert (RF9 : reg_get F2 (Z_to_bv 5 9) = FZERO_W) by (rewrite EF2; apply freg_get_same; reflexivity).
  awalk [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gg_stack_malloc1F RT GG) as SM1; unfold stack_malloc_contractF in SM1; eapply SM1 with (lo := lo); rt_side idtac.
  clear - CRB; destruct (p_d v =? 32); unfold RASTER_COST in CRB; lia.
  }
  unfold ret_stF.
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro))) _ => change fcx with (frm_clear fc) end.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa08c4].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCD.
  local_acc FSH fr 10%nat 80 FR64 FR1 ACCRR. local_acc FSH fr 12%nat 96 FR64 FR1 ACCGG. local_acc FSH fr 14%nat 112 FR64 FR1 ACCBB.
  park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa08f4; 0xa09d4; e_stack_malloc 1%nat].
  (* [comment removed for export] *)
  assert (DR : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
  rewrite !(sx32_small (p_d v)) by lia.
  destruct (Z.eq_dec (p_d v) 32) as [D32|DN32].
  all: cycle 1.
  brT.
  awalk [e_returnErrorPtr].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (CR4 : 4 <= rt_credit RT Σ) by (clear - CRB DN32; rewrite (proj2 (Z.eqb_neq (p_d v) 32) DN32) in CRB; exact CRB).
  pose proof RERR as RE. unfold returnError_cps in RE.
  eapply cps_seq.
  { eapply RE with (lo := lo); rt_side idtac.
  1: lit_in_fast.
  1: lit_in_fast.
  lenv_tac.
  }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa0ac8].
  idtac "MARK at pokes".
  try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
  Time (eapply evt_cut;
  [ eapply EVQ_exit;
    [ eapply band32_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
    | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
  | ]).
  clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold band32_exit_W, SHB in MUx. unfold band32_sh_f5 in FSH.
  idtac "MARK pokes applied".
  Time (lazymatch goal with A : ART RT ?Sx _ |- _ => loop_art RT AF Sx mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) end).
  Time (lazymatch type of MUx with munch _ ?ma ?mb =>
    loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
        first [ first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
                clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
                unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; solve [first [lia | Z.div_mod_to_equations; lia]]
              | repeat split; try exact I; notin_side ]) end).
  join_cells FRM FRMr.
  frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xa0b40
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 288, usp)] (@nil Z).
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 0, v, cv end.
  split.
  2: {
  split; [intros _; eqv|].
  split; [intros N; exfalso; apply N; reflexivity|].
  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP|].
  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia|].
  split; [eqv|]. split; [eqv|].
  rewrite (proj2 (Z.eqb_neq (p_d v) 32) DN32). repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
  }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [unfold rt_after_f; split; [split; [assumption| split; assumption]| split; assumption]|].
  split; [intros a Ha _; exact (AGF a Ha)|].
  split.
  { lazymatch goal with |- pix_obj (rt_live RT ?S) ?mc _ _ _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
      replace (rt_live RT S) with (rt_live RT Σ) by (symmetry; eqv);
      unfold hid in POBJ; exact (pix_obj_keep _ m mc pix v cv KL0 POBJ) end.
  }
  left; reflexivity.
  (* [comment removed for export] *)
  awalk [0xa0904; 0xa0a0c; e_stack_malloc 1%nat].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v ?F0) _ _ _ _ _) => remember (bvmap_set k v F0) as F3 eqn:EF3 end.
  step.
  assert (R3_15 : reg_get F3 (Z_to_bv 5 15) = Z_to_bv 64 18446744070479937536) by (rewrite EF3; apply freg_get_same; reflexivity).
  assert (R3_8 : reg_get F3 (Z_to_bv 5 8) = FZERO_W) by (rewrite EF3, freg_get_other by reflexivity; exact RF8).
  assert (R3_9 : reg_get F3 (Z_to_bv 5 9) = FZERO_W) by (rewrite EF3, freg_get_other by reflexivity; exact RF9).
  replace (reg_get F3 15) with (Z_to_bv 64 18446744070479937536) by (symmetry; exact R3_15).
  replace (reg_get F3 8) with FZERO_W by (symmetry; exact R3_8).
  replace (flt_s (Z_to_bv 64 18446744070479937536) FZERO_W) with false by (vm_compute; reflexivity).
  awalk [0xa0910; 0xa0a44].
  step.
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v ?F0) _ _ _ _ _) => remember (bvmap_set k v F0) as F4 eqn:EF4 end.
  assert (R4_18 : reg_get F4 (Z_to_bv 5 18) = FZERO_W) by (rewrite EF4; rewrite freg_get_same by reflexivity; vm_compute; reflexivity).
  assert (R4_15 : reg_get F4 (Z_to_bv 5 15) = Z_to_bv 64 18446744070479937536) by (rewrite EF4, freg_get_other by reflexivity; exact R3_15).
  assert (R4_8 : reg_get F4 (Z_to_bv 5 8) = FZERO_W) by (rewrite EF4, freg_get_other by reflexivity; exact R3_8).
  assert (R4_9 : reg_get F4 (Z_to_bv 5 9) = FZERO_W) by (rewrite EF4, freg_get_other by reflexivity; exact R3_9).
  step.
  replace (reg_get F4 9) with FZERO_W by (symmetry; exact R4_9).
  replace (reg_get F4 18) with FZERO_W by (symmetry; exact R4_18).
  replace (flt_s FZERO_W FZERO_W) with false by (vm_compute; reflexivity).
  awalk [0xa0920; 0xa0a44].
  step.
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v ?F0) _ _ _ _ _) => remember (bvmap_set k v F0) as F5 eqn:EF5 end.
  assert (R5_15 : reg_get F5 (Z_to_bv 5 15) = Z_to_bv 64 18446744070479937536) by (rewrite EF5; apply freg_get_same; reflexivity).
  assert (R5_18 : reg_get F5 (Z_to_bv 5 18) = FZERO_W) by (rewrite EF5, freg_get_other by reflexivity; exact R4_18).
  assert (R5_8 : reg_get F5 (Z_to_bv 5 8) = FZERO_W) by (rewrite EF5, freg_get_other by reflexivity; exact R4_8).
  assert (R5_9 : reg_get F5 (Z_to_bv 5 9) = FZERO_W) by (rewrite EF5, freg_get_other by reflexivity; exact R4_9).
  step.
  replace (reg_get F5 15) with (Z_to_bv 64 18446744070479937536) by (symmetry; exact R5_15).
  replace (reg_get F5 9) with FZERO_W by (symmetry; exact R5_9).
  replace (flt_s (Z_to_bv 64 18446744070479937536) FZERO_W) with false by (vm_compute; reflexivity).
  awalk [0xa092c; 0xa0a44].
  step.
  replace (reg_get F5 8) with FZERO_W by (symmetry; exact R5_8).
  replace (reg_get F5 18) with FZERO_W by (symmetry; exact R5_18).
  replace (flt_s FZERO_W FZERO_W) with false by (vm_compute; reflexivity).
  awalk [e_extractRGBValues; 0xa0a44].
  (* [comment removed for export] *)
  split_at FRM 9%nat FRT.
  lazymatch type of FRT with rw_cells _ _ _ [CB 52 ?jj] =>
      apply (rw_cells_split_CB asegs _ _ [] 52 jj [] [12; 4; 12; 4; 12; 4; 4]%nat) in FRT; [| reflexivity]; cbn [mk_CB_cells app] in FRT end.
  split_at FRT 1%nat FRr. split_at FRr 1%nat FRT2. split_at FRT2 1%nat FRg. split_at FRg 1%nat FRT3. split_at FRT3 1%nat FRb. split_at FRb 1%nat FRT4.
  destruct (cb4_c4 _ _ _ FRr) as (o1 & CR0). clear FRr. destruct (cb4_c4 _ _ _ FRg) as (o2 & CG0). clear FRg. destruct (cb4_c4 _ _ _ FRb) as (o3 & CB0). clear FRb.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  walk_to AF MST [(usp + -224 - 16, usp + -224); (fr + 80, fr + 80 + 4); (fr + 96, fr + 96 + 4); (fr + 112, fr + 112 + 4)] [e_extractRGBValues].   (* [comment removed for export] *)
  eapply evt_cut.
  {
  lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo _ |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (extractRGBValues_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -224) lo (Z_to_bv 64 1) (fr + 80) (fr + 96) (fr + 112) o1 o2 o3
                     CR0 CG0 CB0 ACCRR ACCGG ACCBB ltac:(lia) ltac:(clear - FR64; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(clear - FR64; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(clear - FR64; Z.div_mod_to_equations; lia)
                     ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) STx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - FRSH; unfold parked in FRSH; lia) ltac:(unfold SEGTOP_A; lia) MIx) as ZR end.
  unfold e_extractRGBValues in ZR. exact ZR.
  }
  intros ms' PO. unfold extractRGBValues_post in PO.
  destruct PO as (a0q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & mq & -> & MUl & WMl & MIl & STl & CR1 & CG1 & CB1).
  lazymatch type of MUl with munch _ ?ma ?mb =>
      lazymatch goal with A : ART RT ?S ma |- _ =>
        loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| exact I]]]]) end end.
  lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_transport ma mb MUl ltac:(fun Hx => clear - Hx CKR0 CKR FCD FCD0 FCS FCS0 FRSH FRHI FR0 FRSEG FR64 LOW LOR SPT SPB STa SP0W SP0R0 SP0R1; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  fix_ret_pc.
  (* [comment removed for export] *)
  step.
  replace (reg_get F5 9) with FZERO_W by (symmetry; exact R5_9).
  replace (reg_get F5 18) with FZERO_W by (symmetry; exact R5_18).
  replace (feq_s FZERO_W FZERO_W) with true by (vm_compute; reflexivity).
  awalk [0xa0958; 0xa0a84].
  step.
  replace (reg_get F5 8) with FZERO_W by (symmetry; exact R5_8).
  replace (reg_get F5 18) with FZERO_W by (symmetry; exact R5_18).
  replace (feq_s FZERO_W FZERO_W) with true by (vm_compute; reflexivity).
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; fframe_tac| exact I]]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCreate; 0xa0a84].
  (* [comment removed for export] *)
  rewrite !(sx32_small (p_w v)) by lia. rewrite !(sx32_small (p_h v)) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (WR : 0 < p_w v <= 20000) by lia. assert (HR : 0 < p_h v <= 20000) by lia.
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 1) by (unfold hdr_args_ok; split; [cbn [In]; tauto|]; split; [exact WR|]; split; [exact HR|]; clear - WR HR; split; [| assert ((p_w v * 1 + 31) / 32 <= 626) by (Z.div_mod_to_equations; lia); nia]; assert (1 <= (p_w v * 1 + 31) / 32) by (Z.div_mod_to_equations; lia); nia).
  assert (CRD : RASTER_COST + 64 <= rt_credit RT Σ) by (clear - CRB D32; rewrite D32 in CRB; cbn in CRB; lia).
  eapply cps_seq.
  {
  eapply PCS with (lo := lo) (w := p_w v) (h := p_h v) (d := 1).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [lia| reflexivity].
    - split; [lia| reflexivity].
    - split; [lia| reflexivity].
    - exact HAO.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [lia| lia| lia| exact LVP].
  }
  idtac "MARK pixCreate applied".
  (* [comment removed for export] *)
  after_call RT AF.
  (* [comment removed for export] *)
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σc; rename A into ARTC end.
  lazymatch goal with H : pix_obj (rt_live RT Σc) _ ?p ?vv _ |- _ => rename H into POD; rename p into pixd; rename vv into v1 end.
  lazymatch goal with H : rt_live RT Σc = _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w v1 = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h v1 = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d v1 = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into VDATA1 end.
  lazymatch goal with H : p_cmap v1 = 0 |- _ => rename H into VCMAP end.
  assert (FRSc : rt_frames RT Σc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σc = _ |- _ => rewrite E end; exact FRS).
  assert (LVC : rt_live RT Σc = (p_data v1, rsize v1) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVN; repeat match goal with E : rt_live _ _ = rt_live RT Σ |- _ => rewrite E end; reflexivity).
  assert (SP0C : rt_sp0 RT Σc = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRC : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σc) by (repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E in * end; lia).
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DDIN & DD0 & DD16 & DDN) & DDNE)]; [exfalso; exact (VDATA1 PDZ)|].
  set (dat := p_data v1) in *. set (rs := rsize v1) in *.
  assert (SUBP : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> pixd)
    by (intros e He; split; [rewrite LVC; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ e ARTC LVC); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBD : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> dat)
    by (intros e He; split; [rewrite LVC; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [] dat rs _ e ARTC LVC); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC PDIN SUBP);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC DDIN SUBD);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NPS : pix <> pixd) by (exact (proj2 (SUBP (pix, 64) PIN))).
  assert (NDS : pix <> dat) by (exact (proj2 (SUBD (pix, 64) PIN))).
  assert (NSP : p_data v <> pixd) by (exact (proj2 (SUBP (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  assert (NSD : p_data v <> dat) by (exact (proj2 (SUBD (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  idtac "MARK names".
  (* [comment removed for export] *)
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  fframe_chunk RT AF fr 1%nat 128 pixd 64. fframe_chunk RT AF fr 1%nat 128 dat rs.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (EWD : p_wpl v1 = (p_w v + 31) / 32) by (destruct HOKD as (_ & _ & _ & Q4 & _); rewrite VW, VD in Q4; rewrite Q4; f_equal; lia).
  assert (ERS : rs = 4 * (p_wpl v1 * p_h v)) by (unfold rs, rsize; rewrite VH; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v1 * p_h v) <= 67108864) by (destruct HOKD as (_ & _ & _ & _ & Q5); rewrite VH in Q5; exact Q5).
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "MARK before walk to PCR".
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyResolution; 0xa0a84].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVC; right; right; exact He).
  unfold hid in POD, POBJ.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σc _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD1 : pix_obj (rt_live RT Σc) mc pixd v1 (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); split; [unfold pix_cells; rewrite VW, VH, VD, VCMAP; exact PX| split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS1 : pix_obj (rt_live RT Σc) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUB); apply (pix_obj_agree (rt_live RT Σ) PF m mc pix v cv POBJ AGF PML); unfold pix_cells; exact PS) end.
  hide POD. hide POBJ.
  idtac "MARK objs for PCR".
  (* [comment removed for export] *)
  eapply cps_seq.
  {
  eapply PCR with (lo := lo) (pixd := pixd) (pixs := pix) (vd := v1) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POD1.
  - exact POS1.
  - intros E; apply NPS; symmetry; exact E.
  - lenv_tac.
  }
  idtac "MARK PCR applied".
  (* [comment removed for export] *)
  clear POD1 POS1.
  lazymatch goal with A : ART RT Σc ?mm |- _ =>
    pose proof (live_apart2 RT AF Σc mm pix 64 pixd 64 A (LSUB _ PIN) PDIN ltac:(intros E; inversion E; exact (NPS ltac:(assumption)))) as DSP;
    pose proof (live_apart2 RT AF Σc mm pix 64 dat rs A (LSUB _ PIN) DDIN ltac:(intros E; inversion E; exact (NDS ltac:(assumption)))) as DSD;
    pose proof (live_apart2 RT AF Σc mm pixd 64 dat rs A PDIN DDIN ltac:(intros E; inversion E; apply DDNE; symmetry; assumption)) as DPD;
    pose proof (live_apart2 RT AF Σc mm (p_data v) (4 * (p_wpl v * p_h v)) pixd 64 A (LSUB _ DIN) PDIN ltac:(intros E; inversion E; exact (NSP ltac:(assumption)))) as DRP;
    pose proof (live_apart2 RT AF Σc mm (p_data v) (4 * (p_wpl v * p_h v)) dat rs A (LSUB _ DIN) DDIN ltac:(intros E; inversion E; exact (NSD ltac:(assumption)))) as DRD end.
  park DSP. park DSD. park DPD. park DRP. park DRD.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σc |- _ => rewrite E end; apply LSUB; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  idtac "MARK after PCR".
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σr; rename A into ARTR end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (LVR : rt_live RT Σr = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σr = _ |- _ => rewrite E end; reflexivity).
  assert (FRSr : rt_frames RT Σr = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σr = _ |- _ => rewrite E end; exact FRSc).
  assert (SP0r : rt_sp0 RT Σr = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRr : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σr) by (lazymatch goal with E : rt_credit RT Σc <= rt_credit RT Σr |- _ => clear - E CRC; lia end).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyInputFormat; 0xa0a84].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; apply LSUB; exact He).
  unfold hid in POD, POBJ.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σr _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD2 : pix_obj (rt_live RT Σr) mc pixd (pv_res v1 v) (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); rewrite LVR;
          split; [unfold pix_cells, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PX|
          split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS2 : pix_obj (rt_live RT Σr) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUBr); apply (pix_obj_agree (rt_live RT Σ) PF m mc pix v cv POBJ AGF PML); unfold pix_cells; exact PS) end.
  hide POD. hide POBJ.
  eapply cps_seq.
  {
  eapply PCI with (lo := lo) (pixd := pixd) (pixs := pix) (vd := pv_res v1 v) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POD2.
  - exact POS2.
  - intros E; apply NPS; symmetry; exact E.
  - lenv_tac.
  }
  clear POD2 POS2.
  idtac "MARK PCI applied".
  (* [comment removed for export] *)
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σr |- _ => rewrite E end; apply LSUBr; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σi; rename A into ARTI end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (LVI : rt_live RT Σi = (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σi = _ |- _ => rewrite E end; rewrite LVR; exact LVC).
  assert (FRSi : rt_frames RT Σi = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σi = _ |- _ => rewrite E end; exact FRSr).
  assert (SP0i : rt_sp0 RT Σi = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRi : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σi) by (lazymatch goal with E : rt_credit RT Σr <= rt_credit RT Σi |- _ => clear - E CRr; lia end).
  assert (LSUBi : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σi)) by (intros e He; rewrite LVI; right; right; exact He).
  assert (PDINi : In (pixd, 64) (rt_live RT Σi)) by (rewrite LVI; right; left; reflexivity).
  assert (DDINi : In (dat, rs) (rt_live RT Σi)) by (rewrite LVI; left; reflexivity).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after PCI".
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa0cc4; 0xa0a84].
  (* [comment removed for export] *)
  rewrite !(sx32_small (p_h v)) by lia.
  awalk [0xa0d00; 0xa0a84].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  lazymatch goal with A : ART RT Σi ?ma, WMa : wmono asegs ?ma ?mm |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (wr_at_transport asegs ma mm dat rs (proj1 (af_acc_live RT AF Σi ma dat rs A DDINi)) WMa) as WRD end.
  lazymatch goal with WMa : wmono asegs m ?mm |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (wr_at_transport asegs m mm (p_data v) (4 * (p_wpl v * p_h v)) (proj1 (af_acc_live RT AF Σ m (p_data v) (4 * (p_wpl v * p_h v)) ART0 DIN)) WMa) as WRS end.
  idtac "MARK wr_at".
  (* [comment removed for export] *)
  rewrite ERS in WRD.
  apply wr_at_rw_CB in WRD; [| clear - RSD0; lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm dat dbs (p_wpl v1 * p_h v) DBC ltac:(rewrite DBL; clear - RSD0; lia)) as (wd & UAD & UADL) end.
  apply wr_at_rw_CB in WRS; [| clear - HRS0; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC.
  lazymatch type of SBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm (p_data v) sbs (p_wpl v * p_h v) SBC ltac:(rewrite SBL; clear - HRS0; lia)) as (ws & UAS & UASL) end.
  pose proof FRM as HC. split_at HC 4%nat HCW. split_at HCW 1%nat HC3. split_at HC3 1%nat HCH. split_at HCH 1%nat HC5. clear HC HC3 HC5.
  rewrite (sx32_small (p_w v)) in HCW by (clear - HW0 HW2; lia).
  rewrite (sx32_small (p_h v)) in HCH by (clear - HH0 HH2; lia).
  assert (EWS : p_wpl v = p_w v) by (rewrite HWPL, D32; clear - HW0; Z.div_mod_to_equations; lia).
  assert (WDR : 0 < p_wpl v1 <= 2^20 /\ p_w v <= 32 * p_wpl v1) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
  destruct WDR as (WDR & WDW).
  idtac "MARK raster facts".
  (* [comment removed for export] *)
  walk_to AF MST [(dat, dat + 4 * (p_wpl v1 * p_h v))] [0xa0d00].   (* [comment removed for export] *)
  rewrite !(sx32_small (p_wpl v1)) by (clear - WDR; lia).
  rewrite !(sx32_small (p_wpl v)) by (clear - EWS HW0 HW2; lia). rewrite !(unsigned_lit (p_wpl v)) by (clear - EWS HW0 HW2; lia).
  replace (p_wpl v * 4) with (4 * p_wpl v) by (clear; lia).
  assert (Q1 : Z.of_nat (Z.to_nat (p_h v)) = p_h v - 0) by (clear - HH0; lia).
  assert (Q3 : (1 <= Z.to_nat (p_h v))%nat) by (clear - HH0; lia).
  assert (Q4 : 0 < p_w v <= 20000) by (clear - HW0 HW2; lia).
  assert (Q5 : p_w v <= p_wpl v) by (clear - EWS; lia).
  assert (Q7 : 0 < p_wpl v <= 2^20) by (clear - EWS HW0 HW2; lia).
  assert (Q9 : 0 < p_h v <= 2^20) by (clear - HH0 HH2; lia).
  assert (Q10 : p_wpl v * p_h v <= 2^24) by (clear - HRS1; lia).
  assert (Q11 : p_wpl v1 * p_h v <= 2^24) by (clear - RSD1; lia).
  assert (S8 : p_data v mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (SHI : p_data v + 4 * (p_wpl v * p_h v) <= 2^47) by (clear - CKR0 SP0R1; lia).
  assert (SSH : p_data v + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= p_data v) by (clear - CKH0; unfold parked in CKH0; lia).
  assert (SSEG : p_data v + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= p_data v) by (clear - CKS0; unfold parked, SEGTOP_A in *; lia).
  assert (T8 : dat mod 8 = 0) by (clear - DD16; Z.div_mod_to_equations; lia).
  assert (THI : dat + 4 * (p_wpl v1 * p_h v) <= 2^47) by (clear - CKR2 ERS SP0R1; lia).
  assert (TSH : dat + 4 * (p_wpl v1 * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= dat) by (clear - CKH2 ERS; unfold parked in CKH2; lia).
  assert (TSEG : dat + 4 * (p_wpl v1 * p_h v) <= 0x10000 \/ SEGTOP_A <= dat) by (clear - CKS2 ERS; unfold parked, SEGTOP_A in *; lia).
  assert (SEP : p_data v + 4 * (p_wpl v * p_h v) <= dat \/ dat + 4 * (p_wpl v1 * p_h v) <= p_data v) by (clear - DRD ERS; unfold parked in DRD; lia).
  assert (W0 : 0 < fr + 32) by (clear - FR0; lia).
  assert (WHI : fr + 32 + 4 <= 2^47) by (clear - FRHI SP0R1; lia).
  assert (WSEP : fr + 32 + 4 <= dat \/ dat + 4 * (p_wpl v1 * p_h v) <= fr + 32) by (clear - FCD2 ERS; unfold parked in FCD2; lia).
  assert (H0' : 0 < fr + 48) by (clear - FR0; lia).
  assert (HHI : fr + 48 + 4 <= 2^47) by (clear - FRHI SP0R1; lia).
  assert (HSEP : fr + 48 + 4 <= dat \/ dat + 4 * (p_wpl v1 * p_h v) <= fr + 48) by (clear - FCD2 ERS; unfold parked in FCD2; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ACCS : acc asegs mm (p_data v) (4 * (p_wpl v * p_h v))) by assumption;
      assert (ACCD : acc asegs mm dat (4 * (p_wpl v1 * p_h v))) by (rewrite <- ERS; assumption) end.
  idtac "MARK premises".
  (* [comment removed for export] *)
  eapply evt_cut.
  {
  lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (band32_rows (Z.to_nat (p_h v)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (p_data v) dat (p_wpl v) (p_wpl v1) (p_w v) (p_h v) (fr + 32) (fr + 48) ws wd
                     Q1 ltac:(lia) Q3 Q4 Q5 WDW Q7 WDR Q9 Q10 Q11 D0 S8 SHI SSH SSEG DD0 T8 THI TSH TSEG SEP W0 WHI WSEP H0' HHI HSEP UAS UASL ACCS UAD UADL ACCD HCW HCH MIx) as ZR end.
  unfold SHB in ZR.
  replace (p_data v + 4 * (0 * p_wpl v)) with (p_data v) in ZR by (clear; lia).
  exact ZR.
  }
  idtac "MARK rows applied".
  (* [comment removed for export] *)
  intros ms' PO. unfold band32_exit in PO.
  destruct PO as (t0r & t1r & t2r & a2r & a3r & a7r & s6r & t3r & t4r & t5r & mr & wdr & -> & MUr & WMr & MIr & UASq & ACCSq & UADq & UADLq & ACCDq & HCWq & HCHq).
  unfold SHB.
  assert (FCS2' : dat + rs <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= dat)
    by (clear - FCS2; unfold parked in FCS2; Z.div_mod_to_equations; lia).
  loop_art RT AF Σi mr lo MUr ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINi| rewrite ERS; lia]| exact I]).
  clear UAS UASL UAD UADL SBC DBC SBL DBL HCW HCH ACCS ACCD UASq ACCSq UADq UADLq ACCDq HCWq HCHq.
  idtac "MARK loop_art".
  (* [comment removed for export] *)
  lazymatch type of MUr with munch _ ?ma ?mb =>
      loop_transport ma mb MUr ltac:(fun Hx => clear - Hx CKR2 CKS2 ERS RSD0 FCD2 FCS2' DSD DPD DRD CKR0 CKR CKR1 FRSH FRHI FR0 FRSEG FR64 LOW LOR SPT SPB STa SP0W SP0R0 SP0R1; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "MARK loop_transport".
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINi| rewrite ERS; lia]| exact I]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (NCD _ Hx) as NCDx; clear - NCDx ERS; split; [lia| exact I]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa0ac8].
  idtac "MARK at pokes".
  try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
  Time (eapply evt_cut;
  [ eapply EVQ_exit;
    [ eapply band32_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
    | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
  | ]).
  clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold band32_exit_W, SHB in MUx. unfold band32_sh_f5 in FSH.
  idtac "MARK pokes applied".
  Time (lazymatch goal with A : ART RT ?Sx _ |- _ => loop_art RT AF Sx mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) end).
  Time (lazymatch type of MUx with munch _ ?ma ?mb =>
    loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
        first [ first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
                clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
                unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; solve [first [lia | Z.div_mod_to_equations; lia]]
              | repeat split; try exact I; notin_side ]) end).
  join_cells FRM FRMr.
  (* [comment removed for export] *)
  frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xa0b40
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK frame released".
  (* [comment removed for export] *)
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp)] (@nil Z).
  cps_stop.
  idtac "MARK epilogue walked".
  (* [comment removed for export] *)
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  set (vf := pv_inf (pv_res v1 v) v).
  assert (VFC : p_cmap vf = 0) by (exact VCMAP).
  assert (VFD : p_data vf = dat) by reflexivity.
  unfold hid in SUBP, SUBD, HOKD.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vf, (mkCmapv 0 0 0 0) end.
  split.
  2: {
  split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
  split.
  { intros _. rewrite LV2, LVI.
    pose proof (live_destroy_tmpl (rt_live RT Σ) pixd dat rs 0 0 0 vf (mkCmapv 0 0 0 0) VFD VFC
                  (fun N => False_ind _ (N eq_refl)) VDATA1 DDNE (fun N => False_ind _ (N eq_refl))
                  (fun e He => conj (proj2 (SUBP e He)) (proj2 (SUBD e He))) (fun N => False_ind _ (N eq_refl))) as LD.
    cbn [Z.eqb] in LD. exact LD. }
  split.
  { intros p n Hp. rewrite LV2, LVI in Hp. cbn [In] in Hp. destruct Hp as [Hp|[Hp|Hp]]; [injection Hp as <- <-; exact DDN| injection Hp as <- <-; lia| exact (LVP p n Hp)]. }
  split; [rewrite LV2, LVI; cbn [length]; lia|].
  split; [exact FRS2|]. split; [rewrite SP2; exact SP0i|].
  rewrite D32. cbn [Z.eqb Pos.eqb]. rewrite CR2. clear - CRi. unfold RASTER_COST in *. lia.
  }
  idtac "MARK post part 2".
  (* [comment removed for export] *)
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [unfold rt_after_f; split; [split; [assumption| split; assumption]| split; assumption]|].
  split; [intros a Ha _; exact (AGF a Ha)|].
  split.
  { rewrite LV2.
    lazymatch goal with |- pix_obj _ ?mc _ _ _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
      apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUBi);
      unfold hid in POBJ; exact (pix_obj_keep _ m mc pix v cv KL0 POBJ) end.
  }
  right. split; [| rewrite VFD; exact VDATA1].
  rewrite LV2.
  split; [unfold pix_cells, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PXD|].
  split; [split; [exact PDINi| split; [exact PD0| split; [exact PD16| lia]]]|].
  split; [exact HOKD|].
  split; [right; split; [split; [exact DDINi| split; [exact DD0| split; [exact DD16| exact DDN]]]| exact DDNE]| left; exact VFC].
Qed.
End BAND32C.
