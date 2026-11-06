(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_walkkit Km_kit Km_frompix_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section KFP_EXIT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (pix : Z) (v : pixv) (cv : cmapv) (fr : Z).


Lemma kfp_exit_ok_0 : kfp_exit_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr.
Proof using AF RC GP.
  intros S mc kel hv js j0
    r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r21 r22 r23 r24 r25 r28 r29 r30 r31 F' fc'
    CTX ARTc MIc WMc ST FR FHV FSH LH SSP AGF FRS SP0S CRS POBJ KOR.
  destruct CTX as (FDO & MST & ART0 & POBJ0 & LOW & LOR & LO0 & SPT & SPA & SPB & LVP & FRB & DNZ & FR0 & FR64 & NFA).
  unfold kfp_stack_0 in FR. unfold kfp_fshadow in FSH.
  destruct (af_client_consts RT AF S mc ARTc) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF S mc ARTc) as SP0R. pose proof (af_sp0_win RT AF S mc ARTc) as SP0W.
  rewrite SP0S in SP0R, SP0W.
  unfold entry_st, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  set (QF := kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv).
  set (PF := kfp_PF RT Σ usp) in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST as (STa & STb & _).
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FRA0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FRA64 & FRSEG).
  pose proof (af_frames_hi RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite SP0S in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  park_disj.
  walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92420].
  idtac "X1-WALK".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch _ mc ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (KL1 : keeps_live (rt_live RT S) mc m1)
      by (apply (keeps_live_walk1 RT AF S mc m1 fr usp (usp - 128) ARTc ltac:(rewrite FRS; left; reflexivity)
                   ltac:(rewrite SP0S; unfold STACK_WIN; lia) MUx));
    pose proof (pix_obj_keep _ mc m1 pix v cv KL1 POBJ) as POBJ1;
    assert (KOR1 : (kel = 0 /\ rt_live RT S = rt_live RT Σ)
                   \/ (exists data rows, p_d v = 8 /\ kel_obj (rt_live RT S) m1 kel (p_h v) (p_w v) 2 2 data rows
                                        /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ)))
      by (destruct KOR as [K|(d & rs & D8 & KO & LV)]; [left; exact K| right; exists d, rs; split; [exact D8| split; [exact (kel_obj_keep _ _ _ _ _ _ _ _ _ _ KL1 KO)| exact LV]]]) end.
  clear POBJ KOR.
  idtac "X2-OBJ".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (LVINC : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)).
  { intros e He. destruct KOR1 as [(_ & LV)|(d & rs & _ & _ & LV)]; rewrite LV; [exact He|].
    unfold km_live. apply in_or_app. right. right. right. exact He. }
  frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 599080
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "X3-RELEASE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with K : forall b kk, In (b, kk) (rt_live RT S) -> forall a : word, _ -> ?mb a = ?ma a |- _ =>
    pose proof (pix_obj_keep _ ma mb pix v cv K POBJ1) as POBJ2;
    assert (KOR2 : (kel = 0 /\ rt_live RT S = rt_live RT Σ)
                   \/ (exists data rows, p_d v = 8 /\ kel_obj (rt_live RT S) mb kel (p_h v) (p_w v) 2 2 data rows
                                        /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ)))
      by (destruct KOR1 as [KK|(d & rs & D8 & KO & LV)]; [left; exact KK| right; exists d, rs; split; [exact D8| split; [exact (kel_obj_keep _ _ _ _ _ _ _ _ _ _ K KO)| exact LV]]]) end.
  clear POBJ1 KOR1.
  idtac "X4-OBJ".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 128, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -128) |- _ => release_frame FR ST' usp end).
  idtac "X4-WALK".
  (* [comment removed for export] *)
  cps_stop.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
    lazymatch goal with
    | _ : ART RT S mf |- _ => idtac
    | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
        assert (ARTf : ART RT S mf)
          by (apply (art_client_writes RT AF S mm mf (usp + -128) W A MUx WMx);
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
              | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
        (* [comment removed for export] *)
        assert (KL3 : keeps_live (rt_live RT S) mm mf)
          by (intros bb kk Hin a Ha; apply MUx; cbn [outside]; split; [| exact I];
              pose proof (af_live_range RT AF S mm bb kk A Hin) as (_ & R1 & _); unfold STACK_WIN in R1;
              repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R1 end; lia);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
    end end.
  idtac "X5-ART".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  rename POBJ2 into POBJ3. rename KOR2 into KOR3.
  idtac "X6-OBJ".
  apply cps_finish; intros c Hc; subst QF; unfold kfp_post; cbv beta.
  lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end.
  exists kel.
  lazymatch goal with |- _ /\ (kel = 0 -> ?L = _) /\ _ =>
    assert (LVS : L = rt_live RT S) by (repeat match goal with H : rt_live _ _ = rt_live RT S |- _ => rewrite H end; reflexivity) end.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    idtac "X6-A".
    split; [intros a Ha _; apply AGF; exact Ha|].
    rewrite LVS. split; [exact POBJ3|].
    destruct KOR3 as [(K0 & _)|(d & rs & D8 & KO & LV)]; [left; exact K0| right; exists d, rs; split; [exact D8| split; [exact KO| exact LV]]].
  - idtac "X6-B".
    split; [intros K0; rewrite LVS; destruct KOR3 as [(_ & LV)|(d & rs & _ & KO & _)]; [exact LV| destruct KO as (_ & (_ & KP & _) & _); lia]|].
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    split; [reflexivity| split; [reflexivity| lia]].
Qed.

Lemma kfp_exit_ok_16 : kfp_exit_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv fr.
Proof using AF RC GP.
  intros S mc kel hv js j0 j1
    r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r21 r22 r23 r24 r25 r28 r29 r30 r31 F' fc'
    CTX ARTc MIc WMc ST FR FHV FSH LH SSP AGF FRS SP0S CRS POBJ KOR.
  destruct CTX as (FDO & MST & ART0 & POBJ0 & LOW & LOR & LO0 & SPT & SPA & SPB & LVP & FRB & DNZ & FR0 & FR64 & NFA).
  unfold kfp_stack_16 in FR. unfold kfp_fshadow in FSH.
  destruct (af_client_consts RT AF S mc ARTc) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF S mc ARTc) as SP0R. pose proof (af_sp0_win RT AF S mc ARTc) as SP0W.
  rewrite SP0S in SP0R, SP0W.
  unfold entry_st, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  set (QF := kfp_post RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix v cv).
  set (PF := kfp_PF RT Σ usp) in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST as (STa & STb & _).
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FRA0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FRA64 & FRSEG).
  pose proof (af_frames_hi RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite SP0S in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  park_disj.
  walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92420].
  idtac "X1-WALK".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch _ mc ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (KL1 : keeps_live (rt_live RT S) mc m1)
      by (apply (keeps_live_walk1 RT AF S mc m1 fr usp (usp - 144) ARTc ltac:(rewrite FRS; left; reflexivity)
                   ltac:(rewrite SP0S; unfold STACK_WIN; lia) MUx));
    pose proof (pix_obj_keep _ mc m1 pix v cv KL1 POBJ) as POBJ1;
    assert (KOR1 : (kel = 0 /\ rt_live RT S = rt_live RT Σ)
                   \/ (exists data rows, p_d v = 8 /\ kel_obj (rt_live RT S) m1 kel (p_h v) (p_w v) 2 2 data rows
                                        /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ)))
      by (destruct KOR as [K|(d & rs & D8 & KO & LV)]; [left; exact K| right; exists d, rs; split; [exact D8| split; [exact (kel_obj_keep _ _ _ _ _ _ _ _ _ _ KL1 KO)| exact LV]]]) end.
  clear POBJ KOR.
  idtac "X2-OBJ".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (LVINC : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)).
  { intros e He. destruct KOR1 as [(_ & LV)|(d & rs & _ & _ & LV)]; rewrite LV; [exact He|].
    unfold km_live. apply in_or_app. right. right. right. exact He. }
  frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 599080
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "X3-RELEASE".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with K : forall b kk, In (b, kk) (rt_live RT S) -> forall a : word, _ -> ?mb a = ?ma a |- _ =>
    pose proof (pix_obj_keep _ ma mb pix v cv K POBJ1) as POBJ2;
    assert (KOR2 : (kel = 0 /\ rt_live RT S = rt_live RT Σ)
                   \/ (exists data rows, p_d v = 8 /\ kel_obj (rt_live RT S) mb kel (p_h v) (p_w v) 2 2 data rows
                                        /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ)))
      by (destruct KOR1 as [KK|(d & rs & D8 & KO & LV)]; [left; exact KK| right; exists d, rs; split; [exact D8| split; [exact (kel_obj_keep _ _ _ _ _ _ _ _ _ _ K KO)| exact LV]]]) end.
  clear POBJ1 KOR1.
  idtac "X4-OBJ".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 144, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -144) |- _ => release_frame FR ST' usp end).
  idtac "X4-WALK".
  (* [comment removed for export] *)
  cps_stop.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
    lazymatch goal with
    | _ : ART RT S mf |- _ => idtac
    | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
        assert (ARTf : ART RT S mf)
          by (apply (art_client_writes RT AF S mm mf (usp + -144) W A MUx WMx);
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
              | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
        (* [comment removed for export] *)
        assert (KL3 : keeps_live (rt_live RT S) mm mf)
          by (intros bb kk Hin a Ha; apply MUx; cbn [outside]; split; [| exact I];
              pose proof (af_live_range RT AF S mm bb kk A Hin) as (_ & R1 & _); unfold STACK_WIN in R1;
              repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R1 end; lia);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
    end end.
  idtac "X5-ART".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  rename POBJ2 into POBJ3. rename KOR2 into KOR3.
  idtac "X6-OBJ".
  apply cps_finish; intros c Hc; subst QF; unfold kfp_post; cbv beta.
  lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end.
  exists kel.
  lazymatch goal with |- _ /\ (kel = 0 -> ?L = _) /\ _ =>
    assert (LVS : L = rt_live RT S) by (repeat match goal with H : rt_live _ _ = rt_live RT S |- _ => rewrite H end; reflexivity) end.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    idtac "X6-A".
    split; [intros a Ha _; apply AGF; exact Ha|].
    rewrite LVS. split; [exact POBJ3|].
    destruct KOR3 as [(K0 & _)|(d & rs & D8 & KO & LV)]; [left; exact K0| right; exists d, rs; split; [exact D8| split; [exact KO| exact LV]]].
  - idtac "X6-B".
    split; [intros K0; rewrite LVS; destruct KOR3 as [(_ & LV)|(d & rs & _ & KO & _)]; [exact LV| destruct KO as (_ & (_ & KP & _) & _); lia]|].
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    split; [reflexivity| split; [reflexivity| lia]].
Qed.
End KFP_EXIT.
