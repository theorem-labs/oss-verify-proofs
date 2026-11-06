(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Cf_iface Cf_kit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section PD_NULL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixDestroy_null_ok : pixDestroy_null_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp
    FDO MST -> -> OP PPC ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL, optr, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct OP as (OWN & PP0 & PP8 & PPH & PPS).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  clearbody usp.
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PPLO : pp + 8 <= lo).
  { destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & R & _). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. lia. }
  pose proof PPC as PPC0. hide PPC0.
  assert (AL : usp mod 32 = 16 \/ usp mod 32 = 0) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    park_disj; carve_frame 112%nat ST; park OWN.
  walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 0%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  unpark_accok OWN AGF.
  (eapply cps_seq; [pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac|]).
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [auto| auto| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
  fframe_optr RT AF fr 0%nat 64 OWN usp; park OWN.
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; clear_acc; park_disj.
  walk_to AF MST [(usp - 112, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x906d8].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_accok_munch OWN MUx (rt_live RT Σ) (rt_frames RT Σ) usp
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *.
  (* [comment removed for export] *)
  lazymatch type of AGF with agree_on _ _ ?mm =>
    assert (PPC1 : rw_cells asegs mm pp [C8 (Z_to_bv 64 0)])
      by (unfold hid in PPC0; apply (rw_cells_agree_nw asegs m mm pp _ PPC0); apply (agree_sub PF0 _ m mm AGF); intros zx Hx;
          cbn [cells_size csize Nat.add] in Hx; exact (accok_aclient _ _ _ usp pp 8 zx OWN ltac:(lia))) end.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 112, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_stack_malloc 0%nat; 0x90828].
  frame_release RT AF GP MST Σ fr 0%nat 64 PF0 AGF PFS usp lo 0x90830
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; park_disj.
  walk_to AF MST [(usp - 112, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end).
  cps_stop.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
    lazymatch goal with A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
      assert (ARTf : ART RT S mf)
        by (apply (art_client_writes RT AF S mm mf (usp + -112) W A MUx WMx);
            [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
    end end.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists; split;
  [ eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists;
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|];
    split; [split; [split; [exact ARTf| split; [assumption| split; [| assumption]]]| split; assumption]|];
    [ repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans
    | intros a Ha Ho; apply AGF; lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha; [exact Ha|] end;
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity ]
  | repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; repeat split; auto; lia ].
  - (* [comment removed for export] *)
    park_disj; carve_frame 96%nat ST; park OWN.
  walk_to AF MST [(usp - 96, usp)] [e_stack_malloc 0%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  unpark_accok OWN AGF.
  (eapply cps_seq; [pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac|]).
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [auto| auto| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
  fframe_optr RT AF fr 0%nat 64 OWN usp; park OWN.
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; clear_acc; park_disj.
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x906d8].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_accok_munch OWN MUx (rt_live RT Σ) (rt_frames RT Σ) usp
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *.
  (* [comment removed for export] *)
  lazymatch type of AGF with agree_on _ _ ?mm =>
    assert (PPC1 : rw_cells asegs mm pp [C8 (Z_to_bv 64 0)])
      by (unfold hid in PPC0; apply (rw_cells_agree_nw asegs m mm pp _ PPC0); apply (agree_sub PF0 _ m mm AGF); intros zx Hx;
          cbn [cells_size csize Nat.add] in Hx; exact (accok_aclient _ _ _ usp pp 8 zx OWN ltac:(lia))) end.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 96, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_stack_malloc 0%nat; 0x90828].
  frame_release RT AF GP MST Σ fr 0%nat 64 PF0 AGF PFS usp lo 0x90830
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; park_disj.
  walk_to AF MST [(usp - 96, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -96) |- _ => release_frame FR ST' usp end).
  cps_stop.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
    lazymatch goal with A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
      assert (ARTf : ART RT S mf)
        by (apply (art_client_writes RT AF S mm mf (usp + -96) W A MUx WMx);
            [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
    end end.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists; split;
  [ eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists;
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|];
    split; [split; [split; [exact ARTf| split; [assumption| split; [| assumption]]]| split; assumption]|];
    [ repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans
    | intros a Ha Ho; apply AGF; lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha; [exact Ha|] end;
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity ]
  | repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; repeat split; auto; lia ].
Qed.
End PD_NULL.
