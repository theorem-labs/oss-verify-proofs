(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section STDERR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.

Theorem lept_stderr_ok : lept_stderr_cps RT.
Proof using AF RC GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fmt kinds lo
    FDO MST -> -> FMT ARGS LH SSP ART0 MI ST LOW LOR SPT SPA SPB FRB CRB.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_lept_stderr, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - carve_frame 160%nat ST.
    Time walk_to AF MST [(usp - 160, usp)] [0x48d04].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_6 RT GP) as SM6; unfold stack_malloc_contract' in SM6; eapply SM6 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [auto| auto| lia]).
    lazymatch goal with H : rt_frames RT ?S = (?f, 6%nat) :: _ |- _ => rename H into FRS; set (fr := f) in * end.
    change (fs_size 6) with 4096 in *. change (4096 / 8) with 512 in *. change (4096 - 8) with 4088 in *.
    lazymatch goal with H : wr_at asegs ?mm fr 4088 |- _ => destruct (wr_at_rw_CB mm fr 4088 H ltac:(lia)) as (jf & FRM); clear H end.
    lazymatch goal with H : wr_at asegs ?mm (shad fr) 512 |- _ => destruct (wr_at_rw_CB mm (shad fr) 512 H ltac:(lia)) as (js & FSH); clear H end.
    change (Z.to_nat 4088) with 4088%nat in FRM. change (Z.to_nat 512) with 512%nat in FSH.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      pose proof (af_frames_range RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _);
      pose proof (af_frames_align RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG);
      pose proof (af_frames_hi RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as FRSH end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NFA : forall a, PF a -> (a < fr \/ fr + 4096 <= a) /\ (a < shad fr \/ shad (fr + 4096) <= a))
        by (intros a Ha; apply (new_frame_apart RT AF S mm fr 6 (rt_frames RT Σ) (rt_live RT Σ) usp a A FRS);
            [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia
            | exact Ha ]) end.
    change (fs_size 6) with 4096 in *.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    Time walk_to AF MST [(usp - 160, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x61130].
    (* [comment removed for export] *)
    lazymatch type of FSH with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: [CB 504 ?j]) =>
      apply (rw_cells_split_CB asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7] 504 j [] [250; 254]%nat) in FSH; [| reflexivity];
      cbn [mk_CB_cells app] in FSH;
      split_cells FSH [c0; c1; c2; c3; c4; c5; c6; c7] FSHb end.
    lazymatch type of FSHb with rw_cells _ _ _ (?c :: _) => split_cells FSHb [c] FSHc end.
    pose proof (proj2 FSHb) as WRb. cbn [cells_size csize Nat.add] in WRb. change (Z.of_nat 250) with 250 in WRb.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (rc_set_shadow RT RC 248) as SS; unfold set_shadow_contract in SS; eapply SS with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | Z.div_mod_to_equations; lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    Time walk_to AF MST [(usp - 160, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x61010].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (rc_set_shadow RT RC 0) as SS0; unfold set_shadow_contract in SS0; eapply SS0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | Z.div_mod_to_equations; lia]).
    lazymatch goal with H : bytes_at asegs ?mm (fr / 8 + 2147450888) (repeat _ _) |- _ =>
      assert (ACCM : acc asegs mm (fr + 64) 2000)
        by (change 2000 with (8 * Z.of_nat 250); apply acc_zero_run; [Z.div_mod_to_equations; lia| lia|];
            replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact H) end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    Time walk_to AF MST [(usp - 160, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x4dc44].
    split_before FR (C8 a1) FRva.
    split_last_CB FRM [24; 2000; 2024]%nat.
    split_at FRM 6%nat FRmsg.
    split_at FRmsg 1%nat FRtail.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (gp_vsnprintf RT GP) as VS; unfold vsnprintf_lept_icontract in VS; eapply VS with (kinds := kinds) (D := fr + 64) (ap := usp + -56) (fmt := fmt) (lo := lo);
      rt_side ltac:(idtac).
      all: lazymatch goal with
           | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] => exact FRva
           | |- rw_cells _ _ _ [CB _ _] => exact FRmsg
           | |- lept_args _ ?S ?mm _ _ _ _ _ =>
               lazymatch goal with A : ART RT S mm |- _ =>
                 apply (lept_args_of_lit RT AF GP S mm _ _ _ _ _ A); try assumption;
                 [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                 | pose proof (af_frames_align RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as [_ X]; unfold SEGTOP_A in *; lia ] end
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; split; [intros _; split; [exact ACCM| right; left; exists fr, 6%nat; split; [solve [frames_in_tac]| change (fs_size 6) with 4096; lia]]|];
               split; [intros i Hi; rewrite unsigned_lit by lia; fframe_tac| exact (proj2 FRmsg)]
           | |- (SEGTOP_A <= _) =>
               lazymatch goal with A : ART RT ?S ?mm |- _ => pose proof (af_frames_align RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as [_ X] end; unfold SEGTOP_A in *; lia
           | |- (_ \/ _) => left; repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    Time walk_to AF MST [(usp - 160, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x61130].
    merge3 0x8da14 (Z_to_bv 5 1) (Z_to_bv 5 10) (Z_to_bv 5 11).
    { brfork BZ; awalk [0x8da14]; merge_done. }
    awalk [0x61130].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    (eapply cps_seq; [pose proof (rc_set_shadow RT RC 248) as SS; unfold set_shadow_contract in SS; eapply SS with (lo := lo); rt_side idtac |]).
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | Z.div_mod_to_equations; lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    walk_to AF MST [(usp - 160, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x48ea0].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    (eapply cps_seq; [pose proof (gp_stack_free_6 RT GP) as SF6; unfold stack_free_contract in SF6; eapply SF6 with (lo := lo) (f := fr) (fr := rt_frames RT Σ); rt_side idtac |]).
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    walk_to AF MST [(usp - 160, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -160) |- _ => release_frame FR ST' (usp + -56) end.
    lazymatch goal with ST' : stk asegs _ lo (usp + -56) |- _ => release_frame FRva ST' usp end.
    cps_stop.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
      lazymatch goal with A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
        assert (ARTf : ART RT S mf)
          by (apply (art_client_writes RT AF S mm mf (usp + -160) W A MUx WMx);
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
              | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
      end end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    split.
    + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [exact ARTf| split; [assumption| split; [| assumption]]]|].
      * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
      * split; [intros a Ha; exact (AGF a Ha)| split; assumption].
    + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. auto.
  - carve_frame 176%nat ST.
    Time walk_to AF MST [(usp - 176, usp)] [0x48d04].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_6 RT GP) as SM6; unfold stack_malloc_contract' in SM6; eapply SM6 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [auto| auto| lia]).
    lazymatch goal with H : rt_frames RT ?S = (?f, 6%nat) :: _ |- _ => rename H into FRS; set (fr := f) in * end.
    change (fs_size 6) with 4096 in *. change (4096 / 8) with 512 in *. change (4096 - 8) with 4088 in *.
    lazymatch goal with H : wr_at asegs ?mm fr 4088 |- _ => destruct (wr_at_rw_CB mm fr 4088 H ltac:(lia)) as (jf & FRM); clear H end.
    lazymatch goal with H : wr_at asegs ?mm (shad fr) 512 |- _ => destruct (wr_at_rw_CB mm (shad fr) 512 H ltac:(lia)) as (js & FSH); clear H end.
    change (Z.to_nat 4088) with 4088%nat in FRM. change (Z.to_nat 512) with 512%nat in FSH.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      pose proof (af_frames_range RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _);
      pose proof (af_frames_align RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG);
      pose proof (af_frames_hi RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as FRSH end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (NFA : forall a, PF a -> (a < fr \/ fr + 4096 <= a) /\ (a < shad fr \/ shad (fr + 4096) <= a))
        by (intros a Ha; apply (new_frame_apart RT AF S mm fr 6 (rt_frames RT Σ) (rt_live RT Σ) usp a A FRS);
            [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia
            | exact Ha ]) end.
    change (fs_size 6) with 4096 in *.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    Time walk_to AF MST [(usp - 176, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x61130].
    (* [comment removed for export] *)
    lazymatch type of FSH with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: [CB 504 ?j]) =>
      apply (rw_cells_split_CB asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7] 504 j [] [250; 254]%nat) in FSH; [| reflexivity];
      cbn [mk_CB_cells app] in FSH;
      split_cells FSH [c0; c1; c2; c3; c4; c5; c6; c7] FSHb end.
    lazymatch type of FSHb with rw_cells _ _ _ (?c :: _) => split_cells FSHb [c] FSHc end.
    pose proof (proj2 FSHb) as WRb. cbn [cells_size csize Nat.add] in WRb. change (Z.of_nat 250) with 250 in WRb.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (rc_set_shadow RT RC 248) as SS; unfold set_shadow_contract in SS; eapply SS with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | Z.div_mod_to_equations; lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    Time walk_to AF MST [(usp - 176, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x61010].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (rc_set_shadow RT RC 0) as SS0; unfold set_shadow_contract in SS0; eapply SS0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | Z.div_mod_to_equations; lia]).
    lazymatch goal with H : bytes_at asegs ?mm (fr / 8 + 2147450888) (repeat _ _) |- _ =>
      assert (ACCM : acc asegs mm (fr + 64) 2000)
        by (change 2000 with (8 * Z.of_nat 250); apply acc_zero_run; [Z.div_mod_to_equations; lia| lia|];
            replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact H) end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    Time walk_to AF MST [(usp - 176, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x4dc44].
    split_before FR (C8 a1) FRva.
    split_last_CB FRM [24; 2000; 2024]%nat.
    split_at FRM 6%nat FRmsg.
    split_at FRmsg 1%nat FRtail.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (gp_vsnprintf RT GP) as VS; unfold vsnprintf_lept_icontract in VS; eapply VS with (kinds := kinds) (D := fr + 64) (ap := usp + -56) (fmt := fmt) (lo := lo);
      rt_side ltac:(idtac).
      all: lazymatch goal with
           | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] => exact FRva
           | |- rw_cells _ _ _ [CB _ _] => exact FRmsg
           | |- lept_args _ ?S ?mm _ _ _ _ _ =>
               lazymatch goal with A : ART RT S mm |- _ =>
                 apply (lept_args_of_lit RT AF GP S mm _ _ _ _ _ A); try assumption;
                 [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
                 | pose proof (af_frames_align RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as [_ X]; unfold SEGTOP_A in *; lia ] end
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; split; [intros _; split; [exact ACCM| right; left; exists fr, 6%nat; split; [solve [frames_in_tac]| change (fs_size 6) with 4096; lia]]|];
               split; [intros i Hi; rewrite unsigned_lit by lia; fframe_tac| exact (proj2 FRmsg)]
           | |- (SEGTOP_A <= _) =>
               lazymatch goal with A : ART RT ?S ?mm |- _ => pose proof (af_frames_align RT AF S mm fr 6 A ltac:(rewrite FRS; left; reflexivity)) as [_ X] end; unfold SEGTOP_A in *; lia
           | |- (_ \/ _) => left; repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    Time walk_to AF MST [(usp - 176, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x61130].
    merge3 0x8da14 (Z_to_bv 5 1) (Z_to_bv 5 10) (Z_to_bv 5 11).
    { brfork BZ; awalk [0x8da14]; merge_done. }
    awalk [0x61130].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    (eapply cps_seq; [pose proof (rc_set_shadow RT RC 248) as SS; unfold set_shadow_contract in SS; eapply SS with (lo := lo); rt_side idtac |]).
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                  | Z.div_mod_to_equations; lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    walk_to AF MST [(usp - 176, usp); (fr, fr + 4088); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 512)] [0x48ea0].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    (eapply cps_seq; [pose proof (gp_stack_free_6 RT GP) as SF6; unfold stack_free_contract in SF6; eapply SF6 with (lo := lo) (f := fr) (fr := rt_frames RT Σ); rt_side idtac |]).
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    walk_to AF MST [(usp - 176, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' (usp + -56) end.
    lazymatch goal with ST' : stk asegs _ lo (usp + -56) |- _ => release_frame FRva ST' usp end.
    cps_stop.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mf _))) _ =>
      lazymatch goal with A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
        assert (ARTf : ART RT S mf)
          by (apply (art_client_writes RT AF S mm mf (usp + -176) W A MUx WMx);
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
              | cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I] ]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
      end end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    split.
    + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [exact ARTf| split; [assumption| split; [| assumption]]]|].
      * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
      * split; [intros a Ha; exact (AGF a Ha)| split; assumption].
    + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. auto.
Qed.
End STDERR.
