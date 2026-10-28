(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_iface Sj_num_akit
  Sj_stage2_defs Sj_stage2_main Sj_stage2_world Sj_stage2_numo_defs Sj_stage2_numo Sj_stage2_numw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem numo_world : forall RT, art_facts RT -> slowfa_cps RT -> pffa_cps RT -> numo_stmt RT.
Proof.
  intros RT AF HSL HPF PMc FDO MST E0 OK0 K good GSHZ GMONO GKX GNUM GSTEP w s tws sbs HG HV GLT KC.
  destruct HV as (HK & HW & HSB0 & HSB & (HD1 & HD2) & HSC).
  pose proof (env_ok_ghost _ tws sbs (env_at_ok E0 (wm RT w) OK0)) as OK. pose proof (GSHZ w _ HG) as SHZ.
  assert (KX : exit_k (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w) tws sbs) (wQ RT PMc K w)) by exact (GKX w _ tws sbs HG).
  assert (KX2 : forall v r, exit_k (gapp (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w) tws sbs) [v; r] []) (wQ RT PMc K w)) by (intros v r; exact (GKX w _ (tws ++ [v; r]) (sbs ++ []) HG)).
  pose proof (ok_tcap _ OK0) as [HTC _]. pose proof (n_le_len _ _ (ok_s1 _ OK0)) as HNL.
  pose proof (off_bound E0 OK0 (k s) HK) as HOFF.
  assert (HWT : W s + 2 <= e_tcap E0) by lia.

  assert (AFTER : forall w', good w' (k s + 1) -> is_numstart (e_tok E0 (k s)) = true ->
            (forall r v, (r = 9 \/ r = 0) -> numo_slowret_k (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w') tws sbs) (wQ RT PMc K w') s r v) /\
            (forall r v, (r = 0 \/ r = 1) -> numo_fbret_k (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w') tws sbs) (wQ RT PMc K w') s r v)).
  { intros w' HG' HNUM.
    pose proof (env_ok_ghost _ tws sbs (env_at_ok E0 (wm RT w') OK0)) as OK'. pose proof (GSHZ w' _ HG') as SHZ'.
    assert (KX' : exit_k (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w') tws sbs) (wQ RT PMc K w')) by exact (GKX w' _ tws sbs HG').
    assert (KX2' : forall v r, exit_k (gapp (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w') tws sbs) [v; r] []) (wQ RT PMc K w')) by (intros v r; exact (GKX w' _ (tws ++ [v; r]) (sbs ++ []) HG')).
    assert (KC' : forall v r, num_word v -> objcont_k (gapp (s2_ghost (Sj_stage2_main.wE E0 (WD RT) (wm RT) w') tws sbs) [v; r] []) (wQ RT PMc K w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)))
      by (intros v r Hv; exact (KC HNUM w' v r HG' Hv)).
    split; intros r v HR.
    - exact (seg_numo_after_slow _ OK' SHZ' _ s r v HR ltac:(lia) HWT GLT KX' KX2' KC').
    - exact (seg_numo_after_fb _ OK' SHZ' _ s r v HR ltac:(lia) HWT GLT KX' KX2' KC'). }
  apply (seg_numo _ OK SHZ _ s HK ltac:(lia) HWT GLT KX KX2).
  - intros v r Hv HNUM. apply (KC HNUM w v r); [apply (GMONO w (k s)); [exact HG | lia] | exact Hv].
  -
    intros HNUM. unfold numo_slowcall_k. intros until m1. intros HM. apply evt_done.
    refine (numw_call RT AF PMc FDO MST E0 OK0 K good GNUM GSTEP 0xee4c8 9 0 0xc4044 HSL ltac:(lia) eq_refl w (k s) (e_off E0 (k s)) HG HK HOFF
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _); [repeat constructor |].
    intros w' flag v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG' HM'.
    apply (aevt_evt RT AF PMc MST).
    destruct (AFTER w' HG' HNUM) as [AS _].
    pose proof (AS (if flag then 9 else 0) v ltac:(destruct flag; [left | right]; reflexivity)) as AS'.
    unfold numo_slowret_k in AS'. eapply AS'. exact HM'.
  -
    intros HNUM. unfold numo_fbcall_k. intros until m1. intros HM. apply evt_done.
    refine (numw_call RT AF PMc FDO MST E0 OK0 K good GNUM GSTEP 0xee5cc 0 1 0xc4390 HPF ltac:(lia) eq_refl w (k s) (e_off E0 (k s)) HG HK HOFF
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM _); [repeat constructor |].
    intros w' flag v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG' HM'.
    apply (aevt_evt RT AF PMc MST).
    destruct (AFTER w' HG' HNUM) as [_ AS].
    pose proof (AS (if flag then 0 else 1) v ltac:(destruct flag; [left | right]; reflexivity)) as AS'.
    unfold numo_fbret_k in AS'. eapply AS'. exact HM'.
Qed.
