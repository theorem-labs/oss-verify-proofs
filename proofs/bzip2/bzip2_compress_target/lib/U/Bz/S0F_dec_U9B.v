(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import
     BzLemmasT BzLemmasT2 BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith BzWalkArith3 DecAuxR S0_dec_U13 S0_decCuts S0_decCutsM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCutsM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU9. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecTacF3 S0F_dec_U9A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U9A.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit BzWalkArith4 DecTacM.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section RC.
  Hypothesis HSYM : S0F_cut_SYM A F.

  (* [comment removed for export] *)
  Ltac head_loadsF SMALL MTA S0UR HIST :=
    let RD := fresh "RD" in let pp := fresh "pp" in let q := fresh "q" in let uc := fresh "uc" in
    let QR := fresh "QR" in let UR := fresh "UR" in let HU := fresh "HU" in let OB := fresh "OB" in
    wstepl; wstepl; wstepl; do 2 (lazymatch goal with |- context [bv_swrap 32 (Z.land ?e ?M + ?k)] => rewrite (BzWalkArith4.swrap32_land64_add e k) by lia end); wstepl; UKit.u_guard; wstepl; (* [comment removed for export] *)
    lazymatch goal with DRmtfb : u32arr _ ?mm (_ + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (zw32_read s0segs mm _ a 16 0 _ DRmtfb ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    wstepl; clear RD; (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a 0)] => set (pp := zget a 0) in * end;
    wstepl; wstepl; UKit.u_guard; (* [comment removed for export] *)
    wstepl; wstepl; wstepl; wstepl; UKit.u_guard; wstepl; (* [comment removed for export] *)
    pose proof (MTA pp ltac:(lia)) as QR;
    lazymatch goal with DRmtfa : u8arr _ ?mm (_ + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (zb8_read1 s0segs mm _ a 4096 pp _ DRmtfa ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    wstepl; clear RD; rewrite zxb_lit8 by lia; (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a pp)] => set (q := zget a pp) in * end;
    wstepl; wstepl; wstepl; wstepl; UKit.u_guard; wstepl; (* [comment removed for export] *)
    pose proof (S0UR q) as UR;
    lazymatch goal with DRs2u : u8arr _ ?mm (_ + 3468)%Z (zb8 ?a _) |- _ =>
      pose proof (zb8_read1 s0segs mm _ a 256 q _ DRs2u ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    wstepl; clear RD; rewrite zxb_lit8 by lia; (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a q)] => set (uc := zget a q) in * end;
    wstepl; wstepl; wstepl; wstepl; UKit.u_guard; wstepl; (* [comment removed for export] *)
    pose proof (HIST uc ltac:(lia)) as HU;
    lazymatch goal with DRunz : u32arr _ ?mm (_ + 68)%Z (zw32 ?a _) |- _ =>
      lazymatch type of HIST with hist_ok _ ?sy ?n => pose proof (occ_bounds sy n uc) as OB end; rewrite <- HU in OB;
      pose proof (zw32_read s0segs mm _ a 256 uc _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    wstepl; clear RD; wstepl; wstepl; wstepl; UKit.u_guard; (* [comment removed for export] *)
    wstepl; rewrite zxb_lit8 by lia; rewrite SMALL.

  Lemma S0F_U9_HRUNEND : S0F_cut_HRUNEND A F.
  Proof.
    unfold S0F_cut_HRUNEND. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    cps_destruct DI as (ML & NSR & ESR). cps_pose ML as (AL & GR & TB & MT & BL & CU).
    pose proof (alpha_ok_state L d AL) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (unfold alpha_ok in AL; tauto).
    assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (unfold grp_okF in GR; tauto).
    cps_pose BL as (NBR & SYMB & HIST). destruct MT as [MTI MTA].
    pose proof (mtf_inv_bounds _ MTI 0 ltac:(lia)) as PPR. unfold mtfb in PPR.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP. unfold drep in RP. cps_destruct RP as (_ & _ & _ & S0UR & _).
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. rewrite BN in NBM.
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL.
    destruct (act_small01 _ _ AOK) as [SM|SM]; rewrite SM in SMALL.
    - (* [comment removed for export] *)
      prepS DM MU DP SM. unfold r_of in DR. dr_open.
      hide_all_but_at [S; S + 68; S + 3468; S + 3724; S + 7820; usp + -336]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
      kq_intro. unfold K_HRUNEND in KQ. rewrite run_exit_K in KQ. unfold run_d1, run_uc in KQ.
      head_loadsF SMALL MTA S0UR HIST.
      destruct (Z.eq_dec (sv_es L) (-1)) as [Ees|NE].
      + (* [comment removed for export] *)
        rewrite Ees in *.
        (* [comment removed for export] *)
        replace (-1 + 1)%Z with 0%Z in KQ by lia.
        (* [comment removed for export] *)
        zw32_sw DRunz uc (zget (d_unzftab d) uc + 0)%Z ltac:(rewrite unsigned_lit by lia; f_equal; lia).
        wstepl; oktrap. (* [comment removed for export] *)
        wstepl; oktrap. (* [comment removed for export] *)
        wstepl. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). Lib.Step.mem_after_store. wstepl. (* [comment removed for export] *)
        rewrite (K_L9_exit F L) in KQ by lia.
        change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
        revive_all MUL WML AOK. fold_MU MU SM.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + 0)) DP) as DP'.
        kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'. apply (dinv_SYM_run0 L d uc ML); ulia.
      + assert (ES0 : (0 <= sv_es L)%Z) by lia.
        (* [comment removed for export] *)
        set (E := (sv_es L + 1)%Z) in *.
        (* [comment removed for export] *)
        zw32_sw DRunz uc (zget (d_unzftab d) uc + E)%Z ltac:(rewrite unsigned_lit by ulia; f_equal; ulia).
        wstepl; oktrap. (* [comment removed for export] *)
        wstepl; if_cases Kz; zify_cond_z Kz; [exfalso; ulia|]. (* [comment removed for export] *)
        pose proof FR as FR2; DecTacM.slot_split FR2 12%nat; wstepl; clear FR2. wstepl. (* [comment removed for export] *)
        wstepl; if_cases Kmx; zify_cond_z Kmx; [exfalso; ulia|]. (* [comment removed for export] *)
        wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
        revive_all MUL WML AOK. fold_MU MU SM.
        lazymatch type of KQ with kq _ (K_L9 ?F0 ?L0 ?d1 ?s0 ?u0 ?nb ?e) =>
          replace (K_L9 F0 L0 d1 s0 u0 nb e) with (K_L9 F0 L0 d1 s0 u0 (nb + 0) (e - 0))%Z in KQ by (f_equal; lia) end.
        pose proof (S0F_U9_L9F_all A AOK F HSYM L s J uc E 0 ltac:(ulia)) as NX. unfold L9FcF, L9cF in NX.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E)) DP) as DP'.
        kq_fold. enter_cutF NX DP'; [ apply (dinv_L9_entry L d uc E ML); ulia | exact SM ].
    - (* [comment removed for export] *)
      prepS DM MU DP SM. unfold r_of in DR. dr_open.
      hide_all_but_at [S; S + 68; S + 3468; S + 3724; S + 7820; usp + -336]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
      kq_intro. unfold K_HRUNEND in KQ. rewrite run_exit_K in KQ. unfold run_d1, run_uc in KQ.
      head_loadsF SMALL MTA S0UR HIST.
      destruct (Z.eq_dec (sv_es L) (-1)) as [Ees|NE].
      + rewrite Ees in *.
        replace (-1 + 1)%Z with 0%Z in KQ by lia.
        zw32_sw DRunz uc (zget (d_unzftab d) uc + 0)%Z ltac:(rewrite unsigned_lit by lia; f_equal; lia).
        wstepl; oktrap. (* [comment removed for export] *)
        wstepl; oktrap. (* [comment removed for export] *)
        wstepl. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). Lib.Step.mem_after_store. wstepl.
        rewrite (K_L9_exit F L) in KQ by lia.
        change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
        revive_all MUL WML AOK. fold_MU MU SM.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + 0)) DP) as DP'.
        kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'. apply (dinv_SYM_run0 L d uc ML); ulia.
      + assert (ES0 : (0 <= sv_es L)%Z) by lia.
        set (E := (sv_es L + 1)%Z) in *.
        zw32_sw DRunz uc (zget (d_unzftab d) uc + E)%Z ltac:(rewrite unsigned_lit by ulia; f_equal; ulia).
        wstepl; oktrap.
        wstepl; if_cases Kz; zify_cond_z Kz; [exfalso; ulia|].
        pose proof FR as FR2; DecTacM.slot_split FR2 12%nat; wstepl; clear FR2. wstepl.
        wstepl; if_cases Kmx; zify_cond_z Kmx; [exfalso; ulia|].
        wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
        revive_all MUL WML AOK. fold_MU MU SM.
        lazymatch type of KQ with kq _ (K_L9 ?F0 ?L0 ?d1 ?s0 ?u0 ?nb ?e) =>
          replace (K_L9 F0 L0 d1 s0 u0 nb e) with (K_L9 F0 L0 d1 s0 u0 (nb + 0) (e - 0))%Z in KQ by (f_equal; lia) end.
        pose proof (S0F_U9_L9S_all A AOK F HSYM L s J uc E 0 ltac:(ulia)) as NX. unfold L9ScF, L9cF in NX.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E)) DP) as DP'.
        kq_fold. enter_cutF NX DP'; [ apply (dinv_L9_entry L d uc E ML); ulia | exact SM ].
  Time Qed.
  End RC.
End R.

(* [comment removed for export] *)
Lemma S0F_dec_U9b : forall A, act_ok 320 A -> forall F, S0F_cut_SYM A F -> S0F_cut_HRUNEND A F.
Proof. intros A AOK F HS. exact (S0F_U9_HRUNEND A AOK F HS). Qed.

End ACeilS1.
