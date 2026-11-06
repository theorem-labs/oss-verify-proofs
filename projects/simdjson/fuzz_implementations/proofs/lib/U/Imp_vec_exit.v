(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv MonadX Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Imp_ios_defs Exit_iface F_stdio_exit0 Imp_exit Imp_exit_top.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Exit Pj_loc_defs Stdio_iface F_stdio_exit Drv_kit Drv_facts.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).

Section VecExit.
  Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Hypothesis FREE : rfree_stmt.

  Lemma xagree_of_rheap_pres : forall LB sp m m', rheap_pres LB sp m m' -> xagree sp m m'.
  Proof.
    intros LB sp m m' RP a Ha Ho. apply (RP a Ha). unfold XW, RTPLOC, AEX_VEC_OBJ in Ho. cbn [outside fst snd] in Ho.
    unfold rclient_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP.
    destruct (Z.le_gt_cases sp a) as [H|H]; [left; exact H|]. right; left. lia.
  Qed.

  Lemma xcommon_agree_core : forall (P : Z -> Prop) m m' s s',
    agree_on' P m m' ->
    (forall a, RINCB <= a < RINCB + 1 -> P a) -> (forall a, ROFL <= a < ROFL + 16 -> P a) -> (forall a, 0xe3130 <= a < 0xe3138 -> P a) ->
    (forall a, RSTDIN <= a < RSTDIN + 148 -> P a) -> (forall a, 0xe3220 <= a < 0xe3228 -> P a) -> (forall a, 0xe3040 <= a < 0xe3048 -> P a) ->
    (forall a, RSTDOUT <= a < RSTDOUT + 232 -> P a) -> (forall a, RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024 -> P a) -> (forall a, RSTDERR <= a < RSTDERR + 232 -> P a) ->
    (forall a, PJ_LOC_LO <= a < PJ_LOC_HI -> P a) -> (forall a, IOS <= a < 0xf4c38 -> P a) -> (forall a, RTPLOC <= a < RTPLOC + 8 -> P a) ->
    (forall a, iosx_img_addr a -> P a) ->
    ps_so s' = ps_so s -> xcommon m s ->
    (exists (cdt thr sec : byte) (tm1 : word), rw_cells usegs m' 0x1157d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]) ->
    (exists g, ssp_cells m' g) -> xcommon m' s'.
  Proof.
    intros P m m' s s' AG H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 SO XC LCH' SSP'.
    destruct XC as (_ & INCB & OFL & SIU & SINF & SOU & SEU & SOF & SEF & _ & LB0 & IIO & TPL & IMGF).
    unfold xcommon. rewrite SO. unfold RINCB, ROFL, RTPLOC, RSTDIN, IOS in *.
    Ltac cellP AG Hk H := eapply (rw_cells_agree' _ _ _ _ _ AG); [exact H| intros a Ha; apply Hk; cbn in Ha; lia].
    split; [exact LCH'|].
    split; [cellP AG H1 INCB|]. split; [cellP AG H2 OFL|]. split; [cellP AG H3 SIU|].
    split; [eapply stdin_file0_agree; [exact AG| intros a Ha; apply H4; unfold stdin_addr, RSTDIN in Ha; lia| exact SINF]|].
    split; [cellP AG H5 SOU|]. split; [cellP AG H6 SEU|].
    split; [eapply stdout_file_agree; [exact AG| intros a [Ha|Ha]; [apply H7| apply H8]; exact Ha| exact SOF]|].
    split; [eapply stderr_wfile0_agreeX; [exact AG| intros a Ha; apply H9; exact Ha| exact SEF]|].
    split; [exact SSP'|].
    split; [eapply LOCB_agree; [exact AG| exact H10| exact LB0]|].
    split; [eapply imp_ios_agree; [exact AG| intros a Ha; apply H11; pose proof (imp_ios_addr_bounds a Ha); unfold IOS in *; lia| exact IIO]|].
    split; [cellP AG H12 TPL|].
    eapply iosx_img_facts_agree; [exact AG| exact H13| exact IMGF].
  Qed.
  Ltac xstat_side := unfold iosx_img_addr, RINCB, ROFL, RTPLOC, RSTDIN, IOS; cbn [outside fst snd]; intros a Ha.

  Theorem vec_exit_proof : vec_exit_stmt.
  Proof.
    intros lo hi p CLO GLO sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s ST LO HHI TPE XP MI.
    pose proof XP as (XC & LB & HP & (B & AUX & HB) & (errv & ERR) & (A & IN & VEC & HA)).
    pose proof XC as ((cdt & thr & sec & tm1 & LCH) & _ & _ & _ & _ & _ & _ & _ & _ & (g & [SSP1 SSP2]) & _).
    unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold HDX, X_VECDTOR, AEX_VEC_OBJ, AEX_HRA, GLOBALS_TOP in *.
    pose proof (RHEAP_block_range_proof _ _ _ _ HP IN) as BR. unfold rblock_range in BR. cbn [blk_addr blk_size fst snd] in BR. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0xf32e0, 0xf32e8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 16%nat ST.
    lstep. lstep. lstep.
    lstep. lstep.
    lstep.
    lstep. if_lit.
    lstep. lstep. if_lit.
    lstep.
    lstep. if_cases K; [exfalso; unfold bv_eqb in K; rewrite !unsigned_lit in K by lia; apply Z.eqb_eq in K; lia|]. clear K.
    lstep.
    lstep. if_cases K; [exfalso; unfold bv_eqb in K; rewrite !unsigned_lit in K by lia; apply Z.eqb_eq in K; lia|]. clear K.
    lstep.
    lstep. if_cases K; zify_cond K. 1:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    lstep.
    lstep. if_cases K; zify_cond K. 1:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    lstep. lstep.
    astep.
    astep. astep. astep.
    apply evt_done.

    lazymatch type of MU with munch ?W ?m0 ?mb =>
      assert (XC1 : xcommon mb s) by (eapply (xcommon_agree_core _ m0 mb s s (agree_on'_of_munch W m0 mb MU WM));
        first [ reflexivity | exact XC | exists cdt, thr, sec, tm1; assumption | exists g; split; assumption | xstat_side; split; [lia| split; [lia| exact I]] ]) end.
    lazymatch type of MU with munch ?W ?ma ?mb =>
      assert (HP1 : RHEAP s LB mb) by (eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
        constructor; [left; cbn; lia|];
        constructor; [right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia| constructor]);
      assert (AUX1 : rauxv_ok mb B) by (eapply rauxv_ok_agree; [apply (agree_on_of_munch _ _ _ MU WM)| intros a Ha; cbn; split; [lia| split; [lia| exact I]]
                                                              | intros a Ha; unfold RMallocRep.RAUXV_CELL in Ha; cbn; split; [lia| split; [lia| exact I]]| exact AUX])
    end.

    name_sp sp (-16)%Z. replace (bv_unsigned sp + -16) with (bv_unsigned sp0) in ST by lia.
    eapply implM_post_evt'.
    { eapply FREE with (s := s) (LB := LB) (p := p) (A := A) (n := 8) (lo := lo) (B := B) (errv := errv);
        [ exact HP1 | exact IN | exact AUX1 | lia | exact ST | exact CLO | unfold RFREE_STACK; lia
        | rewrite TPE; unfold errno_addr; rewrite unsigned_lit by lia; exact ERR | assumption | exact TPE | reflexivity ]. }
    cbv beta. intros [] s' ms' PO.
    destruct PO as (x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & RP & FA & SO & HP2).
    rewrite (ret_pc_even _) by (cbn; lia).

    lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
      assert (FR2 : rw_cells usegs m2 fa fcs) by (eapply (rw_cells_agree' _ _ _ _ _ RP); [exact FR|]; intros a Ha; cbn in Ha; unfold rclient_addr; left; lia) end.
    clear FR. unname_sp.
    lstep.
    lstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    lstep.
    apply evt_done. unfold hpost.
    do 15 eexists. exists F, m2. split; [reflexivity|].
    split; [| split; [exact MI2| split; [exact ST2|]]].
    -
      eapply xagree_trans; [| apply (xagree_mono_sp (bv_unsigned sp + -16)); [exact (xagree_of_rheap_pres _ _ _ _ RP)| lia]].
      eapply xagree_of_munch; [exact MU| exact WM| unfold XW, AEX_VEC_OBJ; cbn [outside fst snd]; intros a Ha; lia].
    - eapply (xcommon_agree_core _ _ _ s s' RP);
        first [ exact SO | exact XC1 | exact (RHEAP_libc_head _ _ _ HP2) | exists rr_guard; exact (RHEAP_ssp _ _ _ HP2)
              | xstat_side; unfold rclient_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; right; left; lia ].
  Qed.
End VecExit.
