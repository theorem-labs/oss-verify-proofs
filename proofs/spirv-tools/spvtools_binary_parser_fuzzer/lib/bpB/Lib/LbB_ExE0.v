(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BStep BCells.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit LbB_ExT LbB_ExR1.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition EX_RT2 : list (reg * expr) :=
  [(1%bv, ELit 0xf8c78); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (10%bv, EVar 52);
   (18%bv, EVar 40); (19%bv, EVar 41); (20%bv, EVar 35); (21%bv, EVar 43); (22%bv, EVar 37); (23%bv, EVar 32); (24%bv, EVar 36);
   (25%bv, EVar 47); (26%bv, ELit 2147450880); (27%bv, EVar 49)].

Section E0.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma ex_e0 : forall (e : xent H) (Q : machine_state -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    xpre H e ->
    a0 = Z_to_bv 64 (x_this e) -> a1 = Z_to_bv 64 (x_ioff e) -> a2 = Z_to_bv 64 (x_opc e) -> a3 = Z_to_bv 64 (x_ty e) ->
    (forall ff fp R2 m2, fresh_frame H (x_LF e) 3 ff fp -> rfull R2 ->
       rtbl (Wx H e ff fp 0 0 0 0) R2 EX_RT2 -> Px H e ff fp [] (x_s e) (x_LB e) m2 -> mem_inv asegs m2 ->
       SHAD m2 ff (poison_bytes 64 0) ->
       evt asegs Q (MS R2 (x_F e) (Z_to_bv 64 EX_SM_RA) (x_fc e) None m2 (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR (x_ra e) (x_sp e) (x_gp e) (x_tp e) t0 t1 t2 (x_s0 e) (x_s1 e) a0 a1 a2 a3 a4 a5 a6 a7
               (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e) (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) t3 t4 t5 t6)
          (x_F e) (Z_to_bv 64 AEXHAUSTED) (x_fc e) None (x_m e) (seg_rom asegs)).
  Proof.
    intros e Q t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP Ha0 Ha1 Ha2 Ha3 K.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (xpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (xpre_RH0 H e HP) as RH0.
    pose proof HP as (FZ & _ & _ & _ & _ & RA & _ & _ & _ & ST & _ & _ & (errv & ER) & MI & _ & RAE & LV & AC
                      & RF & LFL & S0 & _ & _ & _ & _ & _ & _ & IOR & OPR & TYR & THO & _).
    destruct THO as (_ & _ & _ & TH0 & TH1 & _).
    pose proof aceil_facts as ACF.
    set (SP := xSP e) in *. set (S1 := xS1 e) in *. set (lo := x_lo e) in *.

    eapply evt_cut.
    { eapply (x1 (x_ra e) (x_sp e) (x_gp e) (x_tp e) t0 t1 t2 (x_s0 e) (x_s1 e) a0 a1 a2 a3 a4 a5 a6 a7 (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e)
                  (x_s6 e) (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) t3 t4 t5 t6 (x_F e) (x_fc e) (x_m e)
                  (x_this e) (x_ioff e) (x_opc e) (x_ty e) lo);
        try change (bv_unsigned (x_sp e)) with SP; try assumption; try lia. }
    intros ms1 P1. destruct P1 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & SV1).
    subst ms1. change (bv_unsigned (x_sp e)) with SP in *. change (SP - 128 - SP mod 32) with S1 in *.

    assert (X1 : aceil <= S1) by lia.
    assert (X2 : as_FSB H + AFS_SIZE <= aceil) by (pose proof (ah_RFS_range H HB _ _ RF) as [(_ & X & _) _]; exact X).
    pose proof (stack_window_ok H (x_LB e) (x_LF e) S1 SP X1 X2) as (W1a & W1b & W1c). clear X1 X2.
    assert (RF1 : as_RFS H (x_LF e) m1) by (eapply (ah_RFS_frame H HB); [exact RF | exact MU1 | exact WM1 | apply Forall_cons; [exact W1b | apply Forall_nil]]).
    assert (RH1 : as_RHEAP H (x_s e) (x_LB e) m1) by (eapply (ah_RHEAP_frame H HB); [exact RH0 | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact W1c | apply Forall_nil]]).

    eapply evt_cut.
    { pose proof (rt_bp_ext H HH) as (_ & _ & SM3 & _). unfold stack_malloc_stmt_bp in SM3. cbn [Z.eqb Pos.eqb] in SM3.
      eapply (SM3 _ (Z_to_bv 64 S1)) with (LF := x_LF e) (lo := lo);
        [exact RF1 | unfold EX_FRAMES, DS_FRAMES, AFS_MAXLIVE_BP, AFS_MAXLIVE in *; lia | rewrite HLib.u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
        | exact CE | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact TP | exact AC1 | exact (ah_thr H HB _ _ _ RH1)]. }
    intros ms2 P2.
    destruct P2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & k1 & k2
                    & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & CF2 & SF2 & FP2 & AC2).
    subst ms2. rewrite HLib.u64_of_Z in MU2, ST2 by lia. unfold AFS_STACK in MU2.
    rewrite (ret_pc_even EX_SM_RA ltac:(unfold EX_SM_RA; lia) eq_refl).
    pose proof (fresh_of_RFS H HB (x_LF e) 3 ff fp m2 RF2) as FFR.
    pose proof (xframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    change (fsz 3) with 512 in *. change (fshn 3) with 64 in *. change (Z.to_nat (512 - 40)) with 472%nat in CF2.
    assert (WFF : wr_at asegs m2 ff 512) by (eapply rw_cells_wr_at; [exact CF2 | cbn; lia]).
    assert (SF0 : rw_cells asegs m2 (ff + 504) [C8 (Z_to_bv 64 fp)]).
    { apply (rw_cells_app asegs m2 ff [CB 24 k1; C8 (Z_to_bv 64 S1); CB 472 k2] [C8 (Z_to_bv 64 fp)]) in CF2 as [_ CFb].
      cbn [cells_size csize] in CFb. change (Z.of_nat (24 + (8 + (472 + 0)))) with 504 in CFb. exact CFb. }
    assert (FAPP : ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
      by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in F10; destruct F10 as [[X Y]|[X Y]]; [left | right]; lia).
    assert (FSH : sh ff + 64 <= ff \/ ff + 512 <= sh ff).
    { destruct FAPP as [X|X].
      - right. assert (0x7fff8000 <= sh ff) by lia. lia.
      - left. unfold sh in *. rewrite ASHADOW_BASE_val in *. clear - X. Z.div_mod_to_equations. lia. }

    assert (ST2f : stk asegs m2 lo SP).
    { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 S1 SP)
        by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; lia]).
      exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
    assert (HI2 : xinv H e ff fp [] (x_s e) (x_LB e) m2).
    { assert (WL2 : Forall (fun iv => aclient_write_ok H (x_LB e) iv /\ stack0_ok iv) [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 512); (sh ff, sh ff + 64)]).
      { repeat apply Forall_cons; try apply Forall_nil; (split; [unfold aclient_write_ok; cbn [fst snd] | ]).
        - left. lia.
        - apply stack0_ok_app. unfold AHI_LO. lia.
        - right; right; right; right; left. unfold AFS_FLAGS, AFS_SIZE. lia.
        - eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | unfold AFS_FLAGS, AFS_SIZE; lia].
        - right; right; right; right; left. unfold AFS_SIZE in *. lia.
        - eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | unfold AFS_SIZE in *; lia].
        - right; right; right; right; left. lia.
        - eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia].
        - right; right; right; right; right; left. lia.
        - right. cbn. assert (sh (ff + 512) <= sh aceil) by (apply sh_mono; lia). lia. }
      apply Forall_and_inv in WL2 as [WL2a WL2b].
      unfold xinv, EX_SAVED, EX_FLAGP. rewrite (xerrno_ATP H e TP) in ER |- *.
      split; [exact RF2|]. split; [exact FFR|].
      split; [eapply (ah_RHEAP_frame H HB); [exact RH1 | exact MU2 | exact WM2 | exact WL2a]|].
      split; [exact AC2|]. split; [exact MI2|].
      split.
      { eapply stack0_transport; [| exact MU2 | exact WM2 | exact WL2b].
        eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia | apply Forall_nil]]. }
      split.
      { eapply (ah_rauxv_frame H HB); [| exact MU2 | exact WM2 | exact WL2a].
        eapply (ah_rauxv_frame H HB); [exact RA | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]. }
      split.
      { exists errv. eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold ATP, AFS_FLAGS; lia].
        eapply rw_cells_transport; [exact ER | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
      split; [exact ST2f|].
      split; [eapply rw_cells_transport; [exact SV1 | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; lia]|].
      split; [exact SF0|].
      split; [destruct WFF as (W0 & W1 & W); split; [lia|]; split; [lia|]; intros i Hi; apply W; lia|].
      split; [exact (proj2 FP2)|].
      split; [| split; [apply Forall_nil|]].
      2: {
        eapply LbB_TdKit.LINV_P5_munch_hi; [exact LV | exact (munch_app _ _ _ _ _ MU1 MU2) |].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP, AFS_FLAGS in *; lia. }
      rewrite app_nil_r.
      eapply (xpres_of_munch H (x_s e) (x_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp) ([(S1, SP)] ++ [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 512); (sh ff, sh ff + 64)]) (x_m e));
        [exact HB | exact RH0 | exact (munch_app _ _ _ _ _ MU1 MU2) | exact (wmono_trans asegs _ _ _ WM1 WM2) |].
      unfold XE. change (fsz 3) with 512. change (fshn 3) with 64.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - left. lia.
      - right. intros a Ha. cbn. right; left. lia.
      - right. intros a Ha. cbn. right; right; left. lia.
      - right. intros a Ha. cbn. right; right; right; left. lia.
      - right. intros a Ha. cbn. right; right; right; right; left. lia. }

    eapply (K ff fp _ m2 FFR (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)); [| exact HI2 | exact MI2 | exact SF2].
    unfold rtbl, EX_RT2.
    assert (ES : Z_to_bv 64 SP = x_sp e) by (apply Z_to_bv_bv_unsigned).
    repeat (apply Forall_cons; [cbn [fst snd]; first [reflexivity | exact ES] |]). apply Forall_nil.
  Qed.
End E0.
