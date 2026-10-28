(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR1 LbB_WoR2 LbB_WoR3.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section E0.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.


  Definition wfc (e : went H) (ff : Z) (m : mem) : Prop :=
       rw_cells asegs m ff [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x2187b); C8 (Z_to_bv 64 0xea7c4)]
    /\ rw_cells asegs m (ff + 3360) [C4 (Z_to_bv 64 (w_env e))]
    /\ rw_cells asegs m (ff + 3408) [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m (ff + 3456) [C4 (Z_to_bv 64 (w_env e))]
    /\ rw_cells asegs m (ff + 3464) [C8 (Z_to_bv 64 (ff + 3376)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (b8 0)]
    /\ u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C)
    /\ rw_cells asegs m (wS1 e) [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)]
    /\ rw_cells asegs m (wS1 e + 16) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (w_words e)); C8 (Z_to_bv 64 (w_n e))]
    /\ rw_cells asegs m (wS1 e + 40) [C8 (Z_to_bv 64 0x7fff8000)]
    /\ rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 2224)); C8 (Z_to_bv 64 (ff + 3376))]
    /\ rw_cells asegs m (wS1 e + 80) [C8 (Z_to_bv 64 ff)].

  Definition wfc_apart (e : went H) (ff : Z) (iv : Z * Z) : Prop :=
    (snd iv <= ff \/ ff + 24 <= fst iv) /\ (snd iv <= ff + 3360 \/ ff + 3364 <= fst iv) /\ (snd iv <= ff + 3408 \/ ff + 3416 <= fst iv)
    /\ (snd iv <= ff + 3456 \/ ff + 3497 <= fst iv) /\ (snd iv <= sh ff \/ sh ff + 476 <= fst iv)
    /\ (snd iv <= wS1 e \/ wS1 e + 64 <= fst iv) /\ (snd iv <= wS1 e + 80 \/ wS1 e + 88 <= fst iv).

  Lemma wfc_munch : forall e ff m m' W, wfc e ff m -> munch W m m' -> wmono asegs m m' -> Forall (wfc_apart e ff) W ->
    wfc e ff m'.
  Proof.
    intros e ff m m' W (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) MU WM FW.
    assert (DJ : forall A n, (forall iv, In iv W -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from W A n).
    { intros A n K. clear - K. induction W as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    assert (FA : forall iv, In iv W -> wfc_apart e ff iv) by (intros iv Hiv; exact (proj1 (Forall_forall _ _) FW iv Hiv)).
    split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C2 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C3 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C4 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C5 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & K & _); cbn; lia]|].
    split; [eapply u8arr_transport; [exact C6 | exact MU | exact WM | rewrite length_map; cbn [length WO_SH2C app repeat];
              apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C7 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C8 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C9 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C10 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]|].
    eapply rw_cells_transport; [exact C11 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & _ & K); cbn; lia].
  Qed.

  Definition e0a_post (e : went H) : machine_state -> Prop :=
    fun ms' => exists (ff fp : Z) x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_MS1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 0) (Z_to_bv 64 46) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3552)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 2752))
                    x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AASAN_MEMSET) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp [] (w_s e) (w_LB e) m'
      /\ wfc e ff m'.

  Lemma e0a : forall (e : went H) (apo : bool) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    wpre H e -> (apo = false -> a7 = Z_to_bv 64 0) ->
    a0 = Z_to_bv 64 (w_ctx e) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (w_words e) -> a3 = Z_to_bv 64 (w_n e) ->
    a4 = Z_to_bv 64 0 -> a5 = Z_to_bv 64 0 -> a6 = Z_to_bv 64 0 ->
    evt asegs (e0a_post e)
      (MS (mkR (w_ra e) (w_sp e) (w_gp e) (w_tp e) t0 t1 t2 (w_s0 e) (w_s1 e) a0 a1 a2 a3 a4 a5 a6 a7
               (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e) (w_s6 e) (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e) t3 t4 t5 t6)
          (w_F e) (Z_to_bv 64 (if apo then APO_ENTRY else AWO_ENTRY)) (w_fc e) None (w_m e) (seg_rom asegs)).
  Proof.
    intros e apo t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HA7 Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_RH0 H e HP) as RH0.
    pose proof HP as (FZ & CTX & NR & WRD & _ & _ & _ & _ & RA & _ & _ & _ & ST & _ & _ & (errv & ER) & MI & _ & RAE & LV & AC
                      & RF & LFL & S0 & _ & _ & _ & _ & _).
    destruct CTX as (pc & j1 & j2 & INC & CC & CAD & ENV).
    pose proof aceil_facts as ACF.
    pose proof (ah_blocks H HB _ _ _ _ RH0 INC) as (CB0 & CB16 & CBn & CBI & CBC & CBF & CBAPP). cbn in CB0, CB16, CBn, CBI, CBC, CBF, CBAPP.
    set (SP := wSP e) in *. set (S1 := wS1 e) in *. set (lo := w_lo e) in *. set (ctx := w_ctx e) in *.
    assert (CTXB : 0 <= ctx < 2 ^ 64) by lia.
    assert (WB : 0 <= w_words e < 2 ^ 64).
    { destruct WRD as [(-> & _)|(pw & k & INw & KR & W0 & _ & WK & _)]; lia. }

    eapply evt_cut.
    { eapply (w1 apo (w_ra e) (w_sp e) (w_gp e) (w_tp e) t0 t1 t2 (w_s0 e) (w_s1 e) a0 a1 a2 a3 a4 a5 a6 a7 (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e)
                  (w_s6 e) (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e) t3 t4 t5 t6 (w_F e) (w_fc e) (w_m e) ctx (w_words e) (w_n e) lo);
        try change (bv_unsigned (w_sp e)) with SP; try assumption; try lia. }
    intros ms1 P1. destruct P1 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & SV1 & CS1).
    subst ms1. change (bv_unsigned (w_sp e)) with SP in *. change (SP - 192 - SP mod 32) with S1 in *.

    assert (X1 : aceil <= S1) by lia.
    assert (X2 : as_FSB H + AFS_SIZE <= aceil) by (pose proof (ah_RFS_range H HB _ _ RF) as [(_ & X & _) _]; exact X).
    pose proof (stack_window_ok H (w_LB e) (w_LF e) S1 SP X1 X2) as (W1a & W1b & W1c). clear X1 X2.
    assert (RF1 : as_RFS H (w_LF e) m1) by (eapply (ah_RFS_frame H HB); [exact RF | exact MU1 | exact WM1 | apply Forall_cons; [exact W1b | apply Forall_nil]]).
    assert (RH1 : as_RHEAP H (w_s e) (w_LB e) m1) by (eapply (ah_RHEAP_frame H HB); [exact RH0 | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact W1c | apply Forall_nil]]).

    pose proof (rt_bp_ext H HH) as (_ & _ & _ & _ & SM6 & _).
    eapply evt_cut.
    { eapply (SM6 _ (Z_to_bv 64 S1)) with (LF := w_LF e) (lo := lo);
        [exact RF1 | unfold PO_FRAMES, AFS_MAXLIVE_BP in *; lia | rewrite HLib.u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
        | exact CE | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact TP | exact AC1 | exact (ah_thr H HB _ _ _ RH1)]. }
    intros ms2 P2.
    destruct P2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & k1 & k2
                    & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & CF2 & SF2 & FP2 & AC2).
    subst ms2. rewrite HLib.u64_of_Z in MU2, ST2 by lia. unfold AFS_STACK in MU2.
    rewrite (ret_pc_even WO_SM_RA ltac:(unfold WO_SM_RA; lia) eq_refl).
    pose proof (fresh_of_RFS H HB (w_LF e) 6 ff fp m2 RF2) as FFR.
    pose proof (wframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    change (fsz 6) with 4096 in *. change (fshn 6) with 512 in *. change (Z.to_nat (4096 - 40)) with 4056%nat in CF2.
    assert (WFF : wr_at asegs m2 ff 4096) by (eapply rw_cells_wr_at; [exact CF2 | cbn; lia]).
    assert (SF0 : rw_cells asegs m2 (ff + 4088) [C8 (Z_to_bv 64 fp)]).
    { apply (rw_cells_app asegs m2 ff [CB 24 k1; C8 (Z_to_bv 64 S1); CB 4056 k2] [C8 (Z_to_bv 64 fp)]) in CF2 as [_ CFb].
      cbn [cells_size csize] in CFb. change (Z.of_nat (24 + (8 + (4056 + 0)))) with 4088 in CFb. exact CFb. }
    destruct SF2 as (_ & _ & USH).
    assert (FAPP : ff + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
      by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in F10; destruct F10 as [[X Y]|[X Y]]; [left | right]; lia).
    assert (FSH : sh ff + 512 <= ff \/ ff + 4096 <= sh ff).
    { destruct FAPP as [X|X].
      - right. assert (0x7fff8000 <= sh ff) by lia. lia.
      - left. unfold sh in *. rewrite ASHADOW_BASE_val in *. clear - X. Z.div_mod_to_equations. lia. }

    assert (ST2f : stk asegs m2 lo SP).
    { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 S1 SP)
        by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; lia]).
      exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
    assert (HI2 : winv H e ff fp [] (w_s e) (w_LB e) m2).
    { assert (WL2 : Forall (fun iv => aclient_write_ok H (w_LB e) iv /\ stack0_ok iv) [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 4096); (sh ff, sh ff + 512)]).
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
        - right. cbn. assert (sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia). lia. }
      apply Forall_and_inv in WL2 as [WL2a WL2b].
      unfold winv, WO_SAVED, WO_FLAGP. rewrite (werrno_ATP H e TP) in ER |- *.
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
        pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV0 & _).
        eapply LbB_TdKit.LINV_P5_munch_hi; [exact LV0 | exact (munch_app _ _ _ _ _ MU1 MU2) |].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP, AFS_FLAGS in *; lia. }
      rewrite app_nil_r.
      eapply (xpres_of_munch H (w_s e) (w_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XW H ff fp) ([(S1, SP)] ++ [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 4096); (sh ff, sh ff + 512)]) (w_m e));
        [exact HB | exact RH0 | exact (munch_app _ _ _ _ _ MU1 MU2) | exact (wmono_trans asegs _ _ _ WM1 WM2) |].
      unfold XW. change (fsz 6) with 4096. change (fshn 6) with 512.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - left. lia.
      - right. intros a Ha. cbn. right; left. lia.
      - right. intros a Ha. cbn. right; right; left. lia.
      - right. intros a Ha. cbn. right; right; right; left. lia.
      - right. intros a Ha. cbn. right; right; right; right; left. lia. }

    assert (RO2 : relro0 m2) by exact (proj1 (wlinv H HB e ff fp [] (w_s e) (w_LB e) m2 HP HI2)).
    assert (US2 : u8arr asegs m2 (sh ff) (map (Z_to_bv 8) (repeat 0 476))).
    { pose proof (u8arr_sub _ _ _ 0 476 USH ltac:(lia) ltac:(lia) ltac:(vm_compute; intros X; discriminate X)) as U.
      rewrite Z.add_0_r in U.
      lazymatch type of U with u8arr _ _ _ ?l => replace l with (map (Z_to_bv 8) (repeat 0 476)) in U by (vm_compute; reflexivity) end.
      exact U. }
    eapply evt_cut.
    { eapply (w2a (w_gp e) (w_tp e) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (w_s3 e) (w_s4 e) (w_s5 e) (w_s11 e) u3 u4 u5 u6
                  (w_F e) (w_fc e) m2 SP S1 ff ctx lo); try lia; try assumption.
      - destruct WFF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    intros ms3 P3. destruct P3 as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3
                                   & C803 & HD3 & SH3).
    subst ms3.
    assert (HI3 : winv H e ff fp [] (w_s e) (w_LB e) m3).
    { eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - right; left. lia.
      - right; right. lia. }

    assert (CC3 : rw_cells asegs m3 ctx [C4 (Z_to_bv 64 (w_env e)); CB 44 j1; C8 (Z_to_bv 64 0); CB 8 j2])
      by (eapply (wcells_keep H HB e ff fp [] (w_s e) (w_LB e) m3 pc ctx 64); [exact HP | exact HI3 | exact INC | lia | cbn; lia | exact CC]).
    assert (CA3 : addressable m3 ctx 64) by (eapply (waddr_keep H HB e ff fp [] (w_s e) (w_LB e) m3 pc ctx 64); [exact HP | exact HI3 | exact INC | exact CAD]).
    eapply evt_cut.
    { eapply (w2bc (w_gp e) (w_tp e) v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 (w_s11 e) v28 v29 v30 v31
                   (w_F e) (w_fc e) m3 SP S1 ff ctx (w_env e) lo j1 j2); try lia; try assumption.
      all: try (destruct CBF as [X|X]; [left | right]; unfold AFS_SIZE in *; lia).
      eapply (wr_at_wmono m2 m3); [| exact WM3]. destruct WFF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi. replace (ff + 3360 + i) with (ff + (3360 + i)) by lia. apply W. lia. }
    intros ms4 P4. destruct P4 as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & EQ4 & MU4 & WM4 & MI4 & ST4
                                   & CSP4 & CE4 & CF4 & SH4).
    subst ms4.
    assert (HI4 : winv H e ff fp [] (w_s e) (w_LB e) m4).
    { eapply (winv_munch H HB); [exact HP | exact HI3 | exact MU4 | exact WM4 | exact MI4 | exact ST4 |].
      unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - right; left. lia.
      - right; left. lia.
      - right; right. lia. }

    eapply evt_cut.
    { eapply (w2d (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) (w_gp e) (w_tp e) y5 y6 y7 (Z_to_bv 64 SP) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 ctx) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) y28 y29 y30 y31
                  (w_F e) (w_fc e) m4 SP S1 ff (w_env e) lo); try lia; try assumption.
      - eapply (wr_at_wmono m2 m4); [| exact (wmono_trans asegs _ _ _ WM3 WM4)]. destruct WFF as (W0 & W1 & W). split; [lia|]. split; [lia|].
        intros i Hi. replace (ff + 3456 + i) with (ff + (3456 + i)) by lia. apply W. lia. }
    intros ms5 P5. destruct P5 as (z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5
                                   & CP5 & CFD5 & CS5 & CB5).
    subst ms5. apply evt_done.
    assert (HI5 : winv H e ff fp [] (w_s e) (w_LB e) m5).
    { eapply (winv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 |].
      unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right; left. lia.
      - left. lia.
      - left. lia. }
    exists ff, fp, z5, z6, z7, z13, z14, z15, z16, z17, z28, z29, z30, z31, m5. split; [reflexivity|].
    split; [exact HI5|].
    assert (DJ : forall (W : list (Z * Z)) A n, (forall iv, In iv W -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from W A n).
    { intros W A n K. clear - K. induction W as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    split.
    { eapply rw_cells_transport; [| exact MU5 | exact WM5 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia].
      eapply rw_cells_transport; [exact HD3 | exact MU4 | exact WM4 | apply DJ; intros iv [<-|[<-|[<-|[<-|[]]]]]; cbn; lia]. }
    split; [eapply rw_cells_transport; [exact CE4 | exact MU5 | exact WM5 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact CF4 | exact MU5 | exact WM5 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia]|].
    split; [exact CP5|]. split; [exact CFD5|].
    split; [eapply u8arr_transport; [exact SH4 | exact MU5 | exact WM5 | rewrite length_map; cbn [length WO_SH2C app repeat];
              apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia]|].
    split; [exact CS5|].
    split.
    { eapply rw_cells_transport; [| exact MU5 | exact WM5 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia].
      eapply rw_cells_transport; [| exact MU4 | exact WM4 | apply DJ; intros iv [<-|[<-|[<-|[<-|[]]]]]; cbn; lia].
      eapply rw_cells_transport; [| exact MU3 | exact WM3 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia].
      eapply rw_cells_transport; [exact CS1 | exact MU2 | exact WM2 | apply DJ; intros iv [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; unfold AFS_FLAGS; lia]. }
    split; [exact CB5|].
    split; [eapply rw_cells_transport; [exact CSP4 | exact MU5 | exact WM5 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia]|].
    eapply rw_cells_transport; [| exact MU5 | exact WM5 | apply DJ; intros iv [<-|[<-|[<-|[]]]]; cbn; lia].
    eapply rw_cells_transport; [exact C803 | exact MU4 | exact WM4 | apply DJ; intros iv [<-|[<-|[<-|[<-|[]]]]]; cbn; lia].
  Qed.
End E0.
