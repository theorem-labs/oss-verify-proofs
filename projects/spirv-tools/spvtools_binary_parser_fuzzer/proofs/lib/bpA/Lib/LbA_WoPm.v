(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_SR LbA_Conv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_Own LbA_RtOwn LbA_DStat LbA_HKit LbA_HStKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit2 LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR5 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoF LbA_WoS1 LbA_WoS3.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoPm.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis PM : parse_module_stmtA H LINV_P5.
  Hypothesis WTR : po_tr_ok H.
  Let HB := rt_bp_base H HHb.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Definition wfc2 (e : went H) (ff : Z) (m : mem) : Prop :=
       rw_cells asegs m ff [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1e8b6); C8 (Z_to_bv 64 0xe9e9c)]
    /\ rw_cells asegs m (ff + 32) [C4 (Z_to_bv 64 (w_env e))]
    /\ rw_cells asegs m (ff + 80) [C8 (Z_to_bv 64 0)]
    /\ u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C)
    /\ rw_cells asegs m (wS1 e) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (w_words e)); C8 (Z_to_bv 64 (w_n e))]
    /\ rw_cells asegs m (wS1 e + 24) [C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 ff)]
    /\ rw_cells asegs m (wS1 e + 56) [C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 ff)].

  Definition wfc2_apart (e : went H) (ff : Z) (iv : Z * Z) : Prop :=
    (snd iv <= ff \/ ff + 24 <= fst iv) /\ (snd iv <= ff + 32 \/ ff + 36 <= fst iv) /\ (snd iv <= ff + 80 \/ ff + 88 <= fst iv)
    /\ (snd iv <= sh ff \/ sh ff + 64 <= fst iv)
    /\ (snd iv <= wS1 e \/ wS1 e + 48 <= fst iv) /\ (snd iv <= wS1 e + 56 \/ wS1 e + 72 <= fst iv).

  Lemma wfc2_of_wfc : forall e ff m, wfc H e ff m -> wfc2 e ff m.
  Proof. intros e ff m (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). repeat (split; [assumption|]). exact C9. Qed.

  Lemma wfc2_apart_of : forall e ff iv, wfc_apart H e ff iv -> wfc2_apart e ff iv.
  Proof. intros e ff iv (K1 & K2 & K3 & K4 & K5 & K6 & K7). unfold wfc2_apart. tauto. Qed.

  Lemma wfc2_munch : forall e ff m m' W, wfc2 e ff m -> munch W m m' -> wmono asegs m m' -> Forall (wfc2_apart e ff) W ->
    wfc2 e ff m'.
  Proof.
    intros e ff m m' W (C1 & C2 & C3 & C6 & C7 & C8 & C9) MU WM FW.
    assert (DJ : forall A n, (forall iv, In iv W -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from W A n).
    { intros A n K. clear - K. induction W as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    assert (FA : forall iv, In iv W -> wfc2_apart e ff iv) by (intros iv Hiv; exact (proj1 (Forall_forall _ _) FW iv Hiv)).
    split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C2 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C3 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & K & _); cbn; lia]|].
    split; [eapply u8arr_transport; [exact C6 | exact MU | exact WM | rewrite length_map; cbn [length WO_SH2C app repeat];
              apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C7 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & K & _); cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C8 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & K & _); cbn; lia]|].
    eapply rw_cells_transport; [exact C9 | exact MU | exact WM | apply DJ; intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K); cbn; lia].
  Qed.

  Lemma wfc2_apres : forall e ff fp XSc sk LBk LB m m', wpre H e -> winv H e ff fp XSc sk LBk m ->
    wfc2 e ff m -> apres H LB (wS1 e) m m' -> wfc2 e ff m'.
  Proof.
    intros e ff fp XSc sk LBk LB m m' HP HI (C1 & C2 & C3 & C6 & C7 & C8 & C9) AP.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & FF8 & FF9 & FF10 & FF11 & FF12 & FF13 & _).
    assert (CL : forall A k, ff <= A -> A + k <= ff + 512 -> aclient_range H LB (wS1 e) A k).
    { intros A k X1 X2. right; right; right; right; left. lia. }
    assert (CS : forall A k, wS1 e <= A -> aclient_range H LB (wS1 e) A k) by (intros A k X; left; exact X).
    split; [eapply (apres_rw_cells H); [exact AP | exact C1 | apply CL; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact C2 | apply CL; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact C3 | apply CL; cbn; lia]|].
    split; [eapply (apres_u8arr H); [exact AP | exact C6 | right; right; right; right; right; left; rewrite length_map; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact C7 | apply CS; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact C8 | apply CS; lia]|].
    eapply (apres_rw_cells H); [exact AP | exact C9 | apply CS; lia].
  Qed.

  Lemma wfc2_xpres : forall e ff fp LB X m m', wpre H e -> fresh_frame H (w_LF e) 3 ff fp ->
    wfc2 e ff m -> xpres H LB (wS1 e) X m m' -> Forall (wfc2_apart e ff) X -> wfc2 e ff m'.
  Proof.
    intros e ff fp LB X m m' HP FF (C1 & C2 & C3 & C6 & C7 & C8 & C9) XP FX.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    assert (FA : forall iv, In iv X -> wfc2_apart e ff iv) by (intros iv Hiv; exact (proj1 (Forall_forall _ _) FX iv Hiv)).
    assert (XC : forall A n, aclient_range H LB (wS1 e) A n -> (forall iv, In iv X -> A + n <= fst iv \/ snd iv <= A) ->
                   xclient_range H LB (wS1 e) X A n).
    { intros A n CR K. split; [exact CR|]. apply Forall_forall. exact K. }
    assert (FR : forall A n, ff <= A -> A + n <= ff + 512 -> aclient_range H LB (wS1 e) A n)
      by (intros A n K1 K2; right; right; right; right; left; lia).
    assert (SR : forall A n, wS1 e <= A -> aclient_range H LB (wS1 e) A n) by (intros A n K; left; exact K).
    split; [eapply xpres_rw_cells; [exact XP | exact C1 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C2 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C3 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_u8arr; [exact XP | exact C6 | rewrite length_map; cbn [length WO_SH2C app repeat];
              apply XC; [right; right; right; right; right; left; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C7 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C8 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & K & _); cbn; lia]]|].
    eapply xpres_rw_cells; [exact XP | exact C9 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K); cbn; lia]].
  Qed.

  Lemma wpm : forall (e : went H) ff fp XSc s LB (LBs : list block) (sc : stateC) m msF mo (Q : config -> Prop)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> wfc H e ff m ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 AWO_PM_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 (ff + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 APM_ENTRY) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_AL H s >= as_AL H (w_s e) ->
    state_repA LB m (ff + 176) sc -> state_sh m sc -> fresh_state sc (w_words e) (w_n e) ->
    Permutation LB (w_LB e ++ LBs) -> Permutation (lbl LBs) (state_blocks sc) ->
    (forall msF' mo' s' LB' LBs' m' XS (c' : parserC) (r : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
            (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 AWO_PM_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (Z_to_bv 64 AWO_PM_RA) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' -> wfc2 e ff m' ->
       xpres H (w_LB e) (wS1 e) ((RtA_Td.ATDLOC, RtA_Td.ATDLOC + 8) :: (ff + 128, ff + 128 + PARSER_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
       state_own LB' (w_LB e) LBs' (pc_state c') ->
       parser_repA LB' m' (ff + 128) c' -> parser_sh m' (ff + 128) c' -> pc_cons c' = ff + 48 ->
       st_words (pc_state c') = w_words e -> st_nwords (pc_state c') = w_n e ->
       lb_small LBs' + 2 ^ 12 <= po_small (w_n e) -> Z.of_nat (length LBs') + 8 <= po_cnt (w_n e) -> nlarge LBs' + 3 <= po_large (w_n e) ->
       st_vsteps (pc_state c') -> (forall q k, In (q, k) (state_blocks (pc_state c')) -> k <= 2 ^ 40) ->
       as_AL H s' >= as_AL H s - po_cost (w_n e) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB LBs sc m msF mo Q t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI WC VIS FZ KR AL0 R SH FR PLB PBL K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & ALe).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (winv_rf H _ _ _ _ _ _ _ HI) as RF.
    destruct (wchain_call H HB e ff fp XSc s LB m HP HI) as [CH CHU].
    destruct (wparser_mk H e ff fp XSc s LB m sc HP HI WC R) as (PR & PSH & FS1 & FS2 & C16 & WRC).
    pose proof FR as (EW & EN & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFL & _).
    eapply (ah_seq H HB).
    { eapply (PM (Z_to_bv 64 AWO_PM_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                (Z_to_bv 64 (ff + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc msF m mo s LB (w_LB e) LBs ((3, ff, fp) :: w_LF e) ((wSP e, bv_unsigned (w_ra e)) :: w_CH e)
                (ff + 128) (wparser ff sc) (w_lo e) (w_B e) (w_shi e) errv);
        cbn [pc_state pc_cons pc_user wparser]; rewrite ?EW; rewrite ?EN; rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - exact FZ.
      - reflexivity.
      - exact PR.
      - exact (PSH SH).
      - exact FS1.
      - exact FS2.
      - exact C16.
      - exact WRC.
      - exact FR.
      - exact HN.
      - exact (wwords_keep H HB e ff fp XSc s LB m HP HI).
      - split; [exact PLB | exact PBL].
      - apply (lb_own_incl LB); [| exact (HOWN _ _ _ RH)]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PLB|]. apply in_or_app. right. exact Hb.
      - exact RH.
      - exact KR.
      - exact BS.
      - exact BC.
      - exact BL.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold APM_STACK. lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - reflexivity.
      - exact (wlinv H HB e ff fp XSc s LB m HP HI).
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - exact RF.
      - cbn [length]. rewrite PO_PM_FRAMES in LFL. lia.
      - exact (winv_s0 H _ _ _ _ _ _ _ HI).
      - lia.
      - exact CH.
      - exact (wpm_pf H e HP).
      - exact CHU.
      - exact (proj1 WTR).
      - lia. }
    intros [msF' mo'] POST.
    destruct POST as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & s' & LB' & LBs' & c' & XS & F' & fc'
                      & VIS' & FZ' & KR' & MP' & MI' & ST' & ER' & RA' & RH' & OWN & LBO & PR' & PSH' & EC & EU & EW' & EN'
                      & B1 & B2 & B3 & VS & CAP & FS & XP & RF' & AC' & S0' & LV' & AL').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    cbn [pc_state pc_cons pc_user wparser] in EC, EU, EW', EN', B1, B2, B3, AL'.
    rewrite ?HLib.u64_of_Z in ST', XP by lia.
    rewrite (ret_pc_even AWO_PM_RA ltac:(unfold AWO_PM_RA; lia) eq_refl) in VIS'.
    rewrite EW in EW'. rewrite EN in EN'. rewrite EN in B1. rewrite EN in B2. rewrite EN in B3. rewrite EN in AL'.
    assert (WC' : wfc2 e ff m').
    { eapply (wfc2_xpres e ff fp (w_LB e) _ m m' HP (winv_ff H _ _ _ _ _ _ _ HI) (wfc2_of_wfc e ff m WC) XP).
      apply Forall_cons; [unfold wfc2_apart; cbn [fst snd]; unfold RtA_Td.ATDLOC; lia|].
      apply Forall_cons; [unfold wfc2_apart, PARSER_SIZE; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi. apply wfc2_apart_of. exact (wscr_apart H HB e ff fp m' iv HP RF' (winv_ff H _ _ _ _ _ _ _ HI) FSi). }
    eapply (K msF' mo' s' LB' LBs' m' XS c' r); [exact VIS' | exact FZ' | exact KR' | exact MP' | | exact WC' | exact XP | exact FS | exact OWN
              | exact PR' | exact PSH' | exact EC | exact EW' | exact EN' | exact B1 | exact B2 | exact B3 | exact VS | exact CAP | lia].
    change ((RtA_Td.ATDLOC, RtA_Td.ATDLOC + 8) :: (ff + 128, ff + 128 + PARSER_SIZE) :: XS) with ([(RtA_Td.ATDLOC, RtA_Td.ATDLOC + 8); (ff + 128, ff + 128 + PARSER_SIZE)] ++ XS) in XP.
    eapply (winv_sr_gen H HB e ff fp XSc XS _ s LB (w_LB e) s' LB' m m' HP HI (fun b Hb => Hb) XP FS).
    - apply Forall_cons; [right; right; right; right; reflexivity|].
      apply Forall_cons; [right; left; cbn [fst snd]; unfold PARSER_SIZE, WO_FLAGP; lia|].
      apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons.
      { cbn [fst snd]. intros _. replace (RtA_Td.ATDLOC + 8 - RtA_Td.ATDLOC) with 8 by lia. exact (RtA_Td.td_wr_any m'). }
      apply Forall_cons.
      { cbn [fst snd]. intros _. replace (ff + 128 + PARSER_SIZE - (ff + 128)) with 288 by (unfold PARSER_SIZE; lia).
        destruct PR' as [Pcons Puser Phdr Pins Phunk Pst D1 Pal Prange Pconsf Pconsm Pconsd]. unfold ST_OFF in D1, Pst.
        pose proof (state_repA_wr LB' m' (ff + 128 + 48) (pc_state c') Pst ltac:(lia) ltac:(lia)) as (W0 & W1 & W2).
        split; [lia|]. split; [lia|]. intros i Hi.
        destruct (Z.lt_ge_cases i 48) as [Hi'|Hi'].
        - unfold wview, wa. pose proof (D1 i ltac:(lia)) as Di. destruct (m' (Z_to_bv 64 (ff + 128 + i))) as [b|] eqn:E; [discriminate | contradiction].
        - replace (ff + 128 + i) with (ff + 128 + 48 + (i - 48)) by lia. apply W2. lia. }
      eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
      destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
        (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|]; split; [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
    - exact LV'.
  Qed.

  Definition wy1_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk LBs : list block) (c' : parserC) (k : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 (r : Z) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 AWO_PM_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 99)
                    (Z_to_bv 64 k) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AWO_PM_RA) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_own LBk (w_LB e) LBs (pc_state c')
      /\ parser_repA LBk m' (ff + 128) c' /\ parser_sh m' (ff + 128) c' /\ pc_cons c' = ff + 48
      /\ st_words (pc_state c') = w_words e /\ st_nwords (pc_state c') = w_n e
      /\ lb_small LBs + 2 ^ 12 <= po_small (w_n e) /\ Z.of_nat (length LBs) + 8 <= po_cnt (w_n e) /\ nlarge LBs + 3 <= po_large (w_n e)
      /\ st_vsteps (pc_state c') /\ (forall q n, In (q, n) (state_blocks (pc_state c')) -> n <= 2 ^ 40)
      /\ wr_at asegs m' (wS1 e + 72) ST_SIZE.

  Lemma seg_pm1 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s9 LB9 XS9 (p4 p5 p6 : bptr) g h k,
    wpre H e -> as_AKREL H s9 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s9 >= as_AL H (w_s e) ->
    Permutation LB9 (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)]) ->
    wx1_post H e ff fp XS9 s9 LB9 g h k (as_VIS H s9 msF) ->
    (forall msF' mo' s10 LB10 LBs XS c', as_AKREL H s10 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s10 >= as_AL H (w_s e) - po_cost (w_n e) ->
       wy1_post e ff fp XS s10 LB10 LBs c' k (as_VIS H s10 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s9 LB9 XS9 p4 p5 p6 g h k HP KR MP AL9 PERM9 P9 K.
    destruct P9 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0
                    & VIS & FZ & HI & WC & C48 & R1 & SH1 & G1 & G2 & G3 & WRT).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    eapply (wpm e ff fp XS9 s9 LB9 [(p4, g, 500); (p5, h, 100); (p6, k, 100)] (mkfreshA (w_words e) (w_n e) g h k) m0 msF mo Q);
      [exact HP | exact HI | exact WC | exact VIS | exact FZ | exact KR | lia | exact R1 | exact SH1
      | apply fresh_mkfreshA; lia | exact PERM9 | rewrite mkfreshA_blocks by lia; apply Permutation_refl |].
    intros msF' mo' s' LB' LBs' m' XS c' r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      VIS' FZ' KR' MP' HI' WC' XP FS OWN PR' PSH' EC EW EN B1 B2 B3 VS CAP AL'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    change ((RtA_Td.ATDLOC, RtA_Td.ATDLOC + 8) :: (ff + 128, ff + 128 + PARSER_SIZE) :: XS) with ([(RtA_Td.ATDLOC, RtA_Td.ATDLOC + 8); (ff + 128, ff + 128 + PARSER_SIZE)] ++ XS) in XP.
    assert (C48' : rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]).
    { pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & _).
      eapply (wS1cell_xp H HHb e ff fp (w_LB e) _ XS m' m0 m'); [exact HP | exact RF' | exact (winv_ff H _ _ _ _ _ _ _ HI) | exact XP | exact FS | | lia | exact C48].
      apply Forall_cons; [cbn [fst snd cells_size csize]; unfold RtA_Td.ATDLOC; lia|].
      apply Forall_cons; [cbn [fst snd cells_size csize]; unfold PARSER_SIZE; lia | apply Forall_nil]. }
    assert (WRT' : wr_at asegs m' (wS1 e + 72) ST_SIZE).
    { eapply xpres_wr_at; [exact XP | exact WRT |]. split; [left; lia|].
      apply Forall_cons; [cbn [fst snd]; unfold RtA_Td.ATDLOC; lia|].
      apply Forall_cons; [cbn [fst snd]; unfold PARSER_SIZE, ST_SIZE; pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & _); lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (_ & _ & _ & _ & _ & _ & B7 & _). right. unfold ST_SIZE. lia. }
    eapply (K msF' mo' s' LB' LBs' (XS9 ++ XS) c'); [exact KR' | mpres_chain | lia |].
    unfold wy1_post. rewrite VIS'.
    do 3 eexists. exists r. do 11 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI'|]. split; [exact WC'|]. split; [exact C48'|]. split; [exact OWN|].
    split; [exact PR'|]. split; [exact PSH'|]. split; [exact EC|]. split; [exact EW|]. split; [exact EN|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact VS|]. split; [exact CAP|]. exact WRT'.
  Qed.
End WoPm.
