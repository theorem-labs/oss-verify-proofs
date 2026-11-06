(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_SR LbA_Conv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_Own LbA_RtOwn LbA_HKit LbA_HStKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit2 LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR6 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoF LbA_WoS1 LbA_WoS2 LbA_WoS3 LbA_WoT2 LbA_WoPm LbA_WoU LbA_WoG LbA_WoS4.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS5.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis MVA : st_mva_stmt H.
  Hypothesis DTOR : st_dtor_stmt H.
  Hypothesis WTR : po_tr_ok H.
  Let HB := rt_bp_base H HHb.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Lemma munch_nil_eq5 : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Lemma wfc2_ad : forall (e : went H) ff fp XSc sk LBk m, winv H e ff fp XSc sk LBk m -> wfc2 H e ff m -> addressable m (ff + 176) ST_SIZE.
  Proof.
    intros e ff fp XSc sk LBk m HI (_ & _ & _ & U & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & _).
    unfold ST_SIZE. replace (ff + 176) with (ff + 128 + 48) by lia.
    eapply (addressable_sub8 m (ff + 128) 288 48 240); [exact (wo_pad m ff U F3 ltac:(lia)) | reflexivity | reflexivity | reflexivity | lia | lia | lia].
  Qed.

  Definition ww1_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (r u v w : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 WO_DT2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (wS1 e + 72)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 w) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 w) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m'
      /\ state_repA LBk m' (ff + 176) (mkfreshA 0 0 u v w) /\ state_sh m' (mkfreshA 0 0 u v w)
      /\ state_repA LBk m' (wS1 e + 72) (state_emptied (mkfreshA 0 0 u v w))
      /\ 0 < u /\ 0 < v /\ 0 < w.

  Lemma seg_mva2 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s13 LB10 LBs XS10 (c' : parserC) (p7 p8 p9 : bptr) r u v w
      (F : bvmap 5 word) (fc : bv 32),
    let LB13 := (p9, w, 100) :: (p8, v, 100) :: (p7, u, 500) :: LB10 in
    wpre H e -> as_AKREL H s13 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s13 >= as_AL H (w_s e) - po_cost (w_n e) ->
    wpf H e ff LB10 LBs c' -> ~ In p7 (map blk_id LB10) -> ~ In p8 (map blk_id ((p7, u, 500) :: LB10)) ->
    ~ In p9 (map blk_id ((p8, v, 100) :: (p7, u, 500) :: LB10)) -> frm_zero fc ->
    wv3_post H e ff fp XS10 s13 LB13 (pc_state c') r u v w F fc (as_VIS H s13 msF) ->
    (forall msF' mo' s14 LB14 XS, as_AKREL H s14 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s14 >= as_AL H (w_s e) - po_cost (w_n e) ->
       Permutation LB14 (w_LB e ++ [(p7, u, 500); (p8, v, 100); (p9, w, 100)]) ->
       ww1_post e ff fp XS s14 LB14 r u v w (as_VIS H s14 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s13 LB10 LBs XS10 c' p7 p8 p9 r u v w F fc LB13 HP KR MP AL13 PF NI7 NI8 NI9 FZ P14 K.
    destruct P14 as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & R & SHP & TS & WU & WV & WW).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BLg & AL0).
    pose proof PF as ((O1 & O2) & _ & _ & _ & _ & _ & _ & _ & CAP).
    assert (PB : Permutation LB13 ([(p7, u, 500); (p8, v, 100); (p9, w, 100)] ++ LB10)) by (unfold LB13; apply perm_wo3).
    destruct (wst_T0_rep H HB e ff fp XS10 s13 LB13 m0 p7 p8 p9 u v w LB10 HP HI TS WU WV WW
                ltac:(unfold LB13; cbn; tauto) ltac:(unfold LB13; cbn; tauto) ltac:(unfold LB13; cbn; tauto) PB) as (R2 & SH2 & G1 & G2 & G3).
    assert (PLB : Permutation LB13 (w_LB e ++ LBs ++ [(p7, u, 500); (p8, v, 100); (p9, w, 100)])).
    { unfold LB13. etransitivity; [apply perm_wo3|]. etransitivity; [apply Permutation_app_comm|].
      rewrite app_assoc. apply Permutation_app_tail. exact O1. }
    eapply (wmva H HHb HOWN MVA WTR e ff fp XS10 s13 LB13 LBs [(p7, u, 500); (p8, v, 100); (p9, w, 100)]
              (pc_state c') (mkfreshA 0 0 u v w) m0 msF mo Q);
      [exact HP | exact HI | exact (wfc2_ad e ff fp XS10 s13 LB13 m0 HI WC) | exact VIS | exact FZ | reflexivity | exact KR | lia
      | exact R | exact SHP | exact R2 | exact SH2 | exact PLB | exact O2
      | rewrite mkfreshA_blocks by lia; apply Permutation_refl | exact CAP |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM R1' SH1' R2' AL'.
    rewrite (ret_pc_even WO_MVA2_RA ltac:(unfold WO_MVA2_RA; lia) eq_refl) in VIS'.
    rewrite state_moved_mkfreshA in R1', SH1'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    assert (WC' : wfc2 H e ff m').
    { eapply (wfc2_xpres H e ff fp (w_LB e) _ m0 m' HP (winv_ff H _ _ _ _ _ _ _ HI) WC XP).
      pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      apply Forall_cons; [unfold wfc2_apart, ST_SIZE; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [unfold wfc2_apart, ST_SIZE; cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi. apply wfc2_apart_of. exact (wscr_apart H HB e ff fp m' iv HP RF' (winv_ff H _ _ _ _ _ _ _ HI) FSi). }

    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI')) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    eapply (ahh_evt_then H HB (wd3_post (w_gp e) (w_tp e) F' fc' (wSP e) (wS1 e) ff (w_lo e) r w m') Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    { exact (wd3 (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (ff + 176)) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (wSP e) (wS1 e) ff (w_lo e) r w
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI') (winv_mi H _ _ _ _ _ _ _ HI')). }
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & EQ & MU & WM & MI1 & ST1).
    pose proof (munch_nil_eq5 m' m1 MU) as EM. subst m1.
    eapply (K msF2 mo2 s' LB' (XS10 ++ XS)); [exact KR2 | mpres_chain | lia | exact PERM |].
    unfold ww1_post. rewrite EQ.
    do 14 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI'|]. split; [exact WC'|].
    split; [exact R1'|]. split; [exact SH1'|]. split; [exact R2'|]. lia.
  Qed.

  Definition ww2_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (r u v w : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 WO_DT3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 176)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 w) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 w) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m'
      /\ state_repA LBk m' (ff + 176) (mkfreshA 0 0 u v w) /\ state_sh m' (mkfreshA 0 0 u v w)
      /\ 0 < u /\ 0 < v /\ 0 < w.

  Lemma seg_dt2 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s14 LB14 XS14 (p7 p8 p9 : bptr) r u v w,
    wpre H e -> as_AKREL H s14 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s14 >= as_AL H (w_s e) - po_cost (w_n e) ->
    Permutation LB14 (w_LB e ++ [(p7, u, 500); (p8, v, 100); (p9, w, 100)]) ->
    ww1_post e ff fp XS14 s14 LB14 r u v w (as_VIS H s14 msF) ->
    (forall msF' mo' s15 LB15 XS, as_AKREL H s15 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s15 >= as_AL H (w_s e) - po_cost (w_n e) ->
       Permutation LB15 (w_LB e ++ [(p7, u, 500); (p8, v, 100); (p9, w, 100)]) ->
       ww2_post e ff fp XS s15 LB15 r u v w (as_VIS H s15 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s14 LB14 XS14 p7 p8 p9 r u v w HP KR MP AL14 PERM14 P15 K.
    destruct P15 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0
                    & VIS & FZ & HI & WC & R1 & SH1 & R2 & G1 & G2 & G3).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BLg & AL0).
    assert (INC : forall b, In b (w_LB e) -> In b LB14).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM14|]. apply in_or_app. left. exact Hb. }
    eapply (wdtT H HHb HOWN DTOR WTR e ff fp XS14 s14 LB14 (state_emptied (mkfreshA 0 0 u v w)) m0 msF mo Q WO_DT2_RA);
      [exact HP | exact HI | exact INC | exact VIS | exact FZ | unfold WO_DT2_RA; lia | reflexivity
      | unfold PO_PF, WO_DT2_RA; cbn; tauto | exact KR | lia | exact R2 | apply state_sh_emptied | reflexivity |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM WR' AL'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH14.
    assert (PERM' : Permutation LB' (w_LB e ++ [(p7, u, 500); (p8, v, 100); (p9, w, 100)])) by (etransitivity; [exact PERM | exact PERM14]).
    change ((wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS) with ([(wS1 e + 72, wS1 e + 72 + ST_SIZE)] ++ XS) in XP.
    assert (WC' : wfc2 H e ff m').
    { eapply (wfc2_xpres H e ff fp LB14 _ m0 m' HP (winv_ff H _ _ _ _ _ _ _ HI) WC XP).
      pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      apply Forall_cons; [unfold wfc2_apart, ST_SIZE; cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi. apply wfc2_apart_of. exact (wscr_apart H HB e ff fp m' iv HP RF' (winv_ff H _ _ _ _ _ _ _ HI) FSi). }
    assert (BLK : forall p n, In (p, n) (state_blocks (mkfreshA 0 0 u v w)) -> In (p, n) (lbl LB14) /\ In (p, n) (lbl LB')).
    { rewrite mkfreshA_blocks by lia. intros p n Hin.
      assert (IN7 : In (p, n) (lbl [(p7, u, 500); (p8, v, 100); (p9, w, 100)])) by (cbn; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; tauto).
      destruct (lbl_in_inv _ _ _ IN7) as (q & Hq).
      split; [apply (lbl_in _ q) | apply (lbl_in _ q)]; (eapply Permutation_in; [apply Permutation_sym; eassumption|]; apply in_or_app; right; exact Hq). }
    destruct (wstate_xp H HHb e ff fp s14 LB14 LB' _ XS m' m0 m' (mkfreshA 0 0 u v w) HP RF' (winv_ff H _ _ _ _ _ _ _ HI) RH14 XP FS
                ltac:(apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]) BLK R1 SH1) as [R1' SH1'].

    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI')) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    eapply (ahh_evt_then H HB (wd4_post (w_gp e) (w_tp e) F' fc' (wSP e) (wS1 e) ff (w_lo e) r w m') Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    { exact (wd4 (w_gp e) (w_tp e) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (wSP e) (wS1 e) ff (w_lo e) r w
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI') (winv_mi H _ _ _ _ _ _ _ HI')). }
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & EQ & MU & WM & MI1 & ST1).
    pose proof (munch_nil_eq5 m' m1 MU) as EM. subst m1.
    eapply (K msF2 mo2 s' LB' (XS14 ++ XS)); [exact KR2 | mpres_chain | lia | exact PERM' |].
    unfold ww2_post. rewrite EQ.
    do 14 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI'|]. split; [exact WC'|].
    split; [exact R1'|]. split; [exact SH1'|]. lia.
  Qed.

  Lemma wdtP : forall (e : went H) ff fp XSc s LB (LBs : list block) (c : stateC) m msF mo (Q : config -> Prop) (r : Z)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> addressable m (ff + 176) ST_SIZE ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 (ff + 176)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
    frm_zero fc -> 0 <= r < 2 ^ 64 -> r mod 2 = 0 -> In (APC0_FREE, [r]) PO_PF ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    state_repA LB m (ff + 176) c -> state_sh m c ->
    Permutation LB (w_LB e ++ LBs) -> Permutation (lbl LBs) (state_blocks c) ->
    (forall p n, In (p, n) (state_blocks c) -> n <= 2 ^ 40) ->
    (forall msF' mo' s' LB' m' XS (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (Z_to_bv 64 r) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' ->
       xpres H (w_LB e) (wS1 e) ((ff + 176, ff + 176 + ST_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
       Permutation LB' (w_LB e) ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB LBs c m msF mo Q r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI AD1 VIS FZ Hr RE INPF KR AL0 R SH PLB PBL CAP K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (winv_rf H _ _ _ _ _ _ _ HI) as RF.
    destruct (wchain_call H HB e ff fp XSc s LB m HP HI) as [CH CHU].
    eapply (ah_seq H HB).
    { eapply (DTOR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                (Z_to_bv 64 (ff + 176)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc msF m mo s LB (w_LB e) LBs ((3, ff, fp) :: w_LF e) (ff + 176) c (w_lo e) (w_B e) (w_shi e) errv
                ((wSP e, bv_unsigned (w_ra e)) :: w_CH e));
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - exact FZ.
      - reflexivity.
      - exact R.
      - exact SH.
      - exact PLB.
      - exact PBL.
      - exact CAP.
      - exact AD1.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE. unfold AFS_SIZE in *. lia.
      - left. exists (3, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 3) with 512. unfold ST_SIZE. lia.
      - right. unfold ST_SIZE. lia.
      - exact RH.
      - exact KR.
      - exact AL0.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold AST_DTOR_STACK, AFREE_STACK. lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - exact RE.
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - exact RF.
      - exact (winv_s0 H _ _ _ _ _ _ _ HI).
      - lia.
      - exact (HOWN _ _ _ RH).
      - destruct WTR as [_ WF]. apply Forall_app in WF as [_ WF]. exact WF.
      - exact CH.
      - exact (wtrace_dtor H e r HP INPF).
      - exact CHU. }
    intros [msF' mo'] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & s' & LB' & XS & F' & fc'
                      & VIS' & FZ' & KR' & MP' & MI' & ST' & ER' & RA' & RH' & PERM & FS & XP & RF' & AC' & S0' & AL' & OWN' & WR').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    rewrite ?HLib.u64_of_Z in ST', XP by lia.
    rewrite (ret_pc_even r Hr RE) in VIS'.
    eapply (K msF' mo' s' LB' m' XS); [exact VIS' | exact FZ' | exact KR' | exact MP' | | exact XP | exact FS | exact PERM | lia].
    change ((ff + 176, ff + 176 + ST_SIZE) :: XS) with ([(ff + 176, ff + 176 + ST_SIZE)] ++ XS) in XP.
    eapply (winv_sr H HB e ff fp XSc XS _ s LB (w_LB e) s' LB' m m' HP HI (fun b Hb => Hb) XP FS).
    - apply Forall_cons; [right; left; cbn [fst snd]; unfold ST_SIZE, WO_FLAGP; lia|].
      apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [cbn [fst snd]; intros _; replace (ff + 176 + ST_SIZE - (ff + 176)) with ST_SIZE by lia; exact WR'|].
      eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
      destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
        (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|]; split; [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
  Qed.

  Definition ww3_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (r w : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 WO_DT3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 w) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 w) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 WO_DT3_RA) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m'.

  Lemma seg_dt3 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s15 LB15 XS15 (p7 p8 p9 : bptr) r u v w,
    wpre H e -> as_AKREL H s15 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s15 >= as_AL H (w_s e) - po_cost (w_n e) ->
    Permutation LB15 (w_LB e ++ [(p7, u, 500); (p8, v, 100); (p9, w, 100)]) ->
    ww2_post e ff fp XS15 s15 LB15 r u v w (as_VIS H s15 msF) ->
    (forall msF' mo' s16 LB16 XS, as_AKREL H s16 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s16 >= as_AL H (w_s e) - po_cost (w_n e) ->
       Permutation LB16 (w_LB e) ->
       ww3_post e ff fp XS s16 LB16 r w (as_VIS H s16 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s15 LB15 XS15 p7 p8 p9 r u v w HP KR MP AL15 PERM15 P16 K.
    destruct P16 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0
                    & VIS & FZ & HI & WC & R1 & SH1 & G1 & G2 & G3).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BLg & AL0).
    eapply (wdtP e ff fp XS15 s15 LB15 [(p7, u, 500); (p8, v, 100); (p9, w, 100)] (mkfreshA 0 0 u v w) m0 msF mo Q WO_DT3_RA);
      [exact HP | exact HI | exact (wfc2_ad e ff fp XS15 s15 LB15 m0 HI WC) | exact VIS | exact FZ | unfold WO_DT3_RA; lia | reflexivity
      | unfold PO_PF, WO_DT3_RA; cbn; tauto | exact KR | lia | exact R1 | exact SH1 | exact PERM15
      | rewrite mkfreshA_blocks by lia; apply Permutation_refl
      | rewrite mkfreshA_blocks by lia; intros p n Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM AL'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    assert (WC' : wfc2 H e ff m').
    { eapply (wfc2_xpres H e ff fp (w_LB e) _ m0 m' HP (winv_ff H _ _ _ _ _ _ _ HI) WC XP).
      pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      apply Forall_cons; [unfold wfc2_apart, ST_SIZE; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi. apply wfc2_apart_of. exact (wscr_apart H HB e ff fp m' iv HP RF' (winv_ff H _ _ _ _ _ _ _ HI) FSi). }
    eapply (K msF' mo' s' LB' (XS15 ++ XS)); [exact KR' | mpres_chain | lia | exact PERM |].
    unfold ww3_post. rewrite VIS'.
    do 15 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI' | exact WC'].
  Qed.
End WoS5.
