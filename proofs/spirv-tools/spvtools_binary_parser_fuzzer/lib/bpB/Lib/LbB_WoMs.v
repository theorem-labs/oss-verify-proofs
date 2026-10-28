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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Ms.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wms_post : forall (e : went H) ff fp XSc sk LBk m m' dst n,
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    ((ff <= dst /\ dst + n <= ff + WO_FLAGP) \/ (wS1 e <= dst /\ dst + n <= wSP e - WO_SAVED)) -> 0 <= n ->
    munch [(dst, dst + n); (wS1 e - AINTRIN_STACK, wS1 e)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    stk asegs m' (w_lo e) (wS1 e) ->
    winv H e ff fp XSc sk LBk m'.
  Proof.
    intros e ff fp XSc sk LBk m m' dst n HP HI WIN Hn MU WM MI' ST'.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    unfold WO_FLAGP, WO_SAVED, AINTRIN_STACK in *.
    eapply (winv_munch H HH); [exact HP | exact HI | exact MU | exact WM | exact MI' | |].
    - destruct (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia)) as [_ STu].
      pose proof aceil_facts.
      exact (stk_merge asegs m' (w_lo e) (wS1 e) (wSP e) ST' (stk_wmono m m' (wS1 e) (wSP e) STu WM ltac:(lia)) ltac:(lia)).
    - unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + destruct WIN as [WIN|WIN]; [right; left | left]; lia.
      + left. lia.
  Qed.

  Lemma wms_ff : forall (e : went H) ff fp XSc sk LBk m (Q : machine_state -> Prop)
      (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (A N dst n : Z) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc sk LBk m -> addressable m A N ->
    ff <= A -> A + N <= ff + WO_FLAGP -> A <= dst -> dst + n <= A + N -> 0 <= n ->
    (forall m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       winv H e ff fp XSc sk LBk m' -> munch [(dst, dst + n); (wS1 e - AINTRIN_STACK, wS1 e)] m m' -> wmono asegs m m' ->
       rw_cells asegs m' dst [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) 0)] ->
       evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 (Z_to_bv 64 dst) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XSc sk LBk m Q ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 A N dst n F fc HP HI PAD A1 A2 D1 D2 Hn K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (winv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (wframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF. unfold WO_FLAGP in A2.
    assert (WD : wr_at asegs m dst n).
    { pose proof (winv_wf H _ _ _ _ _ _ _ HI) as (W0 & W1 & W). unfold WO_FLAGP in *. split; [lia|]. split; [lia|]. intros i Hi.
      replace (dst + i) with (ff + (dst - ff + i)) by lia. apply W. lia. }
    destruct (wr_at_rw_cells m dst n WD ltac:(lia) Hn) as (junk & CJ).
    assert (ACC : accessible m dst n) by (eapply (addressable_accessible m A N); [exact PAD | lia | lia | unfold WO_FLAGP, AAPP_HI in *; lia]).
    assert (SHV : shvis m dst (dst + n)).
    { pose proof (ah_frm_shvis H HH _ _ (6, ff, fp) (winv_rf H _ _ _ _ _ _ _ HI) (or_introl eq_refl)) as X. cbn in X.
      change (fsz 6) with 4096 in X. unfold WO_FLAGP in *. eapply shvis_sub; [exact X | lia | lia | lia | lia | lia]. }
    eapply evt_cut.
    { eapply (ah_memset H HH ra (Z_to_bv 64 (wS1 e))) with (c := 0) (junk := junk) (lo := w_lo e);
        rewrite ?HLib.u64_of_Z by lia;
        [reflexivity | lia | exact CJ | exact ACC | exact SHV
        | exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))) | exact CE | unfold AINTRIN_STACK; lia
        | exact (winv_mi H _ _ _ _ _ _ _ HI) | exact (winv_ac H _ _ _ _ _ _ _ HI) | lia | eapply aapp_in_app_mem; [exact F10 | lia | lia]
        | eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia] | left; lia]. }
    intros ms' P. destruct P as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & CB' & AC').
    subst ms'. assert (Ed : bv_unsigned (Z_to_bv 64 dst) = dst) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    assert (Es : bv_unsigned (Z_to_bv 64 (wS1 e)) = wS1 e) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    rewrite Es in ST'. rewrite Ed in CB'. rewrite En in CB'.
    assert (MU' : munch [(dst, dst + n); (wS1 e - AINTRIN_STACK, wS1 e)] m m') by (eapply munch_eqW; [exact MU | rewrite Ed, En, Es; reflexivity]).
    clear MU. rename MU' into MU.
    apply K; [| exact MU | exact WM | exact CB'].
    assert (HI' : winv H e ff fp XSc sk LBk m').
    { eapply (wms_post e ff fp XSc sk LBk m m' dst n HP HI); [left; unfold WO_FLAGP; lia | exact Hn | exact MU | exact WM | exact MI' | exact ST']. }
    exact HI'.
  Qed.

  Lemma wms_rs : forall (e : went H) ff fp XSc sk LBk m (Q : machine_state -> Prop)
      (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (dst n : Z) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    wS1 e <= dst -> dst + n <= wSP e - WO_SAVED -> 0 <= n ->
    (forall m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       winv H e ff fp XSc sk LBk m' -> munch [(dst, dst + n); (wS1 e - AINTRIN_STACK, wS1 e)] m m' -> wmono asegs m m' ->
       rw_cells asegs m' dst [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) 0)] ->
       evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 (Z_to_bv 64 dst) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XSc sk LBk m Q ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 dst n F fc HP HI D1 D2 Hn K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof aceil_facts as ACF. unfold WO_SAVED in D2.
    pose proof (winv_stk H _ _ _ _ _ _ _ HI) as ST.
    pose proof (winv_s0 H _ _ _ _ _ _ _ HI) as S0.
    assert (WD : wr_at asegs m dst n).
    { pose proof (wr_at_of_stk asegs m _ _ ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (dst + i) with (w_lo e + (dst - w_lo e + i)) by lia. apply W. lia. }
    destruct (wr_at_rw_cells m dst n WD ltac:(unfold AAPP_HI in *; lia) Hn) as (junk & CJ).
    eapply evt_cut.
    { eapply (ah_memset H HH ra (Z_to_bv 64 (wS1 e))) with (c := 0) (junk := junk) (lo := w_lo e);
        rewrite ?HLib.u64_of_Z by lia;
        [reflexivity | lia | exact CJ | eapply stack0_accessible; [exact S0 | lia | lia | lia]
        | eapply stack0_shvis; [exact S0 | lia | lia | lia]
        | exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) ST ltac:(lia))) | exact CE | unfold AINTRIN_STACK; lia
        | exact (winv_mi H _ _ _ _ _ _ _ HI) | exact (winv_ac H _ _ _ _ _ _ _ HI) | lia | eapply stack0_in_app_mem; [exact S0 | lia | lia]
        | apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia] | right; lia]. }
    intros ms' P. destruct P as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & CB' & AC').
    subst ms'. assert (Ed : bv_unsigned (Z_to_bv 64 dst) = dst) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    assert (Es : bv_unsigned (Z_to_bv 64 (wS1 e)) = wS1 e) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    rewrite Es in ST'. rewrite Ed in CB'. rewrite En in CB'.
    assert (MU' : munch [(dst, dst + n); (wS1 e - AINTRIN_STACK, wS1 e)] m m') by (eapply munch_eqW; [exact MU | rewrite Ed, En, Es; reflexivity]).
    clear MU. rename MU' into MU.
    apply K; [| exact MU | exact WM | exact CB'].
    eapply (wms_post e ff fp XSc sk LBk m m' dst n HP HI); [right; unfold WO_SAVED; lia | exact Hn | exact MU | exact WM | exact MI' | exact ST'].
  Qed.
End Ms.
