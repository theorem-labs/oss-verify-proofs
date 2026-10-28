(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63 Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import RegEqv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Frame. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_state RT_main_shape RT_rep D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxAcct AxMeasure AxLz AxEntryRel AxEntryS AxFd AxModelRel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxBdA Require Import BdAParams.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AxA Require Import AxExport AxExportM AxExportH AxExportQ AxExportV AxExportI FinMain1 FinMain2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxA Require Import AxExportS AxExportF AxExportR AxExportL AxExportA AxExportT FinMain3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition RES_A : list (Z * Z) := [(65536, 1613824); (1679360, 3772416); (5451776, 495616); (5947392, 6418432)].
Lemma RES_A_ok : map (fun q : word * word => (bv_unsigned (fst q), bv_unsigned (snd q))) (segments_reserved ctasegs) = RES_A.
Proof. vm_compute. reflexivity. Qed.

Lemma asegs_low : segs_low ctasegs.
Proof. exact (img_low BDA_SEGS BDA_PC bda_img_ok). Qed.

(* [comment removed for export] *)
Definition fin_core (F : bforms) (B : AST) : bool :=
  fin_model a_main SEGTOP_A B && fin_win2 target_alloc_limit B
  && lay_ok B (win_of B) JUNK F && stksh_ok B && atop_hi_ok B
  && reg_lit B 1 MAIN_RA && reg_form B 2 (laddc (bf_sp0 F) (- 48)) && reg_lit B 4 TP_A
  && reg_form B 10 (0, [(v_argc, 1)]) && reg_form B 11 (laddc (bf_sp0 F) 8)
  && chk_stk B (win_of B) F SEGTOP_A (SA LB_ACEIL 0, SA LB_sp0 (- 48)).

Section BridgeA.
Variable OUT_rep : Stdio.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.

(* [comment removed for export] *)
Variable Σ0 : layoutA -> Z -> rtsA.       (* [comment removed for export] *)
Variable h1_of : bforms -> AST -> Z.      (* [comment removed for export] *)
Hypothesis Σ0_lay : forall L h, lay (Σ0 L h) = L.
Hypothesis Σ0_aw : forall L h, aw (Σ0 L h) = [].
Hypothesis Σ0_maps : forall L h, rt_maps (Σ0 L h) = l_maps0 L.
Hypothesis Σ0_eager : forall L h, 0 <= rt_eager (Σ0 L h).
Hypothesis Σ0_live : forall L h, live (Σ0 L h) = [] /\ frames (Σ0 L h) = [] /\ CREDIT_DRV <= credit (Σ0 L h).
Variable fin_art : bforms -> AST -> bool.
Hypothesis Hart : forall (fs0 : Fs.Fs) (ρ : valuation) (B : AST) (ms : machine_state) (model : Model) (F : bforms),
  R ctasegs amodel (MR ctasegs fs0 ρ) target_alloc_limit ρ B (mkCfg ms model) ->
  fin_core F B = true -> fin_art F B = true ->
  layout_ok (Lm ρ (win_of B) JUNK F (vm_maps (m_vmmaps model))) ->
  ART_A (Σ0 (Lm ρ (win_of B) JUNK F (vm_maps (m_vmmaps model))) (h1_of F B)) (mM ρ ms model (win_of B) JUNK F (vm_maps (m_vmmaps model)))
  /\ CLX OUT_rep ERR_rep XENV LIB Stdio.stdout_init (mM ρ ms model (win_of B) JUNK F (vm_maps (m_vmmaps model))).

Definition fin_main (B : AST) : bool :=
  match bf_of ctasegs PCELLS_A B with Some F => fin_core F B && fin_art F B | None => false end.

Lemma fin_main_out (B : AST) : fin_main B = true -> am_out (a_model B) = [].
Proof.
  unfold fin_main. destruct (bf_of ctasegs PCELLS_A B) as [F|]; [|discriminate]. intros H. apply andb_prop in H as [H _].
  unfold fin_core in H. do 10 (apply andb_prop in H as [H _]). unfold fin_model in H. do 5 (apply andb_prop in H as [H _]).
  apply andb_prop in H as [_ H]. destruct (am_out (a_model B)); [reflexivity | discriminate H].
Qed.

Theorem bridgeA (fs0 : Fs.Fs) (B : AST) : fin_main B = true ->
  forall ρ c, R ctasegs amodel (MR ctasegs fs0 ρ) target_alloc_limit ρ B c ->
  exists c', cfg_eqv c' c /\ START RTA OUT_rep ERR_rep XENV LIB (dec_argvB ρ) fs0 c'.
Proof.
  unfold fin_main. destruct (bf_of ctasegs PCELLS_A B) as [F|] eqn:EF; [|discriminate]. intros Hfin ρ [ms model] HR.
  apply andb_prop in Hfin as [Hcore Hfa]. pose proof Hcore as Hcore0. unfold fin_core in Hcore.
  apply andb_prop in Hcore as [Hcore Kstk]. apply andb_prop in Hcore as [Hcore Ka1]. apply andb_prop in Hcore as [Hcore Ka0].
  apply andb_prop in Hcore as [Hcore Ktp]. apply andb_prop in Hcore as [Hcore Ksp]. apply andb_prop in Hcore as [Hcore Kra].
  apply andb_prop in Hcore as [Hcore Kath]. apply andb_prop in Hcore as [Hcore Kss]. apply andb_prop in Hcore as [Hcore Klay].
  apply andb_prop in Hcore as [Kfm Kfw].
  set (W := win_of B) in *. set (L := Lm ρ W JUNK F (vm_maps (m_vmmaps model))) in *.
  set (m := mM ρ ms model W JUNK F (vm_maps (m_vmmaps model))) in *.
  destruct (ex_layout_ok fs0 _ ρ B ms model HR W JUNK F RES_A RES_A_ok eq_refl Klay) as (Hlay & Hat & Esp & Heb).
  fold L in Hlay, Hat, Esp.
  destruct (lay_ok_parts B W JUNK F Klay) as [Hent Hwb].
  destruct (Hart fs0 ρ B ms model F HR Hcore0 Hfa Hlay) as [HART HCLX]. fold L in HART. fold m in HART, HCLX.
  destruct (sp0_bounds ρ B model F Hlay) as [(S1 & S2) EAC]. fold W L in S1, S2, EAC.
  destruct (hz_parts B a_main Kfm Kfw) as (Hpos & HwL & HwH).
  (* [comment removed for export] *)
  assert (Hfm := Kfm). unfold fin_model in Hfm. apply andb_prop in Hfm as [Hfm Hbj]. apply andb_prop in Hfm as [Hfm Hbt].
  apply andb_prop in Hfm as [Hfm Hrv]. apply andb_prop in Hfm as [Hfm Hfd]. apply andb_prop in Hfm as [Hfm Hsh].
  apply andb_prop in Hfm as [Hpc Hout]. apply Z.leb_le in Hbj.
  assert (Erv : a_resv B = RNone) by (destruct (a_resv B); [reflexivity | discriminate Hrv | discriminate Hrv]).
  assert (Efd : am_fd (a_model B) = FDStd) by (destruct (am_fd (a_model B)); first [reflexivity | discriminate Hfd]).
  (* [comment removed for export] *)
  set (usp := l_sp0 L - 48).
  assert (Eusp : leval ρ (laddc (bf_sp0 F) (- 48)) = usp) by (rewrite leval_laddc; unfold usp, L, Lm, L_of; cbn [l_sp0]; lia).
  assert (Eap : leval ρ (laddc (bf_sp0 F) 8) = l_sp0 L + 8) by (rewrite leval_laddc; unfold L, Lm, L_of; cbn [l_sp0]; lia).
  pose proof (argc_len ρ Heb) as Eargc.
  assert (Ea0 : leval ρ (0, [(v_argc, 1)]) = Z.of_nat (length (dec_argvB ρ))) by (rewrite Eargc; unfold leval; cbn [fst snd teval]; lia).
  assert (Hargc : 1 <= ρ v_argc <= 1024) by (destruct Heb as (X & _); exact X).
  exists (mkCfg (canon_ms ms) model). split; [exact (canon_cfg_eqv ms model)|].
  unfold START.
  set (Rg := ms_regs ms).
  set (S0 := Σ0 L (h1_of F B)).
  exists S0, usp, (l_sp0 L + 8),
    (reg_get Rg (Z_to_bv 5 3)), (reg_get Rg (Z_to_bv 5 5)), (reg_get Rg (Z_to_bv 5 6)), (reg_get Rg (Z_to_bv 5 7)), (reg_get Rg (Z_to_bv 5 8)),
    (reg_get Rg (Z_to_bv 5 9)), (reg_get Rg (Z_to_bv 5 12)), (reg_get Rg (Z_to_bv 5 13)), (reg_get Rg (Z_to_bv 5 14)), (reg_get Rg (Z_to_bv 5 15)),
    (reg_get Rg (Z_to_bv 5 16)), (reg_get Rg (Z_to_bv 5 17)), (reg_get Rg (Z_to_bv 5 18)), (reg_get Rg (Z_to_bv 5 19)), (reg_get Rg (Z_to_bv 5 20)),
    (reg_get Rg (Z_to_bv 5 21)), (reg_get Rg (Z_to_bv 5 22)), (reg_get Rg (Z_to_bv 5 23)), (reg_get Rg (Z_to_bv 5 24)), (reg_get Rg (Z_to_bv 5 25)),
    (reg_get Rg (Z_to_bv 5 26)), (reg_get Rg (Z_to_bv 5 27)), (reg_get Rg (Z_to_bv 5 28)), (reg_get Rg (Z_to_bv 5 29)), (reg_get Rg (Z_to_bv 5 30)),
    (reg_get Rg (Z_to_bv 5 31)), (ms_fregs ms), (ms_fcsr ms), m.
  assert (EAw : rtA_allow S0 = AFull ρ W JUNK F (vm_maps (m_vmmaps model))).
  { unfold rtA_allow, S0. rewrite Σ0_aw, Σ0_lay. reflexivity. }
  split; [|split; [exact HART | split; [| split; [exact HCLX | split; [| split; [| split; [| split; [| split]]]]]]]].
  - (* [comment removed for export] *)
    unfold ASTA, RzCPS.AST. cbn [rt_allow RTA ARTM cfg_ms cfg_model]. rewrite EAw.
    split; [exact (ex_macct_full fs0 ρ B ms model HR F a_main Kfm Kfw Hlay Hwb)|].
    split; [|split; [|exact (ex_HZ_full asegs_low fs0 ρ B ms model HR F a_main Kfm Kfw)]].
    + rewrite (canon_entry fs0 _ ρ B ms model HR a_main _ Hpc ltac:(unfold a_main; lia) Erv). cbv zeta. fold Rg.
      rewrite (reg_lit_sound fs0 _ ρ B ms model HR 1 MAIN_RA ltac:(lia) Kra).
      rewrite (reg_form_sound fs0 _ ρ B ms model HR 2 _ ltac:(lia) Ksp ltac:(rewrite Eusp; unfold usp; lia)), Eusp.
      rewrite (reg_lit_sound fs0 _ ρ B ms model HR 4 TP_A ltac:(lia) Ktp).
      rewrite (reg_form_sound fs0 _ ρ B ms model HR 10 _ ltac:(lia) Ka0 ltac:(rewrite Ea0, Eargc; lia)), Ea0.
      rewrite (reg_form_sound fs0 _ ρ B ms model HR 11 _ ltac:(lia) Ka1 ltac:(rewrite Eap; lia)), Eap.
      reflexivity.
    + split.
      * (* [comment removed for export] *)
        destruct (ex_misc ctasegs fs0 _ ρ B ms model HR) as (M1 & M2 & _ & _).
        unfold ARTM_A. split; [unfold S0; rewrite Σ0_maps; change (l_maps0 L) with (vm_maps (m_vmmaps model));
                               rewrite (filter_vpos_id _ (ex_maps_pos ctasegs fs0 _ ρ B ms model HR)); apply Permutation_refl|].
        split; [exact M1|]. split; [exact M2|].
        split; [pose proof (ex_eager ctasegs fs0 _ ρ B ms model HR); pose proof (Σ0_eager L (h1_of F B)); unfold S0, E0_MAX, JUNK in *; lia|].
        exact (ex_artm_sys fs0 ρ B ms model HR F a_main Kfm Kfw Hlay Hat S0 (Σ0_lay L (h1_of F B))).
      * (* [comment removed for export] *)
        destruct (ex_fds ctasegs fs0 _ ρ B ms model HR Efd) as [Hfds _]. destruct (ex_misc ctasegs fs0 _ ρ B ms model HR) as (_ & _ & M3 & _).
        split; [exact Hfds | exact M3].
  - (* [comment removed for export] *)
    exact (ex_mem_inv ctasegs BDA_PC bda_img_ok fs0 _ ρ B ms model HR _ Kath).
  - (* [comment removed for export] *)
    rewrite Esp. apply (ex_argv_rep fs0 _ ρ B ms model HR W JUNK (allow_main L)).
    + exact Hent.
    + rewrite (mr_atop ctasegs fs0 ρ _ model (r_model _ _ _ _ _ _ _ HR)), Hat, EAC, Esp. lia.
  - (* [comment removed for export] *)
    pose proof (chk_stk_sound asegs_low fs0 _ ρ B ms model HR W JUNK F (vm_maps (m_vmmaps model)) HwL HwH ltac:(fold L; lia) SEGTOP_A _ Kstk) as Hs.
    unfold stk_fact in Hs. cbn [fst snd den_addr den_base] in Hs. fold L in Hs. fold m in Hs.
    cbn [rt_sp0 RTA]. unfold rtA_sp0, S0. rewrite Σ0_lay. unfold usp. replace (l_sp0 L - STACK_WIN) with (l_ACEIL L + 0) by (unfold l_ACEIL; lia).
    replace (l_sp0 L - 48) with (l_sp0 L + -48) by lia. exact Hs.
  - (* [comment removed for export] *)
    destruct (Σ0_live L (h1_of F B)) as (L1 & L2 & L3). unfold sigma0_ok. cbn [rt_live rt_frames rt_credit rt_sp0 RTA].
    unfold rtA_live, rtA_frames, rtA_credit, rtA_sp0, S0. rewrite Σ0_lay. unfold usp. repeat split; try assumption; lia.
  - (* [comment removed for export] *)
    unfold usp. destruct Hlay as (_ & H16 & _). clear - H16. Z.div_mod_to_equations. lia.
  - unfold usp. lia.
  - cbn [rt_sp0 RTA]. unfold rtA_sp0, S0. rewrite Σ0_lay. unfold usp, STACK_WIN. lia.
Qed.

End BridgeA.
