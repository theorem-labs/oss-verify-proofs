(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from MainOpen.v: main's argc <> 2 segment (seg_U) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout StepTac
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux
  Spec RefNodes RefStartup RefStartupFacts RefMainEntry RefMainEntryN LibTail LibDiagKn RefPrintfFirst
  MainDefs MainWalk_defs MainSegs.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import MainOpen.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb AgentNodesB NodesB LibWritevB RefNodesB SymDriveB.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import RefPrintfFirstB.
Open Scope bv_scope.

Section Usage.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable model0 : Model.
  (* As MainOpen.v's Section Usage: [main_entry] is a record over the run's input
     ([RefStartup.v:82]), and the launch facts are parameters, with [av]/[envv] tied to
     [inp] by [Hargv]/[Henvp]. *)
  Variable inp : ProcInput.
  Variables (mbase brk entryw : word).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Henvp : in_envp inp = envv.
  Hypothesis Hvl  : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
  Hypothesis Hargc : length av <> 2%nat.
  Hypothesis Hh0 : m_halted model0 = None.
  Hypothesis Hlazy0 : m_vm_lazy model0 = [].

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Definition regU_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 128), 80%Z)].

  Definition frameU (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x67178))
    /\ (exists w : word, rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 64)) 8 = Some (word_to_le_bytes 8 w))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 72)) 8 = Some (word_to_le_bytes 8 (getr R 9))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 80)) 8 = Some (word_to_le_bytes 8 (getr R 18))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 88)) 8 = Some (word_to_le_bytes 8 (getr R 19))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 96)) 8 = Some (word_to_le_bytes 8 (getr R 20))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 104)) 8 = Some (word_to_le_bytes 8 (getr R 21))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 112)) 8 = Some (word_to_le_bytes 8 (getr R 22))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 120)) 8 = Some (word_to_le_bytes 8 (getr R 23)).

  Lemma seg_U_b : forall T,
    (forall R M,
       getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 0x92650 -> getr R 8 = Z_to_bv 64 2 ->
       getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
       frame_mod mem0 M regU_w -> frameU R M ->
       rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0)) ->
       rzb RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ae00) M (seg_rom RSEGS)) model0) T) ->
    rzb RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x2ac68) mem0 (seg_rom RSEGS)) model0) T.
  Proof using All.
    intros T HU. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    (* [RefMainEntryN]'s exports are over the input ([RefMainEntryN.v:31-56]). *)
    assert (Hva_in : valid_argv (in_argv inp)) by (rewrite Hargv; exact Hva).
    assert (Hve_in : valid_envp (in_envp inp)) by (rewrite Henvp; exact Hve).
    pose proof (main_regs_okN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME) as HR.
    pose proof (main_know_okN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME) as HK.
    pose proof (evN_argc inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME) as Hac.
    change (EN inp sp0 rdraw tid regs0) with (ENVU (valsN inp sp0 rdraw tid regs0)) in HR, HK, Hac.
    set (vals := valsN inp sp0 rdraw tid regs0) in *.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0).
    { change (vals_ev vals 1) with (p0N inp rdraw). unfold p0N. rewrite Hargv, Henvp. reflexivity. }
    assert (PJ : forall i, (i < 32)%nat -> vals_ev vals (6 + i) = getr regs0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. exact (evN_junk inp sp0 rdraw tid regs0 i Hi). }
    cbn [ev ENVU] in Hac.
    clearbody vals.
    eapply (rzb_run_lf RSEGS FUELM STOPSM scrU 0x2ac68%Z sr_mainN kn_mainN 40%nat (fst (fst rU)) (snd (fst rU)) (snd rU)
              (fst (fst cU)) (snd (fst cU)) (snd cU) (ENVU vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rU) | vm_cast_no_check (@eq_refl _ cU) | exact HR | exact HK
      | | apply Forall_nil | exact Hh0 | exact Hlazy0 | ].
    { 
      lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. unfold sc_denot. cbn [branch_taken edenot ev ENVU]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN inp Hva_in), Hargv. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R M HR' HK' EQM LF. rewrite cU_knU in HK'.
    change (s_pc (fst (fst rU))) with 0x2ae00%Z. change (s_regs (fst (fst rU))) with srU in HR'.
    assert (RF : regions_flat (ENVU vals) regU).
    { intros r Hr. unfold regU in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENVU]. rewrite P0. lia. }
    pose proof (log_covered_frame (ENVU vals) mem0 regU _ covU RF LF) as FR. rewrite <- EQM in FR.
    unfold regU, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENVU] in FR. rewrite P0 in FR.
    replace (bv_unsigned sp0 + -128)%Z with (bv_unsigned sp0 - 128)%Z in FR by lia.
    apply (HU R M).
    - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - regv HR' (4:reg). reflexivity.
    - regv HR' (8:reg). reflexivity.
    - regv HR' (11:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - exact FR.
    - 
      unfold frameU.
      repeat split.
      + krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 56)%Z with (bv_unsigned sp0 + -56)%Z by lia. exact Hrd.
      + eexists. krdv HK' 0%nat (-64)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 64)%Z with (bv_unsigned sp0 + -64)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-72)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (9:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 72)%Z with (bv_unsigned sp0 + -72)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-80)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (18:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 80)%Z with (bv_unsigned sp0 + -80)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-88)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (19:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 88)%Z with (bv_unsigned sp0 + -88)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-96)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (20:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 96)%Z with (bv_unsigned sp0 + -96)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-104)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (21:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 104)%Z with (bv_unsigned sp0 + -104)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-112)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (22:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 112)%Z with (bv_unsigned sp0 + -112)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-120)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (23:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 120)%Z with (bv_unsigned sp0 + -120)%Z by lia. exact Hrd.
    - 
      krdv HK' 0%nat 8%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
      unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0, P1 in Hrd. exact Hrd.
  Qed.

  (* As MainOpen.v's [arg0_facts]: the pointer is the launch's ([CatExec.v:332-334]) and its
     ceiling is [+ 8], the model's chain argv_ptr_room / length_entry_stack_image_launch /
     entry_page_top_within_window. *)
  Lemma arg0_facts :
    rdn RSEGS mem0 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) (length (nth 0 av []) + 1) = Some (nth 0 av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth 0 av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])))) 8 = Some t8)
    /\ (entry_stack_fits sp0 av envv -> (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])) + 8 <= 0x800000000000)%Z)
    /\ ~ In (Z_to_bv 8 0) (nth 0 av []).
  Proof using Hva Hve Hvsp Htid Hargv Henvp Hvl Hlau ME.
    (* [lia] below must not read the section's [Hargc], which this lemma does not take *)
    try clear Hargc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (Hva_in : valid_argv (in_argv inp)) by (rewrite Hargv; exact Hva).
    assert (Hve_in : valid_envp (in_envp inp)) by (rewrite Henvp; exact Hve).
    assert (Hk : (0 < length (in_argv inp))%nat) by (rewrite Hargv; lia).
    destruct (main_strN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME 0%nat Hk)
      as (Sr & Slo & Shi & Slen & St8).
    pose proof (MuslStrlen.argv_ptr_room Sv48 inp mbase RPH entryw sp0 brk rdraw) as Hroom.
    repeat lazymatch type of Hroom with
           | ?P -> _ =>
               let h := fresh "Hd" in
               assert (h : P) by
                 first [ exact Hva_in | exact Hve_in | exact Hvl | exact Hlau
                       | unfold sp_window_lo; lia
                       | unfold sp_window_hi; lia ];
               specialize (Hroom h); clear h
           end.
    specialize (Hroom 0%nat Hk).
    pose proof (length_entry_stack_image_launch Sv48 inp mbase RPH entryw sp0 brk rdraw Hlau) as Himg.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp0 brk rdraw Hlau) as Htop.
    unfold entry_page_top, va_stack_top, sp_window_hi in Htop.
    rewrite Hargv, Henvp in Sr, Slo, Shi, St8, Hroom. rewrite Hargv in Slen.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split; [exact Slen|]. split; [exact St8|]. split.
    - intros _. lia.
    - destruct Hva as (_ & _ & _ & Hn & _). apply (proj1 (Forall_forall _ _) Hn). apply nth_In. lia.
  Qed.
End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
