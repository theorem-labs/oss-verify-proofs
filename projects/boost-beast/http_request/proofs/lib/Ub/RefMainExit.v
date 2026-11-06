(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Hoare LibTail StepTac WalkTac Spec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefExitBase RefStdioDefs RefExit RefPrintfBufBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPSX : list Z := [0x6bba4]%Z.
Definition FUELX : nat := 100.
Definition scr0 : scripts := SCR [] [] [].

(* [comment removed for export] *)
Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with 0 => ELit 0%Z | 2 => EVar 0 | _ => EVar (9 + i) end)%nat (seq 0 32)).

Definition x_kn : list kentry :=
  [KRange (EVar 0) 0x1000 0x7fffffffffff;
   KWord (SA (EVar 0) 8) 8 (EVar 1); KWord (SA (EVar 0) 16) 8 (EVar 2);
   KWord (SA (EVar 0) 24) 8 (EVar 3); KWord (SA (EVar 0) 32) 8 (EVar 4);
   KWord (SA (EVar 0) 40) 8 (EVar 5); KWord (SA (EVar 0) 48) 8 (EVar 6);
   KWord (SA (EVar 0) 56) 8 (EVar 7); KWord (SA (EVar 0) 64) 8 (EVar 8);
   KWord (SA (EVar 0) 72) 8 (ELit 0x6b4a4)]%Z.

Definition x_r := Eval vm_compute in (sym_exec RSEGS FUELX true STOPSX scr0 (SS 0x2bce8 x_sr [] x_kn 41) []).
Definition x_c := Eval vm_compute in (carry (s_log (fst (fst x_r))) x_kn []).
Definition x_srF : list expr := Eval vm_compute in (s_regs (fst (fst x_r))).

Lemma x_itinerary :
  s_pc (fst (fst x_r)) = 0x6bba4%Z /\ snd (fst x_r) = [] /\ snd (fst x_c) = [] /\ s_log (fst (fst x_r)) = []
  /\ nth 2 x_srF (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit 80) /\ nth 4 x_srF (ELit 0) = EVar 13
  /\ nth 10 x_srF (ELit 0) = EVar 17.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MainExit.
  Variable model : Model.

  (* [comment removed for export] *)
  Record main_frame (mem : word -> option byte) (sp : word) (slots : list word) : Prop := MF {
    mf_len : length slots = 8%nat;
    mf_slots : forall i, (i < 8)%nat ->
        rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (nth i slots (Z_to_bv 64 0)));
    mf_ra : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp + 72)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6b4a4));
    mf_lo : (0x1000 <= bv_unsigned sp)%Z;
    mf_hi : (bv_unsigned sp <= 0x7fffffffffff)%Z }.

  Definition x_vals (regs : bvmap 5 word) (sp : word) (slots : list word) : list word :=
    [sp] ++ slots ++ junk_vals regs.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

  Lemma x_ev_junk : forall regs sp slots i, length slots = 8%nat -> (9 <= i < 41)%nat ->
    ev (ENV (x_vals regs sp slots)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 9))).
  Proof.
    intros regs sp slots i HL Hi. unfold ENV, x_vals. cbn [ev]. unfold vals_ev.
    rewrite app_assoc.
    replace i with (length ([sp] ++ slots) + (i - 9))%nat at 1 by (rewrite length_app, HL; cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  
  Qed.

  Lemma x_ev_slot : forall regs sp slots i, length slots = 8%nat -> (i < 8)%nat ->
    ev (ENV (x_vals regs sp slots)) (S i) = nth i slots (Z_to_bv 64 0).
  Proof.
    intros regs sp slots i HL Hi. unfold ENV, x_vals. cbn [ev]. unfold vals_ev.
    change ([sp] ++ slots ++ junk_vals regs) with (sp :: (slots ++ junk_vals regs)). cbn [nth].
    rewrite app_nth1 by (rewrite HL; exact Hi). apply nth_indep. rewrite HL; exact Hi.
  Qed.

  Lemma x_regs_ok : forall regs mem sp slots, getr regs 2 = sp -> main_frame mem sp slots ->
    regs_ok (ENV (x_vals regs sp slots)) x_sr regs.
  Proof.
    intros regs mem sp slots Hsp MFH. destruct MFH as [HL _ _ _ _].
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth x_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; exact Hsp.
    all: rewrite x_ev_junk by (exact HL || lia); f_equal; apply bv_eq; reflexivity.
  
  Qed.

  Lemma x_know_ok : forall regs mem sp slots, main_frame mem sp slots ->
    know_ok RSEGS (ENV (x_vals regs sp slots)) mem x_kn.
  Proof.
    intros regs mem sp slots MFH. destruct MFH as [HL HS HRA Hlo Hhi]. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (x_vals regs sp slots)) 0 = sp) by reflexivity.
    unfold x_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply krange_intro. cbn [edenot]. rewrite E0. lia.
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 0 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 8)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 0)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 1 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 16)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 1)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 2 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 24)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 2)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 3 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 32)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 3)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 4 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 40)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 4)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 5 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 48)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 5)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 6 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 56)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 6)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 7 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 64)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 7)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | reflexivity | lia | lia | lia | lia | exact HRA].
  
  Qed.

  (* [comment removed for export] *)
  Theorem main_return_exit : forall regs mem (sp status : word) slots pending,
    getr regs 2 = sp -> getr regs 8 = status ->
    main_frame mem sp slots ->
    (forall regs', getr regs' 2 = Z_to_bv 64 (bv_unsigned sp + 80) -> getr regs' 4 = getr regs 4 ->
                   getr regs' 10 = status -> exit_pre regs' mem model status pending) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2bce8) mem (seg_rom RSEGS)) model)
             (t_emit (W 1 pending) (t_exit (bv_and status (Z_to_bv 64 255)) (m_fs model))).
  Proof.
    intros regs mem sp status slots pending Hsp Hs0 MFH HPRE.
    pose proof (x_regs_ok regs mem sp slots Hsp MFH) as HR.
    pose proof (x_know_ok regs mem sp slots MFH) as HK.
    destruct MFH as [HL _ _ Hlo Hhi]. pose proof (u64_range sp) as Hspr.
    (* [comment removed for export] *)
    destruct (HPRE (regupd (regupd (regupd regs 2 (Z_to_bv 64 (bv_unsigned sp + 80))) 4 (getr regs 4)) 10 status))
      as (sp' & tp' & tid & wp2 & rp2 & _ & Hh & Hlazy & _); [gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    eapply (rz_run RSEGS FUELX STOPSX scr0 0x2bce8 x_sr x_kn 41 (fst (fst x_r)) (snd (fst x_r)) (snd x_r)
              (fst (fst x_c)) (snd (fst x_c)) (snd x_c) (ENV (x_vals regs sp slots)) mem (seg_rom RSEGS) regs model);
      [ vm_cast_no_check (@eq_refl _ x_r) | vm_cast_no_check (@eq_refl _ x_c)
      | exact HR | exact HK | apply Forall_nil | apply Forall_nil | exact Hh | exact Hlazy | ].
    clear HR HK. intros R' M' HR HK EQM.
    change (s_pc (fst (fst x_r))) with 0x6bba4%Z. change (s_regs (fst (fst x_r))) with x_srF in HR.
    assert (EM : M' = mem) by (rewrite EQM; reflexivity). rewrite EM. clear EQM EM.
    apply ref_exit_Z. apply HPRE.
    - regv HR (2 : reg). cbn [edenot ev ENV]. rewrite alu_add, vadd_wZ. reflexivity.
    - regv HR (4 : reg). cbn [edenot]. rewrite (x_ev_junk regs sp slots 13 HL) by lia. f_equal; apply bv_eq; reflexivity.
    - regv HR (10 : reg). cbn [edenot]. rewrite (x_ev_junk regs sp slots 17 HL) by lia. rewrite <- Hs0. f_equal; apply bv_eq; reflexivity.
  Qed.
End MainExit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
