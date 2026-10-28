(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive
  RefMemcpyLib AgentLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SymAux RefPrintfLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PrintfBufBase_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Definition pf_stops : list Z := [0x395f8].
Definition pf_fuel : nat := 3000.

Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0xc4c58, 4); (SA (ELit 0) 0xc4c80, 8); (SA (EVar 1) 0, 2)].

Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x396a4) mem rom) (mkst regs' (Z_to_bv 64 0x395f8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xc4c58, 4);
                          (Z_to_bv 64 0xc4c80, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0xc4c80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0xc4c58) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x395f8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
  Proof.
    intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
    rewrite u64_lit by lia. f_equal; lia.
  Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
  Proof.
    intros k. destruct PH. unfold adenot. cbn [a_base a_off edenot].
    change (ev E 1) with (Z_to_bv 64 w). unfold v_addi. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x396a4 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x395f8 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0xc4c80 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0xc4c58 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
  Proof.
    intros dirs ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
    pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
    pose proof (pf_know_ok regs mem sp w can PH) as HK.
    fold E in HR, HK.
    destruct (run_sound RSEGS pf_fuel pf_stops (SCR dirs [] []) 0x396a4 pf_sr pf_kn 40 ss' scs scr' E mem rom regs
                Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite Hpc in Hms.
    assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Hw1 : ev E 1 = Z_to_bv 64 w) by reflexivity.
    exists R', (mem_denot E mem (s_log ss')).
    split; [exact Hms|]. split; [|split; [|split; [|split]]].
    - eapply (keeps_cs_of_same E); eassumption.
    - replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xc4c58, 4);
               (Z_to_bv 64 0xc4c80, 8); (Z_to_bv 64 w, 2)]
        with (map (rdenot E) pf_regions).
      2:{ unfold pf_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. rewrite Hw1, Z0, (u64_lit w) by lia.
          repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold pf_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
        try change (ev E 0) with sp; rewrite ?Hw1, ?Z0, ?(u64_lit w) by lia; lia.
    - pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 0 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
      pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 1 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
      rewrite adenot_var1 in B0, B1.
      apply rdn_2.
      + rewrite u64_lit by lia. lia.
      + rewrite Z.add_0_r in B0. apply B0.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
      + rewrite u64_lit by lia. apply B1.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0xc4c80 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0xc4c58 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.
End FPX_1.

Ltac sc_bool :=
  match goal with
  | Hw4 : ?w mod 4 = ?r |- _ =>
      first [ rewrite (mod4_shift w _ r Hw4); reflexivity
            | rewrite Hw4; reflexivity ]
  end.

Ltac sc_pf :=
  cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
  first
    [ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
    | apply bt_and3; [lia | cbv beta iota; sc_bool]
    | apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].
Section FPX_2. Context {fx : PropExec.FPState}.

Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x396a4 pf_sr [] pf_kn 40) [].

Definition dirsA : list bool := [false; false; false; true; false].
Definition dirsB : list bool := [true; true; true; true; true].

Definition dirsC : list bool := [true; true; true; true; false].
Definition dirsD : list bool := [true; true; true; false; false].

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).
End FPX_2.

Ltac run_case dirs res car :=
  lazymatch goal with
  | PH : pfH ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
      eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | let v := eval vm_compute in (snd (fst res)) in
        change (snd (fst res)) with v;
        destruct PH; split_scs; sc_pf ]
  end.
Section FPX_3. Context {fx : PropExec.FPState}.

Lemma pf_caseA : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x395f8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.

Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x395f8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.

Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x395f8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.

Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x395f8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.

Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x395f8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x396a4) mem rom) (mkst regs' (Z_to_bv 64 0x395f8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xc4c58, 4);
                          (Z_to_bv 64 0xc4c80, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0xc4c80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0xc4c58) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
  intros regs mem rom sp w can PH R1 R2 R11.
  destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
  - exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
  - exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
  - exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
  - exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.
End FPX_3.

