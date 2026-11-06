(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Stqgu D_Exvwg RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit RefPl89.

Module D_Prxvr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Exvwg.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk Frame Stre9ts SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive RefMocc AgentLib.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import SymAux RefPl89.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition PF_FR : Z := 1056.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : 0x63420 <= bv_unsigned sp;   (* [comment removed for export] *)
  PspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Pstk   : stk_ok RSEGS mem sp PF_FR;
  Pimg   : forall i, 0x10000 <= i < 0x31458 -> mem (Z_to_bv 64 i) = None;   (* [comment removed for export] *)
  Pflags : rdn RSEGS mem (Z_to_bv 64 0x31698) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  Pwend  : rdn RSEGS mem (Z_to_bv 64 0x316b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62c58));
  Pwpos  : rdn RSEGS mem (Z_to_bv 64 0x316c0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  Pw     : 0x62858 <= w <= 0x62c56;
  Pbsz   : rdn RSEGS mem (Z_to_bv 64 0x316f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  Plock  : rdn RSEGS mem (Z_to_bv 64 0x31724) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Plbf   : rdn RSEGS mem (Z_to_bv 64 0x31728) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Pcan   : rdn RSEGS mem (Z_to_bv 64 0x623c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Pcan64 : 0 <= can < 2 ^ 64 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pf_vals (regs : bvmap 5 word) (sp : word) (w can : Z) : list word :=
  [sp; Z_to_bv 64 w; Z_to_bv 64 can] ++ junk_vals regs.

Definition pfE (regs : bvmap 5 word) (sp : word) (w can : Z) : env :=
  Env (vals_ev (pf_vals regs sp w can)) (blobs_ev []).

Definition pf_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x17f10 | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition pf_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x63420 0x7fffffffffff;
   KWr (SA (EVar 0) (-1056)) 1056;
   KImg 0x10000 0x31458;
   KWord (SA (ELit 0) 0x31698) 4 (ELit 5);
   KWord (SA (ELit 0) 0x316b8) 8 (ELit 0x62c58);
   KWord (SA (ELit 0) 0x316c0) 8 (EVar 1);
   KRange (EVar 1) 0x62858 0x62c56;
   KWord (SA (ELit 0) 0x316f8) 8 (ELit 1024);
   KWord (SA (ELit 0) 0x31724) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x31728) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x623c8) 8 (EVar 2);
   KWr (SA (ELit 0) 0x31000) 0x32000;   (* [comment removed for export] *)
   KWr (SA (EVar 1) 0) 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allregs32 : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_allregs32 : forall n, (n < 32)%nat -> nth n allregs32 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_idx : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i allregs32 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_allregs32 in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section Entry.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x17f10.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros i Hi. unfold E, pfE, pf_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 w; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = Z_to_bv 64 w. Proof. reflexivity. Qed.
  Lemma ev2 : ev E 2 = Z_to_bv 64 can. Proof. reflexivity. Qed.

  Lemma pf_regs_ok : regs_ok E pf_sr regs.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth pf_sr allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x31000) 204800 = true.
  Proof. (* [comment removed for export] *)
    exact D_Exvwg.ref_wseg_1c. Qed.

  Lemma data_store_ok : forall m a n,
    0x31000 <= a -> a + Z.of_nat n <= 0x63000 -> store_ok RSEGS m (Z_to_bv 64 a) n = true.
  Proof.
    intros m a n Ha Hn.
    eapply (store_ok_window RSEGS m (Z_to_bv 64 0x31000) (Z_to_bv 64 a) 204800 n 0x31000 0x63000);
      [ apply u64_lit; lia | reflexivity | cbn; lia | apply wseg_data
      | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia ].
  Qed.

  Lemma pf_know_ok : know_ok RSEGS E mem pf_kn.
  Proof.
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold pf_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev0. lia.
    - apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1056); [apply ev0 | exact Pstk0 | unfold PF_FR; lia].
    - apply kimg_intro; [lia | lia | exact Pimg0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pflags0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwend0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwpos0].
    - apply krange_intro. cbn [edenot]. rewrite ev1, u64_lit by lia. lia.
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pbsz0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plock0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plbf0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev2 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pcan0].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite ev1, u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.
End Entry.
End D_Prxvr.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Fip9g.D_Prxvr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.

Module D_Przzp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk Frame Stre9ts SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive RefMocc AgentLib.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymAux RefPl89.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Fip9g.D_Prxvr.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition pf_stops : list Z := [0x17f10].
Definition pf_fuel : nat := 3000.

(* [comment removed for export] *)
Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0x31698, 4); (SA (ELit 0) 0x316c0, 8); (SA (EVar 1) 0, 2)].

(* [comment removed for export] *)
Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x17fbc) mem rom) (mkst regs' (Z_to_bv 64 0x17f10) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x31698, 4);
                          (Z_to_bv 64 0x316c0, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x316c0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x31698) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x17f10.
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
    sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x17fbc pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x17f10 ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0x316c0 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread RSEGS kn' (ELit 0) 0x31698 4 = Some (ELit 5) ->
    kread RSEGS kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread RSEGS kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot RSEGS mem E scs ->
    pf_post regs mem rom sp w.
  Proof.
    intros dirs ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
    pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
    pose proof (pf_know_ok regs mem sp w can PH) as HK.
    fold E in HR, HK.
    destruct (run_sound RSEGS pf_fuel pf_stops (SCR dirs [] []) 0x17fbc pf_sr pf_kn 40 ss' scs scr' E mem rom regs
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
    - replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x31698, 4);
               (Z_to_bv 64 0x316c0, 8); (Z_to_bv 64 w, 2)]
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
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x316c0 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x31698 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x17fbc pf_sr [] pf_kn 40) [].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dirsA : list bool := [false; true; false; true; false].  (* [comment removed for export] *)
Definition dirsB : list bool := [true; false; true; true; true].    (* [comment removed for export] *)

Definition dirsC : list bool := [true; false; true; true; false].   (* [comment removed for export] *)
Definition dirsD : list bool := [true; false; true; false; false].  (* [comment removed for export] *)

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).

(* [comment removed for export] *)
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

Lemma pf_caseA : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x17f10 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.

Lemma pf_caseB : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x17f10 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.

Lemma pf_caseC : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x17f10 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.

Lemma pf_caseD : forall regs mem rom sp w can,
  pfH mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x17f10 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem printf0_buffered : forall regs mem rom (sp : word) (w can : Z),
  pfH mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x17f10 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x17fbc) mem rom) (mkst regs' (Z_to_bv 64 0x17f10) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x31698, 4);
                          (Z_to_bv 64 0x316c0, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x316c0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x31698) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
  intros regs mem rom sp w can PH R1 R2 R11.
  destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
  - exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
  - exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
  - exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
  - exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.

End D_Przzp.


Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition FP1_FR : Z := 1200.
(* [comment removed for export] *)
Definition STDOUT_F : Z := 0x31698.
Definition STDOUT_BUF : Z := 0x62858.

(* [comment removed for export] *)
Definition STOPS1 : list Z := [0x25d58; 0x17f10]%Z.
Definition FUEL1 : nat := 5000.
Definition scr1 : scripts := SCR [] [] [].
Definition run1 (ss : sym_state) := sym_exec RSEGS FUEL1 true STOPS1 scr1 ss [].
Definition kn_after1 (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Tactic Notation "run_block1" constr(NX) := run_block_gen FUEL1 STOPS1 scr1 NX false.
Tactic Notation "run_block1_keep" constr(NX) := run_block_gen FUEL1 STOPS1 scr1 NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp1_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
  [sp; Z_to_bv 64 can] ++ junk_vals regs.
Definition fp1E (regs : bvmap 5 word) (sp : word) (can : Z) : env :=
  Env (vals_ev (fp1_vals regs sp can)) (blobs_ev []).

Definition fp1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x17f10 | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

Definition fp1_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x200000000 0x7fffffffffff;
   KWr (SA (EVar 0) (- FP1_FR)) FP1_FR;
   KImg 0x10000 0x31458;
   KImg STDOUT_F (STDOUT_F + 232);
   KWord (SA (ELit 0) 0x623c8) 8 (EVar 1);
   KWr (SA (ELit 0) 0x31000) 0x32000]   (* [comment removed for export] *).

(* [comment removed for export] *)
Definition fp1_regions : list sregion :=
  [(SA (EVar 0) (- FP1_FR), FP1_FR); (SA (ELit 0) STDOUT_F, 232%Z); (SA (ELit 0) STDOUT_BUF, 1%Z)].

(* [comment removed for export] *)
Definition ss1 : sym_state := SS 0x17fbc fp1_sr [] fp1_kn 34.
Definition r1 := Eval vm_compute in run1 ss1.
Definition sr1 : list expr := Eval vm_compute in s_regs (fst (fst r1)).
Definition kn1 : list kentry := Eval vm_compute in kn_after1 r1 fp1_kn.
Definition log1 : list sentry := Eval vm_compute in s_log (fst (fst r1)).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ENOTTY_RET : Z := 0xffffffffffffffe7.
Definition sr2_0 : list expr := Eval vm_compute in sr_upd sr1 (ridx 10) (ELit ENOTTY_RET).
Definition ss2 : sym_state := SS 0x25f50 sr2_0 [] kn1 34.
Definition r2 := Eval vm_compute in run1 ss2.
Definition sr2 : list expr := Eval vm_compute in s_regs (fst (fst r2)).
Definition kn2 : list kentry := Eval vm_compute in kn_after1 r2 kn1.
Definition log2 : list sentry := Eval vm_compute in s_log (fst (fst r2)).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition res3 : stdio_res := Eval vm_compute in
  match stdio_call 34 sr2 kn2 with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma res3_eq : stdio_call 34 sr2 kn2 = Some res3.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition sr3_0 : list expr := Eval vm_compute in sc_sr res3.
Definition kn3_0 : list kentry := Eval vm_compute in sc_kn res3.
Definition ss3 : sym_state := SS (sc_ret res3) sr3_0 [] kn3_0 66.
Definition r3 := Eval vm_compute in run1 ss3.
Definition sr3 : list expr := Eval vm_compute in s_regs (fst (fst r3)).
Definition kn3 : list kentry := Eval vm_compute in kn_after1 r3 kn3_0.
Definition log3 : list sentry := Eval vm_compute in s_log (fst (fst r3)).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cov1 : log_covered fp1_regions log1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cov2 : log_covered fp1_regions log2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cov3 : log_covered fp1_regions log3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma same3 : same_regs fp1_sr sr3 callee_saved = true. Proof. vm_compute. reflexivity. Qed.
Lemma w18_1 : log_w18 log1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma w18_2 : log_w18 log2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma w18_3 : log_w18 log3 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fp1_regions_flat : forall vals ebs, (FP1_FR <= bv_unsigned (vals_ev vals 0))%Z ->
  regions_flat (Env (vals_ev vals) ebs) fp1_regions.
Proof.
  intros vals ebs Hsp r Hr. pose proof (u64_range (vals_ev vals 0)).
  unfold fp1_regions, FP1_FR, STDOUT_F, STDOUT_BUF in *. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev];
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
Qed.

Lemma fp1_outside : forall vals ebs (x : word), (FP1_FR <= bv_unsigned (vals_ev vals 0))%Z ->
  ~ (bv_unsigned (vals_ev vals 0) - FP1_FR <= bv_unsigned x < bv_unsigned (vals_ev vals 0))%Z ->
  ~ (STDOUT_F <= bv_unsigned x < STDOUT_F + 232)%Z ->
  bv_unsigned x <> STDOUT_BUF ->
  outside x (map (rdenot (Env (vals_ev vals) ebs)) fp1_regions).
Proof.
  intros vals ebs x Hsp N1 N2 N3. pose proof (u64_range (vals_ev vals 0)).
  unfold fp1_regions, FP1_FR, STDOUT_F, STDOUT_BUF in *. cbn [map outside rdenot fst snd].
  unfold in_rng, estart. cbn [a_base a_off edenot ev]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite (u_small (bv_unsigned (vals_ev vals 0) + - (1200))) by lia. lit_u. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record fp1H (mem : word -> option byte) (sp : word) (can : Z) : Prop := FP1H {
  F1sp16  : (bv_unsigned sp mod 16 = 0)%Z;
  F1spLo  : (0x200000000 <= bv_unsigned sp)%Z;
  F1spHi  : (bv_unsigned sp <= 0x7fffffffffff)%Z;
  F1stk   : stk_ok RSEGS mem sp FP1_FR;
  F1img   : forall i, (0x10000 <= i < 0x31458)%Z -> mem (Z_to_bv 64 i) = None;
  F1file  : forall i, (STDOUT_F <= i < STDOUT_F + 232)%Z -> mem (Z_to_bv 64 i) = None;
  F1can   : rdn RSEGS mem (Z_to_bv 64 0x623c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  F1can64 : (0 <= can < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Record fp1_post (mem mem' : word -> option byte) (sp : word) : Prop := FP1P {
  P1agree : forall x : word,
      ~ (bv_unsigned sp - FP1_FR <= bv_unsigned x < bv_unsigned sp)%Z ->
      ~ (STDOUT_F <= bv_unsigned x < STDOUT_F + 232)%Z ->
      bv_unsigned x <> STDOUT_BUF ->
      mem' x = mem x;
  P1grows : mem_grows mem mem';
  P1flags : rdn RSEGS mem' (Z_to_bv 64 0x31698) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  P1rpos  : rdn RSEGS mem' (Z_to_bv 64 0x316a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  P1rend  : rdn RSEGS mem' (Z_to_bv 64 0x316a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  P1wend  : rdn RSEGS mem' (Z_to_bv 64 0x316b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62c58));
  P1wpos  : rdn RSEGS mem' (Z_to_bv 64 0x316c0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62858));
  P1wbase : rdn RSEGS mem' (Z_to_bv 64 0x316d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62858));
  P1write : rdn RSEGS mem' (Z_to_bv 64 0x316e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x25d58));
  P1buf   : rdn RSEGS mem' (Z_to_bv 64 0x316f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62858));
  P1bsz   : rdn RSEGS mem' (Z_to_bv 64 0x316f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  P1fd    : rdn RSEGS mem' (Z_to_bv 64 0x31710) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  P1lock  : rdn RSEGS mem' (Z_to_bv 64 0x31724) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  P1lbf   : rdn RSEGS mem' (Z_to_bv 64 0x31728) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) }.

Section Run.
  Context {AMB : Amb}.
  Context {BW : BWorld}.
  Variables (R : bvmap 5 word) (M : word -> option byte) (md : Model) (sp : word) (can : Z).
  Hypothesis PH : fp1H M sp can.
  Hypothesis R1 : getr R 1 = Z_to_bv 64 0x17f10.
  Hypothesis R2 : getr R 2 = sp.
  Hypothesis R11 : getr R 11 = Z_to_bv 64 0.
  Hypothesis Hfd1 : fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Hypothesis Hh : m_halted md = None.
  Hypothesis Hlazy : m_vm_lazy md = [].

  Definition vals1 : list word := fp1_vals R sp can.
  Lemma vals1_len : length vals1 = 34%nat.
  Proof. unfold vals1, fp1_vals. rewrite length_app, junk_vals_length. reflexivity. Qed.
  Lemma ev0 : vals_ev vals1 0 = sp. Proof. reflexivity. Qed.
  Lemma ev1 : vals_ev vals1 1 = Z_to_bv 64 can. Proof. reflexivity. Qed.

  Lemma ev_junk : forall i, (2 <= i < 34)%nat -> vals_ev vals1 i = getr R (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros i Hi. unfold vals1, fp1_vals, vals_ev.
    replace i with (length [sp; Z_to_bv 64 can] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma fp1_regs_ok : regs_ok (Env (vals_ev vals1) (blobs_ev [])) fp1_sr R.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth fp1_sr allregs32 edenot ev].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma fp1_know_ok : know_ok RSEGS (Env (vals_ev vals1) (blobs_ev [])) M fp1_kn.
  Proof.
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold fp1_kn, FP1_FR, STDOUT_F in *. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot ev]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot ev]. rewrite ev0. lia.
    - apply (kwr_of_stk_ok RSEGS _ M (EVar 0) sp 1200); [apply ev0 | assumption | lia].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kword_intro RSEGS _ M (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10ac6) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Theorem first_printf : forall K,
    K [] ->
    (forall R' M', keeps_cs R R' -> fp1_post M M' sp ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f10) M' (seg_rom RSEGS)) md) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17fbc) M (seg_rom RSEGS)) md)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
  Proof.
    intros K HKnil HCONT.
    pose proof fp1_regs_ok as HR. pose proof fp1_know_ok as HK.
    pose proof PH as [Hsp16 HspLo HspHi Hstk Himg Hfile Hcan Hcan64]. pose proof (u64_range sp) as Hsp.
    set (vals := vals1) in *.
    assert (HL : length vals = 34%nat) by apply vals1_len.
    assert (P0 : vals_ev vals 0 = sp) by reflexivity.
    (* [comment removed for export] *)
    run_block1_keep 34%nat.
    rename EQM into EQM1.
    (* [comment removed for export] *)
    eapply (rz_ioctl_winsz RSEGS _ _ _ md ECALLW (Z_to_bv 64 1)); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - exact Hh.
    - exact Hlazy.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - rewrite u_small by lia. lia.
    - exact Hfd1.
    - regv HR (11 : reg). reflexivity.
    - rewrite v_addi_pc4 by lia. change (0x25f4c + 4)%Z with 0x25f50%Z.
      pose proof (regs_set_a0 _ _ _ (errno_ret ENOTTY) (ELit ENOTTY_RET) HR ltac:(apply bv_eq; reflexivity)) as HR2.
      clear HR. rename HR2 into HR.
      change (sr_upd sr1 (ridx 10) (ELit ENOTTY_RET)) with sr2_0 in HR.
      (* [comment removed for export] *)
      run_block1_keep 34%nat.
      rename EQM into EQM2.
      (* [comment removed for export] *)
      apply (stdio_call_sound_frame vals (blobs_ev []) sr2 kn2 _ _ md res3 [Z_to_bv 8 48] [Z_to_bv 8 10] K HR HK
               (eq_trans (f_equal (fun n => stdio_call n sr2 kn2) HL) res3_eq));
        cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res3];
        change (Z.of_nat (@length byte [Z_to_bv 8 48])) with 1%Z; change (Z.of_nat (@length byte [Z_to_bv 8 10])) with 1%Z.
      + cbn [edenot]. lit_u. lia.
      + cbn [edenot]. lit_u. lia.
      + cbn [edenot]. lit_u. reflexivity.
      + lia.
      + left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0.
        lit_u. rewrite u_small by lia. lia.
      + left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0.
        lit_u. rewrite u_small by lia. lia.
      + cbn [edenot]. lit_u. lia.
      + (* [comment removed for export] *)
        cbn [edenot]. lit_u. change (@length byte [Z_to_bv 8 48]) with 1%nat. krd_solve HK.
      + (* [comment removed for export] *)
        cbn [edenot]. change (@length byte [Z_to_bv 8 10]) with 1%nat.
        rewrite (kimg_rdn RSEGS _ _ kn2 ltac:(let i := kidx kn2 (is_kimg_cov 0x10ac6 1) in exact i)
                   _ _ 0x10ac6 1 HK eq_refl) by (cbn; lia).
        apply nl_img.
      + exact Hfd1.
      + exact Hh.
      + exact Hlazy.
      + exact HKnil.
      + (* [comment removed for export] *)
        intros Rw Mw HR3 HK3 HPOST.
        change (sc_sr res3) with sr3_0 in HR3. change (sc_kn res3) with kn3_0 in HK3.
        set (vals' := vals ++ junk_vals Rw) in *.
        assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
        assert (P0' : vals_ev vals' 0 = sp) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        clear HR HK. rename HR3 into HR. rename HK3 into HK.
        run_block1_keep 66%nat.
        rename EQM into EQM3.
        (* [comment removed for export] *)
        set (E := Env (vals_ev vals) (blobs_ev [])) in *. set (E' := Env (vals_ev vals') (blobs_ev [])) in *.
        assert (RF : regions_flat E fp1_regions) by (apply fp1_regions_flat; rewrite P0; unfold FP1_FR; lia).
        assert (RF' : regions_flat E' fp1_regions) by (apply fp1_regions_flat; rewrite P0'; unfold FP1_FR; lia).
        apply HCONT.
        * (* [comment removed for export] *)
          eapply (keeps_cs_of_same E' fp1_sr sr3 R _ same3); [| exact HR].
          subst E' vals'. apply env_app_regs; [rewrite HL; reflexivity | exact fp1_regs_ok].
        * destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
          rewrite edenot_add_lit in Pagree. unfold adenot, v_addi in Pagree. cbn [a_base a_off] in Pagree.
          change (edenot E (EVar 0)) with (vals_ev vals 0) in Pagree.
          rewrite P0 in Pagree. rewrite (u_small (bv_unsigned sp + -1088)) in Pagree by lia.
          split.
          -- intros x N1 N2 N3.
             rewrite EQM3. etransitivity.
             { apply (mem_denot_frame E' Mw fp1_regions log3 x cov3 w18_3 RF'). apply fp1_outside; rewrite ?P0'; first [assumption | unfold FP1_FR; lia]. }
             etransitivity. { apply Pagree; unfold FP1_FR, STDOUT_F in *; lia. }
             rewrite EQM2. etransitivity.
             { apply (mem_denot_frame E M0 fp1_regions log2 x cov2 w18_2 RF). apply fp1_outside; rewrite ?P0; first [assumption | unfold FP1_FR; lia]. }
             rewrite EQM1. apply (mem_denot_frame E M fp1_regions log1 x cov1 w18_1 RF). apply fp1_outside; rewrite ?P0; first [assumption | unfold FP1_FR; lia].
          -- eapply mem_grows_trans; [| rewrite EQM3; apply mem_denot_grows].
             eapply mem_grows_trans; [| exact Pgrows].
             eapply mem_grows_trans; [| rewrite EQM2; apply mem_denot_grows].
             rewrite EQM1; apply mem_denot_grows.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
          -- krd_solve HK.
  Qed.
End Run.
