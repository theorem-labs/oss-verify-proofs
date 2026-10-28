(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ExitBase.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WsegFast PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive RefMemcpyLib AgentLib.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WsegFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import SymAux RefPrintfLib.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition PF_FR : Z := 1056.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : 0x66420 <= bv_unsigned sp;
  PspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Pstk   : stk_ok RSEGS mem sp PF_FR;
  Pimg   : forall i, 0x10000 <= i < 0x33000 -> mem (Z_to_bv 64 i) = None;
  Pflags : rdn RSEGS mem (Z_to_bv 64 0x33f90) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  Pwend  : rdn RSEGS mem (Z_to_bv 64 0x33fb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x650b8));
  Pwpos  : rdn RSEGS mem (Z_to_bv 64 0x33fb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  Pw     : 0x64cb8 <= w <= 0x650b6;
  Pbsz   : rdn RSEGS mem (Z_to_bv 64 0x33ff0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  Plock  : rdn RSEGS mem (Z_to_bv 64 0x3401c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Plbf   : rdn RSEGS mem (Z_to_bv 64 0x34020) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Pcan   : rdn RSEGS mem (Z_to_bv 64 0x64450) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
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
                          | 0 => ELit 0 | 1 => ELit 0x1392c | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition pf_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x66420 0x7fffffffffff;
   KWr (SA (EVar 0) (-1056)) 1056;
   KImg 0x10000 0x33000;
   KWord (SA (ELit 0) 0x33f90) 4 (ELit 5);
   KWord (SA (ELit 0) 0x33fb0) 8 (ELit 0x650b8);
   KWord (SA (ELit 0) 0x33fb8) 8 (EVar 1);
   KRange (EVar 1) 0x64cb8 0x650b6;
   KWord (SA (ELit 0) 0x33ff0) 8 (ELit 1024);
   KWord (SA (ELit 0) 0x3401c) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x34020) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x64450) 8 (EVar 2);
   KWr (SA (ELit 0) 0x33000) 0x33000;
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
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x1392c.
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

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x33000) 208896 = true.
  Proof. exact S0ExitBase.ref_wseg_1c. Qed.  (* [comment removed for export] *)

  Lemma data_store_ok : forall m a n,
    0x33000 <= a -> a + Z.of_nat n <= 0x66000 -> store_ok RSEGS m (Z_to_bv 64 a) n = true.
  Proof.
    intros m a n Ha Hn.
    eapply (store_ok_window RSEGS m (Z_to_bv 64 0x33000) (Z_to_bv 64 a) 208896 n 0x33000 0x66000);
      [ apply u64_lit; lia | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply wseg_data
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
