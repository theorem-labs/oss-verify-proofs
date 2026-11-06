(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__KillFree () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigintSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.KillFree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1list"; "2not"; "3Forall"; "3map"; "4N"; "4Z"; "5dies_by_signal"; "5error_free_unkilled"; "6Fs"; "7PhdrInfo"; "7Segment"; "7mkImage"; "8SpuriousCfg"; "8init_config"]; ["8mkEntry"; "8run_scfg"; "9EntryDraw"; ":ProcInput"; ":WriteEv"; ":event"; ";spec"; ";t_body"; "<ev_not_kill"; "<kill_free"; "=TSet"; "=t_alt2"; "=t_emit"; "=t_exit"; "=t_nil"; ">W"]; [">t_die"; "?srealizes"; "0T"; "0argv"; "0brk0"; "0ch"; "0code"; "0data"; "0evs"; "0fs"; "0inp"; "0lim"; "0mb"; "0msg"; "0pc"; "0ph"]; ["0rnd"; "0s"; "0scfg"; "0segs"; "0sp"; "@bv"]]).
Definition ev_not_kill (e : event) : Prop :=
match e with KillEv _ _ => False | _ => True end.
Definition kill_free (T : TSet) : Prop := forall tr, T tr -> Forall ev_not_kill tr.
Lemma Forall_prefix {A} (P : A -> Prop) : forall (l1 l2 : list A),
is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
induction l1 as [|x l1 IH]; intros l2 Hp Hl2; [constructor|].
destruct l2 as [|y l2]; cbn in Hp; [contradiction|].
destruct Hp as [-> Hp]. inversion Hl2; subst. constructor; [assumption | eapply IH; eassumption].
Qed.
Lemma kill_free_nil : ltac2:(TCodec.tc2 tcn__KillFree "3&I&N%211").
Proof. intros tr ->. constructor. Qed.
Lemma kill_free_emit : ltac2:(TCodec.tc2 tcn__KillFree "C'2'E%211&J'4&Hr2%33621&I%113&Lr4r3%3221%611p061p091pR6>1pRB@1").
Proof.
intros evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
- eapply Forall_prefix; eassumption.
- apply Forall_app. split; [exact Hevs | exact (HT _ Htr')].
Qed.
Lemma kill_free_alt2 : ltac2:(TCodec.tc2 tcn__KillFree "=&J&Ir2%211&Kr4r3%3221%711p061p071p4;1p2<1").
Proof. intros A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.
Lemma kill_free_exit : ltac2:(TCodec.tc2 tcn__KillFree "<'QEyR0%211&:&I&Mr2r1%3221%511pRD71pR>91").
Proof.
intros code fs. unfold t_exit. apply kill_free_emit; [| apply kill_free_nil].
constructor; [exact I | constructor].
Qed.
Lemma Forall_not_kill_writes : ltac2:(TCodec.tc2 tcn__KillFree "C'QEyR0%211'2y8%511%311'4'E&H&5(Dr2%211r1%54:721%93871pS4;1pR<@1").
Proof. intros ch s. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH]. Qed.
Section FPX_1.
Context {fx : PropExec.FPState}.
Lemma kill_free_W_emit : ltac2:(TCodec.tc2 tcn__KillFree "F'7'2'QEy8%211%411&J&Ir1%211&L&Or4r3%3221r2%6221%:11p091pR6=1pS4?1pR<E1").
Proof. intros ch s T HT. apply kill_free_emit; [apply Forall_not_kill_writes | exact HT]. Qed.
Lemma kill_free_die : ltac2:(TCodec.tc2 tcn__KillFree ">'2'QEy8%211%411&:&I&Q0r2r1%3221%511pRD71pRL91").
Proof. intros msg fs. unfold t_die. apply kill_free_W_emit. apply kill_free_exit. Qed.
Lemma kill_free_t_body : ltac2:(TCodec.tc2 tcn__KillFree ">'2'QEy8%211%411&:&I&Gr2r1%3221%511pRD71pR@91").
Proof.
intros data fs. unfold BigintSpec.t_body.
repeat first [ apply kill_free_die
| apply kill_free_W_emit
| apply kill_free_exit
| match goal with |- kill_free (if ?c then _ else _) => destruct c end
| match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.
Lemma kill_free_spec : ltac2:(TCodec.tc2 tcn__KillFree "?'2'QEy8%211%411%511&:&I&Fr2r1%3221%511pRD71pR891").
Proof.
intros argv fs. unfold BigintSpec.spec.
repeat first [ apply kill_free_die
| apply kill_free_t_body
| apply kill_free_alt2
| apply kill_free_exit
| match goal with |- kill_free (if ?c then _ else _) => destruct c end
| match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.
Lemma srealizes_not_dies_by_signal : ltac2:(TCodec.tc2 tcn__KillFree "QG'>'2'<%211'6';'QEyR0%211'B'7'C&J'Q1r:r;&?r9r8r7r6r5r4r3r2%99;87654321r1%>4=<21&I%115&3&8&Ar=(=r<%231EF(@%14EDCB%7563B1A%911%;11p0=1p0@1pR6Q01pRFQ21pRHQ41pS2Q61pRJQ81pR:Q91pS:Q:1pS0Q>1pRNQ@1pS8QB1pS6QF1").
Proof.
intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs HK (tr & sig & fs & Htr & Hin).
apply (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs) in Htr.
pose proof (HK _ Htr) as HF.
apply Forall_forall with (x := KillEv sig fs) in HF; [exact HF | exact Hin].
Qed.
Lemma srealizes_error_free_unkilled : ltac2:(TCodec.tc2 tcn__KillFree "QE'>'2'<%211'6';'QEyR0%211'B'7'C&J'Q1r:r;&?r9r8r7r6r5r4r3r2%99;87654321r1%>4=<21&I%115&9&Ar=(=r<%231DE(@%14DCBA%7563A1@%911p0;1p0>1pR6N1pRFQ01pRHQ21pS2Q41pRJQ61pR:Q71pS:Q81pS0Q<1pRNQ>1pS8Q@1pS6QD1").
Proof.
intros. split; [eapply srealizes_error_free; eassumption | eapply srealizes_not_dies_by_signal; eassumption].
Qed.
End FPX_1.
