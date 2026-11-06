(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Exec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec.WithSegs."; "stdpp.bitvector.definitions."], [["1None"; "1option"; "2eq"; "3machine_state"; "3ms_svc_pending"; "0P"; "0Q"; "4evt"; "4mstep"; "4msteps"; "0a"; "0b"; "0c"; "0ms"; "0ms'"; "0ms1"]; ["5bv"]]).
Section WithSegs.
Variable segs : list Segment.
Definition mstep (ms ms' : machine_state) : Prop :=
ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.
Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.
Lemma msteps_one : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec ";'3&8r2r1%3221'9r3%2215p041pN91pL:1").
Proof. intros. eapply msteps_cons; [eassumption|apply msteps_refl]. Qed.
Lemma msteps_trans : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "<'3'9r3r2%3221r5%5214p031p041pJ91pH:1pF;1").
Proof. intros a b c H; induction H; intros; [assumption|]. eapply msteps_cons; eauto. Qed.
Lemma mstep_det : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec ">'3&8r3r2%3221r4%5213'2%13836p031p061pH;1pF<1pL=1").
Proof. intros ms a b [_ Ha] [_ Hb]. congruence. Qed.
Lemma mstep_not_svc : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "D'3&8r2r1%3221'2'1'@yR0%211%411&4r3%211(0%116%;3631p0=1pNB1pLC1").
Proof. intros ms ms' [H _]; exact H. Qed.
Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
exists ms', msteps ms ms' /\ Q ms'.
Lemma evt_done : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "<'3!p021r2r1%211&7r3%2215p041pL:1p>91").
Proof. intros Q ms H. exists ms. split; [apply msteps_refl|exact H]. Qed.
Lemma evt_step : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "A'3!p021&8r2r1%3221&7r4%2215r5%4213p031p071pQ0>1pL?1p>>1").
Proof. intros Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [eapply msteps_cons; eauto|exact HQ]. Qed.
Lemma evt_cut : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "D'3!p021&7r3r1%3221r5%113r2%7231p031pN<1r4%;21:p031p0:1pLA1p>@1p<A1").
Proof.
intros P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
exists ms2. split; [eapply msteps_trans; eauto| exact HQ].
Qed.
Lemma evt_mono : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "D'3!p021&7r3r1%3221r5%113r2%311p031pN<1r4%;21:p031p0:1pLA1p>@1p<A1").
Proof. intros P Q ms H K. eapply evt_cut; [exact H|]. intros ms' HP. apply evt_done, K, HP. Qed.
Lemma evt_eq : ltac2:(TCodec.tc2 tcn__CJ_Lib_Exec "A'3!p021'2r2r1%33621&7r4%2215r5%4213p031p071pN>1pL?1p>>1").
Proof. intros; subst; assumption. Qed.
End WithSegs.
Arguments mstep segs ms ms' /.
