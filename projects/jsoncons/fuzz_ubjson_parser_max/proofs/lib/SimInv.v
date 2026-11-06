(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SimInv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "stdpp.bitvector.definitions."], [["1list"; "2not"; "3N"; "3Z"; "0Hnoerr"; "0Hstep"; "0Inv"; "4modeled"; "5PhdrInfo"; "5Segment"; "5mkImage"; "6coexec"; "6never_errors"; "6omni_corun"; "7SError"; "7SNext"]; ["7config"; "7init_config"; "7mkEntry"; "7reaches_error"; "7run"; "7sstep"; "7star"; "8EntryDraw"; "9ProcInput"; "9event"; "0brk0"; "0c"; "0c'"; "0evs"; "0inp"; "0lim"]; ["0mb"; "0pc"; "0ph"; "0rnd"; "0segs"; "0sp"; ":bv"; "0tr"]]).
Ltac norm_fd32 :=
repeat match goal with
| |- context [fd32 AT_FDCWD] =>
change (fd32 AT_FDCWD) with AT_FDCWD32
| H : context [fd32 AT_FDCWD] |- _ =>
change (fd32 AT_FDCWD) with AT_FDCWD32 in H
| |- context [fd32 ?x] => change (fd32 x) with x
| H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
end.
Ltac fd32_ok :=
solve [ reflexivity
| assumption
| apply fd32_lt31; assumption
| apply fd32_id; assumption
| apply fd32_lt31; lia
| apply fd32_id; lia ].
Lemma star_inv : ltac2:(TCodec.tc2 tcn__SimInv "Q5'0'9%211'@!p021'I%711r4r3%211'Er6(?r2%211%544871%518p021p091pQJA1pQL>1pQHC1r5%11?'Fr7%241CB=%21Cp021p061pQJL1pR@I1pQHN1p<<1p>N1pR:Q21").
Proof. intros segs Inv Hstep.
intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
apply IHHstar. eapply Hstep; eauto.
Qed.
Lemma inv_no_reaches_error : ltac2:(TCodec.tc2 tcn__SimInv "Q:'0'9%211'@!p021'I%711r4r3%211'Er6(?r2%211%544871%518p021p091pQJA1pQL>1pQHC1%?19&1(>%?4>A<1%311p051pQLF1pQHK1r1%H11&C%12FD%;11p041pQHQ21p:81p<A1p>Q31pR:Q71").
Proof. intros segs Inv Hstep Hnoerr.
intros c HInv (tr & c' & evs & Hstar & Hss).
eapply Hnoerr; [| exact Hss].
eapply star_inv; eauto.
Qed.
Lemma inv_coexec : ltac2:(TCodec.tc2 tcn__SimInv "Q:'0'9%211'@!p021'I%711r4r3%211'Er6(?r2%211%544871%518p021p091pQJA1pQL>1pQHC1%?19&1(>%?4>A<1%311p051pQLF1pQHK1r1%H11';&<%23GE1p041pQHQ21p:81p<A1p>Q31pR:Q71").
Proof. intros segs Inv Hstep Hnoerr.
cofix CH. intros c HInv.
destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
- apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
- apply coexec_step; [exact Hh | |].
+ intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
+ intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.
Lemma no_error_run_corun : ltac2:(TCodec.tc2 tcn__SimInv "Q<'0'9%211'2'8'Q6yR0%211'G'3'H&1&Cr9&Ar8r7r6r5r4r3r2r1%99:87654321%<2;1%>11&=(:r:%231@>(B%14?>=<&<%754=2<1p091pQNI1pR0K1pR8M1pR2O1pQFQ01pR<Q11pR6Q51pR4Q71pR:Q91").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp H. cbn [omni_corun].
apply no_error_coexec, H.
Qed.
Lemma no_error_run_modeled : ltac2:(TCodec.tc2 tcn__SimInv "Q='0'9%211'2'8'Q6yR0%211'G'3'H&1&Cr9&Ar8r7r6r5r4r3r2r1%99:87654321%<2;1%>11&7&D(:r:%231A?(B%14@?>=%643=1<%811p0:1pQNJ1pR0L1pR8N1pR2Q01pQFQ11pR<Q21pR6Q61pR4Q81pR:Q:1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp H.
apply modeled_iff. cbn [img_segments].
eapply coexec_conseq; [apply no_error_run_corun, H | apply never_errors_covered].
Qed.
