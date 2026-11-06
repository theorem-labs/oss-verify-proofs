(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk Frame SymExec SymExec2 SymExec2Sound SymRun RefMemcpyLib AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymAux () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymAux.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "3map"; "4Z"; "0E"; "5Segment"]; ["6word_to_le_bytes"; "7bvmap"; "0R"; "0R'"; "8wbytes"; "9msteps"; ":frame_mod"; ":outside"; ";getr"; ";mkst"; "<callee_saved"; "<keeps_cs"; "=entry_covered"; "=log_covered"; "=rdenot"; "=regions_flat"]; ["=same_regs"; "=sregion"; ">SS"; ">adenot"; ">env"; ">expr"; ">kentry"; ">s_log"; ">s_pc"; ">s_regs"; ">saddr"; ">scripts"; ">sentry"; ">sidecond"; ">sr_get"; ">sym_exec"]; [">sym_state"; "?estart"; "?flat"; "?know_ok"; "?log_flat"; "?mem_denot"; "?regs_ok"; "?scs_denot"; "@In"; "Aadd"; "Ale"; "Alt"; "Aof_nat"; "0a"; "0base"; "0fuel"]; ["0fx"; "0kn"; "0log"; "0m"; "0nx"; "0pc"; "0r"; "0regs"; "0rom"; "0rs"; "0scr"; "0scr'"; "0scs"; "0segs"; "0sr"; "0sr'"]; ["0ss'"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0stops"; "0v"; "0w"; "0x"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition sregion : Type := (saddr * Z)%type.
Definition rdenot (E : env) (r : sregion) : word * Z :=
(Z_to_bv 64 (estart E (fst r)), snd r).
Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
match rs with
| [] => false
| (SA rb rk, n) :: rest =>
(expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
|| entry_covered rest a w
end.
Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
match log with
| [] => true
| SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
end.
Definition regions_flat (E : env) (rs : list sregion) : Prop :=
forall r, In r rs -> flat E (fst r) (snd r).
Lemma entry_covered_in : ltac2:(TCodec.tc2 tcn__SymAux "QN'Q4'1&Q1%211'Q:'2'RByR0%211'9'0&Lr4r3r2%43321(7%83721&Or6r5%3221&QBr7&QL%11=%43361'8&QJ&QAr8%221<&RC%12JE%6231&QK&QI%=1A%2271%4261%=261&;&G&<'6'=%22Q61&Nr9%211%74Q@41D%92O1%;11p0=1p0L1p0Q21p0Q71pU@QA1pU>QE1pSLQG1pTDQI1pNQM1").
Proof.
intros E rs a w x. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered map outside]; intros Hc Hrf Hfa Hx.
- discriminate.
- apply orb_prop in Hc as [Hc|Hc].
+ apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
intros [Hno _]. apply Hno. unfold in_rng, rdenot. cbn [fst snd].
pose proof (Hrf _ (or_introl eq_refl)) as Hfr. cbn [fst snd] in Hfr.
unfold flat, estart in *. cbn [a_base a_off] in *. rewrite <- H1 in *.
rewrite u64_lit by lia. lia.
+ intros [_ Hout]. apply (IH Hc); [| exact Hfa | exact Hx | exact Hout].
intros r Hr. apply Hrf. right. exact Hr.
Qed.
Lemma frame_layer : ltac2:(TCodec.tc2 tcn__SymAux "QJ'Q4'1&Q1%211'RByR0%211'4y8%511%311p051'Q:'2'9'0&Lr5r3r2%43321(7%83721&Or7r6%3221&QBr8&QLr4%211%534?1&F&D&Q3r9%221<&@%12F9%63@31&<'6'=%22Q61&N%11:%64Q=31C%?3H81p0A1p0H1p0M1pU<Q>1pU>Q81pSLQ:1pT8Q<1pTDQE1pNQI1").
Proof.
intros E rs m a w v Hc Hrf Hfa.
pose proof (flat_u E a _ Hfa) as Hu.
eapply frame_mod_weaken.
2:{ apply frame_mod_wbytes. rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). lia. }
intros x Hout. cbn [outside]. split; [|exact I].
intros Hin. unfold in_rng in Hin. rewrite length_N_to_le_bytes, Hu in Hin.
exact (entry_covered_in E rs a w x Hc Hrf Hfa Hin Hout).
Qed.
Theorem log_covered_frame : ltac2:(TCodec.tc2 tcn__SymAux "QA'Q4'RByR0%211'4y8%511%311p051'1&Q1%211'Q<%411'9'0&Mr2r1%3221(7%73621&Or5r3%3221&QDr6%2214&F&QEr7r4%33261&<'6'=%22Q21&N%118%64N31A%<3>81p0>1p0B1p0G1pT6Q01pTDQ31pSNQ71pNQ@1").
Proof.
intros E base rs log. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot log_flat]; intros Hc Hrf Hlf.
- apply frame_mod_refl.
- apply andb_prop in Hc as [H1 H2]. destruct Hlf as (Hw & Hfa & Hlf').
eapply frame_mod_trans_same; [apply IH; assumption|].
apply frame_layer; assumption.
Qed.
Lemma regs_ok_same : ltac2:(TCodec.tc2 tcn__SymAux "Q5'Q4'1'Q5%211&Ay5'RByR0%211%5241%415&QFr6r5r3%43321r7%63143'9&Q>%1286%2257%43D21&Hr4%22<1%32>2%93C21p061p0<1p0?1pT>E1pQ8G1pQ6H1pU0O1pTNQ01pNQ41").
Proof. intros E sr sr' R R' r HR HR' Hs. rewrite (HR r), (HR' r), Hs. reflexivity. Qed.
Fixpoint same_regs (sr sr' : list expr) (rs : list reg) : bool :=
match rs with
| [] => true
| r :: rest => expr_eqb (sr_get sr' r) (sr_get sr r) && same_regs sr sr' rest
end.
Lemma same_regs_sound : ltac2:(TCodec.tc2 tcn__SymAux "Q='Q4'1'Q5%211&Ay5'RByR0%211%5241%415%:11'9'0&Q0r5r4r1%43321(7%83721&QFr7r6%33218r8%5313:&QH%13B;=&Hr2%2291%3272%E3I21p061pT>I1p0:1p0=1p0B1pTDL1pQ8O1pQ6Q01pU0Q71pTNQ81pNQ<1").
Proof.
intros E sr sr' R R' rs. induction rs as [|r0 rest IH]; cbn [same_regs]; intros Hs HR HR' r Hin.
- destruct Hin.
- apply andb_prop in Hs as [H1 H2]. destruct Hin as [<-|Hin].
+ apply (regs_ok_same E sr sr' R R' r0 HR HR'). apply expr_eqb_eq. exact H1.
+ apply IH; assumption.
Qed.
Lemma keeps_cs_of_same : ltac2:(TCodec.tc2 tcn__SymAux "Q3'Q4'1'Q5%211&Ay5'RByR0%211%5241'9'0&Q0r4r3&J%43321(7%83721&QFr6r5%33218r7%5313:&K%125=p031p061p0;1pQ8E1pQ6F1pU0M1pTNN1pNQ21").
Proof. intros E sr sr' R R' Hs HR HR' r Hin. eapply same_regs_sound; eassumption. Qed.
Theorem run_sound_log : ltac2:(TCodec.tc2 tcn__SymAux "SD'1'?%211'2'=%511'Q;'Q5%811'Q<%:11'Q6%<11'Q@'Q=%?11'Q4'RByR0%211'4y8%511%311p051&Ay5%2218'9'6%12A?%221I&Q?r@r?(7r>r=(Q2r<r;r:r9r8%6554321(3%11Q0%?7>=<;:31(5r7r6%34Q6Q421r5%54GQ?21%J3G71&QFr2%235B1&QD%129D&QCrC%241=<G&QGrD%241@FH':'8&Q9%11Q0r1%@3N21&Q7%11Q4%@2Q11'ErF&IvR0&RArB%22QO1&QE%13Q:Q9QB%756Q331Q9&Q8%11QA%82R51%63Q?Q>?%<5;C21Q>%?3>61%H2A1%I2E1qQ6R21%L2R31p0N1p0Q21p0Q61p0Q91p0Q=1pT@R91pTBR=1pSNR>1pNRG1pTHS21pTJRJ1pU2RM1pT:S81pT4S01pT6S31pTNS61pT<S;1pTFS:1pU:S<1pT0S?1pTLSA1").
Proof.
intros segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom regs Hex HR Hlf HK Hsc.
eapply sym_exec_ex; [exact Hex | exact Hsc |].
exists regs. cbn [s_pc s_log s_regs s_know].
split; [reflexivity|]. split; [exact HR|]. split; [exact Hlf | exact HK].
Qed.
End FPX_1.
